import OMAReductions.R_mo_191889_R1
import Mathlib

/-!
# The five exceptional parameters for powerful sums of coprime fourth powers

A primitive representation with b ∣ z determines a fourth root of −1 modulo b³.
A table of roots modulo b, simple-root cancellation, and sign and exchange
symmetries give 14 lattices for the five parameters. Cramer's rule bounds both
coordinates in each lattice. Fourteen small-modulus square tests per lattice
tile bit patterns across both coordinates in blocks of at most 512 rows.
Packed indices specify the surviving points in each row. Their bit mask is
compared with the full intersection of all fourteen tests. Each surviving point
is checked for positivity, size, coprimality and nine further square-residue
conditions. The kernel verifies the root tables, bases, masks, and exhaustive
row checks from the integers printed below.

The cutoff and the five exceptional parameters come from the merged reduction
mo-191889.R1. The underlying minimum was proved by Noam D. Elkies and Gaurav Goel,
*On powerful integers expressible as sums of two coprime fourth powers*.
https://antsmath.org/ANTSXV/papers/ANTS-XV_elkies-goel.pdf
-/

namespace OMA.QuarticExceptional

/-- A primitive representation gives a well-defined projective slope modulo b^3. -/
private theorem slope {b z x y : ℕ} (hb : 0 < b) (hc : x.Coprime y) (hbz : b ∣ z)
    (eqn : x^4+y^4 = b*z^2) :
    ∃ u : ℕ, b^3 ∣ u^4+1 ∧ x ≡ u*y [MOD b^3] := by
  have : NeZero (b^3) := ⟨by positivity⟩
  have cop : y.Coprime b := by
    apply Nat.coprime_of_dvd
    intro p hp hy hb
    have hsum : p ∣ x^4+y^4 := eqn ▸ dvd_mul_of_dvd_left hb _
    have hxp : p ∣ x^4 := (Nat.dvd_add_iff_left (dvd_pow hy (by decide : 4 ≠ 0))).mpr hsum
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt (hp.dvd_of_dvd_pow hxp) hy) hc
  have cop3 := cop.pow_right 3
  obtain ⟨k,hk⟩ := hbz
  have hdiv : b^3 ∣ x^4+y^4 := ⟨k^2,by rw [eqn,hk]; ring⟩
  let v := (x : ZMod (b^3)) * (y : ZMod (b^3))⁻¹
  have hi : (y : ZMod (b^3)) * (y : ZMod (b^3))⁻¹ = 1 := ZMod.coe_mul_inv_eq_one y cop3
  have hv : v * (y : ZMod (b^3)) = x := by
    dsimp only [v]
    rw [mul_assoc,mul_comm _ (y : ZMod (b^3)),hi,mul_one]
  have hz : (x : ZMod (b^3))^4 + (y : ZMod (b^3))^4 = 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have hzero : v^4 + 1 = 0 := by
    have e := congrArg (fun t : ZMod (b^3) => t * ((y : ZMod (b^3))⁻¹)^4) hz
    rw [add_mul, ← mul_pow, ← mul_pow, hi, one_pow, zero_mul] at e
    exact e
  refine ⟨v.val, (ZMod.natCast_eq_zero_iff _ _).mp ?_, (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_⟩
  · simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_one,ZMod.natCast_zmod_val] using hzero
  · simpa only [Nat.cast_mul,ZMod.natCast_zmod_val] using hv.symm

/-- A simple root modulo b has at most one lift modulo b^3. The cancellation
uses the factorization of the difference of two fourth powers. -/
private theorem unique_lift {b u r : ℕ} (hu : b^3 ∣ u^4+1) (hr : b^3 ∣ r^4+1)
    (hs : u ≡ r [MOD b]) (hc : b.Coprime ((r+r)*(r^2+r^2))) :
    u ≡ r [MOD b^3] := by
  let c := (u+r)*(u^2+r^2)
  have hcon : c ≡ (r+r)*(r^2+r^2) [MOD b] := (hs.add Nat.ModEq.rfl).mul ((hs.pow 2).add Nat.ModEq.rfl)
  have hcop : b.Coprime c := by
    change b.gcd c = 1
    rw [Nat.gcd_comm, hcon.gcd_eq, Nat.gcd_comm]
    exact hc
  have powers : u^4 ≡ r^4 [MOD b^3] := Nat.ModEq.add_right_cancel' 1
    ((Nat.modEq_zero_iff_dvd.mpr hu).trans (Nat.modEq_zero_iff_dvd.mpr hr).symm)
  apply Nat.ModEq.cancel_left_of_coprime (hcop.pow_left 3)
  convert powers.add_right (u^3*r+u^2*r^2+u*r^3) using 1 <;> dsimp [c] <;> ring

private def bound : ℕ := 1325648472
private def limit : ℕ := 3088257489493360278725196965477359217

private structure Chart where
  twist : ℕ
  root : ℕ
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  uBound : ℕ
  vBound : ℕ
  deriving Inhabited, DecidableEq

private def Chart.x (L : Chart) (u v : ℤ) := L.a*u + L.c*v
private def Chart.y (L : Chart) (u v : ℤ) := L.b*u + L.d*v

/-- Reduction of the two-dimensional congruence lattice. The determinant is
the modulus, so Cramer's rule gives integer coordinates. -/
private theorem coordinates (L : Chart) (x y : ℤ) (hM : 0 < (L.twist^3 : ℤ))
    (det : L.a*L.d-L.b*L.c=(L.twist:ℤ)^3)
    (ac : (L.twist:ℤ)^3 ∣ L.a-(L.root:ℤ)*L.b)
    (cc : (L.twist:ℤ)^3 ∣ L.c-(L.root:ℤ)*L.d)
    (h : (L.twist:ℤ)^3 ∣ x-(L.root:ℤ)*y)
    (hx : |x| ≤ (bound:ℤ)) (hy : |y| ≤ (bound:ℤ))
    (ub : (|L.c|+|L.d|)*(bound:ℤ) < ((L.uBound:ℤ)+1)*(L.twist:ℤ)^3)
    (vb : (|L.a|+|L.b|)*(bound:ℤ) < ((L.vBound:ℤ)+1)*(L.twist:ℤ)^3) :
    ∃ u v : ℤ, |u| ≤ (L.uBound:ℤ) ∧ |v| ≤ (L.vBound:ℤ) ∧ L.x u v=x ∧ L.y u v=y := by
  let M := (L.twist:ℤ)^3
  have udiv : M ∣ L.d*x - L.c*y := by
    have e : L.d*x-L.c*y=L.d*(x-L.root*y)-(L.c-L.root*L.d)*y := by ring
    rw [e]; exact dvd_sub (dvd_mul_of_dvd_right h _) (dvd_mul_of_dvd_left cc _)
  have vdiv : M ∣ L.a*y - L.b*x := by
    have e : L.a*y-L.b*x=(L.a-L.root*L.b)*y-L.b*(x-L.root*y) := by ring
    rw [e]; exact dvd_sub (dvd_mul_of_dvd_left ac _) (dvd_mul_of_dvd_right h _)
  obtain ⟨u,hu⟩ := udiv
  obtain ⟨v,hv⟩ := vdiv
  have small (e f w X Y : ℤ) (he : e*X-f*Y=M*w)
      (hX : |X| ≤ (bound:ℤ)) (hY : |Y| ≤ (bound:ℤ)) (K : ℕ)
      (hk : (|e|+|f|)*(bound:ℤ) < ((K:ℤ)+1)*M) : |w| ≤ (K:ℤ) := by
    have le : |M*w| ≤ (|e|+|f|)*(bound:ℤ) := calc
      |M*w| = |e*X-f*Y| := congrArg abs he.symm
      _ ≤ |e*X|+|f*Y| := abs_sub _ _
      _ ≤ _ := by rw [abs_mul,abs_mul,add_mul]; gcongr
    rw [abs_mul,abs_of_pos hM,mul_comm M] at le
    have q := (mul_lt_mul_iff_left₀ hM).mp (le.trans_lt hk)
    omega
  refine ⟨u,v,small _ _ _ _ _ hu hx hy _ (by simpa only [add_comm] using ub),
    small _ _ _ _ _ hv hy hx _ vb,?_,?_⟩
  · apply mul_left_cancel₀ (ne_of_gt hM)
    change M*(L.a*u+L.c*v)=M*x
    linear_combination -L.a*hu-L.c*hv+x*det
  · apply mul_left_cancel₀ (ne_of_gt hM)
    change M*(L.b*u+L.d*v)=M*y
    linear_combination -L.b*hu-L.d*hv+y*det

private def rep (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | k+1 => let f := rep p k; (f <<< (p*2^k)) + f

private def factor (p k : ℕ) : ℕ :=
  ((1 <<< (p*2^k))-1) / ((1 <<< p)-1)

/-- Multiplication by the repetition factor tiles a p-bit pattern. The size
inequality keeps adjacent copies from carrying into one another. -/
private theorem repeated (p m k : ℕ) (hm : m < 2^p) :
    m*rep p k < 2^(p*2^k) ∧
    ∀ i < p*2^k, m.testBit (i%p) = true → (m*rep p k).testBit i = true := by
  induction k with
  | zero =>
    simp only [pow_zero,mul_one,rep]
    exact ⟨hm, fun i hi h => by simpa only [Nat.mod_eq_of_lt hi] using h⟩
  | succ k ih =>
    let w := p*2^k
    let t := m*rep p k
    have hw : p*2^(k+1) = w+w := by dsimp [w]; ring
    have ht : t < 2^w := ih.1
    have eq : m*rep p (k+1) = 2^w*t+t := by
      simp only [rep,Nat.shiftLeft_eq,w,t]; ring
    rw [eq,hw,pow_add]
    constructor
    · calc
        2^w*t+t < 2^w*t+2^w := Nat.add_lt_add_left ht _
        _ = 2^w*(t+1) := by ring
        _ ≤ 2^w*2^w := Nat.mul_le_mul_left _ ht
    · intro i hi h
      rw [Nat.testBit_two_pow_mul_add t ht i]
      by_cases hw' : i < w
      · rw [if_pos hw']; exact ih.2 i hw' h
      · rw [if_neg hw']
        have he : i-w+w=i := by omega
        have he' : (i-w)%p=i%p := by
          calc (i-w)%p = (i-w + p*2^k)%p := (Nat.add_mul_mod_self_left _ _ _).symm
               _ = i%p := congrArg (· % p) he
        exact ih.2 (i-w) (by omega) (by rw [he']; exact h)

private structure Good (b : ℕ) (x y : ℤ) : Prop where
  px : 0 < x.natAbs
  py : 0 < y.natAbs
  bx : x.natAbs ≤ bound
  by' : y.natAbs ≤ bound
  primitive : x.natAbs.Coprime y.natAbs
  small : x.natAbs^4 + y.natAbs^4 < limit
  value : ∃ z : ℕ, x^4+y^4 = (b:ℤ)*z^2

private structure Gate where
  p : ℕ
  depth : ℕ
  squares : ℕ
  rows : Array ℕ

private def residue (L : Chart) (p i j : ℕ) : ℕ :=
  let u := (i:ℤ)-L.uBound
  let x := (L.x u j) % (p:ℤ)
  let y := (L.y u j) % (p:ℤ)
  ((x^4+y^4) % (p:ℤ)).toNat

/-- One p-bit row for each residue of the second coordinate. Every modular
square must occur in the appropriate row. -/
private def Gate.OK (g : Gate) (L : Chart) : Prop :=
  0 < g.p ∧ 2*L.uBound+1 ≤ g.p*2^g.depth ∧
  factor g.p g.depth = rep g.p g.depth ∧
  (∀ z : Fin g.p, g.squares.testBit ((L.twist*z.val^2)%g.p) = true) ∧
  ∀ j : Fin g.p, g.rows[j.val]! < 2^g.p ∧
    ∀ i : Fin g.p, g.squares.testBit (residue L g.p i.val j.val) = true →
      g.rows[j.val]!.testBit i.val = true

private def wave (g : Gate) (j : ℕ) : ℕ :=
  g.rows[j%g.p]! * factor g.p g.depth

private theorem residue_eq (L : Chart) (p i j z : ℕ)
    (hz : (L.x ((i:ℤ)-L.uBound) j)^4 + (L.y ((i:ℤ)-L.uBound) j)^4 = (L.twist:ℤ)*z^2) :
    residue L p (i%p) (j%p) = (L.twist*(z%p)^2)%p := by
  have hi : ((i%p : ℕ):ℤ) ≡ (i:ℤ) [ZMOD (p:ℤ)] := Int.natCast_modEq_iff.mpr (Nat.mod_modEq _ _)
  have hj : ((j%p : ℕ):ℤ) ≡ (j:ℤ) [ZMOD (p:ℤ)] := Int.natCast_modEq_iff.mpr (Nat.mod_modEq _ _)
  have hu := hi.sub (Int.ModEq.refl (L.uBound:ℤ))
  have X := (hu.mul_left L.a).add (hj.mul_left L.c)
  have Y := (hu.mul_left L.b).add (hj.mul_left L.d)
  have e := (X.pow 4).add (Y.pow 4)
  change (L.x (((i%p:ℕ):ℤ)-L.uBound) (j%p:ℕ))^4 + (L.y (((i%p:ℕ):ℤ)-L.uBound) (j%p:ℕ))^4
      ≡ _ [ZMOD (p:ℤ)] at e
  rw [show L.a*((i:ℤ)-L.uBound)+L.c*j=L.x ((i:ℤ)-L.uBound) j from rfl,
      show L.b*((i:ℤ)-L.uBound)+L.d*j=L.y ((i:ℤ)-L.uBound) j from rfl,hz] at e
  have zz : (z:ℤ) ≡ ((z%p:ℕ):ℤ) [ZMOD (p:ℤ)] := (Int.natCast_modEq_iff.mpr (Nat.mod_modEq _ _)).symm
  have e' := e.trans ((zz.pow 2).mul_left (L.twist:ℤ))
  let x := L.x (((i%p:ℕ):ℤ)-L.uBound) (j%p:ℕ)
  let y := L.y (((i%p:ℕ):ℤ)-L.uBound) (j%p:ℕ)
  have ex : x % (p:ℤ) ≡ x [ZMOD (p:ℤ)] := by simp [Int.ModEq]
  have ey : y % (p:ℤ) ≡ y [ZMOD (p:ℤ)] := by simp [Int.ModEq]
  have eq := (((ex.pow 4).add (ey.pow 4)).trans e')
  change ((x%(p:ℤ))^4+(y%(p:ℤ))^4)%(p:ℤ) = ((L.twist:ℤ)*((z%p:ℕ):ℤ)^2)%(p:ℤ) at eq
  change (((x%(p:ℤ))^4+(y%(p:ℤ))^4)%(p:ℤ)).toNat = _
  rw [eq]
  exact_mod_cast (show (((L.twist*((z%p)^2))%p:ℕ):ℤ).toNat = _ from Int.toNat_natCast _)

private theorem wave_sound {g : Gate} {L : Chart} {i j : ℕ} (ok : g.OK L) (hi : i < 2*L.uBound+1)
    (h : Good L.twist (L.x ((i:ℤ)-L.uBound) j) (L.y ((i:ℤ)-L.uBound) j)) :
    (wave g j).testBit i = true := by
  obtain ⟨hp,cover,factorOK,squares,rows⟩ := ok
  obtain ⟨z,hz⟩ := h.value
  have row := rows ⟨j%g.p,Nat.mod_lt _ hp⟩
  have sq := squares ⟨z%g.p,Nat.mod_lt _ hp⟩
  have m := row.2 ⟨i%g.p,Nat.mod_lt _ hp⟩ (by rw [residue_eq L g.p i j z hz]; exact sq)
  unfold wave
  rw [factorOK]
  exact (repeated _ _ _ row.1).2 i (hi.trans_le cover) m

/-- These nine moduli distinguish the remaining nonsquares. The certificate
checks every square residue at each modulus. -/
private def squareTables : List (ℕ × ℕ) := [
  (97, 0x1eb628b476067981b8b451b5f),
  (173, 0x1299e1f15fb456f22411973a620913da8b7ea3e1e653),
  (191, 0x112160d566905e7236839d71463e93b185f69954f97b77f),
  (283, 0x348a7e33d517a5a05c99a980229c33be9c1a7c68233c6bbfe6a66c5fa5a17543381aed3),
  (109, 0x1752639f4e85b003685cbe7192bb),
  (397, 0x161ea45ddf2e70303516dd4f16bec2fad633a64824772c02e619d00d3b890499731ad7d0df5a3caeda2b03039d3eee895e1b),
  (311, 0x105305665a11762d2c278d57033b385ca34df04d3ac5e3233f154e1bcb4b9177a5995f35f7ff),
  (227, 0x26876a8197663bac38809297a071371fa16b6fee3ca2399167ea91e9b),
  (71, 0x1164729716b1d977f)]

private def squareTableTest (t : ℕ × ℕ) : Bool :=
  decide (0<t.1) && (List.range t.1).all (fun z => t.2.testBit (z^2%t.1))

set_option maxRecDepth 8000 in
private theorem squareTablesOK : squareTables.all squareTableTest = true := by decide +kernel

private def possibleSquare (n : ℕ) : Bool :=
  squareTables.all (fun t => t.2.testBit (n%t.1))

private theorem actualSquare (z : ℕ) : possibleSquare (z^2) = true := by
  apply List.all_eq_true.mpr
  intro t ht
  have ok := List.all_eq_true.mp squareTablesOK t ht
  simp only [squareTableTest,Bool.and_eq_true,decide_eq_true_eq] at ok
  have hit := List.all_eq_true.mp ok.2 (z%t.1) (List.mem_range.mpr (Nat.mod_lt _ ok.1))
  have eq := (Nat.mod_modEq z t.1).pow 2
  change (z%t.1)^2%t.1=z^2%t.1 at eq
  simpa only [eq] using hit

private def candidate (L : Chart) (j i : ℕ) : Bool :=
  let x := (L.x ((i:ℤ)-L.uBound) j).natAbs
  let y := (L.y ((i:ℤ)-L.uBound) j).natAbs
  let s := x^4+y^4
  let n := L.twist*s
  decide (0<x ∧ 0<y ∧ x≤bound ∧ y≤bound ∧ x.Coprime y ∧ s<limit ∧ possibleSquare n = true)

private theorem candidate_good {L : Chart} {j i : ℕ}
    (h : Good L.twist (L.x ((i:ℤ)-L.uBound) j) (L.y ((i:ℤ)-L.uBound) j)) :
    candidate L j i = true := by
  obtain ⟨z,hz⟩ := h.value
  let x := L.x ((i:ℤ)-L.uBound) j
  let y := L.y ((i:ℤ)-L.uBound) j
  have abs4 (v : ℤ) : (v.natAbs:ℤ)^4=v^4 := by
    rw [Int.natCast_natAbs, ← abs_pow, abs_of_nonneg (by positivity)]
  have hcast : (x.natAbs:ℤ)^4+(y.natAbs:ℤ)^4=(L.twist:ℤ)*z^2 := by
    rw [abs4,abs4]; exact hz
  have hn : x.natAbs^4+y.natAbs^4=L.twist*z^2 := by exact_mod_cast hcast
  have sq : L.twist*(x.natAbs^4+y.natAbs^4)=(L.twist*z)^2 := by rw [hn];ring
  apply decide_eq_true
  refine ⟨h.px,h.py,h.bx,h.by',h.primitive,h.small,?_⟩
  rw [sq]
  exact actualSquare _

private def gateTest (g : Gate) (L : Chart) : Bool :=
  decide (0 < g.p ∧ 2*L.uBound+1 ≤ g.p*2^g.depth ∧ factor g.p g.depth = rep g.p g.depth) &&
    (List.range g.p).all (fun z => g.squares.testBit (L.twist*z^2%g.p)) &&
    (List.range g.p).all (fun j =>
      decide (g.rows[j]! < 2^g.p) && (List.range g.p).all (fun i =>
        !(g.squares.testBit (residue L g.p i j)) || g.rows[j]!.testBit i))

private theorem gate_of_test {g : Gate} {L : Chart} (h : gateTest g L = true) : g.OK L := by
  simp only [gateTest, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1.1.1,h.1.1.2.1,h.1.1.2.2,?_,?_⟩
  · intro z
    exact List.all_eq_true.mp h.1.2 z.val (List.mem_range.mpr z.isLt)
  · intro j
    have row := List.all_eq_true.mp h.2 j.val (List.mem_range.mpr j.isLt)
    simp only [Bool.and_eq_true,decide_eq_true_eq] at row
    refine ⟨row.1,?_⟩
    intro i hit
    have v := List.all_eq_true.mp row.2 i.val (List.mem_range.mpr i.isLt)
    simpa only [hit,Bool.not_true,Bool.false_or] using v

private def Block (f : ℕ → Bool) (lo hi : ℕ) : Prop :=
  ∀ i, lo ≤ i → i < hi → f i = true

private theorem checkedBlock {f : ℕ → Bool} {lo hi : ℕ}
    (h : (List.range (hi-lo)).all (fun j => f (lo+j)) = true) : Block f lo hi := by
  intro i hl hh
  have z := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le hl] using z

private theorem joinBlock {f : ℕ → Bool} {a b c : ℕ}
    (left : Block f a b) (right : Block f b c) : Block f a c := by
  intro i lo hi
  by_cases h : i < b
  · exact left i lo h
  · exact right i (by omega) hi

/-- Read the low sixteen bits as an index in a lattice row. -/
private def listedMask : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k+1, code => (1 <<< (code%65536)) ||| listedMask k (code/65536)

private def excluded (f : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, _ => true
  | k+1, code => !f (code%65536) && excluded f k (code/65536)

private theorem excluded_sound {f : ℕ → Bool} (k code i : ℕ)
    (h : excluded f k code = true) (bit : (listedMask k code).testBit i = true) :
    f i=false := by
  induction k generalizing code with
  | zero => simp [listedMask] at bit
  | succ k ih =>
    simp only [excluded,Bool.and_eq_true,Bool.not_eq_true'] at h
    by_cases e : code%65536=i
    · simpa only [e] using h.1
    · apply ih _ h.2
      simpa [listedMask,Nat.testBit_or,Nat.shiftLeft_eq,Nat.testBit_two_pow,e,Ne.symm e] using bit

private def Region (P : ℕ → Prop) (lo hi : ℕ) : Prop :=
  ∀ j, lo ≤ j → j < hi → P j

private theorem mergeRegion {P : ℕ → Prop} {a b c : ℕ}
    (left : Region P a b) (right : Region P b c) : Region P a c := by
  intro j lo hi
  by_cases h : j<b
  · exact left j lo h
  · exact right j (by omega) hi

private def width (L : Chart) := 2*L.uBound+1
private def ones (n : ℕ) := (1 <<< n)-1

private theorem bit_ones {i n : ℕ} (h : i<n) : (ones n).testBit i=true := by
  simpa [ones,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one] using h

/-- Double a rectangular bit pattern vertically by a shift and a union. -/
private def tile (w : ℕ) : ℕ → ℕ → ℕ
  | 0, m => m
  | k+1, m =>
    let t := tile w k m
    t ||| (t <<< (w*2^k))

private theorem tile_sound {w m : ℕ} (k i : ℕ) (hi : i<w*2^k)
    (h : m.testBit (i%w)=true) : (tile w k m).testBit i=true := by
  induction k generalizing i with
  | zero => simpa [tile, Nat.mod_eq_of_lt (by simpa using hi : i<w)] using h
  | succ k ih =>
    rw [tile,Nat.testBit_or,Bool.or_eq_true]
    by_cases e : i<w*2^k
    · exact Or.inl (ih i e h)
    · right
      rw [Nat.testBit_shiftLeft,Bool.and_eq_true]
      refine ⟨by simp only [decide_eq_true_eq];omega,?_⟩
      have h2 : w*2^(k+1)=w*2^k+w*2^k := by ring
      have eq : (i-w*2^k)%w=i%w := by
        calc (i-w*2^k)%w = (i-w*2^k+w*2^k)%w := (Nat.add_mul_mod_self_left _ _ _).symm
             _ = i%w := by rw [Nat.sub_add_cancel (by omega)]
      exact ih _ (by omega) (by rw [eq];exact h)

/-- One vertical period, starting at row lo. Each horizontal row is clipped
to the chart width before it is placed in this integer. -/
private def period (L : Chart) (g : Gate) (lo : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => period L g lo n ||| ((wave g (lo+n) &&& ones (width L)) <<< (width L*n))

private theorem period_hit {L : Chart} {g : Gate} {lo i j : ℕ} (n : ℕ)
    (hi : i<width L) (hj : j<n) (h : (wave g (lo+j)).testBit i=true) :
    (period L g lo n).testBit (width L*j+i)=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [period,Nat.testBit_or,Bool.or_eq_true]
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj) with ne|rfl
    · exact Or.inl (ih ne)
    · right; simp [Nat.testBit_shiftLeft,Nat.testBit_and,bit_ones hi,h]

private def vDepth (p : ℕ) := (511/p).log2+1

private def sheetGate (L : Chart) (g : Gate) (lo : ℕ) : ℕ :=
  tile (width L*g.p) (vDepth g.p) (period L g lo g.p)

private theorem sheet_gate_hit {L : Chart} {g : Gate} {i j lo : ℕ}
    (ok : g.OK L) (tall : 512≤g.p*2^(vDepth g.p)) (hi : i<width L) (hj : j<512)
    (good : Good L.twist (L.x ((i:ℤ)-L.uBound) (lo+j)) (L.y ((i:ℤ)-L.uBound) (lo+j))) :
    (sheetGate L g lo).testBit (width L*j+i)=true := by
  let w := width L
  have bound (t N : ℕ) (ht : t<N) : w*t+i < w*N := by
    calc w*t+i < w*t+w := Nat.add_lt_add_left hi _
         _ = w*(t+1) := by ring
         _ ≤ w*N := Nat.mul_le_mul_left _ ht
  have mod : (w*j+i)%(w*g.p)=w*(j%g.p)+i := by
    have e : w*j+i = (w*(j%g.p)+i)+(w*g.p)*(j/g.p) := by
      calc w*j+i = w*(j%g.p+g.p*(j/g.p))+i := by rw [Nat.mod_add_div]
           _ = _ := by ring
    rw [e,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (bound _ _ (Nat.mod_lt _ ok.1))]
  apply tile_sound
  · simpa [w,Nat.mul_assoc] using bound _ _ (hj.trans_le tall)
  · rw [show (width L*j+i)%(width L*g.p)=_ from mod]
    apply period_hit g.p hi (Nat.mod_lt _ ok.1)
    have hit := wave_sound (i:=i) (j:=lo+j) ok hi good
    simpa only [wave,Nat.add_mod_mod] using hit

/-- Intersection of the modular tests in an entire horizontal strip. -/
private def plane (L : Chart) (gs : List Gate) (lo n : ℕ) : ℕ :=
  gs.foldr (fun g m => sheetGate L g lo &&& m) (ones (width L*n))

private theorem plane_hit {L : Chart} {gs : List Gate} {lo n j i : ℕ}
    (valid : ∀ g ∈ gs, g.OK L ∧ 512≤g.p*2^vDepth g.p)
    (hn : n≤512) (hi : i<width L) (hj : j<n)
    (good : Good L.twist (L.x ((i:ℤ)-L.uBound) (lo+j)) (L.y ((i:ℤ)-L.uBound) (lo+j))) :
    (plane L gs lo n).testBit (width L*j+i)=true := by
  induction gs with
  | nil =>
    apply bit_ones
    calc width L*j+i < width L*j+width L := Nat.add_lt_add_left hi _
         _ = width L*(j+1) := by ring
         _ ≤ _ := Nat.mul_le_mul_left _ hj
  | cons g gs ih =>
    have a := valid g List.mem_cons_self
    have b := ih (fun k hk => valid k (List.mem_cons_of_mem _ hk))
    simpa only [plane,List.foldr_cons,Nat.testBit_and,sheet_gate_hit a.1 a.2 hi (hj.trans_le hn) good,
      Bool.true_and] using b

/-- Each row gives its length in five bits and lists its indices in sixteen-bit
fields. Equality with the reconstructed row certifies every omission. -/
private def replay (L : Chart) : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _, _ => true
  | n+1, lo, sizes, code, mask =>
    let k := sizes%32
    (mask &&& ones (width L) == listedMask k code) && excluded (candidate L lo) k code &&
      replay L n (lo+1) (sizes/32) (code >>> (16*k)) (mask >>> width L)

private theorem replay_hit (L : Chart) (n lo sizes code mask j i : ℕ)
    (ok : replay L n lo sizes code mask=true) (hj : j<n) (hi : i<width L)
    (bit : mask.testBit (width L*j+i)=true) : candidate L (lo+j) i=false := by
  induction n generalizing lo sizes code mask j with
  | zero => omega
  | succ n ih =>
    simp only [replay,Bool.and_eq_true,beq_iff_eq] at ok
    cases j with
    | zero =>
      simp only [Nat.mul_zero,Nat.zero_add] at bit
      have b : (mask &&& ones (width L)).testBit i=true := by
        simp [Nat.testBit_and,bit_ones hi,bit]
      rw [ok.1.1] at b
      simpa only [Nat.add_zero] using excluded_sound _ _ _ ok.1.2 b
    | succ j =>
      have b : (mask >>> width L).testBit (width L*j+i)=true := by
        rw [Nat.testBit_shiftRight,show width L+(width L*j+i)=width L*(j+1)+i by ring]
        exact bit
      have res := ih _ _ _ _ j ok.2 (by omega) b
      rwa [show lo+1+j=lo+(j+1) by omega] at res

/-- A balanced subdivision keeps shifts and intersections local to a strip. -/
private inductive Patch where
  | leaf (rows sizes code : ℕ)
  | join (left right : Patch)

private def Patch.height : Patch → ℕ
  | .leaf h _ _ => h
  | .join l r => l.height+r.height

private def Patch.check (L : Chart) : Patch → ℕ → ℕ → Bool
  | .leaf n s c, lo, mask => replay L n lo s c mask
  | .join l r, lo, mask =>
    let d := width L*l.height
    l.check L lo (mask &&& ones d) && r.check L (lo+l.height) (mask >>> d)

private theorem patch_hit (L : Chart) (p : Patch) (lo mask j i : ℕ)
    (ok : p.check L lo mask=true) (hj : j<p.height) (hi : i<width L)
    (bit : mask.testBit (width L*j+i)=true) : candidate L (lo+j) i=false := by
  induction p generalizing lo mask j with
  | leaf n s c => exact replay_hit _ _ _ _ _ _ _ _ ok hj hi bit
  | join l r left right =>
    change j<l.height+r.height at hj
    simp only [Patch.check,Bool.and_eq_true] at ok
    by_cases h : j<l.height
    · have small : width L*j+i < width L*l.height := calc
        width L*j+i < width L*j+width L := Nat.add_lt_add_left hi _
        _ = width L*(j+1) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ h
      exact left _ _ _ ok.1 h (by simp [Nat.testBit_and,bit_ones small,bit])
    · have eq : j-l.height+l.height=j := Nat.sub_add_cancel (by omega)
      have b : (mask >>> (width L*l.height)).testBit (width L*(j-l.height)+i)=true := by
        rw [Nat.testBit_shiftRight,show width L*l.height+(width L*(j-l.height)+i)=width L*j+i by
          calc _ = width L*(j-l.height+l.height)+i := by ring
               _ = _ := by rw [eq]]
        exact bit
      have result := right (lo+l.height) _ (j-l.height) ok.2 (by omega) b
      rwa [show lo+l.height+(j-l.height)=lo+j by omega] at result

private def clearPoint (L : Chart) (j : ℕ) : Prop :=
  ∀ i, i<width L → ¬Good L.twist (L.x ((i:ℤ)-L.uBound) j) (L.y ((i:ℤ)-L.uBound) j)

private theorem checkedPatch {L : Chart} {gs : List Gate} (lo : ℕ) (p : Patch)
    (valid : ∀ g ∈ gs, g.OK L ∧ 512≤g.p*2^vDepth g.p) (n : p.height≤512)
    (ok : p.check L lo (plane L gs lo p.height)=true) : Region (clearPoint L) lo (lo+p.height) := by
  intro j hj hj' i hi h
  have eq : lo+(j-lo)=j := by omega
  have ei : (lo:ℤ)+((j-lo:ℕ):ℤ)=(j:ℤ) := by omega
  have good : Good L.twist (L.x ((i:ℤ)-L.uBound) ((lo:ℤ)+((j-lo:ℕ):ℤ)))
      (L.y ((i:ℤ)-L.uBound) ((lo:ℤ)+((j-lo:ℕ):ℤ))) := by rwa [ei]
  have bit := plane_hit (lo:=lo) valid n hi (show j-lo<p.height by omega) good
  have bad := patch_hit L p lo _ (j-lo) i ok (by omega) hi bit
  rw [eq,candidate_good h] at bad
  contradiction

private theorem good_swap {b : ℕ} {x y : ℤ} (h : Good b x y) : Good b y x := by
  refine ⟨h.py,h.px,h.by',h.bx,h.primitive.symm,?_,?_⟩
  · simpa only [add_comm] using h.small
  · simpa only [add_comm] using h.value

private theorem good_neg {b : ℕ} {x y : ℤ} (h : Good b x y) : Good b (-x) y := by
  have he : (-x)^4=x^4 := by ring
  exact ⟨by simpa using h.px,h.py,by simpa using h.bx,h.by',by simpa using h.primitive,
    by simpa only [Int.natAbs_neg] using h.small,by simpa only [he] using h.value⟩

private def Clear (L : Chart) : Prop :=
  ∀ x y : ℤ, Good L.twist x y → (L.twist:ℤ)^3 ∣ x-(L.root:ℤ)*y → False

private def Chart.OK (L : Chart) : Prop :=
  0 < (L.twist:ℤ)^3 ∧ L.a*L.d-L.b*L.c=(L.twist:ℤ)^3 ∧
  (L.twist:ℤ)^3 ∣ L.a-(L.root:ℤ)*L.b ∧ (L.twist:ℤ)^3 ∣ L.c-(L.root:ℤ)*L.d ∧
  (|L.c|+|L.d|)*(bound:ℤ) < ((L.uBound:ℤ)+1)*(L.twist:ℤ)^3 ∧
  (|L.a|+|L.b|)*(bound:ℤ) < ((L.vBound:ℤ)+1)*(L.twist:ℤ)^3

private instance (L : Chart) : Decidable L.OK := by unfold Chart.OK; infer_instance

private theorem clear_of_scan {L : Chart} (ok : L.OK)
    (scanned : Region (clearPoint L) 0 (L.vBound+1)) : Clear L := by
  intro x y h hxy
  obtain ⟨hm,hd,ha,hc,hu,hv⟩ := ok
  have ax : |x| ≤ (bound:ℤ) := by
    rw [← Int.natCast_natAbs]; exact_mod_cast h.bx
  have ay : |y| ≤ (bound:ℤ) := by
    rw [← Int.natCast_natAbs]; exact_mod_cast h.by'
  obtain ⟨u,v,ub,vb,ex,ey⟩ := coordinates L x y hm hd ha hc hxy ax ay hu hv
  have test (s t : ℤ) (hs : |s| ≤ (L.uBound:ℤ)) (ht : |t| ≤ (L.vBound:ℤ))
      (h0 : 0 ≤ t) (possible : Good L.twist (L.x s t) (L.y s t)) : False := by
    let i := (s+L.uBound).toNat
    let j := t.toNat
    have rangeS := abs_le.mp hs
    have rangeT := abs_le.mp ht
    have ei : (i:ℤ)-L.uBound = s := by dsimp [i]; omega
    have ej : (j:ℤ)=t := by dsimp [j]; omega
    have hi : i < 2*L.uBound+1 := by omega
    have hj : j < L.vBound+1 := by omega
    exact scanned _ (Nat.zero_le _) hj _ hi (by rw [ei,ej]; exact possible)
  have position : Good L.twist (L.x u v) (L.y u v) := by rwa [ex,ey]
  by_cases hv0 : 0 ≤ v
  · exact test u v ub vb hv0 position
  · apply test (-u) (-v) (by simpa using ub) (by simpa using vb) (by omega)
    have both := good_swap (good_neg (good_swap (good_neg position)))
    convert both using 1 <;> simp only [Chart.x,Chart.y] <;> ring

/-- Signs and exchange of the two fourth powers preserve the problem. -/
private def turn (t : Fin 4) (x y : ℤ) : ℤ × ℤ :=
  if t=0 then (x,y) else if t=1 then (-x,y) else if t=2 then (y,x) else (-y,x)

private theorem good_turn {b : ℕ} {x y : ℤ} (t : Fin 4) (h : Good b x y) :
    Good b (turn t x y).1 (turn t x y).2 := by
  fin_cases t
  · exact h
  · exact good_neg h
  · exact good_swap h
  · exact good_neg (good_swap h)

private theorem turn_dvd (t : Fin 4) (M r R x y : ℤ) (h : M ∣ x-r*y)
    (ht : M ∣ (turn t r 1).1-R*(turn t r 1).2) :
    M ∣ (turn t x y).1-R*(turn t x y).2 := by
  have e : (turn t x y).1-R*(turn t x y).2 =
      ((turn t 1 0).1-R*(turn t 1 0).2)*(x-r*y) +
        ((turn t r 1).1-R*(turn t r 1).2)*y := by
    fin_cases t <;> simp [turn] <;> ring
  rw [e]
  exact dvd_add (dvd_mul_of_dvd_right h _) (dvd_mul_of_dvd_left ht _)

private structure Entry where
  lift : ℕ
  chart : Chart
  mode : Fin 4
  deriving DecidableEq

private def Entry.OK (e : Entry) (b : ℕ) : Prop :=
  e.chart.twist=b ∧ b^3 ∣ e.lift^4+1 ∧ b.Coprime ((e.lift+e.lift)*(e.lift^2+e.lift^2)) ∧
  (b:ℤ)^3 ∣ (turn e.mode e.lift 1).1-(e.chart.root:ℤ)*(turn e.mode e.lift 1).2

private instance (e : Entry) (b : ℕ) : Decidable (e.OK b) := by unfold Entry.OK;infer_instance

private def Covers (b : ℕ) (es : List Entry) : Prop :=
  ∀ i : Fin b, (i.val^4+1)%b = 0 → ∃ e ∈ es, e.lift%b=i.val

private def rootTest (b : ℕ) (es : List Entry) (i : ℕ) : Bool :=
  (i^4+1)%b != 0 || es.any (fun e => e.lift%b == i)

private theorem covers_of_test {b : ℕ} {es : List Entry}
    (tested : Block (rootTest b es) 0 b) : Covers b es := by
  intro i h
  have pass := tested i.val (Nat.zero_le _) i.isLt
  simpa [rootTest, h, List.any_eq_true] using pass

private theorem by_table {b z x y : ℕ} {es : List Entry} (hb : 0<b)
    (covers : Covers b es) (valid : ∀ e ∈ es, e.OK b) (cleared : ∀ e ∈ es, Clear e.chart)
    (hc : x.Coprime y) (hz : b ∣ z) (eqn : x^4+y^4=b*z^2) (good : Good b x y) : False := by
  obtain ⟨u,hu,hxy⟩ := slope hb hc hz eqn
  have dvd : b ∣ u^4+1 := (dvd_pow_self b (by decide : 3 ≠ 0)).trans hu
  have low := (((Nat.mod_modEq u b).pow 4).add_right 1).trans (Nat.modEq_zero_iff_dvd.mpr dvd)
  obtain ⟨e,he,hmod⟩ := covers ⟨u%b,Nat.mod_lt _ hb⟩ (by simpa [Nat.ModEq] using low)
  obtain ⟨bt,root,simple,match'⟩ := valid e he
  have exactRoot := unique_lift hu root (show u ≡ e.lift [MOD b] from hmod.symm) simple
  have congr := Int.natCast_modEq_iff.mpr (hxy.trans (exactRoot.mul_right y))
  have div : (b:ℤ)^3 ∣ (x:ℤ)-(e.lift:ℤ)*y := by
    simpa only [Nat.cast_pow,Nat.cast_mul] using congr.symm.dvd
  have moved := turn_dvd e.mode ((b:ℤ)^3) e.lift e.chart.root x y div match'
  apply cleared e he _ _
  · rw [bt]; exact good_turn e.mode good
  · simpa only [bt] using moved

private def L0 : Chart := ⟨6577, 66286287192, -21838, 58809, -4242723, -1602277, 27235, 375⟩

private def g0_29 : Gate := ⟨29, 11, 0x13d122f3, #[
    0x1fffffff, 0x5134c10, 0x110d8092, 0x2c05870, 0x1c808438, 0xe020c70, 0x1162950, 0x11032113,
    0x4a92054, 0x120006b9, 0x2f0152, 0x8b05054, 0x44919a, 0x11048319, 0x1ac09012, 0x240d690,
    0x10482331, 0x24880b3, 0x2834454, 0x3d0095, 0x1800133a, 0x1254854, 0x1302391, 0x51a2015,
    0xc101c1c, 0x8404e38, 0x680d01c, 0x6c2292, 0xcb22810]⟩
private theorem g0_29_ok : g0_29.OK L0 := gate_of_test (by decide +kernel)

private def g0_53 : Gate := ⟨53, 11, 0xd228fccfc512d, #[
    0x400000000000, 0x1a60a64695a0c, 0xf30d8a3107840, 0x1f8a8489942288, 0x14940be509101e, 0x183a4d4c3a400c, 0x1589130261212f, 0x1101a640553d89,
    0x124c08115fa66, 0x12062ac2a08d27, 0x2b71841446968, 0x498dda004d614, 0xf018604962ab2, 0x1c84b6180aa252, 0xc8887b8f060a0, 0x80da081f43d18,
    0x498ebe20b0a04, 0x821a5a9446e11, 0x12007039934ab1, 0x3023189a25cf0, 0x191c5e258a6004, 0x1c90481aa8ce81, 0x10d29cf459802, 0x122ab005811de2,
    0x148a072272824b, 0x103ad0a8ee00d0, 0x122631658872a, 0x89054e11a68c6, 0xb810b0077150b, 0xa25d2414e44e0, 0xa8947b881a00d, 0x16104019a2f394,
    0x1278173155812, 0x713200651a47a, 0x8180f3a45918c, 0x98d52c99c0e, 0x108288762295a5, 0x3242050d047d7, 0x160218bc2f8105, 0x22605060f1de1,
    0x4274a4550186d, 0x101e4d54692061, 0x324286b2005bb, 0x1da81696228218, 0xc09e4b1054354, 0x490665fa88103, 0x101191bcaa0265, 0x1235f4848640c8,
    0xb8330025c32b2, 0x525780890a7d0, 0xa3f1144299121, 0x19e021e08c51b, 0xcb0305a962650]⟩
private theorem g0_53_ok : g0_53.OK L0 := gate_of_test (by decide +kernel)

private def g0_37 : Gate := ⟨37, 11, 0x165e211e9b, #[
    0x8, 0x693ab7606, 0x18b6e38546, 0x1765786131, 0x11e8473656, 0x1fe02b0e26, 0xd179431b5, 0x1b7c14c354,
    0x13a1f6c232, 0x1ab0df46c0, 0x19f55e8086, 0x9b08dba47, 0x651a13de3, 0x1d4dd2c291, 0x34f15f223, 0x41b7967a1,
    0x138f4481f5, 0x98aa93de4, 0xbe6478a51, 0x51e267d45, 0x1bc9551913, 0x18122f1cd7, 0x1e69ed8242, 0x4fa8f2c62,
    0x1434bb2bc4, 0x1bc858a663, 0x5db10d971, 0x1017aaf9b0, 0x162fb0d581, 0x436f85ca6, 0xc3283ed95, 0x18c29e8b56,
    0x70d407fb2, 0x6ce2178b5, 0x861ea6ec6, 0xa1c76d1b1, 0x6ed5c9630]⟩
private theorem g0_37_ok : g0_37.OK L0 := gate_of_test (by decide +kernel)

private def g0_59 : Gate := ⟨59, 10, 0x22b62183e7b92bb, #[
    0x1000000000, 0xfc0938fa556717, 0x8e1ad48fd4ebb1, 0x633c29eb66eda08, 0x3e67b38485d5b9, 0x3f49bd28308f96a, 0x728e61564794b4f, 0x1395cb5fd974023,
    0x1e9dcf2f4810ea9, 0xac3b537ab1f4c8, 0x43ef59a660afa24, 0x2f0e17e63ada2a1, 0x5c962993beb09d4, 0x76a3f7e4a21bb0, 0x39d045317d71e93, 0x28b3535beb80c2f,
    0x5952f7265d3ac82, 0x4b7a07dc68d64a3, 0xfed9387154ccf0, 0xe92d988d3654f7, 0x77bb61649614aac, 0x342e2f87364b2c7, 0x5e2137741c8fe45, 0x21502fc38796777,
    0x3c064bc9876f5c6, 0x70bd1dd20a67d1c, 0x640f7f3d5412e68, 0x38d841d3dce933a, 0x281ab30d29bd7b3, 0x776f99439141ec8, 0x5138533eddc4de, 0x7b29619ab02b37a,
    0x2e7797043639732, 0x105579fde04c59d, 0x4ca097717a1ce2f, 0x6dc327a4c0798eb, 0x53c387e8150bbb9, 0x62705dd908f689f, 0x24d9c3e8e85b8d3, 0x50d24d0dbbdcd54,
    0x4d96233692e3bca, 0x6551c3936fe03cc, 0x562c77c0bda7149, 0x3974c9de953504d, 0x3afb5959a2bd0c, 0x1d7d1944173b25e, 0x8a4fdf8adc0376, 0x1afb9328d274ae4,
    0x36b8cfd0e1ea151, 0x6a0ccb35ef84917, 0x71abd95b86a04cb, 0x1025e9e772f255c, 0x5d37f5a75393100, 0x53c4d50ce29fcb4, 0x6218297b25f95a7, 0x742439bccf8276a,
    0x6ecdaf28798c416, 0x657e256b0e22375, 0x554be39207e3a39]⟩
private theorem g0_59_ok : g0_59.OK L0 := gate_of_test (by decide +kernel)

private def g0_47 : Gate := ⟨47, 11, 0x7bcae4d8ac21, #[
    0x7fffffffffff, 0x26a26c3fa233, 0x185b4a35f730, 0x5c2d441da5da, 0x3e4b101e45de, 0x1c84d582bcdd, 0x66e2c88fc532, 0x16268b31c76b,
    0x36a6a82ff0c2, 0x464e0931fc73, 0x61e6e70a9315, 0x499046bbd8ad, 0x334b09a1f7e0, 0x4bd5eb8e0311, 0x7b299e1ca560, 0x47de17209a8e,
    0x51b10839f774, 0x3e3aa127e423, 0x702b0e94a5d7, 0x4992dea1569c, 0x5b5276a11ba4, 0x222bd83d195e, 0xc8f3971f4d, 0x4d76839412af,
    0x3ea905382dd6, 0x165f1d39e260, 0x4f5317837a88, 0x24bb10adc95b, 0x272d50af6932, 0x7d74a52e1a81, 0x5884fc90ab8f, 0x25ddf38211b1,
    0x2e2b209d0f7c, 0x60d4a70f329b, 0x31180e3af57a, 0x40fdf0b21a59, 0x36a37bac4132, 0x75192a1cecf0, 0x39c7f1920e4c, 0x4861fe82acad,
    0x1adc719a2c8d, 0x69947e2268ec, 0x1767a8356427, 0x4f744f011a4f, 0x2b74b7045687, 0x19df58a5b43, 0x5988bf86c8ac]⟩
private theorem g0_47_ok : g0_47.OK L0 := gate_of_test (by decide +kernel)

private def g0_43 : Gate := ⟨43, 11, 0x35883a3ee53, #[
    0x10000, 0x65992aced98, 0x30e46d27c79, 0x2abc2f427a3, 0xbe59a41fd2, 0x726e60e5d62, 0x2247d988cbf, 0x6f84d5e4b0c,
    0x3c96418abd7, 0x67dd564c8a1, 0x4b422f493db, 0x72343866ff, 0x77be9c0c252, 0x7e3113c163b, 0x5393deb847, 0x2182f4cd53f,
    0x698a9ea4c67, 0x5485b02bfe9, 0x3311e92fa6a, 0x132ea3e8a9d, 0x68e7f18e305, 0x5de525a856a, 0x7baad42b494, 0x717418e31fc,
    0x4c972a2f8ae, 0xccacbe92f1, 0x12b2ffa81b4, 0x197cc64af2a, 0x185f95665e8, 0x4a1c43af793, 0x47fb8d07911, 0x5ee9486072f,
    0x4e1fecc3858, 0x2d3b7925e88, 0x3e70a264d57, 0x13dd7aa304d, 0x1f661a4f564, 0x245fa62337c, 0x64e8d74e0ce, 0x7d097f04b34,
    0x5558bc85e87, 0x70d3c7c96c4, 0x1a6336e6a93]⟩
private theorem g0_43_ok : g0_43.OK L0 := gate_of_test (by decide +kernel)

private def g0_31 : Gate := ⟨31, 11, 0x121d47b7, #[
    0x20000, 0x1693d6e1, 0x3582e99e, 0x1d0efd14, 0x70572f31, 0x278b3587, 0x406e2bf9, 0x5cc62e8e,
    0x49cad72a, 0x48bb2bac, 0x7027c69d, 0x5fbd245, 0x5f7a5222, 0x324b6e74, 0x381f137a, 0x18e664bd,
    0x693338cb, 0x7647c0e5, 0x73b69262, 0x2252f7d4, 0x125efd0a, 0x4b1f207b, 0x2ea6e893, 0x275a9c95,
    0xba319d7, 0x7ea3b019, 0xd668f2e, 0x67a75078, 0x45fb85c2, 0x4cba0d67, 0x3b5e4b48]⟩
private theorem g0_31_ok : g0_31.OK L0 := gate_of_test (by decide +kernel)

private def g0_23 : Gate := ⟨23, 12, 0x7acca1, #[
    0x8, 0x770cc5, 0x1f4f42, 0x4ad917, 0x4af744, 0x7c8a53, 0x7c3136, 0x2963e6,
    0x26b317, 0x5760f1, 0x5dd630, 0x4ba9e2, 0x6574a3, 0x1aee86, 0x41bac7, 0x335974,
    0x71a533, 0x230fb6, 0x144fe5, 0x3bd491, 0x26d4f4, 0x3cbe21, 0x4c3bd1]⟩
private theorem g0_23_ok : g0_23.OK L0 := gate_of_test (by decide +kernel)

private def g0_19 : Gate := ⟨19, 12, 0x4f50d, #[
    0x100, 0x65c4b, 0x37a92, 0x350cf, 0x564e3, 0x68a57, 0x3a8f2, 0x37e0c,
    0x43a76, 0x132ee, 0xee99, 0x2dcb8, 0x460fd, 0x49e2b, 0x7d4a2, 0x38e4d,
    0x5e615, 0x492bd, 0x7a474]⟩
private theorem g0_19_ok : g0_19.OK L0 := gate_of_test (by decide +kernel)

private def g0_11 : Gate := ⟨11, 13, 0x5c5, #[
    0x7ff, 0x781, 0x552, 0x496, 0x64c, 0x471, 0x638, 0x4c9,
    0x5a4, 0x52a, 0x607]⟩
private theorem g0_11_ok : g0_11.OK L0 := gate_of_test (by decide +kernel)

private def g0_7 : Gate := ⟨7, 13, 0x17, #[
    0x7f, 0x70, 0x29, 0x26, 0x26, 0x29, 0x70]⟩
private theorem g0_7_ok : g0_7.OK L0 := gate_of_test (by decide +kernel)

private def g0_3 : Gate := ⟨3, 15, 0x3, #[
    0x7, 0x2, 0x2]⟩
private theorem g0_3_ok : g0_3.OK L0 := gate_of_test (by decide +kernel)

private def g0_17 : Gate := ⟨17, 12, 0x1a317, #[
    0x1ffff, 0xf1ac, 0xb768, 0x22fd, 0x9b65, 0xcc7c, 0x12ba9, 0x1d781,
    0x19a59, 0x1a59c, 0x1ebc, 0x15d4c, 0x1e331, 0x6d95, 0x1f445, 0x16ed0,
    0x158f1]⟩
private theorem g0_17_ok : g0_17.OK L0 := gate_of_test (by decide +kernel)

private def g0_61 : Gate := ⟨61, 10, 0x8ec196bf5a60dc5, #[
    0x20000000, 0x9073f57b6f57e70, 0x1ffc9daa38e2adc9, 0x70e36daf637adb6, 0xedb72617f57f432, 0x13cf3cdab780f6ad, 0xcf3cf36ade03dab, 0x1b5dfbadaa4e392a,
    0x1d30a50cbfbcd9ef, 0xbdf861fbd17a2f4, 0x1f96ce7369fe1543, 0xafce09073f57b6f, 0x7f96ce7369fe154, 0x1cfcaacf3553f394, 0xf6b26ce7364d6f5, 0x917ee8ef7177e89,
    0x11c956d77eeb6a93, 0x1abfa193b6dc985f, 0x4a45fba3bdc5dfa, 0x10ee1f27770eee4f, 0x3b1b82df75aefb4, 0x1e729cfcaacf3553, 0x15471c55b93ffc9d, 0x1a2f45e8bdf861fb,
    0x1683b1b82df75aef, 0x190b8ee3a137f6fe, 0x1727c3b87c9ddc3b, 0x65fde6cf7f4c294, 0x11b6d7b1bd6db1c3, 0x19b26b7abdac9b39, 0x17f642e3b8e84dfd, 0xdfd90b8ee3a137f,
    0x1ce6c9adeaf6b26c, 0xe1c6db5ec6f5b6c, 0x14a197f79b3dfd3, 0xee1ddc9f0ee1f27, 0x1bfb7f642e3b8e84, 0xfbad77da0ec6e0b, 0x1efc30fde8bd17a2, 0xdc9ffe4ed51c715,
    0x1e55679aa9f9ca73, 0x16fbad77da0ec6e, 0xf93bb877727c3b8, 0x2fdd1dee2efd129, 0x1fd0c9db6e4c2fea, 0xe4ab6bbf75b549c, 0x148bf7477b8bbf44, 0x157b5936739b26b7,
    0x194e7e55679aa9f9, 0x1543fcb6739b4ff, 0x17b6f57e704839fa, 0x1e1543fcb6739b4f, 0x117a2f45efc30fde, 0x1fbcd9efe9852865, 0x1aa4e392adaefdd6, 0x16ade03dab679e79,
    0xdab780f6ad9e79e, 0x12617f57f43276db, 0x36daf637adb6387, 0x1c9daa38e2adc9ff, 0x1073f57b6f57e704]⟩
private theorem g0_61_ok : g0_61.OK L0 := gate_of_test (by decide +kernel)

private def filters0 : List Gate := [g0_29, g0_53, g0_37, g0_59, g0_47, g0_43, g0_31, g0_23, g0_19, g0_11, g0_7, g0_3, g0_17, g0_61]
private theorem gates0 (g : Gate) (h : g ∈ filters0) : g.OK L0 ∧ 512 ≤ g.p*2^vDepth g.p := by
  simp only [filters0, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨g0_29_ok, by decide +kernel⟩
  · exact ⟨g0_53_ok, by decide +kernel⟩
  · exact ⟨g0_37_ok, by decide +kernel⟩
  · exact ⟨g0_59_ok, by decide +kernel⟩
  · exact ⟨g0_47_ok, by decide +kernel⟩
  · exact ⟨g0_43_ok, by decide +kernel⟩
  · exact ⟨g0_31_ok, by decide +kernel⟩
  · exact ⟨g0_23_ok, by decide +kernel⟩
  · exact ⟨g0_19_ok, by decide +kernel⟩
  · exact ⟨g0_11_ok, by decide +kernel⟩
  · exact ⟨g0_7_ok, by decide +kernel⟩
  · exact ⟨g0_3_ok, by decide +kernel⟩
  · exact ⟨g0_17_ok, by decide +kernel⟩
  · exact ⟨g0_61_ok, by decide +kernel⟩

private def patch0_0 : Patch :=
  (.join (.join (.join (.join (.leaf 16 0x180a5100a01100020021 0x58d42c03103dc811c63dc613b20611f562bd5c5751ce21fd0b965eab1bbb8b957aee63ef5fda3e512bba2056d2bc6690635d4630cb7fca0666e00f8ab9f56a63) (.join (.leaf 16 0x8a0284650054001880 0x57444745cc6ab13473695e992854cdf99c0489c157074ac8085cab191510131e83885b174e4b39390b3452f39c497ef8709e62ca61b85c6151ce42a72d3e23bfacc78b795eea5d7b5551123fce4a378735622428) (.leaf 16 0x8082024602800810940 0x7f03bd1aa5544a1f35b63b831366ce2f938d76d95b31590d4f9e4e5f39391aebd4c262831fe7acf192e254163cbc1a50ac8f775a549253715093403f3b1620a48e09273a04ab0061cc5a903276d2473b43c24279345409c8096102a5))) (.join (.leaf 16 0x5000400c211940048048 0xa822a36b7d14539850624a69405d3d37243e20a48b484425242721307e5e7c6f52cf27aa145cce7d853c2fcbcda5a91f47f843ab2b2dbbacb3c76adc4ab43c0a2eb028f9093502ddc70c68d1c91ac540a1289cad4bcb323324b8080f) (.join (.leaf 16 0x10800800900c2212401 0xbb613dc938ac0f15a2828eb41a5c185b1298b5d288d484513ec13c7f3aac36c3161b0bc9c00ab422b1af199ecbb6c136b7e5726ab60183416e5a58e04052241323a21d211a8fd084) (.leaf 16 0x140010c025004b004a0 0xba76abc493a382843acc759a20a4310629db01094e520ca3cd4dbe0c977791e38cc6857572dd5fe74705048c1f001972c066bcb7b3b8a5e69aa4834f4bff47b734d9325b080f5aa3c87db5fbadc3304f0b92)))) (.join (.join (.leaf 16 0x466081210a42038c64 0xa015bd52af0c3271b808914828f0258d1cf30588c358d14cb082898a6f4444663f0c38642ccf2459745071476b55675e62b42b522b05296022f017200db1313990f28fb04a8e3d4d2367229500eb673f4dfe0dccaa9e6442015dcef7692a2d332874) (.join (.leaf 16 0x12c00400621008700422 0x8ad925ffb21a8fc56e105598497a3ccd36612a6f1a141657100bce4ac97abdcc52c351cb4a06293d0ee87186238f20b9ac2d1de751040b20bd8f4484277c167fc364b7d092598e7b3b3b2c5c246a21ba896b84a07d0e) (.leaf 16 0x180e0204621840608401 0x2f3e10ba035eb031a8439314844e2d7011310784798a46de28840205126ec877c1302dd9c0b29f10792e18fe09977a719c1f7251475d472c40f61641cf522a28a0fc))) (.join (.leaf 16 0x44400ce009420488a7 0x40e459bf2fb9533a112f0bfa06f5b3058a8e530e974189336bce429910c10c830b56825ab36c334e2c160d680ac88932ca90a09d960065ad5a4a35342ef62db60855a1f28e96bd46b3c597812f710013a7459e3f28b8131f0e9b0af50323) (.join (.leaf 16 0x1a020000470012108400 0x81fa79a50cc4c48bb963af29a654a0877b57556b23a7401b4795230bcae5b4a69c3b86d22d9b250b135acee3baeea88e91226c546b0b3a4637fb2d6c4ae366d00322) (.leaf 16 0xe4184000102200801 0xb315a2769ebe26021c600a7505fdbce39aa54d980b35905556f2543d543ab89c80d17b7c5b8a7363cd12ab3696585ba23241))))) (.join (.join (.join (.leaf 16 0x424600e00242510443 0x782b43036c4764595b0532d4b089ac4ea98da4e99b0e8f9e7c6f48882f59282717dd14e6a446827877134fcd437a3e892705bdb6b781b4fd764858983d6a35da2ab910374c0368a4641b598654e2319921540f175e218b30598067f13dae0b88) (.join (.leaf 16 0x10000200240006009c01 0xb461239ea5fd72ba540e1fb8c01fc5b6b82d82f84b2ab75c6beb580d7552a8b1a022793e74251e6913b506657e3d) (.leaf 16 0x10cc01840698020084c4 0xd30f38e64e58406c37a5cfc67d88758a53404dcf15bcd27fd1836aa51ea5bd04ba4fb29352300c1300acce80c16cb85aaeec70bb6f935de15dd7445c406d3c8933bd215f183516d0163113910b0a09b62bf67366a873a595a202a0a999b990b18aa89edd8fb98ad02e30))) (.join (.leaf 16 0x2040a088800142020880 0x7dd86cc064d63312ab4fd190c524b52771bd636240cd33ea28910f37025f4429a96c15d0b03d77e945fb0a70b1f83b23393329a923766289d461a82a91bc2129a52278a9a54c6358314b2515) (.join (.leaf 16 0x4010800a0814000040 0x87f98a7f1b03cddb8dce7a3f6a14496e245723f5178916301500a9f3d18cbb99b1c883d177034aef4aab36682bdc0049ad5c144a) (.leaf 16 0x3080019c400080008142 0xa369a13533432e6f216d1e1fbdca5f4a43ff360d057dbbc5b4dab2c69e39895e731c649e55a852d288b123591546cf35bb62b24fa9a78c0871153a01385f079e0387d3bd4d44)))) (.join (.join (.leaf 16 0x28c03004c00180119003 0xc6cf985c8c137b6c59b79a517c543a0c9fae6c083786a801cc1da0686f0c5e7a3d2c0ae4c19d77c060f74a3115340005b2c98012615d5800ce4ac49fa9a23076d21ba00a66b8) (.join (.leaf 16 0x5002320826000e512000 0xcda5c250a62d89f589b68992468d3aa5214f004f3a87cd8a84101765c7d8c16d79060882491b0004094cb1a88c80882a52b23c1131ecb4fb998f94cd7f0f60b5511e4697b4d6aab99c885f9e3bb940931411c55ac41fa8039dee6d39615453561acf) (.leaf 16 0x104001206218c02000c0 0x928665b013a2d3306f07b7e194e07e366e456bb312d40a2905938c802c7a0a457eca2b63b435a48c92438ecc8950633d3c422e94c214678b4ee8274a232e1176))) (.join (.leaf 16 0x214681880020000188a5 0xa57b5edf49b028df99fa999188e756561480759a3b1d32d48c4b85e08058780a505240732d720a56d49b6cc45146bf5c15d3c70c9bdd72c45f65c77b5bc50470811c24c7d372c4dec4279c732671ce13b91aa341a264a1ba) (.join (.leaf 16 0xc5288002870310062 0xd2b5b5399e50929b903a29cec7c0973f8c954cb10b4aad05a7947fcc615613317c6319ea7c5a75eb52124c7b29fe110ed44ed429d30ac991ac00a1699d979a8391ca85c8786b72ae6db2472d457440ab3fca3bd5389027ad1e461e0f1c761038c24d4ce140f62eab2902626e5d1c3fe28e9c2644) (.leaf 8 0x11401000a0 0xcec1258cb647604c43813f283e173e11a77292e22383209b094c))))))
set_option maxRecDepth 4000 in
private theorem scan0_0 : Region (clearPoint L0) 0 376 :=
  checkedPatch 0 patch0_0 gates0 (by decide +kernel) (by decide +kernel)
private theorem rows0 : Region (clearPoint L0) 0 376 :=
  scan0_0
private theorem clear0 : Clear L0 := clear_of_scan (by decide +kernel) (rows0)

private def L1 : Chart := ⟨4721, 1907040398, -73304, -93025, 728801, -510534, 15614, 2095⟩

private def g1_13 : Gate := ⟨13, 12, 0x9e5, #[
    0x1fff, 0x109, 0x1024, 0xa80, 0x608, 0xe00, 0x111, 0x884,
    0x70, 0x1060, 0x150, 0x409, 0x1084]⟩
private theorem g1_13_ok : g1_13.OK L1 := gate_of_test (by decide +kernel)

private def g1_29 : Gate := ⟨29, 11, 0x13d122f3, #[
    0x1fffffff, 0x8cc6090, 0x701602c, 0x1407a012, 0x8b14a80, 0x472213, 0x35cc800, 0x708404e,
    0x10112466, 0xb228106, 0x35a4048, 0x92886c, 0x15050688, 0x7010638, 0x4a90a81, 0x902a12a,
    0x1838c101, 0xa22c141, 0x6c2292, 0x102404b5, 0x14c10289, 0x2cc4910, 0x18e40421, 0x10002675,
    0x19089c4, 0x402a51a, 0xa900bc0, 0x18680d01, 0x4120c66]⟩
private theorem g1_29_ok : g1_29.OK L1 := gate_of_test (by decide +kernel)

private def g1_5 : Gate := ⟨5, 13, 0x13, #[
    0x1f, 0x8, 0x4, 0x2, 0x1]⟩
private theorem g1_5_ok : g1_5.OK L1 := gate_of_test (by decide +kernel)

private def g1_59 : Gate := ⟨59, 10, 0x22b62183e7b92bb, #[
    0x7ffffffffffffff, 0x41c9c6db6426d39, 0x187ca71ed3c50e8, 0x76e04cc2677a9c4, 0x743305e8d51e41f, 0x41eb1f383b70358, 0x2a8c96b421ada7e, 0x819d54ac2e6ff2,
    0x43e82457babcc46, 0x4074af6bd459896, 0x3b405f63d0815be, 0x63068d6abdca4b8, 0x1cb2cd3bec23225, 0x6807ae0d66b03cf, 0x787ceeee1916011, 0x5d85aed80b694c3,
    0x1aa1a4246dd17bb, 0x6ceb6e25e0496d, 0x669395c739d444a, 0x5d2576d6be88222, 0x677cfa97e689, 0x364716546432ef6, 0x259834cf91b17c5, 0x7625c4c1d8e93e1,
    0x491e1c49735f962, 0x18b79c719507bc8, 0xf511fa0bee7051, 0xe3a2e9948b9b3c, 0x563d151717aa50e, 0x2b45b599668b654, 0x2cd335b45a8a9b4, 0x3d1d15178d5c295,
    0x22532e8b8e0f367, 0x6fa0bf115e22839, 0x1531c73da304f78, 0x59d2470f1251a7e, 0x637064748de1f25, 0x313e658334a8fa3, 0x4c54d1c4d9bdd3, 0x52be7dcc002459f,
    0x2fad6dd49751104, 0x739c75392cd488a, 0xf48edae6c2da48, 0x76c484b0ab377a2, 0x5a036eb43770ca5, 0x130eeee7c3e201a, 0x2cd60ebc02fcf03, 0x6fb9669a729131,
    0x77aad62c18c7494, 0x2178df405b9f6a0, 0x457adea5c05a466, 0x2bbd4482f8588cf, 0x686a55730213fd9, 0x3085ad262a9f96d, 0x5b839f1af046b03, 0x1562f41985fe09e,
    0x5cc86640edc8e57, 0x796f1ca7c305c28, 0x4db6c7270672d9]⟩
private theorem g1_59_ok : g1_59.OK L1 := gate_of_test (by decide +kernel)

private def g1_47 : Gate := ⟨47, 10, 0x4351b2753df, #[
    0x7fffffffffff, 0x2e0c37e21579, 0x6d772b006c47, 0x6cd888339f34, 0x13ea288f9e86, 0x3a7739d40cc1, 0x320b6978f561, 0x5da43170d5c5,
    0x129097fa7712, 0xfc29721f499, 0x5076e60a9e96, 0x33ef88d8340e, 0x1067d21566cf, 0x5f0c66336f8, 0x426de8b64c56, 0x730d2836e627,
    0x65d5d325c560, 0x1e3d54983695, 0x6d612afd4630, 0xe2994cea78e, 0x2788911adf3a, 0x790a0b57947a, 0x1a96d2ab6ea0, 0x22305d27be1e,
    0x4ba0c44f0fbc, 0x54b69580aeda, 0x2d0509ebc53d, 0x8911e4b9f6b, 0x3299470e3cae, 0x75486b618c57, 0x12abc7952d83, 0x4cbaba60d474,
    0x414b0cfc8ced, 0x517b642d464d, 0x6630fa03ed98, 0x4be609e6cd5, 0x311f7cce0583, 0x676e0ad2f2a, 0x4e943f1325f0, 0x7e9094891dcb,
    0x68c25bb47561, 0x696d04d0d5e3, 0x39cee5d06605, 0x11457c8c2f3e, 0x4111b3659f39, 0xd4eeb7c46c0, 0x7ec30753d508]⟩
private theorem g1_47_ok : g1_47.OK L1 := gate_of_test (by decide +kernel)

private def g1_43 : Gate := ⟨43, 10, 0x4a77c5c11ad, #[
    0x20, 0x2c54f4986be, 0x5865a11b27f, 0x4f81a7e2875, 0x5594a3c31ee, 0x243732af83b, 0x4faf56201ec, 0x7d758fb0320,
    0x53b91691ae6, 0x282f0e4b7b6, 0x16632af152f, 0x5296df2c472, 0x4b075445fb3, 0xeaa85adaf1, 0x2bf79153960, 0x63faccc043d,
    0x5b30d4f63a1, 0x19cdb94c0bb, 0x7a4c22cff28, 0x75468c2e4e7, 0x763bc1c8d26, 0x260d92774f9, 0x3b926c194f9, 0x44e0f71bb25,
    0x1d0c58abf39, 0x7cd10c978a7, 0xca76ce66e8, 0x1bcac336c2e, 0xccd7f1de1, 0x72a27bf5034, 0x6d68555c47a, 0x688ab834e6f,
    0xd3eda52a71, 0x23d5319a7a5, 0x349c3d0536f, 0x625a2772b3a, 0x37c6baf826, 0x11abd7c9bc, 0x7d533b096e0, 0x30f14a6abbc,
    0x51f9607cd70, 0x36216986ff2, 0x64bca8d3eb]⟩
private theorem g1_43_ok : g1_43.OK L1 := gate_of_test (by decide +kernel)

private def g1_31 : Gate := ⟨31, 10, 0x121d47b7, #[
    0x200000, 0x457de948, 0xceb8ba3, 0x7166b0e9, 0x17b23e07, 0xd679974, 0x9f1a778, 0x1aea6e89,
    0x7a28743b, 0x73325e98, 0xcf4ea0f, 0x5caa4e56, 0x5efd0a24, 0x25a4f5b8, 0x73a324b6, 0x476033fa,
    0x603715fc, 0x262e76d2, 0x792d21da, 0x5fbd245, 0x12a9d6a7, 0x39798f05, 0x52667197, 0x70a2fdc2,
    0x32bac917, 0x2c7c81ee, 0x4f3582e9, 0x626f4e07, 0x6b347970, 0xeb98c5d, 0x3df51129]⟩
private theorem g1_31_ok : g1_31.OK L1 := gate_of_test (by decide +kernel)

private def g1_23 : Gate := ⟨23, 11, 0x5335f, #[
    0x100000, 0x5748b5, 0x13798e, 0x35595c, 0x1a53f4, 0x7076a3, 0x599b94, 0x748acb,
    0x3ee990, 0x1dd187, 0x72217b, 0x79a4e1, 0x3e1c96, 0x1f7a11, 0x73862e, 0x78265d,
    0x5f4d44, 0x34a766, 0x1f15b8, 0x30bf29, 0x58ea6a, 0x11c67b, 0x56b44b]⟩
private theorem g1_23_ok : g1_23.OK L1 := gate_of_test (by decide +kernel)

private def g1_19 : Gate := ⟨19, 11, 0x30af3, #[
    0x7ffff, 0x4d3b, 0x74f2, 0x2391b, 0x57a60, 0x7560c, 0x1ed3, 0x451f4,
    0x36a8c, 0x22b4e, 0x2272d, 0x36315, 0x512f8, 0x40cb7, 0x57306, 0x75065,
    0x62d89, 0x704f2, 0x10dcb]⟩
private theorem g1_19_ok : g1_19.OK L1 := gate_of_test (by decide +kernel)

private def g1_11 : Gate := ⟨11, 12, 0x5c5, #[
    0x20, 0x5b4, 0x639, 0x2ad, 0x7e, 0x333, 0x666, 0x3f0,
    0x5aa, 0x4e3, 0x16d]⟩
private theorem g1_11_ok : g1_11.OK L1 := gate_of_test (by decide +kernel)

private def g1_7 : Gate := ⟨7, 13, 0x69, #[
    0x10, 0x2d, 0x4d, 0x63, 0xf, 0x66, 0x6a]⟩
private theorem g1_7_ok : g1_7.OK L1 := gate_of_test (by decide +kernel)

private def g1_37 : Gate := ⟨37, 10, 0x9a1dee165, #[
    0x1fffffffff, 0x17dc0e9703, 0x1ceb9f8007, 0x145b5b4599, 0x1fc2a22a1f, 0x121eb39af, 0xd909b69cb, 0x7c6498f95,
    0xeaec42375, 0xc71b15ea3, 0x50d614ef7, 0x144f2a7917, 0x79e49524f, 0x1ac35c3761, 0x1ead5e193, 0x1b2570ea4d,
    0x12a627b791, 0xb6eda8661, 0x391fc4e2d, 0xd1c8fe271, 0x19856ddb5, 0x27b791953, 0xc95c3a937, 0x1261ead5e1,
    0x1bb0eb0d7, 0x1c92a49e79, 0x1a27953c8b, 0x1bdca1ac29, 0x115ea3638d, 0xbb108dd5d, 0xa7c6498f9, 0x14e5b6426d,
    0x1d6735e121, 0x1e151150ff, 0x668b6b68b, 0x18007e75cf, 0x103a5c0efb]⟩
private theorem g1_37_ok : g1_37.OK L1 := gate_of_test (by decide +kernel)

private def g1_3 : Gate := ⟨3, 14, 0x5, #[
    0x7, 0x2, 0x1]⟩
private theorem g1_3_ok : g1_3.OK L1 := gate_of_test (by decide +kernel)

private def g1_61 : Gate := ⟨61, 9, 0x8ec196bf5a60dc5, #[
    0x800000000000000, 0x839fabdb7abf382, 0x1c55b93ffc9daa38, 0x18db6bd8deb6d8e1, 0x1f43276db930bfab, 0x19b56f01ed5b3cf3, 0xd5b3cf3cdab780f, 0xdaa4e392adaefdd,
    0x1fa614a197f79b3d, 0x1e8bd17a2f7e187e, 0x196ce7369fe1543f, 0x1d5edbd5f9c120e7, 0xb6739b4ff0aa1fe, 0x1e729cfcaacf3553, 0x1b39cd935bd5ed64, 0x8948bf7477b8bbf,
    0xefdd6d5271c956d, 0x1eafe864edb72617, 0x1bdc5dfa2522fdd1, 0x1dc3e4eee1ddc9f0, 0xd77da0ec6e0b7dd, 0x9cfcaacf3553f39, 0x1f276a8e38ab727f, 0xf45efc30fde8bd1,
    0x1df683b1b82df75a, 0xe84dfdbfb2171dc, 0x1b93e1dc3e4eee1d, 0xfe9852865fde6cf, 0xdb5ec6f5b6c70e3, 0xc9b39cd935bd5ed, 0x85c771d09bfb7f6, 0x9bfb7f642e3b8e8,
    0x1adeaf6b26ce7364, 0x1b1c38db6bd8deb6, 0x1bcd9efe9852865f, 0xee1ddc9f0ee1f27, 0x18ee3a137f6fec85, 0x1d6bbed0763705be, 0x1a2f45efc30fde8b, 0x1ff93b5471c55b93,
    0xa73f2ab3cd54fce, 0x1aefb41d8dc16fba, 0x1c3e4eee1ddc9f0e, 0xe2efd12917ee8ef, 0x1fa193b6dc985fd5, 0x1adaa4e392adaefd, 0xbf7477b8bbf44a4, 0xc9adeaf6b26ce73,
    0x1f2ab3cd54fce539, 0x9fe1543fcb6739b, 0x1f9c120e7eaf6dea, 0xff0aa1fe5b39cda, 0x1df861fbd17a2f45, 0x1ef367bfa614a197, 0x1aefdd6d5271c956, 0x1bc07b56cf3cf36a,
    0xf3cf36ade03dab6, 0x1f57f43276db930b, 0xe1c6db5ec6f5b6c, 0x1c7156e4fff276a8, 0x9073f57b6f57e70]⟩
private theorem g1_61_ok : g1_61.OK L1 := gate_of_test (by decide +kernel)

private def filters1 : List Gate := [g1_13, g1_29, g1_5, g1_59, g1_47, g1_43, g1_31, g1_23, g1_19, g1_11, g1_7, g1_37, g1_3, g1_61]
private theorem gates1 (g : Gate) (h : g ∈ filters1) : g.OK L1 ∧ 512 ≤ g.p*2^vDepth g.p := by
  simp only [filters1, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨g1_13_ok, by decide +kernel⟩
  · exact ⟨g1_29_ok, by decide +kernel⟩
  · exact ⟨g1_5_ok, by decide +kernel⟩
  · exact ⟨g1_59_ok, by decide +kernel⟩
  · exact ⟨g1_47_ok, by decide +kernel⟩
  · exact ⟨g1_43_ok, by decide +kernel⟩
  · exact ⟨g1_31_ok, by decide +kernel⟩
  · exact ⟨g1_23_ok, by decide +kernel⟩
  · exact ⟨g1_19_ok, by decide +kernel⟩
  · exact ⟨g1_11_ok, by decide +kernel⟩
  · exact ⟨g1_7_ok, by decide +kernel⟩
  · exact ⟨g1_37_ok, by decide +kernel⟩
  · exact ⟨g1_3_ok, by decide +kernel⟩
  · exact ⟨g1_61_ok, by decide +kernel⟩

private def patch1_0 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x10020000000044000001 0x47d322c833eb0af3666905793cfe) (.leaf 16 0xc00008400000008020 0x52a851f908922ad80e8b50022851146e535e)) (.join (.leaf 16 0x60000032842000800 0x5d7d3090279773d50fc10cb568295b2c30d92ecc21c550f17645778369be) (.leaf 16 0x3004200840110800 0x685266f4069f639d2ece24cd12cf18b2616553af630613a4))) (.join (.join (.leaf 16 0x14022002000000080e0 0x795a419724b4209a068c64e4011b760a73273d923282493f451c73e9499e2b980f9f0d260b160753) (.leaf 16 0x8000008000800100402 0x368d242212304bb609650f2570ef3699)) (.join (.leaf 16 0x10400080000840100000 0x315e0acb0c9c38c44c1e6a603aed) (.leaf 16 0x8060000020004100c00 0x511f6edf468f0f5a2ac91201188f126864e978d72ee5209e)))) (.join (.join (.join (.leaf 16 0x20000002840002000 0x64da70d4383417b4137e022b4d3a61bd563e53774edf29ad265f1a3202bf) (.leaf 16 0x8003000000100000420 0x267a46300c6a0436755d3e2628061b7355806c1c)) (.join (.leaf 16 0x420084400002000001 0x5a6e3a62126e4d7978a050aa11983034) (.leaf 16 0xc00000600000300040 0x640f34c9301c701a647d3dd4430b0f250b4672a3500c))) (.join (.join (.leaf 16 0x400000210804088000 0x5b3e555838dc464b50074e8162de62995d874f7b438842c740353e1c29db26cc1ef50dbd0c4f0a8308cc05690045) (.leaf 16 0xc20180000040000000 0x4b5725be0e213ca861c143080924348a)) (.join (.leaf 16 0x4008c0000004080e0 0x5d1315fb50804ac9093d05af628f2cd920cc043e3b3a6e7d5eec59433eba313f1d8a011b) (.leaf 16 0x20400008201040008004 0x453c23770e630cd265405d1350200cf878347645677d586229cf1894081b0079))))) (.join (.join (.join (.join (.leaf 16 0x8c01080000004600000 0x1de64ed3a0f336a5d765f7a692610c56f7e69f060c024ab165c0fc0) (.leaf 16 0x120080000000008000 0x797f62795d435a4457a8544e53f829ab03b778f136e4)) (.join (.leaf 16 0x10003000001800100420 0x4e9945343f4e36cb130e6fc44a5034f06e0253cd3d54) (.leaf 16 0x400000010002008001 0xff64f626a5e76726c9d))) (.join (.join (.leaf 16 0x18040080000806000042 0x65940c1e087f1a1e0dad025661376a8760af170e305026693933236a) (.leaf 16 0x28002004000080108400 0x69675efe43473c2b304677de31bb37c64e8b12b35df46f726456)) (.join (.leaf 16 0x30002020c40 0x509d4918065f068d722b62325cfe2089631a18830d8976440984) (.leaf 16 0x23000602002001020 0x79613f332c94233a4d2831da14d959b1581b3fe208922fef42673eaa34e10b534533)))) (.join (.join (.join (.leaf 16 0x4000880003c0000000 0x4f984ea563106004738972a161f853fb4a124890436c3f3a2cfd1b9f16b8109a034d030b00ec) (.leaf 16 0x18001080000006000423 0xebc09520439797e5a763e8530092ea06db22970359b34ba1d05)) (.join (.leaf 16 0x21000000802100002 0x70992c1636a274e33e2b38d93807) (.leaf 16 0x42008000080050000 0xa0c04a859b00e7e3c5218a37595491272646f206587600f4c9c46fe43a418000c2b05c1))) (.join (.join (.leaf 16 0x8000000030842000c00 0x4bf11cb4186d049a56dc397617ee758840762580) (.leaf 16 0x60180000882308000 0x723a60883cfc530e47e61cc92d12640230cf75d06d89589445251efc)) (.join (.leaf 16 0x8860000200082100062 0xcb205eb00876ea12a9a1a143bf173c635eb73560073676934ab268c2f1f16a0) (.leaf 16 0x1401100400800200000 0x6e6f4d7a2993254d09f05c3b7802432d4c87270a5de4634232a9))))))
set_option maxRecDepth 4000 in
private theorem scan1_0 : Region (clearPoint L1) 0 512 :=
  checkedPatch 0 patch1_0 gates1 (by decide +kernel) (by decide +kernel)
private def patch1_512 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x20000040800008020 0x410a58bd30af132d0c58352a139e6217) (.leaf 16 0x4000001002008020 0x4f2537202df329d627dc00670de976281a95)) (.join (.leaf 16 0x480000040000400 0x79b13f80376c3607296920ee15460f7602de30ca5d2d) (.leaf 16 0x20024200002000001 0x266c778a72526b9e6af26aef68b3245f165813f5089d0706103b))) (.join (.join (.leaf 16 0x11000002400000200420 0x7619718757a250bb4cd12ce2747566546606653b5d01509c4e974e594d9d48f446a343c240583c7f39d62959123d039576156a9c3daa3013) (.leaf 16 0x800000040002000000 0x60344d6a5a9d419e3e8f309858e5)) (.join (.leaf 16 0x4001800010022 0x53353f2f227e1e4d417630c33cf04cf5424b) (.leaf 16 0x8000080200000000026 0x35163e762f9a6cd3664963b561c62c291c9d057d)))) (.join (.join (.join (.leaf 16 0x10400008000000000802 0x8ad01ab6adb50010bb523a20fd4356809d6) (.leaf 16 0x40008202840000020 0x5f5538e0680950ad0fe743a43bfc368e27ed27071c774f1c)) (.join (.leaf 16 0x22000200000020000 0x4ff360180c8f37b24232250c214519c1) (.leaf 16 0x1002000220000100020 0x665f49903b58238e707b2e8752ff2678256f328e5f28))) (.join (.join (.leaf 16 0x8010000000801000e0 0x61bd07db4db52a9f0414187577846aec55f741b03cea03af015d) (.leaf 16 0x6000006 0x617737c809c6643c55323cc7380d09c90371)) (.join (.leaf 16 0x1020008000000400800 0x76647617733842c61f683f0f22e04ac747d040562cc44d684c41) (.leaf 16 0x80a0008050000019021 0x294c55b83bef2ddb095506183f59072d79bd416831091c2a09763b1c194a173d5d5235e326b6052341296579))))) (.join (.join (.join (.join (.leaf 16 0x1800c000000000000021 0x52d12388021379c36fc96af85eab5e855726542249da4176366b1cfc1be94e8e64a1) (.leaf 16 0x8001184000040000420 0x2e96232383927c222fc5f37604c559909b1)) (.join (.leaf 16 0x94000000000423 0x5ff865b3400c34312314204215e21d5e39d52e382c76) (.leaf 16 0x400000400080100000 0x69e1435a2ab077ee1fa12341))) (.join (.join (.leaf 16 0x4a0000010000008023 0x304664ad3beb272a23a61f323f58073035a334b433100895) (.leaf 16 0x4012800100c20 0x6f911b2e31fc2a9f26b60c6c03051d176bb353b919d53dea)) (.join (.leaf 16 0x8002000400180008020 0x38bd552612e138be123062d95c3a50fe4a4a3a752c1b3e002ff2) (.leaf 16 0x8021004020012308000 0x613f0e7f1afb25dd76622ae5687564f44d40327a283824d419b20d440a716e733ba617611708)))) (.join (.join (.join (.leaf 16 0x441080200000500001 0x70ba71cf55a035ee136c1fe95b3f48db43ee2a650e021845) (.leaf 16 0x8440000200800000000 0x5a8e5ae46b0b412c186d4597)) (.join (.leaf 16 0x802000020084000000 0x545d1d26273124a0742a4d4c3ba100fa47910e70) (.leaf 16 0x400084000940000040 0x201d67cc3cfa287b691e52ce39f913f5084f5fbf1b78))) (.join (.join (.leaf 16 0x78001004000000118803 0x72ca71985db059eb53f24d114af6448242943e153da4365823f00fc00e952ed8223f4baf609623a116f42c58101a6d55319d2140) (.leaf 16 0x8401082000400 0x46ad18366f495d4074285853601f14114ea03ae4)) (.join (.leaf 16 0x18000000010002108000 0x4cbf453f33ba28545a4355496b7f) (.leaf 16 0x24000000080000c01 0x1f395df648b316280d9c78c3495c5c10570f11161375))))))
set_option maxRecDepth 4000 in
private theorem scan1_512 : Region (clearPoint L1) 512 1024 :=
  checkedPatch 512 patch1_512 gates1 (by decide +kernel) (by decide +kernel)
private def patch1_1024 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x400000000040000401 0x2d56784971a55fd7) (.leaf 16 0x10080004000842200004 0x719137f877074fd93a8516d645163acc737142f74cd11b357773747c2460111f)) (.join (.leaf 16 0x400008200000000000 0x12ba68771c2d5940) (.leaf 16 0x100080006000400 0x59b133c877db614c577541d331421ee816ae045175821920023c694b))) (.join (.join (.leaf 16 0x462000202802000000 0x51f167eb55f81cc32643249621ea794b71086e145b300f43476e) (.leaf 16 0x100000000002440100a0 0x1d7415d14d39420231da30152f10275924a715d404de659a1d6a559d1ab54aa43b50371e22f30478)) (.join (.leaf 16 0x10000584020048000000 0x342a12526d7c53464e5a3abe21731fbb1b921642123712320efe05af73dd08b70c5b4cd745aa16e10243) (.leaf 16 0x20004000800400020 0x3d220fda391378db439d0bc006e7033b)))) (.join (.join (.join (.leaf 16 0x20000010042100400 0x160306d516b348c33e562328) (.leaf 16 0x26100201000004000 0x2977246647863195ca41fab1cc6497a393a0e801a9a0fba70e76c97643a60305fb45f3b5e3c54ea532950484a8643b23c0036ae15b40cfb)) (.join (.leaf 16 0x1004000800008061 0x2c3174cc52f16afb71f3377627055db1) (.leaf 16 0x30801080000802008026 0x5b9c41933dc816ae161f11e41fef06095dd62aba53fe4d91025462f5783c463e40203b2526d52432))) (.join (.join (.leaf 16 0x10200800008c0000402 0x5f234160356507fe2f2b0741072c70ff45ee24883ce25cec4798) (.leaf 16 0x40000000000160020 0x69d84a01696c67085c4f4a61391e35042f9a2c2e2c192aed1bf90a7a058b3a35)) (.join (.leaf 16 0x22000200800000004 0x2416675940854a856d7e439f308f2e191b54) (.leaf 16 0x420100210086000400 0x2d2e2dfc663446d200b579473fee148370993aed29ea2236))))) (.join (.join (.join (.join (.leaf 16 0x8020000000002210001 0x42d85e8947ce36d30a4622a70c902dd2) (.leaf 16 0x1400000310000 0x6db96bd85caa5afe57b1570750f0393937562e5a630424d3222164231bc1)) (.join (.leaf 16 0x9840004000000000421 0x4e5e4a4a3afa3433301e12dc111078c962ee3f45613a615924d3) (.leaf 16 0x10021008000000100400 0x501f211257ab3a35433b34c2645c038b))) (.join (.join (.leaf 16 0x8000080000102000420 0x508c44d647662e530d1a058c40dd63452fd1) (.leaf 16 0x800008c01000e010400 0x1e7c67c362e85f191e75698d6ac4657d537f51174e7e44d000e463162c893266)) (.join (.leaf 16 0x8020080410004000000 0x60c69d71b37790e2ee6281e622346c6) (.leaf 16 0x424000210000008402 0x64e913695622557339b20a1e6ca52010400569000ff20de0)))) (.join (.join (.join (.leaf 16 0x100002100200a000 0x1840656b3a414f144ca10d3a3a006ef058354a9d4a1f4662410d3cd61871) (.leaf 16 0x8000004210800000100 0x6b942f5d01325e6c3cf86d3f615f5db6552150dc47fa2342146f)) (.join (.leaf 16 0x10000010000004028007 0x61602e1b390135e332922b393eac0a1d6c6259393fee240505dd6e116d665ff53c90361b331c1361) (.leaf 16 0x80600002008400 0x39d778a073e12dac15c5037f27c5))) (.join (.join (.leaf 16 0x802001c051000228000 0x2ece085057af4675353132f7179f171d0d95589052a243ae1c8a10f3517c05d25dd25b84716d661236332a2114b8) (.leaf 16 0x10003004000000208000 0x43ea3f307343488e1dff01d2412008c2007b)) (.join (.leaf 16 0x20200000040400800 0x21bd6b99660c42af221a393a514b3b9d2ec8106e4554011b) (.leaf 16 0x8420010010800100045 0x5ffd159a67446e723ae01eb802bd259f341e41b44f8b2b5045d2446142c928472514))))))
set_option maxRecDepth 4000 in
private theorem scan1_1024 : Region (clearPoint L1) 1024 1536 :=
  checkedPatch 1024 patch1_1024 gates1 (by decide +kernel) (by decide +kernel)
private def patch1_1536 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x80000000000400 0x3aa4601e) (.leaf 16 0x8000800b0004008000 0x68a40a126447714e6b466601584957ad56b645ee2fd81be318111617796f258246a8)) (.join (.leaf 16 0x1080200800100400 0x52174ff65afc49226e346bef) (.leaf 16 0x200000002001020000a0 0x4dcb437b267003933fa83374128608fa061530a264ba5e3f4a740aff050e))) (.join (.join (.leaf 16 0x18400000001006000005 0x67ae256916b1009b64c53b3a3dd530902ef9706936ac2a071f721bee) (.leaf 16 0x420000c00000800000 0x78cd13426d116aa761fb4eb4431d277e73735b39431a2b640fdd0de3092a0386)) (.join (.leaf 16 0x1000210000010000 0x24404b309845bf05266) (.leaf 16 0x801000000002018800 0x3e73057f67ff205e4fdb10480b5c49b61862)))) (.join (.join (.join (.leaf 16 0x100000002108502 0x4ed02f4742b82b8f067e2e4878555e814484352b2c4828191930023f2c6a2922) (.leaf 16 0x100020a0200082000401 0x319a07ea7915238e796b765174ad560b3ad8148311560a4e0166482b18c70819198f092141b2)) (.join (.leaf 16 0x11400000010000200c20 0x57c431bd326b301926fa1840106e1aa96a7419dd3ed63bb12ed7465c) (.leaf 16 0x20080200000000020 0x4a4a34bd62dc1721))) (.join (.join (.leaf 16 0x8080000080008800 0x64fe579637ec36871b381887127f04af140a49c53f02163d6c5122e6) (.leaf 16 0x8401a80020000000400 0x27a6347c600777d8769971c9710f6edb6b5860e05c6b59ed514a4ff5487e470c3b8138df33861b4b11620778020f01126d4e52f5347e)) (.join (.leaf 16 0x2c020002000020 0x7835734b6c775d825a7327f621691372111f0caa0b7f682f3a4e40456acf) (.leaf 16 0x400004200002208001 0x44c7060776b0544516570ebc29db18cc))))) (.join (.join (.join (.join (.leaf 16 0x80080060004000000 0x577548604158199b6366798054b84ade41b117cc019b79241434) (.leaf 16 0x1008010000008420 0x20256e426d112ede33cf02d43aed)) (.join (.leaf 16 0x400180a00000008002 0x4e306b0447f447d3698d58534a662784184d3cd46ce34ce5) (.leaf 16 0x401010000008000000 0x781e78ca6be5580b455a146d660755ad43910940))) (.join (.join (.leaf 16 0x1004400000000040 0x3a4452244d3d48c93d5b2bea) (.leaf 16 0x82c1000050002010002 0x108d72ca6f4c6cfa68d1635e5c59540d4dd4495d38382d402aa328ab273d260b1ea61a9b145f116b0979054a04216bbc584711640ed90c420ad71e1b4b7210545d9a0a7f)) (.join (.leaf 16 0x8805084010000000400 0x204a266d13f8689e480736f415bb02dd14d225d1692b2875) (.leaf 16 0x8021000001040100060 0x67c52546033c737637083fe13cf66da1416604fc)))) (.join (.join (.join (.leaf 16 0x4210882100005 0xf1940f15a6038652d850a4412481bb2734b72213809263c0582) (.leaf 16 0x4c00000610800100820 0x76d876076ae65e3b5d24598158ee58cb4c06482a424b3fcd3f2c3e4a2fb2287f25231c3b0ae26f882272012420b26ab907802b7b215d03f9)) (.join (.leaf 16 0x460008000000100000 0x73a8732e6137607e60420cff38ca) (.leaf 16 0x8000000000802108400 0x3a942a283c42505c73580c6f))) (.join (.join (.leaf 16 0x40000401004c000840 0x780b77886d94733956f450f04fdd3e8039f829ae75155ebd4b481b51) (.leaf 16 0xc000000010c0000002 0x5c804d802a7637b130a44fd14e4b133b180f13aa)) (.join (.leaf 16 0x8003000600800108000 0xc6f55ba396d1d394c9a44a109c63f587120701c) (.leaf 16 0x84010000108000 0x2d1a017454683e1f4630))))))
set_option maxRecDepth 4000 in
private theorem scan1_1536 : Region (clearPoint L1) 1536 2048 :=
  checkedPatch 1536 patch1_1536 gates1 (by decide +kernel) (by decide +kernel)
private def patch1_2048 : Patch :=
  (.join (.leaf 16 0x2042000000 0x75dd5aba4cae0bd0267f2a9a) (.join (.leaf 16 0x2100200800008420 0x45771dae3dc52c671c6710b177df50a3049c) (.leaf 16 0x400004010000008404 0x389a48f05ca427074f852845242b186d0bc2)))
set_option maxRecDepth 4000 in
private theorem scan1_2048 : Region (clearPoint L1) 2048 2096 :=
  checkedPatch 2048 patch1_2048 gates1 (by decide +kernel) (by decide +kernel)
private theorem rows1 : Region (clearPoint L1) 0 2096 :=
  (mergeRegion (mergeRegion scan1_0 scan1_512) (mergeRegion scan1_1024 (mergeRegion scan1_1536 scan1_2048)))
private theorem clear1 : Clear L1 := clear_of_scan (by decide +kernel) (rows1)

private def L2 : Chart := ⟨9881, 59642966760, 331619, 877023, -941616, 418867, 1869, 1660⟩

private def g2_5 : Gate := ⟨5, 10, 0x13, #[
    0x10, 0x9, 0x6, 0x6, 0x9]⟩
private theorem g2_5_ok : g2_5.OK L2 := gate_of_test (by decide +kernel)

private def g2_53 : Gate := ⟨53, 7, 0xd228fccfc512d, #[
    0x4000, 0x11214fa0525780, 0x1510206490665f, 0x1240c301e4d546, 0x8fae3242050d0, 0x8f4713200651a, 0x1c0a25d2414e44, 0x103ad0a8ee00d,
    0x1c90481aa8ce81, 0x21a5a9446e114, 0x4b6180aa252e4, 0x2ac2a08d27903, 0xd4c3a400cc1d2, 0x64695a0c0d305, 0x429912151f88a, 0xaa0265808c8de,
    0x5bb19214359, 0x18105b010c5e17, 0x118c40c079d22c, 0xd544a3dc40d0, 0xa091318b2c439, 0x8694e7a2cc01, 0x100381cc9a558c, 0x443dc78305032,
    0x18c20a234b40ad, 0x981309097d624, 0x51883c203cc36, 0xf04628d867808, 0x43206448d7d21, 0x11410c76a05a58, 0x18ef0889814183, 0xe070026354b26,
    0x1ca584100668bc, 0x32241538469a3, 0x148aac01604778, 0xc08c6268973c0, 0x368207d0f4610, 0x3768013585093, 0x990154f626203, 0x1226508a23f150,
    0x16a58994196060, 0x970cac9706600, 0x150d51813c962, 0x61b484e948aa, 0x569610510ec45, 0x4824f02e62ab, 0x2d7021600ee2a, 0xe9140e44e5049,
    0x1238bc4b14c009, 0x131d7c41614084, 0x30c092c5564f0, 0x181022bf4cc124, 0x17ca12203d4940]⟩
private theorem g2_53_ok : g2_53.OK L2 := gate_of_test (by decide +kernel)

private def g2_61 : Gate := ⟨61, 6, 0x1713e6940a59f23b, #[
    0x8000000000, 0x1868142b3561449f, 0x462418df5e236c, 0x1e7d2428ab46251, 0x1d09214794a2ab23, 0x65e4792a4b861a, 0xea7092448c09dcb, 0x1f088448c3caae0b,
    0x31913612bd7308c, 0x1550783026f08d2e, 0x13f8252ad3088961, 0xb2b012e47b68f00, 0xa10d65c3165c4e1, 0x8af6842985e3a82, 0x1191352091f55aa4, 0x17238116d8942e2c,
    0x7434a381608dab6, 0x18d4966f7010602e, 0x3a944b151939ba, 0x832a23975a83887, 0x1018324d88f25f54, 0x4b3935d3841f404, 0xf101748a8247ace, 0x1b70ac0d488c6d11,
    0x4f62c37a04e4238, 0x6dc707618da911, 0x1f29d13009868467, 0x1e7eca0a70832281, 0x64e7319049216ba, 0x51ec4d962c027b, 0xe8117033cb3d0c2, 0x69e607440b90c2f,
    0x1a34d91bc5037900, 0x4904c67393175a1, 0x872829bf3e0513, 0x10c80645ca7f9885, 0x18c37071db022256, 0x1902f61a37907109, 0x1889581a876e22d8, 0x120a89740479cd78,
    0x10e5d64e69080be, 0x788d9260c04abe9, 0xad74e22a60b8470, 0xc546914ae017672, 0x4077b34958dd018, 0x8340e296171b56c, 0x148db440e274d1d0, 0x17c4825644c4956a,
    0x1d0ca10b7a890571, 0x13461d35842a1c8e, 0x16f13a406a6803c5, 0x865aa520fe61a44, 0x7b2060f0555d2c4, 0x15ea43644c60c433, 0x9e18910887f41d5, 0x189124872bb4ee4,
    0x92a4f13d3016187, 0x294f142485f1355, 0x16a8a125f3c22918, 0x1d7d8c123100db11, 0x3566a140b0fe48a]⟩
private theorem g2_61_ok : g2_61.OK L2 := gate_of_test (by decide +kernel)

private def g2_59 : Gate := ⟨59, 6, 0x22b62183e7b92bb, #[
    0x7ffffffffffffff, 0x4beb688f4f6e100, 0x4e7b448405718ff, 0x2916caa47366d9c, 0x5ed1a12eaba0a93, 0x7477a9ab481d252, 0x1b4f2ce4e909d25, 0x559949b7a45a272,
    0x32146230c7e6ecf, 0x6ced4a3c62e1629, 0x51fcc61cc67b242, 0x54b1c7576a8015f, 0x570ed874987ce3, 0x5b24eff3809a4c4, 0x1cb3061ed376638, 0x7970a293ba8a9f0,
    0x3b0b6a687a8f095, 0x26ec2427a91f9a9, 0x6f118e4275a9e0e, 0x6b9402f586f7511, 0x5fa78348172703e, 0x174622a3b8f44f6, 0x701501d9bbf364c, 0x2905ea589a37e59,
    0x700fed3e03d1263, 0xc8b0eab474d8ee, 0x61a74d7d58768a0, 0x670c47bc489ef44, 0x5ada0b42b547b0d, 0x12ee0cc81d9adf8, 0x702660ee907ed66, 0x5a85a0b6b6c378a,
    0x247bc461cc8bde4, 0x357d65cb0c145b8, 0x45aae1a261dc6cb, 0xf96fe01f1922f, 0x3234af412a69fb1, 0x3b3701501cc9b3f, 0x3b8a88c5d1bc8bc, 0x502583cbf5f0393,
    0x435e8053ae22bbd, 0x5c84e311edc1e56, 0x2bc8486eca567e2, 0x3c2cada1baa43c5, 0x3b928a1d3c3e545, 0x16f0c19a70719bb, 0x39fee49b48c964, 0x25c36e1d431cf86,
    0x2dd5c71a57ea005, 0x4670c67f1509379, 0xc78a56e6e51a1d, 0x46188c509bcdd9f, 0x4bdb25335539168, 0x2e4e69e5b292e42, 0x25ab2bdc5d292e0, 0x2ae90b16f725417,
    0x1c4aa6d128e6d9b, 0x404245bce7fc63a, 0x65e22dafa4021db]⟩
private theorem g2_59_ok : g2_59.OK L2 := gate_of_test (by decide +kernel)

private def g2_47 : Gate := ⟨47, 7, 0x7bcae4d8ac21, #[
    0x7fffffffffff, 0x24e762e7e284, 0x2fe17340c5c3, 0x3ec07d97c08c, 0x57c09bd0798a, 0x470d563da1d2, 0x6f80035794bb, 0x1aafc2e18578,
    0x55aa0e167732, 0x3c08b497b6d1, 0x5a251b996257, 0x43c424e6db59, 0x7e08822a7b9b, 0x34adb11add24, 0x4e45ddaa4568, 0x494f639c50da,
    0x34ece82d6233, 0x156312e1b94f, 0x2a2ca6d90cbb, 0x73030dc9a3b6, 0x48e1309cfe3c, 0x73e6c9b42438, 0x778b28cb0f41, 0x68ea0ddd5941,
    0x60ae2e0a6aee, 0x29a3de0bc34c, 0x26cf9c7090b6, 0x190e24f1fce4, 0x61819db7164e, 0x4a68ab74c26d, 0x118d53ca761d, 0x2e6e5b311ad0,
    0xde5256c28e7, 0x7744e45a8956, 0x1b6a5892ed62, 0x220ff677951, 0x4847866b6d9c, 0x3148b7a91a67, 0x5a207a2db7a4, 0x60ab5533b9a1,
    0x7eab07a861d, 0x3ef74a7ab, 0x5561c52e16f1, 0x3207d546782f, 0x7c06f8c40fa6, 0x1d0feb0e8c0b, 0xdce48851f9d]⟩
private theorem g2_47_ok : g2_47.OK L2 := gate_of_test (by decide +kernel)

private def g2_43 : Gate := ⟨43, 7, 0x4a77c5c11ad, #[
    0x7ffffffffff, 0x6b3352dc42c, 0x53386d9f0b, 0x14712877337, 0x2d423c5361f, 0x5e2a26be483, 0x292ce83717a, 0x15a5bac246e,
    0x240ff89b271, 0x4a8e80deb4e, 0x46043e6fd49, 0x3be89e84331, 0x58fe608d358, 0x36a340a7bb2, 0x11e7e4722c9, 0x42e95830d7d,
    0x75fd48c3450, 0x4772ce0839e, 0x7cc2a259dc4, 0x6bb42c80f27, 0x18875e16d55, 0x62ba2e752c2, 0x68695ce8ba8, 0x1556d0f5c23,
    0x7c9e02685ba, 0x6477348a867, 0x2f3820e69dc, 0x614586257f5, 0x37d618352e8, 0x12689c4fcf1, 0x49bbca058ad, 0x2359620cfe3,
    0x519842f22fb, 0x3257ecf840c, 0x2e5af602e2a, 0x51c9b23fe04, 0xec486bb4b5, 0x4bd1d82e692, 0x3824fac8a8f, 0x5f0d9478856,
    0x1d99dc291c5, 0x1a1f36c3994, 0x6684769599a]⟩
private theorem g2_43_ok : g2_43.OK L2 := gate_of_test (by decide +kernel)

private def g2_31 : Gate := ⟨31, 7, 0x6de2b849, #[
    0x7fffffff, 0x5a6acd3, 0x4b62396c, 0x2ab1f02d, 0x1612e59e, 0x66cec183, 0x14eec447, 0x4b9c579,
    0x572b1ca1, 0x5d7c6882, 0x2b7c14f0, 0x5fe599, 0x2f69185c, 0x62556476, 0x70e818cf, 0x2d1325ec,
    0x22d1bd26, 0x5c3f98c0, 0x291b7135, 0x5bd1d0c4, 0x6804cd3f, 0x7b507941, 0x7aea08b1, 0x53ac29c6,
    0x7484f51c, 0x5ca7111b, 0x4d9e0c1b, 0x21a3cd3a, 0x3555a07c, 0x1b49b4e2, 0x168659ab]⟩
private theorem g2_31_ok : g2_31.OK L2 := gate_of_test (by decide +kernel)

private def g2_23 : Gate := ⟨23, 8, 0x7acca1, #[
    0x7fffff, 0x64338e, 0x3cb581, 0x1ad332, 0x166f82, 0x377a10, 0x4c1e36, 0x3a231e,
    0x595da0, 0x41d48f, 0x5538ac, 0x3b4529, 0x2dd294, 0x4aa6a3, 0x383e25, 0x29a0b7,
    0x45cf18, 0x32d8f, 0x6ec10b, 0x66883e, 0x358999, 0x53d035, 0x426e39]⟩
private theorem g2_23_ok : g2_23.OK L2 := gate_of_test (by decide +kernel)

private def g2_19 : Gate := ⟨19, 8, 0x30af3, #[
    0x7ffff, 0x56ba, 0x6688e, 0x3638a, 0x5c585, 0x3a8d8, 0x44bc5, 0x612bc,
    0x136d4, 0x4e7c0, 0x481f3, 0x215b6, 0x19ea4, 0xd1e9, 0x70d8a, 0x6d0d1,
    0x328e3, 0x1b88b, 0x2eb5]⟩
private theorem g2_19_ok : g2_19.OK L2 := gate_of_test (by decide +kernel)

private def g2_11 : Gate := ⟨11, 9, 0x23b, #[
    0x400, 0x6b1, 0x713, 0x4ce, 0x74a, 0x4f4, 0x4bc, 0x54b,
    0x5cc, 0x723, 0x635]⟩
private theorem g2_11_ok : g2_11.OK L2 := gate_of_test (by decide +kernel)

private def g2_7 : Gate := ⟨7, 10, 0x17, #[
    0x7f, 0x38, 0x4a, 0x26, 0x64, 0x52, 0x1c]⟩
private theorem g2_7_ok : g2_7.OK L2 := gate_of_test (by decide +kernel)

private def g2_37 : Gate := ⟨37, 7, 0x9a1dee165, #[
    0x1fffffffff, 0xb6b68b334, 0x1cb6c84db4, 0xc57a8d8e3, 0x79e49524f, 0x1526ec95c3, 0x3f89c5a39, 0x1313dbc8ca,
    0x1ac35c3761, 0x1dca1ac29d, 0x7ca9f1926, 0x22a1ffe15, 0x181d2e077d, 0x1f9d73f, 0x1eb39af09, 0x1ababb108d,
    0x14f22f44f2, 0xf56af0c98, 0x19856ddb50, 0x56ddb50cc, 0xc987ab578, 0x7917a2795, 0x18846eaeae, 0x87ace6bc2,
    0x1e75cfc003, 0x1f703a5c0e, 0x143ffc2a22, 0x124c7ca9f1, 0x1ca1ac29de, 0x3761d61ae, 0x989ede465, 0xe2d1c8fe2,
    0x1d49bb257, 0x1925493cf3, 0x38d8af51b, 0x16d909b69c, 0x16668b6b68]⟩
private theorem g2_37_ok : g2_37.OK L2 := gate_of_test (by decide +kernel)

private def g2_3 : Gate := ⟨3, 11, 0x5, #[
    0x1, 0x6, 0x6]⟩
private theorem g2_3_ok : g2_3.OK L2 := gate_of_test (by decide +kernel)

private def g2_17 : Gate := ⟨17, 8, 0x1a317, #[
    0x1ffff, 0x8c5f, 0x62fa, 0xe92e, 0xbe8c, 0x4b9d, 0x5ce9, 0xe749,
    0xc5f4, 0x2fa3, 0x92e7, 0x973a, 0xb9d2, 0x317d, 0x7497, 0x5f46,
    0xfa31]⟩
private theorem g2_17_ok : g2_17.OK L2 := gate_of_test (by decide +kernel)

private def filters2 : List Gate := [g2_5, g2_53, g2_61, g2_59, g2_47, g2_43, g2_31, g2_23, g2_19, g2_11, g2_7, g2_37, g2_3, g2_17]
private theorem gates2 (g : Gate) (h : g ∈ filters2) : g.OK L2 ∧ 512 ≤ g.p*2^vDepth g.p := by
  simp only [filters2, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨g2_5_ok, by decide +kernel⟩
  · exact ⟨g2_53_ok, by decide +kernel⟩
  · exact ⟨g2_61_ok, by decide +kernel⟩
  · exact ⟨g2_59_ok, by decide +kernel⟩
  · exact ⟨g2_47_ok, by decide +kernel⟩
  · exact ⟨g2_43_ok, by decide +kernel⟩
  · exact ⟨g2_31_ok, by decide +kernel⟩
  · exact ⟨g2_23_ok, by decide +kernel⟩
  · exact ⟨g2_19_ok, by decide +kernel⟩
  · exact ⟨g2_11_ok, by decide +kernel⟩
  · exact ⟨g2_7_ok, by decide +kernel⟩
  · exact ⟨g2_37_ok, by decide +kernel⟩
  · exact ⟨g2_3_ok, by decide +kernel⟩
  · exact ⟨g2_17_ok, by decide +kernel⟩

private def patch2_0 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x400000000800000001 0xbc50989074d) (.leaf 16 0x802000020 0x3440e0100f7)) (.join (.leaf 16 0x4000400 0x1f000e80cf8) (.leaf 16 0x0 0x0))) (.join (.join (.leaf 16 0x200800100000 0x7720398013c) (.leaf 16 0x21080000040000000 0x2460e7a01a90b90)) (.join (.leaf 16 0x0 0x0) (.leaf 16 0x840000000 0xc5606be)))) (.join (.join (.join (.leaf 16 0x400000000002008000 0xb3c0d30085f) (.leaf 16 0x401 0x7970828)) (.join (.leaf 16 0x40000000 0xa4e) (.leaf 16 0x0 0x0))) (.join (.join (.leaf 16 0x80000000000000 0x65b) (.leaf 16 0x80000000000000 0x7bc)) (.join (.leaf 16 0x401000000000000000 0x638062f) (.leaf 16 0x0 0x0))))) (.join (.join (.join (.join (.leaf 16 0x40008000 0x9710b54) (.leaf 16 0x8000000000002000400 0x9580ae701cc)) (.join (.leaf 16 0x60000000002108021 0xda50d8705c8099d07e1072908b10903) (.leaf 16 0x8000 0xd31))) (.join (.join (.leaf 16 0x1000000000000000 0xd4f) (.leaf 16 0x0 0x0)) (.join (.leaf 16 0x20000000000000400 0x80605a0) (.leaf 16 0x200000000021 0xba109bd0466)))) (.join (.join (.join (.leaf 16 0x202000000000 0xa830cf109400208010c) (.leaf 16 0x60000000080200020 0xad309cb08ef0b2005690da20d0c0d57)) (.join (.leaf 16 0x0 0x0) (.leaf 16 0x40000021 0x82b0d1c09de))) (.join (.join (.leaf 16 0x20000000000000000 0x526) (.leaf 16 0x2000010000000000 0x52300c80511)) (.join (.leaf 16 0x0 0x0) (.leaf 16 0x8000000000000008000 0x8500b45))))))
set_option maxRecDepth 4000 in
private theorem scan2_0 : Region (clearPoint L2) 0 512 :=
  checkedPatch 0 patch2_0 gates2 (by decide +kernel) (by decide +kernel)
private def patch2_512 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x10001000000800000000 0xe3e054d0b9502b2) (.leaf 16 0x0 0x0)) (.join (.leaf 16 0x4000000000000 0xe81) (.leaf 16 0x400000000000000000 0xb63))) (.join (.join (.leaf 16 0x400004010040000401 0x4820bed087507050a150ab9) (.leaf 16 0x4000000000021 0x4430c950c68)) (.join (.leaf 16 0x400000000000000020 0xe7a0477) (.leaf 16 0x0 0x0)))) (.join (.join (.join (.leaf 16 0x8000000000040008000 0xca7091002a4) (.leaf 16 0x1000000040000020 0xb920994089a)) (.join (.leaf 16 0x0 0x0) (.leaf 16 0x0 0x0))) (.join (.join (.leaf 16 0x4400802100000 0x40e0da8040706720d5703f3) (.leaf 16 0x4000000000001 0x8bf0b94)) (.join (.leaf 16 0x20000000800000401 0xc490da90c2d017f) (.leaf 16 0x401000000000100000 0xc3a00c800e4))))) (.join (.join (.join (.join (.leaf 16 0x400004000000000000 0xb330d4e) (.leaf 16 0x4000800100400 0x3b607c106aa0db9)) (.join (.leaf 16 0x1000000040008000 0x3850e4a08e4) (.leaf 16 0x18000000000020 0xe590c490a91083c064a036408c6))) (.join (.join (.leaf 16 0x8000000000000000020 0xb78007f) (.leaf 16 0x20000000000008000 0xd6e0d48)) (.join (.leaf 16 0x8001000200000108001 0xe3d090906e106c40b790c6f) (.leaf 16 0x8020000001040000000 0x4550d5e087208170562)))) (.join (.join (.join (.leaf 16 0x4000800000000 0xf002be) (.leaf 16 0x4000000000000 0x2ff)) (.join (.leaf 16 0x8000000000000008000 0x5fc0107) (.leaf 16 0x10002008001 0x2f9092e04e402d5))) (.join (.join (.leaf 16 0x0 0x0) (.leaf 16 0x800000020 0xbfb0191)) (.join (.leaf 16 0x1080000000000000 0x92e0a6a) (.leaf 16 0x400000000800000001 0x95302930d4a))))))
set_option maxRecDepth 4000 in
private theorem scan2_512 : Region (clearPoint L2) 512 1024 :=
  checkedPatch 512 patch2_512 gates2 (by decide +kernel) (by decide +kernel)
private def patch2_1024 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x0 0x0) (.leaf 16 0x400000000000000420 0x34d077207dd)) (.join (.leaf 16 0x40000000 0x246) (.leaf 16 0x80400000000000 0x5700e8d0db4))) (.join (.join (.leaf 16 0x80000800000000 0x3230978) (.leaf 16 0x20000000000100000 0x84e0c46)) (.join (.leaf 16 0x4000000000000 0xa5e) (.leaf 16 0x2000000 0x23f)))) (.join (.join (.join (.leaf 16 0x1000000000100001 0x6bd0cdd0e25) (.leaf 16 0x1000000002000001 0x1b70d26099d)) (.join (.leaf 16 0x80000040000000 0x85101e4) (.leaf 16 0x200000 0x18e0139))) (.join (.join (.leaf 16 0x400 0x1a1) (.leaf 16 0x8000000210800000000 0xdfd09c20a360c33)) (.join (.leaf 16 0x4000000000000 0xc0e) (.leaf 16 0x800000000 0xe1a))))) (.join (.join (.join (.join (.leaf 16 0x1000000000000000 0xad3) (.leaf 16 0x400 0x128)) (.join (.leaf 16 0x1000200000000400 0xbdb086b09e7) (.leaf 16 0x100000002100000 0x18b00df0c73045c))) (.join (.join (.leaf 16 0x40000010000000000 0xe2608590506) (.leaf 16 0x0 0x0)) (.join (.leaf 16 0x80000800000000 0xa0c00d8) (.leaf 16 0x8400000000000000000 0xaec0a5a)))) (.join (.join (.join (.leaf 16 0x420004010000000000 0x59700af0b3c0099) (.leaf 16 0x200000100400 0x7400cf00c1)) (.join (.leaf 16 0x8000000001002000001 0x6990c4f0b9c0e410a68) (.leaf 16 0x8020000000040100000 0x9ce018408440a31))) (.join (.join (.leaf 16 0x100200000000000 0xbe103c20cc4) (.leaf 16 0x2000000 0xb24)) (.join (.leaf 16 0x200000000040 0x1a078e03d3) (.leaf 16 0x420080000000000000 0xa0a560265))))))
set_option maxRecDepth 4000 in
private theorem scan2_1024 : Region (clearPoint L2) 1024 1536 :=
  checkedPatch 1024 patch2_1024 gates2 (by decide +kernel) (by decide +kernel)
private def patch2_1536 : Patch :=
  (.join (.join (.join (.leaf 16 0x1004000000000000 0x2dc063e) (.leaf 16 0x20 0x542)) (.join (.leaf 16 0x420000010000000000 0x835014d0607) (.leaf 16 0x100000 0x1f))) (.join (.join (.leaf 16 0x8000000000040008000 0x7160a7b0a42) (.leaf 16 0x8000000010000000000 0xb020adc)) (.join (.leaf 16 0x400 0xa3f) (.leaf 13 0x300020 0xdd5092b05470c76))))
set_option maxRecDepth 4000 in
private theorem scan2_1536 : Region (clearPoint L2) 1536 1661 :=
  checkedPatch 1536 patch2_1536 gates2 (by decide +kernel) (by decide +kernel)
private theorem rows2 : Region (clearPoint L2) 0 1661 :=
  (mergeRegion (mergeRegion scan2_0 scan2_512) (mergeRegion scan2_1024 scan2_1536))
private theorem clear2 : Clear L2 := clear_of_scan (by decide +kernel) (rows2)

private def L3 : Chart := ⟨9881, 60171849717, 872885, -450698, 787632, 698533, 2042, 1818⟩

private def g3_5 : Gate := ⟨5, 10, 0x13, #[
    0x1f, 0x8, 0x10, 0x1, 0x2]⟩
private theorem g3_5_ok : g3_5.OK L3 := gate_of_test (by decide +kernel)

private def g3_53 : Gate := ⟨53, 7, 0xd228fccfc512d, #[
    0x10000000, 0x48992c9f0561, 0x4363847041d70, 0x1f2100aa70b112, 0x2f62b0158038a, 0x59216c5ac9408, 0x1a02064cebd204, 0x15d00a8f244918,
    0x4ed088133e8a, 0x967a86280e91, 0x23145811ce586, 0x184dcc051a6444, 0x2094125a74457, 0x4920acc03b8d4, 0x864685d8e981, 0x184e2f08c160c2,
    0xfb8848c00187a, 0xaab1422070969, 0x1fcc60340648a, 0x1d888c86299214, 0x19239428121785, 0xa8aa962e902c0, 0x1d252021b01c69, 0x18214a601f442d,
    0x1120326b164171, 0x59518047832f, 0xa84e7250820d6, 0x16082149ce42a6, 0x983c40315340f, 0x1d04d1ac980918, 0x845f00ca5083b, 0xc701b08094979,
    0x6812e8d2aa2a0, 0x3d0902853893a, 0x109328c2622372, 0x24c0580c67f05, 0xd21c08851aaa9, 0x1c300062423be5, 0x60d0621e8e434, 0x32e3742c4c208,
    0x163b8066a09242, 0x1445cb4905208e, 0x44cb140676432, 0x34e7103451886, 0x12e028c2bcd208, 0x2f9902216e405, 0x112449e2a01751, 0x97ae64c080b2,
    0x526b46d09341, 0x3803501a8de85, 0x111a1caa0109f4, 0x1d7041c438d840, 0xd41f269322408]⟩
private theorem g3_53_ok : g3_53.OK L3 := gate_of_test (by decide +kernel)

private def g3_61 : Gate := ⟨61, 7, 0x1713e6940a59f23b, #[
    0x20000000, 0x135c50a3ac8694b, 0x14c912652a63c654, 0x1002a730aeea19ca, 0x1834b1986634b06a, 0x1ca2451229e89e45, 0x1e9784662a2a331, 0xa49638a6651c692,
    0xd0a1e44f0a16c93, 0x1064009839f319f3, 0x1dc1831761ba306, 0x87d6563535f080, 0xe0585a1a0773067, 0x160440d9a0bfd059, 0x103e4324b1a4984f, 0x1485439270a84bab,
    0x1ef0c187bc423108, 0x142865371547653, 0x1435f056a0fac28, 0x6f2d0a169ec4422, 0xe05281ca8f45e2a, 0xc19aa07631b8156, 0x1da0c8a028982dde, 0x194e3fc729812240,
    0x58a341f3500acf8, 0x13be0132289900fb, 0x11029b4b65022eae, 0x84c8990ada4c96d, 0x16830d7680b7586, 0x1601d4ff2b80685, 0x106f4c65ec122644, 0x9132241bd3197b0,
    0x50b00ea7f95c034, 0x30d7680b75860b4, 0x15b4992da84c8990, 0xbaba2053696ca04, 0xef804c8a26403ee, 0xf9a80567c1628d, 0x1812240ca71fe394, 0x1bdda0c8a028982d,
    0x13540ec63702acc1, 0x12a3d178a9c0a503, 0x22111bcb4285a7b, 0xa1af82b507d614, 0x653715476530a14, 0x18846211ef0c187b, 0xeae90a8724e1509, 0xf90c92c692613e0,
    0xcd05fe82cd81103, 0x173067702c2d0d03, 0x87d6563535f08, 0x3062ec37460c1dc, 0xe7cc67ce0c80130, 0x1649b4287913c285, 0x124b1c53328e3492, 0x4662a2a3310f4bc,
    0x1d13c8bca2451229, 0x1ab0696330cc6960, 0xa9cc2bba8672a00, 0x9531e32a5324499, 0x694b09ae2851d64]⟩
private theorem g3_61_ok : g3_61.OK L3 := gate_of_test (by decide +kernel)

private def g3_59 : Gate := ⟨59, 7, 0x22b62183e7b92bb, #[
    0x1000000000, 0x29e26a86714fe5a, 0x6bee4ca349d2b9, 0x4caa38726dfc079, 0x5edc327a4c0798e, 0x23bb7cca1c8a0f6, 0x6e8540bf0e1e59d, 0x2396f40fb8d1ac9,
    0x50af0e17e63ada2, 0x5a9fa4de941847c, 0x473552f8e481f8e, 0x100ba6feb4ea726, 0x1bb08a4fdf8adc0, 0x6f2a6cb119b4971, 0x1c5f32825dc5e87, 0x57b35035661a537,
    0x7f22de2137741c8, 0x6b20aca97b932e9, 0x5f4490fbd669982, 0x5d5b907ccf67090, 0x111bae57e256b0e, 0x3c9570812f4f3b9, 0x6764bc75f465105, 0x3dcd54a1a49a1b7,
    0x262ce905579fde, 0x73a4ce9c6c20e9e, 0x6c9658ed0b8be1c, 0x6b80c2f5166a6b7, 0x558fa640ac3b537, 0x59bb682319e14f5, 0xf31882dbb36bca, 0x386a04cbe357b2b,
    0x2cd15e8603afb59, 0x23a16e34d26ce1f, 0x86c72e64b9de5c, 0x3d5412e68c81efe, 0x324b0a55677bb61, 0x4c5f5c7a4dce822, 0x65e9021d527a773, 0x548fd4ebb111c35,
    0x4de67c13b574243, 0x2cd7be1245f5066, 0x13bd2a6a09ae5d3, 0x5dd908f689fc4e0, 0x30cd58159bd7b29, 0x47748299f47385e, 0x5b311a6ca9ee3a4, 0x23f7e4a21bb00ed,
    0x2e5afecba011939, 0x24e3e9559c5c7e, 0x3052f64bf2b4f88, 0x38cfd0e1ea1516d, 0x163be05ed38a4d6, 0x70e1fa0542eee69, 0x2270a67dbb89bc1, 0x4064bc9876f5c67,
    0x7f6c9c38aa66780, 0x7258a64efac2752, 0x651cc2ac8f2969f]⟩
private theorem g3_59_ok : g3_59.OK L3 := gate_of_test (by decide +kernel)

private def g3_47 : Gate := ⟨47, 7, 0x7bcae4d8ac21, #[
    0x200000, 0x6f1c15921d3d, 0x441dcf4d701f, 0x477ce81f6a24, 0xa87fd8388bd, 0x50b9cad5262f, 0x12b2410bf9f7, 0x2d5d2b94e32a,
    0x2bbfce046e03, 0x30e5825dba57, 0x5a9377988c74, 0x2e0633cb4cf9, 0x25d45c126efa, 0x618b524fb317, 0x1c333a4d93b5, 0x188b195d59f6,
    0x7a82b444d4f7, 0x53898bc8d3d5, 0x1a4474da8f6b, 0x70d28f4933e5, 0x68fceb1e4612, 0x71a3ea1d7189, 0x617d2ec76883, 0x2e6d64904fdc,
    0x51df904935b3, 0x1e08b71ba5f4, 0x3c8c75c2be2c, 0x5a4313c6b9f8, 0x3d3e64978a58, 0x66b78ad97112, 0x2d5e589e8c8e, 0x7f7959116a0a,
    0x637cd5d4c688, 0x656e4d92e661, 0x1f466f92568c, 0x12fbb241d15d, 0x54f9969e6303, 0x697188cf764a, 0x3752edd20d38, 0x5603b1039fee,
    0x52a6394ea5d5, 0x277cfe84126a, 0x2fa3255a9ce8, 0x45e88e0dff0a, 0x922b7c0b9f7, 0xfc075979dc1, 0x5de5c24d41c7]⟩
private theorem g3_47_ok : g3_47.OK L3 := gate_of_test (by decide +kernel)

private def g3_43 : Gate := ⟨43, 7, 0x4a77c5c11ad, #[
    0x7ffffffffff, 0x145d143f0fc, 0x29d5c813ab9, 0x528614b2fe9, 0x19bd244497b, 0xb77dda3003, 0x5f518d32c62, 0x650bf429b26,
    0x2cd71c1c1c7, 0x30cd7598666, 0xaa8bca653d, 0x2dd581abb44, 0x40f03997d33, 0x60f3c479e0c, 0x36bad94330a, 0x5b14d86ca36,
    0xfc0fc45ad1, 0x7d2a9494aa5, 0x78dad8f0a50, 0x7f882d6b411, 0x6437ec264e4, 0x6f67381039c, 0x1ce040e737b, 0x139321bf613,
    0x4416b5a08ff, 0x52878dad8f, 0x52a9494aa5f, 0x45ad11f81f8, 0x3629b0d946d, 0x286614daeb6, 0x183cf11e783, 0x665f4ce0781,
    0x116eac0d5da, 0x5e5329e8aa8, 0x3330cd75986, 0x71c1c1c759a, 0x326ca17e853, 0x231a658c57d, 0x60062ddf768, 0x6f491125ecc,
    0x4bfa69430a5, 0x4eae409d5ca, 0x1f87e145d14]⟩
private theorem g3_43_ok : g3_43.OK L3 := gate_of_test (by decide +kernel)

private def g3_31 : Gate := ⟨31, 8, 0x6de2b849, #[
    0x8000000, 0x52d50fb1, 0x25de7234, 0x62b095f3, 0x526a7b83, 0x42932ebe, 0x119df05d, 0x57a63b0a,
    0x74d688d6, 0x24f0abe6, 0x45cc75e4, 0x6560d2fc, 0x70293f3a, 0x319287fa, 0x76f886c4, 0x32b3ccf0,
    0x260f33cd, 0x3723611f, 0x465fe149, 0x75cfc94, 0x533f4b06, 0x5127ae33, 0x1267d50f, 0x176b116b,
    0x7550dc65, 0x44ba0fb9, 0x217d74c9, 0x25c1de56, 0x23cfa90d, 0x522c4e7b, 0x258df0ab]⟩
private theorem g3_31_ok : g3_31.OK L3 := gate_of_test (by decide +kernel)

private def g3_23 : Gate := ⟨23, 8, 0x7acca1, #[
    0x40000, 0x133e5c, 0x436b55, 0x5bd02b, 0x236739, 0xb39f2, 0x51dce8, 0x609b7a,
    0x21ed27, 0x28b6c7, 0x3be1d0, 0x6a4e8e, 0x4adc5c, 0x7b82e1, 0x22b8db, 0x70b92d,
    0x20d7b6, 0x7145ce, 0x1a13e7, 0x58a739, 0x7b7502, 0x586ab5, 0x190e9f]⟩
private theorem g3_23_ok : g3_23.OK L3 := gate_of_test (by decide +kernel)

private def g3_19 : Gate := ⟨19, 8, 0x30af3, #[
    0x7ffff, 0x30b71, 0x426da, 0x1ea43, 0x71b28, 0x2b5d, 0x2361d, 0x139f,
    0x1a3d2, 0x8b37, 0x76688, 0x25e2c, 0x7ce40, 0x5c362, 0x5d6a0, 0xa6c7,
    0x612bc, 0x2db21, 0x47686]⟩
private theorem g3_19_ok : g3_19.OK L3 := gate_of_test (by decide +kernel)

private def g3_11 : Gate := ⟨11, 9, 0x23b, #[
    0x7ff, 0x686, 0x1c5, 0xad, 0x3b0, 0x4d1, 0x598, 0x6e0,
    0x28b, 0x1ca, 0xb6]⟩
private theorem g3_11_ok : g3_11.OK L3 := gate_of_test (by decide +kernel)

private def g3_7 : Gate := ⟨7, 10, 0x17, #[
    0x20, 0x55, 0x4d, 0x1e, 0x47, 0x1b, 0x5a]⟩
private theorem g3_7_ok : g3_7.OK L3 := gate_of_test (by decide +kernel)

private def g3_37 : Gate := ⟨37, 7, 0x9a1dee165, #[
    0x1fffffffff, 0x1c3b30575a, 0x1b15227e72, 0x1b55737610, 0x91c7ab93a, 0x1ba1c6507e, 0xa1e7b3913, 0x1093ede865,
    0x1b8c9a970b, 0xe1a73bb05, 0x153c76403f, 0x26a1daf2d, 0xbce4a9743, 0xeb338437a, 0xcf2ac907d, 0x193476893b,
    0x13dcd62f04, 0xc9efe855, 0xe4fca9e41, 0x153f27413c, 0x1f7930550b, 0x6b3bc907a, 0x16e2c9ee48, 0x1354f35f04,
    0x1ccd72f61, 0x15273d6174, 0x1b85645a7a, 0x6e3cafe01, 0x1ce587506e, 0x15931de874, 0x1b7c90d30b, 0xde785644e,
    0x6385dbf05, 0x15e3892e4e, 0xceaad8437, 0x44a8da73f, 0xcdc3ad75]⟩
private theorem g3_37_ok : g3_37.OK L3 := gate_of_test (by decide +kernel)

private def g3_3 : Gate := ⟨3, 11, 0x5, #[
    0x7, 0x1, 0x2]⟩
private theorem g3_3_ok : g3_3.OK L3 := gate_of_test (by decide +kernel)

private def g3_17 : Gate := ⟨17, 8, 0x1a317, #[
    0x1ffff, 0x1654d, 0xe696, 0x663e, 0x11ac7, 0x8bf4, 0x103d7, 0xaea6,
    0x1b42d, 0x10b76, 0x15d4c, 0xf03d, 0x1f445, 0xd63c, 0x1198f, 0x59cd,
    0xa9b6]⟩
private theorem g3_17_ok : g3_17.OK L3 := gate_of_test (by decide +kernel)

private def filters3 : List Gate := [g3_5, g3_53, g3_61, g3_59, g3_47, g3_43, g3_31, g3_23, g3_19, g3_11, g3_7, g3_37, g3_3, g3_17]
private theorem gates3 (g : Gate) (h : g ∈ filters3) : g.OK L3 ∧ 512 ≤ g.p*2^vDepth g.p := by
  simp only [filters3, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨g3_5_ok, by decide +kernel⟩
  · exact ⟨g3_53_ok, by decide +kernel⟩
  · exact ⟨g3_61_ok, by decide +kernel⟩
  · exact ⟨g3_59_ok, by decide +kernel⟩
  · exact ⟨g3_47_ok, by decide +kernel⟩
  · exact ⟨g3_43_ok, by decide +kernel⟩
  · exact ⟨g3_31_ok, by decide +kernel⟩
  · exact ⟨g3_23_ok, by decide +kernel⟩
  · exact ⟨g3_19_ok, by decide +kernel⟩
  · exact ⟨g3_11_ok, by decide +kernel⟩
  · exact ⟨g3_7_ok, by decide +kernel⟩
  · exact ⟨g3_37_ok, by decide +kernel⟩
  · exact ⟨g3_3_ok, by decide +kernel⟩
  · exact ⟨g3_17_ok, by decide +kernel⟩

private def patch3_0 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x1000000000000001 0x67b07fa) (.leaf 16 0x10040000000 0x4fc090f)) (.join (.leaf 16 0x1080000000100000 0xa240f2d037d) (.leaf 16 0x1000200000000001 0x7f0dd801fe))) (.join (.join (.leaf 16 0x80000000000420 0xfee0b3903e5) (.leaf 16 0x10002000000 0xc4e09cc)) (.join (.leaf 16 0x400000200000000000 0xd630b0a) (.leaf 16 0x0 0x0)))) (.join (.join (.join (.leaf 16 0x200000 0xe78001d) (.leaf 16 0x8000004200000000000 0x36c0f8d06cc)) (.join (.leaf 16 0x1004000000000000 0x67b0b9e) (.leaf 16 0x600000000000 0x82006850376))) (.join (.join (.leaf 16 0x1 0x2f7) (.leaf 16 0x80000000000400 0x21d0e1a)) (.join (.leaf 16 0x20 0x95e) (.leaf 16 0x18000000000000000001 0xd70091e005508b5))))) (.join (.join (.join (.join (.leaf 16 0x0 0x0) (.leaf 16 0x80000000000000000 0x80b05640509042c)) (.join (.leaf 16 0x8001000000000000000 0xccb0729) (.leaf 16 0x400 0x59e))) (.join (.join (.leaf 16 0x1 0x8cb) (.leaf 16 0x10000100000 0x4fc0f42)) (.join (.leaf 16 0x0 0x0) (.leaf 16 0xc00 0xec708460510)))) (.join (.join (.join (.leaf 16 0x0 0x0) (.leaf 16 0x8000000000002000000 0xc810ab4)) (.join (.leaf 16 0x20000000000000000 0x8d0) (.leaf 16 0x20000000000008000 0x7680a80))) (.join (.join (.leaf 16 0x80200000000800 0x470059a0ac204b3) (.leaf 16 0x0 0x0)) (.join (.leaf 16 0x800000001 0x9690970) (.leaf 16 0x400000000800000800 0xa4203bb06d10339))))))
set_option maxRecDepth 4000 in
private theorem scan3_0 : Region (clearPoint L3) 0 512 :=
  checkedPatch 0 patch3_0 gates3 (by decide +kernel) (by decide +kernel)
private def patch3_512 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x100020 0x37d0c12) (.leaf 16 0x0 0x0)) (.join (.leaf 16 0x200000000000000 0x86c07b1039b0011) (.leaf 16 0x14000000000000 0x81c073502ce0218005e))) (.join (.join (.leaf 16 0x210000000020 0x1500b410e82) (.leaf 16 0x40000010000000020 0x9e803b506580a96)) (.join (.leaf 16 0x4000000100000 0x9c90342) (.leaf 16 0x2000000 0x970)))) (.join (.join (.join (.leaf 16 0x4000002000001 0x53506ba099c) (.leaf 16 0x400000000800100000 0x417099c0803)) (.join (.leaf 16 0x8001000020000010000 0x89c0bcd08d706490c260b1d) (.leaf 16 0x1 0x1fe))) (.join (.join (.leaf 16 0x80000002000000 0xf21091b) (.leaf 16 0x8000084000000000001 0xac4058008b50a2b)) (.join (.leaf 16 0x80000000200000 0xc4308920226) (.leaf 16 0x80000010000000020 0xe530b660214018400db0ec4))))) (.join (.join (.join (.join (.leaf 16 0x8000000000000000000 0x172) (.leaf 16 0x0 0x0)) (.join (.leaf 16 0x8020004000000000000 0xe7105b90d6e) (.leaf 16 0x400000000000 0x3010202))) (.join (.join (.leaf 16 0x0 0x0) (.leaf 16 0x401004001800000000 0xecd007f09a60ca9082d0038)) (.join (.leaf 16 0x8000000000040000020 0x21d0d060ee8) (.leaf 16 0x400004000000000000 0xee306d6)))) (.join (.join (.join (.leaf 16 0x400000 0xd8a06430587016c) (.leaf 16 0x40000000040000400 0x8b800b100e6033a)) (.join (.leaf 16 0x800000000 0x7ae) (.leaf 16 0x840000400 0x5ee0feb0099))) (.join (.join (.leaf 16 0x8400000000000000002 0xb5f0ad80ae60a6d) (.leaf 16 0x0 0x0)) (.join (.leaf 16 0x100000 0x5a8) (.leaf 16 0x1000000000000000 0xc8a))))))
set_option maxRecDepth 4000 in
private theorem scan3_512 : Region (clearPoint L3) 512 1024 :=
  checkedPatch 512 patch3_512 gates3 (by decide +kernel) (by decide +kernel)
private def patch3_1024 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x0 0x0) (.leaf 16 0x4000020 0xb4307fb0111)) (.join (.leaf 16 0x400000000000 0xd7f0d29) (.leaf 16 0x80010000000000 0x37))) (.join (.join (.leaf 16 0x802000000 0xd0d02df) (.leaf 16 0x80000020 0x8de07680027)) (.join (.leaf 16 0x10002000000 0x7cb0eee) (.leaf 16 0x20000200000300000 0x6eb0547083e06700495)))) (.join (.join (.join (.leaf 16 0x200000000000 0x189) (.leaf 16 0x40000001 0xfab0e88)) (.join (.leaf 16 0x400 0xd32) (.leaf 16 0x8020004000000008042 0x63000870bd60eab0a8f053a0ba104b6))) (.join (.join (.leaf 16 0x80200000000000 0x1670894) (.leaf 16 0x40000000000108020 0x79b07430b980d6f07e9)) (.join (.leaf 16 0x4000000000000 0xae6) (.leaf 16 0x400100000000000000 0x93d0dae07df))))) (.join (.join (.join (.join (.leaf 16 0x8000004001000000001 0x904057a0a7c00220b3e) (.leaf 16 0x400002100000 0xf8c063905170270)) (.join (.leaf 16 0x400000020000000000 0xb3e080c0063) (.leaf 16 0x1000000800000000 0x340644))) (.join (.join (.leaf 16 0x200040008000 0x4f60e400d8d) (.leaf 16 0x400080020000000003 0x93e00da0fa0091509b409b10498)) (.join (.leaf 16 0x0 0x0) (.leaf 16 0x0 0x0)))) (.join (.join (.join (.leaf 16 0x4000000000000 0xa3c) (.leaf 16 0x8000000000040000020 0xf790d51084f)) (.join (.leaf 16 0x8000000000000000001 0x2fa0c5c) (.leaf 16 0x800000000042100000 0xd8e043b03060c470970))) (.join (.join (.leaf 16 0x10000000000 0x92a) (.leaf 16 0x2000000040000400 0xe4d03e5047f093d)) (.join (.leaf 16 0x80000000008020 0x60f09e108c5) (.leaf 16 0x4000000000000 0xed2))))))
set_option maxRecDepth 4000 in
private theorem scan3_1024 : Region (clearPoint L3) 1024 1536 :=
  checkedPatch 1024 patch3_1024 gates3 (by decide +kernel) (by decide +kernel)
private def patch3_1536 : Patch :=
  (.join (.join (.join (.join (.leaf 16 0x600000010000 0xe770b6e01340c4f03df) (.leaf 16 0x0 0x0)) (.join (.leaf 16 0x0 0x0) (.leaf 16 0x80000000000000 0x241))) (.join (.join (.leaf 16 0x10000000000002000001 0xe0a014d01440c0f) (.leaf 16 0x4000000100020 0x3780ecd0a0e)) (.join (.leaf 16 0x800000000 0x1aa) (.join (.leaf 16 0x0 0x0) (.leaf 16 0x80020000000080 0xd620ba304410c0c0950071f045c))))) (.join (.join (.join (.leaf 16 0x42000001 0xc97049f0d17) (.leaf 16 0xc00000000000000000 0x860061505ab)) (.join (.leaf 16 0x100000 0xb52) (.leaf 16 0x2000000040000000 0x93f02bd0781))) (.join (.join (.leaf 16 0x80000000000000 0x15f) (.leaf 16 0x1 0xd3f)) (.join (.leaf 16 0x108000 0x5b20fce) (.join (.leaf 16 0x20000030000000000 0xf107ed048c0314) (.leaf 11 0x1002000020 0xdc4005303fc0fc4))))))
set_option maxRecDepth 4000 in
private theorem scan3_1536 : Region (clearPoint L3) 1536 1819 :=
  checkedPatch 1536 patch3_1536 gates3 (by decide +kernel) (by decide +kernel)
private theorem rows3 : Region (clearPoint L3) 0 1819 :=
  (mergeRegion (mergeRegion scan3_0 scan3_512) (mergeRegion scan3_1024 scan3_1536))
private theorem clear3 : Clear L3 := clear_of_scan (by decide +kernel) (rows3)

private def L4 : Chart := ⟨9881, 250640081247, 799808, 281815, -114463, 1165862, 1759, 1486⟩

private def g4_5 : Gate := ⟨5, 10, 0x13, #[
    0x1f, 0x1, 0x2, 0x4, 0x8]⟩
private theorem g4_5_ok : g4_5.OK L4 := gate_of_test (by decide +kernel)

private def g4_53 : Gate := ⟨53, 7, 0xd228fccfc512d, #[
    0x400, 0x95323887a6060, 0x101087730f080f, 0xdc9608cdc1140, 0x7eb401740902a, 0x2ec0c22a52ce, 0x1014b6f4826844, 0xc035d98909960,
    0x2656ea89a6001, 0xac36409159138, 0x16a10119ace114, 0x80d7e2248611a, 0x15c61003259a2c, 0xb9c04b82c2a82, 0x1050b0401a72e7, 0xc1eb08053028f,
    0x111818792728a8, 0x328c4c2b421b4, 0xa10c8e45a6861, 0x4cb6204f1c0b0, 0x8d2799c170042, 0xf83092b912910, 0xb218410a72ae8, 0x1f089455211a22,
    0x28363a4785301, 0x3380154951a74, 0x11708b96a11130, 0x15a7443a219110, 0x4aa007305cb15, 0x18971b05101943, 0x12a8a443e88b10, 0x1420861342ea9c,
    0x7524307c11291, 0xe6792c48401d, 0x1c811b4c81a071, 0x89c4c2150c2cb, 0x150c8c5305b085, 0x1278606222a29c, 0x80435e0de2819, 0x834283ce9cb,
    0x107480e7482a86, 0x1300218ea68b34, 0x911fac04b10c2, 0x16620215a510e6, 0x2409b0d439135, 0x455da991000cb, 0x466eb00c0d321, 0x4bdb4a02442c8,
    0x110c0dd00e694a, 0xba00b5f8a8120, 0xcc41a4ec05107, 0x33b84203e021e, 0x1847132a40c0cb]⟩
private theorem g4_53_ok : g4_53.OK L4 := gate_of_test (by decide +kernel)

private def g4_61 : Gate := ⟨61, 6, 0x1713e6940a59f23b, #[
    0x1fffffffffffffff, 0x13846501cb6d2b08, 0x1c53469334012b0d, 0x8b39116a34721a4, 0x220a6139c21e5f2, 0xaa0584c15bab5c0, 0x1ce0fc302532c8c0, 0xb6310ba715862a,
    0x900dd2c574b82e, 0xe50768cc60464c5, 0xd95133c474a0066, 0x1b50616596016a38, 0xe941beb01e001d2, 0x1c3f76c48cc00a2, 0x1ca6c5a07019b882, 0xb041a70d849551d,
    0xc74411f2a31da02, 0x1510c496b839c720, 0x122042f2c94a4e56, 0xb6268a54fc60025, 0x1c633020a0fa5253, 0x6d5e02ee08c209c, 0x122006d132972967, 0x581f7c999244045,
    0xd720028afccb054, 0x44190c36c9d6e09, 0xb41eaa2a39a1209, 0x185602764530e90b, 0x8878f17298013f0, 0x1036a46c3550328b, 0x43046cc6a54e6d, 0x106102d9ca958cd8,
    0x12b60745302ab0d8, 0x18f0883f200653a3, 0x350f425c3289b9, 0xbc16a4121671515, 0x4c11241dae4db0c, 0x2758a834cfd450, 0x17c0d2880892664f, 0x1002279a53a5322d,
    0x3d5b0e410c41dd0, 0x6631f29297c1410, 0xb236a90018fca94, 0x10225a9c94a4d3d, 0x118454138e7075a4, 0x11719016e3153e2, 0xc106ae2aa486c39, 0x11b29d0476603816,
    0x17e1c11400cc48db, 0xc14b92e001e035f, 0x3056c715a01a69a, 0x454d998014b88f3, 0x17053a8c98818cc5, 0x180481d074ba8d2e, 0x636815186a39742, 0x1f839c0c4d329030,
    0xd02a80eb576a0c8, 0x1282213e9e10e721, 0x4e68896138b15a2, 0x11651ec35200b325, 0x1310e44352db4e02]⟩
private theorem g4_61_ok : g4_61.OK L4 := gate_of_test (by decide +kernel)

private def g4_59 : Gate := ⟨59, 6, 0x22b62183e7b92bb, #[
    0x1000000000000, 0x2259bffc8493c31, 0x493496fd57d58c0, 0x5f1303629759a5d, 0x1af98cb16d55319, 0x615bd3d18e2656c, 0x5a98f0a259e8e6b, 0x4599fa943dd228e,
    0x6ddc9c8784f093c, 0x487119cb4cabdda, 0x3b165f18df383c0, 0x37fb874698a1952, 0x64be257a0e62e39, 0x1d7ac984693ccf8, 0x3cbc9756643b207, 0x51f1b3f509d267,
    0x1d3f843586a97ca, 0x4c9e8e8efe8b310, 0x297232bcbda6718, 0x76104effe35700a, 0x7a93e117f8140f9, 0x223285bfbba8a87, 0x757654a1d9834e3, 0x249f3acc2bc8d69,
    0x2e5f426b13f4e82, 0x4d58ebe9a848f85, 0x31d6ed2c3ea103e, 0x5ddcb15a3385744, 0xc57a693511bcbe, 0x3f581322fe969a4, 0x1035f8965a5fd13, 0x4bd461f4f622b25,
    0x1a77748ba87316a, 0x6ed719f0215f0d2, 0x2e356687c48565f, 0x5f4e905cbf2359, 0x39f24a5ac4f50cd, 0x54dd5f1cb066e14, 0x42988b8545777f6, 0xf92be7c0a07fa2,
    0x6410dd403ab1ffd, 0x189d2863996f4f5, 0x62f26423345fdc5, 0x43f9714fa5586b0, 0x31f143992e42bf3, 0x527a7b8137099ab, 0x26bd707ccf25886, 0x48fa4e71d19c17a,
    0x43bfd92a614658b, 0x74d1b80f073ec63, 0x311c256ef54cb4e, 0x72776cf243c8784, 0x3f3345c512ef0a5, 0x1e32b759c5e6914, 0x17b50cda991c62f, 0x633eb2632aada34,
    0x191f6e966ba51b, 0x5259240c6afaafd, 0x7b348a30f2484ff]⟩
private theorem g4_59_ok : g4_59.OK L4 := gate_of_test (by decide +kernel)

private def g4_47 : Gate := ⟨47, 7, 0x7bcae4d8ac21, #[
    0x7fffffffffff, 0x23f966af024c, 0x31c3c4c5faa8, 0x5e6ba76b0b, 0x772305a13f54, 0x300aa7a59c7b, 0x69467c41536e, 0x6ef88c09b5e0,
    0x788996e2b0d5, 0x430da8a5dd8d, 0x44eb7ce1141d, 0x3394d2a92fe0, 0x69f7a3883312, 0x2b4f1c2d9ad0, 0xea5028e9ef9, 0x296922cd55e3,
    0x1699cfe84c58, 0x593399636c0e, 0x1e468e41b51f, 0x4dd267e064aa, 0x515f8f421a99, 0x4ef0db660172, 0x2fb044e4b867, 0x3e9ea862dc24,
    0x7c48768c2af2, 0x75cc3a4e441b, 0x729d00cdb61e, 0xb32b085e3f5, 0x32aa4c0fcc97, 0x79f15b04e2c4, 0x1ae06d8d3399, 0x6834642fe732,
    0x158f5566892d, 0x713ef2e2814a, 0x5416b36871e5, 0x169198238bdf, 0x4c0fe92a9653, 0x2370510e7dae, 0x4363774a2b61, 0x1f561a8ed322,
    0x760f5b20623e, 0x16ed95047cc5, 0xdbc734bcaa0, 0x6e55f90b4189, 0x1a1adcbacf4, 0xc2abf464787, 0x446481eacd3f]⟩
private theorem g4_47_ok : g4_47.OK L4 := gate_of_test (by decide +kernel)

private def g4_43 : Gate := ⟨43, 7, 0x4a77c5c11ad, #[
    0x8000000000, 0x18e795467d8, 0x381e97f9622, 0x4e9af3a12d8, 0x7d413e8c26b, 0x1f1c8dc638b, 0x4e892cdbe0e, 0x3b860b81b7e,
    0x6a720434efd, 0x1ba3e57822b, 0x7ab42f484f2, 0x6d0cdf18c9c, 0x5bcd5c20de4, 0x1d24383d7d6, 0x68a947955cb, 0x49fe24e9998,
    0xd92f4d5535, 0x7a03d8ae98e, 0x3de884aec72, 0x1a25c6eda55, 0x38c8b2558ef, 0x68f5ed25a06, 0xb605a4b7af, 0xef71aa4d13,
    0x2caa5b763a4, 0x5e4e3752117, 0x2f719751bc0, 0x58acaab2f49, 0x4919997247f, 0xbd3aa9e295, 0x5c6bebc1c24, 0x6d27b043ab3,
    0x5b39318fb30, 0x2f4f212f42d, 0x6cd441ea7c5, 0x2bbf72c204e, 0x6e7ed81d061, 0x39707db3491, 0x7cd1c63b138, 0x5fd64317c82,
    0x391b485cf59, 0xe4469fe978, 0xc1be62a9e7]⟩
private theorem g4_43_ok : g4_43.OK L4 := gate_of_test (by decide +kernel)

private def g4_31 : Gate := ⟨31, 7, 0x6de2b849, #[
    0x7fffffff, 0x43696f12, 0x5f298668, 0x3d1eba04, 0x3e1cc2c5, 0x1a3ca65c, 0x6602b89f, 0x4745ce62,
    0x2c52b1b5, 0x45645db2, 0x1c1bf08d, 0x2102f5db, 0x68415dda, 0x5b674624, 0x7e3426e0, 0x7342d998,
    0x2167199b, 0x163f0764, 0x736d2462, 0x410b5bba, 0x2042dbaf, 0x6c1cb10f, 0x13514dba, 0x251aad8d,
    0x51714673, 0x2033f91d, 0x1e2c3a65, 0x1c3ea343, 0x3c5e205d, 0x4a7d1661, 0x4b6148f6]⟩
private theorem g4_31_ok : g4_31.OK L4 := gate_of_test (by decide +kernel)

private def g4_23 : Gate := ⟨23, 8, 0x7acca1, #[
    0x7fffff, 0x26b5c2, 0x8e32f, 0x4e4355, 0x4fd0b0, 0x2dc3c1, 0x1314b7, 0x4574d4,
    0x7a241d, 0x3832e6, 0x2a11be, 0x492747, 0x717249, 0x3ec42a, 0x33a60e, 0x5c122f,
    0x159751, 0x769464, 0x41e1da, 0x685f9, 0x556139, 0x7a6388, 0x21d6b2]⟩
private theorem g4_23_ok : g4_23.OK L4 := gate_of_test (by decide +kernel)

private def g4_19 : Gate := ⟨19, 8, 0x30af3, #[
    0x800, 0x1a1fa, 0x5c42f, 0x692d5, 0x65745, 0x6d625, 0x131db, 0x253c7,
    0x233f2, 0x5e638, 0x633d1, 0x7e624, 0x1e52e, 0x5c64d, 0x235ba, 0x1753a,
    0x5a4ba, 0x211df, 0x7c2c5]⟩
private theorem g4_19_ok : g4_19.OK L4 := gate_of_test (by decide +kernel)

private def g4_11 : Gate := ⟨11, 9, 0x23b, #[
    0x7ff, 0x6d, 0xa7, 0x345, 0x3b, 0x19a, 0x166, 0x370,
    0x28b, 0x394, 0x2d8]⟩
private theorem g4_11_ok : g4_11.OK L4 := gate_of_test (by decide +kernel)

private def g4_7 : Gate := ⟨7, 9, 0x17, #[
    0x7f, 0x38, 0x52, 0x32, 0x49, 0x29, 0x43]⟩
private theorem g4_7_ok : g4_7.OK L4 := gate_of_test (by decide +kernel)

private def g4_37 : Gate := ⟨37, 7, 0x9a1dee165, #[
    0x1fffffffff, 0xc1b9d23bc, 0x1edeb53840, 0x19333653d8, 0x156451ba7c, 0xc20fdc71d, 0x1af2d1e192, 0x1241e7dfc,
    0x92bb09cde, 0xb91bccec4, 0xa07f73d03, 0x1c2e97268b, 0x12c718b76a, 0x1cc2723da9, 0x3aab541d7, 0x43fb2476c,
    0x4f6f82497, 0x149db5558a, 0x18b47527a5, 0xbc95c5a3a, 0x3555b7255, 0x12483ede4e, 0xdc49bf843, 0x17055aab8e,
    0xb789c8679, 0xdda31c695, 0x2c9d2e87d, 0x179dfc0ac, 0x6e67b13a2, 0x16721ba927, 0x1f7cf04903, 0x130f169eb4,
    0x11c77e086b, 0x1cbb144d53, 0x1794d99931, 0x4395af6f0, 0x1b8973b063]⟩
private theorem g4_37_ok : g4_37.OK L4 := gate_of_test (by decide +kernel)

private def g4_3 : Gate := ⟨3, 11, 0x5, #[
    0x7, 0x2, 0x2]⟩
private theorem g4_3_ok : g4_3.OK L4 := gate_of_test (by decide +kernel)

private def g4_17 : Gate := ⟨17, 8, 0x1a317, #[
    0x100, 0x1f147, 0x12bba, 0x93de, 0xcdc7, 0x1db94, 0x1ad71, 0x12f4d,
    0x7b78, 0x3dbc, 0x165e9, 0x11d6b, 0x53b7, 0x1c766, 0xf792, 0xbba9,
    0x1c51f]⟩
private theorem g4_17_ok : g4_17.OK L4 := gate_of_test (by decide +kernel)

private def filters4 : List Gate := [g4_5, g4_53, g4_61, g4_59, g4_47, g4_43, g4_31, g4_23, g4_19, g4_11, g4_7, g4_37, g4_3, g4_17]
private theorem gates4 (g : Gate) (h : g ∈ filters4) : g.OK L4 ∧ 512 ≤ g.p*2^vDepth g.p := by
  simp only [filters4, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨g4_5_ok, by decide +kernel⟩
  · exact ⟨g4_53_ok, by decide +kernel⟩
  · exact ⟨g4_61_ok, by decide +kernel⟩
  · exact ⟨g4_59_ok, by decide +kernel⟩
  · exact ⟨g4_47_ok, by decide +kernel⟩
  · exact ⟨g4_43_ok, by decide +kernel⟩
  · exact ⟨g4_31_ok, by decide +kernel⟩
  · exact ⟨g4_23_ok, by decide +kernel⟩
  · exact ⟨g4_19_ok, by decide +kernel⟩
  · exact ⟨g4_11_ok, by decide +kernel⟩
  · exact ⟨g4_7_ok, by decide +kernel⟩
  · exact ⟨g4_37_ok, by decide +kernel⟩
  · exact ⟨g4_3_ok, by decide +kernel⟩
  · exact ⟨g4_17_ok, by decide +kernel⟩

private def patch4_0 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x8000008000004000001 0xab4096d007f082603af06df) (.leaf 16 0x400000400800100400 0x6260d4209220d360bfb032c)) (.join (.leaf 16 0x0 0x0) (.leaf 16 0x2000000000000400 0x6d2056d0b65))) (.join (.join (.leaf 16 0x80000000000000 0xda8) (.leaf 16 0x4010000000000 0x4b40c82)) (.join (.leaf 16 0x200002000020 0x74507e40b14) (.leaf 16 0x20000000000 0x6c503fb)))) (.join (.join (.join (.leaf 16 0x20000000000000000 0xb86) (.leaf 16 0x40000020 0x3420d90)) (.join (.leaf 16 0x400000000000000000 0x90e) (.leaf 16 0x200000 0x6b80289))) (.join (.join (.leaf 16 0x84000080000000 0xa4808e90d7c0b2e) (.leaf 16 0x400000010000000800 0x420adc07ab01d0)) (.join (.leaf 16 0x802000000 0xc9e0ac6) (.leaf 16 0x2000002 0xcd906ab0117))))) (.join (.join (.join (.join (.leaf 16 0x400000000000000000 0x5e) (.leaf 16 0x8000000000000000020 0x5dd0309)) (.join (.leaf 16 0x8002000000000000000 0x9ee069e04a6) (.leaf 16 0x180000000000020 0x9b40811016809e2))) (.join (.join (.leaf 16 0x4000000000000 0xc04) (.leaf 16 0x10401000200000000000 0xa2801d10dae0b3d0528)) (.join (.leaf 16 0x20000030040000000 0xb800aca0691015c0c82) (.leaf 16 0x20000001800100000 0x613052303e903800a38)))) (.join (.join (.join (.leaf 16 0x80000000000020 0x2b9077b) (.leaf 16 0x40108000 0xdb10af3054d)) (.join (.leaf 16 0x200000 0x8770684) (.leaf 16 0x8000000000000000000 0x60a))) (.join (.join (.leaf 16 0x0 0x0) (.leaf 16 0x20 0x7b)) (.join (.leaf 16 0x8000080000000000001 0x1f1056e0677) (.leaf 16 0x200000000000 0xbf8))))))
set_option maxRecDepth 4000 in
private theorem scan4_0 : Region (clearPoint L4) 0 512 :=
  checkedPatch 0 patch4_0 gates4 (by decide +kernel) (by decide +kernel)
private def patch4_512 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x20004000000000000 0x8dd0d6c) (.leaf 16 0x1000000800000020 0x66a09580607)) (.join (.leaf 16 0x400080000000000020 0xc140324041b) (.leaf 16 0x420000000000000000 0x4db049e))) (.join (.join (.leaf 16 0x400000000020 0xd0a0b630100) (.leaf 16 0x401000020000000001 0xcfd07d8065d026d09ca)) (.join (.leaf 16 0x8020000000000000400 0x36d046a0ce5) (.leaf 16 0x80000000 0xc890943)))) (.join (.join (.join (.leaf 16 0x8000 0xd27) (.leaf 16 0x400004000000100000 0x14207b20650)) (.join (.leaf 16 0x0 0x0) (.leaf 16 0x400000000002000800 0xd710bc903710092))) (.join (.join (.leaf 16 0x0 0x0) (.leaf 16 0x18000000000000000002 0x9a905c9038d064304c2)) (.join (.leaf 16 0xc00000010000000000 0x36700f300210d91) (.leaf 16 0x84000000000000 0x7b40547))))) (.join (.join (.join (.join (.leaf 16 0x1000200000000400 0x636041b0817) (.leaf 16 0x800000000 0x46)) (.join (.leaf 16 0x200040000000 0x59e03bb) (.leaf 16 0x400000000000 0xa71078b))) (.join (.join (.leaf 16 0x20000000000 0xa0f0629) (.leaf 16 0x420000000000100000 0xad803d90038)) (.join (.leaf 16 0x80000000000000 0x19c) (.leaf 16 0x400000000000000000 0x535)))) (.join (.join (.join (.leaf 16 0x200000 0x61c0034) (.leaf 16 0x1000000002008000 0xc6a046603f5)) (.join (.leaf 16 0x4000000000000 0x82c) (.leaf 16 0x60 0xa75065704fa))) (.join (.join (.leaf 16 0x8000000000040000401 0x19c09ba051a060f) (.leaf 16 0x40000020 0x3fd07ea)) (.join (.leaf 16 0x20000000000000000 0x63f) (.leaf 16 0x1000000800008000 0x6020856032a))))))
set_option maxRecDepth 4000 in
private theorem scan4_512 : Region (clearPoint L4) 512 1024 :=
  checkedPatch 512 patch4_512 gates4 (by decide +kernel) (by decide +kernel)
private def patch4_1024 : Patch :=
  (.join (.join (.join (.join (.leaf 16 0x80000040000001 0x1ba0670095e) (.join (.leaf 16 0x8000000000000 0xadb08e8) (.leaf 16 0x400000200000000400 0xbd102cf052f))) (.join (.join (.leaf 16 0x10000000000 0x5f5) (.leaf 16 0x1000008400 0x4fe048f039d0157)) (.join (.leaf 16 0x0 0x0) (.leaf 16 0x2000000 0x1ab)))) (.join (.join (.leaf 16 0x1004000800100000 0x2d7025d047b05e8) (.join (.leaf 16 0x38000 0xd6c0b4108b3082407400560007a) (.leaf 16 0x400 0x21e))) (.join (.join (.leaf 16 0x80000000000021 0x55c02380cb5) (.leaf 16 0x410002000001 0x3f0022908d106af05db)) (.join (.leaf 16 0x0 0x0) (.leaf 16 0x20004000000000000 0x2ee01f5))))) (.join (.join (.join (.leaf 16 0x2000000000100000 0xba705ce0a42) (.join (.leaf 16 0x0 0x0) (.leaf 16 0x800000000 0xccc))) (.join (.join (.leaf 16 0x200000000001 0x8eb026c) (.leaf 16 0x10800000000 0x5c10481)) (.join (.leaf 16 0x20000000800200000 0x46008da08850308) (.leaf 16 0x40000000 0x864)))) (.join (.join (.join (.leaf 16 0x2000000 0xc0d) (.leaf 16 0x200000 0x5b40003)) (.join (.leaf 16 0x10020 0xd7c060805a7) (.leaf 16 0x0 0x0))) (.join (.join (.leaf 16 0x80000000000000 0x1d5) (.leaf 16 0x8000000200000000002 0xc94044a05a702a5)) (.join (.leaf 16 0x10c00000010000000000 0x44203bb0c7304b3003b02ce) (.leaf 15 0x20 0x28c))))))
set_option maxRecDepth 4000 in
private theorem scan4_1024 : Region (clearPoint L4) 1024 1487 :=
  checkedPatch 1024 patch4_1024 gates4 (by decide +kernel) (by decide +kernel)
private theorem rows4 : Region (clearPoint L4) 0 1487 :=
  (mergeRegion scan4_0 (mergeRegion scan4_512 scan4_1024))
private theorem clear4 : Clear L4 := clear_of_scan (by decide +kernel) (rows4)

private def L5 : Chart := ⟨9881, 370454897724, 878483, 312512, -236415, 1014067, 1718, 1636⟩

private def g5_5 : Gate := ⟨5, 10, 0x13, #[
    0x8, 0xc, 0xa, 0x9, 0x18]⟩
private theorem g5_5_ok : g5_5.OK L5 := gate_of_test (by decide +kernel)

private def g5_53 : Gate := ⟨53, 7, 0xd228fccfc512d, #[
    0x400000, 0x6268973c06046, 0x10c5e17c082d8, 0x1d4940be509101, 0x778a455600b02, 0x19002dd8c90a1a, 0x8115fa660926, 0x120a9c234d18c8,
    0x12c04646f2a809, 0x2ab2780c3024b, 0x1345e729610401, 0x4510a6448547e, 0x4c75f10585021, 0x1c0098d52c99c, 0x5683034c14c8d, 0x12c53002647178,
    0x5060f1de1113, 0x10749a98748019, 0x125d2281c89ca0, 0x28218ed40b4b1, 0x185411a4f2062a, 0x42c01dc542d70, 0x91afa42432064, 0x4a5c84b6180aa,
    0x55604824f02e6, 0x10f04628d86780, 0x1a5a9446e1141, 0x1610510ec452b4, 0x1c203cc3628c41, 0xa8ce81e48240d, 0x148aa030da4274, 0x244c098484beb,
    0x1081d685477006, 0x86a8c09e4b105, 0x511a5a056e308, 0x920a722702897, 0x18330025c32b25, 0x819110f71e0c1, 0xd23d1c4c80194, 0x1a962650658182,
    0xe073269563200, 0xc908143411f5c, 0x88fc54244ca11, 0xb300410d29cf4, 0x151a4818603c9a, 0xd3202a9ec4c40, 0x122631658872a, 0x40c920ccbf510,
    0x26b0a12637680, 0x1b881a00d544a3, 0xaf011214fa052, 0x20368207d0f46, 0x118c40c079d22c]⟩
private theorem g5_53_ok : g5_53.OK L5 := gate_of_test (by decide +kernel)

private def g5_61 : Gate := ⟨61, 6, 0x1713e6940a59f23b, #[
    0x400, 0xe005216dd289ab3, 0xd3cfc4110325913, 0x7381e292a25328b, 0x868e20be1aef060, 0x5c24a8c243c89fa, 0x12693b0b8443e918, 0x107b21c3506539b,
    0x1155807995bd4805, 0x8d3e05750bc8c3, 0x1e2126a15c3098d5, 0x1415c5c3426d4239, 0x1b520c2c835f9a40, 0x44988b98782ca75, 0x1e2946402f8e4952, 0xf251d3507b02072,
    0x10da467376c4102a, 0xd6b3ce4a915812, 0x46d44c0b35eb814, 0x817d8b135d54288, 0x8cefc094218789c, 0x147c16048d6101fe, 0xb4e210736e423a1, 0x1dd9a88e090b302c,
    0x14128b665d50f10c, 0x13bcda1a2440a1d1, 0x18d825708394918f, 0xc59362092e0ab4e, 0x823bd5897243864, 0x10c5b68b9b1a82c0, 0xc60af596203a20f, 0x11a6bd418de08b8,
    0x36745b68c20682b, 0x13a46af71044c384, 0x1d2411b268ce5aa0, 0x7043a906c7e3125, 0x891616cf73170a0, 0xae99b4520a611e1, 0x241c4566ee6819a, 0x1db38211cb50b884,
    0x1ac481a0f8aff010, 0x10a40fdcc4723c3, 0xeb2346fa0422855, 0xb340c8ad88503af, 0x549cf35ac090351, 0xdbb39896c2a8104, 0x1782b2e293c9c081, 0x7d0098a51e9524e,
    0x78674464895ca68, 0xb04d0c12b604b3f, 0x190b0e8ea0b38856, 0x10ea159211f56321, 0x2ba81f2c418627a, 0x16a67806aa340257, 0x2b0e137821b394c, 0x8874372592312f8,
    0x1090c5490e8bf227, 0x161f411c5840c1ee, 0x115251e0739a2994, 0x102208fcf2d91349, 0x12eda12801d9ab22]⟩
private theorem g5_61_ok : g5_61.OK L5 := gate_of_test (by decide +kernel)

private def g5_59 : Gate := ⟨59, 6, 0x22b62183e7b92bb, #[
    0x80, 0x5b4028b7fc8563e, 0x76efbe48023381b, 0x6dd1c131dc76926, 0x4d5451d1f5bd506, 0x5ab6e5334cb4913, 0x347b6f46a7c8249, 0x1f52c55bd60b722,
    0x346be66cea66254, 0x5b905ae57ac1d23, 0x25e71b1cf358643, 0x24453a27b72a97d, 0x439cc2ff1c51d64, 0x24cf3fa8a26ec26, 0x2caf76c419e2e4c, 0x3b52e3e1ca8dc68,
    0x1a1ec8d397d0d27, 0x7511b1f4cdccd22, 0x767bd8e006f31d, 0x7f2281ff2415f30, 0x2f1ae5f27c07960, 0x533021aebd57d2a, 0x53b8e2e0cc9d32b, 0x37ed28a8076a53d,
    0x3ae03f07616a33d, 0x63c1d1c9e995d23, 0x1c18c1c3de9f559, 0x4a3bd532d6b1c26, 0x5211693bd4ded34, 0x7b60cce3f00df42, 0x403f1ccc1b7a17d, 0x6caf725a212965b,
    0x35ad32af714b21c, 0x65ef0e0c60e4d57, 0x265e4e2e0f1e25d, 0x5a1b83f01d75e62, 0x5b805452dfb5e52, 0x64cc1d1c772ea65, 0x2af5d610332aa5f, 0xf93e9d63d034f,
    0x2093fe0513f867d, 0x5801c6f79b85c67, 0x4eccbe3622ba259, 0x2fa72c4de167258, 0x454e1f1d2b70b1d, 0x1e608dbbd4d193a, 0x591457f3cc9321b, 0x28e3fd0ce70935c,
    0x53b791728895f4a, 0x6b3ce3639e96130, 0xd7a9d68276e25c, 0x195cd99f58b1523, 0x41af6a8d2be2276, 0x4f958bdb78b4920, 0x34cb329db56e449, 0x76be2e28aacb055,
    0x38ee320e2edb24b, 0x310049f7ddbec0e, 0x4ffb4500b6be35]⟩
private theorem g5_59_ok : g5_59.OK L5 := gate_of_test (by decide +kernel)

private def g5_47 : Gate := ⟨47, 7, 0x7bcae4d8ac21, #[
    0x4000000, 0x1ade2b65c44b, 0x570319e5a67c, 0x2d2a6394ea5d, 0x3c2fa5d8ed1, 0x17a2a1ff60e2, 0x19872b726c97, 0x2cfb188b195d,
    0xb9f712456f8, 0x57c58f231d7, 0x11b80d5dfe7, 0x467bb2569718, 0xf4933e5e1a5, 0x2b243a7bbc7, 0x79627a32396a, 0x6a2e09377d25,
    0x77cfe84126a4, 0x5cdac9209fb8, 0x742e72b5498b, 0x30fa337c92b4, 0x7bfa82b444d4, 0x5c11f80eb2f3, 0x73f1690c4f1a, 0x6e95d872c12e,
    0x1069c3752edd, 0x1e4612d1f9d6, 0x69ae03f10773, 0x6445a82bfbca, 0x2927d98be18b, 0x3255a9ce85f4, 0x3f20926b6747, 0x2c9042fe7dc9,
    0x17dd920e8ae9, 0x53898bc8d3d5, 0x7bbcb849a838, 0x30f4f9925e29, 0x1d2d49bbcc46, 0x7f75603b1039, 0x7189e347d43a, 0x6d4491df3a07,
    0x531a231be6ae, 0x26c9da9c333a, 0x60dff0a8bd11, 0x6e374be87822, 0x4ae538ca96ae, 0x4cb4f3181d4f, 0x4474da8f6b34]⟩
private theorem g5_47_ok : g5_47.OK L5 := gate_of_test (by decide +kernel)

private def g5_43 : Gate := ⟨43, 7, 0x4a77c5c11ad, #[
    0x7ffffffffff, 0x5790f9ac341, 0x59be0946aa5, 0x4d3f4e4505a, 0x4e0f3bb1065, 0x5f804634fb8, 0x68c6aacd3b, 0x405a3f1b966,
    0x53e042ad2e7, 0x1894d43e9ae, 0xbee1551d0b, 0x12a7655e325, 0x11b616c1f36, 0x40dd54d3c74, 0x4051da652fb, 0xedbf89320a,
    0x193ee115857, 0x4933b17bc22, 0xb5718d39d8, 0x45b287be503, 0x466af6e019c, 0x13259784ee3, 0x4c7721e9a4c, 0x1398076f566,
    0x1c0a7de14da, 0x1b9cb18ead, 0x1443de8dcc9, 0x4ea1a8877c9, 0x504c91fdb7, 0x1df4a65b8a0, 0x12e3cb2abb0, 0x46cf83686d8,
    0x4a4c7aa6e54, 0xd0b8aa877d, 0x47597c2b291, 0x5e74b54207c, 0x1669d8fc5a0, 0xdcb3556316, 0x51df2c6201f, 0x1a608ddcf07,
    0x15a0a272fcb, 0x5a5562907d9, 0x582c359f09e]⟩
private theorem g5_43_ok : g5_43.OK L5 := gate_of_test (by decide +kernel)

private def g5_31 : Gate := ⟨31, 7, 0x6de2b849, #[
    0x7fffffff, 0x3fd0099a, 0xd10575f, 0x6d26d388, 0x4d548db8, 0x4e2bc84b, 0x21a3cd3a, 0x52645a37,
    0x1d83079b, 0x7729c446, 0x633f8740, 0x58f816aa, 0x353ac29c, 0x185c5ed2, 0x34d59a61, 0x3ed41e5,
    0x53c15be, 0x3432cd59, 0x625bd1d0, 0x31ca1ae5, 0x6aab40f8, 0x18170fe6, 0x3b111ca7, 0x66cf060d,
    0x2f62d132, 0x12e59e2c, 0x4e909ea3, 0x48ed8955, 0x588e5b25, 0x47d75045, 0x72cc805f]⟩
private theorem g5_31_ok : g5_31.OK L5 := gate_of_test (by decide +kernel)

private def g5_23 : Gate := ⟨23, 8, 0x7acca1, #[
    0x10000, 0x2533e3, 0x3b078d, 0x47d3d0, 0x65289f, 0x4f14ba, 0x3dd125, 0x4da9e8,
    0x31aee8, 0x4dbe18, 0x77a330, 0x359746, 0x53598b, 0xbdc33, 0x7b6461, 0x6b185d,
    0x2b645e, 0x177a92, 0x51e574, 0x294fe4, 0x17c42f, 0x41bac7, 0x194b1f]⟩
private theorem g5_23_ok : g5_23.OK L5 := gate_of_test (by decide +kernel)

private def g5_19 : Gate := ⟨19, 8, 0x30af3, #[
    0x7ffff, 0x13593, 0x53961, 0xe17a, 0x54b34, 0x44fc8, 0x6211f, 0x703aa,
    0xc727, 0x495d4, 0x25752, 0x1c9c6, 0x6ab81, 0x7f108, 0x227e4, 0x259a5,
    0xbd0e, 0x30d39, 0x19359]⟩
private theorem g5_19_ok : g5_19.OK L5 := gate_of_test (by decide +kernel)

private def g5_11 : Gate := ⟨11, 9, 0x23b, #[
    0x4, 0x574, 0x5cc, 0x31d, 0x49e, 0x647, 0x27c, 0x12f,
    0xd7, 0x3a6, 0x6a5]⟩
private theorem g5_11_ok : g5_11.OK L5 := gate_of_test (by decide +kernel)

private def g5_7 : Gate := ⟨7, 9, 0x17, #[
    0x7f, 0x15, 0x32, 0x43, 0x61, 0x26, 0x54]⟩
private theorem g5_7_ok : g5_7.OK L5 := gate_of_test (by decide +kernel)

private def g5_37 : Gate := ⟨37, 7, 0x9a1dee165, #[
    0x10000, 0x1e34cd568e, 0x185adbb13c, 0x1f4645cf15, 0x4fb4f458b, 0x3ae95c3e5, 0x14323bf8d5, 0x12ff611917,
    0xd18f592bb, 0x1f68632e66, 0x1ec3317a27, 0x10b12dff0b, 0xe276dd568, 0x1b191f9473, 0x1536a923eb, 0x17dd53e61,
    0x8fdb3c90e, 0x847dbabc3, 0x2968facf6, 0x10de6be2d2, 0x587abb7c4, 0x4e1279b7e, 0x10cf9577d, 0xbaf892ad9,
    0x179c53f131, 0x1c2d576dc8, 0x3a1ff691a, 0x1fc8bd1986, 0x1ecce98c2d, 0xdba935e31, 0x13d1310dfe, 0xb563fb898,
    0x114f8752eb, 0x9a345e5be, 0x1f51e744c5, 0x6791bb6b4, 0x1ee2d56658]⟩
private theorem g5_37_ok : g5_37.OK L5 := gate_of_test (by decide +kernel)

private def g5_3 : Gate := ⟨3, 11, 0x5, #[
    0x7, 0x2, 0x1]⟩
private theorem g5_3_ok : g5_3.OK L5 := gate_of_test (by decide +kernel)

private def g5_17 : Gate := ⟨17, 8, 0x1a317, #[
    0x1ffff, 0x9673, 0x11ac7, 0x1af03, 0x1685b, 0x132ba, 0x1d117, 0x7c66,
    0x14db2, 0xdb2a, 0x63e3, 0x88bf, 0x1d4ca, 0x1a16e, 0xf5e, 0x358f,
    0xe696]⟩
private theorem g5_17_ok : g5_17.OK L5 := gate_of_test (by decide +kernel)

private def filters5 : List Gate := [g5_5, g5_53, g5_61, g5_59, g5_47, g5_43, g5_31, g5_23, g5_19, g5_11, g5_7, g5_37, g5_3, g5_17]
private theorem gates5 (g : Gate) (h : g ∈ filters5) : g.OK L5 ∧ 512 ≤ g.p*2^vDepth g.p := by
  simp only [filters5, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨g5_5_ok, by decide +kernel⟩
  · exact ⟨g5_53_ok, by decide +kernel⟩
  · exact ⟨g5_61_ok, by decide +kernel⟩
  · exact ⟨g5_59_ok, by decide +kernel⟩
  · exact ⟨g5_47_ok, by decide +kernel⟩
  · exact ⟨g5_43_ok, by decide +kernel⟩
  · exact ⟨g5_31_ok, by decide +kernel⟩
  · exact ⟨g5_23_ok, by decide +kernel⟩
  · exact ⟨g5_19_ok, by decide +kernel⟩
  · exact ⟨g5_11_ok, by decide +kernel⟩
  · exact ⟨g5_7_ok, by decide +kernel⟩
  · exact ⟨g5_37_ok, by decide +kernel⟩
  · exact ⟨g5_3_ok, by decide +kernel⟩
  · exact ⟨g5_17_ok, by decide +kernel⟩

private def patch5_0 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x1 0x6b6) (.leaf 16 0x2000000 0x881)) (.join (.leaf 16 0x104000000000000 0xb7705f80a4c) (.leaf 16 0x8000000000000010020 0xc17065c01b0009a))) (.join (.join (.leaf 16 0x0 0x0) (.leaf 16 0x20000200040100040 0x72b01c5053a0b9d047b0369)) (.join (.leaf 16 0x8c0000000 0xcd0ae709610602) (.leaf 16 0x0 0x0)))) (.join (.join (.join (.leaf 16 0x20 0x47c) (.leaf 16 0x200000000020 0x5a80ba7)) (.join (.leaf 16 0x1000000000000800 0x3be0240001c) (.leaf 16 0x20008000000000000 0x6b70bf107a0))) (.join (.join (.leaf 16 0x2000000000008000 0xc0c054e028d) (.leaf 16 0x800000000 0x300)) (.join (.leaf 16 0x0 0x0) (.leaf 16 0x8000000000000010000 0x4f4010c0005))))) (.join (.join (.join (.join (.leaf 16 0x400 0x242) (.leaf 16 0x8000000001000000040 0xb340815027f082000fa)) (.join (.leaf 16 0x8020000000000100000 0x16601840691) (.leaf 16 0x200040000400 0xad506bb049a))) (.join (.join (.leaf 16 0x800000000 0xaf1) (.leaf 16 0x400000010000000020 0x2d300c605ad)) (.join (.leaf 16 0x6000000 0xc6d09ca0440) (.leaf 16 0x400004000000100000 0x91306b8088a)))) (.join (.join (.join (.leaf 16 0x8000 0x8) (.leaf 16 0x10000000000 0x3e6)) (.join (.leaf 16 0x8000 0xbc1) (.leaf 16 0x0 0x0))) (.join (.join (.leaf 16 0x80000000000000 0x38c) (.leaf 16 0x401004000000008040 0x85f07830cb1025b0a1708ff)) (.join (.leaf 16 0x20000000000000000 0xd0c) (.leaf 16 0x8400000010000000020 0x49f033207c9055b))))))
set_option maxRecDepth 4000 in
private theorem scan5_0 : Region (clearPoint L5) 0 512 :=
  checkedPatch 0 patch5_0 gates5 (by decide +kernel) (by decide +kernel)
private def patch5_512 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x400 0xab7) (.leaf 16 0x8020000000000000000 0x2350d0f)) (.join (.leaf 16 0x820000000800000800 0x974077101aa040e0a8f098a) (.leaf 16 0x800000020 0x6b902d8))) (.join (.join (.leaf 16 0x10000000000 0x66c) (.leaf 16 0x0 0x0)) (.join (.leaf 16 0x1080000000100000 0x6c00643027e) (.leaf 16 0x0 0x0)))) (.join (.join (.join (.leaf 16 0x200000000000000 0x9e904cb042701a1) (.leaf 16 0x20000000800000000 0x8aa0224)) (.join (.leaf 16 0x1000000000000400 0x67504a4) (.leaf 16 0x0 0x0))) (.join (.join (.leaf 16 0xc000000000000 0xcde044101ca) (.leaf 16 0x400002000000 0xc3405940cd8)) (.join (.leaf 16 0x8000000010004000000 0xfd0a5e05ad02fa) (.leaf 16 0x21080000000100000 0x1700b7003f706ba))))) (.join (.join (.join (.join (.leaf 16 0x40000000 0x855) (.leaf 16 0x0 0x0)) (.join (.leaf 16 0x0 0x0) (.leaf 16 0x8001 0xaf40116))) (.join (.join (.leaf 16 0x80000002000000 0xb840ad3) (.leaf 16 0x20000000000100000 0xbfb050d)) (.join (.leaf 16 0x1000200000008000 0x64702ee00bc) (.leaf 16 0x0 0x0)))) (.join (.join (.join (.leaf 16 0x20 0x10) (.leaf 16 0x400080000040100000 0x3c30b70006200a3)) (.join (.leaf 16 0x820 0xb4806c50d1a) (.leaf 16 0x1000010002000020 0xa080850028906bb))) (.join (.join (.leaf 16 0x210800000000 0x80acb09a9) (.leaf 16 0x8000000000000000000 0x700)) (.join (.leaf 16 0x400 0x400) (.leaf 16 0x8400000000000008001 0xbbd0288039b08dc))))))
set_option maxRecDepth 4000 in
private theorem scan5_512 : Region (clearPoint L5) 512 1024 :=
  checkedPatch 512 patch5_512 gates5 (by decide +kernel) (by decide +kernel)
private def patch5_1024 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x0 0x0) (.leaf 16 0x800100000 0x855004f)) (.join (.leaf 16 0x0 0x0) (.leaf 16 0x0 0x0))) (.join (.join (.leaf 16 0x400000000000108000 0x1660c5e05b2) (.leaf 16 0x2004000000000400 0xc32082c0c3d0615)) (.join (.leaf 16 0x800000000000000000 0x6bc032d) (.leaf 16 0x0 0x0)))) (.join (.join (.join (.leaf 16 0x0 0x0) (.leaf 16 0x8000004020000000001 0x46f07710b1f043f0622)) (.join (.leaf 16 0x0 0x0) (.leaf 16 0x200000000000 0xca7))) (.join (.join (.leaf 16 0x0 0x0) (.leaf 16 0x10040000000 0x6ca05d0)) (.join (.leaf 16 0x20000200000000000 0x7690acb) (.leaf 16 0x400 0xc83))))) (.join (.join (.join (.join (.leaf 16 0x0 0x0) (.leaf 16 0xc0000020 0xd1c02e001980bb9)) (.join (.leaf 16 0x80000002000000 0x6bd056c) (.leaf 16 0x1004000800000000 0xb430a9e08a5))) (.join (.join (.leaf 16 0x108000 0x2920913) (.leaf 16 0x20000010800000000 0x4bf06340648)) (.join (.leaf 16 0x802000000 0x6810166) (.leaf 16 0x200000000000 0x14d)))) (.join (.join (.join (.leaf 16 0x0 0x0) (.leaf 16 0x4000000300020 0xbb10c1f091d01cc0783)) (.join (.leaf 16 0x0 0x0) (.leaf 16 0x100400 0x5fd0472))) (.join (.join (.leaf 16 0x4000000100020 0x4a40657030f) (.leaf 16 0x1004200004010000 0x1c50d3907f90ae606db037202a5)) (.join (.leaf 16 0x220000000000 0x3ac09ef06be) (.leaf 16 0x20000000040000000 0x710138))))))
set_option maxRecDepth 4000 in
private theorem scan5_1024 : Region (clearPoint L5) 1024 1536 :=
  checkedPatch 1024 patch5_1024 gates5 (by decide +kernel) (by decide +kernel)
private def patch5_1536 : Patch :=
  (.join (.join (.leaf 16 0x401080000000000000 0x6cf09f40d32) (.join (.leaf 16 0x200000000000 0x967) (.leaf 16 0x40000000000000000 0xac50797))) (.join (.join (.leaf 16 0x8020000000000000000 0xbd00196) (.leaf 16 0x8020 0x76f05a3)) (.join (.leaf 16 0x1 0x363) (.leaf 5 0x1 0x14d))))
set_option maxRecDepth 4000 in
private theorem scan5_1536 : Region (clearPoint L5) 1536 1637 :=
  checkedPatch 1536 patch5_1536 gates5 (by decide +kernel) (by decide +kernel)
private theorem rows5 : Region (clearPoint L5) 0 1637 :=
  (mergeRegion (mergeRegion scan5_0 scan5_512) (mergeRegion scan5_1024 scan5_1536))
private theorem clear5 : Clear L5 := clear_of_scan (by decide +kernel) (rows5)

private def L6 : Chart := ⟨6497, 7981929259, -2264, 92939, -2949315, -61192, 14552, 460⟩

private def g6_29 : Gate := ⟨29, 10, 0x13d122f3, #[
    0x1fffffff, 0xe020c7, 0xbc0548, 0xd69012, 0x4ceb000, 0x3842027, 0xa26982, 0x8b14a80,
    0xa0a88b, 0x1198c120, 0xa812548, 0x1a03407, 0x10d80928, 0xc844e20, 0x119a0224, 0xcc49101,
    0x109811c8, 0xd845240, 0x2c380b0, 0xa84a92, 0xcc4120c, 0x2834454, 0x688054a, 0x2810659,
    0x10e39010, 0x19900035, 0x15812025, 0x1e804a80, 0x3838c10]⟩
private theorem g6_29_ok : g6_29.OK L6 := gate_of_test (by decide +kernel)

private def g6_53 : Gate := ⟨53, 10, 0xd228fccfc512d, #[
    0x40000000, 0xa8f244918ae80, 0x163a60410c8d0b, 0xc054554b17481, 0x10788062a681e9, 0xc0633f8289301, 0xec86444cb1406, 0x28e00d406a37a,
    0x100aa70b112f9, 0x47396184628b, 0x109695558a1103, 0x624064d62c82e, 0xd8404a4bcb1c, 0x3d1c86860d062, 0x12028be640885b, 0xd41f269322408,
    0x1933af4813404, 0x3b8d42490566, 0x1e172472850242, 0x10410a4e721535, 0x1184c446e50932, 0x2904751172d24, 0x820526b46d093, 0xd8e11c1075c08,
    0x86280e9104b3d, 0x61e9f7109180, 0xdc10a5300fa21, 0xbe0194a107684, 0x11211df2f0c001, 0x1a4112e028c2bc, 0x75c10710e3610, 0x16c5ac94082c9,
    0x169d115c412824, 0x1214ec4464314c, 0x1509ce4a1041ac, 0x81429c49d0f42, 0x141248563b8066, 0x59025eb993020, 0x48992c9f05610, 0x2204cfa2809da,
    0x160c2c2717846, 0x1a7a4a40436038, 0x268d64c048c74, 0x110a35552d21c0, 0x8c430d39c40d1, 0x911a1caa0109f, 0x18ac05600e285e, 0x51a6444c26e60,
    0x192283f98c0680, 0x102ca8c023c197, 0x5d1a554540681, 0x16261040cb8dd0, 0xea312449e2a01]⟩
private theorem g6_53_ok : g6_53.OK L6 := gate_of_test (by decide +kernel)

private def g6_59 : Gate := ⟨59, 9, 0x22b62183e7b92bb, #[
    0x4000000000, 0xabed6b569b1438, 0x5f16651bc447327, 0x67c194ce19c734d, 0x652f0e487bdeac0, 0x64df16725c961b4, 0x207a4e34b7a0fad, 0x19a0edafa8a6acc,
    0x37e89da410a5d97, 0x1b91df02f6ecc82, 0x5768478f61a4d69, 0x105ce45ef8e23f2, 0x5904bf89e63145f, 0x5d4d161dfd80a33, 0x83d9cf1b55b1a3, 0x3d311d88ed48add,
    0x1832f6d32e28eab, 0x365e0cf88bc7f20, 0x68f4f5c0091f6f1, 0xbf47639a4ba896, 0x1824a77897cda8f, 0x43d834762e75d32, 0x7c1d0eae5d1d509, 0x280fe6dfac5d211,
    0xe137572badf0d0, 0x1570faa95ee347, 0x1440cd0a5edfdcd, 0x5a6736f53252a34, 0x76da569d4a53446, 0x9a9e76060d8e7f, 0x60c0dcf2b23f9c6, 0x4a572d4b6dd88b2,
    0x4995ed9ccb4b152, 0x6f4a1660452cefe, 0x752abe1d5038b1d, 0x6ba9d5d90e02c3e, 0x46bf6cfe02a212e, 0x174eae1707e42ae, 0x4e8dc58378532eb, 0x7d23dca4833c56c,
    0x24b38dc5fa1a457, 0x120075e5e2e3dbe, 0x7a23e60f4d813f8, 0xe996de983355c5, 0x56e2371197aed44, 0x55b1e7378231636, 0x37f70d165773140, 0xcf23fa4137e8a3,
    0x63ef44e74113f11, 0x30de3c42dd65ac9, 0x6de81f713b104cd, 0x2104b722fdba6e9, 0x22beb6e0b30cd59, 0x3da58e4bc0ad7c1, 0x2749cd1f64cb61a, 0x7bc24e1e94c0d5e,
    0x730e65307cecb38, 0x447b14cd1f79338, 0x32d5ad6faa070a3]⟩
private theorem g6_59_ok : g6_59.OK L6 := gate_of_test (by decide +kernel)

private def g6_47 : Gate := ⟨47, 10, 0x7bcae4d8ac21, #[
    0x7fffffffffff, 0x1197abd71c06, 0xdea227a98bc, 0x1fe82acad90c, 0x27213560af37, 0x52ebf02b0e94, 0x670423629777, 0x5ba5b822b43a,
    0x315c3cdce152, 0x6504abe6bb41, 0x237bac41326d, 0x60616d28d7dc, 0x4d4747de172, 0x2a15ed2649cb, 0x34ca3f113476, 0x476b2c4d1663,
    0x5a846e92da93, 0xd4a70f329bc, 0x1596622fe1b2, 0x50fbf0334b09, 0x3e3a73c4c059, 0x31ce3f8c9072, 0x645de7c96203, 0x2849f908df1d,
    0x5884fc90ab8f, 0x349f3dd13c04, 0x498fe39c64e0, 0x191e72e3e9a0, 0x16607ef8590d, 0x3fa2334d44d8, 0x2678729583d9, 0x5a4bb10adc95,
    0x4591a6b71c66, 0x6447e29966e2, 0x1325bd42ad39, 0x3df1715904e8, 0x58a5b43033be, 0x6411aef62b64, 0x6b3ea905382d, 0x39d9e1d464a8,
    0x6a20ed2ed5c2, 0x4a3621073eee, 0x6a07eba5297, 0x283564272ecf, 0x5a9aa0bfc309, 0x4af222bd83d1, 0x475eaf4c4603]⟩
private theorem g6_47_ok : g6_47.OK L6 := gate_of_test (by decide +kernel)

private def g6_43 : Gate := ⟨43, 10, 0x35883a3ee53, #[
    0x40000, 0x2f0bd09e8d5, 0x1f66232fd12, 0x559322873ee, 0x703094bbdf4, 0x3354fd0c17a, 0x3e9a9988f49, 0x15aaef292d4,
    0x2ba64b9517c, 0x28cbe632579, 0x63fdc683c88, 0x69dbc92f442, 0x330d27ab21f, 0x4bf8259a7d0, 0x1b735499a63, 0x693e3cb0e46,
    0x72eb1726e60, 0x55ebbc96418, 0x37f87234386, 0x2385393deb8, 0x4d485b02bfe, 0x68e7f18e305, 0x17418e31fce, 0x32ffa81b425,
    0x443af793943, 0x6cc38589c3f, 0x2a304d27baf, 0x4e0cec9d1ae, 0x16c4e1a78f9, 0x598cb32559d, 0x5217cb3483f, 0x4df09abc961,
    0x16845e927b7, 0x4622782c77f, 0x153d498cfa6, 0x547d153a4cb, 0x2856929eeab, 0x7d25e2332b2, 0x4cbd0617e55, 0xe5f7ba5218,
    0x2aef9c28993, 0x78917e988cd, 0x75562f217a1]⟩
private theorem g6_43_ok : g6_43.OK L6 := gate_of_test (by decide +kernel)

private def g6_31 : Gate := ⟨31, 10, 0x121d47b7, #[
    0x7fffffff, 0x50296fb4, 0x3649b2aa, 0x2c5328d7, 0x131a7963, 0x755c7038, 0x4c7c6703, 0x6399338c,
    0x5a34ba58, 0x47e22ba8, 0x1f81f911, 0x1d7eb81, 0x2a95a5a9, 0x37f62424, 0xb49687e, 0x5833e60d,
    0x6d833e60, 0x43f0b496, 0x3121237f, 0x54ad2d4a, 0x40ebf5c, 0x6444fc0f, 0x8aea23f, 0x68d2e962,
    0x198e64ce, 0x4e0731f1, 0x38e071d5, 0x2634f2c6, 0x5758a651, 0x32aa6c93, 0x296fb4a0]⟩
private theorem g6_31_ok : g6_31.OK L6 := gate_of_test (by decide +kernel)

private def g6_23 : Gate := ⟨23, 11, 0x7acca1, #[
    0x7fffff, 0x3a5233, 0x46938e, 0xe457c, 0x346b25, 0x2c25f4, 0x5eb811, 0x28692f,
    0x121ccf, 0x78864d, 0x7a8c19, 0x46551e, 0x54c5e2, 0x62be60, 0x423ec9, 0x7093cc,
    0x2c2bd2, 0x3af620, 0x4868be, 0x2c5a93, 0x44e0fa, 0x12c5c7, 0x14bb31]⟩
private theorem g6_23_ok : g6_23.OK L6 := gate_of_test (by decide +kernel)

private def g6_19 : Gate := ⟨19, 11, 0x4f50d, #[
    0x20000, 0x49ae3, 0x170b7, 0x418df, 0x19ed4, 0xe9e9, 0x145f5, 0x5323b,
    0x1e4ea, 0x524de, 0x57b24, 0x45727, 0x5dc4c, 0x4afa2, 0x9797, 0x42b79,
    0x1fb18, 0x4ed0e, 0x1c759]⟩
private theorem g6_19_ok : g6_19.OK L6 := gate_of_test (by decide +kernel)

private def g6_11 : Gate := ⟨11, 12, 0x5c5, #[
    0x400, 0x5aa, 0x4d9, 0x473, 0x696, 0x7c1, 0x60f, 0x5a5,
    0x738, 0x66c, 0x556]⟩
private theorem g6_11_ok : g6_11.OK L6 := gate_of_test (by decide +kernel)

private def g6_7 : Gate := ⟨7, 13, 0x17, #[
    0x7f, 0x64, 0x70, 0x4a, 0x54, 0x43, 0x49]⟩
private theorem g6_7_ok : g6_7.OK L6 := gate_of_test (by decide +kernel)

private def g6_37 : Gate := ⟨37, 10, 0x9a1dee165, #[
    0x1fffffffff, 0x1a72db2136, 0x1e79e49524, 0x8fe27168e, 0x1ac35c3761, 0x1f2a7c6498, 0x1d2e077dc, 0x1ace6bc243,
    0x122f44f2a7, 0x15b76d4330, 0x7ab57864c, 0x1bababb108, 0xfc003f3ae, 0x10a88a87ff, 0x29dee50d6, 0x19195313db,
    0x12570ea4dd, 0x146c71b15e, 0x168b3345b5, 0xd16d6d166, 0x362bd46c7, 0xea4dd92b8, 0x989ede465, 0x1b9435853b,
    0x1150fff0a8, 0x3f3ae7e0, 0x1d5d8846ea, 0xd5e1930f5, 0xeda86615b, 0xf44f2a791, 0x735e121eb, 0x14b81df703,
    0x54f8c931f, 0xc35c3761d, 0x7f138b472, 0x19e7925493, 0x14e5b6426d]⟩
private theorem g6_37_ok : g6_37.OK L6 := gate_of_test (by decide +kernel)

private def g6_3 : Gate := ⟨3, 14, 0x5, #[
    0x7, 0x1, 0x2]⟩
private theorem g6_3_ok : g6_3.OK L6 := gate_of_test (by decide +kernel)

private def g6_61 : Gate := ⟨61, 9, 0x8ec196bf5a60dc5, #[
    0x400000000, 0x1e17645d8755f37e, 0xfac2cfef2ad466e, 0x1e29e76d3a368ff4, 0x994b5f7b5eb99b4, 0x3fd7caf9f09a867, 0x1707efbcc3f909c7, 0x64596cf67bb7e87,
    0x1b4e5f6dd1c6d731, 0x15b9fc64559bfbe0, 0xf7611b5f85feab2, 0xf63fa36891b93bf, 0x1d175bd4be2b557a, 0x1df0f29f978547e3, 0x18efb615ed2d7173, 0x16460ef7df21afd9,
    0x6dded3c5eca74ad, 0x198bfbdf3459b0cb, 0x1ffe2fa40666dad3, 0x17aed9df18367c1e, 0xae2736c75fa2e7d, 0x17e6762fb4f8d49a, 0x1f592b6fb8ba685b, 0x122bc8ff456be5b7,
    0xcd9dcee33f7033b, 0x1ebeaa8639df38b5, 0x1dc1baf57ae7fa04, 0x42c7add6d53df5b, 0x19ed08ec7f94e9be, 0xdb7c62dd867b5cd, 0xa37bfcf5e7d6128, 0x10d7cf5e7fbd8a14,
    0x15bcc3768c7db6b3, 0x12e53fc6e216f37d, 0x1f7956d76bc684da, 0xbfcebd5ebb07720, 0x39f738c2aafafad, 0x181df98ee77366dc, 0x14fad45fe27a89ed, 0x2cba3beda935fda,
    0x563e5be8dccfd59, 0xe8bf5c6d9c8eabe, 0x7cd831f736ebd78, 0xb6ccc04be8fffcb, 0x1b3459f7bfa33d3, 0x5ca6f4796f76cb5, 0x1eb09f7dee0c4d9b, 0x11d696f50dbee3ce,
    0x1c543d3f29e1f7c7, 0x155a8fa57b5d175e, 0x193b122d8bf8defd, 0xaff43f5b10dde4d, 0x1bfb3544c7f3b507, 0x1d6c7176df4e5b8c, 0xfdbbcde6d344ce1, 0x1213f867befc1de3,
    0x2b21f3ea7d7f8e6, 0x133af5bdf5a5322d, 0x1e2d8b96dcf28f2f, 0xc56a9efe686be76, 0x19f55c3744dd0f7e]⟩
private theorem g6_61_ok : g6_61.OK L6 := gate_of_test (by decide +kernel)

private def g6_41 : Gate := ⟨41, 10, 0x4c7d4af8c9, #[
    0x1ffffffffff, 0x18ab7be33df, 0x1a1393edfbf, 0x1267bcf9b5f, 0x1b28ebf2ebf, 0x1deadbfade, 0xba5a7d9feb, 0x19b7e7fca3a,
    0x1bc33a37bbf, 0x1aec5cdff6a, 0x2fef739be5, 0xb663ecdff5, 0x19f1aefb27d, 0x137f1f24ff9, 0x1af96757a77, 0x187af57feb2,
    0x13dea3e3fba, 0xbdbdda43ef, 0x19bfbe8e763, 0x139bbd5f5b6, 0x3b5f7bf4dc, 0x183b2fdefad, 0x196dafabdd9, 0x13c6e717dfd,
    0x1af7c25bbdb, 0x195dfc7c57b, 0x34d7feaf5e, 0xbee5eae69f, 0x199ff24f8fe, 0x13be4df758f, 0x1aaffb37c66, 0x8a7d9cef7f,
    0xb56ffb3a37, 0x1bfddec5cc3, 0x135c53fe7ed, 0x1ad7f9be5a5, 0x107b5fdb57b, 0x1bfd74fd714, 0x9fad9f3de6, 0xbfdfb7c9c8,
    0x3fbcc7ded5]⟩
private theorem g6_41_ok : g6_41.OK L6 := gate_of_test (by decide +kernel)

private def filters6 : List Gate := [g6_29, g6_53, g6_59, g6_47, g6_43, g6_31, g6_23, g6_19, g6_11, g6_7, g6_37, g6_3, g6_61, g6_41]
private theorem gates6 (g : Gate) (h : g ∈ filters6) : g.OK L6 ∧ 512 ≤ g.p*2^vDepth g.p := by
  simp only [filters6, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨g6_29_ok, by decide +kernel⟩
  · exact ⟨g6_53_ok, by decide +kernel⟩
  · exact ⟨g6_59_ok, by decide +kernel⟩
  · exact ⟨g6_47_ok, by decide +kernel⟩
  · exact ⟨g6_43_ok, by decide +kernel⟩
  · exact ⟨g6_31_ok, by decide +kernel⟩
  · exact ⟨g6_23_ok, by decide +kernel⟩
  · exact ⟨g6_19_ok, by decide +kernel⟩
  · exact ⟨g6_11_ok, by decide +kernel⟩
  · exact ⟨g6_7_ok, by decide +kernel⟩
  · exact ⟨g6_37_ok, by decide +kernel⟩
  · exact ⟨g6_3_ok, by decide +kernel⟩
  · exact ⟨g6_61_ok, by decide +kernel⟩
  · exact ⟨g6_41_ok, by decide +kernel⟩

private def patch6_0 : Patch :=
  (.join (.join (.join (.join (.leaf 16 0x9002000012042008421 0x2c4064b74a29208c0a45413f38636bad67bc5a6f2cb20a836e636c9d05121654279638d8) (.join (.leaf 16 0x104a208404000c000020 0x618c3e1c1fa861035e9026a125cf03ee5b7a08403df53e8349a637ee04b501c35d7f57232a81176d14660e0e2a76) (.leaf 16 0x84000c010808308400 0x42512fe568a613106ccb3d191c2a04d760ce6b52224118d21845520d3779203507511c14))) (.join (.join (.leaf 16 0x20803008000080118425 0x675059052b5f0dd34360259962db368f0678146a12c643123e65442e4d8428000db24d592c375a744f334b8937042aaf) (.leaf 16 0x401004030850008040 0x49d957330baa6b42361a0792688048036db4511648b5417c393024871a3516b50423522a19db)) (.join (.leaf 16 0x463084003000500421 0x526b48a425e409524bca310926f2444c57a330051e6011c9054f02ee0233542d50c7415a35a525db2fa3482f5c89) (.leaf 16 0x30423180611100100465 0x655c64a75e3357674ef40af60d5126404d4c43f234bb3a0c2a670fb822291c3c08da4f8439ea204362301f531b2d172861da1f96529b262b16fb658e5e3a35301edf1c86)))) (.join (.join (.leaf 16 0x8c22100011006108001 0x51e7459b1de617490ed14de8125a695828ec344656ef3c8249cc1ee718d53d9f141c458d) (.join (.leaf 16 0x410a8211800108800 0x65461258572e49956954589255434a204661398827a725291dff1036565c485d526924e8036f33d14cc06b7c552f) (.leaf 16 0x31002018c8030085 0x5ada3f4332e7532c36dc065023a316980b3167dd62fd211570c93757076f07515eaa416532081d9917fb12f55e6b3f9312f3042070eb335c2aa318c10e5d))) (.join (.join (.leaf 16 0x94000002b0880300c80 0x3b406acd49c92732052b03e8617d6f8268b651994d5949dc42ed411f3272263d202f12de65084eff4e0946b7266e0ae164895786497f479e2e5d1d6e0ec2) (.leaf 16 0x81008240104108000 0x5ca33388261c106d6bfe587012f01b3d5ebc293a150c0beb60854fc04f273c7f4983273931fd3112)) (.join (.leaf 16 0x48822484210804220803 0x686f66d95f3a5efb52c449d139e035bf02503afc07ae1b8d311305ce6c19677e62e6599e49d82d3a0adb06f405442c0d1857300d6a0235f5190317790654702a6c5c25bf15f46c5e137e318804e60034) (.leaf 16 0x860084c500c4012001 0x65101a156b7a5d7c331317b913a85db459c15979574e361224ed67a161c04f0c309e21b73b40267f1bf62371151856d30bac66b7665964e94e1d38b931570b7a06f96630))))) (.join (.join (.join (.leaf 16 0x860090220080210021 0x4701402c43ba12c9129017a671956bdb5ac004f66a1e4266297368350c193029127958f9433962df5242) (.join (.leaf 16 0x4050804300c0010022 0x6af662d1525e2f3f150f02f46e20138a0a7862f8505914d770f31d39190066dd64c248c935f72fb4) (.leaf 16 0x8c0210001084c128021 0x33c36bfa549910f81845097b1da609522eca6ea460a83771348c1e5f1db00e22039a71866b5518cc16b314610a3b602b22fb))) (.join (.join (.leaf 16 0x800008c001846d00081 0x493018576cd92ef708f7683c36f60fed5a5246aa1ac4159971ae5b6853ea4fd73c193a382e55216b1676117a0b43032603015b344af51f00184957e2) (.leaf 16 0x402004410180110864 0xe6e2d6b095235d671170c1248c1569f49f238cd2b3802eb025a4ecf647500d1464e2ca15f79196b042c52692de01c6e11fd)) (.join (.leaf 16 0x1204621084008c00 0x70a7556c4ed3480c2698375755aa4662102f45ae2cf63b980ca36d8034e03c0e155a695749412e2f2bdd) (.leaf 16 0x64100c32842201c61 0x46aa43122d616526633a3379145922861f8671506e83591437fc13210685600f5496140471ac633458ca45ba01100493162c5a262c81660365eb566443ef23e2032d02043c7436af0d854573)))) (.join (.join (.join (.leaf 16 0x8425080e00802018409 0x6bb43da818c95aba4e81472d2b97158c01db6d0a640c5aea439e3a9002ab01934047471154be47aa43861d956a5a61da5ef75ae04d0249662c0c13a20786) (.leaf 16 0x4308c01088a008040 0x469f223366a86576402619435a2e4933159a2b223e2c294c0c9943d641bc38f532852b4b53883f2b017b)) (.join (.leaf 16 0x200146018021004a2 0x27825fb35f2132532e38136056833da827d03d0c2601212f58ce2aad03b73eb3369c25e7098a09146e11199c) (.leaf 16 0x8001104220884000422 0x5b4829c357b230bb33125da6690138bf568b229f12a67048393d561d5a0f2a3809c9))) (.join (.join (.leaf 16 0x20010044500c6108821 0x6cb061735aca583f3ae832a618bd05453d200acf6c8a0e2267673c81294e0e2f022d66695ad8219c47fe35a602791f424299474131b94b312742) (.leaf 16 0x2004002840700061 0x3da814260e0a6fc05e865aa64aca2ac720896362389a325f2b7b29d628d909416b0f5fee4ee56eb3)) (.join (.leaf 16 0x8822184800800048c25 0x3455565309675ea7389b27ef655330f720502d4e527f4bfd2468143762f468c3681053d54d092d8d0cb906500213004b334c110210274233654028640e390a9608b9) (.leaf 13 0x2180011844000002 0x505511cd5c803c931915277a627d20bf129d4d9a6c7828476bac218d))))))
set_option maxRecDepth 4000 in
private theorem scan6_0 : Region (clearPoint L6) 0 461 :=
  checkedPatch 0 patch6_0 gates6 (by decide +kernel) (by decide +kernel)
private theorem rows6 : Region (clearPoint L6) 0 461 :=
  scan6_0
private theorem clear6 : Clear L6 := clear_of_scan (by decide +kernel) (rows6)

private def L7 : Chart := ⟨6497, 20910520237, -319918, -333217, 441329, -397560, 4055, 3157⟩

private def g7_29 : Gate := ⟨29, 9, 0x13d122f3, #[
    0x1000000, 0x1d64188, 0x1791c10, 0x1ac106c, 0xb156101, 0x58c405c, 0x146da01, 0x13621c10,
    0x5211136, 0x132b8240, 0x11427a10, 0x3412a26, 0x9901471, 0x9181c52, 0xf142409, 0x11e90242,
    0x1124a381, 0x1328e280, 0x5864548, 0x51085e4, 0x990241d, 0x946c888, 0xd908384, 0x50805b6,
    0x343a023, 0x11a8086a, 0xb036083, 0x1d008389, 0x17011826]⟩
private theorem g7_29_ok : g7_29.OK L7 := gate_of_test (by decide +kernel)

private def g7_53 : Gate := ⟨53, 8, 0xd228fccfc512d, #[
    0x8000000, 0x5f284880f525, 0x14cc124c08115f, 0x181258aac9e030, 0x424c75f105850, 0xb14c00991c5e2, 0x12281c89ca092e, 0x17150b5c085803,
    0xf02e62ab02412, 0xad2c20a21d88a, 0xa4550186d213a, 0x151813c9620a86, 0x12e19592e0cc0, 0xcb0305a962650, 0x508a23f150913, 0xd3202a9ec4c4,
    0x1ac28498dda004, 0x8207d0f46101b, 0xf018118c4d12e, 0xb023bc522ab0, 0x12241538469a31, 0x1a2f394b08200c, 0x131aa593381c0, 0x18ef0889814183,
    0x1696228218ed4, 0x32246be9090c8, 0x10f04628d86780, 0xf30d8a310784, 0x98484beb12260, 0x15b8c20a234b40, 0xc140c8887b8f, 0x1c0e64d2ac640,
    0x180208694e7a2c, 0x62cb10e541226, 0x6aa251ee20680, 0x1a45918c40c079, 0xc0431785f020b, 0x1002dd8c90a1ac, 0x1191bcaa026580, 0x448547e228853,
    0x53234ad060698, 0x1983a4d4c3a40, 0x10a82349e40c55, 0xe425b0c055129, 0x88dc22821a5a9, 0x41206aa33a079, 0xd081d685477, 0x1a4829c89c0a25,
    0x3d1c4c8019469, 0x50d047d719210, 0x603c9aa8d240c, 0x1d440819241997, 0x125780890a7d02]⟩
private theorem g7_53_ok : g7_53.OK L7 := gate_of_test (by decide +kernel)

private def g7_59 : Gate := ⟨59, 8, 0x22b62183e7b92bb, #[
    0x80000000000, 0x702e95cd8429fc7, 0x8ec9777a1f7c02, 0x3f608cd35cd02dd, 0x3df1d72a2a6a981, 0x7e62d289864c57b, 0x2d1080e5b71b77e, 0x3ab5ae44dd55928,
    0x6b46e63e08995cd, 0x22c3ec1dcbb4c27, 0x690da319d4d7d52, 0x1b7bc04f296566a, 0x5214d151fd639e6, 0x2299b3e1a80dc7f, 0x1b339cb86421f3b, 0x3469b9d2e9ec0ac,
    0x243cb93d0fbd11c, 0x4d8ade85b376198, 0x745bada043f3a19, 0x27b7e879a6053c2, 0x5b3dd1b12c7b26, 0x558eea29eb1c354, 0x3bcbb14164ea59c, 0x239dadf7026a839,
    0x1360f6176346eba, 0x1ea3cdc5a796429, 0x2879f0bfd53899, 0x24acd7bd520c5f8, 0xa4a97f0ded0796, 0x30a8f1de13790e7, 0x3dc78a86e709ec8, 0x7f4a92869e0b7b,
    0x5ef59a921fa304a, 0x687cf0a0991cabf, 0x51d9e2bc94269e5, 0x743783645d762c6, 0x77dadce29c15640, 0x4146e9ee39a5726, 0x4a2bb8d52ac38d7, 0x6c5de6d064de348,
    0x4f0bf6f243ca065, 0x2daed17985cfc2, 0x50bda8d91986ecd, 0x5e4e9e12388bdf0, 0x25cecb163503797, 0xe9ce66cdcf8426, 0x43e6cca2fe3b015, 0x45459425679c6bf,
    0x7901ef6c566a694, 0x4c62d84b4abeb2b, 0x5c1be1a2e432dd3, 0x3e33b16bb3a9910, 0x113ad6ae149aabb, 0x5380845a7eed8ed, 0x48a5a33fdea3261, 0x2a75c7de8195654,
    0x6598837ebb40b3a, 0x77749b88403ef85, 0x59d4ba07e3f9421]⟩
private theorem g7_59_ok : g7_59.OK L7 := gate_of_test (by decide +kernel)

private def g7_47 : Gate := ⟨47, 8, 0x7bcae4d8ac21, #[
    0x2000, 0x256f1ac76a0b, 0xb36c1b9e770, 0xb4177e1a9c7, 0x540a2e5af1ed, 0x17d3350f6c89, 0x68fea45b221b, 0x4335359b702f,
    0x73e59b22ac4a, 0x6fa009ea6aad, 0x298c13fdb2d2, 0x747435752e58, 0x2595ce2d7564, 0x285d971663f4, 0x39df0a78f910, 0x5608d6e178f9,
    0x4b3970776394, 0x3796ef03a894, 0x134fe774e222, 0x7c1180d7ef43, 0x4c3aee9e2d22, 0x485cebe56c29, 0x6d89f98973a0, 0x181d2dcce9ce,
    0x52e0639cb99d, 0x7e46d82e748c, 0x5ce84ca1b53e, 0x5d70ca25a3cb, 0x620fe17bf58, 0x1fcb22223977, 0x5da7b148ae07, 0x3a73494e3770,
    0x2c41acf8f43b, 0x43ee7044f8f2, 0x26e8517e3347, 0x4ea6913575a3, 0x30b8b8d3a575, 0x20c6525a6dfe, 0x4017ddaab2bc, 0x669f3a91aa26,
    0x32b30fa076cd, 0x15fc5ec226d1, 0x332fa489b785, 0x5140adbc7ad3, 0x3a0b471cac3f, 0xdb340773cec, 0x63da9682b71a]⟩
private theorem g7_47_ok : g7_47.OK L7 := gate_of_test (by decide +kernel)

private def g7_43 : Gate := ⟨43, 8, 0x35883a3ee53, #[
    0x7ffffffffff, 0x1b91ce3a60e, 0x297a16f61a1, 0x5b00ed8b333, 0x108e6e9b54e, 0x7ba10d8e456, 0x3e3db472828, 0x34f7ec6a204,
    0x4b7a30a68dc, 0x785a01a7763, 0x4479f47e481, 0x3690ca8f7c8, 0x33885fc2751, 0x690a1d27e96, 0x2a685b27535, 0x59ce099e931,
    0x47c1265b746, 0x67c833aac31, 0x5015f60b9ec, 0x5d4c8b8350f, 0x2a8d0bab5c3, 0x1125aacbb47, 0x6922716e9aa, 0x2c5561d6ae8,
    0x4caef8560e8, 0x6a029bce837, 0x4f9c61aae6, 0x20f8b176d32, 0x1ce6c64bcc8, 0x595565726d, 0x1425b4bf25c, 0x47345721fd,
    0x425b09f78a9, 0x6788c093f17, 0x1687e3772c0, 0x17b49d8b286, 0x7bcb1022b1b, 0x6f1f0a0a716, 0x2177b5138d8, 0x1c423956cbb,
    0x4036e6668db, 0x17a542c37b4, 0x62763832e39]⟩
private theorem g7_43_ok : g7_43.OK L7 := gate_of_test (by decide +kernel)

private def g7_31 : Gate := ⟨31, 9, 0x121d47b7, #[
    0x7fffffff, 0xd2e962d, 0x6d833e60, 0x1c663993, 0x7da50296, 0x457511f8, 0x785a4b43, 0x1c0e63e3,
    0x29b24d95, 0x1113f03f, 0x48dfd890, 0x6071d571, 0x314ca35d, 0x81d7eb8, 0x29552b4b, 0x79632634,
    0x34f2c64c, 0x54ad2d4a, 0x4081d7eb, 0x146bac53, 0x7038eab8, 0x589091bf, 0x444fc0fc, 0x6caa9b24,
    0x1cc7c67, 0x50fc2d25, 0x7511f88a, 0x2df6940a, 0x31cc99c6, 0xdb067cc, 0x258b4697]⟩
private theorem g7_31_ok : g7_31.OK L7 := gate_of_test (by decide +kernel)

private def g7_23 : Gate := ⟨23, 9, 0x7acca1, #[
    0x7fffff, 0x22c25f, 0x751833, 0x24f338, 0x7d44e, 0xe8d27, 0x6a1a4b, 0x262f15,
    0x762075, 0x66252e, 0x15a359, 0x78864d, 0x47d930, 0x6a4d62, 0x19ba52, 0x1bd702,
    0x19547a, 0x15e92c, 0x5c7258, 0x783915, 0x490e67, 0x2be60c, 0x517d21]⟩
private theorem g7_23_ok : g7_23.OK L7 := gate_of_test (by decide +kernel)

private def g7_19 : Gate := ⟨19, 9, 0x4f50d, #[
    0x100, 0x7278a, 0x637e0, 0x17971, 0x517d4, 0x4ed0e, 0x54937, 0x1c9ae,
    0x19771, 0x6a19e, 0x6f30a, 0x11dd3, 0xeb27, 0x3d925, 0x2e16e, 0x257d1,
    0x11d3d, 0x60fd8, 0x6a3c9]⟩
private theorem g7_19_ok : g7_19.OK L7 := gate_of_test (by decide +kernel)

private def g7_11 : Gate := ⟨11, 10, 0x5c5, #[
    0x7ff, 0x1c6, 0x3e0, 0x499, 0x2a9, 0x496, 0x496, 0x2a9,
    0x499, 0x3e0, 0x1c6]⟩
private theorem g7_11_ok : g7_11.OK L7 := gate_of_test (by decide +kernel)

private def g7_7 : Gate := ⟨7, 11, 0x17, #[
    0x7f, 0x54, 0x4c, 0x7, 0x1c, 0x26, 0x25]⟩
private theorem g7_7_ok : g7_7.OK L7 := gate_of_test (by decide +kernel)

private def g7_37 : Gate := ⟨37, 8, 0x9a1dee165, #[
    0x1fffffffff, 0x1556c21bb3, 0x6f3c2b227, 0x6ee72c3a8, 0x16174a939e, 0xc9ee48b71, 0x13f27413ca, 0x93dcd62f0,
    0x6f4eb3384, 0xc807f53c7, 0x7dbd0cb09, 0x1238f57274, 0x16b87660ae, 0x9cfc8951b, 0x176fc14c70, 0x4c77a1d2b,
    0x16e159169e, 0x1824d53cd7, 0x2a85fde4c, 0xf7f42a832, 0x7956483eb, 0xd1350ed79, 0x170bdc64d4, 0x6507edd0e,
    0x15227e72d8, 0xcdc3ad75, 0x9d5e3892e, 0x1a617b7c90, 0x195fc026e3, 0x199ae5ec21, 0x8d677920f, 0x1905c9f953,
    0x1a24ef268e, 0x192a5d0d79, 0x1869ceec15, 0x9a879ece4, 0x1b086d55cd]⟩
private theorem g7_37_ok : g7_37.OK L7 := gate_of_test (by decide +kernel)

private def g7_3 : Gate := ⟨3, 12, 0x5, #[
    0x7, 0x1, 0x2]⟩
private theorem g7_3_ok : g7_3.OK L7 := gate_of_test (by decide +kernel)

private def g7_61 : Gate := ⟨61, 8, 0x8ec196bf5a60dc5, #[
    0x20000000, 0x1dd7330e47bedf0a, 0x197d02e4d4fe6fe3, 0x16c3fab3da137877, 0x1477f487d8c7fee0, 0x1b5f6d2d50f0dab7, 0x1f623d3fcf34097d, 0x3f3e11d5a3d3dde,
    0x1dd654aace07c5ff, 0x8fc6ed916efa65d, 0x13cc679dd946fd47, 0x16f1cfcc57e95c3c, 0xac93ffbd7ed2981, 0x77ee7c7c6b27127, 0x5595bdc8b756bdd, 0x433b8f5d70d8fef,
    0x18937777d6f445ae, 0xaeef7de1a54cba9, 0x6b69b5918b7f6af, 0x13e77aae91e1eb8e, 0x15fb1a9fcb5c94a7, 0x121eddf31feb9266, 0x13fa87d0cdbfe25c, 0x1f952fd4937a3733,
    0xeebea2b99beb2c9, 0x1aedb64785d399e7, 0x15ab84bf85e77d35, 0x1f4dcd66c43b9fb8, 0x1e6fdbd3066cf8cc, 0x1d1cba68dbf9bce8, 0xa57fcdf8ca943db, 0x16de14a98fd9ff52,
    0x18b9ecfed8b2e9c5, 0x1998f9b3065edfb3, 0x18efcee11b359d97, 0xd65f73d0fe90ead, 0x1f3cce5d0f136dba, 0x149a6beccea2bebb, 0x1e6762f6495fa54f, 0x9d23fed985f0afe,
    0xb324ebfc67ddbc2, 0xf2949d69fcac6fd, 0xb8ebc3c4baaf73e, 0x7ab7f68c4d6cb6b, 0x14ae9952c3df7bba, 0x1bad117b5f777648, 0x7bf8d875d78ee61, 0x5deb57689ded4d5,
    0x724726b1f1f3bf7, 0x140ca5bf5effe49a, 0x9e1d4bf519f9c7b, 0xf15fb14ddcf319e, 0x15d32fbb44dbb1f8, 0x1ffd1f039aa9535d, 0x3dde5e2d5c43e7e, 0x1df481679fe5e237,
    0x1f6ad87855a5b7d6, 0x83bff18df097f71, 0xf70f642de6afe1b, 0x1e3fb3f9593a05f4, 0x1a87dbef1386675d]⟩
private theorem g7_61_ok : g7_61.OK L7 := gate_of_test (by decide +kernel)

private def g7_41 : Gate := ⟨41, 8, 0x4c7d4af8c9, #[
    0x1ffffffffff, 0xe0fde6fbc7, 0x1e556ff8bf1, 0x1bb642d7fdd, 0x1f48cddf2bf, 0x1ea55b9a7fe, 0x13b7df59537, 0x1f3bf78c5ea,
    0x1bdd246d7df, 0x6de773e37d, 0xb661dddf6f, 0x1fac37f17e3, 0x13e39badbfc, 0x1777adb92cf, 0xad2b3fecef, 0x1f9ef93dc74,
    0x16f9bdd35d5, 0x1b1d3ebf8b7, 0xf7caf1fdb8, 0xfffc5aaf31, 0x13db5f14fdb, 0x1e76fca3eb6, 0x1fa33d568ff, 0x17876fe3d4f,
    0x6fb47f5f2e, 0x1b6aeb2ef67, 0xfcb8ef27de, 0x1abdcdff352, 0x177cd276d7b, 0x1e4ff6d7671, 0xff1fa3fb0d, 0x16bdbeeee19,
    0x1b2fb1f3b9e, 0x1efefad892e, 0x7d5e8c7bf7, 0xe7b2a6befb, 0xbdff9676a9, 0x17ff53eecc4, 0xeeeffad09b, 0x13e3f47fdaa,
    0x3b8f7d9efc]⟩
private theorem g7_41_ok : g7_41.OK L7 := gate_of_test (by decide +kernel)

private def filters7 : List Gate := [g7_29, g7_53, g7_59, g7_47, g7_43, g7_31, g7_23, g7_19, g7_11, g7_7, g7_37, g7_3, g7_61, g7_41]
private theorem gates7 (g : Gate) (h : g ∈ filters7) : g.OK L7 ∧ 512 ≤ g.p*2^vDepth g.p := by
  simp only [filters7, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨g7_29_ok, by decide +kernel⟩
  · exact ⟨g7_53_ok, by decide +kernel⟩
  · exact ⟨g7_59_ok, by decide +kernel⟩
  · exact ⟨g7_47_ok, by decide +kernel⟩
  · exact ⟨g7_43_ok, by decide +kernel⟩
  · exact ⟨g7_31_ok, by decide +kernel⟩
  · exact ⟨g7_23_ok, by decide +kernel⟩
  · exact ⟨g7_19_ok, by decide +kernel⟩
  · exact ⟨g7_11_ok, by decide +kernel⟩
  · exact ⟨g7_7_ok, by decide +kernel⟩
  · exact ⟨g7_37_ok, by decide +kernel⟩
  · exact ⟨g7_3_ok, by decide +kernel⟩
  · exact ⟨g7_61_ok, by decide +kernel⟩
  · exact ⟨g7_41_ok, by decide +kernel⟩

private def patch7_0 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x18024000a000c0020001 0x131f0b7707e41c9812770c57097b051411cf0d370b1209f300a011270e170ca9107f0ef70e4001ad0fd7) (.leaf 16 0x800200040008001000 0x1667071715bf0f3d07f70188151711fe08d7031f146f09b7055604b613c70a97064d040f)) (.join (.leaf 16 0x44108c001804200480 0x1f6e19af02b71a7a1e36190709f60397185f170a04771b450eb217b705571bf01e701d08170f0637) (.leaf 16 0x180010002008c0018004 0x1d9f168f06131cf71c4f152a1ba70ea300171aff0cd500f71a571928142501d7))) (.join (.join (.leaf 16 0x400004020046000c01 0x1e3d0d8d1f97164c0f721eef065105fd1e4707b6021613b6) (.leaf 16 0x84000000208040 0x35d0a6210a8041505fb0fde0e09)) (.join (.leaf 16 0x18401000200040010001 0x1c36166a0c681a7d0d6f147b09d30be901e71873) (.leaf 16 0x801000210000000000 0x1d4716721ea213f21a9a)))) (.join (.join (.join (.leaf 16 0x1000010800000021 0xf0d0de60cd51aab1795) (.leaf 16 0x2000400000108001 0x17ec16b81a0106d10b4305d21cc1)) (.join (.leaf 16 0x30002000c40 0x1ee81179100016540fe50c3b0100114d087a) (.leaf 16 0x8020000400040100000 0x1cf00ba11beb0a1e02da04ed))) (.join (.join (.leaf 16 0x401000000040100001 0xd6003cf07fb031e1b74) (.leaf 16 0xc01000020000008800 0x1cfd146e08f91eae0b070ae40480191f0ea8)) (.join (.leaf 16 0x800008020 0x75f1ee81f08) (.leaf 16 0x8022000000002010400 0xcd1d521d0d124a16720fec0a6d180d))))) (.join (.join (.join (.join (.leaf 16 0x400000010800008401 0x9d303ac08e007d41caa1f53) (.leaf 16 0x8000100010800208041 0xc94081f01590e4311800b5a0a7210e11e961d1d0bf5)) (.join (.leaf 16 0x8020000420040000002 0x1bae10e30939040d12ac06af18a216540570) (.leaf 16 0x21100020800208000 0xc2e19aa1dc308801d991ad00c88151c0f760bc7))) (.join (.join (.leaf 16 0x8020008000000200821 0x553058a1cd110da0ff3089f12c3011d00520e98) (.leaf 16 0x10400000200002008022 0x175008050dde12c1181f1ce709ab131b1029)) (.join (.leaf 16 0x1080000000000000 0x11641c28) (.leaf 16 0x40004000002100420 0x13e10977076b052e13ec046502ac)))) (.join (.join (.join (.leaf 16 0x2004000002000042 0x1882001f0f600d4512000f6c1e7819fc) (.leaf 16 0x1000011804008000 0xae90a041f7806b203400ffa06d1183c)) (.join (.leaf 16 0x40004000000200020 0x113904c4158a13ec0d790ad0) (.leaf 16 0x8002000400000000402 0x17c81905021b18bb080b1ca8063705f1))) (.join (.join (.leaf 16 0x8400080000002008001 0x1b181d2c059d186d132c17fa) (.leaf 16 0x200002100020 0x11ec0d5900721d52)) (.join (.leaf 16 0x800008c200880028042 0xcd81a651d0d0d1404da1fa105ac100105031f4e1bd9153114390934089700f61b3804fc) (.leaf 16 0x8400000020000000800 0x1a9a0e9814bd10521b78163a))))))
set_option maxRecDepth 4000 in
private theorem scan7_0 : Region (clearPoint L7) 0 512 :=
  checkedPatch 0 patch7_0 gates7 (by decide +kernel) (by decide +kernel)
private def patch7_512 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x400000200000000020 0x1e903ac0469) (.leaf 16 0x401080210000000002 0xa9603cf16e1114d178012360ca2)) (.join (.leaf 16 0x400180040040000021 0x13290cfc089100db120a06dd05be050d11eb02140813) (.leaf 16 0x10401000001840010042 0x18040fd009511a02178b100803350067159a020e1d4b06571e8e0caf))) (.join (.join (.leaf 16 0x1084000040000001 0x158e106611880f1c1cd1) (.leaf 16 0x10000040000401 0x17fe11ef05f802681458029b1581)) (.join (.leaf 16 0x420004020840000000 0x939020108721a610f15181c07b7) (.leaf 16 0x84000080000001 0x19ab08850c4a012915ac)))) (.join (.join (.join (.leaf 16 0x100030002100001 0x177e001b100f016700fe146315af0d59) (.leaf 16 0x4000000100000 0x1d9c11dd)) (.join (.leaf 16 0x10846010402 0x6220f6c084e1d471150002b04c300cd037f165f107b) (.leaf 16 0x801000000008000801 0x1ec900330be51f8c10c20ba605e015ab052004b6))) (.join (.join (.leaf 16 0x88201002008400 0x194a11fe092809e819f0054917e51d590cf6) (.leaf 16 0x10000000210040000020 0x17100bf0101612f100a2180f)) (.join (.leaf 16 0x10000100402 0x18010e861842177c0606) (.leaf 16 0x8201800108040 0x17eb03170aa509df04220198173000c41381124d))))) (.join (.join (.join (.join (.leaf 16 0x20008800000000c21 0x114106e0ab31def100c053100ea14290f010b8009f905aa) (.leaf 16 0x100400 0xee91938)) (.join (.leaf 16 0x20008000802008020 0x632101d06f00734172506d01d20) (.leaf 16 0x441000210042000001 0x14081f020cab026012f505fb08520af30431))) (.join (.join (.leaf 16 0x8400080030002000420 0x120f152a08ac180110a40b1b14d205c9033d) (.leaf 16 0x80004000000108000 0x132312b4060e0492129b1b3d1423)) (.join (.leaf 16 0x400 0x1612) (.leaf 16 0x80010040000c22 0x1024185614761ed61306003f074b0cd8029a)))) (.join (.join (.join (.leaf 16 0x800000002840000040 0xf8a0ab61bbd18a7160c12fb04d616811116058a) (.leaf 16 0x23000200006000000 0x59d1fa618d20eb403a71402066a050e)) (.join (.leaf 16 0x10000084000004000000 0x1ecf0d560c210adb1e5205ea) (.leaf 16 0x400000011000000400 0xd2c02401c0504dc1401))) (.join (.join (.leaf 16 0x10001000000140008421 0x1c7d1b38102b1a8b1908189b111602910e3b01571ce30c1a) (.leaf 16 0x860000000002100000 0x12e009d91e250f8b0a0f06dc0a51)) (.join (.leaf 16 0x400002100062 0x1a92186414911c9d1f5d1dec0cbc15fa0e6e) (.leaf 16 0x422000000000008022 0x7018bd0d5909400ab91e1819a310cd))))))
set_option maxRecDepth 4000 in
private theorem scan7_512 : Region (clearPoint L7) 512 1024 :=
  checkedPatch 512 patch7_512 gates7 (by decide +kernel) (by decide +kernel)
private def patch7_1024 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x180000044000000 0x19571895015703841dc819b4) (.leaf 16 0x20088000040010000 0x103211c1114a09ec12c413300d78)) (.join (.leaf 16 0x8000080000000018402 0x1a2b07db16bb15e606a81f4e1495096d) (.leaf 16 0x21000000840000402 0x125e05550c521deb12c31f291530))) (.join (.join (.leaf 16 0x21000000800300041 0x1b6c13ff1c2c1a74147e0c4219720fb4004f) (.leaf 16 0x24000000080018402 0x5e51c16167b147607c60a21014b1bbe0f1302ef03e21f58143d)) (.join (.leaf 16 0x800080001840000801 0x1f3f10391ca41a11183d02f81b5d17160c460987) (.leaf 16 0x423080000840000000 0xfc9179819420f7602cb19381bf51b88)))) (.join (.join (.join (.leaf 16 0x10001004200040018000 0x11c108210e6112d21441158e16520f3e0e96) (.leaf 16 0x8400000220040100000 0x8130e720a0b1b4510f610f51339)) (.join (.leaf 16 0x2004000840200003 0x18d9089802640507092217f20a4a1b2b0d4e0394) (.leaf 16 0x8020000000000108000 0x104011ac1407181e))) (.join (.join (.leaf 16 0x21000200806000000 0x17170222193e11351deb157e113b) (.leaf 16 0x2000010000100001 0x724029b121e010d0e53)) (.join (.leaf 16 0x10003000000000008801 0x1634002a1c16105608bd00c21ee80bb01b81) (.leaf 16 0x8020080000000108020 0x115b16f91c1701330d0b043f))))) (.join (.join (.join (.join (.leaf 16 0x10020008020800000021 0x1c0308230422194018ef1b8719e013fd02bc0adb) (.leaf 16 0x20080000080000001 0x2ee02b01f2502381047)) (.join (.leaf 16 0x8000080220000000000 0x1305137716861dca13e3) (.leaf 16 0x8000004000000000400 0x1a3e166e0858))) (.join (.join (.leaf 16 0x401004600000110003 0xf0100c512c91e2419d60be7087619300d1a1ce7111f1002) (.leaf 16 0x8000000000002100000 0x15091e890a90)) (.join (.leaf 16 0x8000000200020 0x11ad07751b7f010c104e) (.leaf 16 0x8000000210002008400 0x85d1bbc07f3031318240784)))) (.join (.join (.join (.leaf 16 0x200000842100020 0x170e161607f6019f0c4618b41c5d0a151a38) (.leaf 16 0x80200000700400 0x99f181f1f881db81a261425053a0279025a03f9)) (.join (.leaf 16 0x8020000800000000000 0x1ee80be81cfd173e15af02b9) (.leaf 16 0x1020000000002008401 0x1e49121e0809078e0c0a13e3067b1055160b))) (.join (.join (.leaf 16 0x80000020004000401 0x6da06a0030f006f1e000d3517d906d50f8a1f21) (.leaf 16 0x800000000 0x600)) (.join (.leaf 16 0x8400000020002000860 0x1ed503e71e8911481255172b14c31a2919091513) (.leaf 16 0x8060004200800100420 0xbc81f0b1c7504300c1a01c90f7212f40573071e))))))
set_option maxRecDepth 4000 in
private theorem scan7_1024 : Region (clearPoint L7) 1024 1536 :=
  checkedPatch 1024 patch7_1024 gates7 (by decide +kernel) (by decide +kernel)
private def patch7_1536 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x80001000408400 0x148f1b210873187b0e2b0df20729105c041b) (.leaf 16 0x100000000200801 0x1ed004321105058f1041085a01ec)) (.join (.leaf 16 0x8020000010000000000 0x16330bc20dfb) (.leaf 16 0x21000001000008003 0xcb41f5a1cd1130e0c2216f413ce0638))) (.join (.join (.leaf 16 0x188000044000001 0x1b7f143913831e7306c416a41e1618fd099c) (.leaf 16 0x20004000000100460 0x36c001410631eb410100d05072a)) (.join (.leaf 16 0x1004010042108000 0xcd060f130013ec0e6e144c0ceb) (.leaf 16 0x8001004010000000821 0x5431839097f1670161314e6163f0852)))) (.join (.join (.join (.leaf 16 0x8040004000802000420 0x19ff0e9e05e519cd1afe075c12660746) (.leaf 16 0xc21004000040010002 0x1e3a1447051412961a7d0054018111880a571171065f)) (.join (.leaf 16 0x180010082008800 0x1e04114f0f67071e186f051c106a069f14b60352) (.leaf 16 0x8060014000802300000 0xfeb1e690fc2076a181a166f159102e0002212a908ca155f140a0004))) (.join (.join (.leaf 16 0x20000010800100000 0x1a4f043c037e1c4d) (.leaf 16 0x400080000040000400 0x14ea068a05fa0da6)) (.join (.leaf 16 0x1080000000100041 0x191512c916351b3f118409d9) (.leaf 16 0x100200040010001 0x1e9114a113ae10711f5a047413b2))))) (.join (.join (.join (.join (.leaf 16 0xc21000000802000800 0x1c41161f0b321e041d2b1f1b13b51d5a1255) (.leaf 16 0x23000200000000000 0x1a9a17980f3d05950f46)) (.join (.leaf 16 0x10000004200000008000 0x1d55025b182d009a01ae) (.leaf 16 0x400080220040000000 0x1308095a14d3119a0d911dd0))) (.join (.join (.leaf 16 0xa0004200800108020 0x1f751e530df905be004e1cb208ce10780eb816e70d00) (.leaf 16 0x8400080000040200000 0xa360ad50241086b1a8205df)) (.join (.leaf 16 0x10400000010000100400 0x19ce0fea19920bee182b0530) (.leaf 16 0x1000200804000001 0xa8103551615120306061c3c)))) (.join (.join (.join (.leaf 16 0x20022000200046008001 0x1d7b19fc093f00850c211255019e05ea0c9f1aa4171d0dc00db1085d) (.leaf 16 0x400004210000000000 0x8c40b8602fd107f)) (.join (.leaf 16 0x20080000040 0x194a04cb1ed607cc1b7611d4) (.leaf 16 0x8022010000800010400 0xbee06c015e903db17be0f3f058804470a3e0712028e0d84))) (.join (.join (.leaf 16 0x84210040000402 0xea7194b05730a36171009a11c1d0d05) (.leaf 16 0x1 0x5fe)) (.join (.leaf 16 0x10420000410880000001 0x1442126b046616e3169c10861e0a1c830e1e059b11c3) (.leaf 16 0x8001084020004000400 0x7020fa2067606280adb02a90fc30e961cc6))))))
set_option maxRecDepth 4000 in
private theorem scan7_1536 : Region (clearPoint L7) 1536 2048 :=
  checkedPatch 1536 patch7_1536 gates7 (by decide +kernel) (by decide +kernel)
private def patch7_2048 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x8000004000000000040 0x1a8f0be2179a082e) (.leaf 16 0x20020000010000000000 0x1f4e12980f7c034405df1a86)) (.join (.leaf 16 0x1000000080000000 0x15b116890b19) (.leaf 16 0x84000042200000 0x172b108d13ab153312bd0401))) (.join (.join (.leaf 16 0x100200840008c0100022 0x68b04811a970d5715ba16f21d9f1bf5073406541caa19530303) (.leaf 16 0xc00100010000000000 0x1eb8164c06240f3d041c067a)) (.join (.leaf 16 0x8401000000000200461 0x1f908cd0d3015af128c189016c107af03ab1a89) (.leaf 16 0xc010000008000 0x1d2214e5039c130604b2)))) (.join (.join (.join (.leaf 16 0x80030000008800 0x1094192511ec08ad06ab0f9108e2) (.leaf 16 0x40004010000000040 0x9d6042209ea182713500e49)) (.join (.leaf 16 0x402000000040010001 0x1b040be4046b0e4f111700c618a3) (.leaf 16 0x1000020002000000 0x161a1d1f19150415))) (.join (.join (.leaf 16 0x8000000002000308002 0x2111e1e154f097b023b1e5508b5043a1270071e0337) (.leaf 16 0x1084200000010000 0x109b0ffd021c0dd81ad51739)) (.join (.leaf 16 0x100000000008000 0x1e130041152a) (.leaf 16 0x2008220800000000 0x1a740fbb1f5905e01f5a0f15098a0297))))) (.join (.join (.join (.join (.leaf 16 0x8001000210940008000 0x1d801b45031800a0121e1ccd16ec0ea50d5502d215b2) (.leaf 16 0xc00180010004108420 0x13ab119c006b1f7110760ac50ceb0ac501e215cd128a18ab01a8)) (.join (.leaf 16 0x22008410800000000 0x10a21b8212130b0407580cb50361169b1d98) (.leaf 16 0x10421000000000000c01 0x18630027004f1a400d0d0cee047e043f1215))) (.join (.join (.leaf 16 0x1000220002000001 0x26d04fe1c0204bd0fb20ac5) (.leaf 16 0x80010800018001 0x8fa01591071183d14b60feb1684)) (.join (.leaf 16 0x20000000010000010001 0x1b450ebe090d05ae183710d701b41100) (.leaf 16 0x8400088000000100400 0x8ca10a91193138105501c241792)))) (.join (.join (.join (.leaf 16 0x440008000000000020 0x12931c2907c31b25129f137c) (.leaf 16 0x18000084000802000420 0x13dc0514012b12d61e5706f0126702081071)) (.join (.leaf 16 0x180010804000001 0x1931040f00dc0bd408cb1b3d13d10ccf) (.leaf 16 0x10011002008041 0x1c6a119a0f60058e05940653036d08d014e61bfb049a1465))) (.join (.join (.leaf 16 0x10020000000040108000 0x1ec810b01ee70fa60789085c) (.leaf 16 0x400000030000000400 0x1c91123e10d501a30fa6)) (.join (.leaf 16 0xa0000000042100020 0x193e167f11040e7a0b820a3f03480e781b30) (.leaf 16 0x420008e00040100000 0x12df0beb1e1b16ec1cbb1bc9143e11a50c870b49004e099c1ab2))))))
set_option maxRecDepth 4000 in
private theorem scan7_2048 : Region (clearPoint L7) 2048 2560 :=
  checkedPatch 2048 patch7_2048 gates7 (by decide +kernel) (by decide +kernel)
private def patch7_2560 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x420000000000018021 0x182313510c2105d000d81c0c05df) (.leaf 16 0x800000002800008040 0x13e006f19bb186e15990e77012616511b7f0020)) (.join (.leaf 16 0x8041000000040000002 0x1ce12e40bc1181e1ec210b70fde) (.leaf 16 0x840008000 0x1d4d183c1b99))) (.join (.join (.leaf 16 0x421080000000000021 0xccc0dfe04fc011a0d101bb8) (.leaf 16 0x400080000084008403 0x16330b68196417171507065806a21d351bb217ef06da)) (.join (.leaf 16 0x400004000004110c00 0x716166c157202cc00d9173714a01db40dec06f0) (.leaf 16 0x40000000002100041 0x172500e302e81d05174710be13c6)))) (.join (.join (.join (.leaf 16 0x12840010024 0x1151f471ef61abb0cea03d50a5d146e13941c2912671186102d063e) (.leaf 16 0x1000200006100401 0xe2b0066194307c0010b15bb07f706ae)) (.join (.leaf 16 0x8220000000000 0xef00074014b05880549) (.leaf 16 0x18400080000800008400 0x1c5802bd01ae1a3b0a180300166f1cc6))) (.join (.join (.leaf 16 0x8000008410040000800 0x8d01f5a0bfe150013711ad60c96194410c5) (.leaf 16 0x8000080000800300000 0x15821905019014d013830c6e)) (.join (.leaf 16 0x80000880000020 0x93a13aa13c205c21f9e) (.leaf 16 0x400000000002000001 0xe31723000f))))) (.join (.join (.join (.join (.leaf 16 0x420000020800000040 0x8b508540b7c04531bd2193f04b5) (.leaf 16 0x8000000210100010000 0x11dc01ef158e1e451c550676001510cc050b)) (.join (.leaf 16 0x20000100040 0x187312900c6a13240313) (.leaf 16 0x60088000040000020 0x112906e4026c0fb40c4207d603671dde))) (.join (.join (.leaf 16 0x62000200042008002 0x1e9f166b01c21d9c1cfe0b03133c03a017c5183a04a0) (.leaf 16 0x400004000000001002 0xc3007f91ea51b8713940b8014d01104)) (.join (.leaf 16 0x88000000100021 0x153317ef098610d3048c1c3f) (.leaf 16 0x10002084400800000400 0x15b702071465003b0e6e083d10010cce12a2184c)))) (.join (.join (.join (.leaf 16 0x20000000000100000 0xaa50f3d) (.leaf 16 0x1004202002000001 0xe2018f200cd13ff0ef305960116017d0a93)) (.join (.leaf 16 0x8000000200002010001 0x1e050d7602ef068602790b9c) (.leaf 16 0x8000200010804000000 0x1c8f1cd51985183905600ff4145310da00ba))) (.join (.join (.leaf 16 0x8000004200000200400 0x1f7214d30ab71e7f19af1a4f) (.leaf 16 0x402004201002010021 0x1e461f7e130605b2007d1137102904150a8e02fd1b4512b9)) (.join (.leaf 16 0x420000010000000000 0xf0d17831611) (.leaf 16 0x440008000040108020 0x7b90f58000f17ee150604de085d1b911eeb))))))
set_option maxRecDepth 4000 in
private theorem scan7_2560 : Region (clearPoint L7) 2560 3072 :=
  checkedPatch 2560 patch7_2560 gates7 (by decide +kernel) (by decide +kernel)
private def patch7_3072 : Patch :=
  (.join (.join (.leaf 16 0x400100030044010020 0x10f1b190fe5170e0c7f0c0d10e116000be012e40f611ed2) (.join (.leaf 16 0x80000042000400 0x1b75194709160cea) (.leaf 16 0x80010000300060 0x1ac1123310ab051400dd1ac8061604bd))) (.join (.leaf 16 0x4600000000000 0x174019e208ba0140) (.join (.leaf 16 0x400000211000000400 0x14301ca4057c1d471a92189e) (.leaf 6 0xa000041 0x1c65178b0ce40792009015950bae0c1f))))
set_option maxRecDepth 4000 in
private theorem scan7_3072 : Region (clearPoint L7) 3072 3158 :=
  checkedPatch 3072 patch7_3072 gates7 (by decide +kernel) (by decide +kernel)
private theorem rows7 : Region (clearPoint L7) 0 3158 :=
  (mergeRegion (mergeRegion scan7_0 (mergeRegion scan7_512 scan7_1024)) (mergeRegion (mergeRegion scan7_1536 scan7_2048) (mergeRegion scan7_2560 scan7_3072)))
private theorem clear7 : Clear L7 := clear_of_scan (by decide +kernel) (rows7)

private def L8 : Chart := ⟨6497, 53683659591, -455276, 172173, -420553, -443329, 4175, 3032⟩

private def g8_29 : Gate := ⟨29, 9, 0x13d122f3, #[
    0x1fffffff, 0x10321303, 0x120a504a, 0x150002b5, 0x124024c9, 0x10528254, 0x11188a22, 0x10002b5a,
    0x1861a082, 0x10c34105, 0x10093264, 0x1ce00e00, 0x10981c0c, 0x13803803, 0x188a2288, 0x11144511,
    0x1c01c01c, 0x13038190, 0x10070073, 0x1264c900, 0x1a082c30, 0x14105861, 0x15ad4000, 0x14451188,
    0x12a414a0, 0x19324024, 0x1ad4000a, 0x1520a504, 0x1c0c84c0]⟩
private theorem g8_29_ok : g8_29.OK L8 := gate_of_test (by decide +kernel)

private def g8_53 : Gate := ⟨53, 8, 0xd228fccfc512d, #[
    0x1fffffffffffff, 0xc5023c430a436, 0x18844302f94942, 0x60094e807cd0a, 0x14190c1380472b, 0x2b4c2003aa0ab, 0x15525982e6050, 0x88452858622b3,
    0xa1817844d6e0, 0x11000a0e59b932, 0x16cc6806445013, 0xd283e06750060, 0xdc9c209b0a006, 0x1d4c2248221a31, 0x14848c67059a1, 0x4308f99431441,
    0x305b145caa009, 0x1d948844987804, 0x14145432506e0c, 0x1748969ac2401, 0x9291a20105e59, 0xa39910f460c40, 0x133002ab400b4e, 0x4605a04c34175,
    0x1824e8020161e7, 0x1c420dc16058b, 0x8681642583546, 0x1340b098ab0690, 0x18211c34681a0e, 0xb920f9e1a010, 0x2d0312ba0b0c8, 0xa00665cb400b5,
    0x44ce2808c18bc, 0x2c4a4a69e8201, 0x14897420090d65, 0x151414c1d8293, 0x10894dc8078648, 0x146d06240154e8, 0xf8861208a30a6, 0x18909421668398,
    0x122195e3161104, 0x21c9d98014364, 0x3e0a581802b98, 0xb19b72028898, 0x280045327669c, 0x140c2801dac887, 0xa5108b3511868, 0xd255402819d06,
    0x2196a35415700, 0x184c175388072, 0x194803142cf805, 0x61108d0a4a7d0, 0x1e20519b094308]⟩
private theorem g8_53_ok : g8_53.OK L8 := gate_of_test (by decide +kernel)

private def g8_59 : Gate := ⟨59, 8, 0x22b62183e7b92bb, #[
    0x200000000000, 0x71c51d64873985f, 0x7c1d85a8cf5d701, 0x5452dfb5e52b7, 0x54ede45ca2257d2, 0x31f5b4028b7fc85, 0x4dd84c933cfea28, 0x4f4cae91e3c1d1c,
    0x3a38ee5d4cb9330, 0x1e71b1cf4b0986b, 0x3eddf7c90046703, 0x3931657bb620cf1, 0x69f55938318387b, 0x40ccaa97d57aeb0, 0x1d68276e25c1af5, 0x74704c771da49b6,
    0x43b52e3e1ca8dc6, 0x384d28ef54cb5ac, 0x1e81a780f93e9d6, 0x3eb162a46657366, 0x28e8fadea834d54, 0x43d91a72fa1a4e6, 0x52908b49dea6f69, 0x67d4127fc0a27f,
    0x2f889da0d7b5469, 0x334cb4913b56dca, 0x6c7d3373348ba88, 0x360cce3f00df42f, 0x4f60071bde6e171, 0x24904f958bdb78b, 0x4f90492d1edbd1a, 0x47003798e8767bd,
    0x6399836f42fb00f, 0x7665f1b115d12cc, 0x496996653b6adc8, 0x2dc88fa962adeb0, 0x2415f30fe4503fe, 0x16884a596f657b9, 0x72c4de1672585f4, 0x5af8b8a2ab2c157,
    0x2a346be66cea662, 0xf2c0bc6b97c9f0, 0x38a590e35ad32af, 0x63a56e163b15387, 0x71907176d925b8e, 0x3720b5caf583a47, 0x4aa99810d75eabe, 0x64d57cbde1c18c1,
    0x753464e8f3046dd, 0x1f7ddbec0e62009, 0x1c6c73cd6190d2f, 0x53b8e2e0cc9d32b, 0x4ba997938b83c78, 0x4990dd91457f3cc, 0x16d7c6a13fed14, 0x513db954bea4453,
    0x5a51500ed4a7adf, 0x2d0dc1f80ebaf31, 0x35c51c7fa19ce12]⟩
private theorem g8_59_ok : g8_59.OK L8 := gate_of_test (by decide +kernel)

private def g8_47 : Gate := ⟨47, 8, 0x7bcae4d8ac21, #[
    0x7fffffffffff, 0xe39794e831b, 0x7c4a872bc721, 0x2b0a5e9d525a, 0x65709d842b5d, 0x233f78838b7, 0x5b118c33ec93, 0x12236d77f46,
    0x322e4593f3d0, 0x3c443eaa1c79, 0x480f4aef3f80, 0x1d574a8ad6c2, 0xf5652c1a54f, 0x162d8305f2cf, 0x171d5d1a3ca2, 0x3262d46d9365,
    0xd5dad712296, 0x4b4d3c8c6db0, 0x6421701fe99d, 0x703b6065664f, 0x5505ff6088e9, 0x5d4e20fa0b65, 0x66733e708c85, 0x336a85ba4c9c,
    0x2b6639325da1, 0x6733a1310e7c, 0x395da6d05f04, 0x5055971106ff, 0x6e07f266a606, 0x4213b997f80e, 0x59690db6313c, 0x5d5869448eb5,
    0x2326a6c9b62b, 0x5c74453c58ba, 0x5a34f34fa0c1, 0x3578f2a5834a, 0x755c436b5152, 0x780901fcf752, 0x111e9e38557c, 0x3a260bcfc9a2,
    0x224062feeb6c, 0x446dc937cc31, 0x6620ed1c11ef, 0x753bad421b9, 0x286a5a4ab97a, 0x291f84e3d4e1, 0x4e38d8c1729e]⟩
private theorem g8_47_ok : g8_47.OK L8 := gate_of_test (by decide +kernel)

private def g8_43 : Gate := ⟨43, 8, 0x35883a3ee53, #[
    0x10, 0x311d0c7df19, 0x58b5717f214, 0x5ae364dc01f, 0x33d5da623b, 0x4ccad23bd32, 0x3a79da80a3d, 0x3c1902b673f,
    0x7944b4ae276, 0x37f0d82897a, 0x260f4f598f2, 0x2d179053cf9, 0x4ce882ec2f7, 0x6d685c4fa32, 0x2cef143d255, 0x571daf11991,
    0x32ec76061db, 0x33ee594e9c, 0x60a6eae11f6, 0x2315a7a7517, 0x7593c14af70, 0x74ea4d910d7, 0x89b2572fd6, 0x75283c9ae1d,
    0x2e5e5a8c5d1, 0x87576506df, 0x729a77cc072, 0x606e374db7, 0x188f5b8eb13, 0x4bc28f73554, 0x5f23a16b698, 0x437411733de,
    0x3ca09e8b53e, 0x19af2f0649e, 0x1141b0fecbd, 0x4752d229edc, 0x66d40983df9, 0x5015b9e5d78, 0x3dc4b533299, 0x465babcc1b8,
    0x3b26c75bf0, 0x4fe8ead1a50, 0x7be30b88d31]⟩
private theorem g8_43_ok : g8_43.OK L8 := gate_of_test (by decide +kernel)

private def g8_31 : Gate := ⟨31, 9, 0x121d47b7, #[
    0x7fffffff, 0x32de0e58, 0x72cfa052, 0x294dda86, 0x22c6bb70, 0x77810d47, 0x1982dace, 0x550ce3d1,
    0x36d4a26a, 0x47c1d549, 0x6e405d53, 0x41193f3a, 0x1b41729e, 0x41bb91f, 0x1d4687b1, 0x4cda68e4,
    0x32d99271, 0xb15c8de, 0x6ec10f89, 0x7416c794, 0x64c415cf, 0x5013bcab, 0x5c1f192a, 0x295b6564,
    0x398558bc, 0x5a0cc735, 0x40f7e2b, 0x6b1a20ed, 0x5d94a615, 0x2f9a74a0, 0x3da61a7]⟩
private theorem g8_31_ok : g8_31.OK L8 := gate_of_test (by decide +kernel)

private def g8_23 : Gate := ⟨23, 9, 0x7acca1, #[
    0x7fffff, 0x10bdd8, 0xe5535, 0x32bb41, 0x69991a, 0x6b4f4, 0x445cf1, 0x6d14a5,
    0x1e3698, 0x63b219, 0x6cd107, 0x41f12b, 0x291f07, 0x41166f, 0x309b8e, 0x32d8f0,
    0x4a516e, 0x1e7446, 0x5e5ac0, 0x31332d, 0x5ba9a, 0x5954e2, 0x377a10]⟩
private theorem g8_23_ok : g8_23.OK L8 := gate_of_test (by decide +kernel)

private def g8_19 : Gate := ⟨19, 9, 0x4f50d, #[
    0x7ffff, 0x11cae, 0x48fc1, 0x13167, 0x3017d, 0x728f0, 0x696a4, 0x43369,
    0x6aa26, 0x1af42, 0x6b10b, 0x2ad91, 0x1865b, 0x52c95, 0x29c3c, 0x1afa,
    0x1939a, 0x6260f, 0x711d4]⟩
private theorem g8_19_ok : g8_19.OK L8 := gate_of_test (by decide +kernel)

private def g8_11 : Gate := ⟨11, 10, 0x5c5, #[
    0x40, 0x33a, 0x497, 0x11f, 0x3ac, 0x4ae, 0x6a5, 0x6b8,
    0x713, 0x527, 0x399]⟩
private theorem g8_11_ok : g8_11.OK L8 := gate_of_test (by decide +kernel)

private def g8_7 : Gate := ⟨7, 11, 0x17, #[
    0x8, 0x5a, 0x6c, 0x78, 0xf, 0x1b, 0x2d]⟩
private theorem g8_7_ok : g8_7.OK L8 := gate_of_test (by decide +kernel)

private def g8_37 : Gate := ⟨37, 8, 0x9a1dee165, #[
    0x80000000, 0x16d686791b, 0xdf268d179, 0x10b563fb89, 0x16ea4d78c5, 0x8bd1986fe, 0x15db72385a, 0x12ad95d7c4,
    0xdf89c24f3, 0x1286f35f16, 0x108fb75786, 0x1eea9f3085, 0x3f28e7b19, 0xff85c2c4b, 0x1ccdf68632, 0xbcbfd8464,
    0x3ae95c3e5, 0x119173c57e, 0xcd568ef1a, 0x159963dc5a, 0x4c5fa8f3a, 0x1ae29f0ea5, 0x9e89886ff, 0x199d3185be,
    0xffb48d0e8, 0x7e26379c5, 0xbbe8433e5, 0x188587abb7, 0x10a5a3eb3d, 0xfdb3c90e4, 0x1aa48faea6, 0xdd568713b,
    0x1e89fd8662, 0xbb68c7ac9, 0x1686477f1a, 0x7da7a2c59, 0x15b7627985]⟩
private theorem g8_37_ok : g8_37.OK L8 := gate_of_test (by decide +kernel)

private def g8_3 : Gate := ⟨3, 12, 0x5, #[
    0x4, 0x6, 0x5]⟩
private theorem g8_3_ok : g8_3.OK L8 := gate_of_test (by decide +kernel)

private def g8_61 : Gate := ⟨61, 8, 0x8ec196bf5a60dc5, #[
    0x8000000, 0x1acb25dd7d457337, 0x163e3e77ee724726, 0x11cfcc57e95c3cb7, 0xad6b2fb9e87f487, 0x9d02fa78fecfe56, 0x1f4336ff89727f50, 0xf7f1b0ebaf1dcc2,
    0x14cba8fc6ed916ef, 0x1065edfb3ccc7cd9, 0x1ff8c6f84bfb8a0e, 0x13d7ec6a7f2d7252, 0x17deeea95d32a587, 0x3ab47a7bbc3f3e1, 0xde14a98fd9ff52b, 0x237efa40b3cff2f,
    0xc5bfb579ada6d64, 0xf0f12eabdcf971d, 0x1f6beda5aa1e1b56, 0x1379d1d1cba68dbf, 0x39aa9535dffe8f8, 0x9bbbbeb7a22d762, 0x1e12cc93aff19f76, 0x84de1ded87f567b,
    0x1acd88773f71f4dc, 0xf15fb14ddcf319e, 0x16bdd2acadee45ba, 0x124afd2a7f99d8bd, 0x1ccc391efb7c2bba, 0x19f5db6c8f0ba733, 0x1ffc93540ca5bf5e, 0x1fbd7ed29815649f,
    0x19e672e8789b6dd7, 0x13aeea1f6fbc4e19, 0x4de8dccff2a5fa9, 0x16aed13bda9aa5de, 0xf3cc679dd946fd4, 0x159d97c77e7708d9, 0x16f357f0dbdc3d9, 0x7b77cc7fae499a4,
    0x192375a22f6beeee, 0x1c0f8bffdd654aac, 0xcfed8b2e9c5c5cf, 0xfb56c3c2ad2dbeb, 0xf5c74f9deaba478, 0x3135b2dacf56fed, 0x47a7f9e6812fbf6, 0x1b6a57fcdf8ca943,
    0x1c43e7e1eef2f16a, 0x1ef0d2a65d4abbbd, 0x1ca5275a7f2b1bf5, 0x1fb828efe90fb18f, 0xcd9f199e6fdbd3, 0x12fbb44dbb1f8ae9, 0xf219dc7aeb86c7f, 0xf857f2748ffb661,
    0x19353f9bf8f2fa05, 0x157097f0bcefa6b5, 0x18f69e1d4bf519f9, 0x6b271273bf73e3e, 0x15f667515f5dd269]⟩
private theorem g8_61_ok : g8_61.OK L8 := gate_of_test (by decide +kernel)

private def g8_41 : Gate := ⟨41, 8, 0x4c7d4af8c9, #[
    0x1ffffffffff, 0x2fbfb3c6e7, 0x1bd5b7f5bc1, 0x3fb33fe49f, 0x1dce6f945fd, 0x1eff77b1730, 0x1ff5961ebd5, 0x1d6cf9ef327,
    0xdc1dafbdfa, 0x13edfbfd09c, 0x195dfc7c57b, 0x194759b7e7f, 0x1ff66f8cdaa, 0x1f73e35df64, 0x6f96975aff, 0xf6f7690fbd,
    0xf6a8fef31f, 0xd7d5eece5b, 0x1fd9475f975, 0xae69f5f72f, 0xec5cdff6ad, 0x146eb56ffb3, 0xceaf4efaf9, 0x137fae9fae2,
    0x17d6da7377a, 0xadef8cf7f1, 0x1edebdf096e, 0x13ecff5ae96, 0x19df26fbac7, 0xdff55b31f6, 0x1c53fe7ed9a, 0x1753dea3e3f,
    0x16f9390bfdf, 0x10765fbdf5b, 0x6d7e4cf79f, 0x15ffabd7869, 0x1fef0ce8dee, 0xe77bfa29f6, 0x1bf8f927fcc, 0x157b83dafed,
    0x1be8e763cdf]⟩
private theorem g8_41_ok : g8_41.OK L8 := gate_of_test (by decide +kernel)

private def filters8 : List Gate := [g8_29, g8_53, g8_59, g8_47, g8_43, g8_31, g8_23, g8_19, g8_11, g8_7, g8_37, g8_3, g8_61, g8_41]
private theorem gates8 (g : Gate) (h : g ∈ filters8) : g.OK L8 ∧ 512 ≤ g.p*2^vDepth g.p := by
  simp only [filters8, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨g8_29_ok, by decide +kernel⟩
  · exact ⟨g8_53_ok, by decide +kernel⟩
  · exact ⟨g8_59_ok, by decide +kernel⟩
  · exact ⟨g8_47_ok, by decide +kernel⟩
  · exact ⟨g8_43_ok, by decide +kernel⟩
  · exact ⟨g8_31_ok, by decide +kernel⟩
  · exact ⟨g8_23_ok, by decide +kernel⟩
  · exact ⟨g8_19_ok, by decide +kernel⟩
  · exact ⟨g8_11_ok, by decide +kernel⟩
  · exact ⟨g8_7_ok, by decide +kernel⟩
  · exact ⟨g8_37_ok, by decide +kernel⟩
  · exact ⟨g8_3_ok, by decide +kernel⟩
  · exact ⟨g8_61_ok, by decide +kernel⟩
  · exact ⟨g8_41_ok, by decide +kernel⟩

private def patch8_0 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x20000010044208821 0x1cc6016b05241bb300e108dd03f7070d0c960a230d39104f) (.leaf 16 0x20000000000108000 0xe8d007e0d70)) (.join (.leaf 16 0x200040000000 0x111e0a91) (.leaf 16 0x4200006000000 0xccb07b21cbe0dc10597))) (.join (.join (.leaf 16 0x1000000000108000 0x4d318f80326) (.leaf 16 0x8800000200800000400 0x1f420861328167a0b0911ed)) (.join (.leaf 16 0x20004031000100020 0x2ae0b33084c056c03fe1e07011518d01ef2) (.leaf 16 0x42080000000200001 0x1a0d00cb10420b4412bc1080094713e4)))) (.join (.join (.join (.leaf 16 0x20000020000000401 0x187d0dee0110079a1a18) (.leaf 16 0x10020000010000000040 0x181108a508bc20101c040785)) (.join (.leaf 16 0x420000001800100000 0x5c318fb095f03930113138b) (.leaf 16 0x402000000004000400 0x1a9c1601121a1e0b129a1ca5))) (.join (.join (.leaf 16 0x40080020002000020 0x145a016f040114ee09a2087e0cc5) (.leaf 16 0x20000200002300001 0x1809175d1ee31c800b7006170049)) (.join (.leaf 16 0x430040018002 0xedf0669128e10b1023f1eae1c1418360b6d17790788) (.leaf 16 0x80031040000000 0x147913d61035063912eb01de1529))))) (.join (.join (.join (.join (.leaf 16 0x8000000600006000040 0x20021edd038902c520000b8d007d20640f96) (.leaf 16 0x8001004000040000401 0x15f8115218da15501ab60b8d)) (.join (.leaf 16 0x6000400 0x6b3051b048c0602) (.leaf 16 0x820004000804000001 0x1fd300fb0f3601291abb0a3d040d11a2))) (.join (.join (.leaf 16 0x8400000210002008020 0xcf9026f0a6e16c71b3108481ce2) (.leaf 16 0x8001080200000000021 0x132e10e2044c02780d401b0e)) (.join (.leaf 16 0x200040008c0000000 0xad314e506a8187a16d80a78) (.leaf 16 0x8000000430000300020 0x1944187405ac1bb313e5060818f81028012e1796)))) (.join (.join (.join (.leaf 16 0x40004200004000800 0x1ee30ab100ad0db210640930093b0686) (.leaf 16 0x4010002000002 0x1865092c04e5198d02f5)) (.join (.leaf 16 0x8000000011002000001 0xba906911bda1a0000860060) (.leaf 16 0x20088000008000400 0x16b5122d1fc318981e111b9515de0c771e6b))) (.join (.join (.leaf 16 0x20000010080008001 0x151113d0201d068b19341ea3) (.leaf 16 0x20000000040000423 0xdfa1e8c0d6f1b5614cd11131098)) (.join (.leaf 16 0x841104000800000000 0x15871374115304ac1a031f6e09c02086172c) (.leaf 16 0x8000004000040000003 0xf220c6618a31fba175d101b))))))
set_option maxRecDepth 4000 in
private theorem scan8_0 : Region (clearPoint L8) 0 512 :=
  checkedPatch 0 patch8_0 gates8 (by decide +kernel) (by decide +kernel)
private def patch8_512 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x8000088200000008421 0x96607550dee06cb152101ad0edd02660582) (.leaf 16 0x10000004000004100020 0x1730084514ba1cfd1ad20da80644)) (.join (.leaf 16 0x1000000800010003 0x1a5105781ece0ce2197206cb0322) (.leaf 16 0x400000410002100000 0x1ba11b3010fd1255017315b0))) (.join (.join (.leaf 16 0x80004000800108000 0x1ff41bee15dd0f0411c01346114405b1) (.leaf 16 0x8000000210002100040 0xf0e00731e2c141512680f29087e)) (.join (.leaf 16 0x1004000804110003 0x100e042b1c701cff0122105218a101a71a4e12f505f6) (.leaf 16 0x1084000000300040 0x1b21e530e1d176c0b0800d6136102c8)))) (.join (.join (.join (.leaf 16 0x8020000000040000040 0x13190aa600411c950dd9) (.leaf 16 0x401300000002000401 0x9a306e01efa1a6c174416f7166114301e64048d1d3f)) (.join (.leaf 16 0x8001000210002000400 0xc98185601a9046a1d3f0a31) (.leaf 16 0x400080420000108020 0x160d0bff1e0e0a0c170c11750e8e12321838))) (.join (.join (.leaf 16 0x2000600000000000 0x1d6104a110e80e3a0ce6) (.leaf 16 0x4000000108400 0x557197b16160cc6)) (.join (.leaf 16 0x400004220002018800 0x41600fc187c1ae41001182319f410060c491edd0c38) (.leaf 16 0x400000000040000c21 0x18bc072220990f4c01041ccd177b))))) (.join (.join (.join (.join (.leaf 16 0x10000188000800308000 0x3b602091fac128f00ad107902111f331f7e0ffe02270e24) (.leaf 16 0x4000000008400 0x513014c0b15)) (.join (.leaf 16 0x8001000010000000400 0x200f11a612882092) (.leaf 16 0x8000080000800100001 0x17d81617201a207b0209))) (.join (.join (.leaf 16 0x800842008401 0x1e8c15a0154a14ad14f011841a63119b1f5206c8) (.leaf 16 0x400000200004100022 0x70307200d430a9c135813971cac0c2c)) (.join (.leaf 16 0x8100c000000100000 0x16370f4c0cb601fa0e6c1b6d089f03280ff4) (.leaf 16 0x8041004000080000020 0x1e6a1fad0c5c042e1d1b192a140b1605)))) (.join (.join (.join (.leaf 16 0x8000000210006008000 0x16681bc60af61eb60c890226034d) (.leaf 16 0x4200000000002 0x19d31ec517511448)) (.join (.leaf 16 0x18002000000000100005 0x15dc095e000419460fe80a8f1e6a194b162e11d710e1) (.leaf 16 0x88200844000000 0xd73178a0ba51d3f0d04004a1436011f))) (.join (.join (.leaf 16 0x400000001800100040 0x1e091e1119d6046a00940d5a0199) (.leaf 16 0x8002008001840000020 0x15fe1abf16991fc412571da81c53123203310161)) (.join (.leaf 16 0x10021000010000000003 0xa9704e5064d01fe15b61e6b16220fe7) (.leaf 16 0x420000020002108000 0xdf5008307e607400789087d0722))))))
set_option maxRecDepth 4000 in
private theorem scan8_512 : Region (clearPoint L8) 512 1024 :=
  checkedPatch 512 patch8_512 gates8 (by decide +kernel) (by decide +kernel)
private def patch8_1024 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x800108000 0x1ede0d6b02d4) (.leaf 16 0x820080010000208400 0xa34027d18ec134b0b2412080b8d040119f3)) (.join (.leaf 16 0x11000100000 0xb011f9310781eec) (.leaf 16 0x800004200000100001 0x1e11003b00a8046319250df6))) (.join (.join (.leaf 16 0x9000000400040008001 0x10b01f0613ae0a7c04f0060805c1097505cc0536) (.leaf 16 0x1080000000000000 0xfda16a7)) (.join (.leaf 16 0x4010040008001 0x9ea1b111d5c12111756) (.leaf 16 0x8000000000040008401 0xfc301560d6d11ab145b)))) (.join (.join (.join (.leaf 16 0x8420080020002000021 0x108e163d091f1a821b8a123904621fc61e3e) (.leaf 16 0x20090001000100001 0x3f08781b6b14ea0db905e41b95177b13310364)) (.join (.leaf 16 0x801004010004100800 0x1d561a48151a17db1481164b01a015da0e0300ad) (.leaf 16 0x860000020000000000 0xdcd0bd61e44175d07ea17a20e96))) (.join (.join (.leaf 16 0x42000010800010021 0x147e091b10d00c58105519a31a33095b07bb159b) (.leaf 16 0x4220000010000 0x14612bd0fcd0ecc1d5b1839)) (.join (.leaf 16 0x20000000401 0x1e8905c116731efe) (.leaf 16 0x10001000001004108000 0x18281588126a1ce214a5152c0f3e0beb205c))))) (.join (.join (.join (.join (.leaf 16 0x20000000044000400 0x25d1d2a1a560cb20b63) (.leaf 16 0x8400084200002000020 0x4c715e3158904fd0824094106f4)) (.join (.leaf 16 0x20000000000108021 0x18081cdc10b71916170c) (.leaf 16 0x10800101c0000021 0x2f71fc10c6a1e391d9f1c73181113b00d74042815e90e1c))) (.join (.join (.leaf 16 0x8000084020002100420 0x52717721daa081c02b8113704131a9619b5) (.leaf 16 0x400000020040118440 0x8e1205d1ad216580fc018e911d502bd00381e8108b8)) (.join (.leaf 16 0x80040880000c20 0x45a19f60ccd08f8037a1e9516d4141520211ea00de40020) (.leaf 16 0x1000200042008403 0x1bcb02b107af1c0a1f6a03c91dc9129b112a)))) (.join (.join (.join (.leaf 16 0x8421000000800008020 0x1dd70c6e153b155e1d6d14ad0654) (.leaf 16 0x1000001800001000 0x1140140310520950173811810c25097d)) (.join (.leaf 16 0x400080000040200020 0x16c8120f1bdd1d56093d0103) (.leaf 16 0x8000080000000000020 0x27e0fd70e8b))) (.join (.join (.leaf 16 0x8401108000880100002 0x19fe08c21e9c1a3510c31ff719be135b0fbd084308211f9a05a0) (.leaf 16 0x400000000800000021 0xa7c110c14710fb3)) (.join (.leaf 16 0x801004200800208004 0x49400f8066811fa173f096612cc0e490ff71ea71d4e0c6a0568) (.leaf 16 0x21004000000000002 0xcc811541d1816ee1398))))))
set_option maxRecDepth 4000 in
private theorem scan8_1024 : Region (clearPoint L8) 1024 1536 :=
  checkedPatch 1024 patch8_1024 gates8 (by decide +kernel) (by decide +kernel)
private def patch8_1536 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x20000010840008460 0x1db00fad111a0bf90a6d03bc1b371550074f) (.leaf 16 0x8440100000840100020 0xef5092c1f5f1eb01ec50d6113ac14cf10a30731)) (.join (.leaf 16 0x10001000000000108000 0xd94087b0e0005db076e) (.leaf 16 0x401000010000000020 0xae0085a0e7c0ad2))) (.join (.join (.leaf 16 0x8421000400000000000 0x9801d9005ba0fa620691a63) (.leaf 16 0x8000000020000000401 0x63f200812fd10a614c1)) (.join (.leaf 16 0x400100210002000000 0xa4409ea03ec060813ee01d0) (.leaf 16 0x10420000001044000021 0x153b0ba11f61142220101c8b1bdf1e650593046a0d1c)))) (.join (.join (.join (.leaf 16 0x401080000040010000 0x199112b91d7112e71a4b097e) (.leaf 16 0x1000000002000c00 0x207201041af11a45190b)) (.join (.leaf 16 0x8000088010000108402 0x1ca12590a3704e916611a7611ab16df0b4e0809) (.leaf 16 0x180200000000000 0x1c8b1a4a0c7017cf))) (.join (.join (.leaf 16 0x1000010000000401 0x132e0f9907140fce) (.leaf 16 0x42008c010802208020 0x14a212b01eaa1c1f0e49091d0c89030c1934095a00ef0db40b8d)) (.join (.leaf 16 0x1000010800000401 0x17c71b1a0c6e1bbb01be) (.leaf 16 0x800110c010000008000 0x1ba1169a201506cb1e640869043012a20cdd))))) (.join (.join (.join (.join (.leaf 16 0xc000880000000 0x151808c3049e0b4020600026) (.leaf 16 0x420080600040000001 0x1c810c8c0e0920910b0f07550104059d)) (.join (.leaf 16 0x801080000000000002 0x184802f01058107a1e531841) (.leaf 16 0x800000000 0x7aa))) (.join (.join (.leaf 16 0x8001000020002100003 0x10d60c6c106604cf1cdc0f8c1c0d135f1173) (.leaf 16 0x801004020002108000 0x1b69026d007a10d6105c0f8112bf16d81985)) (.join (.leaf 16 0x400008000000000020 0x9b91e96181d1ecf) (.leaf 16 0x8000000200040400020 0xcf008e80a971ec519a613d606fb0e27)))) (.join (.join (.join (.leaf 16 0x20084011000008440 0x3e807af16fc00301c130f7f08ed0a6519a510ab) (.leaf 16 0x8000004201000000000 0x11bc046a10b81cfd13fe)) (.join (.leaf 16 0x8440180000802000400 0x129141518ad033e18bc181d12020d4f05471aa8) (.leaf 16 0x400080010000200001 0x1bad10921ce3145f13901b0e))) (.join (.join (.leaf 16 0x8080080000000100022 0x7db1aed12b30e3705611232176406001bf50f7f) (.leaf 16 0x10800000200800000021 0x7aa040e1eee04df05ba07701bf21b1d)) (.join (.leaf 16 0x400000210000200000 0xcc8030b00ab15ce0328) (.leaf 16 0x8021080000840000001 0x472108e0b9b07a312fc13e203d0))))))
set_option maxRecDepth 4000 in
private theorem scan8_1536 : Region (clearPoint L8) 1536 2048 :=
  checkedPatch 1536 patch8_1536 gates8 (by decide +kernel) (by decide +kernel)
private def patch8_2048 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x441200010000000000 0x208a0599052a13b618e311d50809044e0a87) (.leaf 16 0x1000200800000000 0xb0c15f81f3a)) (.join (.leaf 16 0x220800010000 0x100a13c106cb18de17e60cc5) (.leaf 16 0x3000010040000022 0x1ec00f72041902aa1647035f19b005f9))) (.join (.join (.leaf 16 0x400000000002000020 0x10a11d3f05a2) (.leaf 16 0x180200000000022 0x121a0a1006140d3f09c0199405b3)) (.join (.leaf 16 0x8000084000000008001 0x153b0c3b10e214780b9d) (.leaf 16 0x60000220080000440 0x16a3040101cd02f91a9c13d00e8a05b412d2136301ae)))) (.join (.join (.join (.leaf 16 0x100c400000100000 0x29b165c091a05961bb00cb60210) (.leaf 16 0x8405000000002000000 0x204e1111170d13f20d3e06f004a9066b)) (.join (.leaf 16 0x80401042000000 0x8a00f74043d1c2119a5040a11ab) (.leaf 16 0x40000011040000020 0x14df089f0f650e19046a1cff12f6))) (.join (.join (.leaf 16 0x10040000001 0x7f613d31e5d) (.leaf 16 0x20080000840100000 0x6d90b7314aa0d460385)) (.join (.leaf 16 0x1000200040300001 0x46612320a8b13070ffc0c1e1867) (.leaf 16 0x402000200002010800 0xf37209a123008af01b40a4605ac160413d0))))) (.join (.join (.join (.join (.leaf 16 0x1000200002000000 0xf5c09ce0ff8) (.leaf 16 0x421004400040018003 0x10cd1a371c2b01ef0d400a9119821e790c04075d1fde142311bc)) (.join (.leaf 16 0x8800000010002100021 0xe641ea7100a16131f520d46170f087e) (.leaf 16 0x8000000000082400000 0xdee099200a105091985190c0f580b23))) (.join (.join (.leaf 16 0x802000c010840100020 0xa8b18081c47124e066e1b6505510b9c0bb70ed5) (.leaf 16 0x210000100021 0x166e19e51f6704a618b3)) (.join (.leaf 16 0x420080002000000400 0x60e076c171f1a5117330cce0a87179c) (.leaf 16 0x2004010800000022 0xb4b075d1e6b16fa126811d21ef50cdd)))) (.join (.join (.join (.leaf 16 0x30002000c0108403 0x1cdc19be0bba0fed1b2c0cb6026714540b70093a1b781ae7021e) (.leaf 16 0x8020000000041 0x18ad01e711510861071e0658105b)) (.join (.leaf 16 0x200080120020 0x1d84202320080c261ec1170b103600ca1563) (.leaf 16 0x200200040000402 0x202317e610e209f207f515da152b0f4b0d49))) (.join (.join (.leaf 16 0x80210800100000 0x1f321433041a16f91c97) (.leaf 16 0x20180000002010400 0xc7220421f401d691e3211630b8d13ee)) (.join (.leaf 16 0x800008010000000021 0x18fb12821a090e2d078701a90f84) (.leaf 16 0x8881080010840008421 0x72b20011ac11c8b157d05ea0280196a0a6e148503bb0bc01a271c5e158503e6))))))
set_option maxRecDepth 4000 in
private theorem scan8_2048 : Region (clearPoint L8) 2048 2560 :=
  checkedPatch 2048 patch8_2048 gates8 (by decide +kernel) (by decide +kernel)
private def patch8_2560 : Patch :=
  (.join (.join (.join (.join (.leaf 16 0x8040004000000108000 0xad90be50aac09150677007f) (.join (.leaf 16 0x210042008000 0x5700db20272150a05df) (.leaf 16 0x441004001800000040 0x260209c1f060f3e023310e50a540535162b02cf))) (.join (.join (.leaf 16 0x2080000040000400 0x1ed61b770f4d1ac3046a) (.leaf 16 0x8000080201080100001 0x12ef1d32150b0d4605841a12111f0aa61dc9)) (.join (.leaf 16 0x4000802000041 0x1fc108b100c21343038907ac) (.leaf 16 0x8005000600800100421 0x20301fd3171114b611240a991cf90fdf09610b04030c1b830fc30be9)))) (.join (.join (.join (.leaf 16 0x8400000011044010001 0x992109a10be04e804760674178a0c5314150cf00885) (.leaf 16 0x8000004400002008000 0x4fd121f1b95041916891661)) (.join (.leaf 16 0x8000000410040200020 0x5290eb703bb00441e9516a60dee15f8) (.leaf 16 0x100010002100c2008420 0x10b50f301c61144c0f311d48135b0ce40d5b10e201211d15))) (.join (.join (.leaf 16 0x1000010000100002 0x1730272030e1c3a0416) (.leaf 16 0x2000001000210020 0x1d5917db1589049e18800b791f97053508d3)) (.join (.leaf 16 0x400040000002 0x1e87037d031a094b01a1) (.leaf 16 0x802000002 0x646085b14e71205))))) (.join (.join (.join (.leaf 16 0x60000400000010000 0x1e53072301e51ee81472117d0800) (.join (.leaf 16 0x200200840000c0100400 0x1f44158a081b075e0359085c16341e2a190b10fe0f1a06e0) (.leaf 16 0x8041004010002000020 0x1c0413b501b7088d1a271a6d05030f1c))) (.join (.join (.leaf 16 0xc20004000802808000 0x17b71055025101f811e80278066e1e21154212b30fa80f24098a07fb02ab1231) (.leaf 16 0x80210802000040 0x940ae6123113eb04010bff07bb)) (.join (.leaf 16 0x4011000010001 0x49a022b1a001274180e07701a2a) (.leaf 16 0x10001080200880200020 0xe0503801d4118ef059e063f15ce13cf1e02151809bf)))) (.join (.join (.join (.leaf 16 0x8000000210002008800 0x901ac70c4613f71f220cc70c26) (.leaf 16 0x4000040100440 0xaa60f5f069217841e410856)) (.join (.leaf 16 0x402000200002000441 0x16670f2b0037077915f819be09d8057f1324) (.leaf 16 0x8002100400084008000 0x980013500381ffd061f1b7517b81cc41137105b0a910bd9))) (.join (.join (.leaf 16 0x800000200000100401 0x11c909f810821acc18930f17) (.leaf 16 0x8001000210040000000 0x17c604a9099520841274)) (.join (.leaf 16 0x800000020042008001 0x8fc027d15490c430f9f1f781b470885) (.leaf 9 0x2100400 0x16ee13a51e2f))))))
set_option maxRecDepth 4000 in
private theorem scan8_2560 : Region (clearPoint L8) 2560 3033 :=
  checkedPatch 2560 patch8_2560 gates8 (by decide +kernel) (by decide +kernel)
private theorem rows8 : Region (clearPoint L8) 0 3033 :=
  (mergeRegion (mergeRegion scan8_0 (mergeRegion scan8_512 scan8_1024)) (mergeRegion scan8_1536 (mergeRegion scan8_2048 scan8_2560)))
private theorem clear8 : Clear L8 := clear_of_scan (by decide +kernel) (rows8)

private def L9 : Chart := ⟨6497, 66612250569, -438359, -80241, 111720, -605167, 3465, 2506⟩

private def g9_29 : Gate := ⟨29, 8, 0x13d122f3, #[
    0x4000, 0x6218c23, 0x120783c0, 0x370076, 0x8552095, 0x19990884, 0x1ede0000, 0x10608e38,
    0x4cc9803, 0x49920d8, 0x50c2929, 0x120904b6, 0x5502a8a, 0xa1c3850, 0x12a12152, 0x95090a9,
    0x143870a, 0xa2a8154, 0xda41209, 0x12928614, 0x3609324, 0x18032664, 0x38e20c1, 0xf6f,
    0x4221333, 0x15209542, 0xdc01d80, 0x783c09, 0x1886308c]⟩
private theorem g9_29_ok : g9_29.OK L9 := gate_of_test (by decide +kernel)

private def g9_53 : Gate := ⟨53, 8, 0xd228fccfc512d, #[
    0x1fffffffffffff, 0x1948844987804e, 0x121acb4897420, 0xc2211a1494fa0, 0x50c51048611f3, 0x11338a023062f, 0x1a9c4039061305, 0x11ea61124110d1,
    0x12ba0b0c816818, 0xcd255402819d, 0x1c0cea00c0d283, 0x83b0423868d03, 0xa0076b221e818, 0x1c994400283966, 0xb212c1aa321a, 0x8898058cdb901,
    0x452858622b344, 0x2c3cf824e8020, 0x393b300286c82, 0xea82ac5698400, 0xcc00aad002d3a, 0xb341cc6242508, 0x3004a7403e685, 0x105e594948d1,
    0x1146d06240154e, 0x18861486cc5023, 0x32828a864a0dc, 0x530760a4c2a28, 0x1847881466c250, 0x18a2e550048c16, 0x20116252534f4, 0x3142cf805ca4,
    0xb34214848c670, 0xccb968016aa0, 0x55c00432d46a8, 0x1270826c28019b, 0x10d00802e483e7, 0x1288459a88c342, 0x445013b663403, 0x1340b098ab0690,
    0x64ecd38280045, 0x14302f089adc, 0x17058162c38841, 0xc0f82960600ae, 0xcc17302805549, 0x1752302d0261a0, 0x15e3161104910c, 0xe574190c13804,
    0x1221e8c1880a39, 0xc299f10c24114, 0x110c0be5250b10, 0x120085d225a6b, 0x4a6e403c32442]⟩
private theorem g9_53_ok : g9_53.OK L9 := gate_of_test (by decide +kernel)

private def g9_59 : Gate := ⟨59, 7, 0x22b62183e7b92bb, #[
    0x80000000000, 0x45b0fd4b5df4203, 0x1f51aae220de26f, 0x6082daff9638987, 0x2717c8c9ed585d4, 0x3044ed3bd8747a5, 0x405ca69cabff823, 0x130bff0f46ec115,
    0x133ea195b183ade, 0x36229dda72d25d2, 0x2171a9f64b9be28, 0x4b5ce83a7a8ac99, 0x77f5dc28c2f4888, 0x4065ce1761aea7d, 0x45cfaaba11ba616, 0x378ad619de0a4ab,
    0x1ea8dc479762cb4, 0x3ab0f248d5bc74c, 0x4d18c3b7b2c96f0, 0x23a69b215bfb0a5, 0x7e16ddc2ee2920c, 0x38a59f5dbc4c892, 0x66a4ed841e9c3bc, 0x794690f1279745b,
    0x6f73a6a40c85e55, 0x4d6ad53cccf81a4, 0x3c67e4e9573e280, 0x12f381cdceb548e, 0x34fec9c89bcc065, 0x1a639881fe7cb62, 0x408ce32c46d3e7f, 0x9c9bf96a6033d9,
    0x59c0e7a4712ad73, 0x4b93f31e0147cea, 0x1e55ab592581f33, 0x12b2e77baa7a130, 0x4784b14fda2e9e4, 0x10db92b33dc3978, 0x5d7cd28e491323d, 0x21ddb43f3049477,
    0x426cb2e2a50dfda, 0x76e18c590f6934d, 0x92786ae32e3dab, 0x711d8abc2d346e9, 0x4c35a8f6d52507b, 0x2eaaf9d16865d88, 0x7439d301be57586, 0xa1dd7f71112f43,
    0x2e0b9d69993515e, 0x37cac742147d9d2, 0x2ddca2364ba4b4e, 0x54c2be647b5c18d, 0x787fe864a883762, 0x1cb29d01c41ffd5, 0x6e5b9106a5e2e1b, 0x4989f4722ba1ab7,
    0x7fada083e191c69, 0x23aac57cf647b04, 0x695f86d1c042fba]⟩
private theorem g9_59_ok : g9_59.OK L9 := gate_of_test (by decide +kernel)

private def g9_47 : Gate := ⟨47, 8, 0x7bcae4d8ac21, #[
    0x7fffffffffff, 0x3d07bc594658, 0x6207d37c06f8, 0x30dc9a3b6e60, 0x7dee94f56, 0x466d3b3a0b58, 0x36de92d103d1, 0x588d6e9234ad,
    0x220ff6779510, 0x57b44a3732c4, 0x51ce379495b, 0xb8615e0d57e, 0x3455ba6136ca, 0x557c09bd0798, 0x10b64d9f38e1, 0x5cfc508939d8,
    0x283775650747, 0x4e87f5874605, 0x71e48e1309cf, 0x2e16f1aac38a, 0x625c3729e558, 0x2ad54cee687, 0x5a2722eed522, 0x5b6ce4847866,
    0x24e6db598788, 0x689c8b512add, 0x6556a83859dc, 0x1d8748c6a9e5, 0x31ed0e9470d5, 0xe24f1fce432, 0x35fc2e6818b8, 0x55dd82b8b829,
    0x2147e746e724, 0x364da121c73e, 0x3207d546782f, 0x4bb54594db21, 0x750c3a1faac1, 0x58e71436a4a7, 0xa45bd48d33b, 0x4dfe08822a7b,
    0x2ed6236d4b12, 0x692f6da2f022, 0x1b96cc46b417, 0x6f7c001abca5, 0xb2761819db7, 0x597c08c7d80f, 0x47bc178698a6]⟩
private theorem g9_47_ok : g9_47.OK L9 := gate_of_test (by decide +kernel)

private def g9_43 : Gate := ⟨43, 8, 0x35883a3ee53, #[
    0x7ffffffffff, 0x65d4529d4cc, 0x4c949c361bd, 0x74a70e0fa8c, 0x8d35ed078e, 0xf149bf20ba, 0x71b816b512e, 0x315d4378365,
    0xd789fa2c85, 0x56f6c397044, 0x8935b2afd2, 0x7f3e1035846, 0x6a411db729c, 0x1f2dd453854, 0xbcd846dab1, 0x381816ce5be,
    0x3e120eea713, 0x5c099b8a74b, 0x68a6843b1cf, 0x33cbd0c41d3, 0x1d7ccb28626, 0x7545812af1b, 0x7aa40d157d8, 0x30a699f5c64,
    0x41185e9e6cb, 0x46e10b28bf3, 0x728ecc81dd2, 0x72bb8243ec8, 0x539b40c0e7d, 0x2db10d9e88d, 0xe515da7c2a, 0x276dc412b39,
    0xd6043e7f62, 0x7aa6d64884b, 0x74e1b7b522, 0x1a2fc8f58a1, 0x60f615d46a6, 0x456b40ec774, 0x27ec94785d, 0x705bd658871,
    0x2f838729731, 0x4361c9499bd, 0x15ca515d333]⟩
private theorem g9_43_ok : g9_43.OK L9 := gate_of_test (by decide +kernel)

private def g9_31 : Gate := ⟨31, 8, 0x121d47b7, #[
    0x7fffffff, 0x1705f472, 0x1d0a9357, 0x7f4a2063, 0x5388cec3, 0x2f43a42d, 0x551a46ae, 0x41eda385,
    0x2f6842f2, 0x69464b2e, 0x5d122dcc, 0x2b3d90d2, 0x1b236e32, 0x138c71f1, 0x3f459e4, 0x79d4610d,
    0x573ec218, 0x5f809e68, 0x63923e38, 0x9b131db, 0x79a92c26, 0x1174ced1, 0x452dd349, 0x2de93d08,
    0x6f068716, 0x3155d589, 0x5ead097, 0x23970dcc, 0x25ff1811, 0x2173ab25, 0x41d138be]⟩
private theorem g9_31_ok : g9_31.OK L9 := gate_of_test (by decide +kernel)

private def g9_23 : Gate := ⟨23, 9, 0x7acca1, #[
    0x8000, 0x1f2e13, 0x2b0dad, 0x3d02bb, 0x4e51b3, 0x1673e4, 0x67451d, 0x5826de,
    0x6d2743, 0x1d45b6, 0x7c3a0e, 0x476a4e, 0x2b7172, 0x2e1f70, 0x515c6d, 0x725bc2,
    0x320d7b, 0x5173b8, 0x673427, 0x4539cd, 0x205edd, 0x586ab5, 0x3a7cc8]⟩
private theorem g9_23_ok : g9_23.OK L9 := gate_of_test (by decide +kernel)

private def g9_19 : Gate := ⟨19, 9, 0x4f50d, #[
    0x7ffff, 0x43947, 0x3d621, 0xd7d, 0x2395c, 0x4b526, 0x5b22a, 0x1cd19,
    0x78323, 0x34c33, 0x36619, 0x7e260, 0x64c59, 0x6aa26, 0x4b256, 0x11d4e,
    0x5f58, 0x74235, 0xf14e]⟩
private theorem g9_19_ok : g9_19.OK L9 := gate_of_test (by decide +kernel)

private def g9_11 : Gate := ⟨11, 10, 0x5c5, #[
    0x7ff, 0xad, 0x459, 0x651, 0x343, 0x41d, 0x383, 0x42d,
    0xa7, 0x1a3, 0x351]⟩
private theorem g9_11_ok : g9_11.OK L9 := gate_of_test (by decide +kernel)

private def g9_7 : Gate := ⟨7, 10, 0x17, #[
    0x7f, 0x25, 0x19, 0x43, 0x43, 0x19, 0x25]⟩
private theorem g9_7_ok : g9_7.OK L9 := gate_of_test (by decide +kernel)

private def g9_37 : Gate := ⟨37, 8, 0x9a1dee165, #[
    0x1000000, 0x113b6eab43, 0xde714fc4c, 0x163dc5aacc, 0x1e170b12df, 0x12ad95d7c4, 0xddb5a19e4, 0xcc5e89fd8,
    0x19f2aefa1, 0x1f51e744c5, 0x6fb431973, 0x1bf13849e6, 0x196f93468b, 0xb2576d18f, 0x1abb7c42c3, 0x7c3a975c5,
    0xbfd84645e, 0xa1bcd7c5a, 0x130b563fb8, 0x18d5a191df, 0x1d67b0a5a3, 0xc437fa7a2, 0x1d2b87ca3a, 0x47dbabc34,
    0x16dd49af18, 0x593ed3d16, 0x4391fb679, 0x1185becce9, 0x5cf15fa32, 0xea9f3085f, 0x122f4661bf, 0x10b5b76279,
    0x17536a923e, 0x11a1d0ffb4, 0xb4778d335, 0x1e51cf6323, 0xaedb91c2d]⟩
private theorem g9_37_ok : g9_37.OK L9 := gate_of_test (by decide +kernel)

private def g9_3 : Gate := ⟨3, 12, 0x5, #[
    0x1, 0x6, 0x6]⟩
private theorem g9_3_ok : g9_3.OK L9 := gate_of_test (by decide +kernel)

private def g9_61 : Gate := ⟨61, 7, 0x8ec196bf5a60dc5, #[
    0x1fffffffffffffff, 0x1c8f8e24fddda939, 0x153fb46e125c3fe9, 0x3b7da9bb3b6a954, 0x3bfa2dd5f6e14c6, 0x9575eda0c3dd6e7, 0x16dbece631b3a297, 0x7ce6ec9ed428cf7,
    0x13efe2132da9c8bf, 0xf17cd5dc68a57c7, 0x8df9dbb6de3512c, 0x1e7b17ee8fcc34c2, 0x1cf2fe686e1b56d1, 0xa82d87726d9f3fb, 0x192a4e2f2d71fa7d, 0x145a7784df9f0faa,
    0x1e6ebf0604d7d63d, 0x143b927fb9dbe720, 0x48ee939dda9f95e, 0xf438afb75097bd6, 0x1deaf1b8b2e78b29, 0xbf637b8fb09d3c8, 0x1fa780dbaf2a657a, 0x146b00cef4f37f9b,
    0xa967bbb4f301f6b, 0x17e3b165c5eb724b, 0x5163df05fded31b, 0x1d7b6f41d955d6b0, 0x13721d7e437f972c, 0xf76e786aa3e80f7, 0x1cb75a8ff44c6cea, 0xad769d5cd8c8bfc,
    0xf3b77bbc05f1558, 0x15c2764d3a7fb09f, 0x17b6f5c35aeaa6e0, 0x1de3453632defe83, 0x146e3f7493b5e8e9, 0xef34ab5be033cb7, 0x1806b1767fb3cbdc, 0x180f2fd7a9953d76,
    0xf637e84f2e437c7, 0xc7abde53479d347, 0x1a8e179af7a42bb7, 0x4bb891ea7e56ee7, 0x124ee14139f6e77f, 0x7ebb3ef1afac818, 0xf72d1557c3e7ec8, 0x392a4ef97e3ad3d,
    0x10da0ab7f3e6d93b, 0x13fa79e2dab61d85, 0x1f46f3d0cb0cfc5d, 0xdcfd88d22b1edb7, 0x159f47b8fa9458ee, 0x23fbe7f44e56d32, 0x1bb39f3bcc50ade4, 0x19bedb7a51736319,
    0x1bd754b9daef0c16, 0x1a2fee18ca1dbeae, 0xadf6e0aa55b7376, 0x116fe565ff0e921d, 0x38f89e7256eefc9]⟩
private theorem g9_61_ok : g9_61.OK L9 := gate_of_test (by decide +kernel)

private def g9_41 : Gate := ⟨41, 8, 0x4c7d4af8c9, #[
    0x1ffffffffff, 0x1cb9e5b6deb, 0x11fe4df69b7, 0x1f7a1d7e747, 0xb4d3deadf7, 0x1ee7dc1beab, 0x1710bddfef5, 0xe7bdc7f3f0,
    0x19d7bdbb663, 0x164ff8f367d, 0x1eeced55b7a, 0x11dd79dcfea, 0x1477b9edeae, 0x1ffd047779b, 0x7fda81fafd, 0x1fdfd5941de,
    0x1eb6adf2f6c, 0x1da3b97b3bd, 0x1ebff16f869, 0x11f8b93bddf, 0xd3f6cdd9db, 0xdcdd9b7e5b, 0x1ddee4e8fc7, 0xb0fb47febe,
    0x1ee6f4ee2de, 0x1b7a7dab6bc, 0x1dc14d5fdfd, 0x1fafc0adff2, 0xcf77105fff, 0x1abdbcef715, 0xbf9dcf5dc5, 0xf6d55b9bbd,
    0x1f3678ff936, 0x336edef5cf, 0x7e7f1def38, 0x17bfdde8476, 0xabec1df3bf, 0x17dabde596b, 0x1173f5c2f7f, 0x16cb7d93fc7,
    0xbdb6d3ce9f]⟩
private theorem g9_41_ok : g9_41.OK L9 := gate_of_test (by decide +kernel)

private def filters9 : List Gate := [g9_29, g9_53, g9_59, g9_47, g9_43, g9_31, g9_23, g9_19, g9_11, g9_7, g9_37, g9_3, g9_61, g9_41]
private theorem gates9 (g : Gate) (h : g ∈ filters9) : g.OK L9 ∧ 512 ≤ g.p*2^vDepth g.p := by
  simp only [filters9, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨g9_29_ok, by decide +kernel⟩
  · exact ⟨g9_53_ok, by decide +kernel⟩
  · exact ⟨g9_59_ok, by decide +kernel⟩
  · exact ⟨g9_47_ok, by decide +kernel⟩
  · exact ⟨g9_43_ok, by decide +kernel⟩
  · exact ⟨g9_31_ok, by decide +kernel⟩
  · exact ⟨g9_23_ok, by decide +kernel⟩
  · exact ⟨g9_19_ok, by decide +kernel⟩
  · exact ⟨g9_11_ok, by decide +kernel⟩
  · exact ⟨g9_7_ok, by decide +kernel⟩
  · exact ⟨g9_37_ok, by decide +kernel⟩
  · exact ⟨g9_3_ok, by decide +kernel⟩
  · exact ⟨g9_61_ok, by decide +kernel⟩
  · exact ⟨g9_41_ok, by decide +kernel⟩

private def patch9_0 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0xc21 0x17840302015b07720d89) (.leaf 16 0x80000000000000 0x72f)) (.join (.leaf 16 0x8001000200000010000 0xa4f0cd012c718760dae) (.leaf 16 0x8020000010842000020 0xde60e5706e00dcd00d517cb079f))) (.join (.join (.leaf 16 0x1000000040008000 0x11e40dd3000d) (.leaf 16 0x18800000010000000400 0x143510a009050f2007150c171805)) (.join (.leaf 16 0x40008c210000000440 0xe110f4d192816b202780df8145601b5096a05b7) (.leaf 16 0x8400004001800000002 0x2710e430f2511cf0d0c057506ac0037)))) (.join (.join (.join (.leaf 16 0x8021000010006100000 0x93703db0e1d0e240fa00c4d040a0b5e) (.leaf 16 0x84010000000000 0x108d0730163f)) (.join (.leaf 16 0x8000000000802000000 0xe4207000e55) (.leaf 16 0x1022000000800010001 0x1ae113b70e2c04810ea010b700a10ff317690cd40aa5))) (.join (.join (.leaf 16 0x200800000400 0x1b000aea054b) (.leaf 16 0x22000201040108400 0x16030e9909ec021217aa0c1a111103fa0bd70e67)) (.join (.leaf 16 0x800084000800100002 0x16150c8f184f104403e71a9a06200376) (.leaf 16 0x2080000006100000 0xefd063619e50f400e8c064110c1))))) (.join (.join (.join (.join (.leaf 16 0xc010000000020 0x11b70b1101c609331ae1) (.leaf 16 0x8440004020002008001 0x161004e516ce041d124e0eb1043a086c0edd0ebf)) (.join (.leaf 16 0x20004000000008000 0x1611610012c) (.leaf 16 0x100000840200060 0xf5a0ed60c011391087a00d71730118f0125))) (.join (.join (.leaf 16 0x8400004200000000020 0x17c300770f21066b12d5) (.leaf 16 0x400000000800000000 0xefb0ed7)) (.join (.leaf 16 0x400000600084108021 0x125d165d0cd308ea164e0c1f1a5b0c1206e607e7178307c1) (.leaf 16 0x8042004020000000000 0x1ca093f081f19e50ecf0fb7199c13e5)))) (.join (.join (.join (.leaf 16 0x18401000000000000081 0x13ce09d50240084b070813580f650f2001c90ccc) (.leaf 16 0x1000210000100040 0x11540aab0f5a08a8040c0317)) (.join (.leaf 16 0x10c21100001042100000 0x13f605331a9c0aab0436009314991469132b147308580a2508ff0f45) (.leaf 16 0x80220000000000 0x174810140fa9064f))) (.join (.join (.leaf 16 0x8000004200800008001 0x6e031012560f6a170e0f58) (.leaf 16 0x8001000400040100020 0x166c0b9518b913f6157c12ff1695)) (.join (.leaf 16 0x8000008010004100000 0xfed10f70f8f13f9165b00ee0596) (.leaf 16 0x10000000020000000001 0x542039e13981071188c))))))
set_option maxRecDepth 4000 in
private theorem scan9_0 : Region (clearPoint L9) 0 512 :=
  checkedPatch 0 patch9_0 gates9 (by decide +kernel) (by decide +kernel)
private def patch9_512 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x20100210000000001 0xfb4102501ab1585149e1942) (.leaf 16 0x400080200802300001 0xbb413ba0b6a165d0a3315e510b2089904dd)) (.join (.leaf 16 0x20008400042000001 0x14981a96034f06be02bf103114c70ff5) (.leaf 16 0x401004400800100001 0x63e04240f720c910b1d10ce17130fd9))) (.join (.join (.leaf 16 0x104001000000000 0x1aa40878101005c90115) (.leaf 16 0x10040084000004010420 0xd31013f107507c316b00a0a05ac02250ffe0b1817ac1550)) (.join (.leaf 16 0xc01000010000008800 0x18b60a7907fa1999036b18a715950e0c) (.leaf 16 0x200080008000 0x873112b10230b91)))) (.join (.join (.join (.leaf 16 0x802008400 0xdd6093c11541821) (.leaf 16 0x8000000a00002208400 0x166317fc10480bf208e9075d188010b902b2036b18aa)) (.join (.leaf 16 0x400004010802000040 0x10251442109005b1005f10f40b36) (.leaf 16 0x421000200002018020 0x15ba145f106d01ab11881810146905b31267))) (.join (.join (.leaf 16 0x1108010040008001 0xab510fd0a8516140a9b004302450b8401f9) (.leaf 16 0x10021000000000000820 0x12ae1092188e17310c1d044b0911)) (.join (.leaf 16 0x42080000840000040 0x19e50d6f048a014019ad18e910c616af1160) (.leaf 16 0x1008010000100001 0x10ac04f502b5101511e51a41))))) (.join (.join (.join (.join (.leaf 16 0x100000000001401 0x146306d61927114110b70d0a0b320c0f) (.leaf 16 0x8801080211000000001 0xb9f1a130621030d081f17ff008718fb0ed70946)) (.join (.leaf 16 0x20000010002000000 0x69c03c710dc) (.leaf 16 0x180210000008401 0x15a309d601631185151f124207cd112b))) (.join (.join (.leaf 16 0x8421004010000008020 0xf7f03270a3006c10475110113270a1e) (.leaf 16 0x401000000040100000 0x1a6307cd18cd0bbe)) (.join (.leaf 16 0x20100000000200000 0x165a11260cec06f4031c) (.leaf 16 0x8020080000800000401 0xa00094c0afb10ab129f11c9)))) (.join (.join (.join (.leaf 16 0x401100000042000001 0x114b12980700058d1a9202841127) (.leaf 16 0x400000000004108400 0x13de14f801e5014e199b1723)) (.join (.leaf 16 0x210802008000 0x14ae1875120d08f104e5) (.leaf 16 0x8000000020046000840 0xfaa11c609a110b81aa8197b103d1a63066412fc1170))) (.join (.join (.leaf 16 0x20000010000000020 0xb720da20ea4) (.leaf 16 0x8400000000000308001 0xadb1251146511950ec20deb1a69)) (.join (.leaf 16 0x8000000200000008000 0x6bf154c006e) (.leaf 16 0x400000010800000022 0x1672187011ba049319a71359))))))
set_option maxRecDepth 4000 in
private theorem scan9_512 : Region (clearPoint L9) 512 1024 :=
  checkedPatch 512 patch9_512 gates9 (by decide +kernel) (by decide +kernel)
private def patch9_1024 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x4000002008000 0x9761173000b) (.leaf 16 0x10401084000084000400 0xc01050f07700de414a711df12c10a5e12950e900d90)) (.join (.leaf 16 0x10400088020004100000 0x13b60924106a175917fe06dd13db03a90a6a0490185e) (.leaf 16 0x22084001080018400 0x1204161609df0b670c320d1b0a8719eb177a1a9b12d7065e094b))) (.join (.join (.leaf 16 0x1184000042000021 0x12d90acd0a2102f011640674150e08881261) (.leaf 16 0x400004200800000020 0x196a1564139e17ea1169)) (.join (.leaf 16 0x400000000000008002 0x1413161912290664) (.leaf 16 0x802108c00 0xab0e09115b1283190c0b9908b1)))) (.join (.join (.join (.leaf 16 0x800000000800010021 0x16dc094413fc131d124e0a840b52) (.leaf 16 0x8020000200040100001 0x1055166c17b3036712970e02)) (.join (.leaf 16 0x60100000080000000 0x14700672026d188e075b127308a7) (.leaf 16 0x400008000802200400 0xcd9136101fd023e0b4d19f6068b0460))) (.join (.join (.leaf 16 0x22080410000200001 0xa2519b4011804ef161c129812fc0e8f07c404b8) (.leaf 16 0x2000000000100002 0x769026b18ea120411c8)) (.join (.leaf 16 0x2000000044000000 0x14cd12bd09990c730896) (.leaf 16 0x200000000420 0xaf7035d13a5))))) (.join (.join (.join (.join (.leaf 16 0x8400004000040000400 0x12e20e2304ef151f0550) (.leaf 16 0x40080000000100020 0x1964082a183d122c0cec)) (.join (.leaf 16 0x80210000000000 0x152a175713e9) (.leaf 16 0x401000220004009800 0xb4e025a14bf1a5a056c19a6111d0f8f130711fe0f3a0a5b04490131))) (.join (.join (.leaf 16 0x2000801 0xcef145f08e312f6) (.leaf 16 0x10021000000002200001 0x142d124a0ba112c1132c1afb01881397)) (.join (.leaf 16 0x4000000008800 0x158706c71a6c1745) (.leaf 16 0x40000020006000000 0xcd300ac13510bda128b0b5f048a)))) (.join (.join (.join (.leaf 16 0x400040000020 0x6c70626097f054b) (.leaf 16 0x20080010082200000 0x3b1137607e11471078112e514f407ad)) (.join (.leaf 16 0x20000210006308400 0x19ae15e40908159b085107400ab109f8028400870499) (.leaf 16 0x10801000201840000020 0x182003eb17d3139b0c2810a017a4095506070bb6115f))) (.join (.join (.leaf 16 0x22004000004000800 0x14b514030be004fe12e301ab15370740) (.leaf 16 0x4010000000001 0xd551432056a)) (.join (.leaf 16 0x80210000000440 0x19fb044916410dc813c00380) (.leaf 16 0x10000000002 0x13cf12a10ac4))))))
set_option maxRecDepth 4000 in
private theorem scan9_1024 : Region (clearPoint L9) 1024 1536 :=
  checkedPatch 1024 patch9_1024 gates9 (by decide +kernel) (by decide +kernel)
private def patch9_1536 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x100200000400001 0x111107300b2514f913e50c8b08db0a95) (.leaf 16 0x20000200040010020 0x26e027b00230a5b05e1097f)) (.join (.leaf 16 0x8400000201004000021 0xf6a102511bf169e140a09cd01bd155d0503) (.leaf 16 0x8421080000040000000 0x38709b5104c1704153d02b5))) (.join (.join (.leaf 16 0x8000084000840008001 0x16c0072c142f16181a8c0e750268) (.leaf 16 0x400084000000008000 0xb5003dc080a14dd)) (.join (.leaf 16 0x8040080010040100801 0x16cb1924145412c5005816fb021115b0013c14cd) (.leaf 16 0x21080000040000400 0x10ed13cc018c06231581)))) (.join (.join (.join (.leaf 16 0x220040100400 0x25917bc07f018c5169206b3) (.leaf 16 0x820004210800000001 0x1175049c111706d719861250178a1479)) (.join (.leaf 16 0x423100a10002000020 0x1344182c1a2416780c3a0aa106451a0f185e16cd15c5132a09f31758142d) (.leaf 16 0x10000000421002020000 0x1ab700a10c9b024716d20211118808340380198a149e140f0445))) (.join (.join (.leaf 16 0x20004010800000400 0xe3816a0005f0a6d17cc) (.leaf 16 0x420004000080008000 0x151e11b412ca14c30c4f02de)) (.join (.leaf 16 0x420000020002118021 0x13cd14e816dc156814ba17b516210fe50c9b0c0f1609) (.leaf 16 0x400008400040000840 0x677050f00b614e80636086d1a380bf20f1109ca))))) (.join (.join (.join (.join (.leaf 16 0x420004001000000041 0x30c09fb05f6155c0e0913e811bd14c5) (.leaf 16 0x21000011080000020 0xc81150d17a7191a164d0f9400771905)) (.join (.leaf 16 0x84000040008000 0x14530c980f121812) (.leaf 16 0x18001000400800000020 0x153210a60d881a330f5e0b211564159b))) (.join (.join (.leaf 16 0x8000840100c2008400 0x16910bfc0ceb0459025610de0ba40a660c010c5b08c8) (.leaf 16 0x80410800000000 0xc2c099c07a111721537)) (.join (.leaf 16 0x10002004000040000800 0x1484075d13e711aa12f1198a186f1557) (.leaf 16 0x8420080200000000003 0xb3611cb13e308b910d5160315d405b9)))) (.join (.join (.join (.leaf 16 0x8400000201008000401 0xa205c218ea1ac804db16d51601157c15110fbf09d8) (.leaf 16 0x4000002000022 0x95b0e70076617a80dbb)) (.join (.leaf 16 0x8020080020080000022 0x14e910111a2315a10ffb12e20e4d18cc111e0bfc) (.leaf 16 0x421000000000000040 0x82d0fb61719173305c2))) (.join (.join (.leaf 16 0x8002184000000008000 0x6d610820b0e15c60edf08c40ede1570) (.leaf 16 0x200000008400 0x17e70c7d12a4)) (.join (.leaf 16 0x400000000802010021 0x15eb053c03df17ca06900b001929) (.leaf 16 0x20080010000008001 0x133908f1169e175d0268))))))
set_option maxRecDepth 4000 in
private theorem scan9_1536 : Region (clearPoint L9) 1536 2048 :=
  checkedPatch 1536 patch9_1536 gates9 (by decide +kernel) (by decide +kernel)
private def patch9_2048 : Patch :=
  (.join (.join (.join (.join (.leaf 16 0x4200000010002 0x155d10ed0aab00bf168812ac) (.join (.leaf 16 0x8020080000000200020 0x19860fee0556056301c01610) (.leaf 16 0x2010200800100020 0x17f9073317a1148a0f970bbc05e910be0d97169d))) (.join (.join (.leaf 16 0x402080020004100000 0xa790a2e015719790e3f0bb40ba102e11635) (.leaf 16 0x20004200000000020 0x277074b077a1a57)) (.join (.leaf 16 0x801004000802100002 0x19e304bf134b04e4165a0a5900311a2d0676) (.leaf 16 0x8010000000c2208040 0xcad078500d61ae618250f7a1018050d0132163017e5047d)))) (.join (.join (.leaf 16 0x40084010840108000 0x28a006a0ac4167f0635101b09450adb0021) (.join (.leaf 16 0x20000000040008481 0x83f18aa0be9038711410d5a04c902d11739) (.leaf 16 0x80400800100c0100400 0xa1b1a4016a40bda1829146e081106b9153f14ec))) (.join (.join (.leaf 16 0x40080000000108420 0x1891036e13a808ae190e15491126) (.leaf 16 0x40000000000100800 0x15be074010b819b31740)) (.join (.leaf 16 0x8400000000800000003 0x186d0f100d3b16c916941456) (.leaf 16 0x1000200004000000 0x1a9d003f059f0442))))) (.join (.join (.join (.leaf 16 0x4212040208041 0xe890c53152d15a110af0f200bb3177d09a903d916ee03bc03280abe) (.join (.leaf 16 0x100010000100000 0x176201ea171e16f2) (.leaf 16 0x800000210140000401 0x1a6f0508059a17d418b117130c0c068400fc077f091b))) (.join (.join (.leaf 16 0x2080000800100000 0xcca04ff1afa04581780) (.leaf 16 0x20000210000008421 0xb28173817a5084e0caa05a00e7b)) (.join (.leaf 16 0x420000000800100401 0x132118f506c1190c162200c0) (.leaf 16 0x10002000200842008000 0x18a914d7175d03c514ab14c5109011731b0e)))) (.join (.join (.join (.leaf 16 0x8420004000040018000 0x674045a07cb0d68012d19b114ce0a9c) (.leaf 16 0x8400004200000000020 0x1782010a0911052216ab)) (.join (.leaf 16 0x8001000000000400020 0x33d0c2919391730139009bc03df) (.leaf 16 0x10000080020800000000 0xd9f058002360f9501ff1347))) (.join (.join (.leaf 16 0x84000002000401 0x8fc06c108bf17a7186f) (.leaf 16 0x80000042000002 0x197d15d0081f167f1607)) (.join (.leaf 16 0x8001184210002008421 0x283045811330e0503b605d61879014917cc1aba125802700632) (.leaf 11 0x8000802008000 0xb5d03a30c5618aa0348))))))
set_option maxRecDepth 4000 in
private theorem scan9_2048 : Region (clearPoint L9) 2048 2507 :=
  checkedPatch 2048 patch9_2048 gates9 (by decide +kernel) (by decide +kernel)
private theorem rows9 : Region (clearPoint L9) 0 2507 :=
  (mergeRegion (mergeRegion scan9_0 scan9_512) (mergeRegion scan9_1024 (mergeRegion scan9_1536 scan9_2048)))
private theorem clear9 : Clear L9 := clear_of_scan (by decide +kernel) (rows9)

private def L10 : Chart := ⟨4777, 2378092411, 268025, -9122, 81689, 403935, 5905, 3370⟩

private def g10_13 : Gate := ⟨13, 10, 0x9e5, #[
    0x1fff, 0x1500, 0x111, 0x830, 0x421, 0x1204, 0xe0, 0x1003,
    0x490, 0x242, 0x106, 0x844, 0xa80]⟩
private theorem g10_13_ok : g10_13.OK L10 := gate_of_test (by decide +kernel)

private def g10_61 : Gate := ⟨61, 8, 0x1713e6940a59f23b, #[
    0x2000000000000, 0x41cf06543d89dc0, 0x15bc2e951f088842, 0x1ef12d6d2091a110, 0x12ac062e2188c4ef, 0x8ccc6be2f62800a, 0xe9096689a388751, 0x13bc084e3c70426c,
    0x162c050b076f5611, 0xc05403190e5b9dd, 0x19686c0a22ae432b, 0x1684a2882fa545e8, 0xd4248b5b3031f3, 0x5107ce47a81cc1a, 0x3f80120496f06bd, 0x941b4a3e0c65da,
    0x136d5119c032945a, 0xa0c34c4dadaa0f0, 0x5499c541795b1c0, 0x860b9249792a996, 0xe654b2850665706, 0x49c9682e4a112f3, 0x144933033564067b, 0x1b3043d461a61a49,
    0x18d802583572d8a3, 0x196c61dcc0046e07, 0x4801fad2a1c4ae6, 0x1b11e5136506ad04, 0x1be55001c6551835, 0x998f28a0dcb6062, 0x8d01e39d3642ab, 0x1c058835509b2e71,
    0xa78cc9181b4ec14, 0x553eeb062a98e0, 0x53c46c82d5829b2, 0xfc00919d48e152d, 0x1c31b4f81d8800ce, 0x1200d8f146d3ab06, 0x1e1066e49619618a, 0x66491779809ab30,
    0xb49c933d22149d0, 0x69533983a998285, 0x4e8309a65527a49, 0x11cc9500e36a7a0a, 0x19618283c156d6c8, 0x455b6568a5300e6, 0x16c14816e98c1f14, 0x400fe2f583da481,
    0x19f045160ce05789, 0x9215833e30336b4, 0xa290b45e8a97d04, 0x1b0b4f5309d5114, 0x1501aee769c263, 0x501a3621abdb834, 0x1081ee4d90838f1c, 0x13484ba2b8471645,
    0xb1998940051bd1f, 0x301aa7dc8c4611d, 0x15a47bc22162412d, 0xba1ed5084443e2a, 0x1079c100ee46f0a9]⟩
private theorem g10_61_ok : g10_61.OK L10 := gate_of_test (by decide +kernel)

private def g10_41 : Gate := ⟨41, 9, 0x1b382b50737, #[
    0x2, 0xd1ce65c150, 0x1ce8549d85, 0x14b41d11e64, 0x18874bdb00c, 0x9a5fc91118, 0xc491ee0a5c, 0x150036e7661,
    0xf8b2854439, 0x14f6a3b070, 0x30d184d5f4, 0xa7492bc20d, 0x3e043248fd, 0x189964a8e68, 0x16e4a8a0b45, 0x4f25e0c4e1,
    0x11dd81943b0, 0x157404bac1c, 0x2e6954f91, 0x160862b5ccc, 0x9689cead8, 0x1b573916900, 0x133ad461069, 0x9f2a967404,
    0x1835d202ea9, 0xdc2981bb88, 0x72307a4f24, 0x2d0515276d, 0x16715269918, 0x1f124c207c5, 0x1043d492e55, 0xfab218b0c1,
    0xe0dc56f280, 0x1c22a14d1f4, 0x66e76c00ac, 0x1a507789231, 0x188893fa590, 0x100dbd2e119, 0x6788b82d29, 0x1b92a17385,
    0xa83a6738b0]⟩
private theorem g10_41_ok : g10_41.OK L10 := gate_of_test (by decide +kernel)

private def g10_37 : Gate := ⟨37, 9, 0x165e211e9b, #[
    0x400000, 0x138f4481f5, 0x1fec8e1a8, 0x14d846dd23, 0x15f361017a, 0xb45e50c6d, 0xd8242f34f, 0x18d2756ec0,
    0x149ef2262a, 0xa6ce2178b, 0x84f78cca3, 0x1b17d86ac, 0x2986a9b7c, 0x1113ea3cb1, 0xe38546c5b, 0x1457cc8f14,
    0xf53763218, 0x123d4dd2c2, 0x1be1729886, 0x329d0fb61, 0x976578943, 0x98dd95e18, 0x1e267d4528, 0x6c5438eda,
    0x78af9118d, 0x1b2ac3283e, 0xc37d1b035, 0x663de42c5, 0x1d08e6cad1, 0xc89ef2554, 0xed5c96303, 0x19e84836f2,
    0x614f45ab6, 0x1010d9f55e, 0x176c4365c4, 0x10e26ff015, 0x10245e39af]⟩
private theorem g10_37_ok : g10_37.OK L10 := gate_of_test (by decide +kernel)

private def g10_59 : Gate := ⟨59, 8, 0x22b62183e7b92bb, #[
    0x20, 0x39c05e2e71f5943, 0x3e5e95aa89b5c84, 0x21fbf6157e44348, 0x627561b7ccb9344, 0x63cd388293b3cda, 0x8cabf5c5d53c83, 0xd890b57f90d78b,
    0x4be86973b1c29c5, 0x7683c011a6be3db, 0x1360d7a792fc2ca, 0x49572fa539d5309, 0x3c0cad8cc6fd711, 0x5019c2d65edf551, 0x1eafb484388ef13, 0x47dca50b6d43d1c,
    0x47a6d5ec0364b95, 0x197516f215687d9, 0x15f34e22ff02a8b, 0x567842cd9b1394f, 0x1ab0d36aad137c6, 0x41704af1e36fa59, 0xd86b1b9d8c7d46, 0x393282ff771a303,
    0x2c7d0a2faccf948, 0x760336e64a187db, 0xf18aa3cbf88cd9, 0x732cb4daa02d9d6, 0x1c17e4657e7b848, 0x65d82e6fb471a84, 0x638b7d9d06e990a, 0x779fa989fa0e090,
    0x6d0156cb4d33b5c, 0x447f4f15463c4d9, 0x61499db301bedf, 0x7ccd7d142f8d094, 0x163bbfd05327606, 0x78c6e763586c315, 0x7db1e3d483a0cd2, 0x322d55b2c35631f,
    0x72366cd0879af94, 0x503fd11cb3ea68a, 0x5aa13da2ba64df, 0x49b00dead978d4e, 0x70adb4294ef89c5, 0x5c47084b7d5e647, 0x3ede9ad0e602c55, 0x2fd8cc6d4c0f447,
    0x2ae7297d3aa4c86, 0xfd2797ac1b229a, 0x1f596200f05bede, 0x50e373a585f4d1c, 0x2c27fab4246c68f, 0x72ae8ebf54c4609, 0x737250472cf1ad9, 0x274cfb61ab91916,
    0x89faa1bf7e1096, 0x6b64556a5e9f109, 0x6be39d1e80e7614]⟩
private theorem g10_59_ok : g10_59.OK L10 := gate_of_test (by decide +kernel)

private def g10_47 : Gate := ⟨47, 8, 0x7bcae4d8ac21, #[
    0x7fffffffffff, 0xc320fde43b6, 0x341a8b7d47d0, 0x53e0206cdb57, 0x253ba3147dc4, 0x7e208c4ef623, 0x728a322ad96b, 0xd1b1b729695,
    0x3fb7b03424c8, 0x5325aa916cf8, 0x3a29094aebf1, 0x15b714e1781d, 0x23923c9ab933, 0x66c63e70fc04, 0x73c87365699, 0x1267b6ef4054,
    0x1c75b4803eea, 0x51cd9541cba6, 0x38e5bb918c2c, 0xd6832dd87ca, 0x398eab066b31, 0x61d501eaf14b, 0x3ed406e3588e, 0x1a5f092e3729,
    0xe921f4b253b, 0x58ec056f9c46, 0x6af01570f4a3, 0x4c1aae33a335, 0x376982d614f8, 0x313bb4e38d0c, 0x705536715974, 0x25b5c715df,
    0x5eedbcc90a80, 0x4d9c279c265a, 0x61cf8c6cc80f, 0x2b278938b327, 0x50e51db52e07, 0x6a52128ba3f5, 0x512ab49947cd, 0x581bdbf84c9,
    0x29db1b162a5a, 0x6a898a29f5a6, 0x6e46208ff11b, 0x4518bb9488ef, 0x66c080f97ab6, 0x57da2b0582f8, 0x4f7e09861b70]⟩
private theorem g10_47_ok : g10_47.OK L10 := gate_of_test (by decide +kernel)

private def g10_43 : Gate := ⟨43, 9, 0x35883a3ee53, #[
    0x4000, 0x49d64f26b92, 0x61dc30f99f, 0x6fd8a8d58a8, 0x56ab40b55ad, 0x44bba454fca, 0x1990b6eeda1, 0x1df4a52fb80,
    0x4ca299e6667, 0x334e7505739, 0x718c84c63f7, 0x326c9af40bd, 0x19471f1f1c5, 0x66f204f66c6, 0x11044b9ff9d, 0x4d617557435,
    0x387ad787252, 0x340596bcf5a, 0xfc6682cc7e, 0x6e07e0774a5, 0x3a2ebc0f03d, 0x4f5928a4d79, 0x1af33d64a29, 0x745d781e07a,
    0x60774a5dc0f, 0x63f0fc6682c, 0x202cb5e7ad3, 0x5e1c949c3d6, 0x6b3585d55d, 0x208973ff3a4, 0x4f66c6cde40, 0x6299471f1f1,
    0x364d7a05eb2, 0x318fdf8c642, 0x72cd39d415c, 0x4533ccccf32, 0x2fb803be94a, 0x9990b6eeda, 0x5d22a7e544b, 0x556b6b55a05,
    0x1bf62a3562a, 0x3861f33e187, 0x6b9293ac9e4]⟩
private theorem g10_43_ok : g10_43.OK L10 := gate_of_test (by decide +kernel)

private def g10_31 : Gate := ⟨31, 9, 0x6de2b849, #[
    0x8000, 0x40a4fceb, 0x5c65eaa1, 0x2149975f, 0x6c23edc8, 0x5d22c4e7, 0x31d7922e, 0xf24cfaa,
    0x584af9e2, 0x1e0cacf3, 0x5c1de564, 0x235ba6b4, 0x267e960d, 0x7d8d2d5, 0x4c64a1fe, 0x20fb9897,
    0x748cef82, 0x3fc29319, 0x55a58df0, 0x5834bf32, 0x16b2ed62, 0x1353dc1d, 0x679a983c, 0x23cfa90d,
    0x2af99278, 0x3a24f5c6, 0x7391a25d, 0x9dbe21b, 0x7d74c942, 0x42abd31d, 0x6b9f9281]⟩
private theorem g10_31_ok : g10_31.OK L10 := gate_of_test (by decide +kernel)

private def g10_23 : Gate := ⟨23, 10, 0x5335f, #[
    0x20000, 0x7198b3, 0x11e1f5, 0x40de5e, 0x55ee41, 0x28f6ca, 0x47dba, 0x75a46c,
    0xcaa7b, 0x6d8b86, 0x343b8e, 0x54d15d, 0x595ba8, 0x61671d, 0xdb61d, 0x298de5,
    0x2d7362, 0x7105db, 0x78a536, 0x3d5827, 0x5817a7, 0x3c4af8, 0x4c7cd1]⟩
private theorem g10_23_ok : g10_23.OK L10 := gate_of_test (by decide +kernel)

private def g10_19 : Gate := ⟨19, 10, 0x4f50d, #[
    0x7ffff, 0x6b47, 0x129da, 0x17b88, 0x71cc2, 0x545b4, 0x62e8a, 0x1b73,
    0x702e5, 0x73648, 0x67126, 0x7a74, 0x40ced, 0x23517, 0x152da, 0x47433,
    0x7411d, 0x245b9, 0x30e2d]⟩
private theorem g10_19_ok : g10_19.OK L10 := gate_of_test (by decide +kernel)

private def g10_11 : Gate := ⟨11, 11, 0x23b, #[
    0x7ff, 0x6e, 0x15a, 0x585, 0x598, 0xa7, 0xe5, 0x519,
    0x5a1, 0x45a, 0x76]⟩
private theorem g10_11_ok : g10_11.OK L10 := gate_of_test (by decide +kernel)

private def g10_7 : Gate := ⟨7, 11, 0x69, #[
    0x7f, 0x49, 0xe, 0x4a, 0x25, 0x61, 0x26]⟩
private theorem g10_7_ok : g10_7.OK L10 := gate_of_test (by decide +kernel)

private def g10_3 : Gate := ⟨3, 12, 0x3, #[
    0x2, 0x3, 0x6]⟩
private theorem g10_3_ok : g10_3.OK L10 := gate_of_test (by decide +kernel)

private def g10_53 : Gate := ⟨53, 8, 0x12dd703303aed3, #[
    0x1fffffffffffff, 0x579b9d67d27bd, 0x1fa7ecd277ec38, 0x13c3dfc1fdef11, 0x1943e43afcd7fb, 0x107cf6d46ed6ef, 0xfd5c0a5ff45fb, 0x5beabcbe2dfc6,
    0x1aeab7b97741ee, 0x1fd69216fb2f76, 0x1e7b6ee053fb4e, 0x16ae58be63ff55, 0x8abb2cfff766a, 0x16fd93caf1bb2b, 0x1bbd4b1778bbcd, 0xa63dd695efee6,
    0x14ff3f2cdedcc8, 0x1b4727d77f35e1, 0xe9a8e7bff3699, 0x1c65ad5de7e45f, 0x13d97a2ac6bdf7, 0x1af4fbfe58d187, 0xf899df2d89fd7, 0x1bdff17c661b4e,
    0x1e1b635d5ddcfc, 0x171d9ab7e7e687, 0x69763b3deaf3d, 0x5979eaf79b8dd, 0x3bc2cfcfdab37, 0x1e7e7775758db, 0xf6e5b0cc7d1ff, 0x7dd7f2369f732,
    0x1d7c31634ffbe5, 0xf3df7ac6a8bd3, 0x18ff44fcf756b4, 0x5d32d9ffbce2b, 0xb70f59fdd7c9c, 0x1ca2676f669f9f, 0x194cefef52d778, 0x17767ba3dd1a57,
    0x1dba9bb1ea7937, 0x144acddffe69ba, 0x15b55ff8cfa34e, 0x19ee5bf940eedb, 0xfedde9bed092d, 0x1d6ef05dd3bdaa, 0x168c7f68fa7aaf, 0xfdbf45ff4a075,
    0x183eed6ec56de7, 0xa7bfd67eb84f8, 0xf311ef7f07f78, 0x17e386fdc966fc, 0x1a97bc97cd73b3]⟩
private theorem g10_53_ok : g10_53.OK L10 := gate_of_test (by decide +kernel)

private def filters10 : List Gate := [g10_13, g10_61, g10_41, g10_37, g10_59, g10_47, g10_43, g10_31, g10_23, g10_19, g10_11, g10_7, g10_3, g10_53]
private theorem gates10 (g : Gate) (h : g ∈ filters10) : g.OK L10 ∧ 512 ≤ g.p*2^vDepth g.p := by
  simp only [filters10, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨g10_13_ok, by decide +kernel⟩
  · exact ⟨g10_61_ok, by decide +kernel⟩
  · exact ⟨g10_41_ok, by decide +kernel⟩
  · exact ⟨g10_37_ok, by decide +kernel⟩
  · exact ⟨g10_59_ok, by decide +kernel⟩
  · exact ⟨g10_47_ok, by decide +kernel⟩
  · exact ⟨g10_43_ok, by decide +kernel⟩
  · exact ⟨g10_31_ok, by decide +kernel⟩
  · exact ⟨g10_23_ok, by decide +kernel⟩
  · exact ⟨g10_19_ok, by decide +kernel⟩
  · exact ⟨g10_11_ok, by decide +kernel⟩
  · exact ⟨g10_7_ok, by decide +kernel⟩
  · exact ⟨g10_3_ok, by decide +kernel⟩
  · exact ⟨g10_53_ok, by decide +kernel⟩

private def patch10_0 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x40000000802000001 0x17940636007604431711) (.leaf 16 0x1004000000000020 0x1e9a181705d4)) (.join (.leaf 16 0x400000000840000401 0x24d0189a1e8e13a4262a) (.leaf 16 0x8000000010000300000 0xfcd26232c52191d014a))) (.join (.join (.leaf 16 0x8442000200000100040 0x29851a2315861357260b10da03f3103728e219a0) (.leaf 16 0x200000000110000 0x2c7922ef1aa601b42dac2a080f52)) (.join (.leaf 16 0x20040000000 0x2ab01b290cca) (.leaf 16 0x10400000000802000400 0x6af01d50889070f1bac2d88)))) (.join (.join (.join (.leaf 16 0x40000000210040000400 0x2c02288e283c26241cb2121d0dfc04e12de9095d1e1a1c2f) (.leaf 16 0x2200c020000008020 0x2da21d35030a298813fb0f9d15ca0aa30c882487)) (.join (.leaf 16 0x8000004400840000000 0x2b3005f023881db81c130793) (.leaf 16 0x20000000042000000 0x1451e3b11eb))) (.join (.join (.leaf 16 0x401004200004008060 0x1af002830ee208ce1a0019751ebe29d61eae1024) (.leaf 16 0x81004000002000021 0x1fc419520b0304c726b015702cbf049a1f41)) (.join (.leaf 16 0x8400004001000100000 0x296c19f8204712700be3046c) (.leaf 16 0x202800000000 0x772237a227d20ca19f6057a))))) (.join (.join (.join (.join (.leaf 16 0x2000000000200000 0x252309c42672214d) (.leaf 16 0x1400000010002000040 0x225314280d290bce04e71a5c2b6321d00c5b)) (.join (.leaf 16 0x80000040000400 0x22d601ff297a) (.leaf 16 0x20000208001 0x23591e9410e50829026d1483))) (.join (.join (.leaf 16 0x400000400002010000 0x2115239602f223dc1eaa1bb3) (.leaf 16 0x8020000000040000400 0x24e21c171d74245f)) (.join (.leaf 16 0x8006004000000100020 0x9de2a8425651eca1b220f0c09280cc522840fb5) (.leaf 16 0x400000600000000000 0x1f7e25e81f3f05bf)))) (.join (.join (.join (.leaf 16 0x421008000042000c40 0x1c6a2da80e8c1cef1bd9266b16a2264b096e09370f5a046f) (.leaf 16 0x2000000040110400 0x1ecf0744097606b327a826ee2c2c)) (.join (.leaf 16 0x61000000000000802 0x27f416f30835281c1ca8015627711136) (.leaf 16 0x20010000000100000 0x6c62877283c1db21b9313cf))) (.join (.join (.leaf 16 0x800000011800000000 0xdcf00b5133c28fa19d60c68) (.leaf 16 0x1000000042108000 0x1cdf18941fab297d0059)) (.join (.leaf 16 0xc00000000842000420 0x2de92a831cdb0e25201409da10e42a00) (.leaf 16 0x8020080000802000020 0x269818a92b062d2626170163))))))
set_option maxRecDepth 4000 in
private theorem scan10_0 : Region (clearPoint L10) 0 512 :=
  checkedPatch 0 patch10_0 gates10 (by decide +kernel) (by decide +kernel)
private def patch10_512 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x220802000000 0x155e2b8920e60af61d5c) (.leaf 16 0x8420080200002000000 0x79f1ca0007f0c4420442c0c)) (.join (.leaf 16 0x8021000000800000800 0x2d121c28161217442c8f01a5) (.leaf 16 0x5000000800000002 0x2d95113f104c0341008b20cb1da7094a))) (.join (.join (.leaf 16 0x10000004200000010000 0x1fde1e3d2e0c2e182de8024a) (.leaf 16 0x80000800008000 0x1a230b8f03c3)) (.join (.leaf 16 0x8000004220002020001 0x23ad22ae1d110ab901682df920cb155512f5049311f5) (.leaf 16 0x60084000040000401 0x2bbf231614cd0e360f0a01c024762617)))) (.join (.join (.join (.leaf 16 0x401004000880000020 0x122e10482c4e2464264320552cba) (.leaf 16 0x1000200804000000 0x2b190ff21dd42c2305dd)) (.join (.leaf 16 0x1080010002000020 0x23d71b6d122e2dbe1105) (.leaf 16 0x4000002008020 0x211d092e0817132a))) (.join (.join (.leaf 16 0x1184020002000401 0xbe21fd14c708681fc62df702a60b4708590052) (.leaf 16 0x40800100020 0x26831f3317920707232b02790f01)) (.join (.leaf 16 0x8020000201042008020 0x2d811fc403c7293c0c4a162c1fc00a48270e) (.leaf 16 0x21000010040000800 0x1f6027eb10ae0ad6276d0070))))) (.join (.join (.join (.join (.leaf 16 0x4000000000820 0x16331e5607a321f4) (.leaf 16 0x10021000010040208001 0x27a204b32e0721c30607265822cd20a12b5d2724)) (.join (.leaf 16 0x1080000800100000 0x1d2c126128cf271c) (.leaf 16 0x20000011000008000 0x84f268d25840eaa1993))) (.join (.join (.leaf 16 0x18000000210000100042 0x20880772061814f220f2223f236f08870b5b07fe) (.leaf 16 0x8200000000000 0x16d50e56274a)) (.join (.leaf 16 0x8000000010000000401 0xe0e108d24560166) (.leaf 16 0x41000200000208001 0x26e7003a2cd422872453201513a502a0)))) (.join (.join (.join (.leaf 16 0x800000000002008000 0x1c9b01bf153f20a2) (.leaf 16 0x1080000000000021 0x48d13450f060f67)) (.join (.leaf 16 0x1004010080008022 0x1a1728452d9a27d6199e00722aee24c01a6a) (.leaf 16 0x8000004010002000000 0x18a3274022ad13a2))) (.join (.join (.leaf 16 0x821000400000100000 0x1c8805390e9e29172ddc24f70ab7) (.leaf 16 0x10023000400040000000 0x28ff09d8079d26fa239a22a525bc23051b2a)) (.join (.leaf 16 0x10000001800042000400 0x218b07be2c3326cf1d961b7016de14f80c650c5f0bd105c3041f0302027807630b8c) (.leaf 16 0x20004000000000000 0xba01a41))))))
set_option maxRecDepth 4000 in
private theorem scan10_512 : Region (clearPoint L10) 512 1024 :=
  checkedPatch 512 patch10_512 gates10 (by decide +kernel) (by decide +kernel)
private def patch10_1024 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x8000008000040120400 0x180c23a7215c2a6c01f6257522fe0eec01f62a3a) (.leaf 16 0x20000010800000801 0x48d250c2623295613ab2abb)) (.join (.leaf 16 0x30800008000 0xe2002900188217900fd) (.leaf 16 0x1000001080000400 0x222f1d3012b31f6001772977))) (.join (.join (.leaf 16 0x401000000000100800 0x1777261a23440eec0220) (.leaf 16 0x20004210000000020 0xe1a213f1f9015132256)) (.join (.leaf 16 0x800000000000000401 0x2a8500a023da243d) (.leaf 16 0x30000000000 0xb6d09870324)))) (.join (.join (.join (.leaf 16 0x8000000020004000000 0x15c423361d1e1bd910b8) (.leaf 16 0x10800000400802000020 0x155214b228ab25692df62dcd18eb179b092f)) (.join (.leaf 16 0x10400084000040000000 0x1d4b1900000d118c271c2594) (.leaf 16 0x10000080001842000020 0x13ae02dd21b319f9181803b71d351799014e))) (.join (.join (.leaf 16 0xc0000001 0x2a8513990ed90cd9) (.leaf 16 0x800180000002008401 0x2be60a441e4e0c88014204d7258a231128f6)) (.join (.leaf 16 0x200844000001 0x2c1d2bad27d61dff00640580) (.leaf 16 0x8000042100000 0x1d5a1289055b194e0703))))) (.join (.join (.join (.join (.leaf 16 0x1080000802010000 0x299907f616b71a732ddc05f2) (.leaf 16 0x1000010000000020 0xd4b097f2d0c)) (.join (.leaf 16 0x821000000800408020 0x2af4249707342e08003b2a0a24941b9e1058239428a9) (.leaf 16 0x80000000008400 0x2c8e0b5c08d3))) (.join (.join (.leaf 16 0x8000800000421 0x26d0247614820af929352cbc) (.leaf 16 0x10002080010844008021 0x2185015a08d606a6036d0b922a6b1fc92c9b1f60199625540d4b)) (.join (.leaf 16 0x8000000000040018800 0xa7e297a2dd62b9a27cd1cb40f43) (.leaf 16 0x10004100000 0x27882c1b213b2b29)))) (.join (.join (.join (.leaf 16 0x4000800000400 0x49a18a31b9a) (.leaf 16 0xc0100000 0x2ce9127d0884287b)) (.join (.leaf 16 0x20000000840100420 0x5291f86048a198606f119f5) (.leaf 16 0x20000000800000006 0x1bcd22552755201618130c100b4a08e8))) (.join (.join (.leaf 16 0x401084200080000000 0x18315472749286f159125de21ac) (.leaf 16 0x4000002100800 0x2877239b017a19880eb4)) (.join (.leaf 16 0x200802000000 0x2169010f0b11) (.leaf 16 0x104000840008002 0x12f90fd327af1bd90baa12912bdc0a4b))))))
set_option maxRecDepth 4000 in
private theorem scan10_1024 : Region (clearPoint L10) 1024 1536 :=
  checkedPatch 1024 patch10_1024 gates10 (by decide +kernel) (by decide +kernel)
private def patch10_1536 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x10020104020000200400 0x29f21c8722e726d801ee206212ec1166259b0d062cd7) (.leaf 16 0x10020080200800100000 0x177704d2023e11f8255016fd1555)) (.join (.leaf 16 0x10400000010002000000 0x18a309c218b42a310784) (.leaf 16 0x1000010002000000 0x28c2c7503d4))) (.join (.join (.leaf 16 0x40000000000000000 0x21580853) (.leaf 16 0x8000084810040000020 0xf351fce27be2bc326cc123d0c8c23470db11a77)) (.join (.leaf 16 0x400084000040000000 0x643215c18121c15) (.leaf 16 0x1000000002010000 0x2e617aa12960ca3)))) (.join (.join (.join (.leaf 16 0x80230802100402 0x8e51cc42d6d102a090426561f0314142b6208c60110) (.leaf 16 0x400000000800100401 0x29ff198d181e12d32ad3)) (.join (.leaf 16 0x800000000 0x1897) (.leaf 16 0x300000 0x1699059b02c2))) (.join (.join (.leaf 16 0x4000802000120 0x2ddc0e80156b2b752b54260a22f320ac201d1f3811220f21) (.leaf 16 0x420000000000008021 0x50b2464129f22520a09)) (.join (.leaf 16 0x8440000010040000000 0x21df2d782c9507b729191039) (.leaf 16 0x20000000000100420 0x1d4728022dfd0426))))) (.join (.join (.join (.join (.leaf 16 0x8000004201040000020 0x1389136d10f61e261cca2a3320b0) (.leaf 16 0x2000000040000020 0x2b66222506742047)) (.join (.leaf 16 0x600000000401 0x13ed11dd0abd06fb07bd) (.leaf 16 0x8001080010040000000 0x1000248a2911066a0f79))) (.join (.join (.leaf 16 0x1000200080018001 0x1c2b2b99288407341d031be619ab1dc3) (.leaf 16 0x40004010000000000 0x16c207a221f41d1d)) (.join (.leaf 16 0x8001008200002000020 0x28b91d1416c010332b5c2a61153a) (.leaf 16 0x401000210800000000 0x1a3516a2173906d61045)))) (.join (.join (.join (.leaf 16 0x10002000000 0xf560905) (.leaf 16 0x1004200000010001 0x21ff062b14e61da3072d118e)) (.join (.leaf 16 0x8001004010004100400 0x1b161f4308682e1e18ba10c302b6038e) (.leaf 16 0x20000050040000000 0x1da72c2423181c3a080606762d82))) (.join (.join (.leaf 16 0x1080201802108000 0x2b5001b41fa822540bc805622b5a00071651) (.leaf 16 0xc0000000000000ac00 0x2c052baa12de1f1e2c622b02241b1fcf16ab12df046c02b201b901ad0091)) (.join (.leaf 16 0x8000 0x4ed) (.leaf 16 0x40004410000100000 0x1de916f4002f2a1c009a08681d71))))))
set_option maxRecDepth 4000 in
private theorem scan10_1536 : Region (clearPoint L10) 1536 2048 :=
  checkedPatch 1536 patch10_1536 gates10 (by decide +kernel) (by decide +kernel)
private def patch10_2048 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x201080008021 0x199d10e40d7206c704f60a36242502e4) (.leaf 16 0x400000000802310000 0x190726880c8f2ba7053a03cc1f900b5c)) (.join (.leaf 16 0x110000 0x10451ca801f3) (.leaf 16 0x400000010802008802 0x12f60dbc0f3709a001e81324037012320e08))) (.join (.join (.leaf 16 0x800000200800000400 0x2be1282a0208010807f6) (.leaf 16 0x20004000000008001 0x2d072d7a1a07052f)) (.join (.leaf 16 0x801000000802010040 0x234f0e5527af212e01e1234b1a00167b1033) (.leaf 16 0x800180010000000000 0x2b4223de28d91ac80fe92d4d)))) (.join (.join (.join (.leaf 16 0x8001000010040100400 0x38e0b1c18941b5806c7198a) (.leaf 16 0x2000010004000000 0x17dd08a21a7a26ee0b62)) (.join (.leaf 16 0x8820080000000000800 0x2e151ec411c2102c204d2d9b1714) (.leaf 16 0x20004400000100801 0xc8805232bfc057d2b6d280f14621315))) (.join (.join (.leaf 16 0x4200000000001 0xe5c1270091c) (.leaf 16 0x20000000006000000 0x141c223419961885)) (.join (.leaf 16 0x1000010000030000 0x21c603e8276d24ea22f9147709d202eb) (.leaf 16 0x10000080200000000000 0x26ea0e261ede1133))))) (.join (.join (.join (.join (.leaf 16 0x20010010080000040 0x257825ae20a10d020a5f1a022ce015ca277f0f27) (.leaf 16 0x400000401000000021 0x147717eb134728691219226d232b)) (.join (.leaf 16 0x9000004000002000401 0xca71ea01ac515de123c182505b81cf82990) (.leaf 16 0xc00000000002000020 0x254e1393125318460ba6))) (.join (.join (.leaf 16 0x1000001000000000 0x1a561b8c0445) (.leaf 16 0x1000080000040000000 0x2b8a23851aef052621540c07)) (.join (.leaf 16 0x801004000000000000 0x1ce1191f23591821) (.leaf 16 0x18400080000040200000 0x12bd080d01c8104b0bce2c552d9a1e2e)))) (.join (.join (.join (.leaf 16 0x8002000200000100022 0x157102106a12d9b29620901137202a1) (.leaf 16 0x400002000400 0x1e97196f1ead0290)) (.join (.leaf 16 0x1100002000000001 0x2dfc2b6020b629442615218e076720a6) (.leaf 16 0x20000210080000000 0x1bdc29271908258b01ff))) (.join (.join (.leaf 16 0x4000800000020 0x24ed05be0cfd) (.leaf 16 0x400084000800000020 0x23ec10b4286c0550207d)) (.join (.leaf 16 0x4000002008020 0x1b8b15631e9b18bb) (.leaf 16 0x80000000300020 0x52f23a31d9e0e011f09))))))
set_option maxRecDepth 4000 in
private theorem scan10_2048 : Region (clearPoint L10) 2048 2560 :=
  checkedPatch 2048 patch10_2048 gates10 (by decide +kernel) (by decide +kernel)
private def patch10_2560 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x800004000000000060 0x165d14f81dd52b401f4906d4) (.leaf 16 0x80410002000000 0x165026ab1cfd015a0de9)) (.join (.leaf 16 0x40084000000000020 0xe9201b927ee15c400fd) (.leaf 16 0x1000010000008000 0xd5a0385071e))) (.join (.join (.leaf 16 0x10000000020002000000 0xe320ab5202b099f15db) (.leaf 16 0x200000000400 0xccd243a)) (.join (.leaf 16 0x8000000000000000000 0x2d12) (.leaf 16 0x80400082000800 0x4d22a7f129b28e81b921c8420140696)))) (.join (.join (.join (.leaf 16 0x8400000000800000000 0x119b11f310a8) (.leaf 16 0x10081080000800000000 0x2d2d052526391cab11780aa301d215671f2e)) (.join (.leaf 16 0x8001004000042010001 0x51d288127af1c1b1bb42b0a14080385) (.leaf 16 0x400000000800000001 0x2bf91ba00013))) (.join (.join (.leaf 16 0x400000210020 0x1daa0beb2257077518100b851999) (.leaf 16 0x1000200040100020 0x12161eb320b62d5e0bad)) (.join (.leaf 16 0x4000000000421 0x2b65029c0525211c) (.leaf 16 0x100400 0x25e81eb8))))) (.join (.join (.join (.join (.leaf 16 0x400000000002110000 0x1a352df420230700027b) (.leaf 16 0x8420000000000008c00 0xcc40f88287707691ec80a2e01e4)) (.join (.leaf 16 0x8001000000000000000 0x29680de9) (.leaf 16 0x20004400000000001 0x1bc70a7e26860e240c16))) (.join (.join (.leaf 16 0x800000010000000800 0x27fb09c41bfb2a221cd9) (.leaf 16 0x401000000800100000 0x17920696234b24e6)) (.join (.leaf 16 0x8420004000040018008 0x14772d991b222776091c24bc0d3f05742c082926291b1ae619150e2a010f00aa) (.leaf 16 0x84000004000000 0x284f208921711201)))) (.join (.join (.join (.leaf 16 0x8001000001000100800 0x2ad92c47071e046c1f16235c14e6) (.leaf 16 0x420000010002010420 0x1c2008b137d263a11b30c2c14110412)) (.join (.leaf 16 0x84000000200000 0x577287a1bff0657) (.leaf 16 0x384200000100400 0x2aa0242e1a9b1678163f10c60af609f22a31214a18e2))) (.join (.join (.leaf 16 0x600800008001 0x237a10090b5f266b1ed721ee) (.leaf 16 0x80010800000400 0xf8f1e141e8d2bc1)) (.join (.leaf 16 0x10401000000840108001 0xe65028520a1004309fd0e1103620af50dbc) (.leaf 16 0xc0000000 0xee1089503d0))))))
set_option maxRecDepth 4000 in
private theorem scan10_2560 : Region (clearPoint L10) 2560 3072 :=
  checkedPatch 2560 patch10_2560 gates10 (by decide +kernel) (by decide +kernel)
private def patch10_3072 : Patch :=
  (.join (.join (.join (.join (.leaf 16 0x80010000000020 0x107c02fb21ee) (.leaf 16 0x420004000040208002 0x21fd104026541a2229b30faa13bc0ec70bbb)) (.join (.leaf 16 0x10420084010000000000 0x22df1f8516e91a020b711d321399) (.leaf 16 0x8420004000040000000 0x1cf17dd275b0c660cdf))) (.join (.join (.leaf 16 0x10000000000000 0x1fd0126a0bb002fc) (.leaf 16 0x401080000000000400 0x1a351a570186055c)) (.join (.leaf 16 0x4000000000000 0xdfc) (.join (.leaf 16 0x8001000000000008060 0x192d01361e102a7417510bbd) (.leaf 16 0x8021180000004000001 0x1cea0a7e21f41782067305702c2005a4233e))))) (.join (.join (.join (.leaf 16 0x8400004001000000020 0x165715322b9f213f04990b65) (.leaf 16 0x1000400004008400 0x4510cf30a0b296e09f703941ddd)) (.join (.leaf 16 0x10400000200082008800 0x253311d4075915e2288b1a9c0ca923b00d690207) (.join (.leaf 16 0x1000000000000000 0x2119) (.leaf 16 0x4001040100000 0x21a627131ee62ba71913)))) (.join (.join (.leaf 16 0x1040008c2100000 0x25d425bd1843191514560e1b0235136f0328) (.leaf 16 0x20004000000000020 0x14921de8276a)) (.join (.leaf 16 0x40084410040000001 0xeda0343256f26f5184f029811171038250c) (.join (.leaf 16 0x10002000421 0x2bc8068a22772c9b0943) (.leaf 11 0x4020000100000 0xc9029e0192b0e95))))))
set_option maxRecDepth 4000 in
private theorem scan10_3072 : Region (clearPoint L10) 3072 3371 :=
  checkedPatch 3072 patch10_3072 gates10 (by decide +kernel) (by decide +kernel)
private theorem rows10 : Region (clearPoint L10) 0 3371 :=
  (mergeRegion (mergeRegion scan10_0 (mergeRegion scan10_512 scan10_1024)) (mergeRegion (mergeRegion scan10_1536 scan10_2048) (mergeRegion scan10_2560 scan10_3072)))
private theorem clear10 : Clear L10 := clear_of_scan (by decide +kernel) (rows10)

private def L11 : Chart := ⟨4777, 10254846966, 64573, 38449, -773236, 1227753, 24333, 1252⟩

private def g11_13 : Gate := ⟨13, 12, 0x9e5, #[
    0x400, 0x42c, 0x681, 0x1504, 0x518, 0xe02, 0x4c2, 0x443,
    0xe40, 0x1418, 0x1520, 0xc81, 0x434]⟩
private theorem g11_13_ok : g11_13.OK L11 := gate_of_test (by decide +kernel)

private def g11_61 : Gate := ⟨61, 10, 0x1713e6940a59f23b, #[
    0x80000000000000, 0x12a3d178a9c0a503, 0x18dc0ab3066a81d8, 0xb8a147590d29613, 0x5a7b11088de5a14, 0x280a260b77bb419, 0xa94c912652a63c6, 0x15a83eb0a0286be0,
    0x129c7f8e53024481, 0xea19ca801539857, 0xdc551d94c2850ca, 0x159f058a341f3500, 0xcc331a583560d2c, 0x1ef108c423de1830, 0x289900fb9df0099, 0x12891448a7a27917,
    0x9c2a12eae90a872, 0x14da5b2811757440, 0x8cc43d2f08cc545, 0x12c692613e07c864, 0x16a1322642b69325, 0xcca38d24a49638a, 0x682ff4166c0881b, 0x2dd6182d061aed0,
    0x1e44f0a16c93685, 0x681dcc19dc0b0b4, 0x9fe5700d0a1601d, 0x13832004c1cf98cf, 0x18d4d7c20010faca, 0x6f4c65ec1226448, 0xdd183077060c5d8, 0x5d86e8c183b8306,
    0x17b04899120de98c, 0x158d4d7c20010fac, 0xe7cc67ce0c8013, 0x1fcae01a142c03a9, 0xb0b4340ee60cee, 0x13c285b24da143c8, 0x1da02dd6182d061a, 0xb360440d9a0bfd,
    0x999471a49492c71, 0x2b69325b5099132, 0x11a4984f81f21925, 0x198a8a8cc43d2f08, 0xd9408baba205369, 0x1c9385425d5d215, 0x8a7a279179448a2, 0x8a26403ee77c026,
    0x7bc3061ef108c42, 0x198d2c1ab069633, 0x1cd402b3e0b14683, 0x11d94c2850ca6e2a, 0x2bba8672a0054e6, 0x1ca604890329c7f8, 0xad41f58501435f0, 0x14a98f195299224c,
    0xa260b77bb41914, 0x12d0a169ec442237, 0x8eb21a52c26b8a1, 0x1d8c6e0559833540, 0x2a702940e547a2f]⟩
private theorem g11_61_ok : g11_61.OK L11 := gate_of_test (by decide +kernel)

private def g11_41 : Gate := ⟨41, 11, 0x1b382b50737, #[
    0x100000, 0x954f910173, 0x127f4b21888, 0x592a39a313, 0x1590c5860be, 0x18b28544397, 0xe460f49e48, 0x52d0744799,
    0xdab9c8b48, 0x10a1b92a173, 0xec23bb0328, 0x5619b9db0, 0x1c20d53a495, 0x40f8bf124c, 0x1b829718923, 0x901754e0d7,
    0xe65c15068e, 0x10c56b99960, 0x36f4b84660, 0x17254505a2d, 0xe0dc56f280, 0x29ed4760e, 0x168b414549d, 0xcc43a5ed8,
    0xd333ad461, 0xe2c15074ce, 0x1d60e55d012, 0x189231d283b, 0x6491fa3e04, 0x1524b956087, 0x1b73b30d40, 0x2981bb886e,
    0x19d0a93b0a1, 0x25a273ab60, 0x133c45c1694, 0x24f25e0c4e, 0x1d3845429a3, 0xfa0c346135, 0x1918b38a934, 0x22309a5fc9,
    0x19d0113e552]⟩
private theorem g11_41_ok : g11_41.OK L11 := gate_of_test (by decide +kernel)

private def g11_37 : Gate := ⟨37, 11, 0x165e211e9b, #[
    0x1fffffffff, 0x14b8872cca, 0xf4a489d86, 0x1a30ea05cd, 0x1a6c12c2e9, 0x2d47835c5, 0x72a5e6e20, 0x14027b9ba1,
    0x14da892e70, 0x1904bce68c, 0x133a176027, 0x1e8f4ed20, 0xec49154bc, 0x1ae309cdc, 0x8ac956dc1, 0x11560cf7a0,
    0x1bc6e04986, 0x1b824543cb, 0x2984f5a5c, 0x15e43283a5, 0x54483bd3c, 0x40ec7b619, 0x1e60d5105e, 0xd526a283b,
    0x1218eb03b3, 0x151246e3d2, 0xe5e2f004b, 0xdd0b99e40, 0xe7a413316, 0x922b650e7, 0x13bc80585d, 0xcf4a9c047,
    0x183c568a3a, 0x6906cb974, 0xae18bb3a, 0x1224a5e61b, 0x9c23a5533]⟩
private theorem g11_37_ok : g11_37.OK L11 := gate_of_test (by decide +kernel)

private def g11_59 : Gate := ⟨59, 10, 0x22b62183e7b92bb, #[
    0x2000000, 0x41bb1787fe864a8, 0xcbb10baabe745a, 0x48991edd7cd28e4, 0x4c067b22726fe5a, 0x642f2aef73a6a4, 0x1ab78e98eac3c92, 0x325cdf142171a9f,
    0x7f2c7130f820b6b, 0x3915d0d5bc989f4, 0x2d3326a2bcb82e7, 0x62c87b49a6f6e18, 0x56b24b03e667956, 0x40e6e75aa4712f3, 0x5bb85dc52419f85, 0x2e70bb0d753ec06,
    0x394d3957ff04701, 0x2fc368e0217dd69, 0x1857cc8f6b831b5, 0x61ad47b6a9283dc, 0x21b725667b872f0, 0x604671962369f3f, 0x3f28d21e24f2e8b, 0x50f546e23cbb165,
    0x526c453bb4e5a4b, 0x1bcfa8d571106f1, 0x61bdcb7220d4bc5, 0x3d0c50eebfb8889, 0x5fda84d965c54a1, 0x1f3aa5c9f98f00a, 0x3e28078cfc9d2ae, 0x7ec2951d34d90ad,
    0x2f4888efebb8518, 0x61d1e95822769de, 0x7647b0447558af9, 0x12e92d396ee511b, 0x42d346e9e23b157, 0x3f68ba7923c258a, 0x1fe7cb6234c731, 0x6107a70ef335276,
    0x619de0a4ab6f15a, 0x656c60eb7899f5, 0x7d4b5df42038b61, 0x27407107ff54e59, 0x1d301be57586e87, 0x76d0fcc1251dd0e, 0x40e7a4712ad73b3, 0x5ab54f333e06926,
    0x518c3b7b2c96f09, 0x2d73a0e9ea2b266, 0x2717c8c9ed585d4, 0x3feb6820f86471a, 0x137cac742147d9d, 0x56249e1ab8cb8f6, 0x1812b2e77baa7a1, 0xcad3fb27226f30,
    0x44938a59f5dbc4c, 0x4c2d173eaae846e, 0x608a930bff0f46e]⟩
private theorem g11_59_ok : g11_59.OK L11 := gate_of_test (by decide +kernel)

private def g11_47 : Gate := ⟨47, 11, 0x7bcae4d8ac21, #[
    0x400000000, 0x1125f4cd43db, 0x6304ff6cb494, 0x385e3e6b046b, 0x48a61d774f16, 0x236c173a467e, 0x245703dda7b1, 0x51cea6913575,
    0x330fa076cd65, 0x773cec1b6680, 0x471682efc353, 0x4b36455895cf, 0x2cc7e8a1765c, 0x444d3f9dd388, 0x74b733a738c0, 0x5efd603107f0,
    0x4a1f738227c7, 0x3eed5595e401, 0x63d69d140adb, 0x5a56f1ac76a0, 0x6a45b221bd1f, 0x52e58e8e86ae, 0x49672e0eec72, 0x1d7cad853217,
    0x36a7d73a1328, 0xe9cd2538ddc, 0x2e34e95d585c, 0x9b44afe2f61, 0x31ed4b415b8d, 0x172d78f6d40a, 0x3556efa009ea, 0x39df0a78f910,
    0xd7ef43f823, 0x399da5c0c739, 0x3f96444472ee, 0x22fc668e9ba1, 0x544d9a7cea46, 0x682d1c72b0fd, 0x6e79dc059b6, 0x40be19a9acdb,
    0x2cae716bab22, 0x781d44a3796e, 0x1d06d89f9897, 0x570ca25a3cbb, 0x4f8f43b58835, 0x5fe418ca4b4d, 0x65f49136f0ac]⟩
private theorem g11_47_ok : g11_47.OK L11 := gate_of_test (by decide +kernel)

private def g11_43 : Gate := ⟨43, 11, 0x35883a3ee53, #[
    0x4000000000, 0x40ad9cfde0c, 0x2ab3bc50f49, 0x1b221afd3a9, 0x3311eb71d62, 0x229edc8ea5a, 0x7be30b88d31, 0x4051eba79da,
    0x6b42e27d196, 0x2bdc3ac9e0a, 0x1b8dd36dc3, 0x597a4506c3f, 0x51d5a34a13f, 0x5329995a477, 0x82ec2f799d, 0xba315a7a75,
    0x3be6039729a, 0x78cd7978324, 0x31d6fc01d93, 0x60cf576988e, 0xa79f2b45e4, 0x414dd5c23ed, 0x506df10eaec, 0x4a09e8b53e7,
    0x60dc465babc, 0x71b26e00fda, 0x63c9307a7ac, 0x7b9653a7019, 0x3a2b9796a31, 0x22e67bd0dd, 0x197b896a665, 0x717f214b16a,
    0x537f0d82897, 0x3030edb2ec7, 0x7a941e4d70e, 0x5ada62f91d0, 0x4056e7975e2, 0x7be32c47431, 0x289695c4ede, 0x1991ae3b5e2,
    0x1b2572fd611, 0x2aa4bc28f73, 0x204c1efce6d]⟩
private theorem g11_43_ok : g11_43.OK L11 := gate_of_test (by decide +kernel)

private def g11_31 : Gate := ⟨31, 11, 0x6de2b849, #[
    0x20000000, 0x197c7d3, 0x405f4cbe, 0x1b65c89d, 0x41419ff9, 0x5c63b1b1, 0x4b29a5ce, 0x539e72c1,
    0x55dd50f, 0xea7e570, 0x1e85b42f, 0x47b88477, 0x126d635b, 0x5552e674, 0x5c3b4aa5, 0x17bd1332,
    0x44cc8bde, 0x5a552dc3, 0x52e674aa, 0x4dac6b64, 0x1ee211de, 0x4f42da17, 0xea7e57, 0xf0abbaa,
    0x5834e79c, 0x173a594d, 0x58d8dc63, 0x19ff9828, 0x4b913a6d, 0x17d32fa0, 0xcbe3e98]⟩
private theorem g11_31_ok : g11_31.OK L11 := gate_of_test (by decide +kernel)

private def g11_23 : Gate := ⟨23, 12, 0x5335f, #[
    0x400000, 0x385cd5, 0x35a267, 0x39f305, 0x1c6d3a, 0x779b2, 0x1f0576, 0x30dbc6,
    0x274ad9, 0x2da15e, 0x2de5d, 0x51fb9, 0x277e28, 0x2e9ed0, 0x1ea16d, 0x26d4b9,
    0x18f6c3, 0x1ba83e, 0x1367b8, 0x172d8e, 0x2833e7, 0x39916b, 0x2ace87]⟩
private theorem g11_23_ok : g11_23.OK L11 := gate_of_test (by decide +kernel)

private def g11_19 : Gate := ⟨19, 12, 0x4f50d, #[
    0x7ffff, 0x57a11, 0xea71, 0x136aa, 0x7e260, 0x43369, 0x139a3, 0x6a4d2,
    0x7a035, 0xe51e, 0x53878, 0x2fac, 0x12b4b, 0x4e4c5, 0x66196, 0x23f06,
    0x36455, 0x2b88e, 0x2f588]⟩
private theorem g11_19_ok : g11_19.OK L11 := gate_of_test (by decide +kernel)

private def g11_11 : Gate := ⟨11, 13, 0x23b, #[
    0x2, 0x674, 0x3c9, 0x47c, 0x475, 0x574, 0x3a9, 0x38d,
    0x789, 0x4f4, 0x399]⟩
private theorem g11_11_ok : g11_11.OK L11 := gate_of_test (by decide +kernel)

private def g11_7 : Gate := ⟨7, 13, 0x69, #[
    0x2, 0x78, 0x35, 0x4d, 0x4d, 0x35, 0x78]⟩
private theorem g11_7_ok : g11_7.OK L11 := gate_of_test (by decide +kernel)

private def g11_3 : Gate := ⟨3, 14, 0x3, #[
    0x1, 0x3, 0x5]⟩
private theorem g11_3_ok : g11_3.OK L11 := gate_of_test (by decide +kernel)

private def g11_53 : Gate := ⟨53, 10, 0x12dd703303aed3, #[
    0x1fffffffffffff, 0x1db3912ffd94f5, 0x19ff7de5ac6174, 0x19ae5b85c766ff, 0x186d3beaf2ae7e, 0x1f0cf275cef87b, 0xaed68ded279fd, 0x1bb1afb68b75f8,
    0x1b39569b31f8ff, 0x69fdcdc86abfb, 0x16efe15b5fa0d7, 0x1df82f0b9efe4b, 0xdd9ce9a778d5f, 0x14736f7ebcbee, 0x1479a9b47ccffd, 0x167ecf6f6829db,
    0xfbcb4ad7723dd, 0xaf4a3f7a7fc47, 0x7c3887bbb3f5f, 0xeebbd66edeae0, 0xfb6cfdfba8166, 0x1461fcfdce765d, 0x3bf2ff955dae1, 0x365572dbf3cfe,
    0xf9a7e7d2b4ecd, 0xe5a5fa91cf7d7, 0x1e557317e1b7db, 0x161fa33aa9fb7d, 0x1ce257e969dd7d, 0xb52f9f967d66e, 0x13f6d3aa9b0fe7, 0xeaa7fd3f710eb,
    0x19cefcfe18b74d, 0x577efcdb7ccd0, 0x1edd9af75dc0ea, 0x137778470f9f5f, 0x1f97bf14bd5c47, 0x13bad4b4f7d778, 0x105bdbcdf9bb72, 0xcf8b65678b7fe,
    0xf5fbdb38a0efa, 0x7b965ce6edf56, 0x1de743d07efa4f, 0x17eb6a1fddbd60, 0x1584ecefe59bfa, 0x1e3365aa737fe3, 0x1b45b7d63763f5, 0x192dec5add57f3,
    0x1dceb93cc3fbc3, 0x153d5f72d86fce, 0x1b8e8769d67fec, 0x18d69efbfe65d0, 0x6ffd22736f5e5]⟩
private theorem g11_53_ok : g11_53.OK L11 := gate_of_test (by decide +kernel)

private def filters11 : List Gate := [g11_13, g11_61, g11_41, g11_37, g11_59, g11_47, g11_43, g11_31, g11_23, g11_19, g11_11, g11_7, g11_3, g11_53]
private theorem gates11 (g : Gate) (h : g ∈ filters11) : g.OK L11 ∧ 512 ≤ g.p*2^vDepth g.p := by
  simp only [filters11, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨g11_13_ok, by decide +kernel⟩
  · exact ⟨g11_61_ok, by decide +kernel⟩
  · exact ⟨g11_41_ok, by decide +kernel⟩
  · exact ⟨g11_37_ok, by decide +kernel⟩
  · exact ⟨g11_59_ok, by decide +kernel⟩
  · exact ⟨g11_47_ok, by decide +kernel⟩
  · exact ⟨g11_43_ok, by decide +kernel⟩
  · exact ⟨g11_31_ok, by decide +kernel⟩
  · exact ⟨g11_23_ok, by decide +kernel⟩
  · exact ⟨g11_19_ok, by decide +kernel⟩
  · exact ⟨g11_11_ok, by decide +kernel⟩
  · exact ⟨g11_7_ok, by decide +kernel⟩
  · exact ⟨g11_3_ok, by decide +kernel⟩
  · exact ⟨g11_53_ok, by decide +kernel⟩

private def patch11_0 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0xc0300c460886411881 0x9ca17db402009cba79530f4b9ba074f21c96bdcfb9d9bd3c94e2882b70914b5a29e17dd76c30372cb3b42081066f739c67cf44771d7cba75089d9bfd636e51c2256d141913057d85423d399339095f0d) (.leaf 16 0x401004820842230465 0xa0bc9c5b97fab5bc9e945a4c0d77939923f460c28f38bb6b8ad7589eb95b9c7699e86cf4652552c0867627e724db1f25b1498215410837a7111c)) (.join (.leaf 16 0x401004020210200804 0x62776414bb02b6a1522fb240a70a9b4c7adb6b3d4673114e0d467ebd7d926c906771643e23621c8a0d89addf4ea8a97e720cb760a51d23031041) (.leaf 16 0x1010800008010421 0x4bc0bba48dd25aac2fc288c271556c933a26b43cb2a3457a44eb84390441558b98fe04fe))) (.join (.join (.leaf 16 0x8005128822002210001 0xbb8196a97eba776d2dd91a8c50ca2f289e6d9c177a136fd5696f46803cfc31b61a7802e8a2649154267c15df3e430a0e8b1d5dab3aa410c8642c850b7fb2b9fd041a23ca) (.leaf 16 0x38001000010004028002 0xaecea490a3e987ec7d8548bc218c65e1691b5e9b5127b8e2890361dc61a302138e984551)) (.join (.leaf 16 0x280811140030c8300041 0xba9ca041879678396ea0bc267ed8433813ff2ddeb9307c52839a2be72ac90988027a719b55a2459c4269406e34fba965980a72de8b437415643d4f444c093ee20dd4485722febdb4) (.leaf 16 0x18080000020000709060 0xa1204e943168b477706747480fae38730822bc97960c93b6564b2b7a07bc00776796b277839d7a19153f586d37020e8a)))) (.join (.join (.join (.leaf 16 0x14010848308c4118401 0xb72da6bc5c49163b103032049cc7694bab355544494044dcab09a0573ff0544862dc1f86056689b508f26e229209627953f46310b8d6) (.leaf 16 0x18880000231044800024 0x8c3d125410a7814a2762b42485d12fd900ed1d649e678fcd0beea57c2d3d4287b7d572f9b9be9519809d73d149142df31aeb045f00e78ebc8acc1e601d79)) (.join (.leaf 16 0x8840214201140010024 0x3dc69b3a51ea5eac5949bd7ea8ae95e5879fbe085e294512434108b24aa359672fbabcbeb2f964ab643926f23b9e2dd86b00959e658663c42b95) (.leaf 16 0x11800000e1000a220801 0xb0fc0eacb0cb9bfd8ff45afc326b2590a29c89017d6979026dec461128e36cb59e26521a36600f310b0225260d1494027f8056db0c638c8082f67329))) (.join (.join (.leaf 16 0x9c01010260804000480 0x6e6a84295d364c372c2b25c521cf0ae986afb779891d696d3f7b3f0ca11e7b086636390529881eb729a76d011bd431a1b2b1854d49ad1a34) (.leaf 16 0x1100300c000182308040 0x48ab3159b01f91657e331566783036f618489ea350ae2763ac98999795e2625621781a885ae7bd72a82762121fbca2157c19)) (.join (.leaf 16 0x800000023004e320c20 0xb6187f854d984d8946ae701fb8ef93eb7cc3635245c31024021fbe14a82d9525868b8477214a078e8f8c51cd0ef73444) (.leaf 16 0x10c20210401800008062 0x5db7355b3e1b07f203c371d4afe3986f7eae565781c13c5e31b42f83677a66cfae459f308a5e85029f46646b164b743a11d9))))) (.join (.join (.join (.join (.leaf 16 0x304610046141422200a1 0xbd75bb60a3818da87f8a4d7c498376eb6d863ddd66abb45d91985d7b2f077d37af49a22d443f39bc35c92b2c16dc08b1a9308dde65e548db488e4b9f67130b6abda299c9836416e49f1170e05a634efc4c8278b2) (.leaf 16 0x82300810086109003 0xba75a2ab2c161c1a59853df2810163375f1a5c3d54b10e4fb03f2b0e1994043404fb61fe47406f4663cd509473892ac28e0c4b7b33732aabbd5a20d30abc)) (.join (.leaf 16 0x28401084040008110461 0xb4d89e2584ae6e9d2fb220582601753e86e5bd90a22d8895331b7d8e5bf40de309ceb026240c1aeb4928aafd79395df4b68b) (.leaf 16 0x88a201040100a108402 0xa942b96d48f6923054d752c750042b52a387627abde6ac954dae00a55ce34a4db5b667a996b742cc12ba09210330823e1e649a8055c23490))) (.join (.join (.leaf 16 0x10e4100000884148423 0xb60467bc53c10067aa918dc6720c6aaa568e0de6078f87686a49696567b25877224e0b8e4f3a182f262021404cdab8f29d019c3b7b126fe9481a4349263d255076f3b6dc6bff687b461a) (.leaf 16 0x82118c2008805088e0 0x1c7f10c489bf44c7bc76869c6bdfa1b65e4b538578a84ea5b031ab5a5d454b0a2b1727751d884b2d6ebe36399867959e754b714f5ffe17731107)) (.join (.leaf 16 0x1000000cc100c0310021 0xbb23a82299f245270db3a78f8c3487407baf65201324285c9ff39b1c4ea9b9f3a7f0a6df6439582335008745) (.leaf 16 0x1842318000180a001801 0xa08298f15e2cad342da2ac6456eb05c9aff2a2bd1e199d5c931b17be9aad6ace526810510c81b2f59bc592f77ccb2f822d157a5d)))) (.join (.join (.join (.leaf 16 0x8821084600848409000 0xbdb7867619b826318c4c7df17af572db69513dc27c126b166c6052821c8e12a59bfe233e0a5604358be6b08eab8d3d62344d) (.leaf 16 0x40405200621042300826 0xb457abf46d186bfb686a399330f91c4d7dc7a9455b5f396124e216aa41b22c041da6107a58e43c6717d7ae5101b6bb59982840663ebeb32d73cd1fe96a7a1f0babfca1ec97036d5f2c88292c12fd)) (.join (.leaf 16 0x28004004e700ca020800 0x9f2099a489b471a303a58390659f0b58017656c1a4fc737d5cd34da81d78198f0e3ca9729774880884c4651753c835c4a5625af03ed8921752de3a892bc30766a18b7cc23cf83b0c99255ae2) (.leaf 16 0x9063080020004308080 0x9ad1926a8b76324903a57225245e0e6b9d5994441d226e8a91530edf7f7c244b4fc0424f16181e75bd0ab3115dc62772))) (.join (.join (.leaf 16 0x280210106101001008a0 0x8fa787126f8e6c0c60936b1f81319a79738267972c798685464443d5486cae09a9e17f32437a448d43f8097bb84fb6c3b68291c40bd6) (.leaf 16 0x30860380000000020c03 0x705b68ca3c9f38e7341700c3b7dca546792024930942bc2684d9561950d116480ad704baafcb8600352d0cc99ffd772c0bec3c233c052e4f)) (.join (.leaf 16 0x480280001042108843 0xb5af8b4d34c82cb527e7ad847e9e6d2011220b6cbd090313aaf77302965a82e669c91ff4a28a39e1896772786d32) (.leaf 16 0x1064084c10902320820 0x7c3e5c61111c0ba958704fd12c9dad7a803e374a1d2921cf849bb286887178fd5ebc4d6e102014a619fd9e4f884874884da14e1ba47519af045b76873ff02a640faf6fe76e91555f))))))
set_option maxRecDepth 4000 in
private theorem scan11_0 : Region (clearPoint L11) 0 512 :=
  checkedPatch 0 patch11_0 gates11 (by decide +kernel) (by decide +kernel)
private def patch11_512 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x1c07008611040021c44 0xb2149dae93c0297120a4146b0c85bcaf76fe6cbd47f03caa32a9320f383137a4b6b89fa593fc6f195dea4dc1a7bbbbd37e5677af2ff682b355b93eeb39f72e3c0fe208c2b4ab4746a436925754a420e4) (.leaf 16 0x9063010232000000421 0x3834bc43a0076f903beb9a35616f3afb94b66c3033f991bc8ec97bff1cad46776e49299610806f9a5f402fd6049b5be986509b61)) (.join (.leaf 16 0x6428c214000408061 0x92d66e161c8864ef529e33222f73ba21acec989d8baa14197f7f688d421b11b988057b2f70ac48783cc618c610b20ef905a0bd0b884637e907d993975e5c4ba701230700) (.leaf 16 0x8021204e4014a028400 0x89ba8439a0688d9933012c1613cb52da913b66365cfa32d228672124196e53fd22fc200a1cd7a2f567615f27596d4a559c883ded1de31bc1070cbab676cb23f71c4d0f801cfc))) (.join (.join (.leaf 16 0x1000020c030044109460 0x88e93c78a0e04b3c3f6038039c0f87f658db8d84389c11e47d5e72b6712733431eeda47893656bae5cdb306276005b5746fb) (.leaf 16 0x28c22000241840208462 0xb604805f4ba9319c15a5aa4f7e2d00579b09acf084165d72b2fe74884fce18d28dfe73f269698b6faebd071a5bef876651a13d0813c7b21d0729)) (.join (.leaf 16 0xc20388c10806000005 0x9bca91fc70458d2484457e376dc866284a553cd316925988268bbd03b9d990900faa034e00c0a56faa7c55ab2e9b180fa7ee91625ee64c770a13) (.leaf 16 0x1840210c011814208880 0xadd3817b529b2ee2681c32df0cb005454aa1468140fb65e784cc5ecc1d4db74eb04097ac8ccf852f73df609338421b501175848e3c4fb6315ab9358db5cf94da360a24ee)))) (.join (.join (.join (.leaf 16 0x388820040109c0108443 0xbbe1a60f964070296a9538e92790391833f092307d875db913a947fe3f67731c3aa727f297c0971780c56b5e3127278520a68ed930c768e89e667fe278f171e92d27) (.leaf 16 0x422090050088118020 0x72181be7706b4875908ebc7f850b76474e0fafc3758573bd70576108790851e1830162644daf3c4eaa76793a6a5561f89747)) (.join (.leaf 16 0x1844120002004a311020 0xb82f6bdc132f3e3d2e2001fe0e58bd156bf650cc0baf5b7d3707374d90954c553cbf309e2b2f871e7e6f0d6576f229348b89839160ef33b08808) (.leaf 16 0x80060084030940520400 0xa90385d180da8029721e689261035931586650c13e043c7e35c435202524200eb8a6a0b08a3e300fb4712aae2a8115f03a26ae2b80f878b112780298a3f8820a5d8947fd082ab21486c26b26255c9243))) (.join (.join (.leaf 16 0x18002000201082008c01 0xb9d265463f1a5d683e4593f87470509469655139a5db835db5545f880af3af7d) (.leaf 16 0xe0000000004209421 0xa59a9522603726d61174114d0c5541bb2e312b410ac86f27b95baf739cc098516b331d209e94)) (.join (.leaf 16 0x8402190201000308021 0x7e1c61dab4845fb29c2d7854765392307928768f45c32beab9610921a7309a899276ae93130a95ad) (.leaf 16 0x842000a20844010440 0xa3485d4b5b0b33305e38148e973b93b683a0770943e24ec918f6976212ce637857b5b4f9733e2620bdf044eb))))) (.join (.join (.join (.join (.leaf 16 0x1842100c040044328061 0xb427ab7824c399174fd7771f79b34faa45f79e18952884267a52b8bf2b34245da1ac1bb7098d9486510f2eda2b47276c823b2ecf1cffabfc) (.leaf 16 0x83104011042311040 0x7482366011550872addf5c26244e9f575a57af0eb98b440930ad9cd50ea396dd42da1b3e931e89ac86a973951c771b90a36b66f8)) (.join (.leaf 16 0x18021108a21002100443 0x92ab913b01d72a5a21bf674b118669de1e6fa9659c178bd942cf378b95be888da6a78a789acc75e75040200708797f6a7bb176a0) (.leaf 16 0x19cc1080031884001000 0x8fb86d4d33a2836c7f767b2378e971c7141902e5af3ea97261f24534280e16059c817e2f57b113b51256b3ef98011d5ea0c82457aa661133860052bb29ea19c1))) (.join (.join (.leaf 16 0x4008803100130800 0xa7f49e8256d31ea346af1605974a8d7987047012ab8a8201654c5d4211ed1064a8c69a771ae3170b56b7549742cf3f5d2e1e18f70c6367e017a6) (.leaf 16 0x29c00200c30804109085 0xb4477ab1758d185414b5ba18b45b91c284397d1056f80a60b5aa787e5f0552ffba15b6d25b1c398129cf231ba8136c316580442e87c65b184e759e3687ed70145a993c436b8b5f34569d3ff9b103aa7b6b2148830c7b)) (.join (.leaf 16 0x104a00040400820104a1 0xba9055c28664bc7483a73d213c5e13539feb729240732591072caa161d5eb319ad915bc25c7faea09a3f5d284e1342392af0) (.leaf 16 0x180040082110400180c0 0x967536132734bbe0b7df838c0585853d74888e54ae189efa09307e074a4f4a01377e9ffb9d5c7be37a6a624b0330)))) (.join (.join (.join (.leaf 16 0x18463280210010100020 0xa65fa26b46a67b228dbd7dcd40a79f5727e72426a0a4884b6360562c010c1e4e2a0db5d4ae8d9c2287ab6e615d6d515712b428e3a1a0) (.leaf 16 0x11140094212806300c42 0x24b40a4aaf17800f790b6219bbbda968a83d8c2f8bd480e262b26045370928ba4d13ba9cb938b3fa7731671a0834a355a96555b747312b8f13247701115e087b87f7702150ecadfd2d7b289d7df27b7f432c31cb)) (.join (.leaf 16 0x8460104600882500023 0xa50a2af07ae13de3175a588f20cd79b688b64c7708e85a27acf30b4d78e18f4b8dd443e243263e9a9bafb53e193918fd) (.leaf 16 0x1200028c801940208020 0x9bd61a8e8baa81a9728764ea34861a3112c1092198c77e85625609370921933341161cc8869c7db758713f8f406b3a3b31f2aaa57d4c4d254ab8429569543fd276d113aa))) (.join (.join (.leaf 16 0x1104a03042110c04 0x28747c01587386f7b31c91a1234c1a340bc1b3268a2e5b35510a32020d0ea6bf546e74854e604c8c97fa95be14b5b3c185e37b571434) (.leaf 16 0x80200104021020004a0 0x61c0a874b78d4d2e149c0a83a4d1757f957c7ba578053765ba9c9e2f7b3354ee29e22f949f2d93ed7e17336b28ce)) (.join (.leaf 16 0x30427008012144308420 0x7ce554815393299d291f17259f4e3138b1838a0378ce5ad85a203c353ba6791a3d2982da980a835281e445908e0172326a34236420d397e74a9880c17e1578fc280e4bb14b4b) (.leaf 16 0x42320c430048121c60 0x990c5613996f59b52304be14b11e68c402a251d340950690421b236da16f508a0f878e2090238ffc86a94fe3aa29a1c795d3775e61e0b6a8b1d592ed74dc5e6b3bcf0b1c702946c83343))))))
set_option maxRecDepth 4000 in
private theorem scan11_512 : Region (clearPoint L11) 512 1024 :=
  checkedPatch 512 patch11_512 gates11 (by decide +kernel) (by decide +kernel)
private def patch11_1024 : Patch :=
  (.join (.join (.join (.leaf 16 0x8820080801182800402 0x54ea5cc73c752eebabdea8ed388f291f03f03ff317949d9f905155da4e72186a00df2dd5a6598f607d6477c04c6529ea1ec914e12f7f68e24a3b) (.join (.leaf 16 0x8001200470900308021 0x1c9e218699e879b94cd2450062d61a678eef7a6d77d630d31a470645051119ec7f567de4212a0c241155103b0dda0da685837f25) (.leaf 16 0x14a008040280c300400 0xb41a80276f7a5f73009f64ef40593f75058b03a38cdb6e914a4fa0b66e44359d1dd918c3a9bf74c96b72674309210279bddc6e2658c5ad93))) (.join (.join (.leaf 16 0x1040418c2218006008e6 0x7b0971b9115bb9be80136aa218c9b4f37146210687cc63d116e9af48795308e5bdcf839080ab98f1943893ec5f1c52502fe894d42de1a05f9d7971e76ff66c305f935b28ba16a04e913082fe7d857a70) (.leaf 16 0xa000000230042009001 0x2ac0ae049751824b593431e31a7f111a0bda3f2ab17f89c210c58b3e74403d075dab3841229217324a2e)) (.join (.leaf 16 0x1006010404088a400021 0x8250391e3aec2e0c15db35d9083f7d1f707c6ad1462f0737981db8478808a1eea00b8e864c70363f9ff1720d463625295943b0fd) (.leaf 16 0x100260048008c2118002 0x981433d0ad99a5ea917a6fb55f4153cd359d1ccdbb45a6a439390b6bb2b2b09a8e898de80e468bcabb1152dd03cd8c5c800e)))) (.join (.join (.join (.leaf 16 0x204200044000c0221003 0xb64f7a7948b13b78b4675c6aa96583967466bc25076806f55aa246a79a108712690022e96d5f5ae70aaa069748ed11a00c24) (.leaf 16 0x10041288020000501040 0x8706396cbd345f019baf95195b353b401da21005865f834107c40779784f5aa923ca188401b7a4fc8cf357a12ee99b7032a4)) (.join (.leaf 16 0x88601000000c2218823 0x329eb2c519e3a1799da785209a777dd9376b1fb310f9b61cb0df52a97f8d50c10d78832867203783bbfb5c76122b) (.leaf 16 0xc21100221040119421 0xbcef88d773c53783b7d1aa614ba22715b27e0eac5b3e2f6758d1afbf974472e61df3b7c6a2c0443541081b03bbb95b0a))) (.join (.join (.leaf 16 0x9041180052844000862 0x8dc9b136a1b13845042bae2b77109d4d5c6636b12022b006a91f9b3a48d406b67f597f337dac6762478b81549a9779e35bd70464564452e102948a03408f) (.leaf 16 0x20081084003800008463 0x9ece90c616b010bf890f87e1689d09b42aae4c924c49ab2c6303589a521a18e713a9128cb98603186b4b20f11d64ba1e5ebf39e1)) (.join (.leaf 16 0x84084610206108020 0x892e85d77b241eab9744817d4a2845e4162dbb3b5cb41a0110610552a97d9d617c836d4343c8359d35401a99956d577942db5403207006fc) (.leaf 5 0x600820 0xb03ea4289b3879b456650c0d17760d07a4f2)))))
set_option maxRecDepth 4000 in
private theorem scan11_1024 : Region (clearPoint L11) 1024 1253 :=
  checkedPatch 1024 patch11_1024 gates11 (by decide +kernel) (by decide +kernel)
private theorem rows11 : Region (clearPoint L11) 0 1253 :=
  (mergeRegion scan11_0 (mergeRegion scan11_512 scan11_1024))
private theorem clear11 : Clear L11 := clear_of_scan (by decide +kernel) (rows11)

private def L12 : Chart := ⟨4777, 12690219022, 173822, 116069, -257105, 455454, 8665, 3525⟩

private def g12_13 : Gate := ⟨13, 11, 0x9e5, #[
    0x1fff, 0x221, 0x848, 0x1003, 0x1024, 0xc10, 0x150, 0x540,
    0x418, 0x1204, 0x7, 0x908, 0x222]⟩
private theorem g12_13_ok : g12_13.OK L12 := gate_of_test (by decide +kernel)

private def g12_61 : Gate := ⟨61, 9, 0x1713e6940a59f23b, #[
    0x8, 0x13a406a6803c5b78, 0x90544ba023ce6bc, 0xb5d1939cc641248, 0x4180bb1a92cdee, 0x4891813b96ea709, 0xa4f13d301618749, 0xc41a0714b0b8dab,
    0x10289821ca0a6fcf, 0x12231b4476e1581a, 0xcb862cb89c2a10d, 0x68142b3561449fc, 0x44432d52907f30d, 0x8405f043975939a, 0x1658b009ec0a3d89, 0x128962a32737403a,
    0x1f088448c3caae0b, 0x135514a78a1242f8, 0x13a68e85236d1038, 0x11729fe62161900c, 0xc586f409c84704f, 0x48af6842985e3a8, 0x236c023120c6faf, 0x2aae9621ec8183c,
    0x4983012afa4f11b, 0x1022e067967a184e, 0x10e832a23975a838, 0x17308c18c89b095e, 0xf9e1148c5aa2849, 0x959131255aaf89, 0x1186e0e3b60444ad, 0x122206dc707618da,
    0x1f55aa48c89a9048, 0x1455a3128879f49, 0x90d91318310cebd, 0x15ae9c454c1708e, 0x185e69e607440b9, 0x8f25f5480c1926c, 0x18137846975541e, 0x1f63048c4036c47a,
    0x1c7a194216f5120a, 0xe213902f61a379, 0x9868467f94e898, 0x8b6c4a17165c8e, 0x1424851e528aac8f, 0x7553c3122110fe8, 0x2ece4c546914ae, 0x1bc5037900d1a6c8,
    0x1c9ae9c20fa0212c, 0xcfe094ab4c22258, 0x192286acd428161f, 0x854391d3461d358, 0x1a876e22d8c44ac, 0x1f650538419140f9, 0x1b1d0d28e058236a, 0xe18680cbc8f2549,
    0xe5769dc81891248, 0x1b34958dd018203b, 0x4826339c98bad09, 0x1673c405d22a091e, 0xda3c01656025c8f]⟩
private theorem g12_61_ok : g12_61.OK L12 := gate_of_test (by decide +kernel)

private def g12_41 : Gate := ⟨41, 9, 0x1b382b50737, #[
    0x1ffffffffff, 0x41998217f4, 0x1ad803006d7, 0x1249b88911d, 0x88be88a2d1, 0x5862d68c34, 0x11f8b092486, 0x11a4c963445,
    0x1d90981909b, 0x22234ab54b, 0x39c4738168, 0x67c80809f3, 0x114a306bac1, 0x83e07c11ac, 0x1c18e529c60, 0xd116ae0075,
    0x10f2aa78601, 0xa5335994a, 0x9669191c4c, 0x10574ba8292, 0xe2541f82a4, 0x91c4a83f05, 0x1a829282ba5, 0x19a46471312,
    0x940a533599, 0x13c300c3caa, 0x22d5c00ead, 0x60e0c7294e, 0x1f046b107c0, 0x14a306bac18, 0xf999f20202, 0xe702d039c4,
    0x1111a55aa58, 0x26fb213032, 0x9634458d26, 0x7e2c24921a, 0x18685862d68, 0x1445168a22f, 0x493711223b, 0x6d7d6c0180,
    0x6085fd0833]⟩
private theorem g12_41_ok : g12_41.OK L12 := gate_of_test (by decide +kernel)

private def g12_37 : Gate := ⟨37, 9, 0x165e211e9b, #[
    0x1fffffffff, 0x113c8d5255, 0x4f2325d26, 0x1e78d42158, 0xf0927f248, 0x3722aa276, 0x1235495627, 0x1722aa2761,
    0x182ffa0c30, 0x1b4216ce1c, 0xd88d9586a, 0xbfe830c30, 0x5d2627919, 0x1fc921e124, 0x8d9586a6c, 0x1aa7003957,
    0xa9c00e55f, 0x16ce1cda10, 0x163cf1a842, 0x18f3c6a10a, 0x138736842d, 0x1003957d53, 0xe55f54e, 0x1a9b11b2b,
    0x18493f9243, 0x464ba4c4f, 0xc17fd0618, 0x9b11b2b0d, 0x16842d9c39, 0x5ff418618, 0x5544ec372, 0x92ac4f235,
    0x1544ec3722, 0x1e490f0927, 0x2b1e78d42, 0x4c4f2325d, 0xb13c8d525]⟩
private theorem g12_37_ok : g12_37.OK L12 := gate_of_test (by decide +kernel)

private def g12_59 : Gate := ⟨59, 9, 0x22b62183e7b92bb, #[
    0x7ffffffffffffff, 0x7fc0098548bb3e6, 0x2ea45450d7c1677, 0x2d98b2c8448e5fe, 0x39dd2033617351b, 0x76d546a684633ac, 0x238685cb1df5c13, 0x6ba364d8d706178,
    0x42b3f259101e5b7, 0x4cc45ac9aec461f, 0x29a362707ccd2dc, 0x53cc9fd9212561c, 0x1f95799522b0db0, 0x38d9a52a1f56e30, 0x1bd80b6831f685b, 0x3999d70c3c03f8a,
    0x188a1feb1c73d60, 0x79f8fd3d04ca12, 0x65e52123c8b5d69, 0x4fa62b58550aef, 0x578d0f384d3f013, 0x6ec214ef3b23419, 0x4ab0e193eab7864, 0x1ab25f832c8b8ce,
    0x6ac6722f96d2225, 0x60ae5524d5721f5, 0x15f393cd6258895, 0x40d4a5117ddea1b, 0x5ab7d1448b3cd05, 0x20f5a87207eef41, 0x578282f77e04e15, 0x76ada0b3cd1228b,
    0x1581d857bbe88a5, 0x67d4a911a46b3c9, 0x3a83af84eab24aa, 0x31aba444b69f44e, 0x26ac731d134c1fa, 0x6a9261ed57c987, 0x21bb982c4dcf728, 0x58f5c80fcb21cf0,
    0x2f90f750aa1ad46, 0x53d396bad13c484, 0x7cf0485320bcbf1, 0x288c06bce38d7f8, 0x4cce51fc03c30eb, 0xdecda16f8c16d0, 0x4d8e0c76af854a5, 0x54fc0db0d44a99e,
    0x19e5386a4849bf9, 0x62ca3b4b33e0e46, 0x1199f862375935a, 0x66a1eda78089a4f, 0x62eb1e860eb1b26, 0x30e2c83afb8d3a1, 0x55b735cc6216562, 0x5dced8ace86cc04,
    0xcda7fa7122134d, 0x12baee683eb0a2a, 0x1ff67cdd12a190]⟩
private theorem g12_59_ok : g12_59.OK L12 := gate_of_test (by decide +kernel)

private def g12_47 : Gate := ⟨47, 9, 0x7bcae4d8ac21, #[
    0x7fffffffffff, 0x1eb640c47dd8, 0x5c50295c4fbc, 0x6c3dca740336, 0x537499f8192a, 0x5e8e20cc4b4f, 0x69671ed80553, 0x1e1c6155fa32,
    0x61b1bba515b0, 0x23217f399683, 0x4615797c4876, 0x607593399636, 0x44eb7ce1141d, 0x66ba76b0b00b, 0xb4189dcabf2, 0x653981fd2552,
    0x73e2b609c589, 0x89c970cebec, 0x1aabc6a5a48b, 0x1abe2265b8ac, 0xfe59abc0931, 0x65411f314b76, 0x21c796a0b59b, 0x7d45995842f1,
    0xafc7a10d4cd, 0xe16cd682b4f, 0xa9b769467c4, 0x1fc46481eacd, 0x7561a8ed3223, 0x5566892d2b1e, 0x6441beb98749, 0x1f3c8d1c836a,
    0x729a5525fc0c, 0xb427ea9dc8c, 0x759e80686b72, 0x5c8dc14439f6, 0x381b634ce64d, 0x218b7091f4f5, 0x13160b4ce7f4, 0x36186d452eec,
    0x61e262fd5431, 0x1a5e5500dbc7, 0x45ef96919823, 0x3b2aa4c0fcc9, 0x70db6601729d, 0x28e9ef91d4a0, 0x35e0ddf11813]⟩
private theorem g12_47_ok : g12_47.OK L12 := gate_of_test (by decide +kernel)

private def g12_43 : Gate := ⟨43, 9, 0x35883a3ee53, #[
    0x7ffffffffff, 0x3a06d97816b, 0x73cda6f700, 0x4365383459f, 0x7e145105bd6, 0x749dca8781c, 0x26c3fa816ca, 0x3b9748d5590,
    0x4ea668eaa45, 0x780b3b099bc, 0x5456b1b8875, 0x56691a5a4e3, 0x29f5d930a2c, 0x3aaf80338a7, 0x67c6103e6e4, 0x3ff0a0c2b68,
    0xd253297b33, 0x58da8a83753, 0x13cbf1ea105, 0x2a58c1e7467, 0x453b62d9d09, 0x31e63b42e19, 0x30e85b8cf1a, 0x217368db946,
    0x4c5cf0634ab, 0x410af1fa792, 0x15d82a2b637, 0x19bd2994963, 0x2da860a1ff8, 0x4ecf810c7cc, 0x4a39803eabb, 0x68a19375f28,
    0xe4b4b12cd7, 0x5c23b1ad456, 0x7b321b9a03c, 0x44aae2ccae6, 0x1355625d3b8, 0x26d02bf86c9, 0x703c2a7725c, 0x57b411450fd,
    0x73458394d87, 0x1decb679c0, 0x2d03d36c0bb]⟩
private theorem g12_43_ok : g12_43.OK L12 := gate_of_test (by decide +kernel)

private def g12_31 : Gate := ⟨31, 10, 0x6de2b849, #[
    0x10000, 0xe2a8e3f, 0x6eec0fc, 0x660cf927, 0x7efc5028, 0x60e63f19, 0x25afd69, 0x33961a73,
    0x57703ba8, 0x4bc0f4b6, 0x54b4ad55, 0x1cce3366, 0x1b64d559, 0x335ca29d, 0x4b968b4e, 0x6dc809db,
    0x3720276f, 0x65a2d3a5, 0x728a759a, 0x35564db2, 0x4d98e671, 0x556a5a56, 0x5a5e07a5, 0x2bb81dd4,
    0x1cb0d39b, 0x2d7eb482, 0x31f8ce0e, 0x28147efc, 0x493e60cf, 0x7e06eec0, 0x78e2a8e3]⟩
private theorem g12_31_ok : g12_31.OK L12 := gate_of_test (by decide +kernel)

private def g12_23 : Gate := ⟨23, 10, 0x5335f, #[
    0x7fffff, 0x65f4c0, 0x1caa9c, 0x184fe4, 0x387623, 0x58f1a4, 0x750c2b, 0x49566a,
    0x210bcf, 0x4d2599, 0x712e91, 0x4c8be8, 0x9917d, 0x247897, 0x25999a, 0x42f3d,
    0x549566, 0x57d43, 0x78d258, 0x70ec46, 0x10c27f, 0x29c395, 0x7d3032]⟩
private theorem g12_23_ok : g12_23.OK L12 := gate_of_test (by decide +kernel)

private def g12_19 : Gate := ⟨19, 10, 0x4f50d, #[
    0x7ffff, 0x6823b, 0x746a2, 0x26ce2, 0x37303, 0x1cc2e, 0x6b47, 0x4a45b,
    0x6d152, 0x53a07, 0x172f, 0x2a2da, 0x6894e, 0xb587, 0x50ce3, 0x33b6,
    0x1cd92, 0x158ba, 0x7105e]⟩
private theorem g12_19_ok : g12_19.OK L12 := gate_of_test (by decide +kernel)

private def g12_11 : Gate := ⟨11, 11, 0x23b, #[
    0x7ff, 0x7c, 0x295, 0x496, 0x4c9, 0x631, 0xe3, 0x664,
    0x25a, 0x2aa, 0x40f]⟩
private theorem g12_11_ok : g12_11.OK L12 := gate_of_test (by decide +kernel)

private def g12_7 : Gate := ⟨7, 12, 0x69, #[
    0x40, 0x47, 0x6a, 0x66, 0x59, 0x55, 0x78]⟩
private theorem g12_7_ok : g12_7.OK L12 := gate_of_test (by decide +kernel)

private def g12_3 : Gate := ⟨3, 13, 0x3, #[
    0x2, 0x6, 0x3]⟩
private theorem g12_3_ok : g12_3.OK L12 := gate_of_test (by decide +kernel)

private def g12_53 : Gate := ⟨53, 9, 0x12dd703303aed3, #[
    0x1fffffffffffff, 0x1d06bdbbf856d7, 0x19f6d9fbf7502c, 0xd3aa9b0fe79fb, 0x1c5077d3d7ef6c, 0x1fb371d0ed3acf, 0x1b1afb68b75f8d, 0x1fbd3fe23abd28,
    0x7edf6c3f46755, 0x113bad4b4f7d77, 0xf62d6eabf9e4b, 0xbcab9fb0da77d, 0x1ffb479a9b47cc, 0x1cd3f3e95a766b, 0xbdd7703abdbb3, 0xb37f5584ecefe,
    0x15ed9c897feca7, 0xbc2e7bf92fbf, 0x1b9cecbb461fcf, 0x10eb7553fe9fb8, 0x1ee59739bb7d58, 0x1df7fccba18d69, 0x11f8ffd9cab4d9, 0xf9f0e21eeecfd,
    0x4afd2d3bafbce, 0xdf9bb7282dede, 0x1de1f73ae4f30f, 0x1e19e4eb9df0f7, 0xf6f6829dbb3f6, 0xe7bebb9697ea4, 0x17e6eef08e1f3e, 0x1365aa737fe3f1,
    0x12d630ba67fdf7, 0x357dbb39d34ef, 0x3bf2ff955dae1, 0x1e7f0c5ba6e73b, 0x1fbe93fbce87a0, 0x1ca6ffd22736f5, 0xfee6e4355fd9a, 0x19bb7ab81dd77a,
    0x1acdcb52f9f967, 0x67c5b2b3c5bff, 0x17dcb61bf3aa7a, 0x1a4f3faaed68de, 0x1dd7de5a56bb91, 0x155cc5f86df6fc, 0x297ab88ff97bf, 0x163f5da2dbeb1b,
    0x1e6b96e171d9bf, 0x6defd797dc147, 0x1bf3cfe1b2ab96, 0x6815dfbf36df3, 0x1d6d43fbb7ac17]⟩
private theorem g12_53_ok : g12_53.OK L12 := gate_of_test (by decide +kernel)

private def filters12 : List Gate := [g12_13, g12_61, g12_41, g12_37, g12_59, g12_47, g12_43, g12_31, g12_23, g12_19, g12_11, g12_7, g12_3, g12_53]
private theorem gates12 (g : Gate) (h : g ∈ filters12) : g.OK L12 ∧ 512 ≤ g.p*2^vDepth g.p := by
  simp only [filters12, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨g12_13_ok, by decide +kernel⟩
  · exact ⟨g12_61_ok, by decide +kernel⟩
  · exact ⟨g12_41_ok, by decide +kernel⟩
  · exact ⟨g12_37_ok, by decide +kernel⟩
  · exact ⟨g12_59_ok, by decide +kernel⟩
  · exact ⟨g12_47_ok, by decide +kernel⟩
  · exact ⟨g12_43_ok, by decide +kernel⟩
  · exact ⟨g12_31_ok, by decide +kernel⟩
  · exact ⟨g12_23_ok, by decide +kernel⟩
  · exact ⟨g12_19_ok, by decide +kernel⟩
  · exact ⟨g12_11_ok, by decide +kernel⟩
  · exact ⟨g12_7_ok, by decide +kernel⟩
  · exact ⟨g12_3_ok, by decide +kernel⟩
  · exact ⟨g12_53_ok, by decide +kernel⟩

private def patch12_0 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x60004200000100001 0x3fa73f6e0b9e3212425b037621d9) (.leaf 16 0x200800108020 0x36ee0e94424b28700d7a)) (.join (.leaf 16 0x8000000401082000401 0x3c5836612718438d38b930b42f07175f22161fec) (.leaf 16 0x200802100000 0x359e42d30193365e))) (.join (.join (.leaf 16 0x5008000000200001 0x3f8f3c4a3c35259c22160ce502a022531af81dff) (.leaf 16 0x10400000000842000401 0x42cc0e8b13c009d9179a225e2c572448)) (.join (.leaf 16 0x8000004000040100042 0x26b1f9422900db815670e3e1c1205ce) (.leaf 16 0x20080200002010020 0x3b40319638ae15a319bd11f530c9)))) (.join (.join (.join (.leaf 16 0x20000080020000008401 0x35f5221b20bc0b38044322cd14171cd835da1a25) (.leaf 16 0x1000220000100400 0x4ba26da295f2253281c27ea)) (.join (.leaf 16 0x1008400000108003 0xd5b230a22e326a4160336d5377e3d3026b71838) (.leaf 16 0x10001000200040000402 0x198d04cf05a7433b2b563998343c32ce))) (.join (.join (.leaf 16 0x62000000000108421 0x3c14167f145d23470d3600681d5c08f508aa164b) (.leaf 16 0x40000000000200061 0x3e1d35b81d4f142842163ff423580cd0)) (.join (.leaf 16 0x104001840100c0200401 0x301b13b123842a111f0c1561096d34181d2211a102112d2222903fb9145e) (.leaf 16 0x8020084003080000001 0x236824c806e70bd43c263ae72db624cd23051e6b4153108a2926))))) (.join (.join (.join (.join (.leaf 16 0x100210002000c0000801 0x3dfc3008308133c233e32f261f1217d72ba2031c1271) (.leaf 16 0x1000080000002000402 0x367034c4225d1f9f06a71b1d32f823c10655)) (.join (.leaf 16 0x100030802100441 0x3c2814c83aa82e5f012c01f028a82dfb3144288709d91084) (.leaf 16 0x420000000802000803 0x1b0a159933e708f22bdb23fe30e522cd1e28))) (.join (.join (.leaf 16 0x10000010003 0x30b20dce029a2b9518160e97) (.leaf 16 0x8000080210000200c00 0x134e07a70985209e243b23ed2b6f0a2d01f2)) (.join (.leaf 16 0x8001004401000008001 0x144434d32c7a41f82eba3fdf1b8a1e290caa) (.leaf 16 0x18403000600080000020 0x22f6160504e4114134a82bba230a2550171f1615429424781bbe)))) (.join (.join (.join (.leaf 16 0x200842000001 0x12d628d918df130c0abd) (.leaf 16 0x10000088011800000001 0xa1c00f825570b2506e124b5393d23160e612e04)) (.join (.leaf 16 0x60000220040010801 0x229f1e8e1e82247218c506771b703bd3056124d7087e08d0) (.leaf 16 0x100400084a000000 0x34a224f22efa340c3f2221a811200b9e0990))) (.join (.join (.leaf 16 0x22080220040110001 0x2598186b016930dc03da386b23472716345c409731cd06e3) (.leaf 16 0x88010004000c0110001 0x3c763e5d0589252f28b70cd032491c3f08e917c84294284e17fa)) (.join (.leaf 16 0x2000000200802100062 0x39932df027c124311afd10a40a92004c09f7046409cf41c224731ebc1378307304f6) (.leaf 16 0x8820088000040100000 0x28af256c24f7325e303a27b7048640344170))))))
set_option maxRecDepth 4000 in
private theorem scan12_0 : Region (clearPoint L12) 0 512 :=
  checkedPatch 0 patch12_0 gates12 (by decide +kernel) (by decide +kernel)
private def patch12_512 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x3080200006100021 0x3c731c4b0dd51c3c0d6838ad057e03c2356b30850309) (.leaf 16 0x420084011000200460 0x3e37176042243f292c223152147a3c2e2384168034df17ea0598)) (.join (.leaf 16 0x30000004010000000402 0x3a1039322dd72ce3191200ec146133343e5025a9011c) (.leaf 16 0x8423000010000000001 0x32bb359e08f522e11d65071e201432e2))) (.join (.join (.leaf 16 0xc210800100801 0x2f772b1029a414623a1d11f840af2f3525e61a74) (.leaf 16 0x20000000080008001 0x12c30eec07b7257c3ae5)) (.join (.leaf 16 0x420000000000220003 0x13301bfd35dd262335e820761a3100523ff123c11a77) (.leaf 16 0x8001004000002010421 0x2dc7143b095941732c95265617b03e722242)))) (.join (.join (.join (.leaf 16 0x804100c610840000802 0x8d4399700ea1e6e2c0427e4176e23290818006427ac1f63266012ee066a35510e53) (.leaf 16 0x80210002000002 0x2384204a1bee2cb33f8b1422)) (.join (.leaf 16 0x1000240002200000 0x23fe0c61347a2c40269d26010eee35051a24) (.leaf 16 0x10420000200002000463 0x2d55088d04c31b5715b3210713b4301021db1e6a2ee81f631976))) (.join (.join (.leaf 16 0x8420284000042100041 0x6a9153b0cf13d9d344223231c480b9326da1a792b8b07a23a8119720bbe) (.leaf 16 0xc20004000002108802 0x6af066a00882a31402e01fc371b224b41223b9b37c017ce)) (.join (.leaf 16 0x10021000000846200480 0x1e0510cf40f0271731d411f62ab5255d178f41281dd415a335e32ab422871963) (.leaf 16 0x38841000220840001001 0x3a9230192bb125a722f520cd0d4a24130a313ade268600a90205359b243b2aa61c6828c70e8c0c650a511284))))) (.join (.join (.join (.join (.leaf 16 0xc21104000040008000 0x2fd927540a4816990fe5376c271b043f3f343745) (.leaf 16 0x4000000008840 0x300a30d7198403d332bf0f7b)) (.join (.leaf 16 0x1000004200000000001 0x3ed42926275e24531e6a27673a2f) (.leaf 16 0x8041000010040100041 0xda52fcb2ccc05922db828d52f023f702c392791))) (.join (.join (.leaf 16 0x61000400800400001 0x39d032c41ec715070ebc0d573048347a27d525ba24783668) (.leaf 16 0x800000c000000010801 0x2a7823651b431b2b1a86095e27ce270b0fb1)) (.join (.leaf 16 0x8400014001804008020 0x36463c1b362e217712f208f0006742da2050175912430edf35e31354) (.leaf 16 0x460080000800208002 0x375a382935d327cc0a7e149e280b186026da3c9e1b20)))) (.join (.join (.join (.leaf 16 0x1000000080000000 0x2c5341c10c54) (.leaf 16 0x8000104010080000022 0x171d3a592de529570efd3fdf28481cf324b516c6)) (.join (.leaf 16 0x18002000211840000021 0x1bb51603069742b916a53c6a0db727901bfc18f02ec33c0c0e1b) (.leaf 16 0x4010840000400 0xd6c28853d512a5a2f95))) (.join (.join (.leaf 16 0x8000080000004001802 0xb68067f2923060a3c583036270d237c1b9f05173f0d0490) (.leaf 16 0x8028008000002010000 0x337d13143a0732de2da9268925cc24f2172a142128c20edc0f8e421634bb)) (.join (.leaf 16 0x10400000410002100000 0x1bff072d142023a71a0e3b62293e0f94) (.leaf 16 0x422084000040300000 0x2f85202028ff281542de42e33e9b2d95176c0e84))))))
set_option maxRecDepth 4000 in
private theorem scan12_512 : Region (clearPoint L12) 512 1024 :=
  checkedPatch 512 patch12_512 gates12 (by decide +kernel) (by decide +kernel)
private def patch12_1024 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0xc210000110400 0x3bda285c003a35cf1e28280024101da13f31) (.leaf 16 0x420000020844000001 0x293c1bf726a216bd1ab3169f295427c1417c)) (.join (.leaf 16 0x800010210000100800 0x40cb071b3884378e10fc0d5216c9252f0b273f160dfb) (.leaf 16 0x10400004400002000042 0x3b4d332041bc0ce7296e04a50eec3b0a13153aa0366b))) (.join (.join (.leaf 16 0x400000000002008401 0x271c3a85135a06e62979) (.leaf 16 0x2000000000802108080 0x39d539c637ed2fdc202e1b90104b065a114a269706e90f883992289a10f308f5)) (.join (.leaf 16 0x100210040000400 0x2c3e01ab057724283ab829b6) (.leaf 16 0x820000050000300001 0x439d0a4625303fd423e9217a1ee818f13f7c256c145c1e4f)))) (.join (.join (.join (.leaf 16 0x1000080400000200021 0x3be827cc08e2021707471597139f3c9129f31633130f) (.leaf 16 0x8001000201802300400 0x43663f2e23a12c5f144013d836d93d153447316f06eb)) (.join (.leaf 16 0x30402080000082000000 0x40303ab4359434a822fe0fcc1af02ad014a42eb42a30291f3f8f) (.leaf 16 0x4000000000000 0x3ad))) (.join (.join (.leaf 16 0x200000100c4000003 0x2ffa2a6d1f131c1c12892d2e25902bd025a91315) (.leaf 16 0x10001084000000028020 0x2728065104871b2e162141ac34a5309d27b510b32c53)) (.join (.leaf 16 0x1040000c0100021 0x30ea18a92aaa37512ad32a460d87210722ab) (.leaf 16 0x420080210000000420 0x39b5226e29a41795069d0e9e3084))))) (.join (.join (.join (.join (.leaf 16 0x822000001802100001 0x1ced06be412f2ae725e6242b17f817d42baf04032e08) (.leaf 16 0x8400084020002400401 0x214613f6432c0d6c1b030c7039a3362f2def115c0d0324792d7f)) (.join (.leaf 16 0x400008200040000062 0x2b24378d21ee19d619ea185d176b16c6066b03b6) (.leaf 16 0x200010040010401 0x31212ad019df06fa3df4252f2db8079b1ebb1603))) (.join (.join (.leaf 16 0x20000040000000000 0x3a3c3d5c3a24126f04ba) (.leaf 16 0x10000000011042008403 0x199a16db262313aa00d32e66026e132d319036a72b612a29)) (.join (.leaf 16 0x84200800101c03 0x1e672035002d2d16058f3e47233021dd1afb1a6e158804583bf71ced1113) (.leaf 16 0x801088200002000c01 0x38d100d603a614441d8414d5353802282b9e1a26098d043c)))) (.join (.join (.join (.leaf 16 0x8001104400000008421 0x33b81319367328d2353d402127dc41e3110b14af1f40) (.leaf 16 0x1000000100100000 0x89d3a742e78246d16b72bdb)) (.join (.leaf 16 0x20080000044210001 0x487354922bd433f2aae266010a829a718820dc3) (.leaf 16 0x10040088000840008002 0x3c4a003a3c1e3bc532e032892f142c522c1812f214c00b20))) (.join (.join (.leaf 16 0x40100c020000110c20 0x41cf0213339128e10d4519cf17a8096d34b12496338f233510ed1c72) (.leaf 16 0x420100011000000020 0x1a31202d22a4080b2c553815292d0536)) (.join (.leaf 16 0x441080201000200001 0x33733f1e2bd516f710a50da632fd26be42f62fb5032f) (.leaf 16 0x1421008210000000402 0x3e593589297524111fc1365b264d2c922b332efc336e4304269d0f64))))))
set_option maxRecDepth 4000 in
private theorem scan12_1024 : Region (clearPoint L12) 1024 1536 :=
  checkedPatch 1024 patch12_1024 gates12 (by decide +kernel) (by decide +kernel)
private def patch12_1536 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x100000 0x22c0) (.leaf 16 0x2008000100108040 0x3dd92ccf19e40b5931a02c5d08d407120ce20f6d19ab0ef2)) (.join (.leaf 16 0x800008060004e100420 0xd1b3ec81c210c660c3f3fd53d3f25fa24af20fc16e5159a0adf112f43a51102) (.leaf 16 0x8821004001000108000 0x24132d0c0b88344926da07a81e0e0ed83e3b040c))) (.join (.join (.leaf 16 0x10040004210000000020 0x2bb8299614b80b0a00d838ae40b43dcb) (.leaf 16 0x8003000600800108400 0x115530732ce326cd2d7f29a614f1026e1afb2d152cf5)) (.join (.leaf 16 0x421000020000000841 0x37e60e3e2fd13c2b2dde369903be31e127b32d49) (.leaf 16 0xc001000018001 0x3dbd3a1e37bf3f4513b92e7921b50cd03997)))) (.join (.join (.join (.leaf 16 0x8480000040802000401 0x23a43eb742f714f80b9e078440f62dd1299b2717084d12c82d861bdc) (.leaf 16 0x90010000100420 0x21c143af2efc27201bb50835251824f63e20)) (.join (.leaf 16 0x18000000010840200002 0x4319392b075a1c8a0d0e13332dc32c3d3e62372a) (.leaf 16 0x8400080030840400001 0x1c0b331721701e081bb219de29a4399424f1229014ad147d2400))) (.join (.join (.leaf 16 0x1000088000042100c61 0x25981ec70cd90c6607e1089e02ad2e002dd3182022bc066604cf36852a0d09d70baa) (.leaf 16 0x801084400000400000 0x3d7e393a1ec202e600423ef3133042f427542115040b)) (.join (.leaf 16 0x8401100030082008001 0xf69076342d63a4b36622e3d2c060ee734b42bdb05cb13de1467) (.leaf 16 0x88200004100020 0x25412dbf0be62cc2358910e4297e1d08))))) (.join (.join (.join (.join (.leaf 16 0x1004200000008000 0x32f02e7a10a5024e) (.leaf 16 0x410002008000 0x1add063436cd2a371b5e)) (.join (.leaf 16 0x8021004600000000402 0x430e92eb70e6830101db00ae1180d27910bb3) (.leaf 16 0x400000400882108001 0xc612de90563170a39f1074c035230d5307335aa))) (.join (.join (.leaf 16 0x1001000010800030800 0x2ef42d47161f10073bad1e821045253323d61eb213600a32008134420a1c) (.leaf 16 0xc80004410080000002 0x2f1c15910a2d3bbd39f7332c304f2ec6420d2f500b7120bc035e2314082c)) (.join (.leaf 16 0x23004000080400001 0xa2932db27ce1682196641c226563dfc3d51126c102c415a) (.leaf 16 0x80000044008021 0x276a24841d170425422717592f31)))) (.join (.join (.join (.leaf 16 0x4000800800000 0x306d21d1426e3e932c41251f1afc18ec156510b8) (.leaf 16 0xc00080210802000421 0x405a33fa029825c93b5a335216531a772f6e0cfc2a38)) (.join (.leaf 16 0x80400002120000 0x290340ad137e1b74179832ac2dcc09a30579) (.leaf 16 0x8000008070000100420 0x42672da0044f39792b3929bf280b27b20c7b06692fab33ee0835))) (.join (.join (.leaf 16 0x1084210000000020 0x12ec1d2c30a3381510181cb3) (.leaf 16 0x401000200082008840 0x1625066719f92fe81a1c317638d32575124326da12dc)) (.join (.leaf 16 0x1004040002000020 0xaba3cee395124c0127e0cff2e8a1f39) (.leaf 16 0x1004230000010001 0x3d311e6716f7410e30252e51428e280a3bde))))))
set_option maxRecDepth 4000 in
private theorem scan12_1536 : Region (clearPoint L12) 1536 2048 :=
  checkedPatch 1536 patch12_1536 gates12 (by decide +kernel) (by decide +kernel)
private def patch12_2048 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x2108c4100400 0x3f122e27334f3856264719690e30057428480322) (.leaf 16 0x8000084001002320002 0x1f632bdd30623961067f28f934cc2edf1e40296b21df178c00011a7708b0)) (.join (.leaf 16 0x402010410000000040 0x138d37000b65416830cf2da9134e25900ad31d020a4706fa) (.leaf 16 0x421008000802008002 0x1cc32c8309f313c16150e5330143af02b6b0ba1))) (.join (.join (.leaf 16 0x8040080002000108000 0x3eef34612ed63cae41ce3f7638690833315e08a4) (.leaf 16 0x420000000002100402 0x30dc33bb1432001f0bb928850802)) (.join (.leaf 16 0xc000002300000084a0 0x37882cb40ad23cfa3d5e1e1a15fa2b57045128d525b724f711621126) (.leaf 16 0x8020180200000000801 0x434b04d63b020e9b02ad232f3103196603b8)))) (.join (.join (.join (.leaf 16 0x4200842018001 0x262620e4308d04db0d4e25700962014f3119) (.leaf 16 0x22080010844000000 0x3e7a2c5f28c2147b2e783ae1221831b227d3)) (.join (.leaf 16 0x28441088000000019040 0x3c6d2f892c65112902fb00bb412f304115ca03be2b5526b63c6a23e3087731562f5b1f48000d2fb0222e) (.leaf 16 0x10008000000800010000 0x2c2d19b242ee3ddf36f42c361e831e441e1615472e9526b72444))) (.join (.join (.leaf 16 0x8020000600000108400 0x1d6b165d1b540a08072d31932233317c) (.leaf 16 0x420080000080000001 0x3c0a4115377136a319542677)) (.join (.leaf 16 0x220842000402 0x30f828ff06df434e31d03c401186279e1ac5) (.leaf 16 0x80184010804000008 0x3f612d43252d1eb5324e0cd4012128871e1a2fe04312111a2e4e25f9211b1bf715d8135410090838))))) (.join (.join (.join (.join (.leaf 16 0xc010804101021 0x30401b2e09f4320d20c32c651b0706f241a620b2151e0a8d34940445) (.leaf 16 0x8002000001040008840 0x42222dbf1a721d3d182b01642128095505652b3f2004)) (.join (.leaf 16 0x11420004010802000020 0x3304265236e52854211c06a705d72eba324a410500191fbd319f) (.leaf 16 0x80000000040100820 0x396b1f8a0544051508da293c418225693b7b))) (.join (.join (.leaf 16 0x10002000001000010040 0x2fd81c7f328730651d5c185241453e743ddb1e0f) (.leaf 16 0x801000250040100002 0x2423229014072b923b9e33c7328c076f064a3b8f2ae8214017dc)) (.join (.leaf 16 0x460100010012008020 0x32c431db20771b4928cb1900193c3f303dba2edb2c8e1a9812480bf70b2b083b3d870b90) (.leaf 16 0x48400080200000210020 0x382d35a2263b230c16cd11030eec0548037c178c328327613d8a046e42d43bdb0778)))) (.join (.join (.join (.leaf 16 0x8004010000000000403 0x18612b7a1c4d165f0339388337c032682947063235c729790451) (.leaf 16 0x4000000108001 0x3e1b172c40f93301)) (.join (.leaf 16 0x1000200140000440 0x418a13b53f612d911b5016d212ce36cd30ea1c3f) (.leaf 16 0x400000410884120800 0x2c77301f1809115c42b23ef814832f3808090a6940f3397938f53895333e0e30))) (.join (.join (.leaf 16 0x84000000000000401 0x361f1b7a033401b133cd32b32d7c29b62035237d) (.leaf 16 0x4201082200000 0x76026c0303f05233ffb0f790b2f40f0337b)) (.join (.leaf 16 0x8000004201000000400 0x264d025621f718a302923f2f) (.leaf 16 0x420004610080100800 0x2f56074c23030be008d401de185233b8316f19e416000d51))))))
set_option maxRecDepth 4000 in
private theorem scan12_2048 : Region (clearPoint L12) 2048 2560 :=
  checkedPatch 2048 patch12_2048 gates12 (by decide +kernel) (by decide +kernel)
private def patch12_2560 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x10c000040000020080c1 0x31992476267d0e170dcf358528573fbe3df23a0b24f023830988022f3a37) (.leaf 16 0x23080620804000000 0x3bb6320e233e18011ac5231a16c8030a33f529f324f73c743236)) (.join (.leaf 16 0x4040000100001 0x1f583a0511460aa400df27193925) (.leaf 16 0x421004201004000022 0x20b30ad50613343231fa05c800061d3e02592d7f1bb0142d))) (.join (.join (.leaf 16 0x1000108000000001a000 0x3a1a022811fb31f431240f27083a36da3034274417b60ee10cfd0bb3075a) (.leaf 16 0x3000200000200401 0x37cc346f056e30dc220311b011d30dae)) (.join (.leaf 16 0x2000a00840208021 0x28850eae385620bd1a8a174b050e29bc39972a301b9d1e8016aa0a2d) (.leaf 16 0x8400080200902008001 0xd9b34ac41f529a433b2406933c711e50dda0f2b222d0142)))) (.join (.join (.join (.leaf 16 0x20000000840000000 0x68f185504ba) (.leaf 16 0x200004000800000022 0x425539c738d136a235a0354c33d92ecb2ebd2dac2c4728ea26bf19530cb20abf2ac4331c374505660305)) (.join (.leaf 16 0x8401000200840100022 0x706057b3af310b10ebc04814147065834e93279) (.leaf 16 0xc00080000800108403 0x115b0bdd02283ee3186e130013272a7e2a6d133600a0))) (.join (.join (.leaf 16 0x8400004200000608442 0x3df738532c021a183d98248721e1141d13030937167335263a590c991801004d) (.leaf 16 0x28420000210044108020 0x421e2ce928dd26aa25870ca401a541a625d01af52a0119281e91002d2815)) (.join (.leaf 16 0x280000802200020 0x43a732c52bda2476219c17030a71356312732246) (.leaf 16 0x10004000200046200000 0x36aa2bc1417a2d922aaa25a6400106af32fe1042071e192f07d1))))) (.join (.join (.join (.join (.leaf 16 0x40000000040208422 0x38950f6d35a0043c003d394607853a2723281ca7) (.leaf 16 0x400000020040000800 0x1ae190004592fcb2ddf1cea)) (.join (.leaf 16 0x23000010000018480 0x22a73b1727010b9535dd13f70b5f01a23b5c3edc2de12a841656) (.leaf 16 0x20080200008000402 0x3a4b20693f1041bf3bd12c9806cd2d5042ac4278))) (.join (.join (.leaf 16 0x84010100108c2000840 0x37b727ee23a13d7e361a338310ba2ae71396317526c20f2b042f09a2034c3785203c) (.leaf 16 0x10000004000800018000 0x2e2526de16c62803404f0f3b024e)) (.join (.leaf 16 0x423000000080008001 0x36cb069d3657221418761320040b0baf07a7) (.leaf 16 0x8420080000800200000 0x2e2d186c3dcd297918d743393c4f)))) (.join (.join (.join (.leaf 16 0x10400000000040300401 0x2cc0184a36942753412824910001170b23fc) (.leaf 16 0x8400000000000408002 0x3408322c2fe92db22b2401cc3a9f11c50d77)) (.join (.leaf 16 0x8800000020800000080 0x380830812b903ece2eda11bf3c323a5821620daf) (.leaf 16 0x21184200882000003 0x3c16128927430acc0a781e81020305103374236f158536d10a960722))) (.join (.join (.leaf 16 0x420000020046000000 0x2ba3104b3e1e3d91037c2eab0a1c02cc) (.leaf 16 0x22008010006000400 0x32d80ffa029235d12eea0c1527121c120805370e)) (.join (.leaf 16 0x30020000001040000002 0x423824161aea170b0d6001e219c226d70f873b4230562b61) (.leaf 16 0x8180211000208c00 0x3e2c3111264925441da91a56058e0486429439970df30ee32ac12ecf1cae374b348d20823c1f2a4c1cd8))))))
set_option maxRecDepth 4000 in
private theorem scan12_2560 : Region (clearPoint L12) 2560 3072 :=
  checkedPatch 2560 patch12_2560 gates12 (by decide +kernel) (by decide +kernel)
private def patch12_3072 : Patch :=
  (.join (.join (.join (.join (.leaf 16 0x1000420000000000 0x344e287e153123a70252) (.join (.leaf 16 0x8400000220040018040 0x28c35624183377216c637883b021783153b21331815) (.leaf 16 0x8003000000002008421 0x32af416736e12b9e23001377117d048d39be))) (.join (.join (.leaf 16 0x10000000012040200001 0x384a339137c521a6203c1e4c0731150a254811ef23e6) (.leaf 16 0x20020620042000801 0x2262340e2a1b2785201f1ee418f60bf1095b3512280d1aa530340085291e0c670442002b1aa8)) (.join (.leaf 16 0x4001000008400 0x3802103303c43d981669) (.leaf 16 0x800000000002000001 0x32e21a4310b11792)))) (.join (.join (.leaf 16 0x441188010000010002 0x264d202e13b0383f40720ebc00a93da814f82bdb33891dc82e6622d2) (.join (.leaf 16 0x401180200002010000 0x4ba0a3e3b9c31152b520ffa06af38dd2994) (.leaf 16 0xc00084000002000020 0x387c359731533c1207972bba360e))) (.join (.join (.leaf 16 0x8060080021040118000 0x41aa286915c00c1338983ef8141d3d032fb238513811163c158b09ef) (.leaf 16 0x10401000040040011800 0x171c059b00d110c23f0d37ed2e3c2bc1167e236e22ce40103925317330fa08090386)) (.join (.leaf 16 0x400100000000100c61 0x34a23ff40a062c1841e92d8d030c2beb29e30c4d38b9) (.leaf 16 0x1610000000001 0x3f502f4527c7238a1cf91ab31a2a083e0290015501003dc939e3))))) (.join (.join (.join (.leaf 16 0x8400008000080100400 0x1855059931a219663b1921913fd038f6) (.join (.leaf 16 0x8820000010000008000 0x30131258004c1a0e0442361c) (.leaf 16 0x80004000800100023 0x3b912f290b1f08cd03b72a3039330c123d4c1f6a15df))) (.join (.join (.leaf 16 0x400010000002000003 0x256f1cd814260efe0817264e39c9315d2c55) (.leaf 16 0x4221842100020 0x2dce2fd428571894340f148f0c0e39703e9b2813261e)) (.join (.leaf 16 0x20008010080300001 0x16743bf2328028c62e8221a93c1f2c6715913064) (.leaf 16 0x403000020002000020 0x65e26b021fc048d39ad36a10c354108)))) (.join (.join (.join (.leaf 16 0x421080000002000001 0x2de838092c921d3d3e0b173b) (.leaf 16 0x400004070000000022 0x316f39ea2809234720bc20a41906078107211e3f3d482627)) (.join (.leaf 16 0x40100000084c008403 0x163d2c382bde2107376c246721e3135410ae04af114c24501a37158b11e3) (.leaf 16 0x10001004211002100400 0x367632473a2739cd1dbf0e672c7a0e841930239f3241))) (.join (.join (.leaf 16 0x22084200080000020 0x372629571bb526da258a23c03c1020a40bc1) (.leaf 16 0x400004420000010001 0x3a6433b2180f15042ccf2051312310cc24d6)) (.join (.leaf 16 0x10800100420 0x1bab129b207e0487014f) (.leaf 6 0x4028001 0x416b3b7d30f52e6f1abc12b0106606f5))))))
set_option maxRecDepth 4000 in
private theorem scan12_3072 : Region (clearPoint L12) 3072 3526 :=
  checkedPatch 3072 patch12_3072 gates12 (by decide +kernel) (by decide +kernel)
private theorem rows12 : Region (clearPoint L12) 0 3526 :=
  (mergeRegion (mergeRegion scan12_0 (mergeRegion scan12_512 scan12_1024)) (mergeRegion (mergeRegion scan12_1536 scan12_2048) (mergeRegion scan12_2560 scan12_3072)))
private theorem clear12 : Clear L12 := clear_of_scan (by decide +kernel) (rows12)

private def L13 : Chart := ⟨4777, 20566973577, -225253, -243212, 212623, -254369, 5679, 5696⟩

private def g13_13 : Gate := ⟨13, 10, 0x9e5, #[
    0x800, 0x1610, 0x681, 0x12a, 0x28c, 0x4e, 0x1130, 0x432,
    0x1c8, 0xc5, 0x152, 0x1205, 0x1421]⟩
private theorem g13_13_ok : g13_13.OK L13 := gate_of_test (by decide +kernel)

private def g13_61 : Gate := ⟨61, 8, 0x1713e6940a59f23b, #[
    0x1fffffffffffffff, 0x1ba58ae9705c0900, 0x47ca8c768098e88, 0x1457e6582a35c80, 0x145302ab0d895b03, 0x1c821883ba03d5b0, 0x500331236efc382, 0x75abb5064340aa0,
    0x16a34721a4459c88, 0xb2c02d471b50616, 0x153f1800956c4d14, 0x122987485e15809d, 0x1216715155e0b520, 0x192949a7a10225a9, 0x52e23cc8a9b330, 0x9005992c5947b0d,
    0x532c8c0e707e181, 0x337105ca6c5a07, 0xa5ca59e4400da26, 0x152a736810c11b31, 0x92664fbe0694404, 0x90d872c106ae2aa, 0x8e5d08c6d02a30d, 0x1695844e1194072d,
    0x464c57283b46630, 0x138e41510c496b83, 0x15b8248832186d93, 0x129d1e3c220fc801, 0x14103318f9494be, 0x6bec14b92e001e, 0x19c86504427d3c21, 0x12f90882984e7087,
    0x1d274a0df580f00, 0x4a7c633020a0fa5, 0xfc110f1e2e53002, 0x186130449076b936, 0x1a48c22a09c7383a, 0x18b7053a8c98818c, 0xa621c886a5b69c, 0x1502d8c42e9c5618,
    0x1d5820d386c24aa8, 0xa581f7c99924404, 0x20c205b3952b19b, 0xc0089e694e94c8b, 0x8d94e823b301c0b, 0x1f839c0c4d329030, 0x18a68d266802561b, 0x16544cf11d280199,
    0x110217964a5272b4, 0x141eaa2a39a12095, 0x6a1e84b86513720, 0x8daa40063f2a516, 0x2b638ad00d34d0c, 0x68896138b15a227, 0xb0982b756b80aa, 0xfddb12330028838,
    0xf0177046104e1b5, 0xa46c3550328b81b, 0xb150699fa8a0027, 0x6405b8c54f8822e, 0xe83a5d46976012]⟩
private theorem g13_61_ok : g13_61.OK L13 := gate_of_test (by decide +kernel)

private def g13_41 : Gate := ⟨41, 9, 0x1b382b50737, #[
    0x1ffffffffff, 0xd0b93a1624, 0x16a492b6409, 0x8ce624c632, 0x1820c3679b0, 0x1061b3cd86, 0x1e0f06183c1, 0x115256a4a8a,
    0x16d02da0ba, 0x1624685c9d, 0x1b40b682e82, 0x10008e77738, 0xfd00b55a01, 0x30783e0f06, 0x648ce624c6, 0x16ab402fd,
    0x8c54628e71, 0x19ddce20011, 0x12495b204da, 0xa8a92b5254, 0x14628e71462, 0x314738a315, 0x15256a4a8a8, 0xd9026d4925,
    0x400239ddce, 0x738a31518a, 0x1fa016ab402, 0x11923398931, 0x10783e0f061, 0x2d56805fa, 0xe777388004, 0xba0b6816d,
    0x1c9d0b12342, 0xe82da05b41, 0x8a92b52545, 0x1e0c30783e, 0x10d9e6c3041, 0x6cf361820c, 0x6319233989, 0x8136a492b6,
    0x12342e4e858]⟩
private theorem g13_41_ok : g13_41.OK L13 := gate_of_test (by decide +kernel)

private def g13_37 : Gate := ⟨37, 9, 0x165e211e9b, #[
    0x1fffffffff, 0x11eb0d4899, 0x134a1e46b8, 0x1c00f67546, 0x132a570e25, 0x1c04d74b15, 0x895e7a544, 0xadba480f8,
    0x1124cf4a1d, 0xbeb0c80d9, 0xc1ccfe411, 0x2b124bd66, 0xcd585d186, 0x8e5e4a14e, 0x13fb0498a2, 0xf7304b0e2,
    0x41e9f4619, 0xc15f70705, 0x13ca1c9aa8, 0x2ab270a79, 0x141c1df506, 0x130c5f2f04, 0x8e1a419de, 0x8a3241bf9,
    0xe50a4f4e2, 0xc31743566, 0xcd7a491a8, 0x1104fe6706, 0x1360261afa, 0x170a5e6491, 0x3e024bb6a, 0x454bcf522,
    0x151a5d6407, 0x148e1d4a99, 0xc55cde007, 0x3ac4f0a59, 0x1322561af1]⟩
private theorem g13_37_ok : g13_37.OK L13 := gate_of_test (by decide +kernel)

private def g13_59 : Gate := ⟨59, 8, 0x22b62183e7b92bb, #[
    0x7ffffffffffffff, 0x53ae66a22f43361, 0x1c81c49fb350f0f, 0x732f0b667510f60, 0x87fade1a2254ae, 0x7b4f9817d8411e1, 0x3682d6b631740bb, 0x6ed20719eb218ba,
    0x6ed42980d5d7334, 0x733fc1054dc2d0b, 0x5423ff3c4355252, 0x73d121f08f32bc4, 0x4de794f122b3445, 0x5c99cac093f386a, 0x656c7bd9e490285, 0x27fdd80b59209c6,
    0x2d105b736e62b1a, 0x4f013ea94c3599e, 0x2047761e3f55ca2, 0x14e22b27a3a7c4d, 0x31ae4640b23775d, 0xcd72c346ea48fc, 0x7ab05c1fe4a498a, 0x5425d08d3f3723a,
    0x1ab161c5d8f5a64, 0x6b18ee4f5e32803, 0x1e444d61afa5e91, 0x4f349f16d980b0b, 0x6a397ac65960559, 0x7934e02a5951d75, 0x501cb27d75c54d2, 0xd7a715cd5034d3,
    0x23e4b3ce8680cdb, 0x1ac889e44bd2fac, 0x49dc635e00a63d7, 0xe1a356132d78dd, 0x442e90aae2767e5, 0x60e8357a8c9293f, 0x30d3acc1f892bb1, 0x989d635d776268,
    0x13511ca591f2e2f, 0x61bb881229d57e3, 0x55f203cbccd6194, 0x3b6822d2c6a33b6, 0x406eff931c824d6, 0x6f78da9d0a0493c, 0xd4e64eab0e7e48, 0x3ca79ecd1166a24,
    0x3e122f391ea6788, 0x73ff10aa5255611, 0x20ff33e85a1d95, 0x650add96675d58, 0x63812ddae8c26bc, 0x35ad05b6e817463, 0x2067cb7c3c410df, 0x1ed7f843a95222c,
    0x1b43d3383784573, 0x648e04e7878566f, 0x1599d72c36617a2]⟩
private theorem g13_59_ok : g13_59.OK L13 := gate_of_test (by decide +kernel)

private def g13_47 : Gate := ⟨47, 8, 0x7bcae4d8ac21, #[
    0x7fffffffffff, 0x73399d098873, 0x4b4ac297a754, 0x2606dc0fe4cd, 0x1f649db118c3, 0x5123ad6eac34, 0x7d5438f2f110, 0x4f34fa0c1b46,
    0x2b2960d2a78f, 0x602407f3dd4b, 0x564c5a8db26c, 0x36224062feeb, 0x2677210b80ff, 0x43721d4eeb5, 0x7a0b65ba9c41, 0x460b94f4e38d,
    0xe4c976855b3, 0x150e578e43f1, 0x55971106ffa, 0x4119fbc41c5b, 0x7965a436d8c4, 0x3d0645c8b27e, 0x2c5d5c74453c, 0x2b5b08eaba54,
    0x6d6a2a5d5710, 0x5d1a3ca22e3a, 0x305e7e4d13a2, 0x534f231b6c25, 0x4c41da3823df, 0x4d505ff6088e, 0x38548fc271ea, 0x1938cdaa16e9,
    0x6831b1c72f29, 0x682f82395da6, 0x7610ad772b84, 0x7732ff01d084, 0x2236d77f4602, 0x1935364db15a, 0x1203d2bbcfe0, 0x4a6af1e54b06,
    0x167962d8305f, 0x155f088f4f1c, 0x62452c3576b5, 0x137cc3188db9, 0x3032b327f03b, 0x29692ae5e943, 0x4e67ce1190b9]⟩
private theorem g13_47_ok : g13_47.OK L13 := gate_of_test (by decide +kernel)

private def g13_43 : Gate := ⟨43, 9, 0x35883a3ee53, #[
    0x8, 0x39a379531b8, 0x3725b03cfd, 0x44af695aae8, 0x1a014fe1aef, 0x48d1be32d3c, 0x626999ded9, 0x358d0ea7d58,
    0x7af90288ecb, 0x6ce2c70baaa, 0x2c1a1ce25bf, 0x285cadfd918, 0x1287a3adb2d, 0x305af051a7f, 0x29cc7ab6629, 0x40f0f96665d,
    0x5dd195f8e08, 0x726d811a2bf, 0x6f149f899c8, 0x6bc5364d62c, 0x71bc08738af, 0x21ad957714e, 0x23baa6d6139, 0x473840f63fa,
    0x1ac9b28f59a, 0x6647e4a3d89, 0x516206d93fe, 0x1c7ea62ee88, 0x199a7c3c0dd, 0x19b578ce54a, 0x16283d6837f, 0x36d7178525a,
    0x26fed4e850c, 0x691ce160d7e, 0x57438d1cdaa, 0x5c45027d7e9, 0x2f95c2c6b0d, 0x5ee6659184d, 0x2d31f62c49e, 0x561fca0167b,
    0x556a5bd488b, 0x4f03693b05f, 0x632a7b1670e]⟩
private theorem g13_43_ok : g13_43.OK L13 := gate_of_test (by decide +kernel)

private def g13_31 : Gate := ⟨31, 9, 0x6de2b849, #[
    0x7fffffff, 0x2d91ba1c, 0x25379a0d, 0x3f22a0b5, 0x77259829, 0x3a766429, 0x333aa934, 0x29c35f82,
    0x47ada831, 0x2a18279f, 0x527a60b9, 0x41b49fb0, 0x31392c3e, 0x64c55e15, 0x1c675f80, 0x589e2d8a,
    0x4791aa36, 0x2e63803f, 0x2a32750f, 0x49c8cf86, 0x12d821bf, 0x65e4b3a0, 0x41855f3c, 0x5b5e3182,
    0x2c39483f, 0x55ccc592, 0x66e5d284, 0x1a4ef283, 0x544fd5a0, 0x1eca560b, 0x589b470b]⟩
private theorem g13_31_ok : g13_31.OK L13 := gate_of_test (by decide +kernel)

private def g13_23 : Gate := ⟨23, 9, 0x5335f, #[
    0x7fffff, 0x7423cc, 0x3dc161, 0x743526, 0x2eda84, 0x3580dd, 0x6c9079, 0x60cd69,
    0x33a2ca, 0x3e1ca2, 0x29cf44, 0x2b0eb4, 0x22d70d, 0x222f39, 0x645387, 0x65345c,
    0x396b30, 0x39e093, 0x6bb01a, 0x2215b7, 0x764ac2, 0x68683b, 0x733c42]⟩
private theorem g13_23_ok : g13_23.OK L13 := gate_of_test (by decide +kernel)

private def g13_19 : Gate := ⟨19, 10, 0x4f50d, #[
    0x7ffff, 0x5eb1, 0x11cae, 0x59155, 0x191f8, 0xcb66, 0x4e4c5, 0x4b256,
    0x5f580, 0x14e1e, 0x47872, 0x501af, 0x16a4d, 0x1a327, 0x66d3, 0x41f89,
    0x5aa89, 0x47538, 0x8d7a]⟩
private theorem g13_19_ok : g13_19.OK L13 := gate_of_test (by decide +kernel)

private def g13_11 : Gate := ⟨11, 11, 0x23b, #[
    0x7ff, 0x6d, 0x38a, 0x22b, 0x41d, 0x68c, 0x598, 0xdc,
    0x16a, 0x728, 0x5b]⟩
private theorem g13_11_ok : g13_11.OK L13 := gate_of_test (by decide +kernel)

private def g13_7 : Gate := ⟨7, 11, 0x69, #[
    0x4, 0x36, 0x47, 0x56, 0x2d, 0x3c, 0x4d]⟩
private theorem g13_7_ok : g13_7.OK L13 := gate_of_test (by decide +kernel)

private def g13_3 : Gate := ⟨3, 12, 0x3, #[
    0x1, 0x6, 0x6]⟩
private theorem g13_3_ok : g13_3.OK L13 := gate_of_test (by decide +kernel)

private def g13_53 : Gate := ⟨53, 8, 0x12dd703303aed3, #[
    0x1fffffffffffff, 0xddbeac7b965ce, 0x1a97cfcb3eb372, 0x9ff11d5e947ef, 0x10cf275cef87bf, 0x1bb1faed16df58, 0x1bb35eebb81d5e, 0x15dae11df97fca,
    0x1bf856d7e835ed, 0x1ccba18d69efbf, 0x1c5b2b3c5bff33, 0x7edf6c3f46755, 0x1ecf6f6829dbb3, 0x1b37fe6b96e171, 0x9d9dfcb37f558, 0xb74dce77e7f0c,
    0x1b3f7eea0599f6, 0x1f1ffb39569b31, 0xafb96c37e754f, 0x15de2775a969ef, 0x5fa91cf7d772d, 0x5f7051cdbdfaf, 0x1225ffb29ebdb3, 0x1a4fef3a1e83f7,
    0x14eaa6c3f9e7ed, 0x1ebe7c3887bbb3, 0x146f693cfeabb5, 0x1fcf25bd8b5baa, 0x18470f9f5f9bbb, 0x7f0d955cb6fcf, 0x1e173dfc97df82, 0x1e537fe9139b7a,
    0x16ce283be9ebf7, 0xfbce257e969dd, 0x56bb91eebef2d, 0x1fb0da77d5e55c, 0x1aa737fe3f19b2, 0x815dfbf36df33, 0x1fb9cecbb461fc, 0x1b34fee6e4355f,
    0x1a759ffb371d0e, 0x505bdbcdf9bb7, 0xbf0dbedf955cc, 0x168f35368f99ff, 0x5ac6174cffbef, 0x5fada87f76f58, 0x7ee21d6eaa7fd, 0x775deb376f570,
    0x1a2dd7e37635f6, 0x1dceb93cc3fbc3, 0x5eae23fe5efc5, 0x1f34fcfa569d9a, 0x778d5f6ece74d]⟩
private theorem g13_53_ok : g13_53.OK L13 := gate_of_test (by decide +kernel)

private def filters13 : List Gate := [g13_13, g13_61, g13_41, g13_37, g13_59, g13_47, g13_43, g13_31, g13_23, g13_19, g13_11, g13_7, g13_3, g13_53]
private theorem gates13 (g : Gate) (h : g ∈ filters13) : g.OK L13 ∧ 512 ≤ g.p*2^vDepth g.p := by
  simp only [filters13, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨g13_13_ok, by decide +kernel⟩
  · exact ⟨g13_61_ok, by decide +kernel⟩
  · exact ⟨g13_41_ok, by decide +kernel⟩
  · exact ⟨g13_37_ok, by decide +kernel⟩
  · exact ⟨g13_59_ok, by decide +kernel⟩
  · exact ⟨g13_47_ok, by decide +kernel⟩
  · exact ⟨g13_43_ok, by decide +kernel⟩
  · exact ⟨g13_31_ok, by decide +kernel⟩
  · exact ⟨g13_23_ok, by decide +kernel⟩
  · exact ⟨g13_19_ok, by decide +kernel⟩
  · exact ⟨g13_11_ok, by decide +kernel⟩
  · exact ⟨g13_7_ok, by decide +kernel⟩
  · exact ⟨g13_3_ok, by decide +kernel⟩
  · exact ⟨g13_53_ok, by decide +kernel⟩

private def patch13_0 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x80000000000041 0x6726fc00e9162f) (.leaf 16 0x20000002040000021 0x241329f3287f2641134012c41d6e200c)) (.join (.leaf 16 0x421000a00000000402 0x10511b780f591ea610670df10bec03be24ad29e92024) (.leaf 16 0x8400000000000008400 0xa3527282bec04a8))) (.join (.join (.leaf 16 0x1008010802000401 0xc0827d0093e08fa16fc0d620bee2a19) (.leaf 16 0x401004610000001000 0xaa00a7320c126e61828153a0883271d0a9f05b301a9)) (.join (.leaf 16 0x400000001000000000 0x5182a4a09c5) (.leaf 16 0x8000084400000010000 0x22a604d718d611b310d21bfb0784)))) (.join (.join (.join (.leaf 16 0x8400004000800108001 0x17a817c90495260a01ad247f1b44) (.leaf 16 0x20802200000 0x254001e123002aa7231a162a)) (.join (.leaf 16 0x4000000000020 0xb9801a6) (.leaf 16 0x8001000000000100800 0x254c11322b531a211445))) (.join (.join (.leaf 16 0x20 0xb0e) (.leaf 16 0x4000002000060 0x208418962bb8225814a8)) (.join (.leaf 16 0x20080200082000400 0xa5f03591ae7254c21c705dd158e) (.leaf 16 0x20000020000100800 0x33b0bd4027a1b7d0d370b75))))) (.join (.join (.join (.join (.leaf 16 0x20100000800000002 0x13bb1c1a1350026b205911c8) (.leaf 16 0x401080000040000000 0x192119630661106a)) (.join (.leaf 16 0x20800000400 0x16250cda229c24a6) (.leaf 16 0x800000420 0x122e22801546))) (.join (.join (.leaf 16 0x1080010000008000 0x1e52073a02e626a5) (.leaf 16 0x200004100000 0x27931af2160f0101)) (.join (.leaf 16 0x400100000800208001 0x1e2408bb0618047e1e13125b1a301f1e) (.leaf 16 0x10000080010000000001 0x21f112dc25810c351bd6)))) (.join (.join (.join (.leaf 16 0x4000000100001 0x289a019c256e) (.leaf 16 0x200800000000 0x26ea1f99)) (.join (.leaf 16 0x20084000800000400 0x1a9a1ccd1afd24d21321) (.leaf 16 0x61080000004200040 0x200c131b1166162026a2290f0c022ad9003e21b21bf1))) (.join (.join (.leaf 16 0x110000 0x14ed220c192a) (.leaf 16 0x80000000000400 0x21851f9f)) (.join (.leaf 16 0x20080020802200400 0xe9026ba20cb0fd0259c06eb043f00bb0a60) (.leaf 16 0x20004000000000021 0x6a719061bca0179))))))
set_option maxRecDepth 4000 in
private theorem scan13_0 : Region (clearPoint L13) 0 512 :=
  checkedPatch 0 patch13_0 gates13 (by decide +kernel) (by decide +kernel)
private def patch13_512 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x8000080000004000404 0x18951e471c4f0a4315582a831eb20d6102ce) (.leaf 16 0x20008001080000020 0x12d01147016023f01cb8220510710535)) (.join (.leaf 16 0x21084002000008000 0x2f20aa52997025c29301750126408211d8d) (.leaf 16 0x1080210000100400 0x1c132a5923d11c9707381340))) (.join (.join (.leaf 16 0x40100010800000000 0x11bc118c21191add1a2628a9) (.leaf 16 0x8000000000000000003 0x2011161b0b7e0385)) (.join (.leaf 16 0x18400000200000000800 0x23fe19c40f7c0e2d21f42372145d) (.leaf 16 0x8400000010004108000 0x1d6427b20ffa10600fd10fec119a)))) (.join (.join (.join (.leaf 16 0x1000400000000001 0x13d81f54190906c2) (.leaf 16 0x10000104010000000020 0x2aa117fb21e2052a1ea226751ff2)) (.join (.leaf 16 0x8000042008000 0x1fb515ef144c11c31365) (.leaf 16 0x8020084000000000400 0xe6820e024570cac24ea))) (.join (.join (.leaf 16 0x180230040000001 0x1d8c1adb0a5a0e4125f70ec20e871e31280d) (.leaf 16 0x1000400800000000 0x261927091de81561)) (.join (.leaf 16 0x100022 0x16162854217d20ae) (.leaf 16 0x400000020004000002 0xf891eb00ee00c65038f1aa8023b))))) (.join (.join (.join (.join (.leaf 16 0x8060200000802000021 0x1c8f23e3203b1efe21771aa11a3301b22a0514d718bb08fa) (.leaf 16 0x10020000000000000000 0x27e22711185c)) (.join (.leaf 16 0x400080000842008040 0x290303410ed304420971086927f00d92) (.leaf 16 0x40080000000000000 0x1c760af924be))) (.join (.join (.leaf 16 0x800108400 0x1e41101329e604e0) (.leaf 16 0x4000080120001 0x1f0528c0236b1fcb247a18bf14e409c51096)) (.join (.leaf 16 0x4000000000400 0x1d521b3) (.leaf 16 0x802100c010000000020 0x1e9114d804d629e910070c9d1611126a)))) (.join (.join (.join (.leaf 16 0x610044008000 0x25d01eda111813ab1c251db703761015) (.leaf 16 0x8020100000000108000 0x1b6f049c209801841ff61374)) (.join (.leaf 16 0x8000000200802200000 0x8e0102503230a2c290f09da) (.leaf 16 0x8000080010040000000 0xb3f20bc1d1a1174))) (.join (.join (.leaf 16 0x802000040 0x13de22c416720e30) (.leaf 16 0x8200000018003 0x77606f10c682be229450ba82b670e680971)) (.join (.leaf 16 0x18000100200000000400 0x52004660049122e0d3d207e2165) (.leaf 16 0x10000080000002100400 0x247815cf056300651bdd182e))))))
set_option maxRecDepth 4000 in
private theorem scan13_512 : Region (clearPoint L13) 512 1024 :=
  checkedPatch 512 patch13_512 gates13 (by decide +kernel) (by decide +kernel)
private def patch13_1024 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x800100c200000100422 0xfd7160c226f0fb60c881417148127f60ce227350493) (.leaf 16 0x400000210084000000 0x1afb1eef10d6265f14141ee60e8c)) (.join (.leaf 16 0x421000200000000000 0x23412baf0ab32232) (.leaf 16 0x4400000100001 0xf710f2c00640c5f0c28))) (.join (.join (.leaf 16 0x10c00000210044000000 0x123b0cef242c18710e99012120fc24eb27cd0506) (.leaf 16 0x1000000802200001 0x7d40b8f21ce218c11202724)) (.join (.leaf 16 0x8001004400040100020 0x1fc40bcc130a16670aac15b2105109c1) (.leaf 16 0x8420100010000000001 0xc9d2b180c3625c31e8021f722ff)))) (.join (.join (.join (.leaf 16 0x1802000020 0x1c1c162b044009be128f) (.leaf 16 0xc200880000001 0x12280d490ce90a7315232c031f8b1e1d)) (.join (.leaf 16 0x8000000020004000002 0xb1a105407d22a38032e160700cd) (.leaf 16 0x400000000802000440 0x29f323cc05f816d2212201ae))) (.join (.join (.leaf 16 0x8000000000000108000 0x500128b19c0) (.leaf 16 0x801080000000000000 0x1d5908c9062b113f)) (.join (.leaf 16 0x88010040000400 0x3eb0a91097309a90d051fde) (.leaf 16 0x402000201800008042 0x24990ff20b7414a825f01a110ec00d4525b70f4c09c501ae))))) (.join (.join (.join (.join (.leaf 16 0x400000200800000021 0x1b0e010023702a09002c) (.leaf 16 0x80010002010820 0x50c1181087a2775174f28791be314a4)) (.join (.leaf 16 0x20000200840008400 0x1efa19d30281025c1cd229b5) (.leaf 16 0x8800000001000208000 0x265919c705740cf307d4271516022666))) (.join (.join (.leaf 16 0x21084200044000080 0xaf9126907460d571f20109b2ab92566288e237109eb0526) (.leaf 16 0x20000000000500021 0x1aff293b20b41cfc15af0ad6269e1036)) (.join (.leaf 16 0x80210042000000 0xeb4292301d821801730) (.leaf 16 0xc00084000804100400 0x22ac180206a12a8e2b911d3b1a5310ca03291d1a)))) (.join (.join (.join (.leaf 16 0x8001000200800000020 0x158026332c0519e2127d) (.leaf 16 0x84008802 0x24e91f872bbe149b086f24c40653075506df)) (.join (.leaf 16 0x400080000802000020 0x14931b3e28131cbe1630) (.leaf 16 0x8001000010800000440 0xd9c272c03120b7e25a12bd21bf7))) (.join (.join (.leaf 16 0x10000000001 0x15fd2b2d) (.leaf 16 0x40100000002008020 0x2aca0ffa14cc01c124cd27000f71)) (.join (.leaf 16 0x460004200000008002 0x1eb4264410810bfe029b05ea1a811f210320) (.leaf 16 0x401100410002008002 0xcca08e318dd0ef2262913af125211a2278f27310791))))))
set_option maxRecDepth 4000 in
private theorem scan13_1024 : Region (clearPoint L13) 1024 1536 :=
  checkedPatch 1024 patch13_1024 gates13 (by decide +kernel) (by decide +kernel)
private def patch13_1536 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x8000004200046000420 0x288f137f0add13aa255721370a1f1b471694) (.leaf 16 0x401008000082010002 0x22ef06b02a4727cd1f131e371d460f01022a28a6276a)) (.join (.leaf 16 0x420000000002000000 0x11c81d612662) (.leaf 16 0x420004000000008000 0x1c941e9b1a89149a))) (.join (.join (.leaf 16 0x420000000002000400 0x7771a7e29ca04f5) (.leaf 16 0x1000000800000000 0x15f80c12)) (.join (.leaf 16 0x20080200800000020 0x7f01fd92c492828289a) (.leaf 16 0xc200804000002 0x244c22bd0f260c8f137519920ace14241094)))) (.join (.join (.join (.leaf 16 0x10400080210002008000 0x17170f532653206f203f09f71d12101c) (.leaf 16 0x20100200040008060 0x1c101e41040004770d6217882959041f019a)) (.join (.leaf 16 0x10020000410100108021 0xefe0bd8088c1c1c158f296726e61b4f139912ca22ca03b5093b0afd) (.leaf 16 0x8400000200002100000 0x1fbd1388146c219527db))) (.join (.join (.leaf 16 0x20100000040000000 0x6f41cf61ab11224) (.leaf 16 0x10000000020 0x22140859)) (.join (.leaf 16 0x10000000602802000420 0x2a342711237b1d780f141cef1491115e08d6084606020ea52439) (.leaf 16 0x420008000800200001 0x26f304a6209c138125f609df030b15f3))))) (.join (.join (.join (.join (.leaf 16 0x23004000040010000 0x3c2221b215e13a0253f09fb1a230e68) (.leaf 16 0x8802 0xb0e27850c0126a41127)) (.join (.leaf 16 0x400000010848000020 0x299029bd0a2710b923e1203f13fc00b01a1b) (.leaf 16 0x400004000040000000 0x20af235a2b01))) (.join (.join (.leaf 16 0x441004010800008021 0x228a20ee021624aa165c2bd601622954211e295c) (.leaf 16 0x10001080600802000400 0x4c203150366050327a208700354273514560a1b)) (.join (.leaf 16 0x21004010000008020 0xe210cb909be03902003287b) (.leaf 16 0x8420080400042008021 0x21e5004f2bce05901a7112522b4917dd000d0f392405)))) (.join (.join (.join (.leaf 16 0x800000001000100800 0x118d1166154c072a15ee16b50631) (.leaf 16 0x80000800000000 0x1ebd1247)) (.join (.leaf 16 0x8001000410084108002 0x211f24a60bd405bc0d2216520121079f00f80f2a1a5c06a1044e) (.leaf 16 0x80000000000840 0x2c0f040402a123fc050f))) (.join (.join (.leaf 16 0x400000200800000000 0x1d3a19a81f5e) (.leaf 16 0x8440000200882000400 0x18d311b61b9312a20ebf2c490e2d044b04792acd)) (.join (.leaf 16 0x8000000210000100000 0x8eb0dd1218b1a2d) (.leaf 16 0x8c00000000000108400 0x2c156f13f80d9228a8042b1086))))))
set_option maxRecDepth 4000 in
private theorem scan13_1536 : Region (clearPoint L13) 1536 2048 :=
  checkedPatch 1536 patch13_1536 gates13 (by decide +kernel) (by decide +kernel)
private def patch13_2048 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x80210802000400 0x14390dae12d3239d14810395) (.leaf 16 0x421004010800300420 0x97f0e3c1626255415e91e172b00093d02e111ff14fb)) (.join (.leaf 16 0x1010010000000020 0x11f9279d1900071006e92b4a0ed1) (.leaf 16 0x8022000200000008401 0x2b8820611fc712e00bfc23fc27af0b7d))) (.join (.join (.leaf 16 0x80000000000020 0x246b277f) (.leaf 16 0x8060000600800000000 0x16a22b8b257c16672a5c18950bbc0fd0)) (.join (.leaf 16 0x10800018042 0x28f22051ba912c40cbb2c46243327460221) (.leaf 16 0x40000010002100c00 0x23141c1211e6298108b3263208290356)))) (.join (.join (.join (.leaf 16 0x21000000802008000 0xaee0f50056213c500d3) (.leaf 16 0x804080200000000001 0xe4703af224c1ab317a20703035f0be92bc9)) (.join (.leaf 16 0xc21000020000000040 0x240e1a7200ef22e515e41cc60c111fc90b36) (.leaf 16 0x10800000021 0x11fa269306cb2468))) (.join (.join (.leaf 16 0x10001004010000008400 0x25162383153506840a7310d926f8) (.leaf 16 0x400000010800100421 0x29590169210e0fe5169f0dff239a)) (.join (.leaf 16 0x8000000010044000020 0x199d0042116c2577159c0a31) (.leaf 16 0x400104400040010000 0x30b27410562023d2bbb208f26d1032e01e2))))) (.join (.join (.join (.join (.leaf 16 0x8c00100000000108401 0x122723ba2209162711bd106623b41dd30eef0f2a) (.leaf 16 0x8001000200000008000 0x1b80135214711633)) (.join (.leaf 16 0x821000000002000041 0x14171280294f28e719b12385223b260b) (.leaf 16 0x10002300400 0x19c422160e21046303a3235c))) (.join (.join (.leaf 16 0x800008022 0x14fb0b8008a515df0c2c) (.leaf 16 0x800000200840008001 0x1b100005021e1cb62b0c154f0a79)) (.join (.leaf 16 0x80000000100400 0x77617752c15) (.leaf 16 0x400002100000 0x297a2107001b1874)))) (.join (.join (.join (.leaf 16 0x210040000400 0x8140ee71d5116ae) (.leaf 16 0x21000000000000021 0x83026f404e12b6e)) (.join (.leaf 16 0x8020000200040000020 0x15807ca035f1eaa1fab) (.leaf 16 0x8001000200880000400 0x18c5248301b229040f440c4f1a26))) (.join (.join (.leaf 16 0x108000000a100020 0x3db17b32990242e1f3c08cf00fd298d181c) (.leaf 16 0x1000200000 0x29a817532be415da)) (.join (.leaf 16 0xc00080010042000c00 0x20501df307510f8c240a045b193c246208690406) (.leaf 16 0x420000420000000441 0xacc0e471ddf124e09b500b913212a0506b80564))))))
set_option maxRecDepth 4000 in
private theorem scan13_2048 : Region (clearPoint L13) 2048 2560 :=
  checkedPatch 2048 patch13_2048 gates13 (by decide +kernel) (by decide +kernel)
private def patch13_2560 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x20004000800008000 0x187711fc199c0a76) (.leaf 16 0x1000610000008000 0x1fed2bfa108d049f0da227ac)) (.join (.leaf 16 0x80000040200421 0x1f97186f21970a28131909c41548) (.leaf 16 0x1000000001 0x14a8033a0cd3))) (.join (.join (.leaf 16 0x200000042008000 0x2873222d0fc4079723751b190149) (.leaf 16 0x400104001000008800 0x22b81b4f0fa127c52bc121650ae01d771ade)) (.join (.leaf 16 0x10400000020000000000 0x16360f3403b7196e15d5) (.leaf 16 0x402000000802000001 0x13062ad41d5f122a03e81ac8)))) (.join (.join (.join (.leaf 16 0x41004200000000400 0x226f06c70b0726bc03e1167c) (.leaf 16 0x8020084210080100440 0x164b025406ea0e3c0e8c0ea303a002e0047f281113f10554)) (.join (.leaf 16 0x80450082000001 0x1e192c21203f2b3923c9152f00d00064289a09e018080a3d) (.leaf 16 0x104200002000001 0x8bf03df1fcf0dfe20b008e2))) (.join (.join (.leaf 16 0x4000000018000 0x18311bd416df0338) (.leaf 16 0x8040000400082018000 0x17dd25ef2253190f0efe239207392b24234810d80b0f)) (.join (.leaf 16 0x40000c000800100020 0x24471e770d9c0b6513c124050463) (.leaf 16 0x2088200000000000 0x19d515d004110a0a07842354))))) (.join (.join (.join (.join (.leaf 16 0x420000210000000401 0x1d950e19125e07480ecb0572) (.leaf 16 0x400000010000100000 0x14d1272609da)) (.join (.leaf 16 0x1004210000010420 0x28df13072ba52af02bd523bc07fe0b4d) (.leaf 16 0x8000080010000008000 0x14352032002c1e04))) (.join (.join (.leaf 16 0x20004020002008400 0x1d9f234d24da0364009416f81631) (.leaf 16 0x10001080000842000000 0x586034012f722d113ca204d0f3c)) (.join (.leaf 16 0x8800000010002008400 0x16e10b3800cd2a020b5402e021bf) (.leaf 16 0x400004000000000020 0x5090e0228f1)))) (.join (.join (.join (.leaf 16 0x18000000000040000040 0x29841fc41d391c3c21891f0c) (.leaf 16 0x1080000000000002 0x1c18206b189415cb)) (.join (.leaf 16 0x80000002000400 0x71013f108b3) (.leaf 16 0x8001008000840008020 0x3b01fa09c5081815f713690d69005e))) (.join (.join (.leaf 16 0x420000000042000021 0x20c61f4a1ed301cf0a2c2813) (.leaf 16 0x2088200040000400 0x2739157218f70ad301cd28321c2c1d1a)) (.join (.leaf 16 0x8000000010001 0x1eda0d15178f09f11ca0) (.leaf 16 0x10041000200082000801 0x2069059e1b03150f036522581b8b07b51576112f0cda0e75))))))
set_option maxRecDepth 4000 in
private theorem scan13_2560 : Region (clearPoint L13) 2560 3072 :=
  checkedPatch 2560 patch13_2560 gates13 (by decide +kernel) (by decide +kernel)
private def patch13_3072 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x401084010000100400 0x25be112522132c3f01fa205f16f9) (.leaf 16 0x10400080400800210000 0x24ac180b02c40fe71de41d0006d710cf02082b6c18bf)) (.join (.leaf 16 0x424104200080100020 0x7ba032727f7263f21981d20281800a3245d24d9151607d315c60ca5) (.leaf 16 0x1080001000100000 0x22922bf913e509800db2))) (.join (.join (.leaf 16 0x40000010000000400 0x23f50bda06240fde) (.leaf 16 0x1004010002000400 0xd61249326122b0c0d06)) (.join (.leaf 16 0x20040100020 0xdb80d1c130516be09c1) (.leaf 16 0x42004000000100000 0x1c27066b22f91f7e27071ee3)))) (.join (.join (.join (.leaf 16 0x400002000020 0x289c13db25a611c1) (.leaf 16 0x40004000802000000 0x21a40ff81ecd0ac3057d)) (.join (.leaf 16 0x440100000800000080 0x1f5269f24712b59012611ed1dde1382105a08f0) (.leaf 16 0x1080010080000000 0xa7c236b15c122d8163a))) (.join (.join (.leaf 16 0x20 0x1f51) (.leaf 16 0x800000200040008000 0x296400de0e84298319e7)) (.join (.leaf 16 0x420004000002000002 0x10bb0a531cf528eb12190af9) (.leaf 16 0x1080000000100400 0x70225ff081d02ef))))) (.join (.join (.join (.join (.leaf 16 0x20008601040000000 0x197c23f5237a2a0525a30fdf2a820ad50a09) (.leaf 16 0x820100000040000400 0x17ff087729641f2b0c2c2aaf2a4f)) (.join (.leaf 16 0x8021000000040000400 0x83d29dd049518e12242) (.leaf 16 0x8420084200080000400 0x1790cc00c4c16d721f100132a40265314b8))) (.join (.join (.leaf 16 0x8004100200000000000 0xe03206f15bc11030f65286708da043f) (.leaf 16 0x1000000000000000800 0xc8c0b3c07cd0181220914ef)) (.join (.leaf 16 0x10000000400000010020 0x20cb08c62480067d190c11801ca8) (.leaf 16 0x801000200000008400 0x294b1b6e10e11e26010d12a9)))) (.join (.join (.join (.leaf 16 0x1084000000008000 0xe191bb3097a0b4f) (.leaf 16 0x10020000200144000020 0x15fe0ef60eb10e6325cc23bd1f331706119c27f616231168)) (.join (.leaf 16 0x10000000000 0x1ff6) (.leaf 16 0x8000180000000000000 0x129623dd1a9203f8))) (.join (.join (.leaf 16 0x1400000200002100000 0x23af21d212f30c8d0a1a0824130b071b) (.leaf 16 0x8400000000840008c00 0x286c1b76068a2a100e7e24c11c1207f9)) (.join (.leaf 16 0x21000000002000061 0x4ba13ce022a1e20113301a915b7) (.leaf 16 0x8000000010000408000 0x590049e2b0910d30f100ea82a83))))))
set_option maxRecDepth 4000 in
private theorem scan13_3072 : Region (clearPoint L13) 3072 3584 :=
  checkedPatch 3072 patch13_3072 gates13 (by decide +kernel) (by decide +kernel)
private def patch13_3584 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x8400000000080000000 0x39d104e1e1706a1) (.leaf 16 0x20080010040100000 0x290800d1111118181b14)) (.join (.leaf 16 0x8020004000800108001 0x2333167921f825a301d3215e0c1f) (.leaf 16 0x400080400040008800 0x1354129718c40be61cba1229264208b0))) (.join (.join (.leaf 16 0x108c210000100420 0xb4328672b062a4f11c920e203020a901e071bc7) (.leaf 16 0x20000001000000000 0x52d0d130218)) (.join (.leaf 16 0x200002000001 0x26f903ca0520) (.leaf 16 0x1080000000100000 0x2b2f17aa15b2)))) (.join (.join (.join (.leaf 16 0x4200000000400 0xd6a002f2c0d) (.leaf 16 0x8000084000000100020 0x12f119b52bad1689075f)) (.join (.leaf 16 0x4001802000000 0x127d27c414cf06742674) (.leaf 16 0x2080201000000040 0x1eda011e0b9d109a09c4002828071a5d))) (.join (.join (.leaf 16 0x10000000000084000020 0x2522223029d704d822911dc21cc2) (.leaf 16 0x8000104030004008020 0x18122b340df4061305da034300e62ad3109f01860515)) (.join (.leaf 16 0x88200004000400 0x119a295c198b155b269a21d50843) (.leaf 16 0x10000000000000100c01 0x27e02111037827981eb30e752678))))) (.join (.join (.join (.join (.leaf 16 0x400000010002100421 0x146915ad22eb173b0b7e27c71f4a) (.leaf 16 0x2000400000100020 0xceb0c9d271c0f772a801e16)) (.join (.leaf 16 0x400084200000000001 0xe5f219824cc1c8200ec) (.leaf 16 0x40004200840008040 0x1a1708720a9c198f2a43274b118e26200d82))) (.join (.join (.leaf 16 0x21000010040000040 0x53e167508251e8910de0a6a) (.leaf 16 0x800000000000000401 0x2c0f01a601790415)) (.join (.leaf 16 0x210000000040 0x2a1814a40c1f087b) (.leaf 16 0x21080000802000000 0xa5a0e38211b202f0975)))) (.join (.join (.join (.leaf 16 0x420000000000010000 0x288d1320058d035f) (.leaf 16 0x3000000000000420 0x244515a8024c1d212110)) (.join (.leaf 16 0x8001000600800000000 0x2468062b0aed064f053c2846) (.leaf 16 0x402088000000008400 0x1b770d3d012a0a5520f70f151604074f))) (.join (.join (.leaf 16 0x10002000040 0x1e2b1b2c08bd0550) (.leaf 16 0x8020080000000000400 0x16bd11a116590573)) (.join (.leaf 16 0x8400000210040100001 0xec206802c4b20e01b680add0d3a) (.leaf 16 0x4080000000000001 0x2a9614af11c104f501580444))))))
set_option maxRecDepth 4000 in
private theorem scan13_3584 : Region (clearPoint L13) 3584 4096 :=
  checkedPatch 3584 patch13_3584 gates13 (by decide +kernel) (by decide +kernel)
private def patch13_4096 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x4200800008000 0x12d30fe9023224da) (.leaf 16 0x886000401 0x249f1882124319180bf508cf052d0f77)) (.join (.leaf 16 0x8461000010000100400 0x193225ff1fb414e003e0116a01d00dcf13c7) (.leaf 16 0x4410000000001 0x64926d40d22161d15a3))) (.join (.join (.leaf 16 0x200000008420 0x1fe4285707730dad) (.leaf 16 0x10020100010082300000 0x229b0600118d05c601be0dc32af01f5c16ea1bd110160e56)) (.join (.leaf 16 0x8000002108001 0xf820ad62b5319582c3000cb) (.leaf 16 0x8001008020802000401 0x99828962a931ba8295f0f911eba067001c90c10)))) (.join (.join (.join (.leaf 16 0x20000000040010420 0x221f0d9e0d4a0b1919941183) (.leaf 16 0x18400000000002000000 0x260522ff0fb81b5a2148)) (.join (.leaf 16 0x420000000800008000 0x971142227e726e1) (.leaf 16 0x8800004000800008800 0x117317151268169f01de1b781afb0149))) (.join (.join (.leaf 16 0x80000200100100000 0x286c119b0e950d91090121230f590a3c0347159e) (.leaf 16 0x4400000000000 0x1a1610070b7e)) (.join (.leaf 16 0x8000000000000308420 0x29dc21f21b40005e16320f2e1109) (.leaf 16 0x20004200000010001 0x207421f521fa1958154f0d9d))))) (.join (.join (.join (.join (.leaf 16 0x800084000800000020 0x1dc20f520ba7115b1fd1255c) (.leaf 16 0x100010000108000 0x1fd9165a08711acc2787)) (.join (.leaf 16 0x2000000800000000 0x1dc21aea2267) (.leaf 16 0x1000020002000400 0x65f1f371915035601a3))) (.join (.join (.leaf 16 0x801 0x2963003d22f2) (.leaf 16 0x2000211000000022 0x1eb50b8609c7159926ea010c148f235d01f3)) (.join (.leaf 16 0x400002000000 0x119f114d1747) (.leaf 16 0x6008041 0x227f16bb05ec01f517870f7c0dc5)))) (.join (.join (.join (.leaf 16 0x40100020 0xb8322461b6e) (.leaf 16 0x401000010840010020 0x1d802a10143b039013ea29380d641206)) (.join (.leaf 16 0x820000221000101000 0x2bed255a1d5123250cce099b1a7b08f8170f13400f4c0d2a05cf) (.leaf 16 0x8001000000000000001 0x2a2526902666))) (.join (.join (.leaf 16 0x1004000800008000 0xca9150905252ba0) (.leaf 16 0x10400004000004100000 0x108608881d0b28fc237b0ede05ce)) (.join (.leaf 16 0x2080020000008000 0x1d7415940eaf0a98073e1270) (.leaf 16 0x1080000080008440 0x69a2a56120e063408592aef1e390078))))))
set_option maxRecDepth 4000 in
private theorem scan13_4096 : Region (clearPoint L13) 4096 4608 :=
  checkedPatch 4096 patch13_4096 gates13 (by decide +kernel) (by decide +kernel)
private def patch13_4608 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x80000040108001 0x1939257707af175e0825) (.leaf 16 0x18403080000880000400 0x223915e5140e0e1f18e8161f06f813e928940d4b0a9d0ea0)) (.join (.leaf 16 0x40000000 0x1637) (.leaf 16 0x8400000211000000400 0x2b7420d100a510752788251812b3))) (.join (.join (.leaf 16 0x420004200040000020 0x24fc12231d3311e41b681ad5) (.leaf 16 0x403084200002000000 0x108e11ff0fc80ed12bc1189622c30c7c)) (.join (.leaf 16 0x20100030000000000 0x1521228114a2830210a0613) (.leaf 16 0x20000200002000002 0x1e9b16e802a91d59162e)))) (.join (.join (.join (.leaf 16 0x10400084000884000003 0x16f30de113c71f6c08fa2bc5257e00d10895020f227e158f0229) (.leaf 16 0x180200800000400 0x2ba5096702f511701eb02bfc)) (.join (.leaf 16 0x8401000000040008060 0x1414233d24aa146f2b4226711ce71069) (.leaf 16 0x1004200002000001 0x1ff1295e091d111205fc))) (.join (.join (.leaf 16 0x13002000000 0x18bb29b71bcd188b030702cc0160177e) (.leaf 16 0x8020004000000010020 0x7721d110b3c2b9f2b2a26c3)) (.join (.leaf 16 0x8400000220840010000 0x1a5021be2b131ab90aba231c07160a9a0256) (.leaf 16 0x2000400 0x21e82bdf))))) (.join (.join (.join (.join (.leaf 16 0x3000200000200000 0x2bca247311ec0b38172d0cee) (.leaf 16 0x108001 0x158a0fec079f)) (.join (.leaf 16 0x20000000002000020 0x2a14152b13c7) (.leaf 16 0x400000000802000000 0xfae04b2001b))) (.join (.join (.leaf 16 0x1080200000010400 0x272519de0acc2afd06282927) (.leaf 16 0x10000004000800000002 0x205818ea101620f5100e055e)) (.join (.leaf 16 0x8402000200002100060 0xcc101140859026f28b20e011e1d27f11e711a89) (.leaf 16 0x800000000080000000 0x1b5b197e0b72096a)))) (.join (.join (.join (.leaf 16 0x8400004200802000820 0x2ad809c4284903f6217c1b6224581a09193c) (.leaf 16 0x8040004001080008020 0x14b122ca08aa020627cb022a193701182a6225b1)) (.join (.leaf 16 0x841084010000000001 0x18770d9418e7019b01481df9291015850728) (.leaf 16 0x20088200800000000 0xb661a532218202a1a3a2341))) (.join (.join (.leaf 16 0x8000004200000000000 0x2051c49089b) (.leaf 16 0x4000200840000000 0x2a71260825b71acc04a827d208e9)) (.join (.leaf 16 0x84000802200020 0xeae1430017902e916041013108d) (.leaf 16 0x104000000008c00 0x27f6144f065f07de258f0e6d0c00))))))
set_option maxRecDepth 4000 in
private theorem scan13_4608 : Region (clearPoint L13) 4608 5120 :=
  checkedPatch 4608 patch13_4608 gates13 (by decide +kernel) (by decide +kernel)
private def patch13_5120 : Patch :=
  (.join (.join (.join (.join (.join (.leaf 16 0x441004410000010000 0x1d092922009c0e0c02100fd90c6127c21c8e010d) (.leaf 16 0x40004000800100020 0x14bc01d31abf28b50dc92882)) (.join (.leaf 16 0x20088000040008000 0xbb710e61c040c6e07f4213b) (.leaf 16 0x10001004610002000801 0x2b3d280a15800e3a1f70197f0bea29ab26901c8a0aeb0515))) (.join (.join (.leaf 16 0x401000020002100021 0x7b81aaf176c10e22bcf100306b61461) (.leaf 16 0x400000000040000400 0x6c28ff0a0e)) (.join (.leaf 16 0x800200400000000041 0x13210ba813490fa0095c085325e1075a2a8423b50377) (.leaf 16 0x20000000800008000 0xf2e1e9d0db6)))) (.join (.join (.join (.leaf 16 0x10000008000040008021 0x1add0e6c20031bc2206224b613541582) (.leaf 16 0x42010000 0x95911991d150931)) (.join (.leaf 16 0x20000010000200020 0x14b423c624bf1f8d17a2) (.leaf 16 0x1100000086100020 0xe02c0a00de206f09132a6f115507bc0fda1d8d))) (.join (.join (.leaf 16 0x8000 0x206f) (.leaf 16 0x800080000800000022 0x163d0839128f106a1a171cad157b)) (.join (.leaf 16 0x420000000000000402 0xe2504191bae1f6119d6) (.leaf 16 0x1080020000000000 0xfdd16c9248f0b36))))) (.join (.join (.join (.join (.leaf 16 0x20080200802100040 0x25991304220b2803174216c9202d1eb3) (.leaf 16 0x40000000000100020 0x16d3005c1d981ec5)) (.join (.leaf 16 0x200002208400 0xd0719f40e8200480cc711b3) (.leaf 16 0x420000000002100401 0x166715f82a91064906e90717))) (.join (.join (.leaf 16 0x8c200000000060 0x280b2ba019e1024a1d6e2ad929300c9d) (.leaf 16 0x1000000840000401 0x1bfe271526032a4f142f)) (.join (.leaf 16 0x8020088000000208000 0xf96026f002b2b310e86157608f821f3) (.leaf 16 0x800108440 0x1d60296f0f9a05cd270e1643)))) (.join (.join (.join (.leaf 16 0x800000c0000000 0x26b22ae2179178f) (.leaf 16 0x180001000100420 0x259313c91073267e119c1a3328401d0c)) (.join (.leaf 16 0x1004000040108000 0x118020900b81162e1196) (.leaf 16 0x8c00000000002010800 0x11ba198b16a6002e1f7b192a13d51bef07cd))) (.join (.join (.leaf 16 0x420080000840000000 0x1153039e256a293e07e0) (.leaf 16 0x400000000000300000 0x16b626bf0509009b)) (.join (.leaf 16 0x1000200000000000 0x254808b4) (.leaf 16 0x8400180040800000040 0x10a413be28a91b88035923681d7b1571073029f3298606d7))))))
set_option maxRecDepth 4000 in
private theorem scan13_5120 : Region (clearPoint L13) 5120 5632 :=
  checkedPatch 5120 patch13_5120 gates13 (by decide +kernel) (by decide +kernel)
private def patch13_5632 : Patch :=
  (.join (.join (.leaf 16 0x8060000000000200000 0xc291f4017470c3109ce0767) (.leaf 16 0x1004000040000800 0x24fb06030cf20e8d0676)) (.join (.leaf 16 0x400000002000000000 0x26ba1ce81c641b2c0af9) (.join (.leaf 16 0x21000002000000020 0x114e137329c3281027e2013d24b5) (.leaf 1 0x0 0x0))))
set_option maxRecDepth 4000 in
private theorem scan13_5632 : Region (clearPoint L13) 5632 5697 :=
  checkedPatch 5632 patch13_5632 gates13 (by decide +kernel) (by decide +kernel)
private theorem rows13 : Region (clearPoint L13) 0 5697 :=
  (mergeRegion (mergeRegion (mergeRegion scan13_0 (mergeRegion scan13_512 scan13_1024)) (mergeRegion scan13_1536 (mergeRegion scan13_2048 scan13_2560))) (mergeRegion (mergeRegion scan13_3072 (mergeRegion scan13_3584 scan13_4096)) (mergeRegion scan13_4608 (mergeRegion scan13_5120 scan13_5632))))
private theorem clear13 : Clear L13 := clear_of_scan (by decide +kernel) (rows13)

private def entries6577 : List Entry := [
  ⟨66286287192, L0, 0⟩,
  ⟨116742003219, L0, 3⟩,
  ⟨167758818814, L0, 2⟩,
  ⟨218214534841, L0, 1⟩]

private theorem root6577_0 : Block (rootTest 6577 entries6577) 0 128 := checkedBlock (by decide +kernel)
private theorem root6577_128 : Block (rootTest 6577 entries6577) 128 256 := checkedBlock (by decide +kernel)
private theorem root6577_256 : Block (rootTest 6577 entries6577) 256 384 := checkedBlock (by decide +kernel)
private theorem root6577_384 : Block (rootTest 6577 entries6577) 384 512 := checkedBlock (by decide +kernel)
private theorem root6577_512 : Block (rootTest 6577 entries6577) 512 640 := checkedBlock (by decide +kernel)
private theorem root6577_640 : Block (rootTest 6577 entries6577) 640 768 := checkedBlock (by decide +kernel)
private theorem root6577_768 : Block (rootTest 6577 entries6577) 768 896 := checkedBlock (by decide +kernel)
private theorem root6577_896 : Block (rootTest 6577 entries6577) 896 1024 := checkedBlock (by decide +kernel)
private theorem root6577_1024 : Block (rootTest 6577 entries6577) 1024 1152 := checkedBlock (by decide +kernel)
private theorem root6577_1152 : Block (rootTest 6577 entries6577) 1152 1280 := checkedBlock (by decide +kernel)
private theorem root6577_1280 : Block (rootTest 6577 entries6577) 1280 1408 := checkedBlock (by decide +kernel)
private theorem root6577_1408 : Block (rootTest 6577 entries6577) 1408 1536 := checkedBlock (by decide +kernel)
private theorem root6577_1536 : Block (rootTest 6577 entries6577) 1536 1664 := checkedBlock (by decide +kernel)
private theorem root6577_1664 : Block (rootTest 6577 entries6577) 1664 1792 := checkedBlock (by decide +kernel)
private theorem root6577_1792 : Block (rootTest 6577 entries6577) 1792 1920 := checkedBlock (by decide +kernel)
private theorem root6577_1920 : Block (rootTest 6577 entries6577) 1920 2048 := checkedBlock (by decide +kernel)
private theorem root6577_2048 : Block (rootTest 6577 entries6577) 2048 2176 := checkedBlock (by decide +kernel)
private theorem root6577_2176 : Block (rootTest 6577 entries6577) 2176 2304 := checkedBlock (by decide +kernel)
private theorem root6577_2304 : Block (rootTest 6577 entries6577) 2304 2432 := checkedBlock (by decide +kernel)
private theorem root6577_2432 : Block (rootTest 6577 entries6577) 2432 2560 := checkedBlock (by decide +kernel)
private theorem root6577_2560 : Block (rootTest 6577 entries6577) 2560 2688 := checkedBlock (by decide +kernel)
private theorem root6577_2688 : Block (rootTest 6577 entries6577) 2688 2816 := checkedBlock (by decide +kernel)
private theorem root6577_2816 : Block (rootTest 6577 entries6577) 2816 2944 := checkedBlock (by decide +kernel)
private theorem root6577_2944 : Block (rootTest 6577 entries6577) 2944 3072 := checkedBlock (by decide +kernel)
private theorem root6577_3072 : Block (rootTest 6577 entries6577) 3072 3200 := checkedBlock (by decide +kernel)
private theorem root6577_3200 : Block (rootTest 6577 entries6577) 3200 3328 := checkedBlock (by decide +kernel)
private theorem root6577_3328 : Block (rootTest 6577 entries6577) 3328 3456 := checkedBlock (by decide +kernel)
private theorem root6577_3456 : Block (rootTest 6577 entries6577) 3456 3584 := checkedBlock (by decide +kernel)
private theorem root6577_3584 : Block (rootTest 6577 entries6577) 3584 3712 := checkedBlock (by decide +kernel)
private theorem root6577_3712 : Block (rootTest 6577 entries6577) 3712 3840 := checkedBlock (by decide +kernel)
private theorem root6577_3840 : Block (rootTest 6577 entries6577) 3840 3968 := checkedBlock (by decide +kernel)
private theorem root6577_3968 : Block (rootTest 6577 entries6577) 3968 4096 := checkedBlock (by decide +kernel)
private theorem root6577_4096 : Block (rootTest 6577 entries6577) 4096 4224 := checkedBlock (by decide +kernel)
private theorem root6577_4224 : Block (rootTest 6577 entries6577) 4224 4352 := checkedBlock (by decide +kernel)
private theorem root6577_4352 : Block (rootTest 6577 entries6577) 4352 4480 := checkedBlock (by decide +kernel)
private theorem root6577_4480 : Block (rootTest 6577 entries6577) 4480 4608 := checkedBlock (by decide +kernel)
private theorem root6577_4608 : Block (rootTest 6577 entries6577) 4608 4736 := checkedBlock (by decide +kernel)
private theorem root6577_4736 : Block (rootTest 6577 entries6577) 4736 4864 := checkedBlock (by decide +kernel)
private theorem root6577_4864 : Block (rootTest 6577 entries6577) 4864 4992 := checkedBlock (by decide +kernel)
private theorem root6577_4992 : Block (rootTest 6577 entries6577) 4992 5120 := checkedBlock (by decide +kernel)
private theorem root6577_5120 : Block (rootTest 6577 entries6577) 5120 5248 := checkedBlock (by decide +kernel)
private theorem root6577_5248 : Block (rootTest 6577 entries6577) 5248 5376 := checkedBlock (by decide +kernel)
private theorem root6577_5376 : Block (rootTest 6577 entries6577) 5376 5504 := checkedBlock (by decide +kernel)
private theorem root6577_5504 : Block (rootTest 6577 entries6577) 5504 5632 := checkedBlock (by decide +kernel)
private theorem root6577_5632 : Block (rootTest 6577 entries6577) 5632 5760 := checkedBlock (by decide +kernel)
private theorem root6577_5760 : Block (rootTest 6577 entries6577) 5760 5888 := checkedBlock (by decide +kernel)
private theorem root6577_5888 : Block (rootTest 6577 entries6577) 5888 6016 := checkedBlock (by decide +kernel)
private theorem root6577_6016 : Block (rootTest 6577 entries6577) 6016 6144 := checkedBlock (by decide +kernel)
private theorem root6577_6144 : Block (rootTest 6577 entries6577) 6144 6272 := checkedBlock (by decide +kernel)
private theorem root6577_6272 : Block (rootTest 6577 entries6577) 6272 6400 := checkedBlock (by decide +kernel)
private theorem root6577_6400 : Block (rootTest 6577 entries6577) 6400 6528 := checkedBlock (by decide +kernel)
private theorem root6577_6528 : Block (rootTest 6577 entries6577) 6528 6577 := checkedBlock (by decide +kernel)
private theorem covered6577 : Covers 6577 entries6577 := covers_of_test
  (joinBlock (joinBlock (joinBlock (joinBlock (joinBlock root6577_0 (joinBlock root6577_128 root6577_256)) (joinBlock root6577_384 (joinBlock root6577_512 root6577_640))) (joinBlock (joinBlock root6577_768 (joinBlock root6577_896 root6577_1024)) (joinBlock (joinBlock root6577_1152 root6577_1280) (joinBlock root6577_1408 root6577_1536)))) (joinBlock (joinBlock (joinBlock root6577_1664 (joinBlock root6577_1792 root6577_1920)) (joinBlock root6577_2048 (joinBlock root6577_2176 root6577_2304))) (joinBlock (joinBlock root6577_2432 (joinBlock root6577_2560 root6577_2688)) (joinBlock (joinBlock root6577_2816 root6577_2944) (joinBlock root6577_3072 root6577_3200))))) (joinBlock (joinBlock (joinBlock (joinBlock root6577_3328 (joinBlock root6577_3456 root6577_3584)) (joinBlock root6577_3712 (joinBlock root6577_3840 root6577_3968))) (joinBlock (joinBlock root6577_4096 (joinBlock root6577_4224 root6577_4352)) (joinBlock (joinBlock root6577_4480 root6577_4608) (joinBlock root6577_4736 root6577_4864)))) (joinBlock (joinBlock (joinBlock root6577_4992 (joinBlock root6577_5120 root6577_5248)) (joinBlock root6577_5376 (joinBlock root6577_5504 root6577_5632))) (joinBlock (joinBlock root6577_5760 (joinBlock root6577_5888 root6577_6016)) (joinBlock (joinBlock root6577_6144 root6577_6272) (joinBlock root6577_6400 root6577_6528))))))
private theorem entriesOK6577 : ∀ e ∈ entries6577, e.OK 6577 := by decide +kernel
private theorem cleared6577 (e : Entry) (h : e ∈ entries6577) : Clear e.chart := by
  simp only [entries6577, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact clear0
  · exact clear0
  · exact clear0
  · exact clear0

private def entries4721 : List Entry := [
  ⟨1907040398, L1, 0⟩,
  ⟨16109545607, L1, 2⟩,
  ⟨89111351754, L1, 3⟩,
  ⟨103313856963, L1, 1⟩]

private theorem root4721_0 : Block (rootTest 4721 entries4721) 0 128 := checkedBlock (by decide +kernel)
private theorem root4721_128 : Block (rootTest 4721 entries4721) 128 256 := checkedBlock (by decide +kernel)
private theorem root4721_256 : Block (rootTest 4721 entries4721) 256 384 := checkedBlock (by decide +kernel)
private theorem root4721_384 : Block (rootTest 4721 entries4721) 384 512 := checkedBlock (by decide +kernel)
private theorem root4721_512 : Block (rootTest 4721 entries4721) 512 640 := checkedBlock (by decide +kernel)
private theorem root4721_640 : Block (rootTest 4721 entries4721) 640 768 := checkedBlock (by decide +kernel)
private theorem root4721_768 : Block (rootTest 4721 entries4721) 768 896 := checkedBlock (by decide +kernel)
private theorem root4721_896 : Block (rootTest 4721 entries4721) 896 1024 := checkedBlock (by decide +kernel)
private theorem root4721_1024 : Block (rootTest 4721 entries4721) 1024 1152 := checkedBlock (by decide +kernel)
private theorem root4721_1152 : Block (rootTest 4721 entries4721) 1152 1280 := checkedBlock (by decide +kernel)
private theorem root4721_1280 : Block (rootTest 4721 entries4721) 1280 1408 := checkedBlock (by decide +kernel)
private theorem root4721_1408 : Block (rootTest 4721 entries4721) 1408 1536 := checkedBlock (by decide +kernel)
private theorem root4721_1536 : Block (rootTest 4721 entries4721) 1536 1664 := checkedBlock (by decide +kernel)
private theorem root4721_1664 : Block (rootTest 4721 entries4721) 1664 1792 := checkedBlock (by decide +kernel)
private theorem root4721_1792 : Block (rootTest 4721 entries4721) 1792 1920 := checkedBlock (by decide +kernel)
private theorem root4721_1920 : Block (rootTest 4721 entries4721) 1920 2048 := checkedBlock (by decide +kernel)
private theorem root4721_2048 : Block (rootTest 4721 entries4721) 2048 2176 := checkedBlock (by decide +kernel)
private theorem root4721_2176 : Block (rootTest 4721 entries4721) 2176 2304 := checkedBlock (by decide +kernel)
private theorem root4721_2304 : Block (rootTest 4721 entries4721) 2304 2432 := checkedBlock (by decide +kernel)
private theorem root4721_2432 : Block (rootTest 4721 entries4721) 2432 2560 := checkedBlock (by decide +kernel)
private theorem root4721_2560 : Block (rootTest 4721 entries4721) 2560 2688 := checkedBlock (by decide +kernel)
private theorem root4721_2688 : Block (rootTest 4721 entries4721) 2688 2816 := checkedBlock (by decide +kernel)
private theorem root4721_2816 : Block (rootTest 4721 entries4721) 2816 2944 := checkedBlock (by decide +kernel)
private theorem root4721_2944 : Block (rootTest 4721 entries4721) 2944 3072 := checkedBlock (by decide +kernel)
private theorem root4721_3072 : Block (rootTest 4721 entries4721) 3072 3200 := checkedBlock (by decide +kernel)
private theorem root4721_3200 : Block (rootTest 4721 entries4721) 3200 3328 := checkedBlock (by decide +kernel)
private theorem root4721_3328 : Block (rootTest 4721 entries4721) 3328 3456 := checkedBlock (by decide +kernel)
private theorem root4721_3456 : Block (rootTest 4721 entries4721) 3456 3584 := checkedBlock (by decide +kernel)
private theorem root4721_3584 : Block (rootTest 4721 entries4721) 3584 3712 := checkedBlock (by decide +kernel)
private theorem root4721_3712 : Block (rootTest 4721 entries4721) 3712 3840 := checkedBlock (by decide +kernel)
private theorem root4721_3840 : Block (rootTest 4721 entries4721) 3840 3968 := checkedBlock (by decide +kernel)
private theorem root4721_3968 : Block (rootTest 4721 entries4721) 3968 4096 := checkedBlock (by decide +kernel)
private theorem root4721_4096 : Block (rootTest 4721 entries4721) 4096 4224 := checkedBlock (by decide +kernel)
private theorem root4721_4224 : Block (rootTest 4721 entries4721) 4224 4352 := checkedBlock (by decide +kernel)
private theorem root4721_4352 : Block (rootTest 4721 entries4721) 4352 4480 := checkedBlock (by decide +kernel)
private theorem root4721_4480 : Block (rootTest 4721 entries4721) 4480 4608 := checkedBlock (by decide +kernel)
private theorem root4721_4608 : Block (rootTest 4721 entries4721) 4608 4721 := checkedBlock (by decide +kernel)
private theorem covered4721 : Covers 4721 entries4721 := covers_of_test
  (joinBlock (joinBlock (joinBlock (joinBlock (joinBlock root4721_0 root4721_128) (joinBlock root4721_256 root4721_384)) (joinBlock (joinBlock root4721_512 root4721_640) (joinBlock root4721_768 (joinBlock root4721_896 root4721_1024)))) (joinBlock (joinBlock (joinBlock root4721_1152 root4721_1280) (joinBlock root4721_1408 root4721_1536)) (joinBlock (joinBlock root4721_1664 root4721_1792) (joinBlock root4721_1920 (joinBlock root4721_2048 root4721_2176))))) (joinBlock (joinBlock (joinBlock (joinBlock root4721_2304 root4721_2432) (joinBlock root4721_2560 root4721_2688)) (joinBlock (joinBlock root4721_2816 root4721_2944) (joinBlock root4721_3072 (joinBlock root4721_3200 root4721_3328)))) (joinBlock (joinBlock (joinBlock root4721_3456 root4721_3584) (joinBlock root4721_3712 (joinBlock root4721_3840 root4721_3968))) (joinBlock (joinBlock root4721_4096 root4721_4224) (joinBlock root4721_4352 (joinBlock root4721_4480 root4721_4608))))))
private theorem entriesOK4721 : ∀ e ∈ entries4721, e.OK 4721 := by decide +kernel
private theorem cleared4721 (e : Entry) (h : e ∈ entries4721) : Clear e.chart := by
  simp only [entries4721, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact clear1
  · exact clear1
  · exact clear1
  · exact clear1

private def entries9881 : List Entry := [
  ⟨59642966760, L2, 0⟩,
  ⟨60171849717, L3, 0⟩,
  ⟨250640081247, L4, 0⟩,
  ⟨250671099130, L2, 2⟩,
  ⟨283425298270, L4, 3⟩,
  ⟨370454897724, L5, 0⟩,
  ⟨370485915607, L3, 3⟩,
  ⟨403240114747, L5, 3⟩,
  ⟨561483030094, L5, 2⟩,
  ⟨594237229234, L3, 2⟩,
  ⟨594268247117, L5, 1⟩,
  ⟨681297846571, L4, 2⟩,
  ⟨714052045711, L2, 3⟩,
  ⟨714083063594, L4, 1⟩,
  ⟨904551295124, L3, 1⟩,
  ⟨905080178081, L2, 1⟩]

private theorem root9881_0 : Block (rootTest 9881 entries9881) 0 128 := checkedBlock (by decide +kernel)
private theorem root9881_128 : Block (rootTest 9881 entries9881) 128 256 := checkedBlock (by decide +kernel)
private theorem root9881_256 : Block (rootTest 9881 entries9881) 256 384 := checkedBlock (by decide +kernel)
private theorem root9881_384 : Block (rootTest 9881 entries9881) 384 512 := checkedBlock (by decide +kernel)
private theorem root9881_512 : Block (rootTest 9881 entries9881) 512 640 := checkedBlock (by decide +kernel)
private theorem root9881_640 : Block (rootTest 9881 entries9881) 640 768 := checkedBlock (by decide +kernel)
private theorem root9881_768 : Block (rootTest 9881 entries9881) 768 896 := checkedBlock (by decide +kernel)
private theorem root9881_896 : Block (rootTest 9881 entries9881) 896 1024 := checkedBlock (by decide +kernel)
private theorem root9881_1024 : Block (rootTest 9881 entries9881) 1024 1152 := checkedBlock (by decide +kernel)
private theorem root9881_1152 : Block (rootTest 9881 entries9881) 1152 1280 := checkedBlock (by decide +kernel)
private theorem root9881_1280 : Block (rootTest 9881 entries9881) 1280 1408 := checkedBlock (by decide +kernel)
private theorem root9881_1408 : Block (rootTest 9881 entries9881) 1408 1536 := checkedBlock (by decide +kernel)
private theorem root9881_1536 : Block (rootTest 9881 entries9881) 1536 1664 := checkedBlock (by decide +kernel)
private theorem root9881_1664 : Block (rootTest 9881 entries9881) 1664 1792 := checkedBlock (by decide +kernel)
private theorem root9881_1792 : Block (rootTest 9881 entries9881) 1792 1920 := checkedBlock (by decide +kernel)
private theorem root9881_1920 : Block (rootTest 9881 entries9881) 1920 2048 := checkedBlock (by decide +kernel)
private theorem root9881_2048 : Block (rootTest 9881 entries9881) 2048 2176 := checkedBlock (by decide +kernel)
private theorem root9881_2176 : Block (rootTest 9881 entries9881) 2176 2304 := checkedBlock (by decide +kernel)
private theorem root9881_2304 : Block (rootTest 9881 entries9881) 2304 2432 := checkedBlock (by decide +kernel)
private theorem root9881_2432 : Block (rootTest 9881 entries9881) 2432 2560 := checkedBlock (by decide +kernel)
private theorem root9881_2560 : Block (rootTest 9881 entries9881) 2560 2688 := checkedBlock (by decide +kernel)
private theorem root9881_2688 : Block (rootTest 9881 entries9881) 2688 2816 := checkedBlock (by decide +kernel)
private theorem root9881_2816 : Block (rootTest 9881 entries9881) 2816 2944 := checkedBlock (by decide +kernel)
private theorem root9881_2944 : Block (rootTest 9881 entries9881) 2944 3072 := checkedBlock (by decide +kernel)
private theorem root9881_3072 : Block (rootTest 9881 entries9881) 3072 3200 := checkedBlock (by decide +kernel)
private theorem root9881_3200 : Block (rootTest 9881 entries9881) 3200 3328 := checkedBlock (by decide +kernel)
private theorem root9881_3328 : Block (rootTest 9881 entries9881) 3328 3456 := checkedBlock (by decide +kernel)
private theorem root9881_3456 : Block (rootTest 9881 entries9881) 3456 3584 := checkedBlock (by decide +kernel)
private theorem root9881_3584 : Block (rootTest 9881 entries9881) 3584 3712 := checkedBlock (by decide +kernel)
private theorem root9881_3712 : Block (rootTest 9881 entries9881) 3712 3840 := checkedBlock (by decide +kernel)
private theorem root9881_3840 : Block (rootTest 9881 entries9881) 3840 3968 := checkedBlock (by decide +kernel)
private theorem root9881_3968 : Block (rootTest 9881 entries9881) 3968 4096 := checkedBlock (by decide +kernel)
private theorem root9881_4096 : Block (rootTest 9881 entries9881) 4096 4224 := checkedBlock (by decide +kernel)
private theorem root9881_4224 : Block (rootTest 9881 entries9881) 4224 4352 := checkedBlock (by decide +kernel)
private theorem root9881_4352 : Block (rootTest 9881 entries9881) 4352 4480 := checkedBlock (by decide +kernel)
private theorem root9881_4480 : Block (rootTest 9881 entries9881) 4480 4608 := checkedBlock (by decide +kernel)
private theorem root9881_4608 : Block (rootTest 9881 entries9881) 4608 4736 := checkedBlock (by decide +kernel)
private theorem root9881_4736 : Block (rootTest 9881 entries9881) 4736 4864 := checkedBlock (by decide +kernel)
private theorem root9881_4864 : Block (rootTest 9881 entries9881) 4864 4992 := checkedBlock (by decide +kernel)
private theorem root9881_4992 : Block (rootTest 9881 entries9881) 4992 5120 := checkedBlock (by decide +kernel)
private theorem root9881_5120 : Block (rootTest 9881 entries9881) 5120 5248 := checkedBlock (by decide +kernel)
private theorem root9881_5248 : Block (rootTest 9881 entries9881) 5248 5376 := checkedBlock (by decide +kernel)
private theorem root9881_5376 : Block (rootTest 9881 entries9881) 5376 5504 := checkedBlock (by decide +kernel)
private theorem root9881_5504 : Block (rootTest 9881 entries9881) 5504 5632 := checkedBlock (by decide +kernel)
private theorem root9881_5632 : Block (rootTest 9881 entries9881) 5632 5760 := checkedBlock (by decide +kernel)
private theorem root9881_5760 : Block (rootTest 9881 entries9881) 5760 5888 := checkedBlock (by decide +kernel)
private theorem root9881_5888 : Block (rootTest 9881 entries9881) 5888 6016 := checkedBlock (by decide +kernel)
private theorem root9881_6016 : Block (rootTest 9881 entries9881) 6016 6144 := checkedBlock (by decide +kernel)
private theorem root9881_6144 : Block (rootTest 9881 entries9881) 6144 6272 := checkedBlock (by decide +kernel)
private theorem root9881_6272 : Block (rootTest 9881 entries9881) 6272 6400 := checkedBlock (by decide +kernel)
private theorem root9881_6400 : Block (rootTest 9881 entries9881) 6400 6528 := checkedBlock (by decide +kernel)
private theorem root9881_6528 : Block (rootTest 9881 entries9881) 6528 6656 := checkedBlock (by decide +kernel)
private theorem root9881_6656 : Block (rootTest 9881 entries9881) 6656 6784 := checkedBlock (by decide +kernel)
private theorem root9881_6784 : Block (rootTest 9881 entries9881) 6784 6912 := checkedBlock (by decide +kernel)
private theorem root9881_6912 : Block (rootTest 9881 entries9881) 6912 7040 := checkedBlock (by decide +kernel)
private theorem root9881_7040 : Block (rootTest 9881 entries9881) 7040 7168 := checkedBlock (by decide +kernel)
private theorem root9881_7168 : Block (rootTest 9881 entries9881) 7168 7296 := checkedBlock (by decide +kernel)
private theorem root9881_7296 : Block (rootTest 9881 entries9881) 7296 7424 := checkedBlock (by decide +kernel)
private theorem root9881_7424 : Block (rootTest 9881 entries9881) 7424 7552 := checkedBlock (by decide +kernel)
private theorem root9881_7552 : Block (rootTest 9881 entries9881) 7552 7680 := checkedBlock (by decide +kernel)
private theorem root9881_7680 : Block (rootTest 9881 entries9881) 7680 7808 := checkedBlock (by decide +kernel)
private theorem root9881_7808 : Block (rootTest 9881 entries9881) 7808 7936 := checkedBlock (by decide +kernel)
private theorem root9881_7936 : Block (rootTest 9881 entries9881) 7936 8064 := checkedBlock (by decide +kernel)
private theorem root9881_8064 : Block (rootTest 9881 entries9881) 8064 8192 := checkedBlock (by decide +kernel)
private theorem root9881_8192 : Block (rootTest 9881 entries9881) 8192 8320 := checkedBlock (by decide +kernel)
private theorem root9881_8320 : Block (rootTest 9881 entries9881) 8320 8448 := checkedBlock (by decide +kernel)
private theorem root9881_8448 : Block (rootTest 9881 entries9881) 8448 8576 := checkedBlock (by decide +kernel)
private theorem root9881_8576 : Block (rootTest 9881 entries9881) 8576 8704 := checkedBlock (by decide +kernel)
private theorem root9881_8704 : Block (rootTest 9881 entries9881) 8704 8832 := checkedBlock (by decide +kernel)
private theorem root9881_8832 : Block (rootTest 9881 entries9881) 8832 8960 := checkedBlock (by decide +kernel)
private theorem root9881_8960 : Block (rootTest 9881 entries9881) 8960 9088 := checkedBlock (by decide +kernel)
private theorem root9881_9088 : Block (rootTest 9881 entries9881) 9088 9216 := checkedBlock (by decide +kernel)
private theorem root9881_9216 : Block (rootTest 9881 entries9881) 9216 9344 := checkedBlock (by decide +kernel)
private theorem root9881_9344 : Block (rootTest 9881 entries9881) 9344 9472 := checkedBlock (by decide +kernel)
private theorem root9881_9472 : Block (rootTest 9881 entries9881) 9472 9600 := checkedBlock (by decide +kernel)
private theorem root9881_9600 : Block (rootTest 9881 entries9881) 9600 9728 := checkedBlock (by decide +kernel)
private theorem root9881_9728 : Block (rootTest 9881 entries9881) 9728 9856 := checkedBlock (by decide +kernel)
private theorem root9881_9856 : Block (rootTest 9881 entries9881) 9856 9881 := checkedBlock (by decide +kernel)
private theorem covered9881 : Covers 9881 entries9881 := covers_of_test
  (joinBlock (joinBlock (joinBlock (joinBlock (joinBlock (joinBlock root9881_0 root9881_128) (joinBlock root9881_256 root9881_384)) (joinBlock (joinBlock root9881_512 root9881_640) (joinBlock root9881_768 (joinBlock root9881_896 root9881_1024)))) (joinBlock (joinBlock (joinBlock root9881_1152 root9881_1280) (joinBlock root9881_1408 (joinBlock root9881_1536 root9881_1664))) (joinBlock (joinBlock root9881_1792 root9881_1920) (joinBlock root9881_2048 (joinBlock root9881_2176 root9881_2304))))) (joinBlock (joinBlock (joinBlock (joinBlock root9881_2432 root9881_2560) (joinBlock root9881_2688 (joinBlock root9881_2816 root9881_2944))) (joinBlock (joinBlock root9881_3072 root9881_3200) (joinBlock root9881_3328 (joinBlock root9881_3456 root9881_3584)))) (joinBlock (joinBlock (joinBlock root9881_3712 root9881_3840) (joinBlock root9881_3968 (joinBlock root9881_4096 root9881_4224))) (joinBlock (joinBlock root9881_4352 root9881_4480) (joinBlock root9881_4608 (joinBlock root9881_4736 root9881_4864)))))) (joinBlock (joinBlock (joinBlock (joinBlock (joinBlock root9881_4992 root9881_5120) (joinBlock root9881_5248 root9881_5376)) (joinBlock (joinBlock root9881_5504 root9881_5632) (joinBlock root9881_5760 (joinBlock root9881_5888 root9881_6016)))) (joinBlock (joinBlock (joinBlock root9881_6144 root9881_6272) (joinBlock root9881_6400 (joinBlock root9881_6528 root9881_6656))) (joinBlock (joinBlock root9881_6784 root9881_6912) (joinBlock root9881_7040 (joinBlock root9881_7168 root9881_7296))))) (joinBlock (joinBlock (joinBlock (joinBlock root9881_7424 root9881_7552) (joinBlock root9881_7680 (joinBlock root9881_7808 root9881_7936))) (joinBlock (joinBlock root9881_8064 root9881_8192) (joinBlock root9881_8320 (joinBlock root9881_8448 root9881_8576)))) (joinBlock (joinBlock (joinBlock root9881_8704 root9881_8832) (joinBlock root9881_8960 (joinBlock root9881_9088 root9881_9216))) (joinBlock (joinBlock root9881_9344 root9881_9472) (joinBlock root9881_9600 (joinBlock root9881_9728 root9881_9856)))))))
private theorem entriesOK9881 : ∀ e ∈ entries9881, e.OK 9881 := by decide +kernel
private theorem cleared9881 (e : Entry) (h : e ∈ entries9881) : Clear e.chart := by
  simp only [entries9881, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact clear2
  · exact clear3
  · exact clear4
  · exact clear2
  · exact clear4
  · exact clear5
  · exact clear3
  · exact clear5
  · exact clear5
  · exact clear3
  · exact clear5
  · exact clear4
  · exact clear2
  · exact clear4
  · exact clear3
  · exact clear2

private def entries6497 : List Entry := [
  ⟨7981929259, L6, 0⟩,
  ⟨20910520237, L7, 0⟩,
  ⟨53683659591, L8, 0⟩,
  ⟨62383452529, L6, 2⟩,
  ⟨66612250569, L9, 0⟩,
  ⟨91565562784, L7, 2⟩,
  ⟨108085182861, L8, 2⟩,
  ⟨136977632357, L9, 3⟩,
  ⟨137267293116, L9, 2⟩,
  ⟨166159742612, L8, 3⟩,
  ⟨182679362689, L7, 3⟩,
  ⟨207632674904, L9, 1⟩,
  ⟨211861472944, L6, 3⟩,
  ⟨220561265882, L8, 1⟩,
  ⟨253334405236, L7, 1⟩,
  ⟨266262996214, L6, 1⟩]

private theorem root6497_0 : Block (rootTest 6497 entries6497) 0 128 := checkedBlock (by decide +kernel)
private theorem root6497_128 : Block (rootTest 6497 entries6497) 128 256 := checkedBlock (by decide +kernel)
private theorem root6497_256 : Block (rootTest 6497 entries6497) 256 384 := checkedBlock (by decide +kernel)
private theorem root6497_384 : Block (rootTest 6497 entries6497) 384 512 := checkedBlock (by decide +kernel)
private theorem root6497_512 : Block (rootTest 6497 entries6497) 512 640 := checkedBlock (by decide +kernel)
private theorem root6497_640 : Block (rootTest 6497 entries6497) 640 768 := checkedBlock (by decide +kernel)
private theorem root6497_768 : Block (rootTest 6497 entries6497) 768 896 := checkedBlock (by decide +kernel)
private theorem root6497_896 : Block (rootTest 6497 entries6497) 896 1024 := checkedBlock (by decide +kernel)
private theorem root6497_1024 : Block (rootTest 6497 entries6497) 1024 1152 := checkedBlock (by decide +kernel)
private theorem root6497_1152 : Block (rootTest 6497 entries6497) 1152 1280 := checkedBlock (by decide +kernel)
private theorem root6497_1280 : Block (rootTest 6497 entries6497) 1280 1408 := checkedBlock (by decide +kernel)
private theorem root6497_1408 : Block (rootTest 6497 entries6497) 1408 1536 := checkedBlock (by decide +kernel)
private theorem root6497_1536 : Block (rootTest 6497 entries6497) 1536 1664 := checkedBlock (by decide +kernel)
private theorem root6497_1664 : Block (rootTest 6497 entries6497) 1664 1792 := checkedBlock (by decide +kernel)
private theorem root6497_1792 : Block (rootTest 6497 entries6497) 1792 1920 := checkedBlock (by decide +kernel)
private theorem root6497_1920 : Block (rootTest 6497 entries6497) 1920 2048 := checkedBlock (by decide +kernel)
private theorem root6497_2048 : Block (rootTest 6497 entries6497) 2048 2176 := checkedBlock (by decide +kernel)
private theorem root6497_2176 : Block (rootTest 6497 entries6497) 2176 2304 := checkedBlock (by decide +kernel)
private theorem root6497_2304 : Block (rootTest 6497 entries6497) 2304 2432 := checkedBlock (by decide +kernel)
private theorem root6497_2432 : Block (rootTest 6497 entries6497) 2432 2560 := checkedBlock (by decide +kernel)
private theorem root6497_2560 : Block (rootTest 6497 entries6497) 2560 2688 := checkedBlock (by decide +kernel)
private theorem root6497_2688 : Block (rootTest 6497 entries6497) 2688 2816 := checkedBlock (by decide +kernel)
private theorem root6497_2816 : Block (rootTest 6497 entries6497) 2816 2944 := checkedBlock (by decide +kernel)
private theorem root6497_2944 : Block (rootTest 6497 entries6497) 2944 3072 := checkedBlock (by decide +kernel)
private theorem root6497_3072 : Block (rootTest 6497 entries6497) 3072 3200 := checkedBlock (by decide +kernel)
private theorem root6497_3200 : Block (rootTest 6497 entries6497) 3200 3328 := checkedBlock (by decide +kernel)
private theorem root6497_3328 : Block (rootTest 6497 entries6497) 3328 3456 := checkedBlock (by decide +kernel)
private theorem root6497_3456 : Block (rootTest 6497 entries6497) 3456 3584 := checkedBlock (by decide +kernel)
private theorem root6497_3584 : Block (rootTest 6497 entries6497) 3584 3712 := checkedBlock (by decide +kernel)
private theorem root6497_3712 : Block (rootTest 6497 entries6497) 3712 3840 := checkedBlock (by decide +kernel)
private theorem root6497_3840 : Block (rootTest 6497 entries6497) 3840 3968 := checkedBlock (by decide +kernel)
private theorem root6497_3968 : Block (rootTest 6497 entries6497) 3968 4096 := checkedBlock (by decide +kernel)
private theorem root6497_4096 : Block (rootTest 6497 entries6497) 4096 4224 := checkedBlock (by decide +kernel)
private theorem root6497_4224 : Block (rootTest 6497 entries6497) 4224 4352 := checkedBlock (by decide +kernel)
private theorem root6497_4352 : Block (rootTest 6497 entries6497) 4352 4480 := checkedBlock (by decide +kernel)
private theorem root6497_4480 : Block (rootTest 6497 entries6497) 4480 4608 := checkedBlock (by decide +kernel)
private theorem root6497_4608 : Block (rootTest 6497 entries6497) 4608 4736 := checkedBlock (by decide +kernel)
private theorem root6497_4736 : Block (rootTest 6497 entries6497) 4736 4864 := checkedBlock (by decide +kernel)
private theorem root6497_4864 : Block (rootTest 6497 entries6497) 4864 4992 := checkedBlock (by decide +kernel)
private theorem root6497_4992 : Block (rootTest 6497 entries6497) 4992 5120 := checkedBlock (by decide +kernel)
private theorem root6497_5120 : Block (rootTest 6497 entries6497) 5120 5248 := checkedBlock (by decide +kernel)
private theorem root6497_5248 : Block (rootTest 6497 entries6497) 5248 5376 := checkedBlock (by decide +kernel)
private theorem root6497_5376 : Block (rootTest 6497 entries6497) 5376 5504 := checkedBlock (by decide +kernel)
private theorem root6497_5504 : Block (rootTest 6497 entries6497) 5504 5632 := checkedBlock (by decide +kernel)
private theorem root6497_5632 : Block (rootTest 6497 entries6497) 5632 5760 := checkedBlock (by decide +kernel)
private theorem root6497_5760 : Block (rootTest 6497 entries6497) 5760 5888 := checkedBlock (by decide +kernel)
private theorem root6497_5888 : Block (rootTest 6497 entries6497) 5888 6016 := checkedBlock (by decide +kernel)
private theorem root6497_6016 : Block (rootTest 6497 entries6497) 6016 6144 := checkedBlock (by decide +kernel)
private theorem root6497_6144 : Block (rootTest 6497 entries6497) 6144 6272 := checkedBlock (by decide +kernel)
private theorem root6497_6272 : Block (rootTest 6497 entries6497) 6272 6400 := checkedBlock (by decide +kernel)
private theorem root6497_6400 : Block (rootTest 6497 entries6497) 6400 6497 := checkedBlock (by decide +kernel)
private theorem covered6497 : Covers 6497 entries6497 := covers_of_test
  (joinBlock (joinBlock (joinBlock (joinBlock (joinBlock root6497_0 (joinBlock root6497_128 root6497_256)) (joinBlock root6497_384 (joinBlock root6497_512 root6497_640))) (joinBlock (joinBlock root6497_768 (joinBlock root6497_896 root6497_1024)) (joinBlock root6497_1152 (joinBlock root6497_1280 root6497_1408)))) (joinBlock (joinBlock (joinBlock root6497_1536 (joinBlock root6497_1664 root6497_1792)) (joinBlock root6497_1920 (joinBlock root6497_2048 root6497_2176))) (joinBlock (joinBlock root6497_2304 (joinBlock root6497_2432 root6497_2560)) (joinBlock (joinBlock root6497_2688 root6497_2816) (joinBlock root6497_2944 root6497_3072))))) (joinBlock (joinBlock (joinBlock (joinBlock root6497_3200 (joinBlock root6497_3328 root6497_3456)) (joinBlock root6497_3584 (joinBlock root6497_3712 root6497_3840))) (joinBlock (joinBlock root6497_3968 (joinBlock root6497_4096 root6497_4224)) (joinBlock (joinBlock root6497_4352 root6497_4480) (joinBlock root6497_4608 root6497_4736)))) (joinBlock (joinBlock (joinBlock root6497_4864 (joinBlock root6497_4992 root6497_5120)) (joinBlock root6497_5248 (joinBlock root6497_5376 root6497_5504))) (joinBlock (joinBlock root6497_5632 (joinBlock root6497_5760 root6497_5888)) (joinBlock (joinBlock root6497_6016 root6497_6144) (joinBlock root6497_6272 root6497_6400))))))
private theorem entriesOK6497 : ∀ e ∈ entries6497, e.OK 6497 := by decide +kernel
private theorem cleared6497 (e : Entry) (h : e ∈ entries6497) : Clear e.chart := by
  simp only [entries6497, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact clear6
  · exact clear7
  · exact clear8
  · exact clear6
  · exact clear9
  · exact clear7
  · exact clear8
  · exact clear9
  · exact clear9
  · exact clear8
  · exact clear7
  · exact clear9
  · exact clear6
  · exact clear8
  · exact clear7
  · exact clear6

private def entries4777 : List Entry := [
  ⟨2378092411, L10, 0⟩,
  ⟨10254846966, L11, 0⟩,
  ⟨12690219022, L12, 0⟩,
  ⟨14401379039, L10, 2⟩,
  ⟨20566973577, L13, 0⟩,
  ⟨24713505650, L12, 2⟩,
  ⟨37346445027, L13, 3⟩,
  ⟨47658571638, L11, 3⟩,
  ⟨61351273795, L11, 2⟩,
  ⟨71663400406, L13, 2⟩,
  ⟨84296339783, L12, 3⟩,
  ⟨88442871856, L13, 1⟩,
  ⟨94608466394, L10, 3⟩,
  ⟨96319626411, L12, 1⟩,
  ⟨98754998467, L11, 1⟩,
  ⟨106631753022, L10, 1⟩]

private theorem root4777_0 : Block (rootTest 4777 entries4777) 0 128 := checkedBlock (by decide +kernel)
private theorem root4777_128 : Block (rootTest 4777 entries4777) 128 256 := checkedBlock (by decide +kernel)
private theorem root4777_256 : Block (rootTest 4777 entries4777) 256 384 := checkedBlock (by decide +kernel)
private theorem root4777_384 : Block (rootTest 4777 entries4777) 384 512 := checkedBlock (by decide +kernel)
private theorem root4777_512 : Block (rootTest 4777 entries4777) 512 640 := checkedBlock (by decide +kernel)
private theorem root4777_640 : Block (rootTest 4777 entries4777) 640 768 := checkedBlock (by decide +kernel)
private theorem root4777_768 : Block (rootTest 4777 entries4777) 768 896 := checkedBlock (by decide +kernel)
private theorem root4777_896 : Block (rootTest 4777 entries4777) 896 1024 := checkedBlock (by decide +kernel)
private theorem root4777_1024 : Block (rootTest 4777 entries4777) 1024 1152 := checkedBlock (by decide +kernel)
private theorem root4777_1152 : Block (rootTest 4777 entries4777) 1152 1280 := checkedBlock (by decide +kernel)
private theorem root4777_1280 : Block (rootTest 4777 entries4777) 1280 1408 := checkedBlock (by decide +kernel)
private theorem root4777_1408 : Block (rootTest 4777 entries4777) 1408 1536 := checkedBlock (by decide +kernel)
private theorem root4777_1536 : Block (rootTest 4777 entries4777) 1536 1664 := checkedBlock (by decide +kernel)
private theorem root4777_1664 : Block (rootTest 4777 entries4777) 1664 1792 := checkedBlock (by decide +kernel)
private theorem root4777_1792 : Block (rootTest 4777 entries4777) 1792 1920 := checkedBlock (by decide +kernel)
private theorem root4777_1920 : Block (rootTest 4777 entries4777) 1920 2048 := checkedBlock (by decide +kernel)
private theorem root4777_2048 : Block (rootTest 4777 entries4777) 2048 2176 := checkedBlock (by decide +kernel)
private theorem root4777_2176 : Block (rootTest 4777 entries4777) 2176 2304 := checkedBlock (by decide +kernel)
private theorem root4777_2304 : Block (rootTest 4777 entries4777) 2304 2432 := checkedBlock (by decide +kernel)
private theorem root4777_2432 : Block (rootTest 4777 entries4777) 2432 2560 := checkedBlock (by decide +kernel)
private theorem root4777_2560 : Block (rootTest 4777 entries4777) 2560 2688 := checkedBlock (by decide +kernel)
private theorem root4777_2688 : Block (rootTest 4777 entries4777) 2688 2816 := checkedBlock (by decide +kernel)
private theorem root4777_2816 : Block (rootTest 4777 entries4777) 2816 2944 := checkedBlock (by decide +kernel)
private theorem root4777_2944 : Block (rootTest 4777 entries4777) 2944 3072 := checkedBlock (by decide +kernel)
private theorem root4777_3072 : Block (rootTest 4777 entries4777) 3072 3200 := checkedBlock (by decide +kernel)
private theorem root4777_3200 : Block (rootTest 4777 entries4777) 3200 3328 := checkedBlock (by decide +kernel)
private theorem root4777_3328 : Block (rootTest 4777 entries4777) 3328 3456 := checkedBlock (by decide +kernel)
private theorem root4777_3456 : Block (rootTest 4777 entries4777) 3456 3584 := checkedBlock (by decide +kernel)
private theorem root4777_3584 : Block (rootTest 4777 entries4777) 3584 3712 := checkedBlock (by decide +kernel)
private theorem root4777_3712 : Block (rootTest 4777 entries4777) 3712 3840 := checkedBlock (by decide +kernel)
private theorem root4777_3840 : Block (rootTest 4777 entries4777) 3840 3968 := checkedBlock (by decide +kernel)
private theorem root4777_3968 : Block (rootTest 4777 entries4777) 3968 4096 := checkedBlock (by decide +kernel)
private theorem root4777_4096 : Block (rootTest 4777 entries4777) 4096 4224 := checkedBlock (by decide +kernel)
private theorem root4777_4224 : Block (rootTest 4777 entries4777) 4224 4352 := checkedBlock (by decide +kernel)
private theorem root4777_4352 : Block (rootTest 4777 entries4777) 4352 4480 := checkedBlock (by decide +kernel)
private theorem root4777_4480 : Block (rootTest 4777 entries4777) 4480 4608 := checkedBlock (by decide +kernel)
private theorem root4777_4608 : Block (rootTest 4777 entries4777) 4608 4736 := checkedBlock (by decide +kernel)
private theorem root4777_4736 : Block (rootTest 4777 entries4777) 4736 4777 := checkedBlock (by decide +kernel)
private theorem covered4777 : Covers 4777 entries4777 := covers_of_test
  (joinBlock (joinBlock (joinBlock (joinBlock (joinBlock root4777_0 root4777_128) (joinBlock root4777_256 root4777_384)) (joinBlock (joinBlock root4777_512 root4777_640) (joinBlock root4777_768 (joinBlock root4777_896 root4777_1024)))) (joinBlock (joinBlock (joinBlock root4777_1152 root4777_1280) (joinBlock root4777_1408 (joinBlock root4777_1536 root4777_1664))) (joinBlock (joinBlock root4777_1792 root4777_1920) (joinBlock root4777_2048 (joinBlock root4777_2176 root4777_2304))))) (joinBlock (joinBlock (joinBlock (joinBlock root4777_2432 root4777_2560) (joinBlock root4777_2688 root4777_2816)) (joinBlock (joinBlock root4777_2944 root4777_3072) (joinBlock root4777_3200 (joinBlock root4777_3328 root4777_3456)))) (joinBlock (joinBlock (joinBlock root4777_3584 root4777_3712) (joinBlock root4777_3840 (joinBlock root4777_3968 root4777_4096))) (joinBlock (joinBlock root4777_4224 root4777_4352) (joinBlock root4777_4480 (joinBlock root4777_4608 root4777_4736))))))
private theorem entriesOK4777 : ∀ e ∈ entries4777, e.OK 4777 := by decide +kernel
private theorem cleared4777 (e : Entry) (h : e ∈ entries4777) : Clear e.chart := by
  simp only [entries4777, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact clear10
  · exact clear11
  · exact clear12
  · exact clear10
  · exact clear13
  · exact clear12
  · exact clear13
  · exact clear11
  · exact clear11
  · exact clear13
  · exact clear12
  · exact clear13
  · exact clear10
  · exact clear12
  · exact clear11
  · exact clear10

private theorem exceptional : OMA.R_mo_191889_R1.H2 := by
  intro b z x y member _ _ hz hx hxy hy hc he hl
  have good : Good b (x:ℤ) y := by
    refine ⟨by simpa using hx, by simpa using (lt_of_lt_of_le hx hxy),
      by simpa [bound] using (hxy.trans hy), by simpa [bound] using hy,
      by simpa using hc, ?_, ⟨z, by exact_mod_cast he⟩⟩
    simpa only [Int.natAbs_natCast, he, limit] using hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl|rfl|rfl|rfl|rfl
  · exact by_table (by decide) covered4721 entriesOK4721 cleared4721 hc hz he good
  · exact by_table (by decide) covered4777 entriesOK4777 cleared4777 hc hz he good
  · exact by_table (by decide) covered6497 entriesOK6497 cleared6497 hc hz he good
  · exact by_table (by decide) covered6577 entriesOK6577 cleared6577 hc hz he good
  · exact by_table (by decide) covered9881 entriesOK9881 cleared9881 hc hz he good

end OMA.QuarticExceptional

theorem OMA.solution : OMA.R_mo_191889_R1.H2 := OMA.QuarticExceptional.exceptional
