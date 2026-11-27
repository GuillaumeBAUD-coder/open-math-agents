import OMAReductions.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1

/-!
Nonvanishing of OEIS A105751 from index four onward.
The exact powers of two in the four residue classes are due to KitaKen1.
The block argument below is adapted from the Apache-2.0-licensed source at
https://github.com/KitaKen1/oeis-a105751-two-adic/blob/a9692d90078c4dff1478acaaa70be2fba06a3ef9/lean/OeisA105751TwoAdicFC.lean
License: https://www.apache.org/licenses/LICENSE-2.0

This adaptation uses the project sequence directly and deduces the nonvanishing
hypothesis of ZenimXD's reduction by extracting the odd factor in each case.
-/

open Complex Filter Topology Nat

namespace A105751Proof

/-- The pair `(r,s)` represents the Gaussian integer `r + 4 s i`. -/
structure Quad4 where
  re : ℤ
  im : ℤ

namespace Quad4

theorem ext {x y : Quad4} (hre : x.re = y.re) (him : x.im = y.im) : x = y := by
  cases x
  cases y
  simp_all

def one : Quad4 := ⟨1, 0⟩

def mul (z w : Quad4) : Quad4 :=
  ⟨z.re * w.re - 16 * z.im * w.im, z.re * w.im + z.im * w.re⟩

@[simp] theorem one_re : one.re = 1 := rfl
@[simp] theorem one_im : one.im = 0 := rfl
@[simp] theorem mul_re (z w : Quad4) : (mul z w).re = z.re * w.re - 16 * z.im * w.im := rfl
@[simp] theorem mul_im (z w : Quad4) : (mul z w).im = z.re * w.im + z.im * w.re := rfl

theorem mul_assoc (x y z : Quad4) : mul (mul x y) z = mul x (mul y z) := by
  apply Quad4.ext <;> simp [mul] <;> ring

theorem mul_comm (x y : Quad4) : mul x y = mul y x := by
  apply Quad4.ext <;> simp [mul] <;> ring

@[simp] theorem one_mul (x : Quad4) : mul one x = x := by
  apply Quad4.ext <;> simp [mul]

@[simp] theorem mul_one (x : Quad4) : mul x one = x := by
  rw [mul_comm, one_mul]

/-- The determinant comparing the two formal slopes `im / re`. -/
def cross (z w : Quad4) : ℤ := z.im * w.re - z.re * w.im

def norm4 (z : Quad4) : ℤ := z.re ^ 2 + 16 * z.im ^ 2

theorem cross_mul_right (x y z : Quad4) :
    cross (mul x z) (mul y z) = norm4 z * cross x y := by
  simp [cross, norm4, mul]
  ring

theorem cross_mul_left (x y z : Quad4) :
    cross (mul z x) (mul z y) = norm4 z * cross x y := by
  simpa [mul_comm] using cross_mul_right x y z

theorem cross_trans_num (x y z : Quad4) :
    y.re * cross x z = z.re * cross x y + x.re * cross y z := by
  simp [cross]
  ring

theorem odd_re_mul {x y : Quad4} (hx : Odd x.re) (hy : Odd y.re) :
    Odd (mul x y).re := by
  rcases hx with ⟨a, ha⟩
  rcases hy with ⟨b, hb⟩
  refine ⟨2 * a * b + a + b - 8 * x.im * y.im, ?_⟩
  simp only [mul_re, ha, hb]
  ring

/-- Product of `len` consecutive factors, beginning at `start`. -/
def prodFrom (f : ℕ → Quad4) (start : ℕ) : ℕ → Quad4
  | 0 => one
  | len + 1 => mul (prodFrom f start len) (f (start + len))

@[simp] theorem prodFrom_zero (f : ℕ → Quad4) (start : ℕ) :
    prodFrom f start 0 = one := rfl

@[simp] theorem prodFrom_succ (f : ℕ → Quad4) (start len : ℕ) :
    prodFrom f start (len + 1) = mul (prodFrom f start len) (f (start + len)) := rfl

theorem prodFrom_add (f : ℕ → Quad4) (start a b : ℕ) :
    prodFrom f start (a + b) =
      mul (prodFrom f start a) (prodFrom f (start + a) b) := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [Nat.add_succ, prodFrom_succ, ih, prodFrom_succ]
      rw [mul_assoc]
      congr 2
      simp [Nat.add_assoc]

theorem odd_re_prodFrom (f : ℕ → Quad4) (hf : ∀ n, Odd (f n).re)
    (start len : ℕ) : Odd (prodFrom f start len).re := by
  induction len with
  | zero => exact odd_one
  | succ len ih => exact odd_re_mul ih (hf _)

end Quad4

/-- `ExactTwo k z` means that the exact power of two dividing `z` is `2^k`. -/
def ExactTwo (k : ℕ) (z : ℤ) : Prop :=
  ∃ u : ℤ, Odd u ∧ z = (2 : ℤ) ^ k * u

theorem exactTwo_zero_iff_odd (z : ℤ) : ExactTwo 0 z ↔ Odd z := by
  simp [ExactTwo]

theorem ExactTwo.nonzero {k : ℕ} {z : ℤ} (h : ExactTwo k z) : z ≠ 0 := by
  rcases h with ⟨u, hu, rfl⟩
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by
    intro huz
    subst u
    norm_num at hu)

theorem ExactTwo.mul_odd {k : ℕ} {z u : ℤ} (hz : ExactTwo k z) (hu : Odd u) :
    ExactTwo k (z * u) := by
  rcases hz with ⟨v, hv, rfl⟩
  refine ⟨v * u, hv.mul hu, ?_⟩
  ring

theorem ExactTwo.neg {k : ℕ} {z : ℤ} (hz : ExactTwo k z) : ExactTwo k (-z) := by
  rcases hz with ⟨u, hu, rfl⟩
  refine ⟨-u, hu.neg, ?_⟩
  ring

theorem pow_two_dvd_of_dvd_mul_odd (k : ℕ) {r z : ℤ} (hr : Odd r)
    (h : (2 : ℤ) ^ k ∣ r * z) : (2 : ℤ) ^ k ∣ z := by
  have hcop : IsCoprime (2 : ℤ) r := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hr.natAbs.coprime_two_left
  exact hcop.pow_left.dvd_of_dvd_mul_left h

theorem ExactTwo.of_mul_odd {k : ℕ} {z u : ℤ} (hzu : ExactTwo k (z * u))
    (hu : Odd u) : ExactTwo k z := by
  rcases hzu with ⟨v, hv, hvEq⟩
  have hd : (2 : ℤ) ^ k ∣ z * u := ⟨v, hvEq⟩
  have hdz : (2 : ℤ) ^ k ∣ z := by
    rw [mul_comm] at hd
    exact pow_two_dvd_of_dvd_mul_odd k hu hd
  rcases hdz with ⟨w, hw⟩
  refine ⟨w, ?_, hw⟩
  have hwumul : Odd (w * u) := by
    rw [hw] at hvEq
    have heq : w * u = v := by
      apply mul_left_cancel₀ (pow_ne_zero k (by norm_num : (2 : ℤ) ≠ 0))
      simpa [mul_assoc] using hvEq
    exact heq ▸ hv
  exact (Int.odd_mul.mp hwumul).1

theorem Quad4.cross_prodFrom_dvd
    (f g : ℕ → Quad4) (hf : ∀ n, Odd (f n).re) (hg : ∀ n, Odd (g n).re)
    (startF startG len N : ℕ)
    (hcross : ∀ j < len, (2 : ℤ) ^ N ∣ Quad4.cross (f (startF + j)) (g (startG + j))) :
    (2 : ℤ) ^ N ∣
      Quad4.cross (Quad4.prodFrom f startF len) (Quad4.prodFrom g startG len) := by
  induction len with
  | zero => simp [Quad4.prodFrom, Quad4.cross]
  | succ len ih =>
      let p := Quad4.prodFrom f startF len
      let q := Quad4.prodFrom g startG len
      let a := f (startF + len)
      let b := g (startG + len)
      let x := Quad4.mul p a
      let y := Quad4.mul q a
      let z := Quad4.mul q b
      have hpq : (2 : ℤ) ^ N ∣ Quad4.cross p q :=
        ih (fun j hj ↦ hcross j (Nat.lt_succ_of_lt hj))
      have hab : (2 : ℤ) ^ N ∣ Quad4.cross a b := by
        exact hcross len (Nat.lt_succ_self len)
      have hxy : (2 : ℤ) ^ N ∣ Quad4.cross x y := by
        rw [show Quad4.cross x y = Quad4.norm4 a * Quad4.cross p q by
          exact Quad4.cross_mul_right p q a]
        exact dvd_mul_of_dvd_right hpq _
      have hyz : (2 : ℤ) ^ N ∣ Quad4.cross y z := by
        rw [show Quad4.cross y z = Quad4.norm4 q * Quad4.cross a b by
          exact Quad4.cross_mul_left a b q]
        exact dvd_mul_of_dvd_right hab _
      have hyre : Odd y.re :=
        Quad4.odd_re_mul (Quad4.odd_re_prodFrom g hg startG len) (hf _)
      have hmul : (2 : ℤ) ^ N ∣ y.re * Quad4.cross x z := by
        rw [Quad4.cross_trans_num x y z]
        exact dvd_add (dvd_mul_of_dvd_right hxy _) (dvd_mul_of_dvd_right hyz _)
      have hxz : (2 : ℤ) ^ N ∣ Quad4.cross x z :=
        pow_two_dvd_of_dvd_mul_odd N hyre hmul
      simpa [x, z, p, q, a, b, Quad4.prodFrom_succ] using hxz

theorem exactTwo_mul_im_of_cross {k : ℕ} {p q : Quad4}
    (hpim : ExactTwo k p.im) (hqim : ExactTwo k q.im)
    (hqre : Odd q.re)
    (hcross : (2 : ℤ) ^ (k + 2) ∣ Quad4.cross p q) :
    ExactTwo (k + 1) (Quad4.mul p q).im := by
  rcases hpim with ⟨u, hu, hpu⟩
  rcases hqim with ⟨v, hv, hqv⟩
  rcases hcross with ⟨c, hc⟩
  refine ⟨u * q.re - 2 * c, (hu.mul hqre).sub_even ⟨c, by ring⟩, ?_⟩
  simp only [Quad4.mul_im, hpu, hqv, Quad4.cross] at hc ⊢
  simp only [pow_succ] at hc ⊢
  ring_nf at hc ⊢
  omega

/-- A dyadic block of factors has exactly the expected power of two in its
normalized imaginary coordinate. -/
theorem exactTwo_prodFrom_pow
    (f : ℕ → Quad4) (hre : ∀ n, Odd (f n).re) (him : ∀ n, Odd (f n).im)
    (hshift : ∀ x d : ℕ,
      (4 : ℤ) * d ∣ Quad4.cross (f x) (f (x + d)))
    (start k : ℕ) :
    ExactTwo k (Quad4.prodFrom f start (2 ^ k)).im := by
  induction k generalizing start with
  | zero =>
      simpa [Quad4.prodFrom, exactTwo_zero_iff_odd] using him start
  | succ k ih =>
      let L : ℕ := 2 ^ k
      let p := Quad4.prodFrom f start L
      let q := Quad4.prodFrom f (start + L) L
      have hpim : ExactTwo k p.im := ih start
      have hqim : ExactTwo k q.im := ih (start + L)
      have hqre : Odd q.re := Quad4.odd_re_prodFrom f hre (start + L) L
      have hpq : (2 : ℤ) ^ (k + 2) ∣ Quad4.cross p q := by
        apply Quad4.cross_prodFrom_dvd f f hre hre start (start + L) L (k + 2)
        intro j hj
        have h := hshift (start + j) L
        have hidx : start + L + j = start + j + L := by omega
        rw [hidx]
        convert h using 1
        simp [L, pow_add]
        ring
      have hmul : ExactTwo (k + 1) (Quad4.mul p q).im :=
        exactTwo_mul_im_of_cross hpim hqim hqre hpq
      have hsplit : 2 ^ (k + 1) = L + L := by
        simp [L, pow_succ]
        omega
      rw [hsplit, Quad4.prodFrom_add]
      simpa [p, q] using hmul

/-- The normalized imaginary coordinate of a product of equally-scaled factors
has the parity of the number of factors. -/
theorem scaledParity_prodFrom
    (g : ℕ → Quad4) (hre : ∀ n, Odd (g n).re)
    {k : ℕ} (him : ∀ n, ExactTwo k (g n).im)
    (start len : ℕ) :
    ∃ u : ℤ,
      (Quad4.prodFrom g start len).im = (2 : ℤ) ^ k * u ∧
      (Odd u ↔ Odd (len : ℤ)) := by
  induction len with
  | zero =>
      refine ⟨0, by simp [Quad4.prodFrom], ?_⟩
      norm_num
  | succ len ih =>
      rcases ih with ⟨u, hu, hpar⟩
      rcases him (start + len) with ⟨v, hv, hvEq⟩
      let p := Quad4.prodFrom g start len
      let a := g (start + len)
      refine ⟨p.re * v + u * a.re, ?_, ?_⟩
      · simp only [Quad4.prodFrom_succ, Quad4.mul_im, hu, hvEq, p, a]
        ring
      · have hpodd : Odd p.re := Quad4.odd_re_prodFrom g hre start len
        have haodd : Odd a.re := hre _
        have hfirst : Odd (p.re * v) := hpodd.mul hv
        have hsecond : Odd (u * a.re) ↔ Odd u := by
          simp [Int.odd_mul, haodd]
        have hlen : Odd ((len + 1 : ℕ) : ℤ) ↔ ¬ Odd (len : ℤ) := by
          simp only [Nat.cast_add, Nat.cast_one, Int.odd_add]
          simp
        rw [Int.odd_add, hlen]
        have hsecondEven : Even (u * a.re) ↔ ¬ Odd u := by
          rw [← Int.not_odd_iff_even, Int.odd_mul]
          simp [haodd]
        rw [hsecondEven]
        simpa [hfirst] using not_congr hpar

/-- Exact two-adic order for an arbitrary nonempty initial block. -/
theorem exactTwo_prodFrom
    (f : ℕ → Quad4) (hre : ∀ n, Odd (f n).re) (him : ∀ n, Odd (f n).im)
    (hshift : ∀ x d : ℕ,
      (4 : ℤ) * d ∣ Quad4.cross (f x) (f (x + d)))
    (start len : ℕ) (hlen : len ≠ 0) :
    ExactTwo (padicValNat 2 len) (Quad4.prodFrom f start len).im := by
  let k := padicValNat 2 len
  let L := 2 ^ k
  let blocks := len / L
  have hLdvd : L ∣ len := by
    simpa [L, k] using (pow_padicValNat_dvd (p := 2) (n := len))
  have hlen_eq : blocks * L = len := by
    exact Nat.div_mul_cancel hLdvd
  have hblocks_ne : blocks ≠ 0 := by
    intro hb
    rw [hb, zero_mul] at hlen_eq
    exact hlen hlen_eq.symm
  have hblocks_odd : Odd blocks := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro htwo
    rcases htwo with ⟨c, hc⟩
    have hbad : 2 ^ (k + 1) ∣ len := by
      refine ⟨c, ?_⟩
      rw [← hlen_eq, hc]
      simp [L, pow_succ]
      ring
    exact pow_succ_padicValNat_not_dvd (p := 2) hlen hbad
  let g : ℕ → Quad4 := fun j ↦ Quad4.prodFrom f (start + j * L) L
  have gre : ∀ j, Odd (g j).re := by
    intro j
    exact Quad4.odd_re_prodFrom f hre _ _
  have gim : ∀ j, ExactTwo k (g j).im := by
    intro j
    simpa [g, L] using exactTwo_prodFrom_pow f hre him hshift (start + j * L) k
  have hblocks_prod :
      Quad4.prodFrom g 0 blocks = Quad4.prodFrom f start (blocks * L) := by
    induction blocks with
    | zero => simp [Quad4.prodFrom]
    | succ b ih =>
        rw [Quad4.prodFrom_succ, ih]
        rw [Nat.succ_mul, Quad4.prodFrom_add]
        congr 2
        simp
  rcases scaledParity_prodFrom g gre gim 0 blocks with ⟨u, hu, huodd⟩
  have hu' : Odd u := huodd.mpr (by exact_mod_cast hblocks_odd)
  refine ⟨u, hu', ?_⟩
  change (Quad4.prodFrom f start len).im = (2 : ℤ) ^ k * u
  rw [← hlen_eq, ← hblocks_prod, hu]

/- ## The A105751 four-factor blocks -/

def blockE (n : ℕ) : ℤ :=
  let x : ℤ := n
  128 * x ^ 4 + 320 * x ^ 3 + 232 * x ^ 2 + 40 * x - 5

def blockF (n : ℕ) : ℤ :=
  let x : ℤ := n
  (x + 1) * (4 * x + 1) * (8 * x + 5)

/-- After extracting the factor `2` from one four-term block. -/
def smallBlock (n : ℕ) : Quad4 := ⟨blockE n, -blockF n⟩

def normalizedFourBlockProduct (m : ℕ) : Quad4 :=
  Quad4.prodFrom smallBlock 0 m

def evenARed (n : ℕ) : ℤ :=
  let x : ℤ := n
  1048576 * x ^ 8 + 4718592 * x ^ 7 + 8486912 * x ^ 6 + 7741440 * x ^ 5 +
    3668224 * x ^ 4 + 741888 * x ^ 3 - 33632 * x ^ 2 - 34920 * x

def evenHRed (n : ℕ) : ℤ :=
  let x : ℤ := n
  262144 * x ^ 7 + 1032192 * x ^ 6 + 1648640 * x ^ 5 + 1370880 * x ^ 4 +
    631456 * x ^ 3 + 157248 * x ^ 2 + 18715 * x

def evenA (n : ℕ) : ℤ := -13975 + 4 * evenARed n
def evenH (n : ℕ) : ℤ := 2925 + 4 * evenHRed n
def evenSuperBlock (n : ℕ) : Quad4 := ⟨evenA n, -evenH n⟩

def oddARed (n : ℕ) : ℤ :=
  let x : ℤ := n
  1048576 * x ^ 8 + 524288 * x ^ 7 - 688128 * x ^ 6 - 286720 * x ^ 5 +
    84224 * x ^ 4 + 28672 * x ^ 3 - 2272 * x ^ 2 - 520 * x

def oddHRed (n : ℕ) : ℤ :=
  let x : ℤ := n
  262144 * x ^ 7 + 114688 * x ^ 6 - 71680 * x ^ 5 - 26880 * x ^ 4 +
    4256 * x ^ 3 + 1232 * x ^ 2 - 45 * x

def oddA (n : ℕ) : ℤ := 25 + 4 * oddARed n
def oddH (n : ℕ) : ℤ := -25 + 4 * oddHRed n
def oddSuperBlock (n : ℕ) : Quad4 := ⟨oddA n, -oddH n⟩

theorem smallBlock_re_odd (n : ℕ) : Odd (smallBlock n).re := by
  refine ⟨64 * (n : ℤ) ^ 4 + 160 * (n : ℤ) ^ 3 + 116 * (n : ℤ) ^ 2 +
    20 * n - 3, ?_⟩
  change blockE n = _
  simp [blockE]
  ring

theorem evenSuperBlock_re_odd (n : ℕ) : Odd (evenSuperBlock n).re := by
  change Odd (evenA n)
  refine (by norm_num : Odd (-13975 : ℤ)).add_even ?_
  refine ⟨2 * evenARed n, ?_⟩
  ring

theorem evenSuperBlock_im_odd (n : ℕ) : Odd (evenSuperBlock n).im := by
  have h : Odd (evenH n) := by
    refine (by norm_num : Odd (2925 : ℤ)).add_even ?_
    exact ⟨2 * evenHRed n, by ring⟩
  change Odd (-evenH n)
  exact h.neg

theorem oddSuperBlock_re_odd (n : ℕ) : Odd (oddSuperBlock n).re := by
  change Odd (oddA n)
  refine (by norm_num : Odd (25 : ℤ)).add_even ?_
  exact ⟨2 * oddARed n, by ring⟩

theorem oddSuperBlock_im_odd (n : ℕ) : Odd (oddSuperBlock n).im := by
  have h : Odd (oddH n) := by
    refine (by norm_num : Odd (-25 : ℤ)).add_even ?_
    exact ⟨2 * oddHRed n, by ring⟩
  change Odd (-oddH n)
  exact h.neg

theorem evenSuperBlock_eq (n : ℕ) :
    Quad4.mul (smallBlock (2 * n)) (smallBlock (2 * n + 1)) = evenSuperBlock n := by
  apply Quad4.ext <;>
    simp [Quad4.mul, smallBlock, blockE, blockF, evenSuperBlock, evenA, evenH,
      evenARed, evenHRed] <;>
    ring

theorem oddSuperBlock_eq_pair (n : ℕ) :
    Quad4.mul (smallBlock (2 * n + 1)) (smallBlock (2 * n + 2)) =
      oddSuperBlock (n + 1) := by
  apply Quad4.ext <;>
    simp [Quad4.mul, smallBlock, blockE, blockF, oddSuperBlock, oddA, oddH,
      oddARed, oddHRed] <;>
    ring

theorem oddSuperBlock_zero :
    oddSuperBlock 0 = Quad4.mul ⟨-5, 0⟩ (smallBlock 0) := by
  apply Quad4.ext <;> norm_num [Quad4.mul, oddSuperBlock, oddA, oddH, oddARed, oddHRed,
    smallBlock, blockE, blockF]

theorem polynomial_shift_dvd (p : Polynomial ℤ) (x d : ℕ) :
    (d : ℤ) ∣ p.eval ((x + d : ℕ) : ℤ) - p.eval (x : ℤ) := by
  simpa using Polynomial.sub_dvd_eval_sub ((x + d : ℕ) : ℤ) (x : ℤ) p

theorem evenARed_shift_dvd (x d : ℕ) :
    (d : ℤ) ∣ evenARed (x + d) - evenARed x := by
  let p : Polynomial ℤ :=
    1048576 * Polynomial.X ^ 8 + 4718592 * Polynomial.X ^ 7 +
    8486912 * Polynomial.X ^ 6 + 7741440 * Polynomial.X ^ 5 +
    3668224 * Polynomial.X ^ 4 + 741888 * Polynomial.X ^ 3 -
    33632 * Polynomial.X ^ 2 - 34920 * Polynomial.X
  simpa [p, evenARed] using polynomial_shift_dvd p x d

theorem evenHRed_shift_dvd (x d : ℕ) :
    (d : ℤ) ∣ evenHRed (x + d) - evenHRed x := by
  let p : Polynomial ℤ :=
    262144 * Polynomial.X ^ 7 + 1032192 * Polynomial.X ^ 6 +
    1648640 * Polynomial.X ^ 5 + 1370880 * Polynomial.X ^ 4 +
    631456 * Polynomial.X ^ 3 + 157248 * Polynomial.X ^ 2 +
    18715 * Polynomial.X
  simpa [p, evenHRed] using polynomial_shift_dvd p x d

theorem oddARed_shift_dvd (x d : ℕ) :
    (d : ℤ) ∣ oddARed (x + d) - oddARed x := by
  let p : Polynomial ℤ :=
    1048576 * Polynomial.X ^ 8 + 524288 * Polynomial.X ^ 7 -
    688128 * Polynomial.X ^ 6 - 286720 * Polynomial.X ^ 5 +
    84224 * Polynomial.X ^ 4 + 28672 * Polynomial.X ^ 3 -
    2272 * Polynomial.X ^ 2 - 520 * Polynomial.X
  simpa [p, oddARed] using polynomial_shift_dvd p x d

theorem oddHRed_shift_dvd (x d : ℕ) :
    (d : ℤ) ∣ oddHRed (x + d) - oddHRed x := by
  let p : Polynomial ℤ :=
    262144 * Polynomial.X ^ 7 + 114688 * Polynomial.X ^ 6 -
    71680 * Polynomial.X ^ 5 - 26880 * Polynomial.X ^ 4 +
    4256 * Polynomial.X ^ 3 + 1232 * Polynomial.X ^ 2 -
    45 * Polynomial.X
  simpa [p, oddHRed] using polynomial_shift_dvd p x d

theorem const_add_four_shift_dvd (r : ℕ → ℤ)
    (hr : ∀ (x d : ℕ), (d : ℤ) ∣ r (x + d) - r x) (c : ℤ) (x d : ℕ) :
    (4 : ℤ) * (d : ℤ) ∣ (c + 4 * r x) - (c + 4 * r (x + d)) := by
  rcases hr x d with ⟨q, hq⟩
  refine ⟨-q, ?_⟩
  calc
    (c + 4 * r x) - (c + 4 * r (x + d)) = -4 * (r (x + d) - r x) := by ring
    _ = (4 : ℤ) * (d : ℤ) * (-q) := by rw [hq]; ring

theorem cross_shift_of_component_shift
    (f : ℕ → Quad4)
    (hre : ∀ (x d : ℕ), (4 : ℤ) * (d : ℤ) ∣ (f x).re - (f (x + d)).re)
    (him : ∀ (x d : ℕ), (4 : ℤ) * (d : ℤ) ∣ (f x).im - (f (x + d)).im)
    (x d : ℕ) :
    (4 : ℤ) * (d : ℤ) ∣ Quad4.cross (f x) (f (x + d)) := by
  have hr := hre x d
  have hi := him x d
  have hcomb : (4 : ℤ) * (d : ℤ) ∣
      ((f x).im - (f (x + d)).im) * (f (x + d)).re -
        ((f x).re - (f (x + d)).re) * (f (x + d)).im :=
    dvd_sub (dvd_mul_of_dvd_left hi _) (dvd_mul_of_dvd_left hr _)
  have heq :
      Quad4.cross (f x) (f (x + d)) =
        ((f x).im - (f (x + d)).im) * (f (x + d)).re -
          ((f x).re - (f (x + d)).re) * (f (x + d)).im := by
    simp only [Quad4.cross]
    ring
  rw [heq]
  exact hcomb

theorem evenSuperBlock_cross_shift (x d : ℕ) :
    (4 : ℤ) * (d : ℤ) ∣ Quad4.cross (evenSuperBlock x) (evenSuperBlock (x + d)) := by
  apply cross_shift_of_component_shift evenSuperBlock
  · intro a b
    simpa [evenSuperBlock, evenA] using
      const_add_four_shift_dvd evenARed evenARed_shift_dvd (-13975) a b
  · intro a b
    have h := const_add_four_shift_dvd evenHRed evenHRed_shift_dvd 2925 a b
    rcases h with ⟨q, hq⟩
    refine ⟨-q, ?_⟩
    change -evenH a - -evenH (a + b) = (4 : ℤ) * (b : ℤ) * (-q)
    change evenH a - evenH (a + b) = (4 : ℤ) * (b : ℤ) * q at hq
    linear_combination -hq

theorem oddSuperBlock_cross_shift (x d : ℕ) :
    (4 : ℤ) * (d : ℤ) ∣ Quad4.cross (oddSuperBlock x) (oddSuperBlock (x + d)) := by
  apply cross_shift_of_component_shift oddSuperBlock
  · intro a b
    simpa [oddSuperBlock, oddA] using
      const_add_four_shift_dvd oddARed oddARed_shift_dvd 25 a b
  · intro a b
    have h := const_add_four_shift_dvd oddHRed oddHRed_shift_dvd (-25) a b
    rcases h with ⟨q, hq⟩
    refine ⟨-q, ?_⟩
    change -oddH a - -oddH (a + b) = (4 : ℤ) * (b : ℤ) * (-q)
    change oddH a - oddH (a + b) = (4 : ℤ) * (b : ℤ) * q at hq
    linear_combination -hq

/- Regrouping the normalized four-term blocks into the two superblock families. -/

theorem normalizedFourBlockProduct_even (q : ℕ) :
    normalizedFourBlockProduct (2 * q) = Quad4.prodFrom evenSuperBlock 0 q := by
  induction q with
  | zero => simp [normalizedFourBlockProduct]
  | succ q ih =>
      rw [normalizedFourBlockProduct] at ih
      rw [show 2 * (q + 1) = 2 * q + 2 by omega]
      rw [normalizedFourBlockProduct, Quad4.prodFrom_add, ih]
      rw [Quad4.prodFrom_succ]
      congr 1
      rw [Quad4.prodFrom_succ, Quad4.prodFrom_zero,
        Quad4.one_mul]
      rw [show 0 + 2 * q + 0 = 2 * q by omega,
        show 0 + 2 * q + 1 = 2 * q + 1 by omega,
        show 0 + q = q by omega]
      exact evenSuperBlock_eq q

theorem oddSuperBlock_tail (q : ℕ) :
    Quad4.prodFrom oddSuperBlock 1 q = Quad4.prodFrom smallBlock 1 (2 * q) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Quad4.prodFrom_succ, ih]
      rw [show 2 * (q + 1) = 2 * q + 2 by omega]
      rw [Quad4.prodFrom_add]
      congr 1
      rw [Quad4.prodFrom_succ]
      rw [Quad4.prodFrom_succ, Quad4.prodFrom_zero, Quad4.one_mul]
      rw [show 1 + q = q + 1 by omega,
        show 1 + 2 * q + 0 = 2 * q + 1 by omega,
        show 1 + 2 * q + 1 = 2 * q + 2 by omega]
      exact (oddSuperBlock_eq_pair q).symm

theorem oddSuperBlock_product (q : ℕ) :
    Quad4.prodFrom oddSuperBlock 0 (q + 1) =
      Quad4.mul ⟨-5, 0⟩ (normalizedFourBlockProduct (2 * q + 1)) := by
  rw [show q + 1 = 1 + q by omega]
  rw [Quad4.prodFrom_add oddSuperBlock 0 1 q]
  rw [show 2 * q + 1 = 1 + 2 * q by omega]
  rw [normalizedFourBlockProduct]
  rw [Quad4.prodFrom_add smallBlock 0 1 (2 * q)]
  rw [oddSuperBlock_tail]
  simp only [Quad4.prodFrom_succ, Quad4.prodFrom_zero, Quad4.one_mul,
    zero_add]
  rw [oddSuperBlock_zero, Quad4.mul_assoc]

theorem exactTwo_normalized_even (q : ℕ) (hq : q ≠ 0) :
    ExactTwo (padicValNat 2 q) (normalizedFourBlockProduct (2 * q)).im := by
  rw [normalizedFourBlockProduct_even]
  exact exactTwo_prodFrom evenSuperBlock evenSuperBlock_re_odd
    evenSuperBlock_im_odd evenSuperBlock_cross_shift 0 q hq

theorem exactTwo_normalized_odd (q : ℕ) :
    ExactTwo (padicValNat 2 (q + 1)) (normalizedFourBlockProduct (2 * q + 1)).im := by
  have hprod := exactTwo_prodFrom oddSuperBlock oddSuperBlock_re_odd
    oddSuperBlock_im_odd oddSuperBlock_cross_shift 0 (q + 1) (by omega)
  rw [oddSuperBlock_product] at hprod
  have him : (Quad4.mul ⟨-5, 0⟩ (normalizedFourBlockProduct (2 * q + 1))).im =
      (normalizedFourBlockProduct (2 * q + 1)).im * (-5) := by
    simp [Quad4.mul]
    ring
  rw [him] at hprod
  exact ExactTwo.of_mul_odd hprod (by norm_num)

/- ## Connection with the Gaussian-integer product defining A105751 -/

def Quad4.toGaussian (z : Quad4) : GaussianInt := ⟨z.re, 4 * z.im⟩

theorem Quad4.toGaussian_mul (z w : Quad4) :
    Quad4.toGaussian (Quad4.mul z w) = Quad4.toGaussian z * Quad4.toGaussian w := by
  ext <;> simp [Quad4.toGaussian, Quad4.mul] <;> ring

def gaussianFactor (n : ℕ) : GaussianInt := ⟨1, n⟩

def gaussianProduct (n : ℕ) : GaussianInt :=
  (Finset.range (n + 1)).prod gaussianFactor

theorem gaussianProduct_toComplex (n : ℕ) :
    ((gaussianProduct n : GaussianInt) : ℂ) =
      (Finset.range (n + 1)).prod (fun k : ℕ ↦ 1 + (k : ℂ) * I) := by
  simp [gaussianProduct, gaussianFactor, map_prod, GaussianInt.toComplex_def]

theorem sequenceA_eq_gaussianProduct_im (n : ℕ) :
    OeisA105751.a n = (gaussianProduct n).im := by
  rw [OeisA105751.a]
  rw [← gaussianProduct_toComplex]
  simpa using (Int.floor_intCast (R := ℝ) (gaussianProduct n).im)

theorem gaussianProduct_succ (n : ℕ) :
    gaussianProduct (n + 1) = gaussianProduct n * gaussianFactor (n + 1) := by
  simp [gaussianProduct, Finset.prod_range_succ]

theorem gaussianFourBlock (m : ℕ) :
    gaussianFactor (4 * m + 1) * gaussianFactor (4 * m + 2) *
        gaussianFactor (4 * m + 3) * gaussianFactor (4 * m + 4) =
      (2 : GaussianInt) * Quad4.toGaussian (smallBlock m) := by
  ext <;>
    simp [gaussianFactor, Quad4.toGaussian, smallBlock, blockE, blockF] <;>
    ring

theorem normalizedFourBlockProduct_succ (m : ℕ) :
    normalizedFourBlockProduct (m + 1) =
      Quad4.mul (normalizedFourBlockProduct m) (smallBlock m) := by
  simp [normalizedFourBlockProduct, Quad4.prodFrom_succ]

theorem gaussianProduct_four (m : ℕ) :
    gaussianProduct (4 * m) =
      (2 : GaussianInt) ^ m * Quad4.toGaussian (normalizedFourBlockProduct m) := by
  induction m with
  | zero =>
      norm_num [gaussianProduct, gaussianFactor, normalizedFourBlockProduct,
        Quad4.prodFrom, Quad4.toGaussian]
  | succ m ih =>
      have hstep : gaussianProduct (4 * (m + 1)) =
          gaussianProduct (4 * m) * gaussianFactor (4 * m + 1) *
            gaussianFactor (4 * m + 2) * gaussianFactor (4 * m + 3) *
              gaussianFactor (4 * m + 4) := by
        rw [show 4 * (m + 1) = (((4 * m + 1) + 1) + 1) + 1 by omega]
        rw [gaussianProduct_succ, gaussianProduct_succ, gaussianProduct_succ,
          gaussianProduct_succ]
      rw [hstep, ih]
      rw [normalizedFourBlockProduct_succ, Quad4.toGaussian_mul]
      rw [show
        (2 : GaussianInt) ^ m * Quad4.toGaussian (normalizedFourBlockProduct m) *
              gaussianFactor (4 * m + 1) * gaussianFactor (4 * m + 2) *
                gaussianFactor (4 * m + 3) * gaussianFactor (4 * m + 4) =
            ((2 : GaussianInt) ^ m * Quad4.toGaussian (normalizedFourBlockProduct m)) *
              (gaussianFactor (4 * m + 1) * gaussianFactor (4 * m + 2) *
                gaussianFactor (4 * m + 3) * gaussianFactor (4 * m + 4)) by ring]
      rw [gaussianFourBlock]
      simp only [pow_succ]
      ring

@[simp] theorem gaussian_two_pow (m : ℕ) :
    (2 : GaussianInt) ^ m = ⟨(2 : ℤ) ^ m, 0⟩ := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [pow_succ, ih]
      ext <;> simp [pow_succ]

theorem sequenceA_four (m : ℕ) :
    OeisA105751.a (4 * m) =
      (2 : ℤ) ^ (m + 2) * (normalizedFourBlockProduct m).im := by
  rw [sequenceA_eq_gaussianProduct_im, gaussianProduct_four]
  simp [Quad4.toGaussian, pow_add]
  ring

theorem sequenceA_four_add_one (m : ℕ) :
    OeisA105751.a (4 * m + 1) = (2 : ℤ) ^ m *
      ((4 * (m : ℤ) + 1) * (normalizedFourBlockProduct m).re +
        4 * (normalizedFourBlockProduct m).im) := by
  rw [sequenceA_eq_gaussianProduct_im]
  rw [show 4 * m + 1 = 4 * m + 1 by rfl, gaussianProduct_succ]
  rw [gaussianProduct_four]
  simp [gaussianFactor, Quad4.toGaussian]
  ring

theorem sequenceA_four_add_two (m : ℕ) :
    OeisA105751.a (4 * m + 2) = (2 : ℤ) ^ m *
      ((8 * (m : ℤ) + 3) * (normalizedFourBlockProduct m).re -
        4 * (16 * (m : ℤ) ^ 2 + 12 * (m : ℤ) + 1) *
          (normalizedFourBlockProduct m).im) := by
  rw [sequenceA_eq_gaussianProduct_im]
  rw [show 4 * m + 2 = (4 * m + 1) + 1 by omega]
  rw [gaussianProduct_succ, gaussianProduct_succ, gaussianProduct_four]
  simp [gaussianFactor, Quad4.toGaussian]
  ring

theorem sequenceA_four_add_three (m : ℕ) :
    OeisA105751.a (4 * m + 3) = -(2 : ℤ) ^ (m + 3) *
      ((24 * (m : ℤ) ^ 2 + 24 * (m : ℤ) + 5) *
          (normalizedFourBlockProduct m).im +
        4 * (m : ℤ) * ((m : ℤ) + 1) * (2 * (m : ℤ) + 1) *
          (normalizedFourBlockProduct m).re) := by
  rw [sequenceA_eq_gaussianProduct_im]
  rw [show 4 * m + 3 = ((4 * m + 1) + 1) + 1 by omega]
  rw [gaussianProduct_succ, gaussianProduct_succ, gaussianProduct_succ,
    gaussianProduct_four]
  simp [gaussianFactor, Quad4.toGaussian, pow_add]
  ring

/- ## Exact valuations in the four residue classes -/

theorem ExactTwo.pow_mul_left {k : ℕ} {z : ℤ} (hz : ExactTwo k z) (r : ℕ) :
    ExactTwo (r + k) ((2 : ℤ) ^ r * z) := by
  rcases hz with ⟨u, hu, rfl⟩
  refine ⟨u, hu, ?_⟩
  rw [pow_add]
  ring

theorem ExactTwo.add_higher {k : ℕ} {z t c : ℤ}
    (hz : ExactTwo k z) (hc : Odd c) (ht : (2 : ℤ) ^ (k + 1) ∣ t) :
    ExactTwo k (c * z + t) := by
  rcases hz with ⟨u, hu, rfl⟩
  rcases ht with ⟨v, rfl⟩
  refine ⟨c * u + 2 * v, (hc.mul hu).add_even ⟨v, by ring⟩, ?_⟩
  rw [pow_succ]
  ring

theorem exactTwo_normalized_half (m : ℕ) (hm : m ≠ 0) :
    ExactTwo (padicValNat 2 ((m + 1) / 2))
      (normalizedFourBlockProduct m).im := by
  obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' m
  · subst m
    have hq0 : q ≠ 0 := by omega
    have h := exactTwo_normalized_even q hq0
    have hhalf : (2 * q + 1) / 2 = q := by omega
    rwa [hhalf]
  · subst m
    have h := exactTwo_normalized_odd q
    have hhalf : (2 * q + 1 + 1) / 2 = q + 1 := by omega
    rwa [hhalf]

theorem twice_half_dvd_consecutive (m : ℕ) :
    (2 : ℤ) * (((m + 1) / 2 : ℕ) : ℤ) ∣ (m : ℤ) * ((m : ℤ) + 1) := by
  obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' m
  · subst m
    have hhalf : (2 * q + 1) / 2 = q := by omega
    rw [hhalf]
    refine ⟨(2 * q + 1 : ℕ), ?_⟩
    norm_num
  · subst m
    have hhalf : (2 * q + 1 + 1) / 2 = q + 1 := by omega
    rw [hhalf]
    refine ⟨(2 * q + 1 : ℕ), ?_⟩
    norm_num
    ring

theorem higher_term_dvd (m : ℕ) :
    (2 : ℤ) ^ (padicValNat 2 ((m + 1) / 2) + 1) ∣
      4 * (m : ℤ) * ((m : ℤ) + 1) * (2 * (m : ℤ) + 1) *
        (normalizedFourBlockProduct m).re := by
  let h := (m + 1) / 2
  let k := padicValNat 2 h
  have hpowNat : 2 ^ k ∣ h := pow_padicValNat_dvd (p := 2) (n := h)
  have hpow : (2 : ℤ) ^ k ∣ (h : ℤ) := by exact_mod_cast hpowNat
  have hpair : (2 : ℤ) * (h : ℤ) ∣ (m : ℤ) * ((m : ℤ) + 1) := by
    simpa [h] using twice_half_dvd_consecutive m
  rcases hpow with ⟨d, hd⟩
  rcases hpair with ⟨e, he⟩
  refine ⟨4 * d * e * (2 * (m : ℤ) + 1) *
    (normalizedFourBlockProduct m).re, ?_⟩
  change 4 * (m : ℤ) * ((m : ℤ) + 1) * (2 * (m : ℤ) + 1) *
      (normalizedFourBlockProduct m).re = (2 : ℤ) ^ (k + 1) * _
  calc
    4 * (m : ℤ) * ((m : ℤ) + 1) * (2 * (m : ℤ) + 1) *
        (normalizedFourBlockProduct m).re =
      4 * ((m : ℤ) * ((m : ℤ) + 1)) * (2 * (m : ℤ) + 1) *
        (normalizedFourBlockProduct m).re := by ring
    _ = (2 : ℤ) ^ (k + 1) *
        (4 * d * e * (2 * (m : ℤ) + 1) *
          (normalizedFourBlockProduct m).re) := by
      rw [he, hd, pow_succ]
      ring

theorem exactTwo_sequenceA_four (m : ℕ) (hm : m ≠ 0) :
    ExactTwo (m + 2 + padicValNat 2 ((m + 1) / 2)) (OeisA105751.a (4 * m)) := by
  rw [sequenceA_four]
  exact (exactTwo_normalized_half m hm).pow_mul_left (m + 2)

theorem exactTwo_sequenceA_four_add_one (m : ℕ) :
    ExactTwo m (OeisA105751.a (4 * m + 1)) := by
  rw [sequenceA_four_add_one]
  apply ExactTwo.pow_mul_left (k := 0) (r := m)
  rw [exactTwo_zero_iff_odd]
  apply Odd.add_even
  · have hre : Odd (normalizedFourBlockProduct m).re := by
      exact Quad4.odd_re_prodFrom smallBlock smallBlock_re_odd 0 m
    exact (show Odd (4 * (m : ℤ) + 1) from ⟨2 * (m : ℤ), by ring⟩).mul hre
  · exact ⟨2 * (normalizedFourBlockProduct m).im, by ring⟩

theorem exactTwo_sequenceA_four_add_two (m : ℕ) :
    ExactTwo m (OeisA105751.a (4 * m + 2)) := by
  rw [sequenceA_four_add_two]
  apply ExactTwo.pow_mul_left (k := 0) (r := m)
  rw [exactTwo_zero_iff_odd]
  apply Odd.sub_even
  · exact (show Odd (8 * (m : ℤ) + 3) from ⟨4 * (m : ℤ) + 1, by ring⟩).mul
      (by exact Quad4.odd_re_prodFrom smallBlock smallBlock_re_odd 0 m)
  · exact ⟨2 * (16 * (m : ℤ) ^ 2 + 12 * (m : ℤ) + 1) *
      (normalizedFourBlockProduct m).im, by ring⟩

theorem exactTwo_sequenceA_four_add_three (m : ℕ) (hm : m ≠ 0) :
    ExactTwo (m + 3 + padicValNat 2 ((m + 1) / 2))
      (OeisA105751.a (4 * m + 3)) := by
  rw [sequenceA_four_add_three]
  have hbracket : ExactTwo (padicValNat 2 ((m + 1) / 2))
      ((24 * (m : ℤ) ^ 2 + 24 * (m : ℤ) + 5) *
          (normalizedFourBlockProduct m).im +
        4 * (m : ℤ) * ((m : ℤ) + 1) * (2 * (m : ℤ) + 1) *
          (normalizedFourBlockProduct m).re) := by
    apply ExactTwo.add_higher (exactTwo_normalized_half m hm)
    · exact ⟨12 * (m : ℤ) ^ 2 + 12 * (m : ℤ) + 2, by ring⟩
    · exact higher_term_dvd m
  have hpos := hbracket.pow_mul_left (m + 3)
  simpa only [neg_mul] using hpos.neg

end A105751Proof

open A105751Proof in
theorem OMA.solution : OMA.R_OeisA105751_conjecture_variants_moll_p_mod_4_eq_1_R1.H2 := by
  intro n hn
  let m := n / 4
  have hm : m ≠ 0 := by dsimp [m]; omega
  have cases : n = 4 * m ∨ n = 4 * m + 1 ∨ n = 4 * m + 2 ∨ n = 4 * m + 3 := by
    dsimp [m]
    omega
  rcases cases with h | h | h | h <;> rw [h]
  · exact (exactTwo_sequenceA_four m hm).nonzero
  · exact (exactTwo_sequenceA_four_add_one m).nonzero
  · exact (exactTwo_sequenceA_four_add_two m).nonzero
  · exact (exactTwo_sequenceA_four_add_three m hm).nonzero

/- License for the adapted exact-valuation proof.

Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      “License” shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      “Licensor” shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      “Legal Entity” shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      “control” means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      “You” (or “Your”) shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      “Source” form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      “Object” form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      “Work” shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      “Derivative Works” shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      “Contribution” shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, “submitted”
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as “Not a Contribution.”

      “Contributor” shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a “NOTICE” text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an “AS IS” BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS
-/
