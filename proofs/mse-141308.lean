import OMAStatements.S_mse_141308
import Mathlib

namespace Proof_mse_141308

private def uVal (n : ℕ) : ℕ :=
  if n % 12 = 8 then 37 else if n % 4 = 1 then 32 else if n % 12 = 2 then 12 else 28

private lemma seed_eq_cubic (n : ℕ) :
    (OMA.S_mse_141308.seed n : ℤ) = (uVal n : ℤ) ^ 3 - 3 * (uVal n : ℤ) := by
  unfold OMA.S_mse_141308.seed uVal
  split_ifs <;> norm_num

private lemma S_cast_eq {N q : ℕ} (s : ℕ) (hq : q ∣ N) (i : ℕ) :
    ZMod.castHom hq (ZMod q) (OMA.S_mse_141308.S N s i) = OMA.S_mse_141308.S q s i := by
  induction i with
  | zero =>
    change ZMod.castHom hq (ZMod q) (s : ZMod N) = (s : ZMod q)
    exact map_natCast (ZMod.castHom hq (ZMod q)) s
  | succ i ih =>
    change ZMod.castHom hq (ZMod q) (OMA.S_mse_141308.S N s i ^ 2 - 2) =
      OMA.S_mse_141308.S q s i ^ 2 - 2
    rw [map_sub, map_pow, map_ofNat, ih]

private lemma S_eq_pow_add_inv {R : Type*} [CommRing R] (s : ℕ) (a b : R)
    (hab : a * b = 1) (hadd : a + b = (s : R)) (i : ℕ) (N : ℕ)
    (f : ZMod N →+* R) :
    f (OMA.S_mse_141308.S N s i) = a ^ (2 ^ i) + b ^ (2 ^ i) := by
  induction i with
  | zero =>
    change f (s : ZMod N) = a ^ 1 + b ^ 1
    rw [map_natCast, pow_one, pow_one, hadd]
  | succ i ih =>
    change f (OMA.S_mse_141308.S N s i ^ 2 - 2) = a ^ (2 ^ (i + 1)) + b ^ (2 ^ (i + 1))
    rw [map_sub, map_pow, map_ofNat, ih]
    have hmul : a ^ (2 ^ i) * b ^ (2 ^ i) = 1 := by
      rw [← mul_pow, hab, one_pow]
    calc (a ^ (2 ^ i) + b ^ (2 ^ i)) ^ 2 - 2
        = (a ^ (2 ^ i)) ^ 2 + (b ^ (2 ^ i)) ^ 2 + 2 * (a ^ (2 ^ i) * b ^ (2 ^ i)) - 2 := by ring
      _ = (a ^ (2 ^ i)) ^ 2 + (b ^ (2 ^ i)) ^ 2 := by rw [hmul]; ring
      _ = a ^ (2 ^ (i + 1)) + b ^ (2 ^ (i + 1)) := by rw [← pow_mul, ← pow_mul, ← pow_succ]

/-- Concrete quadratic extension `ZMod q [√D]` with multiplication `(a,b)*(c,d) = (ac + Dbd, ad + bc)`. -/
private structure QuadExt (q : ℕ) (D : ZMod q) where
  re : ZMod q
  im : ZMod q

namespace QuadExt

variable {q : ℕ} {D : ZMod q}

private lemma eq_of_re_im {x y : QuadExt q D} (h1 : x.re = y.re) (h2 : x.im = y.im) : x = y := by
  cases x; cases y; congr

private instance : Zero (QuadExt q D) := ⟨⟨0, 0⟩⟩
private instance : One (QuadExt q D) := ⟨⟨1, 0⟩⟩
private instance : Add (QuadExt q D) := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
private instance : Neg (QuadExt q D) := ⟨fun x => ⟨-x.re, -x.im⟩⟩
private instance : Sub (QuadExt q D) := ⟨fun x y => ⟨x.re - y.re, x.im - y.im⟩⟩
private instance : Mul (QuadExt q D) :=
  ⟨fun x y => ⟨x.re * y.re + D * x.im * y.im, x.re * y.im + x.im * y.re⟩⟩
private instance : NatCast (QuadExt q D) := ⟨fun n => ⟨(n : ZMod q), 0⟩⟩
private instance : IntCast (QuadExt q D) := ⟨fun z => ⟨(z : ZMod q), 0⟩⟩

private lemma zero_re : (0 : QuadExt q D).re = 0 := rfl
private lemma zero_im : (0 : QuadExt q D).im = 0 := rfl
private lemma one_re : (1 : QuadExt q D).re = 1 := rfl
private lemma one_im : (1 : QuadExt q D).im = 0 := rfl
private lemma add_re (x y : QuadExt q D) : (x + y).re = x.re + y.re := rfl
private lemma add_im (x y : QuadExt q D) : (x + y).im = x.im + y.im := rfl
private lemma neg_re (x : QuadExt q D) : (-x).re = -x.re := rfl
private lemma neg_im (x : QuadExt q D) : (-x).im = -x.im := rfl
private lemma sub_re (x y : QuadExt q D) : (x - y).re = x.re - y.re := rfl
private lemma sub_im (x y : QuadExt q D) : (x - y).im = x.im - y.im := rfl
private lemma mul_re (x y : QuadExt q D) : (x * y).re = x.re * y.re + D * x.im * y.im := rfl
private lemma mul_im (x y : QuadExt q D) : (x * y).im = x.re * y.im + x.im * y.re := rfl
private lemma natCast_re (n : ℕ) : (n : QuadExt q D).re = (n : ZMod q) := rfl
private lemma natCast_im (n : ℕ) : (n : QuadExt q D).im = 0 := rfl
private lemma intCast_re (z : ℤ) : (z : QuadExt q D).re = (z : ZMod q) := rfl
private lemma intCast_im (z : ℤ) : (z : QuadExt q D).im = 0 := rfl

private instance : CommRing (QuadExt q D) where
  add_assoc a b c := eq_of_re_im (by simp only [add_re]; ring) (by simp only [add_im]; ring)
  zero_add a := eq_of_re_im (by simp only [add_re, zero_re]; ring) (by simp only [add_im, zero_im]; ring)
  add_zero a := eq_of_re_im (by simp only [add_re, zero_re]; ring) (by simp only [add_im, zero_im]; ring)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_comm a b := eq_of_re_im (by simp only [add_re]; ring) (by simp only [add_im]; ring)
  neg_add_cancel a := eq_of_re_im (by simp only [add_re, neg_re, zero_re]; ring)
    (by simp only [add_im, neg_im, zero_im]; ring)
  sub_eq_add_neg a b := eq_of_re_im (by simp only [sub_re, add_re, neg_re]; ring)
    (by simp only [sub_im, add_im, neg_im]; ring)
  mul_assoc a b c := eq_of_re_im (by simp only [mul_re, mul_im]; ring)
    (by simp only [mul_re, mul_im]; ring)
  one_mul a := eq_of_re_im (by simp only [mul_re, one_re, one_im]; ring)
    (by simp only [mul_im, one_re, one_im]; ring)
  mul_one a := eq_of_re_im (by simp only [mul_re, one_re, one_im]; ring)
    (by simp only [mul_im, one_re, one_im]; ring)
  zero_mul a := eq_of_re_im (by simp only [mul_re, zero_re, zero_im]; ring)
    (by simp only [mul_im, zero_re, zero_im]; ring)
  mul_zero a := eq_of_re_im (by simp only [mul_re, zero_re, zero_im]; ring)
    (by simp only [mul_im, zero_re, zero_im]; ring)
  left_distrib a b c := eq_of_re_im (by simp only [mul_re, add_re, add_im]; ring)
    (by simp only [mul_im, add_re, add_im]; ring)
  right_distrib a b c := eq_of_re_im (by simp only [mul_re, add_re, add_im]; ring)
    (by simp only [mul_im, add_re, add_im]; ring)
  mul_comm a b := eq_of_re_im (by simp only [mul_re]; ring) (by simp only [mul_im]; ring)
  natCast_zero := eq_of_re_im (by rw [natCast_re, zero_re, Nat.cast_zero]) rfl
  natCast_succ n := eq_of_re_im (by rw [natCast_re, add_re, natCast_re, one_re, Nat.cast_succ])
    (by rw [natCast_im, add_im, natCast_im, one_im, add_zero])
  intCast_ofNat n := eq_of_re_im (by rw [intCast_re, natCast_re, Int.cast_natCast]) rfl
  intCast_negSucc n := eq_of_re_im
    (by rw [intCast_re, neg_re, natCast_re, Int.cast_negSucc])
    (by rw [intCast_im, neg_im, natCast_im, neg_zero])

private def ofBase : ZMod q →+* QuadExt q D where
  toFun a := ⟨a, 0⟩
  map_one' := rfl
  map_mul' a b := eq_of_re_im (by simp only [mul_re]; ring) (by simp only [mul_im]; ring)
  map_zero' := rfl
  map_add' a b := eq_of_re_im rfl (by simp only [add_im]; ring)

private lemma ofBase_pow (a : ZMod q) (k : ℕ) : (⟨a, 0⟩ : QuadExt q D) ^ k = ⟨a ^ k, 0⟩ :=
  (map_pow (ofBase (D := D)) a k).symm

private lemma charP [NeZero q] : CharP (QuadExt q D) q := by
  constructor
  intro k
  constructor
  · intro hk
    have hre : (k : ZMod q) = 0 := congrArg QuadExt.re hk
    exact (ZMod.natCast_eq_zero_iff k q).mp hre
  · intro hk
    exact eq_of_re_im ((ZMod.natCast_eq_zero_iff k q).mpr hk) rfl

private lemma sqrt_sq : (⟨0, 1⟩ : QuadExt q D) ^ 2 = ⟨D, 0⟩ := by
  rw [sq]
  exact eq_of_re_im (by simp only [mul_re]; ring) (by simp only [mul_im]; ring)

private lemma sqrt_odd_pow (k : ℕ) :
    (⟨0, 1⟩ : QuadExt q D) ^ (2 * k + 1) = ⟨0, D ^ k⟩ := by
  rw [pow_succ, pow_mul, sqrt_sq, ofBase_pow]
  exact eq_of_re_im (by simp only [mul_re]; ring) (by simp only [mul_im]; ring)

private lemma frobenius [hp : Fact q.Prime] (hq2 : q ≠ 2) (hD : D ^ ((q - 1) / 2) = -1)
    (x : QuadExt q D) : x ^ q = ⟨x.re, -x.im⟩ := by
  have hcp : CharP (QuadExt q D) q := charP
  have hx : x = ⟨x.re, 0⟩ + ⟨x.im, 0⟩ * ⟨0, 1⟩ :=
    eq_of_re_im (by simp only [add_re, mul_re]; ring) (by simp only [add_im, mul_im]; ring)
  rw [hx, add_pow_char, mul_pow, ofBase_pow, ofBase_pow, ZMod.pow_card, ZMod.pow_card]
  have hodd : q = 2 * ((q - 1) / 2) + 1 := by
    rcases hp.out.eq_two_or_odd with rfl | hodd
    · exact absurd rfl hq2
    · omega
  have hsqq : (⟨0, 1⟩ : QuadExt q D) ^ q = ⟨0, -1⟩ := by
    rw [congrArg (fun m => (⟨0, 1⟩ : QuadExt q D) ^ m) hodd, sqrt_odd_pow, hD]
  rw [hsqq]
  exact eq_of_re_im (by simp only [add_re, mul_re]; ring) (by simp only [add_im, mul_im]; ring)

end QuadExt

private lemma legendre_cases (p : ℕ) [Fact p.Prime] (a : ℤ) :
    legendreSym p a = 0 ∨ legendreSym p a = 1 ∨ legendreSym p a = -1 := by
  unfold legendreSym
  rw [quadraticChar_apply, quadraticCharFun]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

private lemma euler_non_square {q : ℕ} [hp : Fact q.Prime] (hq2 : q ≠ 2) {D : ZMod q}
    (hnsq : ¬ IsSquare D) : D ^ ((q - 1) / 2) = -1 := by
  have hD0 : D ≠ 0 := by
    intro h0; exact hnsq ⟨0, by simp [h0]⟩
  have hodd : 2 * ((q - 1) / 2) = q - 1 := by
    rcases hp.out.eq_two_or_odd with rfl | hodd
    · exact absurd rfl hq2
    · omega
  have hsq : (D ^ ((q - 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, hodd]
    exact ZMod.pow_card_sub_one_eq_one hD0
  have hpm : D ^ ((q - 1) / 2) = 1 ∨ D ^ ((q - 1) / 2) = -1 := sq_eq_one_iff.mp hsq
  rcases hpm with h1 | hm1
  · exfalso
    have hqdiv : q / 2 = (q - 1) / 2 := by
      rcases hp.out.eq_two_or_odd with rfl | hodd
      · exact absurd rfl hq2
      · omega
    have hleg_cast : (legendreSym q (D.val : ℤ) : ZMod q) = 1 := by
      rw [legendreSym.eq_pow, hqdiv, Int.cast_natCast, ZMod.natCast_zmod_val, h1]
    have hleg_ne_neg1 : legendreSym q (D.val : ℤ) ≠ -1 := by
      intro hm
      rw [hm] at hleg_cast
      have h2zero : (2 : ZMod q) = 0 := by
        have : (-1 : ZMod q) = 1 := by simpa using hleg_cast
        linear_combination -this
      have hdvd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp h2zero
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      have h2le := hp.out.two_le
      omega
    have hleg_ne_zero : legendreSym q (D.val : ℤ) ≠ 0 := by
      intro hz
      rw [hz, Int.cast_zero] at hleg_cast
      exact zero_ne_one hleg_cast
    have hleg1 : legendreSym q (D.val : ℤ) = 1 := by
      rcases legendre_cases q (D.val : ℤ) with h | h | h
      · exact absurd h hleg_ne_zero
      · exact h
      · exact absurd h hleg_ne_neg1
    have hsqz : IsSquare ((D.val : ℤ) : ZMod q) := (legendreSym.eq_one_iff q (by
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]; exact hD0)).mp hleg1
    rw [Int.cast_natCast, ZMod.natCast_zmod_val] at hsqz
    exact hnsq hsqz
  · exact hm1

private lemma order_two_pow_of_half_eq_neg_one {G : Type*} [Group G] (x : G) (n : ℕ)
    (hn : 1 ≤ n) (hneg : x ^ (2 ^ (n - 1)) ≠ 1) (hone : x ^ (2 ^ n) = 1) :
    orderOf x = 2 ^ n := by
  have hdvd : orderOf x ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hone
  rw [Nat.dvd_prime_pow Nat.prime_two] at hdvd
  obtain ⟨k, hk, hord⟩ := hdvd
  have hkn : k = n := by
    by_contra hne
    have hlt : k ≤ n - 1 := by omega
    have hdiv : 2 ^ k ∣ 2 ^ (n - 1) := Nat.pow_dvd_pow 2 hlt
    rw [← hord] at hdiv
    exact hneg (orderOf_dvd_iff_pow_eq_one.mp hdiv)
  rw [hord, hkn]

private lemma prime_divisor_ge_of_S_zero {N s n q : ℕ} (hn : 3 ≤ n) (hN : N = 3 * 2 ^ n + 1)
    (hq : q.Prime) (hqN : q ∣ N) (hS : OMA.S_mse_141308.S N s (n - 2) = 0) : 2 ^ n - 1 ≤ q := by
  have hfact : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := by
    intro h2
    subst h2
    have heven : 2 ∣ 3 * 2 ^ n + 1 := hN ▸ hqN
    have h2pow : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have : 2 ∣ 1 := (Nat.dvd_add_right (dvd_mul_of_dvd_right h2pow 3)).mp heven
    omega
  have h2ne : (2 : ZMod q) ≠ 0 := by
    intro h0
    have : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp h0
    have := Nat.le_of_dvd (by norm_num) this
    have := hq.two_le
    omega
  have hSq : OMA.S_mse_141308.S q s (n - 2) = 0 := by
    have := S_cast_eq s hqN (n - 2)
    rw [hS, map_zero] at this
    exact this.symm
  have hm1ne1 : (-1 : ZMod q) ≠ 1 := by
    intro h
    have : (2 : ZMod q) = 0 := by linear_combination -h
    exact h2ne this
  by_cases hsq : IsSquare (((s : ZMod q) ^ 2 - 4))
  · obtain ⟨w, hw⟩ := hsq
    set a : ZMod q := ((s : ZMod q) + w) * (2 : ZMod q)⁻¹
    set b : ZMod q := ((s : ZMod q) - w) * (2 : ZMod q)⁻¹
    have hab : a * b = 1 := by
      have h2inv : (2 : ZMod q) * (2 : ZMod q)⁻¹ = 1 := mul_inv_cancel₀ h2ne
      have hws : w * w = (s : ZMod q) ^ 2 - 4 := hw.symm
      calc a * b = ((s : ZMod q) ^ 2 - w * w) * ((2 : ZMod q)⁻¹ * (2 : ZMod q)⁻¹) := by ring
        _ = 4 * ((2 : ZMod q)⁻¹ * (2 : ZMod q)⁻¹) := by rw [hws]; ring
        _ = ((2 : ZMod q) * (2 : ZMod q)⁻¹) * ((2 : ZMod q) * (2 : ZMod q)⁻¹) := by ring
        _ = 1 := by rw [h2inv]; ring
    have hadd : a + b = (s : ZMod q) := by
      have h2inv : (2 : ZMod q) * (2 : ZMod q)⁻¹ = 1 := mul_inv_cancel₀ h2ne
      calc a + b = (s : ZMod q) * ((2 : ZMod q) * (2 : ZMod q)⁻¹) := by ring
        _ = (s : ZMod q) := by rw [h2inv, mul_one]
    have hSval : OMA.S_mse_141308.S q s (n - 2) = a ^ (2 ^ (n - 2)) + b ^ (2 ^ (n - 2)) :=
      S_eq_pow_add_inv s a b hab hadd (n - 2) q (RingHom.id (ZMod q))
    rw [hSq] at hSval
    have hpow_neg1 : a ^ (2 ^ (n - 1)) = -1 := by
      have hmul : a ^ (2 ^ (n - 2)) * b ^ (2 ^ (n - 2)) = 1 := by
        rw [← mul_pow, hab, one_pow]
      have h2n : 2 ^ (n - 1) = 2 ^ (n - 2) + 2 ^ (n - 2) := by
        rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]; ring
      rw [h2n, pow_add]
      have h0 := congrArg (a ^ (2 ^ (n - 2)) * ·) hSval.symm
      simp only [mul_zero, mul_add, hmul] at h0
      linear_combination h0
    have hpow_one : a ^ (2 ^ n) = 1 := by
      rw [show n = (n - 1) + 1 by omega, pow_succ, pow_mul, hpow_neg1]
      ring
    have ha0 : a ≠ 0 := by
      intro ha; rw [ha, zero_mul] at hab; exact zero_ne_one hab
    let u : (ZMod q)ˣ := Units.mk0 a ha0
    have hu_neg : u ^ (2 ^ (n - 1)) ≠ 1 := by
      intro h
      have hv : a ^ (2 ^ (n - 1)) = 1 := by simpa [u] using congrArg Units.val h
      rw [hpow_neg1] at hv
      exact hm1ne1 hv
    have hu_one : u ^ (2 ^ n) = 1 := by
      apply Units.ext
      simpa [u] using hpow_one
    have hord : orderOf u = 2 ^ n :=
      order_two_pow_of_half_eq_neg_one u n (by omega) hu_neg hu_one
    have hdvd : 2 ^ n ∣ q - 1 := by
      have hcard : Fintype.card (ZMod q)ˣ = q - 1 := by
        rw [ZMod.card_units_eq_totient, Nat.totient_prime hq]
      rw [← hord, ← hcard]
      exact orderOf_dvd_card
    have hpos : 0 < q - 1 := by
      have := hq.two_le; omega
    have hle : 2 ^ n ≤ q - 1 := Nat.le_of_dvd hpos hdvd
    omega
  · set D : ZMod q := (s : ZMod q) ^ 2 - 4
    have hDeul : D ^ ((q - 1) / 2) = -1 := euler_non_square hq2 hsq
    set a : QuadExt q D := ⟨(s : ZMod q) * (2 : ZMod q)⁻¹, (2 : ZMod q)⁻¹⟩
    set b : QuadExt q D := ⟨(s : ZMod q) * (2 : ZMod q)⁻¹, -(2 : ZMod q)⁻¹⟩
    have h2inv : (2 : ZMod q) * (2 : ZMod q)⁻¹ = 1 := mul_inv_cancel₀ h2ne
    have hab : a * b = 1 := by
      apply QuadExt.eq_of_re_im
      · rw [QuadExt.mul_re, QuadExt.one_re]
        show (s : ZMod q) * (2 : ZMod q)⁻¹ * ((s : ZMod q) * (2 : ZMod q)⁻¹) +
          ((s : ZMod q) ^ 2 - 4) * (2 : ZMod q)⁻¹ * -(2 : ZMod q)⁻¹ = 1
        calc (s : ZMod q) * (2 : ZMod q)⁻¹ * ((s : ZMod q) * (2 : ZMod q)⁻¹) +
              ((s : ZMod q) ^ 2 - 4) * (2 : ZMod q)⁻¹ * -(2 : ZMod q)⁻¹
            = ((2 : ZMod q) * (2 : ZMod q)⁻¹) * ((2 : ZMod q) * (2 : ZMod q)⁻¹) := by ring
          _ = 1 := by rw [h2inv]; ring
      · rw [QuadExt.mul_im, QuadExt.one_im]
        show (s : ZMod q) * (2 : ZMod q)⁻¹ * -(2 : ZMod q)⁻¹ +
          (2 : ZMod q)⁻¹ * ((s : ZMod q) * (2 : ZMod q)⁻¹) = 0
        ring
    have hadd : a + b = (s : QuadExt q D) := by
      apply QuadExt.eq_of_re_im
      · rw [QuadExt.add_re, QuadExt.natCast_re]
        show (s : ZMod q) * (2 : ZMod q)⁻¹ + (s : ZMod q) * (2 : ZMod q)⁻¹ = (s : ZMod q)
        calc (s : ZMod q) * (2 : ZMod q)⁻¹ + (s : ZMod q) * (2 : ZMod q)⁻¹
            = (s : ZMod q) * ((2 : ZMod q) * (2 : ZMod q)⁻¹) := by ring
          _ = (s : ZMod q) := by rw [h2inv, mul_one]
      · rw [QuadExt.add_im, QuadExt.natCast_im]
        show (2 : ZMod q)⁻¹ + -(2 : ZMod q)⁻¹ = 0
        ring
    have hSval : QuadExt.ofBase (D := D) (OMA.S_mse_141308.S q s (n - 2)) =
        a ^ (2 ^ (n - 2)) + b ^ (2 ^ (n - 2)) :=
      S_eq_pow_add_inv s a b hab hadd (n - 2) q (QuadExt.ofBase (D := D))
    rw [hSq, map_zero] at hSval
    have hpow_neg1 : a ^ (2 ^ (n - 1)) = -1 := by
      have hmul : a ^ (2 ^ (n - 2)) * b ^ (2 ^ (n - 2)) = 1 := by
        rw [← mul_pow, hab, one_pow]
      have h2n : 2 ^ (n - 1) = 2 ^ (n - 2) + 2 ^ (n - 2) := by
        rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]; ring
      rw [h2n, pow_add]
      have h0 := congrArg (a ^ (2 ^ (n - 2)) * ·) hSval.symm
      simp only [mul_zero, mul_add, hmul] at h0
      linear_combination h0
    have hpow_one : a ^ (2 ^ n) = 1 := by
      rw [show n = (n - 1) + 1 by omega, pow_succ, pow_mul, hpow_neg1]
      ring
    have hfrob : a ^ q = b := QuadExt.frobenius hq2 hDeul a
    have hpow_q1 : a ^ (q + 1) = 1 := by
      rw [pow_succ, hfrob, mul_comm, hab]
    let u : (QuadExt q D)ˣ :=
      ⟨a, b, hab, by rw [mul_comm]; exact hab⟩
    have hu_neg : u ^ (2 ^ (n - 1)) ≠ 1 := by
      intro h
      have hv : a ^ (2 ^ (n - 1)) = 1 := by simpa [u] using congrArg Units.val h
      rw [hpow_neg1] at hv
      have hre : (-1 : ZMod q) = 1 := congrArg QuadExt.re hv
      exact hm1ne1 hre
    have hu_one : u ^ (2 ^ n) = 1 := by
      apply Units.ext
      simpa [u] using hpow_one
    have hu_q1 : u ^ (q + 1) = 1 := by
      apply Units.ext
      simpa [u] using hpow_q1
    have hord : orderOf u = 2 ^ n :=
      order_two_pow_of_half_eq_neg_one u n (by omega) hu_neg hu_one
    have hdvd : 2 ^ n ∣ q + 1 := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one hu_q1
    have hle : 2 ^ n ≤ q + 1 := Nat.le_of_dvd (by omega) hdvd
    omega

private lemma prime_of_S_zero {n : ℕ} (hn : 3 ≤ n)
    (hS : OMA.S_mse_141308.S (3 * 2 ^ n + 1) (OMA.S_mse_141308.seed n) (n - 2) = 0) :
    (3 * 2 ^ n + 1).Prime := by
  set N := 3 * 2 ^ n + 1
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hN2 : 2 ≤ N := by omega
  by_contra hnp
  have hmin : N.minFac.Prime := Nat.minFac_prime (by omega)
  have hdvd : N.minFac ∣ N := Nat.minFac_dvd N
  have hsq : N.minFac * N.minFac ≤ N := by
    have hle := Nat.minFac_sq_le_self (by omega) hnp
    simpa [sq] using hle
  have hge : 2 ^ n - 1 ≤ N.minFac := prime_divisor_ge_of_S_zero hn rfl hmin hdvd hS
  set t := 2 ^ n - 1
  have ht : 2 ^ n = t + 1 := by omega
  have ht7 : 7 ≤ t := by omega
  have hbig : 3 * (t + 1) + 1 < t * t := by nlinarith
  have hmul : t * t ≤ N.minFac * N.minFac := Nat.mul_le_mul hge hge
  omega

private lemma pow_two_mod_five (n : ℕ) : 2 ^ n % 5 = 2 ^ (n % 4) % 5 := by
  conv_lhs => rw [← Nat.div_add_mod n 4, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

private lemma pow_two_mod_seven (n : ℕ) : 2 ^ n % 7 = 2 ^ (n % 3) % 7 := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

private lemma pow_two_mod_thirteen (n : ℕ) : 2 ^ n % 13 = 2 ^ (n % 12) % 13 := by
  conv_lhs => rw [← Nat.div_add_mod n 12, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

private lemma pow_two_mod_seventeen (n : ℕ) : 2 ^ n % 17 = 2 ^ (n % 8) % 17 := by
  conv_lhs => rw [← Nat.div_add_mod n 8, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

private lemma leg_odd_prime {N p : ℕ} [Fact N.Prime] [Fact p.Prime] (hp2 : p ≠ 2)
    (hNp : N ≠ p) (hN4 : N % 4 = 1) : legendreSym N (p : ℤ) = legendreSym p (N : ℤ) := by
  have hN2 : N ≠ 2 := by omega
  have hrec := legendreSym.quadratic_reciprocity hN2 hp2 hNp
  have heven : Even (N / 2 * (p / 2)) := Even.mul_right ⟨N / 2 / 2, by omega⟩ (p / 2)
  rw [heven.neg_one_pow] at hrec
  rcases legendre_cases p (N : ℤ) with h | h | h
  · rw [h, zero_mul] at hrec; norm_num at hrec
  · rw [h, one_mul] at hrec; rw [h, hrec]
  · rw [h] at hrec; rw [h]; linarith

private lemma leg_at_two {N : ℕ} [Fact N.Prime] (hN8 : N % 8 = 1) :
    legendreSym N 2 = 1 := by
  rw [legendreSym.at_two (by omega : N ≠ 2)]
  have h1 : (N : ZMod 8) = 1 := by
    rw [← ZMod.natCast_mod, hN8]; rfl
  simp [ZMod.χ₈, h1]

private lemma leg_at_three {N : ℕ} [Fact N.Prime] (hN97 : 97 ≤ N) (hN4 : N % 4 = 1)
    (hN3 : N % 3 = 1) : legendreSym N 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl, leg_odd_prime (by decide) (by omega) hN4]
  have hm : (N : ℤ) % ((3 : ℕ) : ℤ) = 1 := by exact_mod_cast hN3
  rw [legendreSym.mod, hm]
  exact (by decide : @legendreSym 3 ⟨by decide⟩ 1 = 1)

private lemma leg_at_five {N : ℕ} [Fact N.Prime] (hN97 : 97 ≤ N) (hN4 : N % 4 = 1) :
    (N % 5 = 2 ∨ N % 5 = 3 → legendreSym N 5 = -1) ∧
    (N % 5 = 4 → legendreSym N 5 = 1) := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  constructor
  · intro h
    rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) by rfl, leg_odd_prime (by decide) (by omega) hN4]
    rcases h with h | h
    · have hm : (N : ℤ) % ((5 : ℕ) : ℤ) = 2 := by exact_mod_cast h
      rw [legendreSym.mod, hm]
      exact (by decide : @legendreSym 5 ⟨by decide⟩ 2 = -1)
    · have hm : (N : ℤ) % ((5 : ℕ) : ℤ) = 3 := by exact_mod_cast h
      rw [legendreSym.mod, hm]
      exact (by decide : @legendreSym 5 ⟨by decide⟩ 3 = -1)
  · intro h
    rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) by rfl, leg_odd_prime (by decide) (by omega) hN4]
    have hm : (N : ℤ) % ((5 : ℕ) : ℤ) = 4 := by exact_mod_cast h
    rw [legendreSym.mod, hm]
    exact (by decide : @legendreSym 5 ⟨by decide⟩ 4 = 1)

private lemma leg_at_seven {N : ℕ} [Fact N.Prime] (hN97 : 97 ≤ N) (hN4 : N % 4 = 1)
    (hN7 : N % 7 = 6) : legendreSym N 7 = -1 := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  rw [show (7 : ℤ) = ((7 : ℕ) : ℤ) by rfl, leg_odd_prime (by decide) (by omega) hN4]
  have hm : (N : ℤ) % ((7 : ℕ) : ℤ) = 6 := by exact_mod_cast hN7
  rw [legendreSym.mod, hm]
  exact (by decide : @legendreSym 7 ⟨by decide⟩ 6 = -1)

private lemma leg_at_thirteen {N : ℕ} [Fact N.Prime] (hN97 : 97 ≤ N) (hN4 : N % 4 = 1)
    (hN13 : N % 13 = 2 ∨ N % 13 = 5 ∨ N % 13 = 11) :
    legendreSym N 13 = -1 := by
  haveI : Fact (Nat.Prime 13) := ⟨by decide⟩
  rw [show (13 : ℤ) = ((13 : ℕ) : ℤ) by rfl, leg_odd_prime (by decide) (by omega) hN4]
  rcases hN13 with h | h | h
  · have hm : (N : ℤ) % ((13 : ℕ) : ℤ) = 2 := by exact_mod_cast h
    rw [legendreSym.mod, hm]
    exact (by decide : @legendreSym 13 ⟨by decide⟩ 2 = -1)
  · have hm : (N : ℤ) % ((13 : ℕ) : ℤ) = 5 := by exact_mod_cast h
    rw [legendreSym.mod, hm]
    exact (by decide : @legendreSym 13 ⟨by decide⟩ 5 = -1)
  · have hm : (N : ℤ) % ((13 : ℕ) : ℤ) = 11 := by exact_mod_cast h
    rw [legendreSym.mod, hm]
    exact (by decide : @legendreSym 13 ⟨by decide⟩ 11 = -1)

private lemma leg_at_seventeen {N : ℕ} [Fact N.Prime] (hN97 : 97 ≤ N) (hN4 : N % 4 = 1)
    (hN17 : N % 17 = 7 ∨ N % 17 = 12) :
    legendreSym N 17 = -1 := by
  haveI : Fact (Nat.Prime 17) := ⟨by decide⟩
  rw [show (17 : ℤ) = ((17 : ℕ) : ℤ) by rfl, leg_odd_prime (by decide) (by omega) hN4]
  rcases hN17 with h | h
  · have hm : (N : ℤ) % ((17 : ℕ) : ℤ) = 7 := by exact_mod_cast h
    rw [legendreSym.mod, hm]
    exact (by decide : @legendreSym 17 ⟨by decide⟩ 7 = -1)
  · have hm : (N : ℤ) % ((17 : ℕ) : ℤ) = 12 := by exact_mod_cast h
    rw [legendreSym.mod, hm]
    exact (by decide : @legendreSym 17 ⟨by decide⟩ 12 = -1)

private lemma leg_u_pm_two {n : ℕ} (hn : 2 < n)
    (hres : n % 12 = 2 ∨ n % 12 = 6 ∨ n % 12 = 8 ∨ n % 12 = 10 ∨ n % 4 = 1)
    [Fact (3 * 2 ^ n + 1).Prime] :
    legendreSym (3 * 2 ^ n + 1) ((uVal n : ℤ) + 2) = -1 ∧
    legendreSym (3 * 2 ^ n + 1) ((uVal n : ℤ) - 2) = -1 := by
  set N := 3 * 2 ^ n + 1
  have hn5 : 5 ≤ n := by omega
  have hN97 : 97 ≤ N := by
    have : 32 ≤ 2 ^ n := by
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn5
    omega
  have h8dvd : 8 ∣ 2 ^ n := by
    have : 2 ^ 3 ∣ 2 ^ n := Nat.pow_dvd_pow 2 (by omega)
    simpa using this
  have hN8 : N % 8 = 1 := by
    obtain ⟨k, hk⟩ := h8dvd
    show (3 * 2 ^ n + 1) % 8 = 1
    rw [hk]; omega
  have hN4 : N % 4 = 1 := by omega
  have hN3 : N % 3 = 1 := by
    show (3 * 2 ^ n + 1) % 3 = 1; omega
  have hL2 : legendreSym N 2 = 1 := leg_at_two hN8
  have hL3 : legendreSym N 3 = 1 := leg_at_three hN97 hN4 hN3
  rcases hres with h12 | h12 | h12 | h12 | h4
  · have hu : uVal n = 12 := by unfold uVal; split_ifs <;> omega
    have hN5 : N % 5 = 3 := by
      show (3 * 2 ^ n + 1) % 5 = 3
      rw [Nat.add_mod, Nat.mul_mod, pow_two_mod_five, show n % 4 = 2 by omega]
      norm_num
    have hN7 : N % 7 = 6 := by
      show (3 * 2 ^ n + 1) % 7 = 6
      rw [Nat.add_mod, Nat.mul_mod, pow_two_mod_seven, show n % 3 = 2 by omega]
      norm_num
    have hL5 : legendreSym N 5 = -1 := (leg_at_five hN97 hN4).1 (Or.inr hN5)
    have hL7 : legendreSym N 7 = -1 := leg_at_seven hN97 hN4 hN7
    rw [hu]
    constructor
    · rw [show ((12 : ℕ) : ℤ) + 2 = 2 * 7 by norm_num, legendreSym.mul, hL2, hL7]; norm_num
    · rw [show ((12 : ℕ) : ℤ) - 2 = 2 * 5 by norm_num, legendreSym.mul, hL2, hL5]; norm_num
  · have hu : uVal n = 28 := by unfold uVal; split_ifs <;> omega
    have hN5 : N % 5 = 3 := by
      show (3 * 2 ^ n + 1) % 5 = 3
      rw [Nat.add_mod, Nat.mul_mod, pow_two_mod_five, show n % 4 = 2 by omega]
      norm_num
    have hN13 : N % 13 = 11 := by
      show (3 * 2 ^ n + 1) % 13 = 11
      rw [Nat.add_mod, Nat.mul_mod, pow_two_mod_thirteen, h12]
      norm_num
    have hL5 : legendreSym N 5 = -1 := (leg_at_five hN97 hN4).1 (Or.inr hN5)
    have hL13 : legendreSym N 13 = -1 := leg_at_thirteen hN97 hN4 (Or.inr (Or.inr hN13))
    rw [hu]
    constructor
    · rw [show ((28 : ℕ) : ℤ) + 2 = 2 * 3 * 5 by norm_num,
        legendreSym.mul, legendreSym.mul, hL2, hL3, hL5]; norm_num
    · rw [show ((28 : ℕ) : ℤ) - 2 = 2 * 13 by norm_num, legendreSym.mul, hL2, hL13]; norm_num
  · have hu : uVal n = 37 := by unfold uVal; simp [h12]
    have hN5 : N % 5 = 4 := by
      show (3 * 2 ^ n + 1) % 5 = 4
      rw [Nat.add_mod, Nat.mul_mod, pow_two_mod_five, show n % 4 = 0 by omega]
      norm_num
    have hN7 : N % 7 = 6 := by
      show (3 * 2 ^ n + 1) % 7 = 6
      rw [Nat.add_mod, Nat.mul_mod, pow_two_mod_seven, show n % 3 = 2 by omega]
      norm_num
    have hN13 : N % 13 = 2 := by
      show (3 * 2 ^ n + 1) % 13 = 2
      rw [Nat.add_mod, Nat.mul_mod, pow_two_mod_thirteen, h12]
      norm_num
    have hL5 : legendreSym N 5 = 1 := (leg_at_five hN97 hN4).2 hN5
    have hL7 : legendreSym N 7 = -1 := leg_at_seven hN97 hN4 hN7
    have hL13 : legendreSym N 13 = -1 := leg_at_thirteen hN97 hN4 (Or.inl hN13)
    rw [hu]
    constructor
    · rw [show ((37 : ℕ) : ℤ) + 2 = 3 * 13 by norm_num, legendreSym.mul, hL3, hL13]; norm_num
    · rw [show ((37 : ℕ) : ℤ) - 2 = 5 * 7 by norm_num, legendreSym.mul, hL5, hL7]; norm_num
  · have hu : uVal n = 28 := by unfold uVal; split_ifs <;> omega
    have hN5 : N % 5 = 3 := by
      show (3 * 2 ^ n + 1) % 5 = 3
      rw [Nat.add_mod, Nat.mul_mod, pow_two_mod_five, show n % 4 = 2 by omega]
      norm_num
    have hN13 : N % 13 = 5 := by
      show (3 * 2 ^ n + 1) % 13 = 5
      rw [Nat.add_mod, Nat.mul_mod, pow_two_mod_thirteen, h12]
      norm_num
    have hL5 : legendreSym N 5 = -1 := (leg_at_five hN97 hN4).1 (Or.inr hN5)
    have hL13 : legendreSym N 13 = -1 := leg_at_thirteen hN97 hN4 (Or.inr (Or.inl hN13))
    rw [hu]
    constructor
    · rw [show ((28 : ℕ) : ℤ) + 2 = 2 * 3 * 5 by norm_num,
        legendreSym.mul, legendreSym.mul, hL2, hL3, hL5]; norm_num
    · rw [show ((28 : ℕ) : ℤ) - 2 = 2 * 13 by norm_num, legendreSym.mul, hL2, hL13]; norm_num
  · have hu : uVal n = 32 := by unfold uVal; split_ifs <;> omega
    have hN5 : N % 5 = 2 := by
      show (3 * 2 ^ n + 1) % 5 = 2
      rw [Nat.add_mod, Nat.mul_mod, pow_two_mod_five, h4]
      norm_num
    have hN17 : N % 17 = 7 ∨ N % 17 = 12 := by
      have h8 : n % 8 = 1 ∨ n % 8 = 5 := by omega
      rcases h8 with h8 | h8
      · left
        show (3 * 2 ^ n + 1) % 17 = 7
        rw [Nat.add_mod, Nat.mul_mod, pow_two_mod_seventeen, h8]; norm_num
      · right
        show (3 * 2 ^ n + 1) % 17 = 12
        rw [Nat.add_mod, Nat.mul_mod, pow_two_mod_seventeen, h8]; norm_num
    have hL5 : legendreSym N 5 = -1 := (leg_at_five hN97 hN4).1 (Or.inl hN5)
    have hL17 : legendreSym N 17 = -1 := leg_at_seventeen hN97 hN4 hN17
    rw [hu]
    constructor
    · rw [show ((32 : ℕ) : ℤ) + 2 = 2 * 17 by norm_num, legendreSym.mul, hL2, hL17]; norm_num
    · rw [show ((32 : ℕ) : ℤ) - 2 = 2 * 3 * 5 by norm_num,
        legendreSym.mul, legendreSym.mul, hL2, hL3, hL5]; norm_num

private lemma S_zero_of_prime {n : ℕ} (hn : 2 < n)
    (hres : n % 12 = 2 ∨ n % 12 = 6 ∨ n % 12 = 8 ∨ n % 12 = 10 ∨ n % 4 = 1)
    (hP : (3 * 2 ^ n + 1).Prime) :
    OMA.S_mse_141308.S (3 * 2 ^ n + 1) (OMA.S_mse_141308.seed n) (n - 2) = 0 := by
  set N := 3 * 2 ^ n + 1
  have _ : Fact N.Prime := ⟨hP⟩
  have hn5 : 5 ≤ n := by omega
  have hN97 : 97 ≤ N := by
    have : 32 ≤ 2 ^ n := by
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn5
    omega
  have hN2 : N ≠ 2 := by omega
  have h2ne : (2 : ZMod N) ≠ 0 := by
    intro h0
    have : N ∣ 2 := (ZMod.natCast_eq_zero_iff 2 N).mp h0
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have ⟨hLp, hLm⟩ := leg_u_pm_two hn hres
  set u := uVal n
  have hLsq : legendreSym N ((u : ℤ) ^ 2 - 4) = 1 := by
    rw [show (u : ℤ) ^ 2 - 4 = ((u : ℤ) + 2) * ((u : ℤ) - 2) by ring,
      legendreSym.mul, hLp, hLm]
    norm_num
  have hDne : (((u : ℤ) ^ 2 - 4 : ℤ) : ZMod N) ≠ 0 := by
    intro h0
    have hz : legendreSym N ((u : ℤ) ^ 2 - 4) = 0 := (legendreSym.eq_zero_iff N _).mpr h0
    omega
  have hsq : IsSquare (((u : ℤ) ^ 2 - 4 : ℤ) : ZMod N) :=
    (legendreSym.eq_one_iff N hDne).mp hLsq
  obtain ⟨w, hw⟩ := hsq
  have hws : w * w = (u : ZMod N) ^ 2 - 4 := by
    simpa using hw.symm
  have h2inv : (2 : ZMod N) * (2 : ZMod N)⁻¹ = 1 := mul_inv_cancel₀ h2ne
  set β : ZMod N := ((u : ZMod N) + w) * (2 : ZMod N)⁻¹
  set βi : ZMod N := ((u : ZMod N) - w) * (2 : ZMod N)⁻¹
  have hβmul : β * βi = 1 := by
    calc β * βi = ((u : ZMod N) ^ 2 - w * w) * ((2 : ZMod N)⁻¹ * (2 : ZMod N)⁻¹) := by ring
      _ = 4 * ((2 : ZMod N)⁻¹ * (2 : ZMod N)⁻¹) := by rw [hws]; ring
      _ = ((2 : ZMod N) * (2 : ZMod N)⁻¹) * ((2 : ZMod N) * (2 : ZMod N)⁻¹) := by ring
      _ = 1 := by rw [h2inv]; ring
  have hβadd : β + βi = (u : ZMod N) := by
    calc β + βi = (u : ZMod N) * ((2 : ZMod N) * (2 : ZMod N)⁻¹) := by ring
      _ = (u : ZMod N) := by rw [h2inv, mul_one]
  have hu2_nsq : ¬ IsSquare (((u : ℤ) + 2 : ℤ) : ZMod N) :=
    (legendreSym.eq_neg_one_iff N).mp hLp
  have hβ_nsq : ¬ IsSquare β := by
    intro ⟨t, ht⟩
    have hβp1 : (β + 1) ^ 2 = β * ((u : ZMod N) + 2) := by
      calc (β + 1) ^ 2 = β ^ 2 + 2 * β + 1 := by ring
        _ = β ^ 2 + 2 * β + β * βi := by rw [hβmul]
        _ = β * (β + βi + 2) := by ring
        _ = β * ((u : ZMod N) + 2) := by rw [hβadd]
    have ht0 : t ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at ht
      rw [ht, zero_mul] at hβmul
      exact zero_ne_one hβmul
    apply hu2_nsq
    refine ⟨(β + 1) * t⁻¹, ?_⟩
    have hmul_eq : t * t = β := ht.symm
    have hti : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0
    push_cast
    calc (u : ZMod N) + 2
        = ((u : ZMod N) + 2) * ((t * t⁻¹) * (t * t⁻¹)) := by rw [hti]; ring
      _ = (t * t * ((u : ZMod N) + 2)) * (t⁻¹ * t⁻¹) := by ring
      _ = (β * ((u : ZMod N) + 2)) * (t⁻¹ * t⁻¹) := by rw [hmul_eq]
      _ = (β + 1) ^ 2 * (t⁻¹ * t⁻¹) := by rw [← hβp1]
      _ = (β + 1) * t⁻¹ * ((β + 1) * t⁻¹) := by ring
  have hβpow : β ^ ((N - 1) / 2) = -1 := euler_non_square hN2 hβ_nsq
  set α : ZMod N := β ^ 3
  set αi : ZMod N := βi ^ 3
  have hαmul : α * αi = 1 := by
    rw [← mul_pow, hβmul, one_pow]
  have hαadd : α + αi = (OMA.S_mse_141308.seed n : ZMod N) := by
    have hseed : (OMA.S_mse_141308.seed n : ZMod N) = (u : ZMod N) ^ 3 - 3 * (u : ZMod N) := by
      have := congrArg (Int.cast : ℤ → ZMod N) (seed_eq_cubic n)
      simpa [u] using this
    rw [hseed, ← hβadd]
    calc β ^ 3 + βi ^ 3
        = (β + βi) ^ 3 - 3 * (β * βi) * (β + βi) := by ring
      _ = (β + βi) ^ 3 - 3 * (β + βi) := by rw [hβmul]; ring
  have hSval : OMA.S_mse_141308.S N (OMA.S_mse_141308.seed n) (n - 2) =
      α ^ (2 ^ (n - 2)) + αi ^ (2 ^ (n - 2)) :=
    S_eq_pow_add_inv (OMA.S_mse_141308.seed n) α αi hαmul hαadd (n - 2) N (RingHom.id (ZMod N))
  rw [hSval]
  have hαhalf : α ^ (2 ^ (n - 1)) = -1 := by
    have hexp : 3 * 2 ^ (n - 1) = (N - 1) / 2 := by
      have hpow : 2 ^ n = 2 ^ (n - 1) * 2 := by
        conv_lhs => rw [show n = (n - 1) + 1 by omega]
        rw [pow_succ]
      show 3 * 2 ^ (n - 1) = (3 * 2 ^ n + 1 - 1) / 2
      rw [hpow]
      omega
    calc α ^ (2 ^ (n - 1)) = β ^ (3 * 2 ^ (n - 1)) := by rw [← pow_mul]
      _ = β ^ ((N - 1) / 2) := by rw [hexp]
      _ = -1 := hβpow
  have hsq_neg1 : α ^ (2 ^ (n - 2)) * α ^ (2 ^ (n - 2)) = -1 := by
    rw [← pow_add, show 2 ^ (n - 2) + 2 ^ (n - 2) = 2 ^ (n - 1) by
      rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]; ring]
    exact hαhalf
  have hinv_eq : αi ^ (2 ^ (n - 2)) = -(α ^ (2 ^ (n - 2))) := by
    have h1 : α ^ (2 ^ (n - 2)) * αi ^ (2 ^ (n - 2)) = 1 := by
      rw [← mul_pow, hαmul, one_pow]
    calc αi ^ (2 ^ (n - 2))
        = -((-1) * αi ^ (2 ^ (n - 2))) := by ring
      _ = -((α ^ (2 ^ (n - 2)) * α ^ (2 ^ (n - 2))) * αi ^ (2 ^ (n - 2))) := by rw [hsq_neg1]
      _ = -(α ^ (2 ^ (n - 2)) * (α ^ (2 ^ (n - 2)) * αi ^ (2 ^ (n - 2)))) := by ring
      _ = -(α ^ (2 ^ (n - 2))) := by rw [h1, mul_one]
  rw [hinv_eq, add_neg_cancel]

end Proof_mse_141308

theorem OMA.solution : type_of% @OMA.S_mse_141308.main := by
  intro n hn hres
  constructor
  · exact Proof_mse_141308.S_zero_of_prime hn hres
  · exact Proof_mse_141308.prime_of_S_zero (by omega)
