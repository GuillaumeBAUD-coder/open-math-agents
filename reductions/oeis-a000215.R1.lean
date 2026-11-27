import OMAStatements.S_oeis_a000215

-- Credit: @DavidHallgren
namespace OMA.R_oeis_a000215_R1

/-- The compositeness question beyond the consecutive factor certificates below. -/
def H1 : Prop := ∀ n : ℕ, 20 ≤ n → ¬ (2 ^ (2 ^ n) + 1).Prime

/-- For the factor bound it suffices to study products of two primes. -/
def H2 : Prop := ∀ n p q : ℕ, 20 ≤ n → p.Prime → q.Prime → p ≤ q →
    p * q = 2 ^ (2 ^ n) + 1 → p < 3 * 2 ^ ((2 ^ n) / 2 - n - 2)

/-- The remaining converse in Hasler's divisibility test, with x = n - 1. -/
def H3 : Prop := ∀ x : ℕ, 4 < x → 4 ∣ x → ¬ (x - 1).Prime →
    (¬ ∃ s : ℕ, x = 2 ^ s) →
    (∀ p k : ℕ, p.Prime → p ≠ 2 → k ≠ 0 →
      x ≠ 4 * p ^ k ∧ (x = 8 * p ^ k → p = 3 ∧ k % 4 = 3) ∧
      (x = 12 * p ^ k → p = 7 ∨ p = 11 ∨ p = 19)) →
    (x % 8 = 4 → ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ q ≠ r ∧ q ∣ x ^ 2 + 1 ∧
      r ∣ x ^ 2 + 1 ∧ q % 16 ≠ 1 ∧ r % 16 ≠ 1 ∧ jacobiSym (x + 1 : ℕ) q = -1) →
    ¬ (x ^ 4 - 1 ∣ 2 ^ x - 1)

lemma first_primes {n : ℕ} (hn : n ≤ 4) : (2 ^ (2 ^ n) + 1).Prime := by
  interval_cases n <;> norm_num

-- One divisor from the FermatSearch factor tables for each index 5 through 19.
-- The kernel verifies divisibility, properness, and the strict bound on each divisor.
lemma factor_certificates (n : ℕ) (lo : 5 ≤ n) (hi : n < 20) :
    ∃ d : ℕ, 2 ≤ d ∧ d < 2 ^ (2 ^ n) + 1 ∧ d ∣ 2 ^ (2 ^ n) + 1 ∧
      d < 3 * 2 ^ ((2 ^ n) / 2 - n - 2) := by
  let factors : List ℕ := [641, 274177, 59649589127497217, 1238926361552897,
    2424833, 45592577, 319489, 114689, 2710954639361,
    116928085873074369829035993834596371340386703423373313, 1214251009,
    825753601, 31065037602817, 13631489, 70525124609]
  have cert : ∀ i : Fin 15, let m := i.val + 5; let d := factors[i.val]!;
      2 ≤ d ∧ d < 2 ^ (2 ^ m) + 1 ∧ d ∣ 2 ^ (2 ^ m) + 1 ∧
      d < 3 * 2 ^ ((2 ^ m) / 2 - m - 2) := by decide +kernel
  let i : Fin 15 := ⟨n - 5, by omega⟩
  have eq : i.val + 5 = n := by dsimp [i]; omega
  exact ⟨factors[i.val]!, by simpa only [eq] using cert i⟩

lemma cube_bound (n : ℕ) (hn : 6 ≤ n) :
    2 ^ (2 ^ n) + 1 < (3 * 2 ^ ((2 ^ n) / 2 - n - 2)) ^ 3 := by
  have grow : 6 * n + 18 ≤ 2 ^ n := by
    induction n, hn using Nat.le_induction with
    | base => decide
    | succ n hn ih => rw [pow_succ]; omega
  let e := (2 ^ n) / 2 - n - 2
  have he : 2 ^ n ≤ e * 3 := by dsimp [e]; omega
  have h := Nat.pow_le_pow_right (by decide : 0 < 2) he
  rw [pow_mul] at h
  change 2 ^ (2 ^ n) + 1 < (3 * 2 ^ e) ^ 3
  rw [mul_pow]
  have pos : 0 < (2 ^ e : ℕ) ^ 3 := by positivity
  omega

lemma large_factor_bound (semiprime : H2) (n : ℕ) (hn : 20 ≤ n)
    (comp : ¬ (2 ^ (2 ^ n) + 1).Prime) :
    Nat.minFac (2 ^ (2 ^ n) + 1) < 3 * 2 ^ ((2 ^ n) / 2 - n - 2) := by
  let F := 2 ^ (2 ^ n) + 1
  let p := F.minFac
  let q := F / p
  have fpos : 1 < F := by dsimp [F]; have := Nat.one_le_two_pow (n := 2 ^ n); omega
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpq : p ≤ q := Nat.minFac_le_div (by omega) comp
  have prod : p * q = F := Nat.mul_div_cancel' (Nat.minFac_dvd _)
  by_cases hq : q.Prime
  · exact semiprime n p q hn hp hq hpq prod
  obtain ⟨a, b, alt, blt, ab⟩ := (Nat.not_prime_iff_exists_mul_eq (hp.two_le.trans hpq)).mp hq
  have nontriv (u v : ℕ) (hv : v < q) (huv : u * v = q) : 2 ≤ u := by
    by_contra! small
    interval_cases u <;> simp_all
    omega
  have dq : q ∣ F := ⟨p, by simpa only [Nat.mul_comm] using prod.symm⟩
  have da : a ∣ q := ⟨b, ab.symm⟩
  have db : b ∣ q := ⟨a, by simpa only [Nat.mul_comm] using ab.symm⟩
  have ha : p ≤ a := Nat.minFac_le_of_dvd (nontriv a b blt ab) (da.trans dq)
  have hb : p ≤ b := Nat.minFac_le_of_dvd (nontriv b a alt (by simpa only [Nat.mul_comm] using ab))
    (db.trans dq)
  have three : p ^ 3 ≤ F := calc
    p ^ 3 = p * (p * p) := by ring
    _ ≤ p * (a * b) := Nat.mul_le_mul_left p (Nat.mul_le_mul ha hb)
    _ = F := by rw [ab, prod]
  have lt := three.trans_lt (cube_bound n (by omega))
  exact lt_of_not_ge (fun h => (not_lt_of_ge (Nat.pow_le_pow_left h 3)) lt)

-- The forward implication follows Sela Fried, On several conjectures stated in A000215.
lemma fermat_divisibility (k : ℕ) (hk : 1 < k) :
    (2 ^ (2 ^ k)) ^ 4 - 1 ∣ 2 ^ (2 ^ (2 ^ k)) - 1 := by
  have bound : k + 2 ≤ 2 ^ k := by
    have hk' : 2 ≤ k := hk
    induction k, hk' using Nat.le_induction with
    | base => decide
    | succ k hk ih => rw [pow_succ]; omega
  rw [← pow_mul, show 2 ^ k * 4 = 2 ^ (k + 2) by rw [pow_add]; rfl]
  exact Nat.pow_sub_one_dvd_pow_sub_one 2 (pow_dvd_pow 2 bound)

lemma power_two_converse (s : ℕ) (big : 4 < 2 ^ s)
    (div : (2 ^ s) ^ 4 - 1 ∣ 2 ^ (2 ^ s) - 1) :
    ∃ k : ℕ, 1 < k ∧ 2 ^ (2 ^ k) = 2 ^ s := by
  rw [← pow_mul, Nat.dvd_iff_mod_eq_zero, Nat.pow_sub_one_mod_pow_sub_one] at div
  have rem : (2 ^ s) % (s * 4) = 0 := by
    by_contra nonzero
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ 2 ^ s % (s * 4) by omega)
    omega
  have divides : s ∣ 2 ^ s := (dvd_mul_right s 4).trans (Nat.dvd_of_mod_eq_zero rem)
  obtain ⟨k, _, eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp divides
  refine ⟨k, ?_, by rw [eq]⟩
  by_contra! small
  interval_cases k <;> simp_all

lemma restrictions (x : ℕ) (big : 4 < x) (div : x ^ 4 - 1 ∣ 2 ^ x - 1) :
    Even x ∧ ¬ (x - 1).Prime := by
  constructor
  · by_contra h
    have odd : Odd (x ^ 4) := (Nat.not_even_iff_odd.mp h).pow
    obtain ⟨t, ht⟩ := odd
    have evenDiv : 2 ∣ x ^ 4 - 1 := by omega
    have h1 := evenDiv.trans div
    have h2 : 2 ∣ 2 ^ x := dvd_pow_self 2 (by omega)
    have := Nat.one_le_two_pow (n := x)
    omega
  · intro prime
    let p := x - 1
    have hp : p.Prime := prime
    have hcop : Nat.Coprime 2 p := Nat.prime_two.coprime_iff_not_dvd.mpr (by
      intro h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h
      dsimp [p] at this; omega)
    have one : 1 ≡ 2 ^ x [MOD p] := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr
      ((Nat.sub_one_dvd_pow_sub_one x 4).trans div)
    have little := (Nat.ModEq.pow_card_sub_one_eq_one hp hcop).mul_right 4
    have index : x = (p - 1) + 2 := by dsimp [p]; omega
    have four : 2 ^ x ≡ 4 [MOD p] := by
      conv_lhs => rw [index, pow_add]
      simpa using little
    have impossible : p ∣ 3 := (Nat.modEq_iff_dvd' (by decide : 1 ≤ 4)).mp (one.trans four)
    have := Nat.le_of_dvd (by decide : 0 < 3) impossible
    dsimp [p] at this; omega

lemma square_add_one_dvd (x : ℕ) (hx : 0 < x) : x ^ 2 + 1 ∣ x ^ 4 - 1 := by
  refine ⟨x ^ 2 - 1, ?_⟩
  have hx2 : 1 ≤ x ^ 2 := Nat.pow_pos hx
  have hx4 : 1 ≤ x ^ 4 := Nat.pow_pos hx
  zify [hx2, hx4]; ring

/-- If x = 4j + 2 passes the test, then 2 is a square modulo x² + 1.
    But x² + 1 is 5 modulo 8, so its Jacobi symbol at 2 is -1. -/
lemma four_dvd_of_test (x : ℕ) (big : 4 < x) (even : Even x)
    (div : x ^ 4 - 1 ∣ 2 ^ x - 1) : 4 ∣ x := by
  by_contra four
  let j := x / 4
  have hx : x = 4 * j + 2 := by
    obtain ⟨v, hv⟩ := even
    dsimp [j]
    omega
  let m := x ^ 2 + 1
  have meq : m = 8 * (2 * j ^ 2 + 2 * j) + 5 := by dsimp [m]; rw [hx]; ring
  have m8 : m % 8 = 5 := by omega
  have m2 : m % 2 = 1 := by omega
  have bad : ¬ IsSquare (2 : ZMod m) := by
    have hj : jacobiSym 2 m = -1 := by
      rw [jacobiSym.at_two (Nat.odd_iff.mpr m2), ZMod.χ₈_nat_eq_if_mod_eight]
      simp [m8, m2]
    simpa using ZMod.nonsquare_of_jacobiSym_eq_neg_one hj
  have md : m ∣ x ^ 4 - 1 := square_add_one_dvd x (by omega)
  have hm : 1 ≡ 2 ^ x [MOD m] :=
    (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr (md.trans div)
  have powone : (2 : ZMod m) ^ x = 1 := by
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hm.symm
  let u : ZMod m := x
  have hu : u ^ 2 + 1 = 0 := by
    have h := ZMod.natCast_self m
    change ((x ^ 2 + 1 : ℕ) : ZMod m) = 0 at h
    push_cast at h
    exact h
  let a : ZMod m := 2 ^ j
  let z : ZMod m := 2 * a ^ 2
  have hz : z ^ 2 = 1 := calc
    z ^ 2 = (2 : ZMod m) ^ (4 * j + 2) := by
      dsimp [z, a]
      rw [show 4 * j + 2 = (j * 2 + 1) * 2 by omega, pow_mul,
        pow_succ (2 : ZMod m) (j * 2), pow_mul (2 : ZMod m) j 2]
      ring
    _ = 1 := by rwa [← hx]
  let L := (1 + z) + u * (1 - z)
  have hl : L ^ 2 = 4 * z := calc
    L ^ 2 = 4 * z + (u ^ 2 + 1) * (1 - z) ^ 2 + 2 * u * (1 - z ^ 2) := by
      dsimp [L]; ring
    _ = 4 * z := by rw [hu, hz]; ring
  apply bad
  refine ⟨a * L, ?_⟩
  calc
    2 = 2 * z ^ 2 := by rw [hz]; ring
    _ = a ^ 2 * (4 * z) := by dsimp [z]; ring
    _ = (a * L) * (a * L) := by rw [← hl]; ring

-- Apart from p itself, every prime divisor of this geometric sum is 1 modulo p.
lemma geom_prime (b p k q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : q ≠ p)
    (hd : q ∣ ∑ i ∈ Finset.range (p ^ k), b ^ i) : q ≡ 1 [MOD p] := by
  let _ : Fact q.Prime := ⟨hq⟩
  have hsum := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  push_cast at hsum
  by_cases hb : (b : ZMod q) = 1
  · simp [hb] at hsum
    have hqp : q ∣ p ^ k := (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using hsum)
    exact (hne ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqp))).elim
  have hbpow : (b : ZMod q) ^ (p ^ k) = 1 := by
    have h := geom_sum_mul (b : ZMod q) (p ^ k)
    rw [hsum, zero_mul] at h
    exact sub_eq_zero.mp h.symm
  let o := orderOf (b : ZMod q)
  have hdiv : o ∣ p ^ k := orderOf_dvd_of_pow_eq_one hbpow
  obtain ⟨e, _, he⟩ := (Nat.dvd_prime_pow hp).mp hdiv
  have he0 : e ≠ 0 := by rintro rfl; exact hb (orderOf_eq_one_iff.mp (by simpa [o] using he))
  have hb0 : (b : ZMod q) ≠ 0 := by
    intro h; simp [h, hp.ne_zero] at hbpow
  have card : o ∣ q - 1 := ZMod.orderOf_dvd_card_sub_one hb0
  exact ((Nat.modEq_iff_dvd' hq.one_le).mpr ((he ▸ dvd_pow_self p he0).trans card)).symm

lemma geom_divisor (b p k v : ℕ) (hp : p.Prime) (hn : ¬ p ∣ v)
    (hd : v ∣ ∑ i ∈ Finset.range (p ^ k), b ^ i) : v ≡ 1 [MOD p] := by
  induction v using Nat.recOnMul with
  | zero => simp at hn
  | one => rfl
  | prime q hq => exact geom_prime b p k q hp hq (by rintro rfl; exact hn dvd_rfl) hd
  | mul a b' ia ib =>
    have da : a ∣ a * b' := dvd_mul_right _ _
    have db : b' ∣ a * b' := dvd_mul_left _ _
    simpa using (ia (fun h => hn (h.trans da)) (da.trans hd)).mul
      (ib (fun h => hn (h.trans db)) (db.trans hd))

-- For a fixed cofactor t, the possible residues are controlled by 2^t-1.
lemma small_divisor (t p k v : ℕ) (hp : p.Prime) (hn : ¬ p ∣ v)
    (hd : v ∣ 2 ^ (t * p ^ k) - 1) :
    ∃ d : ℕ, d ∣ 2 ^ t - 1 ∧ d ∣ v ∧ v ≡ d [MOD p] := by
  let G := ∑ i ∈ Finset.range (p ^ k), (2 ^ t) ^ i
  have hG : G * (2 ^ t - 1) = 2 ^ (t * p ^ k) - 1 := by
    rw [pow_mul]
    exact geom_sum_mul_of_one_le Nat.one_le_two_pow _
  obtain ⟨r, d, hr, hdBase, h⟩ := exists_dvd_and_dvd_of_dvd_mul (hG.symm ▸ hd : v ∣ G * (2 ^ t - 1))
  have dr : r ∣ v := ⟨d, h⟩
  refine ⟨d, hdBase, ⟨r, by rw [h, Nat.mul_comm]⟩, ?_⟩
  have h1 := geom_divisor (2 ^ t) p k r hp (fun h => hn (h.trans dr)) hr
  simpa only [h, one_mul] using h1.mul_right d

lemma divisor_before (t p k : ℕ) (ht : 0 < t) (hp : p.Prime) (hk : k ≠ 0)
    (div : (t * p ^ k) ^ 4 - 1 ∣ 2 ^ (t * p ^ k) - 1) :
    ∃ d : ℕ, d ∣ 2 ^ t - 1 ∧ d ∣ t * p ^ k - 1 ∧ p ∣ d + 1 := by
  let x := t * p ^ k
  have hx : 1 ≤ x := by change 0 < t * p ^ k; exact Nat.mul_pos ht (Nat.pow_pos hp.pos)
  have px : p ∣ x := dvd_mul_of_dvd_right (dvd_pow_self p hk) t
  have pn : ¬ p ∣ x - 1 := by
    intro h
    have h' : p ∣ x - (x - 1) := Nat.dvd_sub px h
    rw [show x - (x - 1) = 1 by omega] at h'; exact hp.not_dvd_one h'
  obtain ⟨d, hd, dh, hm⟩ := small_divisor t p k (x - 1) hp pn
    ((Nat.sub_one_dvd_pow_sub_one x 4).trans div)
  have hx0 : x ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr px
  have h1 := hm.add_right 1
  rw [Nat.sub_add_cancel hx] at h1
  have plus : p ∣ d + 1 := Nat.modEq_zero_iff_dvd.mp (h1.symm.trans hx0)
  exact ⟨d, hd, dh, plus⟩

-- Apply the cofactor test to x - 1. Its residue modulo p is -1.
lemma force_three (p k : ℕ) (hp : p.Prime) (odd : p ≠ 2) (hk : k ≠ 0)
    (div : (4 * p ^ k) ^ 4 - 1 ∣ 2 ^ (4 * p ^ k) - 1) :
    p = 3 ∧ 5 ∣ 4 * p ^ k - 1 := by
  obtain ⟨d, hd, dh, plus⟩ := divisor_before 4 p k (by decide) hp hk div
  have hdle := Nat.le_of_dvd (by decide : 0 < 15) hd
  have ple := Nat.le_of_dvd (by omega : 0 < d + 1) plus
  have cert : ∀ d : Fin 16, ∀ p : Fin 17, d.val ∣ 15 → p.val.Prime →
      p.val ≠ 2 → p.val ∣ d.val + 1 → p.val = 3 ∧ d.val = 5 := by decide +kernel
  obtain ⟨h3, rfl⟩ := cert ⟨d, by omega⟩ ⟨p, by omega⟩ hd hp odd plus
  exact ⟨h3, dh⟩

-- Reciprocity swaps x + 1 with x² + 1; the latter is 2 modulo x + 1.
lemma symbol_obstruction (x : ℕ) (hx : x % 8 = 4) :
    jacobiSym (x + 1 : ℕ) (x ^ 2 + 1) = -1 := by
  have xm : (x ^ 2 + 1) % 4 = 1 := by
    rw [Nat.add_mod, Nat.pow_mod]; have : x % 4 = 0 := by omega
    simp [this]
  have odd : Odd (x + 1) := Nat.odd_iff.mpr (by omega)
  have hmod : (x ^ 2 + 1) % (x + 1) = 2 % (x + 1) := by
    have eq : x ^ 2 + 1 = (x - 1) * (x + 1) + 2 := by
      have hpos : 1 ≤ x := by omega
      zify [hpos]; ring
    rw [eq, Nat.mul_add_mod_self_right]
  rw [jacobiSym.quadratic_reciprocity_one_mod_four' odd xm]
  have red : jacobiSym (x ^ 2 + 1 : ℕ) (x + 1) = jacobiSym 2 (x + 1) := by
    apply jacobiSym.mod_left'
    exact_mod_cast hmod
  rw [red, jacobiSym.at_two odd, ZMod.χ₈_nat_eq_if_mod_eight]
  simp [show (x + 1) % 8 = 5 by omega, show (x + 1) % 2 = 1 by omega]

lemma primitive_eight {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) (y : ZMod q)
    (hy : y ^ 4 = -1) : IsPrimitiveRoot y 8 := by
  have h8 : y ^ 8 = 1 := by rw [show 8 = 4 * 2 by decide, pow_mul, hy]; ring
  have h4 : y ^ 4 ≠ 1 := by
    rw [hy]; intro h
    have two : (2 : ZMod q) = 0 := by linear_combination - h
    exact hq ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 q).mp (by simpa using two)))
  have od := orderOf_dvd_of_pow_eq_one h8
  have ond : ¬orderOf y ∣ 4 := fun h => h4 (orderOf_dvd_iff_pow_eq_one.mp h)
  apply IsPrimitiveRoot.iff_orderOf.mpr
  have bound := Nat.le_of_dvd (by decide : 0 < 8) od
  generalize orderOf y = a at *
  interval_cases a <;> norm_num at *

-- If y is a square, all eighth roots of unity are squares, since y generates them.
lemma local_square {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) (y : ZMod q) (r : ℕ)
    (odd : Odd r) (hy : y ^ 4 = -1) (ysq : IsSquare y) (test : (2 : ZMod q) ^ (4 * r) = 1) :
    IsSquare (y ^ 2 + 1) := by
  have prim := primitive_eight hq y hy
  have yn : y ≠ 0 := by intro h; simp [h] at hy
  let s := (y ^ 2 + 1) / y
  have ss : s ^ 2 = 2 := by
    dsimp [s]; field_simp
    linear_combination hy
  have sunit : s ≠ 0 := by
    intro h
    have zero : (2 : ZMod q) = 0 := by simpa [h] using ss.symm
    exact hq ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 q).mp (by simpa using zero)))
  have h8 : (s ^ r) ^ 8 = 1 := by
    rw [← pow_mul, show r * 8 = 2 * (4 * r) by omega, pow_mul, ss, test]
  obtain ⟨i, _, hi⟩ := prim.eq_pow_of_pow_eq_one h8
  have hsr : IsSquare (s ^ r) := hi ▸ ysq.pow i
  obtain ⟨j, hj⟩ := odd
  have hs : IsSquare s := by
    have key : (s ^ (j + 1)) ^ 2 / s ^ r = s := by
      rw [← pow_mul, show (j + 1) * 2 = r + 1 by omega, pow_succ]
      field_simp
    exact key ▸ (IsSquare.sq _).div hsr
  have key : s * y = y ^ 2 + 1 := div_mul_cancel₀ _ yn
  exact key ▸ hs.mul ysq

lemma three_pow_mod_five (k : ℕ) : (3 : ZMod 5) ^ k = 3 ^ (k % 4) := by
  calc
    _ = (3 : ZMod 5) ^ (4 * (k / 4) + k % 4) := by rw [Nat.div_add_mod]
    _ = _ := by rw [pow_add, pow_mul, show (3 : ZMod 5) ^ 4 = 1 by decide, one_pow, one_mul]

lemma even_three_exponent (k : ℕ) (hd : 5 ∣ 4 * 3 ^ k - 1) : Even k := by
  have hm : 1 ≡ 4 * 3 ^ k [MOD 5] := (Nat.modEq_iff_dvd' (show 0 < 4 * 3 ^ k by positivity)).mpr hd
  have hh := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hm
  push_cast at hh
  rw [three_pow_mod_five] at hh
  have bound := Nat.mod_lt k (by decide : 0 < 4)
  have ek : k % 4 = 2 := by
    have cert : ∀ t : Fin 4, (1 : ZMod 5) = 4 * 3 ^ t.val → t.val = 2 := by decide +kernel
    exact cert ⟨_, bound⟩ hh
  exact Nat.even_iff.mpr (by omega)

/-- No x = 4*p^k, with p an odd prime and k positive, passes Hasler's test. -/
theorem four_prime_power (p k : ℕ) (hp : p.Prime) (odd : p ≠ 2) (hk : k ≠ 0) :
    ¬ ((4 * p ^ k) ^ 4 - 1 ∣ 2 ^ (4 * p ^ k) - 1) := by
  intro test
  obtain ⟨rfl, h5⟩ := force_three p k hp odd hk test
  obtain ⟨j, hj⟩ := even_three_exponent k h5
  let r := 3 ^ k
  let x := 4 * r
  let y := 2 * 3 ^ j
  have rodd : Odd r := (by decide : Odd (3 : ℕ)).pow
  have hx8 : x % 8 = 4 := by obtain ⟨i, hi⟩ := rodd; dsimp [x]; omega
  have xy : x = y ^ 2 := by dsimp [x, r, y]; rw [hj, pow_add]; ring
  let m := x ^ 2 + 1
  have xm : m ∣ x ^ 4 - 1 := square_add_one_dvd x (by omega)
  -- A negative Jacobi symbol supplies a prime where x + 1 is a nonsquare.
  obtain ⟨q, hq, qm, neg⟩ := jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one
    (symbol_obstruction x hx8)
  let _ : Fact q.Prime := ⟨hq⟩
  have z := (ZMod.natCast_eq_zero_iff _ _).mpr qm
  push_cast at z
  have z4 : (y : ZMod q) ^ 4 = -1 := by
    rw [xy] at z
    push_cast at z
    linear_combination z
  have q2 : q ≠ 2 := by
    rintro rfl
    have h : (x ^ 2 + 1) % 2 = 1 := by rw [Nat.add_mod, Nat.pow_mod]; simp [show x % 2 = 0 by omega]
    omega
  have prim := primitive_eight q2 _ z4
  have yn : (y : ZMod q) ≠ 0 := by intro h; simp [h] at z4
  have q8 : 8 ∣ q - 1 := prim.eq_orderOf ▸ ZMod.orderOf_dvd_card_sub_one yn
  have top : q ∣ 2 ^ x - 1 := (qm.trans xm).trans test
  have q3 : q ≠ 3 := by omega
  have hn : ¬ 3 ∣ q := fun h => q3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp h).symm
  obtain ⟨d, hd, dq, cong⟩ := small_divisor 4 3 k q Nat.prime_three hn top
  have d1 : d = 1 := (Nat.dvd_prime hq).mp dq |>.resolve_right (by
    intro deq
    rw [deq] at hd
    have qq := Nat.le_of_dvd (by decide : 0 < 15) hd
    interval_cases q <;> norm_num at *)
  have qr3 : q % 3 = 1 := by simpa [Nat.ModEq, d1] using cong
  have sq3 : IsSquare (3 : ZMod q) := by
    have sym : jacobiSym 3 q = 1 := by
      change jacobiSym ((3 : ℕ) : ℤ) q = 1
      rw [jacobiSym.quadratic_reciprocity_one_mod_four' (by decide : Odd (3 : ℕ))
        (show q % 4 = 1 by have := hq.two_le; omega)]
      have h : jacobiSym (q : ℤ) 3 = jacobiSym 1 3 := by
        apply jacobiSym.mod_left'; exact_mod_cast qr3
      rw [h, jacobiSym.one_left]
    simpa using ZMod.isSquare_of_jacobiSym_eq_one sym
  have sq2 : IsSquare (2 : ZMod q) := (ZMod.exists_sq_eq_two_iff q2).mpr
    (Or.inl (by have := hq.two_le; omega))
  have ysq : IsSquare (y : ZMod q) := by simpa [y] using sq2.mul (sq3.pow j)
  have hm : (2 : ZMod q) ^ x = 1 := by
    have h := (Nat.modEq_iff_dvd' (Nat.one_le_two_pow (n := x))).mpr top
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr h.symm
  have sq := local_square q2 _ r rodd z4 ysq hm
  apply ZMod.nonsquare_of_jacobiSym_eq_neg_one neg
  simpa [xy] using sq

/-- In the adjacent family x = 8*p^k, the only possible odd prime is 3. -/
lemma eight_prime_power (p k : ℕ) (hp : p.Prime) (odd : p ≠ 2) (hk : k ≠ 0)
    (test : (8 * p ^ k) ^ 4 - 1 ∣ 2 ^ (8 * p ^ k) - 1) : p = 3 := by
  obtain ⟨d, hd, _, plus⟩ := divisor_before 8 p k (by decide) hp hk test
  have hdle := Nat.le_of_dvd (by decide : 0 < 255) hd
  have ple := Nat.le_of_dvd (by omega : 0 < d + 1) plus
  have cert : ∀ d : Fin 256, d.val ∣ 255 → ∀ p : Fin 257, p.val.Prime →
      p.val ≠ 2 → p.val ∣ d.val + 1 → p.val = 3 ∨ p.val = 13 ∨ p.val = 43 := by decide +kernel
  rcases cert ⟨d, by omega⟩ hd ⟨p, by omega⟩ hp odd plus with done | h
  · exact done
  exfalso
  have a : (p : ZMod 7) ^ 4 = 1 := by rcases h with rfl | rfl <;> decide
  have x4 : ((8 * p ^ k : ℕ) : ZMod 7) ^ 4 = 1 := by
    push_cast
    rw [mul_pow, ← pow_mul, Nat.mul_comm k 4, pow_mul, a, one_pow, mul_one]
    decide
  have xt : 1 ≡ (8 * p ^ k) ^ 4 [MOD 7] := (ZMod.natCast_eq_natCast_iff _ _ _).mp (by
    simpa using x4.symm)
  have pos : 0 < (8 * p ^ k) ^ 4 := Nat.pow_pos (Nat.mul_pos (by decide) (Nat.pow_pos hp.pos))
  have seven := ((Nat.modEq_iff_dvd' pos).mp xt).trans test
  have hm : (2 : ZMod 7) ^ (8 * p ^ k) = 1 := by
    have m := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr seven
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr m.symm
  have order : orderOf (2 : ZMod 7) = 3 := by
    have h3 := orderOf_dvd_of_pow_eq_one (by decide : (2 : ZMod 7) ^ 3 = 1)
    exact ((Nat.dvd_prime Nat.prime_three).mp h3).resolve_left (fun h =>
      (by decide : (2 : ZMod 7) ≠ 1) (orderOf_eq_one_iff.mp h))
  have three := orderOf_dvd_of_pow_eq_one hm
  rw [order] at three
  have p3 := Nat.prime_three.dvd_of_dvd_pow ((Nat.prime_three.dvd_mul.mp three).resolve_left (by decide))
  rcases h with rfl | rfl <;> norm_num at p3

-- If 5 and 17 both divided x^4-1, removing 85 would leave a divisor of the
-- geometric sum that is 2 modulo 3. Every such divisor coprime to 3 is 1 modulo 3.
lemma eight_three_exponent (k : ℕ) (hk : k ≠ 0)
    (test : (8 * 3 ^ k) ^ 4 - 1 ∣ 2 ^ (8 * 3 ^ k) - 1) : k % 4 = 3 := by
  let x := 8 * 3 ^ k
  let V := x ^ 4 - 1
  have x3 : 3 ∣ x := dvd_mul_of_dvd_right (dvd_pow_self 3 hk) 8
  have xv : 0 < x ^ 4 := Nat.pow_pos (Nat.mul_pos (by decide) (Nat.pow_pos (by decide : 0 < 3)))
  have v3 : V % 3 = 2 := by
    have h : 3 ∣ x ^ 4 := x3.trans (dvd_pow_self x (by decide))
    dsimp [V]; omega
  have five : 5 ∣ V := by
    have h : (8 : ZMod 5) ^ 4 * ((3 : ZMod 5) ^ 4) ^ k = 1 := by
      rw [show (3 : ZMod 5) ^ 4 = 1 by decide, one_pow, mul_one]; decide
    have eq : 1 ≡ x ^ 4 [MOD 5] := (ZMod.natCast_eq_natCast_iff _ _ _).mp (by
      dsimp [x]; push_cast; rw [mul_pow, ← pow_mul, Nat.mul_comm k 4, pow_mul]; exact h.symm)
    exact (Nat.modEq_iff_dvd' xv).mp eq
  have no85 : ¬ 85 ∣ V := by
    rintro ⟨w, hw⟩
    let G := ∑ i ∈ Finset.range (3 ^ k), (256 : ℕ) ^ i
    have hG : G * 255 = 2 ^ x - 1 := by
      dsimp [x]; rw [pow_mul]; exact geom_sum_mul_of_one_le (by decide : 1 ≤ (256 : ℕ)) _
    have wdiv : 85 * w ∣ 85 * (3 * G) := by
      rw [← hw, show 85 * (3 * G) = G * 255 by ring, hG]; exact test
    have w3 : w % 3 = 2 := by omega
    have dw : w ∣ 3 * G := Nat.dvd_of_mul_dvd_mul_left (by decide) wdiv
    have cw : w.Coprime 3 := Nat.prime_three.coprime_iff_not_dvd.mpr (by omega) |>.symm
    have h1 := geom_divisor 256 3 k w Nat.prime_three (by omega) (cw.dvd_of_dvd_mul_left dw)
    change w % 3 = 1 % 3 at h1; omega
  have no17 : ¬ 17 ∣ x - 1 := by
    intro h
    exact no85 ((by decide : Nat.Coprime 5 17).mul_dvd_of_dvd_of_dvd five
      (h.trans (Nat.sub_one_dvd_pow_sub_one x 4)))
  obtain ⟨d, hd, dh, plus⟩ := divisor_before 8 3 k (by decide) Nat.prime_three hk test
  have hdle := Nat.le_of_dvd (by decide : 0 < 255) hd
  have d17 : ¬ 17 ∣ d := fun h => no17 (h.trans dh)
  have cert : ∀ d : Fin 256, d.val ∣ 255 → 3 ∣ d.val + 1 → ¬ 17 ∣ d.val → d.val = 5 := by decide +kernel
  have deq := cert ⟨d, by omega⟩ hd plus d17
  change d = 5 at deq
  rw [deq] at dh
  have hm := (Nat.modEq_iff_dvd' (show 0 < 8 * 3 ^ k by positivity)).mpr dh
  have hz := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hm
  push_cast at hz
  rw [three_pow_mod_five] at hz
  have last : ∀ t : Fin 4, (1 : ZMod 5) = 8 * 3 ^ t.val → t.val = 3 := by decide +kernel
  exact last ⟨k % 4, Nat.mod_lt _ (by decide)⟩ hz

/-- This cofactor already allows two distinct odd primes in x. -/
lemma twelve_prime_power (p k : ℕ) (hp : p.Prime) (odd : p ≠ 2) (hk : k ≠ 0)
    (test : (12 * p ^ k) ^ 4 - 1 ∣ 2 ^ (12 * p ^ k) - 1) : p = 7 ∨ p = 11 ∨ p = 19 := by
  obtain ⟨d, hd, dh, plus⟩ := divisor_before 12 p k (by decide) hp hk test
  have pos : 0 < 12 * p ^ k := Nat.mul_pos (by decide) (Nat.pow_pos hp.pos)
  have three : 3 ∣ 12 * p ^ k := dvd_mul_of_dvd_left (by decide) _
  have d3 : ¬ 3 ∣ d := by intro h; have := h.trans dh; omega
  have cop : d.Coprime (3 ^ 2) := (Nat.prime_three.coprime_iff_not_dvd.mpr d3).symm.pow_right 2
  have cut : d ∣ 455 := cop.dvd_of_dvd_mul_left (show d ∣ 3 ^ 2 * 455 from hd)
  have bound := Nat.le_of_dvd (by decide : 0 < 455) cut
  have ple := Nat.le_of_dvd (by omega : 0 < d + 1) plus
  have table : ∀ d : Fin 456, d.val ∣ 455 → ∀ p : Fin 457, p.val.Prime →
      p.val ≠ 2 → p.val ∣ d.val + 1 →
      p.val = 3 ∨ p.val = 23 ∨ p.val = 7 ∨ p.val = 11 ∨ p.val = 19 := by decide +kernel
  rcases table ⟨d, by omega⟩ cut ⟨p, by omega⟩ hp odd plus with h | h | h
  · change p = 3 at h
    subst p
    have no := four_prime_power 3 (k + 1) Nat.prime_three (by decide) (by omega)
    rw [pow_succ 3 k, show 4 * (3 ^ k * 3) = 12 * 3 ^ k by ring] at no
    exact (no test).elim
  · change p = 23 at h
    subst p
    have hx : 1 ≡ 12 * 23 ^ k [MOD 11] := (ZMod.natCast_eq_natCast_iff _ _ _).mp (by
      push_cast
      rw [show (23 : ZMod 11) = 1 by decide, one_pow, mul_one]
      decide)
    have eleven := ((Nat.modEq_iff_dvd' pos).mp hx).trans
      ((Nat.sub_one_dvd_pow_sub_one (12 * 23 ^ k) 4).trans test)
    have modpow := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr eleven
    have powone : (2 : ZMod 11) ^ (12 * 23 ^ k) = 1 := by
      simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr modpow.symm
    have ord := orderOf_dvd_of_pow_eq_one (by decide : (2 : ZMod 11) ^ 10 = 1)
    have n2 : ¬ orderOf (2 : ZMod 11) ∣ 2 := fun h =>
      (by decide : (2 : ZMod 11) ^ 2 ≠ 1) (orderOf_dvd_iff_pow_eq_one.mp h)
    have n5 : ¬ orderOf (2 : ZMod 11) ∣ 5 := fun h =>
      (by decide : (2 : ZMod 11) ^ 5 ≠ 1) (orderOf_dvd_iff_pow_eq_one.mp h)
    have order : orderOf (2 : ZMod 11) = 10 := by
      have le := Nat.le_of_dvd (by decide : 0 < 10) ord
      generalize orderOf (2 : ZMod 11) = o at *
      interval_cases o <;> norm_num at *
    have ten := orderOf_dvd_of_pow_eq_one powone
    rw [order] at ten
    have five := (show 5 ∣ 10 by decide).trans ten
    have h23 := Nat.prime_five.dvd_of_dvd_pow ((Nat.prime_five.dvd_mul.mp five).resolve_left (by decide))
    norm_num at h23
  · exact h

/-- Odd powers detect the identity on fourth roots of unity. -/
lemma odd_fourth_root {G : Type*} [Monoid G] {z : G} {u : ℕ}
    (hu : Odd u) (h4 : z ^ 4 = 1) (ho : z ^ u = 1) : z = 1 := by
  have cop : u.Coprime 4 := hu.coprime_two_right.pow_right 2
  have h := pow_gcd_eq_one.mpr ⟨ho, h4⟩
  rwa [cop.gcd_eq_one, pow_one] at h

/-- A prime that is 1 modulo 16 cannot supply the negative symbol if its local test passes. -/
lemma one_mod_sixteen_square (x q : ℕ) (hx : x % 8 = 4) (hq : q.Prime)
    (qm : q ∣ x ^ 2 + 1) (qc : q % 16 = 1) (test : q ∣ 2 ^ x - 1) :
    IsSquare ((x + 1 : ℕ) : ZMod q) := by
  let _ : Fact q.Prime := ⟨hq⟩
  let v : ZMod q := x
  let u := x / 4
  let t := q / 16
  have xu : x = 4 * u := by dsimp [u]; omega
  have ou : Odd u := Nat.odd_iff.mpr (by dsimp [u]; omega)
  have qt : q = 16 * t + 1 := by dsimp [t]; omega
  have q2 : q ≠ 2 := by omega
  have nz : (2 : ZMod q) ≠ 0 := by
    intro h
    exact q2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 q).mp (by simpa using h)))
  have one : (2 : ZMod q) ^ x = 1 := by
    have h := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr test
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr h.symm
  have f := ZMod.pow_card_sub_one_eq_one nz
  have z4 : ((2 : ZMod q) ^ (4 * t)) ^ 4 = 1 := by
    rwa [← pow_mul, show 4 * t * 4 = q - 1 by omega]
  have zu : ((2 : ZMod q) ^ (4 * t)) ^ u = 1 := by
    rw [← pow_mul, show 4 * t * u = x * t by rw [xu]; ring, pow_mul, one, one_pow]
  have z := odd_fourth_root ou z4 zu
  have minus : v ^ 2 + 1 = 0 := by
    simpa [v] using (ZMod.natCast_eq_zero_iff _ _).mpr qm
  have h4 : v ^ 4 = 1 := by linear_combination (v ^ 2 - 1) * minus
  have eq : (v + 1) ^ 2 = 2 * v := by linear_combination minus
  have euler : (v + 1) ^ (q / 2) = 1 := by
    rw [show q / 2 = 2 * (4 * t) by omega, pow_mul, eq, mul_pow, z, one_mul,
      pow_mul, h4, one_pow]
  have zero : v + 1 ≠ 0 := by
    intro h
    apply nz
    linear_combination minus - (v - 1) * h
  have sq := (FiniteField.isSquare_iff (F := ZMod q) (by simpa only [ZMod.ringChar_zmod_n] using q2)
    zero).mpr (by simpa only [ZMod.card] using euler)
  simpa [v] using sq

lemma product_one_mod_sixteen (c : ℕ) (hpos : c ≠ 0)
    (h : ∀ r : ℕ, r.Prime → r ∣ c → r ≡ 1 [MOD 16]) : c ≡ 1 [MOD 16] := by
  induction c using Nat.recOnMul with
  | zero => exact (hpos rfl).elim
  | one => rfl
  | prime p hp => exact h p hp dvd_rfl
  | mul a b ia ib =>
    have ha := ia (by rintro rfl; simp at hpos)
      (fun r hr rd => h r hr (rd.trans (dvd_mul_right _ _)))
    have hb := ib (by rintro rfl; simp at hpos)
      (fun r hr rd => h r hr (rd.trans (dvd_mul_left _ _)))
    simpa using ha.mul hb

/-- A passing x = 4 mod 8 needs two distinct primes outside 1 mod 16 in x²+1.
    One of them is a prime with a negative Jacobi symbol. -/
lemma two_exceptional_primes (x : ℕ) (hx : x % 8 = 4)
    (test : x ^ 2 + 1 ∣ 2 ^ x - 1) :
    ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ q ≠ r ∧ q ∣ x ^ 2 + 1 ∧ r ∣ x ^ 2 + 1 ∧
      q % 16 ≠ 1 ∧ r % 16 ≠ 1 ∧ jacobiSym (x + 1 : ℕ) q = -1 := by
  let m := x ^ 2 + 1
  have m0 : m ≠ 0 := by dsimp [m]; omega
  have m1 : m ≡ 1 [MOD 16] := by
    let a := x / 4
    have xa : x = 4 * a := by dsimp [a]; omega
    change (x ^ 2 + 1) % 16 = 1 % 16
    rw [xa, mul_pow, show (4 : ℕ) ^ 2 = 16 by decide, Nat.mul_add_mod_self_left]
  have neg : jacobiSym (x + 1 : ℕ) m = -1 := symbol_obstruction x hx
  have exceptional (q : ℕ) (hq : q.Prime) (qm : q ∣ m) (j : jacobiSym (x + 1 : ℕ) q = -1) :
      q % 16 ≠ 1 := fun qc => ZMod.nonsquare_of_jacobiSym_eq_neg_one j (by
        simpa using one_mod_sixteen_square x q hx hq qm qc (qm.trans test))
  obtain ⟨q, hq, qm, jq⟩ := jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one neg
  have exc := exceptional q hq qm jq
  suffices second : ∃ r : ℕ, r.Prime ∧ r ∣ m ∧ q ≠ r ∧ r % 16 ≠ 1 by
    obtain ⟨r, hr, rm, ne, bad⟩ := second
    exact ⟨q, r, hq, hr, ne, qm, rm, exc, bad, jq⟩
  by_contra! none
  obtain ⟨k, c, qc, mc⟩ := Nat.exists_eq_pow_mul_and_not_dvd m0 q hq.ne_one
  have cp : c ≠ 0 := by rintro rfl; simp at qc
  have cm : c ∣ m := ⟨q ^ k, by rw [mc, Nat.mul_comm]⟩
  have c1 := product_one_mod_sixteen c cp (fun r hr rc => by
    have ne : q ≠ r := by rintro rfl; exact qc rc
    exact none r hr (rc.trans cm) ne)
  have pk : q ^ k ≡ 1 [MOD 16] := by
    rw [mc] at m1
    exact (by simpa using (c1.mul_left (q ^ k)).symm.trans m1)
  have qodd : Odd q := hq.odd_of_ne_two (by
    rintro rfl
    have h : m % 2 = 1 := by change m % 16 = 1 % 16 at m1; omega
    omega)
  have pow4 : (q : ZMod 16) ^ 4 = 1 := by
    have cert : ∀ i : Fin 16, i.val % 2 = 1 → (i.val : ZMod 16) ^ 4 = 1 := by decide +kernel
    have h := cert ⟨q % 16, Nat.mod_lt _ (by decide)⟩ (by change q % 16 % 2 = 1; have := Nat.odd_iff.mp qodd; omega)
    simpa using h
  have even : Even k := by
    by_contra absent
    have zk : (q : ZMod 16) ^ k = 1 := by
      simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr pk
    have z1 := odd_fourth_root (Nat.not_even_iff_odd.mp absent) pow4 zk
    exact exc ((ZMod.natCast_eq_natCast_iff q 1 16).mp (by simpa using z1))
  rw [mc, jacobiSym.mul_right' _ (pow_ne_zero _ hq.ne_zero) cp, jacobiSym.pow_right,
    jq, even.neg_one_pow, one_mul] at neg
  obtain ⟨r, hr, rc, jr⟩ := jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one neg
  exact exceptional r hr (rc.trans cm) jr (none r hr (rc.trans cm) (by rintro rfl; exact qc rc))

-- A square root modulo the complementary factor proves uniqueness without factoring it.
lemma unique_witness_certificate (x q c a : ℕ) (hx : x % 8 = 4) (hq : q.Prime)
    (factor : x ^ 2 + 1 = q * c) (root : x + 1 ≡ a ^ 2 [MOD c]) :
    jacobiSym (x + 1 : ℕ) q = -1 ∧
      ∀ p : ℕ, p.Prime → p ∣ x ^ 2 + 1 → jacobiSym (x + 1 : ℕ) p = -1 → p = q := by
  have unique (p : ℕ) (hp : p.Prime) (pm : p ∣ x ^ 2 + 1)
      (neg : jacobiSym (x + 1 : ℕ) p = -1) : p = q := by
    rw [factor] at pm
    rcases hp.dvd_mul.mp pm with pq | pc
    · exact (Nat.prime_dvd_prime_iff_eq hp hq).mp pq
    · exfalso
      have reduced := root.of_dvd pc
      have square : IsSquare ((x + 1 : ℕ) : ZMod p) := by
        apply (isSquare_iff_exists_sq _).mpr
        exact ⟨a, by simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr reduced⟩
      exact ZMod.nonsquare_of_jacobiSym_eq_neg_one neg (by simpa using square)
  obtain ⟨p, hp, pm, neg⟩ := jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one
    (symbol_obstruction x hx)
  exact ⟨unique p hp pm neg ▸ neg, unique⟩

lemma mersenne_dvd_iff (m x : ℕ) : m ∣ 2 ^ x - 1 ↔ (2 : ZMod m) ^ x = 1 := by
  rw [← Nat.modEq_iff_dvd' Nat.one_le_two_pow, ← ZMod.natCast_eq_natCast_iff]
  push_cast
  exact eq_comm

/-- Each remaining residue class occurs even when the first half passes and
    the unique negative-symbol prime also passes. Each example fails the full test. -/
theorem surviving_witness_classes (b : ℕ) (hb : b = 5 ∨ b = 9 ∨ b = 13) :
    ∃ x q : ℕ, x % 8 = 4 ∧ q.Prime ∧ q % 16 = b ∧ q ∣ x ^ 2 + 1 ∧
      x ^ 2 - 1 ∣ 2 ^ x - 1 ∧ q ∣ 2 ^ x - 1 ∧ ¬ (x ^ 2 + 1 ∣ 2 ^ x - 1) ∧
      jacobiSym (x + 1 : ℕ) q = -1 ∧
      ∀ p : ℕ, p.Prime → p ∣ x ^ 2 + 1 → jacobiSym (x + 1 : ℕ) p = -1 → p = q := by
  rcases hb with rfl | rfl | rfl
  · refine ⟨6818292, 5, by decide +kernel, by norm_num, by decide +kernel, by decide +kernel,
      ?_, ?_, ?_, ?_⟩
    · rw [mersenne_dvd_iff]
      change (2 : ZMod 46489105797263) ^ 6818292 = 1
      reduce_mod_char
    · rw [mersenne_dvd_iff]
      reduce_mod_char
    · rw [mersenne_dvd_iff]
      change (2 : ZMod 46489105797265) ^ 6818292 ≠ 1
      reduce_mod_char
      decide +kernel
    · exact unique_witness_certificate _ _ 9297821159453 1392599994243
        (by decide +kernel) (by norm_num) (by decide +kernel) (by decide +kernel)
  · refine ⟨34407660, 281, by decide +kernel, by norm_num, by decide +kernel, by decide +kernel,
      ?_, ?_, ?_, ?_⟩
    · rw [mersenne_dvd_iff]
      change (2 : ZMod 1183887066675599) ^ 34407660 = 1
      reduce_mod_char
    · rw [mersenne_dvd_iff]
      reduce_mod_char
    · rw [mersenne_dvd_iff]
      change (2 : ZMod 1183887066675601) ^ 34407660 ≠ 1
      reduce_mod_char
      decide +kernel
    · exact unique_witness_certificate _ _ 4213121233721 606124847645
        (by decide +kernel) (by norm_num) (by decide +kernel) (by decide +kernel)
  · refine ⟨9589860, 61, by decide +kernel, by norm_num, by decide +kernel, by decide +kernel,
      ?_, ?_, ?_, ?_⟩
    · rw [mersenne_dvd_iff]
      change (2 : ZMod 91965414819599) ^ 9589860 = 1
      reduce_mod_char
    · rw [mersenne_dvd_iff]
      reduce_mod_char
    · rw [mersenne_dvd_iff]
      change (2 : ZMod 91965414819601) ^ 9589860 ≠ 1
      reduce_mod_char
      decide +kernel
    · exact unique_witness_certificate _ _ 1507629751141 11444095358
        (by decide +kernel) (by norm_num) (by decide +kernel) (by decide +kernel)

/-- For the first example, an odd multiplier alone repairs the full divisibility.
    The failing prime 113 has order 28, whose odd factor 7 is missing from x. -/
lemma odd_order_failure :
    let x : ℕ := 6818292
    Odd 49893557 ∧ (x ^ 4 - 1 ∣ 2 ^ (x * 49893557) - 1) ∧
      113 ∣ x ^ 2 + 1 ∧ orderOf (2 : ZMod 113) = 28 ∧ ¬ 7 ∣ x := by
  refine ⟨by decide +kernel, ?_, by decide +kernel, ?_, by decide +kernel⟩
  · rw [mersenne_dvd_iff]
    change (2 : ZMod 2161236957829205253069885695) ^ 340188840544644 = 1
    reduce_mod_char
  · have h := orderOf_dvd_of_pow_eq_one (by decide +kernel : (2 : ZMod 113) ^ 28 = 1)
    have a : ¬ orderOf (2 : ZMod 113) ∣ 14 := fun hd =>
      (by decide +kernel : (2 : ZMod 113) ^ 14 ≠ 1) (orderOf_dvd_iff_pow_eq_one.mp hd)
    have b : ¬ orderOf (2 : ZMod 113) ∣ 4 := fun hd =>
      (by decide +kernel : (2 : ZMod 113) ^ 4 ≠ 1) (orderOf_dvd_iff_pow_eq_one.mp hd)
    have le := Nat.le_of_dvd (by decide : 0 < 28) h
    generalize orderOf (2 : ZMod 113) = t at *
    interval_cases t <;> norm_num at *

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a000215.main := by
  intro tail semiprime mixed
  refine ⟨?_, ?_, ?_⟩
  · intro n
    refine ⟨fun hp => ?_, first_primes⟩
    by_contra! lo
    by_cases hi : n < 20
    · obtain ⟨d, hd, lt, dvd, _⟩ := factor_certificates n lo hi
      exact Nat.not_prime_of_dvd_of_lt dvd hd lt hp
    · exact tail n (by omega) hp
  · rintro n ⟨a, b, ha, hb, eq⟩
    have comp : ¬ (2 ^ (2 ^ n) + 1).Prime := eq ▸ Nat.not_prime_mul (by omega : a ≠ 1) (by omega : b ≠ 1)
    by_cases small : n ≤ 4
    · exact (comp (first_primes small)).elim
    by_cases hi : n < 20
    · obtain ⟨d, hd, _, dvd, bound⟩ := factor_certificates n (by omega) hi
      exact (Nat.minFac_le_of_dvd hd dvd).trans_lt bound
    exact large_factor_bound semiprime n (by omega) comp
  · intro n hn
    constructor
    · rintro ⟨k, hk, rfl⟩
      simpa using fermat_divisibility k hk
    · intro div
      have big : 4 < n - 1 := by omega
      have res := restrictions (n - 1) big div
      by_cases power : ∃ s : ℕ, n - 1 = 2 ^ s
      · obtain ⟨s, eq⟩ := power
        rw [eq] at big div
        obtain ⟨k, hk, val⟩ := power_two_converse s big div
        exact ⟨k, hk, by omega⟩
      apply (mixed (n - 1) big (four_dvd_of_test _ big res.1 div) res.2 power ?_
        (fun hx => two_exceptional_primes _ hx ((square_add_one_dvd _ (by omega)).trans div)) div).elim
      intro p k hp odd hk
      constructor
      · intro h
        rw [h] at div
        exact four_prime_power p k hp odd hk div
      · constructor
        · intro h
          rw [h] at div
          obtain rfl := eight_prime_power p k hp odd hk div
          exact ⟨rfl, eight_three_exponent k hk div⟩
        · intro h
          rw [h] at div
          exact twelve_prime_power p k hp odd hk div

end OMA.R_oeis_a000215_R1
