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
    (¬ ∃ s : ℕ, x = 2 ^ s) → ¬ (x ^ 4 - 1 ∣ 2 ^ x - 1)

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
  have md : m ∣ x ^ 4 - 1 := by
    refine ⟨x ^ 2 - 1, ?_⟩
    dsimp [m]
    have hx2 : 1 ≤ x ^ 2 := Nat.pow_pos (by omega)
    have hx4 : 1 ≤ x ^ 4 := Nat.pow_pos (by omega)
    zify [hx2, hx4]
    ring
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
      exact (mixed (n - 1) big (four_dvd_of_test _ big res.1 div) res.2 power div).elim

end OMA.R_oeis_a000215_R1
