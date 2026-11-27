import FormalConjectures.Wikipedia.BealConjecture

-- Credit: @Hennyrick

namespace OMA.R_BealConjecture_beal_conjecture_R2

/-- Equations in which no base is a positive power of two. -/
def H1 : Prop :=
  ∀ {a b c x y z : Nat}, a ≠ 0 → b ≠ 0 → c ≠ 0 → 2 < x → 2 < y → 2 < z →
    (¬ ∃ j : Nat, 0 < j ∧ a = 2 ^ j) → (¬ ∃ j : Nat, 0 < j ∧ b = 2 ^ j) →
    (¬ ∃ j : Nat, 0 < j ∧ c = 2 ^ j) →
    a ^ x + b ^ y = c ^ z → 1 < Nat.gcd a (Nat.gcd b c)

/-- An odd perfect power cannot exceed another by a power of two with
exponent at least three when the two odd-base exponents are coprime. -/
def H2 : Prop :=
  ∀ {b c y z k : Nat}, b % 2 = 1 → c % 2 = 1 → 2 < y → 2 < z →
    2 < k → Nat.gcd y z = 1 → 2 ^ k + b ^ y ≠ c ^ z

/-- Two odd perfect powers with coprime exponents greater than two
cannot sum to a power of two with exponent at least three. -/
def H3 : Prop :=
  ∀ {a b x y k : Nat}, a % 2 = 1 → b % 2 = 1 → 2 < x → 2 < y →
    2 < k → Nat.gcd x y = 1 → a ^ x + b ^ y ≠ 2 ^ k

namespace BealPartial

/-- The geometric quotient has the same parity as the exponent and exceeds
one for exponents above one. -/
theorem difference_factor (u v : Nat) (hu : u % 2 = 1)
    (hv : v % 2 = 1) (hvu : v < u) (n : Nat) :
    ∃ q : Nat, u ^ n = v ^ n + (u - v) * q ∧ q % 2 = n % 2 ∧ (1 < n → 1 < q) := by
  induction n with
  | zero => exact ⟨0, by simp, rfl, by omega⟩
  | succ n ih =>
    obtain ⟨q, hfactor, hmod, _⟩ := ih
    refine ⟨u ^ n + v * q, ?_, ?_, ?_⟩
    · have hsum : u - v + v = u := by omega
      calc
        u ^ (n + 1) = u ^ n * (u - v + v) := by rw [hsum, Nat.pow_succ]
        _ = (u - v) * u ^ n + v * (u ^ n) := by grind
        _ = (u - v) * u ^ n + v * (v ^ n + (u - v) * q) := by rw [← hfactor]
        _ = v ^ (n + 1) + (u - v) * (u ^ n + v * q) := by rw [Nat.pow_succ]; grind
    · have huPow : u ^ n % 2 = 1 := by rw [Nat.pow_mod, hu, Nat.one_pow]
      rw [Nat.add_mod, Nat.mul_mod, hv, hmod, huPow, Nat.one_mul]
      omega
    · intro h
      cases n with
      | zero => omega
      | succ t =>
        have hut : 0 < u ^ t := Nat.pow_pos (by omega)
        have hle : u ≤ u ^ t * u := by
          simpa using (Nat.mul_le_mul_right u (show 1 ≤ u ^ t by omega))
        rw [Nat.pow_succ]
        omega

theorem odd_factor_of_two_pow (q : Nat) (hq : q % 2 = 1) (k d : Nat)
    (heq : d * q = 2 ^ k) : q = 1 := by
  induction k generalizing d with
  | zero =>
    have hdvd : q ∣ 1 := ⟨d, by simpa [Nat.mul_comm] using heq.symm⟩
    exact Nat.dvd_one.mp hdvd
  | succ k ih =>
    rw [Nat.pow_succ] at heq
    have heven := congrArg (fun a : Nat => a % 2) heq
    change d * q % 2 = 2 ^ k * 2 % 2 at heven
    rw [Nat.mul_mod, hq, Nat.mul_one, Nat.mod_mod, Nat.mul_mod_left] at heven
    have hd : d = d / 2 * 2 := by omega
    apply ih (d / 2)
    apply Nat.mul_right_cancel (m := 2) (by decide)
    calc
      d / 2 * q * 2 = (d / 2 * 2) * q := by grind
      _ = 2 ^ k * 2 := by rw [← hd, heq]

/-- The difference of odd powers with the same odd exponent greater than one
and unequal positive odd bases cannot be a power of two. -/
theorem odd_power_difference {u v n : Nat} (hu : u % 2 = 1) (hv : v % 2 = 1)
    (hvu : v < u) (hn : 1 < n) (hodd : n % 2 = 1) (k : Nat) :
    u ^ n - v ^ n ≠ 2 ^ k := by
  intro heq
  obtain ⟨q, hfac, hmod, hlarge⟩ := difference_factor u v hu hv hvu n
  have hpow : (u - v) * q = 2 ^ k := by omega
  have hone := odd_factor_of_two_pow q (hmod.trans hodd) k (u - v) hpow
  have hq := hlarge hn
  omega

end BealPartial

namespace BealEven

theorem power_two_factor {a b k : Nat} (h : a * b = 2 ^ k) : ∃ i : Nat, a = 2 ^ i := by
  induction k generalizing a b with
  | zero =>
    have := Nat.eq_one_of_dvd_one (show a ∣ 1 from ⟨b, h.symm⟩)
    exact ⟨0, this⟩
  | succ k ih =>
    rw [Nat.pow_succ] at h
    by_cases he : a % 2 = 0
    · let c := a / 2
      have ha : a = 2 * c := by dsimp [c]; omega
      rw [ha, Nat.mul_assoc] at h
      obtain ⟨i, hi⟩ := ih (a := c) (b := b) (by omega)
      exact ⟨i + 1, by rw [ha, hi, Nat.pow_succ, Nat.mul_comm]⟩
    · have hd : b % 2 = 0 := by
        have hp := congrArg (· % 2) h
        simp only [Nat.mul_mod a b 2, Nat.mul_mod_left] at hp
        have hodd : a % 2 = 1 := by omega
        simpa [hodd] using hp
      let c := b / 2
      have hb : b = c * 2 := by dsimp [c]; omega
      rw [hb, ← Nat.mul_assoc] at h
      exact ih (a := a) (b := c) (by omega)

theorem four_dvd_large_power {n j : Nat} (he : n = 2 ^ j) (hn : 2 < n) :
    4 ∣ n := by
  cases j with
  | zero => simp_all
  | succ j =>
    cases j with
    | zero => simp_all
    | succ j =>
      refine ⟨2 ^ j, ?_⟩
      rw [he, Nat.pow_succ, Nat.pow_succ]
      omega

theorem succ_power_of_square_diff {a b k : Nat} (hab : b < a)
    (ha : a % 2 = 1) (hb : b % 2 = 1) (h : a ^ 2 - b ^ 2 = 2 ^ k) :
    a = b + 2 ∧ ∃ j : Nat, b + 1 = 2 ^ j := by
  rw [Nat.pow_two_sub_pow_two] at h
  obtain ⟨r, hr⟩ := power_two_factor h
  obtain ⟨s, hs⟩ := power_two_factor ((Nat.mul_comm _ _).trans h)
  have hfour := four_dvd_large_power hr (by omega)
  have hgap : a = b + 2 := by
    apply Classical.byContradiction
    intro hne
    have hfour' := four_dvd_large_power hs (by omega)
    omega
  refine ⟨hgap, ?_⟩
  cases r with
  | zero => simp only [Nat.pow_zero] at hr; omega
  | succ r =>
    refine ⟨r, ?_⟩
    rw [Nat.pow_succ] at hr
    omega

theorem odd_factor {u : Nat} (hu : u%2=1) (d : Nat) :
    ∃ j : Nat, u ^ (2*d+1) + 1 = (u+1)*(2*j+1) := by
  let a := u / 2
  have ha : u = 2*a+1 := by dsimp [a]; omega
  induction d with
  | zero => exact ⟨0, by simp⟩
  | succ d ih =>
    obtain ⟨j, hj⟩ := ih
    refine ⟨j + a * u^(2*d+1), ?_⟩
    rw [show 2*d.succ+1 = (2*d+1)+2 by omega, Nat.pow_add]
    calc
      u^(2*d+1) * u^2 + 1 = (u^(2*d+1)+1) + (u+1)*(2*a)*u^(2*d+1) := by
        grind
      _ = _ := by rw [hj]; grind

theorem eq_one_of_succ_pow_two {u m k : Nat} (hu : u%2=1) (hm : 2 ≤ m)
    (he : u^m+1=2^k) : u^m=1 := by
  let d := m / 2
  have hp : m = 2*d ∨ m = 2*d+1 := by dsimp [d]; omega
  rcases hp with heven | hodd
  · have hpow : u^m = (u^d)^2 := by rw [heven, Nat.mul_comm 2 d, Nat.pow_mul]
    have hoddpow : u^d%2 = 1 := by rw [Nat.pow_mod, hu, Nat.one_pow]
    let a := u^d / 2
    have ha : u^d = 2*a+1 := by dsimp [a]; omega
    have hfour : u^m + 1 = 4*(a*a+a)+2 := by rw [hpow, ha]; grind
    cases k with
    | zero => simp at he; omega
    | succ k =>
      cases k with
      | zero => change u^m+1=2 at he; omega
      | succ k => simp only [Nat.pow_succ] at he; omega
  · obtain ⟨j, hj⟩ := odd_factor hu d
    rw [← hodd] at hj
    have hq := BealPartial.odd_factor_of_two_pow (2*j+1) (by omega) k (u+1) (hj.symm.trans he)
    have hj0 : j=0 := by omega
    subst j
    simp at hj
    by_cases h1 : u = 1
    · simp [h1]
    · have hl : 1 < u := by omega
      have hlt := Nat.pow_lt_pow_right hl (show 1 < m by omega)
      simp only [Nat.pow_one] at hlt
      omega

/-- A difference of squares of odd perfect powers cannot be a power of two. -/
theorem even_power_difference
    {u v m n : Nat} (hu : u % 2 = 1) (hv : v % 2 = 1)
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hgt : u ^ m > v ^ n) (k : Nat) :
    (u ^ m) ^ 2 - (v ^ n) ^ 2 ≠ 2 ^ k := by
  intro h
  obtain ⟨hgap, j, hj⟩ := succ_power_of_square_diff hgt
    (by rw [Nat.pow_mod, hu, Nat.one_pow]) (by rw [Nat.pow_mod, hv, Nat.one_pow]) h
  have hunit := eq_one_of_succ_pow_two hv hn hj
  have heq : u ^ m = 3 := by omega
  by_cases he : u = 1
  · simp [he] at heq
  · have hle : u ^ 2 ≤ u ^ m := Nat.pow_le_pow_right (by omega) hm
    have hlow : 2 ≤ u := by omega
    have hfour : 2 ^ 2 ≤ u ^ 2 := Nat.pow_le_pow_left hlow 2
    omega

end BealEven

namespace BealSum

theorem sum_factor (v d m : Nat) (hv : v % 2 = 1) (hd : d % 2 = 0) :
    ∃ q : Nat, (v + d) ^ (2 * m + 1) + v ^ (2 * m + 1) = (v + d + v) * q ∧
        q % 2 = 1 := by
  induction m with
  | zero => exact ⟨1, by simp, rfl⟩
  | succ m ih =>
    obtain ⟨q, hq, ho⟩ := ih
    refine ⟨v ^ 2 * q + (v + d) ^ (2 * m + 1) * d, ?_, ?_⟩
    · rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega, Nat.pow_add, Nat.pow_add]
      calc
        _ = v ^ 2 * ((v + d) ^ (2*m+1) + v ^ (2*m+1)) +
            (v + d + v) * ((v + d) ^ (2*m+1) * d) := by grind
        _ = _ := by rw [hq]; grind
    · rw [Nat.add_mod, Nat.mul_mod, Nat.mul_mod ((v + d) ^ _) d, hd, Nat.pow_mod, hv, ho]
      simp

theorem odd_sum_ordered {u v n k : Nat} (hu : u % 2 = 1) (hv : v % 2 = 1)
    (hvu : v ≤ u) (hn : 1 < n) (ho : n % 2 = 1) (hk : 2 ≤ k) :
    u ^ n + v ^ n ≠ 2 ^ k := by
  intro heq
  let d := u - v
  have hud : v + d = u := by dsimp [d]; omega
  have hd : d % 2 = 0 := by dsimp [d]; omega
  obtain ⟨q,hfac,hq⟩ := sum_factor v d (n / 2) hv hd
  rw [hud, show 2 * (n / 2) + 1 = n by omega] at hfac
  have hq1 := BealPartial.odd_factor_of_two_pow q hq k (u+v) (hfac.symm.trans heq)
  rw [hq1, Nat.mul_one] at hfac
  by_cases hu1 : u = 1
  · have hv1 : v = 1 := by omega
    rw [hu1, hv1, Nat.one_pow] at heq
    have := Nat.pow_le_pow_right (n := 2) (by decide) hk
    omega
  · have hu' : u ^ 1 < u ^ n := Nat.pow_lt_pow_right (by omega) hn
    have hv' : v ^ 1 ≤ v ^ n := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [Nat.pow_one] at hu' hv'
    omega

theorem odd_power_sum {u v n k : Nat} (hu : u % 2 = 1) (hv : v % 2 = 1)
    (hn : 1 < n) (ho : n % 2 = 1) (hk : 2 ≤ k) : u ^ n + v ^ n ≠ 2 ^ k := by
  rcases Nat.le_total v u with h | h
  · exact odd_sum_ordered hu hv h hn ho hk
  · rw [Nat.add_comm]
    exact odd_sum_ordered hv hu h hn ho hk

theorem even_power_mod_four {a n : Nat} (ha : a % 2 = 1) (hn : 2 ∣ n) :
    a ^ n % 4 = 1 := by
  have hs : a ^ 2 % 4 = 1 := by
    change a ^ 2 % 4 = 1
    rw [Nat.pow_mod]
    rcases (show a % 4 = 1 ∨ a % 4 = 3 by omega) with h | h <;> rw [h] <;> decide
  obtain ⟨t, rfl⟩ := hn
  rw [Nat.pow_mul, Nat.pow_mod, hs, Nat.one_pow]

theorem rhs_two_power {a b x y k : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1)
    (hk : 2 ≤ k) (hg : 1 < Nat.gcd x y) : a ^ x + b ^ y ≠ 2 ^ k := by
  by_cases he : 2 ∣ Nat.gcd x y
  · have h1 := even_power_mod_four ha (Nat.dvd_trans he (Nat.gcd_dvd_left x y))
    have h2 := even_power_mod_four hb (Nat.dvd_trans he (Nat.gcd_dvd_right x y))
    intro heq
    have hd : 4 ∣ 2 ^ k := Nat.pow_dvd_pow (2 : Nat) hk
    have hz := Nat.mod_eq_zero_of_dvd hd
    rw [← heq, Nat.add_mod, h1, h2] at hz
    contradiction
  · let g := Nat.gcd x y
    have ho : g % 2 = 1 := by dsimp [g]; omega
    obtain ⟨i, hi⟩ := Nat.gcd_dvd_left x y
    obtain ⟨j, hj⟩ := Nat.gcd_dvd_right x y
    have ha' : a ^ i % 2 = 1 := by rw [Nat.pow_mod, ha, Nat.one_pow]
    have hb' : b ^ j % 2 = 1 := by rw [Nat.pow_mod, hb, Nat.one_pow]
    have h := odd_power_sum ha' hb' hg ho hk
    change (a ^ i) ^ (Nat.gcd x y) + (b ^ j) ^ (Nat.gcd x y) ≠ 2 ^ k at h
    rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm i, Nat.mul_comm j, ← hi, ← hj] at h
    exact h

end BealSum

namespace BealTwoPower

theorem odd_pow {a : Nat} (h : a % 2 = 1) (n : Nat) : a ^ n % 2 = 1 := by
  rw [Nat.pow_mod, h, Nat.one_pow]

theorem smaller_base {a b n k : Nat} (h : 2 ^ k + a ^ n = b ^ n) : a < b := by
  apply Nat.lt_of_not_ge
  intro hle
  have := Nat.pow_le_pow_left hle n
  have := Nat.two_pow_pos k
  omega

theorem lhs_two_power {b c y z k : Nat} (hb : b % 2 = 1) (hc : c % 2 = 1)
    (hy : 2 < y) (hz : 2 < z) (hg : 1 < Nat.gcd y z) : 2 ^ k + b ^ y ≠ c ^ z := by
  intro heq
  let d := Nat.gcd y z
  have dy : d ∣ y := Nat.gcd_dvd_left y z
  have dz : d ∣ z := Nat.gcd_dvd_right y z
  by_cases h : d % 2 = 0
  · have hd := Nat.dvd_of_mod_eq_zero h
    obtain ⟨i, hi⟩ := Nat.dvd_trans hd dy
    obtain ⟨j, hj⟩ := Nat.dvd_trans hd dz
    rw [hi, hj, Nat.mul_comm 2 i, Nat.mul_comm 2 j, Nat.pow_mul, Nat.pow_mul] at heq
    have hne := BealEven.even_power_difference hc hb (m := j) (n := i)
      (by omega) (by omega) (smaller_base heq) k
    apply hne
    rw [← heq, Nat.add_sub_cancel]
  · obtain ⟨i, hi⟩ := dy
    obtain ⟨j, hj⟩ := dz
    rw [hi, hj, Nat.mul_comm d i, Nat.mul_comm d j, Nat.pow_mul, Nat.pow_mul] at heq
    have hne := BealPartial.odd_power_difference (odd_pow hc j) (odd_pow hb i)
      (smaller_base heq) hg (show d % 2 = 1 by omega) k
    apply hne
    rw [← heq, Nat.add_sub_cancel]

theorem parity_pow {a n : Nat} (hn : 0 < n) : a ^ n % 2 = a % 2 := by
  rw [Nat.pow_mod]
  by_cases h : a % 2 = 0
  · simp [h, Nat.zero_pow hn]
  · rw [show a % 2 = 1 by omega, Nat.one_pow]

/-- If one summand is a positive power of two and the other two exponents share
a divisor greater than one, the other two bases are even. -/
theorem even_of_power_of_two_summand {b c y z k : Nat} (hy : 2 < y) (hz : 2 < z)
    (hk : 0 < k) (hg : 1 < Nat.gcd y z) (heq : 2 ^ k + b ^ y = c ^ z) :
    2 ∣ b ∧ 2 ∣ c := by
  have hm := congrArg (fun t : Nat => t % 2) heq
  change (2 ^ k + b ^ y) % 2 = c ^ z % 2 at hm
  rw [Nat.add_mod, parity_pow hk, parity_pow (by omega : 0 < y),
    parity_pow (by omega : 0 < z)] at hm
  by_cases hb : b % 2 = 0
  · exact ⟨Nat.dvd_of_mod_eq_zero hb, Nat.dvd_of_mod_eq_zero (by omega)⟩
  · exact False.elim (lhs_two_power (by omega) (by omega) hy hz hg heq)

/-- If the sum is a power of two with exponent at least two and the summand
exponents share a divisor greater than one, both summand bases are even. -/
theorem even_of_power_of_two_sum {a b x y k : Nat} (hx : 0 < x) (hy : 0 < y)
    (hk : 2 ≤ k) (hg : 1 < Nat.gcd x y) (heq : a ^ x + b ^ y = 2 ^ k) :
    2 ∣ a ∧ 2 ∣ b := by
  have hm := congrArg (fun t : Nat => t % 2) heq
  change (a ^ x + b ^ y) % 2 = 2 ^ k % 2 at hm
  rw [Nat.add_mod, parity_pow hx, parity_pow hy, parity_pow (by omega : 0 < k)] at hm
  by_cases ha : a % 2 = 0
  · exact ⟨Nat.dvd_of_mod_eq_zero ha, Nat.dvd_of_mod_eq_zero (by omega)⟩
  · exact False.elim (BealSum.rhs_two_power (by omega) (by omega) hk hg heq)

end BealTwoPower

theorem even_pair_left (h2 : H2) {b c y z k : Nat}
    (hy : 2 < y) (hz : 2 < z) (hk : 2 < k) (heq : 2 ^ k + b ^ y = c ^ z) :
    2 ∣ b ∧ 2 ∣ c := by
  by_cases hg : 1 < Nat.gcd y z
  · exact BealTwoPower.even_of_power_of_two_summand hy hz (by omega) hg heq
  have hgpos := Nat.gcd_pos_of_pos_left z (show 0 < y by omega)
  have hm := congrArg (fun a : Nat => a % 2) heq
  change (2 ^ k + b ^ y) % 2 = c ^ z % 2 at hm
  rw [Nat.add_mod, BealTwoPower.parity_pow (by omega : 0 < k), BealTwoPower.parity_pow (by omega : 0 < y),
    BealTwoPower.parity_pow (by omega : 0 < z)] at hm
  by_cases he : b % 2 = 0
  · exact ⟨Nat.dvd_of_mod_eq_zero he, Nat.dvd_of_mod_eq_zero (by omega)⟩
  · exact False.elim (h2 (by omega) (by omega) hy hz hk (by omega) heq)

theorem even_pair_right (h3 : H3) {a b x y k : Nat}
    (hx : 2 < x) (hy : 2 < y) (hk : 2 < k) (heq : a ^ x + b ^ y = 2 ^ k) :
    2 ∣ a ∧ 2 ∣ b := by
  by_cases hg : 1 < Nat.gcd x y
  · exact BealTwoPower.even_of_power_of_two_sum (by omega) (by omega) (by omega) hg heq
  have hgpos := Nat.gcd_pos_of_pos_left y (show 0 < x by omega)
  have hm := congrArg (fun a : Nat => a % 2) heq
  change (a ^ x + b ^ y) % 2 = 2 ^ k % 2 at hm
  rw [Nat.add_mod, BealTwoPower.parity_pow (by omega : 0 < x), BealTwoPower.parity_pow (by omega : 0 < y),
    BealTwoPower.parity_pow (by omega : 0 < k)] at hm
  by_cases he : a % 2 = 0
  · exact ⟨Nat.dvd_of_mod_eq_zero he, Nat.dvd_of_mod_eq_zero (by omega)⟩
  · exact False.elim (h3 (by omega) (by omega) hx hy hk (by omega) heq)

theorem positive_power_even {j : Nat} (hj : 0 < j) : 2 ∣ 2 ^ j :=
  Nat.dvd_of_mod_eq_zero (BealTwoPower.parity_pow hj)

theorem large_product {j n : Nat} (hj : 0 < j) (hn : 2 < n) : 2 < j * n := by
  have := Nat.mul_le_mul_right n (show 1 ≤ j by omega)
  omega

theorem gcd_of_even {a b c : Nat} (ha : a ≠ 0)
    (ea : 2 ∣ a) (eb : 2 ∣ b) (ec : 2 ∣ c) : 1 < Nat.gcd a (Nat.gcd b c) :=
  Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by omega)) (Nat.dvd_gcd ea (Nat.dvd_gcd eb ec))

theorem cases_to_gcd (h1 : H1) (h2 : H2) (h3 : H3) {a b c x y z : Nat}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hx : 2 < x) (hy : 2 < y) (hz : 2 < z)
    (heq : a ^ x + b ^ y = c ^ z) : 1 < Nat.gcd a (Nat.gcd b c) := by
  by_cases ha2 : ∃ j : Nat, 0 < j ∧ a = 2 ^ j
  · obtain ⟨j, hj, rfl⟩ := ha2
    rw [← Nat.pow_mul] at heq
    obtain ⟨eb, ec⟩ := even_pair_left h2 hy hz (large_product hj hx) heq
    exact gcd_of_even ha (positive_power_even hj) eb ec
  by_cases hb2 : ∃ j : Nat, 0 < j ∧ b = 2 ^ j
  · obtain ⟨j, hj, rfl⟩ := hb2
    rw [← Nat.pow_mul, Nat.add_comm] at heq
    obtain ⟨ea, ec⟩ := even_pair_left h2 hx hz (large_product hj hy) heq
    exact gcd_of_even ha ea (positive_power_even hj) ec
  by_cases hc2 : ∃ j : Nat, 0 < j ∧ c = 2 ^ j
  · obtain ⟨j, hj, rfl⟩ := hc2
    rw [← Nat.pow_mul] at heq
    obtain ⟨ea, eb⟩ := even_pair_right h3 hx hy (large_product hj hz) heq
    exact gcd_of_even ha ea eb (positive_power_even hj)
  exact h1 ha hb hc hx hy hz ha2 hb2 hc2 heq

theorem main : H1 → H2 → H3 → type_of% @BealConjecture.beal_conjecture := by
  intro h1 h2 h3 a b c x y z ha hb hc hx hy hz heq
  simpa only [Finset.gcd_insert, Finset.gcd_singleton, id_eq, normalize_eq, gcd_eq_nat_gcd] using
    (cases_to_gcd h1 h2 h3 ha hb hc hx hy hz heq)

end OMA.R_BealConjecture_beal_conjecture_R2
