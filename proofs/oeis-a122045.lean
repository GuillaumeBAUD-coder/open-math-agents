import OMAStatements.S_oeis_a122045

namespace OMA.S_oeis_a122045

open Finset




/-! ### The Euler recurrence in convolution form -/

theorem E_zero : E 0 = 1 := by rw [E]

theorem E_succ (n : ℕ) : E (n + 1) =
    -∑ k : Fin ((n + 1) / 2), ((n + 1).choose (2 * (k + 1)) : ℤ) * E (n + 1 - 2 * (k + 1)) := by
  rw [E]

theorem even_sum (f : ℕ → ℤ) (n : ℕ) :
    ∑ j ∈ range (n + 1), (if Even j then f j else 0) = ∑ k ∈ range (n / 2 + 1), f (2 * k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    rcases Nat.even_or_odd (n + 1) with h | h
    · rw [if_pos h]
      obtain ⟨t, ht⟩ := h
      have e : (n + 1) / 2 = n / 2 + 1 := by omega
      rw [e, sum_range_succ (fun k => f (2 * k)) (n / 2 + 1)]
      congr 2
      omega
    · rw [if_neg (Nat.not_even_iff_odd.mpr h), add_zero]
      obtain ⟨t, ht⟩ := h
      have e : (n + 1) / 2 = n / 2 := by omega
      rw [e]

/-- For `n ≥ 1`, `∑_{j even} C(n, j) E (n - j) = 0`. -/
theorem E_rec (n : ℕ) :
    ∑ j ∈ range (n + 1 + 1), (if Even j then ((n + 1).choose j : ℤ) * E (n + 1 - j) else 0) = 0 := by
  rw [even_sum (fun j => ((n + 1).choose j : ℤ) * E (n + 1 - j)) (n + 1), sum_range_succ']
  simp only [mul_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
  rw [E_succ, Fin.sum_univ_eq_sum_range (fun k => ((n + 1).choose (2 * (k + 1)) : ℤ) *
    E (n + 1 - 2 * (k + 1)))]
  ring

/-! ### The alternating power sums `S N n = ∑_{a < N} (-1)^a (2a+1)^n` -/

/-- `S N n = ∑_{a < N} (-1)^a (2a+1)^n`. -/
def S (N n : ℕ) : ℤ := ∑ a ∈ range N, (-1 : ℤ) ^ a * (2 * (a : ℤ) + 1) ^ n

theorem alt_sum (t : ℕ) : ∑ a ∈ range (2 * t + 1), (-1 : ℤ) ^ a = 1 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show 2 * (t + 1) + 1 = 2 * t + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih]
    rw [(show Odd (2 * t + 1) from ⟨t, rfl⟩).neg_one_pow,
      (show Even (2 * t + 1 + 1) from ⟨t + 1, by ring⟩).neg_one_pow]
    ring

theorem binom_even (x : ℤ) (n : ℕ) :
    2 * ∑ j ∈ range (n + 1), (if Even j then (n.choose j : ℤ) * x ^ (n - j) else 0) =
      (1 + x) ^ n + (-1 + x) ^ n := by
  rw [add_pow, add_pow, ← sum_add_distrib, mul_sum]
  refine sum_congr rfl (fun j _ => ?_)
  split_ifs with h
  · rw [h.neg_one_pow]
    ring
  · rw [(Nat.not_even_iff_odd.mp h).neg_one_pow]
    ring

/-- For odd `N` and `n ≥ 1`, `2 ∑_{j even} C(n, j) S N (n - j) = (2N)^n` (a telescoping sum). -/
theorem T_eq (t n : ℕ) (hn : 1 ≤ n) :
    2 * ∑ j ∈ range (n + 1), (if Even j then (n.choose j : ℤ) * S (2 * t + 1) (n - j) else 0) =
      (2 * (2 * (t : ℤ) + 1)) ^ n := by
  have step : ∀ j, (if Even j then (n.choose j : ℤ) * S (2 * t + 1) (n - j) else 0) =
      ∑ a ∈ range (2 * t + 1), (-1 : ℤ) ^ a *
        (if Even j then (n.choose j : ℤ) * (2 * (a : ℤ) + 1) ^ (n - j) else 0) := by
    intro j
    split_ifs
    · rw [S, mul_sum]
      refine sum_congr rfl (fun a _ => ?_)
      ring
    · simp
  rw [sum_congr rfl (fun j _ => step j), sum_comm, mul_sum]
  have step2 : ∀ a : ℕ, 2 * ∑ j ∈ range (n + 1), (-1 : ℤ) ^ a *
      (if Even j then (n.choose j : ℤ) * (2 * (a : ℤ) + 1) ^ (n - j) else 0) =
        (-1 : ℤ) ^ a * ((2 * (a : ℤ) + 2) ^ n + (2 * (a : ℤ)) ^ n) := by
    intro a
    have hb := binom_even (2 * (a : ℤ) + 1) n
    rw [show (1 + (2 * (a : ℤ) + 1)) = 2 * a + 2 by ring,
      show (-1 + (2 * (a : ℤ) + 1)) = 2 * a by ring] at hb
    rw [← mul_sum, ← hb]
    ring
  rw [sum_congr rfl (fun a _ => step2 a)]
  have step3 : ∀ a : ℕ, (-1 : ℤ) ^ a * ((2 * (a : ℤ) + 2) ^ n + (2 * (a : ℤ)) ^ n) =
      (-1 : ℤ) ^ a * (2 * (a : ℤ)) ^ n - (-1 : ℤ) ^ (a + 1) * (2 * ((a + 1 : ℕ) : ℤ)) ^ n := by
    intro a
    push_cast
    ring
  rw [sum_congr rfl (fun a _ => step3 a),
    sum_range_sub' (fun a : ℕ => (-1 : ℤ) ^ a * (2 * (a : ℤ)) ^ n)]
  rw [(show Odd (2 * t + 1) from ⟨t, rfl⟩).neg_one_pow]
  simp only [pow_zero, Nat.cast_zero, mul_zero, zero_pow (by omega : n ≠ 0)]
  push_cast
  ring

/-- For odd `N`, `E n ≡ S N n (mod N)`. -/
theorem cong (t : ℕ) : ∀ n : ℕ, ((2 * t + 1 : ℕ) : ℤ) ∣ E n - S (2 * t + 1) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · have h0 : S (2 * t + 1) 0 = 1 := by
        rw [S]
        simp
      rw [E_zero, h0, sub_self]
      exact dvd_zero _
    · have hE := E_rec n
      have hT := T_eq t (n + 1) (by omega)
      have hX : ((2 * t + 1 : ℕ) : ℤ) ∣ ∑ j ∈ range (n + 1 + 1),
          (if Even j then ((n + 1).choose j : ℤ) * S (2 * t + 1) (n + 1 - j) else 0) := by
        have h2 : (2 : ℤ) * ∑ j ∈ range (n + 1 + 1),
            (if Even j then ((n + 1).choose j : ℤ) * S (2 * t + 1) (n + 1 - j) else 0) =
              2 * ((2 * (t : ℤ) + 1) * (2 * (2 * (t : ℤ) + 1)) ^ n) := by
          rw [hT]
          ring
        rw [mul_left_cancel₀ two_ne_zero h2]
        push_cast
        exact dvd_mul_right _ _
      have hD : ∑ j ∈ range (n + 1 + 1), (if Even j then ((n + 1).choose j : ℤ) *
          (E (n + 1 - j) - S (2 * t + 1) (n + 1 - j)) else 0) =
          ∑ j ∈ range (n + 1 + 1), (if Even j then ((n + 1).choose j : ℤ) * E (n + 1 - j) else 0) -
          ∑ j ∈ range (n + 1 + 1),
            (if Even j then ((n + 1).choose j : ℤ) * S (2 * t + 1) (n + 1 - j) else 0) := by
        rw [← sum_sub_distrib]
        refine sum_congr rfl (fun j _ => ?_)
        split_ifs <;> ring
      have hND : ((2 * t + 1 : ℕ) : ℤ) ∣ ∑ j ∈ range (n + 1 + 1), (if Even j then
          ((n + 1).choose j : ℤ) * (E (n + 1 - j) - S (2 * t + 1) (n + 1 - j)) else 0) := by
        rw [hD, hE, zero_sub]
        exact (dvd_neg).mpr hX
      rw [sum_range_succ', if_pos (show Even 0 from ⟨0, rfl⟩)] at hND
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero] at hND
      have hrest : ((2 * t + 1 : ℕ) : ℤ) ∣ ∑ j ∈ range (n + 1), (if Even (j + 1) then
          ((n + 1).choose (j + 1) : ℤ) * (E (n + 1 - (j + 1)) - S (2 * t + 1) (n + 1 - (j + 1)))
          else 0) := by
        apply dvd_sum
        intro j hj
        split_ifs
        · exact Dvd.dvd.mul_left (ih _ (by omega)) _
        · exact dvd_zero _
      exact (dvd_add_right hrest).mp hND

/-! ### Kernel arithmetic -/

/-- `acc * b ^ e % m` by repeated squaring; `fuel` bounds the number of bits of `e`. -/
def powMod (m fuel : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => Nat.mod acc m)
    (fun _ ih b e acc => cond (Nat.beq e 0) (Nat.mod acc m)
      (ih (Nat.mod (Nat.mul b b) m) (Nat.div e 2)
        (cond (Nat.beq (Nat.mod e 2) 1) (Nat.mod (Nat.mul acc b) m) acc))) fuel

theorem beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem beq_true {a b : ℕ} (h : a = b) : Nat.beq a b = true := by
  subst h
  exact Nat.beq_refl a

theorem powMod_zero (m b e acc : ℕ) : powMod m 0 b e acc = acc % m := rfl

theorem powMod_succ (m fuel b e acc : ℕ) : powMod m (fuel + 1) b e acc =
    if e = 0 then acc % m
    else powMod m fuel (b * b % m) (e / 2) (if e % 2 = 1 then acc * b % m else acc) := by
  show cond (Nat.beq e 0) _ _ = _
  by_cases h0 : e = 0
  · subst h0; rfl
  · rw [beq_false h0, if_neg h0]
    show powMod m fuel (Nat.mod (Nat.mul b b) m) (Nat.div e 2)
      (cond (Nat.beq (Nat.mod e 2) 1) (Nat.mod (Nat.mul acc b) m) acc) = _
    by_cases h2 : e % 2 = 1
    · have h2' : Nat.mod e 2 = 1 := h2
      rw [beq_true h2', if_pos h2]; rfl
    · have h2' : Nat.mod e 2 ≠ 1 := h2
      rw [beq_false h2', if_neg h2]; rfl

theorem powMod_spec (m : ℕ) : ∀ fuel b e acc, e < 2 ^ fuel →
    powMod m fuel b e acc = acc * b ^ e % m := by
  intro fuel
  induction fuel with
  | zero =>
    intro b e acc he
    have : e = 0 := by simpa using he
    subst this
    simp [powMod_zero]
  | succ fuel ih =>
    intro b e acc he
    rw [powMod_succ]
    by_cases h0 : e = 0
    · subst h0
      simp
    · have he2 : e / 2 < 2 ^ fuel := by
        rw [pow_succ] at he
        omega
      rw [if_neg h0, ih _ _ _ he2]
      have hb : (b * b % m) ^ (e / 2) ≡ b ^ (2 * (e / 2)) [MOD m] := by
        rw [pow_mul, sq]
        exact (Nat.mod_modEq _ _).pow _
      rcases Nat.mod_two_eq_zero_or_one e with hr | hr
      · rw [if_neg (by omega)]
        have he' : e = 2 * (e / 2) := by omega
        have := hb.mul_left acc
        rw [← he'] at this
        exact this
      · rw [if_pos hr]
        have he' : b ^ e = b * b ^ (2 * (e / 2)) := by
          rw [← pow_succ']
          congr 1
          omega
        have := (Nat.mod_modEq (acc * b) m).mul hb
        rw [he', ← mul_assoc]
        exact this

/-- `∑_{a < k}` of `(2a+1)^n mod p` for even `a` and `p - ((2a+1)^n mod p)` for odd `a`. -/
def chk (p n : ℕ) : ℕ → ℕ :=
  Nat.rec 0 (fun a ih => Nat.add ih (cond (Nat.beq (Nat.mod a 2) 0)
    (powMod p 64 (Nat.add (Nat.mul 2 a) 1) n 1) (Nat.sub p (powMod p 64 (Nat.add (Nat.mul 2 a) 1) n 1))))

theorem chk_succ (p n a : ℕ) : chk p n (a + 1) = chk p n a +
    (if a % 2 = 0 then powMod p 64 (2 * a + 1) n 1 else p - powMod p 64 (2 * a + 1) n 1) := by
  show Nat.add (chk p n a) (cond (Nat.beq (Nat.mod a 2) 0) _ _) = _
  by_cases h : a % 2 = 0
  · have h' : Nat.mod a 2 = 0 := h
    rw [beq_true h', if_pos h]; rfl
  · have h' : Nat.mod a 2 ≠ 0 := h
    rw [beq_false h', if_neg h]; rfl

/-- `S p n ≡ chk p n p (mod p)` when the exponent fits in 64 bits. -/
theorem S_cong (p n : ℕ) (hp : 0 < p) (hn : n < 2 ^ 64) :
    ∀ k, (p : ℤ) ∣ (∑ a ∈ range k, (-1 : ℤ) ^ a * (2 * (a : ℤ) + 1) ^ n) - (chk p n k : ℤ) := by
  intro k
  induction k with
  | zero => simp [chk]
  | succ k ih =>
    rw [sum_range_succ, chk_succ, powMod_spec p 64 _ _ _ hn, one_mul]
    have hr : (2 * k + 1) ^ n % p ≤ p := (Nat.mod_lt _ hp).le
    have hm : (p : ℤ) ∣ (2 * (k : ℤ) + 1) ^ n - (((2 * k + 1) ^ n % p : ℕ) : ℤ) := by
      rw [Int.natCast_mod]
      push_cast
      exact (Int.mod_modEq _ _).dvd
    split_ifs with h
    · rw [(Nat.even_iff.mpr h).neg_one_pow]
      push_cast
      have := dvd_add ih hm
      ring_nf at this ⊢
      exact this
    · rw [(Nat.odd_iff.mpr (by omega)).neg_one_pow]
      rw [Nat.cast_add, Nat.cast_sub hr]
      have := dvd_sub (dvd_sub ih hm) (dvd_refl (p : ℤ))
      ring_nf at this ⊢
      exact this

/-- `p ∣ E n` from the kernel check `chk p n p ≡ 0 (mod p)`, for odd `p = 2t + 1`. -/
theorem dvd_E (t n : ℕ) (hn : n < 2 ^ 64) (h : chk (2 * t + 1) n (2 * t + 1) % (2 * t + 1) = 0) :
    ((2 * t + 1 : ℕ) : ℤ) ∣ E n := by
  have h1 := cong t n
  have h2 := S_cong (2 * t + 1) n (by omega) hn (2 * t + 1)
  have h3 : ((2 * t + 1 : ℕ) : ℤ) ∣ (chk (2 * t + 1) n (2 * t + 1) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero h)
  have : E n = (E n - S (2 * t + 1) n) + (S (2 * t + 1) n - chk (2 * t + 1) n (2 * t + 1)) +
      (chk (2 * t + 1) n (2 * t + 1) : ℤ) := by ring
  rw [this]
  exact dvd_add (dvd_add h1 (by simpa [S] using h2)) h3

/-! ### The counterexample `m = 373745 = 5 * 17 * 4397` -/

theorem dvd5 : (5 : ℤ) ∣ E 373744 := by
  have := dvd_E 2 373744 (by norm_num) (by decide +kernel)
  simpa using this

theorem dvd17 : (17 : ℤ) ∣ E 373744 := by
  have := dvd_E 8 373744 (by norm_num) (by decide +kernel)
  simpa using this

theorem dvd4397 : (4397 : ℤ) ∣ E 373744 := by
  have := dvd_E 2198 373744 (by norm_num) (by decide +kernel)
  simpa using this

theorem dvd_m : (373745 : ℤ) ∣ E 373744 := by
  have h85 : (85 : ℤ) ∣ E 373744 := by
    have := IsCoprime.mul_dvd (show IsCoprime (5 : ℤ) 17 by
      rw [Int.isCoprime_iff_gcd_eq_one]; rfl) dvd5 dvd17
    simpa using this
  have := IsCoprime.mul_dvd (show IsCoprime (85 : ℤ) 4397 by
    rw [Int.isCoprime_iff_gcd_eq_one]; rfl) h85 dvd4397
  simpa using this

theorem not_carmichael : ¬ IsCarmichael 373745 := by
  rintro ⟨-, -, h⟩
  have h2 : 2 ^ (373745 - 1) % 373745 = 1 := h 2 (by norm_num)
  have e : 2 ^ (373745 - 1) % 373745 = powMod 373745 64 2 373744 1 := by
    rw [powMod_spec 373745 64 2 373744 1 (by norm_num), one_mul]
  have hv : powMod 373745 64 2 373744 1 = 318581 := by decide +kernel
  rw [e, hv] at h2
  exact absurd h2 (by decide)

/-- Control: the smallest odd composite dividing its Euler number, 1105 = 5 * 13 * 17, a
Carmichael number with all prime factors `≡ 1 (mod 4)`. -/
theorem control : (5 : ℤ) ∣ E 1104 ∧ (13 : ℤ) ∣ E 1104 ∧ (17 : ℤ) ∣ E 1104 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using dvd_E 2 1104 (by norm_num) (by decide +kernel)
  · simpa using dvd_E 6 1104 (by norm_num) (by decide +kernel)
  · simpa using dvd_E 8 1104 (by norm_num) (by decide +kernel)

theorem disproof :
    ¬ ((∀ p : ℕ, p.Prime → p ≠ 2 → ((p : ℤ) ∣ E (p - 1) ↔ p % 4 = 1)) ∧
      (∀ m : ℕ, Odd m → 1 < m → ¬ m.Prime → ((m : ℤ) ∣ E (m - 1) ↔ InA265237 m))) := by
  rintro ⟨-, h⟩
  have hm := h 373745 ⟨186872, by norm_num⟩ (by norm_num) (by norm_num)
  have hd : ((373745 : ℕ) : ℤ) ∣ E (373745 - 1) := by
    rw [show 373745 - 1 = 373744 by norm_num]
    exact_mod_cast dvd_m
  exact not_carmichael (hm.mp hd).1

end OMA.S_oeis_a122045

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a122045.main) :=
  OMA.S_oeis_a122045.disproof
