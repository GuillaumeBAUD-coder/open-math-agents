import OMAStatements.S_oeis_a036447

/-!
Proof of Vaclav Kotesovec's conjecture for OEIS A036447:
For n >= 8, a(n) enters a 4-phase decimal-digit automaton:
- n = 4*m:     2*m digits,     bot2 = 71,      top2 in {86, 88}
- n = 4*m + 1: 2*m + 1 digits, bot2 = 71,      top2 = 24
- n = 4*m + 2: 2*m + 1 digits, bot2 in {84,94}, top2 = 24
- n = 4*m + 3: 2*m + 1 digits, bot2 in {84,94}, top2 in {86, 88}
Hence 10^(n/2 - 1) <= a(n) <= 10^(n/2 + 1) for all n >= 8, so a(n)^(1/n) -> sqrt 10.
-/

namespace OMA.P_oeis_a036447

private def rev (x : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 x).reverse

private def rev2 (t : ℕ) : ℕ := 10 * (t % 10) + t / 10

private lemma digits_len_of_bounds {x d : ℕ} (hd : 1 ≤ d)
    (hlo : 10 ^ (d - 1) ≤ x) (hhi : x < 10 ^ d) :
    (Nat.digits 10 x).length = d := by
  have h10 : 1 ≤ 10 ^ (d - 1) := Nat.one_le_pow _ _ (by norm_num)
  have hxne : x ≠ 0 := by omega
  rw [Nat.length_digits 10 x (by norm_num) hxne]
  have hhi' : x < 10 ^ ((d - 1) + 1) := by rwa [Nat.sub_add_cancel hd]
  have hlog : Nat.log 10 x = d - 1 :=
    (Nat.log_eq_iff (Or.inr ⟨by norm_num, hxne⟩)).mpr ⟨hlo, hhi'⟩
  omega

private lemma rev_props {x d : ℕ} (hd : 4 ≤ d)
    (hlo : 10 ^ (d - 1) ≤ x) (hhi : x < 10 ^ d) (hx10 : x % 10 ≠ 0) :
    10 ^ (d - 1) ≤ rev x ∧ rev x < 10 ^ d ∧
      rev x % 100 = rev2 (x / 10 ^ (d - 2)) ∧ rev x / 10 ^ (d - 2) = rev2 (x % 100) := by
  set L := Nat.digits 10 x
  have hL_len : L.length = d := digits_len_of_bounds (by omega) hlo hhi
  have hL_lt : ∀ z ∈ L, z < 10 := fun z hz => Nat.digits_lt_base (by norm_num) hz
  have hL_of : Nat.ofDigits 10 L = x := Nat.ofDigits_digits 10 x
  have hpow10 : 10 ≤ 10 ^ (d - 1) := by
    have : 10 ^ 1 ≤ 10 ^ (d - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using this
  have hxne : x ≠ 0 := by omega
  have hxdiv_ne : x / 10 ≠ 0 := by omega
  have hL0 : L = (x % 10) :: Nat.digits 10 (x / 10) :=
    Nat.digits_eq_cons_digits_div (by norm_num) hxne
  have hL1 : Nat.digits 10 (x / 10) =
      ((x / 10) % 10) :: Nat.digits 10 ((x / 10) / 10) :=
    Nat.digits_eq_cons_digits_div (by norm_num) hxdiv_ne
  set mid := Nat.digits 10 ((x / 10) / 10)
  have hL_front : L = (x % 10) :: ((x / 10) % 10) :: mid := by rw [hL0, hL1]
  have hmid_len : mid.length = d - 2 := by
    have := congrArg List.length hL_front
    simp [hL_len] at this
    omega
  have hmid_lt : ∀ z ∈ mid.reverse, z < 10 := by
    intro z hz
    apply hL_lt z
    rw [hL_front]
    simp [List.mem_reverse.mp hz]
  have hmid_pow : Nat.ofDigits 10 mid.reverse < 10 ^ (d - 2) := by
    simpa [hmid_len] using Nat.ofDigits_lt_base_pow_length (b := 10) (by norm_num) hmid_lt
  have hrev_front :
      rev x = Nat.ofDigits 10 mid.reverse + 10 ^ (d - 2) * ((x / 10) % 10 + 10 * (x % 10)) := by
    rw [rev, show Nat.digits 10 x = L from rfl, hL_front]
    simp [List.reverse_cons, Nat.ofDigits_append, Nat.ofDigits, hmid_len]
  have hdiv_res : rev x / 10 ^ (d - 2) = rev2 (x % 100) := by
    rw [hrev_front, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hmid_pow, zero_add]
    simp only [rev2]
    omega
  have hd0_lo : 1 ≤ x % 10 := Nat.pos_of_ne_zero hx10
  have hd0_hi : x % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have hd1_hi : (x / 10) % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have hlead_lo : 10 ≤ (x / 10) % 10 + 10 * (x % 10) := by omega
  have hlead_hi : (x / 10) % 10 + 10 * (x % 10) + 1 ≤ 100 := by omega
  have hp1 : 10 ^ (d - 2) * 10 = 10 ^ (d - 1) := by
    rw [← pow_succ]
    congr 1
    omega
  have hp2 : 10 ^ (d - 2) * 100 = 10 ^ d := by
    rw [show (100 : ℕ) = 10 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  have hrev_lo : 10 ^ (d - 1) ≤ rev x := by
    calc 10 ^ (d - 1) = 10 ^ (d - 2) * 10 := hp1.symm
      _ ≤ 10 ^ (d - 2) * ((x / 10) % 10 + 10 * (x % 10)) := Nat.mul_le_mul_left _ hlead_lo
      _ ≤ rev x := by omega
  have hrev_hi : rev x < 10 ^ d := by
    calc rev x < 10 ^ (d - 2) + 10 ^ (d - 2) * ((x / 10) % 10 + 10 * (x % 10)) := by omega
      _ = 10 ^ (d - 2) * ((x / 10) % 10 + 10 * (x % 10) + 1) := by ring
      _ ≤ 10 ^ (d - 2) * 100 := Nat.mul_le_mul_left _ hlead_hi
      _ = 10 ^ d := hp2
  set front := L.take (d - 2)
  set back := L.drop (d - 2)
  have hL_back : L = front ++ back := (List.take_append_drop (d - 2) L).symm
  have hfront_len : front.length = d - 2 := List.length_take_of_le (by omega)
  have hback_len : back.length = 2 := by
    simp [back, hL_len]
    omega
  have hmod_res : rev x % 100 = rev2 (x / 10 ^ (d - 2)) := by
    rcases back with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp at hback_len
    · simp at hback_len
    · have hL_split : L = front ++ [a, b] := hL_back
      have ha : a < 10 := hL_lt a (by rw [hL_split]; simp)
      have hb : b < 10 := hL_lt b (by rw [hL_split]; simp)
      have hfront_lt : ∀ z ∈ front, z < 10 := fun z hz =>
        hL_lt z (by rw [hL_split]; simp [hz])
      have hfront_pow : Nat.ofDigits 10 front < 10 ^ (d - 2) := by
        simpa [hfront_len] using Nat.ofDigits_lt_base_pow_length (b := 10) (by norm_num) hfront_lt
      have hx_eq : x = Nat.ofDigits 10 front + 10 ^ (d - 2) * (a + 10 * b) := by
        rw [← hL_of, hL_split, Nat.ofDigits_append, hfront_len]
        simp [Nat.ofDigits]
      have hxdiv : x / 10 ^ (d - 2) = a + 10 * b := by
        rw [hx_eq, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hfront_pow, zero_add]
      have hrev_back : rev x = b + 10 * a + 100 * Nat.ofDigits 10 front.reverse := by
        rw [rev, show Nat.digits 10 x = L from rfl, hL_split, List.reverse_append]
        simp [Nat.ofDigits]
        ring
      have hmod1 : (b + 10 * a + 100 * Nat.ofDigits 10 front.reverse) % 100 = b + 10 * a := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      rw [hxdiv, hrev_back, hmod1]
      simp only [rev2]
      omega
    · simp at hback_len
  exact ⟨hrev_lo, hrev_hi, hmod_res, hdiv_res⟩

private def State0 (L x : ℕ) : Prop :=
  4 ≤ L ∧ 10 ^ (L - 1) ≤ x ∧ x < 10 ^ L ∧
    x % 100 = 71 ∧ (x / 10 ^ (L - 2) = 86 ∨ x / 10 ^ (L - 2) = 88)

private def State1 (L x : ℕ) : Prop :=
  4 ≤ L ∧ 10 ^ (L - 1) ≤ x ∧ x < 10 ^ L ∧
    x % 100 = 71 ∧ x / 10 ^ (L - 2) = 24

private def State2 (L x : ℕ) : Prop :=
  4 ≤ L ∧ 10 ^ (L - 1) ≤ x ∧ x < 10 ^ L ∧
    (x % 100 = 84 ∨ x % 100 = 94) ∧ x / 10 ^ (L - 2) = 24

private def State3 (L x : ℕ) : Prop :=
  4 ≤ L ∧ 10 ^ (L - 1) ≤ x ∧ x < 10 ^ L ∧
    (x % 100 = 84 ∨ x % 100 = 94) ∧ (x / 10 ^ (L - 2) = 86 ∨ x / 10 ^ (L - 2) = 88)

private lemma div_eq_of_bounds {a b q : ℕ} (hb : 0 < b) (hlo : q * b ≤ a) (hhi : a < (q + 1) * b) :
    a / b = q :=
  le_antisymm (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hb).mpr hhi))
    ((Nat.le_div_iff_mul_le hb).mpr hlo)

private lemma step01 {L x : ℕ} (h : State0 L x) : State1 (L + 1) (rev (2 * x)) := by
  rcases h with ⟨hL, _, _, hmod, hdiv⟩
  set p := 10 ^ (L - 2)
  have hp : 0 < p := by positivity
  have hdecomp : x = x % p + p * (x / p) := (Nat.mod_add_div x p).symm
  have hmodp : x % p < p := Nat.mod_lt x hp
  have h2x_range : 170 * p ≤ 2 * x ∧ 2 * x < 180 * p := by
    rcases hdiv with h86 | h88
    · rw [h86] at hdecomp; omega
    · rw [h88] at hdecomp; omega
  have hp10 : 10 ^ (L - 1) = 10 * p := by
    rw [show L - 1 = (L - 2) + 1 by omega, pow_succ]
    ring
  have hp100 : 10 ^ L = 100 * p := by
    rw [show L = (L - 2) + 2 by omega, pow_add]
    ring
  have hp1000 : 10 ^ (L + 1) = 1000 * p := by
    rw [show L + 1 = (L - 2) + 3 by omega, pow_add]
    ring
  have h2x_lo : 10 ^ L ≤ 2 * x := by rw [hp100]; omega
  have h2x_hi : 2 * x < 10 ^ (L + 1) := by rw [hp1000]; omega
  have h2x_div : 2 * x / 10 ^ (L - 1) = 17 := by
    rw [hp10]
    exact div_eq_of_bounds (by positivity) (by nlinarith) (by nlinarith)
  have h2x_mod : (2 * x) % 100 = 42 := by omega
  have h2x_nz : (2 * x) % 10 ≠ 0 := by omega
  obtain ⟨hrlo, hrhi, hrmod, hrdiv⟩ := rev_props (d := L + 1) (by omega) h2x_lo h2x_hi h2x_nz
  rw [Nat.add_sub_cancel] at hrlo
  rw [show L + 1 - 2 = L - 1 by omega] at hrmod hrdiv
  refine ⟨by omega, hrlo, hrhi, ?_, ?_⟩
  · rw [hrmod, h2x_div]
    decide
  · rw [show L + 1 - 2 = L - 1 by omega, hrdiv, h2x_mod]
    decide

private lemma step12 {L x : ℕ} (h : State1 L x) : State2 L (rev (2 * x)) := by
  rcases h with ⟨hL, _, _, hmod, hdiv⟩
  set p := 10 ^ (L - 2)
  have hp : 0 < p := by positivity
  have hdecomp : x = x % p + p * (x / p) := (Nat.mod_add_div x p).symm
  rw [hdiv] at hdecomp
  have hmodp : x % p < p := Nat.mod_lt x hp
  have h2x_range : 48 * p ≤ 2 * x ∧ 2 * x < 50 * p := by omega
  have hp10 : 10 ^ (L - 1) = 10 * p := by
    rw [show L - 1 = (L - 2) + 1 by omega, pow_succ]
    ring
  have hp100 : 10 ^ L = 100 * p := by
    rw [show L = (L - 2) + 2 by omega, pow_add]
    ring
  have h2x_lo : 10 ^ (L - 1) ≤ 2 * x := by rw [hp10]; omega
  have h2x_hi : 2 * x < 10 ^ L := by rw [hp100]; omega
  have h2x_div : 2 * x / p = 48 ∨ 2 * x / p = 49 := by
    by_cases hc : 2 * x < 49 * p
    · left; exact div_eq_of_bounds hp (by omega) hc
    · right; exact div_eq_of_bounds hp (by omega) (by omega)
  have h2x_mod : (2 * x) % 100 = 42 := by omega
  have h2x_nz : (2 * x) % 10 ≠ 0 := by omega
  obtain ⟨hrlo, hrhi, hrmod, hrdiv⟩ := rev_props (d := L) hL h2x_lo h2x_hi h2x_nz
  refine ⟨hL, hrlo, hrhi, ?_, ?_⟩
  · rw [hrmod]
    rcases h2x_div with h48 | h49
    · left; rw [h48]; decide
    · right; rw [h49]; decide
  · rw [hrdiv, h2x_mod]
    decide

private lemma step23 {L x : ℕ} (h : State2 L x) : State3 L (rev (2 * x)) := by
  rcases h with ⟨hL, _, _, hmod, hdiv⟩
  set p := 10 ^ (L - 2)
  have hp : 0 < p := by positivity
  have hdecomp : x = x % p + p * (x / p) := (Nat.mod_add_div x p).symm
  rw [hdiv] at hdecomp
  have hmodp : x % p < p := Nat.mod_lt x hp
  have h2x_range : 48 * p ≤ 2 * x ∧ 2 * x < 50 * p := by omega
  have hp10 : 10 ^ (L - 1) = 10 * p := by
    rw [show L - 1 = (L - 2) + 1 by omega, pow_succ]
    ring
  have hp100 : 10 ^ L = 100 * p := by
    rw [show L = (L - 2) + 2 by omega, pow_add]
    ring
  have h2x_lo : 10 ^ (L - 1) ≤ 2 * x := by rw [hp10]; omega
  have h2x_hi : 2 * x < 10 ^ L := by rw [hp100]; omega
  have h2x_div : 2 * x / p = 48 ∨ 2 * x / p = 49 := by
    by_cases hc : 2 * x < 49 * p
    · left; exact div_eq_of_bounds hp (by omega) hc
    · right; exact div_eq_of_bounds hp (by omega) (by omega)
  have h2x_mod : (2 * x) % 100 = 68 ∨ (2 * x) % 100 = 88 := by
    rcases hmod with h84 | h94 <;> omega
  have h2x_nz : (2 * x) % 10 ≠ 0 := by
    rcases h2x_mod with h68 | h88 <;> omega
  obtain ⟨hrlo, hrhi, hrmod, hrdiv⟩ := rev_props (d := L) hL h2x_lo h2x_hi h2x_nz
  refine ⟨hL, hrlo, hrhi, ?_, ?_⟩
  · rw [hrmod]
    rcases h2x_div with h48 | h49
    · left; rw [h48]; decide
    · right; rw [h49]; decide
  · rw [hrdiv]
    rcases h2x_mod with h68 | h88
    · left; rw [h68]; decide
    · right; rw [h88]; decide

private lemma step30 {L x : ℕ} (h : State3 L x) : State0 (L + 1) (rev (2 * x)) := by
  rcases h with ⟨hL, _, _, hmod, hdiv⟩
  set p := 10 ^ (L - 2)
  have hp : 0 < p := by positivity
  have hdecomp : x = x % p + p * (x / p) := (Nat.mod_add_div x p).symm
  have hmodp : x % p < p := Nat.mod_lt x hp
  have h2x_range : 170 * p ≤ 2 * x ∧ 2 * x < 180 * p := by
    rcases hdiv with h86 | h88
    · rw [h86] at hdecomp; omega
    · rw [h88] at hdecomp; omega
  have hp10 : 10 ^ (L - 1) = 10 * p := by
    rw [show L - 1 = (L - 2) + 1 by omega, pow_succ]
    ring
  have hp100 : 10 ^ L = 100 * p := by
    rw [show L = (L - 2) + 2 by omega, pow_add]
    ring
  have hp1000 : 10 ^ (L + 1) = 1000 * p := by
    rw [show L + 1 = (L - 2) + 3 by omega, pow_add]
    ring
  have h2x_lo : 10 ^ L ≤ 2 * x := by rw [hp100]; omega
  have h2x_hi : 2 * x < 10 ^ (L + 1) := by rw [hp1000]; omega
  have h2x_div : 2 * x / 10 ^ (L - 1) = 17 := by
    rw [hp10]
    exact div_eq_of_bounds (by positivity) (by nlinarith) (by nlinarith)
  have h2x_mod : (2 * x) % 100 = 68 ∨ (2 * x) % 100 = 88 := by
    rcases hmod with h84 | h94 <;> omega
  have h2x_nz : (2 * x) % 10 ≠ 0 := by
    rcases h2x_mod with h68 | h88 <;> omega
  obtain ⟨hrlo, hrhi, hrmod, hrdiv⟩ := rev_props (d := L + 1) (by omega) h2x_lo h2x_hi h2x_nz
  rw [Nat.add_sub_cancel] at hrlo
  rw [show L + 1 - 2 = L - 1 by omega] at hrmod hrdiv
  refine ⟨by omega, hrlo, hrhi, ?_, ?_⟩
  · rw [hrmod, h2x_div]
    decide
  · rw [show L + 1 - 2 = L - 1 by omega, hrdiv]
    rcases h2x_mod with h68 | h88
    · left; rw [h68]; decide
    · right; rw [h88]; decide

private lemma a_succ_eq (n : ℕ) :
    OMA.S_oeis_a036447.a (n + 1) = rev (2 * OMA.S_oeis_a036447.a n) := rfl

private lemma a_8_eq : OMA.S_oeis_a036447.a 8 = 8671 := by decide

private lemma state0_loop : ∀ m : ℕ, State0 (2 * (m + 2)) (OMA.S_oeis_a036447.a (4 * (m + 2))) := by
  intro m
  induction m with
  | zero =>
    rw [show 2 * (0 + 2) = 4 by rfl, show 4 * (0 + 2) = 8 by rfl, a_8_eq]
    refine ⟨by omega, by decide, by decide, by decide, Or.inl (by decide)⟩
  | succ m ih =>
    have h1 : State1 (2 * (m + 2) + 1) (OMA.S_oeis_a036447.a (4 * (m + 2) + 1)) := by
      rw [a_succ_eq]; exact step01 ih
    have h2 : State2 (2 * (m + 2) + 1) (OMA.S_oeis_a036447.a (4 * (m + 2) + 2)) := by
      rw [a_succ_eq]; exact step12 h1
    have h3 : State3 (2 * (m + 2) + 1) (OMA.S_oeis_a036447.a (4 * (m + 2) + 3)) := by
      rw [a_succ_eq]; exact step23 h2
    have h0 : State0 (2 * (m + 2) + 2) (OMA.S_oeis_a036447.a (4 * (m + 2) + 4)) := by
      rw [a_succ_eq]; exact step30 h3
    simpa [Nat.mul_add, Nat.add_assoc] using h0

private lemma a_bounds {n : ℕ} (hn : 8 ≤ n) :
    10 ^ (n / 2 - 1) ≤ OMA.S_oeis_a036447.a n ∧
      OMA.S_oeis_a036447.a n ≤ 10 ^ (n / 2 + 1) := by
  set m := n / 4 - 2
  have h0 := state0_loop m
  have h1 : State1 (2 * (m + 2) + 1) (OMA.S_oeis_a036447.a (4 * (m + 2) + 1)) := by
    rw [a_succ_eq]; exact step01 h0
  have h2 : State2 (2 * (m + 2) + 1) (OMA.S_oeis_a036447.a (4 * (m + 2) + 2)) := by
    rw [a_succ_eq]; exact step12 h1
  have h3 : State3 (2 * (m + 2) + 1) (OMA.S_oeis_a036447.a (4 * (m + 2) + 3)) := by
    rw [a_succ_eq]; exact step23 h2
  rcases (by omega : n = 4 * (m + 2) ∨ n = 4 * (m + 2) + 1 ∨
      n = 4 * (m + 2) + 2 ∨ n = 4 * (m + 2) + 3) with hn_eq | hn_eq | hn_eq | hn_eq
  · rw [hn_eq]
    rcases h0 with ⟨_, hlo, hhi, _, _⟩
    have hlo' : 10 ^ ((4 * (m + 2)) / 2 - 1) ≤ 10 ^ (2 * (m + 2) - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hhi' : 10 ^ (2 * (m + 2)) ≤ 10 ^ ((4 * (m + 2)) / 2 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · rw [hn_eq]
    rcases h1 with ⟨_, hlo, hhi, _, _⟩
    have hlo' : 10 ^ ((4 * (m + 2) + 1) / 2 - 1) ≤ 10 ^ (2 * (m + 2)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hhi' : 10 ^ (2 * (m + 2) + 1) ≤ 10 ^ ((4 * (m + 2) + 1) / 2 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.add_sub_cancel] at hlo
    omega
  · rw [hn_eq]
    rcases h2 with ⟨_, hlo, hhi, _, _⟩
    have hlo' : 10 ^ ((4 * (m + 2) + 2) / 2 - 1) ≤ 10 ^ (2 * (m + 2)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hhi' : 10 ^ (2 * (m + 2) + 1) ≤ 10 ^ ((4 * (m + 2) + 2) / 2 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.add_sub_cancel] at hlo
    omega
  · rw [hn_eq]
    rcases h3 with ⟨_, hlo, hhi, _, _⟩
    have hlo' : 10 ^ ((4 * (m + 2) + 3) / 2 - 1) ≤ 10 ^ (2 * (m + 2)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hhi' : 10 ^ (2 * (m + 2) + 1) ≤ 10 ^ ((4 * (m + 2) + 3) / 2 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.add_sub_cancel] at hlo
    omega

end OMA.P_oeis_a036447

theorem OMA.solution : type_of% @OMA.S_oeis_a036447.main := by
  have hexp_inv : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hexp_lo :
      Filter.Tendsto (fun n : ℕ => ((n / 2 - 1 : ℕ) : ℝ) / (n : ℝ))
        Filter.atTop (nhds (1 / 2 : ℝ)) := by
    have hleft : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / 2 - (3 : ℝ) / 2 * ((1 : ℝ) / (n : ℝ)))
        Filter.atTop (nhds (1 / 2 : ℝ)) := by
      simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hexp_inv)
    have hright : Filter.Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) Filter.atTop (nhds (1 / 2 : ℝ)) :=
      tendsto_const_nhds
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hleft hright ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
      have hdiv : n ≤ 2 * (n / 2 - 1) + 3 := by omega
      have hdivR : (n : ℝ) ≤ 2 * ((n / 2 - 1 : ℕ) : ℝ) + 3 := by exact_mod_cast hdiv
      have hmul : ((1 : ℝ) / 2 - (3 : ℝ) / 2 * ((1 : ℝ) / (n : ℝ))) * (n : ℝ) =
          ((n : ℝ) - 3) / 2 := by
        field_simp [ne_of_gt hn_pos]
      rw [le_div_iff₀ hn_pos, hmul]
      linarith
    · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
      have hdiv : 2 * (n / 2 - 1) ≤ n := by omega
      have hdivR : 2 * ((n / 2 - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdiv
      rw [div_le_iff₀ hn_pos]
      linarith
  have hexp_hi :
      Filter.Tendsto (fun n : ℕ => ((n / 2 + 1 : ℕ) : ℝ) / (n : ℝ))
        Filter.atTop (nhds (1 / 2 : ℝ)) := by
    have hleft : Filter.Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) Filter.atTop (nhds (1 / 2 : ℝ)) :=
      tendsto_const_nhds
    have hright : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / 2 + (1 : ℝ) / (n : ℝ))
        Filter.atTop (nhds (1 / 2 : ℝ)) := by
      simpa using tendsto_const_nhds.add hexp_inv
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hleft hright ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
      have hdiv : n ≤ 2 * (n / 2 + 1) := by omega
      have hdivR : (n : ℝ) ≤ 2 * ((n / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast hdiv
      rw [le_div_iff₀ hn_pos]
      linarith
    · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
      have hdiv : 2 * (n / 2 + 1) ≤ n + 2 := by omega
      have hdivR : 2 * ((n / 2 + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 2 := by exact_mod_cast hdiv
      have hmul : ((1 : ℝ) / 2 + (1 : ℝ) / (n : ℝ)) * (n : ℝ) = ((n : ℝ) + 2) / 2 := by
        field_simp [ne_of_gt hn_pos]
      rw [div_le_iff₀ hn_pos, hmul]
      linarith
  have hlim_lo :
      Filter.Tendsto (fun n : ℕ => (10 : ℝ) ^ (((n / 2 - 1 : ℕ) : ℝ) / (n : ℝ)))
        Filter.atTop (nhds (Real.sqrt 10)) := by
    rw [Real.sqrt_eq_rpow]
    exact tendsto_const_nhds.rpow hexp_lo (Or.inl (by norm_num))
  have hlim_hi :
      Filter.Tendsto (fun n : ℕ => (10 : ℝ) ^ (((n / 2 + 1 : ℕ) : ℝ) / (n : ℝ)))
        Filter.atTop (nhds (Real.sqrt 10)) := by
    rw [Real.sqrt_eq_rpow]
    exact tendsto_const_nhds.rpow hexp_hi (Or.inl (by norm_num))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim_lo hlim_hi ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 8] with n hn
    have hb := (OMA.P_oeis_a036447.a_bounds hn).1
    have hbR : (10 : ℝ) ^ (n / 2 - 1 : ℕ) ≤ (OMA.S_oeis_a036447.a n : ℝ) := by
      exact_mod_cast hb
    have hrpow := Real.rpow_le_rpow (by positivity) hbR (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))
    rw [← Real.rpow_natCast (10 : ℝ), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10),
      mul_one_div] at hrpow
    exact hrpow
  · filter_upwards [Filter.eventually_ge_atTop 8] with n hn
    have hb := (OMA.P_oeis_a036447.a_bounds hn).2
    have hbR : (OMA.S_oeis_a036447.a n : ℝ) ≤ (10 : ℝ) ^ (n / 2 + 1 : ℕ) := by
      exact_mod_cast hb
    have hrpow := Real.rpow_le_rpow (by positivity) hbR (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))
    rw [← Real.rpow_natCast (10 : ℝ), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10),
      mul_one_div] at hrpow
    exact hrpow
