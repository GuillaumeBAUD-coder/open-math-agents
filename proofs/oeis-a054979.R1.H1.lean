import OMAReductions.R_oeis_a054979_R1

open OMA.S_oeis_a054979
open scoped BigOperators

namespace OMA.A054979

def S (p e : ℕ) : ℕ := ∑ b ∈ e.divisors, p ^ b
def F (p e : ℕ) : ℚ := (S p e : ℚ) / (p : ℚ) ^ e

lemma S_pos {p e : ℕ} (hp : 0 < p) (he : e ≠ 0) : 0 < S p e := by
  have hmem : e ∈ e.divisors := Nat.mem_divisors_self e he
  have hle : p ^ e ≤ S p e :=
    Finset.single_le_sum (f := fun b => p ^ b) (fun b _ => Nat.zero_le _) hmem
  exact lt_of_lt_of_le (pow_pos hp e) hle

lemma F_eq {p e : ℕ} (hp : 0 < p) (he : e ≠ 0) :
    F p e = 1 + ((∑ b ∈ e.divisors.erase e, (p : ℚ) ^ b) / (p : ℚ) ^ e) := by
  have hmem : e ∈ e.divisors := Nat.mem_divisors_self e he
  have hcast : (S p e : ℚ) = ∑ b ∈ e.divisors, (p : ℚ) ^ b := by
    simp [S]
  have hdecomp : (∑ b ∈ e.divisors, (p : ℚ) ^ b) =
      (p : ℚ) ^ e + ∑ b ∈ e.divisors.erase e, (p : ℚ) ^ b := by
    rw [← Finset.add_sum_erase _ (fun b => (p : ℚ) ^ b) hmem]
  have hpe : (p : ℚ) ^ e ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne')
  unfold F
  rw [hcast, hdecomp]
  field_simp

lemma F_one {p : ℕ} (hp : 0 < p) : F p 1 = 1 := by
  have hS : S p 1 = p := by simp [S, Nat.divisors_one]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold F
  rw [hS]
  field_simp

lemma F_two {p : ℕ} (hp : 0 < p) : F p 2 = 1 + 1 / (p : ℚ) := by
  have hS : S p 2 = p + p ^ 2 := by
    have hd : (2 : ℕ).divisors = {1, 2} := by decide
    simp [S, hd, Finset.sum_insert, Finset.sum_singleton]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold F
  rw [hS]
  push_cast
  field_simp
  ring

lemma F_three {p : ℕ} (hp : 0 < p) : F p 3 = 1 + 1 / (p : ℚ) ^ 2 := by
  have hS : S p 3 = p + p ^ 3 := by
    have hd : (3 : ℕ).divisors = {1, 3} := by decide
    simp [S, hd, Finset.sum_insert, Finset.sum_singleton]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold F
  rw [hS]
  push_cast
  field_simp
  ring

lemma F_four {p : ℕ} (hp : 0 < p) : F p 4 = 1 + ((p : ℚ) + (p : ℚ) ^ 2) / (p : ℚ) ^ 4 := by
  have hS : S p 4 = p + p ^ 2 + p ^ 4 := by
    have hd : (4 : ℕ).divisors = {1, 2, 4} := by decide
    simp [S, hd, Finset.sum_insert, Finset.sum_singleton]
    ring
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold F
  rw [hS]
  push_cast
  field_simp
  ring

lemma le_half_of_mem_erase {b e : ℕ} (hb : b ∈ e.divisors.erase e) : b ≤ e / 2 := by
  rw [Finset.mem_erase] at hb
  obtain ⟨hne, hmem⟩ := hb
  obtain ⟨hbdvd, he0⟩ := Nat.mem_divisors.mp hmem
  have hble : b ≤ e := Nat.divisor_le hmem
  have hblt : b < e := lt_of_le_of_ne hble hne
  obtain ⟨c, rfl⟩ := hbdvd
  have hc2 : 2 ≤ c := by
    by_contra hc
    interval_cases c
    · simp at he0
    · simp at hne
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  nlinarith

lemma sum_erase_le {p e : ℕ} (hp : 2 ≤ p) (_he : 0 < e) :
    (∑ b ∈ e.divisors.erase e, (p : ℚ) ^ b) ≤ (e : ℚ) * (p : ℚ) ^ (e / 2) := by
  have hterm : ∀ b ∈ e.divisors.erase e, (p : ℚ) ^ b ≤ (p : ℚ) ^ (e / 2) := by
    intro b hb
    have hb2 : b ≤ e / 2 := le_half_of_mem_erase hb
    exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ p by omega)) hb2
  have hcard : (e.divisors.erase e).card ≤ e :=
    le_trans (Finset.card_le_card (Finset.erase_subset _ _)) (Nat.card_divisors_le_self e)
  calc
    (∑ b ∈ e.divisors.erase e, (p : ℚ) ^ b)
        ≤ ∑ _b ∈ e.divisors.erase e, (p : ℚ) ^ (e / 2) := Finset.sum_le_sum hterm
    _ = ((e.divisors.erase e).card : ℚ) * (p : ℚ) ^ (e / 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (e : ℚ) * (p : ℚ) ^ (e / 2) := by
        have hc : ((e.divisors.erase e).card : ℚ) ≤ (e : ℚ) := by exact_mod_cast hcard
        have hx : (0 : ℚ) ≤ (p : ℚ) ^ (e / 2) := by positivity
        exact mul_le_mul_of_nonneg_right hc hx

lemma two_mul_le_three_pow (k : ℕ) (hk : 5 ≤ k) : 2 * k ≤ 3 ^ (k - 2) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      have h3 : 0 < 3 ^ (k - 2) := pow_pos (by norm_num) _
      calc
        2 * (k + 1) = 2 * k + 2 := by ring
        _ ≤ 3 ^ (k - 2) + 2 := by omega
        _ ≤ 3 * 3 ^ (k - 2) := by nlinarith
        _ = 3 ^ (k - 1) := by
            rw [show k - 1 = k - 2 + 1 by omega, pow_succ]
            ring
        _ = 3 ^ (k + 1 - 2) := by rw [show k + 1 - 2 = k - 1 by omega]

lemma two_mul_le_pow_of_five {p k : ℕ} (hp : 3 ≤ p) (hk : 5 ≤ k) :
    2 * k ≤ p ^ (k - 2) :=
  le_trans (two_mul_le_three_pow k hk) (Nat.pow_le_pow_left hp (k - 2))

lemma two_mul_le_pow_pred {p k : ℕ} (hp : 3 ≤ p) (hk : 3 ≤ k) :
    2 * k ≤ p ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base =>
      have h9 : 9 ≤ p * p := Nat.mul_le_mul hp hp
      show 6 ≤ p ^ 2
      rw [show p ^ 2 = p * p by ring]
      omega
  | succ k hk ih =>
      have hk1 : 1 ≤ k := by omega
      have hpk : 0 < p ^ (k - 1) := pow_pos (by omega) _
      have h1 : 2 * k + 2 ≤ p ^ (k - 1) + 2 := by omega
      have h2 : p ^ (k - 1) + 2 ≤ 3 * p ^ (k - 1) := by nlinarith
      have h3 : 3 * p ^ (k - 1) ≤ p * p ^ (k - 1) := by
        exact Nat.mul_le_mul_right _ hp
      calc
        2 * (k + 1) = 2 * k + 2 := by ring
        _ ≤ p ^ (k - 1) + 2 := h1
        _ ≤ 3 * p ^ (k - 1) := h2
        _ ≤ p * p ^ (k - 1) := h3
        _ = p ^ (k - 1 + 1) := (pow_succ' p (k - 1)).symm
        _ = p ^ (k + 1 - 1) := by rw [show k - 1 + 1 = k + 1 - 1 by omega]

lemma e_le_pow_pred {p e : ℕ} (hp : 3 ≤ p) (he : 5 ≤ e) :
    e ≤ p ^ (e - e / 2 - 1) := by
  have hk : 3 ≤ e - e / 2 := by omega
  have h1 : e ≤ 2 * (e - e / 2) := by omega
  exact le_trans h1 (two_mul_le_pow_pred hp hk)

lemma e_mul_pred_le_pow {p e : ℕ} (hp : 3 ≤ p) (he : 9 ≤ e) :
    e * (p - 1) ≤ p ^ (e - e / 2 - 1) := by
  set k := e - e / 2 with hkdef
  have hk5 : 5 ≤ k := by omega
  have hek : e ≤ 2 * k := by omega
  have h2k : 2 * k ≤ p ^ (k - 2) := two_mul_le_pow_of_five hp hk5
  have h1 : e * (p - 1) ≤ 2 * k * (p - 1) := Nat.mul_le_mul_right _ hek
  have h2 : 2 * k * (p - 1) ≤ 2 * k * p := Nat.mul_le_mul_left _ (by omega : p - 1 ≤ p)
  have h3 : 2 * k * p ≤ p ^ (k - 2) * p := Nat.mul_le_mul_right _ h2k
  have h4 : p ^ (k - 2) * p = p ^ (k - 1) := (pow_succ p (k - 2)).symm.trans (by rw [show k - 2 + 1 = k - 1 by omega])
  calc
    e * (p - 1) ≤ 2 * k * (p - 1) := h1
    _ ≤ 2 * k * p := h2
    _ ≤ p ^ (k - 2) * p := h3
    _ = p ^ (k - 1) := h4
    _ = p ^ (e - e / 2 - 1) := by rw [← hkdef]

lemma F_le_crude {p e : ℕ} (hp : 3 ≤ p) (he : 5 ≤ e) :
    F p e ≤ 1 + (e : ℚ) / (p : ℚ) ^ (e - e / 2) := by
  have hp0 : 0 < p := by omega
  have he0 : e ≠ 0 := by omega
  rw [F_eq hp0 he0]
  have hA := sum_erase_le (p := p) (e := e) (by omega) (by omega)
  have hpe : (0 : ℚ) < (p : ℚ) ^ e := by positivity
  have hstep : (∑ b ∈ e.divisors.erase e, (p : ℚ) ^ b) / (p : ℚ) ^ e
      ≤ ((e : ℚ) * (p : ℚ) ^ (e / 2)) / (p : ℚ) ^ e :=
    div_le_div_of_nonneg_right hA (le_of_lt hpe)
  have hpow : ((e : ℚ) * (p : ℚ) ^ (e / 2)) / (p : ℚ) ^ e
      = (e : ℚ) / (p : ℚ) ^ (e - e / 2) := by
    have hsplit : (p : ℚ) ^ e = (p : ℚ) ^ (e / 2) * (p : ℚ) ^ (e - e / 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit]
    have hp2 : (p : ℚ) ^ (e / 2) ≠ 0 := pow_ne_zero _ (by positivity)
    field_simp
  linarith [hstep.trans_eq hpow]

lemma F_bound_general {p e : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (he : 1 ≤ e) :
    F p e ≤ 1 + 1 / (p : ℚ) := by
  have hp0 : 0 < p := hp.pos
  have hpq : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp0
  rcases Nat.lt_or_ge e 5 with h5 | h5
  · interval_cases e
    · rw [F_one hp0]
      have : (0 : ℚ) < 1 / (p : ℚ) := by positivity
      linarith
    · rw [F_two hp0]
    · rw [F_three hp0]
      have hle : (p : ℚ) ≤ (p : ℚ) ^ 2 := by
        have h : 0 ≤ (p : ℚ) * ((p : ℚ) - 1) :=
          mul_nonneg (le_of_lt hpq) (by
            have : (1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast (show 1 ≤ p by omega)
            linarith)
        nlinarith [h]
      have h1 : 1 / (p : ℚ) ^ 2 ≤ 1 / (p : ℚ) := one_div_le_one_div_of_le hpq hle
      linarith
    · rw [F_four hp0]
      have hpk : (0 : ℚ) < (p : ℚ) ^ 4 := by positivity
      have hmain : ((p : ℚ) + (p : ℚ) ^ 2) / (p : ℚ) ^ 4 ≤ 1 / (p : ℚ) := by
        rw [div_le_div_iff₀ hpk hpq]
        have h : 0 ≤ (p : ℚ) ^ 2 * ((p : ℚ) ^ 2 - (p : ℚ) - 1) := by
          have h1 : 0 ≤ (p : ℚ) ^ 2 := by positivity
          have h2 : 0 ≤ (p : ℚ) ^ 2 - (p : ℚ) - 1 := by
            have : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp3
            nlinarith
          exact mul_nonneg h1 h2
        nlinarith [h]
      linarith
  · have hc := F_le_crude (p := p) (e := e) hp3 h5
    have hle : (e : ℚ) / (p : ℚ) ^ (e - e / 2) ≤ 1 / (p : ℚ) := by
      have hpk : (0 : ℚ) < (p : ℚ) ^ (e - e / 2) := by positivity
      rw [div_le_div_iff₀ hpk hpq]
      have hkp : (e : ℚ) * (p : ℚ) ≤ (p : ℚ) ^ (e - e / 2) := by
        have hnat : e * p ≤ p ^ (e - e / 2) := by
          have hpred := e_le_pow_pred hp3 h5
          calc
            e * p ≤ p ^ (e - e / 2 - 1) * p := Nat.mul_le_mul_right _ hpred
            _ = p ^ (e - e / 2) := by
                conv_rhs => rw [show e - e / 2 = (e - e / 2 - 1) + 1 by omega, pow_succ]
        exact_mod_cast hnat
      simpa using hkp
    linarith

lemma F_bound_square {p e : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (he : 1 ≤ e)
    (hsq : IsSquare e) :
    F p e ≤ 1 + 1 / ((p : ℚ) * ((p : ℚ) - 1)) := by
  have hp0 : 0 < p := hp.pos
  have hp3q : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp3
  have hden : (0 : ℚ) < (p : ℚ) * ((p : ℚ) - 1) := by nlinarith
  obtain ⟨s, hs⟩ := hsq
  rcases s with _ | _ | _ | s
  · have he0 : e = 0 := by simpa using hs
    omega
  · have he1 : e = 1 := by simpa using hs
    subst e
    rw [F_one hp0]
    have : (0 : ℚ) < 1 / ((p : ℚ) * ((p : ℚ) - 1)) := by positivity
    linarith
  · have he4 : e = 4 := by simpa using hs
    subst e
    rw [F_four hp0]
    have hpk : (0 : ℚ) < (p : ℚ) ^ 4 := by positivity
    have hmain : ((p : ℚ) + (p : ℚ) ^ 2) / (p : ℚ) ^ 4
        ≤ 1 / ((p : ℚ) * ((p : ℚ) - 1)) := by
      rw [div_le_div_iff₀ hpk hden]
      have h : 0 ≤ (p : ℚ) ^ 2 * ((p : ℚ) ^ 2 - 1) := by
        have h1 : 0 ≤ (p : ℚ) ^ 2 := by positivity
        have h2 : 0 ≤ (p : ℚ) ^ 2 - 1 := by
          have : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp3
          nlinarith
        exact mul_nonneg h1 h2
      nlinarith [h]
    linarith
  · have hs3 : 3 ≤ s + 3 := by omega
    have he9 : 9 ≤ e := by
      rw [hs]
      have h9 : 3 * 3 ≤ (s + 3) * (s + 3) := Nat.mul_le_mul hs3 hs3
      omega
    have hc := F_le_crude (p := p) (e := e) hp3 (by omega)
    have hmul : e * (p - 1) ≤ p ^ (e - e / 2 - 1) := e_mul_pred_le_pow hp3 he9
    have hle : (e : ℚ) / (p : ℚ) ^ (e - e / 2)
        ≤ 1 / ((p : ℚ) * ((p : ℚ) - 1)) := by
      have hpk : (0 : ℚ) < (p : ℚ) ^ (e - e / 2) := by positivity
      rw [div_le_div_iff₀ hpk hden]
      have hmulq : (e : ℚ) * ((p : ℚ) - 1) ≤ (p : ℚ) ^ (e - e / 2 - 1) := by
        have h1 : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ p)]
          norm_num
        calc
          (e : ℚ) * ((p : ℚ) - 1) = ((e * (p - 1) : ℕ) : ℚ) := by
            rw [Nat.cast_mul, h1]
          _ ≤ ((p ^ (e - e / 2 - 1) : ℕ) : ℚ) := by exact_mod_cast hmul
          _ = (p : ℚ) ^ (e - e / 2 - 1) := by norm_num
      have hpk' : (e : ℚ) * ((p : ℚ) * ((p : ℚ) - 1)) ≤ (p : ℚ) ^ (e - e / 2) := by
        have h1 : (e : ℚ) * ((p : ℚ) - 1) * (p : ℚ)
            ≤ (p : ℚ) ^ (e - e / 2 - 1) * (p : ℚ) :=
          mul_le_mul_of_nonneg_right hmulq (by positivity)
        have h2 : (p : ℚ) ^ (e - e / 2 - 1) * (p : ℚ) = (p : ℚ) ^ (e - e / 2) := by
          conv_rhs => rw [show e - e / 2 = (e - e / 2 - 1) + 1 by omega, pow_succ]
        calc
          (e : ℚ) * ((p : ℚ) * ((p : ℚ) - 1))
              = (e : ℚ) * ((p : ℚ) - 1) * (p : ℚ) := by ring
          _ ≤ (p : ℚ) ^ (e - e / 2 - 1) * (p : ℚ) := h1
          _ = (p : ℚ) ^ (e - e / 2) := h2
      simpa using hpk'
    linarith

def sb (p : ℕ) : ℚ := 1 + 1 / ((p : ℚ) * ((p : ℚ) - 1))

lemma one_le_sb {p : ℕ} (hp : 3 ≤ p) : 1 ≤ sb p := by
  unfold sb
  have hden : (0 : ℚ) < (p : ℚ) * ((p : ℚ) - 1) := by
    have : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
    nlinarith
  have : (0 : ℚ) < 1 / ((p : ℚ) * ((p : ℚ) - 1)) := by positivity
  linarith

lemma sb_three : sb 3 = 7 / 6 := by norm_num [sb]

lemma step_alg {x : ℚ} (hx : 5 ≤ x) :
    (4 / 3) * (x - 1) / x * (1 + 1 / ((x + 1) * x)) ≤ (4 / 3) * x / (x + 1) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x + 1 := by linarith
  have h : 0 < (x + 1) * x := mul_pos hx1 hx0
  field_simp
  nlinarith

lemma prod_Icc_sb_le_aux (N : ℕ) (hN : 5 ≤ N) :
    ∏ n ∈ Finset.Icc 5 N, sb n ≤ (4 / 3) * ((N : ℚ) - 1) / (N : ℚ) := by
  induction N, hN using Nat.le_induction with
  | base =>
      norm_num [sb, Finset.Icc_self]
  | succ N hN ih =>
      have hNq : (5 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN
      have hsb : sb (N + 1) = 1 + 1 / (((N : ℚ) + 1) * (N : ℚ)) := by
        unfold sb
        push_cast
        ring
      rw [Finset.prod_Icc_succ_top (by omega), hsb]
      have hnonneg : (0 : ℚ) ≤ 1 + 1 / (((N : ℚ) + 1) * (N : ℚ)) := by positivity
      calc
        (∏ n ∈ Finset.Icc 5 N, sb n) * (1 + 1 / (((N : ℚ) + 1) * (N : ℚ)))
            ≤ ((4 / 3) * ((N : ℚ) - 1) / (N : ℚ))
                * (1 + 1 / (((N : ℚ) + 1) * (N : ℚ))) :=
              mul_le_mul_of_nonneg_right ih hnonneg
        _ ≤ (4 / 3) * (((N : ℚ) + 1) - 1) / ((N : ℚ) + 1) := by
              have hs := step_alg (x := (N : ℚ)) hNq
              convert hs using 1 <;> ring
        _ = (4 / 3) * ((↑(N + 1) : ℚ) - 1) / (↑(N + 1) : ℚ) := by
              push_cast
              ring

lemma prod_Icc_sb_le (N : ℕ) (hN : 5 ≤ N) :
    ∏ n ∈ Finset.Icc 5 N, sb n ≤ 4 / 3 := by
  have haux := prod_Icc_sb_le_aux N hN
  have hNq : (0 : ℚ) < (N : ℚ) := by exact_mod_cast (by omega : 0 < N)
  have h1 : ((N : ℚ) - 1) / (N : ℚ) ≤ 1 := by
    rw [div_le_one hNq]
    linarith
  calc
    ∏ n ∈ Finset.Icc 5 N, sb n ≤ (4 / 3) * ((N : ℚ) - 1) / (N : ℚ) := haux
    _ = (4 / 3) * (((N : ℚ) - 1) / (N : ℚ)) := by ring
    _ ≤ (4 / 3) * 1 := by gcongr
    _ = 4 / 3 := by norm_num

lemma prod_sb_le {T : Finset ℕ} (hT : ∀ p ∈ T, 5 ≤ p) :
    ∏ p ∈ T, sb p ≤ 4 / 3 := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.prod_empty]
    norm_num
  · set N := T.max' hne with hNdef
    have hN5 : 5 ≤ N := hT _ (Finset.max'_mem T hne)
    have hsub : T ⊆ Finset.Icc 5 N := by
      intro p hp
      rw [Finset.mem_Icc]
      exact ⟨hT p hp, Finset.le_max' T p hp⟩
    have h1 : ∏ p ∈ T, sb p ≤ ∏ p ∈ Finset.Icc 5 N, sb p := by
      apply Finset.prod_le_prod_of_subset_of_one_le hsub
      · intro n hn
        exact le_trans zero_le_one (one_le_sb (by
          have := hT n hn
          omega))
      · intro n hn hnp
        rw [Finset.mem_Icc] at hn
        exact one_le_sb (by omega)
    exact le_trans h1 (prod_Icc_sb_le N hN5)

lemma odd_S_iff_odd_card {p e : ℕ} (hp : Odd p) :
    Odd (S p e) ↔ Odd e.divisors.card := by
  unfold S
  rw [Finset.odd_sum_iff_odd_card_odd]
  have h : e.divisors.filter (fun b => Odd (p ^ b)) = e.divisors := by
    apply Finset.filter_true_of_mem
    intro b _hb
    exact hp.pow
  rw [h]

lemma isSquare_of_odd_card_divisors {e : ℕ} (he : e ≠ 0) (hodd : Odd e.divisors.card) :
    IsSquare e := by
  have hcard := Nat.card_divisors he
  rw [hcard] at hodd
  have hfac : ∀ p ∈ e.primeFactors, Odd (e.factorization p + 1) := by
    intro p hp
    by_contra hpo
    have hev : Even (e.factorization p + 1) := Nat.not_odd_iff_even.mp hpo
    have hdvd : 2 ∣ e.factorization p + 1 := even_iff_two_dvd.mp hev
    have hprod : 2 ∣ ∏ x ∈ e.primeFactors, (e.factorization x + 1) :=
      dvd_trans hdvd (Finset.dvd_prod_of_mem _ hp)
    have hevprod : Even (∏ x ∈ e.primeFactors, (e.factorization x + 1)) :=
      even_iff_two_dvd.mpr hprod
    exact (Nat.not_even_iff_odd.mpr hodd) hevprod
  have heven : ∀ p, Even (e.factorization p) := by
    intro p
    by_cases hp : p ∈ e.primeFactors
    · have h := hfac p hp
      have h1 : ¬ Odd (e.factorization p) := Nat.odd_add_one.mp h
      exact Nat.not_odd_iff_even.mp h1
    · by_cases hpp : p.Prime
      · have hz : e.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd (by
          intro hdvd
          exact hp (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, he⟩))
        rw [hz]
        exact ⟨0, by norm_num⟩
      · rw [Nat.factorization_eq_zero_of_not_prime _ hpp]
        exact ⟨0, by norm_num⟩
  have hprod : (∏ p ∈ e.primeFactors, p ^ e.factorization p) = e := by
    have h := Nat.prod_factorization_pow_eq_self he
    simpa [Finsupp.prod] using h
  refine ⟨∏ p ∈ e.primeFactors, p ^ (e.factorization p / 2), ?_⟩
  have hmain : (∏ p ∈ e.primeFactors, p ^ (e.factorization p / 2))
      * (∏ p ∈ e.primeFactors, p ^ (e.factorization p / 2)) = e := by
    rw [← Finset.prod_mul_distrib]
    calc
      (∏ p ∈ e.primeFactors,
          (p ^ (e.factorization p / 2) * p ^ (e.factorization p / 2)))
          = ∏ p ∈ e.primeFactors, p ^ (e.factorization p / 2 + e.factorization p / 2) := by
            apply Finset.prod_congr rfl
            intro p _hp
            rw [← pow_add]
      _ = ∏ p ∈ e.primeFactors, p ^ e.factorization p := by
            apply Finset.prod_congr rfl
            intro p _hp
            have h2 : e.factorization p / 2 + e.factorization p / 2 = e.factorization p := by
              obtain ⟨k, hk⟩ := heven p
              omega
            rw [h2]
      _ = e := hprod
  exact hmain.symm

lemma prod_primeFactors_pow_factorization {n : ℕ} (hn : n ≠ 0) :
    (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
  have h := Nat.prod_factorization_pow_eq_self hn
  simpa [Finsupp.prod] using h

lemma ratio_eq_prod {k : ℕ} (hk : k ≠ 0) :
    (sigmaE k : ℚ) / (k : ℚ) = ∏ p ∈ k.primeFactors, F p (k.factorization p) := by
  have hsig : (sigmaE k : ℚ) = ∏ p ∈ k.primeFactors, (S p (k.factorization p) : ℚ) := by
    simp [sigmaE, S]
  have hkq : (k : ℚ) = ∏ p ∈ k.primeFactors, (p : ℚ) ^ (k.factorization p) := by
    calc
      (k : ℚ) = ((∏ p ∈ k.primeFactors, p ^ k.factorization p : ℕ) : ℚ) := by
        rw [prod_primeFactors_pow_factorization hk]
      _ = ∏ p ∈ k.primeFactors, (p : ℚ) ^ (k.factorization p) := by
        push_cast
        rfl
  rw [hsig, hkq]
  simp only [F]
  rw [← Finset.prod_div_distrib]

lemma sigmaE_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b) :
    sigmaE (a * b) = sigmaE a * sigmaE b := by
  rw [sigmaE, sigmaE, sigmaE, Nat.primeFactors_mul ha hb,
    Finset.prod_union hab.disjoint_primeFactors]
  congr 1
  · apply Finset.prod_congr rfl
    intro p hp
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hpa : p ∣ a := (Nat.mem_primeFactors.mp hp).2.1
    have hpb0 : b.factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hpb
      have hpg : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa hpb
      rw [hab] at hpg
      exact hpp.not_dvd_one hpg
    rw [Nat.factorization_mul ha hb]
    simp [hpb0]
  · apply Finset.prod_congr rfl
    intro p hp
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hpb : p ∣ b := (Nat.mem_primeFactors.mp hp).2.1
    have hpa0 : a.factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hpa
      have hpg : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa hpb
      rw [hab] at hpg
      exact hpp.not_dvd_one hpg
    rw [Nat.factorization_mul ha hb]
    simp [hpa0]

lemma sigmaE_two : sigmaE 2 = 2 := by
  rw [sigmaE, Nat.Prime.primeFactors Nat.prime_two]
  simp [Nat.Prime.factorization Nat.prime_two, S, Nat.divisors_one]

lemma odd_of_mem_primeFactors_odd {m p : ℕ} (hm : Odd m) (hp : p ∈ m.primeFactors) :
    Odd p := by
  have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hpdvd : p ∣ m := (Nat.mem_primeFactors.mp hp).2.1
  rcases Nat.Prime.eq_two_or_odd hpp with h | h
  · exfalso
    have h2dvd : 2 ∣ m := by rw [← h]; exact hpdvd
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2dvd)
  · exact Nat.odd_iff.mpr h

lemma factorization_two_prod (s : Finset ℕ) (g : ℕ → ℕ) (hg : ∀ x ∈ s, g x ≠ 0) :
    (∏ x ∈ s, g x).factorization 2 = ∑ x ∈ s, (g x).factorization 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have ha0 : g a ≠ 0 := hg a (Finset.mem_insert_self a s)
      have hs0 : ∏ x ∈ s, g x ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun x hx => hg x (Finset.mem_insert_of_mem hx))
      rw [Finset.prod_insert ha, Nat.factorization_mul ha0 hs0, Finsupp.add_apply,
        Finset.sum_insert ha]
      rw [ih (fun x hx => hg x (Finset.mem_insert_of_mem hx))]

lemma F_nonneg {p e : ℕ} (hp : 0 < p) : 0 ≤ F p e := by
  unfold F
  have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp
  exact div_nonneg (by positivity) (le_of_lt (pow_pos hp0 _))

theorem no_odd_ePerfect {m : ℕ} (hm_odd : Odd m) : ¬ IsEPerfect m := by
  rintro ⟨hm_pos, hsig⟩
  have hm0 : m ≠ 0 := hm_pos.ne'
  have hm2 : m.factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    exact (Nat.not_even_iff_odd.mpr hm_odd) (even_iff_two_dvd.mpr hdvd)
  have hfact2 : (sigmaE m).factorization 2 = 1 := by
    rw [hsig, Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply, hm2]
    have htwo : (2 : ℕ).factorization 2 = 1 := by
      rw [Nat.Prime.factorization Nat.prime_two]
      simp
    rw [htwo]
  have hg_ne : ∀ p ∈ m.primeFactors, S p (m.factorization p) ≠ 0 := by
    intro p hp
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hpdvd : p ∣ m := (Nat.mem_primeFactors.mp hp).2.1
    have he1 : 1 ≤ m.factorization p :=
      (Nat.Prime.dvd_iff_one_le_factorization hpp hm0).mp hpdvd
    exact (S_pos hpp.pos (by omega)).ne'
  have hsum : ∑ p ∈ m.primeFactors, (S p (m.factorization p)).factorization 2 = 1 := by
    have h := factorization_two_prod m.primeFactors
      (fun p => S p (m.factorization p)) hg_ne
    have hsig_prod : sigmaE m = ∏ p ∈ m.primeFactors, S p (m.factorization p) := rfl
    rw [← hsig_prod, hfact2] at h
    exact h.symm
  have hsum_ne : ∑ p ∈ m.primeFactors, (S p (m.factorization p)).factorization 2 ≠ 0 := by
    rw [hsum]
    norm_num
  obtain ⟨q, hqmem, hqne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  have hqpos : 0 < (S q (m.factorization q)).factorization 2 := Nat.pos_of_ne_zero hqne
  have hsplit := Finset.add_sum_erase m.primeFactors
    (fun p => (S p (m.factorization p)).factorization 2) hqmem
  have hrest0 : ∑ p ∈ m.primeFactors.erase q, (S p (m.factorization p)).factorization 2 = 0 := by
    omega
  have hrest_each : ∀ p ∈ m.primeFactors.erase q,
      (S p (m.factorization p)).factorization 2 = 0 := by
    intro p hp
    exact (Finset.sum_eq_zero_iff.mp hrest0) p hp
  have hsquare : ∀ p ∈ m.primeFactors.erase q, IsSquare (m.factorization p) := by
    intro p hp
    have hmem : p ∈ m.primeFactors := (Finset.mem_erase.mp hp).2
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hmem).1
    have hpdvd : p ∣ m := (Nat.mem_primeFactors.mp hmem).2.1
    have he1 : 1 ≤ m.factorization p :=
      (Nat.Prime.dvd_iff_one_le_factorization hpp hm0).mp hpdvd
    have hSpos : 0 < S p (m.factorization p) := S_pos hpp.pos (by omega)
    have hnot2 : ¬ 2 ∣ S p (m.factorization p) := by
      have hz := hrest_each p hp
      rw [Nat.factorization_eq_zero_iff] at hz
      rcases hz with h | h | h
      · exact absurd Nat.prime_two h
      · exact h
      · exact absurd h hSpos.ne'
    have hoddS : Odd (S p (m.factorization p)) := by
      rw [← Nat.not_even_iff_odd]
      intro hev
      exact hnot2 (even_iff_two_dvd.mp hev)
    have hpodd : Odd p := odd_of_mem_primeFactors_odd hm_odd hmem
    have hcard : Odd (m.factorization p).divisors.card := (odd_S_iff_odd_card hpodd).mp hoddS
    exact isSquare_of_odd_card_divisors (by omega) hcard
  have hratio := ratio_eq_prod hm0
  have hratio2 : (sigmaE m : ℚ) / (m : ℚ) = 2 := by
    rw [hsig]
    have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm0
    field_simp
    push_cast
    ring
  have hprod2 : ∏ p ∈ m.primeFactors, F p (m.factorization p) = 2 := by
    rw [← hratio, hratio2]
  have hsplitprod : ∏ p ∈ m.primeFactors, F p (m.factorization p)
      = (∏ p ∈ m.primeFactors.erase q, F p (m.factorization p)) * F q (m.factorization q) := by
    exact (Finset.prod_erase_mul m.primeFactors (fun p => F p (m.factorization p)) hqmem).symm
  have hqprime : q.Prime := (Nat.mem_primeFactors.mp hqmem).1
  have hqdvd : q ∣ m := (Nat.mem_primeFactors.mp hqmem).2.1
  have hqe1 : 1 ≤ m.factorization q :=
    (Nat.Prime.dvd_iff_one_le_factorization hqprime hm0).mp hqdvd
  have hqodd : Odd q := odd_of_mem_primeFactors_odd hm_odd hqmem
  have hq3 : 3 ≤ q := by
    have h2 := hqprime.two_le
    have := Nat.odd_iff.mp hqodd
    omega
  have hFq : F q (m.factorization q) ≤ 1 + 1 / (q : ℚ) :=
    F_bound_general hqprime hq3 hqe1
  have hrestF : ∏ p ∈ m.primeFactors.erase q, F p (m.factorization p)
      ≤ ∏ p ∈ m.primeFactors.erase q, sb p := by
    apply Finset.prod_le_prod
    · intro p hp
      have hmem : p ∈ m.primeFactors := (Finset.mem_erase.mp hp).2
      have hpp : p.Prime := (Nat.mem_primeFactors.mp hmem).1
      exact F_nonneg hpp.pos
    · intro p hp
      have hmem : p ∈ m.primeFactors := (Finset.mem_erase.mp hp).2
      have hpp : p.Prime := (Nat.mem_primeFactors.mp hmem).1
      have hpdvd : p ∣ m := (Nat.mem_primeFactors.mp hmem).2.1
      have he1 : 1 ≤ m.factorization p :=
        (Nat.Prime.dvd_iff_one_le_factorization hpp hm0).mp hpdvd
      have hpodd : Odd p := odd_of_mem_primeFactors_odd hm_odd hmem
      have hp3 : 3 ≤ p := by
        have h2 := hpp.two_le
        have := Nat.odd_iff.mp hpodd
        omega
      exact F_bound_square hpp hp3 he1 (hsquare p hp)
  rcases eq_or_ne q 3 with hqeq | hqne
  · subst q
    have hrest4 : ∏ p ∈ m.primeFactors.erase 3, F p (m.factorization p) ≤ 4 / 3 := by
      have hsb : ∏ p ∈ m.primeFactors.erase 3, sb p ≤ 4 / 3 := by
        apply prod_sb_le
        intro p hp
        have hmem : p ∈ m.primeFactors := (Finset.mem_erase.mp hp).2
        have hpp : p.Prime := (Nat.mem_primeFactors.mp hmem).1
        have hpodd : Odd p := odd_of_mem_primeFactors_odd hm_odd hmem
        have hpne3 : p ≠ 3 := (Finset.mem_erase.mp hp).1
        have hp3 : 3 ≤ p := by
          have h2 := hpp.two_le
          have := Nat.odd_iff.mp hpodd
          omega
        have := Nat.odd_iff.mp hpodd
        omega
      linarith
    have hF3 : F 3 (m.factorization 3) ≤ 4 / 3 := by
      calc F 3 (m.factorization 3) ≤ 1 + 1 / (3 : ℚ) := hFq
        _ = 4 / 3 := by norm_num
    have hmul : (∏ p ∈ m.primeFactors.erase 3, F p (m.factorization p)) * F 3 (m.factorization 3)
        ≤ (4 / 3) * (4 / 3) := by
      exact mul_le_mul hrest4 hF3 (F_nonneg (by norm_num)) (by norm_num)
    have hle : (2 : ℚ) ≤ 16 / 9 := by
      calc (2 : ℚ) = ∏ p ∈ m.primeFactors, F p (m.factorization p) := hprod2.symm
        _ = (∏ p ∈ m.primeFactors.erase 3, F p (m.factorization p)) * F 3 (m.factorization 3) := hsplitprod
        _ ≤ (4 / 3) * (4 / 3) := hmul
        _ = 16 / 9 := by norm_num
    norm_num at hle
  · have hq5 : 5 ≤ q := by
      have := Nat.odd_iff.mp hqodd
      omega
    have hFq6 : F q (m.factorization q) ≤ 6 / 5 := by
      calc F q (m.factorization q) ≤ 1 + 1 / (q : ℚ) := hFq
        _ ≤ 1 + 1 / (5 : ℚ) := by
            have hq5q : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq5
            have h1 : 1 / (q : ℚ) ≤ 1 / (5 : ℚ) :=
              one_div_le_one_div_of_le (by norm_num) hq5q
            linarith
        _ = 6 / 5 := by norm_num
    have hrest73 : ∏ p ∈ m.primeFactors.erase q, F p (m.factorization p) ≤ (7 / 6) * (4 / 3) := by
      have hsb : ∏ p ∈ m.primeFactors.erase q, sb p ≤ (7 / 6) * (4 / 3) := by
        by_cases h3 : 3 ∈ m.primeFactors.erase q
        · rw [← Finset.prod_erase_mul (m.primeFactors.erase q) sb h3]
          have hT : ∀ p ∈ (m.primeFactors.erase q).erase 3, 5 ≤ p := by
            intro p hp
            have hmem : p ∈ m.primeFactors := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).2
            have hpp : p.Prime := (Nat.mem_primeFactors.mp hmem).1
            have hpodd : Odd p := odd_of_mem_primeFactors_odd hm_odd hmem
            have hpne3 : p ≠ 3 := (Finset.mem_erase.mp hp).1
            have hp3 : 3 ≤ p := by
              have h2 := hpp.two_le
              have := Nat.odd_iff.mp hpodd
              omega
            have := Nat.odd_iff.mp hpodd
            omega
          have hle := prod_sb_le hT
          rw [sb_three]
          nlinarith
        · have hT : ∀ p ∈ m.primeFactors.erase q, 5 ≤ p := by
            intro p hp
            have hmem : p ∈ m.primeFactors := (Finset.mem_erase.mp hp).2
            have hpp : p.Prime := (Nat.mem_primeFactors.mp hmem).1
            have hpodd : Odd p := odd_of_mem_primeFactors_odd hm_odd hmem
            have hpne3 : p ≠ 3 := by
              intro h
              exact h3 (by rw [← h]; exact hp)
            have hp3 : 3 ≤ p := by
              have h2 := hpp.two_le
              have := Nat.odd_iff.mp hpodd
              omega
            have := Nat.odd_iff.mp hpodd
            omega
          have hle := prod_sb_le hT
          nlinarith
      linarith
    have hmul : (∏ p ∈ m.primeFactors.erase q, F p (m.factorization p)) * F q (m.factorization q)
        ≤ ((7 / 6) * (4 / 3)) * (6 / 5) := by
      exact mul_le_mul hrest73 hFq6 (F_nonneg hqprime.pos) (by norm_num)
    have hle : (2 : ℚ) ≤ ((7 / 6) * (4 / 3)) * (6 / 5) := by
      calc (2 : ℚ) = ∏ p ∈ m.primeFactors, F p (m.factorization p) := hprod2.symm
        _ = (∏ p ∈ m.primeFactors.erase q, F p (m.factorization p)) * F q (m.factorization q) := hsplitprod
        _ ≤ ((7 / 6) * (4 / 3)) * (6 / 5) := hmul
    norm_num at hle

theorem four_dvd {k : ℕ} (hk : IsEPerfect k) : 4 ∣ k := by
  obtain ⟨hkpos, hsig⟩ := hk
  by_contra h4
  by_cases h2 : 2 ∣ k
  · obtain ⟨m, rfl⟩ := h2
    have hmpos : 0 < m := by omega
    have hmodd : Odd m := by
      rw [← Nat.not_even_iff_odd]
      intro hev
      apply h4
      obtain ⟨c, hc⟩ := hev
      exact ⟨c, by rw [hc]; ring⟩
    have hcop : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hmodd
    have hmul := sigmaE_mul (a := 2) (b := m) (by norm_num) (by omega) hcop
    have hsig2 : sigmaE (2 * m) = 2 * sigmaE m := by
      rw [hmul, sigmaE_two]
    have hsig_m : sigmaE m = 2 * m := by
      have h : 2 * sigmaE m = 4 * m := by
        rw [← hsig2, hsig]
        ring
      omega
    exact no_odd_ePerfect hmodd ⟨hmpos, hsig_m⟩
  · have hkodd : Odd k := by
      rw [← Nat.not_even_iff_odd]
      intro hev
      exact h2 (even_iff_two_dvd.mp hev)
    exact no_odd_ePerfect hkodd ⟨hkpos, hsig⟩

end OMA.A054979

open OMA.A054979

theorem OMA.solution : OMA.R_oeis_a054979_R1.H1 := by
  intro k hk
  exact four_dvd hk
