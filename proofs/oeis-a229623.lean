import OMAStatements.S_oeis_a229623

-- Problem: A229623: Palindromes m such that m - sumofdigits(m) is also a palindrome.
-- Upstream: formal-conjectures statements/oeis-a229623.lean:0 (declaration OMA.S_oeis_a229623.main)
-- Credit: @Raimo33 (the owner of the agent is credited as the solver)
-- Proof: every qualifying m >= 10^4 is 10^k + 1. With L digits, s = digit sum < 10^(L/2):
-- if m - s loses a digit, the zero-padding of m forces m = 10^(L-1) + 1; if the top half of
-- m - s equals that of m, mirroring gives 10^(L/2) | s, impossible; otherwise a borrow occurs,
-- which forces s = 10^q (mod 10^(q+1)) with s <= 18 (q + 1), impossible.
-- Below 10^4 the sequence is checked by decide.

namespace OMA.P_a229623
open OMA.S_oeis_a229623

/-- The `i`-th decimal digit of `y`. -/
def dg (y i : ℕ) : ℕ := y / 10 ^ i % 10

lemma len_eq {y L : ℕ} (hL : 1 ≤ L) (h1 : 10 ^ (L - 1) ≤ y) (h2 : y < 10 ^ L) :
    (Nat.digits 10 y).length = L := by
  apply le_antisymm
  · exact (Nat.digits_length_le_iff (by norm_num) y).2 h2
  · by_contra h
    push Not at h
    have := (Nat.digits_length_le_iff (by norm_num) y).1 (by omega : (Nat.digits 10 y).length ≤ L - 1)
    omega

lemma lt_of_len (y : ℕ) : y < 10 ^ (Nat.digits 10 y).length :=
  (Nat.digits_length_le_iff (by norm_num) y).1 le_rfl

lemma ge_of_len (y : ℕ) (hy : y ≠ 0) : 10 ^ ((Nat.digits 10 y).length - 1) ≤ y := by
  by_contra h
  push Not at h
  have := (Nat.digits_length_le_iff (by norm_num) y).2 h
  have : (Nat.digits 10 y).length ≠ 0 := by
    simpa using Nat.digits_ne_nil_iff_ne_zero.2 hy
  omega

lemma getElem_dg (y i : ℕ) (h : i < (Nat.digits 10 y).length) :
    (Nat.digits 10 y)[i] = dg y i := by
  rw [dg, ← Nat.getD_digits y i (by norm_num), List.getD_eq_getElem _ _ h]

lemma pal_iff (y : ℕ) : (Nat.digits 10 y).Palindrome ↔
    ∀ i < (Nat.digits 10 y).length, dg y i = dg y ((Nat.digits 10 y).length - 1 - i) := by
  rw [List.Palindrome.iff_reverse_eq]
  constructor
  · intro h i hi
    have e := List.getElem_of_eq h (by simpa using hi)
    rw [List.getElem_reverse, getElem_dg, getElem_dg] at e
    exact e.symm
  · intro h
    apply List.ext_getElem (by simp)
    intro i h1 h2
    rw [List.getElem_reverse, getElem_dg, getElem_dg]
    exact (h i h2).symm

lemma mod_eq_of_dg {a b : ℕ} : ∀ n, (∀ i < n, dg a i = dg b i) → a % 10 ^ n = b % 10 ^ n
  | 0, _ => by simp [Nat.mod_one]
  | n + 1, h => by
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ, mod_eq_of_dg n (fun i hi => h i (by omega))]
    have := h n (by omega)
    simp only [dg] at this
    rw [this]

lemma dg_of_div_eq {a b k : ℕ} (h : a / 10 ^ k = b / 10 ^ k) (i : ℕ) (hi : k ≤ i) :
    dg a i = dg b i := by
  unfold dg
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h]

lemma dg_div (a k i : ℕ) : dg (a / 10 ^ k) i = dg a (k + i) := by
  unfold dg; rw [Nat.div_div_eq_div_mul, ← pow_add]

lemma dg_mod (a n i : ℕ) (hi : i < n) : dg (a % 10 ^ n) i = dg a i := by
  unfold dg
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hi
  rw [show i + t + 1 = i + (t + 1) by ring, pow_add, Nat.mod_mul_right_div_self,
    pow_succ]
  exact Nat.mod_mod_of_dvd _ (dvd_mul_left 10 _)

lemma dg_small (a i : ℕ) (h : a < 10 ^ i) : dg a i = 0 := by
  simp [dg, Nat.div_eq_of_lt h]

lemma ds_split {a b k : ℕ} (hb : b < 10 ^ k) :
    (Nat.digits 10 (b + 10 ^ k * a)).sum = (Nat.digits 10 b).sum + (Nat.digits 10 a).sum := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  have hl : (Nat.digits 10 b).length ≤ k := (Nat.digits_length_le_iff (by norm_num) b).2 hb
  have := Nat.digits_append_zeroes_append_digits (b := 10) (k := k - (Nat.digits 10 b).length)
    (m := a) (n := b) (by norm_num) ha
  rw [Nat.add_sub_cancel' hl] at this
  rw [← this]
  simp

lemma ds_le (y : ℕ) : (Nat.digits 10 y).sum ≤ 9 * (Nat.digits 10 y).length := by
  have := List.sum_le_card_nsmul (Nat.digits 10 y) 9
    (fun d hd => by have := Nat.digits_lt_base (by norm_num) hd; omega)
  simpa [mul_comm] using this

lemma ds_le_of_lt {y n : ℕ} (h : y < 10 ^ n) : (Nat.digits 10 y).sum ≤ 9 * n :=
  (ds_le y).trans (by
    have := (Nat.digits_length_le_iff (by norm_num) y).2 h
    omega)

lemma nine_lt (k : ℕ) (hk : 2 ≤ k) : 9 * (2 * k + 1) < 10 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have : 2 ≤ 10 ^ k := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
    rw [pow_succ]; omega

lemma eighteen_lt (q : ℕ) (hq : 2 ≤ q) : 18 * (q + 1) < 10 ^ q := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have : 2 ≤ 10 ^ k := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
    rw [pow_succ]; omega

lemma top_digit {m L : ℕ} (hL : 1 ≤ L) (h1 : 10 ^ (L - 1) ≤ m) (h2 : m < 10 ^ L) :
    1 ≤ m / 10 ^ (L - 1) ∧ m / 10 ^ (L - 1) < 10 := by
  constructor
  · exact (Nat.le_div_iff_mul_le (by positivity)).2 (by simpa using h1)
  · rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc m < 10 ^ L := h2
      _ = 10 * 10 ^ (L - 1) := by rw [← pow_succ']; congr 1; omega

lemma ds_single {d : ℕ} (h : d < 10) : (Nat.digits 10 d).sum = d := by
  interval_cases d <;> simp

lemma pw {a b : ℕ} (h : a ≤ b) : 10 ^ a ≤ 10 ^ b := Nat.pow_le_pow_right (by norm_num) h

theorem big (m : ℕ) (hm : 10 ^ 4 ≤ m) (hq : qualifies m) : ∃ k, m = 10 ^ k + 1 := by
  obtain ⟨hpm, hpx⟩ := hq
  have hm0 : m ≠ 0 := by positivity
  have h1 : 10 ^ ((Nat.digits 10 m).length - 1) ≤ m := ge_of_len m hm0
  have h2 : m < 10 ^ (Nat.digits 10 m).length := lt_of_len m
  rw [pal_iff] at hpm
  generalize hLdef : (Nat.digits 10 m).length = L at h1 h2 hpm
  have hL5 : 5 ≤ L := by
    by_contra h
    have : 10 ^ L ≤ 10 ^ 4 := pw (by omega)
    omega
  have hs9 : (Nat.digits 10 m).sum ≤ 9 * L := hLdef ▸ ds_le m
  have hd0le : dg m 0 ≤ (Nat.digits 10 m).sum := by
    rw [← getElem_dg m 0 (by omega)]; exact List.le_sum_of_mem (List.getElem_mem _)
  generalize hsdef : (Nat.digits 10 m).sum = s at hs9 hpx hd0le
  have hj2 : 2 ≤ L / 2 := by omega
  have hsj : s < 10 ^ (L / 2) :=
    lt_of_le_of_lt hs9 (lt_of_le_of_lt (by omega) (nine_lt (L / 2) hj2))
  generalize hj : L / 2 = j at hj2 hsj
  have hjL : j + j ≤ L := by omega
  obtain ⟨ht1, ht2⟩ := top_digit (by omega) h1 h2
  have hdL : dg m (L - 1) = m / 10 ^ (L - 1) := Nat.mod_eq_of_lt ht2
  have hd0 : dg m 0 = m / 10 ^ (L - 1) := by
    rw [hpm 0 (by omega)]; simpa using hdL
  have hs0 : 0 < s := by omega
  have hsm : s ≤ m := by
    have := pw (show j ≤ L - 1 by omega)
    omega
  have hpj : 10 ^ j ≤ 10 ^ (L - 1) := pw (by omega)
  have hdm := Nat.div_add_mod m (10 ^ (L - 1))
  by_cases hA : m - s < 10 ^ (L - 1)
  · -- the leading digit drops: m = 10^(L-1) + 1
    have hr : m % 10 ^ (L - 1) < s := by
      have : 10 ^ (L - 1) ≤ 10 ^ (L - 1) * (m / 10 ^ (L - 1)) := Nat.le_mul_of_pos_right _ ht1
      omega
    have htop : m / 10 ^ (L - 1) = 1 := by
      by_contra hne
      have : 10 ^ (L - 1) * 2 ≤ 10 ^ (L - 1) * (m / 10 ^ (L - 1)) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    have hz1 : ∀ i, j ≤ i → i < L - 1 → dg m i = 0 := by
      intro i hi1 hi2
      rw [← dg_mod m (L - 1) i hi2]
      exact dg_small _ _ (lt_of_lt_of_le hr (lt_of_lt_of_le hsj (pw hi1)).le)
    have hz : ∀ i, 1 ≤ i → i < L - 1 → dg m i = 0 := by
      intro i hi1 hi2
      by_cases c : j ≤ i
      · exact hz1 i c hi2
      · rw [hpm i (by omega)]; exact hz1 _ (by omega) (by omega)
    have hmod : m % 10 ^ (L - 1) = 1 % 10 ^ (L - 1) := by
      apply mod_eq_of_dg
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [hd0, htop]; rfl
      · rw [hz i hi0 hi, dg_small]; exact Nat.one_lt_pow (by omega) (by norm_num)
    rw [Nat.mod_eq_of_lt (Nat.one_lt_pow (by omega) (by norm_num))] at hmod
    rw [htop, mul_one] at hdm
    exact ⟨L - 1, by omega⟩
  push Not at hA
  have hLx : (Nat.digits 10 (m - s)).length = L :=
    len_eq (by omega) hA (lt_of_le_of_lt (Nat.sub_le _ _) h2)
  rw [pal_iff, hLx] at hpx
  have hjLj : 10 ^ j ≤ 10 ^ (L - j) := pw (by omega)
  exfalso
  have hms : m - s + s = m := Nat.sub_add_cancel hsm
  by_cases hE : (m - s) / 10 ^ (L - j) = m / 10 ^ (L - j)
  · have hd : ∀ i < j, dg (m - s) i = dg m i := by
      intro i hi
      rw [hpx i (by omega), hpm i (by omega)]
      exact dg_of_div_eq hE _ (by omega)
    have hmod : m - s ≡ m [MOD 10 ^ j] := mod_eq_of_dg j hd
    have h' : (m - s) + s ≡ (m - s) + 0 [MOD 10 ^ j] := by
      rw [add_zero, hms]; exact hmod.symm
    have hdvd : 10 ^ j ∣ s := Nat.modEq_zero_iff_dvd.1 (Nat.ModEq.add_left_cancel' _ h')
    have := Nat.le_of_dvd hs0 hdvd
    omega
  have hb : m % 10 ^ (L - j) < s := by
    by_contra hc
    push Not at hc
    apply hE
    have e : m - s = (m % 10 ^ (L - j) - s) + 10 ^ (L - j) * (m / 10 ^ (L - j)) := by
      have := Nat.mod_add_div m (10 ^ (L - j)); omega
    rw [e, Nat.add_mul_div_left _ _ (by positivity),
      Nat.div_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) (Nat.mod_lt _ (by positivity))), zero_add]
  have hq0 : dg m (Nat.findGreatest (fun i => dg m i ≠ 0) (j - 1)) ≠ 0 :=
    Nat.findGreatest_spec (P := fun i => dg m i ≠ 0) (m := 0) (Nat.zero_le _) (by rw [hd0]; omega)
  have hqj : Nat.findGreatest (fun i => dg m i ≠ 0) (j - 1) ≤ j - 1 := Nat.findGreatest_le _
  have hqmax : ∀ i, Nat.findGreatest (fun i => dg m i ≠ 0) (j - 1) < i → i ≤ j - 1 →
      dg m i = 0 := fun i h1 h2 => by
    have := Nat.findGreatest_is_greatest h1 h2; simpa using this
  generalize Nat.findGreatest (fun i => dg m i ≠ 0) (j - 1) = q at hq0 hqj hqmax
  have hmid : ∀ i, q < i → i < L - 1 - q → dg m i = 0 := by
    intro i hi1 hi2
    by_cases c1 : i ≤ j - 1
    · exact hqmax i hi1 c1
    by_cases c2 : i < L - j
    · rw [← dg_mod m (L - j) i c2]
      exact dg_small _ _ (lt_of_lt_of_le hb (le_trans hsj.le (pw (by omega))))
    · rw [hpm i (by omega)]; exact hqmax _ (by omega) (by omega)
  have hlowlt : m % 10 ^ (q + 1) < 10 ^ (q + 1) := Nat.mod_lt _ (by positivity)
  have hlow : m % 10 ^ (L - 1 - q) = m % 10 ^ (q + 1) := by
    have : m % 10 ^ (L - 1 - q) = (m % 10 ^ (q + 1)) % 10 ^ (L - 1 - q) :=
      mod_eq_of_dg _ (fun i hi => by
        by_cases c : i ≤ q
        · rw [dg_mod m (q + 1) i (by omega)]
        · rw [hmid i (by omega) hi, dg_small]
          exact lt_of_lt_of_le hlowlt (pw (by omega)))
    rw [this, Nat.mod_eq_of_lt (lt_of_lt_of_le hlowlt (pw (by omega)))]
  generalize hlowdef : m % 10 ^ (q + 1) = low at hlowlt hlow
  have hm_eq : m = low + 10 ^ (L - 1 - q) * (m / 10 ^ (L - 1 - q)) := by
    rw [← hlow]; exact (Nat.mod_add_div m _).symm
  have htoplt : m / 10 ^ (L - 1 - q) < 10 ^ (q + 1) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    convert h2 using 2; omega
  have hds : s = (Nat.digits 10 low).sum + (Nat.digits 10 (m / 10 ^ (L - 1 - q))).sum := by
    rw [← hsdef]
    conv_lhs => rw [hm_eq]
    exact ds_split (lt_of_lt_of_le hlowlt (pw (by omega)))
  have hs18 : s ≤ 18 * (q + 1) := by
    have := ds_le_of_lt hlowlt; have := ds_le_of_lt htoplt; omega
  have hlows : low < s := by
    have : m % 10 ^ (L - j) = low := by
      rw [← Nat.mod_mod_of_dvd m (pow_dvd_pow 10 (show L - j ≤ L - 1 - q by omega)), hlow,
        Nat.mod_eq_of_lt (lt_of_lt_of_le hlowlt (pw (by omega)))]
    omega
  have hps : low = m % 10 ^ q + 10 ^ q * (m / 10 ^ q % 10) := by
    rw [← hlowdef]; exact Nat.mod_pow_succ
  have hDpos : 1 ≤ dg m q := Nat.pos_of_ne_zero hq0
  have hlow_ge : 10 ^ q ≤ low := by
    have : 10 ^ q * 1 ≤ 10 ^ q * dg m q := Nat.mul_le_mul_left _ hDpos
    simp only [dg] at this; omega
  generalize htopdef : m / 10 ^ (L - 1 - q) = top at hm_eq htoplt hds
  have htop0 : dg top 0 = dg m q := by
    rw [← htopdef, dg_div, add_zero, hpm (L - 1 - q) (by omega)]; congr 1; omega
  have htopmod : top % 10 ≠ 0 := by
    have := htop0 ▸ hq0; simpa [dg] using this
  have htop1 : 1 ≤ top := by omega
  have hx_div : (m - s) / 10 ^ (L - 1 - q) = top - 1 := by
    have hpq : 10 ^ j ≤ 10 ^ (L - 1 - q) := pw (by omega)
    have hw : m - s = (10 ^ (L - 1 - q) + low - s) + 10 ^ (L - 1 - q) * (top - 1) := by
      have : 10 ^ (L - 1 - q) * top = 10 ^ (L - 1 - q) * (top - 1) + 10 ^ (L - 1 - q) := by
        rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ htop1)]
      omega
    rw [hw, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (by omega), zero_add]
  have hT0 : dg (top - 1) 0 = dg top 0 - 1 := by
    simp only [dg, pow_zero, Nat.div_one]; omega
  have hTk : ∀ k, dg (top - 1) (1 + k) = dg top (1 + k) := by
    intro k
    have : (top - 1) / 10 = top / 10 := by omega
    rw [← dg_div, ← dg_div, pow_one, this]
  have hxi : ∀ i < q, dg (m - s) i = dg m i := by
    intro i hi
    rw [hpx i (by omega), hpm i (by omega)]
    have e1 : L - 1 - i = (L - 1 - q) + (1 + (q - i - 1)) := by omega
    rw [e1, ← dg_div (m - s) (L - 1 - q), ← dg_div m (L - 1 - q), hx_div, htopdef, hTk]
  have hxq : dg (m - s) q = dg m q - 1 := by
    rw [hpx q (by omega), hpm q (by omega)]
    have e1 : L - 1 - q = (L - 1 - q) + 0 := by omega
    rw [e1, ← dg_div (m - s) (L - 1 - q), ← dg_div m (L - 1 - q), hx_div, htopdef, hT0]
  have hxmod : (m - s) % 10 ^ (q + 1) = low - 10 ^ q := by
    rw [Nat.mod_pow_succ, mod_eq_of_dg q hxi]
    have hxq' : (m - s) / 10 ^ q % 10 = dg m q - 1 := hxq
    rw [hxq']
    have : 10 ^ q * (dg m q - 1) + 10 ^ q = 10 ^ q * dg m q := by
      rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ hDpos)]
    simp only [dg] at this hps ⊢
    omega
  have hcong : low + (s - 10 ^ q) ≡ low + 0 [MOD 10 ^ (q + 1)] := by
    have e : low + (s - 10 ^ q) = (m - s) % 10 ^ (q + 1) + s := by omega
    rw [e, add_zero, ← hlowdef]
    calc (m - s) % 10 ^ (q + 1) + s ≡ (m - s) + s [MOD 10 ^ (q + 1)] :=
          Nat.ModEq.add_right _ (Nat.mod_modEq _ _)
      _ = m := hms
      _ ≡ m % 10 ^ (q + 1) [MOD 10 ^ (q + 1)] := (Nat.mod_modEq _ _).symm
  obtain ⟨c, hc⟩ := Nat.modEq_zero_iff_dvd.1 (Nat.ModEq.add_left_cancel' _ hcong)
  rcases Nat.lt_or_ge q 2 with hq2 | hq2
  · interval_cases q
    · -- q = 0
      have hlow0 : low = dg m 0 := by simp only [dg] at hps ⊢; omega
      have htopv : top = dg m 0 := by
        rw [← htop0]; simp only [dg, pow_zero, Nat.div_one]; omega
      rw [ds_single (by omega), ds_single (by omega)] at hds
      omega
    · -- q = 1
      norm_num at hc hs18 hlow_ge
      omega
  · have := eighteen_lt q hq2
    omega

lemma pow_eq (k i : ℕ) (h : i ≤ k) : 10 ^ k = 10 ^ i * 10 ^ (k - i) := by
  rw [← pow_add]; congr 1; omega

lemma dg_pow_add (k i : ℕ) (hk : 1 ≤ k) (hi : i ≤ k) :
    dg (10 ^ k + 1) i = if i = 0 ∨ i = k then 1 else 0 := by
  unfold dg
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · have : 10 ^ k = 10 * 10 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
    simp; omega
  · rw [pow_eq k i hi, show 10 ^ i * 10 ^ (k - i) + 1 = 1 + 10 ^ i * 10 ^ (k - i) by ring,
      Nat.add_mul_div_left _ _ (by positivity),
      Nat.div_eq_of_lt (Nat.one_lt_pow (by omega) (by norm_num)), zero_add]
    by_cases h : i = k
    · subst h; simp
    · have : 10 ^ (k - i) = 10 * 10 ^ (k - i - 1) := by rw [← pow_succ']; congr 1; omega
      rw [if_neg (by omega), this]; simp

lemma dg_pow_sub (k i : ℕ) (hi : i < k) : dg (10 ^ k - 1) i = 9 := by
  unfold dg
  have h1 : 1 ≤ 10 ^ i := Nat.one_le_pow _ _ (by norm_num)
  have h2 : 1 ≤ 10 ^ (k - i) := Nat.one_le_pow _ _ (by norm_num)
  have e : 10 ^ k - 1 = (10 ^ i - 1) + 10 ^ i * (10 ^ (k - i) - 1) := by
    rw [pow_eq k i hi.le, Nat.mul_sub_one]
    have : 10 ^ i ≤ 10 ^ i * 10 ^ (k - i) := Nat.le_mul_of_pos_right _ h2
    omega
  rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (by omega), zero_add]
  have : 10 ^ (k - i) = 10 * 10 ^ (k - i - 1) := by rw [← pow_succ']; congr 1; omega
  have : 1 ≤ 10 ^ (k - i - 1) := Nat.one_le_pow _ _ (by norm_num)
  omega

theorem qual_pow (k : ℕ) (hk : 1 ≤ k) : qualifies (10 ^ k + 1) := by
  have hds : (Nat.digits 10 (10 ^ k + 1)).sum = 2 := by
    rw [show 10 ^ k + 1 = 1 + 10 ^ k * 1 by ring, ds_split (Nat.one_lt_pow (by omega) (by norm_num))]
    simp
  have hlt : 10 ^ k + 1 < 10 ^ (k + 1) := by rw [pow_succ]; have := Nat.one_le_pow k 10 (by norm_num); omega
  refine ⟨?_, ?_⟩
  · rw [pal_iff, len_eq (L := k + 1) (by omega) (by simp) hlt]
    intro i hi
    rw [dg_pow_add k i hk (by omega), dg_pow_add k _ hk (by omega)]
    by_cases h : i = 0 ∨ i = k
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  · rw [hds, show 10 ^ k + 1 - 2 = 10 ^ k - 1 by omega]
    have hge : 10 ^ (k - 1) ≤ 10 ^ k - 1 := by
      have : 10 ^ k = 10 * 10 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
      omega
    rw [pal_iff, len_eq (L := k) hk hge (by have := Nat.one_le_pow k 10 (by norm_num); omega)]
    intro i hi
    rw [dg_pow_sub k i hi, dg_pow_sub k _ (by omega)]

instance : DecidablePred qualifies := fun m => by unfold qualifies; infer_instance

set_option maxRecDepth 100000 in
lemma count3 : Nat.count qualifies 1001 = 20 := by decide

set_option maxRecDepth 100000 in
lemma count4 : Nat.count qualifies 10001 = 21 := by decide

lemma count_step (k : ℕ) (hk : 4 ≤ k) :
    Nat.count qualifies (10 ^ (k + 1) + 1) = Nat.count qualifies (10 ^ k + 1) + 1 := by
  have hb : 10 ^ (k + 1) + 1 = (10 ^ k + 1) + ((9 * 10 ^ k - 1) + 1) := by
    rw [pow_succ]; have := Nat.one_le_pow k 10 (by norm_num); omega
  rw [hb, Nat.count_add]
  congr 1
  rw [Nat.count_succ', if_pos (by simpa using qual_pow k (by omega)), Nat.add_eq_right,
    Nat.count_eq_card_filter_range, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro t ht hq
  simp only [Finset.mem_range] at ht
  have h4 : 10 ^ 4 ≤ 10 ^ k + 1 + (t + 1) := le_trans (pw hk) (by omega)
  obtain ⟨i, hi⟩ := big _ h4 hq
  have hlo : 10 ^ k < 10 ^ i := by omega
  have hhi : 10 ^ i < 10 ^ (k + 1) := by rw [pow_succ] at *; omega
  rw [Nat.pow_lt_pow_iff_right (by norm_num)] at hlo hhi
  omega

lemma count_pow (k : ℕ) (hk : 4 ≤ k) : Nat.count qualifies (10 ^ k + 1) = k + 17 := by
  induction k, hk using Nat.le_induction with
  | base => exact count4
  | succ k hk ih => rw [count_step k hk, ih]

end OMA.P_a229623

open OMA.S_oeis_a229623 OMA.P_a229623 in
theorem OMA.solution : type_of% @OMA.S_oeis_a229623.main := by
  intro n hn
  rcases Nat.lt_or_ge n 22 with h | h
  · obtain rfl : n = 21 := by omega
    have := Nat.nth_count (qual_pow 3 (by norm_num))
    norm_num at this ⊢
    rwa [count3] at this
  · have := Nat.nth_count (qual_pow (n - 18) (by omega))
    rwa [count_pow (n - 18) (by omega), show n - 18 + 17 = n - 1 by omega] at this
