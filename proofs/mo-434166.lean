import OMAStatements.S_mo_434166
import Mathlib
open OMA.S_mo_434166

/-- The natural power sum `1^k + ... + n^k`. -/
def PS (k n : ℕ) : ℕ := ∑ j ∈ Finset.Icc 1 n, j ^ k

lemma ps_succ (k n : ℕ) : PS k (n + 1) = PS k n + (n + 1) ^ k := by
  unfold PS
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma ps2 (n : ℕ) : 6 * PS 2 n = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp [PS]
  | succ n ih => rw [ps_succ, mul_add, ih]; ring

lemma ps3 (n : ℕ) : 4 * PS 3 n = (n * (n + 1)) ^ 2 := by
  induction n with
  | zero => simp [PS]
  | succ n ih => rw [ps_succ, mul_add, ih]; ring

lemma key (k n p : ℕ) (hp : p.Prime) (hpn : p ≤ n) (hn : n < 2 * p)
    (h : ∃ m : ℤ, F k n = m) : p ^ k ∣ PS k n := by
  obtain ⟨m, hm⟩ := h
  have hp0 : 0 < p := hp.pos
  have hmem : p ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hp0, hpn⟩
  set T := (Finset.Icc 1 n).erase p with hT
  set D : ℕ := ∏ j ∈ T, j ^ k with hD
  have hTpos : ∀ j ∈ T, 0 < j := by
    intro j hj
    have := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hj)).1
    omega
  have hcop : Nat.Coprime (p ^ k) D := by
    apply Nat.Coprime.pow_left
    apply Nat.Coprime.prod_right
    intro j hj
    apply Nat.Coprime.pow_right
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    rintro ⟨t, rfl⟩
    have hj' := Finset.mem_erase.mp hj
    have h1 := Finset.mem_Icc.mp hj'.2
    have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0; simp at h1
      · exact h0
    have ht2 : t < 2 := by
      by_contra hc
      rw [not_lt] at hc
      have : p * 2 ≤ p * t := Nat.mul_le_mul_left p hc
      omega
    have : t = 1 := by omega
    subst this
    exact hj'.1 (by ring)
  have hdvd : ∀ j ∈ T, j ^ k ∣ D := fun j hj => Finset.dvd_prod_of_mem _ hj
  set N : ℕ := ∑ j ∈ T, D / j ^ k with hN
  have hHsplit : (∑ j ∈ Finset.Icc 1 n, 1 / (j : ℚ) ^ k)
      = 1 / (p : ℚ) ^ k + ∑ j ∈ T, 1 / (j : ℚ) ^ k := by
    exact (Finset.add_sum_erase _ (fun j : ℕ => 1 / (j : ℚ) ^ k) hmem).symm
  have hDN : (D : ℚ) * ∑ j ∈ T, 1 / (j : ℚ) ^ k = N := by
    rw [hN, Finset.mul_sum, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj0 : (j : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast (hTpos j hj).ne')
    rw [Nat.cast_div (hdvd j hj) (by exact_mod_cast hj0)]
    push_cast
    try field_simp
  have hS : (∑ j ∈ Finset.Icc 1 n, (j : ℚ) ^ k) = (PS k n : ℚ) := by
    simp [PS]
  have hpk : (p : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp0.ne')
  have eq1 : (m : ℚ) * D * p ^ k = (PS k n : ℚ) * (D + N * p ^ k) := by
    rw [← hm, F, hS, hHsplit, ← hDN]
    field_simp
    try ring
  have eq2 : (m : ℤ) * D * p ^ k = (PS k n : ℤ) * (D + N * p ^ k) := by
    exact_mod_cast eq1
  have h3 : ((p ^ k : ℕ) : ℤ) ∣ ((PS k n * D : ℕ) : ℤ) := by
    refine ⟨m * D - PS k n * N, ?_⟩
    push_cast
    linear_combination (-1 : ℤ) * eq2
  have h4 : p ^ k ∣ PS k n * D := Int.natCast_dvd_natCast.mp h3
  exact hcop.dvd_of_dvd_mul_right h4

lemma mul_eq_of_bounds {p x c : ℕ} (hd : p ∣ x) (h1 : c * p < x) (h2 : x < (c + 2) * p) :
    x = (c + 1) * p := by
  obtain ⟨t, rfl⟩ := hd
  have hlo : c < t := by
    by_contra hc
    rw [not_lt] at hc
    have := Nat.mul_le_mul_left p hc
    nlinarith
  have hhi : t < c + 2 := by
    by_contra hc
    rw [not_lt] at hc
    have := Nat.mul_le_mul_left p hc
    nlinarith
  have : t = c + 1 := by omega
  subst this
  ring

lemma red2 {p X Y : ℕ} (hp : 0 < p) (h : p ^ 2 ∣ X) (hX : X = p * Y) : p ∣ Y := by
  subst hX
  rw [pow_two] at h
  exact Nat.dvd_of_mul_dvd_mul_left hp h

lemma red3 {p X Y : ℕ} (hp : 0 < p) (h : p ^ 3 ∣ X) (hX : X = p ^ 2 * Y) : p ∣ Y := by
  subst hX
  rw [pow_succ] at h
  exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hp 2) h

lemma no_one {p : ℕ} (hp : p.Prime) (h : p ∣ 1) : False :=
  hp.one_lt.ne' (Nat.dvd_one.mp h)

lemma L2 (n p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hpn : p ≤ n) (hn : n < 2 * p)
    (h : p ^ 2 ∣ n * (n + 1) * (2 * n + 1)) : False := by
  have hp0 := hp.pos
  have hp1 : p ∣ n * (n + 1) * (2 * n + 1) := (dvd_pow_self p two_ne_zero).trans h
  rcases (Nat.Prime.dvd_mul hp).mp hp1 with h12 | h3
  · rcases (Nat.Prime.dvd_mul hp).mp h12 with ha | hb
    · have hn1 : n = (0 + 1) * p := mul_eq_of_bounds ha (by omega) (by omega)
      have hY : p ∣ (n + 1) * (2 * n + 1) :=
        red2 hp0 h (by rw [hn1]; ring)
      rcases (Nat.Prime.dvd_mul hp).mp hY with h1 | h1
      · exact no_one hp ((Nat.dvd_add_right ha).mp h1)
      · exact no_one hp ((Nat.dvd_add_right (dvd_mul_of_dvd_right ha 2)).mp h1)
    · have hn1 : n + 1 = (1 + 1) * p := mul_eq_of_bounds hb (by omega) (by omega)
      have hY : p ∣ 2 * n * (2 * n + 1) :=
        red2 hp0 h (by
          have : n * (n + 1) * (2 * n + 1) = n * ((1 + 1) * p) * (2 * n + 1) := by rw [hn1]
          rw [this]; ring)
      rcases (Nat.Prime.dvd_mul hp).mp hY with h1 | h1
      · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
        · have := Nat.le_of_dvd (by norm_num) h2
          omega
        · exact no_one hp ((Nat.dvd_add_right h2).mp hb)
      · have h2 : p ∣ 2 * n + 1 + 1 := by
          have : 2 * n + 1 + 1 = 2 * (n + 1) := by ring
          rw [this]; exact dvd_mul_of_dvd_right hb 2
        exact no_one hp ((Nat.dvd_add_right h1).mp h2)
  · have hn1 : 2 * n + 1 = (2 + 1) * p := mul_eq_of_bounds h3 (by omega) (by omega)
    have hY : p ∣ 3 * n * (n + 1) :=
      red2 hp0 h (by rw [hn1]; ring)
    rcases (Nat.Prime.dvd_mul hp).mp hY with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
      · have := Nat.le_of_dvd (by norm_num) h2
        omega
      · have := mul_eq_of_bounds h2 (c := 0) (by omega) (by omega)
        omega
    · have := mul_eq_of_bounds h1 (c := 1) (by omega) (by omega)
      omega

lemma L3 (n p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (hpn : p ≤ n) (hn : n < 2 * p)
    (h : p ^ 3 ∣ (n * (n + 1)) ^ 2) : False := by
  have hp0 := hp.pos
  have hp1 : p ∣ n * (n + 1) :=
    hp.dvd_of_dvd_pow ((dvd_pow_self p (by norm_num : (3 : ℕ) ≠ 0)).trans h)
  rcases (Nat.Prime.dvd_mul hp).mp hp1 with ha | hb
  · have hn1 : n = (0 + 1) * p := mul_eq_of_bounds ha (by omega) (by omega)
    have hY : p ∣ (n + 1) ^ 2 := red3 hp0 h (by rw [hn1]; ring)
    exact no_one hp ((Nat.dvd_add_right ha).mp (hp.dvd_of_dvd_pow hY))
  · have hn1 : n + 1 = (1 + 1) * p := mul_eq_of_bounds hb (by omega) (by omega)
    have hY : p ∣ (2 * n) ^ 2 := red3 hp0 h (by
      have : (n * (n + 1)) ^ 2 = (n * ((1 + 1) * p)) ^ 2 := by rw [hn1]
      rw [this]; ring)
    rcases (Nat.Prime.dvd_mul hp).mp (hp.dvd_of_dvd_pow hY) with h2 | h2
    · have := Nat.le_of_dvd (by norm_num) h2
      omega
    · exact no_one hp ((Nat.dvd_add_right h2).mp hb)

lemma exists_p (n : ℕ) (h : 5 ≤ n) : ∃ p, p.Prime ∧ 5 ≤ p ∧ p ≤ n ∧ n < 2 * p := by
  by_cases h10 : n < 10
  · exact ⟨5, by norm_num, le_rfl, h, by omega⟩
  · obtain ⟨p, hp, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega)
    exact ⟨p, hp, by omega, by omega, by omega⟩

lemma not_int_of {q : ℚ} {a b : ℤ} (hq : q * (b : ℚ) = a) (hb : 0 < b) (hab : ¬ b ∣ a) :
    ¬ ∃ m : ℤ, q = m := by
  rintro ⟨m, rfl⟩
  have : m * b = a := by exact_mod_cast hq
  exact hab ⟨m, by rw [← this]; ring⟩

lemma F_one (k : ℕ) : F k 1 = ((1 : ℤ) : ℚ) := by
  simp [F]

theorem OMA.solution : type_of% @OMA.S_mo_434166.main := by
  intro n hn
  by_cases h5 : 5 ≤ n
  · obtain ⟨p, hp, hp5, hpn, hnp⟩ := exists_p n h5
    refine ⟨⟨fun h => ?_, fun h => by omega⟩, ⟨fun h => ?_, fun h => by omega⟩⟩
    · have h1 := key 2 n p hp hpn hnp h
      have h2 : p ^ 2 ∣ n * (n + 1) * (2 * n + 1) := by
        rw [← ps2]; exact dvd_mul_of_dvd_right h1 6
      exact (L2 n p hp hp5 hpn hnp h2).elim
    · have h1 := key 3 n p hp hpn hnp h
      have h2 : p ^ 3 ∣ (n * (n + 1)) ^ 2 := by
        rw [← ps3]; exact dvd_mul_of_dvd_right h1 4
      exact (L3 n p hp hp5 hpn hnp h2).elim
  · have hcases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact ⟨⟨fun _ => rfl, fun _ => ⟨1, F_one 2⟩⟩, ⟨fun _ => rfl, fun _ => ⟨1, F_one 3⟩⟩⟩
    · refine ⟨⟨fun h => (not_int_of (a := 25) (b := 4) ?_ (by norm_num) (by decide) h).elim,
        fun h => by omega⟩,
        ⟨fun h => (not_int_of (a := 81) (b := 8) ?_ (by norm_num) (by decide) h).elim,
        fun h => by omega⟩⟩
      · simp [F, show Finset.Icc 1 2 = {1, 2} by decide]; norm_num
      · simp [F, show Finset.Icc 1 2 = {1, 2} by decide]; norm_num
    · refine ⟨⟨fun h => (not_int_of (a := 343) (b := 18) ?_ (by norm_num) (by decide) h).elim,
        fun h => by omega⟩,
        ⟨fun h => (not_int_of (a := 251) (b := 6) ?_ (by norm_num) (by decide) h).elim,
        fun h => by omega⟩⟩
      · simp [F, show Finset.Icc 1 3 = {1, 2, 3} by decide]; norm_num
      · simp [F, show Finset.Icc 1 3 = {1, 2, 3} by decide]; norm_num
    · refine ⟨⟨fun h => (not_int_of (a := 1025) (b := 24) ?_ (by norm_num) (by decide) h).elim,
        fun h => by omega⟩,
        ⟨fun h => (not_int_of (a := 50875) (b := 432) ?_ (by norm_num) (by decide) h).elim,
        fun h => by omega⟩⟩
      · simp [F, show Finset.Icc 1 4 = {1, 2, 3, 4} by decide]; norm_num
      · simp [F, show Finset.Icc 1 4 = {1, 2, 3, 4} by decide]; norm_num
