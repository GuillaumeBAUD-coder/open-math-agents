import OMAStatements.S_oeis_a374446

namespace OMA.A374446Proof

open Polynomial

def good4 (m : ℕ) : Prop := ∀ d ∈ Nat.digits 4 m, d = 0 ∨ d = 3

lemma good4_zero : good4 0 := by simp [good4]

lemma good4_step {m : ℕ} (hm : m ≠ 0) : good4 m ↔
    (m % 4 = 0 ∨ m % 4 = 3) ∧ good4 (m / 4) := by
  rw [good4, Nat.digits_eq_cons_digits_div (by decide) hm]
  simp [good4]

lemma good4_4n_three (n : ℕ) : good4 (4*n+3) ↔ good4 n := by
  rw [good4_step (by omega)]
  have hmod : (4*n+3) % 4 = 3 := by omega
  have hdiv : (4*n+3) / 4 = n := by omega
  simp [hmod, hdiv]

lemma good4_4n_zero (n : ℕ) : good4 (4*n) ↔ good4 n := by
  by_cases hn : n=0
  · subst n; simp [good4_zero]
  · rw [good4_step (by omega)]
    have hmod : (4*n) % 4 = 0 := by omega
    have hdiv : (4*n) / 4 = n := by omega
    simp [hmod, hdiv]

lemma good4_4n_one (n : ℕ) : ¬good4 (4*n+1) := by
  rw [good4_step (by omega)]
  have hmod : (4*n+1) % 4 = 1 := by omega
  simp [hmod]

lemma good4_4n_two (n : ℕ) : ¬good4 (4*n+2) := by
  rw [good4_step (by omega)]
  have hmod : (4*n+2) % 4 = 2 := by omega
  simp [hmod]

lemma zero_iff_good4 (A : ℕ → ℤ)
    (h_even0 : ∀ n, (A (4*n) : ZMod 2) = 1)
    (h_even1 : ∀ n, (A (4*n+1) : ZMod 2) = 1)
    (h_two : ∀ n, A (4*n+2) = if n = 0 then 0 else 8*A (n-1))
    (h_three : ∀ n, A (4*n+3) = 8*A n) :
    ∀ n, A n = 0 ↔ good4 (n+1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let q := n / 4
    have hn : n = 4*q + n%4 := by dsimp [q]; omega
    have hr : n%4 < 4 := Nat.mod_lt _ (by decide)
    interval_cases h : n%4
    ·
      have hn0 : n = 4*q := by omega
      rw [hn0]
      have hz : A (4*q) ≠ 0 := by
        intro hh
        have ht := h_even0 q
        rw [hh] at ht
        norm_num at ht
      have hg : ¬good4 (4*q+1) := good4_4n_one q
      simp [hz, hg]
    ·
      have hn1 : n = 4*q+1 := by omega
      rw [hn1]
      have hz : A (4*q+1) ≠ 0 := by
        intro hh
        have ht := h_even1 q
        rw [hh] at ht
        norm_num at ht
      have hg : ¬good4 (4*q+2) := good4_4n_two q
      simpa using (show A (4*q+1) = 0 ↔ good4 (4*q+2) by simp [hz, hg])
    ·
      have hn2 : n = 4*q+2 := by omega
      by_cases hq : q=0
      · subst q
        have hn' : n = 2 := by omega
        subst n
        have ha : A 2 = 0 := by simpa using h_two 0
        have hg : good4 3 := by simpa using (good4_4n_three 0).mpr good4_zero
        simpa [ha] using hg
      · have hqle : q - 1 < n := by omega
        have heq := ih (q-1) hqle
        have hh := h_two q
        rw [if_neg hq] at hh
        have hg : good4 (n+1) ↔ good4 q := by
          have hn3 : n + 1 = 4*q+3 := by omega
          rw [hn3, good4_4n_three]
        have hq1 : q - 1 + 1 = q := by omega
        rw [hq1] at heq
        rw [hg, hn2, hh]
        simpa using heq
    ·
      have hn3 : n = 4*q+3 := by omega
      have hqle : q < n := by omega
      have heq := ih q hqle
      have hg : good4 (n+1) ↔ good4 (q+1) := by
        have he : n + 1 = 4*(q+1) := by omega
        rw [he, good4_4n_zero]
      rw [hg, hn3, h_three]
      simpa using heq

noncomputable def P (K : ℕ) : ℤ[X] := ∏ k ∈ Finset.range K, (1 - X ^ (2 ^ k)) ^ 3

lemma P_succ (k : ℕ) : P (k+1) = (1-X)^3 * Polynomial.expand ℤ 2 (P k) := by
  unfold P
  rw [Finset.prod_range_succ']
  simp only [pow_zero, pow_one]
  conv_lhs => rw [mul_comm]
  congr 1
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [map_pow, map_sub, map_one, Polynomial.expand_X]
  have hpow : 2 ^ (j+1) = 2 * 2^j := by simp [pow_succ]; ring
  rw [hpow, pow_mul]

lemma P_coeff_stable_step {k n : ℕ} (h : n < 2^k) : (P (k+1)).coeff n = (P k).coeff n := by
  have hp : P (k+1) = P k + (P k * (-3 + 3 * X^(2^k) - X^(2^k) * X^(2^k))) * X^(2^k) := by
    unfold P
    rw [Finset.prod_range_succ]
    ring
  rw [hp, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow']
  simp [show ¬2^k ≤ n by omega]

lemma P_coeff_stable {n k l : ℕ} (h : n < 2^k) (hkl : k ≤ l) : (P l).coeff n = (P k).coeff n := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    rw [P_coeff_stable_step (lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hkl)), ih]

noncomputable def A (n : ℕ) : ℤ := (P (n+1)).coeff n

lemma A_coeff_eq (n k : ℕ) (h : n < 2^k) : A n = (P k).coeff n := by
  unfold A
  by_cases hkn : k ≤ n+1
  · exact P_coeff_stable h hkn
  · symm
    apply P_coeff_stable (lt_trans (Nat.lt_two_pow_self (n := n)) (Nat.pow_lt_pow_right (by decide) (by omega : n < n+1)))
    omega

lemma P_double (k : ℕ) : P (k+2) = (1-X)^3 * (1-X^2)^3 * Polynomial.expand ℤ 4 (P k) := by
  rw [show k+2=(k+1)+1 by omega, P_succ, P_succ]
  simp only [map_mul, map_pow, map_sub, map_one, Polynomial.expand_X]
  rw [← Polynomial.expand_mul]
  norm_num
  ring

lemma four_factor_identity : (1-(X : ℤ[X]))^3 * (1-X^2)^3 =
    1 - 3*X + 8*X^3 - 6*X^4 - 6*X^5 + 8*X^6 - 3*X^8 + X^9 := by ring


lemma coeff_mod4_three (f : ℤ[X]) (n : ℕ) :
    ((1-X)^3*(1-X^2)^3 * Polynomial.expand ℤ 4 f).coeff (4*n+3) = 8*f.coeff n := by
  let F := Polynomial.expand ℤ 4 f
  have he : (1-X)^3*(1-X^2)^3 * F =
      F - 3*F*X^1 + 8*F*X^3 - 6*F*X^4 - 6*F*X^5 + 8*F*X^6 - 3*F*X^8 + F*X^9 := by ring
  rw [he]
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_mul_X_pow',
    Polynomial.coeff_ofNat_mul]
  dsimp [F]
  simp only [Polynomial.coeff_expand (p := 4) (by decide)]
  rcases n with _ | _ | n
  · simp
  · simp
  · have h1 : (4*(n+1+1)-1)%4 ≠ 0 := by omega
    have h2 : (4*(n+1+1)-2)%4 ≠ 0 := by omega
    have h3 : (4*(n+1+1)-3)%4 ≠ 0 := by omega
    have h5 : (4*(n+1+1)-5)%4 ≠ 0 := by omega
    have h6 : (4*(n+1+1)-6)%4 ≠ 0 := by omega
    simp [Nat.dvd_iff_mod_eq_zero, h1,h2,h3,h5,h6]


lemma coeff_mod4_two (f : ℤ[X]) (n : ℕ) :
    ((1-X)^3*(1-X^2)^3 * Polynomial.expand ℤ 4 f).coeff (4*n+2) =
    if n=0 then 0 else 8*f.coeff (n-1) := by
  let F := Polynomial.expand ℤ 4 f
  have he : (1-X)^3*(1-X^2)^3 * F =
      F - 3*F*X^1 + 8*F*X^3 - 6*F*X^4 - 6*F*X^5 + 8*F*X^6 - 3*F*X^8 + F*X^9 := by ring
  rw [he]
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_mul_X_pow',
    Polynomial.coeff_ofNat_mul]
  dsimp [F]
  simp only [Polynomial.coeff_expand (p := 4) (by decide)]
  rcases n with _ | _ | n
  · simp
  · simp
  · have h1 : (4*(n+1+1)-2)%4 ≠ 0 := by omega
    have h2 : (4*(n+1+1)-3)%4 ≠ 0 := by omega
    have h3 : (4*(n+1+1)-7)%4 ≠ 0 := by omega
    have h4 : (4*(n+1+1)-1)%4 ≠ 0 := by omega
    have h5 : (4*(n+1+1)-6)%4 ≠ 0 := by omega
    have hm : (4*(n+1+1)-4)%4 = 0 := by omega
    have hd : (4*(n+1+1)-4)/4 = n+1 := by omega
    simp [Nat.dvd_iff_mod_eq_zero, h1,h2,h3,h4,h5,hm,hd]

lemma A_four_three (n : ℕ) : A (4*n+3) = 8*A n := by
  have hpow : n < 2^n := Nat.lt_two_pow_self
  have hbig : 4*n+3 < 2^((n+1)+2) := by
    rw [show (n+1)+2 = n+1+1+1 by omega, pow_succ, pow_succ, pow_succ]
    nlinarith
  rw [A_coeff_eq _ ((n+1)+2) hbig, P_double, coeff_mod4_three]
  have hn : n < 2^(n+1) := by rw [pow_succ]; nlinarith
  rw [A_coeff_eq n (n+1) hn]

lemma A_four_two (n : ℕ) : A (4*n+2) = if n=0 then 0 else 8*A (n-1) := by
  have hpow : n < 2^n := Nat.lt_two_pow_self
  have hbig : 4*n+2 < 2^((n+1)+2) := by
    rw [show (n+1)+2 = n+1+1+1 by omega, pow_succ, pow_succ, pow_succ]
    nlinarith
  rw [A_coeff_eq _ ((n+1)+2) hbig, P_double, coeff_mod4_two]
  split_ifs with hn
  · rfl
  · have hsmall : n-1 < 2^(n+1) := by
      have hbase : n-1 < 2^n := by omega
      rw [pow_succ]
      nlinarith
    rw [A_coeff_eq (n-1) (n+1) hsmall]

lemma char2square (f : (ZMod 2)[X]) : (1-f)^2=1-f^2 := by
  have h2 : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
  simp only [sub_eq_add_neg, CharTwo.neg_eq]
  ring_nf
  simp [h2]

noncomputable def Q (K : ℕ) : (ZMod 2)[X] := ∏ k ∈ Finset.range K, (1 - X ^ (2 ^ k)) ^ 3

lemma Q_succ (k : ℕ) : Q (k+1) = Q k * (1 - X ^ (2 ^ k)) ^ 3 := by
  simp [Q, Finset.prod_range_succ]

lemma Q_telescoping (k : ℕ) : Q k * (1-X)^3 = (1-X^(2^k))^3 := by
  induction k with
  | zero => simp [Q]
  | succ k ih =>
    calc
      Q (k+1) * (1-X)^3 = (Q k * (1-X)^3) * (1-X^(2^k))^3 := by rw [Q_succ]; ring
      _ = (1-X^(2^k))^3 * (1-X^(2^k))^3 := by rw [ih]
      _ = ((1-X^(2^k))^2)^3 := by ring
      _ = (1-X^(2^k*2))^3 := by rw [char2square, pow_mul]
      _ = (1-X^(2^(k+1)))^3 := by
        have hh : 2^(k+1) = 2^k*2 := pow_succ _ _
        rw [hh]

lemma Q_eq_map_P (k : ℕ) : Q k = (P k).map (Int.castRingHom (ZMod 2)) := by
  unfold Q P
  simp [Polynomial.map_prod]

lemma char2pow4 : (1-(X : (ZMod 2)[X]))^4 = 1-X^4 := by
  calc
    (1-(X : (ZMod 2)[X]))^4 = ((1-X)^2)^2 := by ring
    _ = (1-X^2)^2 := by rw [char2square]
    _ = 1-X^4 := by rw [char2square]; ring

lemma Q_telescoping4 (k : ℕ) : Q k * (1-X^4) = (1-X^(2^k))^3 * (1-X) := by
  rw [← char2pow4]
  calc
    Q k * (1-X)^4 = (Q k * (1-X)^3) * (1-X) := by ring
    _ = (1-X^(2^k))^3 * (1-X) := by rw [Q_telescoping]

lemma Q_coeff_period {k n : ℕ} (hn : 4 ≤ n) (hk : n < 2^k) :
    (Q k).coeff n = (Q k).coeff (n-4) := by
  have hs : ((1-X^(2^k))^3 * (1-X) : (ZMod 2)[X]) =
      (1-X) + ((1-X) * (-3+3*X^(2^k)-X^(2^k)*X^(2^k))) * X^(2^k) := by ring
  have h := congrArg (fun f : (ZMod 2)[X] => f.coeff n) (Q_telescoping4 k)
  rw [hs, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow', if_neg (by omega)] at h
  have hz : ((1-X : (ZMod 2)[X]).coeff n) = 0 := by
    simp [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X, show n ≠ 0 by omega, show 1 ≠ n by omega]
  rw [hz, add_zero] at h
  rw [mul_sub, mul_one, Polynomial.coeff_sub, Polynomial.coeff_mul_X_pow', if_pos hn] at h
  exact sub_eq_zero.mp h

lemma Q_coeff_eq (n k : ℕ) (h : n < 2^k) : (Q k).coeff n = (A n : ZMod 2) := by
  rw [Q_eq_map_P, Polynomial.coeff_map, A_coeff_eq n k h]
  rfl

lemma A_parity_period {n : ℕ} (hn : 4 ≤ n) : (A n : ZMod 2) = (A (n-4) : ZMod 2) := by
  have hp : n < 2^(n+1) := by
    have := Nat.lt_two_pow_self (n := n)
    rw [pow_succ]
    nlinarith
  have hp' : n-4 < 2^(n+1) := by omega
  have h := Q_coeff_period (k := n+1) hn hp
  rwa [Q_coeff_eq n _ hp, Q_coeff_eq (n-4) _ hp'] at h

lemma P_two : P 2 = (1-X)^3*(1-X^2)^3 := by simp [P, Finset.prod_range_succ]

lemma A_zero : A 0 = 1 := by
  rw [A_coeff_eq 0 2 (by norm_num), P_two, four_factor_identity]
  norm_num [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_ofNat_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one]

lemma A_one : A 1 = -3 := by
  rw [A_coeff_eq 1 2 (by norm_num), P_two, four_factor_identity]
  norm_num [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_ofNat_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one]

lemma A_four_zero_cast (n : ℕ) : (A (4*n) : ZMod 2) = 1 := by
  induction n with
  | zero => simp [A_zero]
  | succ n ih =>
    have h := A_parity_period (n := 4*(n+1)) (by omega)
    have he : 4*(n+1)-4 = 4*n := by omega
    rw [he] at h
    exact h.trans ih

lemma A_four_one_cast (n : ℕ) : (A (4*n+1) : ZMod 2) = 1 := by
  induction n with
  | zero =>
    simp only [mul_zero, zero_add, A_one]
    decide
  | succ n ih =>
    have h := A_parity_period (n := 4*(n+1)+1) (by omega)
    have he : 4*(n+1)+1-4 = 4*n+1 := by omega
    rw [he] at h
    exact h.trans ih


theorem actual_zero_iff_good4 : ∀ n, A n = 0 ↔ good4 (n+1) :=
  zero_iff_good4 A A_four_zero_cast A_four_one_cast A_four_two A_four_three

lemma nth_positive_shift (p : ℕ → Prop) (hp0 : p 0) (hi : (Set.ofPred p).Infinite) (n : ℕ) :
    Nat.nth (fun x => p (x+1)) n = Nat.nth p (n+1) - 1 := by
  classical
  let t := Nat.nth p (n+1)
  have hzero : Nat.nth p 0 = 0 := Nat.nth_zero_of_zero hp0
  have htpos : 0 < t := by
    have hh := (Nat.nth_strictMono hi) (show 0 < n+1 by omega)
    rw [hzero] at hh
    exact hh
  have htp : p t := Nat.nth_mem_of_infinite hi _
  have htc : Nat.count p t = n+1 := Nat.count_nth_of_infinite hi _
  have he : 1 + (t-1) = t := by omega
  have hc := Nat.count_add p 1 (t-1)
  rw [he, Nat.count_one, if_pos hp0, htc] at hc
  have hc' : Nat.count (fun x => p (x+1)) (t-1) = n := by
    have hc2 : n+1 = 1 + Nat.count (fun x => p (x+1)) (t-1) := by simpa [Nat.add_comm] using hc
    omega
  have hm : p ((t-1)+1) := by simpa [show t-1+1=t by omega] using htp
  have h := Nat.nth_count (p := fun x => p (x+1)) hm
  rw [hc'] at h
  exact h

lemma good4_three_mul_pow (n : ℕ) : good4 (3*4^n) := by
  induction n with
  | zero => simpa using (good4_4n_three 0).mpr good4_zero
  | succ n ih =>
    have he : 3*4^(n+1) = 4*(3*4^n) := by rw [pow_succ]; ring
    rw [he, good4_4n_zero]
    exact ih

lemma good4_infinite : (Set.ofPred good4).Infinite := by
  have hs : StrictMono (fun n : ℕ => 3*4^n) := by
    intro a b hab
    exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by decide) hab) (by decide)
  have hr : Set.range (fun n : ℕ => 3*4^n) ⊆ Set.ofPred good4 := by
    rintro _ ⟨n, rfl⟩
    exact good4_three_mul_pow n
  exact (Set.infinite_range_of_injective hs.injective).mono hr

theorem nth_good4_zero (n : ℕ) :
    Nat.nth (fun m => A m = 0) n = Nat.nth good4 (n+1) - 1 := by
  have he : (fun m => A m = 0) = (fun m => good4 (m+1)) := by
    funext m
    exact propext (actual_zero_iff_good4 m)
  rw [he]
  exact nth_positive_shift good4 good4_zero good4_infinite n

def allEven (L : List (List ℕ)) : Prop := ∀ x ∈ L, x.length % 2 = 0

lemma allEven_reverse (L : List (List ℕ)) : allEven L.reverse ↔ allEven L := by
  simp [allEven]

lemma allEven_cons (a : List ℕ) (L : List (List ℕ)) : allEven (a::L) ↔
    a.length % 2 = 0 ∧ allEven L := by
  simp [allEven]

lemma split_loop_parity (L : List ℕ) (b : ℕ) (g h : List ℕ)
    (acc acc' : List (List ℕ)) (hh : g.length % 2 = h.length % 2)
    (ha : allEven acc ↔ allEven acc') :
    allEven (List.splitBy.loop (· == ·) L b g acc) ↔
      allEven (List.splitBy.loop (· == ·) L b h acc') := by
  induction L generalizing b g h acc acc' with
  | nil =>
    simp only [List.splitBy.loop, allEven_reverse, allEven_cons, List.length_reverse, List.length_cons]
    have he : ((g.length + 1) % 2 = 0) ↔ ((h.length + 1) % 2 = 0) := by omega
    exact and_congr he ha
  | cons a L ih =>
    simp only [List.splitBy.loop]
    split
    · apply ih
      · simp only [List.length_cons]
        omega
      · exact ha
    · apply ih
      · rfl
      · simp only [allEven_cons, List.length_reverse, List.length_cons]
        have he : ((g.length+1)%2=0) ↔ ((h.length+1)%2=0) := by omega
        exact and_congr he ha

def runsEven (L : List ℕ) : Prop := allEven (L.splitBy (· == ·))

lemma runsEven_pair (a : ℕ) (L : List ℕ) : runsEven (a::a::L) ↔ runsEven L := by
  cases L with
  | nil => simp [runsEven, allEven, List.splitBy, List.splitBy.loop]
  | cons b L =>
    by_cases hab : a=b
    · subst b
      simp only [runsEven, List.splitBy, List.splitBy.loop, beq_self_eq_true]
      apply split_loop_parity
      · simp
      · rfl
    · have hab' : (a == b) = false := by simp [hab]
      simp only [runsEven, List.splitBy, List.splitBy.loop, beq_self_eq_true, hab']
      apply split_loop_parity
      · rfl
      · simp [allEven]

lemma split_loop_acc (L : List ℕ) (b : ℕ) (g : List ℕ) (acc : List (List ℕ)) :
    allEven (List.splitBy.loop (· == ·) L b g acc) → allEven acc := by
  induction L generalizing b g acc with
  | nil =>
    change allEven (((b::g).reverse::acc).reverse) → allEven acc
    rw [allEven_reverse, allEven_cons]
    exact And.right
  | cons a L ih =>
    simp only [List.splitBy.loop]
    split
    · exact ih _ _ _
    · intro h
      have hh := ih _ _ _ h
      exact (allEven_cons _ _).mp hh |>.2

lemma runsEven_diff (a b : ℕ) (L : List ℕ) (hab : a ≠ b) : ¬runsEven (a::b::L) := by
  have hab' : (a == b) = false := by simp [hab]
  simp only [runsEven, List.splitBy, List.splitBy.loop, hab']
  intro hh
  have he := split_loop_acc L b [] [[a]] hh
  simp [allEven] at he

lemma runsEven_singleton (a : ℕ) : ¬runsEven [a] := by
  simp [runsEven, allEven, List.splitBy, List.splitBy.loop]

lemma runsEven_iff (L : List ℕ) : runsEven L ↔
    ∀ r ∈ L.splitBy (· == ·), Even r.length := by
  simp [runsEven, allEven, Nat.even_iff]

def evbin (m : ℕ) : Prop := allEven ((Nat.digits 2 m).splitBy (· == ·))


lemma binary_two_digits {m : ℕ} (hm : 4 ≤ m) :
  Nat.digits 2 m = [m % 2, (m / 2) % 2] ++ Nat.digits 2 (m / 4) := by
  rw [Nat.digits_eq_cons_digits_div (by decide) (by omega : m ≠ 0),
      Nat.digits_eq_cons_digits_div (by decide) (by omega : m / 2 ≠ 0)]
  have he : m / 2 / 2 = m / 4 := by omega
  simp [he]

lemma good4_evbin_bridge
    (pair : ∀ (a : ℕ) (l : List ℕ),
      allEven ((a :: a :: l).splitBy (· == ·)) ↔ allEven (l.splitBy (· == ·)))
    (diff : ∀ (a b : ℕ) (l : List ℕ), a ≠ b →
      ¬ allEven ((a :: b :: l).splitBy (· == ·))) :
    ∀ m : ℕ, evbin m ↔ good4 m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hsmall : m < 4
    · interval_cases m <;> norm_num [evbin, good4, allEven, Nat.digits, Nat.digitsAux, List.splitBy, List.splitBy.loop]
      all_goals decide
    · have hm : 4 ≤ m := by omega
      have hzero : m ≠ 0 := by omega
      have hlt : m / 4 < m := Nat.div_lt_self (by omega) (by decide)
      have he := ih (m/4) hlt
      have hd := binary_two_digits hm
      have hm4 : m % 4 < 4 := Nat.mod_lt _ (by decide)
      rw [good4_step hzero]
      change allEven ((Nat.digits 2 m).splitBy (· == ·)) ↔ _
      rw [hd]
      interval_cases h : m % 4
      · have h1 : m % 2 = 0 := by omega
        have h2 : (m / 2) % 2 = 0 := by omega
        simp only [h1, h2, List.cons_append, List.nil_append, pair, true_or, true_and]
        exact he
      · have h1 : m % 2 = 1 := by omega
        have h2 : (m / 2) % 2 = 0 := by omega
        simpa [h1, h2] using diff 1 0 (Nat.digits 2 (m / 4)) (by decide)
      · have h1 : m % 2 = 0 := by omega
        have h2 : (m / 2) % 2 = 1 := by omega
        simpa [h1, h2] using diff 0 1 (Nat.digits 2 (m / 4)) (by decide)
      · have h1 : m % 2 = 1 := by omega
        have h2 : (m / 2) % 2 = 1 := by omega
        simp only [h1, h2, List.cons_append, List.nil_append, pair, OfNat.ofNat_ne_zero, or_true, true_and]
        exact he


theorem evenRuns_iff_good4 (m : ℕ) :
    (∀ r ∈ (Nat.digits 2 m).splitBy (· == ·), Even r.length) ↔ good4 m := by
  have h := good4_evbin_bridge runsEven_pair runsEven_diff m
  exact (runsEven_iff (Nat.digits 2 m)).symm.trans h

end OMA.A374446Proof

open OMA.A374446Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a374446.main := by
  intro n hn
  change Nat.nth (fun m => A m = 0) (n - 1) =
    Nat.nth (fun m => ∀ r ∈ (Nat.digits 2 m).splitBy (· == ·), Even r.length) n - 1
  have he : (fun m => (∀ r ∈ (Nat.digits 2 m).splitBy (· == ·), Even r.length)) = good4 := by
    funext m
    exact propext (evenRuns_iff_good4 m)
  rw [he]
  have h := nth_good4_zero (n-1)
  have hn' : n-1+1=n := by omega
  simpa [hn'] using h

