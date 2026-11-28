import OMAStatements.S_oeis_a372561

namespace OMA.S_oeis_a372561_Proof

open OMA.S_oeis_a372561

/-! ### Part 1: Basic Jacobsthal, lift, stretch, and grid identities -/

private lemma three_mul_jac_int : ∀ i : ℕ,
    3 * (jac i : ℤ) + (if i % 2 = 0 then 1 else -1) = (2 : ℤ) ^ i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    match i with
    | 0 => norm_num [jac]
    | 1 => norm_num [jac]
    | n + 2 =>
      have h1 := ih (n + 1) (by omega)
      have h2 := ih n (by omega)
      simp only [jac, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      by_cases hn : n % 2 = 0
      · have hn1 : (n + 1) % 2 ≠ 0 := by omega
        have hn2 : (n + 2) % 2 = 0 := by omega
        rw [if_pos hn] at h2
        rw [if_neg hn1, pow_succ] at h1
        rw [if_pos hn2]
        rw [pow_succ, pow_succ]
        linarith
      · have hn1 : (n + 1) % 2 = 0 := by omega
        have hn2 : (n + 2) % 2 ≠ 0 := by omega
        rw [if_neg hn] at h2
        rw [if_pos hn1, pow_succ] at h1
        rw [if_neg hn2]
        rw [pow_succ, pow_succ]
        linarith

private lemma three_dvd_four_pow_sub_one (e : ℕ) : 3 ∣ 4 ^ e - 1 := by
  induction e with
  | zero => simp
  | succ e ih =>
    obtain ⟨k, hk⟩ := ih
    have h1 : 1 ≤ 4 ^ e := Nat.one_le_pow _ _ (by omega)
    refine ⟨4 * k + 1, ?_⟩
    rw [pow_succ']
    omega

private lemma three_mul_lift_add_one (e y : ℕ) :
    3 * lift e y + 1 = 4 ^ e * (3 * y + 1) := by
  unfold lift
  have hdvd := three_dvd_four_pow_sub_one e
  have h1 : 3 * ((4 ^ e - 1) / 3) = 4 ^ e - 1 := Nat.mul_div_cancel' hdvd
  have h2 : 1 ≤ 4 ^ e := Nat.one_le_pow _ _ (by omega)
  rw [mul_add, h1]
  have h3 : 3 * (4 ^ e * y) = 4 ^ e * (3 * y) := by ring
  rw [h3, mul_add, mul_one]
  omega

private lemma lift_zero (y : ℕ) : lift 0 y = y := by
  simp [lift]

private lemma lift_add (e₁ e₂ y : ℕ) : lift e₁ (lift e₂ y) = lift (e₁ + e₂) y := by
  have h1 := three_mul_lift_add_one e₁ (lift e₂ y)
  have h2 := three_mul_lift_add_one e₂ y
  have h3 := three_mul_lift_add_one (e₁ + e₂) y
  rw [pow_add] at h3
  have : 3 * lift e₁ (lift e₂ y) + 1 = 3 * lift (e₁ + e₂) y + 1 := by
    rw [h1, h2, h3]; ring
  omega

private lemma lift_one_eq_jac (e : ℕ) : lift e 1 = jac (2 * e + 2) := by
  have h1 := three_mul_lift_add_one e 1
  have h2 := three_mul_jac_int (2 * e + 2)
  have heven : (2 * e + 2) % 2 = 0 := by omega
  rw [if_pos heven] at h2
  have hpow : (2 : ℤ) ^ (2 * e + 2) = 4 ^ e * 4 := by
    rw [pow_add, pow_mul]; norm_num
  rw [hpow] at h2
  have h1z : (3 * (lift e 1 : ℤ) + 1) = (4 : ℤ) ^ e * 4 := by exact_mod_cast h1
  omega

private lemma stretch_eq_lift (n : ℕ) : stretch n = lift (valuation n) (reduced n) := by
  unfold stretch lift reduced
  have hdvd : 2 ^ valuation n ∣ 3 * n + 1 := padicValNat_dvd_iff_le (by omega) |>.mpr le_rfl
  have h4 : 4 ^ valuation n = 2 ^ valuation n * 2 ^ valuation n := by
    rw [← mul_pow]; norm_num
  have hmul : 4 ^ valuation n * ((3 * n + 1) / 2 ^ valuation n) = (3 * n + 1) * 2 ^ valuation n := by
    rw [h4, mul_assoc, mul_comm (2 ^ valuation n) ((3 * n + 1) / 2 ^ valuation n),
      Nat.div_mul_cancel hdvd, mul_comm]
  rw [hmul]

private lemma valuation_lift (e y : ℕ) : valuation (lift e y) = 2 * e + valuation y := by
  unfold valuation
  rw [three_mul_lift_add_one]
  have h4 : (4 : ℕ) ^ e = 2 ^ (2 * e) := by rw [pow_mul]; norm_num
  rw [h4]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow]

private lemma reduced_lift (e y : ℕ) : reduced (lift e y) = reduced y := by
  unfold reduced
  rw [three_mul_lift_add_one, valuation_lift]
  have h4 : (4 : ℕ) ^ e = 2 ^ (2 * e) := by rw [pow_mul]; norm_num
  rw [h4, pow_add, Nat.mul_div_mul_left _ _ (by positivity)]

private lemma grid_eq_lift : ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    ∃ e : ℕ, grid n k = lift e ((reduced^[n + k - 2]) 27) ∧
      (2 ≤ n → valuation ((reduced^[n + k - 3]) 27) ≤ e) := by
  intro n
  induction n with
  | zero => intro _ hn _; omega
  | succ n ih =>
    intro k _ hk
    rcases eq_or_lt_of_le (Nat.zero_le n) with rfl | hn_pos
    · refine ⟨0, ?_, by omega⟩
      have hidx : 0 + 1 + k - 2 = k - 1 := by omega
      simp [grid, lift_zero, hidx]
    · obtain ⟨e, he_eq, _⟩ := ih k hn_pos hk
      have hgrid_step : grid (n + 1) k = stretch (grid n k) := by
        unfold grid
        have hsub : n + 1 - 1 = (n - 1) + 1 := by omega
        rw [hsub, Function.iterate_succ_apply']
      rw [hgrid_step, he_eq, stretch_eq_lift, valuation_lift, reduced_lift]
      refine ⟨2 * e + valuation ((reduced^[n + k - 2]) 27), ?_, ?_⟩
      · have hidx : n + 1 + k - 2 = (n + k - 2) + 1 := by omega
        rw [hidx, Function.iterate_succ_apply']
      · intro _
        have hidx : n + 1 + k - 3 = n + k - 2 := by omega
        rw [hidx]
        omega

/-! ### Part 2: Binary popcount and minimum-exponent lemma -/

private def popcountAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else n % 2 + popcountAux fuel (n / 2)

private lemma popcountAux_eq : ∀ f1 f2 n, n ≤ f1 → n ≤ f2 → popcountAux f1 n = popcountAux f2 n := by
  intro f1
  induction f1 with
  | zero =>
    intro f2 n h1 h2
    have hn0 : n = 0 := by omega
    subst hn0
    cases f2 <;> rfl
  | succ f1 ih =>
    intro f2 n h1 h2
    cases f2 with
    | zero =>
      have hn0 : n = 0 := by omega
      subst hn0; rfl
    | succ f2 =>
      unfold popcountAux
      split_ifs with hn0
      · rfl
      · congr 1
        exact ih f2 (n / 2) (by omega) (by omega)

private def popcount (n : ℕ) : ℕ := popcountAux n n

private lemma popcount_zero : popcount 0 = 0 := rfl

private lemma popcount_eq (n : ℕ) (hn : n ≠ 0) :
    popcount n = n % 2 + popcount (n / 2) := by
  unfold popcount
  cases n with
  | zero => exact (hn rfl).elim
  | succ m =>
    conv_lhs => unfold popcountAux
    rw [if_neg (Nat.succ_ne_zero m)]
    congr 1
    exact popcountAux_eq m ((m + 1) / 2) ((m + 1) / 2) (by omega) le_rfl

private lemma popcount_two_mul (n : ℕ) : popcount (2 * n) = popcount n := by
  by_cases h : n = 0
  · subst h; simp [popcount]
  · rw [popcount_eq (2 * n) (by omega), Nat.mul_mod_right, zero_add, Nat.mul_div_right _ (by omega)]

private lemma popcount_two_mul_add_one (n : ℕ) : popcount (2 * n + 1) = 1 + popcount n := by
  rw [popcount_eq (2 * n + 1) (by omega)]
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [h1, h2]

private lemma popcount_pow_two (p : ℕ) : popcount (2 ^ p) = 1 := by
  induction p with
  | zero => rw [pow_zero, popcount_eq 1 (by omega)]; simp [popcount_zero]
  | succ p ih => rw [pow_succ', popcount_two_mul, ih]

private lemma popcount_add_le : ∀ a b : ℕ, popcount (a + b) ≤ popcount a + popcount b := by
  intro a b
  have hgen : ∀ s a b : ℕ, a + b = s → popcount (a + b) ≤ popcount a + popcount b := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro a b hab
      by_cases ha : a = 0
      · subst ha; simp [popcount_zero]
      · by_cases hb : b = 0
        · subst hb; simp [popcount_zero]
        · have ha_eq : a = 2 * (a / 2) + a % 2 := (Nat.div_add_mod a 2).symm
          have hb_eq : b = 2 * (b / 2) + b % 2 := (Nat.div_add_mod b 2).symm
          have hpa := popcount_eq a ha
          have hpb := popcount_eq b hb
          have hlt1 : a / 2 + b / 2 < s := by omega
          have hih1 := ih (a / 2 + b / 2) hlt1 (a / 2) (b / 2) rfl
          rcases Nat.mod_two_eq_zero_or_one a with ha0 | ha1 <;>
          rcases Nat.mod_two_eq_zero_or_one b with hb0 | hb1
          · have hsum : a + b = 2 * (a / 2 + b / 2) := by omega
            rw [hsum, popcount_two_mul, hpa, hpb, ha0, hb0]; omega
          · have hsum : a + b = 2 * (a / 2 + b / 2) + 1 := by omega
            rw [hsum, popcount_two_mul_add_one, hpa, hpb, ha0, hb1]; omega
          · have hsum : a + b = 2 * (a / 2 + b / 2) + 1 := by omega
            rw [hsum, popcount_two_mul_add_one, hpa, hpb, ha1, hb0]; omega
          · have hsum : a + b = 2 * ((a / 2 + 1) + b / 2) := by omega
            have hlt2 : (a / 2 + 1) + b / 2 < s := by omega
            have hih2 := ih ((a / 2 + 1) + b / 2) hlt2 (a / 2 + 1) (b / 2) rfl
            have hstep : popcount (a / 2 + 1) ≤ popcount (a / 2) + 1 := by
              have hlt3 : a / 2 + 1 < s := by omega
              have h3 := ih (a / 2 + 1) hlt3 (a / 2) 1 rfl
              have hp1 : popcount 1 = 1 := by rw [popcount_eq 1 (by omega)]; simp [popcount_zero]
              omega
            rw [hsum, popcount_two_mul, hpa, hpb, ha1, hb1]; omega
  exact hgen (a + b) a b rfl

private lemma popcount_sum_pow_two_le (s : Multiset ℕ) :
    popcount (s.map (2 ^ ·)).sum ≤ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp [popcount_zero]
  | cons p s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    have h1 := popcount_add_le (2 ^ p) (s.map (2 ^ ·)).sum
    rw [popcount_pow_two] at h1
    omega

private lemma popcount_mod_le (n k : ℕ) : popcount (n % 2 ^ k) ≤ popcount n := by
  induction k generalizing n with
  | zero => simp [Nat.mod_one, popcount_zero]
  | succ k ih =>
    by_cases hn : n = 0
    · subst hn; simp [popcount_zero]
    · have h1 : n % 2 ^ (k + 1) = 2 * (n / 2 % 2 ^ k) + n % 2 := by
        rw [pow_succ']
        have h2 := Nat.mod_mul_right_div_self n 2 (2 ^ k)
        have h3 := Nat.div_add_mod (n % (2 * 2 ^ k)) 2
        have h4 : n % (2 * 2 ^ k) % 2 = n % 2 := Nat.mod_mod_of_dvd n (dvd_mul_right 2 _)
        rw [h4, h2] at h3
        omega
      rw [h1]
      rcases Nat.mod_two_eq_zero_or_one n with hm | hm
      · rw [hm, add_zero, popcount_two_mul, popcount_eq n hn, hm, zero_add]
        exact ih (n / 2)
      · rw [hm, popcount_two_mul_add_one, popcount_eq n hn, hm]
        have := ih (n / 2)
        omega

private lemma min_exp_ge_of_pow_two_dvd :
    ∀ (k : ℕ) (s : Multiset ℕ) (K : ℕ), s.card = k → 1 ≤ k →
      2 ^ K ∣ (s.map (2 ^ ·)).sum → ∀ p ∈ s, K ≤ p + (k - 1) := by
  intro k
  induction k with
  | zero => intro _ _ _ h1; omega
  | succ k ih =>
    intro s K hcard _ hdvd p hp
    rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hk_pos
    · have hs1 : s = {p} := by
        obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hp
        rw [ht, Multiset.card_cons] at hcard
        have ht0 : t = 0 := Multiset.card_eq_zero.mp (by omega)
        rw [ht, ht0]; rfl
      rw [hs1, Multiset.map_singleton, Multiset.sum_singleton] at hdvd
      have hle := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd
      omega
    · -- Find the minimum element p0 of s
      have hne : s ≠ 0 := by intro h0; rw [h0] at hcard; simp at hcard
      let p0 := s.toFinset.min' (by simpa [Multiset.toFinset_nonempty] using hne)
      have hp0_mem : p0 ∈ s := Multiset.mem_toFinset.mp (Finset.min'_mem _ _)
      have hp0_le : ∀ q ∈ s, p0 ≤ q := fun q hq =>
        Finset.min'_le _ q (Multiset.mem_toFinset.mpr hq)
      suffices hmin : K ≤ p0 + k by
        have := hp0_le p hp; omega
      by_cases hK : K ≤ p0
      · omega
      · -- Since p0 < K, 2^(p0 + 1) | 2^K | sum, so p0 must appear at least twice in s!
        have hdvd1 : 2 ^ (p0 + 1) ∣ (s.map (2 ^ ·)).sum :=
          dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hdvd
        obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hp0_mem
        have hp0_in_t : p0 ∈ t := by
          by_contra hnot
          have ht_dvd : 2 ^ (p0 + 1) ∣ (t.map (2 ^ ·)).sum := by
            have hall : ∀ q ∈ t, 2 ^ (p0 + 1) ∣ 2 ^ q := by
              intro q hq
              have hq_ge : p0 ≤ q := hp0_le q (by rw [ht]; exact Multiset.mem_cons_of_mem hq)
              have hq_ne : q ≠ p0 := fun h => hnot (h ▸ hq)
              exact Nat.pow_dvd_pow 2 (by omega)
            have hsum_dvd : ∀ u : Multiset ℕ, (∀ q ∈ u, 2 ^ (p0 + 1) ∣ 2 ^ q) →
                2 ^ (p0 + 1) ∣ (u.map (2 ^ ·)).sum := by
              intro u
              induction u using Multiset.induction_on with
              | empty => intro _; simp
              | cons a u ihu =>
                intro h
                rw [Multiset.map_cons, Multiset.sum_cons]
                exact dvd_add (h a (by simp)) (ihu (fun q hq => h q (Multiset.mem_cons_of_mem hq)))
            exact hsum_dvd t hall
          rw [ht, Multiset.map_cons, Multiset.sum_cons] at hdvd1
          have hp0_dvd : 2 ^ (p0 + 1) ∣ 2 ^ p0 := (Nat.dvd_add_left ht_dvd).mp hdvd1
          have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hp0_dvd
          omega
        obtain ⟨u, hu⟩ := Multiset.exists_cons_of_mem hp0_in_t
        let s' := (p0 + 1) ::ₘ u
        have hs'_card : s'.card = k := by
          rw [ht, hu, Multiset.card_cons, Multiset.card_cons] at hcard
          simp only [s', Multiset.card_cons]
          omega
        have hs'_sum : (s'.map (2 ^ ·)).sum = (s.map (2 ^ ·)).sum := by
          rw [ht, hu]
          simp only [s', Multiset.map_cons, Multiset.sum_cons, pow_succ']
          ring
        have hdvd' : 2 ^ K ∣ (s'.map (2 ^ ·)).sum := by rw [hs'_sum]; exact hdvd
        have hih := ih s' K hs'_card hk_pos hdvd' (p0 + 1) (Multiset.mem_cons_self _ _)
        omega

/-! ### Part 3: Representation algebra, lift-step lower bound, and executable `canEO` -/

private lemma repr_sum_pow_two {x : ℕ} {m : Multiset ℕ} (hrep : represents x m) :
    let ec := (m.filter (fun i => i % 2 = 0)).card
    let oc := (m.filter (fun i => i % 2 ≠ 0)).card
    ec + oc = m.card ∧
    3 * (x : ℤ) + (ec : ℤ) - (oc : ℤ) = (((m.map (fun i : ℕ => (2 : ℕ) ^ i)).sum : ℕ) : ℤ) := by
  intro ec oc
  have hcard : ec + oc = m.card := by
    have h1 := Multiset.filter_add_not (fun i : ℕ => i % 2 = 0) m
    have h2 := congrArg Multiset.card h1
    simpa [ec, oc, Multiset.card_add] using h2
  refine ⟨hcard, ?_⟩
  rw [← hrep.2]
  unfold value
  clear hrep hcard
  dsimp only [ec, oc]
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
    have ha := three_mul_jac_int a
    by_cases he : a % 2 = 0
    · rw [if_pos he] at ha
      have hne : ¬ (a % 2 ≠ 0) := by omega
      rw [Multiset.filter_cons_of_pos (p := fun i => i % 2 = 0) s he,
        Multiset.filter_cons_of_neg (p := fun i => i % 2 ≠ 0) s hne]
      simp only [Multiset.card_cons, Nat.cast_add, Nat.cast_one]
      linarith
    · rw [if_neg he] at ha
      have hne : a % 2 ≠ 0 := he
      rw [Multiset.filter_cons_of_neg (p := fun i => i % 2 = 0) s he,
        Multiset.filter_cons_of_pos (p := fun i => i % 2 ≠ 0) s hne]
      simp only [Multiset.card_cons, Nat.cast_add, Nat.cast_one]
      linarith

private lemma represents_shift_up {x : ℕ} {m : Multiset ℕ} (hrep : represents x m)
    (heo : ((m.filter (fun i => i % 2 = 0)).card : ℤ) -
           ((m.filter (fun i => i % 2 ≠ 0)).card : ℤ) = 1) (d : ℕ) :
    represents (lift d x) (m.map (· + 2 * d)) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    rcases Multiset.mem_map.mp hi with ⟨j, hj, rfl⟩
    have := hrep.1 j hj; omega
  · have hsum := (repr_sum_pow_two hrep).2
    have hm' : represents (value (m.map (· + 2 * d))) (m.map (· + 2 * d)) :=
      ⟨fun i hi => by rcases Multiset.mem_map.mp hi with ⟨j, hj, rfl⟩; have := hrep.1 j hj; omega, rfl⟩
    have hsum' := (repr_sum_pow_two hm').2
    have hec_eq : ((m.map (· + 2 * d)).filter (fun i => i % 2 = 0)).card =
        (m.filter (fun i => i % 2 = 0)).card := by
      rw [Multiset.filter_map, Multiset.card_map]
      congr 1; apply Multiset.filter_congr; intro j _; simp
    have hoc_eq : ((m.map (· + 2 * d)).filter (fun i => i % 2 ≠ 0)).card =
        (m.filter (fun i => i % 2 ≠ 0)).card := by
      rw [Multiset.filter_map, Multiset.card_map]
      congr 1; apply Multiset.filter_congr; intro j _; simp
    have hpow_sum : ((m.map (· + 2 * d)).map (fun i : ℕ => (2 : ℕ) ^ i)).sum =
        4 ^ d * (m.map (fun i : ℕ => (2 : ℕ) ^ i)).sum := by
      rw [Multiset.map_map]
      have h4 : (4 : ℕ) ^ d = 2 ^ (2 * d) := by rw [pow_mul]; norm_num
      rw [h4]
      clear hsum hsum' hm' hec_eq hoc_eq hrep heo
      induction m using Multiset.induction_on with
      | empty => simp
      | cons a s ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons, Function.comp_def, pow_add] at ih ⊢
        rw [ih]; ring
    rw [hec_eq, hoc_eq, hpow_sum] at hsum'
    have hlift : (3 * (lift d x : ℤ) + 1) = (4 : ℤ) ^ d * (3 * (x : ℤ) + 1) := by
      exact_mod_cast three_mul_lift_add_one d x
    have hpow_cast : (((4 ^ d * (m.map (fun i : ℕ => (2 : ℕ) ^ i)).sum : ℕ) : ℤ)) =
        (4 : ℤ) ^ d * (((m.map (fun i : ℕ => (2 : ℕ) ^ i)).sum : ℕ) : ℤ) := by push_cast; rfl
    rw [hpow_cast] at hsum'
    have hval : 3 * (value (m.map (· + 2 * d)) : ℤ) + 1 = 3 * (lift d x : ℤ) + 1 := by
      nlinarith
    omega

private lemma minCoins_le_of_represents {x : ℕ} {m : Multiset ℕ} (hrep : represents x m) :
    minCoins x ≤ m.card :=
  Nat.sInf_le ⟨m, hrep, rfl⟩

private lemma le_minCoins_of_forall {x R : ℕ}
    (h : ∀ m : Multiset ℕ, represents x m → R ≤ m.card) :
    R ≤ minCoins x := by
  have hne : {r : ℕ | ∃ m : Multiset ℕ, represents x m ∧ m.card = r}.Nonempty := by
    refine ⟨x, Multiset.replicate x 2, ⟨fun i hi => by
      have := Multiset.eq_of_mem_replicate hi; omega, ?_⟩, by simp⟩
    simp [value, jac]
  exact le_csInf hne (fun r ⟨m, hm, hr⟩ => hr ▸ h m hm)

private lemma minCoins_lift_step {y e R : ℕ} (hR : R ≤ 9) (he : 6 ≤ e)
    (hlow : ∀ m : Multiset ℕ, represents (lift e y) m → R ≤ m.card) :
    ∀ m : Multiset ℕ, represents (lift (e + 1) y) m → R ≤ m.card := by
  intro m hrep
  by_contra hlt
  push Not at hlt
  have hrcard : m.card ≤ 8 := by omega
  obtain ⟨hcard_eq, hsum_z⟩ := repr_sum_pow_two hrep
  let ec := (m.filter (fun i => i % 2 = 0)).card
  let oc := (m.filter (fun i => i % 2 ≠ 0)).card
  have hlift_z : (3 * (lift (e + 1) y : ℤ) + 1) = (4 : ℤ) ^ (e + 1) * (3 * (y : ℤ) + 1) := by
    exact_mod_cast three_mul_lift_add_one (e + 1) y
  let s := m.map (· - 2)
  have hs_card : s.card = m.card := Multiset.card_map _ _
  have h4s : (m.map (fun i : ℕ => (2 : ℕ) ^ i)).sum = 4 * (s.map (fun i : ℕ => (2 : ℕ) ^ i)).sum := by
    have hall : ∀ i ∈ m, 2 ≤ i := hrep.1
    dsimp only [s]
    rw [Multiset.map_map]
    clear hrep hsum_z hcard_eq hs_card hlt hrcard ec oc
    revert hall
    induction m using Multiset.induction_on with
    | empty => intro _; simp
    | cons a t ih =>
      intro hall
      simp only [Multiset.map_cons, Multiset.sum_cons, Function.comp_def] at ih ⊢
      have ha : 2 ≤ a := hall a (by simp)
      have ha_pow : 2 ^ a = 4 * 2 ^ (a - 2) := by
        conv_lhs => rw [show a = (a - 2) + 2 by omega, pow_add]
        ring
      rw [ha_pow, ih (fun i hi => hall i (Multiset.mem_cons_of_mem hi))]
      ring
  have h4s_z : (((m.map (fun i : ℕ => (2 : ℕ) ^ i)).sum : ℕ) : ℤ) =
      4 * (((s.map (fun i : ℕ => (2 : ℕ) ^ i)).sum : ℕ) : ℤ) := by
    exact_mod_cast h4s
  have hN_z : 4 * (((s.map (fun i : ℕ => (2 : ℕ) ^ i)).sum : ℕ) : ℤ) =
      4 * ((4 ^ e * (3 * y + 1) : ℕ) : ℤ) + ((ec : ℤ) - (oc : ℤ) - 1) := by
    have hpow : (4 : ℤ) ^ (e + 1) = 4 * (4 : ℤ) ^ e := by rw [pow_succ']
    have hrhs : ((4 ^ e * (3 * y + 1) : ℕ) : ℤ) = (4 : ℤ) ^ e * (3 * (y : ℤ) + 1) := by
      push_cast; rfl
    rw [hpow, mul_assoc] at hlift_z
    rw [hrhs]
    linarith
  have hdvd4 : (4 : ℤ) ∣ ((ec : ℤ) - (oc : ℤ) - 1) := by
    refine ⟨(((s.map (fun i : ℕ => (2 : ℕ) ^ i)).sum : ℕ) : ℤ) - ((4 ^ e * (3 * y + 1) : ℕ) : ℤ), ?_⟩
    linarith
  obtain ⟨δ, hδ⟩ := hdvd4
  have hδ_cases : δ = -2 ∨ δ = -1 ∨ δ = 0 ∨ δ = 1 := by omega
  have hN_eq_z : (((s.map (fun i : ℕ => (2 : ℕ) ^ i)).sum : ℕ) : ℤ) =
      ((4 ^ e * (3 * y + 1) : ℕ) : ℤ) + δ := by linarith
  have h4e_big : 1024 ≤ 4 ^ e := by
    calc 1024 = 4 ^ 5 := by norm_num
      _ ≤ 4 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hM_ge : 1024 ≤ 4 ^ e * (3 * y + 1) := by nlinarith
  rcases hδ_cases with rfl | rfl | rfl | rfl
  · -- δ = -2: popcount(N % 1024) = popcount(1022) = 9 > 8 >= s.card
    have hN_nat : (s.map (2 ^ ·)).sum = 4 ^ e * (3 * y + 1) - 2 := by omega
    have hmod : (s.map (2 ^ ·)).sum % 2 ^ 10 = 1022 := by
      have hdvd10 : 2 ^ 10 ∣ 4 ^ e := by
        rw [show (4 : ℕ) ^ e = 2 ^ (2 * e) by rw [pow_mul]; norm_num]
        exact Nat.pow_dvd_pow 2 (by omega)
      obtain ⟨q, hq⟩ := hdvd10
      have hq_pos : 1 ≤ q * (3 * y + 1) := by
        have : 1024 * (q * (3 * y + 1)) = 4 ^ e * (3 * y + 1) := by
          rw [hq, show (2 : ℕ) ^ 10 = 1024 by norm_num]; ring
        omega
      have h1 : (s.map (2 ^ ·)).sum = 2 ^ 10 * (q * (3 * y + 1) - 1) + 1022 := by
        rw [hN_nat, hq]
        have : 2 ^ 10 = 1024 := by norm_num
        rw [this]
        have : 1024 * q * (3 * y + 1) = 1024 * (q * (3 * y + 1)) := by ring
        rw [this, Nat.mul_sub_left_distrib]
        omega
      rw [h1, Nat.mul_add_mod]
      norm_num
    have hpop_ge : 9 ≤ popcount (s.map (2 ^ ·)).sum := by
      have h1 := popcount_mod_le (s.map (2 ^ ·)).sum 10
      rw [hmod] at h1
      have hp : popcount 1022 = 9 := by decide
      omega
    have hpop_le := popcount_sum_pow_two_le s
    omega
  · -- δ = -1: popcount(N % 1024) = popcount(1023) = 10 > 8 >= s.card
    have hN_nat : (s.map (2 ^ ·)).sum = 4 ^ e * (3 * y + 1) - 1 := by omega
    have hmod : (s.map (2 ^ ·)).sum % 2 ^ 10 = 1023 := by
      have hdvd10 : 2 ^ 10 ∣ 4 ^ e := by
        rw [show (4 : ℕ) ^ e = 2 ^ (2 * e) by rw [pow_mul]; norm_num]
        exact Nat.pow_dvd_pow 2 (by omega)
      obtain ⟨q, hq⟩ := hdvd10
      have hq_pos : 1 ≤ q * (3 * y + 1) := by
        have : 1024 * (q * (3 * y + 1)) = 4 ^ e * (3 * y + 1) := by
          rw [hq, show (2 : ℕ) ^ 10 = 1024 by norm_num]; ring
        omega
      have h1 : (s.map (2 ^ ·)).sum = 2 ^ 10 * (q * (3 * y + 1) - 1) + 1023 := by
        rw [hN_nat, hq]
        have : 2 ^ 10 = 1024 := by norm_num
        rw [this]
        have : 1024 * q * (3 * y + 1) = 1024 * (q * (3 * y + 1)) := by ring
        rw [this, Nat.mul_sub_left_distrib]
        omega
      rw [h1, Nat.mul_add_mod]
      norm_num
    have hpop_ge : 10 ≤ popcount (s.map (2 ^ ·)).sum := by
      have h1 := popcount_mod_le (s.map (2 ^ ·)).sum 10
      rw [hmod] at h1
      have hp : popcount 1023 = 10 := by decide
      omega
    have hpop_le := popcount_sum_pow_two_le s
    omega
  · -- δ = 0: every coin in m has i >= 4, so shifting down by 2 gives a representation of lift e y!
    have hN_nat : (s.map (2 ^ ·)).sum = 4 ^ e * (3 * y + 1) := by omega
    have hs_pos : 1 ≤ s.card := by
      by_contra h0; push Not at h0
      have hs0 : s = 0 := Multiset.card_eq_zero.mp (by omega)
      rw [hs0] at hN_nat; simp at hN_nat
    have hdvd2e : 2 ^ (2 * e) ∣ (s.map (2 ^ ·)).sum := by
      rw [hN_nat, show (4 : ℕ) ^ e = 2 ^ (2 * e) by rw [pow_mul]; norm_num]
      exact dvd_mul_right _ _
    have hall_ge4 : ∀ i ∈ m, 4 ≤ i := by
      intro i hi
      have hp : i - 2 ∈ s := Multiset.mem_map_of_mem _ hi
      have hmin := min_exp_ge_of_pow_two_dvd s.card s (2 * e) rfl hs_pos hdvd2e (i - 2) hp
      have hi2 := hrep.1 i hi
      omega
    let m' := m.map (· - 2)
    have hm'_rep : represents (lift e y) m' := by
      refine ⟨fun j hj => by rcases Multiset.mem_map.mp hj with ⟨i, hi, rfl⟩; have := hall_ge4 i hi; omega, ?_⟩
      have hm'_self : represents (value m') m' :=
        ⟨fun j hj => by rcases Multiset.mem_map.mp hj with ⟨i, hi, rfl⟩; have := hall_ge4 i hi; omega, rfl⟩
      have hsum' := (repr_sum_pow_two hm'_self).2
      have hec' : (m'.filter (fun i => i % 2 = 0)).card = ec := by
        dsimp [m', ec]; rw [Multiset.filter_map, Multiset.card_map]
        congr 1; apply Multiset.filter_congr; intro i hi
        have := hall_ge4 i hi; simp; omega
      have hoc' : (m'.filter (fun i => i % 2 ≠ 0)).card = oc := by
        dsimp [m', oc]; rw [Multiset.filter_map, Multiset.card_map]
        congr 1; apply Multiset.filter_congr; intro i hi
        have := hall_ge4 i hi; simp; omega
      rw [hec', hoc'] at hsum'
      have hpow' : (m'.map (fun i : ℕ => (2 : ℕ) ^ i)).sum = 4 ^ e * (3 * y + 1) := hN_nat
      rw [hpow'] at hsum'
      have hle_y : (3 * (lift e y : ℤ) + 1) = ((4 ^ e * (3 * y + 1) : ℕ) : ℤ) := by
        exact_mod_cast three_mul_lift_add_one e y
      omega
    have := hlow m' hm'_rep
    have hm'_card : m'.card = m.card := Multiset.card_map _ _
    omega
  · -- δ = 1: N = 4^e * (3*y + 1) + 1 is odd, so 2 ∈ m; keep one 2 and shift the rest down by 2!
    have hN_nat : (s.map (2 ^ ·)).sum = 4 ^ e * (3 * y + 1) + 1 := by exact_mod_cast hN_eq_z
    have h0_mem : 0 ∈ s := by
      by_contra hnot
      have heven : 2 ∣ (s.map (2 ^ ·)).sum := by
        have hall : ∀ p ∈ s, 2 ∣ 2 ^ p := fun p hp =>
          dvd_pow_self 2 (fun h => hnot (h ▸ hp))
        clear hN_nat hnot
        revert hall
        induction s using Multiset.induction_on with
        | empty => intro _; simp
        | cons a t iht =>
          intro hall
          rw [Multiset.map_cons, Multiset.sum_cons]
          exact dvd_add (hall a (by simp)) (iht (fun p hp => hall p (Multiset.mem_cons_of_mem hp)))
      rw [hN_nat] at heven
      have h2_4e : 2 ∣ 4 ^ e * (3 * y + 1) := by
        rw [show (4 : ℕ) ^ e = 2 ^ (2 * e) by rw [pow_mul]; norm_num]
        exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _
      have : 2 ∣ 1 := (Nat.dvd_add_right h2_4e).mp heven
      omega
    have h2_mem : 2 ∈ m := by
      rcases Multiset.mem_map.mp h0_mem with ⟨i, hi, hi0⟩
      have := hrep.1 i hi
      have : i = 2 := by omega
      exact this ▸ hi
    obtain ⟨m1, hm1⟩ := Multiset.exists_cons_of_mem h2_mem
    let s1 := m1.map (· - 2)
    have hs1_sum : (s1.map (2 ^ ·)).sum = 4 ^ e * (3 * y + 1) := by
      have hs_eq : s = 0 ::ₘ s1 := by dsimp [s, s1]; rw [hm1, Multiset.map_cons]
      rw [hs_eq, Multiset.map_cons, Multiset.sum_cons, pow_zero] at hN_nat
      omega
    have hs1_pos : 1 ≤ s1.card := by
      by_contra h0; push Not at h0
      have hs0 : s1 = 0 := Multiset.card_eq_zero.mp (by omega)
      rw [hs0] at hs1_sum; simp at hs1_sum
    have hs1_card : s1.card = m.card - 1 := by
      rw [hm1, Multiset.card_cons] at hs_card ⊢
      simp [s1]
    have hdvd2e : 2 ^ (2 * e) ∣ (s1.map (2 ^ ·)).sum := by
      rw [hs1_sum, show (4 : ℕ) ^ e = 2 ^ (2 * e) by rw [pow_mul]; norm_num]
      exact dvd_mul_right _ _
    have hall1_ge4 : ∀ i ∈ m1, 4 ≤ i := by
      intro i hi
      have hp : i - 2 ∈ s1 := Multiset.mem_map_of_mem _ hi
      have hmin := min_exp_ge_of_pow_two_dvd s1.card s1 (2 * e) rfl hs1_pos hdvd2e (i - 2) hp
      have hi2 := hrep.1 i (by rw [hm1]; exact Multiset.mem_cons_of_mem hi)
      omega
    let m' := 2 ::ₘ m1.map (· - 2)
    have hm'_rep : represents (lift e y) m' := by
      refine ⟨fun j hj => ?_, ?_⟩
      · rcases Multiset.mem_cons.mp hj with rfl | hj1
        · omega
        · rcases Multiset.mem_map.mp hj1 with ⟨i, hi, rfl⟩; have := hall1_ge4 i hi; omega
      · have hm'_self : represents (value m') m' :=
          ⟨fun j hj => by
            rcases Multiset.mem_cons.mp hj with rfl | hj1
            · omega
            · rcases Multiset.mem_map.mp hj1 with ⟨i, hi, rfl⟩; have := hall1_ge4 i hi; omega, rfl⟩
        have hsum' := (repr_sum_pow_two hm'_self).2
        have hec' : (m'.filter (fun i => i % 2 = 0)).card = ec := by
          dsimp [m', ec]; rw [hm1, Multiset.filter_cons_of_pos _ (by decide),
            Multiset.filter_cons_of_pos _ (by decide), Multiset.card_cons, Multiset.card_cons,
            Multiset.filter_map, Multiset.card_map]
          congr 2; apply Multiset.filter_congr; intro i hi
          have := hall1_ge4 i hi; simp; omega
        have hoc' : (m'.filter (fun i => i % 2 ≠ 0)).card = oc := by
          dsimp [m', oc]; rw [hm1, Multiset.filter_cons_of_neg _ (by decide),
            Multiset.filter_cons_of_neg _ (by decide), Multiset.filter_map, Multiset.card_map]
          congr 1; apply Multiset.filter_congr; intro i hi
          have := hall1_ge4 i hi; simp; omega
        rw [hec', hoc'] at hsum'
        have hpow' : (m'.map (fun i : ℕ => (2 : ℕ) ^ i)).sum = 4 + 4 ^ e * (3 * y + 1) := by
          dsimp [m']
          rw [Multiset.map_cons, Multiset.sum_cons, hs1_sum]
          norm_num
        rw [hpow', Nat.cast_add] at hsum'
        have hle_y : (3 * (lift e y : ℤ) + 1) = ((4 ^ e * (3 * y + 1) : ℕ) : ℤ) := by
          exact_mod_cast three_mul_lift_add_one e y
        omega
    have := hlow m' hm'_rep
    have hm'_card : m'.card = m.card := by
      dsimp [m']; rw [hm1, Multiset.card_cons, Multiset.card_cons, Multiset.card_map]
    omega

/-! ### Part 4: Executable `canEO` lower-bound verifier for `e ≤ 6` -/

private def anyRange (hi : ℕ) (P : ℕ → Bool) : Bool :=
  let rec go : ℕ → ℕ → Bool
    | 0, _ => false
    | fuel + 1, cur => if P cur then true else go fuel (cur + 1)
  go (hi + 1) 0

private lemma anyRange_eq_true {hi : ℕ} {P : ℕ → Bool} {x : ℕ} (hx : x ≤ hi) (hP : P x = true) :
    anyRange hi P = true := by
  have hgo : ∀ fuel cur, cur ≤ x → x < cur + fuel → anyRange.go P fuel cur = true := by
    intro fuel
    induction fuel with
    | zero => intro cur h1 h2; omega
    | succ fuel ih =>
      intro cur h1 h2
      unfold anyRange.go
      split_ifs with hc
      · rfl
      · rcases eq_or_lt_of_le h1 with rfl | hlt
        · exact (hc hP).elim
        · exact ih (cur + 1) (by omega) (by omega)
  exact hgo (hi + 1) 0 (Nat.zero_le x) (by omega)

private def canEOAux : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => false
  | fuel + 1, n, er, or_ =>
    if n = 0 then (er == 0) && (or_ == 0)
    else if er + or_ == 0 then false
    else if er + or_ < popcount n then false
    else if n < er + 2 * or_ then false
    else
      anyRange er (fun a0 =>
        anyRange or_ (fun b0 =>
          let s := a0 + 2 * b0
          if s ≤ n && (n - s) % 4 == 0 then
            canEOAux fuel ((n - s) / 4) (er - a0) (or_ - b0)
          else false))

private def canEO (n er or_ : ℕ) : Bool := canEOAux (n + 1) n er or_

private lemma canEOAux_of_multisets :
    ∀ (fuel n : ℕ) (se so : Multiset ℕ),
      n < fuel →
      (se.map (4 ^ ·)).sum + 2 * (so.map (4 ^ ·)).sum = n →
      canEOAux fuel n se.card so.card = true := by
  intro fuel
  induction fuel with
  | zero => intro n _ _ hlt; omega
  | succ fuel ih =>
    intro n se so hlt hsum
    unfold canEOAux
    by_cases hn0 : n = 0
    · rw [if_pos hn0]
      have hse0 : se = 0 := by
        by_contra hne
        obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
        obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem ha
        rw [ht, Multiset.map_cons, Multiset.sum_cons] at hsum
        have : 1 ≤ 4 ^ a := Nat.one_le_pow _ _ (by omega)
        omega
      have hso0 : so = 0 := by
        by_contra hne
        obtain ⟨b, hb⟩ := Multiset.exists_mem_of_ne_zero hne
        obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hb
        rw [ht, Multiset.map_cons, Multiset.sum_cons] at hsum
        have : 1 ≤ 4 ^ b := Nat.one_le_pow _ _ (by omega)
        omega
      simp [hse0, hso0]
    · rw [if_neg hn0]
      have hcard_pos : ¬ (se.card + so.card == 0) = true := by
        rw [beq_iff_eq]; intro h0
        have hse0 : se = 0 := Multiset.card_eq_zero.mp (by omega)
        have hso0 : so = 0 := Multiset.card_eq_zero.mp (by omega)
        rw [hse0, hso0] at hsum; simp at hsum; exact hn0 hsum.symm
      rw [if_neg hcard_pos]
      have hpop : popcount n ≤ se.card + so.card := by
        let s2 := se.map (2 * ·) + so.map (fun b => 2 * b + 1)
        have hs2_sum : (s2.map (2 ^ ·)).sum = n := by
          rw [← hsum]
          dsimp [s2]
          rw [Multiset.map_add, Multiset.sum_add, Multiset.map_map, Multiset.map_map]
          congr 1
          · congr 1; ext a; simp [Function.comp_def, pow_mul]
          · have h2 : ∀ t : Multiset ℕ, (t.map (fun b => 2 ^ (2 * b + 1))).sum = 2 * (t.map (4 ^ ·)).sum := by
              intro t
              induction t using Multiset.induction_on with
              | empty => simp
              | cons b u ihu =>
                rw [Multiset.map_cons, Multiset.sum_cons, ihu, Multiset.map_cons, Multiset.sum_cons]
                have hb : 2 ^ (2 * b + 1) = 2 * 4 ^ b := by rw [pow_succ', pow_mul]; norm_num
                rw [hb]; ring
            simpa [Function.comp_def] using h2 so
        have hs2_card : s2.card = se.card + so.card := by simp [s2]
        rw [← hs2_sum, ← hs2_card]
        exact popcount_sum_pow_two_le s2
      rw [if_neg (by simp; omega)]
      have hge_card : se.card + 2 * so.card ≤ n := by
        have h1 : ∀ t : Multiset ℕ, t.card ≤ (t.map (4 ^ ·)).sum := by
          intro t
          induction t using Multiset.induction_on with
          | empty => simp
          | cons a u ihu =>
            simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
            have : 1 ≤ 4 ^ a := Nat.one_le_pow _ _ (by omega)
            omega
        have := h1 se; have := h1 so; omega
      rw [if_neg (by simp; omega)]
      -- Split se and so into zeros and positive exponents
      let a0 := (se.filter (· = 0)).card
      let b0 := (so.filter (· = 0)).card
      let se' := (se.filter (· ≠ 0)).map (· - 1)
      let so' := (so.filter (· ≠ 0)).map (· - 1)
      have ha0_le : a0 ≤ se.card := Multiset.card_le_card (Multiset.filter_le _ _)
      have hb0_le : b0 ≤ so.card := Multiset.card_le_card (Multiset.filter_le _ _)
      have hse_split : (se.map (4 ^ ·)).sum = a0 + 4 * (se'.map (4 ^ ·)).sum := by
        have h1 := Multiset.filter_add_not (· = 0) se
        conv_lhs => rw [← h1, Multiset.map_add, Multiset.sum_add]
        congr 1
        · have h0s : (se.filter (· = 0)).map (4 ^ ·) = Multiset.replicate a0 1 := by
            apply Multiset.eq_replicate.mpr
            refine ⟨by simp [a0], fun x hx => ?_⟩
            rcases Multiset.mem_map.mp hx with ⟨y, hy, rfl⟩
            have hy0 : y = 0 := (Multiset.mem_filter.mp hy).2
            simp [hy0]
          rw [h0s, Multiset.sum_replicate, smul_eq_mul, mul_one]
        · dsimp [se']; rw [Multiset.map_map]
          have hall : ∀ y ∈ se.filter (· ≠ 0), 1 ≤ y := fun y hy => by
            have := (Multiset.mem_filter.mp hy).2; omega
          generalize se.filter (· ≠ 0) = t at hall ⊢
          induction t using Multiset.induction_on with
          | empty => simp
          | cons y u ihu =>
            simp only [Multiset.map_cons, Multiset.sum_cons, Function.comp_def]
            have hy1 : 1 ≤ y := hall y (by simp)
            have hyp : 4 ^ y = 4 * 4 ^ (y - 1) := by
              conv_lhs => rw [show y = (y - 1) + 1 by omega, pow_succ']
            dsimp only [Function.comp_def] at ihu
            rw [hyp, ihu (fun z hz => hall z (Multiset.mem_cons_of_mem hz))]
            ring
      have hso_split : (so.map (4 ^ ·)).sum = b0 + 4 * (so'.map (4 ^ ·)).sum := by
        have h1 := Multiset.filter_add_not (· = 0) so
        conv_lhs => rw [← h1, Multiset.map_add, Multiset.sum_add]
        congr 1
        · have h0s : (so.filter (· = 0)).map (4 ^ ·) = Multiset.replicate b0 1 := by
            apply Multiset.eq_replicate.mpr
            refine ⟨by simp [b0], fun x hx => ?_⟩
            rcases Multiset.mem_map.mp hx with ⟨y, hy, rfl⟩
            have hy0 : y = 0 := (Multiset.mem_filter.mp hy).2
            simp [hy0]
          rw [h0s, Multiset.sum_replicate, smul_eq_mul, mul_one]
        · dsimp [so']; rw [Multiset.map_map]
          have hall : ∀ y ∈ so.filter (· ≠ 0), 1 ≤ y := fun y hy => by
            have := (Multiset.mem_filter.mp hy).2; omega
          generalize so.filter (· ≠ 0) = t at hall ⊢
          induction t using Multiset.induction_on with
          | empty => simp
          | cons y u ihu =>
            simp only [Multiset.map_cons, Multiset.sum_cons, Function.comp_def]
            have hy1 : 1 ≤ y := hall y (by simp)
            have hyp : 4 ^ y = 4 * 4 ^ (y - 1) := by
              conv_lhs => rw [show y = (y - 1) + 1 by omega, pow_succ']
            dsimp only [Function.comp_def] at ihu
            rw [hyp, ihu (fun z hz => hall z (Multiset.mem_cons_of_mem hz))]
            ring
      have hse'_card : se'.card = se.card - a0 := by
        have h1 := congrArg Multiset.card (Multiset.filter_add_not (· = 0) se)
        simp only [Multiset.card_add] at h1
        dsimp [se', a0]; rw [Multiset.card_map]; omega
      have hso'_card : so'.card = so.card - b0 := by
        have h1 := congrArg Multiset.card (Multiset.filter_add_not (· = 0) so)
        simp only [Multiset.card_add] at h1
        dsimp [so', b0]; rw [Multiset.card_map]; omega
      let q := (se'.map (4 ^ ·)).sum + 2 * (so'.map (4 ^ ·)).sum
      have hnq : n = (a0 + 2 * b0) + 4 * q := by
        rw [← hsum, hse_split, hso_split]; dsimp [q]; ring
      have hcond : (a0 + 2 * b0 ≤ n && (n - (a0 + 2 * b0)) % 4 == 0) = true := by
        rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]; omega
      have hdiv_eq : (n - (a0 + 2 * b0)) / 4 = q := by omega
      have hq_lt : q < fuel := by omega
      have hrec : canEOAux fuel q (se.card - a0) (so.card - b0) = true := by
        rw [← hse'_card, ← hso'_card]
        exact ih q se' so' hq_lt rfl
      refine anyRange_eq_true ha0_le (anyRange_eq_true hb0_le ?_)
      dsimp only
      rw [if_pos hcond, hdiv_eq]
      exact hrec

private lemma canEO_of_multisets
    (n : ℕ) (se so : Multiset ℕ)
    (hsum : (se.map (4 ^ ·)).sum + 2 * (so.map (4 ^ ·)).sum = n) :
    canEO n se.card so.card = true :=
  canEOAux_of_multisets (n + 1) n se so (by omega) hsum

private def hasRepLt (x R : ℕ) : Bool :=
  anyRange (R - 1) (fun r =>
    if r == 0 then false
    else
      anyRange r (fun ec =>
        let oc := r - ec
        if 3 * x + ec ≥ oc && (3 * x + ec - oc) % 4 == 0 then
          canEO ((3 * x + ec - oc) / 4) ec oc
        else false))

private lemma le_of_hasRepLt_false {x R : ℕ} (hx : 0 < x) (h : hasRepLt x R = false) :
    ∀ m : Multiset ℕ, represents x m → R ≤ m.card := by
  intro m hrep
  by_contra hlt
  push Not at hlt
  have hm_pos : 1 ≤ m.card := by
    by_contra h0; push Not at h0
    have hm0 : m = 0 := Multiset.card_eq_zero.mp (by omega)
    have hv := hrep.2; rw [hm0] at hv; simp [value] at hv; omega
  obtain ⟨hcard_eq, hsum_z⟩ := repr_sum_pow_two hrep
  let ec := (m.filter (fun i => i % 2 = 0)).card
  let oc := (m.filter (fun i => i % 2 ≠ 0)).card
  let me := m.filter (fun i => i % 2 = 0)
  let mo := m.filter (fun i => i % 2 ≠ 0)
  let se := me.map (fun i => (i - 2) / 2)
  let so := mo.map (fun i => (i - 3) / 2)
  have hsum_split : (m.map (fun i => 2 ^ i)).sum =
      4 * ((se.map (4 ^ ·)).sum + 2 * (so.map (4 ^ ·)).sum) := by
    have h1 := Multiset.filter_add_not (fun i : ℕ => i % 2 = 0) m
    have hall := hrep.1
    conv_lhs => rw [← h1, Multiset.map_add, Multiset.sum_add]
    have he_sum : (me.map (fun i => 2 ^ i)).sum = 4 * (se.map (4 ^ ·)).sum := by
      dsimp [se]; rw [Multiset.map_map]
      have hme : ∀ i ∈ me, 2 ≤ i ∧ i % 2 = 0 := fun i hi =>
        ⟨hall i (Multiset.mem_of_mem_filter hi), (Multiset.mem_filter.mp hi).2⟩
      clear hsum_z hcard_eq h1 hall
      revert hme
      induction me using Multiset.induction_on with
      | empty => intro _; simp
      | cons a t iht =>
        intro hme
        simp only [Multiset.map_cons, Multiset.sum_cons, Function.comp_def]
        have ⟨ha2, ha0⟩ := hme a (by simp)
        have ha_pow : 2 ^ a = 4 * 4 ^ ((a - 2) / 2) := by
          have : 4 ^ ((a - 2) / 2) = 2 ^ (2 * ((a - 2) / 2)) := by rw [pow_mul]; norm_num
          rw [this, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
          congr 1; omega
        dsimp only [Function.comp_def] at iht
        rw [ha_pow, iht (fun i hi => hme i (Multiset.mem_cons_of_mem hi))]
        ring
    have ho_sum : (mo.map (fun i => 2 ^ i)).sum = 8 * (so.map (4 ^ ·)).sum := by
      dsimp [so]; rw [Multiset.map_map]
      have hmo : ∀ i ∈ mo, 2 ≤ i ∧ i % 2 ≠ 0 := fun i hi =>
        ⟨hall i (Multiset.mem_of_mem_filter hi), (Multiset.mem_filter.mp hi).2⟩
      clear hsum_z hcard_eq h1 hall he_sum
      revert hmo
      induction mo using Multiset.induction_on with
      | empty => intro _; simp
      | cons a t iht =>
        intro hmo
        simp only [Multiset.map_cons, Multiset.sum_cons, Function.comp_def]
        have ⟨ha2, ha1⟩ := hmo a (by simp)
        have ha_pow : 2 ^ a = 8 * 4 ^ ((a - 3) / 2) := by
          have : 4 ^ ((a - 3) / 2) = 2 ^ (2 * ((a - 3) / 2)) := by rw [pow_mul]; norm_num
          rw [this, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
          congr 1; omega
        dsimp only [Function.comp_def] at iht
        rw [ha_pow, iht (fun i hi => hmo i (Multiset.mem_cons_of_mem hi))]
        ring
    change (me.map (fun i => 2 ^ i)).sum + (mo.map (fun i => 2 ^ i)).sum = _
    rw [he_sum, ho_sum]; ring
  have hsum_z' : 3 * (x : ℤ) + (ec : ℤ) - (oc : ℤ) =
      ((4 * ((se.map (4 ^ ·)).sum + 2 * (so.map (4 ^ ·)).sum) : ℕ) : ℤ) := by
    have hcast : (m.map (fun i : ℕ => (2 : ℤ) ^ i)).sum =
        (((m.map (fun i : ℕ => (2 : ℕ) ^ i)).sum : ℕ) : ℤ) := by
      rw [Nat.cast_multiset_sum, Multiset.map_map]
      simp only [Function.comp_def, Nat.cast_pow, Nat.cast_ofNat]
    have hsum_z'' : 3 * (x : ℤ) + (ec : ℤ) - (oc : ℤ) = (m.map (fun i : ℕ => (2 : ℤ) ^ i)).sum := by
      simpa [ec, oc] using hsum_z
    rw [hsum_z'', hcast, hsum_split]
  have hcard_eq' : ec + oc = m.card := hcard_eq
  have hge_oc : oc ≤ 3 * x + ec := by omega
  have hN_eq : 3 * x + ec - oc = 4 * ((se.map (4 ^ ·)).sum + 2 * (so.map (4 ^ ·)).sum) := by
    omega
  have hcan : canEO ((3 * x + ec - oc) / 4) ec oc = true := by
    have hdiv : (3 * x + ec - oc) / 4 = (se.map (4 ^ ·)).sum + 2 * (so.map (4 ^ ·)).sum := by omega
    rw [hdiv]
    have hse_c : se.card = ec := Multiset.card_map _ _
    have hso_c : so.card = oc := Multiset.card_map _ _
    rw [← hse_c, ← hso_c]
    exact canEO_of_multisets _ se so rfl
  have hm_ne : m.card ≠ 0 := by
    intro h0
    have hm0 : m = 0 := Multiset.card_eq_zero.mp h0
    subst hm0
    have : 0 = x := by simpa [value] using hrep.2
    omega
  have htrue : hasRepLt x R = true := by
    unfold hasRepLt
    refine anyRange_eq_true (x := m.card) (by omega) ?_
    rw [if_neg (by simp [hm_ne])]
    refine anyRange_eq_true (x := ec) (by omega) ?_
    have hoc_eq : m.card - ec = oc := by omega
    dsimp only
    rw [hoc_eq]
    have hcond : (3 * x + ec ≥ oc && (3 * x + ec - oc) % 4 == 0) = true := by
      rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      exact ⟨hge_oc, by omega⟩
    rw [if_pos hcond]
    exact hcan
  rw [htrue] at h
  exact Bool.noConfusion h

/-! ### Part 5: Computable `v2`, trajectory table, witnesses, and finite verification -/

private def v2Aux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if n % 2 == 0 then 1 + v2Aux fuel (n / 2) else 0

private lemma v2Aux_eq_padicValNat :
    ∀ fuel n : ℕ, 0 < n → n ≤ fuel → v2Aux fuel n = padicValNat 2 n := by
  intro fuel
  induction fuel with
  | zero => intro n hn hle; omega
  | succ fuel ih =>
    intro n hn hle
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    unfold v2Aux
    by_cases h2 : n % 2 = 0
    · have hbeq : (n % 2 == 0) = true := beq_iff_eq.mpr h2
      rw [if_pos hbeq]
      have hdvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero h2
      have hdiv_pos : 0 < n / 2 := by omega
      have hmul : n = 2 * (n / 2) := (Nat.mul_div_cancel' hdvd).symm
      rw [ih (n / 2) hdiv_pos (by omega)]
      conv_rhs => rw [hmul]
      rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num)]
    · have hbeq : (n % 2 == 0) = false := beq_false_of_ne h2
      rw [if_neg (by simp [hbeq])]
      exact (padicValNat.eq_zero_of_not_dvd (by omega)).symm

private def v2 (n : ℕ) : ℕ := v2Aux n n

private lemma v2_eq_padicValNat (n : ℕ) (hn : 0 < n) : v2 n = padicValNat 2 n :=
  v2Aux_eq_padicValNat n n hn le_rfl

private def redComp (n : ℕ) : ℕ := (3 * n + 1) / 2 ^ v2 (3 * n + 1)

private lemma redComp_eq_reduced (n : ℕ) : redComp n = reduced n := by
  unfold redComp reduced valuation
  rw [v2_eq_padicValNat (3 * n + 1) (by omega)]

private def T (m : ℕ) : ℕ := (reduced^[m]) 27

private def TComp (m : ℕ) : ℕ := (redComp^[m]) 27

private lemma TComp_eq_T (m : ℕ) : TComp m = T m := by
  unfold TComp T
  have h : redComp = reduced := funext redComp_eq_reduced
  rw [h]

private def V (m : ℕ) : ℕ := valuation (T m)

private def VComp (m : ℕ) : ℕ := v2 (3 * TComp m + 1)

private lemma VComp_eq_V (m : ℕ) : VComp m = V m := by
  unfold VComp V valuation
  rw [TComp_eq_T, v2_eq_padicValNat (3 * T m + 1) (by omega)]

private lemma T_ge_41 : ∀ m : ℕ, 41 ≤ m → T m = 1 := by
  have h41 : T 41 = 1 := by rw [← TComp_eq_T]; decide
  have h1 : reduced 1 = 1 := by rw [← redComp_eq_reduced]; decide
  intro m hm
  have hsub : m = (m - 41) + 41 := by omega
  rw [hsub]
  generalize m - 41 = k
  induction k with
  | zero => simpa using h41
  | succ k ih =>
    unfold T at ih ⊢
    rw [show k + 1 + 41 = (k + 41) + 1 by omega, Function.iterate_succ_apply', ih, h1]

private def witList : ℕ → List ℕ
  | 1 => [4, 5, 6, 7, 8]
  | 2 => [5, 6, 7, 8, 10]
  | 3 => [3, 4, 5, 8, 8]
  | 4 => [3, 4, 6, 8, 9]
  | 5 => [3, 8, 10]
  | 6 => [4, 7, 8, 9, 10]
  | 7 => [6, 7, 9, 10, 12]
  | 8 => [5, 8, 12]
  | 9 => [4, 5, 6, 9, 10]
  | 10 => [5, 6, 8, 9, 12]
  | 11 => [3, 6, 8, 9, 10]
  | 12 => [4, 5, 6, 7, 9, 10, 10]
  | 13 => [5, 6, 7, 12, 12]
  | 14 => [3, 4, 6, 10, 11]
  | 15 => [3, 7, 8, 8, 12]
  | 16 => [4, 6, 7, 8, 9, 11, 12]
  | 17 => [7, 8, 9, 12, 14]
  | 18 => [7, 8, 10, 11, 12, 13, 14]
  | 19 => [3, 6, 7, 8, 9, 10, 10]
  | 20 => [4, 5, 7, 8, 12]
  | 21 => [5, 8, 10, 12, 13]
  | 22 => [4, 5, 6, 7, 8, 9, 12]
  | 23 => [5, 6, 7, 8, 9, 11, 12, 12, 12]
  | 24 => [3, 4, 5, 6, 9, 10, 12]
  | 25 => [3, 4, 5, 7, 8, 12, 12]
  | 26 => [3, 4, 7, 9, 12, 12, 12]
  | 27 => [3, 5, 6, 7, 8, 9, 10, 10, 14]
  | 28 => [5, 6, 7, 8, 12, 13, 14]
  | 29 => [7, 8, 9, 11, 13, 14, 14, 16, 16]
  | 30 => [3, 4, 14]
  | 31 => [3, 5, 12, 12, 14]
  | 32 => [6, 12, 15]
  | 33 => [10, 14, 15, 17, 18]
  | 34 => [6, 8, 12, 13, 13]
  | 35 => [8, 10, 11, 12, 13]
  | 36 => [11, 12, 13, 14, 14]
  | 37 => [7, 8, 12]
  | 38 => [3, 5, 6, 6, 8]
  | 39 => [7, 8, 8]
  | 40 => [14]
  | _ => [10]

private def checkWit (m : ℕ) : Bool :=
  let L := witList m
  let emin := VComp (m - 1)
  let R := L.length
  let ec := (L.filter (fun i => i % 2 == 0)).length
  let oc := (L.filter (fun i => i % 2 != 0)).length
  (R ≤ 9) &&
  (0 < TComp m) &&
  (emin ≤ 6) &&
  (L.all (fun i => 2 ≤ i)) &&
  ((L.map jac).sum == lift emin (TComp m)) &&
  (ec == oc + 1) &&
  ((List.range (7 - emin)).all (fun d => !hasRepLt (lift (emin + d) (TComp m)) R))

private lemma checkWit_all_1_to_40 :
    (List.range 40).all (fun k => checkWit (k + 1)) = true := by
  decide +kernel

private lemma minCoins_lift_eq_of_checkWit {m e : ℕ} (hm : 1 ≤ m) (hm40 : m ≤ 40)
    (he : V (m - 1) ≤ e) : minCoins (lift e (T m)) = (witList m).length := by
  have hchk : checkWit m = true := by
    have h1 := List.all_eq_true.mp checkWit_all_1_to_40 (m - 1) (List.mem_range.mpr (by omega))
    simpa [show m - 1 + 1 = m by omega] using h1
  unfold checkWit at hchk
  simp only [VComp_eq_V, TComp_eq_T, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true, Bool.not_eq_true'] at hchk
  rcases hchk with ⟨⟨⟨⟨⟨⟨hR9, hTpos⟩, hemin6⟩, hall2⟩, hsum_eq⟩, hec_oc⟩, hlow_all⟩
  let L := witList m
  let emin := V (m - 1)
  let R := L.length
  -- Upper bound: shift L up by 2 * (e - emin)
  have hrep_base : represents (lift emin (T m)) (L : Multiset ℕ) := by
    refine ⟨fun i hi => hall2 i hi, ?_⟩
    simpa [value] using hsum_eq
  have heo_base : (((L : Multiset ℕ).filter (fun i => i % 2 = 0)).card : ℤ) -
      (((L : Multiset ℕ).filter (fun i => i % 2 ≠ 0)).card : ℤ) = 1 := by
    have he1 : ((L : Multiset ℕ).filter (fun i => i % 2 = 0)).card =
        (L.filter (fun i => i % 2 == 0)).length := by
      rw [Multiset.filter_coe, Multiset.coe_card]
      congr 1
    have ho1 : ((L : Multiset ℕ).filter (fun i => i % 2 ≠ 0)).card =
        (L.filter (fun i => i % 2 != 0)).length := by
      rw [Multiset.filter_coe, Multiset.coe_card]
      congr 1; apply List.filter_congr; intro x _
      by_cases hx : x % 2 = 0 <;> simp [hx] <;> omega
    rw [he1, ho1, hec_oc]; push_cast; ring
  have hrep_e : represents (lift e (T m)) ((L : Multiset ℕ).map (· + 2 * (e - emin))) := by
    have h1 := represents_shift_up hrep_base heo_base (e - emin)
    rwa [lift_add, Nat.sub_add_cancel he] at h1
  have hupper : minCoins (lift e (T m)) ≤ R := by
    simpa [R] using minCoins_le_of_represents hrep_e
  -- Lower bound: check for e <= 6 via hlow_all, then step up for e >= 6 via minCoins_lift_step
  have hlow_le6 : ∀ e' : ℕ, emin ≤ e' → e' ≤ 6 →
      ∀ ms : Multiset ℕ, represents (lift e' (T m)) ms → R ≤ ms.card := by
    intro e' he1 he2
    have hfalse : hasRepLt (lift e' (T m)) R = false := by
      have h1 := hlow_all (e' - emin) (List.mem_range.mpr (by omega))
      have heq : V (m - 1) + (e' - emin) = e' := by dsimp [emin]; omega
      simpa [R, heq] using h1
    have hpos : 0 < lift e' (T m) := by
      unfold lift
      have h4 : 0 < 4 ^ e' := Nat.pos_of_ne_zero (by positivity)
      have hmul : 0 < 4 ^ e' * T m := Nat.mul_pos h4 hTpos
      omega
    exact le_of_hasRepLt_false hpos hfalse
  have hlow_all_e : ∀ e' : ℕ, emin ≤ e' →
      ∀ ms : Multiset ℕ, represents (lift e' (T m)) ms → R ≤ ms.card := by
    intro e' he1
    by_cases he6 : e' ≤ 6
    · exact hlow_le6 e' he1 he6
    · have hsub : e' = 6 + (e' - 6) := by omega
      rw [hsub]
      generalize e' - 6 = d
      induction d with
      | zero => exact hlow_le6 6 hemin6 le_rfl
      | succ d ih =>
        rw [show 6 + (d + 1) = (6 + d) + 1 by omega]
        exact minCoins_lift_step hR9 (by omega) ih
  have hlower : R ≤ minCoins (lift e (T m)) := le_minCoins_of_forall (hlow_all_e e he)
  exact le_antisymm hupper hlower

private lemma minCoins_lift_one (e : ℕ) : minCoins (lift e 1) = 1 := by
  have hrep : represents (lift e 1) {2 * e + 2} := by
    refine ⟨fun i hi => by simp at hi; omega, ?_⟩
    simp [value, lift_one_eq_jac]
  have hupper : minCoins (lift e 1) ≤ 1 := minCoins_le_of_represents hrep
  have hlower : 1 ≤ minCoins (lift e 1) := by
    refine le_minCoins_of_forall fun m hm => ?_
    by_contra h0; push Not at h0
    have hm0 : m = 0 := Multiset.card_eq_zero.mp (by omega)
    have hv := hm.2; rw [hm0] at hv; simp [value, lift] at hv
    have : 1 ≤ 4 ^ e := Nat.one_le_pow _ _ (by omega)
    omega
  exact le_antisymm hupper hlower

private def stableVal (m : ℕ) : ℕ :=
  if m ≤ 40 then (witList m).length else 1

private lemma minCoins_grid_eq_stable {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    minCoins (grid n k) = stableVal (n + k - 2) := by
  obtain ⟨e, he_eq, he_ge⟩ := grid_eq_lift n k (by omega) hk
  rw [he_eq]
  have hge := he_ge hn
  have hidx : n + k - 3 = (n + k - 2) - 1 := by omega
  rw [hidx] at hge
  unfold stableVal
  split_ifs with hm40
  · exact minCoins_lift_eq_of_checkWit (by omega) hm40 hge
  · have hT1 : T (n + k - 2) = 1 := T_ge_41 (n + k - 2) (by omega)
    change minCoins (lift e (T (n + k - 2))) = 1
    rw [hT1]
    exact minCoins_lift_one e

/-! ### Part 6: Main theorem -/

theorem main_proof :
    (∀ n k : ℕ, 2 ≤ n → 1 ≤ k → n + k = 14 → minCoins (grid n k) = 7) ∧
    (∀ n k : ℕ, 2 ≤ n → 1 ≤ k → n + k = 31 → minCoins (grid n k) = 9) ∧
    (∀ n k : ℕ, 1 < n → 1 < k → minCoins (grid n k) = minCoins (grid k n)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n k hn hk hsum
    rw [minCoins_grid_eq_stable hn hk, hsum]
    rfl
  · intro n k hn hk hsum
    rw [minCoins_grid_eq_stable hn hk, hsum]
    rfl
  · intro n k hn hk
    rw [minCoins_grid_eq_stable (by omega) (by omega),
        minCoins_grid_eq_stable (by omega) (by omega), add_comm n k]

end OMA.S_oeis_a372561_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a372561.main :=
  OMA.S_oeis_a372561_Proof.main_proof
