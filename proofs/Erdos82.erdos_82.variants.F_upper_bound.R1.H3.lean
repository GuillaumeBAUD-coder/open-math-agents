import OMAReductions.R_Erdos82_erdos_82_variants_F_upper_bound_R1

open scoped Classical

section Helpers

private lemma sum_pair_lt_eq_double (n : ℕ) (F : Fin n → Fin n → ℝ)
    (hdiag : ∀ u : Fin n, F u u = 0) :
    (∑ u : Fin n, ∑ v : Fin n, F u v) =
    ∑ e ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), (F e.1 e.2 + F e.2 e.1) := by
  let E := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let Egt := Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1)
  let Ediag := Finset.univ.filter (fun p : Fin n × Fin n => p.1 = p.2)
  have hpart : (Finset.univ : Finset (Fin n × Fin n)) = E ∪ Egt ∪ Ediag := by
    ext p
    simp only [E, Egt, Ediag, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases lt_trichotomy p.1 p.2 with h | h | h <;> tauto
  have hdisj1 : Disjoint E Egt := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [E, Egt, Finset.mem_filter] at h1 h2
    exact lt_asymm h1.2 h2.2
  have hdisj2 : Disjoint (E ∪ Egt) Ediag := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [E, Egt, Ediag, Finset.mem_union, Finset.mem_filter] at h1 h2
    rcases h1 with h1 | h1
    · exact h1.2.ne h2.2
    · exact h1.2.ne h2.2.symm
  have hdouble : (∑ u : Fin n, ∑ v : Fin n, F u v) =
      ∑ p : Fin n × Fin n, F p.1 p.2 := (Fintype.sum_prod_type (fun p : Fin n × Fin n => F p.1 p.2)).symm
  rw [hdouble]
  calc ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)), F p.1 p.2
      = (∑ p ∈ E, F p.1 p.2) + (∑ p ∈ Egt, F p.1 p.2) + (∑ p ∈ Ediag, F p.1 p.2) := by
        rw [hpart, Finset.sum_union hdisj2, Finset.sum_union hdisj1]
    _ = (∑ p ∈ E, F p.1 p.2) + (∑ p ∈ E, F p.2 p.1) + 0 := by
        have hgt : ∑ p ∈ Egt, F p.1 p.2 = ∑ p ∈ E, F p.2 p.1 := by
          refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
          · intro p hp; simp only [E, Egt, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hp
          · intro p1 _ p2 _ h; simp only [Prod.mk.injEq] at h; exact Prod.ext h.2 h.1
          · intro p hp; refine ⟨(p.2, p.1), ?_, by ext <;> rfl⟩
            simp only [E, Egt, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hp
          · intro _ _; rfl
        have hdg : ∑ p ∈ Ediag, F p.1 p.2 = 0 := by
          refine Finset.sum_eq_zero fun p hp => ?_
          have heq : p.1 = p.2 := (Finset.mem_filter.mp hp).2
          rw [heq, hdiag]
        rw [hgt, hdg]
    _ = ∑ e ∈ E, (F e.1 e.2 + F e.2 e.1) := by rw [add_zero, Finset.sum_add_distrib]

private lemma chernoff_edge_sum (n : ℕ)
    (q : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)} → ℝ)
    (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    (coef : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)} → ℝ)
    (hcoef : ∀ e, |coef e| ≤ 2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) (L : ℝ) :
    (∑ G : SimpleGraph (Fin n),
      (if (∑ e : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)},
            coef e * (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0)) ≤ L
        then (1 : ℝ) else 0) *
      (∏ e : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)},
        if G.Adj e.1.1 e.1.2 then q e else 1 - q e)) ≤
    Real.exp (t * (L - ∑ e, coef e * q e) + t ^ 2 * ∑ e, (coef e) ^ 2) := by
  let E := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let eGraph : SimpleGraph (Fin n) ≃ ({p : Fin n × Fin n // p ∈ E} → Bool) :=
    { toFun := fun G e => decide (G.Adj e.1.1 e.1.2)
      invFun := fun f =>
        { Adj := fun u v =>
            if h : u < v then f ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩ = true
            else if h' : v < u then f ⟨(v, u), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩⟩ = true
            else False
          symm := ⟨by
            intro u v h
            rcases lt_trichotomy u v with huv | rfl | hvu
            · have hn : ¬ v < u := lt_asymm huv; simpa [huv, hn] using h
            · simp at h
            · have hn : ¬ u < v := lt_asymm hvu; simpa [hvu, hn] using h⟩
          loopless := ⟨by intro u h; simp at h⟩ }
      left_inv := fun G => by
        ext u v
        rcases lt_trichotomy u v with huv | rfl | hvu
        · simp [huv]
        · simp
        · have hn : ¬ u < v := lt_asymm hvu; simp [hn, hvu, G.adj_comm]
      right_inv := fun f => by
        ext ⟨⟨u, v⟩, he⟩
        have huv : u < v := (Finset.mem_filter.mp he).2
        simp [huv] }
  have hw_nonneg : ∀ G : SimpleGraph (Fin n),
      0 ≤ ∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e := by
    intro G
    refine Finset.prod_nonneg fun e _ => ?_
    have := hq e
    split_ifs <;> linarith
  have hmarkov :
      (∑ G : SimpleGraph (Fin n),
        (if (∑ e : {p : Fin n × Fin n // p ∈ E}, coef e * (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0)) ≤ L
          then (1 : ℝ) else 0) *
        (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e)) ≤
      ∑ G : SimpleGraph (Fin n),
        Real.exp (t * (L - ∑ e : {p : Fin n × Fin n // p ∈ E},
          coef e * (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0))) *
        (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) := by
    refine Finset.sum_le_sum fun G _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (hw_nonneg G)
    split_ifs with hle
    · exact Real.one_le_exp (mul_nonneg ht0 (sub_nonneg.mpr hle))
    · exact (Real.exp_pos _).le
  have hexp_prod :
      (∑ G : SimpleGraph (Fin n),
        Real.exp (t * (L - ∑ e : {p : Fin n × Fin n // p ∈ E},
          coef e * (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0))) *
        (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e)) =
      Real.exp (t * L) * ∏ e : {p : Fin n × Fin n // p ∈ E},
        ((1 - q e) + q e * Real.exp (-t * coef e)) := by
    have hrew : ∀ G : SimpleGraph (Fin n),
        Real.exp (t * (L - ∑ e : {p : Fin n × Fin n // p ∈ E},
          coef e * (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0))) *
        (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) =
        Real.exp (t * L) * ∏ e : {p : Fin n × Fin n // p ∈ E},
          (if G.Adj e.1.1 e.1.2 then q e * Real.exp (-t * coef e) else 1 - q e) := by
      intro G
      have harg : t * (L - ∑ e : {p : Fin n × Fin n // p ∈ E},
            coef e * (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0)) =
          t * L + ∑ e : {p : Fin n × Fin n // p ∈ E},
            (if G.Adj e.1.1 e.1.2 then -t * coef e else 0) := by
        rw [mul_sub, sub_eq_add_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
        congr 1
        refine Finset.sum_congr rfl fun e _ => ?_
        split_ifs <;> ring
      rw [harg, Real.exp_add, Real.exp_sum, mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun e _ => ?_
      split_ifs <;> simp [mul_comm]
    simp_rw [hrew, ← Finset.mul_sum]
    congr 1
    have hequiv :
        (∑ G : SimpleGraph (Fin n), ∏ e : {p : Fin n × Fin n // p ∈ E},
          if G.Adj e.1.1 e.1.2 then q e * Real.exp (-t * coef e) else 1 - q e) =
        ∑ f : ({p : Fin n × Fin n // p ∈ E} → Bool), ∏ e : {p : Fin n × Fin n // p ∈ E},
          if f e = true then q e * Real.exp (-t * coef e) else 1 - q e := by
      refine Fintype.sum_equiv eGraph _ _ fun G => ?_
      refine Finset.prod_congr rfl fun e _ => by simp [eGraph]
    rw [hequiv, ← Fintype.prod_sum (fun (e : {p : Fin n × Fin n // p ∈ E}) (b : Bool) =>
      if b = true then q e * Real.exp (-t * coef e) else 1 - q e)]
    refine Finset.prod_congr rfl fun e _ => ?_
    simp [add_comm]
  have hmgf : ∀ e : {p : Fin n × Fin n // p ∈ E},
      (1 - q e) + q e * Real.exp (-t * coef e) ≤
      Real.exp (q e * (-t * coef e) + (t * coef e) ^ 2) := by
    intro e
    set x : ℝ := -t * coef e
    have hx : |x| ≤ 1 := by
      rw [abs_mul, abs_neg, abs_of_nonneg ht0]
      nlinarith [hcoef e]
    have hexp : Real.exp x ≤ 1 + x + x ^ 2 := by
      have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hx)).2
      linarith
    have hq0 : 0 ≤ q e := (hq e).1
    have hq1 : q e ≤ 1 := (hq e).2
    have hx2 : x ^ 2 = (t * coef e) ^ 2 := by dsimp only [x]; ring
    calc (1 - q e) + q e * Real.exp x
        ≤ (1 - q e) + q e * (1 + x + x ^ 2) := by gcongr
      _ = 1 + q e * x + q e * x ^ 2 := by ring
      _ ≤ 1 + q e * x + x ^ 2 := by gcongr; exact mul_le_of_le_one_left (sq_nonneg x) hq1
      _ = 1 + (q e * x + (t * coef e) ^ 2) := by rw [hx2]; ring
      _ ≤ Real.exp (q e * x + (t * coef e) ^ 2) := by
          linarith [Real.add_one_le_exp (q e * x + (t * coef e) ^ 2)]
  have hprod_le :
      (∏ e : {p : Fin n × Fin n // p ∈ E}, ((1 - q e) + q e * Real.exp (-t * coef e))) ≤
      Real.exp (-t * ∑ e, coef e * q e + t ^ 2 * ∑ e, (coef e) ^ 2) := by
    have hnonneg : ∀ e : {p : Fin n × Fin n // p ∈ E},
        0 ≤ (1 - q e) + q e * Real.exp (-t * coef e) := by
      intro e
      have := hq e
      have := Real.exp_pos (-t * coef e)
      nlinarith
    calc (∏ e : {p : Fin n × Fin n // p ∈ E}, ((1 - q e) + q e * Real.exp (-t * coef e)))
        ≤ ∏ e : {p : Fin n × Fin n // p ∈ E}, Real.exp (q e * (-t * coef e) + (t * coef e) ^ 2) :=
          Finset.prod_le_prod (fun e _ => hnonneg e) (fun e _ => hmgf e)
      _ = Real.exp (∑ e : {p : Fin n × Fin n // p ∈ E}, (q e * (-t * coef e) + (t * coef e) ^ 2)) :=
          (Real.exp_sum _ _).symm
      _ = Real.exp (-t * ∑ e, coef e * q e + t ^ 2 * ∑ e, (coef e) ^ 2) := by
          congr 1
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          congr 1 <;> refine Finset.sum_congr rfl fun e _ => by ring
  calc (∑ G : SimpleGraph (Fin n),
        (if (∑ e : {p : Fin n × Fin n // p ∈ E}, coef e * (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0)) ≤ L
          then (1 : ℝ) else 0) *
        (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e))
      ≤ Real.exp (t * L) * ∏ e : {p : Fin n × Fin n // p ∈ E},
          ((1 - q e) + q e * Real.exp (-t * coef e)) := hmarkov.trans_eq hexp_prod
    _ ≤ Real.exp (t * L) * Real.exp (-t * ∑ e, coef e * q e + t ^ 2 * ∑ e, (coef e) ^ 2) :=
        mul_le_mul_of_nonneg_left hprod_le (Real.exp_pos _).le
    _ = Real.exp (t * (L - ∑ e, coef e * q e) + t ^ 2 * ∑ e, (coef e) ^ 2) := by
        rw [← Real.exp_add]; congr 1; ring

private lemma card_powersetCard_le_pow (n m : ℕ) (_hn : 1 ≤ n) :
    ((Finset.univ : Finset (Fin n)).powersetCard m).card ≤ n ^ m := by
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hf : 1 ≤ m.factorial := Nat.factorial_pos m
  calc Nat.choose n m
      ≤ Nat.choose n m * m.factorial := Nat.le_mul_of_pos_right _ hf
    _ = n.descFactorial m := by rw [mul_comm, Nat.descFactorial_eq_factorial_mul_choose]
    _ ≤ n ^ m := Nat.descFactorial_le_pow n m

private lemma log_div_log_two_le {n : ℕ} (hn : 3 ≤ n) :
    (Nat.log 2 n + 1 : ℝ) ≤ 3 * Real.log (n : ℝ) := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hlog1 : 1 ≤ Real.log (n : ℝ) := by
    have hexp3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    have : Real.exp 1 ≤ (n : ℝ) := le_trans hexp3.le (by exact_mod_cast hn)
    exact (Real.le_log_iff_exp_le (by positivity)).mpr this
  have hpow : (2 : ℝ) ^ (Nat.log 2 n : ℕ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hlog_pow : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
    have h := Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow] at h
  have hlog2 : 1 / 2 < Real.log 2 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have hexp4 : Real.exp 1 < 4 := Real.exp_one_lt_d9.trans (by norm_num)
    have hsq : (Real.exp (1 / 2)) ^ 2 < 2 ^ 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
      exact hexp4
    by_contra! hle
    have := mul_self_le_mul_self (by norm_num) hle
    rw [← sq, ← sq] at this
    linarith
  have hnat_le : (Nat.log 2 n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hnonneg : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
    nlinarith
  linarith

private lemma log_cubed_le_n_twelfth (n : ℕ) (hn : 1 ≤ n) :
    (Real.log (n : ℝ)) ^ 3 ≤ 10368 * (n : ℝ) ^ (1 / 12 : ℝ) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hsum : ((1 / 12 : ℝ) * Real.log (n : ℝ)) ^ 3 / (Nat.factorial 3 : ℝ) ≤
      Real.exp ((1 / 12 : ℝ) * Real.log (n : ℝ)) := by
    have h1 : ((1 / 12 : ℝ) * Real.log (n : ℝ)) ^ 3 / (Nat.factorial 3 : ℝ) ≤
        ∑ i ∈ Finset.range 4, ((1 / 12 : ℝ) * Real.log (n : ℝ)) ^ i / (i.factorial : ℝ) :=
      Finset.single_le_sum (f := fun i => ((1 / 12 : ℝ) * Real.log (n : ℝ)) ^ i / (i.factorial : ℝ))
        (fun i _ => by positivity) (Finset.mem_range.mpr (by decide))
    exact h1.trans (Real.sum_le_exp_of_nonneg (by positivity) 4)
  have hexp : Real.exp ((1 / 12 : ℝ) * Real.log (n : ℝ)) = (n : ℝ) ^ (1 / 12 : ℝ) := by
    rw [Real.rpow_def_of_pos (by positivity), mul_comm]
  rw [hexp] at hsum
  have hfact3 : (Nat.factorial 3 : ℝ) = 6 := by norm_num
  rw [hfact3] at hsum
  linarith

private lemma ind_and (P Q : Prop) [Decidable (P ∧ Q)] [Decidable P] [Decidable Q] :
    (if P ∧ Q then (1 : ℝ) else 0) = (if P then 1 else 0) * (if Q then 1 else 0) := by
  by_cases hP : P
  · by_cases hQ : Q
    · rw [if_pos ⟨hP, hQ⟩, if_pos hP, if_pos hQ, one_mul]
    · rw [if_neg (fun h => hQ h.2), if_pos hP, if_neg hQ, mul_zero]
  · rw [if_neg (fun h => hP h.1), if_neg hP, zero_mul]

private lemma ind_or_disj (P Q : Prop) [Decidable (P ∨ Q)] [Decidable P] [Decidable Q]
    (hPQ : ¬ (P ∧ Q)) :
    (if P ∨ Q then (1 : ℝ) else 0) = (if P then 1 else 0) + (if Q then 1 else 0) := by
  by_cases hP : P
  · have hQ : ¬ Q := fun h => hPQ ⟨hP, h⟩
    rw [if_pos (Or.inl hP), if_pos hP, if_neg hQ, add_zero]
  · by_cases hQ : Q
    · rw [if_pos (Or.inr hQ), if_neg hP, if_pos hQ, zero_add]
    · rw [if_neg (fun h => h.elim hP hQ), if_neg hP, if_neg hQ, add_zero]

private lemma sum_ite_mem_fin {n : ℕ} (X : Finset (Fin n))
    [DecidablePred (fun v : Fin n => v ∈ X)] :
    (∑ v : Fin n, if v ∈ X then (1 : ℝ) else 0) = (X.card : ℝ) := by
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun v : Fin n => v ∈ X) = X := by
    ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hf, Finset.sum_const, nsmul_eq_mul, mul_one]

private lemma sum_orderEmb {n m : ℕ} (X : Finset (Fin n)) (hX : X.card = m) (g : Fin n → ℝ) :
    ∑ x ∈ X, g x = ∑ i : Fin m, g (X.orderEmbOfFin hX i) := by
  let emb := X.orderEmbOfFin hX
  refine Finset.sum_bij (fun x hx =>
    let h : x ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hx
    Classical.choose h) ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro x1 hx1 x2 hx2 h
    have h1 : x1 ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hx1
    have h2 : x2 ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hx2
    have := congrArg emb h
    rwa [Classical.choose_spec h1, Classical.choose_spec h2] at this
  · intro i _
    have hi : emb i ∈ X := by
      have : emb i ∈ Set.range emb := Set.mem_range_self _
      rwa [Finset.range_orderEmbOfFin] at this
    refine ⟨emb i, hi, ?_⟩
    exact emb.injective (Classical.choose_spec (show emb i ∈ Set.range emb by
      rw [Finset.range_orderEmbOfFin]; exact hi))
  · intro x hx
    have h1 : x ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hx
    rw [Classical.choose_spec h1]

private lemma sum_pairs_orderEmb {n m : ℕ} (X : Finset (Fin n)) (hX : X.card = m)
    (g : Fin n → ℝ) :
    (∑ x₁ ∈ X, ∑ x₂ ∈ X, if x₁ ≠ x₂ then g x₁ * g x₂ else 0) =
    ∑ i : Fin m, ∑ j : Fin m,
      if i ≠ j then g (X.orderEmbOfFin hX i) * g (X.orderEmbOfFin hX j) else 0 := by
  let emb := X.orderEmbOfFin hX
  refine Finset.sum_bij (fun x₁ hx₁ =>
    let h : x₁ ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hx₁
    Classical.choose h) ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro x1 hx1 x2 hx2 h
    have h1 : x1 ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hx1
    have h2 : x2 ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hx2
    have := congrArg emb h
    rwa [Classical.choose_spec h1, Classical.choose_spec h2] at this
  · intro i _
    have hi : emb i ∈ X := by
      have : emb i ∈ Set.range emb := Set.mem_range_self _
      rwa [Finset.range_orderEmbOfFin] at this
    refine ⟨emb i, hi, ?_⟩
    exact emb.injective (Classical.choose_spec (show emb i ∈ Set.range emb by
      rw [Finset.range_orderEmbOfFin]; exact hi))
  · intro x₁ hx₁
    have h1 : x₁ ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hx₁
    have heq1 : emb (Classical.choose h1) = x₁ := Classical.choose_spec h1
    refine Finset.sum_bij (fun x₂ hx₂ =>
      let h : x₂ ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hx₂
      Classical.choose h) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro y1 hy1 y2 hy2 h
      have h1' : y1 ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hy1
      have h2' : y2 ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hy2
      have := congrArg emb h
      rwa [Classical.choose_spec h1', Classical.choose_spec h2'] at this
    · intro j _
      have hj : emb j ∈ X := by
        have : emb j ∈ Set.range emb := Set.mem_range_self _
        rwa [Finset.range_orderEmbOfFin] at this
      refine ⟨emb j, hj, ?_⟩
      exact emb.injective (Classical.choose_spec (show emb j ∈ Set.range emb by
        rw [Finset.range_orderEmbOfFin]; exact hj))
    · intro x₂ hx₂
      have h2 : x₂ ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hx₂
      have heq2 : emb (Classical.choose h2) = x₂ := Classical.choose_spec h2
      have hne : x₁ ≠ x₂ ↔ Classical.choose h1 ≠ Classical.choose h2 := by
        conv_lhs => rw [← heq1, ← heq2]
        exact emb.injective.ne_iff
      by_cases hc : Classical.choose h1 ≠ Classical.choose h2
      · have hx : x₁ ≠ x₂ := hne.mpr hc
        rw [if_pos hx, if_pos hc, heq1, heq2]
      · have hx : ¬ (x₁ ≠ x₂) := fun h => hc (hne.mp h)
        rw [if_neg hx, if_neg hc]

private lemma H3_coef1_sq_le {n m : ℕ} {A B S : Finset (Fin n)}
    (hAcard : A.card = m) (hBcard : B.card = m)
    (hSA : ∀ x, x ∈ S → x ∉ A) (hSB : ∀ x, x ∈ S → x ∉ B) (hAB : ∀ x, x ∈ A → x ∉ B) :
    ∑ e : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)},
      (((if (e.1.1 ∈ S ∧ e.1.2 ∈ B) ∨ (e.1.2 ∈ S ∧ e.1.1 ∈ B) then (1 : ℝ) else 0) -
        (if (e.1.1 ∈ S ∧ e.1.2 ∈ A) ∨ (e.1.2 ∈ S ∧ e.1.1 ∈ A) then 1 else 0)) ^ 2) ≤
    2 * (S.card : ℝ) * (m : ℝ) := by
  let E := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let F_c : Fin n → Fin n → ℝ := fun u v => if u ∈ S ∧ (v ∈ A ∨ v ∈ B) then 1 else 0
  have hFc_nn : ∀ x y : Fin n, 0 ≤ F_c x y := fun x y => by
    dsimp only [F_c]
    by_cases h : x ∈ S ∧ (y ∈ A ∨ y ∈ B)
    · rw [if_pos h]; norm_num
    · rw [if_neg h]
  have h1 : ∑ e : {p : Fin n × Fin n // p ∈ E},
      (((if (e.1.1 ∈ S ∧ e.1.2 ∈ B) ∨ (e.1.2 ∈ S ∧ e.1.1 ∈ B) then (1 : ℝ) else 0) -
        (if (e.1.1 ∈ S ∧ e.1.2 ∈ A) ∨ (e.1.2 ∈ S ∧ e.1.1 ∈ A) then 1 else 0)) ^ 2) ≤
      ∑ e ∈ E, (F_c e.1 e.2 + F_c e.2 e.1) := by
    rw [Finset.sum_coe_sort E (fun p : Fin n × Fin n =>
      ((if (p.1 ∈ S ∧ p.2 ∈ B) ∨ (p.2 ∈ S ∧ p.1 ∈ B) then (1 : ℝ) else 0) -
        (if (p.1 ∈ S ∧ p.2 ∈ A) ∨ (p.2 ∈ S ∧ p.1 ∈ A) then 1 else 0)) ^ 2)]
    refine Finset.sum_le_sum fun ⟨u, v⟩ _ => ?_
    have hnn_uv := hFc_nn u v
    have hnn_vu := hFc_nn v u
    by_cases huS : u ∈ S
    · have huA : u ∉ A := hSA u huS
      have huB : u ∉ B := hSB u huS
      by_cases hvB : v ∈ B
      · have hvA : v ∉ A := fun h => hAB v h hvB
        have hB1 : (u ∈ S ∧ v ∈ B) ∨ (v ∈ S ∧ u ∈ B) := Or.inl ⟨huS, hvB⟩
        have hA0 : ¬ ((u ∈ S ∧ v ∈ A) ∨ (v ∈ S ∧ u ∈ A)) :=
          fun h => h.elim (fun h1 => hvA h1.2) (fun h1 => huA h1.2)
        have hF1 : F_c u v = 1 := by dsimp only [F_c]; rw [if_pos ⟨huS, Or.inr hvB⟩]
        rw [if_pos hB1, if_neg hA0, hF1]; linarith
      · by_cases hvA : v ∈ A
        · have hB0 : ¬ ((u ∈ S ∧ v ∈ B) ∨ (v ∈ S ∧ u ∈ B)) :=
            fun h => h.elim (fun h1 => hvB h1.2) (fun h1 => huB h1.2)
          have hA1 : (u ∈ S ∧ v ∈ A) ∨ (v ∈ S ∧ u ∈ A) := Or.inl ⟨huS, hvA⟩
          have hF1 : F_c u v = 1 := by dsimp only [F_c]; rw [if_pos ⟨huS, Or.inl hvA⟩]
          rw [if_neg hB0, if_pos hA1, hF1]; norm_num at *; linarith
        · have hB0 : ¬ ((u ∈ S ∧ v ∈ B) ∨ (v ∈ S ∧ u ∈ B)) :=
            fun h => h.elim (fun h1 => hvB h1.2) (fun h1 => huB h1.2)
          have hA0 : ¬ ((u ∈ S ∧ v ∈ A) ∨ (v ∈ S ∧ u ∈ A)) :=
            fun h => h.elim (fun h1 => hvA h1.2) (fun h1 => huA h1.2)
          rw [if_neg hB0, if_neg hA0]; linarith
    · by_cases hvS : v ∈ S
      · have hvA : v ∉ A := hSA v hvS
        have hvB : v ∉ B := hSB v hvS
        by_cases huB : u ∈ B
        · have huA : u ∉ A := fun h => hAB u h huB
          have hB1 : (u ∈ S ∧ v ∈ B) ∨ (v ∈ S ∧ u ∈ B) := Or.inr ⟨hvS, huB⟩
          have hA0 : ¬ ((u ∈ S ∧ v ∈ A) ∨ (v ∈ S ∧ u ∈ A)) :=
            fun h => h.elim (fun h1 => hvA h1.2) (fun h1 => huA h1.2)
          have hF1 : F_c v u = 1 := by dsimp only [F_c]; rw [if_pos ⟨hvS, Or.inr huB⟩]
          rw [if_pos hB1, if_neg hA0, hF1]; linarith
        · by_cases huA : u ∈ A
          · have hB0 : ¬ ((u ∈ S ∧ v ∈ B) ∨ (v ∈ S ∧ u ∈ B)) :=
              fun h => h.elim (fun h1 => hvB h1.2) (fun h1 => huB h1.2)
            have hA1 : (u ∈ S ∧ v ∈ A) ∨ (v ∈ S ∧ u ∈ A) := Or.inr ⟨hvS, huA⟩
            have hF1 : F_c v u = 1 := by dsimp only [F_c]; rw [if_pos ⟨hvS, Or.inl huA⟩]
            rw [if_neg hB0, if_pos hA1, hF1]; norm_num at *; linarith
          · have hB0 : ¬ ((u ∈ S ∧ v ∈ B) ∨ (v ∈ S ∧ u ∈ B)) :=
              fun h => h.elim (fun h1 => hvB h1.2) (fun h1 => huB h1.2)
            have hA0 : ¬ ((u ∈ S ∧ v ∈ A) ∨ (v ∈ S ∧ u ∈ A)) :=
              fun h => h.elim (fun h1 => hvA h1.2) (fun h1 => huA h1.2)
            rw [if_neg hB0, if_neg hA0]; linarith
      · have hB0 : ¬ ((u ∈ S ∧ v ∈ B) ∨ (v ∈ S ∧ u ∈ B)) :=
          fun h => h.elim (fun h1 => huS h1.1) (fun h1 => hvS h1.1)
        have hA0 : ¬ ((u ∈ S ∧ v ∈ A) ∨ (v ∈ S ∧ u ∈ A)) :=
          fun h => h.elim (fun h1 => huS h1.1) (fun h1 => hvS h1.1)
        rw [if_neg hB0, if_neg hA0]; linarith
  rw [← sum_pair_lt_eq_double n F_c (fun u => by
    dsimp only [F_c]
    rw [if_neg (fun ⟨hS, hABu⟩ => hABu.elim (fun hA => hSA u hS hA) (fun hB => hSB u hS hB))])] at h1
  have h2 : (∑ u : Fin n, ∑ v : Fin n, F_c u v) ≤ 2 * (S.card : ℝ) * (m : ℝ) := by
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun u _ hu =>
      Finset.sum_eq_zero fun v _ => by dsimp only [F_c]; rw [if_neg (fun h => hu h.1)])]
    calc ∑ u ∈ S, ∑ v : Fin n, F_c u v
        ≤ ∑ _ ∈ S, ((A.card : ℝ) + (B.card : ℝ)) := by
          refine Finset.sum_le_sum fun u _ => ?_
          calc ∑ v : Fin n, F_c u v
              ≤ ∑ v : Fin n, ((if v ∈ A then (1 : ℝ) else 0) + (if v ∈ B then (1 : ℝ) else 0)) := by
                refine Finset.sum_le_sum fun v _ => ?_
                dsimp only [F_c]
                by_cases hvA : v ∈ A
                · rw [if_pos hvA]
                  have ha : (if u ∈ S ∧ (v ∈ A ∨ v ∈ B) then (1 : ℝ) else 0) ≤ 1 := by
                    by_cases h : u ∈ S ∧ (v ∈ A ∨ v ∈ B)
                    · rw [if_pos h]
                    · rw [if_neg h]; norm_num
                  have hb : (0 : ℝ) ≤ if v ∈ B then 1 else 0 := by
                    by_cases h : v ∈ B
                    · rw [if_pos h]; norm_num
                    · rw [if_neg h]
                  linarith
                · rw [if_neg hvA, zero_add]
                  by_cases hvB : v ∈ B
                  · rw [if_pos hvB]
                    by_cases h : u ∈ S ∧ (v ∈ A ∨ v ∈ B)
                    · rw [if_pos h]
                    · rw [if_neg h]; norm_num
                  · have hnot : ¬ (u ∈ S ∧ (v ∈ A ∨ v ∈ B)) := fun ⟨_, h⟩ => h.elim hvA hvB
                    rw [if_neg hnot, if_neg hvB]
            _ = (∑ v : Fin n, if v ∈ A then (1 : ℝ) else 0) +
                  (∑ v : Fin n, if v ∈ B then (1 : ℝ) else 0) := Finset.sum_add_distrib
            _ = (A.card : ℝ) + (B.card : ℝ) := by
                rw [sum_ite_mem_fin A, sum_ite_mem_fin B]
      _ = (S.card : ℝ) * ((m : ℝ) + (m : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, hAcard, hBcard]
      _ = 2 * (S.card : ℝ) * (m : ℝ) := by ring
  exact h1.trans h2

private lemma H3_coef2_sq_le {n m : ℕ} {A B : Finset (Fin n)}
    (hAcard : A.card = m) (hBcard : B.card = m) (hAB : ∀ x, x ∈ A → x ∉ B) :
    ∑ e : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)},
      (((if e.1.1 ∈ B ∧ e.1.2 ∈ B then (2 : ℝ) else 0) -
        (if e.1.1 ∈ A ∧ e.1.2 ∈ A then (2 : ℝ) else 0)) ^ 2) ≤
    4 * (m : ℝ) ^ 2 := by
  let E := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let F_c : Fin n → Fin n → ℝ := fun u v =>
    if (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B) then 2 else 0
  have hFc_nn : ∀ x y : Fin n, 0 ≤ F_c x y := fun x y => by
    dsimp only [F_c]
    by_cases h : (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B)
    · rw [if_pos h]; norm_num
    · rw [if_neg h]
  have h1 : ∑ e : {p : Fin n × Fin n // p ∈ E},
      (((if e.1.1 ∈ B ∧ e.1.2 ∈ B then (2 : ℝ) else 0) -
        (if e.1.1 ∈ A ∧ e.1.2 ∈ A then (2 : ℝ) else 0)) ^ 2) ≤
      ∑ e ∈ E, (F_c e.1 e.2 + F_c e.2 e.1) := by
    rw [Finset.sum_coe_sort E (fun p : Fin n × Fin n =>
      ((if p.1 ∈ B ∧ p.2 ∈ B then (2 : ℝ) else 0) -
        (if p.1 ∈ A ∧ p.2 ∈ A then (2 : ℝ) else 0)) ^ 2)]
    refine Finset.sum_le_sum fun ⟨u, v⟩ _ => ?_
    by_cases hA : u ∈ A ∧ v ∈ A
    · have hB : ¬ (u ∈ B ∧ v ∈ B) := fun h => hAB u hA.1 h.1
      have hF1 : F_c u v = 2 := by dsimp only [F_c]; rw [if_pos (Or.inl hA)]
      have hF2 : F_c v u = 2 := by dsimp only [F_c]; rw [if_pos (Or.inl ⟨hA.2, hA.1⟩)]
      rw [if_neg hB, if_pos hA, hF1, hF2]; norm_num
    · by_cases hB : u ∈ B ∧ v ∈ B
      · have hF1 : F_c u v = 2 := by dsimp only [F_c]; rw [if_pos (Or.inr hB)]
        have hF2 : F_c v u = 2 := by dsimp only [F_c]; rw [if_pos (Or.inr ⟨hB.2, hB.1⟩)]
        rw [if_pos hB, if_neg hA, hF1, hF2]; norm_num
      · have h1 := hFc_nn u v
        have h2 := hFc_nn v u
        rw [if_neg hB, if_neg hA]; linarith
  have h2 : ∑ e ∈ E, (F_c e.1 e.2 + F_c e.2 e.1) ≤ ∑ u : Fin n, ∑ v : Fin n, F_c u v := by
    let F0 : Fin n → Fin n → ℝ := fun u v => if u = v then 0 else F_c u v
    have hlt : ∑ e ∈ E, (F_c e.1 e.2 + F_c e.2 e.1) = ∑ u : Fin n, ∑ v : Fin n, F0 u v := by
      rw [sum_pair_lt_eq_double n F0 (fun u => by dsimp only [F0]; rw [if_pos rfl])]
      refine Finset.sum_congr rfl fun e he => ?_
      have hne : e.1 ≠ e.2 := ((Finset.mem_filter.mp he).2).ne
      dsimp only [F0]
      rw [if_neg hne, if_neg hne.symm]
    rw [hlt]
    refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
    dsimp only [F0]
    by_cases huv : u = v
    · rw [if_pos huv]; exact hFc_nn u v
    · rw [if_neg huv]
  have h3 : (∑ u : Fin n, ∑ v : Fin n, F_c u v) = 4 * (m : ℝ) ^ 2 := by
    have hsplit : ∀ u v : Fin n, F_c u v =
        (if u ∈ A ∧ v ∈ A then (2 : ℝ) else 0) + (if u ∈ B ∧ v ∈ B then (2 : ℝ) else 0) := by
      intro u v
      dsimp only [F_c]
      by_cases hA : u ∈ A ∧ v ∈ A
      · have hB : ¬ (u ∈ B ∧ v ∈ B) := fun h => hAB u hA.1 h.1
        rw [if_pos (Or.inl hA), if_pos hA, if_neg hB, add_zero]
      · by_cases hB : u ∈ B ∧ v ∈ B
        · rw [if_pos (Or.inr hB), if_neg hA, if_pos hB, zero_add]
        · rw [if_neg (fun h => h.elim hA hB), if_neg hA, if_neg hB, add_zero]
    simp_rw [hsplit, Finset.sum_add_distrib]
    have hsA : (∑ u : Fin n, ∑ v : Fin n, if u ∈ A ∧ v ∈ A then (2 : ℝ) else 0) =
        2 * (m : ℝ) ^ 2 := by
      rw [← Finset.sum_subset (Finset.subset_univ A) (fun u _ hu =>
        Finset.sum_eq_zero fun v _ => by rw [if_neg (fun h => hu h.1)])]
      calc ∑ u ∈ A, ∑ v : Fin n, (if u ∈ A ∧ v ∈ A then (2 : ℝ) else 0)
          = ∑ u ∈ A, ∑ _ ∈ A, (2 : ℝ) := by
            refine Finset.sum_congr rfl fun u hu => ?_
            rw [← Finset.sum_subset (Finset.subset_univ A) (fun v _ hv => by rw [if_neg (fun h => hv h.2)])]
            refine Finset.sum_congr rfl fun v hv => by rw [if_pos ⟨hu, hv⟩]
        _ = 2 * (m : ℝ) ^ 2 := by
            rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hAcard]; ring
    have hsB : (∑ u : Fin n, ∑ v : Fin n, if u ∈ B ∧ v ∈ B then (2 : ℝ) else 0) =
        2 * (m : ℝ) ^ 2 := by
      rw [← Finset.sum_subset (Finset.subset_univ B) (fun u _ hu =>
        Finset.sum_eq_zero fun v _ => by rw [if_neg (fun h => hu h.1)])]
      calc ∑ u ∈ B, ∑ v : Fin n, (if u ∈ B ∧ v ∈ B then (2 : ℝ) else 0)
          = ∑ u ∈ B, ∑ _ ∈ B, (2 : ℝ) := by
            refine Finset.sum_congr rfl fun u hu => ?_
            rw [← Finset.sum_subset (Finset.subset_univ B) (fun v _ hv => by rw [if_neg (fun h => hv h.2)])]
            refine Finset.sum_congr rfl fun v hv => by rw [if_pos ⟨hu, hv⟩]
        _ = 2 * (m : ℝ) ^ 2 := by
            rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hBcard]; ring
    rw [hsA, hsB]; ring
  exact h1.trans (h2.trans_eq h3)

private lemma H3_struct_pt {n k m : ℕ} {c₂ : ℝ} (hc₂ : 0 < c₂) (hn_pos : (0 : ℝ) < (n : ℝ))
    (hm5 : 5 * m ≤ k) (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) (hUk : U.card = k)
    (d : ℕ) (hd : ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d)
    (a b : Fin n) (hab : a < b) (hspan : c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ))
    (hUa : m ≤ (U.filter (· ≤ a)).card) (hUb : m ≤ (U.filter (b ≤ ·)).card) :
    (∃ p ∈ ((Finset.univ : Finset (Fin n)).powersetCard m ×ˢ
        (Finset.univ : Finset (Fin n)).powersetCard m ×ˢ
        (Finset.univ : Finset (Fin n)).powersetCard (k - 2 * m)).filter
        (fun p : Finset (Fin n) × Finset (Fin n) × Finset (Fin n) =>
          Disjoint p.1 p.2.1 ∧ Disjoint p.2.2 (p.1 ∪ p.2.1) ∧
          ∀ u ∈ p.1, ∀ v ∈ p.2.1, c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ ((v : ℕ) : ℝ) - ((u : ℕ) : ℝ)),
      (∑ e : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)},
        ((if (e.1.1 ∈ p.2.2 ∧ e.1.2 ∈ p.2.1) ∨ (e.1.2 ∈ p.2.2 ∧ e.1.1 ∈ p.2.1) then (1 : ℝ) else 0) -
          (if (e.1.1 ∈ p.2.2 ∧ e.1.2 ∈ p.1) ∨ (e.1.2 ∈ p.2.2 ∧ e.1.1 ∈ p.1) then 1 else 0)) *
        (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0)) ≤
        c₂ * ((p.2.2.card : ℕ) : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))) ∨
    (∃ p ∈ ((Finset.univ : Finset (Fin n)).powersetCard m ×ˢ
        (Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun p : Finset (Fin n) × Finset (Fin n) => Disjoint p.1 p.2 ∧
          ∀ u ∈ p.1, ∀ v ∈ p.2, c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ ((v : ℕ) : ℝ) - ((u : ℕ) : ℝ)),
      (∑ e : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)},
        ((if e.1.1 ∈ p.2 ∧ e.1.2 ∈ p.2 then (2 : ℝ) else 0) -
          (if e.1.1 ∈ p.1 ∧ e.1.2 ∈ p.1 then (2 : ℝ) else 0)) *
        (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0)) ≤
        -(c₂ * (k : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (32 * (n : ℝ)))) := by
  let E := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let coef₁ (A B S : Finset (Fin n)) (e : Fin n × Fin n) : ℝ :=
    (if (e.1 ∈ S ∧ e.2 ∈ B) ∨ (e.2 ∈ S ∧ e.1 ∈ B) then 1 else 0) -
    (if (e.1 ∈ S ∧ e.2 ∈ A) ∨ (e.2 ∈ S ∧ e.1 ∈ A) then 1 else 0)
  let coef₂ (A B : Finset (Fin n)) (e : Fin n × Fin n) : ℝ :=
    (if e.1 ∈ B ∧ e.2 ∈ B then (2 : ℝ) else 0) -
    (if e.1 ∈ A ∧ e.2 ∈ A then (2 : ℝ) else 0)
  let T₀ : ℝ := c₂ * (k : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (32 * (n : ℝ))
  let BadTriples := ((Finset.univ : Finset (Fin n)).powersetCard m ×ˢ
      (Finset.univ : Finset (Fin n)).powersetCard m ×ˢ
      (Finset.univ : Finset (Fin n)).powersetCard (k - 2 * m)).filter
      (fun p : Finset (Fin n) × Finset (Fin n) × Finset (Fin n) =>
        Disjoint p.1 p.2.1 ∧ Disjoint p.2.2 (p.1 ∪ p.2.1) ∧
        ∀ u ∈ p.1, ∀ v ∈ p.2.1, c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ ((v : ℕ) : ℝ) - ((u : ℕ) : ℝ))
  let BadPairs := ((Finset.univ : Finset (Fin n)).powersetCard m ×ˢ
      (Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun p : Finset (Fin n) × Finset (Fin n) => Disjoint p.1 p.2 ∧
        ∀ u ∈ p.1, ∀ v ∈ p.2, c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ ((v : ℕ) : ℝ) - ((u : ℕ) : ℝ))
  let Z1 (A B S : Finset (Fin n)) : ℝ :=
    ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₁ A B S e.1 * (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0)
  let Z2 (A B : Finset (Fin n)) : ℝ :=
    ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₂ A B e.1 * (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0)
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hUa
  obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hUb
  let S := U \ (A ∪ B)
  have hAU : A ⊆ U := hAsub.trans (Finset.filter_subset _ _)
  have hBU : B ⊆ U := hBsub.trans (Finset.filter_subset _ _)
  have hdisjAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have hxa : x ≤ a := (Finset.mem_filter.mp (hAsub hxA)).2
    have hbx : b ≤ x := (Finset.mem_filter.mp (hBsub hxB)).2
    exact absurd (le_trans hbx hxa) (not_le_of_gt hab)
  have hdisjS : Disjoint S (A ∪ B) := Finset.sdiff_disjoint
  have hABU : A ∪ B ⊆ U := Finset.union_subset hAU hBU
  have hScard : S.card = k - 2 * m := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hABU, Finset.card_union_of_disjoint hdisjAB, hUk, hAcard, hBcard]
    omega
  have hgap : ∀ u ∈ A, ∀ v ∈ B, c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ ((v : ℕ) : ℝ) - ((u : ℕ) : ℝ) := by
    intro u hu v hv
    have hua : ((u : ℕ) : ℝ) ≤ ((a : ℕ) : ℝ) := by exact_mod_cast (Finset.mem_filter.mp (hAsub hu)).2
    have hbv : ((b : ℕ) : ℝ) ≤ ((v : ℕ) : ℝ) := by exact_mod_cast (Finset.mem_filter.mp (hBsub hv)).2
    linarith
  have hsum_zero : Z1 A B S + Z2 A B = 0 := by
    have hdeg_diff :
        (∑ v ∈ B, ((U.filter (fun w => G.Adj v w)).card : ℝ)) -
        (∑ u ∈ A, ((U.filter (fun w => G.Adj u w)).card : ℝ)) = 0 := by
      have hB_eq : ∑ v ∈ B, ((U.filter (fun w => G.Adj v w)).card : ℝ) = (m : ℝ) * (d : ℝ) := by
        calc ∑ v ∈ B, ((U.filter (fun w => G.Adj v w)).card : ℝ)
            = ∑ _ ∈ B, (d : ℝ) := Finset.sum_congr rfl fun v hv => by exact_mod_cast hd v (hBU hv)
          _ = (B.card : ℝ) * (d : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ = (m : ℝ) * (d : ℝ) := by rw [hBcard]
      have hA_eq : ∑ u ∈ A, ((U.filter (fun w => G.Adj u w)).card : ℝ) = (m : ℝ) * (d : ℝ) := by
        calc ∑ u ∈ A, ((U.filter (fun w => G.Adj u w)).card : ℝ)
            = ∑ _ ∈ A, (d : ℝ) := Finset.sum_congr rfl fun u hu => by exact_mod_cast hd u (hAU hu)
          _ = (A.card : ℝ) * (d : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ = (m : ℝ) * (d : ℝ) := by rw [hAcard]
      linarith
    let F : Fin n → Fin n → ℝ := fun u v =>
      ((if u ∈ B ∧ v ∈ U then (1 : ℝ) else 0) - (if u ∈ A ∧ v ∈ U then 1 else 0)) *
      (if G.Adj u v then 1 else 0)
    have hF_sum : (∑ u : Fin n, ∑ v : Fin n, F u v) =
        (∑ v ∈ B, ((U.filter (fun w => G.Adj v w)).card : ℝ)) -
        (∑ u ∈ A, ((U.filter (fun w => G.Adj u w)).card : ℝ)) := by
      have h1 : (∑ u : Fin n, ∑ v : Fin n,
          (if u ∈ B ∧ v ∈ U then (1 : ℝ) else 0) * (if G.Adj u v then 1 else 0)) =
          ∑ v ∈ B, ((U.filter (fun w => G.Adj v w)).card : ℝ) := by
        calc (∑ u : Fin n, ∑ v : Fin n,
              (if u ∈ B ∧ v ∈ U then (1 : ℝ) else 0) * (if G.Adj u v then 1 else 0))
            = ∑ v ∈ B, ∑ w ∈ U, (if G.Adj v w then (1 : ℝ) else 0) := by
              rw [← Finset.sum_subset (Finset.subset_univ B) (fun u _ hu =>
                Finset.sum_eq_zero fun v _ => by rw [if_neg (fun h => hu h.1), zero_mul])]
              refine Finset.sum_congr rfl fun v hv => ?_
              rw [← Finset.sum_subset (Finset.subset_univ U) (fun w _ hw => by
                rw [if_neg (fun h => hw h.2), zero_mul])]
              refine Finset.sum_congr rfl fun w hw => by rw [if_pos ⟨hv, hw⟩, one_mul]
          _ = ∑ v ∈ B, ((U.filter (fun w => G.Adj v w)).card : ℝ) := by
              refine Finset.sum_congr rfl fun v _ => ?_
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      have h2 : (∑ u : Fin n, ∑ v : Fin n,
          (if u ∈ A ∧ v ∈ U then (1 : ℝ) else 0) * (if G.Adj u v then 1 else 0)) =
          ∑ u ∈ A, ((U.filter (fun w => G.Adj u w)).card : ℝ) := by
        calc (∑ u : Fin n, ∑ v : Fin n,
              (if u ∈ A ∧ v ∈ U then (1 : ℝ) else 0) * (if G.Adj u v then 1 else 0))
            = ∑ u ∈ A, ∑ w ∈ U, (if G.Adj u w then (1 : ℝ) else 0) := by
              rw [← Finset.sum_subset (Finset.subset_univ A) (fun u _ hu =>
                Finset.sum_eq_zero fun v _ => by rw [if_neg (fun h => hu h.1), zero_mul])]
              refine Finset.sum_congr rfl fun u hu => ?_
              rw [← Finset.sum_subset (Finset.subset_univ U) (fun w _ hw => by
                rw [if_neg (fun h => hw h.2), zero_mul])]
              refine Finset.sum_congr rfl fun w hw => by rw [if_pos ⟨hu, hw⟩, one_mul]
          _ = ∑ u ∈ A, ((U.filter (fun w => G.Adj u w)).card : ℝ) := by
              refine Finset.sum_congr rfl fun u _ => ?_
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      simp_rw [F, sub_mul, Finset.sum_sub_distrib]
      rw [h1, h2]
    have hF_diag : ∀ u : Fin n, F u u = 0 := fun u => by
      dsimp only [F]; rw [if_neg (G.loopless.irrefl u), mul_zero]
    have hpair := sum_pair_lt_eq_double n F hF_diag
    have hZ_eq : (∑ e ∈ E, (F e.1 e.2 + F e.2 e.1)) = Z1 A B S + Z2 A B := by
      dsimp only [Z1, Z2]
      rw [← Finset.sum_coe_sort E, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ⟨⟨u, v⟩, _⟩ _ => ?_
      have hSA : ∀ x, ¬ (x ∈ S ∧ x ∈ A) := fun x ⟨hxS, hxA⟩ =>
        (Finset.disjoint_left.mp hdisjS hxS) (Finset.mem_union_left B hxA)
      have hSB : ∀ x, ¬ (x ∈ S ∧ x ∈ B) := fun x ⟨hxS, hxB⟩ =>
        (Finset.disjoint_left.mp hdisjS hxS) (Finset.mem_union_right A hxB)
      have hAB_n : ∀ x, ¬ (x ∈ A ∧ x ∈ B) := fun x ⟨hxA, hxB⟩ =>
        Finset.disjoint_left.mp hdisjAB hxA hxB
      have hU_ind : ∀ x : Fin n,
          (if x ∈ U then (1 : ℝ) else 0) =
            (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0) + (if x ∈ S then 1 else 0) := by
        intro x
        by_cases hxA : x ∈ A
        · have hxU : x ∈ U := hAU hxA
          have hxB : x ∉ B := fun h => hAB_n x ⟨hxA, h⟩
          have hxS : x ∉ S := fun h => hSA x ⟨h, hxA⟩
          rw [if_pos hxU, if_pos hxA, if_neg hxB, if_neg hxS]; ring
        · by_cases hxB : x ∈ B
          · have hxU : x ∈ U := hBU hxB
            have hxS : x ∉ S := fun h => hSB x ⟨h, hxB⟩
            rw [if_pos hxU, if_neg hxA, if_pos hxB, if_neg hxS]; ring
          · by_cases hxU : x ∈ U
            · have hxS : x ∈ S := Finset.mem_sdiff.mpr ⟨hxU, Finset.notMem_union.mpr ⟨hxA, hxB⟩⟩
              rw [if_pos hxU, if_neg hxA, if_neg hxB, if_pos hxS]; ring
            · have hxS : x ∉ S := fun h => hxU (Finset.sdiff_subset h)
              rw [if_neg hxU, if_neg hxA, if_neg hxB, if_neg hxS]; ring
      dsimp only [F, coef₁, coef₂]
      by_cases hadj_uv : G.Adj u v
      · have hadj_vu : G.Adj v u := (G.adj_comm u v).mp hadj_uv
        rw [if_pos hadj_uv, if_pos hadj_vu, mul_one, mul_one, mul_one, mul_one]
        have h1B : (if (u ∈ S ∧ v ∈ B) ∨ (v ∈ S ∧ u ∈ B) then (1 : ℝ) else 0) =
            (if u ∈ S then 1 else 0) * (if v ∈ B then 1 else 0) +
            (if v ∈ S then 1 else 0) * (if u ∈ B then 1 else 0) := by
          rw [ind_or_disj _ _ (fun ⟨h1, h2⟩ => hSB u ⟨h1.1, h2.2⟩), ind_and, ind_and]
        have h1A : (if (u ∈ S ∧ v ∈ A) ∨ (v ∈ S ∧ u ∈ A) then (1 : ℝ) else 0) =
            (if u ∈ S then 1 else 0) * (if v ∈ A then 1 else 0) +
            (if v ∈ S then 1 else 0) * (if u ∈ A then 1 else 0) := by
          rw [ind_or_disj _ _ (fun ⟨h1, h2⟩ => hSA u ⟨h1.1, h2.2⟩), ind_and, ind_and]
        have h2B : (if u ∈ B ∧ v ∈ B then (2 : ℝ) else 0) =
            2 * ((if u ∈ B then (1 : ℝ) else 0) * (if v ∈ B then 1 else 0)) := by
          by_cases hu : u ∈ B <;> by_cases hv : v ∈ B
          · rw [if_pos ⟨hu, hv⟩, if_pos hu, if_pos hv]; norm_num
          · rw [if_neg (fun h => hv h.2), if_pos hu, if_neg hv]; norm_num
          · rw [if_neg (fun h => hu h.1), if_neg hu, if_pos hv]; norm_num
          · rw [if_neg (fun h => hu h.1), if_neg hu, if_neg hv]; norm_num
        have h2A : (if u ∈ A ∧ v ∈ A then (2 : ℝ) else 0) =
            2 * ((if u ∈ A then (1 : ℝ) else 0) * (if v ∈ A then 1 else 0)) := by
          by_cases hu : u ∈ A <;> by_cases hv : v ∈ A
          · rw [if_pos ⟨hu, hv⟩, if_pos hu, if_pos hv]; norm_num
          · rw [if_neg (fun h => hv h.2), if_pos hu, if_neg hv]; norm_num
          · rw [if_neg (fun h => hu h.1), if_neg hu, if_pos hv]; norm_num
          · rw [if_neg (fun h => hu h.1), if_neg hu, if_neg hv]; norm_num
        rw [ind_and (u ∈ B) (v ∈ U), ind_and (u ∈ A) (v ∈ U),
          ind_and (v ∈ B) (u ∈ U), ind_and (v ∈ A) (u ∈ U),
          hU_ind v, hU_ind u, h1B, h1A, h2B, h2A]
        ring
      · have hadj_vu : ¬ G.Adj v u := fun h => hadj_uv ((G.adj_comm u v).mpr h)
        rw [if_neg hadj_uv, if_neg hadj_vu]; ring
    linarith
  have hS_ge_half : (k : ℝ) / 2 ≤ (S.card : ℝ) := by
    have : k ≤ 2 * S.card := by omega
    have : (k : ℝ) ≤ 2 * (S.card : ℝ) := by exact_mod_cast this
    linarith
  set T := c₂ * (S.card : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))
  have hT0_le_T : T₀ ≤ T := by
    dsimp only [T₀, T]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc c₂ * (k : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) * (16 * (n : ℝ))
        = c₂ * ((k : ℝ) / 2) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) * (32 * (n : ℝ)) := by ring
      _ ≤ c₂ * (S.card : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) * (32 * (n : ℝ)) := by
          gcongr
  by_cases hZ1 : Z1 A B S ≤ T
  · left
    refine ⟨(A, B, S), ?_, hZ1⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard]
    exact ⟨⟨⟨Finset.subset_univ _, hAcard⟩, ⟨Finset.subset_univ _, hBcard⟩,
      ⟨Finset.subset_univ _, hScard⟩⟩, hdisjAB, hdisjS, hgap⟩
  · right
    have hZ2 : Z2 A B ≤ -T₀ := by linarith
    refine ⟨(A, B), ?_, hZ2⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard]
    exact ⟨⟨⟨Finset.subset_univ _, hAcard⟩, ⟨Finset.subset_univ _, hBcard⟩⟩, hdisjAB, hgap⟩

private lemma H3_bound1_pt {n k m : ℕ} {c₂ C : ℝ}
    (hc₂ : 0 < c₂) (hC : 0 < C) (hc2C4 : 4 ≤ c₂ ^ 2 * C ^ 4 / 24576)
    (hn_pos : (0 : ℝ) < (n : ℝ)) (hk_pos : (0 : ℝ) < (k : ℝ))
    (hm1 : 1 ≤ m) (hm5 : 5 * m ≤ k) (hm_pos : (0 : ℝ) < (m : ℝ))
    (hlogn_ge1 : 1 ≤ Real.log (n : ℝ)) (hlogn_pos : 0 < Real.log (n : ℝ))
    (hk_lb : C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) ≤ (k : ℝ))
    (hm_lb : (k : ℝ) / (6 * Real.log (n : ℝ)) ≤ (m : ℝ))
    {A B S : Finset (Fin n)} (hAcard : A.card = m) (hBcard : B.card = m) (hScard : S.card = k - 2 * m)
    (hdisjAB : Disjoint A B) (hdisjS : Disjoint S (A ∪ B))
    (hgap : ∀ u ∈ A, ∀ v ∈ B, c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ ((v : ℕ) : ℝ) - ((u : ℕ) : ℝ)) :
    (∑ G : SimpleGraph (Fin n),
      (if (∑ e : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)},
            ((if (e.1.1 ∈ S ∧ e.1.2 ∈ B) ∨ (e.1.2 ∈ S ∧ e.1.1 ∈ B) then (1 : ℝ) else 0) -
              (if (e.1.1 ∈ S ∧ e.1.2 ∈ A) ∨ (e.1.2 ∈ S ∧ e.1.1 ∈ A) then 1 else 0)) *
            (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0)) ≤
          c₂ * ((S.card : ℕ) : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))
        then (1 : ℝ) else 0) *
      (∏ e : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)},
        if G.Adj e.1.1 e.1.2
        then (1 / 4 + (e.1.1 : ℝ) / (2 * (n : ℝ))) * (1 / 4 + (e.1.2 : ℝ) / (2 * (n : ℝ)))
        else 1 - (1 / 4 + (e.1.1 : ℝ) / (2 * (n : ℝ))) * (1 / 4 + (e.1.2 : ℝ) / (2 * (n : ℝ))))) ≤
    Real.exp (-4 * (k : ℝ) * Real.log (n : ℝ)) := by
  let E := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let p_vert : Fin n → ℝ := fun u => 1 / 4 + (u : ℝ) / (2 * (n : ℝ))
  have hp_vert : ∀ u : Fin n, 1 / 4 ≤ p_vert u ∧ p_vert u ≤ 3 / 4 := by
    intro u
    have hu0 : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg u
    have hu1 : (u : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr u.isLt.le
    constructor
    · have : 0 ≤ (u : ℝ) / (2 * (n : ℝ)) := by positivity
      dsimp only [p_vert]; linarith
    · have : (u : ℝ) / (2 * (n : ℝ)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      dsimp only [p_vert]; linarith
  let q : {p : Fin n × Fin n // p ∈ E} → ℝ := fun e => p_vert e.1.1 * p_vert e.1.2
  have hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1 := by
    intro e
    obtain ⟨_, _⟩ := hp_vert e.1.1
    obtain ⟨_, _⟩ := hp_vert e.1.2
    exact ⟨by positivity, by nlinarith⟩
  let coef₁ : Fin n × Fin n → ℝ := fun e =>
    (if (e.1 ∈ S ∧ e.2 ∈ B) ∨ (e.2 ∈ S ∧ e.1 ∈ B) then 1 else 0) -
    (if (e.1 ∈ S ∧ e.2 ∈ A) ∨ (e.2 ∈ S ∧ e.1 ∈ A) then 1 else 0)
  have hSA : ∀ x, x ∈ S → x ∉ A := fun x hx => by
    have := Finset.disjoint_left.mp hdisjS hx
    exact fun h => this (Finset.mem_union_left B h)
  have hSB : ∀ x, x ∈ S → x ∉ B := fun x hx => by
    have := Finset.disjoint_left.mp hdisjS hx
    exact fun h => this (Finset.mem_union_right A h)
  have hAB : ∀ x, x ∈ A → x ∉ B := fun x hx => Finset.disjoint_left.mp hdisjAB hx
  let F_mu : Fin n → Fin n → ℝ := fun u v =>
    ((if u ∈ S ∧ v ∈ B then (1 : ℝ) else 0) - (if u ∈ S ∧ v ∈ A then 1 else 0)) * (p_vert u * p_vert v)
  have hmu_eq : (∑ e : {p : Fin n × Fin n // p ∈ E}, coef₁ e.1 * q e) =
      ∑ w ∈ S, p_vert w * ((∑ v ∈ B, p_vert v) - (∑ u ∈ A, p_vert u)) := by
    have h1 : (∑ e : {p : Fin n × Fin n // p ∈ E}, coef₁ e.1 * q e) =
        ∑ e ∈ E, (F_mu e.1 e.2 + F_mu e.2 e.1) := by
      rw [Finset.sum_coe_sort E (fun p : Fin n × Fin n => coef₁ p * (p_vert p.1 * p_vert p.2))]
      refine Finset.sum_congr rfl fun ⟨u, v⟩ _ => ?_
      dsimp only [F_mu, coef₁, q]
      have h1B : (if (u ∈ S ∧ v ∈ B) ∨ (v ∈ S ∧ u ∈ B) then (1 : ℝ) else 0) =
          (if u ∈ S then 1 else 0) * (if v ∈ B then 1 else 0) +
          (if v ∈ S then 1 else 0) * (if u ∈ B then 1 else 0) := by
        rw [ind_or_disj _ _ (fun ⟨h1, h2⟩ => hSB u h1.1 h2.2), ind_and, ind_and]
      have h1A : (if (u ∈ S ∧ v ∈ A) ∨ (v ∈ S ∧ u ∈ A) then (1 : ℝ) else 0) =
          (if u ∈ S then 1 else 0) * (if v ∈ A then 1 else 0) +
          (if v ∈ S then 1 else 0) * (if u ∈ A then 1 else 0) := by
        rw [ind_or_disj _ _ (fun ⟨h1, h2⟩ => hSA u h1.1 h2.2), ind_and, ind_and]
      rw [h1B, h1A, ind_and (u ∈ S) (v ∈ B), ind_and (u ∈ S) (v ∈ A),
        ind_and (v ∈ S) (u ∈ B), ind_and (v ∈ S) (u ∈ A)]
      ring
    rw [h1, ← sum_pair_lt_eq_double n F_mu (fun u => by
      dsimp only [F_mu]
      rw [if_neg (fun ⟨h1, h2⟩ => hSB u h1 h2), if_neg (fun ⟨h1, h2⟩ => hSA u h1 h2)]
      ring)]
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun w _ hw =>
      Finset.sum_eq_zero fun v _ => by
        dsimp only [F_mu]; rw [if_neg (fun h => hw h.1), if_neg (fun h => hw h.1), sub_self, zero_mul])]
    refine Finset.sum_congr rfl fun w hw => ?_
    have hsB : ∑ v : Fin n, (if w ∈ S ∧ v ∈ B then (1 : ℝ) else 0) * (p_vert w * p_vert v) =
        p_vert w * ∑ v ∈ B, p_vert v := by
      rw [← Finset.sum_subset (Finset.subset_univ B) (fun v _ hv => by
        rw [if_neg (fun h => hv h.2), zero_mul])]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v hv => by rw [if_pos ⟨hw, hv⟩, one_mul]
    have hsA : ∑ v : Fin n, (if w ∈ S ∧ v ∈ A then (1 : ℝ) else 0) * (p_vert w * p_vert v) =
        p_vert w * ∑ v ∈ A, p_vert v := by
      rw [← Finset.sum_subset (Finset.subset_univ A) (fun v _ hv => by
        rw [if_neg (fun h => hv h.2), zero_mul])]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v hv => by rw [if_pos ⟨hw, hv⟩, one_mul]
    simp_rw [F_mu, sub_mul, Finset.sum_sub_distrib, hsB, hsA, mul_sub]
  have hBA_diff : (m : ℝ) * (c₂ * (k : ℝ) ^ (3 / 2 : ℝ) / (2 * (n : ℝ))) ≤
      (∑ v ∈ B, p_vert v) - (∑ u ∈ A, p_vert u) := by
    let embA := A.orderEmbOfFin hAcard
    let embB := B.orderEmbOfFin hBcard
    rw [sum_orderEmb A hAcard p_vert, sum_orderEmb B hBcard p_vert, ← Finset.sum_sub_distrib]
    calc (m : ℝ) * (c₂ * (k : ℝ) ^ (3 / 2 : ℝ) / (2 * (n : ℝ)))
        = ∑ _ : Fin m, (c₂ * (k : ℝ) ^ (3 / 2 : ℝ) / (2 * (n : ℝ))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ i : Fin m, (p_vert (embB i) - p_vert (embA i)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hiA : embA i ∈ A := by
            have : embA i ∈ Set.range embA := Set.mem_range_self _
            rwa [Finset.range_orderEmbOfFin] at this
          have hiB : embB i ∈ B := by
            have : embB i ∈ Set.range embB := Set.mem_range_self _
            rwa [Finset.range_orderEmbOfFin] at this
          have hdiff : p_vert (embB i) - p_vert (embA i) =
              (((embB i : ℕ) : ℝ) - ((embA i : ℕ) : ℝ)) / (2 * (n : ℝ)) := by
            dsimp only [p_vert]; ring
          rw [hdiff]
          exact div_le_div_of_nonneg_right (hgap (embA i) hiA (embB i) hiB) (by positivity)
  have hmu_lb : 2 * (c₂ * (S.card : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))) ≤
      ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₁ e.1 * q e := by
    rw [hmu_eq]
    have hS_term : ∀ w ∈ S,
        (1 / 4 : ℝ) * ((m : ℝ) * (c₂ * (k : ℝ) ^ (3 / 2 : ℝ) / (2 * (n : ℝ)))) ≤
        p_vert w * ((∑ v ∈ B, p_vert v) - (∑ u ∈ A, p_vert u)) :=
      fun w _ => mul_le_mul (hp_vert w).1 hBA_diff (by positivity) (by positivity)
    calc 2 * (c₂ * (S.card : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ)))
        = (S.card : ℝ) * ((1 / 4 : ℝ) * ((m : ℝ) * (c₂ * (k : ℝ) ^ (3 / 2 : ℝ) / (2 * (n : ℝ))))) := by ring
      _ = ∑ _ ∈ S, ((1 / 4 : ℝ) * ((m : ℝ) * (c₂ * (k : ℝ) ^ (3 / 2 : ℝ) / (2 * (n : ℝ))))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ w ∈ S, p_vert w * ((∑ v ∈ B, p_vert v) - (∑ u ∈ A, p_vert u)) :=
          Finset.sum_le_sum hS_term
  have hmu_ub : ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₁ e.1 * q e ≤
      2 * (S.card : ℝ) * (m : ℝ) := by
    rw [hmu_eq]
    have hB_ub : ∑ v ∈ B, p_vert v ≤ (m : ℝ) := by
      calc ∑ v ∈ B, p_vert v ≤ ∑ _ ∈ B, (1 : ℝ) :=
            Finset.sum_le_sum fun v _ => (hp_vert v).2.trans (by norm_num)
        _ = (m : ℝ) := by rw [Finset.sum_const, hBcard, nsmul_eq_mul, mul_one]
    have hA_lb : 0 ≤ ∑ u ∈ A, p_vert u :=
      Finset.sum_nonneg fun u _ => by linarith [(hp_vert u).1]
    calc ∑ w ∈ S, p_vert w * ((∑ v ∈ B, p_vert v) - (∑ u ∈ A, p_vert u))
        ≤ ∑ _ ∈ S, (1 : ℝ) * (m : ℝ) := by
          refine Finset.sum_le_sum fun w _ => ?_
          refine mul_le_mul ((hp_vert w).2.trans (by norm_num)) (by linarith) ?_ (by norm_num)
          exact le_trans (by positivity) hBA_diff
      _ ≤ 2 * (S.card : ℝ) * (m : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          nlinarith
  have hC2_ub : ∑ e : {p : Fin n × Fin n // p ∈ E}, (coef₁ e.1) ^ 2 ≤
      2 * (S.card : ℝ) * (m : ℝ) :=
    H3_coef1_sq_le hAcard hBcard hSA hSB hAB
  have hcoef1 : ∀ e : {p : Fin n × Fin n // p ∈ E}, |coef₁ e.1| ≤ 2 := by
    intro e; dsimp only [coef₁]; split_ifs <;> norm_num
  set T := c₂ * (S.card : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))
  have hS1 : 1 ≤ S.card := by omega
  have hS_pos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hS1
  have hT_pos : 0 < T := by positivity
  have hT_le_Sm : T ≤ (S.card : ℝ) * (m : ℝ) := by
    have : 2 * T ≤ 2 * (S.card : ℝ) * (m : ℝ) := hmu_lb.trans hmu_ub
    linarith
  set t : ℝ := T / (4 * (S.card : ℝ) * (m : ℝ))
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 / 2 := by
    dsimp only [t]
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hch := chernoff_edge_sum n q hq (fun e => coef₁ e.1) hcoef1 ht0 ht1 T
  have hexp_le : t * (T - ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₁ e.1 * q e) +
      t ^ 2 * ∑ e : {p : Fin n × Fin n // p ∈ E}, (coef₁ e.1) ^ 2 ≤
      -4 * (k : ℝ) * Real.log (n : ℝ) := by
    have h1 : t * (T - ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₁ e.1 * q e) +
        t ^ 2 * ∑ e : {p : Fin n × Fin n // p ∈ E}, (coef₁ e.1) ^ 2 ≤
        t * (-T) + t ^ 2 * (2 * (S.card : ℝ) * (m : ℝ)) := by
      refine add_le_add ?_ (mul_le_mul_of_nonneg_left hC2_ub (sq_nonneg t))
      refine mul_le_mul_of_nonneg_left (by linarith) ht0
    have h2 : t * (-T) + t ^ 2 * (2 * (S.card : ℝ) * (m : ℝ)) =
        -(T ^ 2 / (8 * (S.card : ℝ) * (m : ℝ))) := by
      dsimp only [t]; field_simp [hS_pos.ne', hm_pos.ne']; ring
    have hS_half : (k : ℝ) / 2 ≤ (S.card : ℝ) := by
      have : k ≤ 2 * S.card := by omega
      have : (k : ℝ) ≤ 2 * (S.card : ℝ) := by exact_mod_cast this
      linarith
    have h3 : 4 * (k : ℝ) * Real.log (n : ℝ) ≤ T ^ 2 / (8 * (S.card : ℝ) * (m : ℝ)) := by
      have hT2 : T ^ 2 / (8 * (S.card : ℝ) * (m : ℝ)) =
          c₂ ^ 2 * (S.card : ℝ) * (m : ℝ) * (k : ℝ) ^ 3 / (2048 * (n : ℝ) ^ 2) := by
        dsimp only [T]
        have hk3 : ((k : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = (k : ℝ) ^ 3 := by
          rw [← Real.rpow_natCast ((k : ℝ) ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul hk_pos.le,
            show (3 / 2 : ℝ) * ((2 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        field_simp [hn_pos.ne', hS_pos.ne', hm_pos.ne']
        rw [hk3]
        ring
      have hk4 : C ^ 4 * (n : ℝ) ^ 2 * (Real.log (n : ℝ)) ^ 3 ≤ (k : ℝ) ^ 4 := by
        have h1' : (C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ)) ^ 4 ≤ (k : ℝ) ^ 4 :=
          pow_le_pow_left₀ (by positivity) hk_lb 4
        have h2' : (C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ)) ^ 4 =
            C ^ 4 * (n : ℝ) ^ 2 * (Real.log (n : ℝ)) ^ 3 := by
          have hsq4 : (Real.sqrt (n : ℝ)) ^ 4 = (n : ℝ) ^ 2 := by
            calc (Real.sqrt (n : ℝ)) ^ 4 = ((Real.sqrt (n : ℝ)) ^ 2) ^ 2 := by ring
              _ = (n : ℝ) ^ 2 := by rw [Real.sq_sqrt hn_pos.le]
          have hlog4 : ((Real.log (n : ℝ)) ^ (3 / 4 : ℝ)) ^ 4 = (Real.log (n : ℝ)) ^ 3 := by
            rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hlogn_pos.le,
              show (3 / 4 : ℝ) * ((4 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          rw [mul_pow, mul_pow, hsq4, hlog4]
        exact h2' ▸ h1'
      rw [hT2]
      calc 4 * (k : ℝ) * Real.log (n : ℝ)
          ≤ (c₂ ^ 2 * C ^ 4 / 24576) * (k : ℝ) * Real.log (n : ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_ hlogn_pos.le
            exact mul_le_mul_of_nonneg_right hc2C4 hk_pos.le
        _ ≤ (c₂ ^ 2 * C ^ 4 / 24576) * (k : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            nlinarith
        _ = c₂ ^ 2 * (k : ℝ) * (C ^ 4 * (n : ℝ) ^ 2 * (Real.log (n : ℝ)) ^ 3) /
              (24576 * (n : ℝ) ^ 2 * Real.log (n : ℝ)) := by
            field_simp [hn_pos.ne', hlogn_pos.ne']
        _ ≤ c₂ ^ 2 * (k : ℝ) * (k : ℝ) ^ 4 / (24576 * (n : ℝ) ^ 2 * Real.log (n : ℝ)) := by
            gcongr
        _ = c₂ ^ 2 * ((k : ℝ) / 2) * ((k : ℝ) / (6 * Real.log (n : ℝ))) * (k : ℝ) ^ 3 /
              (2048 * (n : ℝ) ^ 2) := by
            field_simp [hn_pos.ne', hlogn_pos.ne']
            ring
        _ ≤ c₂ ^ 2 * (S.card : ℝ) * (m : ℝ) * (k : ℝ) ^ 3 / (2048 * (n : ℝ) ^ 2) := by
            gcongr
    linarith
  exact hch.trans (Real.exp_le_exp.mpr hexp_le)

private lemma H3_Mreq_eq {c₂ C M_req : ℝ} (hc₂ : 0 < c₂) (hC : 0 < C)
    (hM_eq : M_req = 10368 * 768 * 4 / (c₂ * C ^ (5 / 2 : ℝ))) :
    4 * 10368 = c₂ * C ^ (5 / 2 : ℝ) / 768 * M_req := by
  have hC52 : C ^ (5 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hC (5 / 2)).ne'
  rw [hM_eq]
  field_simp [hc₂.ne', hC52]

private lemma H3_bound2_mu_nonneg {n m k : ℕ} {c₂ : ℝ} (hc₂ : 0 < c₂) (hn_pos : (0 : ℝ) < (n : ℝ))
    {A B : Finset (Fin n)} (hAcard : A.card = m) (hBcard : B.card = m)
    (hgap : ∀ u ∈ A, ∀ v ∈ B, c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ ((v : ℕ) : ℝ) - ((u : ℕ) : ℝ)) :
    0 ≤ ∑ e : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)},
      ((if e.1.1 ∈ B ∧ e.1.2 ∈ B then (2 : ℝ) else 0) -
        (if e.1.1 ∈ A ∧ e.1.2 ∈ A then (2 : ℝ) else 0)) *
      ((1 / 4 + (e.1.1 : ℝ) / (2 * (n : ℝ))) * (1 / 4 + (e.1.2 : ℝ) / (2 * (n : ℝ)))) := by
  let E := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let p_vert : Fin n → ℝ := fun u => 1 / 4 + (u : ℝ) / (2 * (n : ℝ))
  have hp_vert : ∀ u : Fin n, 1 / 4 ≤ p_vert u ∧ p_vert u ≤ 3 / 4 := by
    intro u
    have hu0 : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg u
    have hu1 : (u : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr u.isLt.le
    constructor
    · have : 0 ≤ (u : ℝ) / (2 * (n : ℝ)) := by positivity
      dsimp only [p_vert]; linarith
    · have : (u : ℝ) / (2 * (n : ℝ)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      dsimp only [p_vert]; linarith
  let coef₂ : Fin n × Fin n → ℝ := fun e =>
    (if e.1 ∈ B ∧ e.2 ∈ B then (2 : ℝ) else 0) -
    (if e.1 ∈ A ∧ e.2 ∈ A then (2 : ℝ) else 0)
  let F_mu : Fin n → Fin n → ℝ := fun u v =>
    ((if u ∈ B ∧ v ∈ B ∧ u ≠ v then (1 : ℝ) else 0) -
     (if u ∈ A ∧ v ∈ A ∧ u ≠ v then 1 else 0)) * (p_vert u * p_vert v)
  have hmu_eq : (∑ e : {p : Fin n × Fin n // p ∈ E}, coef₂ e.1 * (p_vert e.1.1 * p_vert e.1.2)) =
      (∑ v₁ ∈ B, ∑ v₂ ∈ B, if v₁ ≠ v₂ then p_vert v₁ * p_vert v₂ else 0) -
      (∑ u₁ ∈ A, ∑ u₂ ∈ A, if u₁ ≠ u₂ then p_vert u₁ * p_vert u₂ else 0) := by
    have h1 : (∑ e : {p : Fin n × Fin n // p ∈ E}, coef₂ e.1 * (p_vert e.1.1 * p_vert e.1.2)) =
        ∑ e ∈ E, (F_mu e.1 e.2 + F_mu e.2 e.1) := by
      rw [Finset.sum_coe_sort E (fun p : Fin n × Fin n => coef₂ p * (p_vert p.1 * p_vert p.2))]
      refine Finset.sum_congr rfl fun ⟨u, v⟩ huv => ?_
      have hne : u ≠ v := ((Finset.mem_filter.mp huv).2).ne
      dsimp only [F_mu, coef₂]
      have hB1 : (if v ∈ B ∧ u ∈ B ∧ v ≠ u then (1 : ℝ) else 0) = if u ∈ B ∧ v ∈ B then 1 else 0 := by
        by_cases h : u ∈ B ∧ v ∈ B
        · rw [if_pos ⟨h.2, h.1, hne.symm⟩, if_pos h]
        · rw [if_neg (fun h' => h ⟨h'.2.1, h'.1⟩), if_neg h]
      have hB2 : (if u ∈ B ∧ v ∈ B ∧ u ≠ v then (1 : ℝ) else 0) = if u ∈ B ∧ v ∈ B then 1 else 0 := by
        by_cases h : u ∈ B ∧ v ∈ B
        · rw [if_pos ⟨h.1, h.2, hne⟩, if_pos h]
        · rw [if_neg (fun h' => h ⟨h'.1, h'.2.1⟩), if_neg h]
      have hA1 : (if v ∈ A ∧ u ∈ A ∧ v ≠ u then (1 : ℝ) else 0) = if u ∈ A ∧ v ∈ A then 1 else 0 := by
        by_cases h : u ∈ A ∧ v ∈ A
        · rw [if_pos ⟨h.2, h.1, hne.symm⟩, if_pos h]
        · rw [if_neg (fun h' => h ⟨h'.2.1, h'.1⟩), if_neg h]
      have hA2 : (if u ∈ A ∧ v ∈ A ∧ u ≠ v then (1 : ℝ) else 0) = if u ∈ A ∧ v ∈ A then 1 else 0 := by
        by_cases h : u ∈ A ∧ v ∈ A
        · rw [if_pos ⟨h.1, h.2, hne⟩, if_pos h]
        · rw [if_neg (fun h' => h ⟨h'.1, h'.2.1⟩), if_neg h]
      have h2B : (if u ∈ B ∧ v ∈ B then (2 : ℝ) else 0) = 2 * (if u ∈ B ∧ v ∈ B then (1 : ℝ) else 0) := by
        by_cases h : u ∈ B ∧ v ∈ B
        · rw [if_pos h, if_pos h]; ring
        · rw [if_neg h, if_neg h]; ring
      have h2A : (if u ∈ A ∧ v ∈ A then (2 : ℝ) else 0) = 2 * (if u ∈ A ∧ v ∈ A then (1 : ℝ) else 0) := by
        by_cases h : u ∈ A ∧ v ∈ A
        · rw [if_pos h, if_pos h]; ring
        · rw [if_neg h, if_neg h]; ring
      rw [hB1, hB2, hA1, hA2, h2B, h2A]
      ring
    rw [h1, ← sum_pair_lt_eq_double n F_mu (fun u => by
      dsimp only [F_mu]
      rw [if_neg (fun h => h.2.2 rfl), if_neg (fun h => h.2.2 rfl), sub_self, zero_mul])]
    have hB_eq : (∑ u : Fin n, ∑ v : Fin n,
        (if u ∈ B ∧ v ∈ B ∧ u ≠ v then (1 : ℝ) else 0) * (p_vert u * p_vert v)) =
        ∑ v₁ ∈ B, ∑ v₂ ∈ B, if v₁ ≠ v₂ then p_vert v₁ * p_vert v₂ else 0 := by
      rw [← Finset.sum_subset (Finset.subset_univ B) (fun u _ hu =>
        Finset.sum_eq_zero fun v _ => by rw [if_neg (fun h => hu h.1), zero_mul])]
      refine Finset.sum_congr rfl fun v₁ hv₁ => ?_
      rw [← Finset.sum_subset (Finset.subset_univ B) (fun v₂ _ hv₂ => by
        rw [if_neg (fun h => hv₂ h.2.1), zero_mul])]
      refine Finset.sum_congr rfl fun v₂ hv₂ => by
        by_cases hne : v₁ ≠ v₂
        · rw [if_pos ⟨hv₁, hv₂, hne⟩, if_pos hne, one_mul]
        · rw [if_neg (fun h => hne h.2.2), if_neg hne, zero_mul]
    have hA_eq : (∑ u : Fin n, ∑ v : Fin n,
        (if u ∈ A ∧ v ∈ A ∧ u ≠ v then (1 : ℝ) else 0) * (p_vert u * p_vert v)) =
        ∑ u₁ ∈ A, ∑ u₂ ∈ A, if u₁ ≠ u₂ then p_vert u₁ * p_vert u₂ else 0 := by
      rw [← Finset.sum_subset (Finset.subset_univ A) (fun u _ hu =>
        Finset.sum_eq_zero fun v _ => by rw [if_neg (fun h => hu h.1), zero_mul])]
      refine Finset.sum_congr rfl fun u₁ hu₁ => ?_
      rw [← Finset.sum_subset (Finset.subset_univ A) (fun u₂ _ hu₂ => by
        rw [if_neg (fun h => hu₂ h.2.1), zero_mul])]
      refine Finset.sum_congr rfl fun u₂ hu₂ => by
        by_cases hne : u₁ ≠ u₂
        · rw [if_pos ⟨hu₁, hu₂, hne⟩, if_pos hne, one_mul]
        · rw [if_neg (fun h => hne h.2.2), if_neg hne, zero_mul]
    simp_rw [F_mu, sub_mul, Finset.sum_sub_distrib, hB_eq, hA_eq]
  change 0 ≤ ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₂ e.1 * (p_vert e.1.1 * p_vert e.1.2)
  rw [hmu_eq, sum_pairs_orderEmb A hAcard p_vert, sum_pairs_orderEmb B hBcard p_vert, sub_nonneg]
  let embA := A.orderEmbOfFin hAcard
  let embB := B.orderEmbOfFin hBcard
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases hij : i ≠ j
  · rw [if_pos hij, if_pos hij]
    have hiA : embA i ∈ A := by
      have : embA i ∈ Set.range embA := Set.mem_range_self _
      rwa [Finset.range_orderEmbOfFin] at this
    have hjA : embA j ∈ A := by
      have : embA j ∈ Set.range embA := Set.mem_range_self _
      rwa [Finset.range_orderEmbOfFin] at this
    have hiB : embB i ∈ B := by
      have : embB i ∈ Set.range embB := Set.mem_range_self _
      rwa [Finset.range_orderEmbOfFin] at this
    have hjB : embB j ∈ B := by
      have : embB j ∈ Set.range embB := Set.mem_range_self _
      rwa [Finset.range_orderEmbOfFin] at this
    have hi_le : p_vert (embA i) ≤ p_vert (embB i) := by
      have h1 : 0 ≤ ((embB i : ℕ) : ℝ) - ((embA i : ℕ) : ℝ) := le_trans (by positivity) (hgap _ hiA _ hiB)
      have h2 : ((embA i : ℕ) : ℝ) ≤ ((embB i : ℕ) : ℝ) := by linarith
      dsimp only [p_vert]
      gcongr
    have hj_le : p_vert (embA j) ≤ p_vert (embB j) := by
      have h1 : 0 ≤ ((embB j : ℕ) : ℝ) - ((embA j : ℕ) : ℝ) := le_trans (by positivity) (hgap _ hjA _ hjB)
      have h2 : ((embA j : ℕ) : ℝ) ≤ ((embB j : ℕ) : ℝ) := by linarith
      dsimp only [p_vert]
      gcongr
    exact mul_le_mul hi_le hj_le (by linarith [(hp_vert (embA j)).1]) (by linarith [(hp_vert (embB i)).1])
  · rw [if_neg hij, if_neg hij]

private lemma H3_bound2_case2 {n k m : ℕ} {c₂ C M_req T₀ : ℝ}
    (hc₂ : 0 < c₂) (hC : 0 < C)
    (hM_eq : M_req = 10368 * 768 * 4 / (c₂ * C ^ (5 / 2 : ℝ))) (hn_gt_M6 : M_req ^ 6 < (n : ℝ))
    (hT0_eq : T₀ = c₂ * (k : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (32 * (n : ℝ)))
    (hn1 : 1 ≤ n) (hn_pos : (0 : ℝ) < (n : ℝ)) (hk_pos : (0 : ℝ) < (k : ℝ))
    (hlogn_ge1 : 1 ≤ Real.log (n : ℝ)) (hlogn_pos : 0 < Real.log (n : ℝ))
    (hk_lb : C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) ≤ (k : ℝ))
    (hm_lb : (k : ℝ) / (6 * Real.log (n : ℝ)) ≤ (m : ℝ)) :
    4 * (k : ℝ) * Real.log (n : ℝ) ≤ T₀ / 4 := by
  have hk_lb2 : C * Real.sqrt (n : ℝ) ≤ (k : ℝ) := by
    have hlog34 : 1 ≤ (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) := Real.one_le_rpow hlogn_ge1 (by norm_num)
    calc C * Real.sqrt (n : ℝ) = C * Real.sqrt (n : ℝ) * 1 := by ring
      _ ≤ C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) := by gcongr
      _ ≤ (k : ℝ) := hk_lb
  have hk52 : C ^ (5 / 2 : ℝ) * (n : ℝ) ^ (5 / 4 : ℝ) ≤ (k : ℝ) ^ (5 / 2 : ℝ) := by
    have h1 : (C * Real.sqrt (n : ℝ)) ^ (5 / 2 : ℝ) ≤ (k : ℝ) ^ (5 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hk_lb2 (by norm_num)
    have h2 : (C * Real.sqrt (n : ℝ)) ^ (5 / 2 : ℝ) = C ^ (5 / 2 : ℝ) * (n : ℝ) ^ (5 / 4 : ℝ) := by
      rw [Real.mul_rpow hC.le (Real.sqrt_nonneg n), Real.sqrt_eq_rpow, ← Real.rpow_mul hn_pos.le,
        show (1 / 2 : ℝ) * (5 / 2 : ℝ) = 5 / 4 by norm_num]
    exact h2 ▸ h1
  have hM_lt : M_req < (n : ℝ) ^ (1 / 6 : ℝ) := by
    have hM0 : 0 ≤ M_req := by rw [hM_eq]; positivity
    have h1 := Real.rpow_lt_rpow (by positivity) hn_gt_M6 (by norm_num : (0 : ℝ) < 1 / 6)
    rw [← Real.rpow_natCast M_req 6, ← Real.rpow_mul hM0,
      show ((6 : ℕ) : ℝ) * (1 / 6 : ℝ) = 1 by norm_num, Real.rpow_one] at h1
    exact h1
  have hlog_pow : 4 * (Real.log (n : ℝ)) ^ 2 ≤ c₂ * C ^ (5 / 2 : ℝ) / 768 * (n : ℝ) ^ (1 / 4 : ℝ) := by
    have h3 := log_cubed_le_n_twelfth n hn1
    have hlog2 : (Real.log (n : ℝ)) ^ 2 ≤ (Real.log (n : ℝ)) ^ 3 := by nlinarith
    have hn14 : (n : ℝ) ^ (1 / 6 : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ) = (n : ℝ) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hn_pos, show (1 / 6 : ℝ) + (1 / 12 : ℝ) = 1 / 4 by norm_num]
    calc 4 * (Real.log (n : ℝ)) ^ 2
        ≤ 4 * (Real.log (n : ℝ)) ^ 3 := by linarith
      _ ≤ 4 * (10368 * (n : ℝ) ^ (1 / 12 : ℝ)) := mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = c₂ * C ^ (5 / 2 : ℝ) / 768 * (M_req * (n : ℝ) ^ (1 / 12 : ℝ)) := by
          rw [← mul_assoc, H3_Mreq_eq hc₂ hC hM_eq, mul_assoc]
      _ ≤ c₂ * C ^ (5 / 2 : ℝ) / 768 * ((n : ℝ) ^ (1 / 6 : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ)) := by
          gcongr
      _ = c₂ * C ^ (5 / 2 : ℝ) / 768 * (n : ℝ) ^ (1 / 4 : ℝ) := by rw [hn14]
  have hn54 : (n : ℝ) ^ (5 / 4 : ℝ) / (n : ℝ) = (n : ℝ) ^ (1 / 4 : ℝ) := by
    rw [div_eq_mul_inv]
    conv_lhs => arg 2; rw [← Real.rpow_one (n : ℝ)]
    rw [← Real.rpow_neg hn_pos.le, ← Real.rpow_add hn_pos,
      show (5 / 4 : ℝ) + -(1 : ℝ) = 1 / 4 by norm_num]
  have hT0_div : T₀ / 4 = c₂ * (k : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (128 * (n : ℝ)) := by
    rw [hT0_eq]; ring
  have hk52_split : (k : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) = (k : ℝ) ^ (5 / 2 : ℝ) := by
    conv_lhs => arg 1; rw [← Real.rpow_one (k : ℝ)]
    rw [← Real.rpow_add hk_pos, show (1 : ℝ) + 3 / 2 = 5 / 2 by norm_num]
  rw [hT0_div]
  calc 4 * (k : ℝ) * Real.log (n : ℝ)
      = (4 * (Real.log (n : ℝ)) ^ 2) * (k : ℝ) / Real.log (n : ℝ) := by
        field_simp [hlogn_pos.ne']; try ring
    _ ≤ (c₂ * C ^ (5 / 2 : ℝ) / 768 * (n : ℝ) ^ (1 / 4 : ℝ)) * (k : ℝ) / Real.log (n : ℝ) := by
        gcongr
    _ = c₂ * (k : ℝ) * (C ^ (5 / 2 : ℝ) * (n : ℝ) ^ (5 / 4 : ℝ)) / (768 * (n : ℝ) * Real.log (n : ℝ)) := by
        rw [← hn54]; field_simp [hn_pos.ne', hlogn_pos.ne']; try ring
    _ ≤ c₂ * (k : ℝ) * (k : ℝ) ^ (5 / 2 : ℝ) / (768 * (n : ℝ) * Real.log (n : ℝ)) := by
        gcongr
    _ = c₂ * (k : ℝ) * ((k : ℝ) / (6 * Real.log (n : ℝ))) * (k : ℝ) ^ (3 / 2 : ℝ) / (128 * (n : ℝ)) := by
        rw [← hk52_split]; field_simp [hn_pos.ne', hlogn_pos.ne']; try ring
    _ ≤ c₂ * (k : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (128 * (n : ℝ)) := by
        gcongr

private lemma H3_bound2_pt {n k m : ℕ} {c₂ C M_req : ℝ}
    (hc₂ : 0 < c₂) (hC : 0 < C) (hc2C4 : 4 ≤ c₂ ^ 2 * C ^ 4 / 24576)
    (hM_eq : M_req = 10368 * 768 * 4 / (c₂ * C ^ (5 / 2 : ℝ))) (hn_gt_M6 : M_req ^ 6 < (n : ℝ))
    (hn1 : 1 ≤ n) (hn_pos : (0 : ℝ) < (n : ℝ)) (hk_pos : (0 : ℝ) < (k : ℝ))
    (hm_pos : (0 : ℝ) < (m : ℝ)) (hlogn_ge1 : 1 ≤ Real.log (n : ℝ)) (hlogn_pos : 0 < Real.log (n : ℝ))
    (hk_lb : C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) ≤ (k : ℝ))
    (hm_lb : (k : ℝ) / (6 * Real.log (n : ℝ)) ≤ (m : ℝ))
    {A B : Finset (Fin n)} (hAcard : A.card = m) (hBcard : B.card = m)
    (hdisjAB : Disjoint A B)
    (hgap : ∀ u ∈ A, ∀ v ∈ B, c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ ((v : ℕ) : ℝ) - ((u : ℕ) : ℝ)) :
    (∑ G : SimpleGraph (Fin n),
      (if (∑ e : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)},
            ((if e.1.1 ∈ B ∧ e.1.2 ∈ B then (2 : ℝ) else 0) -
              (if e.1.1 ∈ A ∧ e.1.2 ∈ A then (2 : ℝ) else 0)) *
            (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0)) ≤
          -(c₂ * (k : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (32 * (n : ℝ)))
        then (1 : ℝ) else 0) *
      (∏ e : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)},
        if G.Adj e.1.1 e.1.2
        then (1 / 4 + (e.1.1 : ℝ) / (2 * (n : ℝ))) * (1 / 4 + (e.1.2 : ℝ) / (2 * (n : ℝ)))
        else 1 - (1 / 4 + (e.1.1 : ℝ) / (2 * (n : ℝ))) * (1 / 4 + (e.1.2 : ℝ) / (2 * (n : ℝ))))) ≤
    Real.exp (-4 * (k : ℝ) * Real.log (n : ℝ)) := by
  let E := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let p_vert : Fin n → ℝ := fun u => 1 / 4 + (u : ℝ) / (2 * (n : ℝ))
  have hp_vert : ∀ u : Fin n, 1 / 4 ≤ p_vert u ∧ p_vert u ≤ 3 / 4 := by
    intro u
    have hu0 : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg u
    have hu1 : (u : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr u.isLt.le
    constructor
    · have : 0 ≤ (u : ℝ) / (2 * (n : ℝ)) := by positivity
      dsimp only [p_vert]; linarith
    · have : (u : ℝ) / (2 * (n : ℝ)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      dsimp only [p_vert]; linarith
  let q : {p : Fin n × Fin n // p ∈ E} → ℝ := fun e => p_vert e.1.1 * p_vert e.1.2
  have hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1 := by
    intro e
    obtain ⟨_, _⟩ := hp_vert e.1.1
    obtain ⟨_, _⟩ := hp_vert e.1.2
    exact ⟨by positivity, by nlinarith⟩
  let coef₂ : Fin n × Fin n → ℝ := fun e =>
    (if e.1 ∈ B ∧ e.2 ∈ B then (2 : ℝ) else 0) -
    (if e.1 ∈ A ∧ e.2 ∈ A then (2 : ℝ) else 0)
  set T₀ : ℝ := c₂ * (k : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (32 * (n : ℝ))
  have hAB : ∀ x, x ∈ A → x ∉ B := fun x hx => Finset.disjoint_left.mp hdisjAB hx
  have hmu_nonneg : 0 ≤ ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₂ e.1 * q e := by
    dsimp only [coef₂, q, p_vert]
    exact H3_bound2_mu_nonneg hc₂ hn_pos hAcard hBcard hgap
  have hC2_ub : ∑ e : {p : Fin n × Fin n // p ∈ E}, (coef₂ e.1) ^ 2 ≤ 4 * (m : ℝ) ^ 2 :=
    H3_coef2_sq_le hAcard hBcard hAB
  have hcoef2 : ∀ e : {p : Fin n × Fin n // p ∈ E}, |coef₂ e.1| ≤ 2 := by
    intro e; dsimp only [coef₂]; split_ifs <;> norm_num
  set t : ℝ := min (1 / 2) (T₀ / (8 * (m : ℝ) ^ 2))
  have hT0_pos : 0 < T₀ := by positivity
  have ht0 : 0 ≤ t := le_min (by norm_num) (by positivity)
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have hch := chernoff_edge_sum n q hq (fun e => coef₂ e.1) hcoef2 ht0 ht1 (-T₀)
  have hexp_le : t * (-T₀ - ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₂ e.1 * q e) +
      t ^ 2 * ∑ e : {p : Fin n × Fin n // p ∈ E}, (coef₂ e.1) ^ 2 ≤
      -4 * (k : ℝ) * Real.log (n : ℝ) := by
    have h1 : t * (-T₀ - ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₂ e.1 * q e) +
        t ^ 2 * ∑ e : {p : Fin n × Fin n // p ∈ E}, (coef₂ e.1) ^ 2 ≤
        -t * T₀ + 4 * (m : ℝ) ^ 2 * t ^ 2 := by
      refine add_le_add ?_ ?_
      · calc t * (-T₀ - ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₂ e.1 * q e)
            ≤ t * (-T₀) := mul_le_mul_of_nonneg_left (by linarith) ht0
          _ = -t * T₀ := by ring
      · calc t ^ 2 * ∑ e : {p : Fin n × Fin n // p ∈ E}, (coef₂ e.1) ^ 2
            ≤ t ^ 2 * (4 * (m : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hC2_ub (sq_nonneg t)
          _ = 4 * (m : ℝ) ^ 2 * t ^ 2 := by ring
    have h2 : -t * T₀ + 4 * (m : ℝ) ^ 2 * t ^ 2 ≤ -4 * (k : ℝ) * Real.log (n : ℝ) := by
      by_cases hcase : T₀ ≤ 4 * (m : ℝ) ^ 2
      · have ht_eq : t = T₀ / (8 * (m : ℝ) ^ 2) := by
          dsimp only [t]; refine min_eq_right ?_
          rw [div_le_iff₀ (by positivity)]; linarith
        rw [ht_eq]
        have hval : -(T₀ / (8 * (m : ℝ) ^ 2)) * T₀ + 4 * (m : ℝ) ^ 2 * (T₀ / (8 * (m : ℝ) ^ 2)) ^ 2 =
            -(T₀ ^ 2 / (16 * (m : ℝ) ^ 2)) := by
          field_simp [hm_pos.ne']; ring
        rw [hval]
        have hT02 : T₀ ^ 2 / (16 * (m : ℝ) ^ 2) =
            c₂ ^ 2 * (k : ℝ) ^ 5 / (16384 * (n : ℝ) ^ 2) := by
          dsimp only [T₀]
          have hk3 : ((k : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = (k : ℝ) ^ 3 := by
            rw [← Real.rpow_natCast ((k : ℝ) ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul hk_pos.le,
              show (3 / 2 : ℝ) * ((2 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          field_simp [hn_pos.ne', hm_pos.ne']
          rw [hk3]
          ring
        have hk4 : C ^ 4 * (n : ℝ) ^ 2 * (Real.log (n : ℝ)) ^ 3 ≤ (k : ℝ) ^ 4 := by
          have h1' : (C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ)) ^ 4 ≤ (k : ℝ) ^ 4 :=
            pow_le_pow_left₀ (by positivity) hk_lb 4
          have h2' : (C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ)) ^ 4 =
              C ^ 4 * (n : ℝ) ^ 2 * (Real.log (n : ℝ)) ^ 3 := by
            have hsq4 : (Real.sqrt (n : ℝ)) ^ 4 = (n : ℝ) ^ 2 := by
              calc (Real.sqrt (n : ℝ)) ^ 4 = ((Real.sqrt (n : ℝ)) ^ 2) ^ 2 := by ring
                _ = (n : ℝ) ^ 2 := by rw [Real.sq_sqrt hn_pos.le]
            have hlog4 : ((Real.log (n : ℝ)) ^ (3 / 4 : ℝ)) ^ 4 = (Real.log (n : ℝ)) ^ 3 := by
              rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hlogn_pos.le,
                show (3 / 4 : ℝ) * ((4 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            rw [mul_pow, mul_pow, hsq4, hlog4]
          exact h2' ▸ h1'
        have hbound : 4 * (k : ℝ) * Real.log (n : ℝ) ≤ T₀ ^ 2 / (16 * (m : ℝ) ^ 2) := by
          rw [hT02]
          calc 4 * (k : ℝ) * Real.log (n : ℝ)
              ≤ (c₂ ^ 2 * C ^ 4 / 24576) * (k : ℝ) * Real.log (n : ℝ) := by
                refine mul_le_mul_of_nonneg_right ?_ hlogn_pos.le
                exact mul_le_mul_of_nonneg_right hc2C4 hk_pos.le
            _ ≤ (c₂ ^ 2 * C ^ 4 / 16384) * (k : ℝ) * (Real.log (n : ℝ)) ^ 3 := by
                have h16 : (c₂ ^ 2 * C ^ 4 / 24576) ≤ c₂ ^ 2 * C ^ 4 / 16384 := by
                  gcongr; norm_num
                have hlog3 : Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 := by
                  calc Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by nlinarith
                    _ ≤ (Real.log (n : ℝ)) ^ 3 := by nlinarith
                refine mul_le_mul (mul_le_mul_of_nonneg_right h16 hk_pos.le) hlog3 hlogn_pos.le (by positivity)
            _ = c₂ ^ 2 * (k : ℝ) * (C ^ 4 * (n : ℝ) ^ 2 * (Real.log (n : ℝ)) ^ 3) / (16384 * (n : ℝ) ^ 2) := by
                field_simp [hn_pos.ne']
            _ ≤ c₂ ^ 2 * (k : ℝ) * (k : ℝ) ^ 4 / (16384 * (n : ℝ) ^ 2) := by gcongr
            _ = c₂ ^ 2 * (k : ℝ) ^ 5 / (16384 * (n : ℝ) ^ 2) := by ring
        linarith
      · have ht_eq : t = 1 / 2 := by
          dsimp only [t]; refine min_eq_left ?_
          rw [le_div_iff₀ (by positivity)]
          linarith
        rw [ht_eq]
        have hval : -(1 / 2 : ℝ) * T₀ + 4 * (m : ℝ) ^ 2 * (1 / 2 : ℝ) ^ 2 ≤ -(T₀ / 4) := by
          linarith
        have hbound : 4 * (k : ℝ) * Real.log (n : ℝ) ≤ T₀ / 4 :=
          H3_bound2_case2 hc₂ hC hM_eq hn_gt_M6 rfl hn1 hn_pos hk_pos hlogn_ge1 hlogn_pos hk_lb hm_lb
        linarith
    exact h1.trans h2
  exact hch.trans (Real.exp_le_exp.mpr hexp_le)

end Helpers

set_option maxHeartbeats 800000 in
theorem OMA.solution : OMA.R_Erdos82_erdos_82_variants_F_upper_bound_R1.H3 := by
  intro c₂ hc₂
  set C : ℝ := max 1 (max (20 / Real.sqrt c₂) ((4000 / c₂) ^ (2 / 5 : ℝ)))
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hc2C4 : 4 ≤ c₂ ^ 2 * C ^ 4 / 24576 := by
    have h20 : 20 / Real.sqrt c₂ ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
    have hsq : 400 / c₂ ≤ C ^ 2 := by
      have h1 : (20 / Real.sqrt c₂) ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (by positivity) h20 2
      rwa [div_pow, Real.sq_sqrt hc₂.le, show (20 : ℝ) ^ 2 = 400 by norm_num] at h1
    have h4 : 160000 / c₂ ^ 2 ≤ C ^ 4 := by
      have h1 : (400 / c₂) ^ 2 ≤ (C ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hsq 2
      have h2 : (C ^ 2) ^ 2 = C ^ 4 := by ring
      have h3 : (400 / c₂) ^ 2 = 160000 / c₂ ^ 2 := by ring
      linarith
    have hmul : 160000 ≤ c₂ ^ 2 * C ^ 4 := by
      linarith [(div_le_iff₀ (sq_pos_of_pos hc₂)).mp h4]
    linarith
  have hc2C52 : 4000 ≤ c₂ * C ^ (5 / 2 : ℝ) := by
    have h52 : (4000 / c₂) ^ (2 / 5 : ℝ) ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
    have hr : 4000 / c₂ ≤ C ^ (5 / 2 : ℝ) := by
      have h := Real.rpow_le_rpow (by positivity) h52 (by norm_num : (0 : ℝ) ≤ 5 / 2)
      rw [← Real.rpow_mul (by positivity)] at h
      norm_num at h
      exact h
    linarith [(div_le_iff₀ hc₂).mp hr]
  set M_req : ℝ := 10368 * 768 * 4 / (c₂ * C ^ (5 / 2 : ℝ))
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (max (max (256 : ℝ) (M_req ^ 6)) (3 : ℝ))
  refine ⟨C, hC, N₁, fun n hn k hk_lb hk_le => ?_⟩
  have hn3 : 3 ≤ n := by
    have : (3 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hN₁ (by exact_mod_cast hn))
    exact_mod_cast this.le
  have hn256 : 256 ≤ n := by
    have : (256 : ℝ) < (n : ℝ) :=
      lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _))
        (lt_of_lt_of_le hN₁ (by exact_mod_cast hn))
    exact_mod_cast this.le
  have hn1 : 1 ≤ n := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hlogn_ge1 : 1 ≤ Real.log (n : ℝ) := by
    have hexp3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    have : Real.exp 1 ≤ (n : ℝ) := le_trans hexp3.le (by exact_mod_cast hn3)
    exact (Real.le_log_iff_exp_le hn_pos).mpr this
  have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
  have hk_ge_sqrt : Real.sqrt (n : ℝ) ≤ (k : ℝ) := by
    have hC1 : 1 ≤ C := le_max_left _ _
    have hlog34 : 1 ≤ (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) := Real.one_le_rpow hlogn_ge1 (by norm_num)
    calc Real.sqrt (n : ℝ)
        = 1 * Real.sqrt (n : ℝ) * 1 := by ring
      _ ≤ C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) := by gcongr
      _ ≤ (k : ℝ) := hk_lb
  have hk16 : 16 ≤ k := by
    have h16_le_sqrt : (16 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      norm_num
      exact_mod_cast hn256
    exact_mod_cast h16_le_sqrt.trans hk_ge_sqrt
  have hk1 : 1 ≤ k := by omega
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  set m : ℕ := k / (Nat.log 2 k + 1)
  have hlogk_ge4 : 4 ≤ Nat.log 2 k := by
    have h16 : Nat.log 2 16 = 4 := by decide
    exact h16 ▸ Nat.log_mono_right hk16
  have hm5 : 5 * m ≤ k := by
    have hmul : (Nat.log 2 k + 1) * m ≤ k := Nat.mul_div_le k (Nat.log 2 k + 1)
    have hle : 5 * m ≤ (Nat.log 2 k + 1) * m := Nat.mul_le_mul_right m (by omega)
    omega
  have hm1 : 1 ≤ m := by
    have hpow_le : Nat.log 2 k + 1 ≤ k := by
      have hpow : 2 ^ (Nat.log 2 k) ≤ k := Nat.pow_log_le_self 2 (by omega)
      have hlin : ∀ r : ℕ, 4 ≤ r → r + 1 ≤ 2 ^ r := by
        intro r hr
        induction r, hr using Nat.le_induction with
        | base => decide
        | succ r hr ih =>
          rw [pow_succ']
          omega
      exact (hlin _ hlogk_ge4).trans hpow
    exact Nat.div_pos hpow_le (by omega)
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hlogk_le_logn : (Nat.log 2 k + 1 : ℝ) ≤ 3 * Real.log (n : ℝ) := by
    have hle : Nat.log 2 k ≤ Nat.log 2 n := Nat.log_mono_right hk_le
    have h1 : (Nat.log 2 k + 1 : ℝ) ≤ (Nat.log 2 n + 1 : ℝ) := by exact_mod_cast Nat.add_le_add_right hle 1
    exact h1.trans (log_div_log_two_le hn3)
  have hm_lb : (k : ℝ) / (6 * Real.log (n : ℝ)) ≤ (m : ℝ) := by
    have hlt : k < (m + 1) * (Nat.log 2 k + 1) := Nat.lt_mul_of_div_lt (Nat.lt_succ_self m) (by positivity)
    have hlt_r : (k : ℝ) < ((m : ℝ) + 1) * (Nat.log 2 k + 1 : ℝ) := by exact_mod_cast hlt
    have hm_2 : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by exact_mod_cast (by omega : m + 1 ≤ 2 * m)
    have h1 : (k : ℝ) ≤ (2 * (m : ℝ)) * (3 * Real.log (n : ℝ)) := by
      calc (k : ℝ) ≤ ((m : ℝ) + 1) * (Nat.log 2 k + 1 : ℝ) := hlt_r.le
        _ ≤ (2 * (m : ℝ)) * (3 * Real.log (n : ℝ)) :=
            mul_le_mul hm_2 hlogk_le_logn (by positivity) (by positivity)
    rw [div_le_iff₀ (by positivity)]
    linarith
  let E := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let p_vert : Fin n → ℝ := fun u => 1 / 4 + (u : ℝ) / (2 * (n : ℝ))
  have hp_vert : ∀ u : Fin n, 1 / 4 ≤ p_vert u ∧ p_vert u ≤ 3 / 4 := by
    intro u
    have hu0 : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg u
    have hu1 : (u : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr u.isLt.le
    constructor
    · have : 0 ≤ (u : ℝ) / (2 * (n : ℝ)) := by positivity
      dsimp only [p_vert]; linarith
    · have : (u : ℝ) / (2 * (n : ℝ)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      dsimp only [p_vert]; linarith
  let q : {p : Fin n × Fin n // p ∈ E} → ℝ := fun e => p_vert e.1.1 * p_vert e.1.2
  have hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1 := by
    intro e
    obtain ⟨h1, h2⟩ := hp_vert e.1.1
    obtain ⟨h3, h4⟩ := hp_vert e.1.2
    exact ⟨by positivity, by nlinarith⟩
  let coef₁ (A B S : Finset (Fin n)) (e : Fin n × Fin n) : ℝ :=
    (if (e.1 ∈ S ∧ e.2 ∈ B) ∨ (e.2 ∈ S ∧ e.1 ∈ B) then 1 else 0) -
    (if (e.1 ∈ S ∧ e.2 ∈ A) ∨ (e.2 ∈ S ∧ e.1 ∈ A) then 1 else 0)
  let coef₂ (A B : Finset (Fin n)) (e : Fin n × Fin n) : ℝ :=
    (if e.1 ∈ B ∧ e.2 ∈ B then (2 : ℝ) else 0) -
    (if e.1 ∈ A ∧ e.2 ∈ A then (2 : ℝ) else 0)
  let T₀ : ℝ := c₂ * (k : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (32 * (n : ℝ))
  let BadTriples := ((Finset.univ : Finset (Fin n)).powersetCard m ×ˢ
      (Finset.univ : Finset (Fin n)).powersetCard m ×ˢ
      (Finset.univ : Finset (Fin n)).powersetCard (k - 2 * m)).filter
      (fun p : Finset (Fin n) × Finset (Fin n) × Finset (Fin n) =>
        Disjoint p.1 p.2.1 ∧ Disjoint p.2.2 (p.1 ∪ p.2.1) ∧
        ∀ u ∈ p.1, ∀ v ∈ p.2.1, c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ ((v : ℕ) : ℝ) - ((u : ℕ) : ℝ))
  let BadPairs := ((Finset.univ : Finset (Fin n)).powersetCard m ×ˢ
      (Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun p : Finset (Fin n) × Finset (Fin n) => Disjoint p.1 p.2 ∧
        ∀ u ∈ p.1, ∀ v ∈ p.2, c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ ((v : ℕ) : ℝ) - ((u : ℕ) : ℝ))
  let Z1 (A B S : Finset (Fin n)) (G : SimpleGraph (Fin n)) : ℝ :=
    ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₁ A B S e.1 * (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0)
  let Z2 (A B : Finset (Fin n)) (G : SimpleGraph (Fin n)) : ℝ :=
    ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₂ A B e.1 * (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0)
  have hn_gt_M6 : M_req ^ 6 < (n : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _))
      (lt_of_lt_of_le hN₁ (by exact_mod_cast hn))
  have hstruct : ∀ G : SimpleGraph (Fin n),
      (∃ U : Finset (Fin n), U.card = k ∧
        (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
        (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
          m ≤ (U.filter (· ≤ a)).card ∧ m ≤ (U.filter (b ≤ ·)).card)) →
      (∃ p ∈ BadTriples, Z1 p.1 p.2.1 p.2.2 G ≤
          c₂ * ((p.2.2.card : ℕ) : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))) ∨
      (∃ p ∈ BadPairs, Z2 p.1 p.2 G ≤ -T₀) := by
    rintro G ⟨U, hUk, ⟨d, hd⟩, ⟨a, b, hab, hspan, hUa, hUb⟩⟩
    dsimp only [BadTriples, BadPairs, Z1, Z2, coef₁, coef₂, T₀]
    exact H3_struct_pt hc₂ hn_pos hm5 G U hUk d hd a b hab hspan hUa hUb
  have hw_nonneg : ∀ G : SimpleGraph (Fin n),
      0 ≤ ∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e := by
    intro G
    refine Finset.prod_nonneg fun e _ => ?_
    have := hq e
    split_ifs <;> linarith
  have h1_bound : ∀ p ∈ BadTriples,
      (∑ G : SimpleGraph (Fin n),
        (if Z1 p.1 p.2.1 p.2.2 G ≤
            c₂ * ((p.2.2.card : ℕ) : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))
          then (1 : ℝ) else 0) *
        (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e)) ≤
      Real.exp (-4 * (k : ℝ) * Real.log (n : ℝ)) := by
    rintro ⟨A, B, S⟩ hp
    simp only [BadTriples, Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard] at hp
    rcases hp with ⟨⟨⟨_, hAcard⟩, ⟨_, hBcard⟩, ⟨_, hScard⟩⟩, hdisjAB, hdisjS, hgap⟩
    dsimp only [Z1, coef₁, q, p_vert]
    exact H3_bound1_pt hc₂ hC hc2C4 hn_pos hk_pos hm1 hm5 hm_pos hlogn_ge1 hlogn_pos
      hk_lb hm_lb hAcard hBcard hScard hdisjAB hdisjS hgap
  have h2_bound : ∀ p ∈ BadPairs,
      (∑ G : SimpleGraph (Fin n),
        (if Z2 p.1 p.2 G ≤ -T₀ then (1 : ℝ) else 0) *
        (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e)) ≤
      Real.exp (-4 * (k : ℝ) * Real.log (n : ℝ)) := by
    rintro ⟨A, B⟩ hp
    simp only [BadPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard] at hp
    rcases hp with ⟨⟨⟨_, hAcard⟩, ⟨_, hBcard⟩⟩, hdisjAB, hgap⟩
    dsimp only [Z2, coef₂, T₀, q, p_vert]
    exact H3_bound2_pt hc₂ hC hc2C4 rfl hn_gt_M6 hn1 hn_pos hk_pos hm_pos hlogn_ge1 hlogn_pos
      hk_lb hm_lb hAcard hBcard hdisjAB hgap
  have hBad_pt : ∀ G : SimpleGraph (Fin n),
      (if ∃ U : Finset (Fin n), U.card = k ∧
          (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
          (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
            m ≤ (U.filter (· ≤ a)).card ∧ m ≤ (U.filter (b ≤ ·)).card)
        then (1 : ℝ) else 0) *
      (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) ≤
      (∑ p ∈ BadTriples,
        (if Z1 p.1 p.2.1 p.2.2 G ≤
            c₂ * ((p.2.2.card : ℕ) : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))
          then (1 : ℝ) else 0) *
        (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e)) +
      (∑ p ∈ BadPairs,
        (if Z2 p.1 p.2 G ≤ -T₀ then (1 : ℝ) else 0) *
        (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e)) := by
    intro G
    have hwG := hw_nonneg G
    by_cases hG : ∃ U : Finset (Fin n), U.card = k ∧
        (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
        (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
          m ≤ (U.filter (· ≤ a)).card ∧ m ≤ (U.filter (b ≤ ·)).card)
    · rw [if_pos hG, one_mul]
      have hnn1 : ∀ p' ∈ BadTriples, 0 ≤
          (if Z1 p'.1 p'.2.1 p'.2.2 G ≤
              c₂ * ((p'.2.2.card : ℕ) : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))
            then (1 : ℝ) else 0) *
          (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) :=
        fun p' _ => mul_nonneg (ite_nonneg zero_le_one le_rfl) hwG
      have hnn2 : ∀ p' ∈ BadPairs, 0 ≤
          (if Z2 p'.1 p'.2 G ≤ -T₀ then (1 : ℝ) else 0) *
          (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) :=
        fun p' _ => mul_nonneg (ite_nonneg zero_le_one le_rfl) hwG
      rcases hstruct G hG with ⟨p, hp, hZ1⟩ | ⟨p, hp, hZ2⟩
      · have hle1 : (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) ≤
            ∑ p' ∈ BadTriples,
              (if Z1 p'.1 p'.2.1 p'.2.2 G ≤
                  c₂ * ((p'.2.2.card : ℕ) : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))
                then (1 : ℝ) else 0) *
              (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) := by
          calc (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e)
              = (if Z1 p.1 p.2.1 p.2.2 G ≤
                    c₂ * ((p.2.2.card : ℕ) : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))
                  then (1 : ℝ) else 0) *
                (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) := by
                rw [if_pos hZ1, one_mul]
            _ ≤ ∑ p' ∈ BadTriples,
                  (if Z1 p'.1 p'.2.1 p'.2.2 G ≤
                      c₂ * ((p'.2.2.card : ℕ) : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))
                    then (1 : ℝ) else 0) *
                  (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) :=
                Finset.single_le_sum hnn1 hp
        have hle2 : 0 ≤ ∑ p' ∈ BadPairs,
            (if Z2 p'.1 p'.2 G ≤ -T₀ then (1 : ℝ) else 0) *
            (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) :=
          Finset.sum_nonneg hnn2
        linarith
      · have hle1 : 0 ≤ ∑ p' ∈ BadTriples,
            (if Z1 p'.1 p'.2.1 p'.2.2 G ≤
                c₂ * ((p'.2.2.card : ℕ) : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))
              then (1 : ℝ) else 0) *
            (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) :=
          Finset.sum_nonneg hnn1
        have hle2 : (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) ≤
            ∑ p' ∈ BadPairs,
              (if Z2 p'.1 p'.2 G ≤ -T₀ then (1 : ℝ) else 0) *
              (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) := by
          calc (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e)
              = (if Z2 p.1 p.2 G ≤ -T₀ then (1 : ℝ) else 0) *
                (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) := by
                rw [if_pos hZ2, one_mul]
            _ ≤ ∑ p' ∈ BadPairs,
                  (if Z2 p'.1 p'.2 G ≤ -T₀ then (1 : ℝ) else 0) *
                  (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) :=
                Finset.single_le_sum hnn2 hp
        linarith
    · rw [if_neg hG, zero_mul]
      refine add_nonneg ?_ ?_
      · exact Finset.sum_nonneg fun p' _ => mul_nonneg (ite_nonneg (zero_le_one : (0 : ℝ) ≤ 1) le_rfl) hwG
      · exact Finset.sum_nonneg fun p' _ => mul_nonneg (ite_nonneg (zero_le_one : (0 : ℝ) ≤ 1) le_rfl) hwG
  have hTriples_card : (BadTriples.card : ℝ) ≤ (n : ℝ) ^ k := by
    have hsub : BadTriples.card ≤ ((Finset.univ : Finset (Fin n)).powersetCard m ×ˢ
        (Finset.univ : Finset (Fin n)).powersetCard m ×ˢ
        (Finset.univ : Finset (Fin n)).powersetCard (k - 2 * m)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rw [Finset.card_product, Finset.card_product] at hsub
    have hmul : ((Finset.univ : Finset (Fin n)).powersetCard m).card *
        (((Finset.univ : Finset (Fin n)).powersetCard m).card *
        ((Finset.univ : Finset (Fin n)).powersetCard (k - 2 * m)).card) ≤ n ^ k := by
      have h1 := card_powersetCard_le_pow n m hn1
      have h2 := card_powersetCard_le_pow n (k - 2 * m) hn1
      calc _ ≤ n ^ m * (n ^ m * n ^ (k - 2 * m)) := Nat.mul_le_mul h1 (Nat.mul_le_mul h1 h2)
        _ = n ^ (m + (m + (k - 2 * m))) := by rw [← pow_add, ← pow_add]
        _ = n ^ k := by congr 1; omega
    exact_mod_cast hsub.trans hmul
  have hPairs_card : (BadPairs.card : ℝ) ≤ (n : ℝ) ^ k := by
    have hsub : BadPairs.card ≤ ((Finset.univ : Finset (Fin n)).powersetCard m ×ˢ
        (Finset.univ : Finset (Fin n)).powersetCard m).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rw [Finset.card_product] at hsub
    have hmul : ((Finset.univ : Finset (Fin n)).powersetCard m).card *
        ((Finset.univ : Finset (Fin n)).powersetCard m).card ≤ n ^ k := by
      have h1 := card_powersetCard_le_pow n m hn1
      calc _ ≤ n ^ m * n ^ m := Nat.mul_le_mul h1 h1
        _ = n ^ (m + m) := by rw [← pow_add]
        _ ≤ n ^ k := Nat.pow_le_pow_right hn1 (by omega)
    exact_mod_cast hsub.trans hmul
  have hnk_exp : (n : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log (n : ℝ)) := by
    rw [← Real.rpow_natCast (n : ℝ) k, Real.rpow_def_of_pos hn_pos, mul_comm]
  have hsum_eq :
      (∑ G : SimpleGraph (Fin n),
        (if ∃ U : Finset (Fin n), U.card = k ∧
            (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
            (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
              k / (Nat.log 2 k + 1) ≤ (U.filter (· ≤ a)).card ∧
              k / (Nat.log 2 k + 1) ≤ (U.filter (b ≤ ·)).card)
          then (1 : ℝ) else 0) *
        (∏ e ∈ E,
          if G.Adj e.1 e.2
          then (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))
          else 1 - (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n)))) =
      (∑ G : SimpleGraph (Fin n),
        (if ∃ U : Finset (Fin n), U.card = k ∧
            (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
            (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
              m ≤ (U.filter (· ≤ a)).card ∧ m ≤ (U.filter (b ≤ ·)).card)
          then (1 : ℝ) else 0) *
        (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e)) := by
    refine Finset.sum_congr rfl fun G _ => ?_
    congr 1
    rw [← Finset.prod_coe_sort E]
  rw [hsum_eq]
  calc (∑ G : SimpleGraph (Fin n),
        (if ∃ U : Finset (Fin n), U.card = k ∧
            (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
            (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
              m ≤ (U.filter (· ≤ a)).card ∧ m ≤ (U.filter (b ≤ ·)).card)
          then (1 : ℝ) else 0) *
        (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e))
      ≤ (∑ p ∈ BadTriples, ∑ G : SimpleGraph (Fin n),
          (if Z1 p.1 p.2.1 p.2.2 G ≤
              c₂ * ((p.2.2.card : ℕ) : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))
            then (1 : ℝ) else 0) *
          (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e)) +
        (∑ p ∈ BadPairs, ∑ G : SimpleGraph (Fin n),
          (if Z2 p.1 p.2 G ≤ -T₀ then (1 : ℝ) else 0) *
          (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e)) := by
        calc _ ≤ ∑ G : SimpleGraph (Fin n),
              ((∑ p ∈ BadTriples,
                  (if Z1 p.1 p.2.1 p.2.2 G ≤
                      c₂ * ((p.2.2.card : ℕ) : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))
                    then (1 : ℝ) else 0) *
                  (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e)) +
                (∑ p ∈ BadPairs,
                  (if Z2 p.1 p.2 G ≤ -T₀ then (1 : ℝ) else 0) *
                  (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e))) :=
                Finset.sum_le_sum fun G _ => hBad_pt G
          _ = _ := by
                rw [Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := BadPairs)]
    _ ≤ (∑ _ ∈ BadTriples, Real.exp (-4 * (k : ℝ) * Real.log (n : ℝ))) +
          (∑ _ ∈ BadPairs, Real.exp (-4 * (k : ℝ) * Real.log (n : ℝ))) :=
        add_le_add (Finset.sum_le_sum h1_bound) (Finset.sum_le_sum h2_bound)
    _ = ((BadTriples.card : ℝ) + (BadPairs.card : ℝ)) * Real.exp (-4 * (k : ℝ) * Real.log (n : ℝ)) := by
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]; ring
    _ ≤ (2 * (n : ℝ) ^ k) * Real.exp (-4 * (k : ℝ) * Real.log (n : ℝ)) := by gcongr; linarith
    _ = 2 * Real.exp (-3 * (k : ℝ) * Real.log (n : ℝ)) := by
        rw [hnk_exp, mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ 2 * Real.exp (-3 * Real.log (n : ℝ)) := by
        gcongr
        have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
        nlinarith
    _ = 2 / (n : ℝ) ^ 3 := by
        have h3 : -3 * Real.log (n : ℝ) = -(((3 : ℕ) : ℝ) * Real.log (n : ℝ)) := by push_cast; ring
        rw [h3, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hn_pos, ← div_eq_mul_inv]
    _ < 1 / (2 * (n : ℝ) ^ 2) := by
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        have hn5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 5 ≤ n)
        have hmul : 4 * (n : ℝ) ^ 2 < (n : ℝ) * (n : ℝ) ^ 2 :=
          mul_lt_mul_of_pos_right (by linarith) (by positivity)
        linarith [show (n : ℝ) * (n : ℝ) ^ 2 = (n : ℝ) ^ 3 by ring]

