import FormalConjectures.ErdosProblems.«675»

open Asymptotics Filter Erdos675

/-- Elements of `S ⊆ [0, X]` pairwise congruent mod `d` number at most `X / d + 1`. -/
lemma OMA.card_le_of_modEq (S : Finset ℕ) (d X : ℕ) (hd : 0 < d) (hX : ∀ s ∈ S, s ≤ X)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, s ≡ s' [MOD d]) : (S.card : ℝ) ≤ (X : ℝ) / d + 1 := by
  have h1 : S.card ≤ (Finset.range (X / d + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun s => s / d)
    · intro s hs
      simp only [Finset.coe_range, Set.mem_Iio]
      have := Nat.div_le_div_right (c := d) (hX s hs)
      omega
    · intro s hs s' hs' h
      have hm := hS s hs s' hs'
      simp only at h
      unfold Nat.ModEq at hm
      rw [← Nat.div_add_mod s d, ← Nat.div_add_mod s' d, h, hm]
  rw [Finset.card_range] at h1
  have h2 : ((X / d : ℕ) : ℝ) ≤ (X : ℝ) / d := Nat.cast_div_le
  have h3 : (S.card : ℝ) ≤ ((X / d + 1 : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h3
  linarith

/-- Telescoping: `∑_{n < m ≤ K} 1/m² ≤ 2/(2n+1)`. -/
lemma OMA.sum_inv_sq_le (n K : ℕ) :
    ∑ m ∈ Finset.Ioc n K, (1 : ℝ) / ((m : ℝ) * m) ≤ 2 / (2 * (n : ℝ) + 1) := by
  rcases le_or_gt n K with h | h
  · have key : ∀ K, n ≤ K → ∑ m ∈ Finset.Ioc n K, (1 : ℝ) / ((m : ℝ) * m) ≤
        2 / (2 * (n : ℝ) + 1) - 2 / (2 * (K : ℝ) + 1) := by
      intro K hK
      induction K, hK using Nat.le_induction with
      | base => simp
      | succ K hK ih =>
        rw [Finset.sum_Ioc_succ_top hK]
        have hk : (0 : ℝ) ≤ K := by positivity
        have e : (1 : ℝ) / (((K + 1 : ℕ) : ℝ) * ((K + 1 : ℕ) : ℝ)) ≤
            2 / (2 * (K : ℝ) + 1) - 2 / (2 * ((K + 1 : ℕ) : ℝ) + 1) := by
          push_cast
          rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
            (by positivity)]
          nlinarith
        linarith
    have := key K h
    have : (0 : ℝ) ≤ 2 / (2 * (K : ℝ) + 1) := by positivity
    linarith
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp only [Finset.sum_empty]
    positivity

lemma OMA.not_sqf_of_dvd {p m : ℕ} (hp : p.Prime) (h : p * p ∣ m) : ¬ Squarefree m := by
  intro hs
  exact (Nat.squarefree_iff_prime_squarefree.mp hs) p hp h

/-- Key lemma: a translation for the squarefree numbers is divisible by `p²` for small `p`. -/
lemma OMA.sq_dvd_of_translation (n t p : ℕ) (hn : 1 ≤ n) (hp : p.Prime)
    (hR : 3 * Nat.sqrt n * (p * p) ≤ n) (ht : IsTranslation {m : ℕ | Squarefree m} n t) :
    p * p ∣ t := by
  by_contra hnd
  set d := p * p with hd_def
  have hp2 : 2 ≤ p := hp.two_le
  have hd : 0 < d := by positivity
  have htm : t % d ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
  have htm' : t % d < d := Nat.mod_lt _ hd
  set b := d - t % d with hb
  have hb1 : 1 ≤ b := by omega
  have hbd : b < d := by omega
  have hbt : d ∣ b + t := by
    refine ⟨t / d + 1, ?_⟩
    have := Nat.div_add_mod t d
    rw [hb]
    rw [mul_add, mul_one]
    omega
  set R := Nat.sqrt n with hR_def
  have hR1 : 1 ≤ R := Nat.le_sqrt.mpr (by simpa using hn)
  set J := 3 * R with hJ
  -- every `j < J` gives a nonsquarefree `b + d j` with a prime square factor `q ≠ p`, `q ≤ R`
  set Qs := (Finset.Icc 2 R).filter (fun q => q.Prime ∧ q ≠ p) with hQs
  have hcover : Finset.range J ⊆
      Qs.biUnion (fun q => (Finset.range J).filter (fun j => q * q ∣ b + d * j)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjn : b + d * j ≤ n := by
      have : d * j + d ≤ d * J := by
        have : j + 1 ≤ J := hj
        nlinarith
      have : d * J ≤ n := by rw [hJ]; nlinarith
      omega
    have hns : ¬ Squarefree (b + d * j + t) := by
      apply OMA.not_sqf_of_dvd hp
      have : d ∣ b + t + d * j := dvd_add hbt (dvd_mul_right _ _)
      rw [show b + d * j + t = b + t + d * j by ring]
      exact this
    have hns' : ¬ Squarefree (b + d * j) := by
      intro h
      exact hns ((ht.2 (b + d * j) (by omega) hjn).mp h)
    rw [Nat.squarefree_iff_prime_squarefree] at hns'
    push Not at hns'
    obtain ⟨q, hq, hqd⟩ := hns'
    rw [Finset.mem_biUnion]
    refine ⟨q, ?_, ?_⟩
    · rw [hQs, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hq.two_le, ?_⟩, hq, ?_⟩
      · rw [hR_def, Nat.le_sqrt]
        exact le_trans (Nat.le_of_dvd (by omega) hqd) hjn
      · rintro rfl
        have : q * q ∣ b := by
          have h2 : q * q ∣ d * j := dvd_mul_right _ _
          exact (Nat.dvd_add_right h2).mp (by rwa [add_comm] at hqd)
        have := Nat.le_of_dvd (by omega) this
        omega
    · rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hj, hqd⟩
  have hcard : (J : ℝ) ≤ ∑ q ∈ Qs, ((J : ℝ) / ((q : ℝ) * q) + 1) := by
    have h1 := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    rw [Finset.card_range] at h1
    have h1' : (J : ℝ) ≤ ∑ q ∈ Qs,
        (((Finset.range J).filter (fun j => q * q ∣ b + d * j)).card : ℝ) := by
      exact_mod_cast h1
    refine h1'.trans (Finset.sum_le_sum fun q hq => ?_)
    rw [hQs, Finset.mem_filter] at hq
    have hq2 := hq.2.1.two_le
    have hcop : Nat.Coprime (q * q) d := by
      have : Nat.Coprime q p := (Nat.coprime_primes hq.2.1 hp).mpr hq.2.2
      exact Nat.Coprime.mul_left (Nat.Coprime.mul_right this this) (Nat.Coprime.mul_right this this)
    have := OMA.card_le_of_modEq ((Finset.range J).filter (fun j => q * q ∣ b + d * j))
      (q * q) J (by positivity)
      (fun s hs => by
        rw [Finset.mem_filter, Finset.mem_range] at hs; omega)
      (fun s hs s' hs' => by
        rw [Finset.mem_filter] at hs hs'
        have h1 : b + d * s ≡ b + d * s' [MOD q * q] :=
          (Nat.modEq_zero_iff_dvd.mpr hs.2).trans (Nat.modEq_zero_iff_dvd.mpr hs'.2).symm
        exact Nat.ModEq.cancel_left_of_coprime hcop (Nat.ModEq.add_left_cancel' b h1))
    push_cast at this
    exact this
  rw [Finset.sum_add_distrib] at hcard
  have hsum1 : ∑ q ∈ Qs, (J : ℝ) / ((q : ℝ) * q) ≤ (J : ℝ) * (1 / 4 + 2 / 5) := by
    have e1 : ∑ q ∈ Qs, (J : ℝ) / ((q : ℝ) * q) = (J : ℝ) * ∑ q ∈ Qs, 1 / ((q : ℝ) * q) := by
      rw [Finset.mul_sum]; congr 1; ext q; ring
    rw [e1]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hsub : Qs ⊆ insert 2 (Finset.Ioc 2 R) := by
      intro q hq
      rw [hQs, Finset.mem_filter, Finset.mem_Icc] at hq
      rw [Finset.mem_insert, Finset.mem_Ioc]
      omega
    calc ∑ q ∈ Qs, 1 / ((q : ℝ) * q) ≤ ∑ q ∈ insert 2 (Finset.Ioc 2 R), 1 / ((q : ℝ) * q) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = 1 / 4 + ∑ q ∈ Finset.Ioc 2 R, 1 / ((q : ℝ) * q) := by
          rw [Finset.sum_insert (by simp)]; norm_num
      _ ≤ 1 / 4 + 2 / 5 := by
          have := OMA.sum_inv_sq_le 2 R
          norm_num at this ⊢
          linarith
  have hsum2 : ∑ q ∈ Qs, (1 : ℝ) ≤ R := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have : Qs.card ≤ R := by
      have : Qs.card ≤ (Finset.Icc 2 R).card := Finset.card_filter_le _ _
      rw [Nat.card_Icc] at this
      omega
    exact_mod_cast this
  have hJR : (J : ℝ) = 3 * R := by rw [hJ]; push_cast; ring
  have hR1' : (1 : ℝ) ≤ R := by exact_mod_cast hR1
  rw [hJR] at hcard hsum1
  linarith

/-- Existence of a translation for the squarefree numbers. -/
lemma OMA.exists_translation (n : ℕ) : ∃ t, IsTranslation {m : ℕ | Squarefree m} n t := by
  set P := (Finset.range (n + 1)).filter Nat.Prime with hP
  set M := ∏ q ∈ P, q * q with hM
  have hMpos : 0 < M := Finset.prod_pos fun q hq => by
    rw [hP, Finset.mem_filter] at hq; have := hq.2.pos; positivity
  have hMdvd : ∀ p, p.Prime → p ≤ n → p * p ∣ M := fun p hp hpn =>
    Finset.dvd_prod_of_mem (fun q => q * q) (by rw [hP, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hp⟩)
  have hMcop : ∀ p, p.Prime → n < p → Nat.Coprime (p * p) M := fun p hp hpn => by
    rw [hM]
    apply Nat.Coprime.prod_right
    intro q hq
    rw [hP, Finset.mem_filter, Finset.mem_range] at hq
    have : Nat.Coprime p q := (Nat.coprime_primes hp hq.2).mpr (by omega)
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_right this this) (Nat.Coprime.mul_right this this)
  set L := n * (2 * n + 1) * (M + n) + 1 with hL
  set X := L * L with hX
  set Q := (M + n) * L with hQ
  have hL1 : 1 ≤ L := by omega
  have hQQ : n + M * X < Q * Q + 1 := by
    rw [hQ, hX]
    have : (M + n) * (L * L) ≤ (M + n) * L * ((M + n) * L) := by
      have h1 : 1 ≤ M + n := by omega
      calc (M + n) * (L * L) = 1 * ((M + n) * L * L) := by ring
        _ ≤ (M + n) * ((M + n) * L * L) := Nat.mul_le_mul_right _ h1
        _ = _ := by ring
    have h4 : n ≤ n * (L * L) := Nat.le_mul_of_pos_right _ (by positivity)
    have e : (M + n) * (L * L) = M * (L * L) + n * (L * L) := by ring
    omega
  set bad := (Finset.Icc 1 X).filter
    (fun s => ∃ a ∈ Finset.Icc 1 n, Squarefree a ∧ ¬ Squarefree (a + M * s)) with hbad
  set Ps := (Finset.Ioc n Q).filter Nat.Prime with hPs
  have hcover : bad ⊆ (Finset.Icc 1 n).biUnion (fun a => Ps.biUnion
      (fun p => (Finset.Icc 1 X).filter (fun s => p * p ∣ a + M * s))) := by
    intro s hs
    rw [hbad, Finset.mem_filter] at hs
    obtain ⟨hsX, a, ha, hsa, hns⟩ := hs
    rw [Nat.squarefree_iff_prime_squarefree] at hns
    push Not at hns
    obtain ⟨p, hp, hpd⟩ := hns
    rw [Finset.mem_biUnion]
    refine ⟨a, ha, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨p, ?_, by rw [Finset.mem_filter]; exact ⟨hsX, hpd⟩⟩
    rw [Finset.mem_Icc] at ha hsX
    have hpn : n < p := by
      by_contra h
      push Not at h
      have h1 : p * p ∣ M * s := Dvd.dvd.mul_right (hMdvd p hp h) s
      have h2 : p * p ∣ a := (Nat.dvd_add_left h1).mp hpd
      exact (Nat.squarefree_iff_prime_squarefree.mp hsa) p hp h2
    rw [hPs, Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨hpn, ?_⟩, hp⟩
    by_contra h
    push Not at h
    have h1 := Nat.le_of_dvd (by omega) hpd
    have h2 : M * s ≤ M * X := Nat.mul_le_mul_left _ hsX.2
    have h3 : (Q + 1) * (Q + 1) ≤ p * p := Nat.mul_le_mul h h
    nlinarith
  have hbadcard : (bad.card : ℝ) ≤ n * ((X : ℝ) * (2 / (2 * n + 1)) + Q) := by
    have h1 := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    have h1' : (bad.card : ℝ) ≤ ∑ a ∈ Finset.Icc 1 n, ∑ p ∈ Ps,
        (((Finset.Icc 1 X).filter (fun s => p * p ∣ a + M * s)).card : ℝ) := by
      have h2 : ∀ a ∈ Finset.Icc 1 n, (Ps.biUnion
          (fun p => (Finset.Icc 1 X).filter (fun s => p * p ∣ a + M * s))).card ≤
          ∑ p ∈ Ps, ((Finset.Icc 1 X).filter (fun s => p * p ∣ a + M * s)).card :=
        fun a _ => Finset.card_biUnion_le
      have h3 := h1.trans (Finset.sum_le_sum h2)
      exact_mod_cast h3
    refine h1'.trans ?_
    have hn : ((Finset.Icc 1 n).card : ℝ) = n := by simp
    rw [show (n : ℝ) * ((X : ℝ) * (2 / (2 * n + 1)) + Q) =
      ∑ _a ∈ Finset.Icc 1 n, ((X : ℝ) * (2 / (2 * n + 1)) + Q) by
        rw [Finset.sum_const, nsmul_eq_mul, hn]]
    apply Finset.sum_le_sum
    intro a ha
    have h4 : ∀ p ∈ Ps, (((Finset.Icc 1 X).filter (fun s => p * p ∣ a + M * s)).card : ℝ)
        ≤ (X : ℝ) * (1 / ((p : ℝ) * p)) + 1 := by
      intro p hp
      rw [hPs, Finset.mem_filter, Finset.mem_Ioc] at hp
      have hcop := hMcop p hp.2 hp.1.1
      have hp2 := hp.2.two_le
      have := OMA.card_le_of_modEq ((Finset.Icc 1 X).filter (fun s => p * p ∣ a + M * s))
        (p * p) X (by positivity)
        (fun s hs => by rw [Finset.mem_filter, Finset.mem_Icc] at hs; omega)
        (fun s hs s' hs' => by
          rw [Finset.mem_filter] at hs hs'
          have h1 : a + M * s ≡ a + M * s' [MOD p * p] :=
            (Nat.modEq_zero_iff_dvd.mpr hs.2).trans (Nat.modEq_zero_iff_dvd.mpr hs'.2).symm
          exact Nat.ModEq.cancel_left_of_coprime hcop (Nat.ModEq.add_left_cancel' a h1))
      push_cast at this
      calc _ ≤ (X : ℝ) / ((p : ℝ) * p) + 1 := this
        _ = _ := by ring
    refine (Finset.sum_le_sum h4).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h5 : ∑ p ∈ Ps, 1 / ((p : ℝ) * p) ≤ 2 / (2 * n + 1) :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)).trans (OMA.sum_inv_sq_le n Q)
    have h6 : ∑ p ∈ Ps, (1 : ℝ) ≤ Q := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      have : Ps.card ≤ (Finset.Ioc n Q).card := Finset.card_filter_le _ _
      rw [Nat.card_Ioc] at this
      exact_mod_cast (this.trans (Nat.sub_le _ _))
    have : (X : ℝ) * ∑ p ∈ Ps, 1 / ((p : ℝ) * p) ≤ (X : ℝ) * (2 / (2 * n + 1)) :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    linarith
  have hlt : bad.card < (Finset.Icc 1 X).card := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
    have key : (n : ℝ) * ((X : ℝ) * (2 / (2 * n + 1)) + Q) < X := by
      have hnQ : (n : ℝ) * Q * (2 * n + 1) < X := by
        have : n * Q * (2 * n + 1) < X := by
          rw [hX, hQ]
          have : n * ((M + n) * L) * (2 * n + 1) = (n * (2 * n + 1) * (M + n)) * L := by ring
          rw [this]
          exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        exact_mod_cast this
      have h2 : (0 : ℝ) < 2 * n + 1 := by positivity
      have e : (n : ℝ) * ((X : ℝ) * (2 / (2 * n + 1)) + Q) =
          (2 * n * X + n * Q * (2 * n + 1)) / (2 * n + 1) := by
        field_simp
      rw [e, div_lt_iff₀ h2]
      have e2 : (X : ℝ) * (2 * n + 1) = 2 * n * X + X := by ring
      linarith
    have := hbadcard.trans_lt key
    exact_mod_cast this
  obtain ⟨s, hs, hsb⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  rw [Finset.mem_Icc] at hs
  refine ⟨M * s, Nat.mul_pos hMpos (by omega), fun a ha1 han => ?_⟩
  show Squarefree a ↔ Squarefree (a + M * s)
  constructor
  · intro hsa
    by_contra hns
    exact hsb (by
      rw [hbad, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨hs, a, Finset.mem_Icc.mpr ⟨ha1, han⟩, hsa, hns⟩)
  · intro h
    by_contra hsa
    rw [Nat.squarefree_iff_prime_squarefree] at hsa
    push Not at hsa
    obtain ⟨p, hp, hpd⟩ := hsa
    have hpn : p ≤ n := by
      have := Nat.le_of_dvd (by omega) hpd
      nlinarith [hp.two_le]
    exact OMA.not_sqf_of_dvd hp (dvd_add hpd (Dvd.dvd.mul_right (hMdvd p hp hpn) s)) h

theorem OMA.solution : type_of% @Erdos675.erdos_675.parts.iii := by
  refine ⟨1 / 8, by norm_num, ?_⟩
  rw [eventually_atTop]
  refine ⟨30 ^ 16, fun n hn => ?_⟩
  set t := minTranslation {m : ℕ | Squarefree m} n with ht_def
  have ht : IsTranslation {m : ℕ | Squarefree m} n t :=
    Nat.sInf_mem (OMA.exists_translation n)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  set z := (n : ℝ) ^ (1 / 16 : ℝ) with hz
  have hz0 : 0 ≤ z := by positivity
  have hz16 : z ^ 16 = (n : ℝ) := by
    rw [hz, ← Real.rpow_natCast, ← Real.rpow_mul hn0]; norm_num
  have hz30 : 30 ≤ z := by
    by_contra h
    push Not at h
    have h1 : z ^ 16 < (30 : ℝ) ^ 16 := pow_lt_pow_left₀ h hz0 (by norm_num)
    have h2 : ((30 ^ 16 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  have hc : (n : ℝ) ^ (1 / 8 : ℝ) = z ^ 2 := by
    rw [hz, ← Real.rpow_natCast, ← Real.rpow_mul hn0]; norm_num
  have hsqrt : Real.sqrt n = z ^ 8 := by
    rw [← hz16, show z ^ 16 = (z ^ 8) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  set y := ⌊z ^ 4 / 2⌋₊ with hy
  have hy1 : (y : ℝ) ≤ z ^ 4 / 2 := Nat.floor_le (by positivity)
  have hy2 : z ^ 4 / 2 - 1 < (y : ℝ) := by
    have := Nat.lt_floor_add_one (z ^ 4 / 2); rw [← hy] at this; linarith
  have hz4 : (810000 : ℝ) ≤ z ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num) hz30 4]
  have hy0 : (1 : ℝ) ≤ y := by linarith
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  -- every prime `p ≤ y` divides `t`
  have hdvd : ∀ p, p.Prime → p ≤ y → p ∣ t := by
    intro p hp hpy
    have hcond : 3 * Nat.sqrt n * (p * p) ≤ n := by
      have h1 : ((Nat.sqrt n : ℕ) : ℝ) ≤ z ^ 8 := hsqrt ▸ Real.nat_sqrt_le_real_sqrt
      have h2 : ((p * p : ℕ) : ℝ) ≤ z ^ 8 / 4 := by
        have : (p : ℝ) ≤ y := by exact_mod_cast hpy
        push_cast
        have hp0 : (0 : ℝ) ≤ p := by positivity
        nlinarith
      have h3 : ((3 * Nat.sqrt n * (p * p) : ℕ) : ℝ) ≤ n := by
        rw [Nat.cast_mul, Nat.cast_mul, ← hz16]
        have : (0 : ℝ) ≤ ((p * p : ℕ) : ℝ) := by positivity
        have : (0 : ℝ) ≤ ((Nat.sqrt n : ℕ) : ℝ) := by positivity
        push_cast at *
        nlinarith
      exact_mod_cast h3
    exact Dvd.dvd.trans (dvd_mul_right p p) (OMA.sq_dvd_of_translation n t p hn1 hp hcond ht)
  have hprim : primorial y ∣ t := by
    unfold primorial
    apply Finset.prod_primes_dvd
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact hp.2.prime
    · intro p hp
      rw [Finset.mem_filter, Finset.mem_range] at hp
      exact hdvd p hp.2 (by omega)
  have hprim_le : (primorial y : ℝ) ≤ t := by
    exact_mod_cast Nat.le_of_dvd ht.1 hprim
  have htheta : Chebyshev.theta y ≤ Real.log t := by
    rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
    exact Real.log_le_log (by exact_mod_cast primorial_pos y) hprim_le
  have hge := Chebyshev.theta_ge y
  -- the error terms
  have hlogz : Real.log z ≤ z := by
    have := Real.log_le_sub_one_of_pos (show 0 < z by linarith); linarith
  have hlog1 : Real.log ((y : ℝ) + 1) ≤ 4 * z := by
    have h1 : Real.log ((y : ℝ) + 1) ≤ Real.log (z ^ 4) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hlogy : Real.log (y : ℝ) ≤ 4 * z := by
    have := Real.log_le_log (by positivity : (0 : ℝ) < y) (show (y : ℝ) ≤ y + 1 by linarith)
    linarith
  have hlogy0 : 0 ≤ Real.log (y : ℝ) := Real.log_nonneg hy0
  have hsy : Real.sqrt (y : ℝ) ≤ z ^ 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have herr : 2 * Real.sqrt (y : ℝ) * Real.log y ≤ 2 * z ^ 2 * (4 * z) := by
    have := mul_le_mul hsy hlogy hlogy0 (by positivity)
    nlinarith
  have hl2 := Real.log_two_gt_d9
  have hmain : z ^ 2 < Chebyshev.theta y := by
    have h1 : (z ^ 4 / 2 - 1) * Real.log 2 ≤ (y : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hy2.le (by positivity)
    have h2 : (z ^ 4 / 2 - 1) * 0.6931471803 ≤ (z ^ 4 / 2 - 1) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hl2.le (by linarith)
    have h3 : z ^ 2 + 8 * z ^ 3 + 4 * z + 1 < (z ^ 4 / 2 - 1) * 0.6931471803 := by
      have hz3 : (27000 : ℝ) ≤ z ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) hz30 3]
      nlinarith [pow_le_pow_left₀ (by norm_num) hz30 2]
    linarith
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht.1
  rw [hc]
  calc Real.exp (z ^ 2) < Real.exp (Real.log t) := Real.exp_lt_exp.mpr (by linarith)
    _ = t := Real.exp_log htpos
