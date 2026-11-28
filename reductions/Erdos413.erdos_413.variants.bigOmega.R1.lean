import FormalConjectures.ErdosProblems.«413»

-- Reduction Erdos413.erdos_413.variants.bigOmega.R1 of Erdős Problem 413 (Ω-barrier variant)
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
/-!
# Reduction of Erdős Problem 413 (Ω-barrier variant)

Target: `{n | IsBarrier (fun m => Ω m) n}.Infinite`, where
`IsBarrier f n := ∀ m < n, (m : ℝ) + f m ≤ n`.

The reduction proves the exact characterisation

  `target ↔ {q | q, 2q+1 prime and the window conditions hold}.Infinite`

and splits it into two independent steps:

* **H1** — infinitely many Sophie Germain primes (famous open conjecture). Necessary: every barrier
  `n ≥ 6` is `n = 2q+2` with `q` and `2q+1` prime, so the target implies H1 (`target_imp_sg_infinite`).
* **H2** — a positive proportion of Sophie Germain pairs are *barrier candidates*, i.e. satisfy the
  remaining window conditions `Ω (2q+2-j) ≤ j` for `3 ≤ j ≤ log₂ (2q+2)`. Measured with
  `tools/bar413.c`: `14046` barriers `≥ 8` versus `229568` Sophie Germain pairs below `1e8`, ratio
  `≈ 1/16.4`, stable from `1e5` to `1e9`; a Dickson-type "constellation" statement expected to hold.

Only the last `log₂ n` values below `n` can violate the barrier condition (`isBarrier_iff_window`),
because `Ω m ≤ log₂ m`; and `j = 1, 2` are automatic for an SG pair (`Ω (2q+1) = 1`,
`Ω (2q) = Ω q + 1 = 2`). Hence the `j ≥ 3` conditions are exactly what remains.
-/

namespace OMA.R_Erdos413_erdos_413_variants_bigOmega_R1

open ArithmeticFunction
open scoped omega Omega

/-- **H1**: infinitely many Sophie Germain primes. -/
def H1 : Prop := {q : ℕ | q.Prime ∧ (2 * q + 1).Prime}.Infinite

/-- **H2**: a positive proportion of Sophie Germain pairs are barrier candidates. -/
def H2 : Prop :=
  ∃ c : ℕ, 0 < c ∧ ∀ x : ℕ,
    ({q : ℕ | q.Prime ∧ (2 * q + 1).Prime} ∩ Set.Iic x).ncard ≤ c * (({q : ℕ | q.Prime ∧ (2 * q + 1).Prime ∧ ∀ j, 3 ≤ j → j ≤ Nat.log2 (2 * q + 2) → Ω (2 * q + 2 - j) ≤ j} ∩ Set.Iic x).ncard) + c

/-! ### Elementary `Ω` API -/

theorem two_pow_length_le_prod : ∀ l : List ℕ, (∀ x ∈ l, 2 ≤ x) → 2 ^ l.length ≤ l.prod
  | [], _ => by simp
  | a :: l, h => by
    have ha : 2 ≤ a := h a (List.mem_cons_self ..)
    have hl : ∀ x ∈ l, 2 ≤ x := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have ih := two_pow_length_le_prod l hl
    rw [List.length_cons, List.prod_cons, pow_succ]
    calc 2 ^ l.length * 2 ≤ l.prod * a := Nat.mul_le_mul ih ha
      _ = a * l.prod := Nat.mul_comm _ _

theorem two_pow_cardFactors_le {n : ℕ} (hn : n ≠ 0) : 2 ^ Ω n ≤ n := by
  conv_rhs => rw [← Nat.prod_primeFactorsList hn]
  rw [ArithmeticFunction.cardFactors_apply]
  exact two_pow_length_le_prod _ fun x hx =>
    (Nat.prime_of_mem_primeFactorsList hx).two_le

theorem cardFactors_le_log2 {n : ℕ} (hn : n ≠ 0) : Ω n ≤ Nat.log2 n :=
  (Nat.le_log2 hn).2 (two_pow_cardFactors_le hn)

theorem log2_mono {m n : ℕ} (h : m ≤ n) : Nat.log2 m ≤ Nat.log2 n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · omega
    · rw [Nat.le_log2 (Nat.ne_of_gt hn)]
      exact le_trans (Nat.log2_self_le (Nat.ne_of_gt hm)) h

theorem omega_two_mul {v : ℕ} (hv : v ≠ 0) : Ω (2 * v) = Ω v + 1 := by
  rw [ArithmeticFunction.cardFactors_mul (by norm_num) hv,
    ArithmeticFunction.cardFactors_apply_prime Nat.prime_two]
  omega

theorem omega_prime_eq_one {k : ℕ} (h : k.Prime) : Ω k = 1 :=
  ArithmeticFunction.cardFactors_eq_one_iff_prime.2 h

theorem omega_le_one {k : ℕ} (hk0 : k ≠ 0) (h : Ω k ≤ 1) : k = 1 ∨ k.Prime := by
  rcases Nat.lt_or_ge 1 k with hk | hk
  · refine Or.inr (ArithmeticFunction.cardFactors_eq_one_iff_prime.1 ?_)
    have := ArithmeticFunction.cardFactors_pos_iff_one_lt.2 hk
    omega
  · exact Or.inl (by omega)

/-! ### The window lemma -/

theorem isBarrier_int_iff (n : ℕ) :
    Erdos413.IsBarrier (fun m => Ω m) n ↔ ∀ m < n, m + Ω m ≤ n := by
  simp only [Erdos413.IsBarrier]
  constructor
  · intro h m hm
    exact_mod_cast h m hm
  · intro h m hm
    exact_mod_cast h m hm

/-- Only the last `log₂ n` values below `n` constrain a barrier. -/
theorem isBarrier_iff_window (n : ℕ) :
    Erdos413.IsBarrier (fun m => Ω m) n ↔ ∀ j, 1 ≤ j → j ≤ Nat.log2 n → Ω (n - j) ≤ j := by
  rw [isBarrier_int_iff]
  constructor
  · rintro h j hj1 hj
    have hjn : j ≤ n := le_trans hj (Nat.log2_le_self n)
    rcases Nat.eq_zero_or_pos (n - j) with hm0 | hmpos
    · rw [hm0]; simp
    · have hlt : n - j < n := by omega
      have hbar := h (n - j) hlt
      have heq : n - (n - j) = j := by omega
      omega
  · intro h m hm
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · simp
    · by_cases hj : n - m ≤ Nat.log2 n
      · have hbar := h (n - m) (by omega) hj
        have heq : n - (n - m) = m := by omega
        rw [heq] at hbar
        omega
      · have hbound : Ω m ≤ Nat.log2 m := cardFactors_le_log2 (by omega)
        have hmono : Nat.log2 m ≤ Nat.log2 n := log2_mono (by omega)
        omega

/-! ### Every barrier `n ≥ 6` is a Sophie Germain pair -/

theorem barrier_six_data {n : ℕ} (hb : Erdos413.IsBarrier (fun m => Ω m) n) (hn : 6 ≤ n) :
    ∃ q, n = 2 * q + 2 ∧ q.Prime ∧ (2 * q + 1).Prime := by
  have hint := (isBarrier_iff_window n).1 hb
  have hlog1 : 1 ≤ Nat.log2 n := by
    rw [Nat.le_log2 (by omega)]; norm_num; omega
  have hlog2 : 2 ≤ Nat.log2 n := by
    rw [Nat.le_log2 (by omega)]; norm_num; omega
  have h1 : Ω (n - 1) ≤ 1 := by simpa using hint 1 le_rfl hlog1
  have h2 : Ω (n - 2) ≤ 2 := by simpa using hint 2 (by norm_num) hlog2
  have hp1 : (n - 1).Prime := by
    rcases omega_le_one (by omega : n - 1 ≠ 0) h1 with h | h
    · omega
    · exact h
  have hodd : Odd (n - 1) := hp1.eq_two_or_odd'.resolve_left (by omega)
  have heven : Even n := by
    have h := hodd.add_one
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)] at h
  obtain ⟨k, hk⟩ : ∃ k, n = k + k := heven
  have hk3 : 3 ≤ k := by omega
  have hne : k - 1 ≠ 0 := by omega
  have hkey : n - 2 = 2 * (k - 1) := by omega
  have h3 : Ω (k - 1) ≤ 1 := by
    have h := omega_two_mul hne
    rw [← hkey] at h
    omega
  have hq : (k - 1).Prime := by
    rcases omega_le_one hne h3 with h | h
    · omega
    · exact h
  refine ⟨k - 1, by omega, hq, ?_⟩
  have : 2 * (k - 1) + 1 = n - 1 := by omega
  rw [this]
  exact hp1

/-- A barrier candidate yields a barrier. -/
theorem isBarrier_of_candidate_data {q : ℕ} (hq : q.Prime) (hqp : (2 * q + 1).Prime)
    (hwin : ∀ j, 3 ≤ j → j ≤ Nat.log2 (2 * q + 2) → Ω (2 * q + 2 - j) ≤ j) :
    Erdos413.IsBarrier (fun m => Ω m) (2 * q + 2) := by
  rw [isBarrier_iff_window]
  intro j hj1 hjlog
  rcases Nat.lt_or_ge j 3 with hj3 | hj3
  · interval_cases j
    · have : 2 * q + 2 - 1 = 2 * q + 1 := by omega
      rw [this, omega_prime_eq_one hqp]
    · have h2 : 2 * q + 2 - 2 = 2 * q := by omega
      rw [h2, omega_two_mul hq.ne_zero, omega_prime_eq_one hq]
  · exact hwin j hj3 hjlog

/-! ### The characterisation -/

/-- The target implies infinitely many barrier candidates. -/
theorem target_imp_candidates_infinite
    (h : {n : ℕ | Erdos413.IsBarrier (fun m => Ω m) n}.Infinite) : ({q : ℕ | q.Prime ∧ (2 * q + 1).Prime ∧ ∀ j, 3 ≤ j → j ≤ Nat.log2 (2 * q + 2) → Ω (2 * q + 2 - j) ≤ j}).Infinite := by
  have hfin : ({n : ℕ | ¬ 6 ≤ n}).Finite := by
    have h' : {n : ℕ | ¬ 6 ≤ n} = Set.Iio 6 := by ext n; simp [Nat.not_le]
    rw [h']; exact Set.finite_Iio 6
  have hbig : {n : ℕ | Erdos413.IsBarrier (fun m => Ω m) n ∧ 6 ≤ n}.Infinite := by
    have h' := h.sdiff hfin
    convert h' using 1
    ext n; simp
  have hinj : Set.InjOn (fun n : ℕ => (n - 2) / 2)
      {n : ℕ | Erdos413.IsBarrier (fun m => Ω m) n ∧ 6 ≤ n} := by
    rintro a ⟨hba, ha6⟩ b ⟨hbb, hb6⟩ hab
    obtain ⟨qa, rfl, -⟩ := barrier_six_data hba ha6
    obtain ⟨qb, rfl, -⟩ := barrier_six_data hbb hb6
    change (2 * qa + 2 - 2) / 2 = (2 * qb + 2 - 2) / 2 at hab
    have ha' : (2 * qa + 2 - 2) / 2 = qa := by omega
    have hb' : (2 * qb + 2 - 2) / 2 = qb := by omega
    rw [ha', hb'] at hab
    rw [hab]
  have himg := Set.Infinite.image hinj hbig
  refine himg.mono ?_
  rintro q ⟨n, ⟨hbn, hn6⟩, hq⟩
  obtain ⟨qn, hform, hqn, hqpn⟩ := barrier_six_data hbn hn6
  have hqn' : (n - 2) / 2 = qn := by omega
  change (n - 2) / 2 = q at hq
  rw [hqn'] at hq
  subst hq
  have hwin := (isBarrier_iff_window n).1 hbn
  refine ⟨hqn, hqpn, ?_⟩
  intro j hj3 hjlog
  have hlog : j ≤ Nat.log2 n := by rw [hform]; exact hjlog
  have := hwin j (by omega) hlog
  rwa [hform] at this

/-- Infinitely many barrier candidates produce infinitely many barriers. -/
theorem candidates_infinite_imp_target
    (h : ({q : ℕ | q.Prime ∧ (2 * q + 1).Prime ∧ ∀ j, 3 ≤ j → j ≤ Nat.log2 (2 * q + 2) → Ω (2 * q + 2 - j) ≤ j}).Infinite) : {n : ℕ | Erdos413.IsBarrier (fun m => Ω m) n}.Infinite := by
  have hinj : Set.InjOn (fun q : ℕ => 2 * q + 2) ({q : ℕ | q.Prime ∧ (2 * q + 1).Prime ∧ ∀ j, 3 ≤ j → j ≤ Nat.log2 (2 * q + 2) → Ω (2 * q + 2 - j) ≤ j}) := by
    intro a _ b _ hab
    change 2 * a + 2 = 2 * b + 2 at hab
    omega
  refine (Set.Infinite.image hinj h).mono ?_
  rintro n ⟨q, hq, rfl⟩
  exact isBarrier_of_candidate_data hq.1 hq.2.1 hq.2.2

/-- Barriers `≥ 6` are exactly the `2q+2` for barrier candidates. -/
theorem candidates_infinite_iff_target :
    ({q : ℕ | q.Prime ∧ (2 * q + 1).Prime ∧ ∀ j, 3 ≤ j → j ≤ Nat.log2 (2 * q + 2) → Ω (2 * q + 2 - j) ≤ j}).Infinite ↔ (type_of% @Erdos413.erdos_413.variants.bigOmega) :=
  ⟨candidates_infinite_imp_target, target_imp_candidates_infinite⟩

/-- The target implies **H1**: no weakening of the candidate condition closes the problem. -/
theorem target_imp_sg_infinite
    (h : {n : ℕ | Erdos413.IsBarrier (fun m => Ω m) n}.Infinite) : H1 := by
  refine (target_imp_candidates_infinite h).mono ?_
  rintro q ⟨hq, hqp, -⟩
  exact ⟨hq, hqp⟩

/-! ### The counting step -/

/-- Infinitely many Sophie Germain primes, as unbounded counts. -/
theorem countSG_unbounded (h : H1) : ∀ C : ℕ, ∃ x : ℕ, C ≤ ({q : ℕ | q.Prime ∧ (2 * q + 1).Prime} ∩ Set.Iic x).ncard := by
  intro C
  obtain ⟨t, hts, htcard⟩ := h.exists_subset_card_eq (C + 1)
  refine ⟨t.sup id, ?_⟩
  have hsub : (↑t : Set ℕ) ⊆ {q : ℕ | q.Prime ∧ (2 * q + 1).Prime} ∩ Set.Iic (t.sup id) := by
    intro q hq
    refine ⟨hts hq, Set.mem_Iic.mpr ?_⟩
    exact Finset.le_sup (f := id) (by simpa using hq)
  have hfin : ({q : ℕ | q.Prime ∧ (2 * q + 1).Prime} ∩ Set.Iic (t.sup id)).Finite :=
    (Set.finite_Iic (t.sup id)).inter_of_right _
  have hle := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset] at hle
  have hge : C + 1 ≤ ({q : ℕ | q.Prime ∧ (2 * q + 1).Prime} ∩ Set.Iic (t.sup id)).ncard := by
    rw [← htcard]; exact hle
  omega

/-- A finite candidate set bounds all candidate counts. -/
theorem countBC_bounded (h : ({q : ℕ | q.Prime ∧ (2 * q + 1).Prime ∧ ∀ j, 3 ≤ j → j ≤ Nat.log2 (2 * q + 2) → Ω (2 * q + 2 - j) ≤ j}).Finite) :
    ∃ K : ℕ, ∀ x : ℕ, (({q : ℕ | q.Prime ∧ (2 * q + 1).Prime ∧ ∀ j, 3 ≤ j → j ≤ Nat.log2 (2 * q + 2) → Ω (2 * q + 2 - j) ≤ j}) ∩ Set.Iic x).ncard ≤ K := by
  refine ⟨h.toFinset.card, fun x => ?_⟩
  have hsub : (({q : ℕ | q.Prime ∧ (2 * q + 1).Prime ∧ ∀ j, 3 ≤ j → j ≤ Nat.log2 (2 * q + 2) → Ω (2 * q + 2 - j) ≤ j}) ∩ Set.Iic x) ⊆ ({q : ℕ | q.Prime ∧ (2 * q + 1).Prime ∧ ∀ j, 3 ≤ j → j ≤ Nat.log2 (2 * q + 2) → Ω (2 * q + 2 - j) ≤ j}) := Set.inter_subset_left
  have hle := Set.ncard_le_ncard hsub h
  rwa [Set.ncard_eq_toFinset_card _ h] at hle

/-- **Reduction**: `H1` and `H2` together close Erdős Problem 413 in the Ω form. -/
theorem main : H1 → H2 → type_of% @Erdos413.erdos_413.variants.bigOmega := by
  intro h1 h2
  have hbc : ({q : ℕ | q.Prime ∧ (2 * q + 1).Prime ∧ ∀ j, 3 ≤ j → j ≤ Nat.log2 (2 * q + 2) → Ω (2 * q + 2 - j) ≤ j}).Infinite := by
    by_contra hfin
    rw [Set.not_infinite] at hfin
    obtain ⟨K, hK⟩ := countBC_bounded hfin
    obtain ⟨c, hc, hcx⟩ := h2
    obtain ⟨x, hx⟩ := countSG_unbounded h1 (c * K + c + 1)
    have hcx' := hcx x
    have hmul : c * (({q : ℕ | q.Prime ∧ (2 * q + 1).Prime ∧ ∀ j, 3 ≤ j → j ≤ Nat.log2 (2 * q + 2) → Ω (2 * q + 2 - j) ≤ j}) ∩ Set.Iic x).ncard ≤ c * K := Nat.mul_le_mul_left c (hK x)
    omega
  exact candidates_infinite_imp_target hbc

end OMA.R_Erdos413_erdos_413_variants_bigOmega_R1
