import FormalConjectures.ErdosProblems.«1000»

-- Problem: Erdős Problem 1000 — liminf eq zero
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1000.lean:131 (declaration Erdos1000.erdos_1000.variants.liminf_eq_zero)
-- Credit: @ldy985 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Construction (Cassels-type): blocks M_r * e, e running over all divisors of a squarefree
-- L_r = product of many primes larger than M_r. Inside a block, phi_A(k)/n_k <= phi(e)/e,
-- whose block average is prod (1 - 1/(2p)), small since the sum of 1/p diverges.

open Filter Finset

namespace OMA.O13

open Classical

lemma two_pow_ge (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have : 0 < 2 ^ k := by positivity
    rw [pow_succ]; omega

lemma card_coprime (e : ℕ) : ∀ M : ℕ,
    ((Finset.Icc 1 (M * e)).filter (fun m => Nat.Coprime e m)).card = M * Nat.totient e
  | 0 => by simp
  | M + 1 => by
    have h1 : Finset.Icc 1 ((M + 1) * e) =
        Finset.Icc 1 (M * e) ∪ Finset.Ico (M * e + 1) (M * e + 1 + e) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ico]
      rw [add_mul, one_mul]
      omega
    have hd : Disjoint (Finset.Icc 1 (M * e)) (Finset.Ico (M * e + 1) (M * e + 1 + e)) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      simp only [Finset.mem_Icc, Finset.mem_Ico] at hx hy
      omega
    rw [h1, Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hd),
      card_coprime e M, Nat.filter_coprime_Ico_eq_totient]
    ring

lemma prime_mem_of_dvd (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (p : ℕ) (hp : p.Prime)
    (h : p ∣ ∏ q ∈ S, q) : p ∈ S := by
  obtain ⟨q, hq, hdq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 h
  rw [(Nat.prime_dvd_prime_iff_eq hp (hS q hq)).1 hdq]
  exact hq

lemma prod_inj (S T : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hT : ∀ p ∈ T, p.Prime)
    (h : ∏ q ∈ S, q = ∏ q ∈ T, q) : S = T := by
  ext p
  constructor
  · intro hp
    apply prime_mem_of_dvd T hT p (hS p hp)
    rw [← h]
    exact Finset.dvd_prod_of_mem _ hp
  · intro hp
    apply prime_mem_of_dvd S hS p (hT p hp)
    rw [h]
    exact Finset.dvd_prod_of_mem _ hp

lemma totient_prod (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (Nat.totient (∏ p ∈ S, p) : ℝ) = (∏ p ∈ S, (p : ℝ)) * ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hpa : a.Prime := hS a (Finset.mem_insert_self a s)
    have hs : ∀ p ∈ s, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
      rw [Nat.Prime.coprime_iff_not_dvd hpa]
      intro hd
      exact ha (prime_mem_of_dvd s hs a hpa hd)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha,
      Nat.totient_mul hcop, Nat.totient_prime hpa, Nat.cast_mul, Nat.cast_sub hpa.one_le, ih hs]
    have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast hpa.ne_zero
    field_simp
    push_cast
    ring

lemma exists_primes (M : ℕ) (B : ℝ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ M < p) ∧ B ≤ ∑ p ∈ P, (1 / (p : ℝ)) := by
  by_contra hcon
  push Not at hcon
  apply not_summable_one_div_on_primes
  set f : ℕ → ℝ := fun n => if n.Prime ∧ M < n then 1 / (n : ℝ) else 0 with hfdef
  have hf : Summable f := by
    refine summable_of_sum_range_le (c := B) (fun n => ?_) (fun T => ?_)
    · simp only [hfdef]
      split_ifs <;> positivity
    · have := hcon ((Finset.range T).filter (fun n => n.Prime ∧ M < n))
        (fun p hp => (Finset.mem_filter.1 hp).2)
      rw [Finset.sum_filter] at this
      exact this.le
  have hg : Summable (fun n : ℕ => if n.Prime ∧ n ≤ M then 1 / (n : ℝ) else 0) := by
    apply summable_of_ne_finset_zero (s := Finset.range (M + 1))
    intro n hn
    simp only [Finset.mem_range] at hn
    rw [if_neg]
    omega
  convert hf.add hg using 1
  ext n
  by_cases hp : n.Prime
  · by_cases hM : M < n
    · have : ¬ n ≤ M := by omega
      simp [hp, hM, this, hfdef]
    · have : n ≤ M := by omega
      simp [hp, hM, this, hfdef]
  · simp [hp, hfdef]

noncomputable def Pset (M r : ℕ) : Finset ℕ :=
  Classical.choose (exists_primes M (2 * ((r : ℝ) + 1) * ((M : ℝ) + 1)))

lemma Pset_spec (M r : ℕ) : (∀ p ∈ Pset M r, p.Prime ∧ M < p) ∧
    2 * ((r : ℝ) + 1) * ((M : ℝ) + 1) ≤ ∑ p ∈ Pset M r, 1 / (p : ℝ) :=
  Classical.choose_spec (exists_primes M (2 * ((r : ℝ) + 1) * ((M : ℝ) + 1)))

noncomputable def st : ℕ → ℕ
  | 0 => 1
  | r + 1 => st r * ∏ p ∈ Pset (st r) r, p + 1

noncomputable def P (r : ℕ) : Finset ℕ := Pset (st r) r

noncomputable def L (r : ℕ) : ℕ := ∏ p ∈ P r, p

def A : Set ℕ := {x | ∃ r, ∃ S ⊆ P r, x = st r * ∏ p ∈ S, p}

lemma P_prime (r : ℕ) : ∀ p ∈ P r, p.Prime := fun p hp => ((Pset_spec (st r) r).1 p hp).1

lemma P_big (r : ℕ) : ∀ p ∈ P r, st r < p := fun p hp => ((Pset_spec (st r) r).1 p hp).2

lemma st_pos (r : ℕ) : 0 < st r := by
  cases r with
  | zero => simp [st]
  | succ k => simp [st]

lemma prodS_pos (r : ℕ) (S : Finset ℕ) (hS : S ⊆ P r) : 0 < ∏ p ∈ S, p :=
  Finset.prod_pos (fun p hp => (P_prime r p (hS hp)).pos)

lemma prodS_le (r : ℕ) (S : Finset ℕ) (hS : S ⊆ P r) : ∏ p ∈ S, p ≤ L r :=
  Nat.le_of_dvd (prodS_pos r (P r) le_rfl) (Finset.prod_dvd_prod_of_subset S (P r) _ hS)

lemma st_succ (r : ℕ) : st (r + 1) = st r * L r + 1 := rfl

lemma st_mono : Monotone st := by
  apply monotone_nat_of_le_succ
  intro r
  rw [st_succ]
  have := prodS_pos r (P r) le_rfl
  have h2 : st r ≤ st r * L r := Nat.le_mul_of_pos_right _ this
  omega

lemma st_lt (r s : ℕ) (h : r < s) : st r * L r < st s := by
  have := st_mono (Nat.succ_le_of_lt h)
  rw [st_succ] at this
  omega

lemma block_unique (r s : ℕ) (S : Finset ℕ) (hS : S ⊆ P r) (h1 : st s ≤ st r * ∏ p ∈ S, p)
    (h2 : st r * ∏ p ∈ S, p ≤ st s * L s) : r = s := by
  have hle : st r * ∏ p ∈ S, p ≤ st r * L r := Nat.mul_le_mul_left _ (prodS_le r S hS)
  have hge : st r ≤ st r * ∏ p ∈ S, p := Nat.le_mul_of_pos_right _ (prodS_pos r S hS)
  rcases lt_trichotomy r s with h | h | h
  · have := st_lt r s h; omega
  · exact h
  · have := st_lt s r h; omega

lemma A_infinite : A.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨b, hb⟩
  have hmem : st (b + 1) ∈ A := ⟨b + 1, ∅, Finset.empty_subset _, by simp⟩
  have h1 := hb hmem
  have h2 : StrictMono st := by
    apply strictMono_nat_of_lt_succ
    intro r
    have := st_lt r (r + 1) (Nat.lt_succ_self r)
    have h3 : st r ≤ st r * L r := Nat.le_mul_of_pos_right _ (prodS_pos r (P r) le_rfl)
    omega
  have := h2.id_le (b + 1)
  simp at this
  omega

noncomputable def seq : ℕ → ℕ := Nat.nth (fun x => x ∈ A)

lemma hinf : (Set.ofPred fun x => x ∈ A).Infinite := A_infinite

lemma seq_mem (k : ℕ) : seq k ∈ A := Nat.nth_mem_of_infinite hinf k

lemma seq_count (x : ℕ) (hx : x ∈ A) : seq (Nat.count (fun y => y ∈ A) x) = x := Nat.nth_count hx

lemma count_seq (k : ℕ) : Nat.count (fun y => y ∈ A) (seq k) = k := Nat.count_nth_of_infinite hinf k

/-- The key estimate inside a block. -/
lemma ratio_le (r : ℕ) (S : Finset ℕ) (hS : S ⊆ P r) (k : ℕ)
    (hk : seq k = st r * ∏ p ∈ S, p) :
    (Erdos1000.phiSeq seq k : ℝ) / (seq k : ℝ) ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
  set M := st r with hM
  set e := ∏ p ∈ S, p with he
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => P_prime r p (hS hp)
  have hMpos : 0 < M := st_pos r
  have hepos : 0 < e := prodS_pos r S hS
  have hcard : Erdos1000.phiSeq seq k ≤ M * Nat.totient e := by
    rw [← card_coprime e M]
    unfold Erdos1000.phiSeq
    rw [hk]
    apply Finset.card_le_card
    intro m hm
    simp only [Finset.mem_filter] at hm ⊢
    refine ⟨hm.1, ?_⟩
    apply Nat.coprime_of_dvd
    intro p hp hpe hpm
    have hpS : p ∈ S := prime_mem_of_dvd S hSp p hp hpe
    set y := M * ∏ q ∈ S.erase p, q with hy
    have hxy : M * e = p * y := by
      rw [hy, he, ← Finset.mul_prod_erase S (fun q => q) hpS]
      ring
    have hyA : y ∈ A := ⟨r, S.erase p, (Finset.erase_subset p S).trans hS, rfl⟩
    have hypos : 0 < y := by
      rw [hy]
      exact Nat.mul_pos hMpos (prodS_pos r _ ((Finset.erase_subset p S).trans hS))
    have hylt : y < M * e := by
      rw [hxy]
      have := hp.two_le
      nlinarith
    have hxA : M * e ∈ A := ⟨r, S, hS, rfl⟩
    have hj : Nat.count (fun z => z ∈ A) y < k := by
      rw [← count_seq k, hk]
      exact Nat.count_strict_mono hyA hylt
    have hm2 := hm.2 _ hj
    apply hm2
    rw [seq_count y hyA]
    set g := Nat.gcd m (M * e) with hg
    have hgd : g ∣ M * e := Nat.gcd_dvd_right m (M * e)
    have hpg : p ∣ g := Nat.dvd_gcd hpm (by rw [hxy]; exact dvd_mul_right p y)
    obtain ⟨t, ht⟩ := hpg
    have hx : M * e = g * (M * e / g) := (Nat.mul_div_cancel' hgd).symm
    have h3 : p * y = p * (t * (M * e / g)) := by
      rw [← hxy, ← mul_assoc, ← ht]
      exact hx
    have h4 : y = t * (M * e / g) := Nat.eq_of_mul_eq_mul_left hp.pos h3
    exact ⟨t, by rw [h4]; ring⟩
  have hcardR : (Erdos1000.phiSeq seq k : ℝ) ≤ (M : ℝ) * ((e : ℝ) * ∏ p ∈ S, (1 - 1 / (p : ℝ))) := by
    have : (Erdos1000.phiSeq seq k : ℝ) ≤ ((M * Nat.totient e : ℕ) : ℝ) := by exact_mod_cast hcard
    rw [Nat.cast_mul, he, totient_prod S hSp] at this
    rw [he]
    push_cast at this ⊢
    exact this
  rw [hk, div_le_iff₀ (by positivity)]
  push_cast
  calc (Erdos1000.phiSeq seq k : ℝ) ≤ (M : ℝ) * ((e : ℝ) * ∏ p ∈ S, (1 - 1 / (p : ℝ))) := hcardR
    _ = (∏ p ∈ S, (1 - 1 / (p : ℝ))) * ((M : ℝ) * (e : ℝ)) := by ring

lemma ratio_le_one (k : ℕ) : (Erdos1000.phiSeq seq k : ℝ) / (seq k : ℝ) ≤ 1 := by
  apply div_le_one_of_le₀ _ (by positivity)
  have : Erdos1000.phiSeq seq k ≤ seq k := by
    unfold Erdos1000.phiSeq
    calc _ ≤ (Finset.Icc 1 (seq k)).card := Finset.card_filter_le _ _
      _ = seq k := by simp
  exact_mod_cast this

lemma ratio_nonneg (k : ℕ) : 0 ≤ (Erdos1000.phiSeq seq k : ℝ) / (seq k : ℝ) := by positivity

lemma avg_nonneg (N : ℕ) : 0 ≤ Erdos1000.phiAvg seq N := by
  unfold Erdos1000.phiAvg
  apply div_nonneg _ (by positivity)
  exact Finset.sum_nonneg (fun k _ => ratio_nonneg k)

lemma avg_le_one (N : ℕ) : Erdos1000.phiAvg seq N ≤ 1 := by
  unfold Erdos1000.phiAvg
  apply div_le_one_of_le₀ _ (by positivity)
  calc _ ≤ ∑ k ∈ Finset.range N, (1 : ℝ) := Finset.sum_le_sum (fun k _ => ratio_le_one k)
    _ = N := by simp

/-- Average at the end of block r is at most 2/(r+1), and that index is at least r+1. -/
lemma block_avg (r : ℕ) : ∃ N, r + 1 ≤ N ∧ Erdos1000.phiAvg seq N ≤ 2 / ((r : ℝ) + 1) := by
  set cnt := Nat.count (fun y => y ∈ A) with hcnt
  set M := st r with hM
  set N0 := cnt M with hN0
  set N1 := cnt (M * L r + 1) with hN1
  set Q := 2 ^ (P r).card with hQ
  have hPp := P_prime r
  have hmapsto : ∀ S ∈ (P r).powerset, cnt (M * ∏ p ∈ S, p) ∈ Finset.Ico N0 N1 := by
    intro S hS
    rw [Finset.mem_powerset] at hS
    have hxA : M * ∏ p ∈ S, p ∈ A := ⟨r, S, hS, rfl⟩
    rw [Finset.mem_Ico]
    constructor
    · exact Nat.count_monotone _ (Nat.le_mul_of_pos_right _ (prodS_pos r S hS))
    · apply Nat.count_strict_mono hxA
      have := Nat.mul_le_mul_left M (prodS_le r S hS)
      omega
  have hinj : ∀ S₁ ∈ (P r).powerset, ∀ S₂ ∈ (P r).powerset,
      cnt (M * ∏ p ∈ S₁, p) = cnt (M * ∏ p ∈ S₂, p) → S₁ = S₂ := by
    intro S₁ h1 S₂ h2 h
    rw [Finset.mem_powerset] at h1 h2
    have e1 := seq_count _ (⟨r, S₁, h1, rfl⟩ : M * ∏ p ∈ S₁, p ∈ A)
    have e2 := seq_count _ (⟨r, S₂, h2, rfl⟩ : M * ∏ p ∈ S₂, p ∈ A)
    have h3 : M * ∏ p ∈ S₁, p = M * ∏ p ∈ S₂, p := by
      rw [← e1, ← e2]
      exact congrArg seq h
    have h4 := Nat.eq_of_mul_eq_mul_left (st_pos r) h3
    exact prod_inj S₁ S₂ (fun p hp => hPp p (h1 hp)) (fun p hp => hPp p (h2 hp)) h4
  have hsurj : ∀ k ∈ Finset.Ico N0 N1, ∃ S ∈ (P r).powerset, cnt (M * ∏ p ∈ S, p) = k ∧
      seq k = M * ∏ p ∈ S, p := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hyA := seq_mem k
    have hc := count_seq k
    have hlo : M ≤ seq k := by
      by_contra hlt
      push Not at hlt
      have : k < N0 := by rw [← hc]; exact Nat.count_strict_mono hyA hlt
      omega
    have hhi : seq k ≤ M * L r := by
      by_contra hlt
      push Not at hlt
      have : N1 ≤ k := by rw [← hc]; exact Nat.count_monotone _ (Nat.succ_le_of_lt hlt)
      omega
    obtain ⟨s, S, hS, hy⟩ := hyA
    have hrs : s = r := block_unique s r S hS (hy ▸ hlo) (hy ▸ hhi)
    subst hrs
    refine ⟨S, Finset.mem_powerset.2 hS, ?_, hy⟩
    rw [← hy]
    exact hc
  have hcardQ : N1 - N0 = Q := by
    have := Finset.card_bij (s := (P r).powerset) (t := Finset.Ico N0 N1)
      (fun S _ => cnt (M * ∏ p ∈ S, p)) hmapsto hinj
      (fun k hk => by
        obtain ⟨S, hS, h1, _⟩ := hsurj k hk
        exact ⟨S, hS, h1⟩)
    rw [Finset.card_powerset, Nat.card_Ico] at this
    rw [hQ]
    exact this.symm
  have hN01 : N0 ≤ N1 := Nat.count_monotone _
    (Nat.le_succ_of_le (Nat.le_mul_of_pos_right _ (prodS_pos r (P r) le_rfl)))
  have hN1 : N1 = N0 + Q := by omega
  -- the block sum
  have hblock : ∑ k ∈ Finset.Ico N0 N1, (Erdos1000.phiSeq seq k : ℝ) / (seq k : ℝ) ≤
      ∑ S ∈ (P r).powerset, ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
    have := Finset.sum_bij (s := (P r).powerset) (t := Finset.Ico N0 N1)
      (f := fun S => (Erdos1000.phiSeq seq (cnt (M * ∏ p ∈ S, p)) : ℝ) /
        (seq (cnt (M * ∏ p ∈ S, p)) : ℝ))
      (g := fun k => (Erdos1000.phiSeq seq k : ℝ) / (seq k : ℝ))
      (fun S _ => cnt (M * ∏ p ∈ S, p)) hmapsto hinj
      (fun k hk => by
        obtain ⟨S, hS, h1, _⟩ := hsurj k hk
        exact ⟨S, hS, h1⟩) (fun _ _ => rfl)
    rw [← this]
    apply Finset.sum_le_sum
    intro S hS
    rw [Finset.mem_powerset] at hS
    exact ratio_le r S hS _ (seq_count _ ⟨r, S, hS, rfl⟩)
  have hprod : ∑ S ∈ (P r).powerset, ∏ p ∈ S, (1 - 1 / (p : ℝ)) =
      ∏ p ∈ P r, ((1 - 1 / (p : ℝ)) + 1) := by
    rw [Finset.prod_add]
    simp
  -- the product estimate
  set E := ∏ p ∈ P r, (1 - 1 / (2 * (p : ℝ))) with hE
  have hprod2 : ∏ p ∈ P r, ((1 - 1 / (p : ℝ)) + 1) = (Q : ℝ) * E := by
    rw [hE, hQ]
    push_cast
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have : (p : ℝ) ≠ 0 := by exact_mod_cast (hPp p hp).ne_zero
    field_simp
    ring
  have hspec := (Pset_spec M r).2
  change 2 * ((r : ℝ) + 1) * ((M : ℝ) + 1) ≤ ∑ p ∈ P r, 1 / (p : ℝ) at hspec
  set σ := ∑ p ∈ P r, 1 / (p : ℝ) with hσ
  have hE_le : E ≤ Real.exp (-(σ / 2)) := by
    rw [hE, hσ, Finset.sum_div, ← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      have h1 : (1 : ℝ) ≤ p := by exact_mod_cast (hPp p hp).one_le
      have : 1 / (2 * (p : ℝ)) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      linarith
    · intro p hp
      have := Real.add_one_le_exp (-(1 / (p : ℝ) / 2))
      have h2 : 1 / (2 * (p : ℝ)) = 1 / (p : ℝ) / 2 := by ring
      rw [h2]
      linarith
  have hσpos : (r : ℝ) + 1 ≤ σ / 2 := by
    have : (0 : ℝ) ≤ M := by positivity
    nlinarith
  have hEr : E * ((r : ℝ) + 1) ≤ 1 := by
    have h1 := Real.add_one_le_exp (σ / 2)
    have h2 : Real.exp (-(σ / 2)) * Real.exp (σ / 2) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 : 0 ≤ E := by
      rw [hE]
      apply Finset.prod_nonneg
      intro p hp
      have h1 : (1 : ℝ) ≤ p := by exact_mod_cast (hPp p hp).one_le
      have : 1 / (2 * (p : ℝ)) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      linarith
    have h4 : 0 ≤ Real.exp (-(σ / 2)) := (Real.exp_pos _).le
    nlinarith
  have hcardσ : σ ≤ (P r).card := by
    rw [hσ]
    calc ∑ p ∈ P r, 1 / (p : ℝ) ≤ ∑ p ∈ P r, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          have h1 : (1 : ℝ) ≤ p := by exact_mod_cast (hPp p hp).one_le
          rw [div_le_one (by positivity)]
          exact h1
      _ = (P r).card := by simp
  have hQσ : σ ≤ (Q : ℝ) := by
    have : ((P r).card : ℝ) ≤ (Q : ℝ) := by
      rw [hQ]; exact_mod_cast two_pow_ge _
    linarith
  have hN0M : (N0 : ℝ) ≤ M := by exact_mod_cast (Nat.count_le _ : N0 ≤ M)
  have hMQ : ((r : ℝ) + 1) * M ≤ Q := by
    have : (0 : ℝ) ≤ M := by positivity
    nlinarith
  refine ⟨N1, ?_, ?_⟩
  · have : ((r : ℝ) + 1) ≤ (Q : ℝ) := by
      have : (0 : ℝ) ≤ M := by positivity
      nlinarith
    have : r + 1 ≤ Q := by exact_mod_cast this
    omega
  · unfold Erdos1000.phiAvg
    rw [← Finset.sum_range_add_sum_Ico _ hN01]
    have hfirst : ∑ k ∈ Finset.range N0, (Erdos1000.phiSeq seq k : ℝ) / (seq k : ℝ) ≤ N0 := by
      calc _ ≤ ∑ k ∈ Finset.range N0, (1 : ℝ) := Finset.sum_le_sum (fun k _ => ratio_le_one k)
        _ = N0 := by simp
    have hQpos : (0 : ℝ) < Q := by positivity
    have hN1R : (N1 : ℝ) = N0 + Q := by rw [hN1]; push_cast; ring
    rw [div_le_div_iff₀ (by rw [hN1R]; positivity) (by positivity), hN1R]
    have hT := add_le_add hfirst (hblock.trans_eq (hprod.trans hprod2))
    have hN0nn : (0 : ℝ) ≤ N0 := by positivity
    have hr : (0 : ℝ) ≤ (r : ℝ) + 1 := by positivity
    have h5 := mul_le_mul_of_nonneg_right hT hr
    have h6 := mul_le_mul_of_nonneg_left hEr hQpos.le
    have h7 := mul_le_mul_of_nonneg_right hN0M hr
    nlinarith

theorem main : ∃ n : ℕ → ℕ, StrictMono n ∧ 0 < n 0 ∧
    atTop.liminf (Erdos1000.phiAvg n) = 0 := by
  refine ⟨seq, Nat.nth_strictMono hinf, ?_, ?_⟩
  · obtain ⟨r, S, hS, h⟩ := seq_mem 0
    rw [h]
    exact Nat.mul_pos (st_pos r) (prodS_pos r S hS)
  · have hbelow : atTop.IsBoundedUnder (· ≥ ·) (Erdos1000.phiAvg seq) :=
      isBoundedUnder_of ⟨0, fun x => avg_nonneg x⟩
    have habove : atTop.IsBoundedUnder (· ≤ ·) (Erdos1000.phiAvg seq) :=
      isBoundedUnder_of ⟨1, fun x => avg_le_one x⟩
    apply le_antisymm
    · have hall : ∀ r0 : ℕ, atTop.liminf (Erdos1000.phiAvg seq) ≤ 2 / ((r0 : ℝ) + 1) := by
        intro r0
        apply liminf_le_of_frequently_le _ hbelow
        rw [Filter.frequently_atTop]
        intro a
        obtain ⟨N, hN, havg⟩ := block_avg (max r0 a)
        refine ⟨N, by omega, havg.trans ?_⟩
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        have : (r0 : ℝ) ≤ (max r0 a : ℕ) := by exact_mod_cast le_max_left r0 a
        linarith
      by_contra hpos
      push Not at hpos
      set c := atTop.liminf (Erdos1000.phiAvg seq)
      obtain ⟨r0, hr0⟩ := exists_nat_gt (2 / c)
      have h1 := hall r0
      rw [div_lt_iff₀ hpos] at hr0
      rw [le_div_iff₀ (by positivity)] at h1
      nlinarith
    · exact le_liminf_of_le habove.isCoboundedUnder_ge
        (Eventually.of_forall fun x => avg_nonneg x)

end OMA.O13

theorem OMA.solution : type_of% @Erdos1000.erdos_1000.variants.liminf_eq_zero := by
  exact OMA.O13.main
