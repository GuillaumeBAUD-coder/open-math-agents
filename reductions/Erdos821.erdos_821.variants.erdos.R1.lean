import FormalConjectures.ErdosProblems.«821»

/-!
# A counting reduction for repeated totient values

The divisor bound removes multiplicities from a count of shifted-prime witnesses.
Choosing t³ of the resulting primes produces at least t^(2t³) distinct inputs.
Their totients have at most t^(t³) possible values, by unique factorization.
The resulting fiber sizes give exponent 1/12.
-/

-- Credit: @zarnab222-dev
namespace OMA.R_Erdos821_erdos_821_variants_erdos_R1

open Finset Filter Erdos821

/-- Distinct divisor witnesses for one prime cost at most one divisor count. -/
private lemma weighted_supply (t : ℕ) (ht : 2 ≤ t) (W : Finset (ℕ × ℕ))
    (hW : t^5 * t.sqrt ≤ W.card)
    (hpairs : ∀ w ∈ W, w.1.Prime ∧ w.1 ≤ t^6 ∧ w.2 ∈ (w.1 - 1).divisors ∧
      (∀ q ∈ w.2.primeFactors, q ≤ t^2) ∧ (w.1 - 1) / w.2 ≤ t^2)
    (hdiv : ∀ n ∈ Finset.Icc 1 (t^6), n.divisors.card ≤ t.sqrt) :
    ∃ P : Finset ℕ, t^5 ≤ P.card ∧ ∀ p ∈ P,
      p.Prime ∧ p ≤ t^6 ∧ ∀ q ∈ (p-1).primeFactors, q ≤ t^2 := by
  let P := W.image Prod.fst
  have hmap (w) (hw : w ∈ W) : w.1 ∈ P := Finset.mem_image_of_mem _ hw
  have hsize (p) (hp : p ∈ P) : (W.filter (fun w => w.1 = p)).card ≤ t.sqrt := by
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    have ⟨hp', hle, _⟩ := hpairs w hw
    have hpos := hp'.two_le
    apply le_trans _ (hdiv (w.1-1) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩))
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro u hu
      obtain ⟨hu, he⟩ := Finset.mem_filter.mp hu
      change u.2 ∈ (w.1-1).divisors
      rw [← he]
      exact (hpairs u hu).2.2.1
    · intro a ha b hb hab
      apply Prod.ext
      · exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
      · exact hab
  have htot : W.card ≤ P.card * t.sqrt := calc
    W.card = ∑ p ∈ P, (W.filter (fun w => w.1 = p)).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ _p ∈ P, t.sqrt := Finset.sum_le_sum hsize
    _ = _ := by simp
  have hsqrt : 0 < t.sqrt := Nat.sqrt_pos.mpr (by omega)
  refine ⟨P, Nat.le_of_mul_le_mul_right (hW.trans htot) hsqrt, ?_⟩
  intro p hp
  obtain ⟨⟨p', d⟩, hw, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hprime,hle,hd,hsmall,hco⟩ := hpairs _ hw
  refine ⟨hprime, hle, ?_⟩
  intro q hq
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hdvd := (Nat.mem_divisors.mp hd).1
  have hdpos := Nat.pos_of_mem_divisors hd
  have hpp : 0 < p'-1 := Nat.sub_pos_of_lt hprime.one_lt
  have hcopos := Nat.div_pos (Nat.le_of_dvd hpp hdvd) hdpos
  have hqm : q ∣ (p'-1)/d*d := by
    rw [Nat.div_mul_cancel hdvd]
    exact Nat.dvd_of_mem_primeFactors hq
  rcases hqp.dvd_mul.mp hqm with h | h
  · exact (Nat.le_of_dvd hcopos h).trans hco
  · exact hsmall q (Nat.mem_primeFactors.mpr ⟨hqp, h, hdpos.ne'⟩)

-- A subset of k distinct primes gives one squarefree input. Recover the subset from its product.
private lemma block_choose (b k : ℕ) (hb : 1 ≤ b) :
    b ^ k ≤ (b * k).choose k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_mul_right (Nat.succ_ne_zero k), Nat.succ_sub_one, pow_succ']
    apply Nat.mul_le_mul_left
    apply ih.trans (Nat.choose_le_choose k ?_)
    rw [Nat.mul_succ]
    omega

private lemma many_products (t : ℕ) (ht : 2 ≤ t) (P : Finset ℕ) (hcard : t^5 ≤ P.card)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ t^6 ∧ ∀ q ∈ (p-1).primeFactors, q ≤ t^2) :
    ∃ S : Finset ℕ, t^(2*t^3) ≤ S.card ∧ ∀ m ∈ S,
      0 < m.totient ∧ m.totient ≤ t^(6*t^3) ∧ ∀ q ∈ m.totient.primeFactors, q ≤ t^2 := by
  let S := (P.powersetCard (t^3)).image (fun A => ∏ p ∈ A, p)
  have hS : S.card = P.card.choose (t^3) := by
    apply (Finset.card_image_of_injOn ?_).trans (Finset.card_powersetCard ..)
    intro A hA B hB hab
    have h := congrArg Nat.primeFactors hab
    rwa [Nat.primeFactors_prod (fun p hp => (hP p ((Finset.mem_powersetCard.mp hA).1 hp)).1),
      Nat.primeFactors_prod (fun p hp => (hP p ((Finset.mem_powersetCard.mp hB).1 hp)).1)] at h
  refine ⟨S, ?_, ?_⟩
  · rw [hS, pow_mul]
    apply (block_choose (t^2) (t^3) (Nat.one_le_pow _ _ (by omega))).trans
    exact Nat.choose_le_choose _ (by simpa only [← pow_add] using hcard)
  · intro m hm
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hsub, hsize⟩ := Finset.mem_powersetCard.mp hA
    have hprime (p) (hp : p ∈ A) : Nat.Prime p := (hP p (hsub hp)).1
    have hpos := Finset.prod_pos (s := A) (f := id) (fun p hp => (hprime p hp).pos)
    refine ⟨Nat.totient_pos.mpr hpos, ?_, ?_⟩
    · calc
        Nat.totient (∏ p ∈ A, p) ≤ ∏ p ∈ A, p := Nat.totient_le _
        _ ≤ (t^6)^A.card := Finset.prod_le_pow_card _ _ _ (fun p hp => (hP p (hsub hp)).2.1)
        _ = _ := by rw [hsize, pow_mul]
    · have hphi := Nat.totient_mul_prod_primeFactors (∏ p ∈ A, p)
      rw [Nat.primeFactors_prod hprime, mul_comm (∏ p ∈ A, p)] at hphi
      have he := Nat.mul_right_cancel hpos hphi
      intro q hq
      have hdiv := Nat.dvd_of_mem_primeFactors hq
      rw [he] at hdiv
      obtain ⟨p, hp, hd⟩ := ((Nat.prime_of_mem_primeFactors hq).prime.dvd_finsetProd_iff _).mp hdiv
      exact (hP p (hsub hp)).2.2 q (Nat.mem_primeFactors.mpr
        ⟨Nat.prime_of_mem_primeFactors hq, hd, by have := (hprime p hp).two_le; omega⟩)

-- Count possible prime-exponent vectors, as in OpenAI's lean/OAI/NumberTheory/TotientFibers/FiniteFiber.lean (openai/math, adc7f124),
-- specialized to exponents below t^5 and support in [1, t^2].
private theorem smooth_card_bound : ∀ᶠ t : ℕ in Filter.atTop,
    ((Finset.Icc 1 (t^(6*t^3))).filter
      (fun n => ∀ q ∈ n.primeFactors, q ≤ t^2)).card ≤ t^(t^3) := by
  filter_upwards [Filter.eventually_ge_atTop 7] with t ht
  let S := (Finset.Icc 1 (t^(6*t^3))).filter (fun n => ∀ q ∈ n.primeFactors, q ≤ t^2)
  have hmem (n : ↥S) := Finset.mem_filter.mp n.property
  have hpos (n : ↥S) : 0 < n.val := (Finset.mem_Icc.mp (hmem n).1).1
  have hscale : t^(6*t^3) ≤ 2^(6*t^4) := calc
    _ ≤ (2^t)^(6*t^3) := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ = _ := by rw [← pow_mul]; congr 1; ring
  have hexp (n : ↥S) (p : ℕ) : n.val.factorization p < t^5 := by
    by_cases hp : p.Prime
    · have hpow : 2^(n.val.factorization p) ≤ 2^(6*t^4) :=
        (Nat.pow_le_pow_left hp.two_le _).trans <|
          (Nat.ordProj_le p (hpos n).ne').trans <|
            ((Finset.mem_Icc.mp (hmem n).1).2).trans hscale
      have h := (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp hpow
      have hmul := Nat.mul_lt_mul_of_pos_right (by omega : 6 < t) (by positivity : 0 < t^4)
      exact h.trans_lt (by simpa [pow_succ t 4, mul_comm] using hmul)
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
      positivity
  let code (n : ↥S) (p : ↥(Finset.Icc 1 (t^2))) : Fin (t^5) :=
    ⟨n.val.factorization p.val, hexp n p.val⟩
  have hinj : Function.Injective code := by
    intro m n heq
    apply Subtype.ext
    apply Nat.eq_of_factorization_eq (hpos m).ne' (hpos n).ne'
    intro p
    by_cases hp : p ∈ Finset.Icc 1 (t^2)
    · exact congrArg Fin.val (congrFun heq ⟨p, hp⟩)
    · have hout (k : ↥S) : k.val.factorization p = 0 := by
        by_cases hp' : p.Prime
        · apply Nat.factorization_eq_zero_of_not_dvd
          intro hd
          exact hp (Finset.mem_Icc.mpr ⟨hp'.one_le, (hmem k).2 p
            (Nat.mem_primeFactors.mpr ⟨hp', hd, (hpos k).ne'⟩)⟩)
        · exact Nat.factorization_eq_zero_of_not_prime _ hp'
      rw [hout m, hout n]
  calc
    S.card ≤ (t^5)^(t^2) := by
      have h := Fintype.card_le_of_injective code hinj
      simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe,
        Nat.card_Icc, Nat.add_sub_cancel] using h
    _ = t^(5*t^2) := (pow_mul _ _ _).symm
    _ ≤ t^(t^3) := by
      apply pow_le_pow_right₀ (by omega : 1 ≤ t)
      simpa [pow_succ t 2, mul_comm] using Nat.mul_le_mul_right (t^2) (show 5 ≤ t by omega)

-- Finiteness argument adapted from the repository's proof of the Pillai variant of Erdős 821.
/-- Fibers of the totient function over a positive value are finite. -/
private lemma fiber_finite (n : ℕ) (hn : 0 < n) : {m : ℕ | Nat.totient m = n}.Finite := by
  apply Set.Finite.subset (Set.finite_Iic (n * ∏ i ∈ Finset.Icc 1 (n + 1), i))
  intro m hm
  simp only [Set.mem_ofPred_eq] at hm
  simp only [Set.mem_Iic]
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
    omega
  have key := Nat.totient_mul_prod_primeFactors m
  have hsub : m.primeFactors ⊆ Finset.Icc 1 (n + 1) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have h1 : Nat.totient p ∣ Nat.totient m := Nat.totient_dvd_of_dvd hpd
    rw [Nat.totient_prime hpp, hm] at h1
    have h2 := Nat.le_of_dvd hn h1
    have := hpp.two_le
    simp only [Finset.mem_Icc]
    omega
  have h1 : ∏ p ∈ m.primeFactors, p ≤ ∏ i ∈ Finset.Icc 1 (n + 1), i :=
    Finset.prod_le_prod_of_subset_of_one_le' hsub (fun i hi _ => by
      simp only [Finset.mem_Icc] at hi; omega)
  have h2 : 1 ≤ ∏ p ∈ m.primeFactors, (p - 1) := by
    apply Finset.one_le_prod'
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  rw [hm] at key
  calc m ≤ m * ∏ p ∈ m.primeFactors, (p - 1) := Nat.le_mul_of_pos_right m h2
    _ = n * ∏ p ∈ m.primeFactors, p := key.symm
    _ ≤ n * ∏ i ∈ Finset.Icc 1 (n + 1), i := Nat.mul_le_mul_left n h1

private lemma counting_bridge (t : ℕ) (ht : 2 ≤ t) (S T : Finset ℕ)
    (hmap : ∀ m ∈ S, m.totient ∈ T)
    (hrange : ∀ n ∈ T, 0 < n ∧ n ≤ t ^ (6*t^3))
    (hmany : t^(2*t^3) ≤ S.card) (hfew : T.card ≤ t^(t^3)) :
    ∃ n : ℕ, (n : ℝ) ^ (1/12 : ℝ) < (g n : ℝ) ∧ t ≤ g n := by
  let r := t^(t^3)
  have htr : t ≤ r := by
    change t ≤ t^(t^3)
    exact Nat.le_self_pow (by positivity : 0 < t^3).ne' t
  have hr : 1 < r := by omega
  have hcount : T.card * r ≤ S.card := calc
    T.card * r ≤ r * r := Nat.mul_le_mul_right r hfew
    _ = t^(2*t^3) := by dsimp [r]; rw [← pow_add]; congr 1; omega
    _ ≤ S.card := hmany
  have hSne : S.Nonempty := by
    apply Finset.card_pos.mp
    exact lt_of_lt_of_le (by positivity) hmany
  obtain ⟨m, hm⟩ := hSne
  obtain ⟨n, hn, hf⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to hmap
    ⟨m.totient, hmap m hm⟩ hcount
  have hsub : (↑(S.filter (fun m => m.totient = n)) : Set ℕ) ⊆ {m : ℕ | m.totient = n} := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hrg : r ≤ g n := hf.trans (by
    simpa only [Set.ncard_coe_finset, Erdos821.g] using
      Set.ncard_le_ncard hsub (fiber_finite n (hrange n hn).1))
  have hnr : n ≤ r^6 := by
    simpa only [r, ← pow_mul, Nat.mul_comm 6] using (hrange n hn).2
  have hnr' : (n : ℝ) ≤ (r : ℝ)^6 := by exact_mod_cast hnr
  have hr' : 1 < (r : ℝ) := by exact_mod_cast hr
  have hrg' : (r : ℝ) ≤ (g n : ℝ) := by exact_mod_cast hrg
  refine ⟨n, lt_of_lt_of_le ?_ hrg', htr.trans hrg⟩
  apply (Real.rpow_lt_rpow_iff (by positivity) (by positivity) (by norm_num : (0:ℝ) < 12)).mp
  rw [← Real.rpow_mul (by positivity)]
  norm_num
  exact hnr'.trans_lt (pow_lt_pow_right₀ hr' (by norm_num : 6 < 12))

private lemma conclusion
    (hproducts : ∀ᶠ t : ℕ in atTop, ∃ S : Finset ℕ, t^(2*t^3) ≤ S.card ∧
      ∀ m ∈ S, 0 < m.totient ∧ m.totient ≤ t^(6*t^3) ∧
        ∀ q ∈ m.totient.primeFactors, q ≤ t^2)
    (hsmooth : ∀ᶠ t : ℕ in atTop,
      ((Finset.Icc 1 (t^(6*t^3))).filter (fun n => ∀ q ∈ n.primeFactors, q ≤ t^2)).card ≤ t^(t^3)) :
    type_of% @Erdos821.erdos_821.variants.erdos := by
  refine ⟨1/12, by norm_num, ?_⟩
  by_contra hfin
  have hbound := (Set.not_infinite.mp hfin).image Erdos821.g |>.bddAbove
  obtain ⟨B,hB⟩ := hbound
  obtain ⟨t, ht, htB, hS, hT⟩ := ((eventually_ge_atTop 2).and
    ((eventually_gt_atTop B).and (hproducts.and hsmooth))).exists
  obtain ⟨S, hmany, hmem⟩ := hS
  obtain ⟨n, hn, htn⟩ := counting_bridge t ht S _ (fun m hm => by
    obtain ⟨hlo,hhi,hs⟩ := hmem m hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlo,hhi⟩,hs⟩)
    (fun n hn => Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1) hmany hT
  exact (not_le_of_gt htB) (htn.trans (hB ⟨n, hn, rfl⟩))

/-- Count prime–divisor pairs. Each divisor has small prime factors and small cofactor in p−1.
Lichtman's theorem 1.1 (arXiv:2211.09641) gives this supply even with d = p−1, by taking
x = t⁶/2 and β = 1/3. The weighted statement permits several witnesses for each prime. -/
def H1 : Prop := ∀ᶠ t : ℕ in atTop, ∃ W : Finset (ℕ × ℕ), t^5 * t.sqrt ≤ W.card ∧
  ∀ w ∈ W, w.1.Prime ∧ w.1 ≤ t^6 ∧ w.2 ∈ (w.1 - 1).divisors ∧
    (∀ q ∈ w.2.primeFactors, q ≤ t^2) ∧ (w.1 - 1) / w.2 ≤ t^2

/-- A uniform divisor bound limits the number of witnesses that can belong to one prime. -/
def H2 : Prop := ∀ᶠ t : ℕ in atTop, ∀ n ∈ Finset.Icc 1 (t^6), n.divisors.card ≤ t.sqrt

theorem main : H1 → H2 → type_of% @Erdos821.erdos_821.variants.erdos := by
  intro pairs divisors
  apply conclusion _ smooth_card_bound
  change ∀ᶠ t : ℕ in atTop, _ at pairs divisors
  filter_upwards [pairs, divisors, eventually_ge_atTop 2] with t hW hdiv ht
  obtain ⟨W, hcount, hpair⟩ := hW
  obtain ⟨P, hcard, hprime⟩ := weighted_supply t ht W hcount hpair hdiv
  exact many_products t ht P hcard hprime

end OMA.R_Erdos821_erdos_821_variants_erdos_R1
