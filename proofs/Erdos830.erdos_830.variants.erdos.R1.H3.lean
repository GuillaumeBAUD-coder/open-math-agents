import OMAReductions.R_Erdos830_erdos_830_variants_erdos_R1
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.BigOperators.Field

/-!
The abundancy ratio is approximated by the ratio at a gcd with a fixed modulus.
After excluding squares of selected large primes, the presence patterns for
those primes give separated ratios. The Chinese remainder theorem then bounds
the number of residues giving a ratio in a sufficiently short interval.
-/

open Finset Filter
open scoped ArithmeticFunction.sigma

namespace OMA.E830

private def numerator (S T : Finset ℕ) : ℕ := ∏ p ∈ S, if p ∈ T then p+1 else p

private theorem numerator_inj (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 2 < p)
    {T U : Finset ℕ} (heq : numerator S T = numerator S U) :
    ∀ p ∈ S, p ∈ T ↔ p ∈ U := by
  classical
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert p S hlt ih =>
    have hp := hS p (mem_insert_self ..)
    have hs : ∀ q ∈ S, q.Prime ∧ 2 < q := fun q h => hS q (mem_insert_of_mem h)
    have hpS : p ∉ S := fun h => (lt_irrefl p) (hlt p h)
    have hn (A : Finset ℕ) : ¬ p ∣ numerator S A := by
      rw [numerator, Prime.dvd_finsetProd_iff hp.1.prime]
      rintro ⟨q, hq, hd⟩
      have hqodd := (hs q hq).1.eq_two_or_odd.resolve_left (by have := (hs q hq).2; omega)
      have hpodd := hp.1.eq_two_or_odd.resolve_left (by omega)
      have hqle := hlt q hq
      have hb : 0 < (if q ∈ A then q+1 else q) ∧ (if q ∈ A then q+1 else q) < p := by
        split <;> omega
      exact (not_le_of_gt hb.2) (Nat.le_of_dvd hb.1 hd)
    simp only [numerator, prod_insert hpS] at heq
    have hpd (A : Finset ℕ) : (p ∣ (if p ∈ A then p+1 else p) * numerator S A) ↔ p ∉ A := by
      rw [hp.1.dvd_mul, or_iff_left (hn A)]
      split_ifs with hA
      · simp only [hA, not_true_eq_false, iff_false]
        exact fun hd => hp.1.not_dvd_one ((Nat.dvd_add_iff_right (dvd_refl p)).mpr hd)
      · simp [hA]
    have harg : p ∉ T ↔ p ∉ U := (hpd T).symm.trans (heq ▸ hpd U)
    have hmem : p ∈ T ↔ p ∈ U := not_iff_not.mp harg
    have ht : (if p ∈ T then p+1 else p) = (if p ∈ U then p+1 else p) := if_congr hmem rfl rfl
    have hpos : 0 < (if p ∈ T then p+1 else p) := by split <;> have := hp.1.pos <;> omega
    change (if p ∈ T then p+1 else p) * numerator S T =
      (if p ∈ U then p+1 else p) * numerator S U at heq
    rw [← ht] at heq
    have hrest := ih hs (Nat.eq_of_mul_eq_mul_left hpos heq)
    intro q hq
    rcases mem_insert.mp hq with rfl | hq
    · exact hmem
    · exact hrest q hq

private noncomputable def primeRatio (S T : Finset ℕ) : ℝ :=
  ∏ p ∈ S, (if p ∈ T then (p+1 : ℝ) / p else 1)

private theorem primeRatio_quot (S T : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    primeRatio S T = (numerator S T : ℝ) / ((∏ p ∈ S, p : ℕ) : ℝ) := by
  rw [primeRatio,numerator,Nat.cast_prod,Nat.cast_prod,← prod_div_distrib]
  apply prod_congr rfl
  intro p hp
  have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast (hS p hp).ne_zero
  split_ifs <;> simp [hp0]

private theorem primeRatio_sep (S T U : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 2 < p)
    (hdiff : ∃ p ∈ S, ¬ (p ∈ T ↔ p ∈ U)) :
    ((∏ p ∈ S, p : ℕ) : ℝ)⁻¹ ≤ |primeRatio S T - primeRatio S U| := by
  have hpos : 0 < (∏ p ∈ S, p : ℕ) := Finset.prod_pos fun p h => (hS p h).1.pos
  have hposR : (0:ℝ) < ((∏ p ∈ S, p : ℕ) : ℝ) := by exact_mod_cast hpos
  have hn : numerator S T ≠ numerator S U := fun h => by
    obtain ⟨p,hp,hne⟩ := hdiff
    exact hne (numerator_inj S hS h p hp)
  simp only [primeRatio_quot _ _ (fun p hp => (hS p hp).1), ← sub_div, abs_div,
    abs_of_pos hposR, ← one_div]
  apply div_le_div_of_nonneg_right _ hposR.le
  rcases lt_or_gt_of_ne hn with h | h
  · have ha : (numerator S T : ℝ) + 1 ≤ numerator S U := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have ha : (numerator S U : ℝ) + 1 ≤ numerator S T := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    linarith

private noncomputable def ratio (n : ℕ) : ℝ := (σ 1 n : ℝ) / n

private theorem ratio_divisors {n : ℕ} (hn : 0 < n) :
    ratio n = ∑ d ∈ n.divisors, (1:ℝ)/d := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [ratio, ArithmeticFunction.sigma_one_apply, Nat.cast_sum,
    ← Nat.sum_div_divisors n (fun d => (d:ℝ)), Finset.sum_div]
  apply sum_congr rfl
  intro d hd
  have hd' : (d:ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hd']
  field_simp

private theorem ratio_ge_one {n : ℕ} (hn : 0 < n) : 1 ≤ ratio n := by
  rw [ratio_divisors hn]
  have hmem : 1 ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd n,hn.ne'⟩
  simpa using (single_le_sum (f := fun d : ℕ => (1:ℝ)/d) (fun d _ => by positivity) hmem)

private theorem ratio_mul {m n : ℕ} (hc : m.Coprime n) :
    ratio (m*n) = ratio m * ratio n := by
  rw [ratio, ratio, ratio, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc,
    Nat.cast_mul, Nat.cast_mul, mul_div_mul_comm]

private theorem gcd_mul_of_coprime {n a b : ℕ} (hc : a.Coprime b) :
    n.gcd (a*b) = n.gcd a * n.gcd b := by
  apply dvd_antisymm (Nat.gcd_mul_right_dvd_mul_gcd ..)
  apply Nat.dvd_gcd
  · exact (hc.gcd_both n n).mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_left ..) (Nat.gcd_dvd_left ..)
  · exact Nat.mul_dvd_mul (Nat.gcd_dvd_right ..) (Nat.gcd_dvd_right ..)

private theorem distinct_coprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    p.Coprime q :=
  hp.coprime_iff_not_dvd.mpr fun hd => hne ((Nat.dvd_prime hq).mp hd |>.resolve_left hp.ne_one)

private theorem coprime_power_product (S : Finset ℕ) (hprime : ∀ q ∈ S, Nat.Prime q)
    {p : ℕ} (hp : p.Prime) (hn : p ∉ S) (k : ℕ → ℕ) (e : ℕ) :
    (p^e).Coprime (∏ q ∈ S,q^k q) := by
  apply Nat.Coprime.prod_right
  intro q hq
  have hne : p ≠ q := fun heq => hn (heq ▸ hq)
  exact ((distinct_coprime hp (hprime q hq) hne).pow_left _).pow_right _

private theorem ratio_gcd_square {n p : ℕ} (hp : p.Prime) (hn : ¬ p^2 ∣ n) :
    ratio (n.gcd (p^2)) = if p ∣ n then (p+1 : ℝ)/p else 1 := by
  obtain ⟨i,hi,hg⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right n (p^2))
  have hi2 : i ≠ 2 := fun h => hn (h ▸ hg ▸ Nat.gcd_dvd_left _ _)
  have hi01 : i = 0 ∨ i = 1 := by omega
  have hpp : σ 1 p = p+1 := by
    simpa [Finset.sum_range_succ,add_comm] using (ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hp)
  rcases hi01 with rfl | rfl
  · simp only [pow_zero] at hg
    have hnd : ¬ p ∣ n := fun h => hp.not_dvd_one (hg ▸ Nat.dvd_gcd h (dvd_pow_self p (by decide)))
    simp [hg,hnd,ratio]
  · simp only [pow_one] at hg
    have hd : p ∣ n := hg ▸ Nat.gcd_dvd_left _ _
    simp [hg,hd,ratio,hpp]

private theorem ratio_gcd_product (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (n : ℕ) (hn : ∀ p ∈ S, ¬ p^2 ∣ n) :
    ratio (n.gcd (∏ p ∈ S,p^2)) =
      primeRatio S (S.filter (fun p => p ∣ n)) := by
  classical
  calc
    _ = ∏ p ∈ S, ratio (n.gcd (p^2)) := by
      clear hn
      induction S using Finset.induction_on with
      | empty => simp [ratio]
      | @insert p S hpS ih =>
        have hS : ∀ q ∈ S, q.Prime := fun q h => hprime q (mem_insert_of_mem h)
        have hc := coprime_power_product S hS (hprime p (mem_insert_self ..)) hpS (fun _ => 2) 2
        rw [prod_insert hpS, prod_insert hpS, gcd_mul_of_coprime hc,
          ratio_mul (hc.gcd_both n n), ih hS]
    _ = _ := by
      apply prod_congr rfl
      intro p hp
      rw [ratio_gcd_square (hprime p hp) (hn p hp)]
      simp [hp]

private def residueCode (p : ℕ) (hp : p.Prime) (r : Fin (p^2)) :
    Fin p × Fin (p-1) :=
  (⟨r.val / p, (Nat.div_lt_iff_lt_mul hp.pos).mpr (by simpa [pow_two] using r.isLt)⟩,
    ⟨if p ∣ r.val then 0 else r.val % p - 1, by
      split_ifs with hd
      · have := hp.two_le
        omega
      · have := Nat.mod_lt r.val hp.pos
        omega⟩)

private theorem residueCode_inj {p : ℕ} (hp : p.Prime) {r s : Fin (p^2)}
    (hs : p ∣ r.val ↔ p ∣ s.val) (h : residueCode p hp r = residueCode p hp s) : r = s := by
  have hdiv : r.val/p = s.val/p := congrArg (fun v => v.1.val) h
  have hmod : r.val%p = s.val%p := by
    by_cases hr : p ∣ r.val
    · rw [Nat.mod_eq_zero_of_dvd hr, Nat.mod_eq_zero_of_dvd (hs.mp hr)]
    · have hr' := Nat.dvd_iff_mod_eq_zero.not.mp hr
      have hs' := Nat.dvd_iff_mod_eq_zero.not.mp (fun h => hr (hs.mpr h))
      have hcode : r.val % p - 1 = s.val % p - 1 := by
        simpa [residueCode,hr,show ¬ p ∣ s.val from fun h => hr (hs.mpr h)] using
          congrArg (fun v => v.2.val) h
      omega
  apply Fin.ext
  calc
    r.val = r.val % p + p * (r.val/p) := (Nat.mod_add_div ..).symm
    _ = s.val := by rw [hdiv,hmod,Nat.mod_add_div]

private theorem congruent_square_product (S : Finset ℕ) (hp : ∀ p ∈ S, p.Prime)
    {a b : ℕ} (h : ∀ p ∈ S, a ≡ b [MOD p^2]) :
    a ≡ b [MOD ∏ p ∈ S, p^2] := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Nat.modEq_one]
  | @insert p S hpS ih =>
    have hS : ∀ q ∈ S, q.Prime := fun q hq => hp q (mem_insert_of_mem hq)
    rw [prod_insert hpS]
    exact (Nat.modEq_and_modEq_iff_modEq_mul
      (coprime_power_product S hS (hp p (mem_insert_self ..)) hpS (fun _ => 2) 2)).mp
      ⟨h p (mem_insert_self ..), ih hS (fun q hq => h q (mem_insert_of_mem hq))⟩

private noncomputable def intervalGood (S : Finset ℕ) (R : ℕ) (t l : ℝ) (N : ℕ) :
    Finset ℕ := open Classical in
  (Icc 1 N).filter fun n =>
    (∀ p ∈ S, ¬ p^2 ∣ n) ∧
    t ≤ ratio (n.gcd (R * ∏ p ∈ S,p^2)) ∧
    ratio (n.gcd (R * ∏ p ∈ S,p^2)) ≤ t+l

set_option maxHeartbeats 500000 in
private theorem card_intervalGood (S : Finset ℕ) (hp : ∀ p ∈ S, p.Prime ∧ 2 < p)
    (R : ℕ) (hR : 0 < R) (hc : R.Coprime (∏ p ∈ S,p^2)) (t l : ℝ)
    (hl : l < ((∏ p ∈ S,p : ℕ) : ℝ)⁻¹) (N : ℕ) :
    (intervalGood S R t l N).card ≤
      (N/(R * ∏ p ∈ S,p^2)+1)*R*∏ p ∈ S,p*(p-1) := by
  classical
  let Q := R * ∏ p ∈ S,p^2
  let good := intervalGood S R t l N
  let f : good → Fin (N/Q+1) × Fin R × (∀ p : S, Fin p.val × Fin (p.val-1)) := fun n =>
    (⟨n.val/Q, Nat.lt_succ_of_le (Nat.div_le_div_right (mem_Icc.mp (mem_filter.mp n.prop).1).2)⟩,
      ⟨n.val%R,Nat.mod_lt _ hR⟩,
      fun p => residueCode p (hp p p.prop).1
        ⟨n.val%(p.val^2), Nat.mod_lt _ (pow_pos (hp p p.prop).1.pos _)⟩)
  have hf : Function.Injective f := by
    intro a b hab
    have hdiv : a.val/Q = b.val/Q := congrArg (fun x => x.1.val) hab
    have hmodR : a.val%R = b.val%R := congrArg (fun x => x.2.1.val) hab
    have hgR : a.val.gcd R = b.val.gcd R := by
      rw [Nat.gcd_comm a.val R, Nat.gcd_comm b.val R, Nat.gcd_rec R a.val, Nat.gcd_rec R b.val, hmodR]
    obtain ⟨ha, halo,hahi⟩ := (mem_filter.mp a.prop).2
    obtain ⟨hb, hblo,hbhi⟩ := (mem_filter.mp b.prop).2
    have hmul (n : ℕ) (hn : ∀ p ∈ S, ¬ p^2 ∣ n) :
        ratio (n.gcd Q) = ratio (n.gcd R) * primeRatio S (S.filter (fun p => p ∣ n)) := by
      simp only [Q]
      rw [gcd_mul_of_coprime hc, ratio_mul (hc.gcd_both n n),
        ratio_gcd_product S (fun p h => (hp p h).1) n hn]
    change t ≤ ratio (a.val.gcd Q) at halo
    change ratio (a.val.gcd Q) ≤ t+l at hahi
    change t ≤ ratio (b.val.gcd Q) at hblo
    change ratio (b.val.gcd Q) ≤ t+l at hbhi
    have habs : |ratio (a.val.gcd Q) - ratio (b.val.gcd Q)| ≤ l := by
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    have hge := ratio_ge_one (Nat.gcd_pos_of_pos_right a.val hR)
    rw [hmul _ ha, hmul _ hb, ← hgR, ← mul_sub, abs_mul, abs_of_pos (by linarith)] at habs
    have hclose :
        |primeRatio S (S.filter (fun p => p ∣ a.val)) -
          primeRatio S (S.filter (fun p => p ∣ b.val))| ≤ l :=
      (le_mul_of_one_le_left (abs_nonneg _) hge).trans habs
    have heq : ∀ p ∈ S, p ∣ a.val ↔ p ∣ b.val := by
      intro p hpS
      by_contra hne
      have hsep := primeRatio_sep S (S.filter (fun p => p ∣ a.val))
        (S.filter (fun p => p ∣ b.val)) hp ⟨p,hpS,by simpa [hpS] using hne⟩
      exact (not_le_of_gt hl) (hsep.trans hclose)
    have hmod (p : ℕ) (hpS : p ∈ S) : a.val ≡ b.val [MOD p^2] := by
      have hdp : p ∣ p^2 := dvd_pow_self p (by decide)
      have hstatus : p ∣ a.val % (p^2) ↔ p ∣ b.val % (p^2) := by
        simp only [Nat.dvd_iff_mod_eq_zero, Nat.mod_mod_of_dvd _ hdp] at heq ⊢
        exact heq p hpS
      exact congrArg Fin.val (residueCode_inj (hp p hpS).1 hstatus
        (congrArg (fun x => x.2.2 ⟨p,hpS⟩) hab))
    have hmodQ : a.val % Q = b.val % Q := (Nat.modEq_and_modEq_iff_modEq_mul hc).mp
      ⟨hmodR, congruent_square_product S (fun p hpS => (hp p hpS).1) hmod⟩
    apply Subtype.ext
    calc
      a.val = a.val % Q + Q * (a.val/Q) := (Nat.mod_add_div ..).symm
      _ = b.val := by rw [hdiv,hmodQ,Nat.mod_add_div]
  have hcard := Fintype.card_le_of_injective _ hf
  simp only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fin,Fintype.card_pi] at hcard
  rw [show (∏ p : S,p.val*(p.val-1)) = ∏ p ∈ S,p*(p-1) from
    Finset.prod_coe_sort (s := S) (f := fun p : ℕ => p*(p-1))] at hcard
  simpa [Nat.mul_assoc] using hcard

private theorem partial_le_gcd_ratio (S : Finset ℕ) (B n : ℕ) (hn : 0 < n)
    (hS : ∀ p ∈ S, ¬ p^2 ∣ n) :
    let T := ((range (B+1)).filter Nat.Prime) \ S
    let R := ∏ p ∈ T,p^B
    (∑ d ∈ n.divisors.filter (· ≤ B), (1:ℝ)/d) ≤ ratio (n.gcd (R * ∏ p ∈ S,p^2)) := by
  classical
  let T := ((range (B+1)).filter Nat.Prime) \ S
  let R := ∏ p ∈ T,p^B
  let P := ∏ p ∈ S,p^2
  let Q := R * P
  have hg : 0 < n.gcd Q := Nat.gcd_pos_of_pos_left _ hn
  change _ ≤ ratio (n.gcd Q)
  rw [ratio_divisors hg]
  refine sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => by positivity)
  intro d hd
  have hdv := Nat.dvd_of_mem_divisors (mem_filter.mp hd).1
  have hd0 := Nat.pos_of_mem_divisors (mem_filter.mp hd).1
  have hdB := (mem_filter.mp hd).2
  have dvdQ : d ∣ Q := by
    let U := S ∪ T
    let e : ℕ → ℕ := fun p => if p ∈ S then 2 else B
    have hUT : Disjoint S T := disjoint_sdiff_self_right
    have hUprod : ∏ p ∈ U,p^e p = Q := by
      simp only [U]
      rw [prod_union hUT]
      have hps : ∏ p ∈ S,p^e p = P := prod_congr rfl (fun p hp => by simp [e,hp])
      have hpt : ∏ p ∈ T,p^e p = R :=
        prod_congr rfl (fun p hp => by
          have hn := (mem_sdiff.mp hp).2
          simp [e,hn])
      rw [hps,hpt]
      exact mul_comm _ _
    have hsub : d.primeFactors ⊆ U := by
      intro p hp
      have hpd := Nat.dvd_of_mem_primeFactors hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      by_cases hs : p ∈ S
      · exact mem_union_left _ hs
      · exact mem_union_right _ (mem_sdiff.mpr
          ⟨mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_of_dvd hd0 hpd).trans hdB)),hprime⟩,hs⟩)
    rw [← hUprod, ← Nat.prod_factorization_pow_eq_self hd0.ne']
    change (∏ p ∈ d.primeFactors,p^d.factorization p) ∣ _
    refine (prod_dvd_prod_of_dvd _ _ ?_).trans (prod_dvd_prod_of_subset _ _ _ hsub)
    intro p hp
    have hprim := Nat.prime_of_mem_primeFactors hp
    apply pow_dvd_pow
    by_cases hs : p ∈ S
    · have hfact : ¬ 2 ≤ d.factorization p := fun hh =>
        hS p hs (((hprim.pow_dvd_iff_le_factorization hd0.ne').mpr hh).trans hdv)
      simpa [e,hs] using (show d.factorization p ≤ 2 by omega)
    · simp only [e,if_neg hs]
      exact Nat.factorization_le_of_le_pow (hdB.trans (Nat.lt_pow_self hprim.one_lt).le)
  exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hdv dvdQ,hg.ne'⟩

private theorem gcd_ratio_le_full (n Q : ℕ) (hn : 0 < n) : ratio (n.gcd Q) ≤ ratio n := by
  have hg : 0 < n.gcd Q := Nat.gcd_pos_of_pos_left _ hn
  rw [ratio_divisors hg, ratio_divisors hn]
  apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
  intro d hd
  exact Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors hd).trans (Nat.gcd_dvd_left _ _), hn.ne'⟩

private theorem prime_sum_above (K : ℕ) (L : ℝ) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ K < p) ∧ L < ∑ p ∈ S, (1:ℝ)/p := by
  classical
  let f : ℕ → ℝ := fun n => if n.Prime then (1:ℝ)/n else 0
  have hf : ¬ Summable f := by
    intro h
    apply not_summable_one_div_on_primes
    apply h.congr
    intro n
    by_cases hn : n.Prime <;> simp [f,hn]
  have hf0 : 0 ≤ f := fun k => by unfold f; split <;> positivity
  let U := range (K+1)
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, L + (∑ p ∈ U, f p) < ∑ p ∈ T, f p := by
    by_contra! h
    exact hf (summable_of_sum_le hf0 h)
  let S := (T \ U).filter Nat.Prime
  refine ⟨S, ?_, ?_⟩
  · intro p hp
    have h := mem_filter.mp hp
    exact ⟨h.2, by have := (mem_sdiff.mp h.1).2; simpa [U,not_lt] using this⟩
  · have hsplit := sum_inter_add_sum_sdiff T U f
    have hsmall : (∑ p ∈ T ∩ U, f p) ≤ ∑ p ∈ U, f p :=
      sum_le_sum_of_subset_of_nonneg inter_subset_right (fun p _ _ => hf0 p)
    have hl : L < ∑ p ∈ T \ U, f p := by linarith
    simpa only [S,sum_filter,f] using hl

private noncomputable def squareBad (S : Finset ℕ) (N : ℕ) : Finset ℕ := open Classical in
  (Icc 1 N).filter fun n => ∃ p ∈ S,p^2 ∣ n

private theorem squareBad_bound (S : Finset ℕ) (K N : ℕ) (hK : K ≠ 0)
    (hS : ∀ p ∈ S, K < p) :
    ((squareBad S N).card : ℝ) ≤ (N : ℝ) * (K : ℝ)⁻¹ := by
  classical
  have hU : squareBad S N = S.biUnion (fun p => (Ioc 0 N).filter (fun n => p^2 ∣ n)) := by
    ext n
    simp [squareBad, Nat.succ_le_iff, and_left_comm, and_assoc]
    aesop
  rw [hU]
  calc
    _ ≤ ∑ p ∈ S, (((Ioc 0 N).filter (fun n => p^2 ∣ n)).card : ℝ) := by
      exact_mod_cast card_biUnion_le
    _ = ∑ p ∈ S, ((N/(p^2) : ℕ) : ℝ) := by simp [Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ ∑ p ∈ S, (N : ℝ) * ((p : ℝ)^2)⁻¹ := by
      apply sum_le_sum
      intro p hp
      have hp0 : 0 < p := (Nat.zero_le K).trans_lt (hS p hp)
      have hpR : (0:ℝ)<p := by exact_mod_cast hp0
      rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hpR 2), ← Nat.cast_pow]
      exact_mod_cast Nat.div_mul_le_self N (p^2)
    _ ≤ (N : ℝ) * (K : ℝ)⁻¹ := by
      rw [← mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      let M := max K (S.sup id)
      have hsub : S ⊆ Ioc K M := fun p hp => mem_Ioc.mpr
        ⟨hS p hp, (show p ≤ S.sup id from Finset.le_sup (f := id) hp).trans (le_max_right ..)⟩
      exact (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
        ((sum_Ioc_inv_sq_le_sub hK (le_max_left K (S.sup id))).trans
          (sub_le_self _ (show 0 ≤ (M : ℝ)⁻¹ by positivity)))

private theorem intervalGood_bound (S : Finset ℕ) (hp : ∀ p ∈ S, p.Prime ∧ 2 < p)
    (R : ℕ) (hR : 0 < R) (hc : R.Coprime (∏ p ∈ S,p^2)) (t l : ℝ)
    (hl : l < ((∏ p ∈ S,p : ℕ) : ℝ)⁻¹) (N : ℕ) (hN : R * ∏ p ∈ S,p^2 ≤ N) :
    ((intervalGood S R t l N).card : ℝ) ≤
      2*(N : ℝ)*Real.exp (-(∑ p ∈ S,(1:ℝ)/p)) := by
  let Q := R * ∏ p ∈ S,p^2
  let A := R * ∏ p ∈ S,p*(p-1)
  have hQ : 0 < Q := Nat.mul_pos hR (Finset.prod_pos (fun p h => pow_pos (hp p h).1.pos _))
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have ha : (A : ℝ) / Q ≤ Real.exp (-(∑ p ∈ S,(1:ℝ)/p)) := by
    calc
      (A : ℝ) / Q = ∏ p ∈ S, (1 - (1:ℝ)/p) := by
        have hRR : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
        simp only [A,Q,Nat.cast_mul,Nat.cast_prod,Nat.cast_pow,mul_div_mul_left _ _ hRR,
          ← prod_div_distrib]
        apply prod_congr rfl
        intro p h
        have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (hp p h).1.ne_zero
        rw [Nat.cast_sub (hp p h).1.one_lt.le, Nat.cast_one]
        field_simp
      _ ≤ ∏ p ∈ S, Real.exp (-((1:ℝ)/p)) := by
        apply Finset.prod_le_prod
        · intro p h
          have h1 : (1 : ℝ) ≤ p := by exact_mod_cast (hp p h).1.one_lt.le
          have h0 : (0 : ℝ) < p := by linarith
          rw [sub_nonneg, div_le_iff₀ h0, one_mul]
          exact h1
        · intro p h
          simpa [sub_eq_add_neg,add_comm] using Real.add_one_le_exp (-((1:ℝ)/p))
      _ = _ := by rw [← Real.exp_sum, sum_neg_distrib]
  have hd : ((N/Q : ℕ) : ℝ) ≤ (N : ℝ)/Q := by
    rw [le_div_iff₀ hQR]
    exact_mod_cast Nat.div_mul_le_self N Q
  have hQN : (Q : ℝ) ≤ N := by exact_mod_cast hN
  calc
    _ ≤ (((N/Q : ℕ) : ℝ)+1)*(A : ℝ) := by
      rw [← Nat.cast_one,← Nat.cast_add,← Nat.cast_mul]
      exact_mod_cast (show (intervalGood S R t l N).card ≤ (N/Q+1)*A by
        simpa only [Q,A,Nat.mul_assoc] using card_intervalGood S hp R hR hc t l hl N)
    _ ≤ ((N : ℝ)/Q+1)*(A : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = ((N : ℝ)+(Q : ℝ))*((A : ℝ)/Q) := by field_simp
    _ ≤ ((N : ℝ)+(Q : ℝ))*Real.exp (-(∑ p ∈ S,(1:ℝ)/p)) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

set_option maxHeartbeats 500000 in
theorem ratio_antiConcentration
    (tailBound : ∀ η ε : ℝ, 0<η → 0<ε → ∃ B : ℕ, ∀ᶠ N : ℕ in atTop,
      (((Icc 1 N).filter (fun n => η ≤ ratio n - (∑ d ∈ n.divisors.filter (· ≤ B), (1:ℝ)/d))).card:ℝ)
        ≤ ε*N) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ N : ℕ in atTop,
      (((Icc 1 N).filter (fun n => 2 < ratio n ∧ ratio n ≤ 2+η)).card:ℝ) ≤ ε*N := by
  classical
  obtain ⟨K,hK⟩ := exists_nat_gt (max 2 (1 / (ε/3)))
  have hK2 : 2 ≤ K := by exact_mod_cast ((le_max_left _ _).trans_lt hK).le
  have hKR : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hiK : (K : ℝ)⁻¹ ≤ ε/3 := by
    rw [← one_div, div_le_iff₀ hKR]
    exact ((div_lt_iff₀ (by positivity : 0 < ε/3)).mp
      ((le_max_right _ _).trans_lt hK)).le.trans (by rw [mul_comm])
  obtain ⟨S,hS,hsum⟩ := prime_sum_above K (-Real.log (ε/6))
  have hp : ∀ p ∈ S,p.Prime ∧ 2 < p := fun p h => ⟨(hS p h).1,hK2.trans_lt (hS p h).2⟩
  let P := ∏ p ∈ S,p
  have hP : 0 < P := Finset.prod_pos (fun p h => (hp p h).1.pos)
  have hiP : 0 < (P : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hP)
  let η : ℝ := (P : ℝ)⁻¹/4
  have hη : 0 < η := div_pos hiP (by norm_num)
  have hwidth : 2*η < (P : ℝ)⁻¹ := by simp only [η]; linarith
  obtain ⟨B,hB⟩ := tailBound η (ε/3) hη (by positivity)
  let T := ((range (B+1)).filter Nat.Prime) \ S
  let R := ∏ p ∈ T,p^B
  let Q := R * ∏ p ∈ S,p^2
  have hR : 0 < R := Finset.prod_pos fun p h => pow_pos
    (mem_filter.mp (Finset.mem_sdiff.mp h).1).2.pos _
  have hc : R.Coprime (∏ p ∈ S,p^2) := by
    apply Nat.Coprime.prod_left
    intro p hpT
    exact coprime_power_product S (fun q h => (hp q h).1)
      (mem_filter.mp (Finset.mem_sdiff.mp hpT).1).2 (Finset.mem_sdiff.mp hpT).2 (fun _ => 2) B
  refine ⟨η,hη,?_⟩
  filter_upwards [hB,eventually_ge_atTop Q] with N htail hN
  let near := (Icc 1 N).filter (fun n => 2 < ratio n ∧ ratio n ≤ 2+η)
  let largeTail := (Icc 1 N).filter (fun n =>
    η ≤ ratio n - (∑ d ∈ n.divisors.filter (· ≤ B), (1:ℝ)/d))
  let good := intervalGood S R (2-η) (2*η) N
  have hsub : near ⊆ (squareBad S N ∪ largeTail) ∪ good := by
    intro n hn
    obtain ⟨hnN,hnlo,hnhi⟩ := mem_filter.mp hn
    by_cases hs : n ∈ squareBad S N
    · exact mem_union_left _ (mem_union_left _ hs)
    by_cases ht : n ∈ largeTail
    · exact mem_union_left _ (mem_union_right _ ht)
    have hnp : 0 < n := (mem_Icc.mp hnN).1
    have hsn : ∀ p ∈ S, ¬ p^2 ∣ n := by
      intro p hp hd
      exact hs (mem_filter.mpr ⟨hnN,p,hp,hd⟩)
    have htn : ratio n - (∑ d ∈ n.divisors.filter (· ≤ B), (1:ℝ)/d) < η := by
      exact lt_of_not_ge fun h => ht (mem_filter.mpr ⟨hnN,h⟩)
    have h := partial_le_gcd_ratio S B n hnp hsn
    have h' : ratio (n.gcd Q) ≤ ratio n := gcd_ratio_le_full n Q hnp
    apply mem_union_right _
    refine mem_filter.mpr ⟨hnN,hsn,?_,?_⟩
    · change 2-η ≤ ratio (n.gcd Q)
      change (∑ d ∈ n.divisors.filter (· ≤ B), (1:ℝ)/d) ≤ ratio (n.gcd Q) at h
      linarith
    · change ratio (n.gcd Q) ≤ (2-η)+2*η
      linarith
  have hb := squareBad_bound S K N (by omega) (fun p h => (hS p h).2)
  have hgood := intervalGood_bound S hp R hR hc (2-η) (2*η) hwidth N hN
  have hsmall : Real.exp (-(∑ p ∈ S,(1:ℝ)/p)) ≤ ε/6 := by
    rw [← Real.exp_log (by positivity : 0 < ε/6), Real.exp_le_exp]
    linarith
  change (near.card : ℝ) ≤ ε*N
  calc
    _ ≤ (squareBad S N).card + (largeTail.card : ℝ) + (good.card : ℝ) := by
      exact_mod_cast ((card_le_card hsub).trans
        (card_union_le _ _ |>.trans (Nat.add_le_add_right (card_union_le _ _) _)))
    _ ≤ (N : ℝ)*(K : ℝ)⁻¹ + ε/3*N + 2*N*Real.exp (-(∑ p ∈ S,(1:ℝ)/p)) := by
      exact add_le_add (add_le_add hb htail) hgood
    _ ≤ ε*N := by
      have h₁ := mul_le_mul_of_nonneg_left hiK (by positivity : (0:ℝ) ≤ N)
      have h₂ := mul_le_mul_of_nonneg_left hsmall (by positivity : (0:ℝ) ≤ 2*N)
      linarith

end OMA.E830

namespace OMA.E830

private theorem sigma_ratio (n : ℕ) (hn : 0 < n) :
    ((σ 1 n : ℝ) / n) = ∑ d ∈ n.divisors, (1 : ℝ) / d := by
  rw [ArithmeticFunction.sigma_eq_sum_div 1 n]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdpos := Nat.pos_of_mem_divisors hd
  have hprod : ((n / d : ℕ) : ℝ) * d = n := by
    exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
  simp only [pow_one]
  apply (div_eq_div_iff (by exact_mod_cast hn.ne') (by exact_mod_cast hdpos.ne')).mpr
  simpa using hprod

theorem divisorTail : ∀ η ε : ℝ, 0<η → 0<ε → ∃ B : ℕ, ∀ᶠ N : ℕ in atTop,
  (((Icc 1 N).filter (fun n =>
    η ≤ ((σ 1 n : ℝ)/n) - (∑ d ∈ n.divisors.filter (· ≤ B), (1:ℝ)/d))).card:ℝ) ≤ ε*N := by
  intro η ε hη hε
  have hprod : 0 < η * ε := mul_pos hη hε
  obtain ⟨B,hB⟩ := exists_nat_gt (max 1 (1 / (η * ε)))
  have hBpos : 0 < B := by
    have h1 := (le_max_left _ _).trans_lt hB
    exact_mod_cast (show (0 : ℝ) < B from zero_lt_one.trans h1)
  have hBinv : (B : ℝ)⁻¹ ≤ η * ε := by
    rw [← one_div]
    apply (div_le_iff₀ (by exact_mod_cast hBpos)).mpr
    simpa [mul_comm (η*ε)] using
      ((div_lt_iff₀ hprod).mp ((le_max_right _ _).trans_lt hB)).le
  refine ⟨B,?_⟩
  filter_upwards [eventually_ge_atTop B] with N hN
  let U := Icc 1 N
  let D := Ioc B N
  let tail (n : ℕ) : ℝ := (σ 1 n : ℝ) / n -
    ∑ d ∈ n.divisors.filter (· ≤ B), (1 : ℝ) / d
  let bad := U.filter (fun n => η ≤ tail n)
  change (bad.card : ℝ) ≤ ε * N
  have htail (n : ℕ) (hn : n ∈ U) :
      tail n = ∑ d ∈ D.filter (· ∣ n), (1 : ℝ)/d := by
    have hnp : 0 < n := (mem_Icc.mp hn).1
    have hfilter : n.divisors.filter (fun d => ¬ d ≤ B) = D.filter (· ∣ n) := by
      ext d
      simp only [mem_filter,Nat.mem_divisors,mem_Ioc,D,not_le]
      constructor
      · rintro ⟨⟨hdiv,_⟩,hb⟩
        exact ⟨⟨hb,(Nat.le_of_dvd hnp hdiv).trans (mem_Icc.mp hn).2⟩,hdiv⟩
      · rintro ⟨⟨hb,_⟩,hd⟩
        exact ⟨⟨hd,hnp.ne'⟩,hb⟩
    unfold tail
    rw [sigma_ratio n hnp,← Finset.sum_filter_add_sum_filter_not _ (· ≤ B),
        add_sub_cancel_left,hfilter]
  have hcount (d : ℕ) : (U.filter (d ∣ ·)).card = N / d := by
    have hU : U = Ioc 0 N := by
      ext n
      simp [U,Nat.succ_le_iff]
    rw [hU,Nat.Ioc_filter_dvd_card_eq_div]
  have hsum : (∑ n ∈ U, tail n) ≤ (N : ℝ) * (B : ℝ)⁻¹ := calc
    (∑ n ∈ U, tail n) = ∑ n ∈ U, ∑ d ∈ D, if d ∣ n then (1 : ℝ)/d else 0 :=
      Finset.sum_congr rfl (fun n hn => by rw [htail n hn,Finset.sum_filter])
    _ = ∑ d ∈ D, ∑ n ∈ U, if d ∣ n then (1 : ℝ)/d else 0 := Finset.sum_comm
    _ = ∑ d ∈ D, ((N / d : ℕ) : ℝ) * (1/d) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,hcount]
    _ ≤ ∑ d ∈ D, (N : ℝ) * ((d : ℝ)^2)⁻¹ := by
      apply Finset.sum_le_sum
      intro d _
      calc
        ((N / d : ℕ) : ℝ) * (1/d) ≤ ((N : ℝ)/d) * (1/d) :=
          mul_le_mul_of_nonneg_right Nat.cast_div_le (by positivity)
        _ = _ := by rw [div_mul_div_comm,pow_two,div_eq_mul_inv,mul_one]
    _ = (N : ℝ) * ∑ d ∈ D, ((d : ℝ)^2)⁻¹ := (Finset.mul_sum ..).symm
    _ ≤ (N : ℝ) * (B : ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (sum_Ioc_inv_sq_le_sub hBpos.ne' hN).trans (sub_le_self _ (by positivity))
  have hb : (bad.card : ℝ) * η ≤ (N : ℝ) * (η * ε) := calc
    (bad.card : ℝ) * η = ∑ n ∈ bad, η := by simp
    _ ≤ ∑ n ∈ bad, tail n := Finset.sum_le_sum (fun _ hn => (mem_filter.mp hn).2)
    _ ≤ ∑ n ∈ U, tail n := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
      intro n hn _
      rw [htail n hn]
      positivity
    _ ≤ (N : ℝ) * (B : ℝ)⁻¹ := hsum
    _ ≤ (N : ℝ) * (η * ε) := mul_le_mul_of_nonneg_left hBinv (by positivity)
  exact le_of_mul_le_mul_right (by simpa [mul_assoc,mul_left_comm,mul_comm] using hb) hη

end OMA.E830

theorem OMA.solution : OMA.R_Erdos830_erdos_830_variants_erdos_R1.H3 := OMA.E830.ratio_antiConcentration OMA.E830.divisorTail