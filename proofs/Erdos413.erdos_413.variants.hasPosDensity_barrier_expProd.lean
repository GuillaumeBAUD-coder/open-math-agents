import FormalConjectures.ErdosProblems.«413»
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! The product of the prime exponents counts the squarefull divisors. -/

open Finset Filter Finsupp
open scoped Topology Classical

namespace OMA

def Squarefull (d : ℕ) : Prop := d ≠ 0 ∧ ∀ p, d.factorization p ≠ 1

theorem squarefull_one : Squarefull 1 := by simp [Squarefull]

theorem squarefull_coprime {a b : ℕ} (h : a.Coprime b) (ha : a ≠ 0) (hb : b ≠ 0) :
    Squarefull (a * b) ↔ Squarefull a ∧ Squarefull b := by
  unfold Squarefull
  rw [and_iff_right ha, and_iff_right hb, and_iff_right (mul_ne_zero ha hb),
    Nat.factorization_mul_of_coprime h]
  simp only [Finsupp.add_apply]
  have hz (p : ℕ) : a.factorization p = 0 ∨ b.factorization p = 0 := by
    by_contra! hh
    have ha' : p ∈ a.primeFactors := by simpa [← Nat.support_factorization] using hh.1
    have hb' : p ∈ b.primeFactors := by simpa [← Nat.support_factorization] using hh.2
    exact Finset.disjoint_left.mp h.disjoint_primeFactors ha' hb'
  constructor
  · intro hh
    constructor <;> intro p hp
    · rcases hz p with hza | hzb
      · omega
      · exact hh p (by omega)
    · rcases hz p with hza | hzb
      · exact hh p (by omega)
      · omega
  · rintro ⟨h₁,h₂⟩ p
    rcases hz p with hza | hzb
    · simpa [hza] using h₂ p
    · simpa [hzb] using h₁ p

theorem squarefull_prime_pow {p k : ℕ} (hp : p.Prime) :
    Squarefull (p ^ k) ↔ k ≠ 1 := by
  unfold Squarefull
  rw [and_iff_right (pow_ne_zero k hp.ne_zero), hp.factorization_pow]
  constructor
  · intro h
    simpa using h p
  · intro hk q
    by_cases h : p = q
    · subst q
      simpa using hk
    · simp [h]

noncomputable def squarefullIndicator : ArithmeticFunction ℕ := by
  classical
  exact ⟨fun d => if Squarefull d then 1 else 0, by simp [Squarefull]⟩

theorem squarefullIndicator_apply (d : ℕ) :
    squarefullIndicator d = (if Squarefull d then 1 else 0) := by
  classical
  rfl

theorem squarefullIndicator_mult : squarefullIndicator.IsMultiplicative := by
  classical
  refine ⟨by simp [squarefullIndicator_apply, squarefull_one], ?_⟩
  intro a b hab
  by_cases ha : a = 0
  · subst a
    simp
  by_cases hb : b = 0
  · subst b
    simp
  rw [squarefullIndicator_apply, squarefullIndicator_apply, squarefullIndicator_apply,
    squarefull_coprime hab ha hb]
  by_cases A : Squarefull a <;> by_cases B : Squarefull b <;> simp [A, B]

theorem squarefull_prime_pow_sum {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    (ArithmeticFunction.zeta * squarefullIndicator) (p ^ k) = k := by
  classical
  rw [ArithmeticFunction.zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
  simp only [squarefullIndicator_apply, squarefull_prime_pow hp]
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : k = 0
    · subst k
      decide
    · rw [Finset.sum_range_succ, ih (by omega)]
      simp [h]

theorem expProd_eq_card_squarefull (m : ℕ) (hm : m ≠ 0) :
    Erdos413.expProd m = (m.divisors.filter Squarefull).card := by
  classical
  let f : ArithmeticFunction ℕ := ArithmeticFunction.zeta * squarefullIndicator
  have hf : f.IsMultiplicative := ArithmeticFunction.isMultiplicative_zeta.mul squarefullIndicator_mult
  have hprod := Nat.multiplicative_factorization f
    (fun a b h => hf.map_mul_of_coprime h) hf.map_one hm
  have hcard : f m = (m.divisors.filter Squarefull).card := by
    rw [ArithmeticFunction.zeta_mul_apply, Finset.card_filter]
    exact Finset.sum_congr rfl (fun d _ => squarefullIndicator_apply d)
  rw [← hcard, hprod, Erdos413.expProd, Finsupp.prod, Finsupp.prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  exact (squarefull_prime_pow_sum (Nat.prime_of_mem_primeFactors (by simpa using hp))
    (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp))).symm

theorem squarefull_repr (d : ℕ) (hd : Squarefull d) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ d = a ^ 2 * b ^ 3 := by
  induction d using Nat.recOnPrimeCoprime with
  | zero => exact (hd.1 rfl).elim
  | prime_pow p k hp =>
    have hk := (squarefull_prime_pow hp).mp hd
    by_cases h : k % 2 = 0
    · refine ⟨p ^ (k / 2), 1, pow_pos hp.pos _, by decide, ?_⟩
      rw [one_pow, mul_one, ← pow_mul]
      congr 1
      omega
    · refine ⟨p ^ ((k - 3) / 2), p, pow_pos hp.pos _, hp.pos, ?_⟩
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
  | coprime a b ha hb hab iha ihb =>
    obtain ⟨ha', hb'⟩ := (squarefull_coprime hab (by omega) (by omega)).mp hd
    obtain ⟨x, y, hx, hy, e⟩ := iha ha'
    obtain ⟨u, v, hu, hv, f⟩ := ihb hb'
    exact ⟨x * u, y * v, by positivity, by positivity, by rw [e, f]; ring⟩

end OMA

open Finset Filter
open scoped Topology

namespace OMA

noncomputable def powerTerm (q n : ℕ) : ℝ := 1 / ((n : ℝ) + 1) ^ q

theorem powerTerm_nonneg (q n : ℕ) : 0 ≤ powerTerm q n := by
  unfold powerTerm
  positivity

theorem powerTerm_summable (q : ℕ) (hq : 1 < q) : Summable (powerTerm q) := by
  unfold powerTerm
  simpa [Nat.cast_add] using
    (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ q) 1).2
      (Real.summable_one_div_nat_pow.2 hq)

theorem sum_telescope_bound {f g : ℕ → ℝ} (hf : Summable f)
    (hg : ∀ n, 0 ≤ g n) (h : ∀ n, f n ≤ g n - g (n + 1)) :
    (∑' n, f n) ≤ g 0 := by
  apply le_of_tendsto' hf.hasSum.tendsto_sum_nat
  intro n
  have hpartial (k : ℕ) : (∑ i ∈ range k, f i) ≤ g 0 - g k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      linarith [h k]
  linarith [hpartial n, hg n]

theorem square_tail_step (x : ℝ) (hx : 0 < x) :
    1 / (x + 1)^2 ≤ 1 / x - 1 / (x + 1) := by
  have hx' : 0 < x + 1 := by positivity
  calc
    1 / (x + 1)^2 ≤ 1 / (x * (x + 1)) := by
      gcongr
      nlinarith
    _ = 1 / x - 1 / (x + 1) := by field_simp; ring

theorem cube_tail_step (x : ℝ) (hx : 0 < x) :
    1 / (x + 1)^3 ≤ (1 / 2) / x^2 - (1 / 2) / (x + 1)^2 := by
  have hx' : 0 < x + 1 := by positivity
  have heq : (1 / 2) / x^2 - (1 / 2) / (x + 1)^2 =
      (2*x + 1) / (2*x^2*(x + 1)^2) := by field_simp; ring
  rw [heq]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hf : 0 ≤ (x + 1)^2 * (3*x + 1) := by positivity
  nlinarith only [hf]

theorem square_series_bound : (∑' n, powerTerm 2 n) ≤ 33/20 := by
  have hs := powerTerm_summable 2 (by decide)
  rw [← hs.sum_add_tsum_nat_add 10]
  have ht := sum_telescope_bound
    ((summable_nat_add_iff 10).2 hs)
    (g := fun n : ℕ => 1 / ((n : ℝ) + 10)) (by intro; positivity) (by
      intro n
      have h := square_tail_step ((n : ℝ) + 10) (by positivity)
      simpa [powerTerm, Nat.cast_add, add_assoc, add_left_comm, add_comm] using h)
  have hb : (∑ i ∈ range 10, powerTerm 2 i) + 1/10 ≤ (33/20 : ℝ) := by
    norm_num [Finset.sum_range_succ, powerTerm]
  simp only [Nat.cast_zero, zero_add] at ht
  linarith

theorem cube_series_bound : (∑' n, powerTerm 3 n) ≤ 121/100 := by
  have hs := powerTerm_summable 3 (by decide)
  rw [← hs.sum_add_tsum_nat_add 4]
  have ht := sum_telescope_bound
    ((summable_nat_add_iff 4).2 hs)
    (g := fun n : ℕ => (1 / 2) / ((n : ℝ) + 4)^2) (by intro; positivity) (by
      intro n
      have h := cube_tail_step ((n : ℝ) + 4) (by positivity)
      simpa [powerTerm, Nat.cast_add, add_assoc, add_left_comm, add_comm] using h)
  have hb : (∑ i ∈ range 4, powerTerm 3 i) + 1/32 ≤ (121/100 : ℝ) := by
    norm_num [Finset.sum_range_succ, powerTerm]
  norm_num at ht
  linarith

theorem squarefull_series : Summable (Set.indicator {d | Squarefull d} (fun d : ℕ => 1 / (d : ℝ))) ∧
    (∑' d, Set.indicator {d | Squarefull d} (fun d : ℕ => 1 / (d : ℝ)) d) ≤ 3993/2000 := by
  classical
  have hrepr (d : {d : ℕ // Squarefull d}) :
      ∃ x : ℕ × ℕ, d.val = (x.1 + 1)^2 * (x.2 + 1)^3 := by
    obtain ⟨a,b,ha,hb,h⟩ := squarefull_repr d.val d.property
    exact ⟨(a-1,b-1), by simp [Nat.sub_add_cancel (by omega : 1 ≤ a),
      Nat.sub_add_cancel (by omega : 1 ≤ b), h]⟩
  let e : {d : ℕ // Squarefull d} → ℕ × ℕ := fun d => Classical.choose (hrepr d)
  have he (d : {d : ℕ // Squarefull d}) := Classical.choose_spec (hrepr d)
  have hi : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    exact (he a).trans ((congrArg (fun x : ℕ × ℕ => (x.1+1)^2 * (x.2+1)^3) hab).trans (he b).symm)
  let t : ℕ × ℕ → ℝ := fun x => powerTerm 2 x.1 * powerTerm 3 x.2
  have h₂ := powerTerm_summable 2 (by decide)
  have h₃ := powerTerm_summable 3 (by decide)
  have ht : Summable t := h₂.mul_of_nonneg h₃ (powerTerm_nonneg 2) (powerTerm_nonneg 3)
  have heq (d : {d : ℕ // Squarefull d}) : t (e d) = 1 / (d.val : ℝ) := by
    have h : (d.val : ℝ) = ((e d).1 + 1 : ℝ)^2 * ((e d).2 + 1 : ℝ)^3 := by
      exact_mod_cast he d
    rw [h]
    simp [t, powerTerm, mul_comm]
  have hsub : Summable (fun d : {d : ℕ // Squarefull d} => 1 / (d.val : ℝ)) :=
    (ht.comp_injective hi).congr heq
  refine ⟨summable_subtype_iff_indicator.mp hsub, ?_⟩
  rw [← _root_.tsum_subtype]
  calc
    _ ≤ ∑' x, t x := hsub.tsum_le_tsum_of_inj e hi (fun x _ => by
      exact mul_nonneg (powerTerm_nonneg 2 _) (powerTerm_nonneg 3 _)) (fun d => (heq d).ge) ht
    _ = (∑' n, powerTerm 2 n) * (∑' n, powerTerm 3 n) :=
      (h₂.tsum_mul_tsum h₃ ht).symm
    _ ≤ 3993/2000 := by
      calc
        _ ≤ (33/20 : ℝ) * (121/100) := by
          exact mul_le_mul square_series_bound cube_series_bound (tsum_nonneg (powerTerm_nonneg 3))
            (by norm_num)
        _ = 3993/2000 := by norm_num

end OMA

open Finset Filter
open scoped Topology Classical

namespace OMA

noncomputable def truncatedExpProd (T m : ℕ) : ℕ :=
  ((Finset.Icc 1 T).filter fun d => Squarefull d ∧ d ∣ m).card

theorem truncatedExpProd_le (T m : ℕ) (hm : 0 < m) :
    truncatedExpProd T m ≤ Erdos413.expProd m := by
  rw [expProd_eq_card_squarefull m hm.ne']
  apply Finset.card_le_card
  intro d hd
  have h := (Finset.mem_filter.mp hd).2
  exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨h.2,hm.ne'⟩,h.1⟩

theorem truncatedExpProd_one (m : ℕ) : truncatedExpProd 1 m = 1 := by
  unfold truncatedExpProd
  rw [Finset.Icc_self, Finset.filter_true_of_mem]
  · simp
  · intro d hd
    obtain rfl := Finset.mem_singleton.mp hd
    exact ⟨squarefull_one,one_dvd m⟩

theorem truncatedExpProd_le_cutoff (T m : ℕ) : truncatedExpProd T m ≤ T := by
  exact (Finset.card_filter_le ..).trans (by simp)

theorem error_eq_card (T N m : ℕ) (hm : m ∈ Finset.Ico 1 N) :
    Erdos413.expProd m - truncatedExpProd T m =
      ((Finset.Ico (T+1) N).filter fun d => Squarefull d ∧ d ∣ m).card := by
  have hm' := Finset.mem_Ico.mp hm
  have hm₀ : m ≠ 0 := by omega
  rw [expProd_eq_card_squarefull m hm₀]
  let F := m.divisors.filter Squarefull
  let G := (Finset.Icc 1 T).filter fun d => Squarefull d ∧ d ∣ m
  have hsub : G ⊆ F := by
    intro d hd
    have h := (Finset.mem_filter.mp hd).2
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨h.2,hm₀⟩,h.1⟩
  change F.card - G.card = _
  rw [← Finset.card_sdiff_of_subset hsub]
  congr 1
  ext d
  simp only [F,G,Finset.mem_sdiff, Finset.mem_filter, Nat.mem_divisors,
    Finset.mem_Ico, Finset.mem_Icc]
  by_cases hg : Squarefull d <;> by_cases hd : d ∣ m
  · have hp : 0 < d := Nat.pos_of_ne_zero hg.1
    have hle : d ≤ m := Nat.le_of_dvd (by omega) hd
    simp only [hg,hd,and_true,true_and]
    omega
  · simp [hd]
  · simp [hg]
  · simp [hg]

theorem card_multiples_le (N d : ℕ) (hd : 0 < d) :
    (((Finset.Ico 1 N).filter fun m => d ∣ m).card : ℝ) ≤ N / (d : ℝ) := by
  have hc : ((Finset.Ico 1 N).filter fun m => d ∣ m).card ≤ N / d := by
    rw [← Finset.card_range (N / d)]
    refine Finset.card_le_card_of_injOn (fun m => m / d - 1) ?_ ?_
    · intro m hm
      have ⟨hr, hdvd⟩ := Finset.mem_filter.mp hm
      have ⟨h₁,h₂⟩ := Finset.mem_Ico.mp hr
      have hq : 0 < m / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hd
      have hq' : m / d ≤ N / d := Nat.div_le_div_right h₂.le
      apply Finset.mem_range.mpr
      change m / d - 1 < N / d
      omega
    · intro a ha b hb he
      have ⟨ha',hda⟩ := Finset.mem_filter.mp ha
      have ⟨hb',hdb⟩ := Finset.mem_filter.mp hb
      have ha₁ := (Finset.mem_Ico.mp ha').1
      have hb₁ := (Finset.mem_Ico.mp hb').1
      have ha₂ : 0 < a / d := Nat.div_pos (Nat.le_of_dvd (by omega) hda) hd
      have hb₂ : 0 < b / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdb) hd
      have hf : a / d = b / d := by
        change a / d - 1 = b / d - 1 at he
        omega
      calc
        a = a / d * d := (Nat.div_mul_cancel hda).symm
        _ = b / d * d := by rw [hf]
        _ = b := Nat.div_mul_cancel hdb
  calc
    _ ≤ ((N / d : ℕ) : ℝ) := by exact_mod_cast hc
    _ ≤ N / (d : ℝ) := (le_div_iff₀ (by exact_mod_cast hd)).2 (by
      exact_mod_cast Nat.div_mul_le_self N d)

noncomputable abbrev squarefullWeight (d : ℕ) : ℝ :=
  Set.indicator {d | Squarefull d} (fun d : ℕ => 1 / (d : ℝ)) d

theorem weight_nonneg (d : ℕ) : 0 ≤ squarefullWeight d := by
  by_cases h : Squarefull d <;> simp [squarefullWeight, Set.indicator, h]

noncomputable def tailWeight (T : ℕ) : ℝ :=
  ∑' d, squarefullWeight (d + (T+1))

theorem tailWeight_nonneg (T : ℕ) : 0 ≤ tailWeight T :=
  tsum_nonneg (fun _ => weight_nonneg _)

theorem finite_tail_le (T N : ℕ) :
    (∑ d ∈ Finset.Ico (T+1) N, squarefullWeight d) ≤ tailWeight T := by
  have hs := (summable_nat_add_iff (T+1)).2 squarefull_series.1
  calc
    _ = ∑ d ∈ range (N - (T+1)), squarefullWeight (d + (T+1)) := by
      symm
      refine Finset.sum_bij (fun d _ => d + (T+1)) ?_ ?_ ?_ ?_
      · intro d hd
        have := Finset.mem_range.mp hd
        exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      · intro a _ b _ hab
        omega
      · intro d hd
        have := Finset.mem_Ico.mp hd
        exact ⟨d-(T+1), Finset.mem_range.mpr (by omega), by omega⟩
      · simp
    _ ≤ _ := hs.sum_le_tsum _ (fun _ _ => weight_nonneg _)

theorem sum_error_le (T N : ℕ) :
    (∑ m ∈ Finset.Ico 1 N, ((Erdos413.expProd m - truncatedExpProd T m : ℕ) : ℝ))
      ≤ (N : ℝ) * tailWeight T := by
  calc
    _ = ∑ d ∈ Finset.Ico (T+1) N,
        (if Squarefull d then (((Finset.Ico 1 N).filter fun m => d ∣ m).card : ℝ) else 0) := by
      calc
        _ = ∑ m ∈ Finset.Ico 1 N, ∑ d ∈ Finset.Ico (T+1) N,
            (if Squarefull d ∧ d ∣ m then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [error_eq_card T N m hm, Finset.card_filter, Nat.cast_sum]
          refine Finset.sum_congr rfl fun d hd => ?_
          split_ifs <;> simp
        _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun d hd => ?_
          by_cases hg : Squarefull d
          · simp only [hg, true_and, if_true, Finset.card_filter, Nat.cast_sum]
            refine Finset.sum_congr rfl fun m hm => ?_
            split_ifs <;> simp
          · simp [hg]
    _ ≤ ∑ d ∈ Finset.Ico (T+1) N, (N : ℝ) * squarefullWeight d := by
      apply Finset.sum_le_sum
      intro d hd
      by_cases h : Squarefull d
      · simpa [h, squarefullWeight, Set.indicator, div_eq_mul_inv] using
          card_multiples_le N d (Nat.pos_of_ne_zero h.1)
      · simp [h, squarefullWeight, Set.indicator]
    _ = (N : ℝ) * (∑ d ∈ Finset.Ico (T+1) N, squarefullWeight d) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (finite_tail_le T N) (by positivity)

end OMA

open Finset Filter
open scoped Topology Classical

namespace OMA

noncomputable def prefixCount (P : ℕ → Prop) (N : ℕ) : ℕ :=
  ((Finset.range N).filter P).card

theorem prefixCount_le (P : ℕ → Prop) (N : ℕ) : prefixCount P N ≤ N :=
  (Finset.card_filter_le ..).trans_eq (Finset.card_range _)

theorem prefixCount_add (P : ℕ → Prop) (a b : ℕ) :
    prefixCount P (a + b) = prefixCount P a + prefixCount (fun n => P (n+a)) b := by
  simp only [prefixCount, Finset.card_filter]
  rw [Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Nat.add_comm]

theorem prefixCount_mul (P : ℕ → Prop) {q : ℕ} (h : Function.Periodic P q) (k : ℕ) :
    prefixCount P (k*q) = k * prefixCount P q := by
  induction k with
  | zero => simp [prefixCount]
  | succ k ih =>
    rw [Nat.succ_mul, add_comm (k*q), prefixCount_add]
    rw [show (fun n => P (n+q)) = P from funext h, ih, Nat.succ_mul, add_comm]

theorem periodic_prefix_limit (P : ℕ → Prop) (B q : ℕ) (hq : 0 < q)
    (h : Function.Periodic (fun n => P (n+B)) q) :
    ∃ c : ℝ, Tendsto (fun n => (prefixCount P n : ℝ) / (n : ℝ)) atTop (𝓝 c) := by
  let Q : ℕ → Prop := fun n => P (n+B)
  let c : ℝ := (prefixCount Q q : ℝ) / (q : ℝ)
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hc₀ : 0 ≤ c := by dsimp [c]; positivity
  have hc₁ : c ≤ 1 := (div_le_one hqR).2 (by exact_mod_cast prefixCount_le Q q)
  have hcq : (prefixCount Q q : ℝ) = c * q := by
    dsimp [c]
    field_simp
  refine ⟨c, Metric.tendsto_atTop.2 fun ε hε => ?_⟩
  have hsmall : ∀ᶠ n : ℕ in atTop, ((B : ℝ)+q) / (n : ℝ) < ε :=
    (tendsto_const_div_atTop_nhds_zero_nat _).eventually (gt_mem_nhds hε)
  obtain ⟨L,hL⟩ := eventually_atTop.1 hsmall
  refine ⟨max L (B+1), fun n hn => ?_⟩
  have hnB : B ≤ n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let k := (n-B) / q
  let r := (n-B) % q
  have hr : r < q := Nat.mod_lt _ hq
  have hk : k*q+r = n-B := by simpa [k,r,mul_comm] using Nat.div_add_mod (n-B) q
  have hsplit : B+(k*q+r) = n := by omega
  have hcount : prefixCount P n = prefixCount P B + k * prefixCount Q q + prefixCount Q r := by
    calc
      _ = prefixCount P (B+(k*q+r)) := by rw [hsplit]
      _ = prefixCount P B + prefixCount Q (k*q+r) := prefixCount_add _ _ _
      _ = _ := by
        rw [prefixCount_add, prefixCount_mul Q h k, add_assoc]
        rw [show (fun n => Q (n + k*q)) = Q from funext (h.nat_mul k)]
  have hsplitR : (B : ℝ) + (k * q + r : ℝ) = n := by exact_mod_cast hsplit
  have hcountR : (prefixCount P n : ℝ) =
      prefixCount P B + (k : ℝ) * prefixCount Q q + prefixCount Q r := by
    exact_mod_cast hcount
  have herr : (prefixCount P n : ℝ) - c * n =
      (prefixCount P B : ℝ) + prefixCount Q r - (c * B + c * r) := by
    rw [hcountR, hcq, ← hsplitR]
    ring
  have hBcnt : (prefixCount P B : ℝ) ≤ B := by exact_mod_cast prefixCount_le P B
  have hRcnt : (prefixCount Q r : ℝ) ≤ r := by exact_mod_cast prefixCount_le Q r
  have hr' : (r : ℝ) ≤ q := by exact_mod_cast hr.le
  have hcb : c * (B : ℝ) ≤ B := by simpa using mul_le_mul_of_nonneg_right hc₁ (Nat.cast_nonneg B)
  have hcr : c * (r : ℝ) ≤ r := by simpa using mul_le_mul_of_nonneg_right hc₁ (Nat.cast_nonneg r)
  have habs : |(prefixCount P n : ℝ) - c * n| ≤ B + q := by
    rw [herr, abs_le]
    constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (prefixCount P B),
      Nat.cast_nonneg (α := ℝ) (prefixCount Q r), mul_nonneg hc₀ (Nat.cast_nonneg (α := ℝ) B),
      mul_nonneg hc₀ (Nat.cast_nonneg (α := ℝ) r)]
  rw [Real.dist_eq, show (prefixCount P n : ℝ) / n - c = ((prefixCount P n : ℝ) - c*n) / n by
    field_simp, abs_div, abs_of_pos hnR]
  exact (div_le_div_of_nonneg_right habs hnR.le).trans_lt (hL n (by omega))

def IsNonbarrier (f : ℕ → ℕ) (n : ℕ) : Prop :=
  ∃ m ∈ Finset.Ico 1 n, n < m + f m

theorem truncated_periodic (T : ℕ) :
    Function.Periodic (truncatedExpProd T) (Nat.factorial T) := by
  intro n
  unfold truncatedExpProd
  congr 1
  apply Finset.filter_congr
  intro d hd
  have ⟨hd₁,hd₂⟩ := Finset.mem_Icc.mp hd
  have hdq : d ∣ Nat.factorial T := Nat.dvd_factorial (by omega) hd₂
  exact and_congr_right fun _ => (Nat.dvd_add_iff_left hdq).symm

theorem nonbarrier_periodic_after (T : ℕ) :
    Function.Periodic (fun n => IsNonbarrier (truncatedExpProd T) (n+(T+1))) (Nat.factorial T) := by
  let f := truncatedExpProd T
  let q := Nat.factorial T
  have hp : Function.Periodic f q := truncated_periodic T
  change ∀ i : ℕ, IsNonbarrier f (i+q+(T+1)) = IsNonbarrier f (i+(T+1))
  intro i
  set n := i+(T+1) with hn
  rw [show i+q+(T+1) = n+q by omega]
  apply propext
  constructor
  · rintro ⟨m, hm, hbad⟩
    have hm' := Finset.mem_Ico.mp hm
    have hmf := truncatedExpProd_le_cutoff T m
    change f m ≤ T at hmf
    have hmq : q < m := by omega
    refine ⟨m-q, Finset.mem_Ico.mpr ⟨by omega,by omega⟩, ?_⟩
    have he : m-q+q = m := by omega
    have hh := hp (m-q)
    rw [he] at hh
    omega
  · rintro ⟨m, hm, hbad⟩
    have hm' := Finset.mem_Ico.mp hm
    refine ⟨m+q, Finset.mem_Ico.mpr ⟨by omega,by omega⟩, ?_⟩
    have hh := hp m
    omega

theorem truncated_limit (T : ℕ) :
    ∃ c : ℝ, Tendsto
      (fun n => (prefixCount (IsNonbarrier (truncatedExpProd T)) n : ℝ) / (n : ℝ)) atTop (𝓝 c) := by
  exact periodic_prefix_limit _ (T+1) (Nat.factorial T) (Nat.factorial_pos _) (nonbarrier_periodic_after T)

end OMA

open Finset Filter
open scoped Topology Classical

namespace OMA

theorem nonbarrier_count_gap (T N : ℕ) :
    prefixCount (IsNonbarrier (truncatedExpProd T)) N ≤ prefixCount (IsNonbarrier Erdos413.expProd) N ∧
    ((prefixCount (IsNonbarrier Erdos413.expProd) N -
      prefixCount (IsNonbarrier (truncatedExpProd T)) N : ℕ) : ℝ) ≤ (N : ℝ) * tailWeight T := by
  let a := (Finset.range N).filter (IsNonbarrier Erdos413.expProd)
  let b := (Finset.range N).filter (IsNonbarrier (truncatedExpProd T))
  have hab : b ⊆ a := by
    intro n hn
    obtain ⟨hN, m, hm, hmn⟩ := Finset.mem_filter.mp hn
    have hf := truncatedExpProd_le T m (by have := Finset.mem_Ico.mp hm; omega)
    exact Finset.mem_filter.mpr ⟨hN, m, hm, by omega⟩
  constructor
  · exact Finset.card_le_card hab
  change ((a.card - b.card : ℕ) : ℝ) ≤ _
  rw [← Finset.card_sdiff_of_subset hab]
  have hsub : a \ b ⊆ (Finset.Ico 1 N).biUnion (fun m =>
      Finset.Ico (m + truncatedExpProd T m) (m + Erdos413.expProd m)) := by
    intro n hn
    have ⟨ha,hb⟩ := Finset.mem_sdiff.mp hn
    obtain ⟨hN, m, hm, hmn⟩ := Finset.mem_filter.mp ha
    have hi := Finset.mem_Ico.mp hm
    have hN' := Finset.mem_range.mp hN
    have hn' : m + truncatedExpProd T m ≤ n := by
      by_contra! hh
      exact hb (Finset.mem_filter.mpr ⟨hN, m, hm, hh⟩)
    exact Finset.mem_biUnion.mpr ⟨m, Finset.mem_Ico.mpr ⟨hi.1,hi.2.trans hN'⟩,
      Finset.mem_Ico.mpr ⟨hn',hmn⟩⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  calc
    _ ≤ ∑ m ∈ Finset.Ico 1 N, ((Finset.Ico (m + truncatedExpProd T m) (m + Erdos413.expProd m)).card : ℝ) := by
      exact_mod_cast hcard
    _ = ∑ m ∈ Finset.Ico 1 N, ((Erdos413.expProd m - truncatedExpProd T m : ℕ) : ℝ) := by
      simp only [Nat.card_Ico, Nat.add_sub_add_left]
    _ ≤ _ := sum_error_le T N

noncomputable def nonbarrierRatio (f : ℕ → ℕ) (n : ℕ) : ℝ :=
  (prefixCount (IsNonbarrier f) n : ℝ) / (n : ℝ)

theorem nonbarrier_gap (T n : ℕ) :
    dist (nonbarrierRatio Erdos413.expProd n) (nonbarrierRatio (truncatedExpProd T) n) ≤
      tailWeight T := by
  by_cases hn : n = 0
  · simp [hn, nonbarrierRatio, tailWeight_nonneg]
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have ⟨h₁,h₂⟩ := nonbarrier_count_gap T n
  have ha : (prefixCount (IsNonbarrier (truncatedExpProd T)) n : ℝ) ≤
      (prefixCount (IsNonbarrier Erdos413.expProd) n : ℝ) := by exact_mod_cast h₁
  rw [Nat.cast_sub h₁] at h₂
  unfold nonbarrierRatio
  rw [Real.dist_eq, ← sub_div, abs_of_nonneg (div_nonneg (sub_nonneg.mpr ha) hn'.le)]
  exact (div_le_iff₀ hn').2 (by simpa [mul_comm] using h₂)

theorem tailWeight_limit : Tendsto tailWeight atTop (𝓝 0) := by
  let total : ℝ := ∑' d, squarefullWeight d
  have ht : Tendsto (fun N : ℕ => ∑ d ∈ Finset.range (N+1), squarefullWeight d)
      atTop (𝓝 total) :=
    (squarefull_series.1.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have h₀ : Tendsto (fun N : ℕ =>
      total - ∑ d ∈ Finset.range (N+1), squarefullWeight d)
      atTop (𝓝 (total - total)) := tendsto_const_nhds.sub ht
  rw [sub_self] at h₀
  apply h₀.congr
  intro T
  have h := squarefull_series.1.sum_add_tsum_nat_add (T+1)
  dsimp [tailWeight, total]
  linarith

theorem nonbarrier_limit : ∃ c : ℝ, Tendsto (nonbarrierRatio Erdos413.expProd) atTop (𝓝 c) := by
  apply cauchySeq_tendsto_of_complete
  refine Metric.cauchySeq_iff.2 fun ε hε => ?_
  have h₄ : 0 < ε/4 := by linarith
  have hsmall := (tailWeight_limit.eventually (gt_mem_nhds h₄)).exists
  obtain ⟨T,hT⟩ := hsmall
  obtain ⟨c,hc⟩ := truncated_limit T
  change Tendsto (nonbarrierRatio (truncatedExpProd T)) atTop (𝓝 c) at hc
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.1 hc (ε/4) h₄
  refine ⟨N, fun m hm n hn => ?_⟩
  let a := nonbarrierRatio Erdos413.expProd
  let b := nonbarrierRatio (truncatedExpProd T)
  change dist (a m) (a n) < ε
  have h₁ : dist (a m) (b m) < ε/4 := (nonbarrier_gap T m).trans_lt hT
  have h₂ : dist (b n) (a n) < ε/4 := by rw [dist_comm]; exact (nonbarrier_gap T n).trans_lt hT
  have h₃ : dist (b m) c < ε/4 := hN m hm
  have h₄' : dist c (b n) < ε/4 := by rw [dist_comm]; exact hN n hn
  linarith [dist_triangle (a m) (b m) (a n), dist_triangle (b m) c (a n),
    dist_triangle c (b n) (a n)]

theorem nonbarrierRatio_le (n : ℕ) : nonbarrierRatio Erdos413.expProd n ≤ 1993/2000 := by
  have htail : tailWeight 1 ≤ 1993/2000 := by
    have he : (∑ d ∈ Finset.range (1+1), squarefullWeight d) = 1 := by
      norm_num [Finset.sum_range_succ, squarefullWeight, Squarefull, Set.indicator]
    have h := squarefull_series.1.sum_add_tsum_nat_add (1+1)
    change (∑ d ∈ Finset.range (1+1), squarefullWeight d) + tailWeight 1 =
      (∑' d, squarefullWeight d) at h
    rw [he] at h
    linarith [squarefull_series.2]
  have hzero : nonbarrierRatio (truncatedExpProd 1) n = 0 := by
    have hh (x : ℕ) : ¬IsNonbarrier (truncatedExpProd 1) x := by
      rintro ⟨m,hm,hxm⟩
      rw [truncatedExpProd_one] at hxm
      have := (Finset.mem_Ico.mp hm).2
      omega
    simp [nonbarrierRatio, prefixCount, hh]
  have h := (nonbarrier_gap 1 n).trans htail
  rw [hzero, Real.dist_eq, sub_zero] at h
  exact (le_abs_self _).trans h

theorem barrier_iff_not_nonbarrier (n : ℕ) :
    Erdos413.IsBarrier (fun m => (Erdos413.expProd m : ℝ)) n ↔
      ¬IsNonbarrier Erdos413.expProd n := by
  have hzero : Erdos413.expProd 0 = 1 := by simp [Erdos413.expProd]
  constructor
  · rintro h ⟨m,hm,hlt⟩
    have ha := h m (Finset.mem_Ico.mp hm).2
    change (m : ℝ) + (Erdos413.expProd m : ℝ) ≤ n at ha
    exact (not_lt_of_ge (by exact_mod_cast ha : m + Erdos413.expProd m ≤ n)) hlt
  · intro h m hmn
    change (m : ℝ) + (Erdos413.expProd m : ℝ) ≤ n
    by_cases hm : m = 0
    · subst m
      rw [hzero]
      exact_mod_cast (show 0 + 1 ≤ n by omega)
    · have ha : m + Erdos413.expProd m ≤ n := le_of_not_gt fun hlt =>
        h ⟨m,Finset.mem_Ico.mpr ⟨by omega,hmn⟩,hlt⟩
      exact_mod_cast ha

theorem barrier_partialDensity (N : ℕ) (hN : 0 < N) :
    {n | Erdos413.IsBarrier (fun m => (Erdos413.expProd m : ℝ)) n}.partialDensity Set.univ N =
      1 - nonbarrierRatio Erdos413.expProd N := by
  let b := (Finset.range N).filter (fun n => ¬ IsNonbarrier Erdos413.expProd n)
  have hB : ((b : Finset ℕ) : Set ℕ) =
      {n | Erdos413.IsBarrier (fun m => (Erdos413.expProd m : ℝ)) n} ∩ Set.Iio N := by
    ext n
    simp [b, barrier_iff_not_nonbarrier, and_comm]
  have hb : b.card = N - prefixCount (IsNonbarrier Erdos413.expProd) N := by
    have hsum := Finset.card_filter_add_card_filter_not
      (s := Finset.range N) (p := IsNonbarrier Erdos413.expProd)
    rw [Finset.card_range] at hsum
    unfold prefixCount
    dsimp [b]
    omega
  rw [Set.partialDensity, Set.inter_univ, Set.univ_inter, ← hB, Set.ncard_coe_finset,
    Nat.ncard_Iio, hb, Nat.cast_sub (prefixCount_le _ _), sub_div, div_self (by exact_mod_cast hN.ne')]
  rfl

end OMA

open OMA

theorem OMA.solution : type_of% @Erdos413.erdos_413.variants.hasPosDensity_barrier_expProd := by
  obtain ⟨c,hc⟩ := nonbarrier_limit
  have hcb : c ≤ 1993/2000 :=
    le_of_tendsto' hc nonbarrierRatio_le
  refine ⟨1-c, by linarith, ?_⟩
  have hlim : Tendsto (fun n => 1 - nonbarrierRatio Erdos413.expProd n) atTop (𝓝 (1-c)) :=
    tendsto_const_nhds.sub hc
  refine hlim.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  exact (barrier_partialDensity n (by omega)).symm
