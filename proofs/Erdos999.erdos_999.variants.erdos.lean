import FormalConjectures.ErdosProblems.«999»

/-!
Erdős's bounded case of the Duffin–Schaeffer theorem (1964).

The second-moment estimates below are due to Koukoulopoulos and Maynard
(Ann. of Math. 192, 2020). The Lean proofs are adapted from HongJin HE,
github.com/hongjin-he/erdos-lean, commit efede9693a3192e324bc092e5510f16a2aff1804,
and Steven Enamakel's port in project PR 3297, commit 80e32d5916bd.
Copyright HongJin HE. Portions are adapted from plby/lean-proofs,
copyright 2026 The Formal Conjectures Authors. Both sources are licensed
under the Apache License, Version 2.0.

For bounded q f(q), replacing f(q) by min(f(q), 1/2) changes only finitely
many terms. The clipped radii tend to zero and the clipped weights are at
most 1/2. The circle argument below counts distinct denominators directly.
-/

open scoped Classical
section Port24_Defs
open MeasureTheory Filter Finset
namespace DuffinSchaeffer
noncomputable def weight (ψ : ℕ → ℝ) (q : ℕ) : ℝ := (Nat.totient q : ℝ) * ψ q / q
noncomputable def Aq (ψ : ℕ → ℝ) (q : ℕ) : Set UnitAddCircle :=
  approxAddOrderOf UnitAddCircle q (ψ q / q)
noncomputable def Mqr (ψ : ℕ → ℝ) (q r : ℕ) : ℝ := max (r * ψ q) (q * ψ r)
def coprimePart (a b : ℕ) : ℕ := (a / Nat.gcd a b) * (b / Nat.gcd a b)
noncomputable def Lsum (t : ℝ) (a b : ℕ) : ℝ :=
  ∑ p ∈ (coprimePart a b).primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)), (1 : ℝ) / p
noncomputable def Pfac (ψ : ℕ → ℝ) (q r : ℕ) : ℝ :=
  ∏ p ∈ (coprimePart q r).primeFactors.filter (fun p : ℕ => Mqr ψ q r / Nat.gcd q r < (p : ℝ)),
    (1 + 1 / (p : ℝ))
noncomputable def Et (ψ : ℕ → ℝ) (X Y : ℕ) (t : ℝ) : Finset (ℕ × ℕ) :=
  (Icc X Y ×ˢ Icc X Y).filter
    (fun e => Mqr ψ e.1 e.2 ≤ t * Nat.gcd e.1 e.2 ∧ 10 ≤ Lsum t e.1 e.2)
noncomputable def T0 : ℝ := (10 : ℝ) ^ (2000 : ℕ)
noncomputable def K40 : ℝ := (10 : ℝ) ^ (40 : ℕ)
def wsum (μ : ℕ → ℝ) (S : Finset ℕ) : ℝ := ∑ v ∈ S, μ v
def esum (μ : ℕ → ℝ) (E : Finset (ℕ × ℕ)) : ℝ := ∑ e ∈ E, μ e.1 * μ e.2
def vslice (S : Finset ℕ) (p k : ℕ) : Finset ℕ := S.filter (fun v => v.factorization p = k)
structure GCDGraph where
  μ : ℕ → ℝ
  V : Finset ℕ
  W : Finset ℕ
  E : Finset (ℕ × ℕ)
  P : Finset ℕ
  f : ℕ → ℕ
  g : ℕ → ℕ
  μ_nonneg : ∀ n, 0 ≤ μ n
  V_pos : ∀ v ∈ V, 0 < v
  W_pos : ∀ w ∈ W, 0 < w
  E_sub : E ⊆ V ×ˢ W
  P_prime : ∀ p ∈ P, p.Prime
  dvd_V : ∀ p ∈ P, ∀ v ∈ V, p ^ f p ∣ v
  dvd_W : ∀ p ∈ P, ∀ w ∈ W, p ^ g p ∣ w
  gcd_E : ∀ p ∈ P, ∀ e ∈ E, (Nat.gcd e.1 e.2).factorization p = min (f p) (g p)
  exact_V : ∀ p ∈ P, f p ≠ g p → ∀ v ∈ V, v.factorization p = f p
  exact_W : ∀ p ∈ P, f p ≠ g p → ∀ w ∈ W, w.factorization p = g p
namespace GCDGraph
variable (G : GCDGraph)
def Nontrivial : Prop := 0 < esum G.μ G.E
noncomputable def density : ℝ := esum G.μ G.E / (wsum G.μ G.V * wsum G.μ G.W)
def nbhdV (v : ℕ) : Finset ℕ := G.W.filter (fun w => (v, w) ∈ G.E)
def nbhdW (w : ℕ) : Finset ℕ := G.V.filter (fun v => (v, w) ∈ G.E)
def fgDist (p : ℕ) : ℕ := (G.f p - G.g p) + (G.g p - G.f p)
noncomputable def qualityFactor (p : ℕ) : ℝ :=
  (p : ℝ) ^ G.fgDist p /
    ((1 - (if G.f p = G.g p ∧ 1 ≤ G.f p then 1 / (p : ℝ) else 0)) ^ 2 *
      (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10)
noncomputable def quality : ℝ :=
  G.density ^ 10 * wsum G.μ G.V * wsum G.μ G.W * ∏ p ∈ G.P, G.qualityFactor p
def R : Finset ℕ := (G.E.biUnion (fun e => (Nat.gcd e.1 e.2).primeFactors)) \ G.P
def IsSharp (p : ℕ) : Prop :=
  ∃ k : ℕ, (1 - K40 / p) * wsum G.μ G.V ≤ wsum G.μ (vslice G.V p k) ∧
    (1 - K40 / p) * wsum G.μ G.W ≤ wsum G.μ (vslice G.W p k)
open scoped Classical in
noncomputable def Rsharp : Finset ℕ := G.R.filter G.IsSharp
open scoped Classical in
noncomputable def Rflat : Finset ℕ := G.R.filter (fun p => ¬ G.IsSharp p)
def aProd : ℕ := ∏ p ∈ G.P, p ^ G.f p
def bProd : ℕ := ∏ p ∈ G.P, p ^ G.g p
def IsSubgraph (G' G : GCDGraph) : Prop :=
  G'.μ = G.μ ∧ G'.V ⊆ G.V ∧ G'.W ⊆ G.W ∧ G'.E ⊆ G.E ∧ G.P ⊆ G'.P ∧
    ∀ p ∈ G.P, G'.f p = G.f p ∧ G'.g p = G.g p
def induce (V' W' : Finset ℕ) (E' : Finset (ℕ × ℕ)) (hV : V' ⊆ G.V) (hW : W' ⊆ G.W)
    (hE : E' ⊆ G.E) (hE' : E' ⊆ V' ×ˢ W') : GCDGraph where
  μ := G.μ
  V := V'
  W := W'
  E := E'
  P := G.P
  f := G.f
  g := G.g
  μ_nonneg := G.μ_nonneg
  V_pos := fun v hv => G.V_pos v (hV hv)
  W_pos := fun w hw => G.W_pos w (hW hw)
  E_sub := hE'
  P_prime := G.P_prime
  dvd_V := fun p hp v hv => G.dvd_V p hp v (hV hv)
  dvd_W := fun p hp w hw => G.dvd_W p hp w (hW hw)
  gcd_E := fun p hp e he => G.gcd_E p hp e (hE he)
  exact_V := fun p hp hfg v hv => G.exact_V p hp hfg v (hV hv)
  exact_W := fun p hp hfg w hw => G.exact_W p hp hfg w (hW hw)
def restrictPrime (p k l : ℕ) (hp : p.Prime) (hpP : p ∉ G.P) : GCDGraph where
  μ := G.μ
  V := vslice G.V p k
  W := vslice G.W p l
  E := G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l)
  P := insert p G.P
  f := Function.update G.f p k
  g := Function.update G.g p l
  μ_nonneg := G.μ_nonneg
  V_pos := fun v hv => G.V_pos v (Finset.mem_filter.1 hv).1
  W_pos := fun w hw => G.W_pos w (Finset.mem_filter.1 hw).1
  E_sub := by
    intro e he
    obtain ⟨he, h1, h2⟩ := Finset.mem_filter.1 he
    obtain ⟨hv, hw⟩ := Finset.mem_product.1 (G.E_sub he)
    exact Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨hv, h1⟩, Finset.mem_filter.2 ⟨hw, h2⟩⟩
  P_prime := by
    intro q hq
    rcases Finset.mem_insert.1 hq with rfl | hq
    · exact hp
    · exact G.P_prime q hq
  dvd_V := by
    intro q hq v hv
    obtain ⟨hv, hvk⟩ := Finset.mem_filter.1 hv
    rcases Finset.mem_insert.1 hq with rfl | hq'
    · rw [Function.update_self, ← hvk]
      exact Nat.ordProj_dvd v q
    · have hne : q ≠ p := fun h => hpP (h ▸ hq')
      rw [Function.update_of_ne hne]
      exact G.dvd_V q hq' v hv
  dvd_W := by
    intro q hq w hw
    obtain ⟨hw, hwl⟩ := Finset.mem_filter.1 hw
    rcases Finset.mem_insert.1 hq with rfl | hq'
    · rw [Function.update_self, ← hwl]
      exact Nat.ordProj_dvd w q
    · have hne : q ≠ p := fun h => hpP (h ▸ hq')
      rw [Function.update_of_ne hne]
      exact G.dvd_W q hq' w hw
  gcd_E := by
    intro q hq e he0
    obtain ⟨he, h1, h2⟩ := Finset.mem_filter.1 he0
    rcases Finset.mem_insert.1 hq with hqp | hq'
    · subst hqp
      obtain ⟨hv, hw⟩ := Finset.mem_product.1 (G.E_sub he)
      have hv0 : e.1 ≠ 0 := (G.V_pos _ hv).ne'
      have hw0 : e.2 ≠ 0 := (G.W_pos _ hw).ne'
      rw [Function.update_self, Function.update_self, Nat.factorization_gcd hv0 hw0,
        Finsupp.inf_apply, h1, h2]
    · have hne : q ≠ p := fun h => hpP (h ▸ hq')
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
      exact G.gcd_E q hq' e he
  exact_V := by
    intro q hq hfg v hv
    obtain ⟨hv, hvk⟩ := Finset.mem_filter.1 hv
    rcases Finset.mem_insert.1 hq with rfl | hq'
    · rw [Function.update_self]
      exact hvk
    · have hne : q ≠ p := fun h => hpP (h ▸ hq')
      rw [Function.update_of_ne hne, Function.update_of_ne hne] at hfg
      rw [Function.update_of_ne hne]
      exact G.exact_V q hq' hfg v hv
  exact_W := by
    intro q hq hfg w hw
    obtain ⟨hw, hwl⟩ := Finset.mem_filter.1 hw
    rcases Finset.mem_insert.1 hq with rfl | hq'
    · rw [Function.update_self]
      exact hwl
    · have hne : q ≠ p := fun h => hpP (h ▸ hq')
      rw [Function.update_of_ne hne, Function.update_of_ne hne] at hfg
      rw [Function.update_of_ne hne]
      exact G.exact_W q hq' hfg w hw
theorem prime_of_mem_R {p : ℕ} (h : p ∈ G.R) : p.Prime := by
  obtain ⟨h1, -⟩ := Finset.mem_sdiff.1 h
  obtain ⟨e, -, he⟩ := Finset.mem_biUnion.1 h1
  exact Nat.prime_of_mem_primeFactors he
theorem not_mem_P_of_mem_R {p : ℕ} (h : p ∈ G.R) : p ∉ G.P := (Finset.mem_sdiff.1 h).2
def HighDegree : Prop :=
  (∀ v ∈ G.V, 9 * G.density / 10 * wsum G.μ G.W ≤ wsum G.μ (G.nbhdV v)) ∧
    (∀ w ∈ G.W, 9 * G.density / 10 * wsum G.μ G.V ≤ wsum G.μ (G.nbhdW w))
def newUnequal (G' G : GCDGraph) : ℕ := ((G'.P \ G.P).filter (fun p => G'.f p ≠ G'.g p)).card
end GCDGraph
end DuffinSchaeffer
end Port24_Defs

section Port24_Parts_Mertens
open Real Finset
namespace DuffinSchaeffer
namespace MertensAux
lemma Iic_eq_range' (n : ℕ) : Iic n = range (n + 1) := by
  ext m; simp
lemma sum_primes_succ (f : ℕ → ℝ) (n : ℕ) :
    ∑ p ∈ (Iic (n + 1)).filter Nat.Prime, f p =
      ∑ p ∈ (Iic n).filter Nat.Prime, f p + if (n + 1).Prime then f (n + 1) else 0 := by
  rw [Iic_eq_range', Iic_eq_range', sum_filter, sum_filter, sum_range_succ]
lemma sum_primes_Ioc_succ (f : ℕ → ℝ) {M n : ℕ} (h : M ≤ n) :
    ∑ p ∈ (Ioc M (n + 1)).filter Nat.Prime, f p =
      ∑ p ∈ (Ioc M n).filter Nat.Prime, f p + if (n + 1).Prime then f (n + 1) else 0 := by
  rw [sum_filter, sum_filter, sum_Ioc_succ_top h]
lemma theta_le (n : ℕ) : ∑ p ∈ (Iic n).filter Nat.Prime, Real.log p ≤ Real.log 4 * n := by
  have h1 : (Iic n).filter Nat.Prime = Nat.primesLE n := by
    rw [Nat.primesLE_eq_filter_range, Iic_eq_range']
  rw [h1, ← Chebyshev.theta_eq_sum_primesLE_log]
  exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)
lemma log_factorial_eq (n : ℕ) :
    Real.log (n.factorial : ℝ) = ∑ p ∈ (Iic n).filter Nat.Prime,
      ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    exact mem_filter.2 ⟨mem_Iic.2 ((hp.1.dvd_factorial).1 hp.2.1), hp.1⟩
  · intro p _; simp
lemma div_le_factorization (n p : ℕ) (hp : p.Prime) :
    n / p ≤ n.factorial.factorization p := by
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p n))]
  rcases Nat.lt_or_ge n p with h | h
  · simp [Nat.div_eq_of_lt h]
  · have h1 : 1 ∈ Ico 1 (Nat.log p n + 1) := by
      have := Nat.log_pos hp.one_lt h
      simp only [mem_Ico, le_refl, true_and]
      omega
    have := Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) h1
    simpa using this
lemma factorization_le_div (n p : ℕ) (hp : p.Prime) :
    ((n.factorial.factorization p : ℕ) : ℝ) ≤ n / ((p : ℝ) - 1) := by
  have h := Nat.sub_one_mul_factorization_factorial hp (n := n)
  have h' : (p - 1) * n.factorial.factorization p ≤ n := by rw [h]; exact Nat.sub_le _ _
  have hc : (((p - 1) * n.factorial.factorization p : ℕ) : ℝ) ≤ n := by exact_mod_cast h'
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one] at hc
  rw [le_div_iff₀ (by linarith)]
  linarith
lemma log_succ_sub_log_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have := Real.log_le_sub_one_of_pos (x := ((n : ℝ) + 1) / n) (by positivity)
  rw [Real.log_div (by positivity) hn'.ne'] at this
  have e : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
  linarith
lemma sum_log_div_Icc (n : ℕ) (hn : 1 ≤ n) :
    ∑ m ∈ Icc 2 n, Real.log m / ((m : ℝ) * ((m : ℝ) - 1)) ≤
      1 + Real.log 2 - (Real.log ((n : ℝ) + 1) + 1) / n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num; linarith
  | succ n hn ih =>
    rw [sum_Icc_succ_top (by omega)]
    push_cast
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have e0 : ((n : ℝ) + 1 - 1) = n := by ring
    rw [e0]
    set a := Real.log ((n : ℝ) + 1)
    set b := Real.log ((n : ℝ) + 1 + 1)
    have hk : b - a ≤ 1 / ((n : ℝ) + 1) := by
      have := log_succ_sub_log_le (n + 1) (by omega)
      push_cast at this
      exact this
    have hk2 : (n : ℝ) * (b - a) ≤ 1 := by
      have h1 := mul_le_mul_of_nonneg_left hk hn'.le
      have h2 : (n : ℝ) * (1 / ((n : ℝ) + 1)) ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]; linarith
      linarith
    have e : (a + 1) / n - (b + 1) / ((n : ℝ) + 1) - a / (((n : ℝ) + 1) * n) =
        (1 - n * (b - a)) / (((n : ℝ) + 1) * n) := by
      field_simp; ring
    have hnn : 0 ≤ (1 - n * (b - a)) / (((n : ℝ) + 1) * n) :=
      div_nonneg (by linarith) (by positivity)
    linarith
lemma sum_inv_Icc (n : ℕ) (hn : 1 ≤ n) :
    ∑ m ∈ Icc 2 n, 1 / ((m : ℝ) * ((m : ℝ) - 1)) ≤ 1 - 1 / n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [sum_Icc_succ_top (by omega)]
    push_cast
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have e0 : ((n : ℝ) + 1 - 1) = n := by ring
    rw [e0]
    have e : 1 - 1 / (n : ℝ) + 1 / (((n : ℝ) + 1) * n) = 1 - 1 / ((n : ℝ) + 1) := by
      field_simp; ring
    linarith
lemma log_four_lt_two : Real.log 4 < 2 := by
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_lt_d9
  linarith
end MertensAux
open MertensAux
theorem sum_log_prime_div_le (x : ℝ) (hx : 1 ≤ x) :
    ∑ p ∈ (Iic ⌊x⌋₊).filter Nat.Prime, Real.log p / p ≤ Real.log x + 2 := by
  set n := ⌊x⌋₊ with hn
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hx)
  have hnx : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have key : (n : ℝ) * ∑ p ∈ (Iic n).filter Nat.Prime, Real.log p / p ≤
      Real.log (n.factorial : ℝ) + ∑ p ∈ (Iic n).filter Nat.Prime, Real.log p := by
    rw [log_factorial_eq, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro p hp
    have hpp := (mem_filter.1 hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have h1 : (n : ℝ) < p * (((n / p : ℕ) : ℝ) + 1) := by
      exact_mod_cast Nat.lt_mul_div_succ n hpp.pos
    have h2 : ((n / p : ℕ) : ℝ) ≤ ((n.factorial.factorization p : ℕ) : ℝ) := by
      exact_mod_cast div_le_factorization n p hpp
    have h3 : (n : ℝ) / p ≤ ((n.factorial.factorization p : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hp0]; nlinarith
    calc (n : ℝ) * (Real.log p / p) = ((n : ℝ) / p) * Real.log p := by ring
      _ ≤ (((n.factorial.factorization p : ℕ) : ℝ) + 1) * Real.log p :=
          mul_le_mul_of_nonneg_right h3 hlog
      _ = _ := by ring
  have hfac : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos n)
    exact_mod_cast Nat.factorial_le_pow n
  have hθ := theta_le n
  have hlogn : Real.log n ≤ Real.log x := Real.log_le_log hnpos hnx
  have h4 := log_four_lt_two
  by_contra hcon
  replace hcon := not_le.mp hcon
  have : (n : ℝ) * (Real.log n + 2) < n * ∑ p ∈ (Iic n).filter Nat.Prime, Real.log p / p :=
    mul_lt_mul_of_pos_left (by linarith) hnpos
  nlinarith
theorem sum_log_prime_div_ge (x : ℝ) (hx : 1 ≤ x) :
    Real.log x - 3 ≤ ∑ p ∈ (Iic ⌊x⌋₊).filter Nat.Prime, Real.log p / p := by
  set n := ⌊x⌋₊ with hn
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hx)
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  set S := ∑ p ∈ (Iic n).filter Nat.Prime, Real.log p / p with hS
  set B := ∑ p ∈ (Iic n).filter Nat.Prime, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) with hB
  have key : Real.log (n.factorial : ℝ) ≤ n * (S + B) := by
    rw [log_factorial_eq, hS, hB, ← sum_add_distrib, mul_sum]
    apply sum_le_sum
    intro p hp
    have hpp := (mem_filter.1 hp).2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hlog : 0 ≤ Real.log p := Real.log_nonneg hp1.le
    have hv := factorization_le_div n p hpp
    have e : (n : ℝ) * (Real.log p / p + Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) =
        (n / ((p : ℝ) - 1)) * Real.log p := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hv hlog
  have hBle : B ≤ 2 - 1 / n := by
    have hsub : (Iic n).filter Nat.Prime ⊆ Icc 2 n := by
      intro p hp
      simp only [mem_filter, mem_Iic] at hp
      simp only [mem_Icc]
      exact ⟨hp.2.two_le, hp.1⟩
    have h1 : B ≤ ∑ m ∈ Icc 2 n, Real.log m / ((m : ℝ) * ((m : ℝ) - 1)) := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro m hm _
      simp only [mem_Icc] at hm
      have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm.1
      apply div_nonneg (Real.log_nonneg (by linarith))
      apply mul_nonneg <;> linarith
    have h2 := sum_log_div_Icc n hn1
    have h3 : 1 / (n : ℝ) ≤ (Real.log ((n : ℝ) + 1) + 1) / n := by
      apply div_le_div_of_nonneg_right _ hnpos.le
      have : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
      linarith
    have h4 := Real.log_two_lt_d9
    linarith
  have hlow : (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (x := (n : ℝ)) hnpos.le n
    have hpos : (0 : ℝ) < (n : ℝ) ^ n / (n.factorial : ℝ) := by
      have : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
      positivity
    have := Real.log_le_log hpos h
    rw [Real.log_exp, Real.log_div (by positivity) (by exact_mod_cast (Nat.factorial_ne_zero n)),
      Real.log_pow] at this
    linarith
  have hSn : Real.log n - 3 + 1 / n ≤ S := by
    have h5 : (n : ℝ) * Real.log n - 3 * n + 1 ≤ n * S := by
      have : (n : ℝ) * (S + B) ≤ n * (S + (2 - 1 / n)) :=
        mul_le_mul_of_nonneg_left (by linarith) hnpos.le
      have e : (n : ℝ) * (S + (2 - 1 / n)) = n * S + 2 * n - 1 := by field_simp; ring
      linarith
    have e : Real.log n - 3 + 1 / n = ((n : ℝ) * Real.log n - 3 * n + 1) / n := by
      field_simp
    rw [e, div_le_iff₀ hnpos]
    linarith
  have hlx : Real.log x ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log (by linarith) hxn.le
  have := log_succ_sub_log_le n hn1
  linarith
theorem sum_inv_prime_Ioc_le (y x : ℝ) (hy : 2 ≤ y) (hyx : y ≤ x) :
    ∑ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p ≤
      Real.log (Real.log x / Real.log y) + 100 / Real.log y := by
  set M := ⌊y⌋₊ with hM
  set N := ⌊x⌋₊ with hN
  have hM2 : 2 ≤ M := Nat.le_floor (by exact_mod_cast hy)
  have hMN : M ≤ N := Nat.floor_le_floor hyx
  have hAup : ∀ n : ℕ, 1 ≤ n →
      ∑ p ∈ (Iic n).filter Nat.Prime, Real.log p / p ≤ Real.log n + 2 := fun n hn => by
    have := sum_log_prime_div_le (n : ℝ) (by exact_mod_cast hn)
    simpa using this
  have hAlo : ∀ n : ℕ, 1 ≤ n →
      Real.log n - 3 ≤ ∑ p ∈ (Iic n).filter Nat.Prime, Real.log p / p := fun n hn => by
    have := sum_log_prime_div_ge (n : ℝ) (by exact_mod_cast hn)
    simpa using this
  have hlogM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  set AM := ∑ p ∈ (Iic M).filter Nat.Prime, Real.log p / p with hAM
  have inv : ∀ n : ℕ, M ≤ n →
      ∑ p ∈ (Ioc M n).filter Nat.Prime, (1 : ℝ) / p -
          (∑ p ∈ (Iic n).filter Nat.Prime, Real.log p / p - AM) / Real.log n ≤
        Real.log (Real.log n) - Real.log (Real.log M) +
          (5 - Real.log M) * (1 / Real.log M - 1 / Real.log n) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp [hAM]
    | succ n hn ih =>
      set S := ∑ p ∈ (Ioc M n).filter Nat.Prime, (1 : ℝ) / p with hS
      set A := ∑ p ∈ (Iic n).filter Nat.Prime, Real.log p / p with hA
      have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      have hn1 : (1 : ℝ) < (n : ℝ) + 1 := by
        have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        linarith
      have hlogn1 : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos hn1
      have hS' := sum_primes_Ioc_succ (fun p : ℕ => (1 : ℝ) / p) hn
      have hA' := sum_primes_succ (fun p : ℕ => Real.log p / p) n
      rw [hS', hA']
      push_cast
      have hrel : S + (if (n + 1).Prime then 1 / ((n : ℝ) + 1) else 0) -
          (A + (if (n + 1).Prime then Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1) else 0) - AM) /
            Real.log ((n : ℝ) + 1) = S - (A - AM) / Real.log ((n : ℝ) + 1) := by
        split_ifs
        · field_simp; ring
        · ring
      rw [hrel]
      have hD : A - AM ≤ Real.log n + 5 - Real.log M := by
        have h1 := hAup n (by omega)
        have h2 := hAlo M (by omega)
        linarith
      set d := 1 / Real.log n - 1 / Real.log ((n : ℝ) + 1) with hd
      have hd0 : 0 ≤ d := by
        rw [hd, sub_nonneg]
        apply one_div_le_one_div_of_le hlogn
        exact Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by linarith)
      have hll : Real.log n * d ≤
          Real.log (Real.log ((n : ℝ) + 1)) - Real.log (Real.log n) := by
        have h := Real.one_sub_inv_le_log_of_pos
          (x := Real.log ((n : ℝ) + 1) / Real.log n) (by positivity)
        rw [Real.log_div hlogn1.ne' hlogn.ne', inv_div] at h
        have e : Real.log n * d = 1 - Real.log n / Real.log ((n : ℝ) + 1) := by
          rw [hd]; field_simp
        linarith
      have hDd : (A - AM) * d ≤ (Real.log n + 5 - Real.log M) * d :=
        mul_le_mul_of_nonneg_right hD hd0
      have e1 : S - (A - AM) / Real.log ((n : ℝ) + 1) =
          (S - (A - AM) / Real.log n) + (A - AM) * d := by
        rw [hd]; ring
      have e2 : (Real.log n + 5 - Real.log M) * d = Real.log n * d +
          ((5 - Real.log M) * (1 / Real.log M - 1 / Real.log ((n : ℝ) + 1)) -
            (5 - Real.log M) * (1 / Real.log M - 1 / Real.log n)) := by
        rw [hd]; ring
      rw [e1]
      linarith
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hmain := inv N hMN
  have hD : ∑ p ∈ (Iic N).filter Nat.Prime, Real.log p / p - AM ≤
      Real.log N + 5 - Real.log M := by
    have h1 := hAup N (by omega)
    have h2 := hAlo M (by omega)
    linarith
  have hD' : (∑ p ∈ (Iic N).filter Nat.Prime, Real.log p / p - AM) / Real.log N ≤
      1 + (5 - Real.log M) * (1 / Real.log N) := by
    have := div_le_div_of_nonneg_right hD hlogN.le
    have e : (Real.log N + 5 - Real.log M) / Real.log N =
        1 + (5 - Real.log M) * (1 / Real.log N) := by
      field_simp; ring
    linarith
  have eM : Real.log M * (1 / Real.log M) = 1 := by field_simp
  have hSN : ∑ p ∈ (Ioc M N).filter Nat.Prime, (1 : ℝ) / p ≤
      Real.log (Real.log N) - Real.log (Real.log M) + 5 / Real.log M := by
    have e5 : 5 / Real.log M = 5 * (1 / Real.log M) := by ring
    rw [e5]
    nlinarith
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hMy : (M : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyM : y < M + 1 := Nat.lt_floor_add_one y
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hM2r : (2 : ℝ) ≤ M := by exact_mod_cast hM2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have h1 : Real.log (Real.log N) ≤ Real.log (Real.log x) :=
    Real.log_le_log hlogN (Real.log_le_log hNpos hNx)
  rw [Real.log_div hlogx.ne' hlogy.ne']
  have hmL : Real.log M ≤ Real.log y := Real.log_le_log hMpos hMy
  have hLm : Real.log y - Real.log M ≤ 1 / 2 := by
    have h := Real.log_le_sub_one_of_pos (x := y / M) (by positivity)
    rw [Real.log_div (by linarith) hMpos.ne'] at h
    have h2 : y / M - 1 ≤ 1 / 2 := by
      rw [div_sub_one hMpos.ne', div_le_iff₀ hMpos]; linarith
    linarith
  have hll : Real.log (Real.log y) - Real.log (Real.log M) ≤
      (Real.log y - Real.log M) / Real.log M := by
    have h := Real.log_le_sub_one_of_pos (x := Real.log y / Real.log M) (by positivity)
    rw [Real.log_div hlogy.ne' hlogM.ne', div_sub_one hlogM.ne'] at h
    exact h
  have h3 : (Real.log y - Real.log M) / Real.log M ≤ (1 / 2) / Real.log M :=
    div_le_div_of_nonneg_right hLm hlogM.le
  have h4 : (11 / 2) / Real.log M ≤ 100 / Real.log y := by
    rw [div_le_div_iff₀ hlogM hlogy]
    have hl2 : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) hM2r
    have := Real.log_two_gt_d9
    nlinarith
  have e : (1 / 2) / Real.log M + 5 / Real.log M = (11 / 2) / Real.log M := by ring
  linarith
theorem prod_one_add_inv_prime_le (y x : ℝ) (hy : 2 ≤ y) (hyx : y ≤ x) :
    ∏ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, (1 + (1 : ℝ) / p) ≤
      Real.exp (100 / Real.log y) * (Real.log x / Real.log y) := by
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  calc ∏ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, (1 + (1 : ℝ) / p)
      ≤ ∏ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, Real.exp ((1 : ℝ) / p) := by
        apply prod_le_prod
        · intro p _; positivity
        · intro p _
          have := Real.add_one_le_exp ((1 : ℝ) / p)
          linarith
    _ = Real.exp (∑ p ∈ (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p) := by
        rw [Real.exp_sum]
    _ ≤ Real.exp (Real.log (Real.log x / Real.log y) + 100 / Real.log y) :=
        Real.exp_le_exp.mpr (sum_inv_prime_Ioc_le y x hy hyx)
    _ = Real.exp (100 / Real.log y) * (Real.log x / Real.log y) := by
        rw [Real.exp_add, Real.exp_log (by positivity), mul_comm]
theorem prod_inv_one_sub_inv_prime_le : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
    ∏ p ∈ (Iic ⌊x⌋₊).filter Nat.Prime, (1 - (1 : ℝ) / p)⁻¹ ≤ C * Real.log x := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Real.exp (3 / 2 + 100 / Real.log 2) / Real.log 2, by positivity, fun x hx => ?_⟩
  set n := ⌊x⌋₊ with hn
  have hn2 : 2 ≤ n := Nat.le_floor (by exact_mod_cast hx)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hprod : ∏ p ∈ (Iic n).filter Nat.Prime, (1 - (1 : ℝ) / p)⁻¹ ≤
      Real.exp (∑ p ∈ (Iic n).filter Nat.Prime,
        ((1 : ℝ) / p + 1 / ((p : ℝ) * ((p : ℝ) - 1)))) := by
    rw [Real.exp_sum]
    apply prod_le_prod
    · intro p hp
      have hpp := (mem_filter.1 hp).2
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
      have : 0 < 1 - (1 : ℝ) / p := by
        rw [sub_pos, div_lt_one (by linarith)]; exact hp1
      positivity
    · intro p hp
      have hpp := (mem_filter.1 hp).2
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
      have e : (1 - (1 : ℝ) / p)⁻¹ = ((1 : ℝ) / p + 1 / ((p : ℝ) * ((p : ℝ) - 1))) + 1 := by
        have : (p : ℝ) - 1 ≠ 0 := by linarith
        have : (p : ℝ) ≠ 0 := by linarith
        field_simp; ring
      rw [e]
      exact Real.add_one_le_exp _
  rw [sum_add_distrib] at hprod
  have hsub : (Iic n).filter Nat.Prime ⊆ Icc 2 n := by
    intro p hp
    simp only [mem_filter, mem_Iic] at hp
    simp only [mem_Icc]
    exact ⟨hp.2.two_le, hp.1⟩
  have hB : ∑ p ∈ (Iic n).filter Nat.Prime, 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
    have h1 : ∑ p ∈ (Iic n).filter Nat.Prime, 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤
        ∑ m ∈ Icc 2 n, 1 / ((m : ℝ) * ((m : ℝ) - 1)) := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro m hm _
      simp only [mem_Icc] at hm
      have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm.1
      apply div_nonneg zero_le_one
      apply mul_nonneg <;> linarith
    have h2 := sum_inv_Icc n (by omega)
    have h3 : (0 : ℝ) ≤ 1 / n := by positivity
    linarith
  have hsplit : (Iic n).filter Nat.Prime ⊆ insert 2 ((Ioc 2 n).filter Nat.Prime) := by
    intro p hp
    simp only [mem_filter, mem_Iic] at hp
    simp only [mem_insert, mem_filter, mem_Ioc]
    rcases eq_or_ne p 2 with h | h
    · left; exact h
    · right; exact ⟨⟨lt_of_le_of_ne hp.2.two_le (Ne.symm h), hp.1⟩, hp.2⟩
  have hA : ∑ p ∈ (Iic n).filter Nat.Prime, (1 : ℝ) / p ≤
      1 / 2 + ∑ p ∈ (Ioc 2 n).filter Nat.Prime, (1 : ℝ) / p := by
    have h1 := sum_le_sum_of_subset_of_nonneg hsplit
      (f := fun p : ℕ => (1 : ℝ) / p) (fun p _ _ => by positivity)
    rw [sum_insert (by simp)] at h1
    norm_num at h1 ⊢
    linarith
  have hM2 := sum_inv_prime_Ioc_le 2 x le_rfl hx
  have hfl : ⌊(2 : ℝ)⌋₊ = 2 := by norm_num
  rw [hfl] at hM2
  have hexp : Real.exp (∑ p ∈ (Iic n).filter Nat.Prime, (1 : ℝ) / p +
      ∑ p ∈ (Iic n).filter Nat.Prime, 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤
      Real.exp (3 / 2 + 100 / Real.log 2 + Real.log (Real.log x / Real.log 2)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hR : Real.exp (3 / 2 + 100 / Real.log 2 + Real.log (Real.log x / Real.log 2)) =
      Real.exp (3 / 2 + 100 / Real.log 2) * (Real.log x / Real.log 2) := by
    rw [Real.exp_add, Real.exp_log (by positivity)]
  have e : Real.exp (3 / 2 + 100 / Real.log 2) * (Real.log x / Real.log 2) =
      Real.exp (3 / 2 + 100 / Real.log 2) / Real.log 2 * Real.log x := by ring
  linarith
end DuffinSchaeffer
end Port24_Parts_Mertens

section Port24_Parts_Anatomy
open Finset
namespace DuffinSchaeffer
lemma sum_prod_one_add_le (N : ℕ) (T : ℝ) (g : ℕ → ℝ) (hg : ∀ p, 0 ≤ g p) :
    ∑ n ∈ Icc 1 N, ∏ p ∈ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)), (1 + g p) ≤
      (N : ℝ) * ∏ p ∈ (Icc 1 N).filter (fun p : ℕ => p.Prime ∧ T ≤ (p : ℝ)),
        (1 + g p / p) := by
  classical
  set P := (Icc 1 N).filter (fun p : ℕ => p.Prime ∧ T ≤ (p : ℝ)) with hPdef
  have hsub : ∀ n ∈ Icc 1 N, n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)) ⊆ P := by
    intro n hn p hp
    simp only [mem_filter, Nat.mem_primeFactors] at hp
    obtain ⟨⟨hpp, hpn, hn0⟩, hT⟩ := hp
    simp only [hPdef, mem_filter, mem_Icc] at hn ⊢
    exact ⟨⟨hpp.one_lt.le, (Nat.le_of_dvd (by omega) hpn).trans hn.2⟩, hpp, hT⟩
  have step1 : ∀ n ∈ Icc 1 N,
      ∏ p ∈ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)), (1 + g p)
        = ∑ A ∈ P.powerset, if A ⊆ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ))
            then ∏ p ∈ A, g p else 0 := by
    intro n hn
    rw [prod_one_add, ← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext A
    simp only [mem_powerset, mem_filter]
    exact ⟨fun h => ⟨h.trans (hsub n hn), h⟩, fun h => h.2⟩
  rw [sum_congr rfl step1, sum_comm]
  have hIcc : Icc 1 N = Ioc 0 N := by ext; simp; omega
  have step2 : ∀ A ∈ P.powerset,
      ∑ n ∈ Icc 1 N, (if A ⊆ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ))
          then ∏ p ∈ A, g p else 0) ≤ (N : ℝ) * ∏ p ∈ A, (g p / p) := by
    intro A hA
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hApr : ∀ p ∈ A, p.Prime := fun p hp => ((mem_filter.1 (mem_powerset.1 hA hp)).2).1
    have hcard : ((Icc 1 N).filter
        (fun n => A ⊆ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)))).card
          ≤ N / ∏ p ∈ A, p := by
      rw [← Nat.Ioc_filter_dvd_card_eq_div, ← hIcc]
      apply card_le_card
      intro n hn
      simp only [mem_filter] at hn ⊢
      refine ⟨hn.1, ?_⟩
      apply Finset.prod_primes_dvd
      · intro p hp; exact Nat.prime_iff.1 (hApr p hp)
      · intro p hp
        have := hn.2 hp
        simp only [mem_filter, Nat.mem_primeFactors] at this
        exact this.1.2.1
    have hG : 0 ≤ ∏ p ∈ A, g p := prod_nonneg (fun p _ => hg p)
    calc (((Icc 1 N).filter
          (fun n => A ⊆ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)))).card : ℝ)
            * ∏ p ∈ A, g p
          ≤ ((N / ∏ p ∈ A, p : ℕ) : ℝ) * ∏ p ∈ A, g p := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hG
      _ ≤ ((N : ℝ) / ∏ p ∈ A, (p : ℝ)) * ∏ p ∈ A, g p := by
          gcongr; rw [← Nat.cast_prod]; exact Nat.cast_div_le
      _ = (N : ℝ) * ∏ p ∈ A, (g p / p) := by
          rw [prod_div_distrib]; try ring
  calc _ ≤ ∑ A ∈ P.powerset, (N : ℝ) * ∏ p ∈ A, (g p / p) := sum_le_sum step2
    _ = _ := by rw [← mul_sum, prod_one_add]
lemma exp_sub_one_le_eight_mul (u : ℝ) (h0 : 0 ≤ u) (h2 : u ≤ 2) :
    Real.exp u - 1 ≤ 8 * u := by
  have h1 : -u + 1 ≤ Real.exp (-u) := Real.add_one_le_exp (-u)
  have hprod : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have hle : Real.exp u - 1 ≤ u * Real.exp u := by nlinarith [Real.exp_pos u]
  have he2 : Real.exp u ≤ 8 := by
    have : Real.exp u ≤ Real.exp 2 := Real.exp_le_exp.2 h2
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  nlinarith
theorem card_many_large_prime_factors_le : ∃ C : ℝ, 0 < C ∧ ∀ x t c : ℝ, 1 ≤ x → 1 ≤ t →
    1 ≤ c → c ≤ 10 →
    (((Icc 1 ⌊x⌋₊).filter (fun n : ℕ =>
        c ≤ ∑ p ∈ n.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)), (1 : ℝ) / p)).card : ℝ) ≤
      C * x * Real.exp (-(t ^ Real.exp (c - 1))) := by
  refine ⟨Real.exp (Real.exp (300 * Real.exp 9)), Real.exp_pos _, ?_⟩
  intro x t c hx ht hc1 hc10
  set E := Real.exp (c - 1) with hE
  set T := t ^ E with hT
  set S := (Icc 1 ⌊x⌋₊).filter (fun n : ℕ =>
        c ≤ ∑ p ∈ n.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)), (1 : ℝ) / p) with hS
  set K := Real.exp (300 * Real.exp 9) with hK
  have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_exp (by linarith)
  have hE9 : E ≤ Real.exp 9 := Real.exp_le_exp.2 (by linarith)
  have hx0 : 0 ≤ x := by linarith
  have ht0 : 0 < t := by linarith
  have hlt0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have hTexp : T = Real.exp (Real.log t * E) := Real.rpow_def_of_pos ht0 E
  have hTpos : 0 < T := by rw [hTexp]; exact Real.exp_pos _
  have hcardx : (S.card : ℝ) ≤ x := by
    have : S.card ≤ ⌊x⌋₊ := (card_filter_le _ _).trans (by simp)
    calc (S.card : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast this
      _ ≤ x := Nat.floor_le hx0
  have hK64 : 64 ≤ K := by
    have h1 : 1 ≤ Real.exp 9 := Real.one_le_exp (by norm_num)
    have := Real.add_one_le_exp (300 * Real.exp 9)
    linarith
  by_cases hts : Real.log t ≤ 300
  ·
    have hTle : T ≤ K := by
      rw [hTexp, hK]
      apply Real.exp_le_exp.2
      nlinarith
    have h1 : 1 ≤ Real.exp K * Real.exp (-T) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    calc (S.card : ℝ) ≤ x := hcardx
      _ ≤ (Real.exp K * Real.exp (-T)) * x := le_mul_of_one_le_left hx0 h1
      _ = Real.exp K * x * Real.exp (-T) := by ring
  · rw [not_le] at hts
    have htT : t ≤ T := by
      have := Real.rpow_le_rpow_of_exponent_le ht hE1
      simpa [hT] using this
    have hlog2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have ht2 : 2 ≤ t / 2 := by
      have : Real.exp 300 < t := by
        rw [← Real.exp_log ht0]; exact Real.exp_lt_exp.2 hts
      have : (4 : ℝ) ≤ Real.exp 300 := by
        have := Real.add_one_le_exp (300 : ℝ); linarith
      linarith
    set B := (Ioc ⌊t / 2⌋₊ ⌊T⌋₊).filter Nat.Prime with hB
    have hBle : ∑ p ∈ B, (1 : ℝ) / p ≤ c - 1 / 2 := by
      have hM := sum_inv_prime_Ioc_le (t / 2) T ht2 (by linarith)
      have hlogt2 : Real.log (t / 2) = Real.log t - Real.log 2 :=
        Real.log_div (by linarith) (by norm_num)
      have hlogT : Real.log T = E * Real.log t := by
        rw [hT]; exact Real.log_rpow ht0 E
      have hden : 299 ≤ Real.log t - Real.log 2 := by linarith
      have hdpos : 0 < Real.log t - Real.log 2 := by linarith
      have hr : Real.log (Real.log T / Real.log (t / 2))
          = (c - 1) + Real.log (Real.log t / (Real.log t - Real.log 2)) := by
        rw [hlogT, hlogt2, mul_div_assoc, Real.log_mul (by positivity)
          (div_pos (by linarith) hdpos).ne', hE, Real.log_exp]
      have hr2 : Real.log (Real.log t / (Real.log t - Real.log 2))
          ≤ Real.log 2 / (Real.log t - Real.log 2) := by
        have := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0:ℝ) < Real.log t) hdpos)
        have heq : Real.log t / (Real.log t - Real.log 2) - 1
            = Real.log 2 / (Real.log t - Real.log 2) := by
          field_simp; ring
        linarith
      rw [hr, hlogt2] at hM
      have h100 : 100 / (Real.log t - Real.log 2) ≤ 100 / 299 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
      have hl2 : Real.log 2 / (Real.log t - Real.log 2) ≤ 1 / 299 := by
        rw [div_le_div_iff₀ hdpos (by norm_num)]; nlinarith
      linarith
    set g : ℕ → ℝ := fun p => Real.exp (2 * T / p) - 1 with hgdef
    have hg : ∀ p, 0 ≤ g p := by
      intro p; simp only [hgdef, sub_nonneg]
      exact Real.one_le_exp (by positivity)
    set F : ℕ → ℝ := fun n =>
      ∏ p ∈ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)), (1 + g p) with hFdef
    have hF0 : ∀ n, 0 ≤ F n := fun n => prod_nonneg (fun p _ => by linarith [hg p])
    have hrank : ∀ n ∈ S, 1 ≤ Real.exp (-T) * F n := by
      intro n hn
      simp only [hS, mem_filter] at hn
      obtain ⟨-, hsum⟩ := hn
      set Q := n.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)) with hQ
      have hsplit := sum_filter_add_sum_filter_not Q (fun p : ℕ => (p : ℝ) < T)
        (fun p : ℕ => (1 : ℝ) / p)
      have hA : ∑ p ∈ Q.filter (fun p : ℕ => (p : ℝ) < T), (1 : ℝ) / p
          ≤ ∑ p ∈ B, (1 : ℝ) / p := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          simp only [hQ, mem_filter, Nat.mem_primeFactors] at hp
          obtain ⟨⟨⟨hpp, -, -⟩, htp⟩, hpT⟩ := hp
          simp only [hB, mem_filter, mem_Ioc]
          refine ⟨⟨?_, Nat.le_floor hpT.le⟩, hpp⟩
          have : (⌊t / 2⌋₊ : ℝ) < p :=
            lt_of_le_of_lt (Nat.floor_le (by linarith)) (by linarith)
          exact_mod_cast this
        · intro p _ _; positivity
      have hC : ∑ p ∈ Q.filter (fun p : ℕ => ¬ (p : ℝ) < T), (1 : ℝ) / p
          ≤ ∑ p ∈ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)), (1 : ℝ) / p := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          simp only [hQ, mem_filter, not_lt] at hp ⊢
          exact ⟨hp.1.1, hp.2⟩
        · intro p _ _; positivity
      have hhalf : 1 / 2 ≤ ∑ p ∈ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)),
          (1 : ℝ) / p := by linarith
      have hFe : F n = Real.exp (∑ p ∈ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)),
          2 * T / p) := by
        rw [hFdef, Real.exp_sum]
        apply prod_congr rfl; intro p _; simp only [hgdef]; ring
      rw [hFe, ← Real.exp_add]
      apply Real.one_le_exp
      have : ∑ p ∈ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)), 2 * T / (p : ℝ)
          = 2 * T * ∑ p ∈ n.primeFactors.filter (fun p : ℕ => T ≤ (p : ℝ)), (1 : ℝ) / p := by
        rw [mul_sum]; apply sum_congr rfl; intro p _; ring
      rw [this]; nlinarith
    set N := ⌊x⌋₊ with hN
    set P := (Icc 1 N).filter (fun p : ℕ => p.Prime ∧ T ≤ (p : ℝ)) with hP
    have hPsum : ∑ p ∈ P, g p / p ≤ 64 := by
      have hterm : ∑ p ∈ P, g p / p ≤ ∑ p ∈ P, 16 * T * ((p : ℝ) ^ 2)⁻¹ := by
        apply sum_le_sum
        intro p hp
        simp only [hP, mem_filter] at hp
        have hpT : T ≤ (p : ℝ) := hp.2.2
        have hp0 : 0 < (p : ℝ) := by linarith
        have hu2 : 2 * T / p ≤ 2 := by rw [div_le_iff₀ hp0]; linarith
        have := exp_sub_one_le_eight_mul (2 * T / p) (by positivity) hu2
        simp only [hgdef]
        rw [div_le_iff₀ hp0]
        calc Real.exp (2 * T / p) - 1 ≤ 8 * (2 * T / p) := this
          _ = 16 * T * ((p : ℝ) ^ 2)⁻¹ * p := by field_simp; ring
      have hsq : ∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹ ≤ 4 / T := by
        set k := ⌊T / 2⌋₊ with hk
        have hk1 : T / 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
        calc ∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹ ≤ ∑ i ∈ Ioo k (N + 1), ((i : ℝ) ^ 2)⁻¹ := by
              apply sum_le_sum_of_subset_of_nonneg
              · intro p hp
                simp only [hP, mem_filter, mem_Icc] at hp
                simp only [mem_Ioo]
                refine ⟨?_, by omega⟩
                have : (k : ℝ) < p :=
                  lt_of_le_of_lt (Nat.floor_le (by positivity)) (by linarith [hp.2.2])
                exact_mod_cast this
              · intro i _ _; positivity
          _ ≤ 2 / ((k : ℝ) + 1) := sum_Ioo_inv_sq_le k (N + 1)
          _ ≤ 2 / (T / 2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hk1.le
          _ = 4 / T := by field_simp; ring
      calc ∑ p ∈ P, g p / p ≤ ∑ p ∈ P, 16 * T * ((p : ℝ) ^ 2)⁻¹ := hterm
        _ = 16 * T * ∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹ := by rw [mul_sum]
        _ ≤ 16 * T * (4 / T) := by gcongr
        _ = 64 := by field_simp; ring
    have hPprod : ∏ p ∈ P, (1 + g p / p) ≤ Real.exp 64 := by
      calc ∏ p ∈ P, (1 + g p / p) ≤ ∏ p ∈ P, Real.exp (g p / p) := by
            apply Finset.prod_le_prod
            · intro p _; have := hg p; positivity
            · intro p _; have := Real.add_one_le_exp (g p / p); linarith
        _ = Real.exp (∑ p ∈ P, g p / p) := (Real.exp_sum _ _).symm
        _ ≤ Real.exp 64 := Real.exp_le_exp.2 hPsum
    have hall : ∑ n ∈ Icc 1 N, F n ≤ x * Real.exp 64 := by
      calc ∑ n ∈ Icc 1 N, F n ≤ (N : ℝ) * ∏ p ∈ P, (1 + g p / p) :=
            sum_prod_one_add_le N T g hg
        _ ≤ x * Real.exp 64 := by
            gcongr
            · exact prod_nonneg (fun p _ => by have := hg p; positivity)
            · exact Nat.floor_le hx0
    have hSsub : S ⊆ Icc 1 N := filter_subset _ _
    calc (S.card : ℝ) = ∑ n ∈ S, (1 : ℝ) := by simp
      _ ≤ ∑ n ∈ S, Real.exp (-T) * F n := sum_le_sum hrank
      _ ≤ ∑ n ∈ Icc 1 N, Real.exp (-T) * F n :=
          sum_le_sum_of_subset_of_nonneg hSsub (fun n _ _ => by
            have := hF0 n; positivity)
      _ = Real.exp (-T) * ∑ n ∈ Icc 1 N, F n := by rw [mul_sum]
      _ ≤ Real.exp (-T) * (x * Real.exp 64) := by gcongr
      _ ≤ Real.exp (-T) * (x * Real.exp K) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hK64) hx0) (Real.exp_pos _).le
      _ = Real.exp K * x * Real.exp (-T) := by ring
end DuffinSchaeffer
end Port24_Parts_Anatomy

section Port24_Parts_CircleTransfer
open MeasureTheory Filter
namespace DuffinSchaeffer
theorem limsup_Aq_eq (ψ : ℕ → ℝ) :
    limsup (Aq ψ) atTop = addWellApproximable UnitAddCircle (fun n => ψ n / n) := by
  unfold addWellApproximable
  rw [← Nat.cofinite_eq_atTop, cofinite.limsup_set_eq, cofinite.blimsup_set_eq]
  ext x
  simp only [Set.mem_ofPred_eq]
  have hsub1 : {n | 0 < n ∧ x ∈ approxAddOrderOf UnitAddCircle n (ψ n / n)} ⊆
      {n | x ∈ Aq ψ n} := fun n hn => hn.2
  have hsub2 : {n | x ∈ Aq ψ n} ⊆
      insert 0 {n | 0 < n ∧ x ∈ approxAddOrderOf UnitAddCircle n (ψ n / n)} := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hn⟩
  constructor
  · intro h
    by_contra hfin
    exact h ((Set.not_infinite.1 hfin).insert 0 |>.subset hsub2)
  · intro h
    exact h.mono hsub1
theorem addWellApproximable_mono {δ δ' : ℕ → ℝ} (h : ∀ n, δ n ≤ δ' n) :
    addWellApproximable UnitAddCircle δ ⊆ addWellApproximable UnitAddCircle δ' := by
  intro x hx
  rw [UnitAddCircle.mem_addWellApproximable_iff] at hx ⊢
  apply hx.mono
  rintro q ⟨p, hpq, hcop, hdist⟩
  exact ⟨p, hpq, hcop, hdist.trans_le (h q)⟩
theorem ae_approximable_of_ae_circle (ψ : ℕ → ℝ)
    (h : ∀ᵐ x : UnitAddCircle, x ∈ addWellApproximable UnitAddCircle (fun n => ψ n / n)) :
    ∀ᵐ α : ℝ, Erdos999.IsApproximable ψ α := by
  have hpt : ∀ α : ℝ, ((α : UnitAddCircle) ∈
      addWellApproximable UnitAddCircle (fun n => ψ n / n)) → Erdos999.IsApproximable ψ α := by
    intro α hα
    rw [UnitAddCircle.mem_addWellApproximable_iff] at hα
    apply hα.mono
    rintro q ⟨p, hpq, hcop, hdist⟩
    have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le _) hpq
    set k : ℤ := round (α - (p : ℝ) / q) with hk
    refine ⟨hq, (p : ℤ) + k * q, ?_, ?_⟩
    ·
      have h1 : Int.gcd ((p : ℤ) + k * q) (q : ℤ) = Int.gcd (p : ℤ) (q : ℤ) := by
        simp
      rw [h1, Int.gcd_natCast_natCast]
      exact hcop
    · have hn : ‖((α - (p : ℝ) / q : ℝ) : UnitAddCircle)‖ < ψ q / q := by
        simpa [AddCircle.coe_sub] using hdist
      rw [UnitAddCircle.norm_eq] at hn
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq
      have : α - ((((p : ℤ) + k * q : ℤ) : ℝ) / ((q : ℕ) : ℝ)) =
          α - (p : ℝ) / q - (k : ℝ) := by
        push_cast
        field_simp
        ring
      rw [this]
      exact hn
  have hloc : ∀ n : ℤ, ∀ᵐ (α : ℝ) ∂(volume.restrict (Set.Ioc (n : ℝ) (n + 1))),
      (α : UnitAddCircle) ∈ addWellApproximable UnitAddCircle (fun n => ψ n / n) :=
    fun n => (AddCircle.measurePreserving_mk (1 : ℝ) (n : ℝ)).quasiMeasurePreserving.ae h
  have hall : ∀ᵐ (α : ℝ) ∂(volume.restrict (⋃ n : ℤ, Set.Ioc (n : ℝ) (n + 1))),
      (α : UnitAddCircle) ∈ addWellApproximable UnitAddCircle (fun n => ψ n / n) :=
    (ae_restrict_iUnion_iff _ _).2 hloc
  have hU : (⋃ n : ℤ, Set.Ioc (n : ℝ) (n + 1)) = Set.univ := by
    simpa [zero_add] using iUnion_Ioc_add_intCast (0 : ℝ)
  rw [hU, Measure.restrict_univ] at hall
  exact hall.mono fun α hα => hpt α hα
end DuffinSchaeffer
end Port24_Parts_CircleTransfer

section Port24_Parts_Convergence
open MeasureTheory Filter
namespace DuffinSchaeffer
theorem measurableSet_Aq (ψ : ℕ → ℝ) (q : ℕ) : MeasurableSet (Aq ψ q) :=
  Metric.isOpen_thickening.measurableSet
theorem alt_volume_cthickening_le (q : ℕ) (hq : 0 < q) (δ : ℝ) (hδ : 0 ≤ δ) :
    volume (Metric.cthickening δ {y : UnitAddCircle | addOrderOf y = q}) ≤
      ENNReal.ofReal (2 * δ * Nat.totient q) := by
  have hfin : {y : UnitAddCircle | addOrderOf y = q}.Finite :=
    AddCircle.finite_setOfPred_addOrderOf_eq 1 hq
  have hcard : hfin.toFinset.card = Nat.totient q := by
    rw [← Nat.card_eq_card_finite_toFinset hfin]
    exact AddCircle.card_addOrderOf_eq_totient 1
  rw [hfin.isCompact.cthickening_eq_biUnion_closedBall hδ]
  have h1 : (⋃ x ∈ {y : UnitAddCircle | addOrderOf y = q}, Metric.closedBall x δ) =
      ⋃ x ∈ hfin.toFinset, Metric.closedBall x δ := by
    simp
  rw [h1]
  calc volume (⋃ x ∈ hfin.toFinset, Metric.closedBall x δ)
      ≤ ∑ x ∈ hfin.toFinset, volume (Metric.closedBall x δ) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ hfin.toFinset, ENNReal.ofReal (2 * δ) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [AddCircle.volume_closedBall]
        exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
    _ = ENNReal.ofReal (2 * δ * Nat.totient q) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_comm, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
theorem volume_Aq_le (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (q : ℕ) (hq : 0 < q) :
    volume.real (Aq ψ q) ≤ 2 * weight ψ q := by
  have hδ : 0 ≤ ψ q / q := div_nonneg (hψ q) (Nat.cast_nonneg q)
  have hsub : Aq ψ q ⊆ Metric.cthickening (ψ q / q) {y : UnitAddCircle | addOrderOf y = q} :=
    Metric.thickening_subset_cthickening _ _
  have h := (measure_mono hsub).trans (alt_volume_cthickening_le q hq _ hδ)
  have heq : 2 * (ψ q / q) * Nat.totient q = 2 * weight ψ q := by
    unfold weight; ring
  rw [heq] at h
  exact ENNReal.toReal_le_of_le_ofReal (by
    unfold weight; exact mul_nonneg zero_le_two
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hψ q)) (Nat.cast_nonneg _))) h
noncomputable def alt_Cq (ψ : ℕ → ℝ) (q : ℕ) : Set UnitAddCircle :=
  if 0 < q then Metric.cthickening (ψ q / q) {y : UnitAddCircle | addOrderOf y = q} else ∅
theorem alt_ae_eventually_not_mem_Cq (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (hs : Summable (weight ψ)) :
    ∀ᵐ x : UnitAddCircle, ∀ᶠ q in atTop, x ∉ alt_Cq ψ q := by
  apply ae_eventually_notMem
  have hw : ∀ q, 0 ≤ 2 * weight ψ q := fun q => by
    unfold weight; exact mul_nonneg zero_le_two
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hψ q)) (Nat.cast_nonneg _))
  have hle : ∀ q, volume (alt_Cq ψ q) ≤ ENNReal.ofReal (2 * weight ψ q) := by
    intro q
    unfold alt_Cq
    split_ifs with hq
    · have h := alt_volume_cthickening_le q hq (ψ q / q) (div_nonneg (hψ q) (Nat.cast_nonneg q))
      have heq : 2 * (ψ q / q) * Nat.totient q = 2 * weight ψ q := by
        unfold weight; ring
      rwa [heq] at h
    · simp
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' q, 2 * weight ψ q)) ?_
  rw [ENNReal.ofReal_tsum_of_nonneg hw (hs.mul_left 2)]
  exact ENNReal.tsum_le_tsum hle
theorem mem_Cq_of_approx (ψ : ℕ → ℝ) {α : ℝ} {q : ℕ} (hq : 0 < q)
    {p : ℤ} (hg : Int.gcd p q = 1) (ha : |α - p / q| < ψ q / q) :
    (α : UnitAddCircle) ∈ alt_Cq ψ q := by
  simp only [alt_Cq, hq, ↓reduceIte]
  refine Metric.mem_cthickening_of_dist_le _ (((p : ℝ) / q * 1 : ℝ) : UnitAddCircle) _ _ ?_ ?_
  · exact AddCircle.addOrderOf_div_of_gcd_eq_one' hq (by simpa [Int.gcd] using hg)
  · rw [dist_eq_norm, ← AddCircle.coe_sub, mul_one]
    exact QuotientAddGroup.norm_mk_le_norm.trans (by rw [Real.norm_eq_abs]; exact ha.le)

theorem ae_not_approximable_of_summable (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q)
    (hs : Summable (weight ψ)) : ∀ᵐ α : ℝ, ¬ Erdos999.IsApproximable ψ α := by
  have hBC := alt_ae_eventually_not_mem_Cq ψ hψ hs
  have hR : ∀ᵐ α : ℝ, ∀ᶠ q in atTop, ((α : ℝ) : UnitAddCircle) ∉ alt_Cq ψ q := by
    rw [← Measure.restrict_univ (μ := (volume : Measure ℝ)), ← iUnion_Ioc_add_intCast (0 : ℝ),
      ae_restrict_iUnion_iff]
    intro n
    exact (AddCircle.measurePreserving_mk (1 : ℝ) (0 + n)).quasiMeasurePreserving.ae hBC
  filter_upwards [hR] with α hα
  have hfin : {q : ℕ | ((α : ℝ) : UnitAddCircle) ∈ alt_Cq ψ q}.Finite := by
    rw [← Nat.cofinite_eq_atTop] at hα
    simpa using hα
  intro hinf
  apply hinf
  refine hfin.subset ?_
  rintro q ⟨hq, p, hg, ha⟩
  exact mem_Cq_of_approx ψ hq hg ha
end DuffinSchaeffer
end Port24_Parts_Convergence

section Port24_Parts_CoprimeSieve
open Finset
namespace DuffinSchaeffer
namespace CoprimeSieveAux
lemma totient_real (n : ℕ) :
    (Nat.totient n : ℝ) = n * ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / p) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors n)
  simp only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub, Rat.cast_one,
    Rat.cast_inv] at h
  simpa [one_div] using h
lemma prime_factor_bounds {p : ℕ} (hp : p.Prime) :
    0 < 1 - (1 : ℝ) / p ∧ 1 - (1 : ℝ) / p ≤ 1 ∧ 1 / 2 ≤ 1 - (1 : ℝ) / p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h3 : (1 : ℝ) / p ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have h4 : 0 ≤ (1 : ℝ) / p := by positivity
  refine ⟨by linarith, by linarith, by linarith⟩
lemma one_le_factor {p : ℕ} (hp : p.Prime) : 1 ≤ (1 - (1 : ℝ) / p)⁻¹ := by
  obtain ⟨h1, h2, -⟩ := prime_factor_bounds hp
  exact (one_le_inv₀ h1).mpr h2
noncomputable def R (n : ℕ) : ℝ := (n : ℝ) / Nat.totient n
lemma R_nonneg (n : ℕ) : 0 ≤ R n := by unfold R; positivity
lemma R_eq {n : ℕ} (hn : n ≠ 0) : R n = ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / p)⁻¹ := by
  rw [R, totient_real, prod_inv_distrib]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [div_mul_eq_div_div, div_self this, one_div]
lemma R_mono {d n : ℕ} (hd : d ∣ n) (hn : n ≠ 0) : R d ≤ R n := by
  have hd0 : d ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.mp hd)
  rw [R_eq hd0, R_eq hn]
  have hsub : d.primeFactors ⊆ n.primeFactors := Nat.primeFactors_mono hd hn
  rw [← prod_sdiff hsub]
  have h1 : (1 : ℝ) ≤ ∏ p ∈ n.primeFactors \ d.primeFactors, (1 - (1 : ℝ) / p)⁻¹ := by
    calc (1 : ℝ) = ∏ p ∈ n.primeFactors \ d.primeFactors, (1 : ℝ) := by simp
      _ ≤ _ := prod_le_prod (fun _ _ => zero_le_one)
          (fun p hp => one_le_factor (Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1))
  have h2 : 0 ≤ ∏ p ∈ d.primeFactors, (1 - (1 : ℝ) / p)⁻¹ :=
    prod_nonneg (fun p hp => by linarith [one_le_factor (Nat.prime_of_mem_primeFactors hp)])
  nlinarith
lemma R_primePow {d : ℕ} (hd : IsPrimePow d) : R d ≤ 2 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff d).mp hd
  rw [R_eq (pow_ne_zero _ hp.ne_zero), Nat.primeFactors_prime_pow hk.ne' hp, prod_singleton]
  obtain ⟨h1, -, h3⟩ := prime_factor_bounds hp
  rw [inv_le_comm₀ h1 (by norm_num)]
  have : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
  linarith
lemma R_mul_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : R (a * b) ≤ R a * R b := by
  unfold R
  have hta : (0 : ℝ) < Nat.totient a := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero ha)
  have htb : (0 : ℝ) < Nat.totient b := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hb)
  have hsup : (Nat.totient a : ℝ) * Nat.totient b ≤ Nat.totient (a * b) := by
    exact_mod_cast Nat.totient_super_multiplicative a b
  rw [div_mul_div_comm, Nat.cast_mul]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsup
noncomputable def F (m : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n.Coprime m then R n else 0, by simp [R]⟩
lemma F_apply (m n : ℕ) : F m n = if n.Coprime m then R n else 0 := rfl
lemma F_nonneg (m n : ℕ) : 0 ≤ F m n := by
  rw [F_apply]; split_ifs
  · exact R_nonneg n
  · exact le_refl 0
lemma F_mul_log_le (m n : ℕ) :
    F m n * Real.log n ≤ 2 * (ArithmeticFunction.vonMangoldt * F m) n := by
  rw [← ArithmeticFunction.vonMangoldt_sum, mul_sum, ArithmeticFunction.mul_apply]
  have hd := Nat.sum_divisorsAntidiagonal
    (fun a b => ArithmeticFunction.vonMangoldt a * F m b) (n := n)
  rw [hd, mul_sum]
  refine sum_le_sum fun i hi => ?_
  have hid : i ∣ n := Nat.dvd_of_mem_divisors hi
  have hn0 : n ≠ 0 := (Nat.mem_divisors.mp hi).2
  have hi0 : i ≠ 0 := (Nat.pos_of_mem_divisors hi).ne'
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt i := ArithmeticFunction.vonMangoldt_nonneg
  by_cases h0 : ArithmeticFunction.vonMangoldt i = 0
  · rw [h0]; simp
  have hpp : IsPrimePow i := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h0
  have hk0 : n / i ≠ 0 :=
    (Nat.div_pos (Nat.divisor_le hi) (Nat.pos_of_ne_zero hi0)).ne'
  have key : F m n ≤ 2 * F m (n / i) := by
    rw [F_apply, F_apply]
    by_cases h1 : n.Coprime m
    · have h2 : (n / i).Coprime m := Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hid) h1
      rw [if_pos h1, if_pos h2]
      calc R n = R (i * (n / i)) := by rw [Nat.mul_div_cancel' hid]
        _ ≤ R i * R (n / i) := R_mul_le hi0 hk0
        _ ≤ 2 * R (n / i) := mul_le_mul_of_nonneg_right (R_primePow hpp) (R_nonneg _)
    · rw [if_neg h1]
      split_ifs
      · linarith [R_nonneg (n / i)]
      · norm_num
  calc F m n * ArithmeticFunction.vonMangoldt i
      = ArithmeticFunction.vonMangoldt i * F m n := mul_comm _ _
    _ ≤ ArithmeticFunction.vonMangoldt i * (2 * F m (n / i)) := mul_le_mul_of_nonneg_left key hΛ
    _ = 2 * (ArithmeticFunction.vonMangoldt i * F m (n / i)) := by ring
lemma sum_F_log_le (m N : ℕ) :
    ∑ n ∈ Ioc 0 N, F m n * Real.log n ≤
      2 * (Real.log 4 + 4) * N * ∑ n ∈ Ioc 0 N, F m n / n := by
  calc ∑ n ∈ Ioc 0 N, F m n * Real.log n
      ≤ ∑ n ∈ Ioc 0 N, 2 * (ArithmeticFunction.vonMangoldt * F m) n :=
        sum_le_sum fun n _ => F_mul_log_le m n
    _ = 2 * ∑ n ∈ Ioc 0 N, (F m * ArithmeticFunction.vonMangoldt) n := by
        rw [← mul_sum, mul_comm ArithmeticFunction.vonMangoldt (F m)]
    _ = 2 * ∑ k ∈ Ioc 0 N, F m k * ∑ j ∈ Ioc 0 (N / k), ArithmeticFunction.vonMangoldt j := by
        rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
    _ ≤ 2 * ∑ k ∈ Ioc 0 N, F m k * ((Real.log 4 + 4) * ((N : ℝ) / k)) := by
        gcongr with k hk
        · exact F_nonneg m k
        · have h1 : ∑ j ∈ Ioc 0 (N / k), ArithmeticFunction.vonMangoldt j =
              Chebyshev.psi ((N / k : ℕ) : ℝ) := by
            simp [Chebyshev.psi]
          rw [h1]
          calc Chebyshev.psi ((N / k : ℕ) : ℝ) ≤ (Real.log 4 + 4) * ((N / k : ℕ) : ℝ) :=
                Chebyshev.psi_le_const_mul_self (by positivity)
            _ ≤ (Real.log 4 + 4) * ((N : ℝ) / k) := by
                gcongr
                exact Nat.cast_div_le
    _ = 2 * (Real.log 4 + 4) * N * ∑ n ∈ Ioc 0 N, F m n / n := by
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun k _ => by ring
lemma sum_F_logN_le (m N : ℕ) :
    (∑ n ∈ Ioc 0 N, F m n) * Real.log N ≤
      (2 * (Real.log 4 + 4) + 1) * N * ∑ n ∈ Ioc 0 N, F m n / n := by
  have h : ∀ n ∈ Ioc 0 N, F m n * Real.log N ≤ F m n * Real.log n + N * (F m n / n) := by
    intro n hn
    simp only [mem_Ioc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hn.1 hn.2)
    have hlog : Real.log N ≤ Real.log n + N / n := by
      have e : Real.log N = Real.log n + Real.log ((N : ℝ) / n) := by
        rw [Real.log_div hN0.ne' hn0.ne']; ring
      have h2 : Real.log ((N : ℝ) / n) ≤ N / n :=
        (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
      linarith
    have := F_nonneg m n
    calc F m n * Real.log N ≤ F m n * (Real.log n + N / n) := mul_le_mul_of_nonneg_left hlog this
      _ = _ := by ring
  have hA := sum_F_log_le m N
  have e2 : (2 * (Real.log 4 + 4) + 1) * N * ∑ n ∈ Ioc 0 N, F m n / n =
      2 * (Real.log 4 + 4) * N * (∑ n ∈ Ioc 0 N, F m n / n) +
        N * ∑ n ∈ Ioc 0 N, F m n / n := by ring
  calc (∑ n ∈ Ioc 0 N, F m n) * Real.log N = ∑ n ∈ Ioc 0 N, F m n * Real.log N := sum_mul _ _ _
    _ ≤ ∑ n ∈ Ioc 0 N, (F m n * Real.log n + N * (F m n / n)) := sum_le_sum h
    _ = ∑ n ∈ Ioc 0 N, F m n * Real.log n + N * ∑ n ∈ Ioc 0 N, F m n / n := by
        rw [sum_add_distrib, mul_sum]
    _ ≤ _ := by rw [e2]; linarith
noncomputable def f (n : ℕ) : ℝ := 1 / (Nat.totient n : ℝ)
lemma f_nonneg (n : ℕ) : 0 ≤ f n := by unfold f; positivity
lemma f_one : f 1 = 1 := by simp [f]
lemma f_mul {a b : ℕ} (h : Nat.Coprime a b) : f (a * b) = f a * f b := by
  simp [f, Nat.totient_mul h, mul_comm]
lemma f_pow_succ {p : ℕ} (hp : p.Prime) (k : ℕ) :
    f (p ^ (k + 1)) = (1 / ((p : ℝ) - 1)) * (1 / (p : ℝ)) ^ k := by
  rw [f, Nat.totient_prime_pow_succ hp, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_le,
    Nat.cast_one, one_div_pow, div_mul_div_comm, one_mul, mul_comm]
lemma hasSum_f_pow {p : ℕ} (hp : p.Prime) :
    HasSum (fun k => f (p ^ k)) (1 / ((p : ℝ) - 1) * (1 - 1 / (p : ℝ))⁻¹ + 1) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hr0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have hr1 : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (1 / ((p : ℝ) - 1))
  have hg' : HasSum (fun k => f (p ^ (k + 1))) (1 / ((p : ℝ) - 1) * (1 - 1 / (p : ℝ))⁻¹) := by
    have : (fun k => f (p ^ (k + 1))) = fun k => (1 / ((p : ℝ) - 1)) * (1 / (p : ℝ)) ^ k := by
      funext k; exact f_pow_succ hp k
    rw [this]; exact hg
  refine (hasSum_nat_add_iff' 1).mp ?_
  rw [sum_range_one, pow_zero, f_one, add_sub_cancel_right]
  exact hg'
lemma euler_factor_le {p : ℕ} (hp : p.Prime) :
    1 / ((p : ℝ) - 1) * (1 - 1 / (p : ℝ))⁻¹ + 1 ≤
      (1 - 1 / (p : ℝ))⁻¹ * (1 + 2 * ((p : ℝ) ^ 2)⁻¹) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  set q : ℝ := (p : ℝ) with hq
  have hq0 : q ≠ 0 := by linarith
  have hq1 : 0 < q - 1 := by linarith
  have e1 : (1 - 1 / q)⁻¹ = q / (q - 1) := by rw [one_sub_div hq0, inv_div]
  rw [e1]
  have key : q / (q - 1) * (1 + 2 * (q ^ 2)⁻¹) - (1 / (q - 1) * (q / (q - 1)) + 1) =
      (q - 2) / (q * (q - 1) ^ 2) := by
    field_simp
    ring
  have : 0 ≤ (q - 2) / (q * (q - 1) ^ 2) := div_nonneg (by linarith) (by positivity)
  linarith
lemma prod_euler_le (N : ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ p ≤ N) :
    ∏ p ∈ s, (1 / ((p : ℝ) - 1) * (1 - 1 / (p : ℝ))⁻¹ + 1) ≤
      Real.exp 4 * ∏ p ∈ s, (1 - 1 / (p : ℝ))⁻¹ := by
  have hnn : 0 ≤ ∏ p ∈ s, (1 - 1 / (p : ℝ))⁻¹ :=
    prod_nonneg fun p hp => by linarith [one_le_factor (hs p hp).1]
  calc ∏ p ∈ s, (1 / ((p : ℝ) - 1) * (1 - 1 / (p : ℝ))⁻¹ + 1)
      ≤ ∏ p ∈ s, ((1 - 1 / (p : ℝ))⁻¹ * (1 + 2 * ((p : ℝ) ^ 2)⁻¹)) := by
        refine prod_le_prod (fun p hp => ?_) (fun p hp => euler_factor_le (hs p hp).1)
        have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hs p hp).1.two_le
        have : 0 ≤ 1 / ((p : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
        have := one_le_factor (hs p hp).1
        positivity
    _ = (∏ p ∈ s, (1 - 1 / (p : ℝ))⁻¹) * ∏ p ∈ s, (1 + 2 * ((p : ℝ) ^ 2)⁻¹) := prod_mul_distrib
    _ ≤ (∏ p ∈ s, (1 - 1 / (p : ℝ))⁻¹) * Real.exp 4 := by
        refine mul_le_mul_of_nonneg_left ?_ hnn
        calc ∏ p ∈ s, (1 + 2 * ((p : ℝ) ^ 2)⁻¹) ≤ ∏ p ∈ s, Real.exp (2 * ((p : ℝ) ^ 2)⁻¹) :=
              prod_le_prod (fun p _ => by positivity)
                (fun p _ => by linarith [Real.add_one_le_exp (2 * ((p : ℝ) ^ 2)⁻¹)])
          _ = Real.exp (∑ p ∈ s, 2 * ((p : ℝ) ^ 2)⁻¹) := (Real.exp_sum _ _).symm
          _ ≤ Real.exp 4 := by
              apply Real.exp_le_exp.mpr
              rw [← mul_sum]
              have hsub : s ⊆ Ioo 0 (N + 1) := fun p hp => by
                have := hs p hp
                simp only [mem_Ioo]
                exact ⟨this.1.pos, by omega⟩
              have h1 := sum_le_sum_of_subset_of_nonneg hsub
                (f := fun i : ℕ => ((i : ℝ) ^ 2)⁻¹) (fun i _ _ => by positivity)
              have h2 := sum_Ioo_inv_sq_le (α := ℝ) 0 (N + 1)
              norm_num at h2
              linarith
    _ = _ := mul_comm _ _
lemma sum_F_div_le (m N : ℕ) :
    ∑ n ∈ Ioc 0 N, F m n / n ≤
      ∏ p ∈ ((Iic N).filter Nat.Prime).filter (fun p => ¬ p ∣ m),
        (1 / ((p : ℝ) - 1) * (1 - 1 / (p : ℝ))⁻¹ + 1) := by
  classical
  set s := ((Iic N).filter Nat.Prime).filter (fun p => ¬ p ∣ m) with hs
  have hsum : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ => ‖f (p ^ n)‖) := by
    intro p hp
    simpa [Real.norm_eq_abs] using (hasSum_f_pow hp).summable.abs
  obtain ⟨-, hhas⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := f) f_one (fun h => f_mul h) hsum s
  have hsP : ∀ p ∈ s, p.Prime := fun p hp => (mem_filter.mp (mem_filter.mp hp).1).2
  have hfilt : s.filter Nat.Prime = s := filter_true_of_mem hsP
  have hle : ∑ n ∈ Ioc 0 N, F m n / n = ∑ n ∈ (Ioc 0 N).filter (fun n => n.Coprime m), f n := by
    rw [sum_filter]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℝ) ≠ 0 := by
      have : 0 < n := (mem_Ioc.mp hn).1
      exact_mod_cast this.ne'
    rw [F_apply]
    split_ifs
    · unfold R f
      have ht : (Nat.totient n : ℝ) ≠ 0 := by
        have : 0 < n := (mem_Ioc.mp hn).1
        exact_mod_cast (Nat.totient_pos.mpr this).ne'
      field_simp
    · simp
  rw [hle]
  have hmem : ∀ n ∈ (Ioc 0 N).filter (fun n => n.Coprime m), n ∈ Nat.factoredNumbers s := by
    intro n hn
    obtain ⟨hnI, hcop⟩ := mem_filter.mp hn
    obtain ⟨hn1, hn2⟩ := mem_Ioc.mp hnI
    rw [Nat.mem_factoredNumbers_iff_primeFactors_subset]
    refine ⟨hn1.ne', fun p hp => ?_⟩
    obtain ⟨hpp, hpn, -⟩ := Nat.mem_primeFactors.mp hp
    simp only [hs, mem_filter, mem_Iic]
    refine ⟨⟨(Nat.le_of_dvd hn1 hpn).trans hn2, hpp⟩, fun hpm => ?_⟩
    have := Nat.dvd_gcd hpn hpm
    rw [hcop.gcd_eq_one] at this
    exact hpp.not_dvd_one this
  rw [← sum_subtype_of_mem f hmem]
  calc ∑ x ∈ ((Ioc 0 N).filter (fun n => n.Coprime m)).subtype (· ∈ Nat.factoredNumbers s), f x
      ≤ ∑' x : Nat.factoredNumbers s, f x :=
        hhas.summable.sum_le_tsum _ (fun x _ => f_nonneg x)
    _ = ∏ p ∈ s.filter Nat.Prime, ∑' k : ℕ, f (p ^ k) := hhas.tsum_eq
    _ = _ := by
        rw [hfilt]
        exact prod_congr rfl fun p hp => (hasSum_f_pow (hsP p hp)).tsum_eq
end CoprimeSieveAux
open CoprimeSieveAux in
theorem sieve_weighted_coprime : ∃ C : ℝ, 0 < C ∧ ∀ (m g : ℕ) (H : ℝ), 0 < m → 0 < g → 1 ≤ H →
    ∑ h ∈ (Icc 1 ⌊H⌋₊).filter (fun h => Nat.Coprime h m),
        ((Nat.gcd h g : ℝ) / Nat.totient (Nat.gcd h g)) ≤
      C * H * ∏ p ∈ m.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ H), (1 - (1 : ℝ) / p) := by
  obtain ⟨CM, hCM, hMert⟩ := prod_inv_one_sub_inv_prime_le
  set K : ℝ := 2 * (Real.log 4 + 4) + 1 with hK
  have hK0 : 0 < K := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); rw [hK]; linarith
  refine ⟨max 1 (K * Real.exp 4 * CM), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro m g H hm _hg hH
  have hH0 : (0 : ℝ) ≤ H := by linarith
  set N := ⌊H⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by simpa using hH)
  have hNH : (N : ℝ) ≤ H := Nat.floor_le hH0
  set Q := ∏ p ∈ m.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ H), (1 - (1 : ℝ) / p) with hQ
  have hQpos : 0 < Q := prod_pos fun p hp =>
    (prime_factor_bounds (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)).1
  have hLA : ∑ h ∈ (Icc 1 N).filter (fun h => Nat.Coprime h m),
        ((Nat.gcd h g : ℝ) / Nat.totient (Nat.gcd h g)) ≤ ∑ n ∈ Ioc 0 N, F m n := by
    have hIcc : Icc 1 N = Ioc 0 N := by ext; simp; omega
    rw [← hIcc, sum_filter]
    refine sum_le_sum fun h hh => ?_
    rw [F_apply]
    split_ifs
    · exact R_mono (Nat.gcd_dvd_left h g) (by simp at hh; omega)
    · exact le_refl 0
  refine hLA.trans ?_
  rcases Nat.lt_or_ge N 2 with hN2 | hN2
  ·
    have hN1' : N = 1 := by omega
    have hA : ∑ n ∈ Ioc 0 N, F m n ≤ 1 := by
      rw [hN1']
      simp [F_apply, R]
    have hH2 : H < 2 := by
      have : ⌊H⌋₊ < 2 := hN2
      exact (Nat.floor_lt hH0).mp (by simpa using this)
    have hQ1 : Q = 1 := by
      rw [hQ]
      refine prod_eq_one fun p hp => ?_
      exfalso
      obtain ⟨hp1, hp2⟩ := mem_filter.mp hp
      have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp1).two_le
      linarith
    rw [hQ1, mul_one]
    calc ∑ n ∈ Ioc 0 N, F m n ≤ 1 := hA
      _ = 1 * 1 := by norm_num
      _ ≤ max 1 (K * Real.exp 4 * CM) * H := by gcongr; exact le_max_left _ _
  ·
    have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
    set T := (Iic N).filter Nat.Prime with hT
    have hs'eq : m.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ H) = T.filter (fun p => p ∣ m) := by
      ext p
      simp only [hT, mem_filter, Nat.mem_primeFactors, mem_Iic]
      constructor
      · rintro ⟨⟨hp, hpm, -⟩, hpH⟩
        exact ⟨⟨Nat.le_floor hpH, hp⟩, hpm⟩
      · rintro ⟨⟨hpN, hp⟩, hpm⟩
        exact ⟨⟨hp, hpm, hm.ne'⟩, (Nat.le_floor_iff hH0).mp hpN⟩
    have hMN := hMert (N : ℝ) hN2'
    rw [Nat.floor_natCast] at hMN
    have hsplit := prod_filter_mul_prod_filter_not T (fun p => p ∣ m)
      (f := fun p : ℕ => (1 - (1 : ℝ) / p)⁻¹)
    have hQinv : ∏ p ∈ T.filter (fun p => p ∣ m), (1 - (1 : ℝ) / p)⁻¹ = Q⁻¹ := by
      rw [hQ, hs'eq, prod_inv_distrib]
    rw [hQinv] at hsplit
    set Ps := ∏ p ∈ T.filter (fun p => ¬ p ∣ m), (1 - (1 : ℝ) / p)⁻¹ with hPs
    have hPs : Ps ≤ CM * Real.log N * Q := by
      have e : Ps = (Q⁻¹ * Ps) * Q := by field_simp
      rw [e, hsplit]
      exact mul_le_mul_of_nonneg_right hMN hQpos.le
    have hB := sum_F_div_le m N
    have hE := prod_euler_le N (T.filter (fun p => ¬ p ∣ m)) (fun p hp => by
      simp only [hT, mem_filter, mem_Iic] at hp
      exact ⟨hp.1.2, hp.1.1⟩)
    have hB' : ∑ n ∈ Ioc 0 N, F m n / n ≤ Real.exp 4 * (CM * Real.log N * Q) :=
      hB.trans (hE.trans (mul_le_mul_of_nonneg_left hPs (Real.exp_pos 4).le))
    have hAlog := sum_F_logN_le m N
    have hN0 : (0 : ℝ) ≤ N := by positivity
    have hA : (∑ n ∈ Ioc 0 N, F m n) * Real.log N ≤
        ((K * Real.exp 4 * CM) * N * Q) * Real.log N := by
      calc (∑ n ∈ Ioc 0 N, F m n) * Real.log N
          ≤ K * N * ∑ n ∈ Ioc 0 N, F m n / n := hAlog
        _ ≤ K * N * (Real.exp 4 * (CM * Real.log N * Q)) :=
            mul_le_mul_of_nonneg_left hB' (by positivity)
        _ = ((K * Real.exp 4 * CM) * N * Q) * Real.log N := by ring
    have hA' := le_of_mul_le_mul_right hA hlogN
    calc ∑ n ∈ Ioc 0 N, F m n ≤ (K * Real.exp 4 * CM) * N * Q := hA'
      _ ≤ max 1 (K * Real.exp 4 * CM) * H * Q := by
          refine mul_le_mul_of_nonneg_right ?_ hQpos.le
          exact mul_le_mul (le_max_right _ _) hNH hN0 (by positivity)
end DuffinSchaeffer
end Port24_Parts_CoprimeSieve

section Port24_Parts_GraphBasics
open Finset
namespace DuffinSchaeffer
namespace GCDGraph
theorem alt_wsum_nonneg {μ : ℕ → ℝ} (hμ : ∀ n, 0 ≤ μ n) (S : Finset ℕ) : 0 ≤ wsum μ S :=
  Finset.sum_nonneg (fun i _ => hμ i)
theorem alt_esum_nonneg {μ : ℕ → ℝ} (hμ : ∀ n, 0 ≤ μ n) (E : Finset (ℕ × ℕ)) :
    0 ≤ esum μ E :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (hμ _) (hμ _))
theorem alt_wsum_mono {μ : ℕ → ℝ} (hμ : ∀ n, 0 ≤ μ n) {S T : Finset ℕ} (h : S ⊆ T) :
    wsum μ S ≤ wsum μ T :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun i _ _ => hμ i)
theorem alt_esum_le {μ : ℕ → ℝ} (hμ : ∀ n, 0 ≤ μ n) {E : Finset (ℕ × ℕ)} {V W : Finset ℕ}
    (h : E ⊆ V ×ˢ W) : esum μ E ≤ wsum μ V * wsum μ W := by
  have h1 : esum μ E ≤ esum μ (V ×ˢ W) :=
    Finset.sum_le_sum_of_subset_of_nonneg h (fun e _ _ => mul_nonneg (hμ _) (hμ _))
  refine h1.trans (le_of_eq ?_)
  unfold esum wsum
  rw [Finset.sum_product, Finset.sum_mul_sum]
theorem alt_c_pos {p : ℕ} (hp : p.Prime) : 0 < 1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30) := by
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h2 : (1 : ℝ) < (p : ℝ) ^ ((31 : ℝ) / 30) := Real.one_lt_rpow h1 (by norm_num)
  have h3 : 1 / (p : ℝ) ^ ((31 : ℝ) / 30) < 1 := by
    rw [div_lt_one (by linarith)]; exact h2
  linarith
theorem alt_c_le_one (p : ℕ) : 1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30) ≤ 1 := by
  have : 0 ≤ 1 / (p : ℝ) ^ ((31 : ℝ) / 30) := by positivity
  linarith
theorem alt_qf_pos (G : GCDGraph) {p : ℕ} (hp : p.Prime) : 0 < G.qualityFactor p := by
  unfold qualityFactor
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hc := alt_c_pos hp
  have hd : 0 < 1 - (if G.f p = G.g p ∧ 1 ≤ G.f p then 1 / (p : ℝ) else 0) := by
    split_ifs
    · have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact h1
      linarith
    · norm_num
  positivity
theorem alt_prodqf_pos (G : GCDGraph) : 0 < ∏ p ∈ G.P, G.qualityFactor p :=
  Finset.prod_pos (fun p hp => G.alt_qf_pos (G.P_prime p hp))
theorem IsSubgraph.refl (G : GCDGraph) : G.IsSubgraph G := by
  exact ⟨rfl, subset_rfl, subset_rfl, subset_rfl, subset_rfl, fun p _ => ⟨rfl, rfl⟩⟩
theorem IsSubgraph.trans {G₁ G₂ G₃ : GCDGraph} (h₁ : G₁.IsSubgraph G₂) (h₂ : G₂.IsSubgraph G₃) :
    G₁.IsSubgraph G₃ := by
  obtain ⟨a1, b1, c1, d1, e1, f1⟩ := h₁
  obtain ⟨a2, b2, c2, d2, e2, f2⟩ := h₂
  exact ⟨a1.trans a2, b1.trans b2, c1.trans c2, d1.trans d2, e2.trans e1, fun p hp =>
    ⟨(f1 p (e2 hp)).1.trans (f2 p hp).1, (f1 p (e2 hp)).2.trans (f2 p hp).2⟩⟩
theorem R_mono {G' G : GCDGraph} (h : G'.IsSubgraph G) : G'.R ⊆ G.R := by
  intro p hp
  simp only [R, mem_sdiff, mem_biUnion] at hp ⊢
  obtain ⟨⟨e, he, hpe⟩, hnP⟩ := hp
  exact ⟨⟨e, h.2.2.2.1 he, hpe⟩, fun h' => hnP (h.2.2.2.2.1 h')⟩
theorem density_nonneg (G : GCDGraph) : 0 ≤ G.density :=
  div_nonneg (alt_esum_nonneg G.μ_nonneg _)
    (mul_nonneg (alt_wsum_nonneg G.μ_nonneg _) (alt_wsum_nonneg G.μ_nonneg _))
theorem density_le_one (G : GCDGraph) : G.density ≤ 1 :=
  div_le_one_of_le₀ (alt_esum_le G.μ_nonneg G.E_sub)
    (mul_nonneg (alt_wsum_nonneg G.μ_nonneg _) (alt_wsum_nonneg G.μ_nonneg _))
theorem density_pos_iff (G : GCDGraph) : 0 < G.density ↔ G.Nontrivial := by
  constructor
  · intro h
    rcases (alt_esum_nonneg G.μ_nonneg G.E).lt_or_eq with h' | h'
    · exact h'
    · simp [density, ← h'] at h
  · intro h
    exact div_pos h (lt_of_lt_of_le h (alt_esum_le G.μ_nonneg G.E_sub))
theorem wsum_V_pos_of_density_pos (G : GCDGraph) (h : 0 < G.density) : 0 < wsum G.μ G.V := by
  have he : 0 < esum G.μ G.E := (density_pos_iff G).1 h
  have hle := alt_esum_le G.μ_nonneg G.E_sub
  rcases (alt_wsum_nonneg G.μ_nonneg G.V).lt_or_eq with h' | h'
  · exact h'
  · rw [← h'] at hle; simp at hle; linarith
theorem wsum_W_pos_of_density_pos (G : GCDGraph) (h : 0 < G.density) : 0 < wsum G.μ G.W := by
  have he : 0 < esum G.μ G.E := (density_pos_iff G).1 h
  have hle := alt_esum_le G.μ_nonneg G.E_sub
  rcases (alt_wsum_nonneg G.μ_nonneg G.W).lt_or_eq with h' | h'
  · exact h'
  · rw [← h'] at hle; simp at hle; linarith
theorem quality_pos_iff (G : GCDGraph) : 0 < G.quality ↔ 0 < G.density := by
  constructor
  · intro h
    rcases G.density_nonneg.lt_or_eq with h' | h'
    · exact h'
    · exfalso
      unfold quality at h
      rw [← h'] at h
      simp at h
  · intro h
    unfold quality
    have := G.wsum_V_pos_of_density_pos h
    have := G.wsum_W_pos_of_density_pos h
    have := G.alt_prodqf_pos
    positivity
theorem quality_nonneg (G : GCDGraph) : 0 ≤ G.quality := by
  unfold quality
  have := G.density_nonneg
  have := alt_wsum_nonneg G.μ_nonneg G.V
  have := alt_wsum_nonneg G.μ_nonneg G.W
  have := G.alt_prodqf_pos
  positivity
theorem quality_eq (G : GCDGraph) :
    G.quality = esum G.μ G.E ^ 10 / (wsum G.μ G.V ^ 9 * wsum G.μ G.W ^ 9) *
      ∏ p ∈ G.P, G.qualityFactor p := by
  unfold quality density
  rcases eq_or_ne (wsum G.μ G.V) 0 with hS | hS
  · simp [hS]
  rcases eq_or_ne (wsum G.μ G.W) 0 with hT | hT
  · simp [hT]
  rw [div_pow]
  field_simp
theorem restrictPrime_isSubgraph (G : GCDGraph) (p k l : ℕ) (hp : p.Prime) (hpP : p ∉ G.P) :
    (G.restrictPrime p k l hp hpP).IsSubgraph G := by
  refine ⟨rfl, filter_subset _ _, filter_subset _ _, filter_subset _ _, subset_insert _ _,
    fun q hq => ?_⟩
  have hne : q ≠ p := fun h => hpP (h ▸ hq)
  exact ⟨Function.update_of_ne hne _ _, Function.update_of_ne hne _ _⟩
theorem R_restrictPrime_subset (G : GCDGraph) (p k l : ℕ) (hp : p.Prime) (hpP : p ∉ G.P) :
    (G.restrictPrime p k l hp hpP).R ⊆ G.R.erase p := by
  intro q hq
  refine mem_erase.2 ⟨?_, R_mono (G.restrictPrime_isSubgraph p k l hp hpP) hq⟩
  intro h
  rw [h] at hq
  exact (G.restrictPrime p k l hp hpP).not_mem_P_of_mem_R hq (mem_insert_self _ _)
theorem quality_restrictPrime (G : GCDGraph) (p k l : ℕ) (hp : p.Prime) (hpP : p ∉ G.P)
    (hE : 0 < esum G.μ G.E) (hV : 0 < wsum G.μ (vslice G.V p k))
    (hW : 0 < wsum G.μ (vslice G.W p l)) :
    (G.restrictPrime p k l hp hpP).quality =
      G.quality * (esum G.μ (G.restrictPrime p k l hp hpP).E / esum G.μ G.E) ^ 10 *
        (wsum G.μ G.V / wsum G.μ (vslice G.V p k)) ^ 9 *
        (wsum G.μ G.W / wsum G.μ (vslice G.W p l)) ^ 9 *
        ((p : ℝ) ^ ((k - l) + (l - k)) /
          ((1 - (if k = l ∧ 1 ≤ k then 1 / (p : ℝ) else 0)) ^ 2 *
            (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10)) := by
  have hprod : ∏ q ∈ (G.restrictPrime p k l hp hpP).P,
      (G.restrictPrime p k l hp hpP).qualityFactor q =
      ((p : ℝ) ^ ((k - l) + (l - k)) /
          ((1 - (if k = l ∧ 1 ≤ k then 1 / (p : ℝ) else 0)) ^ 2 *
            (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10)) * ∏ q ∈ G.P, G.qualityFactor q := by
    show ∏ q ∈ insert p G.P, _ = _
    rw [prod_insert hpP]
    congr 1
    · simp only [qualityFactor, fgDist, restrictPrime, Function.update_self]
    · apply prod_congr rfl
      intro q hq
      have hne : q ≠ p := fun h => hpP (h ▸ hq)
      simp only [qualityFactor, fgDist, restrictPrime, Function.update_of_ne hne]
  have hS' := hV
  have hT' := hW
  have hS : 0 < wsum G.μ G.V := lt_of_lt_of_le hV (alt_wsum_mono G.μ_nonneg (filter_subset _ _))
  have hT : 0 < wsum G.μ G.W := lt_of_lt_of_le hW (alt_wsum_mono G.μ_nonneg (filter_subset _ _))
  rw [quality_eq, quality_eq G, hprod]
  change esum G.μ (G.restrictPrime p k l hp hpP).E ^ 10 /
    (wsum G.μ (vslice G.V p k) ^ 9 * wsum G.μ (vslice G.W p l) ^ 9) * _ = _
  field_simp
theorem exists_addPrime_zero (G : GCDGraph) (p : ℕ) (hp : p.Prime) (hpP : p ∉ G.P)
    (hpR : p ∉ G.R) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ G'.V = G.V ∧ G'.W = G.W ∧ G'.E = G.E ∧
      G'.P = insert p G.P ∧ G'.f p = 0 ∧ G'.g p = 0 ∧ G'.R ⊆ G.R.erase p ∧
      G.quality ≤ G'.quality ∧ G'.density = G.density := by
  let G' : GCDGraph :=
  { μ := G.μ
    V := G.V
    W := G.W
    E := G.E
    P := insert p G.P
    f := Function.update G.f p 0
    g := Function.update G.g p 0
    μ_nonneg := G.μ_nonneg
    V_pos := G.V_pos
    W_pos := G.W_pos
    E_sub := G.E_sub
    P_prime := by
      intro q hq
      rcases mem_insert.1 hq with rfl | hq
      · exact hp
      · exact G.P_prime q hq
    dvd_V := by
      intro q hq v hv
      rcases mem_insert.1 hq with rfl | hq'
      · simp
      · have hne : q ≠ p := fun h => hpP (h ▸ hq')
        rw [Function.update_of_ne hne]
        exact G.dvd_V q hq' v hv
    dvd_W := by
      intro q hq w hw
      rcases mem_insert.1 hq with rfl | hq'
      · simp
      · have hne : q ≠ p := fun h => hpP (h ▸ hq')
        rw [Function.update_of_ne hne]
        exact G.dvd_W q hq' w hw
    gcd_E := by
      intro q hq e he
      rcases mem_insert.1 hq with rfl | hq'
      · simp only [Function.update_self, min_self]
        apply Finsupp.notMem_support_iff.1
        rw [Nat.support_factorization]
        intro hmem
        exact hpR (mem_sdiff.2 ⟨mem_biUnion.2 ⟨e, he, hmem⟩, hpP⟩)
      · have hne : q ≠ p := fun h => hpP (h ▸ hq')
        rw [Function.update_of_ne hne, Function.update_of_ne hne]
        exact G.gcd_E q hq' e he
    exact_V := by
      intro q hq hfg v hv
      rcases mem_insert.1 hq with rfl | hq'
      · simp at hfg
      · have hne : q ≠ p := fun h => hpP (h ▸ hq')
        rw [Function.update_of_ne hne, Function.update_of_ne hne] at hfg
        rw [Function.update_of_ne hne]
        exact G.exact_V q hq' hfg v hv
    exact_W := by
      intro q hq hfg w hw
      rcases mem_insert.1 hq with rfl | hq'
      · simp at hfg
      · have hne : q ≠ p := fun h => hpP (h ▸ hq')
        rw [Function.update_of_ne hne, Function.update_of_ne hne] at hfg
        rw [Function.update_of_ne hne]
        exact G.exact_W q hq' hfg w hw }
  have hsub : G'.IsSubgraph G := by
    refine ⟨rfl, subset_rfl, subset_rfl, subset_rfl, subset_insert _ _, fun q hq => ?_⟩
    have hne : q ≠ p := fun h => hpP (h ▸ hq)
    exact ⟨Function.update_of_ne hne _ _, Function.update_of_ne hne _ _⟩
  have hqf : G'.qualityFactor p = 1 / (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10 := by
    simp [G', qualityFactor, fgDist]
  have hq : G'.quality = G.quality * G'.qualityFactor p := by
    unfold quality
    rw [show G'.P = insert p G.P from rfl, prod_insert hpP]
    have : ∏ q ∈ G.P, G'.qualityFactor q = ∏ q ∈ G.P, G.qualityFactor q := by
      apply prod_congr rfl
      intro q hq
      have hne : q ≠ p := fun h => hpP (h ▸ hq)
      simp only [G', qualityFactor, fgDist, Function.update_of_ne hne]
    rw [this]
    change G.density ^ 10 * wsum G.μ G.V * wsum G.μ G.W * _ = _
    ring
  have hge : 1 ≤ G'.qualityFactor p := by
    rw [hqf, one_le_div (by have := alt_c_pos hp; positivity)]
    exact pow_le_one₀ (alt_c_pos hp).le (alt_c_le_one p)
  refine ⟨G', hsub, rfl, rfl, rfl, rfl, by simp [G'], by simp [G'], ?_, ?_, rfl⟩
  · intro q hq
    refine mem_erase.2 ⟨?_, R_mono hsub hq⟩
    intro h
    rw [h] at hq
    exact G'.not_mem_P_of_mem_R hq (mem_insert_self _ _)
  · rw [hq]
    exact le_mul_of_one_le_right G.quality_nonneg hge
theorem alt_induce_quality (G : GCDGraph) (V' W' : Finset ℕ) (E' : Finset (ℕ × ℕ))
    (hV : V' ⊆ G.V) (hW : W' ⊆ G.W) (hE : E' ⊆ G.E) (hE' : E' ⊆ V' ×ˢ W') :
    (G.induce V' W' E' hV hW hE hE').quality =
      esum G.μ E' ^ 10 / (wsum G.μ V' ^ 9 * wsum G.μ W' ^ 9) * ∏ p ∈ G.P, G.qualityFactor p :=
  quality_eq _
theorem alt_induce_isSubgraph (G : GCDGraph) (V' W' : Finset ℕ) (E' : Finset (ℕ × ℕ))
    (hV : V' ⊆ G.V) (hW : W' ⊆ G.W) (hE : E' ⊆ G.E) (hE' : E' ⊆ V' ×ˢ W') :
    (G.induce V' W' E' hV hW hE hE').IsSubgraph G :=
  ⟨rfl, hV, hW, hE, subset_rfl, fun _ _ => ⟨rfl, rfl⟩⟩
theorem exists_block_subgraph (G : GCDGraph) (hδ : 0 < G.density) (I J : Finset ℕ)
    (iV jW : ℕ → ℕ) (hI : ∀ v ∈ G.V, iV v ∈ I) (hJ : ∀ w ∈ G.W, jW w ∈ J) :
    ∃ i ∈ I, ∃ j ∈ J, ∃ G' : GCDGraph, G'.IsSubgraph G ∧
      G'.V = G.V.filter (fun v => iV v = i) ∧ G'.W = G.W.filter (fun w => jW w = j) ∧
      G'.E = G.E.filter (fun e => iV e.1 = i ∧ jW e.2 = j) ∧
      G'.P = G.P ∧ G'.f = G.f ∧ G'.g = G.g ∧ 0 < G'.density ∧
      G.density / ((I.card : ℝ) * J.card) ≤ G'.density ∧
      G.quality / ((I.card : ℝ) * J.card) ^ 10 ≤ G'.quality := by
  classical
  have he : 0 < esum G.μ G.E := (density_pos_iff G).1 hδ
  have hS := wsum_V_pos_of_density_pos G hδ
  have hT := wsum_W_pos_of_density_pos G hδ
  have hprod := G.alt_prodqf_pos
  have hVne : G.V.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    simp [wsum, h] at hS
  have hWne : G.W.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    simp [wsum, h] at hT
  obtain ⟨v0, hv0⟩ := hVne
  obtain ⟨w0, hw0⟩ := hWne
  have hIne : I.Nonempty := ⟨iV v0, hI v0 hv0⟩
  have hJne : J.Nonempty := ⟨jW w0, hJ w0 hw0⟩
  set c : ℝ := (I.card : ℝ) * J.card with hc_def
  have hc : 0 < c := by
    have h1 : (0 : ℝ) < I.card := by exact_mod_cast card_pos.2 hIne
    have h2 : (0 : ℝ) < J.card := by exact_mod_cast card_pos.2 hJne
    positivity
  let F : ℕ × ℕ → ℝ := fun ij => esum G.μ (G.E.filter (fun e => iV e.1 = ij.1 ∧ jW e.2 = ij.2))
  have hsum : ∑ ij ∈ I ×ˢ J, F ij = esum G.μ G.E := by
    have hmap : ∀ e ∈ G.E, (fun e : ℕ × ℕ => (iV e.1, jW e.2)) e ∈ I ×ˢ J := by
      intro e he'
      have := mem_product.1 (G.E_sub he')
      exact mem_product.2 ⟨hI _ this.1, hJ _ this.2⟩
    have := Finset.sum_fiberwise_of_maps_to hmap (fun e => G.μ e.1 * G.μ e.2)
    unfold esum at this ⊢
    rw [← this]
    apply sum_congr rfl
    intro ij _
    unfold F esum
    apply sum_congr _ (fun _ _ => rfl)
    apply filter_congr
    intro e _
    simp [Prod.ext_iff]
  obtain ⟨ij, hij, hle⟩ := Finset.exists_le_of_sum_le (hIne.product hJne)
    (show ∑ _ij ∈ I ×ˢ J, esum G.μ G.E / c ≤ ∑ ij ∈ I ×ˢ J, F ij by
      rw [hsum, sum_const, card_product, nsmul_eq_mul]
      push_cast
      rw [← hc_def]
      field_simp
      rfl)
  obtain ⟨hi, hj⟩ := mem_product.1 hij
  set E' := G.E.filter (fun e => iV e.1 = ij.1 ∧ jW e.2 = ij.2) with hE'_def
  set V' := G.V.filter (fun v => iV v = ij.1) with hV'_def
  set W' := G.W.filter (fun w => jW w = ij.2) with hW'_def
  have hE'sub : E' ⊆ V' ×ˢ W' := by
    intro e he'
    obtain ⟨he1, h1, h2⟩ := mem_filter.1 he'
    have := mem_product.1 (G.E_sub he1)
    exact mem_product.2 ⟨mem_filter.2 ⟨this.1, h1⟩, mem_filter.2 ⟨this.2, h2⟩⟩
  have hEij : esum G.μ G.E / c ≤ esum G.μ E' := hle
  have hEpos : 0 < esum G.μ E' := lt_of_lt_of_le (div_pos he hc) hEij
  have hEle : esum G.μ E' ≤ wsum G.μ V' * wsum G.μ W' := alt_esum_le G.μ_nonneg hE'sub
  have hVle : wsum G.μ V' ≤ wsum G.μ G.V := alt_wsum_mono G.μ_nonneg (filter_subset _ _)
  have hWle : wsum G.μ W' ≤ wsum G.μ G.W := alt_wsum_mono G.μ_nonneg (filter_subset _ _)
  have hV0 := alt_wsum_nonneg G.μ_nonneg V'
  have hW0 := alt_wsum_nonneg G.μ_nonneg W'
  have hVW : 0 < wsum G.μ V' * wsum G.μ W' := lt_of_lt_of_le hEpos hEle
  have hVp : 0 < wsum G.μ V' := by
    rcases hV0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hVW; simp at hVW
  have hWp : 0 < wsum G.μ W' := by
    rcases hW0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hVW; simp at hVW
  refine ⟨ij.1, hi, ij.2, hj, G.induce V' W' E' (filter_subset _ _) (filter_subset _ _)
    (filter_subset _ _) hE'sub, alt_induce_isSubgraph _ _ _ _ _ _ _ _, rfl, rfl, rfl, rfl, rfl,
    rfl, (density_pos_iff _).2 hEpos, ?_, ?_⟩
  · show esum G.μ G.E / (wsum G.μ G.V * wsum G.μ G.W) / c ≤
      esum G.μ E' / (wsum G.μ V' * wsum G.μ W')
    calc esum G.μ G.E / (wsum G.μ G.V * wsum G.μ G.W) / c
        = (esum G.μ G.E / c) / (wsum G.μ G.V * wsum G.μ G.W) := by ring
      _ ≤ esum G.μ E' / (wsum G.μ G.V * wsum G.μ G.W) :=
          div_le_div_of_nonneg_right hEij (by positivity)
      _ ≤ esum G.μ E' / (wsum G.μ V' * wsum G.μ W') :=
          div_le_div_of_nonneg_left hEpos.le hVW (mul_le_mul hVle hWle hW0 hS.le)
  · rw [alt_induce_quality, quality_eq]
    calc (esum G.μ G.E ^ 10 / (wsum G.μ G.V ^ 9 * wsum G.μ G.W ^ 9) *
          ∏ p ∈ G.P, G.qualityFactor p) / c ^ 10
        = (esum G.μ G.E / c) ^ 10 / (wsum G.μ G.V ^ 9 * wsum G.μ G.W ^ 9) *
          ∏ p ∈ G.P, G.qualityFactor p := by rw [div_pow]; ring
      _ ≤ esum G.μ E' ^ 10 / (wsum G.μ G.V ^ 9 * wsum G.μ G.W ^ 9) *
          ∏ p ∈ G.P, G.qualityFactor p := by
          gcongr
      _ ≤ esum G.μ E' ^ 10 / (wsum G.μ V' ^ 9 * wsum G.μ W' ^ 9) *
          ∏ p ∈ G.P, G.qualityFactor p := by
          gcongr
theorem alt_real_remove (X Y e a n : ℝ) (hY : 0 < Y) (ha : 0 ≤ a) (haX : a ≤ X) (he : 0 < e)
    (heXY : e ≤ X * Y) (hlt : n < 9 * (e / (X * Y)) / 10 * Y) (he' : e - a * n ≤ (X - a) * Y) :
    e / (X * Y) ≤ (e - a * n) / ((X - a) * Y) ∧
    (e / (X * Y)) ^ 10 * X * Y ≤ ((e - a * n) / ((X - a) * Y)) ^ 10 * (X - a) * Y := by
  have hXY : 0 < X * Y := lt_of_lt_of_le he heXY
  set δ := e / (X * Y) with hδdef
  have hδ : 0 ≤ δ := div_nonneg he.le hXY.le
  have hX : 0 < X := (pos_iff_pos_of_mul_pos hXY).2 hY
  have heq : e = δ * X * Y := by rw [hδdef]; field_simp
  have h1 : a * n ≤ a * (9 * δ / 10 * Y) := mul_le_mul_of_nonneg_left hlt.le ha
  have h2 : a * (9 * δ / 10 * Y) ≤ X * (9 * δ / 10 * Y) :=
    mul_le_mul_of_nonneg_right haX (by positivity)
  have hpos' : 0 < e - a * n := by nlinarith
  have hXa : 0 < X - a := by
    by_contra h
    push Not at h
    have : (X - a) * Y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hY.le
    linarith
  set x := a / (10 * (X - a)) with hx
  have hx0 : 0 ≤ x := by positivity
  have hkey : δ * (1 + x) ≤ (e - a * n) / ((X - a) * Y) := by
    rw [le_div_iff₀ (by positivity)]
    have : δ * (1 + x) * ((X - a) * Y) = δ * X * Y - 9 * δ / 10 * Y * a := by
      rw [hx]; field_simp; ring
    rw [this]; nlinarith
  have hδle : δ ≤ δ * (1 + x) := by nlinarith
  refine ⟨hδle.trans hkey, ?_⟩
  have hb : 1 + ((10 : ℕ) : ℝ) * x ≤ (1 + x) ^ 10 := one_add_mul_le_pow (by linarith) 10
  have h3 : (δ * (1 + x)) ^ 10 ≤ ((e - a * n) / ((X - a) * Y)) ^ 10 :=
    pow_le_pow_left₀ (by positivity) hkey 10
  have h4 : (1 + ((10 : ℕ) : ℝ) * x) * (X - a) = X := by
    rw [hx]; push_cast; field_simp; ring
  calc δ ^ 10 * X * Y = δ ^ 10 * ((1 + ((10 : ℕ) : ℝ) * x) * (X - a)) * Y := by rw [h4]
    _ ≤ δ ^ 10 * ((1 + x) ^ 10 * (X - a)) * Y := by gcongr
    _ = (δ * (1 + x)) ^ 10 * (X - a) * Y := by ring
    _ ≤ _ := by gcongr
theorem alt_esum_split_fst (G : GCDGraph) (v : ℕ) :
    esum G.μ G.E = esum G.μ (G.E.filter (fun e => e.1 ≠ v)) + G.μ v * wsum G.μ (G.nbhdV v) := by
  unfold esum
  rw [← sum_filter_add_sum_filter_not G.E (fun e => e.1 ≠ v)]
  congr 1
  unfold wsum nbhdV
  rw [mul_sum]
  refine Finset.sum_nbij' (fun e => e.2) (fun w => (v, w)) ?_ ?_ ?_ ?_ ?_
  · intro e he
    simp only [mem_filter, not_not] at he ⊢
    obtain ⟨he, rfl⟩ := he
    exact ⟨(mem_product.1 (G.E_sub he)).2, he⟩
  · intro w hw
    simp only [mem_filter, not_not] at hw ⊢
    exact ⟨hw.2, trivial⟩
  · intro e he
    simp only [mem_filter, not_not] at he
    obtain ⟨_, rfl⟩ := he
    rfl
  · intro w _
    rfl
  · intro e he
    simp only [mem_filter, not_not] at he
    obtain ⟨_, rfl⟩ := he
    rfl
theorem alt_esum_split_snd (G : GCDGraph) (w : ℕ) :
    esum G.μ G.E = esum G.μ (G.E.filter (fun e => e.2 ≠ w)) + G.μ w * wsum G.μ (G.nbhdW w) := by
  unfold esum
  rw [← sum_filter_add_sum_filter_not G.E (fun e => e.2 ≠ w)]
  congr 1
  unfold wsum nbhdW
  rw [mul_sum]
  refine Finset.sum_nbij' (fun e => e.1) (fun v => (v, w)) ?_ ?_ ?_ ?_ ?_
  · intro e he
    simp only [mem_filter, not_not] at he ⊢
    obtain ⟨he, rfl⟩ := he
    exact ⟨(mem_product.1 (G.E_sub he)).1, he⟩
  · intro v hv
    simp only [mem_filter, not_not] at hv ⊢
    exact ⟨hv.2, trivial⟩
  · intro e he
    simp only [mem_filter, not_not] at he
    obtain ⟨_, rfl⟩ := he
    rfl
  · intro v _
    rfl
  · intro e he
    simp only [mem_filter, not_not] at he
    obtain ⟨_, rfl⟩ := he
    ring
theorem alt_step10 (G : GCDGraph) (hδ : 0 < G.density) (hH : ¬ G.HighDegree) :
    ∃ G1 : GCDGraph, G1.IsSubgraph G ∧ G1.P = G.P ∧ G1.f = G.f ∧ G1.g = G.g ∧
      G1.V.card + G1.W.card < G.V.card + G.W.card ∧ G.density ≤ G1.density ∧
      G.quality ≤ G1.quality := by
  have he : 0 < esum G.μ G.E := (density_pos_iff G).1 hδ
  have heST := alt_esum_le G.μ_nonneg G.E_sub
  have hS := wsum_V_pos_of_density_pos G hδ
  have hT := wsum_W_pos_of_density_pos G hδ
  have hprod := G.alt_prodqf_pos
  rw [HighDegree, not_and_or] at hH
  rcases hH with hH | hH
  · push Not at hH
    obtain ⟨v, hv, hlt⟩ := hH
    have hE' : G.E.filter (fun e => e.1 ≠ v) ⊆ (G.V.erase v) ×ˢ G.W := by
      intro e he
      rw [mem_filter] at he
      have := mem_product.1 (G.E_sub he.1)
      exact mem_product.2 ⟨mem_erase.2 ⟨he.2, this.1⟩, this.2⟩
    have hsplit := G.alt_esum_split_fst v
    have hVe : wsum G.μ (G.V.erase v) = wsum G.μ G.V - G.μ v := by
      unfold wsum; rw [sum_erase_eq_sub hv]
    have hle' := alt_esum_le G.μ_nonneg hE'
    have hEf : esum G.μ (G.E.filter (fun e => e.1 ≠ v)) =
        esum G.μ G.E - G.μ v * wsum G.μ (G.nbhdV v) := by linarith
    obtain ⟨h1, h2⟩ := alt_real_remove (wsum G.μ G.V) (wsum G.μ G.W) (esum G.μ G.E) (G.μ v)
      (wsum G.μ (G.nbhdV v)) hT (G.μ_nonneg v)
      (single_le_sum (fun i _ => G.μ_nonneg i) hv) he heST hlt
      (by rw [← hEf, ← hVe]; exact hle')
    refine ⟨G.induce (G.V.erase v) G.W _ (erase_subset _ _) subset_rfl (filter_subset _ _) hE',
      alt_induce_isSubgraph _ _ _ _ _ _ _ _, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · show (G.V.erase v).card + G.W.card < _
      rw [card_erase_of_mem hv]
      have := card_pos.2 ⟨v, hv⟩
      omega
    · show G.density ≤ esum G.μ (G.E.filter (fun e => e.1 ≠ v)) /
        (wsum G.μ (G.V.erase v) * wsum G.μ G.W)
      rw [hEf, hVe]; exact h1
    · show G.density ^ 10 * wsum G.μ G.V * wsum G.μ G.W * ∏ p ∈ G.P, G.qualityFactor p ≤
        (esum G.μ (G.E.filter (fun e => e.1 ≠ v)) / (wsum G.μ (G.V.erase v) * wsum G.μ G.W)) ^ 10 *
          wsum G.μ (G.V.erase v) * wsum G.μ G.W * ∏ p ∈ G.P, G.qualityFactor p
      rw [hEf, hVe]
      exact mul_le_mul_of_nonneg_right h2 hprod.le
  · push Not at hH
    obtain ⟨w, hw, hlt⟩ := hH
    have hE' : G.E.filter (fun e => e.2 ≠ w) ⊆ G.V ×ˢ (G.W.erase w) := by
      intro e he
      rw [mem_filter] at he
      have := mem_product.1 (G.E_sub he.1)
      exact mem_product.2 ⟨this.1, mem_erase.2 ⟨he.2, this.2⟩⟩
    have hsplit := G.alt_esum_split_snd w
    have hWe : wsum G.μ (G.W.erase w) = wsum G.μ G.W - G.μ w := by
      unfold wsum; rw [sum_erase_eq_sub hw]
    have hle' := alt_esum_le G.μ_nonneg hE'
    have hEf : esum G.μ (G.E.filter (fun e => e.2 ≠ w)) =
        esum G.μ G.E - G.μ w * wsum G.μ (G.nbhdW w) := by linarith
    have hden : G.density = esum G.μ G.E / (wsum G.μ G.W * wsum G.μ G.V) := by
      rw [density, mul_comm]
    rw [hden] at hlt
    obtain ⟨h1, h2⟩ := alt_real_remove (wsum G.μ G.W) (wsum G.μ G.V) (esum G.μ G.E) (G.μ w)
      (wsum G.μ (G.nbhdW w)) hS (G.μ_nonneg w)
      (single_le_sum (fun i _ => G.μ_nonneg i) hw) he (by rw [mul_comm]; exact heST) hlt
      (by rw [← hEf, ← hWe, mul_comm]; exact hle')
    refine ⟨G.induce G.V (G.W.erase w) _ subset_rfl (erase_subset _ _) (filter_subset _ _) hE',
      alt_induce_isSubgraph _ _ _ _ _ _ _ _, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · show G.V.card + (G.W.erase w).card < _
      rw [card_erase_of_mem hw]
      have := card_pos.2 ⟨w, hw⟩
      omega
    · show G.density ≤ esum G.μ (G.E.filter (fun e => e.2 ≠ w)) /
        (wsum G.μ G.V * wsum G.μ (G.W.erase w))
      rw [hEf, hWe, hden, mul_comm (wsum G.μ G.V)]; exact h1
    · show G.density ^ 10 * wsum G.μ G.V * wsum G.μ G.W * ∏ p ∈ G.P, G.qualityFactor p ≤
        (esum G.μ (G.E.filter (fun e => e.2 ≠ w)) / (wsum G.μ G.V * wsum G.μ (G.W.erase w))) ^ 10 *
          wsum G.μ G.V * wsum G.μ (G.W.erase w) * ∏ p ∈ G.P, G.qualityFactor p
      rw [hEf, hWe, hden, mul_comm (wsum G.μ G.V) (wsum G.μ G.W - G.μ w)]
      have h2' : (esum G.μ G.E / (wsum G.μ G.W * wsum G.μ G.V)) ^ 10 * wsum G.μ G.V *
          wsum G.μ G.W ≤ ((esum G.μ G.E - G.μ w * wsum G.μ (G.nbhdW w)) /
            ((wsum G.μ G.W - G.μ w) * wsum G.μ G.V)) ^ 10 * wsum G.μ G.V *
              (wsum G.μ G.W - G.μ w) := by
        linarith
      exact mul_le_mul_of_nonneg_right h2' hprod.le
theorem exists_highDegree_subgraph (G : GCDGraph) (hδ : 0 < G.density) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ G'.P = G.P ∧ G'.f = G.f ∧ G'.g = G.g ∧
      0 < G'.density ∧ G.density ≤ G'.density ∧ G.quality ≤ G'.quality ∧ G'.HighDegree := by
  suffices H : ∀ n, ∀ G : GCDGraph, G.V.card + G.W.card = n → 0 < G.density →
      ∃ G' : GCDGraph, G'.IsSubgraph G ∧ G'.P = G.P ∧ G'.f = G.f ∧ G'.g = G.g ∧
        0 < G'.density ∧ G.density ≤ G'.density ∧ G.quality ≤ G'.quality ∧ G'.HighDegree from
    H _ G rfl hδ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G hn hδ
  by_cases hH : G.HighDegree
  · exact ⟨G, IsSubgraph.refl G, rfl, rfl, rfl, hδ, le_rfl, le_rfl, hH⟩
  obtain ⟨G1, hsub, hP, hf, hg, hlt, hδ1, hq1⟩ := alt_step10 G hδ hH
  obtain ⟨G', h1, h2, h3, h4, h5, h6, h7, h8⟩ := ih _ (hn ▸ hlt) G1 rfl (hδ.trans_le hδ1)
  exact ⟨G', h1.trans hsub, h2.trans hP, h3.trans hf, h4.trans hg, h5, hδ1.trans h6,
    hq1.trans h7, h8⟩
theorem alt_real_sparse (S T e e1 A B η : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hAS : A ≤ η * S) (hBT : B ≤ η * T) (he : 0 ≤ e) (hη : 0 < η)
    (he1 : η ^ ((9 : ℝ) / 5) * e < e1) :
    e ^ 10 / (S ^ 9 * T ^ 9) ≤ e1 ^ 10 / (A ^ 9 * B ^ 9) := by
  have hr : (η ^ ((9 : ℝ) / 5)) ^ 10 = η ^ 18 := by
    rw [← Real.rpow_natCast (η ^ ((9 : ℝ) / 5)) 10, ← Real.rpow_mul hη.le,
      show (9 : ℝ) / 5 * ((10 : ℕ) : ℝ) = ((18 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hηr : 0 < η ^ ((9 : ℝ) / 5) := Real.rpow_pos_of_pos hη _
  rcases eq_or_ne (S ^ 9 * T ^ 9) 0 with h0 | h0
  · rw [h0, div_zero]; positivity
  have hST : 0 ≤ S ^ 9 * T ^ 9 := by
    have h1 : 0 ≤ A ^ 9 := by positivity
    have h2 : A ^ 9 ≤ (η * S) ^ 9 := pow_le_pow_left₀ hA.le hAS 9
    have h3 : 0 ≤ B ^ 9 := by positivity
    have h4 : B ^ 9 ≤ (η * T) ^ 9 := pow_le_pow_left₀ hB.le hBT 9
    have h5 : 0 ≤ (η * S) ^ 9 * (η * T) ^ 9 := by
      have := mul_le_mul h2 h4 h3 (h1.trans h2)
      have : 0 ≤ A ^ 9 * B ^ 9 := by positivity
      linarith
    have : (η * S) ^ 9 * (η * T) ^ 9 = η ^ 18 * (S ^ 9 * T ^ 9) := by ring
    rw [this] at h5
    exact nonneg_of_mul_nonneg_right (by linarith) (by positivity : (0:ℝ) < η ^ 18)
  have hSTp : 0 < S ^ 9 * T ^ 9 := lt_of_le_of_ne hST (Ne.symm h0)
  rw [div_le_div_iff₀ hSTp (by positivity)]
  have h2 : A ^ 9 ≤ (η * S) ^ 9 := pow_le_pow_left₀ hA.le hAS 9
  have h4 : B ^ 9 ≤ (η * T) ^ 9 := pow_le_pow_left₀ hB.le hBT 9
  calc e ^ 10 * (A ^ 9 * B ^ 9) ≤ e ^ 10 * ((η * S) ^ 9 * (η * T) ^ 9) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul h2 h4 (by positivity) ((by positivity : (0:ℝ) ≤ A ^ 9).trans h2)
    _ = (η ^ ((9 : ℝ) / 5) * e) ^ 10 * (S ^ 9 * T ^ 9) := by
        rw [show (η ^ ((9 : ℝ) / 5) * e) ^ 10 = η ^ 18 * e ^ 10 by rw [mul_pow, hr]]; ring
    _ ≤ e1 ^ 10 * (S ^ 9 * T ^ 9) := by
        apply mul_le_mul_of_nonneg_right _ hSTp.le
        exact pow_le_pow_left₀ (by positivity) he1.le 10
theorem alt_step115 (G : GCDGraph) (hδ : 0 < G.density) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (hA : ¬ ∀ A ⊆ G.V, ∀ B ⊆ G.W, wsum G.μ A ≤ η * wsum G.μ G.V → wsum G.μ B ≤ η * wsum G.μ G.W →
        esum G.μ (G.E.filter (fun e => e.1 ∈ A ∧ e.2 ∈ B)) ≤ η ^ ((9 : ℝ) / 5) * esum G.μ G.E) :
    ∃ G1 : GCDGraph, G1.IsSubgraph G ∧ G1.P = G.P ∧ G1.f = G.f ∧ G1.g = G.g ∧
      G1.V.card + G1.W.card < G.V.card + G.W.card ∧ 0 < G1.density ∧
      G.quality ≤ G1.quality := by
  have he : 0 < esum G.μ G.E := (density_pos_iff G).1 hδ
  have hS := wsum_V_pos_of_density_pos G hδ
  have hT := wsum_W_pos_of_density_pos G hδ
  have hprod := G.alt_prodqf_pos
  push Not at hA
  obtain ⟨A, hAV, B, hBW, hAS, hBT, hlt⟩ := hA
  set E1 := G.E.filter (fun e => e.1 ∈ A ∧ e.2 ∈ B) with hE1
  have hE1sub : E1 ⊆ A ×ˢ B := by
    intro e he'
    obtain ⟨_, h1, h2⟩ := mem_filter.1 he'
    exact mem_product.2 ⟨h1, h2⟩
  have hηr : 0 < η ^ ((9 : ℝ) / 5) := Real.rpow_pos_of_pos hη0 _
  have he1 : 0 < esum G.μ E1 := lt_of_le_of_lt (by positivity) hlt
  have hle := alt_esum_le G.μ_nonneg hE1sub
  have hA0 := alt_wsum_nonneg G.μ_nonneg A
  have hB0 := alt_wsum_nonneg G.μ_nonneg B
  have hAB : 0 < wsum G.μ A * wsum G.μ B := lt_of_lt_of_le he1 hle
  have hAp : 0 < wsum G.μ A := by
    rcases hA0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hAB; simp at hAB
  have hBp : 0 < wsum G.μ B := by
    rcases hB0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hAB; simp at hAB
  have hAne : A ≠ G.V := by
    rintro rfl
    nlinarith
  have hBne : B ≠ G.W := by
    rintro rfl
    nlinarith
  have hAc : A.card < G.V.card := card_lt_card (hAV.ssubset_of_ne hAne)
  have hBc : B.card < G.W.card := card_lt_card (hBW.ssubset_of_ne hBne)
  refine ⟨G.induce A B E1 hAV hBW (filter_subset _ _) hE1sub,
    alt_induce_isSubgraph _ _ _ _ _ _ _ _, rfl, rfl, rfl, by show A.card + B.card < _; omega,
    (density_pos_iff _).2 he1, ?_⟩
  rw [alt_induce_quality, quality_eq]
  exact mul_le_mul_of_nonneg_right (alt_real_sparse _ _ _ _ _ _ η hAp hBp hAS hBT he.le hη0 hlt)
    hprod.le
theorem exists_sparse_small_sets_subgraph (G : GCDGraph) (hδ : 0 < G.density) (η : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ G'.P = G.P ∧ G'.f = G.f ∧ G'.g = G.g ∧
      0 < G'.density ∧ G.quality ≤ G'.quality ∧
      ∀ A ⊆ G'.V, ∀ B ⊆ G'.W, wsum G.μ A ≤ η * wsum G.μ G'.V → wsum G.μ B ≤ η * wsum G.μ G'.W →
        esum G.μ (G'.E.filter (fun e => e.1 ∈ A ∧ e.2 ∈ B)) ≤ η ^ ((9 : ℝ) / 5) * esum G.μ G'.E := by
  suffices H : ∀ n, ∀ G : GCDGraph, G.V.card + G.W.card = n → 0 < G.density →
      ∃ G' : GCDGraph, G'.IsSubgraph G ∧ G'.P = G.P ∧ G'.f = G.f ∧ G'.g = G.g ∧
        0 < G'.density ∧ G.quality ≤ G'.quality ∧
        ∀ A ⊆ G'.V, ∀ B ⊆ G'.W, wsum G.μ A ≤ η * wsum G.μ G'.V →
          wsum G.μ B ≤ η * wsum G.μ G'.W →
          esum G.μ (G'.E.filter (fun e => e.1 ∈ A ∧ e.2 ∈ B)) ≤
            η ^ ((9 : ℝ) / 5) * esum G.μ G'.E from
    H _ G rfl hδ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G hn hδ
  by_cases hA : ∀ A ⊆ G.V, ∀ B ⊆ G.W, wsum G.μ A ≤ η * wsum G.μ G.V →
      wsum G.μ B ≤ η * wsum G.μ G.W →
      esum G.μ (G.E.filter (fun e => e.1 ∈ A ∧ e.2 ∈ B)) ≤ η ^ ((9 : ℝ) / 5) * esum G.μ G.E
  · exact ⟨G, IsSubgraph.refl G, rfl, rfl, rfl, hδ, le_rfl, hA⟩
  obtain ⟨G1, hsub, hP, hf, hg, hlt, hδ1, hq1⟩ := alt_step115 G hδ η hη0 hη1 hA
  obtain ⟨G', h1, h2, h3, h4, h5, h7, h8⟩ := ih _ (hn ▸ hlt) G1 rfl hδ1
  have hμ : G1.μ = G.μ := hsub.1
  rw [hμ] at h8
  exact ⟨G', h1.trans hsub, h2.trans hP, h3.trans hf, h4.trans hg, h5, hq1.trans h7, h8⟩
end GCDGraph
end DuffinSchaeffer
end Port24_Parts_GraphBasics

section Port24_Parts_Unbalanced
open Finset
namespace DuffinSchaeffer
namespace GCDGraph
namespace Unbalanced
lemma sum_pow_le_tsum {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (T : Finset ℕ) :
    ∑ i ∈ T, y ^ i ≤ (1 - y)⁻¹ := by
  rw [← tsum_geometric_of_lt_one hy0 hy1]
  exact (summable_geometric_of_lt_one hy0 hy1).sum_le_tsum T (fun i _ => pow_nonneg hy0 i)
lemma sum_pow_dist_le {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (S : Finset ℕ) (k : ℕ) :
    ∑ l ∈ S, y ^ ((k - l) + (l - k)) ≤ 2 * (1 - y)⁻¹ := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun l => k ≤ l)]
  have h1 : ∑ l ∈ S.filter (fun l => k ≤ l), y ^ ((k - l) + (l - k)) ≤ (1 - y)⁻¹ := by
    have : ∑ l ∈ S.filter (fun l => k ≤ l), y ^ ((k - l) + (l - k)) =
        ∑ i ∈ (S.filter (fun l => k ≤ l)).image (fun l => l - k), y ^ i := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro l hl
        have : k ≤ l := (Finset.mem_filter.1 hl).2
        rw [Nat.sub_eq_zero_of_le this, zero_add]
      · intro a ha b hb hab
        have ha' := (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2
        have hb' := (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2
        simp only at hab
        omega
    rw [this]
    exact sum_pow_le_tsum hy0 hy1 _
  have h2 : ∑ l ∈ S.filter (fun l => ¬ k ≤ l), y ^ ((k - l) + (l - k)) ≤ (1 - y)⁻¹ := by
    have : ∑ l ∈ S.filter (fun l => ¬ k ≤ l), y ^ ((k - l) + (l - k)) =
        ∑ i ∈ (S.filter (fun l => ¬ k ≤ l)).image (fun l => k - l), y ^ i := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro l hl
        have : ¬ k ≤ l := (Finset.mem_filter.1 hl).2
        rw [Nat.sub_eq_zero_of_le (show l ≤ k by omega), add_zero]
      · intro a ha b hb hab
        have ha' := (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2
        have hb' := (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2
        simp only at hab
        omega
    rw [this]
    exact sum_pow_le_tsum hy0 hy1 _
  linarith
lemma wsum_pos_of_esum_pos {μ : ℕ → ℝ} (hμ : ∀ n, 0 ≤ μ n) {V W : Finset ℕ}
    {E : Finset (ℕ × ℕ)} (hE : E ⊆ V ×ˢ W) (h : 0 < esum μ E) :
    0 < wsum μ V ∧ 0 < wsum μ W := by
  have hV0 : 0 ≤ wsum μ V := Finset.sum_nonneg (fun v _ => hμ v)
  have hW0 : 0 ≤ wsum μ W := Finset.sum_nonneg (fun v _ => hμ v)
  refine ⟨lt_of_le_of_ne hV0 ?_, lt_of_le_of_ne hW0 ?_⟩
  · intro h0
    unfold wsum at h0
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hμ v)).1 h0.symm
    have : esum μ E = 0 := Finset.sum_eq_zero (fun e he => by
      rw [hz e.1 (Finset.mem_product.1 (hE he)).1, zero_mul])
    linarith
  · intro h0
    unfold wsum at h0
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hμ v)).1 h0.symm
    have : esum μ E = 0 := Finset.sum_eq_zero (fun e he => by
      rw [hz e.2 (Finset.mem_product.1 (hE he)).2, mul_zero])
    linarith
lemma wsum_slice_add_le {μ : ℕ → ℝ} (hμ : ∀ n, 0 ≤ μ n) (W : Finset ℕ) (p k l : ℕ)
    (hkl : k ≠ l) : wsum μ (vslice W p k) + wsum μ (vslice W p l) ≤ wsum μ W := by
  unfold wsum vslice
  rw [← Finset.sum_union]
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro v hv
      rcases Finset.mem_union.1 hv with h | h <;> exact (Finset.mem_filter.1 h).1
    · intro i _ _
      exact hμ i
  · rw [Finset.disjoint_left]
    intro v h1 h2
    exact hkl ((Finset.mem_filter.1 h1).2.symm.trans (Finset.mem_filter.1 h2).2)
lemma small_other_slice {μ : ℕ → ℝ} (hμ : ∀ n, 0 ≤ μ n) (W : Finset ℕ) (p k l : ℕ)
    (hp : 0 < (p : ℝ)) (hkl : k ≠ l)
    (hW : (1 - K40 / p) * wsum μ W ≤ wsum μ (vslice W p k)) :
    (p : ℝ) * wsum μ (vslice W p l) ≤ K40 * wsum μ W := by
  have hsum := wsum_slice_add_le hμ W p k l hkl
  have h1 := mul_le_mul_of_nonneg_left hW hp.le
  have h2 := mul_le_mul_of_nonneg_left hsum hp.le
  have h3 : (p : ℝ) * ((1 - K40 / p) * wsum μ W) = p * wsum μ W - K40 * wsum μ W := by
    field_simp
  linarith
lemma log_ten_ge : Real.log 2 ≤ Real.log 10 :=
  Real.log_le_log (by norm_num) (by norm_num)
lemma core_ineq (p : ℝ) (hp : 2 ≤ p) (r d : ℕ) (hr : 1 ≤ r) (hd : r + 1 ≤ d)
    (hpr : T0 < p ^ r) (X M den : ℝ)
    (hX : 1 / 100 * ((2 : ℝ) ^ (-(1 : ℝ) / 20)) ^ d / (4 * p ^ ((31 : ℝ) / 30)) < X)
    (hM : p / K40 ≤ M) (hden0 : 0 < den) (hden1 : den ≤ 1) :
    2 < X ^ 10 * M ^ 9 * (p ^ d / den) ∧ 2 < X ^ 11 * M ^ 10 * (p ^ d / den) := by
  have hp0 : 0 < p := by linarith
  have hK : (0 : ℝ) < K40 := by unfold K40; positivity
  have hy : (0 : ℝ) < (2 : ℝ) ^ (-(1 : ℝ) / 20) := by positivity
  have hP : (0 : ℝ) < p ^ ((31 : ℝ) / 30) := by positivity
  have hc : 0 < 1 / 100 * ((2 : ℝ) ^ (-(1 : ℝ) / 20)) ^ d / (4 * p ^ ((31 : ℝ) / 30)) := by
    positivity
  have hX0 : 0 < X := lt_trans hc hX
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hM
  set L := Real.log p with hL
  set l2 := Real.log 2 with hl2
  set l10 := Real.log 10 with hl10
  have hl2pos : 0 < l2 := Real.log_pos (by norm_num)
  have hl210 : l2 ≤ l10 := log_ten_ge
  have hLl2 : l2 ≤ L := Real.log_le_log (by norm_num) hp
  have hlogc : Real.log (1 / 100 * ((2 : ℝ) ^ (-(1 : ℝ) / 20)) ^ d / (4 * p ^ ((31 : ℝ) / 30)))
      = -(2 * l10) + d * (-(1 : ℝ) / 20 * l2) - (2 * l2 + (31 : ℝ) / 30 * L) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, Real.log_rpow (by norm_num), Real.log_mul (by norm_num) (by positivity),
      Real.log_rpow hp0]
    have e1 : Real.log (1 / 100 : ℝ) = -(2 * l10) := by
      rw [one_div, Real.log_inv, show (100 : ℝ) = 10 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    have e2 : Real.log (4 : ℝ) = 2 * l2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    rw [e1, e2]
  have hlogX : -(2 * l10) + d * (-(1 : ℝ) / 20 * l2) - (2 * l2 + (31 : ℝ) / 30 * L) <
      Real.log X := by
    rw [← hlogc]; exact Real.log_lt_log hc hX
  have hlogM : L - 40 * l10 ≤ Real.log M := by
    have := Real.log_le_log (by positivity) hM
    rw [Real.log_div hp0.ne' hK.ne'] at this
    have e : Real.log K40 = 40 * l10 := by
      unfold K40; rw [Real.log_pow]; push_cast; ring
    linarith
  have hrL : 2000 * l10 < r * L := by
    have := Real.log_lt_log (by unfold T0; positivity) hpr
    rw [Real.log_pow] at this
    have e : Real.log T0 = 2000 * l10 := by
      unfold T0; rw [Real.log_pow]; push_cast; ring
    linarith
  have hlogden : Real.log den ≤ 0 := Real.log_nonpos hden0.le hden1
  have hdR : (r : ℝ) + 1 ≤ d := by exact_mod_cast hd
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hZ1 : 0 < X ^ 10 * M ^ 9 * (p ^ d / den) := by positivity
  have hZ2 : 0 < X ^ 11 * M ^ 10 * (p ^ d / den) := by positivity
  have hlogZ : ∀ a b : ℕ, Real.log (X ^ a * M ^ b * (p ^ d / den)) =
      a * Real.log X + b * Real.log M + (d * L - Real.log den) := by
    intro a b
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_div (by positivity) hden0.ne', Real.log_pow, Real.log_pow, Real.log_pow]
  have hm1 : 0 ≤ ((d : ℝ) - (2 * r / 3 + 4 / 3)) * (L - l2 / 2) :=
    mul_nonneg (by linarith) (by linarith)
  have hm2 : 0 ≤ (r : ℝ) * (L - l2) := mul_nonneg (by linarith) (by linarith)
  have hm3 : 0 ≤ ((d : ℝ) - (19 * r / 30 + 41 / 30)) * (L - 11 * l2 / 20) :=
    mul_nonneg (by linarith) (by linarith)
  constructor
  · rw [← Real.log_lt_log_iff two_pos hZ1, hlogZ]
    push_cast
    nlinarith
  · rw [← Real.log_lt_log_iff two_pos hZ2, hlogZ]
    push_cast
    nlinarith
lemma y_le : ((2 : ℝ) ^ (-(1 : ℝ) / 20)) ≤ 49 / 50 := by
  have hy0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 : ℝ) / 20) := by positivity
  have h20 : ((2 : ℝ) ^ (-(1 : ℝ) / 20)) ^ (20 : ℕ) = 1 / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  by_contra h
  push Not at h
  have := pow_lt_pow_left₀ h (by norm_num) (by norm_num : (20 : ℕ) ≠ 0)
  rw [h20] at this
  norm_num at this
lemma pigeonhole (μ : ℕ → ℝ) (hμ : ∀ n, 0 ≤ μ n) (F : Finset (ℕ × ℕ)) (g : ℕ × ℕ → ℕ)
    (c : ℕ) (Efib : ℕ → Finset (ℕ × ℕ)) (hfib : ∀ l, F.filter (fun e => g e = l) ⊆ Efib l)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : B < esum μ F) :
    ∃ l ∈ F.image g, 1 / 100 * ((2 : ℝ) ^ (-(1 : ℝ) / 20)) ^ ((c - l) + (l - c)) * B <
      esum μ (Efib l) := by
  by_contra hcon
  push Not at hcon
  set y : ℝ := (2 : ℝ) ^ (-(1 : ℝ) / 20)
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 49 / 50 := y_le
  set S := F.image g
  have hsum : esum μ F ≤ ∑ l ∈ S, esum μ (Efib l) := by
    unfold esum
    rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := S)
      (fun e he => Finset.mem_image_of_mem _ he)]
    apply Finset.sum_le_sum
    intro l _
    apply Finset.sum_le_sum_of_subset_of_nonneg (hfib l)
    intro e _ _
    exact mul_nonneg (hμ _) (hμ _)
  have hs : ∑ l ∈ S, 1 / 100 * y ^ ((c - l) + (l - c)) ≤ 1 := by
    rw [← Finset.mul_sum]
    have h := sum_pow_dist_le hy0 (by linarith) S c
    have h1y : (1 - y)⁻¹ ≤ 50 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have hnn : 0 ≤ ∑ l ∈ S, y ^ ((c - l) + (l - c)) :=
      Finset.sum_nonneg (fun l _ => pow_nonneg hy0 _)
    linarith
  have hw : ∑ l ∈ S, 1 / 100 * y ^ ((c - l) + (l - c)) * B ≤ B := by
    rw [← Finset.sum_mul]
    calc (∑ l ∈ S, 1 / 100 * y ^ ((c - l) + (l - c))) * B ≤ 1 * B :=
          mul_le_mul_of_nonneg_right hs hB0
      _ = B := one_mul B
  have := Finset.sum_le_sum hcon
  linarith
lemma conclude (G : GCDGraph) (hδ : 0 < G.density) (p : ℕ) (hp : p.Prime) (hpP : p ∉ G.P)
    (r k l : ℕ) (hr : 1 ≤ r) (hpr : T0 < (p : ℝ) ^ r) (hdist : r + 1 ≤ (k - l) + (l - k))
    (hX : 1 / 100 * ((2 : ℝ) ^ (-(1 : ℝ) / 20)) ^ ((k - l) + (l - k)) *
        (esum G.μ G.E / (4 * (p : ℝ) ^ ((31 : ℝ) / 30))) <
      esum G.μ (G.restrictPrime p k l hp hpP).E)
    (hsmall : (p : ℝ) * wsum G.μ (vslice G.V p k) ≤ K40 * wsum G.μ G.V ∨
      (p : ℝ) * wsum G.μ (vslice G.W p l) ≤ K40 * wsum G.μ G.W) :
    2 * G.quality < (G.restrictPrime p k l hp hpP).quality ∧
      2 * G.density * G.quality <
        (G.restrictPrime p k l hp hpP).density * (G.restrictPrime p k l hp hpP).quality := by
  set H := G.restrictPrime p k l hp hpP with hH
  have hkl : k ≠ l := by omega
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hK : (0 : ℝ) < K40 := by unfold K40; positivity
  have hEpos : 0 < esum G.μ G.E := (G.density_pos_iff).1 hδ
  have hq : 0 < G.quality := (G.quality_pos_iff).2 hδ
  have hP1 : (1 : ℝ) < (p : ℝ) ^ ((31 : ℝ) / 30) := Real.one_lt_rpow (by linarith) (by norm_num)
  have hPpos : (0 : ℝ) < (p : ℝ) ^ ((31 : ℝ) / 30) := by linarith
  have hy : (0 : ℝ) < (2 : ℝ) ^ (-(1 : ℝ) / 20) := by positivity
  have hHE : 0 < esum G.μ H.E := by
    refine lt_of_le_of_lt ?_ hX
    positivity
  have hHV := wsum_pos_of_esum_pos G.μ_nonneg H.E_sub hHE
  have hVk : 0 < wsum G.μ (vslice G.V p k) := hHV.1
  have hWl : 0 < wsum G.μ (vslice G.W p l) := hHV.2
  have hVpos := wsum_V_pos_of_density_pos G hδ
  have hWpos := wsum_W_pos_of_density_pos G hδ
  have hquality := G.quality_restrictPrime p k l hp hpP hEpos hVk hWl
  rw [show (if k = l ∧ 1 ≤ k then 1 / (p : ℝ) else 0) = 0 by simp [hkl]] at hquality
  set X := esum G.μ H.E / esum G.μ G.E with hXdef
  set A := wsum G.μ G.V / wsum G.μ (vslice G.V p k) with hA
  set Bw := wsum G.μ G.W / wsum G.μ (vslice G.W p l) with hBw
  set den := (1 - (0 : ℝ)) ^ 2 * (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10 with hden
  set d := (k - l) + (l - k) with hd
  have hden0 : 0 < den := by
    have : 0 < 1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30) := by
      rw [sub_pos, div_lt_one hPpos]; exact hP1
    positivity
  have hden1 : den ≤ 1 := by
    have h1 : 0 ≤ 1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30) := by
      rw [sub_nonneg, div_le_one hPpos]; exact hP1.le
    have h2 : 1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30) ≤ 1 := by
      have : 0 ≤ 1 / (p : ℝ) ^ ((31 : ℝ) / 30) := by positivity
      linarith
    rw [hden]
    simp only [sub_zero, one_pow, one_mul]
    exact pow_le_one₀ h1 h2
  have hA1 : 1 ≤ A := by
    rw [hA, le_div_iff₀ hVk, one_mul]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro i _ _; exact G.μ_nonneg i
  have hB1 : 1 ≤ Bw := by
    rw [hBw, le_div_iff₀ hWl, one_mul]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro i _ _; exact G.μ_nonneg i
  have hM : (p : ℝ) / K40 ≤ A * Bw := by
    rcases hsmall with h | h
    · have hA' : (p : ℝ) / K40 ≤ A := by
        rw [hA, le_div_iff₀ hVk, div_mul_eq_mul_div, div_le_iff₀ hK]; linarith
      nlinarith
    · have hB' : (p : ℝ) / K40 ≤ Bw := by
        rw [hBw, le_div_iff₀ hWl, div_mul_eq_mul_div, div_le_iff₀ hK]; linarith
      nlinarith
  have hXc : 1 / 100 * ((2 : ℝ) ^ (-(1 : ℝ) / 20)) ^ d / (4 * (p : ℝ) ^ ((31 : ℝ) / 30)) < X := by
    rw [hXdef, lt_div_iff₀ hEpos]
    calc 1 / 100 * ((2 : ℝ) ^ (-(1 : ℝ) / 20)) ^ d / (4 * (p : ℝ) ^ ((31 : ℝ) / 30)) *
          esum G.μ G.E
        = 1 / 100 * ((2 : ℝ) ^ (-(1 : ℝ) / 20)) ^ d *
          (esum G.μ G.E / (4 * (p : ℝ) ^ ((31 : ℝ) / 30))) := by ring
      _ < esum G.μ H.E := hX
  obtain ⟨c1, c2⟩ := core_ineq (p : ℝ) hp2 r d hr hdist hpr X (A * Bw) den hXc hM hden0 hden1
  have hqH : H.quality = G.quality * (X ^ 10 * (A * Bw) ^ 9 * ((p : ℝ) ^ d / den)) := by
    rw [hquality]; ring
  have hδH : H.density = G.density * (X * (A * Bw)) := by
    have e1 : H.density = esum G.μ H.E /
        (wsum G.μ (vslice G.V p k) * wsum G.μ (vslice G.W p l)) := rfl
    have e2 : G.density = esum G.μ G.E / (wsum G.μ G.V * wsum G.μ G.W) := rfl
    rw [e1, e2, hXdef, hA, hBw]
    field_simp
  constructor
  · rw [hqH]
    nlinarith
  · have : H.density * H.quality =
        (G.density * G.quality) * (X ^ 11 * (A * Bw) ^ 10 * ((p : ℝ) ^ d / den)) := by
      rw [hqH, hδH]; ring
    rw [this]
    have hδq : 0 < G.density * G.quality := mul_pos hδ hq
    calc 2 * G.density * G.quality = (G.density * G.quality) * 2 := by ring
      _ < _ := mul_lt_mul_of_pos_left c2 hδq
end Unbalanced
open Unbalanced
theorem lemma113 (G : GCDGraph) (hδ : 0 < G.density) (p : ℕ) (hp : p.Prime) (hpP : p ∉ G.P)
    (r k : ℕ) (hr : 1 ≤ r) (hpr : T0 < (p : ℝ) ^ r)
    (hW : (1 - K40 / p) * wsum G.μ G.W ≤ wsum G.μ (vslice G.W p k)) :
    (∃ l : ℕ, r + 1 ≤ (k - l) + (l - k) ∧
        2 * G.quality < (G.restrictPrime p k l hp hpP).quality ∧
        2 * G.density * G.quality <
          (G.restrictPrime p k l hp hpP).density * (G.restrictPrime p k l hp hpP).quality) ∨
      esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧
          r + 1 ≤ (k - e.2.factorization p) + (e.2.factorization p - k))) ≤
        esum G.μ G.E / (4 * (p : ℝ) ^ ((31 : ℝ) / 30)) := by
  by_cases hb : esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧
          r + 1 ≤ (k - e.2.factorization p) + (e.2.factorization p - k))) ≤
        esum G.μ G.E / (4 * (p : ℝ) ^ ((31 : ℝ) / 30))
  · exact Or.inr hb
  left
  push Not at hb
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hEpos : 0 < esum G.μ G.E := (G.density_pos_iff).1 hδ
  have hB0 : 0 ≤ esum G.μ G.E / (4 * (p : ℝ) ^ ((31 : ℝ) / 30)) := by positivity
  obtain ⟨l, hlS, hl⟩ := pigeonhole G.μ G.μ_nonneg _ (fun e => e.2.factorization p) k
    (fun l => G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l))
    (by
      intro l e he
      simp only [Finset.mem_filter] at he ⊢
      exact ⟨he.1.1, he.1.2.1, he.2⟩)
    _ hB0 hb
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hlS
  have hdist := (Finset.mem_filter.1 he).2.2
  refine ⟨e.2.factorization p, hdist, ?_⟩
  refine conclude G hδ p hp hpP r k _ hr hpr hdist hl (Or.inr ?_)
  exact small_other_slice G.μ_nonneg G.W p k _ hp0 (by omega) hW
theorem lemma114 (G : GCDGraph) (hδ : 0 < G.density) (p : ℕ) (hp : p.Prime) (hpP : p ∉ G.P)
    (r l : ℕ) (hr : 1 ≤ r) (hpr : T0 < (p : ℝ) ^ r)
    (hV : (1 - K40 / p) * wsum G.μ G.V ≤ wsum G.μ (vslice G.V p l)) :
    (∃ k : ℕ, r + 1 ≤ (k - l) + (l - k) ∧
        2 * G.quality < (G.restrictPrime p k l hp hpP).quality ∧
        2 * G.density * G.quality <
          (G.restrictPrime p k l hp hpP).density * (G.restrictPrime p k l hp hpP).quality) ∨
      esum G.μ (G.E.filter (fun e => e.2.factorization p = l ∧
          r + 1 ≤ (e.1.factorization p - l) + (l - e.1.factorization p))) ≤
        esum G.μ G.E / (4 * (p : ℝ) ^ ((31 : ℝ) / 30)) := by
  by_cases hb : esum G.μ (G.E.filter (fun e => e.2.factorization p = l ∧
          r + 1 ≤ (e.1.factorization p - l) + (l - e.1.factorization p))) ≤
        esum G.μ G.E / (4 * (p : ℝ) ^ ((31 : ℝ) / 30))
  · exact Or.inr hb
  left
  push Not at hb
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hEpos : 0 < esum G.μ G.E := (G.density_pos_iff).1 hδ
  have hB0 : 0 ≤ esum G.μ G.E / (4 * (p : ℝ) ^ ((31 : ℝ) / 30)) := by positivity
  obtain ⟨k, hkS, hk⟩ := pigeonhole G.μ G.μ_nonneg _ (fun e => e.1.factorization p) l
    (fun k => G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l))
    (by
      intro k e he
      simp only [Finset.mem_filter] at he ⊢
      exact ⟨he.1.1, he.2, he.1.2.1⟩)
    _ hB0 hb
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hkS
  have hdist := (Finset.mem_filter.1 he).2.2
  refine ⟨e.1.factorization p, hdist, ?_⟩
  have hk' : 1 / 100 * ((2 : ℝ) ^ (-(1 : ℝ) / 20)) ^
      ((e.1.factorization p - l) + (l - e.1.factorization p)) *
      (esum G.μ G.E / (4 * (p : ℝ) ^ ((31 : ℝ) / 30))) <
      esum G.μ (G.restrictPrime p (e.1.factorization p) l hp hpP).E := by
    rw [Nat.add_comm (e.1.factorization p - l)]
    exact hk
  refine conclude G hδ p hp hpP r _ l hr hpr hdist hk' (Or.inl ?_)
  exact small_other_slice G.μ_nonneg G.V p l _ hp0 (by omega) hV
end GCDGraph
end DuffinSchaeffer
end Port24_Parts_Unbalanced

section Port24_Parts_GenericPrimes
open Finset
namespace DuffinSchaeffer
namespace GCDGraph
noncomputable def alt_gp_B (α β : ℕ → ℝ) (k l : ℕ) : ℝ :=
  if k = l then (α k * β k) ^ ((9 : ℝ) / 10) else
    (α k * (1 - β k) + β k * (1 - α k) + (α l * (1 - β l) + β l * (1 - α l))) *
      (20 / 21 : ℝ) ^ ((k - l) + (l - k)) / 1000
theorem alt_gp_geom_eq (m : ℕ) :
    ∑ i ∈ range m, (20 / 21 : ℝ) ^ (i + 1) = 20 * (1 - (20 / 21 : ℝ) ^ m) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; ring
theorem alt_gp_geom_le (m : ℕ) : ∑ i ∈ range m, (20 / 21 : ℝ) ^ (i + 1) ≤ 20 := by
  rw [alt_gp_geom_eq]
  have : (0 : ℝ) ≤ (20 / 21 : ℝ) ^ m := by positivity
  linarith
theorem alt_gp_offdiag (n k : ℕ) :
    ∑ l ∈ range n, (if k = l then (0 : ℝ) else (20 / 21 : ℝ) ^ ((k - l) + (l - k))) ≤ 40 := by
  have hpt : ∀ l ∈ range n, (if k = l then (0 : ℝ) else (20 / 21 : ℝ) ^ ((k - l) + (l - k))) ≤
      (if l < k then (20 / 21 : ℝ) ^ (k - l) else 0) +
        (if k < l then (20 / 21 : ℝ) ^ (l - k) else 0) := by
    intro l _
    rcases lt_trichotomy l k with h | h | h
    · rw [if_neg (by omega), if_pos h, if_neg (by omega), add_zero]
      have : l - k = 0 := by omega
      rw [this, add_zero]
    · subst h; simp
    · rw [if_neg (by omega), if_neg (by omega), if_pos h, zero_add]
      have : k - l = 0 := by omega
      rw [this, zero_add]
  refine (sum_le_sum hpt).trans ?_
  rw [sum_add_distrib, ← sum_filter, ← sum_filter]
  have h1 : ∑ l ∈ (range n).filter (fun l => l < k), (20 / 21 : ℝ) ^ (k - l) ≤ 20 := by
    have hsub : (range n).filter (fun l => l < k) ⊆ range k := by
      intro l hl; simp only [mem_filter, mem_range] at hl ⊢; exact hl.2
    refine (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans ?_
    rw [← sum_range_reflect]
    refine le_of_eq_of_le (sum_congr rfl ?_) (alt_gp_geom_le k)
    intro j hj
    simp only [mem_range] at hj
    congr 1
    omega
  have h2 : ∑ l ∈ (range n).filter (fun l => k < l), (20 / 21 : ℝ) ^ (l - k) ≤ 20 := by
    have hset : (range n).filter (fun l => k < l) = Ico (k + 1) n := by
      ext l; simp only [mem_filter, mem_range, mem_Ico]; omega
    rw [hset, sum_Ico_eq_sum_range]
    refine le_of_eq_of_le (sum_congr rfl ?_) (alt_gp_geom_le (n - (k + 1)))
    intro j _
    congr 1
    omega
  linarith
theorem alt_gp_sqrt_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a * b) ^ ((1 : ℝ) / 2) ≤ (a + b) / 2 := by
  rw [Real.mul_rpow ha hb]
  have := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 / 2) (w₂ := 1 / 2) (p₁ := a) (p₂ := b)
    (by norm_num) (by norm_num) ha hb (by norm_num)
  linarith
theorem alt_gp_sum_bound (n : ℕ) (α β : ℕ → ℝ) (hα0 : ∀ k, 0 ≤ α k) (hβ0 : ∀ k, 0 ≤ β k)
    (hα : ∑ k ∈ range n, α k = 1) (hβ : ∑ k ∈ range n, β k = 1) :
    ∑ k ∈ range n, ∑ l ∈ range n, alt_gp_B α β k l ≤ 1 := by
  have hα1 : ∀ k ∈ range n, α k ≤ 1 := fun k hk => by
    rw [← hα]; exact single_le_sum (fun i _ => hα0 i) hk
  have hβ1 : ∀ k ∈ range n, β k ≤ 1 := fun k hk => by
    rw [← hβ]; exact single_le_sum (fun i _ => hβ0 i) hk
  have hn : (range n).Nonempty := by
    rw [nonempty_iff_ne_empty]; intro h; rw [h, sum_empty] at hα; norm_num at hα
  set A : ℕ → ℝ := fun k => α k * (1 - β k) + β k * (1 - α k) with hA
  set e : ℕ → ℕ → ℝ := fun k l =>
    if k = l then (0 : ℝ) else (20 / 21 : ℝ) ^ ((k - l) + (l - k)) with he
  have hA0 : ∀ k ∈ range n, 0 ≤ A k := fun k hk => by
    have := hα1 k hk; have := hβ1 k hk; have := hα0 k; have := hβ0 k
    simp only [hA]; nlinarith
  have he0 : ∀ k l, 0 ≤ e k l := fun k l => by simp only [he]; split_ifs <;> positivity
  have hesymm : ∀ k l, e k l = e l k := fun k l => by
    simp only [he]
    by_cases h : k = l
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h), add_comm]
  have hB : ∀ k l, alt_gp_B α β k l =
      (if k = l then (α k * β k) ^ ((9 : ℝ) / 10) else 0) +
        (A k * e k l / 1000 + A l * e k l / 1000) := fun k l => by
    simp only [alt_gp_B, hA, he]
    split_ifs <;> ring
  simp_rw [hB, sum_add_distrib]
  rw [sum_comm (f := fun k l => A l * e k l / 1000)]
  have hdiag : ∀ k ∈ range n, ∑ l ∈ range n, (if k = l then (α k * β k) ^ ((9 : ℝ) / 10) else 0)
      = (α k * β k) ^ ((9 : ℝ) / 10) := fun k hk => by rw [sum_ite_eq, if_pos hk]
  rw [sum_congr rfl hdiag]
  have hoff1 : ∀ k ∈ range n, ∑ l ∈ range n, A k * e k l / 1000 ≤ A k * 40 / 1000 := by
    intro k hk
    rw [← sum_div, ← mul_sum]
    gcongr
    · exact hA0 k hk
    · exact alt_gp_offdiag n k
  have hoff2 : ∀ l ∈ range n, ∑ k ∈ range n, A l * e k l / 1000 ≤ A l * 40 / 1000 := by
    intro l hl
    simp_rw [hesymm _ l]
    exact hoff1 l hl
  have hS2 := add_le_add (sum_le_sum hoff1) (sum_le_sum hoff2)
  set D := ∑ k ∈ range n, α k * β k with hD
  have hsumA : ∑ k ∈ range n, A k * 40 / 1000 = (2 - 2 * D) * 40 / 1000 := by
    rw [← sum_div, ← sum_mul]
    congr 2
    simp only [hA, hD, mul_sub, mul_one, sum_add_distrib, sum_sub_distrib, hα, hβ]
    rw [show ∑ i ∈ range n, β i * α i = ∑ i ∈ range n, α i * β i from
      sum_congr rfl fun i _ => mul_comm _ _]
    ring
  obtain ⟨k0, hk0, hmax⟩ := exists_max_image (range n) (fun k => α k * β k) hn
  set γ := α k0 * β k0 with hγ
  have hγ0 : 0 ≤ γ := mul_nonneg (hα0 k0) (hβ0 k0)
  have hγ1 : γ ≤ 1 := by
    have := hα1 k0 hk0; have := hβ1 k0 hk0
    calc γ = α k0 * β k0 := rfl
      _ ≤ 1 * 1 := mul_le_mul (hα1 k0 hk0) (hβ1 k0 hk0) (hβ0 k0) zero_le_one
      _ = 1 := by norm_num
  have hDγ : γ ≤ D := single_le_sum (f := fun k => α k * β k)
    (fun i _ => mul_nonneg (hα0 i) (hβ0 i)) hk0
  have hS1 : ∑ k ∈ range n, (α k * β k) ^ ((9 : ℝ) / 10) ≤ γ ^ ((2 : ℝ) / 5) := by
    have hpt : ∀ k ∈ range n, (α k * β k) ^ ((9 : ℝ) / 10) ≤
        γ ^ ((2 : ℝ) / 5) * ((α k + β k) / 2) := by
      intro k hk
      have hx0 : 0 ≤ α k * β k := mul_nonneg (hα0 k) (hβ0 k)
      rw [show (9 : ℝ) / 10 = 2 / 5 + 1 / 2 by norm_num, Real.rpow_add' hx0 (by norm_num)]
      exact mul_le_mul (Real.rpow_le_rpow hx0 (hmax k hk) (by norm_num))
        (alt_gp_sqrt_le _ _ (hα0 k) (hβ0 k)) (by positivity) (by positivity)
    refine (sum_le_sum hpt).trans (le_of_eq ?_)
    rw [← mul_sum, ← sum_div, sum_add_distrib, hα, hβ]
    norm_num
  have hbern : γ ^ ((2 : ℝ) / 5) ≤ 1 + 2 / 5 * (γ - 1) := by
    have := _root_.rpow_one_add_le_one_add_mul_self (s := γ - 1) (by linarith)
      (p := (2 : ℝ) / 5) (by norm_num) (by norm_num)
    simpa using this
  linarith
theorem alt_gp_pos (G : GCDGraph) (hδ : 0 < G.density) :
    0 < esum G.μ G.E ∧ 0 < wsum G.μ G.V ∧ 0 < wsum G.μ G.W := by
  have hV0 : 0 ≤ wsum G.μ G.V := sum_nonneg fun i _ => G.μ_nonneg i
  have hW0 : 0 ≤ wsum G.μ G.W := sum_nonneg fun i _ => G.μ_nonneg i
  unfold density at hδ
  have hVW : wsum G.μ G.V * wsum G.μ G.W ≠ 0 := by
    intro h; rw [h, div_zero] at hδ; exact lt_irrefl _ hδ
  have hVW' : 0 < wsum G.μ G.V * wsum G.μ G.W :=
    lt_of_le_of_ne (mul_nonneg hV0 hW0) (Ne.symm hVW)
  refine ⟨(div_pos_iff_of_pos_right hVW').1 hδ,
    lt_of_le_of_ne hV0 (fun h => hVW (by rw [← h, zero_mul])),
    lt_of_le_of_ne hW0 (fun h => hVW (by rw [← h, mul_zero]))⟩
theorem alt_gp_wsum_nonneg (G : GCDGraph) (S : Finset ℕ) : 0 ≤ wsum G.μ S :=
  sum_nonneg fun i _ => G.μ_nonneg i
theorem alt_gp_esum_nonneg (G : GCDGraph) (S : Finset (ℕ × ℕ)) : 0 ≤ esum G.μ S :=
  sum_nonneg fun i _ => mul_nonneg (G.μ_nonneg _) (G.μ_nonneg _)
theorem alt_gp_vslice_le (G : GCDGraph) (S : Finset ℕ) (p k : ℕ) :
    wsum G.μ (vslice S p k) ≤ wsum G.μ S :=
  sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => G.μ_nonneg i)
theorem alt_gp_two_slices (G : GCDGraph) (S : Finset ℕ) (p k l : ℕ) (hkl : k ≠ l) :
    wsum G.μ (vslice S p k) + wsum G.μ (vslice S p l) ≤ wsum G.μ S := by
  unfold wsum vslice
  rw [← sum_union (disjoint_filter.2 (fun v _ h1 h2 => hkl (h1.symm.trans h2)))]
  exact sum_le_sum_of_subset_of_nonneg (union_subset (filter_subset _ _) (filter_subset _ _))
    (fun i _ _ => G.μ_nonneg i)
theorem alt_gp_wsum_partition (G : GCDGraph) (S : Finset ℕ) (p N : ℕ)
    (hN : ∀ v ∈ S, v.factorization p ≤ N) :
    ∑ k ∈ range (N + 1), wsum G.μ (vslice S p k) = wsum G.μ S := by
  unfold wsum vslice
  exact sum_fiberwise_of_maps_to (fun v hv => mem_range.2 (Nat.lt_succ_of_le (hN v hv))) G.μ
theorem alt_gp_esum_partition (G : GCDGraph) (p N : ℕ)
    (hN : ∀ e ∈ G.E, e.1.factorization p ≤ N ∧ e.2.factorization p ≤ N) :
    ∑ k ∈ range (N + 1), ∑ l ∈ range (N + 1),
      esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l)) =
      esum G.μ G.E := by
  rw [← sum_product' (f := fun k l =>
    esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l)))]
  have h := sum_fiberwise_of_maps_to (s := G.E) (t := range (N + 1) ×ˢ range (N + 1))
    (g := fun e : ℕ × ℕ => (e.1.factorization p, e.2.factorization p))
    (fun e he => mem_product.2 ⟨mem_range.2 (Nat.lt_succ_of_le (hN e he).1),
      mem_range.2 (Nat.lt_succ_of_le (hN e he).2)⟩) (fun e => G.μ e.1 * G.μ e.2)
  unfold esum
  rw [← h]
  refine sum_congr rfl fun x _ => sum_congr ?_ fun _ _ => rfl
  ext e
  simp [Prod.ext_iff]
theorem alt_gp_esum_slice_le (G : GCDGraph) (p k l : ℕ) :
    esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l)) ≤
      wsum G.μ (vslice G.V p k) * wsum G.μ (vslice G.W p l) := by
  have hsub : G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l) ⊆
      vslice G.V p k ×ˢ vslice G.W p l := by
    intro e he
    obtain ⟨he, h1, h2⟩ := mem_filter.1 he
    obtain ⟨hv, hw⟩ := mem_product.1 (G.E_sub he)
    exact mem_product.2 ⟨mem_filter.2 ⟨hv, h1⟩, mem_filter.2 ⟨hw, h2⟩⟩
  unfold esum wsum
  rw [sum_mul_sum, ← sum_product']
  exact sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ => mul_nonneg (G.μ_nonneg _) (G.μ_nonneg _))
theorem alt_gp_B_nonneg (α β : ℕ → ℝ) (hα0 : ∀ k, 0 ≤ α k) (hβ0 : ∀ k, 0 ≤ β k)
    (hα1 : ∀ k, α k ≤ 1) (hβ1 : ∀ k, β k ≤ 1) (k l : ℕ) : 0 ≤ alt_gp_B α β k l := by
  unfold alt_gp_B
  split_ifs
  · exact Real.rpow_nonneg (mul_nonneg (hα0 k) (hβ0 k)) _
  · have := hα0 k; have := hβ0 k; have := hα1 k; have := hβ1 k
    have := hα0 l; have := hβ0 l; have := hα1 l; have := hβ1 l
    have h1 : 0 ≤ α k * (1 - β k) + β k * (1 - α k) + (α l * (1 - β l) + β l * (1 - α l)) := by
      nlinarith
    positivity
theorem alt_gp_lemma121 (G : GCDGraph) (hδ : 0 < G.density) (p : ℕ) :
    ∃ k l : ℕ, 0 < wsum G.μ (vslice G.V p k) ∧ 0 < wsum G.μ (vslice G.W p l) ∧
      alt_gp_B (fun k => wsum G.μ (vslice G.V p k) / wsum G.μ G.V)
          (fun l => wsum G.μ (vslice G.W p l) / wsum G.μ G.W) k l * esum G.μ G.E ≤
        esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l)) := by
  obtain ⟨hE, hV, hW⟩ := alt_gp_pos G hδ
  set N := (G.V ∪ G.W).sup (fun v => v.factorization p) with hNdef
  have hNV : ∀ v ∈ G.V, v.factorization p ≤ N := fun v hv =>
    le_sup (f := fun v => v.factorization p) (mem_union_left _ hv)
  have hNW : ∀ v ∈ G.W, v.factorization p ≤ N := fun v hv =>
    le_sup (f := fun v => v.factorization p) (mem_union_right _ hv)
  have hNE : ∀ e ∈ G.E, e.1.factorization p ≤ N ∧ e.2.factorization p ≤ N := fun e he => by
    obtain ⟨hv, hw⟩ := mem_product.1 (G.E_sub he)
    exact ⟨hNV _ hv, hNW _ hw⟩
  set α : ℕ → ℝ := fun k => wsum G.μ (vslice G.V p k) / wsum G.μ G.V with hα
  set β : ℕ → ℝ := fun l => wsum G.μ (vslice G.W p l) / wsum G.μ G.W with hβ
  have hα0 : ∀ k, 0 ≤ α k := fun k => div_nonneg (alt_gp_wsum_nonneg G _) hV.le
  have hβ0 : ∀ k, 0 ≤ β k := fun k => div_nonneg (alt_gp_wsum_nonneg G _) hW.le
  have hα1 : ∀ k, α k ≤ 1 := fun k => (div_le_one hV).2 (alt_gp_vslice_le G _ _ _)
  have hβ1 : ∀ k, β k ≤ 1 := fun k => (div_le_one hW).2 (alt_gp_vslice_le G _ _ _)
  have hαs : ∑ k ∈ range (N + 1), α k = 1 := by
    simp only [hα]; rw [← sum_div, alt_gp_wsum_partition G _ p N hNV, div_self hV.ne']
  have hβs : ∑ k ∈ range (N + 1), β k = 1 := by
    simp only [hβ]; rw [← sum_div, alt_gp_wsum_partition G _ p N hNW, div_self hW.ne']
  have hsum := alt_gp_sum_bound (N + 1) α β hα0 hβ0 hαs hβs
  by_contra hcon
  push_neg at hcon
  set Ekl : ℕ → ℕ → ℝ := fun k l =>
    esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l)) with hEkl
  have hle : ∀ x ∈ range (N + 1) ×ˢ range (N + 1),
      Ekl x.1 x.2 ≤ alt_gp_B α β x.1 x.2 * esum G.μ G.E := by
    intro x _
    by_cases h : 0 < wsum G.μ (vslice G.V p x.1) ∧ 0 < wsum G.μ (vslice G.W p x.2)
    · exact (hcon x.1 x.2 h.1 h.2).le
    · have h0 : wsum G.μ (vslice G.V p x.1) * wsum G.μ (vslice G.W p x.2) = 0 := by
        rcases not_and_or.1 h with h | h
        · rw [le_antisymm (not_lt.1 h) (alt_gp_wsum_nonneg G _), zero_mul]
        · rw [le_antisymm (not_lt.1 h) (alt_gp_wsum_nonneg G _), mul_zero]
      calc Ekl x.1 x.2 ≤ _ := alt_gp_esum_slice_le G p x.1 x.2
        _ = 0 := h0
        _ ≤ _ := mul_nonneg (alt_gp_B_nonneg α β hα0 hβ0 hα1 hβ1 _ _) hE.le
  have hpart : ∑ x ∈ range (N + 1) ×ˢ range (N + 1), Ekl x.1 x.2 = esum G.μ G.E := by
    rw [sum_product' (f := Ekl)]; exact alt_gp_esum_partition G p N hNE
  have hex : ∃ x ∈ range (N + 1) ×ˢ range (N + 1), (0 : ℝ) < Ekl x.1 x.2 := by
    apply exists_lt_of_sum_lt
    rw [hpart, sum_const_zero]; exact hE
  obtain ⟨x, hx, hxpos⟩ := hex
  have hlt : ∃ x ∈ range (N + 1) ×ˢ range (N + 1),
      Ekl x.1 x.2 < alt_gp_B α β x.1 x.2 * esum G.μ G.E := by
    refine ⟨x, hx, hcon x.1 x.2 ?_ ?_⟩
    · by_contra h0
      have h0' := le_antisymm (not_lt.1 h0) (alt_gp_wsum_nonneg G _)
      have := alt_gp_esum_slice_le G p x.1 x.2
      rw [h0', zero_mul] at this
      exact absurd hxpos (not_lt.2 this)
    · by_contra h0
      have h0' := le_antisymm (not_lt.1 h0) (alt_gp_wsum_nonneg G _)
      have := alt_gp_esum_slice_le G p x.1 x.2
      rw [h0', mul_zero] at this
      exact absurd hxpos (not_lt.2 this)
  have := sum_lt_sum hle hlt
  rw [hpart, ← sum_mul, sum_product' (f := fun k l => alt_gp_B α β k l)] at this
  have h2 := mul_le_mul_of_nonneg_right hsum hE.le
  linarith
theorem alt_gp_F_ge (p : ℕ) (hp : p.Prime) (j : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2) :
    (p : ℝ) ^ j ≤ (p : ℝ) ^ j / ((1 - c) ^ 2 * (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpr : (p : ℝ) ≤ (p : ℝ) ^ ((31 : ℝ) / 30) := by
    conv_lhs => rw [← Real.rpow_one (p : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hq0 : 0 < 1 / (p : ℝ) ^ ((31 : ℝ) / 30) := by positivity
  have hq1 : 1 / (p : ℝ) ^ ((31 : ℝ) / 30) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  apply le_div_self (by positivity)
  · apply mul_pos
    · apply pow_pos; linarith
    · apply pow_pos; linarith
  · calc (1 - c) ^ 2 * (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10 ≤ 1 * 1 := by
          apply mul_le_mul _ _ (by apply pow_nonneg; linarith) zero_le_one
          · apply pow_le_one₀ <;> linarith
          · apply pow_le_one₀ <;> linarith
      _ = 1 := by norm_num
theorem alt_gp_key (a b x S F P : ℝ) (j : ℕ) (ha : 0 < a) (hb : 0 < b) (hSy : a * b ≤ S)
    (hx : S * (20 / 21 : ℝ) ^ j / 1000 ≤ x) (hj : 1 ≤ j) (hP : 2 ≤ P) (hF : P ^ j ≤ F) :
    S ^ 2 / (a * b) * P / (2 * 10 ^ 33) ≤
      min 1 (x / (a * b)) * (x ^ 10 * (1 / a) ^ 9 * (1 / b) ^ 9 * F) := by
  set y := a * b with hy
  have hy0 : 0 < y := mul_pos ha hb
  have hS0 : 0 < S := lt_of_lt_of_le hy0 hSy
  set t : ℝ := (20 / 21 : ℝ) ^ j / 1000 with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    have : (20 / 21 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    rw [ht]; linarith
  have hxS : S * t ≤ x := by rw [ht, ← mul_div_assoc]; exact hx
  have hx0 : 0 < x := lt_of_lt_of_le (mul_pos hS0 ht0) hxS
  have hmin : t ≤ min 1 (x / y) := by
    apply le_min ht1
    rw [le_div_iff₀ hy0]
    calc t * y ≤ t * S := mul_le_mul_of_nonneg_left hSy ht0.le
      _ = S * t := mul_comm _ _
      _ ≤ x := hxS
  have hab : (1 / a) ^ 9 * (1 / b) ^ 9 = 1 / y ^ 9 := by
    rw [hy, mul_pow, one_div_pow, one_div_pow, one_div_mul_one_div]
  have hF0 : 0 < F := lt_of_lt_of_le (by positivity) hF
  have h10 : (S * t) ^ 10 ≤ x ^ 10 := pow_le_pow_left₀ (by positivity) hxS 10
  have hS8 : y ^ 8 ≤ S ^ 8 := pow_le_pow_left₀ hy0.le hSy 8
  have htP : P / (2 * 10 ^ 33) ≤ t ^ 11 * P ^ j := by
    have hr : (1 : ℝ) / 2 ≤ (20 / 21 : ℝ) ^ 11 := by norm_num
    have hbase : 1 ≤ (20 / 21 : ℝ) ^ 11 * P := by nlinarith
    have hpow : (20 / 21 : ℝ) ^ 11 * P ≤ ((20 / 21 : ℝ) ^ 11 * P) ^ j := by
      conv_lhs => rw [← pow_one ((20 / 21 : ℝ) ^ 11 * P)]
      exact pow_le_pow_right₀ hbase hj
    have : t ^ 11 * P ^ j = ((20 / 21 : ℝ) ^ 11 * P) ^ j / 10 ^ 33 := by
      rw [ht, div_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm j 11]; ring
    rw [this, le_div_iff₀ (by norm_num)]
    have : P / (2 * 10 ^ 33) * 10 ^ 33 = (1 / 2) * P := by ring
    rw [this]
    nlinarith
  have hmain : t * (x ^ 10 * (1 / y ^ 9) * F) ≥ t ^ 11 * P ^ j * (S ^ 2 / y) := by
    have h1 : x ^ 10 * (1 / y ^ 9) * F ≥ (S * t) ^ 10 * (1 / y ^ 9) * P ^ j := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right h10 (by positivity)) hF (by positivity)
        (by positivity)
    have h2 : (S * t) ^ 10 * (1 / y ^ 9) * P ^ j ≥ t ^ 10 * P ^ j * (S ^ 2 / y) := by
      have : S ^ 2 / y ≤ S ^ 10 * (1 / y ^ 9) := by
        rw [div_le_iff₀ hy0]
        have e : S ^ 10 * (1 / y ^ 9) * y = S ^ 2 * (S ^ 8 / y ^ 8) := by
          field_simp
        rw [e]
        have : 1 ≤ S ^ 8 / y ^ 8 := by rw [le_div_iff₀ (by positivity)]; linarith
        nlinarith [sq_nonneg S]
      calc t ^ 10 * P ^ j * (S ^ 2 / y) ≤ t ^ 10 * P ^ j * (S ^ 10 * (1 / y ^ 9)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = (S * t) ^ 10 * (1 / y ^ 9) * P ^ j := by ring
    calc t ^ 11 * P ^ j * (S ^ 2 / y) = t * (t ^ 10 * P ^ j * (S ^ 2 / y)) := by ring
      _ ≤ t * ((S * t) ^ 10 * (1 / y ^ 9) * P ^ j) := mul_le_mul_of_nonneg_left h2 ht0.le
      _ ≤ t * (x ^ 10 * (1 / y ^ 9) * F) := mul_le_mul_of_nonneg_left h1 ht0.le
  have hval : min 1 (x / y) * (x ^ 10 * (1 / a) ^ 9 * (1 / b) ^ 9 * F) =
      min 1 (x / y) * (x ^ 10 * (1 / y ^ 9) * F) := by
    rw [mul_assoc (x ^ 10), hab]
  rw [hval]
  have hnn : 0 ≤ x ^ 10 * (1 / y ^ 9) * F := by positivity
  calc S ^ 2 / y * P / (2 * 10 ^ 33) = P / (2 * 10 ^ 33) * (S ^ 2 / y) := by ring
    _ ≤ t ^ 11 * P ^ j * (S ^ 2 / y) :=
        mul_le_mul_of_nonneg_right htP (by positivity)
    _ ≤ t * (x ^ 10 * (1 / y ^ 9) * F) := hmain
    _ ≤ min 1 (x / y) * (x ^ 10 * (1 / y ^ 9) * F) := mul_le_mul_of_nonneg_right hmin hnn
theorem alt_gp_diag (a b x F : ℝ) (ha : 0 < a) (hb : 0 < b) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hx : (a * b) ^ ((9 : ℝ) / 10) ≤ x) (hF : 1 ≤ F) :
    1 ≤ min 1 (x / (a * b)) * (x ^ 10 * (1 / a) ^ 9 * (1 / b) ^ 9 * F) := by
  set y := a * b with hy
  have hy0 : 0 < y := mul_pos ha hb
  have hy1 : y ≤ 1 := by
    calc y = a * b := rfl
      _ ≤ 1 * 1 := mul_le_mul ha1 hb1 hb.le zero_le_one
      _ = 1 := by norm_num
  have hyx : y ≤ x := by
    refine le_trans ?_ hx
    conv_lhs => rw [← Real.rpow_one y]
    exact Real.rpow_le_rpow_of_exponent_ge hy0 hy1 (by norm_num)
  have hmin : min 1 (x / y) = 1 := by
    rw [min_eq_left]; rw [le_div_iff₀ hy0]; linarith
  have hab : (1 / a) ^ 9 * (1 / b) ^ 9 = 1 / y ^ 9 := by
    rw [hy, mul_pow, one_div_pow, one_div_pow, one_div_mul_one_div]
  rw [hmin, one_mul, mul_assoc (x ^ 10), hab]
  have hx10 : y ^ 9 ≤ x ^ 10 := by
    have h1 : ((y ^ ((9 : ℝ) / 10)) ^ (10 : ℕ)) = y ^ 9 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num
    rw [← h1]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hy0.le _) hx 10
  have : 1 ≤ x ^ 10 * (1 / y ^ 9) := by
    rw [mul_one_div, le_div_iff₀ (by positivity)]; linarith
  nlinarith
theorem alt_gp_sharp_real (ak bk al bl η : ℝ) (hak0 : 0 ≤ ak) (hbk0 : 0 ≤ bk) (hal0 : 0 ≤ al)
    (hbl0 : 0 ≤ bl) (hak1 : ak ≤ 1) (hbk1 : bk ≤ 1) (hal1 : al ≤ 1) (hbl1 : bl ≤ 1)
    (hy : 0 < ak * bl)
    (hQ : (ak * (1 - bk) + bk * (1 - ak) + (al * (1 - bl) + bl * (1 - al))) ^ 2 / (ak * bl) ≤ 1 / 5)
    (hS : ak * (1 - bk) + bk * (1 - ak) + (al * (1 - bl) + bl * (1 - al)) ≤ η)
    (hη : 2 * η ≤ 1 / 2) :
    (1 - ak ≤ 2 * η ∧ 1 - bk ≤ 2 * η) ∨ (1 - al ≤ 2 * η ∧ 1 - bl ≤ 2 * η) := by
  set S := ak * (1 - bk) + bk * (1 - ak) + (al * (1 - bl) + bl * (1 - al)) with hSdef
  have t1 : 0 ≤ ak * (1 - bk) := mul_nonneg hak0 (by linarith)
  have t2 : 0 ≤ bk * (1 - ak) := mul_nonneg hbk0 (by linarith)
  have t3 : 0 ≤ al * (1 - bl) := mul_nonneg hal0 (by linarith)
  have t4 : 0 ≤ bl * (1 - al) := mul_nonneg hbl0 (by linarith)
  by_cases hbk : 1 / 2 ≤ bk
  · left
    have h1 : 1 - ak ≤ 2 * η := by nlinarith
    refine ⟨h1, ?_⟩
    have : 1 / 2 ≤ ak := by linarith
    nlinarith
  by_cases hal : 1 / 2 ≤ al
  · right
    have h1 : 1 - bl ≤ 2 * η := by nlinarith
    refine ⟨?_, h1⟩
    have : 1 / 2 ≤ bl := by linarith
    nlinarith
  exfalso
  push_neg at hbk hal
  have hS1 : (ak + bl) / 2 ≤ S := by nlinarith
  have hS2 : ak * bl ≤ S ^ 2 := by nlinarith [sq_nonneg (ak - bl)]
  rw [div_le_iff₀ hy] at hQ
  nlinarith
theorem lemma122 (G : GCDGraph) (hδ : 0 < G.density) (p : ℕ) (hp : p.Prime) (hpP : p ∉ G.P)
    (hpK : K40 < p) :
    (∃ k l : ℕ, 0 < (G.restrictPrime p k l hp hpP).density ∧
        (2 : ℝ) ^ (if k ≠ l then 1 else 0) ≤
          min 1 ((G.restrictPrime p k l hp hpP).density / G.density) *
            ((G.restrictPrime p k l hp hpP).quality / G.quality)) ∨
      G.IsSharp p := by
  obtain ⟨hE, hV, hW⟩ := alt_gp_pos G hδ
  obtain ⟨k, l, hVk, hWl, hB⟩ := alt_gp_lemma121 G hδ p
  set G' := G.restrictPrime p k l hp hpP with hG'
  set E' := esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l))
    with hE'
  set Vk := wsum G.μ (vslice G.V p k) with hVkdef
  set Wl := wsum G.μ (vslice G.W p l) with hWldef
  set V := wsum G.μ G.V with hVdef
  set W := wsum G.μ G.W with hWdef
  set E := esum G.μ G.E with hEdef
  have hq : 0 < G.quality := (quality_pos_iff G).2 hδ
  have hq' := quality_restrictPrime G p k l hp hpP hE hVk hWl
  set F := (p : ℝ) ^ ((k - l) + (l - k)) /
          ((1 - (if k = l ∧ 1 ≤ k then 1 / (p : ℝ) else 0)) ^ 2 *
            (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10) with hFdef
  have hF : (p : ℝ) ^ ((k - l) + (l - k)) ≤ F := by
    apply alt_gp_F_ge p hp
    · split_ifs <;> positivity
    · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      split_ifs
      · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      · norm_num
  have hq'' : G'.quality = G.quality * (E' / E) ^ 10 * (V / Vk) ^ 9 * (W / Wl) ^ 9 * F := hq'
  have hdens : G'.density / G.density = (E' / E) / ((Vk / V) * (Wl / W)) := by
    show (E' / (Vk * Wl)) / (E / (V * W)) = _
    field_simp
  have hqual : G'.quality / G.quality =
      (E' / E) ^ 10 * (1 / (Vk / V)) ^ 9 * (1 / (Wl / W)) ^ 9 * F := by
    rw [hq'', one_div_div, one_div_div, mul_assoc, mul_assoc, mul_assoc,
      mul_div_cancel_left₀ _ hq.ne']
    ring
  have hE'E : E' ≤ E := by
    unfold E' E esum
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun i _ _ => mul_nonneg (G.μ_nonneg _) (G.μ_nonneg _))
  have hα0 : 0 < Vk / V := div_pos hVk hV
  have hβ0 : 0 < Wl / W := div_pos hWl hW
  have hα1 : Vk / V ≤ 1 := (div_le_one hV).2 (alt_gp_vslice_le G _ _ _)
  have hβ1 : Wl / W ≤ 1 := (div_le_one hW).2 (alt_gp_vslice_le G _ _ _)
  by_cases hkl : k = l
  ·
    subst hkl
    left
    refine ⟨k, k, ?_, ?_⟩
    · have hx : (Vk / V * (Wl / W)) ^ ((9 : ℝ) / 10) ≤ E' / E := by
        rw [le_div_iff₀ hE]; simpa [alt_gp_B] using hB
      have : 0 < E' := by
        have := mul_pos (Real.rpow_pos_of_pos (mul_pos hα0 hβ0) ((9 : ℝ) / 10)) hE
        have h2 := (le_div_iff₀ hE).1 hx
        linarith
      show 0 < E' / (Vk * Wl)
      positivity
    · rw [if_neg (by simp), pow_zero, hdens, hqual]
      apply alt_gp_diag _ _ _ _ hα0 hβ0 hα1 hβ1
      · rw [le_div_iff₀ hE]; simpa [alt_gp_B] using hB
      · simpa using hF
  ·
    set ak := Vk / V
    set bl := Wl / W
    set bk := wsum G.μ (vslice G.W p k) / W with hbk
    set al := wsum G.μ (vslice G.V p l) / V with hal
    have hbk0 : 0 ≤ bk := div_nonneg (alt_gp_wsum_nonneg G _) hW.le
    have hal0 : 0 ≤ al := div_nonneg (alt_gp_wsum_nonneg G _) hV.le
    have hbk1 : bk ≤ 1 := (div_le_one hW).2 (alt_gp_vslice_le G _ _ _)
    have hal1 : al ≤ 1 := (div_le_one hV).2 (alt_gp_vslice_le G _ _ _)
    have hbsum : bk + bl ≤ 1 := by
      rw [hbk, ← add_div, div_le_one hW]; exact alt_gp_two_slices G _ p k l hkl
    set S := ak * (1 - bk) + bk * (1 - ak) + (al * (1 - bl) + bl * (1 - al)) with hS
    have hSy : ak * bl ≤ S := by
      have t2 : 0 ≤ bk * (1 - ak) := mul_nonneg hbk0 (by linarith)
      have t3 : 0 ≤ al * (1 - bl) := mul_nonneg hal0 (by linarith)
      have t4 : 0 ≤ bl * (1 - al) := mul_nonneg hβ0.le (by linarith)
      have : ak * bl ≤ ak * (1 - bk) := mul_le_mul_of_nonneg_left (by linarith) hα0.le
      linarith
    have hj : 1 ≤ (k - l) + (l - k) := by omega
    have hx : S * (20 / 21 : ℝ) ^ ((k - l) + (l - k)) / 1000 ≤ E' / E := by
      rw [le_div_iff₀ hE]; simpa [alt_gp_B, hkl] using hB
    have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hkey := alt_gp_key ak bl (E' / E) S F p ((k - l) + (l - k)) hα0 hβ0 hSy hx hj hP hF
    have hE'pos : 0 < E' := by
      have h1 : 0 < S * (20 / 21 : ℝ) ^ ((k - l) + (l - k)) / 1000 := by
        have := lt_of_lt_of_le (mul_pos hα0 hβ0) hSy; positivity
      have := lt_of_lt_of_le h1 hx
      exact (div_pos_iff_of_pos_right hE).1 this
    have hdpos : 0 < G'.density := by
      show 0 < E' / (Vk * Wl)
      positivity
    by_cases hbig : (2 : ℝ) ≤ min 1 (G'.density / G.density) * (G'.quality / G.quality)
    · left
      refine ⟨k, l, hdpos, ?_⟩
      rw [if_pos hkl, pow_one]; exact hbig
    · right
      push_neg at hbig
      rw [hdens, hqual] at hbig
      have hy0 : 0 < ak * bl := mul_pos hα0 hβ0
      have hpK' : (10 : ℝ) ^ 40 < p := by simpa [K40] using hpK
      have hQ : S ^ 2 / (ak * bl) < 4 * 10 ^ 33 / p := by
        have h1 := lt_of_le_of_lt hkey hbig
        have h2 := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2 * 10 ^ 33)).1 h1
        rw [lt_div_iff₀ (by positivity)]
        linarith
      have hSQ : S ≤ S ^ 2 / (ak * bl) := by
        rw [le_div_iff₀ hy0]
        have : 0 < S := lt_of_lt_of_le hy0 hSy
        calc S * (ak * bl) ≤ S * S := mul_le_mul_of_nonneg_left hSy this.le
          _ = S ^ 2 := (sq S).symm
      have hsmall : 4 * 10 ^ 33 / (p : ℝ) ≤ 1 / 10 ^ 6 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      have hres := alt_gp_sharp_real ak bk al bl (4 * 10 ^ 33 / p) hα0.le hbk0 hal0 hβ0.le
        hα1 hbk1 hal1 hβ1 hy0 (by linarith) (by linarith) (by linarith)
      have hKp : 2 * (4 * 10 ^ 33 / (p : ℝ)) ≤ K40 / p := by
        rw [← mul_div_assoc, div_le_div_iff_of_pos_right (by positivity)]
        simp only [K40]; norm_num
      rcases hres with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨k, ?_, ?_⟩
        · have : 1 - K40 / p ≤ ak := by linarith
          calc (1 - K40 / p) * V ≤ ak * V := mul_le_mul_of_nonneg_right this hV.le
            _ = Vk := div_mul_cancel₀ _ hV.ne'
        · have : 1 - K40 / p ≤ bk := by linarith
          calc (1 - K40 / p) * W ≤ bk * W := mul_le_mul_of_nonneg_right this hW.le
            _ = wsum G.μ (vslice G.W p k) := div_mul_cancel₀ _ hW.ne'
      · refine ⟨l, ?_, ?_⟩
        · have : 1 - K40 / p ≤ al := by linarith
          calc (1 - K40 / p) * V ≤ al * V := mul_le_mul_of_nonneg_right this hV.le
            _ = wsum G.μ (vslice G.V p l) := div_mul_cancel₀ _ hV.ne'
        · have : 1 - K40 / p ≤ bl := by linarith
          calc (1 - K40 / p) * W ≤ bl * W := mul_le_mul_of_nonneg_right this hW.le
            _ = Wl := div_mul_cancel₀ _ hW.ne'
theorem prop81 (G : GCDGraph) (hδ : 0 < G.density) (hR : ∀ p ∈ G.R, T0 < (p : ℝ))
    (hflat : G.Rflat.Nonempty) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ 0 < G'.density ∧ G.P ⊂ G'.P ∧ G'.P ⊆ G.P ∪ G.R ∧
      G'.R ⊂ G.R ∧
      (2 : ℝ) ^ (newUnequal G' G) ≤ min 1 (G'.density / G.density) * (G'.quality / G.quality) := by
  classical
  obtain ⟨p, hp⟩ := hflat
  have hpR : p ∈ G.R := (mem_filter.1 hp).1
  have hns : ¬ G.IsSharp p := by
    have := (mem_filter.1 hp).2
    convert this
  have hpp : p.Prime := G.prime_of_mem_R hpR
  have hpP : p ∉ G.P := G.not_mem_P_of_mem_R hpR
  have hpK : K40 < p := by
    have h1 := hR p hpR
    have h2 : K40 < T0 := by
      simp only [K40, T0]; exact pow_lt_pow_right₀ (by norm_num) (by norm_num)
    linarith
  rcases lemma122 G hδ p hpp hpP hpK with ⟨k, l, hd, hq⟩ | hsh
  · refine ⟨G.restrictPrime p k l hpp hpP, restrictPrime_isSubgraph G p k l hpp hpP, hd, ?_, ?_,
      ?_, ?_⟩
    · exact ssubset_insert hpP
    · intro q hq
      rcases mem_insert.1 hq with rfl | hq
      · exact mem_union_right _ hpR
      · exact mem_union_left _ hq
    · refine lt_of_le_of_lt (R_restrictPrime_subset G p k l hpp hpP) ?_
      exact erase_ssubset hpR
    · have hN : newUnequal (G.restrictPrime p k l hpp hpP) G = if k ≠ l then 1 else 0 := by
        unfold newUnequal
        have hset : (insert p G.P \ G.P) = {p} := by
          ext q; simp only [mem_sdiff, mem_insert, mem_singleton]
          constructor
          · rintro ⟨h1 | h1, h2⟩
            · exact h1
            · exact absurd h1 h2
          · rintro rfl; exact ⟨Or.inl rfl, hpP⟩
        show ((insert p G.P \ G.P).filter
          (fun q => Function.update G.f p k q ≠ Function.update G.g p l q)).card = _
        rw [hset, filter_singleton, Function.update_self, Function.update_self]
        split_ifs <;> simp
      rw [hN]; exact hq
  · exact absurd hsh hns
end GCDGraph
end DuffinSchaeffer
end Port24_Parts_GenericPrimes

section Port24_Parts_SmallPrimes
open Finset
namespace DuffinSchaeffer
namespace GCDGraph
noncomputable def alt_sp_B (α β : ℕ → ℝ) (k l : ℕ) : ℝ :=
  if k = l then (α k * β k) ^ ((9 : ℝ) / 10) else
    (α k * (1 - β k) + β k * (1 - α k) + (α l * (1 - β l) + β l * (1 - α l))) *
      (20 / 21 : ℝ) ^ ((k - l) + (l - k)) / 1000
theorem alt_sp_geom_eq (m : ℕ) :
    ∑ i ∈ range m, (20 / 21 : ℝ) ^ (i + 1) = 20 * (1 - (20 / 21 : ℝ) ^ m) := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih]; ring
theorem alt_sp_geom_le (m : ℕ) : ∑ i ∈ range m, (20 / 21 : ℝ) ^ (i + 1) ≤ 20 := by
  rw [alt_sp_geom_eq]
  have : (0 : ℝ) ≤ (20 / 21 : ℝ) ^ m := by positivity
  linarith
theorem alt_sp_offdiag (n k : ℕ) :
    ∑ l ∈ range n, (if k = l then (0 : ℝ) else (20 / 21 : ℝ) ^ ((k - l) + (l - k))) ≤ 40 := by
  have hpt : ∀ l ∈ range n, (if k = l then (0 : ℝ) else (20 / 21 : ℝ) ^ ((k - l) + (l - k))) ≤
      (if l < k then (20 / 21 : ℝ) ^ (k - l) else 0) +
        (if k < l then (20 / 21 : ℝ) ^ (l - k) else 0) := by
    intro l _
    rcases lt_trichotomy l k with h | h | h
    · rw [if_neg (by omega), if_pos h, if_neg (by omega), add_zero]
      have : l - k = 0 := by omega
      rw [this, add_zero]
    · subst h; simp
    · rw [if_neg (by omega), if_neg (by omega), if_pos h, zero_add]
      have : k - l = 0 := by omega
      rw [this, zero_add]
  refine (sum_le_sum hpt).trans ?_
  rw [sum_add_distrib, ← sum_filter, ← sum_filter]
  have h1 : ∑ l ∈ (range n).filter (fun l => l < k), (20 / 21 : ℝ) ^ (k - l) ≤ 20 := by
    have hsub : (range n).filter (fun l => l < k) ⊆ range k := by
      intro l hl; simp only [mem_filter, mem_range] at hl ⊢; exact hl.2
    refine (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans ?_
    rw [← sum_range_reflect]
    refine le_of_eq_of_le (sum_congr rfl ?_) (alt_sp_geom_le k)
    intro j hj
    simp only [mem_range] at hj
    congr 1
    omega
  have h2 : ∑ l ∈ (range n).filter (fun l => k < l), (20 / 21 : ℝ) ^ (l - k) ≤ 20 := by
    have hset : (range n).filter (fun l => k < l) = Ico (k + 1) n := by
      ext l; simp only [mem_filter, mem_range, mem_Ico]; omega
    rw [hset, sum_Ico_eq_sum_range]
    refine le_of_eq_of_le (sum_congr rfl ?_) (alt_sp_geom_le (n - (k + 1)))
    intro j _
    congr 1
    omega
  linarith
theorem alt_sp_sqrt_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a * b) ^ ((1 : ℝ) / 2) ≤ (a + b) / 2 := by
  rw [Real.mul_rpow ha hb]
  have := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 / 2) (w₂ := 1 / 2) (p₁ := a) (p₂ := b)
    (by norm_num) (by norm_num) ha hb (by norm_num)
  linarith
theorem alt_sp_sum_bound (n : ℕ) (α β : ℕ → ℝ) (hα0 : ∀ k, 0 ≤ α k) (hβ0 : ∀ k, 0 ≤ β k)
    (hα : ∑ k ∈ range n, α k = 1) (hβ : ∑ k ∈ range n, β k = 1) :
    ∑ k ∈ range n, ∑ l ∈ range n, alt_sp_B α β k l ≤ 1 := by
  have hα1 : ∀ k ∈ range n, α k ≤ 1 := fun k hk => by
    rw [← hα]; exact single_le_sum (fun i _ => hα0 i) hk
  have hβ1 : ∀ k ∈ range n, β k ≤ 1 := fun k hk => by
    rw [← hβ]; exact single_le_sum (fun i _ => hβ0 i) hk
  have hn : (range n).Nonempty := by
    rw [nonempty_iff_ne_empty]; intro h; rw [h, sum_empty] at hα; norm_num at hα
  set A : ℕ → ℝ := fun k => α k * (1 - β k) + β k * (1 - α k) with hA
  set e : ℕ → ℕ → ℝ := fun k l =>
    if k = l then (0 : ℝ) else (20 / 21 : ℝ) ^ ((k - l) + (l - k)) with he
  have hA0 : ∀ k ∈ range n, 0 ≤ A k := fun k hk => by
    have := hα1 k hk; have := hβ1 k hk; have := hα0 k; have := hβ0 k
    simp only [hA]; nlinarith
  have he0 : ∀ k l, 0 ≤ e k l := fun k l => by simp only [he]; split_ifs <;> positivity
  have hesymm : ∀ k l, e k l = e l k := fun k l => by
    simp only [he]
    by_cases h : k = l
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h), add_comm]
  have hB : ∀ k l, alt_sp_B α β k l =
      (if k = l then (α k * β k) ^ ((9 : ℝ) / 10) else 0) +
        (A k * e k l / 1000 + A l * e k l / 1000) := fun k l => by
    simp only [alt_sp_B, hA, he]
    split_ifs <;> ring
  simp_rw [hB, sum_add_distrib]
  rw [sum_comm (f := fun k l => A l * e k l / 1000)]
  have hdiag : ∀ k ∈ range n, ∑ l ∈ range n, (if k = l then (α k * β k) ^ ((9 : ℝ) / 10) else 0)
      = (α k * β k) ^ ((9 : ℝ) / 10) := fun k hk => by rw [sum_ite_eq, if_pos hk]
  rw [sum_congr rfl hdiag]
  have hoff1 : ∀ k ∈ range n, ∑ l ∈ range n, A k * e k l / 1000 ≤ A k * 40 / 1000 := by
    intro k hk
    rw [← sum_div, ← mul_sum]
    gcongr
    · exact hA0 k hk
    · exact alt_sp_offdiag n k
  have hoff2 : ∀ l ∈ range n, ∑ k ∈ range n, A l * e k l / 1000 ≤ A l * 40 / 1000 := by
    intro l hl
    simp_rw [hesymm _ l]
    exact hoff1 l hl
  have hS2 := add_le_add (sum_le_sum hoff1) (sum_le_sum hoff2)
  set D := ∑ k ∈ range n, α k * β k with hD
  have hsumA : ∑ k ∈ range n, A k * 40 / 1000 = (2 - 2 * D) * 40 / 1000 := by
    rw [← sum_div, ← sum_mul]
    congr 2
    simp only [hA, hD, mul_sub, mul_one, sum_add_distrib, sum_sub_distrib, hα, hβ]
    rw [show ∑ i ∈ range n, β i * α i = ∑ i ∈ range n, α i * β i from
      sum_congr rfl fun i _ => mul_comm _ _]
    ring
  obtain ⟨k0, hk0, hmax⟩ := exists_max_image (range n) (fun k => α k * β k) hn
  set γ := α k0 * β k0 with hγ
  have hγ0 : 0 ≤ γ := mul_nonneg (hα0 k0) (hβ0 k0)
  have hγ1 : γ ≤ 1 := by
    have := hα1 k0 hk0; have := hβ1 k0 hk0
    calc γ = α k0 * β k0 := rfl
      _ ≤ 1 * 1 := mul_le_mul (hα1 k0 hk0) (hβ1 k0 hk0) (hβ0 k0) zero_le_one
      _ = 1 := by norm_num
  have hDγ : γ ≤ D := single_le_sum (f := fun k => α k * β k)
    (fun i _ => mul_nonneg (hα0 i) (hβ0 i)) hk0
  have hS1 : ∑ k ∈ range n, (α k * β k) ^ ((9 : ℝ) / 10) ≤ γ ^ ((2 : ℝ) / 5) := by
    have hpt : ∀ k ∈ range n, (α k * β k) ^ ((9 : ℝ) / 10) ≤
        γ ^ ((2 : ℝ) / 5) * ((α k + β k) / 2) := by
      intro k hk
      have hx0 : 0 ≤ α k * β k := mul_nonneg (hα0 k) (hβ0 k)
      rw [show (9 : ℝ) / 10 = 2 / 5 + 1 / 2 by norm_num, Real.rpow_add' hx0 (by norm_num)]
      exact mul_le_mul (Real.rpow_le_rpow hx0 (hmax k hk) (by norm_num))
        (alt_sp_sqrt_le _ _ (hα0 k) (hβ0 k)) (by positivity) (by positivity)
    refine (sum_le_sum hpt).trans (le_of_eq ?_)
    rw [← mul_sum, ← sum_div, sum_add_distrib, hα, hβ]
    norm_num
  have hbern : γ ^ ((2 : ℝ) / 5) ≤ 1 + 2 / 5 * (γ - 1) := by
    have := _root_.rpow_one_add_le_one_add_mul_self (s := γ - 1) (by linarith)
      (p := (2 : ℝ) / 5) (by norm_num) (by norm_num)
    simpa using this
  linarith
theorem alt_sp_pos (G : GCDGraph) (hδ : 0 < G.density) :
    0 < esum G.μ G.E ∧ 0 < wsum G.μ G.V ∧ 0 < wsum G.μ G.W := by
  have hV0 : 0 ≤ wsum G.μ G.V := sum_nonneg fun i _ => G.μ_nonneg i
  have hW0 : 0 ≤ wsum G.μ G.W := sum_nonneg fun i _ => G.μ_nonneg i
  unfold density at hδ
  have hVW : wsum G.μ G.V * wsum G.μ G.W ≠ 0 := by
    intro h; rw [h, div_zero] at hδ; exact lt_irrefl _ hδ
  have hVW' : 0 < wsum G.μ G.V * wsum G.μ G.W :=
    lt_of_le_of_ne (mul_nonneg hV0 hW0) (Ne.symm hVW)
  refine ⟨(div_pos_iff_of_pos_right hVW').1 hδ,
    lt_of_le_of_ne hV0 (fun h => hVW (by rw [← h, zero_mul])),
    lt_of_le_of_ne hW0 (fun h => hVW (by rw [← h, mul_zero]))⟩
theorem alt_sp_wsum_nonneg (G : GCDGraph) (S : Finset ℕ) : 0 ≤ wsum G.μ S :=
  sum_nonneg fun i _ => G.μ_nonneg i
theorem alt_sp_esum_nonneg (G : GCDGraph) (S : Finset (ℕ × ℕ)) : 0 ≤ esum G.μ S :=
  sum_nonneg fun i _ => mul_nonneg (G.μ_nonneg _) (G.μ_nonneg _)
theorem alt_sp_vslice_le (G : GCDGraph) (S : Finset ℕ) (p k : ℕ) :
    wsum G.μ (vslice S p k) ≤ wsum G.μ S :=
  sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => G.μ_nonneg i)
theorem alt_sp_two_slices (G : GCDGraph) (S : Finset ℕ) (p k l : ℕ) (hkl : k ≠ l) :
    wsum G.μ (vslice S p k) + wsum G.μ (vslice S p l) ≤ wsum G.μ S := by
  unfold wsum vslice
  rw [← sum_union (disjoint_filter.2 (fun v _ h1 h2 => hkl (h1.symm.trans h2)))]
  exact sum_le_sum_of_subset_of_nonneg (union_subset (filter_subset _ _) (filter_subset _ _))
    (fun i _ _ => G.μ_nonneg i)
theorem alt_sp_wsum_partition (G : GCDGraph) (S : Finset ℕ) (p N : ℕ)
    (hN : ∀ v ∈ S, v.factorization p ≤ N) :
    ∑ k ∈ range (N + 1), wsum G.μ (vslice S p k) = wsum G.μ S := by
  unfold wsum vslice
  exact sum_fiberwise_of_maps_to (fun v hv => mem_range.2 (Nat.lt_succ_of_le (hN v hv))) G.μ
theorem alt_sp_esum_partition (G : GCDGraph) (p N : ℕ)
    (hN : ∀ e ∈ G.E, e.1.factorization p ≤ N ∧ e.2.factorization p ≤ N) :
    ∑ k ∈ range (N + 1), ∑ l ∈ range (N + 1),
      esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l)) =
      esum G.μ G.E := by
  rw [← sum_product' (f := fun k l =>
    esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l)))]
  have h := sum_fiberwise_of_maps_to (s := G.E) (t := range (N + 1) ×ˢ range (N + 1))
    (g := fun e : ℕ × ℕ => (e.1.factorization p, e.2.factorization p))
    (fun e he => mem_product.2 ⟨mem_range.2 (Nat.lt_succ_of_le (hN e he).1),
      mem_range.2 (Nat.lt_succ_of_le (hN e he).2)⟩) (fun e => G.μ e.1 * G.μ e.2)
  unfold esum
  rw [← h]
  refine sum_congr rfl fun x _ => sum_congr ?_ fun _ _ => rfl
  ext e
  simp [Prod.ext_iff]
theorem alt_sp_esum_slice_le (G : GCDGraph) (p k l : ℕ) :
    esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l)) ≤
      wsum G.μ (vslice G.V p k) * wsum G.μ (vslice G.W p l) := by
  have hsub : G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l) ⊆
      vslice G.V p k ×ˢ vslice G.W p l := by
    intro e he
    obtain ⟨he, h1, h2⟩ := mem_filter.1 he
    obtain ⟨hv, hw⟩ := mem_product.1 (G.E_sub he)
    exact mem_product.2 ⟨mem_filter.2 ⟨hv, h1⟩, mem_filter.2 ⟨hw, h2⟩⟩
  unfold esum wsum
  rw [sum_mul_sum, ← sum_product']
  exact sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ => mul_nonneg (G.μ_nonneg _) (G.μ_nonneg _))
theorem alt_sp_B_nonneg (α β : ℕ → ℝ) (hα0 : ∀ k, 0 ≤ α k) (hβ0 : ∀ k, 0 ≤ β k)
    (hα1 : ∀ k, α k ≤ 1) (hβ1 : ∀ k, β k ≤ 1) (k l : ℕ) : 0 ≤ alt_sp_B α β k l := by
  unfold alt_sp_B
  split_ifs
  · exact Real.rpow_nonneg (mul_nonneg (hα0 k) (hβ0 k)) _
  · have := hα0 k; have := hβ0 k; have := hα1 k; have := hβ1 k
    have := hα0 l; have := hβ0 l; have := hα1 l; have := hβ1 l
    have h1 : 0 ≤ α k * (1 - β k) + β k * (1 - α k) + (α l * (1 - β l) + β l * (1 - α l)) := by
      nlinarith
    positivity
theorem alt_sp_lemma121 (G : GCDGraph) (hδ : 0 < G.density) (p : ℕ) :
    ∃ k l : ℕ, 0 < wsum G.μ (vslice G.V p k) ∧ 0 < wsum G.μ (vslice G.W p l) ∧
      alt_sp_B (fun k => wsum G.μ (vslice G.V p k) / wsum G.μ G.V)
          (fun l => wsum G.μ (vslice G.W p l) / wsum G.μ G.W) k l * esum G.μ G.E ≤
        esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l)) := by
  obtain ⟨hE, hV, hW⟩ := alt_sp_pos G hδ
  set N := (G.V ∪ G.W).sup (fun v => v.factorization p) with hNdef
  have hNV : ∀ v ∈ G.V, v.factorization p ≤ N := fun v hv =>
    le_sup (f := fun v => v.factorization p) (mem_union_left _ hv)
  have hNW : ∀ v ∈ G.W, v.factorization p ≤ N := fun v hv =>
    le_sup (f := fun v => v.factorization p) (mem_union_right _ hv)
  have hNE : ∀ e ∈ G.E, e.1.factorization p ≤ N ∧ e.2.factorization p ≤ N := fun e he => by
    obtain ⟨hv, hw⟩ := mem_product.1 (G.E_sub he)
    exact ⟨hNV _ hv, hNW _ hw⟩
  set α : ℕ → ℝ := fun k => wsum G.μ (vslice G.V p k) / wsum G.μ G.V with hα
  set β : ℕ → ℝ := fun l => wsum G.μ (vslice G.W p l) / wsum G.μ G.W with hβ
  have hα0 : ∀ k, 0 ≤ α k := fun k => div_nonneg (alt_sp_wsum_nonneg G _) hV.le
  have hβ0 : ∀ k, 0 ≤ β k := fun k => div_nonneg (alt_sp_wsum_nonneg G _) hW.le
  have hα1 : ∀ k, α k ≤ 1 := fun k => (div_le_one hV).2 (alt_sp_vslice_le G _ _ _)
  have hβ1 : ∀ k, β k ≤ 1 := fun k => (div_le_one hW).2 (alt_sp_vslice_le G _ _ _)
  have hαs : ∑ k ∈ range (N + 1), α k = 1 := by
    simp only [hα]; rw [← sum_div, alt_sp_wsum_partition G _ p N hNV, div_self hV.ne']
  have hβs : ∑ k ∈ range (N + 1), β k = 1 := by
    simp only [hβ]; rw [← sum_div, alt_sp_wsum_partition G _ p N hNW, div_self hW.ne']
  have hsum := alt_sp_sum_bound (N + 1) α β hα0 hβ0 hαs hβs
  by_contra hcon
  push_neg at hcon
  set Ekl : ℕ → ℕ → ℝ := fun k l =>
    esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l)) with hEkl
  have hle : ∀ x ∈ range (N + 1) ×ˢ range (N + 1),
      Ekl x.1 x.2 ≤ alt_sp_B α β x.1 x.2 * esum G.μ G.E := by
    intro x _
    by_cases h : 0 < wsum G.μ (vslice G.V p x.1) ∧ 0 < wsum G.μ (vslice G.W p x.2)
    · exact (hcon x.1 x.2 h.1 h.2).le
    · have h0 : wsum G.μ (vslice G.V p x.1) * wsum G.μ (vslice G.W p x.2) = 0 := by
        rcases not_and_or.1 h with h | h
        · rw [le_antisymm (not_lt.1 h) (alt_sp_wsum_nonneg G _), zero_mul]
        · rw [le_antisymm (not_lt.1 h) (alt_sp_wsum_nonneg G _), mul_zero]
      calc Ekl x.1 x.2 ≤ _ := alt_sp_esum_slice_le G p x.1 x.2
        _ = 0 := h0
        _ ≤ _ := mul_nonneg (alt_sp_B_nonneg α β hα0 hβ0 hα1 hβ1 _ _) hE.le
  have hpart : ∑ x ∈ range (N + 1) ×ˢ range (N + 1), Ekl x.1 x.2 = esum G.μ G.E := by
    rw [sum_product' (f := Ekl)]; exact alt_sp_esum_partition G p N hNE
  have hex : ∃ x ∈ range (N + 1) ×ˢ range (N + 1), (0 : ℝ) < Ekl x.1 x.2 := by
    apply exists_lt_of_sum_lt
    rw [hpart, sum_const_zero]; exact hE
  obtain ⟨x, hx, hxpos⟩ := hex
  have hlt : ∃ x ∈ range (N + 1) ×ˢ range (N + 1),
      Ekl x.1 x.2 < alt_sp_B α β x.1 x.2 * esum G.μ G.E := by
    refine ⟨x, hx, hcon x.1 x.2 ?_ ?_⟩
    · by_contra h0
      have h0' := le_antisymm (not_lt.1 h0) (alt_sp_wsum_nonneg G _)
      have := alt_sp_esum_slice_le G p x.1 x.2
      rw [h0', zero_mul] at this
      exact absurd hxpos (not_lt.2 this)
    · by_contra h0
      have h0' := le_antisymm (not_lt.1 h0) (alt_sp_wsum_nonneg G _)
      have := alt_sp_esum_slice_le G p x.1 x.2
      rw [h0', mul_zero] at this
      exact absurd hxpos (not_lt.2 this)
  have := sum_lt_sum hle hlt
  rw [hpart, ← sum_mul, sum_product' (f := fun k l => alt_sp_B α β k l)] at this
  have h2 := mul_le_mul_of_nonneg_right hsum hE.le
  linarith
theorem alt_sp_F_ge (p : ℕ) (hp : p.Prime) (j : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2) :
    (p : ℝ) ^ j ≤ (p : ℝ) ^ j / ((1 - c) ^ 2 * (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpr : (p : ℝ) ≤ (p : ℝ) ^ ((31 : ℝ) / 30) := by
    conv_lhs => rw [← Real.rpow_one (p : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hq0 : 0 < 1 / (p : ℝ) ^ ((31 : ℝ) / 30) := by positivity
  have hq1 : 1 / (p : ℝ) ^ ((31 : ℝ) / 30) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  apply le_div_self (by positivity)
  · apply mul_pos
    · apply pow_pos; linarith
    · apply pow_pos; linarith
  · calc (1 - c) ^ 2 * (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10 ≤ 1 * 1 := by
          apply mul_le_mul _ _ (by apply pow_nonneg; linarith) zero_le_one
          · apply pow_le_one₀ <;> linarith
          · apply pow_le_one₀ <;> linarith
      _ = 1 := by norm_num
theorem alt_sp_key (a b x S F P : ℝ) (j : ℕ) (ha : 0 < a) (hb : 0 < b) (hSy : a * b ≤ S)
    (hx : S * (20 / 21 : ℝ) ^ j / 1000 ≤ x) (hj : 1 ≤ j) (hP : 2 ≤ P) (hF : P ^ j ≤ F) :
    S ^ 2 / (a * b) * P / (2 * 10 ^ 33) ≤
      min 1 (x / (a * b)) * (x ^ 10 * (1 / a) ^ 9 * (1 / b) ^ 9 * F) := by
  set y := a * b with hy
  have hy0 : 0 < y := mul_pos ha hb
  have hS0 : 0 < S := lt_of_lt_of_le hy0 hSy
  set t : ℝ := (20 / 21 : ℝ) ^ j / 1000 with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    have : (20 / 21 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    rw [ht]; linarith
  have hxS : S * t ≤ x := by rw [ht, ← mul_div_assoc]; exact hx
  have hx0 : 0 < x := lt_of_lt_of_le (mul_pos hS0 ht0) hxS
  have hmin : t ≤ min 1 (x / y) := by
    apply le_min ht1
    rw [le_div_iff₀ hy0]
    calc t * y ≤ t * S := mul_le_mul_of_nonneg_left hSy ht0.le
      _ = S * t := mul_comm _ _
      _ ≤ x := hxS
  have hab : (1 / a) ^ 9 * (1 / b) ^ 9 = 1 / y ^ 9 := by
    rw [hy, mul_pow, one_div_pow, one_div_pow, one_div_mul_one_div]
  have hF0 : 0 < F := lt_of_lt_of_le (by positivity) hF
  have h10 : (S * t) ^ 10 ≤ x ^ 10 := pow_le_pow_left₀ (by positivity) hxS 10
  have hS8 : y ^ 8 ≤ S ^ 8 := pow_le_pow_left₀ hy0.le hSy 8
  have htP : P / (2 * 10 ^ 33) ≤ t ^ 11 * P ^ j := by
    have hr : (1 : ℝ) / 2 ≤ (20 / 21 : ℝ) ^ 11 := by norm_num
    have hbase : 1 ≤ (20 / 21 : ℝ) ^ 11 * P := by nlinarith
    have hpow : (20 / 21 : ℝ) ^ 11 * P ≤ ((20 / 21 : ℝ) ^ 11 * P) ^ j := by
      conv_lhs => rw [← pow_one ((20 / 21 : ℝ) ^ 11 * P)]
      exact pow_le_pow_right₀ hbase hj
    have : t ^ 11 * P ^ j = ((20 / 21 : ℝ) ^ 11 * P) ^ j / 10 ^ 33 := by
      rw [ht, div_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm j 11]; ring
    rw [this, le_div_iff₀ (by norm_num)]
    have : P / (2 * 10 ^ 33) * 10 ^ 33 = (1 / 2) * P := by ring
    rw [this]
    nlinarith
  have hmain : t * (x ^ 10 * (1 / y ^ 9) * F) ≥ t ^ 11 * P ^ j * (S ^ 2 / y) := by
    have h1 : x ^ 10 * (1 / y ^ 9) * F ≥ (S * t) ^ 10 * (1 / y ^ 9) * P ^ j := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right h10 (by positivity)) hF (by positivity)
        (by positivity)
    have h2 : (S * t) ^ 10 * (1 / y ^ 9) * P ^ j ≥ t ^ 10 * P ^ j * (S ^ 2 / y) := by
      have : S ^ 2 / y ≤ S ^ 10 * (1 / y ^ 9) := by
        rw [div_le_iff₀ hy0]
        have e : S ^ 10 * (1 / y ^ 9) * y = S ^ 2 * (S ^ 8 / y ^ 8) := by
          field_simp
        rw [e]
        have : 1 ≤ S ^ 8 / y ^ 8 := by rw [le_div_iff₀ (by positivity)]; linarith
        nlinarith [sq_nonneg S]
      calc t ^ 10 * P ^ j * (S ^ 2 / y) ≤ t ^ 10 * P ^ j * (S ^ 10 * (1 / y ^ 9)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = (S * t) ^ 10 * (1 / y ^ 9) * P ^ j := by ring
    calc t ^ 11 * P ^ j * (S ^ 2 / y) = t * (t ^ 10 * P ^ j * (S ^ 2 / y)) := by ring
      _ ≤ t * ((S * t) ^ 10 * (1 / y ^ 9) * P ^ j) := mul_le_mul_of_nonneg_left h2 ht0.le
      _ ≤ t * (x ^ 10 * (1 / y ^ 9) * F) := mul_le_mul_of_nonneg_left h1 ht0.le
  have hval : min 1 (x / y) * (x ^ 10 * (1 / a) ^ 9 * (1 / b) ^ 9 * F) =
      min 1 (x / y) * (x ^ 10 * (1 / y ^ 9) * F) := by
    rw [mul_assoc (x ^ 10), hab]
  rw [hval]
  have hnn : 0 ≤ x ^ 10 * (1 / y ^ 9) * F := by positivity
  calc S ^ 2 / y * P / (2 * 10 ^ 33) = P / (2 * 10 ^ 33) * (S ^ 2 / y) := by ring
    _ ≤ t ^ 11 * P ^ j * (S ^ 2 / y) :=
        mul_le_mul_of_nonneg_right htP (by positivity)
    _ ≤ t * (x ^ 10 * (1 / y ^ 9) * F) := hmain
    _ ≤ min 1 (x / y) * (x ^ 10 * (1 / y ^ 9) * F) := mul_le_mul_of_nonneg_right hmin hnn
theorem alt_sp_diag (a b x F : ℝ) (ha : 0 < a) (hb : 0 < b) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hx : (a * b) ^ ((9 : ℝ) / 10) ≤ x) (hF : 1 ≤ F) :
    1 ≤ min 1 (x / (a * b)) * (x ^ 10 * (1 / a) ^ 9 * (1 / b) ^ 9 * F) := by
  set y := a * b with hy
  have hy0 : 0 < y := mul_pos ha hb
  have hy1 : y ≤ 1 := by
    calc y = a * b := rfl
      _ ≤ 1 * 1 := mul_le_mul ha1 hb1 hb.le zero_le_one
      _ = 1 := by norm_num
  have hyx : y ≤ x := by
    refine le_trans ?_ hx
    conv_lhs => rw [← Real.rpow_one y]
    exact Real.rpow_le_rpow_of_exponent_ge hy0 hy1 (by norm_num)
  have hmin : min 1 (x / y) = 1 := by
    rw [min_eq_left]; rw [le_div_iff₀ hy0]; linarith
  have hab : (1 / a) ^ 9 * (1 / b) ^ 9 = 1 / y ^ 9 := by
    rw [hy, mul_pow, one_div_pow, one_div_pow, one_div_mul_one_div]
  rw [hmin, one_mul, mul_assoc (x ^ 10), hab]
  have hx10 : y ^ 9 ≤ x ^ 10 := by
    have h1 : ((y ^ ((9 : ℝ) / 10)) ^ (10 : ℕ)) = y ^ 9 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]; norm_num
    rw [← h1]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hy0.le _) hx 10
  have : 1 ≤ x ^ 10 * (1 / y ^ 9) := by
    rw [mul_one_div, le_div_iff₀ (by positivity)]; linarith
  nlinarith
theorem alt_sp_sharp_real (ak bk al bl η : ℝ) (hak0 : 0 ≤ ak) (hbk0 : 0 ≤ bk) (hal0 : 0 ≤ al)
    (hbl0 : 0 ≤ bl) (hak1 : ak ≤ 1) (hbk1 : bk ≤ 1) (hal1 : al ≤ 1) (hbl1 : bl ≤ 1)
    (hy : 0 < ak * bl)
    (hQ : (ak * (1 - bk) + bk * (1 - ak) + (al * (1 - bl) + bl * (1 - al))) ^ 2 / (ak * bl) ≤ 1 / 5)
    (hS : ak * (1 - bk) + bk * (1 - ak) + (al * (1 - bl) + bl * (1 - al)) ≤ η)
    (hη : 2 * η ≤ 1 / 2) :
    (1 - ak ≤ 2 * η ∧ 1 - bk ≤ 2 * η) ∨ (1 - al ≤ 2 * η ∧ 1 - bl ≤ 2 * η) := by
  set S := ak * (1 - bk) + bk * (1 - ak) + (al * (1 - bl) + bl * (1 - al)) with hSdef
  have t1 : 0 ≤ ak * (1 - bk) := mul_nonneg hak0 (by linarith)
  have t2 : 0 ≤ bk * (1 - ak) := mul_nonneg hbk0 (by linarith)
  have t3 : 0 ≤ al * (1 - bl) := mul_nonneg hal0 (by linarith)
  have t4 : 0 ≤ bl * (1 - al) := mul_nonneg hbl0 (by linarith)
  by_cases hbk : 1 / 2 ≤ bk
  · left
    have h1 : 1 - ak ≤ 2 * η := by nlinarith
    refine ⟨h1, ?_⟩
    have : 1 / 2 ≤ ak := by linarith
    nlinarith
  by_cases hal : 1 / 2 ≤ al
  · right
    have h1 : 1 - bl ≤ 2 * η := by nlinarith
    refine ⟨?_, h1⟩
    have : 1 / 2 ≤ bl := by linarith
    nlinarith
  exfalso
  push_neg at hbk hal
  have hS1 : (ak + bl) / 2 ≤ S := by nlinarith
  have hS2 : ak * bl ≤ S ^ 2 := by nlinarith [sq_nonneg (ak - bl)]
  rw [div_le_iff₀ hy] at hQ
  nlinarith
theorem alt_sp_density_nonneg (G : GCDGraph) : 0 ≤ G.density :=
  div_nonneg (alt_sp_esum_nonneg G _) (mul_nonneg (alt_sp_wsum_nonneg G _) (alt_sp_wsum_nonneg G _))
theorem alt_sp_ratio_ge (d d' q q' c : ℝ) (h1 : c ≤ q' / q) (h2 : c ≤ d' / d * (q' / q)) :
    c ≤ min 1 (d' / d) * (q' / q) := by
  rcases le_total 1 (d' / d) with h | h
  · rw [min_eq_left h, one_mul]; exact h1
  · rw [min_eq_right h]; exact h2
theorem alt_sp_ratio_mono (d d1 d' q q1 q' : ℝ) (hd : 0 < d) (hq : 0 < q) (hdd1 : d ≤ d1)
    (hqq1 : q ≤ q1) (hd' : 0 ≤ d') (hq' : 0 ≤ q') :
    min 1 (d' / d1) * (q' / q1) ≤ min 1 (d' / d) * (q' / q) := by
  have h1 : d' / d1 ≤ d' / d := div_le_div_of_nonneg_left hd' hd hdd1
  have h2 : q' / q1 ≤ q' / q := div_le_div_of_nonneg_left hq' hq hqq1
  exact mul_le_mul (min_le_min_left _ h1) h2 (div_nonneg hq' (hq.trans_le hqq1).le)
    (le_min zero_le_one (div_nonneg hd' hd.le))
theorem alt_sp_ratio_chain (d0 d1 d2 q0 q1 q2 : ℝ) (hd0 : 0 < d0) (hd1 : 0 < d1) (hd2 : 0 ≤ d2)
    (hq0 : 0 < q0) (hq1 : 0 < q1) (hq2 : 0 ≤ q2) :
    (min 1 (d2 / d1) * (q2 / q1)) * (min 1 (d1 / d0) * (q1 / q0)) ≤
      min 1 (d2 / d0) * (q2 / q0) := by
  have ha : 0 ≤ d2 / d1 := div_nonneg hd2 hd1.le
  have hb : 0 ≤ d1 / d0 := div_nonneg hd1.le hd0.le
  have hmin : min 1 (d2 / d1) * min 1 (d1 / d0) ≤ min 1 (d2 / d0) := by
    have e : d2 / d0 = (d2 / d1) * (d1 / d0) := by field_simp
    rw [e]
    apply le_min
    · calc min 1 (d2 / d1) * min 1 (d1 / d0) ≤ 1 * 1 :=
            mul_le_mul (min_le_left _ _) (min_le_left _ _) (le_min zero_le_one hb) zero_le_one
        _ = 1 := one_mul 1
    · exact mul_le_mul (min_le_right _ _) (min_le_right _ _) (le_min zero_le_one hb) ha
  have e2 : q2 / q0 = (q2 / q1) * (q1 / q0) := by field_simp
  rw [e2]
  calc (min 1 (d2 / d1) * (q2 / q1)) * (min 1 (d1 / d0) * (q1 / q0)) =
      (min 1 (d2 / d1) * min 1 (d1 / d0)) * ((q2 / q1) * (q1 / q0)) := by ring
    _ ≤ min 1 (d2 / d0) * ((q2 / q1) * (q1 / q0)) :=
        mul_le_mul_of_nonneg_right hmin (by positivity)
theorem alt_sp_esum_le_prod (G : GCDGraph) (V' W' : Finset ℕ) (E' : Finset (ℕ × ℕ))
    (h : E' ⊆ V' ×ˢ W') : esum G.μ E' ≤ wsum G.μ V' * wsum G.μ W' := by
  unfold esum wsum
  rw [sum_mul_sum, ← sum_product']
  exact sum_le_sum_of_subset_of_nonneg h (fun i _ _ => mul_nonneg (G.μ_nonneg _) (G.μ_nonneg _))
theorem alt_sp_esum_nbhd (G : GCDGraph) (S : Finset ℕ) (hS : S ⊆ G.V) :
    esum G.μ (G.E.filter (fun e => e.1 ∈ S)) = ∑ v ∈ S, G.μ v * wsum G.μ (G.nbhdV v) := by
  unfold esum wsum nbhdV
  have h1 : ∀ v ∈ S, G.μ v * ∑ w ∈ G.W.filter (fun w => (v, w) ∈ G.E), G.μ w =
      ∑ w ∈ G.W, if (v, w) ∈ G.E then G.μ v * G.μ w else 0 := by
    intro v _
    rw [mul_sum, sum_filter]
  rw [sum_congr rfl h1, ← sum_product' (f := fun v w => if (v, w) ∈ G.E then G.μ v * G.μ w else 0)]
  rw [← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext e
  simp only [mem_filter, mem_product]
  constructor
  · rintro ⟨he, hs⟩
    exact ⟨⟨hs, (mem_product.1 (G.E_sub he)).2⟩, he⟩
  · rintro ⟨⟨hs, _⟩, he⟩
    exact ⟨he, hs⟩
theorem lemma131 (G : GCDGraph) (hδ : 0 < G.density) (p : ℕ) (hp : p.Prime) (hpP : p ∉ G.P) :
    (∃ k l : ℕ, 0 < (G.restrictPrime p k l hp hpP).density ∧
        1 / (10 : ℝ) ^ (40 : ℕ) ≤
          min 1 ((G.restrictPrime p k l hp hpP).density / G.density) *
            ((G.restrictPrime p k l hp hpP).quality / G.quality)) ∨
      ∃ k : ℕ, 9 / 10 * wsum G.μ G.V ≤ wsum G.μ (vslice G.V p k) ∧
        9 / 10 * wsum G.μ G.W ≤ wsum G.μ (vslice G.W p k) := by
  obtain ⟨hE, hV, hW⟩ := alt_sp_pos G hδ
  obtain ⟨k, l, hVk, hWl, hB⟩ := alt_sp_lemma121 G hδ p
  have hq : 0 < G.quality := (quality_pos_iff G).2 hδ
  have hq' := quality_restrictPrime G p k l hp hpP hE hVk hWl
  set G' := G.restrictPrime p k l hp hpP with hG'
  set E' := esum G.μ (G.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = l))
    with hE'
  set Vk := wsum G.μ (vslice G.V p k) with hVkdef
  set Wl := wsum G.μ (vslice G.W p l) with hWldef
  set V := wsum G.μ G.V with hVdef
  set W := wsum G.μ G.W with hWdef
  set E := esum G.μ G.E with hEdef
  set F := (p : ℝ) ^ ((k - l) + (l - k)) /
          ((1 - (if k = l ∧ 1 ≤ k then 1 / (p : ℝ) else 0)) ^ 2 *
            (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10) with hFdef
  have hF : (p : ℝ) ^ ((k - l) + (l - k)) ≤ F := by
    apply alt_sp_F_ge p hp
    · split_ifs <;> positivity
    · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      split_ifs
      · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      · norm_num
  have hq'' : G'.quality = G.quality * (E' / E) ^ 10 * (V / Vk) ^ 9 * (W / Wl) ^ 9 * F := hq'
  have hdens : G'.density / G.density = (E' / E) / ((Vk / V) * (Wl / W)) := by
    show (E' / (Vk * Wl)) / (E / (V * W)) = _
    field_simp
  have hqual : G'.quality / G.quality =
      (E' / E) ^ 10 * (1 / (Vk / V)) ^ 9 * (1 / (Wl / W)) ^ 9 * F := by
    rw [hq'', one_div_div, one_div_div, mul_assoc, mul_assoc, mul_assoc,
      mul_div_cancel_left₀ _ hq.ne']
    ring
  have hα0 : 0 < Vk / V := div_pos hVk hV
  have hβ0 : 0 < Wl / W := div_pos hWl hW
  have hα1 : Vk / V ≤ 1 := (div_le_one hV).2 (alt_sp_vslice_le G _ _ _)
  have hβ1 : Wl / W ≤ 1 := (div_le_one hW).2 (alt_sp_vslice_le G _ _ _)
  by_cases hkl : k = l
  ·
    subst hkl
    left
    refine ⟨k, k, ?_, ?_⟩
    · have hx : (Vk / V * (Wl / W)) ^ ((9 : ℝ) / 10) ≤ E' / E := by
        rw [le_div_iff₀ hE]; simpa [alt_sp_B] using hB
      have : 0 < E' := by
        have := mul_pos (Real.rpow_pos_of_pos (mul_pos hα0 hβ0) ((9 : ℝ) / 10)) hE
        have h2 := (le_div_iff₀ hE).1 hx
        linarith
      show 0 < E' / (Vk * Wl)
      positivity
    · rw [hdens, hqual]
      refine le_trans (by norm_num) (alt_sp_diag _ _ _ _ hα0 hβ0 hα1 hβ1 ?_ ?_)
      · rw [le_div_iff₀ hE]; simpa [alt_sp_B] using hB
      · simpa using hF
  ·
    set ak := Vk / V
    set bl := Wl / W
    set bk := wsum G.μ (vslice G.W p k) / W with hbk
    set al := wsum G.μ (vslice G.V p l) / V with hal
    have hbk0 : 0 ≤ bk := div_nonneg (alt_sp_wsum_nonneg G _) hW.le
    have hal0 : 0 ≤ al := div_nonneg (alt_sp_wsum_nonneg G _) hV.le
    have hbk1 : bk ≤ 1 := (div_le_one hW).2 (alt_sp_vslice_le G _ _ _)
    have hal1 : al ≤ 1 := (div_le_one hV).2 (alt_sp_vslice_le G _ _ _)
    have hbsum : bk + bl ≤ 1 := by
      rw [hbk, ← add_div, div_le_one hW]; exact alt_sp_two_slices G _ p k l hkl
    set S := ak * (1 - bk) + bk * (1 - ak) + (al * (1 - bl) + bl * (1 - al)) with hS
    have hSy : ak * bl ≤ S := by
      have t2 : 0 ≤ bk * (1 - ak) := mul_nonneg hbk0 (by linarith)
      have t3 : 0 ≤ al * (1 - bl) := mul_nonneg hal0 (by linarith)
      have t4 : 0 ≤ bl * (1 - al) := mul_nonneg hβ0.le (by linarith)
      have : ak * bl ≤ ak * (1 - bk) := mul_le_mul_of_nonneg_left (by linarith) hα0.le
      linarith
    have hj : 1 ≤ (k - l) + (l - k) := by omega
    have hx : S * (20 / 21 : ℝ) ^ ((k - l) + (l - k)) / 1000 ≤ E' / E := by
      rw [le_div_iff₀ hE]; simpa [alt_sp_B, hkl] using hB
    have hP : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hkey := alt_sp_key ak bl (E' / E) S F p ((k - l) + (l - k)) hα0 hβ0 hSy hx hj hP hF
    have hE'pos : 0 < E' := by
      have h1 : 0 < S * (20 / 21 : ℝ) ^ ((k - l) + (l - k)) / 1000 := by
        have := lt_of_lt_of_le (mul_pos hα0 hβ0) hSy; positivity
      have := lt_of_lt_of_le h1 hx
      exact (div_pos_iff_of_pos_right hE).1 this
    have hdpos : 0 < G'.density := by
      show 0 < E' / (Vk * Wl)
      positivity
    by_cases hbig : 1 / (10 : ℝ) ^ (40 : ℕ) ≤
        min 1 (G'.density / G.density) * (G'.quality / G.quality)
    · left
      exact ⟨k, l, hdpos, hbig⟩
    · right
      push_neg at hbig
      rw [hdens, hqual] at hbig
      have hy0 : 0 < ak * bl := mul_pos hα0 hβ0
      have hQ : S ^ 2 / (ak * bl) ≤ 1 / 10 ^ 7 := by
        have h1 := lt_of_le_of_lt hkey hbig
        have h2 := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2 * 10 ^ 33)).1 h1
        have h3 : S ^ 2 / (ak * bl) * 2 ≤ S ^ 2 / (ak * bl) * p :=
          mul_le_mul_of_nonneg_left hP (by positivity)
        norm_num at h2 ⊢
        linarith
      have hSQ : S ≤ S ^ 2 / (ak * bl) := by
        rw [le_div_iff₀ hy0]
        have : 0 < S := lt_of_lt_of_le hy0 hSy
        calc S * (ak * bl) ≤ S * S := mul_le_mul_of_nonneg_left hSy this.le
          _ = S ^ 2 := (sq S).symm
      have hres := alt_sp_sharp_real ak bk al bl (1 / 10 ^ 7) hα0.le hbk0 hal0 hβ0.le
        hα1 hbk1 hal1 hβ1 hy0 (by linarith) (by linarith) (by norm_num)
      rcases hres with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨k, ?_, ?_⟩
        · have : 9 / 10 ≤ ak := by linarith
          calc 9 / 10 * V ≤ ak * V := mul_le_mul_of_nonneg_right this hV.le
            _ = Vk := div_mul_cancel₀ _ hV.ne'
        · have : 9 / 10 ≤ bk := by linarith
          calc 9 / 10 * W ≤ bk * W := mul_le_mul_of_nonneg_right this hW.le
            _ = wsum G.μ (vslice G.W p k) := div_mul_cancel₀ _ hW.ne'
      · refine ⟨l, ?_, ?_⟩
        · have : 9 / 10 ≤ al := by linarith
          calc 9 / 10 * V ≤ al * V := mul_le_mul_of_nonneg_right this hV.le
            _ = wsum G.μ (vslice G.V p l) := div_mul_cancel₀ _ hV.ne'
        · have : 9 / 10 ≤ bl := by linarith
          calc 9 / 10 * W ≤ bl * W := mul_le_mul_of_nonneg_right this hW.le
            _ = Wl := div_mul_cancel₀ _ hW.ne'
theorem alt_sp_T0_lt (p : ℕ) (hp : p.Prime) : T0 < (p : ℝ) ^ (7000 : ℕ) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold T0
  calc (10 : ℝ) ^ (2000 : ℕ) < 10 ^ (3 * 700) := pow_lt_pow_right₀ (by norm_num) (by norm_num)
    _ = (10 ^ 3) ^ 700 := pow_mul 10 3 700
    _ ≤ (2 ^ 10) ^ 700 := pow_le_pow_left₀ (by norm_num) (by norm_num) 700
    _ = 2 ^ (10 * 700) := (pow_mul 2 10 700).symm
    _ ≤ (p : ℝ) ^ (10 * 700) := pow_le_pow_left₀ (by norm_num) hp2 _
theorem lemma132 (G : GCDGraph) (hδ : 0 < G.density) (p : ℕ) (hp : p.Prime) (hpP : p ∉ G.P)
    (hpT : (p : ℝ) ≤ T0) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ 0 < G'.density ∧ G'.P = insert p G.P ∧
      G'.R ⊆ G.R.erase p ∧
      1 / (10 : ℝ) ^ (50 : ℕ) ≤ min 1 (G'.density / G.density) * (G'.quality / G.quality) := by
  obtain ⟨G1, hG1, hP1, hf1, hg1, hδ1, hδδ1, hqq1, hHD⟩ := exists_highDegree_subgraph G hδ
  have hq : 0 < G.quality := (quality_pos_iff G).2 hδ
  have hq1 : 0 < G1.quality := (quality_pos_iff G1).2 hδ1
  have hpP1 : p ∉ G1.P := hP1 ▸ hpP
  have hμ1 : G1.μ = G.μ := hG1.1
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have finish : ∀ k l, 0 < (G1.restrictPrime p k l hp hpP1).density →
      1 / (10 : ℝ) ^ (50 : ℕ) ≤
        min 1 ((G1.restrictPrime p k l hp hpP1).density / G1.density) *
          ((G1.restrictPrime p k l hp hpP1).quality / G1.quality) →
      ∃ G' : GCDGraph, G'.IsSubgraph G ∧ 0 < G'.density ∧ G'.P = insert p G.P ∧
        G'.R ⊆ G.R.erase p ∧
        1 / (10 : ℝ) ^ (50 : ℕ) ≤ min 1 (G'.density / G.density) * (G'.quality / G.quality) := by
    intro k l hd hr
    refine ⟨G1.restrictPrime p k l hp hpP1, (restrictPrime_isSubgraph G1 p k l hp hpP1).trans hG1,
      hd, ?_, ?_, ?_⟩
    · show insert p G1.P = _
      rw [hP1]
    · exact (R_restrictPrime_subset G1 p k l hp hpP1).trans (erase_subset_erase p (R_mono hG1))
    · exact hr.trans (alt_sp_ratio_mono _ _ _ _ _ _ hδ hq hδδ1 hqq1 (alt_sp_density_nonneg _)
        ((quality_nonneg _)))
  rcases lemma131 G1 hδ1 p hp hpP1 with ⟨k, l, hd, hr⟩ | ⟨k, hVk9, hWk9⟩
  · refine finish k l hd (le_trans ?_ hr)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    simp only [one_mul]
    exact pow_le_pow_right₀ (by norm_num) (by norm_num)
  obtain ⟨hE1, hV1, hW1⟩ := alt_sp_pos G1 hδ1
  have hsharp : (∃ G' : GCDGraph, G'.IsSubgraph G ∧ 0 < G'.density ∧ G'.P = insert p G.P ∧
        G'.R ⊆ G.R.erase p ∧
        1 / (10 : ℝ) ^ (50 : ℕ) ≤ min 1 (G'.density / G.density) * (G'.quality / G.quality)) ∨
      (1 - K40 / p) * wsum G1.μ G1.W ≤ wsum G1.μ (vslice G1.W p k) := by
    by_cases hbig : (10 : ℝ) ^ (41 : ℕ) < p
    · have hK : K40 < p := by
        have : K40 < (10 : ℝ) ^ (41 : ℕ) := by
          simp only [K40]; exact pow_lt_pow_right₀ (by norm_num) (by norm_num)
        linarith
      rcases lemma122 G1 hδ1 p hp hpP1 hK with ⟨k', l', hd, hr⟩ | ⟨k', hV', hW'⟩
      · left
        refine finish k' l' hd (le_trans ?_ hr)
        have : (1 : ℝ) ≤ 2 ^ (if k' ≠ l' then 1 else 0) := one_le_pow₀ (by norm_num)
        have h2 : 1 / (10 : ℝ) ^ (50 : ℕ) ≤ 1 := by
          rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
        linarith
      · right
        have h9 : 9 / 10 ≤ 1 - K40 / p := by
          have : K40 / p ≤ 1 / 10 := by
            rw [div_le_iff₀ (by positivity)]
            simp only [K40] at hbig ⊢
            have : (10 : ℝ) ^ (41 : ℕ) = 10 * 10 ^ (40 : ℕ) := by ring
            linarith
          linarith
        have hkk : k' = k := by
          by_contra hne
          have h2 := alt_sp_two_slices G1 G1.V p k k' (Ne.symm hne)
          have h3 : 9 / 10 * wsum G1.μ G1.V ≤ wsum G1.μ (vslice G1.V p k') :=
            le_trans (mul_le_mul_of_nonneg_right h9 hV1.le) hV'
          linarith
        subst hkk
        exact hW'
    · right
      push_neg at hbig
      have h9 : 1 - K40 / p ≤ 9 / 10 := by
        have : 1 / 10 ≤ K40 / p := by
          rw [le_div_iff₀ (by positivity)]
          simp only [K40] at hbig ⊢
          have : (10 : ℝ) ^ (41 : ℕ) = 10 * 10 ^ (40 : ℕ) := by ring
          linarith
        linarith
      exact le_trans (mul_le_mul_of_nonneg_right h9 hW1.le) hWk9
  rcases hsharp with hdone | hWk
  · exact hdone
  rcases lemma113 G1 hδ1 p hp hpP1 7000 k (by norm_num) (alt_sp_T0_lt p hp) hWk with
    ⟨l, _, h2q, h2dq⟩ | hsmall
  · apply finish k l
    · by_contra hd
      have hd0 : (G1.restrictPrime p k l hp hpP1).density = 0 :=
        le_antisymm (not_lt.1 hd) (alt_sp_density_nonneg _)
      rw [hd0, zero_mul] at h2dq
      have : 0 < 2 * G1.density * G1.quality := by positivity
      linarith
    · refine le_trans ?_ (alt_sp_ratio_ge _ _ _ _ 2 ?_ ?_)
      · rw [div_le_iff₀ (by positivity)]
        have : (1 : ℝ) ≤ 10 ^ (50 : ℕ) := one_le_pow₀ (by norm_num)
        linarith
      · rw [le_div_iff₀ hq1]; linarith
      · rw [div_mul_div_comm, le_div_iff₀ (by positivity)]; linarith
  set r : ℕ := 7000 with hr
  set V2 := vslice G1.V p k with hV2
  set W2 := G1.W.filter (fun w => (k - w.factorization p) + (w.factorization p - k) ≤ r) with hW2
  set E2 := G1.E.filter (fun e => e.1.factorization p = k ∧
    (k - e.2.factorization p) + (e.2.factorization p - k) ≤ r) with hE2
  have hE2sub : E2 ⊆ V2 ×ˢ W2 := by
    intro e he
    obtain ⟨he, h1, h2⟩ := mem_filter.1 he
    obtain ⟨hv, hw⟩ := mem_product.1 (G1.E_sub he)
    exact mem_product.2 ⟨mem_filter.2 ⟨hv, h1⟩, mem_filter.2 ⟨hw, h2⟩⟩
  set G2 := G1.induce V2 W2 E2 (filter_subset _ _) (filter_subset _ _) (filter_subset _ _) hE2sub
    with hG2
  set E1 := esum G1.μ G1.E with hE1def
  set V1 := wsum G1.μ G1.V with hV1def
  set W1 := wsum G1.μ G1.W with hW1def
  have hδ1eq : G1.density = E1 / (V1 * W1) := rfl
  have hEk : 81 / 100 * E1 ≤ esum G1.μ (G1.E.filter (fun e => e.1.factorization p = k)) := by
    have hset : G1.E.filter (fun e => e.1.factorization p = k) =
        G1.E.filter (fun e => e.1 ∈ V2) := by
      apply filter_congr
      intro e he
      have hv := (mem_product.1 (G1.E_sub he)).1
      simp only [hV2, vslice, mem_filter]
      exact ⟨fun h => ⟨hv, h⟩, fun h => h.2⟩
    rw [hset, alt_sp_esum_nbhd G1 V2 (filter_subset _ _)]
    have hpt : ∀ v ∈ V2, G1.μ v * (9 * G1.density / 10 * W1) ≤ G1.μ v * wsum G1.μ (G1.nbhdV v) :=
      fun v hv => mul_le_mul_of_nonneg_left (hHD.1 v (mem_filter.1 hv).1) (G1.μ_nonneg v)
    refine le_trans ?_ (sum_le_sum hpt)
    rw [← sum_mul]
    have hsum : ∑ v ∈ V2, G1.μ v = wsum G1.μ V2 := rfl
    rw [hsum, hδ1eq]
    have hE1eq : E1 = E1 / (V1 * W1) * V1 * W1 := by field_simp
    have hVW : 0 ≤ E1 / (V1 * W1) * W1 := by positivity
    calc 81 / 100 * E1 = 9 / 10 * (9 * (E1 / (V1 * W1)) / 10 * W1) * V1 := by
          conv_lhs => rw [hE1eq]
          ring
      _ ≤ 9 / 10 * (9 * (E1 / (V1 * W1)) / 10 * W1) * (10 / 9 * wsum G1.μ V2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ = wsum G1.μ V2 * (9 * (E1 / (V1 * W1)) / 10 * W1) := by ring
  have hbad : esum G1.μ (G1.E.filter (fun e => e.1.factorization p = k ∧
      r + 1 ≤ (k - e.2.factorization p) + (e.2.factorization p - k))) ≤ E1 / 4 := by
    refine le_trans hsmall ?_
    apply div_le_div_of_nonneg_left (alt_sp_esum_nonneg G1 _) (by norm_num)
    have : (1 : ℝ) ≤ (p : ℝ) ^ ((31 : ℝ) / 30) := Real.one_le_rpow (by linarith) (by norm_num)
    linarith
  have hsplit : esum G1.μ (G1.E.filter (fun e => e.1.factorization p = k)) =
      esum G1.μ E2 + esum G1.μ (G1.E.filter (fun e => e.1.factorization p = k ∧
        r + 1 ≤ (k - e.2.factorization p) + (e.2.factorization p - k))) := by
    unfold esum
    rw [← sum_filter_add_sum_filter_not (G1.E.filter (fun e => e.1.factorization p = k))
      (fun e => (k - e.2.factorization p) + (e.2.factorization p - k) ≤ r)]
    congr 1
    · rw [filter_filter]
    · rw [filter_filter]
      apply sum_congr _ (fun _ _ => rfl)
      apply filter_congr
      intro e _
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  have hE2 : E1 / 2 ≤ esum G1.μ E2 := by linarith
  have hE2pos : 0 < esum G1.μ E2 := by linarith
  have hVW2 := alt_sp_esum_le_prod G1 V2 W2 E2 hE2sub
  have hV2pos : 0 < wsum G1.μ V2 := by
    have : 0 < 9 / 10 * V1 := by positivity
    linarith
  have hW2pos : 0 < wsum G1.μ W2 := by
    by_contra h
    have h0 := le_antisymm (not_lt.1 h) (alt_sp_wsum_nonneg G1 W2)
    rw [h0, mul_zero] at hVW2
    linarith
  have hV2le : wsum G1.μ V2 ≤ V1 := alt_sp_vslice_le G1 _ _ _
  have hW2le : wsum G1.μ W2 ≤ W1 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => G1.μ_nonneg i)
  have hδ2eq : G2.density = esum G1.μ E2 / (wsum G1.μ V2 * wsum G1.μ W2) := rfl
  have hδ2pos : 0 < G2.density := by rw [hδ2eq]; positivity
  have hδ2 : G1.density / 2 ≤ G2.density := by
    rw [hδ2eq, hδ1eq, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : wsum G1.μ V2 * wsum G1.μ W2 ≤ V1 * W1 :=
      mul_le_mul hV2le hW2le (alt_sp_wsum_nonneg G1 _) hV1.le
    calc E1 * (wsum G1.μ V2 * wsum G1.μ W2) ≤ (2 * esum G1.μ E2) * (V1 * W1) :=
          mul_le_mul (by linarith) h1 (by positivity) (by positivity)
      _ = esum G1.μ E2 * (V1 * W1 * 2) := by ring
  set Pi1 := ∏ q ∈ G1.P, G1.qualityFactor q with hPi1
  have hq1eq : G1.quality = E1 ^ 10 / (V1 ^ 9 * W1 ^ 9) * Pi1 := quality_eq G1
  have hPi1pos : 0 < Pi1 := by
    have h := hq1
    rw [hq1eq] at h
    exact pos_of_mul_pos_right h (by positivity)
  have hq2eq : G2.quality =
      esum G1.μ E2 ^ 10 / (wsum G1.μ V2 ^ 9 * wsum G1.μ W2 ^ 9) * Pi1 := quality_eq G2
  have hq2 : G1.quality / 2 ^ 10 ≤ G2.quality := by
    rw [hq1eq, hq2eq]
    have h1 : (E1 / 2) ^ 10 ≤ esum G1.μ E2 ^ 10 := pow_le_pow_left₀ (by positivity) hE2 10
    have h2 : wsum G1.μ V2 ^ 9 * wsum G1.μ W2 ^ 9 ≤ V1 ^ 9 * W1 ^ 9 :=
      mul_le_mul (pow_le_pow_left₀ hV2pos.le hV2le 9) (pow_le_pow_left₀ hW2pos.le hW2le 9)
        (by positivity) (by positivity)
    have h3 : E1 ^ 10 / (V1 ^ 9 * W1 ^ 9) * Pi1 / 2 ^ 10 = (E1 / 2) ^ 10 / (V1 ^ 9 * W1 ^ 9) * Pi1 := by
      ring
    rw [h3]
    apply mul_le_mul_of_nonneg_right _ hPi1pos.le
    exact div_le_div₀ (by positivity) h1 (by positivity) h2
  obtain ⟨i, hi, j, hj, G3, hG3, hV3, hW3, hE3, hP3, hf3, hg3, hδ3, hδ3b, hq3b⟩ :=
    exists_block_subgraph G2 hδ2pos {0} (Icc (k - r) (k + r)) (fun _ => 0)
      (fun w => w.factorization p) (fun _ _ => mem_singleton_self 0)
      (by
        intro w hw
        have := (mem_filter.1 hw).2
        rw [mem_Icc]; omega)
  have hi0 : i = 0 := mem_singleton.1 hi
  subst hi0
  have hjk : (k - j) + (j - k) ≤ r := by rw [mem_Icc] at hj; omega
  have hcardJ : ((Icc (k - r) (k + r)).card : ℝ) ≤ 14001 := by
    rw [Nat.card_Icc]
    have : k + r + 1 - (k - r) ≤ 14001 := by omega
    exact_mod_cast this
  have hcard1 : (({0} : Finset ℕ).card : ℝ) = 1 := by simp
  rw [hcard1, one_mul] at hδ3b hq3b
  set J := ((Icc (k - r) (k + r)).card : ℝ) with hJ
  have hJpos : 0 < J := by
    rw [hJ]; exact_mod_cast card_pos.2 ⟨k, by rw [mem_Icc]; omega⟩
  clear_value J
  set G' := G1.restrictPrime p k j hp hpP1 with hG'
  have hμ3 : G3.μ = G1.μ := hG3.1
  have hV3' : G3.V = vslice G1.V p k := by
    rw [hV3]; ext v
    rw [mem_filter]
    exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩
  have hW3' : G3.W = vslice G1.W p j := by
    rw [hW3]; ext w
    constructor
    · intro hw
      obtain ⟨hw2, h3⟩ := mem_filter.1 hw
      obtain ⟨hw1, -⟩ := mem_filter.1 (show w ∈ W2 from hw2)
      exact mem_filter.2 ⟨hw1, h3⟩
    · intro hw
      obtain ⟨hw1, h3⟩ := mem_filter.1 hw
      refine mem_filter.2 ⟨show w ∈ W2 from mem_filter.2 ⟨hw1, ?_⟩, h3⟩
      rw [h3]; exact hjk
  have hE3' : G3.E = G1.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = j) := by
    rw [hE3]; ext e
    constructor
    · intro he
      obtain ⟨he2, -, h4⟩ := mem_filter.1 he
      obtain ⟨he1, h1, -⟩ := mem_filter.1 (show e ∈ E2 from he2)
      exact mem_filter.2 ⟨he1, h1, h4⟩
    · intro he
      obtain ⟨he1, h1, h4⟩ := mem_filter.1 he
      refine mem_filter.2 ⟨show e ∈ E2 from mem_filter.2 ⟨he1, h1, ?_⟩, rfl, h4⟩
      rw [h4]; exact hjk
  have hδ'eq : G'.density = G3.density := by
    show esum G1.μ (G1.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = j)) /
      (wsum G1.μ (vslice G1.V p k) * wsum G1.μ (vslice G1.W p j)) = _
    unfold density
    rw [hμ3, hV3', hW3', hE3']
  obtain ⟨hE3pos, hV3pos, hW3pos⟩ := alt_sp_pos G3 hδ3
  rw [hμ3, hV3'] at hV3pos
  rw [hμ3, hW3'] at hW3pos
  rw [hμ3, hE3'] at hE3pos
  have hqG' := quality_restrictPrime G1 p k j hp hpP1 hE1 hV3pos hW3pos
  have hq3eq := quality_eq G3
  have hPi3 : ∏ q ∈ G3.P, G3.qualityFactor q = Pi1 := by
    rw [hP3]
    apply prod_congr rfl
    intro q _
    unfold qualityFactor fgDist
    rw [hf3, hg3]
    rfl
  rw [hPi3, hμ3, hV3', hW3', hE3'] at hq3eq
  set F := (p : ℝ) ^ ((k - j) + (j - k)) /
          ((1 - (if k = j ∧ 1 ≤ k then 1 / (p : ℝ) else 0)) ^ 2 *
            (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10) with hFdef
  have hF : 1 ≤ F := by
    have := alt_sp_F_ge p hp ((k - j) + (j - k))
      (if k = j ∧ 1 ≤ k then 1 / (p : ℝ) else 0) (by split_ifs <;> positivity)
      (by
        split_ifs
        · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        · norm_num)
    exact le_trans (one_le_pow₀ (by linarith)) this
  have hq'eq : G'.quality = G3.quality * F := by
    rw [hqG', hq3eq, hq1eq]
    show E1 ^ 10 / (V1 ^ 9 * W1 ^ 9) * Pi1 *
        (esum G1.μ (G1.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p = j)) /
          E1) ^ 10 * (V1 / wsum G1.μ (vslice G1.V p k)) ^ 9 *
        (W1 / wsum G1.μ (vslice G1.W p j)) ^ 9 * F = _
    field_simp
  have hq3pos : 0 < G3.quality := (quality_pos_iff G3).2 hδ3
  have hq' : G3.quality ≤ G'.quality := by
    rw [hq'eq]; exact le_mul_of_one_le_right hq3pos.le hF
  have hδ'pos : 0 < G'.density := by rw [hδ'eq]; exact hδ3
  apply finish k j hδ'pos
  have hq'1 : G1.quality / (2 ^ 10 * J ^ 10) ≤ G'.quality := by
    calc G1.quality / (2 ^ 10 * J ^ 10) = G1.quality / 2 ^ 10 / J ^ 10 := by rw [div_div]
      _ ≤ G2.quality / J ^ 10 := div_le_div_of_nonneg_right hq2 (by positivity)
      _ ≤ G3.quality := hq3b
      _ ≤ G'.quality := hq'
  have hδ'1 : G1.density / (2 * J) ≤ G'.density := by
    rw [hδ'eq]
    calc G1.density / (2 * J) = G1.density / 2 / J := by rw [div_div]
      _ ≤ G2.density / J := div_le_div_of_nonneg_right hδ2 hJpos.le
      _ ≤ G3.density := hδ3b
  have hJ10 : 2 ^ 10 * J ^ 10 ≤ (10 : ℝ) ^ (50 : ℕ) := by
    have : J ^ 10 ≤ 14001 ^ 10 := pow_le_pow_left₀ hJpos.le hcardJ 10
    calc 2 ^ 10 * J ^ 10 ≤ 2 ^ 10 * 14001 ^ 10 := by gcongr
      _ ≤ (10 : ℝ) ^ (50 : ℕ) := by norm_num
  have hJ11 : 2 * J * (2 ^ 10 * J ^ 10) ≤ (10 : ℝ) ^ (50 : ℕ) := by
    have : J ^ 11 ≤ 14001 ^ 11 := pow_le_pow_left₀ hJpos.le hcardJ 11
    calc 2 * J * (2 ^ 10 * J ^ 10) = 2 ^ 11 * J ^ 11 := by ring
      _ ≤ 2 ^ 11 * 14001 ^ 11 := by gcongr
      _ ≤ (10 : ℝ) ^ (50 : ℕ) := by norm_num
  apply alt_sp_ratio_ge
  · rw [le_div_iff₀ hq1]
    calc 1 / (10 : ℝ) ^ (50 : ℕ) * G1.quality ≤ G1.quality / (2 ^ 10 * J ^ 10) := by
          rw [one_div_mul_eq_div]
          exact div_le_div_of_nonneg_left hq1.le (by positivity) hJ10
      _ ≤ G'.quality := hq'1
  · rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
    calc 1 / (10 : ℝ) ^ (50 : ℕ) * (G1.density * G1.quality) ≤
        G1.density * G1.quality / (2 * J * (2 ^ 10 * J ^ 10)) := by
          rw [one_div_mul_eq_div]
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) hJ11
      _ = G1.density / (2 * J) * (G1.quality / (2 ^ 10 * J ^ 10)) := by
          rw [div_mul_div_comm]
      _ ≤ G'.density * G'.quality :=
          mul_le_mul hδ'1 hq'1 (by positivity) (le_of_lt hδ'pos)
theorem alt_sp_iter (G : GCDGraph) (n : ℕ) :
    ∀ H : GCDGraph, H.IsSubgraph G → 0 < H.density → (∀ p ∈ H.P, (p : ℝ) ≤ T0) →
      (H.R.filter (fun p : ℕ => (p : ℝ) ≤ T0)).card ≤ n →
      ∃ G' : GCDGraph, G'.IsSubgraph H ∧ 0 < G'.density ∧ (∀ p ∈ G'.P, (p : ℝ) ≤ T0) ∧
        (∀ p ∈ G'.R, T0 < (p : ℝ)) ∧
        (1 / (10 : ℝ) ^ (50 : ℕ)) ^ n ≤
          min 1 (G'.density / H.density) * (G'.quality / H.quality) := by
  induction n with
  | zero =>
    intro H _ hδ hP hc
    have hq : 0 < H.quality := (quality_pos_iff H).2 hδ
    refine ⟨H, IsSubgraph.refl H, hδ, hP, ?_, ?_⟩
    · intro p hp
      by_contra h
      push_neg at h
      have : p ∈ H.R.filter (fun p : ℕ => (p : ℝ) ≤ T0) := mem_filter.2 ⟨hp, h⟩
      rw [card_eq_zero.1 (Nat.le_zero.1 hc)] at this
      exact absurd this (notMem_empty p)
    · rw [div_self hδ.ne', div_self hq.ne']; simp
  | succ n ih =>
    intro H hHG hδ hP hc
    have hq : 0 < H.quality := (quality_pos_iff H).2 hδ
    by_cases hex : ∃ p ∈ H.R, (p : ℝ) ≤ T0
    · obtain ⟨p, hpR, hpT⟩ := hex
      obtain ⟨H', hH', hδ', hP', hR', hrat⟩ :=
        lemma132 H hδ p (H.prime_of_mem_R hpR) (H.not_mem_P_of_mem_R hpR) hpT
      have hc' : (H'.R.filter (fun p : ℕ => (p : ℝ) ≤ T0)).card ≤ n := by
        have hsub : H'.R.filter (fun p : ℕ => (p : ℝ) ≤ T0) ⊆
            (H.R.filter (fun p : ℕ => (p : ℝ) ≤ T0)).erase p := by
          intro q hq
          obtain ⟨hq1, hq2⟩ := mem_filter.1 hq
          have := hR' hq1
          rw [mem_erase] at this ⊢
          exact ⟨this.1, mem_filter.2 ⟨this.2, hq2⟩⟩
        have := card_le_card hsub
        rw [card_erase_of_mem (mem_filter.2 ⟨hpR, hpT⟩)] at this
        omega
      have hP'' : ∀ q ∈ H'.P, (q : ℝ) ≤ T0 := by
        intro q hq
        rw [hP'] at hq
        rcases mem_insert.1 hq with rfl | hq
        · exact hpT
        · exact hP q hq
      obtain ⟨G', hG', hδG', hPG', hRG', hratG'⟩ := ih H' (hH'.trans hHG) hδ' hP'' hc'
      have hq' : 0 < H'.quality := (quality_pos_iff H').2 hδ'
      refine ⟨G', hG'.trans hH', hδG', hPG', hRG', ?_⟩
      refine le_trans ?_ (alt_sp_ratio_chain _ _ _ _ _ _ hδ hδ' (alt_sp_density_nonneg _) hq hq'
        (quality_nonneg _))
      rw [pow_succ]
      exact mul_le_mul hratG' hrat (by positivity)
        (le_trans (by positivity) hratG')
    · push_neg at hex
      refine ⟨H, IsSubgraph.refl H, hδ, hP, hex, ?_⟩
      rw [div_self hδ.ne', div_self hq.ne']
      simp only [min_self, mul_one]
      apply pow_le_one₀ (by positivity)
      rw [div_le_one (by positivity)]
      exact one_le_pow₀ (by norm_num)
theorem prop83 (G : GCDGraph) (hP : G.P = ∅) (hδ : 0 < G.density) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ 0 < G'.density ∧ (∀ p ∈ G'.P, (p : ℝ) ≤ T0) ∧
      (∀ p ∈ G'.R, T0 < (p : ℝ)) ∧
      1 / (10 : ℝ) ^ ((10 : ℕ) ^ 3000) ≤
        min 1 (G'.density / G.density) * (G'.quality / G.quality) := by
  set N := (G.R.filter (fun p : ℕ => (p : ℝ) ≤ T0)).card with hN
  obtain ⟨G', hG', hδ', hP', hR', hrat⟩ :=
    alt_sp_iter G N G (IsSubgraph.refl G) hδ (by rw [hP]; simp) le_rfl
  refine ⟨G', hG', hδ', hP', hR', le_trans ?_ hrat⟩
  have hNle : N ≤ 10 ^ 2000 + 1 := by
    have hsub : G.R.filter (fun p : ℕ => (p : ℝ) ≤ T0) ⊆ range (10 ^ 2000 + 1) := by
      intro q hq
      have h := (mem_filter.1 hq).2
      rw [mem_range, Nat.lt_succ_iff]
      have : (q : ℝ) ≤ ((10 ^ 2000 : ℕ) : ℝ) := by
        rw [Nat.cast_pow]; exact h
      exact_mod_cast this
    have := card_le_card hsub
    rwa [card_range] at this
  have hexp : 50 * N ≤ 10 ^ 3000 := by
    have h1 : (10 : ℕ) ^ 3000 = 10 ^ 1000 * 10 ^ 2000 := by rw [← pow_add]
    have h2 : 100 ≤ (10 : ℕ) ^ 1000 := by
      calc 100 = (10 : ℕ) ^ 2 := by norm_num
        _ ≤ 10 ^ 1000 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    have h3 : 1 ≤ (10 : ℕ) ^ 2000 := Nat.one_le_pow _ _ (by norm_num)
    rw [h1]
    have hN' := hNle
    generalize (10 : ℕ) ^ 1000 = Y at h2 ⊢
    generalize (10 : ℕ) ^ 2000 = X at h3 hN' ⊢
    calc 50 * N ≤ 50 * (X + 1) := Nat.mul_le_mul_left 50 hN'
      _ ≤ 100 * X := by omega
      _ ≤ Y * X := Nat.mul_le_mul_right X h2
  rw [one_div_pow, ← pow_mul]
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
  exact pow_le_pow_right₀ (by norm_num) hexp
end GCDGraph
end DuffinSchaeffer
end Port24_Parts_SmallPrimes

section Port24_Parts_SharpPrimes
open Finset
namespace DuffinSchaeffer
namespace GCDGraph
theorem alt_sh_wsum_nonneg (G : GCDGraph) (S : Finset ℕ) : 0 ≤ wsum G.μ S :=
  sum_nonneg fun i _ => G.μ_nonneg i
theorem alt_sh_esum_nonneg (G : GCDGraph) (S : Finset (ℕ × ℕ)) : 0 ≤ esum G.μ S :=
  sum_nonneg fun i _ => mul_nonneg (G.μ_nonneg _) (G.μ_nonneg _)
theorem alt_sh_pos (G : GCDGraph) (hδ : 0 < G.density) :
    0 < esum G.μ G.E ∧ 0 < wsum G.μ G.V ∧ 0 < wsum G.μ G.W := by
  have hV0 : 0 ≤ wsum G.μ G.V := sum_nonneg fun i _ => G.μ_nonneg i
  have hW0 : 0 ≤ wsum G.μ G.W := sum_nonneg fun i _ => G.μ_nonneg i
  unfold density at hδ
  have hVW : wsum G.μ G.V * wsum G.μ G.W ≠ 0 := by
    intro h; rw [h, div_zero] at hδ; exact lt_irrefl _ hδ
  have hVW' : 0 < wsum G.μ G.V * wsum G.μ G.W :=
    lt_of_le_of_ne (mul_nonneg hV0 hW0) (Ne.symm hVW)
  refine ⟨(div_pos_iff_of_pos_right hVW').1 hδ,
    lt_of_le_of_ne hV0 (fun h => hVW (by rw [← h, zero_mul])),
    lt_of_le_of_ne hW0 (fun h => hVW (by rw [← h, mul_zero]))⟩
theorem alt_sh_esum_le_prod (G : GCDGraph) (V' W' : Finset ℕ) (E' : Finset (ℕ × ℕ))
    (h : E' ⊆ V' ×ˢ W') : esum G.μ E' ≤ wsum G.μ V' * wsum G.μ W' := by
  unfold esum wsum
  rw [sum_mul_sum, ← sum_product']
  exact sum_le_sum_of_subset_of_nonneg h (fun i _ _ => mul_nonneg (G.μ_nonneg _) (G.μ_nonneg _))
theorem alt_sh_esum_union_le (G : GCDGraph) (s t : Finset (ℕ × ℕ)) :
    esum G.μ (s ∪ t) ≤ esum G.μ s + esum G.μ t := by
  unfold esum
  rw [← sum_union_inter]
  have : 0 ≤ ∑ e ∈ s ∩ t, G.μ e.1 * G.μ e.2 :=
    sum_nonneg fun i _ => mul_nonneg (G.μ_nonneg _) (G.μ_nonneg _)
  linarith
theorem alt_sh_disj_le (G : GCDGraph) (S : Finset ℕ) (P Q : ℕ → Prop) [DecidablePred P]
    [DecidablePred Q] (h : ∀ v, P v → ¬ Q v) :
    wsum G.μ (S.filter P) + wsum G.μ (S.filter Q) ≤ wsum G.μ S := by
  unfold wsum
  rw [← sum_union (disjoint_filter.2 (fun v _ h1 h2 => h v h1 h2))]
  exact sum_le_sum_of_subset_of_nonneg (union_subset (filter_subset _ _) (filter_subset _ _))
    (fun i _ _ => G.μ_nonneg i)
def alt_sh_plus (G : GCDGraph) (p k : ℕ) (hp : p.Prime) (hpP : p ∉ G.P) : GCDGraph where
  μ := G.μ
  V := G.V.filter (fun v => v.factorization p = k ∨ v.factorization p = k + 1)
  W := G.W.filter (fun w => w.factorization p = k ∨ w.factorization p = k + 1)
  E := G.E.filter (fun e => (e.1.factorization p = k ∧ e.2.factorization p = k) ∨
    (e.1.factorization p = k ∧ e.2.factorization p = k + 1) ∨
    (e.1.factorization p = k + 1 ∧ e.2.factorization p = k))
  P := insert p G.P
  f := Function.update G.f p k
  g := Function.update G.g p k
  μ_nonneg := G.μ_nonneg
  V_pos := fun v hv => G.V_pos v (Finset.mem_filter.1 hv).1
  W_pos := fun w hw => G.W_pos w (Finset.mem_filter.1 hw).1
  E_sub := by
    intro e he
    obtain ⟨he, h⟩ := Finset.mem_filter.1 he
    obtain ⟨hv, hw⟩ := Finset.mem_product.1 (G.E_sub he)
    refine Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨hv, ?_⟩, Finset.mem_filter.2 ⟨hw, ?_⟩⟩
    · omega
    · omega
  P_prime := by
    intro q hq
    rcases Finset.mem_insert.1 hq with hqp | hq
    · rw [hqp]; exact hp
    · exact G.P_prime q hq
  dvd_V := by
    intro q hq v hv
    obtain ⟨hv, hvk⟩ := Finset.mem_filter.1 hv
    rcases Finset.mem_insert.1 hq with hqp | hq'
    · rw [hqp, Function.update_self]
      exact (pow_dvd_pow p (by omega : k ≤ v.factorization p)).trans (Nat.ordProj_dvd v p)
    · have hne : q ≠ p := fun h => hpP (h ▸ hq')
      rw [Function.update_of_ne hne]
      exact G.dvd_V q hq' v hv
  dvd_W := by
    intro q hq w hw
    obtain ⟨hw, hwk⟩ := Finset.mem_filter.1 hw
    rcases Finset.mem_insert.1 hq with hqp | hq'
    · rw [hqp, Function.update_self]
      exact (pow_dvd_pow p (by omega : k ≤ w.factorization p)).trans (Nat.ordProj_dvd w p)
    · have hne : q ≠ p := fun h => hpP (h ▸ hq')
      rw [Function.update_of_ne hne]
      exact G.dvd_W q hq' w hw
  gcd_E := by
    intro q hq e he0
    obtain ⟨he, h⟩ := Finset.mem_filter.1 he0
    rcases Finset.mem_insert.1 hq with hqp | hq'
    · obtain ⟨hv, hw⟩ := Finset.mem_product.1 (G.E_sub he)
      have hv0 : e.1 ≠ 0 := (G.V_pos _ hv).ne'
      have hw0 : e.2 ≠ 0 := (G.W_pos _ hw).ne'
      rw [hqp, Function.update_self, Function.update_self, Nat.factorization_gcd hv0 hw0,
        Finsupp.inf_apply]
      show min (e.1.factorization p) (e.2.factorization p) = min k k
      omega
    · have hne : q ≠ p := fun h => hpP (h ▸ hq')
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
      exact G.gcd_E q hq' e he
  exact_V := by
    intro q hq hfg v hv
    obtain ⟨hv, _⟩ := Finset.mem_filter.1 hv
    rcases Finset.mem_insert.1 hq with hqp | hq'
    · rw [hqp, Function.update_self, Function.update_self] at hfg
      exact absurd rfl hfg
    · have hne : q ≠ p := fun h => hpP (h ▸ hq')
      rw [Function.update_of_ne hne, Function.update_of_ne hne] at hfg
      rw [Function.update_of_ne hne]
      exact G.exact_V q hq' hfg v hv
  exact_W := by
    intro q hq hfg w hw
    obtain ⟨hw, _⟩ := Finset.mem_filter.1 hw
    rcases Finset.mem_insert.1 hq with hqp | hq'
    · rw [hqp, Function.update_self, Function.update_self] at hfg
      exact absurd rfl hfg
    · have hne : q ≠ p := fun h => hpP (h ▸ hq')
      rw [Function.update_of_ne hne, Function.update_of_ne hne] at hfg
      rw [Function.update_of_ne hne]
      exact G.exact_W q hq' hfg w hw
theorem alt_sh_plus_isSubgraph (G : GCDGraph) (p k : ℕ) (hp : p.Prime) (hpP : p ∉ G.P) :
    (alt_sh_plus G p k hp hpP).IsSubgraph G := by
  refine ⟨rfl, filter_subset _ _, filter_subset _ _, filter_subset _ _, subset_insert _ _, ?_⟩
  intro q hq
  have hne : q ≠ p := fun h => hpP (h ▸ hq)
  exact ⟨Function.update_of_ne hne _ _, Function.update_of_ne hne _ _⟩
theorem alt_sh_plus_R (G : GCDGraph) (p k : ℕ) (hp : p.Prime) (hpP : p ∉ G.P) :
    (alt_sh_plus G p k hp hpP).R ⊆ G.R.erase p := by
  intro q hq
  obtain ⟨h1, h2⟩ := mem_sdiff.1 hq
  obtain ⟨e, he, hqe⟩ := mem_biUnion.1 h1
  have hq1 : q ∉ G.P := fun h => h2 (mem_insert_of_mem h)
  have hqp : q ≠ p := fun h => h2 (by rw [h]; exact mem_insert_self p G.P)
  exact mem_erase.2 ⟨hqp, mem_sdiff.2 ⟨mem_biUnion.2 ⟨e, (mem_filter.1 he).1, hqe⟩, hq1⟩⟩
theorem alt_sh_plus_quality (G : GCDGraph) (p k : ℕ) (hp : p.Prime) (hpP : p ∉ G.P)
    (hE : 0 < esum G.μ G.E) (hV : 0 < wsum G.μ G.V) (hW : 0 < wsum G.μ G.W)
    (hV' : 0 < wsum G.μ (alt_sh_plus G p k hp hpP).V)
    (hW' : 0 < wsum G.μ (alt_sh_plus G p k hp hpP).W) :
    (alt_sh_plus G p k hp hpP).quality = G.quality *
      (esum G.μ (alt_sh_plus G p k hp hpP).E / esum G.μ G.E) ^ 10 *
      (wsum G.μ G.V / wsum G.μ (alt_sh_plus G p k hp hpP).V) ^ 9 *
      (wsum G.μ G.W / wsum G.μ (alt_sh_plus G p k hp hpP).W) ^ 9 *
      (1 / ((1 - (if 1 ≤ k then 1 / (p : ℝ) else 0)) ^ 2 *
        (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10)) := by
  set G' := alt_sh_plus G p k hp hpP with hG'
  have hq' : G'.quality = esum G.μ G'.E ^ 10 / (wsum G.μ G'.V ^ 9 * wsum G.μ G'.W ^ 9) *
      ∏ q ∈ G'.P, G'.qualityFactor q := quality_eq G'
  have hq := quality_eq G
  have hprod : ∏ q ∈ G'.P, G'.qualityFactor q =
      (1 / ((1 - (if 1 ≤ k then 1 / (p : ℝ) else 0)) ^ 2 *
        (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10)) * ∏ q ∈ G.P, G.qualityFactor q := by
    show ∏ q ∈ insert p G.P, G'.qualityFactor q = _
    rw [prod_insert hpP]
    congr 1
    · show (p : ℝ) ^ ((Function.update G.f p k p - Function.update G.g p k p) +
          (Function.update G.g p k p - Function.update G.f p k p)) /
        ((1 - (if Function.update G.f p k p = Function.update G.g p k p ∧
          1 ≤ Function.update G.f p k p then 1 / (p : ℝ) else 0)) ^ 2 *
          (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10) = _
      simp only [Function.update_self, Nat.sub_self, add_zero, pow_zero, true_and]
    · apply prod_congr rfl
      intro q hq
      have hne : q ≠ p := fun h => hpP (h ▸ hq)
      show (q : ℝ) ^ ((Function.update G.f p k q - Function.update G.g p k q) +
          (Function.update G.g p k q - Function.update G.f p k q)) /
        ((1 - (if Function.update G.f p k q = Function.update G.g p k q ∧
          1 ≤ Function.update G.f p k q then 1 / (q : ℝ) else 0)) ^ 2 *
          (1 - 1 / (q : ℝ) ^ ((31 : ℝ) / 30)) ^ 10) = G.qualityFactor q
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
      rfl
  rw [hq', hprod, hq]
  field_simp
theorem alt_sh_amgm (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x ^ 10 < y ^ 9 * z) :
    x < (9 * y + z) / 10 := by
  by_contra hge
  push_neg at hge
  have hw := Real.geom_mean_le_arith_mean2_weighted (w₁ := 9 / 10) (w₂ := 1 / 10) (p₁ := y)
    (p₂ := z) (by norm_num) (by norm_num) hy hz (by norm_num)
  have h1 : (y ^ ((9 : ℝ) / 10) * z ^ ((1 : ℝ) / 10)) ^ (10 : ℕ) = y ^ 9 * z := by
    rw [mul_pow, ← Real.rpow_natCast (y ^ ((9 : ℝ) / 10)), ← Real.rpow_mul hy,
      ← Real.rpow_natCast (z ^ ((1 : ℝ) / 10)), ← Real.rpow_mul hz]
    norm_num
  have h2 : (y ^ ((9 : ℝ) / 10) * z ^ ((1 : ℝ) / 10)) ^ (10 : ℕ) ≤ ((9 * y + z) / 10) ^ 10 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have h3 : ((9 * y + z) / 10) ^ 10 ≤ x ^ 10 := pow_le_pow_left₀ (by positivity) hge 10
  linarith
theorem alt_sh_bound1 (x V V' W W' a b F : ℝ) (hV : 0 < V) (hW : 0 < W) (hV' : 0 < V')
    (hW' : 0 < W') (hVa : V' ≤ (1 - a) * V) (hWb : W' ≤ (1 - b) * W) (hF : 0 < F)
    (h : x ^ 10 * (V / V') ^ 9 * (W / W') ^ 9 * F < 1) :
    x ^ 10 < (1 - a) ^ 9 * (1 - b) ^ 9 / F := by
  have hu : V' / V ≤ 1 - a := by rw [div_le_iff₀ hV]; linarith
  have hv : W' / W ≤ 1 - b := by rw [div_le_iff₀ hW]; linarith
  have e : x ^ 10 * (V / V') ^ 9 * (W / W') ^ 9 * F =
      x ^ 10 * F / ((V' / V) ^ 9 * (W' / W) ^ 9) := by
    field_simp
  rw [e, div_lt_one (by positivity)] at h
  have h2 : x ^ 10 < (V' / V) ^ 9 * (W' / W) ^ 9 / F := by
    rw [lt_div_iff₀ hF]; linarith
  refine lt_of_lt_of_le h2 ?_
  apply div_le_div_of_nonneg_right _ hF.le
  apply mul_le_mul (pow_le_pow_left₀ (by positivity) hu 9)
    (pow_le_pow_left₀ (by positivity) hv 9) (by positivity)
  exact le_trans (by positivity) (pow_le_pow_left₀ (by positivity) hu 9)
theorem alt_sh_final (xp xa xb a b c θ e η : ℝ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (haη : a ≤ η)
    (hbη : b ≤ η) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hθ0 : 0 ≤ θ)
    (hxp : xp < (9 * ((1 - a) * (1 - b) * (1 - c)) + (1 - θ) ^ 2 * (1 - c)) / 10)
    (hxa : xa ≤ (1 - c) * (9 * b + θ) / 10) (hxb : xb ≤ (1 - c) * (9 * a + θ) / 10)
    (hcov : 1 ≤ xp + xa + xb + c / 2 + e) (hsmall : η ^ 2 + θ ^ 2 + e ≤ c / 2) : False := by
  have key : (9 * ((1 - a) * (1 - b) * (1 - c)) + (1 - θ) ^ 2 * (1 - c)) / 10 +
      (1 - c) * (9 * b + θ) / 10 + (1 - c) * (9 * a + θ) / 10 =
      (1 - c) + (1 - c) * (9 * (a * b) + θ ^ 2) / 10 := by ring
  have hab : a * b ≤ η ^ 2 := by
    rw [sq]; exact mul_le_mul haη hbη hb0 (le_trans ha0 haη)
  have hnn : 0 ≤ 9 * (a * b) + θ ^ 2 := by positivity
  have h2 : (1 - c) * (9 * (a * b) + θ ^ 2) ≤ 9 * (a * b) + θ ^ 2 := by
    have : 0 ≤ c * (9 * (a * b) + θ ^ 2) := mul_nonneg hc0 hnn
    linarith
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  nlinarith
theorem alt_sh_numeric (P : ℝ) (hP : T0 ≤ P) :
    (K40 / P) ^ 2 + (1 / P) ^ 2 + (K40 / P) ^ ((9 : ℝ) / 5) ≤ 1 / P ^ ((31 : ℝ) / 30) / 2 := by
  unfold T0 at hP
  unfold K40
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hP
  have h30 : (P ^ ((1 : ℝ) / 30)) ^ (30 : ℕ) = P := by
    rw [← Real.rpow_natCast (P ^ ((1 : ℝ) / 30)) 30, ← Real.rpow_mul hP0.le]; norm_num
  have h31 : (P ^ ((1 : ℝ) / 30)) ^ (31 : ℕ) = P ^ ((31 : ℝ) / 30) := by
    rw [← Real.rpow_natCast (P ^ ((1 : ℝ) / 30)) 31, ← Real.rpow_mul hP0.le]; norm_num
  have hs0 : 0 < P ^ ((1 : ℝ) / 30) := Real.rpow_pos_of_pos hP0 _
  generalize P ^ ((1 : ℝ) / 30) = s at h30 h31 hs0
  have hs : (10 : ℝ) ^ (10 : ℕ) ≤ s := by
    have : ((10 : ℝ) ^ (10 : ℕ)) ^ (30 : ℕ) ≤ s ^ (30 : ℕ) := by
      rw [h30, ← pow_mul]
      exact le_trans (pow_le_pow_right₀ (by norm_num) (by norm_num)) hP
    exact le_of_pow_le_pow_left₀ (by norm_num) hs0.le this
  have hs1 : 1 ≤ s := le_trans (one_le_pow₀ (by norm_num)) hs
  have hbig : ∀ n : ℕ, 9 ≤ n → (10 : ℝ) ^ (90 : ℕ) ≤ s ^ n := by
    intro n hn
    calc (10 : ℝ) ^ (90 : ℕ) = ((10 : ℝ) ^ (10 : ℕ)) ^ (9 : ℕ) := by rw [← pow_mul]
      _ ≤ s ^ (9 : ℕ) := pow_le_pow_left₀ (by positivity) hs 9
      _ ≤ s ^ n := pow_le_pow_right₀ hs1 hn
  have e1 : (10 : ℝ) ^ (40 : ℕ) / P = (10 ^ (8 : ℕ) / s ^ (6 : ℕ)) ^ (5 : ℕ) := by
    rw [← h30]; ring
  have hq0 : 0 ≤ (10 : ℝ) ^ (8 : ℕ) / s ^ (6 : ℕ) := by positivity
  have e2 : ((10 ^ (8 : ℕ) / s ^ (6 : ℕ)) ^ (5 : ℕ)) ^ ((9 : ℝ) / 5) =
      (10 ^ (8 : ℕ) / s ^ (6 : ℕ)) ^ (9 : ℕ) := by
    rw [← Real.rpow_natCast ((10 : ℝ) ^ (8 : ℕ) / s ^ (6 : ℕ)) 5, ← Real.rpow_mul hq0]
    norm_num
  rw [e1, e2, ← h31, ← h30]
  have t1 : ((10 ^ (8 : ℕ) / s ^ (6 : ℕ)) ^ (5 : ℕ)) ^ 2 ≤ 1 / (6 * s ^ (31 : ℕ)) := by
    rw [show ((10 ^ (8 : ℕ) / s ^ (6 : ℕ)) ^ (5 : ℕ)) ^ 2 = (10 : ℝ) ^ (80 : ℕ) / s ^ (60 : ℕ) by
      ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h29 := hbig 29 (by norm_num)
    calc (10 : ℝ) ^ (80 : ℕ) * (6 * s ^ (31 : ℕ)) = (6 * 10 ^ (80 : ℕ)) * s ^ (31 : ℕ) := by ring
      _ ≤ s ^ (29 : ℕ) * s ^ (31 : ℕ) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 1 * s ^ (60 : ℕ) := by ring
  have t2 : (1 / s ^ (30 : ℕ)) ^ 2 ≤ 1 / (6 * s ^ (31 : ℕ)) := by
    rw [show (1 / s ^ (30 : ℕ)) ^ 2 = 1 / s ^ (60 : ℕ) by ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h29 := hbig 29 (by norm_num)
    calc 1 * (6 * s ^ (31 : ℕ)) = 6 * s ^ (31 : ℕ) := by ring
      _ ≤ s ^ (29 : ℕ) * s ^ (31 : ℕ) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 1 * s ^ (60 : ℕ) := by ring
  have t3 : (10 ^ (8 : ℕ) / s ^ (6 : ℕ)) ^ (9 : ℕ) ≤ 1 / (6 * s ^ (31 : ℕ)) := by
    rw [show ((10 : ℝ) ^ (8 : ℕ) / s ^ (6 : ℕ)) ^ (9 : ℕ) = (10 : ℝ) ^ (72 : ℕ) / s ^ (54 : ℕ) by
      ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h23 := hbig 23 (by norm_num)
    calc (10 : ℝ) ^ (72 : ℕ) * (6 * s ^ (31 : ℕ)) = (6 * 10 ^ (72 : ℕ)) * s ^ (31 : ℕ) := by ring
      _ ≤ s ^ (23 : ℕ) * s ^ (31 : ℕ) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 1 * s ^ (54 : ℕ) := by ring
  have t4 : 1 / (6 * s ^ (31 : ℕ)) * 3 = 1 / s ^ (31 : ℕ) / 2 := by
    field_simp; ring
  linarith
theorem alt_sh_cover (G G1 : GCDGraph) (p k : ℕ) (hp : p.Prime) (hpP1 : p ∉ G1.P)
    (hμ1 : G1.μ = G.μ) (hE1 : 0 < esum G1.μ G1.E) (η : ℝ)
    (hVk : (1 - η) * wsum G1.μ G1.V ≤ wsum G1.μ (vslice G1.V p k))
    (hWk : (1 - η) * wsum G1.μ G1.W ≤ wsum G1.μ (vslice G1.W p k))
    (hsp : ∀ A ⊆ G1.V, ∀ B ⊆ G1.W, wsum G.μ A ≤ η * wsum G.μ G1.V →
      wsum G.μ B ≤ η * wsum G.μ G1.W →
      esum G.μ (G1.E.filter (fun e => e.1 ∈ A ∧ e.2 ∈ B)) ≤ η ^ ((9 : ℝ) / 5) * esum G.μ G1.E)
    (c : ℝ) (hc : c = 1 / (p : ℝ) ^ ((31 : ℝ) / 30))
    (hbad1 : esum G1.μ (G1.E.filter (fun e => e.1.factorization p = k ∧
      1 + 1 ≤ (k - e.2.factorization p) + (e.2.factorization p - k))) ≤
        esum G1.μ G1.E / (4 * (p : ℝ) ^ ((31 : ℝ) / 30)))
    (hbad2 : esum G1.μ (G1.E.filter (fun e => e.2.factorization p = k ∧
      1 + 1 ≤ (e.1.factorization p - k) + (k - e.1.factorization p))) ≤
        esum G1.μ G1.E / (4 * (p : ℝ) ^ ((31 : ℝ) / 30))) :
    1 ≤ esum G1.μ (alt_sh_plus G1 p k hp hpP1).E / esum G1.μ G1.E +
      esum G1.μ (G1.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p + 1 = k)) /
        esum G1.μ G1.E +
      esum G1.μ (G1.E.filter (fun e => e.1.factorization p + 1 = k ∧ e.2.factorization p = k)) /
        esum G1.μ G1.E + c / 2 + η ^ ((9 : ℝ) / 5) := by
  set E1 := esum G1.μ G1.E with hE1d
  set V1 := wsum G1.μ G1.V with hV1d
  set W1 := wsum G1.μ G1.W with hW1d
  set Gp := alt_sh_plus G1 p k hp hpP1 with hGp
  set Ea := G1.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p + 1 = k)
    with hEa
  set Eb := G1.E.filter (fun e => e.1.factorization p + 1 = k ∧ e.2.factorization p = k)
    with hEb
  set B1 := G1.E.filter (fun e => e.1.factorization p = k ∧
    1 + 1 ≤ (k - e.2.factorization p) + (e.2.factorization p - k)) with hB1
  set B2 := G1.E.filter (fun e => e.2.factorization p = k ∧
    1 + 1 ≤ (e.1.factorization p - k) + (k - e.1.factorization p)) with hB2
  set B3 := G1.E.filter (fun e => ¬ e.1.factorization p = k ∧ ¬ e.2.factorization p = k)
    with hB3
  have hsub : G1.E ⊆ B1 ∪ B2 ∪ B3 ∪ Gp.E ∪ Ea ∪ Eb := by
    intro e he
    have hd : (e.1.factorization p = k ∧ e.2.factorization p = k) ∨
        (e.1.factorization p = k ∧ e.2.factorization p = k + 1) ∨
        (e.1.factorization p = k + 1 ∧ e.2.factorization p = k) ∨
        (e.1.factorization p = k ∧ e.2.factorization p + 1 = k) ∨
        (e.1.factorization p + 1 = k ∧ e.2.factorization p = k) ∨
        (e.1.factorization p = k ∧
          1 + 1 ≤ (k - e.2.factorization p) + (e.2.factorization p - k)) ∨
        (e.2.factorization p = k ∧
          1 + 1 ≤ (e.1.factorization p - k) + (k - e.1.factorization p)) ∨
        (¬ e.1.factorization p = k ∧ ¬ e.2.factorization p = k) := by omega
    rw [mem_union, mem_union, mem_union, mem_union, mem_union]
    rcases hd with h | h | h | h | h | h | h | h
    · left; left; right; exact mem_filter.2 ⟨he, Or.inl h⟩
    · left; left; right; exact mem_filter.2 ⟨he, Or.inr (Or.inl h)⟩
    · left; left; right; exact mem_filter.2 ⟨he, Or.inr (Or.inr h)⟩
    · left; right; exact mem_filter.2 ⟨he, h⟩
    · right; exact mem_filter.2 ⟨he, h⟩
    · left; left; left; left; left; exact mem_filter.2 ⟨he, h⟩
    · left; left; left; left; right; exact mem_filter.2 ⟨he, h⟩
    · left; left; left; right; exact mem_filter.2 ⟨he, h⟩
  have hcov : E1 ≤ esum G1.μ B1 + esum G1.μ B2 + esum G1.μ B3 + esum G1.μ Gp.E +
      esum G1.μ Ea + esum G1.μ Eb := by
    have h0 : E1 ≤ esum G1.μ (B1 ∪ B2 ∪ B3 ∪ Gp.E ∪ Ea ∪ Eb) := by
      unfold esum
      exact sum_le_sum_of_subset_of_nonneg hsub
        (fun i _ _ => mul_nonneg (G1.μ_nonneg _) (G1.μ_nonneg _))
    have u1 := alt_sh_esum_union_le G1 (B1 ∪ B2 ∪ B3 ∪ Gp.E ∪ Ea) Eb
    have u2 := alt_sh_esum_union_le G1 (B1 ∪ B2 ∪ B3 ∪ Gp.E) Ea
    have u3 := alt_sh_esum_union_le G1 (B1 ∪ B2 ∪ B3) Gp.E
    have u4 := alt_sh_esum_union_le G1 (B1 ∪ B2) B3
    have u5 := alt_sh_esum_union_le G1 B1 B2
    linarith
  have hVksplit : wsum G1.μ (vslice G1.V p k) +
      wsum G1.μ (G1.V.filter (fun v => ¬ v.factorization p = k)) = V1 := by
    unfold wsum vslice; exact sum_filter_add_sum_filter_not _ _ _
  have hWksplit : wsum G1.μ (vslice G1.W p k) +
      wsum G1.μ (G1.W.filter (fun w => ¬ w.factorization p = k)) = W1 := by
    unfold wsum vslice; exact sum_filter_add_sum_filter_not _ _ _
  have hB3le : esum G1.μ B3 ≤ η ^ ((9 : ℝ) / 5) * E1 := by
    have h := hsp (G1.V.filter (fun v => ¬ v.factorization p = k)) (filter_subset _ _)
      (G1.W.filter (fun w => ¬ w.factorization p = k)) (filter_subset _ _)
      (by rw [← hμ1]; linarith) (by rw [← hμ1]; linarith)
    rw [← hμ1] at h
    have hset : G1.E.filter (fun e => e.1 ∈ G1.V.filter (fun v => ¬ v.factorization p = k) ∧
        e.2 ∈ G1.W.filter (fun w => ¬ w.factorization p = k)) = B3 := by
      apply filter_congr
      intro e he
      obtain ⟨hv, hw⟩ := mem_product.1 (G1.E_sub he)
      simp only [mem_filter]
      exact ⟨fun h => ⟨h.1.2, h.2.2⟩, fun h => ⟨⟨hv, h.1⟩, ⟨hw, h.2⟩⟩⟩
    rw [hset] at h
    exact h
  have e1 : esum G1.μ B1 ≤ E1 * c / 4 := by
    refine le_trans hbad1 (le_of_eq ?_); rw [hc]; field_simp
  have e2 : esum G1.μ B2 ≤ E1 * c / 4 := by
    refine le_trans hbad2 (le_of_eq ?_); rw [hc]; field_simp
  have : E1 * 1 ≤ E1 * (esum G1.μ Gp.E / E1 + esum G1.μ Ea / E1 + esum G1.μ Eb / E1 + c / 2 +
      η ^ ((9 : ℝ) / 5)) := by
    have ex : E1 * (esum G1.μ Gp.E / E1 + esum G1.μ Ea / E1 + esum G1.μ Eb / E1 + c / 2 +
        η ^ ((9 : ℝ) / 5)) =
        esum G1.μ Gp.E + esum G1.μ Ea + esum G1.μ Eb + E1 * c / 2 +
          η ^ ((9 : ℝ) / 5) * E1 := by
      field_simp
    rw [ex]; linarith
  exact le_of_mul_le_mul_left this hE1
theorem alt_sh_xp (G1 : GCDGraph) (p k : ℕ) (hp : p.Prime) (hpP1 : p ∉ G1.P)
    (hq1 : 0 < G1.quality) (hE1 : 0 < esum G1.μ G1.E) (hV1 : 0 < wsum G1.μ G1.V)
    (hW1 : 0 < wsum G1.μ G1.W) (hVkpos : 0 < wsum G1.μ (vslice G1.V p k))
    (hWkpos : 0 < wsum G1.μ (vslice G1.W p k))
    (c : ℝ) (hc : c = 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) (hc0 : 0 < c) (hc2 : c ≤ 1 / 2)
    (θ : ℝ) (hθ : θ = if 1 ≤ k then 1 / (p : ℝ) else 0) (hθ2 : θ ≤ 1 / 2)
    (hGp_good : (alt_sh_plus G1 p k hp hpP1).quality < G1.quality) :
    esum G1.μ (alt_sh_plus G1 p k hp hpP1).E / esum G1.μ G1.E <
      (9 * ((1 - wsum G1.μ (G1.V.filter (fun v => v.factorization p + 1 = k)) /
          wsum G1.μ G1.V) *
        (1 - wsum G1.μ (G1.W.filter (fun w => w.factorization p + 1 = k)) / wsum G1.μ G1.W) *
          (1 - c)) + (1 - θ) ^ 2 * (1 - c)) / 10 := by
  set E1 := esum G1.μ G1.E with hE1d
  set V1 := wsum G1.μ G1.V with hV1d
  set W1 := wsum G1.μ G1.W with hW1d
  set Gp := alt_sh_plus G1 p k hp hpP1 with hGp
  set Vm := G1.V.filter (fun v => v.factorization p + 1 = k) with hVm
  set Wm := G1.W.filter (fun w => w.factorization p + 1 = k) with hWm
  set a := wsum G1.μ Vm / V1 with ha
  set b := wsum G1.μ Wm / W1 with hb
  set xp := esum G1.μ Gp.E / E1 with hxp
  have hVmk := alt_sh_disj_le G1 G1.V (fun v => v.factorization p + 1 = k)
    (fun v => v.factorization p = k) (fun v h1 h2 => by omega)
  have hWmk := alt_sh_disj_le G1 G1.W (fun w => w.factorization p + 1 = k)
    (fun w => w.factorization p = k) (fun w h1 h2 => by omega)
  have hVpk : wsum G1.μ (vslice G1.V p k) ≤ wsum G1.μ Gp.V :=
    sum_le_sum_of_subset_of_nonneg
      (fun v hv => mem_filter.2 ⟨(mem_filter.1 hv).1, Or.inl (mem_filter.1 hv).2⟩)
      (fun i _ _ => G1.μ_nonneg i)
  have hWpk : wsum G1.μ (vslice G1.W p k) ≤ wsum G1.μ Gp.W :=
    sum_le_sum_of_subset_of_nonneg
      (fun v hv => mem_filter.2 ⟨(mem_filter.1 hv).1, Or.inl (mem_filter.1 hv).2⟩)
      (fun i _ _ => G1.μ_nonneg i)
  have hVp : 0 < wsum G1.μ Gp.V := lt_of_lt_of_le hVkpos hVpk
  have hWp : 0 < wsum G1.μ Gp.W := lt_of_lt_of_le hWkpos hWpk
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one hV1]
    have := alt_sh_wsum_nonneg G1 (vslice G1.V p k)
    have h' : wsum G1.μ Vm + wsum G1.μ (vslice G1.V p k) ≤ V1 := hVmk
    linarith
  have hb1 : b ≤ 1 := by
    rw [hb, div_le_one hW1]
    have := alt_sh_wsum_nonneg G1 (vslice G1.W p k)
    have h' : wsum G1.μ Wm + wsum G1.μ (vslice G1.W p k) ≤ W1 := hWmk
    linarith
  have hVpa : wsum G1.μ Gp.V ≤ (1 - a) * V1 := by
    have h := alt_sh_disj_le G1 G1.V
      (fun v => v.factorization p = k ∨ v.factorization p = k + 1)
      (fun v => v.factorization p + 1 = k) (fun v h1 h2 => by omega)
    have e : (1 - a) * V1 = V1 - wsum G1.μ Vm := by rw [ha]; field_simp
    rw [e]
    have : wsum G1.μ Gp.V + wsum G1.μ Vm ≤ V1 := h
    linarith
  have hWpb : wsum G1.μ Gp.W ≤ (1 - b) * W1 := by
    have h := alt_sh_disj_le G1 G1.W
      (fun v => v.factorization p = k ∨ v.factorization p = k + 1)
      (fun v => v.factorization p + 1 = k) (fun v h1 h2 => by omega)
    have e : (1 - b) * W1 = W1 - wsum G1.μ Wm := by rw [hb]; field_simp
    rw [e]
    have : wsum G1.μ Gp.W + wsum G1.μ Wm ≤ W1 := h
    linarith
  have hqp := alt_sh_plus_quality G1 p k hp hpP1 hE1 hV1 hW1 hVp hWp
  set Fp : ℝ := 1 / ((1 - θ) ^ 2 * (1 - c) ^ 10) with hFp
  have hFp0 : 0 < Fp := by
    rw [hFp]; apply div_pos one_pos; apply mul_pos
    · apply pow_pos; linarith
    · apply pow_pos; linarith
  have hXp : xp ^ 10 * (V1 / wsum G1.μ Gp.V) ^ 9 * (W1 / wsum G1.μ Gp.W) ^ 9 * Fp < 1 := by
    have h := hGp_good
    have hqp' : Gp.quality = G1.quality *
        (xp ^ 10 * (V1 / wsum G1.μ Gp.V) ^ 9 * (W1 / wsum G1.μ Gp.W) ^ 9 * Fp) := by
      rw [hqp, hxp, hFp, hθ, hc]; ring
    rw [hqp'] at h
    exact (mul_lt_iff_lt_one_right hq1).1 h
  have hxp0 : 0 ≤ xp := div_nonneg (alt_sh_esum_nonneg G1 _) hE1.le
  have hxp10 := alt_sh_bound1 xp V1 (wsum G1.μ Gp.V) W1 (wsum G1.μ Gp.W) a b Fp hV1 hW1 hVp hWp
    hVpa hWpb hFp0 hXp
  apply alt_sh_amgm xp _ _ hxp0
  · have : 0 ≤ 1 - a := by linarith
    have : 0 ≤ 1 - b := by linarith
    have : 0 ≤ 1 - c := by linarith
    positivity
  · have : 0 ≤ 1 - c := by linarith
    positivity
  · refine lt_of_lt_of_le hxp10 (le_of_eq ?_)
    rw [hFp]
    have h1 : (1 - θ) ≠ 0 := by linarith
    have h2 : (1 - c) ≠ 0 := by linarith
    field_simp
theorem alt_sh_xa (G1 : GCDGraph) (p k : ℕ) (hp : p.Prime) (hpP1 : p ∉ G1.P)
    (hp0 : (0 : ℝ) < p) (hq1 : 0 < G1.quality) (hE1 : 0 < esum G1.μ G1.E)
    (hV1 : 0 < wsum G1.μ G1.V) (hW1 : 0 < wsum G1.μ G1.W)
    (hVkpos : 0 < wsum G1.μ (vslice G1.V p k))
    (c : ℝ) (hc : c = 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) (hc2 : c ≤ 1 / 2)
    (θ : ℝ) (hθ : θ = if 1 ≤ k then 1 / (p : ℝ) else 0) (hθ0 : 0 ≤ θ)
    (hA : ¬ (1 ≤ k ∧ 0 < wsum G1.μ (G1.W.filter (fun w => w.factorization p + 1 = k)) ∧
      G1.quality ≤ (G1.restrictPrime p k (k - 1) hp hpP1).quality)) :
    esum G1.μ (G1.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p + 1 = k)) /
        esum G1.μ G1.E ≤
      (1 - c) * (9 * (wsum G1.μ (G1.W.filter (fun w => w.factorization p + 1 = k)) /
        wsum G1.μ G1.W) + θ) / 10 := by
  set E1 := esum G1.μ G1.E with hE1d
  set V1 := wsum G1.μ G1.V with hV1d
  set W1 := wsum G1.μ G1.W with hW1d
  set Wm := G1.W.filter (fun w => w.factorization p + 1 = k) with hWm
  set Ea := G1.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p + 1 = k)
    with hEa
  set b := wsum G1.μ Wm / W1 with hb
  set xa := esum G1.μ Ea / E1 with hxa
  have hb0 : 0 ≤ b := div_nonneg (alt_sh_wsum_nonneg G1 _) hW1.le
  have hxa0 : 0 ≤ xa := div_nonneg (alt_sh_esum_nonneg G1 _) hE1.le
  have hEa_le : esum G1.μ Ea ≤ wsum G1.μ (vslice G1.V p k) * wsum G1.μ Wm := by
    apply alt_sh_esum_le_prod
    intro e he
    obtain ⟨he, h1, h2⟩ := mem_filter.1 he
    obtain ⟨hv, hw⟩ := mem_product.1 (G1.E_sub he)
    exact mem_product.2 ⟨mem_filter.2 ⟨hv, h1⟩, mem_filter.2 ⟨hw, h2⟩⟩
  by_cases hk : 1 ≤ k ∧ 0 < wsum G1.μ Wm
  · have hqa : (G1.restrictPrime p k (k - 1) hp hpP1).quality < G1.quality := by
      by_contra h; push_neg at h; exact hA ⟨hk.1, hk.2, h⟩
    have hWeq : vslice G1.W p (k - 1) = Wm := by
      apply filter_congr; intro w _; omega
    have hWk1 : 0 < wsum G1.μ (vslice G1.W p (k - 1)) := by rw [hWeq]; exact hk.2
    have hqr := quality_restrictPrime G1 p k (k - 1) hp hpP1 hE1 hVkpos hWk1
    have hEeq : esum G1.μ (G1.restrictPrime p k (k - 1) hp hpP1).E = esum G1.μ Ea := by
      show esum G1.μ (G1.E.filter
        (fun e => e.1.factorization p = k ∧ e.2.factorization p = k - 1)) = _
      congr 1
      apply filter_congr; intro e _; omega
    have hd1 : (k - (k - 1)) + ((k - 1) - k) = 1 := by omega
    have hne : ¬ (k = k - 1 ∧ 1 ≤ k) := by omega
    rw [hEeq, hWeq, hd1, if_neg hne] at hqr
    have hX : xa ^ 10 * (V1 / wsum G1.μ (vslice G1.V p k)) ^ 9 * (W1 / wsum G1.μ Wm) ^ 9 *
        ((p : ℝ) / (1 - c) ^ 10) < 1 := by
      have hqr' : (G1.restrictPrime p k (k - 1) hp hpP1).quality = G1.quality *
          (xa ^ 10 * (V1 / wsum G1.μ (vslice G1.V p k)) ^ 9 * (W1 / wsum G1.μ Wm) ^ 9 *
            ((p : ℝ) / (1 - c) ^ 10)) := by
        rw [hqr, hxa, hc]; ring
      rw [hqr'] at hqa
      exact (mul_lt_iff_lt_one_right hq1).1 hqa
    have hWmb : wsum G1.μ Wm ≤ (1 - (1 - b)) * W1 := by
      rw [hb, sub_sub_cancel, div_mul_cancel₀ _ hW1.ne']
    have hVsub : wsum G1.μ (vslice G1.V p k) ≤ (1 - 0) * V1 := by
      rw [sub_zero, one_mul]
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => G1.μ_nonneg i)
    have hpc10 : 0 < (p : ℝ) / (1 - c) ^ 10 := by
      have : 0 < 1 - c := by linarith
      positivity
    have hx10 := alt_sh_bound1 xa V1 (wsum G1.μ (vslice G1.V p k)) W1 (wsum G1.μ Wm) 0 (1 - b)
      ((p : ℝ) / (1 - c) ^ 10) hV1 hW1 hVkpos hk.2 hVsub hWmb hpc10 hX
    have hlt := alt_sh_amgm xa (b * (1 - c)) ((1 - c) / p) hxa0
      (mul_nonneg hb0 (by linarith)) (div_nonneg (by linarith) hp0.le)
      (by
        refine lt_of_lt_of_le hx10 (le_of_eq ?_)
        have h2 : (1 - c) ≠ 0 := by linarith
        field_simp
        ring)
    have : θ = 1 / p := by rw [hθ, if_pos hk.1]
    rw [this]
    have e : (9 * (b * (1 - c)) + (1 - c) / p) / 10 = (1 - c) * (9 * b + 1 / p) / 10 := by ring
    linarith
  · have hWm0 : wsum G1.μ Wm = 0 := by
      by_contra h
      obtain ⟨w, hw, _⟩ := exists_ne_zero_of_sum_ne_zero h
      have hk1 : 1 ≤ k := by have := (mem_filter.1 hw).2; omega
      exact hk ⟨hk1, lt_of_le_of_ne (alt_sh_wsum_nonneg G1 _) (Ne.symm h)⟩
    have : esum G1.μ Ea ≤ 0 := by rw [hWm0, mul_zero] at hEa_le; exact hEa_le
    have hxa' : xa ≤ 0 := by rw [hxa]; exact div_nonpos_of_nonpos_of_nonneg this hE1.le
    have : 0 ≤ (1 - c) * (9 * b + θ) / 10 := by
      have : 0 ≤ 1 - c := by linarith
      positivity
    linarith
theorem alt_sh_xb (G1 : GCDGraph) (p k : ℕ) (hp : p.Prime) (hpP1 : p ∉ G1.P)
    (hp0 : (0 : ℝ) < p) (hq1 : 0 < G1.quality) (hE1 : 0 < esum G1.μ G1.E)
    (hV1 : 0 < wsum G1.μ G1.V) (hW1 : 0 < wsum G1.μ G1.W)
    (hWkpos : 0 < wsum G1.μ (vslice G1.W p k))
    (c : ℝ) (hc : c = 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) (hc2 : c ≤ 1 / 2)
    (θ : ℝ) (hθ : θ = if 1 ≤ k then 1 / (p : ℝ) else 0) (hθ0 : 0 ≤ θ)
    (hB : ¬ (1 ≤ k ∧ 0 < wsum G1.μ (G1.V.filter (fun v => v.factorization p + 1 = k)) ∧
      G1.quality ≤ (G1.restrictPrime p (k - 1) k hp hpP1).quality)) :
    esum G1.μ (G1.E.filter (fun e => e.1.factorization p + 1 = k ∧ e.2.factorization p = k)) /
        esum G1.μ G1.E ≤
      (1 - c) * (9 * (wsum G1.μ (G1.V.filter (fun v => v.factorization p + 1 = k)) /
        wsum G1.μ G1.V) + θ) / 10 := by
  set E1 := esum G1.μ G1.E with hE1d
  set V1 := wsum G1.μ G1.V with hV1d
  set W1 := wsum G1.μ G1.W with hW1d
  set Vm := G1.V.filter (fun v => v.factorization p + 1 = k) with hVm
  set Eb := G1.E.filter (fun e => e.1.factorization p + 1 = k ∧ e.2.factorization p = k)
    with hEb
  set a := wsum G1.μ Vm / V1 with ha
  set xb := esum G1.μ Eb / E1 with hxb
  have ha0 : 0 ≤ a := div_nonneg (alt_sh_wsum_nonneg G1 _) hV1.le
  have hxb0 : 0 ≤ xb := div_nonneg (alt_sh_esum_nonneg G1 _) hE1.le
  have hEb_le : esum G1.μ Eb ≤ wsum G1.μ Vm * wsum G1.μ (vslice G1.W p k) := by
    apply alt_sh_esum_le_prod
    intro e he
    obtain ⟨he, h1, h2⟩ := mem_filter.1 he
    obtain ⟨hv, hw⟩ := mem_product.1 (G1.E_sub he)
    exact mem_product.2 ⟨mem_filter.2 ⟨hv, h1⟩, mem_filter.2 ⟨hw, h2⟩⟩
  by_cases hk : 1 ≤ k ∧ 0 < wsum G1.μ Vm
  · have hqb : (G1.restrictPrime p (k - 1) k hp hpP1).quality < G1.quality := by
      by_contra h; push_neg at h; exact hB ⟨hk.1, hk.2, h⟩
    have hVeq : vslice G1.V p (k - 1) = Vm := by
      apply filter_congr; intro w _; omega
    have hVk1 : 0 < wsum G1.μ (vslice G1.V p (k - 1)) := by rw [hVeq]; exact hk.2
    have hqr := quality_restrictPrime G1 p (k - 1) k hp hpP1 hE1 hVk1 hWkpos
    have hEeq : esum G1.μ (G1.restrictPrime p (k - 1) k hp hpP1).E = esum G1.μ Eb := by
      show esum G1.μ (G1.E.filter
        (fun e => e.1.factorization p = k - 1 ∧ e.2.factorization p = k)) = _
      congr 1
      apply filter_congr; intro e _; omega
    have hd1 : ((k - 1) - k) + (k - (k - 1)) = 1 := by omega
    have hne : ¬ (k - 1 = k ∧ 1 ≤ k - 1) := by omega
    rw [hEeq, hVeq, hd1, if_neg hne] at hqr
    have hX : xb ^ 10 * (W1 / wsum G1.μ (vslice G1.W p k)) ^ 9 * (V1 / wsum G1.μ Vm) ^ 9 *
        ((p : ℝ) / (1 - c) ^ 10) < 1 := by
      have hqr' : (G1.restrictPrime p (k - 1) k hp hpP1).quality = G1.quality *
          (xb ^ 10 * (W1 / wsum G1.μ (vslice G1.W p k)) ^ 9 * (V1 / wsum G1.μ Vm) ^ 9 *
            ((p : ℝ) / (1 - c) ^ 10)) := by
        rw [hqr, hxb, hc]; ring
      rw [hqr'] at hqb
      exact (mul_lt_iff_lt_one_right hq1).1 hqb
    have hVma : wsum G1.μ Vm ≤ (1 - (1 - a)) * V1 := by
      rw [ha, sub_sub_cancel, div_mul_cancel₀ _ hV1.ne']
    have hWsub : wsum G1.μ (vslice G1.W p k) ≤ (1 - 0) * W1 := by
      rw [sub_zero, one_mul]
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => G1.μ_nonneg i)
    have hpc10 : 0 < (p : ℝ) / (1 - c) ^ 10 := by
      have : 0 < 1 - c := by linarith
      positivity
    have hx10 := alt_sh_bound1 xb W1 (wsum G1.μ (vslice G1.W p k)) V1 (wsum G1.μ Vm) 0 (1 - a)
      ((p : ℝ) / (1 - c) ^ 10) hW1 hV1 hWkpos hk.2 hWsub hVma hpc10 hX
    have hlt := alt_sh_amgm xb (a * (1 - c)) ((1 - c) / p) hxb0
      (mul_nonneg ha0 (by linarith)) (div_nonneg (by linarith) hp0.le)
      (by
        refine lt_of_lt_of_le hx10 (le_of_eq ?_)
        have h2 : (1 - c) ≠ 0 := by linarith
        field_simp
        ring)
    have : θ = 1 / p := by rw [hθ, if_pos hk.1]
    rw [this]
    have e : (9 * (a * (1 - c)) + (1 - c) / p) / 10 = (1 - c) * (9 * a + 1 / p) / 10 := by ring
    linarith
  · have hVm0 : wsum G1.μ Vm = 0 := by
      by_contra h
      obtain ⟨w, hw, _⟩ := exists_ne_zero_of_sum_ne_zero h
      have hk1 : 1 ≤ k := by have := (mem_filter.1 hw).2; omega
      exact hk ⟨hk1, lt_of_le_of_ne (alt_sh_wsum_nonneg G1 _) (Ne.symm h)⟩
    have : esum G1.μ Eb ≤ 0 := by rw [hVm0, zero_mul] at hEb_le; exact hEb_le
    have hxb' : xb ≤ 0 := by rw [hxb]; exact div_nonpos_of_nonpos_of_nonneg this hE1.le
    have : 0 ≤ (1 - c) * (9 * a + θ) / 10 := by
      have : 0 ≤ 1 - c := by linarith
      positivity
    linarith
theorem alt_sh_contra (G1 : GCDGraph) (p k : ℕ) (hp : p.Prime) (hpP1 : p ∉ G1.P)
    (hpT : T0 ≤ (p : ℝ)) (hp0 : (0 : ℝ) < p) (hp2 : (2 : ℝ) ≤ p) (hq1 : 0 < G1.quality)
    (hE1 : 0 < esum G1.μ G1.E) (hV1 : 0 < wsum G1.μ G1.V) (hW1 : 0 < wsum G1.μ G1.W)
    (η : ℝ) (hη : η = K40 / p) (hη1 : η < 1)
    (hVk : (1 - η) * wsum G1.μ G1.V ≤ wsum G1.μ (vslice G1.V p k))
    (hWk : (1 - η) * wsum G1.μ G1.W ≤ wsum G1.μ (vslice G1.W p k))
    (c : ℝ) (hc : c = 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) (hc0 : 0 < c) (hc2 : c ≤ 1 / 2)
    (hcov' : 1 ≤ esum G1.μ (alt_sh_plus G1 p k hp hpP1).E / esum G1.μ G1.E +
      esum G1.μ (G1.E.filter (fun e => e.1.factorization p = k ∧ e.2.factorization p + 1 = k)) /
        esum G1.μ G1.E +
      esum G1.μ (G1.E.filter (fun e => e.1.factorization p + 1 = k ∧ e.2.factorization p = k)) /
        esum G1.μ G1.E + c / 2 + η ^ ((9 : ℝ) / 5))
    (hGp_good : (alt_sh_plus G1 p k hp hpP1).quality < G1.quality)
    (hA : ¬ (1 ≤ k ∧ 0 < wsum G1.μ (G1.W.filter (fun w => w.factorization p + 1 = k)) ∧
      G1.quality ≤ (G1.restrictPrime p k (k - 1) hp hpP1).quality))
    (hB : ¬ (1 ≤ k ∧ 0 < wsum G1.μ (G1.V.filter (fun v => v.factorization p + 1 = k)) ∧
      G1.quality ≤ (G1.restrictPrime p (k - 1) k hp hpP1).quality)) : False := by
  have hVkpos : 0 < wsum G1.μ (vslice G1.V p k) :=
    lt_of_lt_of_le (mul_pos (by linarith) hV1) hVk
  have hWkpos : 0 < wsum G1.μ (vslice G1.W p k) :=
    lt_of_lt_of_le (mul_pos (by linarith) hW1) hWk
  set θ : ℝ := if 1 ≤ k then 1 / (p : ℝ) else 0 with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; split_ifs <;> positivity
  have hθ1 : θ ≤ 1 / p := by rw [hθ]; split_ifs <;> [exact le_rfl; positivity]
  have hθ2 : θ ≤ 1 / 2 := le_trans hθ1 (by rw [div_le_div_iff₀ hp0 (by norm_num)]; linarith)
  have hxpb := alt_sh_xp G1 p k hp hpP1 hq1 hE1 hV1 hW1 hVkpos hWkpos c hc hc0 hc2 θ hθ hθ2
    hGp_good
  have hxab := alt_sh_xa G1 p k hp hpP1 hp0 hq1 hE1 hV1 hW1 hVkpos c hc hc2 θ hθ hθ0 hA
  have hxbb := alt_sh_xb G1 p k hp hpP1 hp0 hq1 hE1 hV1 hW1 hWkpos c hc hc2 θ hθ hθ0 hB
  set V1 := wsum G1.μ G1.V with hV1d
  set W1 := wsum G1.μ G1.W with hW1d
  set Vm := G1.V.filter (fun v => v.factorization p + 1 = k) with hVm
  set Wm := G1.W.filter (fun w => w.factorization p + 1 = k) with hWm
  set a := wsum G1.μ Vm / V1 with ha
  set b := wsum G1.μ Wm / W1 with hb
  have ha0 : 0 ≤ a := div_nonneg (alt_sh_wsum_nonneg G1 _) hV1.le
  have hb0 : 0 ≤ b := div_nonneg (alt_sh_wsum_nonneg G1 _) hW1.le
  have hVmk := alt_sh_disj_le G1 G1.V (fun v => v.factorization p + 1 = k)
    (fun v => v.factorization p = k) (fun v h1 h2 => by omega)
  have hWmk := alt_sh_disj_le G1 G1.W (fun w => w.factorization p + 1 = k)
    (fun w => w.factorization p = k) (fun w h1 h2 => by omega)
  have haη : a ≤ η := by
    rw [ha, div_le_iff₀ hV1]
    have h' : wsum G1.μ Vm + wsum G1.μ (vslice G1.V p k) ≤ V1 := hVmk
    nlinarith
  have hbη : b ≤ η := by
    rw [hb, div_le_iff₀ hW1]
    have h' : wsum G1.μ Wm + wsum G1.μ (vslice G1.W p k) ≤ W1 := hWmk
    nlinarith
  have hnum := alt_sh_numeric p hpT
  have hsmall : η ^ 2 + θ ^ 2 + η ^ ((9 : ℝ) / 5) ≤ c / 2 := by
    have : θ ^ 2 ≤ (1 / (p : ℝ)) ^ 2 := pow_le_pow_left₀ hθ0 hθ1 2
    rw [hη, hc]
    linarith
  exact alt_sh_final _ _ _ a b c θ (η ^ ((9 : ℝ) / 5)) η ha0 hb0 haη hbη hc0.le (by linarith)
    hθ0 hxpb hxab hxbb hcov' hsmall
theorem lemma141 (G : GCDGraph) (hδ : 0 < G.density) (p : ℕ) (hp : p.Prime) (hpP : p ∉ G.P)
    (hpT : T0 ≤ (p : ℝ)) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ G'.P = insert p G.P ∧ G'.R ⊆ G.R.erase p ∧
      0 < G'.quality ∧ G.quality ≤ G'.quality := by
  have hq : 0 < G.quality := (quality_pos_iff G).2 hδ
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hK40 : (0 : ℝ) < K40 := by unfold K40; positivity
  have hK : K40 < p := by
    have : K40 < T0 := by simp only [K40, T0]; exact pow_lt_pow_right₀ (by norm_num) (by norm_num)
    linarith
  have hpT' : T0 < (p : ℝ) := by
    rcases lt_or_eq_of_le hpT with h | h
    · exact h
    · exfalso
      have hpe : p = 10 ^ 2000 := by
        have : (p : ℝ) = ((10 ^ 2000 : ℕ) : ℝ) := by
          rw [← h]; unfold T0; push_cast; ring
        exact_mod_cast this
      have h2 : 2 ∣ p := by
        rw [hpe]; exact dvd_pow (by norm_num : (2 : ℕ) ∣ 10) (by norm_num)
      have h2p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2
      have h10 : 10 ≤ 10 ^ 2000 := Nat.le_self_pow (by norm_num) 10
      rw [← h2p] at hpe
      generalize (10 : ℕ) ^ 2000 = X at hpe h10
      omega
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  set c : ℝ := 1 / (p : ℝ) ^ ((31 : ℝ) / 30) with hc
  have hpc : (p : ℝ) ≤ (p : ℝ) ^ ((31 : ℝ) / 30) := by
    conv_lhs => rw [← Real.rpow_one (p : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc2 : c ≤ 1 / 2 := by
    rw [hc, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set η : ℝ := K40 / p with hη
  have hη0 : 0 < η := div_pos hK40 hp0
  have hη1 : η < 1 := (div_lt_one hp0).2 hK
  obtain ⟨G1, hG1, hP1, hf1, hg1, hδ1, hqq1, hsp⟩ :=
    exists_sparse_small_sets_subgraph G hδ η hη0 hη1
  have hμ1 : G1.μ = G.μ := hG1.1
  have hq1 : 0 < G1.quality := (quality_pos_iff G1).2 hδ1
  have hpP1 : p ∉ G1.P := hP1 ▸ hpP
  have finish : ∀ G' : GCDGraph, G'.IsSubgraph G1 → G'.P = insert p G1.P →
      G'.R ⊆ G1.R.erase p → G1.quality ≤ G'.quality →
      ∃ G' : GCDGraph, G'.IsSubgraph G ∧ G'.P = insert p G.P ∧ G'.R ⊆ G.R.erase p ∧
        0 < G'.quality ∧ G.quality ≤ G'.quality := by
    intro G' h1 h2 h3 h4
    exact ⟨G', h1.trans hG1, by rw [h2, hP1], h3.trans (erase_subset_erase p (R_mono hG1)),
      lt_of_lt_of_le hq (hqq1.trans h4), hqq1.trans h4⟩
  have finishR : ∀ k l, G1.quality ≤ (G1.restrictPrime p k l hp hpP1).quality →
      ∃ G' : GCDGraph, G'.IsSubgraph G ∧ G'.P = insert p G.P ∧ G'.R ⊆ G.R.erase p ∧
        0 < G'.quality ∧ G.quality ≤ G'.quality :=
    fun k l h => finish _ (restrictPrime_isSubgraph G1 p k l hp hpP1) rfl
      (R_restrictPrime_subset G1 p k l hp hpP1) h
  rcases lemma122 G1 hδ1 p hp hpP1 hK with ⟨k, l, _, hr⟩ | ⟨k, hVk, hWk⟩
  · apply finishR k l
    have h1 : (1 : ℝ) ≤ 2 ^ (if k ≠ l then 1 else 0) := one_le_pow₀ (by norm_num)
    have h2 : min 1 ((G1.restrictPrime p k l hp hpP1).density / G1.density) *
        ((G1.restrictPrime p k l hp hpP1).quality / G1.quality) ≤
        (G1.restrictPrime p k l hp hpP1).quality / G1.quality :=
      mul_le_of_le_one_left (div_nonneg (quality_nonneg _) hq1.le) (min_le_left _ _)
    exact (one_le_div hq1).1 (by linarith)
  have hpr1 : T0 < (p : ℝ) ^ (1 : ℕ) := by rw [pow_one]; exact hpT'
  rcases lemma113 G1 hδ1 p hp hpP1 1 k le_rfl hpr1 hWk with ⟨l, _, h2q, _⟩ | hbad1
  · exact finishR k l (by linarith)
  rcases lemma114 G1 hδ1 p hp hpP1 1 k le_rfl hpr1 hVk with ⟨l, _, h2q, _⟩ | hbad2
  · exact finishR l k (by linarith)
  obtain ⟨hE1, hV1, hW1⟩ := alt_sh_pos G1 hδ1
  have hcov' := alt_sh_cover G G1 p k hp hpP1 hμ1 hE1 η hVk hWk hsp c hc hbad1 hbad2
  by_cases hGp_good : G1.quality ≤ (alt_sh_plus G1 p k hp hpP1).quality
  · exact finish _ (alt_sh_plus_isSubgraph G1 p k hp hpP1) rfl (alt_sh_plus_R G1 p k hp hpP1)
      hGp_good
  by_cases hA_good : 1 ≤ k ∧ 0 < wsum G1.μ (G1.W.filter (fun w => w.factorization p + 1 = k)) ∧
      G1.quality ≤ (G1.restrictPrime p k (k - 1) hp hpP1).quality
  · exact finishR k (k - 1) hA_good.2.2
  by_cases hB_good : 1 ≤ k ∧ 0 < wsum G1.μ (G1.V.filter (fun v => v.factorization p + 1 = k)) ∧
      G1.quality ≤ (G1.restrictPrime p (k - 1) k hp hpP1).quality
  · exact finishR (k - 1) k hB_good.2.2
  exact alt_sh_contra G1 p k hp hpP1 hpT hp0 hp2 hq1 hE1 hV1 hW1 η hη hη1 hVk hWk c hc hc0 hc2
    hcov' (lt_of_not_ge hGp_good) hA_good hB_good |>.elim
theorem prop82 (G : GCDGraph) (hδ : 0 < G.density) (hR : ∀ p ∈ G.R, T0 < (p : ℝ))
    (hflat : G.Rflat = ∅) (hsharp : G.Rsharp.Nonempty) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ 0 < G'.density ∧ G.P ⊂ G'.P ∧ G'.P ⊆ G.P ∪ G.R ∧
      G'.R ⊂ G.R ∧ G.quality ≤ G'.quality := by
  classical
  obtain ⟨p, hp⟩ := hsharp
  have hpR : p ∈ G.R := (mem_filter.1 hp).1
  have hpp : p.Prime := G.prime_of_mem_R hpR
  have hpP : p ∉ G.P := G.not_mem_P_of_mem_R hpR
  obtain ⟨G', hG', hP', hR', hq'pos, hqq'⟩ := lemma141 G hδ p hpp hpP (hR p hpR).le
  refine ⟨G', hG', (quality_pos_iff G').1 hq'pos, ?_, ?_, ?_, hqq'⟩
  · rw [hP']; exact ssubset_insert hpP
  · rw [hP']
    intro q hq
    rcases mem_insert.1 hq with rfl | hq
    · exact mem_union_right _ hpR
    · exact mem_union_left _ hq
  · exact lt_of_le_of_lt hR' (erase_ssubset hpR)
end GCDGraph
end DuffinSchaeffer
end Port24_Parts_SharpPrimes

section Port24_Parts_RemoveR
open Finset
namespace DuffinSchaeffer
theorem alt84_sum_union_le {α : Type*} [DecidableEq α] (s t : Finset α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) : ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  have := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  have h0 : 0 ≤ ∑ x ∈ s ∩ t, f x := Finset.sum_nonneg (fun _ _ => hf _)
  linarith
theorem alt84_esum_le (μ : ℕ → ℝ) (hμ : ∀ n, 0 ≤ μ n) (S : Finset (ℕ × ℕ)) (A B : Finset ℕ)
    (h : S ⊆ A ×ˢ B) : esum μ S ≤ wsum μ A * wsum μ B := by
  unfold esum wsum
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  exact Finset.sum_le_sum_of_subset_of_nonneg h (fun e _ _ => mul_nonneg (hμ _) (hμ _))
theorem alt84_inv_sq (A : Finset ℕ) (N : ℝ) (hN : 1 ≤ N) (hA : ∀ a ∈ A, N ≤ a) :
    ∑ a ∈ A, ((a : ℝ) ^ 2)⁻¹ ≤ 2 / N := by
  set m := ⌈N⌉₊ with hm
  have hNm : N ≤ m := Nat.le_ceil N
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := le_trans hN hNm
    exact_mod_cast this
  have hsub : A ⊆ Ioo (m - 1) (A.sup id + 1) := by
    intro a ha
    rw [Finset.mem_Ioo]
    constructor
    · have : m ≤ a := Nat.ceil_le.2 (hA a ha)
      omega
    · have := Finset.le_sup (f := id) ha
      simp only [id] at this
      omega
  calc ∑ a ∈ A, ((a : ℝ) ^ 2)⁻¹ ≤ ∑ a ∈ Ioo (m - 1) (A.sup id + 1), ((a : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 2 / (((m - 1 : ℕ) : ℝ) + 1) := sum_Ioo_inv_sq_le _ _
    _ = 2 / (m : ℝ) := by rw [Nat.cast_sub hm1]; ring_nf
    _ ≤ 2 / N := by
        apply div_le_div_of_nonneg_left (by norm_num) (by linarith) hNm
theorem alt84_T0_log : Real.log T0 = 2000 * Real.log 10 := by
  unfold T0; rw [Real.log_pow]; push_cast; ring
theorem alt84_log10 : 2 < Real.log 10 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h1 := Real.exp_one_lt_d9
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [this]
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  nlinarith
theorem alt84_log51 : Real.log 51 ≤ 4 - 1 / 39 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : Real.exp (4 - 1 / 39) = Real.exp 1 ^ 4 * Real.exp (-(1 / 39)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [h1]
  have h2 : (2.7182818283 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 4
  have h3 : -(1 / 39 : ℝ) + 1 ≤ Real.exp (-(1 / 39)) := Real.add_one_le_exp _
  have h4 : 0 ≤ Real.exp 1 ^ 4 := by positivity
  nlinarith
theorem alt84_mertens (t : ℝ) (ht : T0 ≤ t) :
    Real.log (Real.log (t ^ (50 : ℕ)) / Real.log (t - 1)) + 100 / Real.log (t - 1) ≤ 4 := by
  have hT : (4 : ℝ) ≤ T0 := by
    unfold T0; exact le_trans (by norm_num) (le_self_pow₀ (by norm_num : (1:ℝ) ≤ 10) (by norm_num))
  have ht4 : 4 ≤ t := le_trans hT ht
  have hl2 := Real.log_two_lt_d9
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl10 := alt84_log10
  have hlogt : 2000 * Real.log 10 ≤ Real.log t := by
    rw [← alt84_T0_log]; exact Real.log_le_log (by unfold T0; positivity) ht
  have hlt1 : Real.log t ≤ Real.log 2 + Real.log (t - 1) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) (by linarith)
  have hL : 3999 ≤ Real.log (t - 1) := by linarith
  have hLpos : 0 < Real.log (t - 1) := by linarith
  have hratio : Real.log (t ^ (50 : ℕ)) / Real.log (t - 1) ≤ 51 := by
    rw [div_le_iff₀ hLpos, Real.log_pow]
    push_cast
    linarith
  have hratio0 : 0 < Real.log (t ^ (50 : ℕ)) / Real.log (t - 1) := by
    apply div_pos _ hLpos
    rw [Real.log_pow]; push_cast; linarith
  have h1 : Real.log (Real.log (t ^ (50 : ℕ)) / Real.log (t - 1)) ≤ Real.log 51 :=
    Real.log_le_log hratio0 hratio
  have h2 : 100 / Real.log (t - 1) ≤ 100 / 3999 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
  have h3 := alt84_log51
  have h4 : (100 : ℝ) / 3999 ≤ 1 / 39 := by norm_num
  linarith
theorem alt84_not_dvd (v w p : ℕ) (hv : 0 < v) (hw : 0 < w) (hp : p.Prime)
    (h : v.factorization p = w.factorization p) : ¬ p ∣ coprimePart v w := by
  intro hdvd
  have hv0 : v ≠ 0 := hv.ne'
  have hw0 : w ≠ 0 := hw.ne'
  have hg : (Nat.gcd v w).factorization p = v.factorization p := by
    rw [Nat.factorization_gcd hv0 hw0, Finsupp.inf_apply, h, inf_idem]
  have h1 : (v / Nat.gcd v w).factorization p = 0 := by
    rw [Nat.factorization_div (Nat.gcd_dvd_left v w), Finsupp.tsub_apply, hg, Nat.sub_self]
  have h2 : (w / Nat.gcd v w).factorization p = 0 := by
    rw [Nat.factorization_div (Nat.gcd_dvd_right v w), Finsupp.tsub_apply, hg, h, Nat.sub_self]
  have hvg0 : v / Nat.gcd v w ≠ 0 :=
    (Nat.div_pos (Nat.gcd_le_left w hv) (Nat.gcd_pos_of_pos_left w hv)).ne'
  have hwg0 : w / Nat.gcd v w ≠ 0 :=
    (Nat.div_pos (Nat.gcd_le_right v hw) (Nat.gcd_pos_of_pos_right v hw)).ne'
  unfold coprimePart at hdvd
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with hd | hd
  · rcases (Nat.factorization_eq_zero_iff _ _).1 h1 with h' | h' | h'
    · exact h' hp
    · exact h' hd
    · exact hvg0 h'
  · rcases (Nat.factorization_eq_zero_iff _ _).1 h2 with h' | h' | h'
    · exact h' hp
    · exact h' hd
    · exact hwg0 h'
theorem alt84_coprimePart_ne_zero (v w : ℕ) (hv : 0 < v) (hw : 0 < w) : coprimePart v w ≠ 0 := by
  unfold coprimePart
  apply Nat.mul_ne_zero
  · exact (Nat.div_pos (Nat.gcd_le_left w hv) (Nat.gcd_pos_of_pos_left w hv)).ne'
  · exact (Nat.div_pos (Nat.gcd_le_right v hw) (Nat.gcd_pos_of_pos_right v hw)).ne'
namespace GCDGraph
theorem alt84_sharp_bound (G : GCDGraph) (p : ℕ) (hp : p.Prime) (hs : G.IsSharp p) :
    esum G.μ (G.E.filter (fun e => p ∣ coprimePart e.1 e.2)) ≤
      2 * (K40 / p) * (wsum G.μ G.V * wsum G.μ G.W) := by
  classical
  obtain ⟨k, hVk, hWk⟩ := hs
  have hsub : G.E.filter (fun e => p ∣ coprimePart e.1 e.2) ⊆
      G.E.filter (fun e => e.1.factorization p ≠ k) ∪
        G.E.filter (fun e => e.2.factorization p ≠ k) := by
    intro e he
    obtain ⟨he, hd⟩ := Finset.mem_filter.1 he
    obtain ⟨hv, hw⟩ := Finset.mem_product.1 (G.E_sub he)
    by_contra hc
    simp only [Finset.mem_union, Finset.mem_filter, not_or, not_and, not_not] at hc
    have h1 := hc.1 he
    have h2 := hc.2 he
    exact alt84_not_dvd e.1 e.2 p (G.V_pos _ hv) (G.W_pos _ hw) hp (h1.trans h2.symm) hd
  have hnn : ∀ e : ℕ × ℕ, 0 ≤ G.μ e.1 * G.μ e.2 := fun e => mul_nonneg (G.μ_nonneg _) (G.μ_nonneg _)
  have hA : esum G.μ (G.E.filter (fun e => e.1.factorization p ≠ k)) ≤
      wsum G.μ (G.V.filter (fun v => v.factorization p ≠ k)) * wsum G.μ G.W := by
    apply alt84_esum_le G.μ G.μ_nonneg
    intro e he
    obtain ⟨he, hk⟩ := Finset.mem_filter.1 he
    obtain ⟨hv, hw⟩ := Finset.mem_product.1 (G.E_sub he)
    exact Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨hv, hk⟩, hw⟩
  have hB : esum G.μ (G.E.filter (fun e => e.2.factorization p ≠ k)) ≤
      wsum G.μ G.V * wsum G.μ (G.W.filter (fun w => w.factorization p ≠ k)) := by
    apply alt84_esum_le G.μ G.μ_nonneg
    intro e he
    obtain ⟨he, hk⟩ := Finset.mem_filter.1 he
    obtain ⟨hv, hw⟩ := Finset.mem_product.1 (G.E_sub he)
    exact Finset.mem_product.2 ⟨hv, Finset.mem_filter.2 ⟨hw, hk⟩⟩
  have hV' : wsum G.μ (G.V.filter (fun v => v.factorization p ≠ k)) ≤ K40 / p * wsum G.μ G.V := by
    have := Finset.sum_filter_add_sum_filter_not G.V (fun v => v.factorization p = k) G.μ
    unfold wsum vslice at *
    linarith
  have hW' : wsum G.μ (G.W.filter (fun w => w.factorization p ≠ k)) ≤ K40 / p * wsum G.μ G.W := by
    have := Finset.sum_filter_add_sum_filter_not G.W (fun w => w.factorization p = k) G.μ
    unfold wsum vslice at *
    linarith
  have hV0 : 0 ≤ wsum G.μ G.V := Finset.sum_nonneg (fun _ _ => G.μ_nonneg _)
  have hW0 : 0 ≤ wsum G.μ G.W := Finset.sum_nonneg (fun _ _ => G.μ_nonneg _)
  calc esum G.μ (G.E.filter (fun e => p ∣ coprimePart e.1 e.2))
      ≤ esum G.μ (G.E.filter (fun e => e.1.factorization p ≠ k) ∪
          G.E.filter (fun e => e.2.factorization p ≠ k)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => hnn e)
    _ ≤ esum G.μ (G.E.filter (fun e => e.1.factorization p ≠ k)) +
          esum G.μ (G.E.filter (fun e => e.2.factorization p ≠ k)) :=
        alt84_sum_union_le _ _ _ hnn
    _ ≤ K40 / p * wsum G.μ G.V * wsum G.μ G.W + wsum G.μ G.V * (K40 / p * wsum G.μ G.W) := by
        apply add_le_add
        · exact le_trans hA (mul_le_mul_of_nonneg_right hV' hW0)
        · exact le_trans hB (mul_le_mul_of_nonneg_left hW' hV0)
    _ = 2 * (K40 / p) * (wsum G.μ G.V * wsum G.μ G.W) := by ring
theorem lemma84 (G : GCDGraph) (t : ℝ) (ht : T0 ≤ t) (hδ : 0 < G.density)
    (hflat : G.Rflat = ∅) (hδt : (10 / t) ^ (50 : ℕ) ≤ G.density)
    (hE : ∀ e ∈ G.E, 10 ≤ Lsum t e.1 e.2) :
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ G'.V = G.V ∧ G'.W = G.W ∧ G'.P = G.P ∧ G'.f = G.f ∧
      G'.g = G.g ∧ 0 < G'.quality ∧ G.quality / 2 ≤ G'.quality ∧
      ∀ e ∈ G'.E, 5 ≤ ∑ p ∈ (coprimePart e.1 e.2).primeFactors.filter
        (fun p : ℕ => t ≤ (p : ℝ) ∧ p ∉ G.R), (1 : ℝ) / p := by
  classical
  have hE0 : 0 < esum G.μ G.E := (G.density_pos_iff).1 hδ
  have hV0 := G.wsum_V_pos_of_density_pos hδ
  have hW0 := G.wsum_W_pos_of_density_pos hδ
  have hq0 : 0 < G.quality := (G.quality_pos_iff).2 hδ
  have hT1 : (4 : ℝ) ≤ T0 := by
    unfold T0; exact le_trans (by norm_num) (le_self_pow₀ (by norm_num : (1:ℝ) ≤ 10) (by norm_num))
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  set N : ℝ := t ^ (50 : ℕ) with hN
  have htN : t ≤ N := by
    calc t = t ^ 1 := (pow_one t).symm
      _ ≤ t ^ (50 : ℕ) := pow_le_pow_right₀ ht1 (by norm_num)
  have hN1 : 1 ≤ N := le_trans ht1 htN
  have hN0 : 0 < N := by linarith
  have hsharp : ∀ p ∈ G.R, G.IsSharp p := by
    intro p hp
    have := (Finset.filter_eq_empty_iff.1 hflat) hp
    simpa using this
  have hcp0 : ∀ e ∈ G.E, coprimePart e.1 e.2 ≠ 0 := by
    intro e he
    obtain ⟨hv, hw⟩ := Finset.mem_product.1 (G.E_sub he)
    exact alt84_coprimePart_ne_zero _ _ (G.V_pos _ hv) (G.W_pos _ hw)
  set S : ℕ × ℕ → ℝ := fun e => ∑ p ∈ (coprimePart e.1 e.2).primeFactors.filter
    (fun p => p ∈ G.R ∧ N ≤ (p : ℝ)), (1 : ℝ) / p with hSdef
  have hS0 : ∀ e, 0 ≤ S e := fun e => Finset.sum_nonneg (fun _ _ => by positivity)
  set R' : Finset ℕ := G.R.filter (fun p : ℕ => N ≤ (p : ℝ)) with hR'
  have hSe : ∀ e ∈ G.E, S e = ∑ p ∈ R', if p ∣ coprimePart e.1 e.2 then (1 : ℝ) / p else 0 := by
    intro e he
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors, hR']
    constructor
    · rintro ⟨⟨_, hdvd, _⟩, hR, hNp⟩; exact ⟨⟨hR, hNp⟩, hdvd⟩
    · rintro ⟨⟨hR, hNp⟩, hdvd⟩; exact ⟨⟨G.prime_of_mem_R hR, hdvd, hcp0 e he⟩, hR, hNp⟩
  have hkey : ∑ e ∈ G.E, G.μ e.1 * G.μ e.2 * S e ≤ esum G.μ G.E / 100 := by
    have h1 : ∑ e ∈ G.E, G.μ e.1 * G.μ e.2 * S e =
        ∑ p ∈ R', (1 : ℝ) / p * esum G.μ (G.E.filter (fun e => p ∣ coprimePart e.1 e.2)) := by
      rw [Finset.sum_congr rfl (fun e he => by rw [hSe e he, Finset.mul_sum]), Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      unfold esum
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> ring
    have h2 : ∀ p ∈ R', (1 : ℝ) / p * esum G.μ (G.E.filter (fun e => p ∣ coprimePart e.1 e.2)) ≤
        2 * K40 * (wsum G.μ G.V * wsum G.μ G.W) * ((p : ℝ) ^ 2)⁻¹ := by
      intro p hp
      have hpR := (Finset.mem_filter.1 hp).1
      have hb := G.alt84_sharp_bound p (G.prime_of_mem_R hpR) (hsharp p hpR)
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (G.prime_of_mem_R hpR).pos
      calc (1 : ℝ) / p * esum G.μ (G.E.filter (fun e => p ∣ coprimePart e.1 e.2))
          ≤ (1 : ℝ) / p * (2 * (K40 / p) * (wsum G.μ G.V * wsum G.μ G.W)) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = 2 * K40 * (wsum G.μ G.V * wsum G.μ G.W) * ((p : ℝ) ^ 2)⁻¹ := by
            field_simp
    have h3 : ∑ p ∈ R', ((p : ℝ) ^ 2)⁻¹ ≤ 2 / N :=
      alt84_inv_sq R' N hN1 (fun a ha => (Finset.mem_filter.1 ha).2)
    have hK : (0 : ℝ) < K40 := by unfold K40; positivity
    have hVW : 0 < wsum G.μ G.V * wsum G.μ G.W := mul_pos hV0 hW0
    have hEeq : esum G.μ G.E = G.density * (wsum G.μ G.V * wsum G.μ G.W) := by
      unfold density; field_simp
    have hδN : (10 : ℝ) ^ 50 / N ≤ G.density := by
      rw [hN, ← div_pow]; exact hδt
    rw [h1]
    calc ∑ p ∈ R', (1 : ℝ) / p * esum G.μ (G.E.filter (fun e => p ∣ coprimePart e.1 e.2))
        ≤ ∑ p ∈ R', 2 * K40 * (wsum G.μ G.V * wsum G.μ G.W) * ((p : ℝ) ^ 2)⁻¹ :=
          Finset.sum_le_sum h2
      _ = 2 * K40 * (wsum G.μ G.V * wsum G.μ G.W) * ∑ p ∈ R', ((p : ℝ) ^ 2)⁻¹ := by
          rw [Finset.mul_sum]
      _ ≤ 2 * K40 * (wsum G.μ G.V * wsum G.μ G.W) * (2 / N) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ (10 : ℝ) ^ 50 / N * (wsum G.μ G.V * wsum G.μ G.W) / 100 := by
          have hXN : 0 ≤ (wsum G.μ G.V * wsum G.μ G.W) / N := by positivity
          have e1 : 2 * K40 * (wsum G.μ G.V * wsum G.μ G.W) * (2 / N) =
              4 * 10 ^ 40 * ((wsum G.μ G.V * wsum G.μ G.W) / N) := by unfold K40; ring
          have e2 : (10 : ℝ) ^ 50 / N * (wsum G.μ G.V * wsum G.μ G.W) / 100 =
              10 ^ 48 * ((wsum G.μ G.V * wsum G.μ G.W) / N) := by ring
          rw [e1, e2]
          nlinarith
      _ ≤ esum G.μ G.E / 100 := by
          rw [hEeq]
          have := mul_le_mul_of_nonneg_right hδN hVW.le
          linarith
  set E' := G.E.filter (fun e => S e ≤ 1) with hE'
  have hbad : esum G.μ (G.E.filter (fun e => ¬ S e ≤ 1)) ≤ esum G.μ G.E / 100 := by
    calc esum G.μ (G.E.filter (fun e => ¬ S e ≤ 1))
        ≤ ∑ e ∈ G.E.filter (fun e => ¬ S e ≤ 1), G.μ e.1 * G.μ e.2 * S e := by
          unfold esum
          apply Finset.sum_le_sum
          intro e he
          have h1 : 1 ≤ S e := le_of_lt (not_le.1 (Finset.mem_filter.1 he).2)
          have h0 : 0 ≤ G.μ e.1 * G.μ e.2 := mul_nonneg (G.μ_nonneg _) (G.μ_nonneg _)
          nlinarith
      _ ≤ ∑ e ∈ G.E, G.μ e.1 * G.μ e.2 * S e :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun e _ _ => mul_nonneg (mul_nonneg (G.μ_nonneg _) (G.μ_nonneg _)) (hS0 e))
      _ ≤ esum G.μ G.E / 100 := hkey
  have hsplit : esum G.μ E' + esum G.μ (G.E.filter (fun e => ¬ S e ≤ 1)) = esum G.μ G.E :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hE'ge : 99 / 100 * esum G.μ G.E ≤ esum G.μ E' := by linarith
  have hE'pos : 0 < esum G.μ E' := by linarith
  let G' := G.induce G.V G.W E' (subset_refl _) (subset_refl _) (Finset.filter_subset _ _)
    ((Finset.filter_subset _ _).trans G.E_sub)
  have hq : G'.quality = G.quality * (esum G.μ E' / esum G.μ G.E) ^ 10 := by
    have hd : G'.density = esum G.μ E' / (wsum G.μ G.V * wsum G.μ G.W) := rfl
    have hqf : ∏ p ∈ G'.P, G'.qualityFactor p = ∏ p ∈ G.P, G.qualityFactor p := rfl
    have hVV : wsum G'.μ G'.V = wsum G.μ G.V := rfl
    have hWW : wsum G'.μ G'.W = wsum G.μ G.W := rfl
    unfold quality
    rw [hd, hqf, hVV, hWW]
    unfold density
    rw [div_pow, div_pow, div_pow]
    field_simp
  have hx : 99 / 100 ≤ esum G.μ E' / esum G.μ G.E := by rw [le_div_iff₀ hE0]; linarith
  refine ⟨G', ⟨rfl, subset_refl _, subset_refl _, Finset.filter_subset _ _, subset_refl _,
    fun p _ => ⟨rfl, rfl⟩⟩, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · rw [hq]; positivity
  · rw [hq]
    have h1 : (99 / 100 : ℝ) ^ 10 ≤ (esum G.μ E' / esum G.μ G.E) ^ 10 :=
      pow_le_pow_left₀ (by norm_num) hx 10
    have h2 : (1 / 2 : ℝ) ≤ (99 / 100) ^ 10 := by norm_num
    nlinarith
  · intro e he
    have he' : e ∈ E' := he
    obtain ⟨heE, hS1⟩ := Finset.mem_filter.1 he'
    have hL := hE e heE
    unfold Lsum at hL
    set A := (coprimePart e.1 e.2).primeFactors with hA
    have hsplit2 := Finset.sum_filter_add_sum_filter_not (A.filter (fun p : ℕ => t ≤ (p : ℝ)))
      (fun p => p ∉ G.R) (fun p : ℕ => (1 : ℝ) / p)
    rw [Finset.filter_filter, Finset.filter_filter] at hsplit2
    have hsub : A.filter (fun p : ℕ => t ≤ (p : ℝ) ∧ ¬ p ∉ G.R) ⊆
        A.filter (fun p : ℕ => t ≤ (p : ℝ) ∧ (p : ℝ) < N) ∪
          A.filter (fun p => p ∈ G.R ∧ N ≤ (p : ℝ)) := by
      intro p hp
      obtain ⟨hpA, htp, hpR⟩ := Finset.mem_filter.1 hp
      rw [not_not] at hpR
      rcases lt_or_ge (p : ℝ) N with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hpA, htp, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hpA, hpR, h⟩)
    have hnn : ∀ p : ℕ, (0 : ℝ) ≤ 1 / p := fun p => by positivity
    have hX : ∑ p ∈ A.filter (fun p : ℕ => t ≤ (p : ℝ) ∧ (p : ℝ) < N), (1 : ℝ) / p ≤ 4 := by
      have hsub2 : A.filter (fun p : ℕ => t ≤ (p : ℝ) ∧ (p : ℝ) < N) ⊆
          (Ioc ⌊t - 1⌋₊ ⌊N⌋₊).filter Nat.Prime := by
        intro p hp
        obtain ⟨hpA, htp, hpN⟩ := Finset.mem_filter.1 hp
        refine Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨?_, ?_⟩, Nat.prime_of_mem_primeFactors hpA⟩
        · rw [Nat.floor_lt (by linarith)]; linarith
        · exact Nat.le_floor hpN.le
      calc ∑ p ∈ A.filter (fun p : ℕ => t ≤ (p : ℝ) ∧ (p : ℝ) < N), (1 : ℝ) / p
          ≤ ∑ p ∈ (Ioc ⌊t - 1⌋₊ ⌊N⌋₊).filter Nat.Prime, (1 : ℝ) / p :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun p _ _ => hnn p)
        _ ≤ Real.log (Real.log N / Real.log (t - 1)) + 100 / Real.log (t - 1) :=
            sum_inv_prime_Ioc_le (t - 1) N (by linarith) (by linarith)
        _ ≤ 4 := alt84_mertens t ht
    have hY : ∑ p ∈ A.filter (fun p : ℕ => t ≤ (p : ℝ) ∧ ¬ p ∉ G.R), (1 : ℝ) / p ≤ 4 + 1 := by
      calc ∑ p ∈ A.filter (fun p : ℕ => t ≤ (p : ℝ) ∧ ¬ p ∉ G.R), (1 : ℝ) / p
          ≤ ∑ p ∈ A.filter (fun p : ℕ => t ≤ (p : ℝ) ∧ (p : ℝ) < N) ∪
              A.filter (fun p => p ∈ G.R ∧ N ≤ (p : ℝ)), (1 : ℝ) / p :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hnn p)
        _ ≤ ∑ p ∈ A.filter (fun p : ℕ => t ≤ (p : ℝ) ∧ (p : ℝ) < N), (1 : ℝ) / p +
              ∑ p ∈ A.filter (fun p => p ∈ G.R ∧ N ≤ (p : ℝ)), (1 : ℝ) / p :=
            alt84_sum_union_le _ _ _ hnn
        _ ≤ 4 + 1 := add_le_add hX hS1
    linarith
end GCDGraph
end DuffinSchaeffer
end Port24_Parts_RemoveR

section Port24_Parts_GoodSubgraph
open Finset
namespace DuffinSchaeffer
theorem alt71_extract {δ q δ' q' X : ℝ} (hδ : 0 < δ) (hq : 0 < q) (hq' : 0 ≤ q')
    (h : X ≤ min 1 (δ' / δ) * (q' / q)) : X * q ≤ q' ∧ X * (δ * q) ≤ δ' * q' := by
  have hr : 0 ≤ q' / q := div_nonneg hq' hq.le
  have h1 : X ≤ q' / q := by
    refine le_trans h ?_
    have := min_le_left 1 (δ' / δ)
    calc min 1 (δ' / δ) * (q' / q) ≤ 1 * (q' / q) := mul_le_mul_of_nonneg_right this hr
      _ = q' / q := one_mul _
  have h2 : X ≤ δ' / δ * (q' / q) :=
    le_trans h (mul_le_mul_of_nonneg_right (min_le_right _ _) hr)
  constructor
  · rwa [le_div_iff₀ hq] at h1
  · rw [div_mul_div_comm, le_div_iff₀ (mul_pos hδ hq)] at h2
    exact h2
theorem alt71_prod_fact (P : Finset ℕ) (f : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime) (q : ℕ) :
    (∏ p ∈ P, p ^ f p).factorization q = if q ∈ P then f q else 0 := by
  classical
  rw [Nat.factorization_prod (fun p hp => pow_ne_zero _ (hP p hp).ne_zero),
    Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (g := fun p => if p = q then f p else 0)]
  · exact Finset.sum_ite_eq' P q f
  · intro p hp
    rw [Nat.factorization_pow, (hP p hp).factorization, Finsupp.smul_apply,
      Finsupp.single_apply]
    split_ifs <;> simp
theorem alt71_prod_dvd (P : Finset ℕ) (f : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime) (v : ℕ) (hv : v ≠ 0)
    (hd : ∀ p ∈ P, p ^ f p ∣ v) : (∏ p ∈ P, p ^ f p) ∣ v := by
  classical
  have h0 : (∏ p ∈ P, p ^ f p) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun p hp => pow_ne_zero _ (hP p hp).ne_zero)
  rw [← Nat.factorization_le_iff_dvd h0 hv, Finsupp.le_def]
  intro q
  rw [alt71_prod_fact P f hP q]
  split_ifs with hq
  · exact ((hP q hq).pow_dvd_iff_le_factorization hv).1 (hd q hq)
  · exact Nat.zero_le _
theorem alt71_div_fact (P : Finset ℕ) (f : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime) (v : ℕ) (hv : v ≠ 0)
    (hd : ∀ p ∈ P, p ^ f p ∣ v) (q : ℕ) :
    (v / ∏ p ∈ P, p ^ f p).factorization q = v.factorization q - (if q ∈ P then f q else 0) := by
  rw [Nat.factorization_div (alt71_prod_dvd P f hP v hv hd), Finsupp.tsub_apply,
    alt71_prod_fact P f hP q]
theorem alt71_div_pos (P : Finset ℕ) (f : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime) (v : ℕ) (hv : 0 < v)
    (hd : ∀ p ∈ P, p ^ f p ∣ v) : 0 < v / ∏ p ∈ P, p ^ f p := by
  have h0 : 0 < (∏ p ∈ P, p ^ f p) :=
    Finset.prod_pos (fun p hp => pow_pos (hP p hp).pos _)
  exact Nat.div_pos (Nat.le_of_dvd hv (alt71_prod_dvd P f hP v hv.ne' hd)) h0
theorem alt71_not_dvd (v w p : ℕ) (hv : 0 < v) (hw : 0 < w) (hp : p.Prime)
    (h : v.factorization p = w.factorization p) : ¬ p ∣ coprimePart v w := by
  intro hdvd
  have hv0 : v ≠ 0 := hv.ne'
  have hw0 : w ≠ 0 := hw.ne'
  have hg : (Nat.gcd v w).factorization p = v.factorization p := by
    rw [Nat.factorization_gcd hv0 hw0, Finsupp.inf_apply, h, inf_idem]
  have h1 : (v / Nat.gcd v w).factorization p = 0 := by
    rw [Nat.factorization_div (Nat.gcd_dvd_left v w), Finsupp.tsub_apply, hg, Nat.sub_self]
  have h2 : (w / Nat.gcd v w).factorization p = 0 := by
    rw [Nat.factorization_div (Nat.gcd_dvd_right v w), Finsupp.tsub_apply, hg, h, Nat.sub_self]
  have hvg0 : v / Nat.gcd v w ≠ 0 :=
    (Nat.div_pos (Nat.gcd_le_left w hv) (Nat.gcd_pos_of_pos_left w hv)).ne'
  have hwg0 : w / Nat.gcd v w ≠ 0 :=
    (Nat.div_pos (Nat.gcd_le_right v hw) (Nat.gcd_pos_of_pos_right v hw)).ne'
  unfold coprimePart at hdvd
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with hd | hd
  · rcases (Nat.factorization_eq_zero_iff _ _).1 h1 with h' | h' | h'
    · exact h' hp
    · exact h' hd
    · exact hvg0 h'
  · rcases (Nat.factorization_eq_zero_iff _ _).1 h2 with h' | h' | h'
    · exact h' hp
    · exact h' hd
    · exact hwg0 h'
theorem alt71_dvd_cp (v w p : ℕ) (hv : 0 < v) (hw : 0 < w)
    (h : v.factorization p ≠ w.factorization p) : p ∣ coprimePart v w := by
  have hv0 : v ≠ 0 := hv.ne'
  have hw0 : w ≠ 0 := hw.ne'
  have hg : (Nat.gcd v w).factorization p = min (v.factorization p) (w.factorization p) := by
    rw [Nat.factorization_gcd hv0 hw0, Finsupp.inf_apply]
  unfold coprimePart
  rcases lt_or_gt_of_ne h with hlt | hlt
  · apply dvd_mul_of_dvd_right
    apply Nat.dvd_of_factorization_pos
    rw [Nat.factorization_div (Nat.gcd_dvd_right v w), Finsupp.tsub_apply, hg]
    omega
  · apply dvd_mul_of_dvd_left
    apply Nat.dvd_of_factorization_pos
    rw [Nat.factorization_div (Nat.gcd_dvd_left v w), Finsupp.tsub_apply, hg]
    omega
theorem alt71_coprimePart_ne_zero (v w : ℕ) (hv : 0 < v) (hw : 0 < w) :
    coprimePart v w ≠ 0 := by
  unfold coprimePart
  apply Nat.mul_ne_zero
  · exact (Nat.div_pos (Nat.gcd_le_left w hv) (Nat.gcd_pos_of_pos_left w hv)).ne'
  · exact (Nat.div_pos (Nat.gcd_le_right v hw) (Nat.gcd_pos_of_pos_right v hw)).ne'
theorem alt71_N_le (t : ℝ) (ht : T0 < t) (N : ℕ) (h : (2 : ℝ) ^ N < t ^ (50 : ℕ)) :
    (N : ℝ) ≤ t := by
  have hT : (30000 : ℝ) ≤ T0 := by
    unfold T0
    calc (30000 : ℝ) ≤ 10 ^ 5 := by norm_num
      _ ≤ 10 ^ 2000 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have ht0 : 0 < t := by linarith
  by_contra hN
  push Not at hN
  have hl := Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at hl
  have hl2 := Real.log_two_gt_d9
  have hs : Real.log t = 2 * Real.log (Real.sqrt t) := by
    rw [Real.log_sqrt ht0.le]; ring
  have hsq0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hs1 := Real.log_le_sub_one_of_pos hsq0
  have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  have hN2 : t * Real.log 2 < (N : ℝ) * Real.log 2 :=
    mul_lt_mul_of_pos_right hN (Real.log_pos (by norm_num))
  push_cast at hl
  have key : Real.sqrt t * Real.sqrt t * 0.69 < 100 * Real.sqrt t := by nlinarith
  have hsqt : Real.sqrt t < 145 := by nlinarith
  nlinarith
namespace GCDGraph
theorem alt71_newUnequal_le {H2 H1 H : GCDGraph} (h21 : H2.IsSubgraph H1) :
    newUnequal H2 H ≤ newUnequal H2 H1 + newUnequal H1 H := by
  classical
  unfold newUnequal
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_union] at hp ⊢
  obtain ⟨⟨hp2, hpH⟩, hne⟩ := hp
  by_cases hp1 : p ∈ H1.P
  · right
    obtain ⟨hf, hg⟩ := h21.2.2.2.2.2 p hp1
    refine ⟨⟨hp1, hpH⟩, ?_⟩
    rwa [← hf, ← hg]
  · left
    exact ⟨⟨hp2, hp1⟩, hne⟩
theorem alt71_newUnequal_self (H : GCDGraph) : newUnequal H H = 0 := by
  unfold newUnequal
  simp
theorem alt71_sharp_of_flat (H : GCDGraph) (hflat : H.Rflat = ∅) (p : ℕ) (hp : p ∈ H.R) :
    p ∈ H.Rsharp := by
  classical
  have := (Finset.filter_eq_empty_iff.1 hflat) hp
  unfold Rsharp
  exact Finset.mem_filter.2 ⟨hp, by simpa using this⟩
theorem alt71_iterate : ∀ n : ℕ, ∀ H : GCDGraph, H.R.card = n → 0 < H.density →
    (∀ p ∈ H.R, T0 < (p : ℝ)) →
    ∃ H' : GCDGraph, H'.IsSubgraph H ∧ 0 < H'.density ∧ H'.R = ∅ ∧
      H.quality ≤ H'.quality ∧ H'.P ⊆ H.P ∪ H.R := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H hn hδ hR
  by_cases h0 : H.R = ∅
  · exact ⟨H, IsSubgraph.refl H, hδ, h0, le_rfl, Finset.subset_union_left⟩
  have hne : H.R.Nonempty := Finset.nonempty_iff_ne_empty.2 h0
  obtain ⟨H1, hs1, hδ1, -, hPR1, hR1, hq1⟩ : ∃ H1 : GCDGraph, H1.IsSubgraph H ∧
      0 < H1.density ∧ H.P ⊂ H1.P ∧ H1.P ⊆ H.P ∪ H.R ∧ H1.R ⊂ H.R ∧
      H.quality ≤ H1.quality := by
    by_cases hf : H.Rflat.Nonempty
    · obtain ⟨H1, a, b, c, d, e, f⟩ := prop81 H hδ hR hf
      refine ⟨H1, a, b, c, d, e, ?_⟩
      have hq0 := (H.quality_pos_iff).2 hδ
      have hq1 := H1.quality_nonneg
      have := (alt71_extract hδ hq0 hq1 f).1
      have h2 : (1 : ℝ) ≤ 2 ^ newUnequal H1 H := one_le_pow₀ (by norm_num)
      nlinarith
    · have hflat : H.Rflat = ∅ := Finset.not_nonempty_iff_eq_empty.1 hf
      have hsharp : H.Rsharp.Nonempty := by
        obtain ⟨p, hp⟩ := hne
        exact ⟨p, alt71_sharp_of_flat H hflat p hp⟩
      obtain ⟨H1, a, b, c, d, e, f⟩ := prop82 H hδ hR hflat hsharp
      exact ⟨H1, a, b, c, d, e, f⟩
  have hR1' : ∀ p ∈ H1.R, T0 < (p : ℝ) := fun p hp => hR p (hR1.subset hp)
  obtain ⟨H2, hs2, hδ2, hR2, hq2, hP2⟩ :=
    ih H1.R.card (hn ▸ Finset.card_lt_card hR1) H1 rfl hδ1 hR1'
  refine ⟨H2, hs2.trans hs1, hδ2, hR2, hq1.trans hq2, ?_⟩
  intro p hp
  rcases Finset.mem_union.1 (hP2 hp) with h | h
  · exact hPR1 h
  · exact Finset.mem_union_right _ (hR1.subset h)
theorem alt71_stage2 : ∀ n : ℕ, ∀ H : GCDGraph, H.R.card = n → 0 < H.density →
    (∀ p ∈ H.R, T0 < (p : ℝ)) →
    ∃ H' : GCDGraph, H'.IsSubgraph H ∧ 0 < H'.density ∧ H'.Rflat = ∅ ∧
      (2 : ℝ) ^ (newUnequal H' H) * H.quality ≤ H'.quality ∧
      (2 : ℝ) ^ (newUnequal H' H) * (H.density * H.quality) ≤ H'.density * H'.quality := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H hn hδ hR
  have hq0 := (H.quality_pos_iff).2 hδ
  by_cases hf : H.Rflat.Nonempty
  · obtain ⟨H1, hs1, hδ1, -, -, hR1, h81⟩ := prop81 H hδ hR hf
    have hq1 := H1.quality_nonneg
    obtain ⟨e1, e2⟩ := alt71_extract hδ hq0 hq1 h81
    have hR1' : ∀ p ∈ H1.R, T0 < (p : ℝ) := fun p hp => hR p (hR1.subset hp)
    obtain ⟨H2, hs2, hδ2, hflat2, f1, f2⟩ :=
      ih H1.R.card (hn ▸ Finset.card_lt_card hR1) H1 rfl hδ1 hR1'
    refine ⟨H2, hs2.trans hs1, hδ2, hflat2, ?_, ?_⟩
    · have hle := alt71_newUnequal_le (H := H) hs2
      have hp : (2 : ℝ) ^ (newUnequal H2 H) ≤ 2 ^ (newUnequal H2 H1 + newUnequal H1 H) :=
        pow_le_pow_right₀ (by norm_num) hle
      rw [pow_add] at hp
      have hA : (0 : ℝ) ≤ 2 ^ newUnequal H2 H1 := by positivity
      calc (2 : ℝ) ^ (newUnequal H2 H) * H.quality
          ≤ 2 ^ newUnequal H2 H1 * 2 ^ newUnequal H1 H * H.quality :=
            mul_le_mul_of_nonneg_right hp hq0.le
        _ = 2 ^ newUnequal H2 H1 * (2 ^ newUnequal H1 H * H.quality) := by ring
        _ ≤ 2 ^ newUnequal H2 H1 * H1.quality := mul_le_mul_of_nonneg_left e1 hA
        _ ≤ H2.quality := f1
    · have hle := alt71_newUnequal_le (H := H) hs2
      have hp : (2 : ℝ) ^ (newUnequal H2 H) ≤ 2 ^ (newUnequal H2 H1 + newUnequal H1 H) :=
        pow_le_pow_right₀ (by norm_num) hle
      rw [pow_add] at hp
      have hA : (0 : ℝ) ≤ 2 ^ newUnequal H2 H1 := by positivity
      have hdq : 0 ≤ H.density * H.quality := (mul_pos hδ hq0).le
      calc (2 : ℝ) ^ (newUnequal H2 H) * (H.density * H.quality)
          ≤ 2 ^ newUnequal H2 H1 * 2 ^ newUnequal H1 H * (H.density * H.quality) :=
            mul_le_mul_of_nonneg_right hp hdq
        _ = 2 ^ newUnequal H2 H1 * (2 ^ newUnequal H1 H * (H.density * H.quality)) := by ring
        _ ≤ 2 ^ newUnequal H2 H1 * (H1.density * H1.quality) :=
            mul_le_mul_of_nonneg_left e2 hA
        _ ≤ H2.density * H2.quality := f2
  · have hflat : H.Rflat = ∅ := Finset.not_nonempty_iff_eq_empty.1 hf
    refine ⟨H, IsSubgraph.refl H, hδ, hflat, ?_, ?_⟩ <;>
      simp [alt71_newUnequal_self]
theorem alt71_final (F G2 : GCDGraph) (hs : F.IsSubgraph G2) (hPF : F.P ⊆ G2.P ∪ G2.R)
    (t : ℝ) (ht : 0 < t)
    (hcount : (((G2.P.filter (fun p => G2.f p ≠ G2.g p ∧ t ≤ (p : ℝ))).card : ℕ) : ℝ) ≤ t)
    (e : ℕ × ℕ) (he : e ∈ F.E)
    (h5 : 5 ≤ ∑ p ∈ (coprimePart e.1 e.2).primeFactors.filter
        (fun p : ℕ => t ≤ (p : ℝ) ∧ p ∉ G2.R), (1 : ℝ) / p) :
    4 ≤ Lsum t (e.1 / F.aProd) (e.2 / F.bProd) := by
  classical
  obtain ⟨hv, hw⟩ := Finset.mem_product.1 (F.E_sub he)
  have hv0 := F.V_pos _ hv
  have hw0 := F.W_pos _ hw
  have hdV : ∀ p ∈ F.P, p ^ F.f p ∣ e.1 := fun p hp => F.dvd_V p hp _ hv
  have hdW : ∀ p ∈ F.P, p ^ F.g p ∣ e.2 := fun p hp => F.dvd_W p hp _ hw
  have hva := alt71_div_pos F.P F.f F.P_prime e.1 hv0 hdV
  have hwb := alt71_div_pos F.P F.g F.P_prime e.2 hw0 hdW
  set B := (coprimePart e.1 e.2).primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ) ∧ p ∉ G2.R)
  set Pd := G2.P.filter (fun p => G2.f p ≠ G2.g p ∧ t ≤ (p : ℝ))
  have hsplit := Finset.sum_filter_add_sum_filter_not B (fun p => p ∈ Pd) (fun p : ℕ => (1 : ℝ) / p)
  have h1 : ∑ p ∈ B.filter (fun p => p ∈ Pd), (1 : ℝ) / p ≤ 1 := by
    calc ∑ p ∈ B.filter (fun p => p ∈ Pd), (1 : ℝ) / p ≤ ∑ p ∈ Pd, (1 : ℝ) / p := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp; exact (Finset.mem_filter.1 hp).2
          · intro p _ _; positivity
      _ ≤ ∑ p ∈ Pd, (1 : ℝ) / t := by
          apply Finset.sum_le_sum
          intro p hp
          have := (Finset.mem_filter.1 hp).2.2
          exact one_div_le_one_div_of_le ht this
      _ = (Pd.card : ℝ) / t := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 1 := by rw [div_le_one ht]; exact hcount
  have h2 : ∑ p ∈ B.filter (fun p => p ∉ Pd), (1 : ℝ) / p ≤ Lsum t (e.1 / F.aProd) (e.2 / F.bProd) := by
    unfold Lsum
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpB, hpPd⟩ := Finset.mem_filter.1 hp
      obtain ⟨hpA, htp, hpR⟩ := Finset.mem_filter.1 hpB
      have hpp := Nat.prime_of_mem_primeFactors hpA
      have hpd := Nat.dvd_of_mem_primeFactors hpA
      have hne : e.1.factorization p ≠ e.2.factorization p := fun h =>
        alt71_not_dvd e.1 e.2 p hv0 hw0 hpp h hpd
      have hfa := alt71_div_fact F.P F.f F.P_prime e.1 hv0.ne' hdV p
      have hfb := alt71_div_fact F.P F.g F.P_prime e.2 hw0.ne' hdW p
      have hne' : (e.1 / F.aProd).factorization p ≠ (e.2 / F.bProd).factorization p := by
        unfold aProd bProd
        rw [hfa, hfb]
        by_cases hpF : p ∈ F.P
        · have hp2 : p ∈ G2.P := by
            rcases Finset.mem_union.1 (hPF hpF) with h | h
            · exact h
            · exact absurd h hpR
          have hfg2 : G2.f p = G2.g p := by
            by_contra h
            exact hpPd (Finset.mem_filter.2 ⟨hp2, h, htp⟩)
          obtain ⟨hff, hgg⟩ := hs.2.2.2.2.2 p hp2
          have hfg : F.f p = F.g p := by rw [hff, hgg, hfg2]
          have hgcd := F.gcd_E p hpF e he
          rw [Nat.factorization_gcd hv0.ne' hw0.ne', Finsupp.inf_apply] at hgcd
          simp only [hpF, ite_true]
          rw [← hfg]
          rw [← hfg] at hgcd
          have hmin : min (F.f p) (F.f p) = F.f p := min_self _
          rw [hmin] at hgcd
          change min (e.1.factorization p) (e.2.factorization p) = F.f p at hgcd
          omega
        · simp only [hpF, ite_false, Nat.sub_zero]
          exact hne
      refine Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hpp, ?_, ?_⟩, htp⟩
      · exact alt71_dvd_cp _ _ p hva hwb hne'
      · exact alt71_coprimePart_ne_zero _ _ hva hwb
    · intro p _ _; positivity
  linarith
theorem prop71 : ∃ c : ℝ, 0 < c ∧ ∀ (G : GCDGraph) (t : ℝ), G.P = ∅ → 0 < G.density →
    (∀ e ∈ G.E, 10 ≤ Lsum t e.1 e.2) → 10 * G.density ^ (-(1 : ℝ) / 50) ≤ t → T0 < t →
    ∃ G' : GCDGraph, G'.IsSubgraph G ∧ 0 < G'.density ∧ G'.R = ∅ ∧ G'.HighDegree ∧
      (c * G.density * t ^ (50 : ℕ) * G.quality ≤ G'.quality ∨
        (c * G.quality ≤ G'.quality ∧
          ∀ e ∈ G'.E, 4 ≤ Lsum t (e.1 / G'.aProd) (e.2 / G'.bProd))) := by
  obtain ⟨K, hK, hKdef⟩ : ∃ K : ℝ, 0 < K ∧ 1 / (10 : ℝ) ^ ((10 : ℕ) ^ 3000) = 1 / K :=
    ⟨_, pow_pos (by norm_num) _, rfl⟩
  refine ⟨1 / (2 * 10 ^ 50 * K), by positivity, ?_⟩
  intro G t hP hδ hL _ hT
  have hq := (G.quality_pos_iff).2 hδ
  have hT1 : (1 : ℝ) ≤ T0 := by unfold T0; exact one_le_pow₀ (by norm_num)
  have ht0 : 0 < t := by linarith
  obtain ⟨G1, hs1, hδ1, hP1, hR1, h83⟩ := prop83 G hP hδ
  rw [hKdef] at h83
  clear hKdef
  obtain ⟨e1, e1'⟩ := alt71_extract hδ hq G1.quality_nonneg h83
  have hq1 : 0 < G1.quality := (G1.quality_pos_iff).2 hδ1
  obtain ⟨G2, hs2, hδ2, hflat2, hq2, hdq2⟩ := alt71_stage2 _ G1 rfl hδ1 hR1
  set N := newUnequal G2 G1 with hNdef
  have hs2' : G2.IsSubgraph G := hs2.trans hs1
  have hRG2 : ∀ p ∈ G2.R, T0 < (p : ℝ) := fun p hp => hR1 p (R_mono hs2 hp)
  have hq2pos : 0 < G2.quality := (G2.quality_pos_iff).2 hδ2
  have h2N : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
  have F1 : G.quality ≤ K * G1.quality := by
    have := mul_le_mul_of_nonneg_left e1 hK.le
    rwa [← mul_assoc, mul_one_div_cancel hK.ne', one_mul] at this
  have F1' : G.density * G.quality ≤ K * (G1.density * G1.quality) := by
    have := mul_le_mul_of_nonneg_left e1' hK.le
    rwa [← mul_assoc, mul_one_div_cancel hK.ne', one_mul] at this
  have hq12 : G1.quality ≤ G2.quality := le_trans (le_mul_of_one_le_left hq1.le h2N) hq2
  have hGq2 : G.quality ≤ K * G2.quality :=
    le_trans F1 (mul_le_mul_of_nonneg_left hq12 hK.le)
  set A := (t / 10) ^ (50 : ℕ) with hA
  have hApos : 0 < A := by positivity
  by_cases hcase : A * G.density * G.quality ≤ K * G2.quality
  ·
    obtain ⟨G3, hs3, hδ3, hR3, hq3, -⟩ := alt71_iterate _ G2 rfl hδ2 hRG2
    obtain ⟨G4, hs4, -, -, -, hδ4, -, hq4, hHD⟩ := exists_highDegree_subgraph G3 hδ3
    refine ⟨G4, hs4.trans (hs3.trans hs2'), hδ4, ?_, hHD, Or.inl ?_⟩
    · exact Finset.subset_empty.1 (hR3 ▸ R_mono hs4)
    · have h1 : 1 / (2 * 10 ^ 50 * K) * G.density * t ^ (50 : ℕ) * G.quality =
          A * G.density * G.quality / K / 2 := by
        rw [hA, div_pow]; field_simp
      rw [h1]
      have h2 : A * G.density * G.quality / K ≤ G2.quality := by
        rw [div_le_iff₀ hK]; linarith
      have h3 : 0 ≤ A * G.density * G.quality / K :=
        div_nonneg (mul_pos (mul_pos hApos hδ) hq).le hK.le
      linarith
  ·
    push Not at hcase
    have hdq12 : G1.density * G1.quality ≤ G2.density * G2.quality :=
      le_trans (le_mul_of_one_le_left (mul_pos hδ1 hq1).le h2N) hdq2
    have hδq : 0 < G.density * G.quality := mul_pos hδ hq
    have hδ2t : (10 / t) ^ (50 : ℕ) ≤ G2.density := by
      have h1 : G.density * G.quality ≤ K * (G2.density * G2.quality) :=
        le_trans F1' (mul_le_mul_of_nonneg_left hdq12 hK.le)
      have h2 : K * (G2.density * G2.quality) < G2.density * (A * G.density * G.quality) := by
        have := mul_lt_mul_of_pos_left hcase hδ2
        have e : K * (G2.density * G2.quality) = G2.density * (K * G2.quality) := by ring
        rw [e]; exact this
      have h3 : 1 < G2.density * A := by
        have h' : 1 * (G.density * G.quality) < (G2.density * A) * (G.density * G.quality) := by
          have e : G2.density * (A * G.density * G.quality) =
              (G2.density * A) * (G.density * G.quality) := by ring
          rw [one_mul, ← e]; exact lt_of_le_of_lt h1 h2
        exact lt_of_mul_lt_mul_right h' hδq.le
      have h4 : (10 / t) ^ (50 : ℕ) * A = 1 := by
        rw [hA, ← mul_pow]; field_simp
      have h5 : (10 / t) ^ (50 : ℕ) = 1 / A := eq_one_div_of_mul_eq_one_left h4
      rw [h5, div_le_iff₀ hApos]
      linarith
    have hN : (2 : ℝ) ^ N < t ^ (50 : ℕ) := by
      have h2N0 : (0 : ℝ) ≤ 2 ^ N := by positivity
      have h1 : 2 ^ N * G.quality ≤ K * G2.quality := by
        calc 2 ^ N * G.quality ≤ 2 ^ N * (K * G1.quality) := mul_le_mul_of_nonneg_left F1 h2N0
          _ = K * (2 ^ N * G1.quality) := by ring
          _ ≤ K * G2.quality := mul_le_mul_of_nonneg_left hq2 hK.le
      have hδ1' : G.density ≤ 1 := G.density_le_one
      have hAt : A ≤ t ^ (50 : ℕ) := by
        rw [hA, div_pow]
        exact div_le_self (by positivity) (one_le_pow₀ (by norm_num))
      have h2 : 2 ^ N * G.quality < A * G.quality := by
        have : A * G.density * G.quality ≤ A * G.quality := by
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδ1' hApos.le) hq.le
          rwa [mul_one] at this
        linarith
      have h3 : (2 : ℝ) ^ N < A := lt_of_mul_lt_mul_right h2 hq.le
      linarith
    have hNt : (N : ℝ) ≤ t := alt71_N_le t hT N hN
    obtain ⟨G3, hs3, hV3, hW3, hP3, hf3, hg3, hq3pos, hq3, hL3⟩ :=
      lemma84 G2 t hT.le hδ2 hflat2 hδ2t (fun e he => hL e (hs2'.2.2.2.1 he))
    have hδ3 : 0 < G3.density := (G3.quality_pos_iff).1 hq3pos
    have hRG3 : ∀ p ∈ G3.R, T0 < (p : ℝ) := fun p hp => hRG2 p (R_mono hs3 hp)
    obtain ⟨G4, hs4, hδ4, hR4, hq4, hP4⟩ := alt71_iterate _ G3 rfl hδ3 hRG3
    obtain ⟨G5, hs5, hP5, hf5, hg5, hδ5, -, hq5, hHD⟩ := exists_highDegree_subgraph G4 hδ4
    refine ⟨G5, hs5.trans (hs4.trans (hs3.trans hs2')), hδ5, ?_, hHD, Or.inr ⟨?_, ?_⟩⟩
    · exact Finset.subset_empty.1 (hR4 ▸ R_mono hs5)
    · have h1 : 1 / (2 * 10 ^ 50 * K) * G.quality ≤ G2.quality / 2 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
        have h10 : (1 : ℝ) ≤ 10 ^ 50 := one_le_pow₀ (by norm_num)
        have h' : K * G2.quality ≤ K * G2.quality * 10 ^ 50 :=
          le_mul_of_one_le_right (mul_nonneg hK.le hq2pos.le) h10
        calc G.quality ≤ K * G2.quality := hGq2
          _ ≤ K * G2.quality * 10 ^ 50 := h'
          _ = G2.quality / 2 * (2 * 10 ^ 50 * K) := by ring
      linarith
    · intro e he
      have he4 : e ∈ G4.E := hs5.2.2.2.1 he
      have he3 : e ∈ G3.E := hs4.2.2.2.1 he4
      have h5 := hL3 e he3
      have ha : G5.aProd = G4.aProd := by unfold aProd; rw [hP5, hf5]
      have hb : G5.bProd = G4.bProd := by unfold bProd; rw [hP5, hg5]
      rw [ha, hb]
      have hs42 : G4.IsSubgraph G2 := hs4.trans hs3
      have hPF : G4.P ⊆ G2.P ∪ G2.R := by
        intro p hp
        rcases Finset.mem_union.1 (hP4 hp) with h | h
        · rw [hP3] at h; exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ (R_mono hs3 h)
      apply alt71_final G4 G2 hs42 hPF t ht0 _ e he4 h5
      have hsub : G2.P.filter (fun p => G2.f p ≠ G2.g p ∧ t ≤ (p : ℝ)) ⊆
          (G2.P \ G1.P).filter (fun p => G2.f p ≠ G2.g p) := by
        intro p hp
        obtain ⟨hp2, hne, htp⟩ := Finset.mem_filter.1 hp
        refine Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hp2, ?_⟩, hne⟩
        intro hp1
        have := hP1 p hp1
        linarith
      have hc := Finset.card_le_card hsub
      have hc' : (((G2.P.filter (fun p => G2.f p ≠ G2.g p ∧ t ≤ (p : ℝ))).card : ℕ) : ℝ) ≤ N := by
        exact_mod_cast hc
      linarith
end GCDGraph
end DuffinSchaeffer
end Port24_Parts_GoodSubgraph

section Port24_Parts_EdgeBound
open Finset
namespace DuffinSchaeffer
theorem alt63_prod_fact (P : Finset ℕ) (f : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime) (q : ℕ) :
    (∏ p ∈ P, p ^ f p).factorization q = if q ∈ P then f q else 0 := by
  classical
  rw [Nat.factorization_prod (fun p hp => pow_ne_zero _ (hP p hp).ne_zero),
    Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (g := fun p => if p = q then f p else 0)]
  · exact Finset.sum_ite_eq' P q f
  · intro p hp
    rw [Nat.factorization_pow, (hP p hp).factorization, Finsupp.smul_apply,
      Finsupp.single_apply]
    split_ifs <;> simp
theorem alt63_prod_dvd (P : Finset ℕ) (f : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime) (v : ℕ) (hv : v ≠ 0)
    (hd : ∀ p ∈ P, p ^ f p ∣ v) : (∏ p ∈ P, p ^ f p) ∣ v := by
  classical
  have h0 : (∏ p ∈ P, p ^ f p) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun p hp => pow_ne_zero _ (hP p hp).ne_zero)
  rw [← Nat.factorization_le_iff_dvd h0 hv, Finsupp.le_def]
  intro q
  rw [alt63_prod_fact P f hP q]
  split_ifs with hq
  · exact ((hP q hq).pow_dvd_iff_le_factorization hv).1 (hd q hq)
  · exact Nat.zero_le _
theorem alt63_prod_pos (P : Finset ℕ) (f : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime) :
    0 < ∏ p ∈ P, p ^ f p :=
  Finset.prod_pos (fun p hp => pow_pos (hP p hp).pos _)
theorem alt63_card_dvd_le (S : Finset ℕ) (a M : ℕ) (ha : 0 < a)
    (hS : ∀ v ∈ S, 0 < v ∧ a ∣ v ∧ v ≤ M) : (S.card : ℝ) ≤ (M : ℝ) / a := by
  have hinj : Set.InjOn (fun v => v / a) S := by
    intro x hx y hy hxy
    simp only at hxy
    obtain ⟨-, hax, -⟩ := hS x hx
    obtain ⟨-, hay, -⟩ := hS y hy
    rw [← Nat.div_mul_cancel hax, ← Nat.div_mul_cancel hay, hxy]
  have hsub : S.image (fun v => v / a) ⊆ Icc 1 (M / a) := by
    intro n hn
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hn
    obtain ⟨hv0, hav, hvM⟩ := hS v hv
    rw [Finset.mem_Icc]
    exact ⟨Nat.div_pos (Nat.le_of_dvd hv0 hav) ha, Nat.div_le_div_right hvM⟩
  have h1 : S.card ≤ M / a := by
    rw [← Finset.card_image_of_injOn hinj]
    calc (S.image (fun v => v / a)).card ≤ (Icc 1 (M / a)).card := Finset.card_le_card hsub
      _ = M / a := by simp
  calc (S.card : ℝ) ≤ ((M / a : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ (M : ℝ) / a := Nat.cast_div_le
theorem alt63_exp_le_one_sub (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have h1 : 0 < 1 - x := by linarith
  have h2 := Real.one_sub_inv_le_log_of_pos h1
  have h3 : -2 * x ≤ 1 - (1 - x)⁻¹ := by
    rw [← div_one (1 : ℝ), one_div_one, ← one_div]
    rw [show (1 : ℝ) - 1 / (1 - x) = -x / (1 - x) by field_simp; ring]
    rw [le_div_iff₀ h1]
    nlinarith
  calc Real.exp (-2 * x) ≤ Real.exp (Real.log (1 - x)) := Real.exp_le_exp.2 (le_trans h3 h2)
    _ = 1 - x := Real.exp_log h1
theorem alt63_zeta_bound : ∃ z0 : ℝ, 0 < z0 ∧ ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
    z0 ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10 := by
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ ((31 : ℝ) / 30)) :=
    Real.summable_one_div_nat_rpow.2 (by norm_num)
  set T := ∑' n : ℕ, 1 / (n : ℝ) ^ ((31 : ℝ) / 30)
  refine ⟨Real.exp (-20 * T), Real.exp_pos _, ?_⟩
  intro S hS
  have hx : ∀ p ∈ S, 0 ≤ 1 / (p : ℝ) ^ ((31 : ℝ) / 30) ∧ 1 / (p : ℝ) ^ ((31 : ℝ) / 30) ≤ 1 / 2 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
    constructor
    · positivity
    · have : (p : ℝ) ≤ (p : ℝ) ^ ((31 : ℝ) / 30) :=
        Real.self_le_rpow_of_one_le (by linarith) (by norm_num)
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
  have hST : ∑ p ∈ S, 1 / (p : ℝ) ^ ((31 : ℝ) / 30) ≤ T :=
    hsum.sum_le_tsum S (fun n _ => by positivity)
  calc Real.exp (-20 * T) ≤ Real.exp (-20 * ∑ p ∈ S, 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) :=
        Real.exp_le_exp.2 (by linarith)
    _ = ∏ p ∈ S, (Real.exp (-2 * (1 / (p : ℝ) ^ ((31 : ℝ) / 30)))) ^ 10 := by
        rw [Finset.mul_sum, Real.exp_sum]
        apply Finset.prod_congr rfl
        intro p _
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
    _ ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10 := by
        apply Finset.prod_le_prod
        · intro p _; positivity
        · intro p hp
          obtain ⟨h0, h1⟩ := hx p hp
          exact pow_le_pow_left₀ (Real.exp_pos _).le (alt63_exp_le_one_sub _ h0 h1) 10
theorem alt63_totient_real (n : ℕ) :
    (Nat.totient n : ℝ) = n * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors n)
  push_cast at h
  exact h
theorem alt63_weight_le (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (P : Finset ℕ) (f g : ℕ → ℕ)
    (v : ℕ) (hv : 0 < v) (hdv : ∀ p ∈ P, f p = g p ∧ 1 ≤ f p → p.Prime ∧ p ∣ v) :
    weight ψ v ≤ ψ v * ∏ p ∈ P, (1 - (if f p = g p ∧ 1 ≤ f p then 1 / (p : ℝ) else 0)) := by
  classical
  have hv0 : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  have hw : weight ψ v = ψ v * ∏ p ∈ v.primeFactors, (1 - (p : ℝ)⁻¹) := by
    unfold weight
    rw [alt63_totient_real v]
    field_simp
  have hP : ∏ p ∈ P, (1 - (if f p = g p ∧ 1 ≤ f p then 1 / (p : ℝ) else 0)) =
      ∏ p ∈ P.filter (fun p => f p = g p ∧ 1 ≤ f p), (1 - (p : ℝ)⁻¹) := by
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro p _
    split_ifs <;> simp
  have hsub : P.filter (fun p => f p = g p ∧ 1 ≤ f p) ⊆ v.primeFactors := by
    intro p hp
    obtain ⟨hpP, hc⟩ := Finset.mem_filter.1 hp
    obtain ⟨hpp, hpv⟩ := hdv p hpP hc
    exact Nat.mem_primeFactors.2 ⟨hpp, hpv, hv.ne'⟩
  have hle : ∏ p ∈ v.primeFactors, (1 - (p : ℝ)⁻¹) ≤
      ∏ p ∈ P.filter (fun p => f p = g p ∧ 1 ≤ f p), (1 - (p : ℝ)⁻¹) := by
    rw [← Finset.prod_sdiff hsub]
    have h1 : ∏ p ∈ v.primeFactors \ P.filter (fun p => f p = g p ∧ 1 ≤ f p),
        (1 - (p : ℝ)⁻¹) ≤ 1 := by
      apply Finset.prod_le_one
      · intro p hp
        have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.1 hp).1
        have : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
        have : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
        linarith
      · intro p _
        have : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
        linarith
    have h2 : 0 ≤ ∏ p ∈ P.filter (fun p => f p = g p ∧ 1 ≤ f p), (1 - (p : ℝ)⁻¹) := by
      apply Finset.prod_nonneg
      intro p hp
      have hpp := hdv p (Finset.mem_filter.1 hp).1 (Finset.mem_filter.1 hp).2
      have : (1 : ℝ) ≤ p := by exact_mod_cast hpp.1.one_lt.le
      have : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
      linarith
    calc (∏ p ∈ v.primeFactors \ P.filter (fun p => f p = g p ∧ 1 ≤ f p), (1 - (p : ℝ)⁻¹)) *
          ∏ p ∈ P.filter (fun p => f p = g p ∧ 1 ≤ f p), (1 - (p : ℝ)⁻¹)
        ≤ 1 * ∏ p ∈ P.filter (fun p => f p = g p ∧ 1 ≤ f p), (1 - (p : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = _ := one_mul _
  rw [hw, hP]
  exact mul_le_mul_of_nonneg_left hle (hψ v)
namespace GCDGraph
theorem alt63_gcd_eq (H : GCDGraph) (hR : H.R = ∅) (e : ℕ × ℕ) (he : e ∈ H.E) :
    Nat.gcd e.1 e.2 = ∏ p ∈ H.P, p ^ min (H.f p) (H.g p) := by
  classical
  obtain ⟨hv, hw⟩ := Finset.mem_product.1 (H.E_sub he)
  have hv0 := H.V_pos _ hv
  have hg0 : Nat.gcd e.1 e.2 ≠ 0 := (Nat.gcd_pos_of_pos_left _ hv0).ne'
  have hp0 : (∏ p ∈ H.P, p ^ min (H.f p) (H.g p)) ≠ 0 :=
    (alt63_prod_pos H.P _ H.P_prime).ne'
  apply Nat.eq_of_factorization_eq hg0 hp0
  intro q
  rw [alt63_prod_fact H.P _ H.P_prime q]
  split_ifs with hq
  · exact H.gcd_E q hq e he
  · rw [Nat.factorization_eq_zero_iff]
    by_contra hc
    push Not at hc
    obtain ⟨hqp, hqd, -⟩ := hc
    have : q ∈ H.R := by
      unfold R
      refine Finset.mem_sdiff.2 ⟨Finset.mem_biUnion.2 ⟨e, he, ?_⟩, hq⟩
      exact Nat.mem_primeFactors.2 ⟨hqp, hqd, hg0⟩
    rw [hR] at this
    exact absurd this (Finset.notMem_empty q)
theorem alt63_X_mul (H : GCDGraph) :
    (∏ p ∈ H.P, p ^ H.fgDist p) * (∏ p ∈ H.P, p ^ min (H.f p) (H.g p)) ^ 2 =
      H.aProd * H.bProd := by
  unfold aProd bProd
  rw [sq, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  rw [← pow_add, ← pow_add, ← pow_add]
  congr 1
  unfold fgDist
  omega
theorem alt63_quality_eq (H : GCDGraph) :
    H.quality = H.density ^ 10 * wsum H.μ H.V * wsum H.μ H.W *
      ((∏ p ∈ H.P, (p : ℝ) ^ H.fgDist p) /
        ((∏ p ∈ H.P, (1 - (if H.f p = H.g p ∧ 1 ≤ H.f p then 1 / (p : ℝ) else 0)) ^ 2) *
          ∏ p ∈ H.P, (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10)) := by
  unfold quality qualityFactor
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib]
end GCDGraph
theorem alt63_Lsum_split (t : ℝ) (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    Lsum t x y ≤ ∑ p ∈ x.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)), (1 : ℝ) / p +
      ∑ p ∈ y.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)), (1 : ℝ) / p := by
  classical
  unfold Lsum
  have hsub : (coprimePart x y).primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)) ⊆
      x.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)) ∪
        y.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)) := by
    intro p hp
    rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
    obtain ⟨⟨hpp, hpd, -⟩, htp⟩ := hp
    unfold coprimePart at hpd
    rcases (Nat.Prime.dvd_mul hpp).1 hpd with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2
        ⟨hpp, h.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left x y)), hx.ne'⟩, htp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2
        ⟨hpp, h.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right x y)), hy.ne'⟩, htp⟩)
  calc _ ≤ ∑ p ∈ (x.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)) ∪
          y.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ))), (1 : ℝ) / p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ _ := alt84_sum_union_le _ _ _ (fun _ => by positivity)
theorem alt63_count (S : Finset ℕ) (a M : ℕ) (ha : 0 < a) (bad : ℕ → Prop) [DecidablePred bad]
    (D : ℝ) (hD : 0 ≤ D)
    (hcount : ∀ x : ℝ, 1 ≤ x → (((Icc 1 ⌊x⌋₊).filter bad).card : ℝ) ≤ D * x)
    (hS : ∀ v ∈ S, 0 < v ∧ a ∣ v ∧ v ≤ M ∧ bad (v / a)) :
    (S.card : ℝ) ≤ D * ((M : ℝ) / a) := by
  rcases S.eq_empty_or_nonempty with h | ⟨v0, hv0⟩
  · rw [h, Finset.card_empty, Nat.cast_zero]; positivity
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hMa : 1 ≤ (M : ℝ) / a := by
    obtain ⟨h0, hd, hM, -⟩ := hS v0 hv0
    rw [le_div_iff₀ haR, one_mul]
    exact_mod_cast (Nat.le_of_dvd h0 hd).trans hM
  have hinj : Set.InjOn (fun v => v / a) S := by
    intro x hx y hy hxy
    simp only at hxy
    obtain ⟨-, hax, -⟩ := hS x hx
    obtain ⟨-, hay, -⟩ := hS y hy
    rw [← Nat.div_mul_cancel hax, ← Nat.div_mul_cancel hay, hxy]
  have hsub : S.image (fun v => v / a) ⊆ (Icc 1 ⌊(M : ℝ) / a⌋₊).filter bad := by
    intro n hn
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hn
    obtain ⟨hv0, hav, hvM, hb⟩ := hS v hv
    refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨Nat.div_pos (Nat.le_of_dvd hv0 hav) ha, ?_⟩, hb⟩
    rw [Nat.floor_div_eq_div]
    exact Nat.div_le_div_right hvM
  calc (S.card : ℝ) = ((S.image (fun v => v / a)).card : ℝ) := by
        rw [Finset.card_image_of_injOn hinj]
    _ ≤ (((Icc 1 ⌊(M : ℝ) / a⌋₊).filter bad).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ D * ((M : ℝ) / a) := hcount _ hMa
theorem alt63_esum_eq (G : GCDGraph) :
    esum G.μ G.E = G.density * (wsum G.μ G.V * wsum G.μ G.W) := by
  unfold GCDGraph.density
  rcases eq_or_ne (wsum G.μ G.V * wsum G.μ G.W) 0 with h | h
  · rw [h, mul_zero]
    have := GCDGraph.alt_esum_le G.μ_nonneg G.E_sub
    rw [h] at this
    exact le_antisymm this (GCDGraph.alt_esum_nonneg G.μ_nonneg _)
  · rw [div_mul_cancel₀ _ h]
theorem alt63_fiber (H : GCDGraph) (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (t : ℝ) (ht : 0 ≤ t)
    (m : ℕ) (hM : ∀ e ∈ H.E, Mqr ψ e.1 e.2 ≤ t * m) (bad : ℕ → Prop) [DecidablePred bad]
    (D : ℝ) (hD : 0 ≤ D)
    (hcount : ∀ x : ℝ, 1 ≤ x → (((Icc 1 ⌊x⌋₊).filter bad).card : ℝ) ≤ D * x)
    (w : ℕ) (F : Finset (ℕ × ℕ)) (hF : ∀ e ∈ F, e ∈ H.E ∧ e.2 = w ∧ bad (e.1 / H.aProd)) :
    (F.card : ℝ) * ψ w ≤ D * t * m / H.aProd := by
  classical
  have ha : 0 < H.aProd := alt63_prod_pos H.P H.f H.P_prime
  have haR : (0 : ℝ) < H.aProd := by exact_mod_cast ha
  rcases F.eq_empty_or_nonempty with hFe | hFne
  · rw [hFe, Finset.card_empty, Nat.cast_zero, zero_mul]; positivity
  set S := F.image Prod.fst with hSdef
  have hSne : S.Nonempty := hFne.image _
  have hvmS : S.max' hSne ∈ S := S.max'_mem hSne
  obtain ⟨e0, he0F, he0v⟩ := Finset.mem_image.1 hvmS
  obtain ⟨he0E, he0w, -⟩ := hF e0 he0F
  have hinj : Set.InjOn Prod.fst (F : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    have h1 := (hF x hx).2.1
    have h2 := (hF y hy).2.1
    exact Prod.ext hxy (h1.trans h2.symm)
  have hcard : F.card = S.card := (Finset.card_image_of_injOn hinj).symm
  have hcS : (S.card : ℝ) ≤ D * (((S.max' hSne : ℕ) : ℝ) / H.aProd) := by
    apply alt63_count S H.aProd (S.max' hSne) ha bad D hD hcount
    intro v hv
    obtain ⟨e, heF, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨heE, -, hb⟩ := hF e heF
    have hv := (Finset.mem_product.1 (H.E_sub heE)).1
    exact ⟨H.V_pos _ hv, alt63_prod_dvd H.P H.f H.P_prime _ (H.V_pos _ hv).ne'
      (fun p hp => H.dvd_V p hp _ hv), S.le_max' _ (Finset.mem_image_of_mem _ heF), hb⟩
  have hψw : ((S.max' hSne : ℕ) : ℝ) * ψ w ≤ t * m := by
    have h := hM e0 he0E
    unfold Mqr at h
    rw [← he0v, ← he0w]
    exact le_trans (le_max_right _ _) h
  calc (F.card : ℝ) * ψ w = S.card * ψ w := by rw [hcard]
    _ ≤ D * (((S.max' hSne : ℕ) : ℝ) / H.aProd) * ψ w := mul_le_mul_of_nonneg_right hcS (hψ w)
    _ = D / H.aProd * (((S.max' hSne : ℕ) : ℝ) * ψ w) := by ring
    _ ≤ D / H.aProd * (t * m) := mul_le_mul_of_nonneg_left hψw (by positivity)
    _ = D * t * m / H.aProd := by ring
theorem alt63_sum_fst (H : GCDGraph) (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (t : ℝ) (ht : 0 ≤ t)
    (m : ℕ) (hM : ∀ e ∈ H.E, Mqr ψ e.1 e.2 ≤ t * m) (bad : ℕ → Prop) [DecidablePred bad]
    (D : ℝ) (hD : 0 ≤ D)
    (hcount : ∀ x : ℝ, 1 ≤ x → (((Icc 1 ⌊x⌋₊).filter bad).card : ℝ) ≤ D * x) :
    ∑ e ∈ H.E.filter (fun e => bad (e.1 / H.aProd)), ψ e.2 ≤
      H.W.card * (D * t * m / H.aProd) := by
  classical
  have hmaps : ∀ e ∈ H.E.filter (fun e => bad (e.1 / H.aProd)), e.2 ∈ H.W := fun e he =>
    (Finset.mem_product.1 (H.E_sub (Finset.mem_filter.1 he).1)).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc _ ≤ ∑ w ∈ H.W, D * t * m / H.aProd := by
        apply Finset.sum_le_sum
        intro w _
        rw [Finset.sum_congr rfl (g := fun _ => ψ w)
          (fun e he => by rw [(Finset.mem_filter.1 he).2]), Finset.sum_const, nsmul_eq_mul]
        apply alt63_fiber H ψ hψ t ht m hM bad D hD hcount w
        intro e he
        simp only [Finset.mem_filter] at he
        exact ⟨he.1.1, he.2, he.1.2⟩
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
theorem alt63_sum_snd (H : GCDGraph) (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (t : ℝ) (ht : 0 ≤ t)
    (m : ℕ) (hM : ∀ e ∈ H.E, Mqr ψ e.1 e.2 ≤ t * m) (bad : ℕ → Prop) [DecidablePred bad] :
    ∑ e ∈ H.E.filter (fun e => bad (e.2 / H.bProd)), ψ e.2 ≤
      (H.W.filter (fun w => bad (w / H.bProd))).card * (t * m / H.aProd) := by
  classical
  have hmaps : ∀ e ∈ H.E.filter (fun e => bad (e.2 / H.bProd)),
      e.2 ∈ H.W.filter (fun w => bad (w / H.bProd)) := fun e he =>
    Finset.mem_filter.2 ⟨(Finset.mem_product.1 (H.E_sub (Finset.mem_filter.1 he).1)).2,
      (Finset.mem_filter.1 he).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc _ ≤ ∑ w ∈ H.W.filter (fun w => bad (w / H.bProd)), t * m / H.aProd := by
        apply Finset.sum_le_sum
        intro w _
        rw [Finset.sum_congr rfl (g := fun _ => ψ w)
          (fun e he => by rw [(Finset.mem_filter.1 he).2]), Finset.sum_const, nsmul_eq_mul]
        have h := alt63_fiber H ψ hψ t ht m hM (fun _ => True) 1 zero_le_one
          (fun x hx => by
            rw [Finset.filter_true_of_mem (fun _ _ => trivial), Nat.card_Icc, one_mul]
            simp only [add_tsub_cancel_right]
            exact Nat.floor_le (by linarith))
          w (((H.E.filter (fun e => bad (e.2 / H.bProd))).filter (fun e => e.2 = w)))
          (fun e he => by
            simp only [Finset.mem_filter] at he
            exact ⟨he.1.1, he.2, trivial⟩)
        rwa [one_mul] at h
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
theorem alt63_quality_le (H : GCDGraph) (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (hμ : H.μ = weight ψ)
    (z0 : ℝ) (hz0 : 0 < z0) (hz : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      z0 ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10)
    (hδ : 0 < H.density) (hHD : H.HighDegree) (w0 : ℕ) (hw0 : w0 ∈ H.W) :
    H.quality ≤ 100 / 81 / z0 * (∏ p ∈ H.P, (p : ℝ) ^ H.fgDist p) *
      ∑ e ∈ ((H.nbhdW w0) ×ˢ H.W).filter (· ∈ H.E), ψ e.1 * ψ e.2 := by
  classical
  have hq0 := H.alt63_quality_eq
  obtain ⟨hHD1, hHD2⟩ := hHD
  rw [Finset.prod_pow (s := H.P) (n := 2)] at hq0
  set δ := H.density with hδdef
  set SV := wsum H.μ H.V with hSV
  set SW := wsum H.μ H.W with hSW
  set X := ∏ p ∈ H.P, (p : ℝ) ^ H.fgDist p with hX
  set Pi1 := ∏ p ∈ H.P, (1 - (if H.f p = H.g p ∧ 1 ≤ H.f p then 1 / (p : ℝ) else 0)) with hPi1
  set Z := ∏ p ∈ H.P, (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10 with hZ
  set E2 := ((H.nbhdW w0) ×ˢ H.W).filter (· ∈ H.E) with hE2
  set Sψ := ∑ e ∈ E2, ψ e.1 * ψ e.2 with hSψ
  have hSV0 : 0 < SV := H.wsum_V_pos_of_density_pos hδ
  have hSW0 : 0 < SW := H.wsum_W_pos_of_density_pos hδ
  have hδ1 : δ ≤ 1 := H.density_le_one
  have hX0 : 0 ≤ X := Finset.prod_nonneg (fun p _ => by positivity)
  have hZz : z0 ≤ Z := hz H.P H.P_prime
  have hZ0 : 0 < Z := lt_of_lt_of_le hz0 hZz
  have hPi10 : 0 < Pi1 := by
    apply Finset.prod_pos
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (H.P_prime p hp).two_le
    split_ifs
    · have : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
      linarith
    · norm_num
  have hSig0 : 0 ≤ Sψ := Finset.sum_nonneg (fun e _ => mul_nonneg (hψ _) (hψ _))
  have hδ0 : 0 ≤ δ := H.density_nonneg
  have hwl : ∀ v, 0 < v → (∀ p ∈ H.P, H.f p = H.g p ∧ 1 ≤ H.f p → p.Prime ∧ p ∣ v) →
      weight ψ v ≤ ψ v * Pi1 := fun v hv hdv => alt63_weight_le ψ hψ H.P H.f H.g v hv hdv
  clear_value δ SV SW X Pi1 Z E2 Sψ
  have h1 : (9 * δ / 10 * SV) * (9 * δ / 10 * SW) ≤ esum H.μ E2 := by
    have heq : esum H.μ E2 = ∑ v ∈ H.nbhdW w0, H.μ v * wsum H.μ (H.nbhdV v) := by
      unfold esum wsum GCDGraph.nbhdV
      rw [hE2, Finset.sum_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      split_ifs <;> simp
    rw [heq]
    calc (9 * δ / 10 * SV) * (9 * δ / 10 * SW) ≤ wsum H.μ (H.nbhdW w0) * (9 * δ / 10 * SW) :=
          mul_le_mul_of_nonneg_right (hHD2 w0 hw0) (by positivity)
      _ = ∑ v ∈ H.nbhdW w0, H.μ v * (9 * δ / 10 * SW) := by unfold wsum; rw [Finset.sum_mul]
      _ ≤ _ := Finset.sum_le_sum (fun v hv => mul_le_mul_of_nonneg_left
          (hHD1 v (Finset.mem_filter.1 hv).1) (H.μ_nonneg v))
  have hwnn : ∀ q, 0 ≤ weight ψ q := fun q =>
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hψ _)) (Nat.cast_nonneg _)
  have h2 : esum H.μ E2 ≤ Pi1 ^ 2 * Sψ := by
    unfold esum
    rw [hμ, hSψ, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    rw [hE2] at he
    have heE : e ∈ H.E := (Finset.mem_filter.1 he).2
    obtain ⟨hv, hw⟩ := Finset.mem_product.1 (H.E_sub heE)
    have hv' : weight ψ e.1 ≤ ψ e.1 * Pi1 :=
      hwl e.1 (H.V_pos _ hv) (fun p hp hc =>
        ⟨H.P_prime p hp, (dvd_pow_self p (by omega : H.f p ≠ 0)).trans (H.dvd_V p hp _ hv)⟩)
    have hw' : weight ψ e.2 ≤ ψ e.2 * Pi1 :=
      hwl e.2 (H.W_pos _ hw) (fun p hp hc =>
        ⟨H.P_prime p hp, (dvd_pow_self p (by omega : H.g p ≠ 0)).trans (H.dvd_W p hp _ hw)⟩)
    calc weight ψ e.1 * weight ψ e.2 ≤ (ψ e.1 * Pi1) * (ψ e.2 * Pi1) :=
          mul_le_mul hv' hw' (hwnn _) (mul_nonneg (hψ _) hPi10.le)
      _ = Pi1 ^ 2 * (ψ e.1 * ψ e.2) := by ring
  have hA : δ ^ 10 * SV * SW ≤ 100 / 81 * (Pi1 ^ 2 * Sψ) := by
    have hδ10 : δ ^ 10 ≤ δ ^ 2 := pow_le_pow_of_le_one hδ0 hδ1 (by norm_num)
    calc δ ^ 10 * SV * SW ≤ δ ^ 2 * SV * SW := by
          have := mul_le_mul_of_nonneg_right hδ10 (mul_pos hSV0 hSW0).le
          linarith [this]
      _ = 100 / 81 * ((9 * δ / 10 * SV) * (9 * δ / 10 * SW)) := by ring
      _ ≤ 100 / 81 * (Pi1 ^ 2 * Sψ) := by
          apply mul_le_mul_of_nonneg_left (h1.trans h2) (by norm_num)
  rw [hq0]
  have hXZ : 0 ≤ X / (Pi1 ^ 2 * Z) := div_nonneg hX0 (mul_pos (pow_pos hPi10 2) hZ0).le
  calc δ ^ 10 * SV * SW * (X / (Pi1 ^ 2 * Z)) ≤ 100 / 81 * (Pi1 ^ 2 * Sψ) * (X / (Pi1 ^ 2 * Z)) :=
        mul_le_mul_of_nonneg_right hA hXZ
    _ = 100 / 81 * X * Sψ / Z := by field_simp
    _ ≤ 100 / 81 * X * Sψ / z0 := div_le_div_of_nonneg_left
          (mul_nonneg (mul_nonneg (by norm_num) hX0) hSig0) hz0 hZz
    _ = 100 / 81 / z0 * X * Sψ := by ring
theorem alt63_qH_le (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (t : ℝ) (ht : 0 ≤ t) (z0 : ℝ)
    (hz0 : 0 < z0) (hz : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      z0 ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ ((31 : ℝ) / 30)) ^ 10)
    (H : GCDGraph) (hμ : H.μ = weight ψ) (hδ : 0 < H.density) (hR : H.R = ∅)
    (hHD : H.HighDegree) (hM : ∀ e ∈ H.E, Mqr ψ e.1 e.2 ≤ t * Nat.gcd e.1 e.2)
    (B1 B2 : ℕ → Prop) [DecidablePred B1] [DecidablePred B2] (D1 D2 : ℝ) (hD1 : 0 ≤ D1)
    (hD2 : 0 ≤ D2)
    (hc1 : ∀ x : ℝ, 1 ≤ x → (((Icc 1 ⌊x⌋₊).filter B1).card : ℝ) ≤ D1 * x)
    (hc2 : ∀ x : ℝ, 1 ≤ x → (((Icc 1 ⌊x⌋₊).filter B2).card : ℝ) ≤ D2 * x)
    (hB : ∀ e ∈ H.E, B1 (e.1 / H.aProd) ∨ B2 (e.2 / H.bProd)) :
    H.quality ≤ 100 / 81 / z0 * (D1 + D2) * t ^ 2 := by
  classical
  set m := ∏ p ∈ H.P, p ^ min (H.f p) (H.g p) with hm
  have hM' : ∀ e ∈ H.E, Mqr ψ e.1 e.2 ≤ t * m := fun e he => by
    have := hM e he
    rwa [H.alt63_gcd_eq hR e he] at this
  have hWne : H.W.Nonempty := by
    rcases H.W.eq_empty_or_nonempty with h | h
    · have := H.wsum_W_pos_of_density_pos hδ
      rw [h] at this
      simp [wsum] at this
    · exact h
  have hw0 : H.W.max' hWne ∈ H.W := H.W.max'_mem hWne
  set w0 := H.W.max' hWne with hw0def
  have hw0pos : 0 < w0 := H.W_pos _ hw0
  have hw0R : (0 : ℝ) < w0 := by exact_mod_cast hw0pos
  have ha : 0 < H.aProd := alt63_prod_pos H.P H.f H.P_prime
  have hb : 0 < H.bProd := alt63_prod_pos H.P H.g H.P_prime
  have haR : (0 : ℝ) < H.aProd := by exact_mod_cast ha
  have hbR : (0 : ℝ) < H.bProd := by exact_mod_cast hb
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hq := alt63_quality_le H ψ hψ hμ z0 hz0 hz hδ hHD w0 hw0
  set E2 := ((H.nbhdW w0) ×ˢ H.W).filter (· ∈ H.E) with hE2
  set X := ∏ p ∈ H.P, (p : ℝ) ^ H.fgDist p with hX
  have hX0 : 0 ≤ X := Finset.prod_nonneg (fun p _ => by positivity)
  have hSig1 : ∑ e ∈ E2, ψ e.1 * ψ e.2 ≤ (t * m / w0) * ∑ e ∈ H.E, ψ e.2 := by
    calc ∑ e ∈ E2, ψ e.1 * ψ e.2 ≤ ∑ e ∈ E2, (t * m / w0) * ψ e.2 := by
          apply Finset.sum_le_sum
          intro e he
          apply mul_le_mul_of_nonneg_right _ (hψ _)
          obtain ⟨he1, -⟩ := Finset.mem_filter.1 he
          obtain ⟨hv, -⟩ := Finset.mem_product.1 he1
          have hvw0 : (e.1, w0) ∈ H.E := (Finset.mem_filter.1 hv).2
          have h := hM' _ hvw0
          unfold Mqr at h
          rw [le_div_iff₀ hw0R, mul_comm]
          exact le_trans (le_max_left _ _) h
      _ = (t * m / w0) * ∑ e ∈ E2, ψ e.2 := by rw [Finset.mul_sum]
      _ ≤ (t * m / w0) * ∑ e ∈ H.E, ψ e.2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg (fun e he => (Finset.mem_filter.1 he).2)
            (fun e _ _ => hψ _)
  have hEeq : H.E.filter (fun e => B1 (e.1 / H.aProd)) ∪
      H.E.filter (fun e => B2 (e.2 / H.bProd)) = H.E := by
    rw [← Finset.filter_or]
    exact Finset.filter_true_of_mem hB
  have hSig2 : ∑ e ∈ H.E, ψ e.2 ≤ ∑ e ∈ H.E.filter (fun e => B1 (e.1 / H.aProd)), ψ e.2 +
      ∑ e ∈ H.E.filter (fun e => B2 (e.2 / H.bProd)), ψ e.2 := by
    calc ∑ e ∈ H.E, ψ e.2 = ∑ e ∈ (H.E.filter (fun e => B1 (e.1 / H.aProd)) ∪
          H.E.filter (fun e => B2 (e.2 / H.bProd))), ψ e.2 := by rw [hEeq]
      _ ≤ _ := alt84_sum_union_le _ _ (fun e : ℕ × ℕ => ψ e.2) (fun _ => hψ _)
  have hS1 := alt63_sum_fst H ψ hψ t ht m hM' B1 D1 hD1 hc1
  have hS2 := alt63_sum_snd H ψ hψ t ht m hM' B2
  have hbdvd : ∀ w ∈ H.W, H.bProd ∣ w := fun w hw =>
    alt63_prod_dvd H.P H.g H.P_prime w (H.W_pos w hw).ne' (fun p hp => H.dvd_W p hp w hw)
  have hWc : (H.W.card : ℝ) ≤ (w0 : ℝ) / H.bProd :=
    alt63_card_dvd_le H.W H.bProd w0 hb
      (fun w hw => ⟨H.W_pos w hw, hbdvd w hw, H.W.le_max' w hw⟩)
  have hW2 : ((H.W.filter (fun w => B2 (w / H.bProd))).card : ℝ) ≤
      D2 * ((w0 : ℝ) / H.bProd) := by
    apply alt63_count _ H.bProd w0 hb B2 D2 hD2 hc2
    intro w hw
    obtain ⟨hw, hb2⟩ := Finset.mem_filter.1 hw
    exact ⟨H.W_pos w hw, hbdvd w hw, H.W.le_max' w hw, hb2⟩
  have hXm : X * (m : ℝ) ^ 2 = (H.aProd : ℝ) * H.bProd := by
    have h := congrArg (Nat.cast : ℕ → ℝ) H.alt63_X_mul
    push_cast at h
    rw [hX, hm]
    push_cast
    exact h
  clear_value X E2
  have hK : 0 ≤ 100 / 81 / z0 * X := mul_nonneg (by positivity) hX0
  have htm : 0 ≤ t * m / w0 := div_nonneg (mul_nonneg ht hmR) hw0R.le
  have htma : 0 ≤ t * m / H.aProd := div_nonneg (mul_nonneg ht hmR) haR.le
  have hD1a : 0 ≤ D1 * t * m / H.aProd := div_nonneg (mul_nonneg (mul_nonneg hD1 ht) hmR) haR.le
  calc H.quality ≤ 100 / 81 / z0 * X * ∑ e ∈ E2, ψ e.1 * ψ e.2 := hq
    _ ≤ 100 / 81 / z0 * X * ((t * m / w0) * (H.W.card * (D1 * t * m / H.aProd) +
          (H.W.filter (fun w => B2 (w / H.bProd))).card * (t * m / H.aProd))) := by
        apply mul_le_mul_of_nonneg_left _ hK
        exact hSig1.trans (mul_le_mul_of_nonneg_left (hSig2.trans (add_le_add hS1 hS2)) htm)
    _ ≤ 100 / 81 / z0 * X * ((t * m / w0) * (((w0 : ℝ) / H.bProd) * (D1 * t * m / H.aProd) +
          (D2 * ((w0 : ℝ) / H.bProd)) * (t * m / H.aProd))) := by
        apply mul_le_mul_of_nonneg_left _ hK
        apply mul_le_mul_of_nonneg_left _ htm
        exact add_le_add (mul_le_mul_of_nonneg_right hWc hD1a)
          (mul_le_mul_of_nonneg_right hW2 htma)
    _ = 100 / 81 / z0 * (D1 + D2) * t ^ 2 * (X * (m : ℝ) ^ 2 / (H.aProd * H.bProd)) := by
        field_simp
    _ = 100 / 81 / z0 * (D1 + D2) * t ^ 2 := by
        rw [hXm, div_self (mul_pos haR hbR).ne', mul_one]
theorem prop63 : ∃ C : ℝ, 0 < C ∧ ∀ (ψ : ℕ → ℝ), (∀ q, 0 ≤ ψ q) → ∀ t : ℝ, 1 ≤ t →
    ∀ G : GCDGraph, G.μ = weight ψ → G.P = ∅ → G.V = G.W → wsum G.μ G.V ≤ 2 →
      (∀ e ∈ G.E, Mqr ψ e.1 e.2 ≤ t * Nat.gcd e.1 e.2 ∧ 10 ≤ Lsum t e.1 e.2) →
      esum G.μ G.E ≤ C / t := by
  classical
  obtain ⟨c, hc, h71⟩ := GCDGraph.prop71
  obtain ⟨z0, hz0, hz⟩ := alt63_zeta_bound
  obtain ⟨CA, hCA, hA⟩ := card_many_large_prime_factors_le
  have hT0 : 0 < T0 := by unfold T0; positivity
  have hf12 : (0 : ℝ) < (Nat.factorial 12 : ℝ) := by exact_mod_cast Nat.factorial_pos 12
  refine ⟨4 * T0 + 4 + 100 / 81 / z0 / c + 2 * (100 / 81 / z0) * CA * (Nat.factorial 12 : ℝ) / c,
    by positivity, ?_⟩
  intro ψ hψ t ht G hμ hP hVW hS hE
  set K := 100 / 81 / z0 with hKdef
  have hK : 0 < K := by positivity
  have ht0 : 0 < t := by linarith
  have hS0 : 0 ≤ wsum G.μ G.V := GCDGraph.alt_wsum_nonneg G.μ_nonneg _
  have hesum : esum G.μ G.E = G.density * (wsum G.μ G.V * wsum G.μ G.V) := by
    rw [alt63_esum_eq, hVW]
  have hqG : G.quality = G.density ^ 9 * esum G.μ G.E := by
    unfold GCDGraph.quality
    rw [hP, Finset.prod_empty, hesum, hVW]
    ring
  have hδ0 : 0 ≤ G.density := G.density_nonneg
  have hδ1 : G.density ≤ 1 := G.density_le_one
  have hE0 : 0 ≤ esum G.μ G.E := GCDGraph.alt_esum_nonneg G.μ_nonneg _
  have hSS0 : 0 ≤ wsum G.μ G.V * wsum G.μ G.V := mul_nonneg hS0 hS0
  have hSS : wsum G.μ G.V * wsum G.μ G.V ≤ 4 := by nlinarith
  have hE4 : esum G.μ G.E ≤ 4 := by
    rw [hesum]
    calc G.density * (wsum G.μ G.V * wsum G.μ G.V) ≤ 1 * 4 :=
          mul_le_mul hδ1 hSS hSS0 zero_le_one
      _ = 4 := one_mul 4
  have hB1 : 0 ≤ K / c := by positivity
  have hB2 : 0 ≤ 2 * K * CA * (Nat.factorial 12 : ℝ) / c := by positivity
  rw [le_div_iff₀ ht0]
  by_cases htT : t ≤ T0
  · have : esum G.μ G.E * t ≤ 4 * T0 :=
      mul_le_mul hE4 htT ht0.le (by norm_num)
    linarith
  push Not at htT
  by_cases hδt : G.density * t < 1
  · have : esum G.μ G.E * t ≤ 4 := by
      rw [hesum]
      calc G.density * (wsum G.μ G.V * wsum G.μ G.V) * t =
            (G.density * t) * (wsum G.μ G.V * wsum G.μ G.V) := by ring
        _ ≤ 1 * 4 := mul_le_mul hδt.le hSS hSS0 zero_le_one
        _ = 4 := one_mul 4
    linarith
  push Not at hδt
  have hδpos : 0 < G.density := by
    rcases hδ0.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hδt; linarith
  have h10 : 10 * G.density ^ (-(1 : ℝ) / 50) ≤ t := by
    have hs0 : 0 < G.density ^ (-(1 : ℝ) / 50) := Real.rpow_pos_of_pos hδpos _
    have hs50 : (G.density ^ (-(1 : ℝ) / 50)) ^ (50 : ℕ) = G.density⁻¹ := by
      rw [← Real.rpow_mul_natCast hδpos.le,
        show (-(1 : ℝ) / 50 * ((50 : ℕ) : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
    have hs50t : (G.density ^ (-(1 : ℝ) / 50)) ^ (50 : ℕ) ≤ t := by
      rw [hs50]
      calc G.density⁻¹ ≤ G.density⁻¹ * (G.density * t) :=
            le_mul_of_one_le_right (inv_nonneg.2 hδ0) hδt
        _ = t := by field_simp
    by_contra hcon
    push Not at hcon
    have h1 : t / 10 < G.density ^ (-(1 : ℝ) / 50) := by linarith
    have h2 : (t / 10) ^ (50 : ℕ) < (G.density ^ (-(1 : ℝ) / 50)) ^ (50 : ℕ) :=
      pow_lt_pow_left₀ h1 (by positivity) (by norm_num)
    have h3 : t ≤ (t / 10) ^ (50 : ℕ) := by
      rw [div_pow, le_div_iff₀ (by positivity)]
      have ht49 : (10 : ℝ) ^ 50 ≤ t ^ (49 : ℕ) := by
        have h1' : (10 : ℝ) ^ 50 ≤ T0 := by
          unfold T0; exact pow_le_pow_right₀ (by norm_num) (by norm_num)
        have h2' : t ≤ t ^ (49 : ℕ) := le_self_pow₀ ht (by norm_num)
        linarith
      calc t * 10 ^ 50 ≤ t * t ^ 49 := mul_le_mul_of_nonneg_left ht49 ht0.le
        _ = t ^ 50 := by ring
    linarith
  have hL : ∀ e ∈ G.E, 10 ≤ Lsum t e.1 e.2 := fun e he => (hE e he).2
  obtain ⟨G', hs, hδ', hR', hHD', hcase⟩ := h71 G t hP hδpos hL h10 htT
  have hμ' : G'.μ = weight ψ := hs.1.trans hμ
  have hM' : ∀ e ∈ G'.E, Mqr ψ e.1 e.2 ≤ t * Nat.gcd e.1 e.2 := fun e he =>
    (hE e (hs.2.2.2.1 he)).1
  have hu9 : 1 ≤ (G.density * t) ^ 9 := one_le_pow₀ hδt
  rcases hcase with h | h
  ·
    have hq' := alt63_qH_le ψ hψ t ht0.le z0 hz0 hz G' hμ' hδ' hR' hHD' hM'
      (fun _ => False) (fun _ => True) 0 1 le_rfl zero_le_one
      (fun x _ => by simp)
      (fun x hx => by
        rw [Finset.filter_true_of_mem (fun _ _ => trivial), Nat.card_Icc, one_mul]
        simp only [add_tsub_cancel_right]
        exact Nat.floor_le (by linarith))
      (fun e _ => Or.inr trivial)
    have hu : 1 ≤ (G.density * t) ^ 10 := one_le_pow₀ hδt
    have hcE : 0 ≤ c * esum G.μ G.E * t ^ 40 :=
      mul_nonneg (mul_nonneg hc.le hE0) (by positivity)
    have hA1 : c * esum G.μ G.E * t ^ 40 * (G.density * t) ^ 10 ≤ K * t ^ 2 := by
      have h' := h.trans hq'
      rw [hqG] at h'
      calc c * esum G.μ G.E * t ^ 40 * (G.density * t) ^ 10 =
            c * G.density * t ^ 50 * (G.density ^ 9 * esum G.μ G.E) := by ring
        _ ≤ K * (0 + 1) * t ^ 2 := h'
        _ = K * t ^ 2 := by ring
    have hA2 : c * esum G.μ G.E * t ^ 40 ≤ K * t ^ 2 :=
      le_trans (le_mul_of_one_le_right hcE hu) hA1
    have hA3 : c * esum G.μ G.E * t ^ 38 ≤ K := by
      have h' : (c * esum G.μ G.E * t ^ 38) * t ^ 2 ≤ K * t ^ 2 := by
        calc (c * esum G.μ G.E * t ^ 38) * t ^ 2 = c * esum G.μ G.E * t ^ 40 := by ring
          _ ≤ _ := hA2
      exact le_of_mul_le_mul_right h' (by positivity)
    have hA4 : c * (esum G.μ G.E * t) ≤ K := by
      have h' : t ≤ t ^ 38 := le_self_pow₀ ht (by norm_num)
      calc c * (esum G.μ G.E * t) ≤ c * (esum G.μ G.E * t ^ 38) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h' hE0) hc.le
        _ = c * esum G.μ G.E * t ^ 38 := by ring
        _ ≤ K := hA3
    have : esum G.μ G.E * t ≤ K / c := by
      rw [le_div_iff₀ hc]; linarith
    have : (0 : ℝ) ≤ 4 * T0 := by positivity
    linarith
  ·
    set bad : ℕ → Prop := fun n : ℕ =>
      (2 : ℝ) ≤ ∑ p ∈ n.primeFactors.filter (fun p : ℕ => t ≤ (p : ℝ)), (1 : ℝ) / p with hbad
    set D := CA * Real.exp (-(t ^ Real.exp (2 - 1))) with hD
    have hD0 : 0 ≤ D := by positivity
    have hcount : ∀ x : ℝ, 1 ≤ x → (((Icc 1 ⌊x⌋₊).filter bad).card : ℝ) ≤ D * x := by
      intro x hx
      have h' := hA x t 2 hx ht (by norm_num) (by norm_num)
      calc (((Icc 1 ⌊x⌋₊).filter bad).card : ℝ) ≤ CA * x * Real.exp (-(t ^ Real.exp (2 - 1))) := by
            convert h' using 3
        _ = D * x := by rw [hD]; ring
    have hB : ∀ e ∈ G'.E, bad (e.1 / G'.aProd) ∨ bad (e.2 / G'.bProd) := by
      intro e he
      have hL4 := h.2 e he
      obtain ⟨hv, hw⟩ := Finset.mem_product.1 (G'.E_sub he)
      have hx : 0 < e.1 / G'.aProd :=
        Nat.div_pos (Nat.le_of_dvd (G'.V_pos _ hv) (alt63_prod_dvd G'.P G'.f G'.P_prime _
          (G'.V_pos _ hv).ne' (fun p hp => G'.dvd_V p hp _ hv)))
          (alt63_prod_pos G'.P G'.f G'.P_prime)
      have hy : 0 < e.2 / G'.bProd :=
        Nat.div_pos (Nat.le_of_dvd (G'.W_pos _ hw) (alt63_prod_dvd G'.P G'.g G'.P_prime _
          (G'.W_pos _ hw).ne' (fun p hp => G'.dvd_W p hp _ hw)))
          (alt63_prod_pos G'.P G'.g G'.P_prime)
      have hsplit := alt63_Lsum_split t _ _ hx hy
      by_contra hcon
      simp only [hbad, not_or, not_le] at hcon
      linarith [hcon.1, hcon.2]
    have hq' := alt63_qH_le ψ hψ t ht0.le z0 hz0 hz G' hμ' hδ' hR' hHD' hM'
      bad bad D D hD0 hD0 hcount hcount hB
    have hEq : esum G.μ G.E ≤ t ^ 9 * G.quality := by
      rw [hqG]
      calc esum G.μ G.E = 1 * esum G.μ G.E := (one_mul _).symm
        _ ≤ (G.density * t) ^ 9 * esum G.μ G.E := mul_le_mul_of_nonneg_right hu9 hE0
        _ = t ^ 9 * (G.density ^ 9 * esum G.μ G.E) := by ring
    have hexp : Real.exp (-(t ^ Real.exp (2 - 1))) ≤ Real.exp (-t) := by
      apply Real.exp_le_exp.2
      have : t ≤ t ^ Real.exp (2 - 1) :=
        Real.self_le_rpow_of_one_le ht (Real.one_le_exp (by norm_num))
      linarith
    have hfac : t ^ 12 * Real.exp (-t) ≤ (Nat.factorial 12 : ℝ) := by
      have h' := Real.pow_div_factorial_le_exp _ ht0.le 12
      rw [div_le_iff₀ hf12] at h'
      calc t ^ 12 * Real.exp (-t) ≤ Real.exp t * (Nat.factorial 12 : ℝ) * Real.exp (-t) :=
            mul_le_mul_of_nonneg_right h' (Real.exp_pos _).le
        _ = (Nat.factorial 12 : ℝ) * (Real.exp t * Real.exp (-t)) := by ring
        _ = (Nat.factorial 12 : ℝ) := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    have hmain : c * (esum G.μ G.E * t) ≤ 2 * K * CA * (Nat.factorial 12 : ℝ) := by
      calc c * (esum G.μ G.E * t) ≤ c * (t ^ 9 * G.quality * t) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hEq ht0.le) hc.le
        _ = t ^ 10 * (c * G.quality) := by ring
        _ ≤ t ^ 10 * (K * (D + D) * t ^ 2) :=
            mul_le_mul_of_nonneg_left (h.1.trans hq') (by positivity)
        _ = 2 * K * CA * (t ^ 12 * Real.exp (-(t ^ Real.exp (2 - 1)))) := by rw [hD]; ring
        _ ≤ 2 * K * CA * (t ^ 12 * Real.exp (-t)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hexp (by positivity)
        _ ≤ 2 * K * CA * (Nat.factorial 12 : ℝ) :=
            mul_le_mul_of_nonneg_left hfac (by positivity)
    have : esum G.μ G.E * t ≤ 2 * K * CA * (Nat.factorial 12 : ℝ) / c := by
      rw [le_div_iff₀ hc]; linarith
    have : (0 : ℝ) ≤ 4 * T0 := by positivity
    linarith
theorem prop54 : ∃ C : ℝ, 0 < C ∧ ∀ (ψ : ℕ → ℝ), (∀ q, 0 ≤ ψ q) → ∀ X Y : ℕ, 1 ≤ X →
    ∑ q ∈ Icc X Y, weight ψ q ≤ 2 → ∀ t : ℝ, 1 ≤ t →
      ∑ e ∈ Et ψ X Y t, weight ψ e.1 * weight ψ e.2 ≤ C / t := by
  obtain ⟨C, hC, h63⟩ := prop63
  refine ⟨C, hC, ?_⟩
  intro ψ hψ X Y hX hsum t ht
  let G : GCDGraph :=
    { μ := weight ψ
      V := Icc X Y
      W := Icc X Y
      E := Et ψ X Y t
      P := ∅
      f := fun _ => 0
      g := fun _ => 0
      μ_nonneg := fun q => div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hψ _)) (Nat.cast_nonneg _)
      V_pos := fun v hv => by have := (Finset.mem_Icc.1 hv).1; omega
      W_pos := fun v hv => by have := (Finset.mem_Icc.1 hv).1; omega
      E_sub := Finset.filter_subset _ _
      P_prime := fun p hp => absurd hp (Finset.notMem_empty p)
      dvd_V := fun p hp => absurd hp (Finset.notMem_empty p)
      dvd_W := fun p hp => absurd hp (Finset.notMem_empty p)
      gcd_E := fun p hp => absurd hp (Finset.notMem_empty p)
      exact_V := fun p hp => absurd hp (Finset.notMem_empty p)
      exact_W := fun p hp => absurd hp (Finset.notMem_empty p) }
  exact h63 ψ hψ t ht G rfl rfl rfl hsum (fun e he => (Finset.mem_filter.1 he).2)
end DuffinSchaeffer
end Port24_Parts_EdgeBound

section Port24_Parts_UnitPairCount
open Finset
namespace DuffinSchaeffer
namespace UnitPairCountAux
lemma card_filter_range_mul_mod (Q : ℕ → Prop) [DecidablePred Q] (d k : ℕ) :
    ((range (d * k)).filter (fun s => Q (s % d))).card = k * ((range d).filter Q).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [mul_add, mul_one, Finset.card_filter, Finset.sum_range_add, ← Finset.card_filter, ih,
      Finset.card_filter (p := Q)]
    have : ∀ x ∈ range d, (if Q ((d * k + x) % d) then 1 else 0) = (if Q x then 1 else 0) := by
      intro x hx
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (mem_range.1 hx)]
    rw [Finset.sum_congr rfl this]
    ring
lemma card_filter_crt (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (co : Nat.Coprime m n)
    (Q1 Q2 : ℕ → Prop) [DecidablePred Q1] [DecidablePred Q2] :
    ((range (m * n)).filter (fun s => Q1 (s % m) ∧ Q2 (s % n))).card =
      ((range m).filter Q1).card * ((range n).filter Q2).card := by
  rw [← card_product]
  refine card_bij (fun s _ => (s % m, s % n)) ?_ ?_ ?_
  · intro s hs
    simp only [mem_filter, mem_range, mem_product] at hs ⊢
    exact ⟨⟨Nat.mod_lt _ (Nat.pos_of_ne_zero hm), hs.2.1⟩,
      Nat.mod_lt _ (Nat.pos_of_ne_zero hn), hs.2.2⟩
  · intro s1 hs1 s2 hs2 heq
    simp only [mem_filter, mem_range, Prod.mk.injEq] at hs1 hs2 heq
    exact ((Nat.modEq_and_modEq_iff_modEq_mul co).1 ⟨heq.1, heq.2⟩).eq_of_lt_of_lt hs1.1 hs2.1
  · rintro ⟨x, y⟩ hxy
    simp only [mem_filter, mem_range, mem_product] at hxy
    obtain ⟨⟨hx, hQ1⟩, hy, hQ2⟩ := hxy
    have h1 : (Nat.chineseRemainder co x y : ℕ) % m = x :=
      Eq.trans (Nat.chineseRemainder co x y).prop.1 (Nat.mod_eq_of_lt hx)
    have h2 : (Nat.chineseRemainder co x y : ℕ) % n = y :=
      Eq.trans (Nat.chineseRemainder co x y).prop.2 (Nat.mod_eq_of_lt hy)
    refine ⟨Nat.chineseRemainder co x y, ?_, ?_⟩
    · simp only [mem_filter, mem_range, h1, h2]
      exact ⟨Nat.chineseRemainder_lt_mul co x y hm hn, hQ1, hQ2⟩
    · simp only [h1, h2]
lemma sieve (F : ℕ → ℕ) (hF : ∀ p s, p ∣ F s ↔ p ∣ F (s % p)) :
    ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ((range (∏ p ∈ P, p)).filter (fun s => ∀ p ∈ P, ¬ p ∣ F s)).card =
        ∏ p ∈ P, ((range p).filter (fun x => ¬ p ∣ F x)).card := by
  intro P
  induction P using Finset.induction_on with
  | empty => intro _; simp
  | insert p P hpP ih =>
    intro hP
    have hp : p.Prime := hP p (mem_insert_self _ _)
    have hP' : ∀ q ∈ P, q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
    have hR0 : (∏ q ∈ P, q) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun q hq => (hP' q hq).ne_zero)
    have co : Nat.Coprime p (∏ q ∈ P, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      exact (Nat.coprime_primes hp (hP' q hq)).2 (fun h => hpP (h ▸ hq))
    rw [prod_insert hpP, prod_insert hpP, ← ih hP',
      ← card_filter_crt p _ hp.ne_zero hR0 co (fun x => ¬ p ∣ F x)
        (fun y => ∀ q ∈ P, ¬ q ∣ F y)]
    congr 1
    apply filter_congr
    intro s _
    simp only [mem_insert, forall_eq_or_imp]
    apply and_congr
    · rw [hF p s]
    · apply forall₂_congr
      intro q hq
      have hqR : q ∣ ∏ q ∈ P, q := Finset.dvd_prod_of_mem _ hq
      rw [hF q s, hF q (s % ∏ q ∈ P, q), Nat.mod_mod_of_dvd _ hqR]
lemma exists_root (p c e : ℕ) (hp : p.Prime) (he : ¬ p ∣ e) : ∃ x < p, p ∣ c + e * x := by
  have := Fact.mk hp
  have he' : (e : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact he
  refine ⟨((-(c : ZMod p)) / e).val, ZMod.val_lt _, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [mul_comm, div_mul_cancel₀ _ he']
  exact add_neg_cancel _
noncomputable def fA (p : ℕ) : ℝ := 1 - (p : ℝ)⁻¹
noncomputable def cfac (x y z p : ℕ) : ℝ :=
  fA p ^ 2 / ((if p ∣ x then fA p else 1) * (if p ∣ y then fA p else 1) *
    (if p ∣ z then fA p else 1))
lemma fA_pos {p : ℕ} (hp : p.Prime) : 0 < fA p := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : (0:ℝ) < p := by linarith
  have hinv : (p:ℝ)⁻¹ * p = 1 := inv_mul_cancel₀ hpos.ne'
  have hi0 : 0 < (p:ℝ)⁻¹ := inv_pos.2 hpos
  have := mul_le_mul_of_nonneg_left hp2 hi0.le
  unfold fA; linarith
lemma prod_fA_pos (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) : 0 < ∏ p ∈ s, fA p :=
  prod_pos (fun p hp => fA_pos (hs p hp))
lemma prod_ite_pos (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (x : ℕ) :
    0 < ∏ p ∈ s, (if p ∣ x then fA p else 1) := by
  apply prod_pos
  intro p hp
  split_ifs
  · exact fA_pos (hs p hp)
  · exact one_pos
lemma per_prime (p x y z good : ℕ) (hp : p.Prime) (h1 : good + 1 ≤ p)
    (h2 : ¬ p ∣ x → ¬ p ∣ y → ¬ p ∣ z → good + 2 ≤ p) :
    (good : ℝ) / p ≤ cfac x y z p := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : (0:ℝ) < p := by linarith
  have hinv : (p:ℝ)⁻¹ * p = 1 := inv_mul_cancel₀ hpos.ne'
  have hf0 : 0 < fA p := fA_pos hp
  have hf1 : fA p ≤ 1 := by
    have : 0 < (p:ℝ)⁻¹ := inv_pos.2 hpos
    unfold fA; linarith
  have hI : ∀ (P : Prop) [Decidable P],
      0 < (if P then fA p else 1) ∧ (if P then fA p else 1) ≤ 1 := by
    intro P _
    split_ifs <;> constructor <;> linarith
  have b1 := hI (p ∣ x)
  have b2 := hI (p ∣ y)
  have b3 := hI (p ∣ z)
  have e1 : p ∣ x → (if p ∣ x then fA p else 1) = fA p := fun h => by simp [h]
  have e2 : p ∣ y → (if p ∣ y then fA p else 1) = fA p := fun h => by simp [h]
  have e3 : p ∣ z → (if p ∣ z then fA p else 1) = fA p := fun h => by simp [h]
  have e1' : ¬ p ∣ x → (if p ∣ x then fA p else 1) = 1 := fun h => by simp [h]
  have e2' : ¬ p ∣ y → (if p ∣ y then fA p else 1) = 1 := fun h => by simp [h]
  have e3' : ¬ p ∣ z → (if p ∣ z then fA p else 1) = 1 := fun h => by simp [h]
  unfold cfac
  generalize (if p ∣ x then fA p else 1) = i1 at b1 e1 e1' ⊢
  generalize (if p ∣ y then fA p else 1) = i2 at b2 e2 e2' ⊢
  generalize (if p ∣ z then fA p else 1) = i3 at b3 e3 e3' ⊢
  by_cases hall : ¬ p ∣ x ∧ ¬ p ∣ y ∧ ¬ p ∣ z
  · rw [e1' hall.1, e2' hall.2.1, e3' hall.2.2, mul_one, mul_one, div_one]
    have hg2 : (good:ℝ) + 2 ≤ p := by exact_mod_cast h2 hall.1 hall.2.1 hall.2.2
    rw [div_le_iff₀ hpos]
    have e : fA p ^ 2 * p = p - 2 * ((p:ℝ)⁻¹ * p) + (p:ℝ)⁻¹ * ((p:ℝ)⁻¹ * p) := by
      unfold fA; ring
    rw [e, hinv]
    have : 0 < (p:ℝ)⁻¹ := inv_pos.2 hpos
    linarith
  · have hJ0 : 0 < i1 * i2 * i3 := mul_pos (mul_pos b1.1 b2.1) b3.1
    have hJ : i1 * i2 * i3 ≤ fA p := by
      by_cases hx : p ∣ x
      · rw [e1 hx]
        have := mul_le_mul_of_nonneg_left (mul_le_one₀ b2.2 b3.1.le b3.2) hf0.le
        nlinarith
      · by_cases hy : p ∣ y
        · rw [e2 hy]
          have := mul_le_mul_of_nonneg_left (mul_le_one₀ b1.2 b3.1.le b3.2) hf0.le
          nlinarith
        · have hz : p ∣ z := by
            by_contra hz; exact hall ⟨hx, hy, hz⟩
          rw [e3 hz]
          have := mul_le_mul_of_nonneg_left (mul_le_one₀ b1.2 b2.1.le b2.2) hf0.le
          nlinarith
    have hg1 : (good:ℝ) + 1 ≤ p := by exact_mod_cast h1
    have hA : (good:ℝ) / p ≤ fA p := by
      rw [div_le_iff₀ hpos]; unfold fA; rw [sub_mul, hinv]; linarith
    have hB : fA p ≤ fA p ^ 2 / (i1 * i2 * i3) := by
      rw [le_div_iff₀ hJ0]; nlinarith
    linarith
lemma totient_div_eq (n : ℕ) (hn : n ≠ 0) :
    (Nat.totient n : ℝ) / n = ∏ p ∈ n.primeFactors, fA p := by
  have h := Nat.totient_eq_mul_prod_factors n
  have h' : ((Nat.totient n : ℚ) : ℝ) =
      ((n * ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) : ℚ) : ℝ) := by rw [h]
  push_cast at h'
  rw [h']
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [mul_div_cancel_left₀ _ this]
  rfl
lemma prod_inter_ite (g x : ℕ) (hx : x ≠ 0) (f : ℕ → ℝ) :
    ∏ p ∈ g.primeFactors ∩ x.primeFactors, f p =
      ∏ p ∈ g.primeFactors, (if p ∣ x then f p else 1) := by
  rw [← Finset.prod_filter]
  congr 1
  ext p
  simp only [mem_inter, mem_filter, Nat.mem_primeFactors]
  tauto
lemma prod_of_dvd (g d : ℕ) (hg : g ≠ 0) (hdg : d ∣ g) (f : ℕ → ℝ) :
    ∏ p ∈ d.primeFactors, f p = ∏ p ∈ g.primeFactors, (if p ∣ d then f p else 1) := by
  rw [← Finset.prod_filter]
  congr 1
  ext p
  simp only [mem_filter, Nat.mem_primeFactors]
  have hd : d ≠ 0 := by rintro rfl; exact hg (Nat.eq_zero_of_zero_dvd hdg)
  constructor
  · rintro ⟨hp, hpd, _⟩; exact ⟨⟨hp, hpd.trans hdg, hg⟩, hpd⟩
  · rintro ⟨⟨hp, _, _⟩, hpd⟩; exact ⟨hp, hpd, hd⟩
end UnitPairCountAux
open UnitPairCountAux in
theorem card_unit_pairs_le (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (h : ℤ) :
    ((((range q) ×ˢ (range r)).filter (fun ab : ℕ × ℕ =>
        Nat.Coprime ab.1 q ∧ Nat.Coprime ab.2 r ∧
        (ab.1 : ℤ) * ((r / Nat.gcd q r : ℕ) : ℤ) - (ab.2 : ℤ) * ((q / Nat.gcd q r : ℕ) : ℤ) ≡ h
          [ZMOD (Nat.lcm q r : ℤ)])).card : ℝ) ≤
      (if Int.gcd h (coprimePart q r) = 1 then 1 else 0) *
        ((Nat.gcd q r : ℝ) * ((Nat.totient q : ℝ) / q) * ((Nat.totient r : ℝ) / r) *
          ((coprimePart q r : ℝ) / Nat.totient (coprimePart q r)) *
          ((Int.gcd h (Nat.gcd q r) : ℝ) / Nat.totient (Int.gcd h (Nat.gcd q r)))) := by
  classical
  have hg0 : 0 < Nat.gcd q r := Nat.gcd_pos_of_pos_left r hq
  have hq'0 : 0 < q / Nat.gcd q r := Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_left q r)) hg0
  have hr'0 : 0 < r / Nat.gcd q r := Nat.div_pos (Nat.le_of_dvd hr (Nat.gcd_dvd_right q r)) hg0
  have cop : Nat.Coprime (q / Nat.gcd q r) (r / Nat.gcd q r) := Nat.coprime_div_gcd_div_gcd hg0
  have hqg : q = Nat.gcd q r * (q / Nat.gcd q r) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_left q r)).symm
  have hrg : r = Nat.gcd q r * (r / Nat.gcd q r) :=
    (Nat.mul_div_cancel' (Nat.gcd_dvd_right q r)).symm
  have hmdef : coprimePart q r = (q / Nat.gcd q r) * (r / Nat.gcd q r) := rfl
  have hdg : Int.gcd h (Nat.gcd q r) ∣ Nat.gcd q r := by
    have := Int.gcd_dvd_right h (Nat.gcd q r : ℤ)
    exact_mod_cast this
  have hgl := Nat.gcd_mul_lcm q r
  generalize Nat.gcd q r = g at *
  generalize q / g = q' at *
  generalize r / g = r' at *
  obtain ⟨d, hdgcd⟩ : ∃ d, Int.gcd h g = d := ⟨_, rfl⟩
  rw [hdgcd] at hdg ⊢
  have hlcm : Nat.lcm q r = g * q' * r' := by
    apply Nat.eq_of_mul_eq_mul_left hg0
    rw [hgl, hqg, hrg]
    ring
  have hlcmZ : ((Nat.lcm q r : ℕ) : ℤ) = (g : ℤ) * q' * r' := by rw [hlcm]; push_cast; ring
  have hcopZ : IsCoprime (q' : ℤ) (r' : ℤ) := Nat.isCoprime_iff_coprime.2 cop
  have hq'Z : (q' : ℤ) ≠ 0 := by exact_mod_cast hq'0.ne'
  have hr'Z : (r' : ℤ) ≠ 0 := by exact_mod_cast hr'0.ne'
  have hgZ : (0 : ℤ) < g := by exact_mod_cast hg0
  have hd0 : d ≠ 0 := by
    rintro rfl; exact hg0.ne' (Nat.eq_zero_of_zero_dvd hdg)
  rw [hlcmZ]
  rcases Finset.eq_empty_or_nonempty (((range q) ×ˢ (range r)).filter (fun ab : ℕ × ℕ =>
        Nat.Coprime ab.1 q ∧ Nat.Coprime ab.2 r ∧
        (ab.1 : ℤ) * (r' : ℤ) - (ab.2 : ℤ) * (q' : ℤ) ≡ h [ZMOD (g : ℤ) * q' * r'])) with
    hE | ⟨⟨a0, b0⟩, h0⟩
  · rw [hE, card_empty, Nat.cast_zero]
    apply mul_nonneg (by split_ifs <;> norm_num)
    positivity
  simp only [mem_filter, mem_product, mem_range] at h0
  obtain ⟨⟨ha0, hb0⟩, hca0, hcb0, hm0⟩ := h0
  obtain ⟨k, hk⟩ := hm0.dvd
  have hA : IsCoprime h (q' : ℤ) := by
    have h1 : IsCoprime ((a0 : ℤ) * r') (q' : ℤ) := by
      apply IsCoprime.mul_left _ hcopZ.symm
      exact Nat.isCoprime_iff_coprime.2
        (Nat.Coprime.coprime_dvd_right (Dvd.intro_left g hqg.symm) hca0)
    have h2 := h1.add_mul_left_left (-(b0 : ℤ) + g * r' * k)
    convert h2 using 1 <;> first | rfl | linear_combination hk
  have hB : IsCoprime h (r' : ℤ) := by
    have h1 : IsCoprime (-((b0 : ℤ) * q')) (r' : ℤ) := by
      apply IsCoprime.neg_left
      apply IsCoprime.mul_left _ hcopZ
      exact Nat.isCoprime_iff_coprime.2
        (Nat.Coprime.coprime_dvd_right (Dvd.intro_left g hrg.symm) hcb0)
    have h2 := h1.add_mul_left_left ((a0 : ℤ) + g * q' * k)
    convert h2 using 1 <;> first | rfl | linear_combination hk
  have hgcd : Int.gcd h (coprimePart q r) = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one, hmdef, Nat.cast_mul]
    exact hA.mul_right hB
  rw [if_pos hgcd, one_mul]
  obtain ⟨Fe, hFe⟩ : ∃ Fe : ℕ → ℕ, ∀ t, Fe t = (a0 + q' * t) * (b0 + r' * t) :=
    ⟨_, fun t => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ,
      T = (range g).filter (fun t => ∀ p ∈ g.primeFactors, ¬ p ∣ Fe t) := ⟨_, rfl⟩
  have hsub : ((range q) ×ˢ (range r)).filter (fun ab : ℕ × ℕ =>
        Nat.Coprime ab.1 q ∧ Nat.Coprime ab.2 r ∧
        (ab.1 : ℤ) * (r' : ℤ) - (ab.2 : ℤ) * (q' : ℤ) ≡ h [ZMOD (g : ℤ) * q' * r']) ⊆
      T.image (fun t => ((a0 + q' * t) % q, (b0 + r' * t) % r)) := by
    rintro ⟨a, b⟩ hab
    simp only [mem_filter, mem_product, mem_range] at hab
    obtain ⟨⟨ha, hb⟩, hca, hcb, hm⟩ := hab
    have hd := (hm0.trans hm.symm).dvd
    have hd' : ((g : ℤ) * q' * r') ∣ ((a : ℤ) - a0) * r' - ((b : ℤ) - b0) * q' := by
      have e : ((a : ℤ) * r' - b * q') - (a0 * r' - b0 * q') =
          ((a : ℤ) - a0) * r' - ((b : ℤ) - b0) * q' := by ring
      rw [← e]; exact hd
    have h1 : (q' : ℤ) ∣ ((a : ℤ) - a0) * r' - ((b : ℤ) - b0) * q' :=
      dvd_trans ⟨g * r', by ring⟩ hd'
    have h2 : (q' : ℤ) ∣ ((a : ℤ) - a0) * r' := by
      have := dvd_add h1 (dvd_mul_left (q' : ℤ) ((b : ℤ) - b0))
      rwa [sub_add_cancel] at this
    obtain ⟨u, hu⟩ := hcopZ.dvd_of_dvd_mul_right h2
    have h1' : (r' : ℤ) ∣ ((a : ℤ) - a0) * r' - ((b : ℤ) - b0) * q' :=
      dvd_trans ⟨g * q', by ring⟩ hd'
    have h2' : (r' : ℤ) ∣ ((b : ℤ) - b0) * q' := by
      have := dvd_sub (dvd_mul_left (r' : ℤ) ((a : ℤ) - a0)) h1'
      rwa [sub_sub_cancel] at this
    obtain ⟨v, hv⟩ := hcopZ.symm.dvd_of_dvd_mul_right h2'
    have hguv : (g : ℤ) ∣ u - v := by
      rw [hu, hv] at hd'
      have hqr : ((q' : ℤ) * r') ≠ 0 := mul_ne_zero hq'Z hr'Z
      rw [← mul_dvd_mul_iff_right hqr]
      have e : (u - v) * ((q' : ℤ) * r') = q' * u * r' - r' * v * q' := by ring
      rw [e, ← mul_assoc]; exact hd'
    obtain ⟨t, htZ⟩ : ∃ t : ℕ, (t : ℤ) = u % g :=
      ⟨(u % g).toNat, Int.toNat_of_nonneg (Int.emod_nonneg u hgZ.ne')⟩
    have htg : t < g := by
      have := Int.emod_lt_of_pos u hgZ
      rw [← htZ] at this; exact_mod_cast this
    have hut : (g : ℤ) ∣ u - t := by
      rw [htZ, Int.emod_def]; exact ⟨u / g, by ring⟩
    have hvt : (g : ℤ) ∣ v - t := by
      have := dvd_sub hut hguv
      convert this using 1 <;> first | rfl | ring
    have haeq : a = (a0 + q' * t) % q := by
      have hmod : a ≡ a0 + q' * t [MOD q] := by
        rw [← Int.natCast_modEq_iff]
        apply Int.modEq_of_dvd
        obtain ⟨w, hw⟩ := hut
        refine ⟨-w, ?_⟩
        rw [hqg]; push_cast
        linear_combination -hu - (q' : ℤ) * hw
      have := hmod
      unfold Nat.ModEq at this
      rw [Nat.mod_eq_of_lt ha] at this
      exact this
    have hbeq : b = (b0 + r' * t) % r := by
      have hmod : b ≡ b0 + r' * t [MOD r] := by
        rw [← Int.natCast_modEq_iff]
        apply Int.modEq_of_dvd
        obtain ⟨w, hw⟩ := hvt
        refine ⟨-w, ?_⟩
        rw [hrg]; push_cast
        linear_combination -hv - (r' : ℤ) * hw
      have := hmod
      unfold Nat.ModEq at this
      rw [Nat.mod_eq_of_lt hb] at this
      exact this
    rw [mem_image]
    refine ⟨t, ?_, Prod.ext haeq.symm hbeq.symm⟩
    rw [hT, mem_filter, mem_range]
    refine ⟨htg, ?_⟩
    intro p hp hpF
    obtain ⟨hpp, hpg, -⟩ := Nat.mem_primeFactors.1 hp
    rw [hFe] at hpF
    rcases (Nat.Prime.dvd_mul hpp).1 hpF with h' | h'
    · have hpq : p ∣ q := hpg.trans (Dvd.intro q' hqg.symm)
      have hpa : p ∣ a := by rw [haeq]; exact (Nat.dvd_mod_iff hpq).2 h'
      have := Nat.dvd_gcd hpa hpq
      rw [Nat.Coprime.gcd_eq_one hca] at this
      exact hpp.not_dvd_one this
    · have hpr : p ∣ r := hpg.trans (Dvd.intro r' hrg.symm)
      have hpb : p ∣ b := by rw [hbeq]; exact (Nat.dvd_mod_iff hpr).2 h'
      have := Nat.dvd_gcd hpb hpr
      rw [Nat.Coprime.gcd_eq_one hcb] at this
      exact hpp.not_dvd_one this
  have hcard1 := (card_le_card hsub).trans card_image_le
  have hFmod : ∀ p s, p ∣ Fe s ↔ p ∣ Fe (s % p) := by
    intro p s
    rw [hFe, hFe, Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
    have hs : s % p ≡ s [MOD p] := Nat.mod_modEq s p
    have : ((a0 + q' * (s % p)) * (b0 + r' * (s % p))) % p =
        ((a0 + q' * s) * (b0 + r' * s)) % p :=
      ((hs.mul_left q').add_left a0).mul ((hs.mul_left r').add_left b0)
    rw [this]
  have hGprime : ∀ p ∈ g.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hRg : (∏ p ∈ g.primeFactors, p) ∣ g := Nat.prod_primeFactors_dvd g
  have hR0 : (∏ p ∈ g.primeFactors, p) ≠ 0 :=
    prod_ne_zero_iff.2 (fun p hp => (hGprime p hp).ne_zero)
  have hTcard : T.card = (g / ∏ p ∈ g.primeFactors, p) *
      ∏ p ∈ g.primeFactors, ((range p).filter (fun x => ¬ p ∣ Fe x)).card := by
    have key := card_filter_range_mul_mod (fun y => ∀ p ∈ g.primeFactors, ¬ p ∣ Fe y)
      (∏ p ∈ g.primeFactors, p) (g / ∏ p ∈ g.primeFactors, p)
    rw [Nat.mul_div_cancel' hRg, sieve Fe hFmod _ hGprime] at key
    rw [← key, hT]
    congr 1
    apply filter_congr
    intro s _
    apply forall₂_congr
    intro p hp
    have hpR : p ∣ ∏ p ∈ g.primeFactors, p := Finset.dvd_prod_of_mem _ hp
    rw [hFmod p s, hFmod p (s % ∏ p ∈ g.primeFactors, p), Nat.mod_mod_of_dvd _ hpR]
  have hTR : (T.card : ℝ) = g * ∏ p ∈ g.primeFactors,
      ((((range p).filter (fun x => ¬ p ∣ Fe x)).card : ℝ) / p) := by
    rw [hTcard, Nat.cast_mul, Nat.cast_div hRg (by exact_mod_cast hR0), Nat.cast_prod,
      Nat.cast_prod, prod_div_distrib]
    ring
  have hnot : ∀ p, p.Prime → p ∣ q' → p ∣ r' → False := by
    intro p hp h1 h2
    have := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one cop] at this
    exact hp.not_dvd_one this
  have hper : ∀ p ∈ g.primeFactors,
      ((((range p).filter (fun x => ¬ p ∣ Fe x)).card : ℝ) / p) ≤ cfac q' r' d p := by
    intro p hp
    obtain ⟨hpp, hpg, -⟩ := Nat.mem_primeFactors.1 hp
    apply per_prime p q' r' d _ hpp
    · obtain ⟨x, hxp, hx⟩ : ∃ x < p, p ∣ Fe x := by
        by_cases hr' : p ∣ r'
        · obtain ⟨x, hxp, hx⟩ := exists_root p a0 q' hpp (fun hq' => hnot p hpp hq' hr')
          exact ⟨x, hxp, by rw [hFe]; exact dvd_mul_of_dvd_left hx _⟩
        · obtain ⟨x, hxp, hx⟩ := exists_root p b0 r' hpp hr'
          exact ⟨x, hxp, by rw [hFe]; exact dvd_mul_of_dvd_right hx _⟩
      have hs : (range p).filter (fun x => ¬ p ∣ Fe x) ⊆ (range p).erase x := by
        intro y hy
        rw [mem_filter] at hy
        rw [mem_erase]
        exact ⟨fun hyx => hy.2 (by rw [hyx]; exact hx), hy.1⟩
      have := card_le_card hs
      rw [card_erase_of_mem (mem_range.2 hxp), card_range] at this
      have := hpp.two_le
      omega
    · intro hq' hr' hd'
      obtain ⟨x1, hx1p, hx1⟩ := exists_root p a0 q' hpp hq'
      obtain ⟨x2, hx2p, hx2⟩ := exists_root p b0 r' hpp hr'
      have hne : x1 ≠ x2 := by
        rintro rfl
        have hpA : (p : ℤ) ∣ (a0 : ℤ) + q' * x1 := by exact_mod_cast hx1
        have hpB : (p : ℤ) ∣ (b0 : ℤ) + r' * x1 := by exact_mod_cast hx2
        have hpX : (p : ℤ) ∣ (a0 : ℤ) * r' - b0 * q' := by
          have := dvd_sub (dvd_mul_of_dvd_left hpA (r' : ℤ)) (dvd_mul_of_dvd_left hpB (q' : ℤ))
          convert this using 1 <;> first | rfl | ring
        have hpgZ : (p : ℤ) ∣ (g : ℤ) := by exact_mod_cast hpg
        have hph : (p : ℤ) ∣ h := by
          have hpL : (p : ℤ) ∣ (g : ℤ) * q' * r' * k :=
            dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpgZ _) _) _
          have e : h = (h - ((a0 : ℤ) * r' - b0 * q')) + ((a0 : ℤ) * r' - b0 * q') := by ring
          rw [e, hk]
          exact dvd_add hpL hpX
        exact hd' (hdgcd ▸ Int.dvd_gcd hph hpgZ)
      have hs : (range p).filter (fun x => ¬ p ∣ Fe x) ⊆ ((range p).erase x1).erase x2 := by
        intro y hy
        rw [mem_filter] at hy
        rw [mem_erase, mem_erase]
        refine ⟨fun hyx => hy.2 ?_, fun hyx => hy.2 ?_, hy.1⟩
        · rw [hyx, hFe]; exact dvd_mul_of_dvd_right hx2 _
        · rw [hyx, hFe]; exact dvd_mul_of_dvd_left hx1 _
      have := card_le_card hs
      rw [card_erase_of_mem (mem_erase.2 ⟨hne.symm, mem_range.2 hx2p⟩),
        card_erase_of_mem (mem_range.2 hx1p), card_range] at this
      have := hpp.two_le
      omega
  have hpfq : q.primeFactors = g.primeFactors ∪ q'.primeFactors := by
    rw [hqg]; exact Nat.primeFactors_mul hg0.ne' hq'0.ne'
  have hpfr : r.primeFactors = g.primeFactors ∪ r'.primeFactors := by
    rw [hrg]; exact Nat.primeFactors_mul hg0.ne' hr'0.ne'
  have hGpos := prod_fA_pos g.primeFactors hGprime
  have hQpos := prod_fA_pos q'.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hRpos := prod_fA_pos r'.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hIq := prod_ite_pos g.primeFactors hGprime q'
  have hIr := prod_ite_pos g.primeFactors hGprime r'
  have hId := prod_ite_pos g.primeFactors hGprime d
  have hq_eq : (Nat.totient q : ℝ) / q = (∏ p ∈ g.primeFactors, fA p) *
      (∏ p ∈ q'.primeFactors, fA p) / ∏ p ∈ g.primeFactors, (if p ∣ q' then fA p else 1) := by
    rw [totient_div_eq q hq.ne', hpfq, ← prod_inter_ite g q' hq'0.ne']
    apply eq_div_of_mul_eq (by rw [prod_inter_ite g q' hq'0.ne']; exact hIq.ne')
    exact prod_union_inter
  have hr_eq : (Nat.totient r : ℝ) / r = (∏ p ∈ g.primeFactors, fA p) *
      (∏ p ∈ r'.primeFactors, fA p) / ∏ p ∈ g.primeFactors, (if p ∣ r' then fA p else 1) := by
    rw [totient_div_eq r hr.ne', hpfr, ← prod_inter_ite g r' hr'0.ne']
    apply eq_div_of_mul_eq (by rw [prod_inter_ite g r' hr'0.ne']; exact hIr.ne')
    exact prod_union_inter
  have hm_eq : (coprimePart q r : ℝ) / Nat.totient (coprimePart q r) =
      1 / ((∏ p ∈ q'.primeFactors, fA p) * (∏ p ∈ r'.primeFactors, fA p)) := by
    rw [← totient_div_eq q' hq'0.ne', ← totient_div_eq r' hr'0.ne', hmdef, Nat.totient_mul cop]
    have h1 : (q' : ℝ) ≠ 0 := by exact_mod_cast hq'0.ne'
    have h2 : (r' : ℝ) ≠ 0 := by exact_mod_cast hr'0.ne'
    have h3 : (Nat.totient q' : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hq'0).ne'
    have h4 : (Nat.totient r' : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hr'0).ne'
    push_cast
    field_simp
  have hd_eq : (d : ℝ) / Nat.totient d =
      1 / ∏ p ∈ g.primeFactors, (if p ∣ d then fA p else 1) := by
    rw [← prod_of_dvd g d hg0.ne' hdg, ← totient_div_eq d hd0]
    have h1 : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
    have h3 : (Nat.totient d : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero hd0)).ne'
    field_simp
  have hRHS : (g : ℝ) * ((Nat.totient q : ℝ) / q) * ((Nat.totient r : ℝ) / r) *
      ((coprimePart q r : ℝ) / Nat.totient (coprimePart q r)) * ((d : ℝ) / Nat.totient d) =
      g * ∏ p ∈ g.primeFactors, cfac q' r' d p := by
    rw [hq_eq, hr_eq, hm_eq, hd_eq]
    simp only [cfac]
    rw [prod_div_distrib, prod_pow, prod_mul_distrib, prod_mul_distrib]
    field_simp
  rw [hRHS]
  calc (_ : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hcard1
    _ = _ := hTR
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.prod_le_prod
      · intro p _; exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      · exact hper
end DuffinSchaeffer
end Port24_Parts_UnitPairCount

section Port24_Parts_MeasureLower
open MeasureTheory
namespace DuffinSchaeffer
section AltMLSecondMoment
open Set
noncomputable section
open scoped Classical
variable {Omega ι : Type*}
def alt_ml_eventIndicator (A : Set Omega) (omega : Omega) : ℝ :=
  if omega ∈ A then 1 else 0
lemma alt_ml_eventIndicator_apply (A : Set Omega) (omega : Omega) :
    alt_ml_eventIndicator A omega = if omega ∈ A then 1 else 0 := rfl
lemma alt_ml_eventIndicator_of_mem {A : Set Omega} {omega : Omega} (h : omega ∈ A) :
    alt_ml_eventIndicator A omega = 1 := by simp [alt_ml_eventIndicator, h]
lemma alt_ml_eventIndicator_of_not_mem {A : Set Omega} {omega : Omega} (h : omega ∉ A) :
    alt_ml_eventIndicator A omega = 0 := by simp [alt_ml_eventIndicator, h]
lemma alt_ml_eventIndicator_nonneg (A : Set Omega) (omega : Omega) :
    0 ≤ alt_ml_eventIndicator A omega := by
  by_cases h : omega ∈ A <;> simp [alt_ml_eventIndicator, h]
lemma alt_ml_eventIndicator_mul (A B : Set Omega) (omega : Omega) :
    alt_ml_eventIndicator A omega * alt_ml_eventIndicator B omega = alt_ml_eventIndicator (A ∩ B) omega := by
  by_cases hA : omega ∈ A <;> by_cases hB : omega ∈ B <;>
    simp [alt_ml_eventIndicator, hA, hB]
lemma alt_ml_eventIndicator_sq (A : Set Omega) (omega : Omega) :
    alt_ml_eventIndicator A omega ^ 2 = alt_ml_eventIndicator A omega := by
  by_cases hA : omega ∈ A <;> simp [alt_ml_eventIndicator, hA]
lemma alt_ml_measurable_eventIndicator [MeasurableSpace Omega] {A : Set Omega}
    (hA : MeasurableSet A) :
    Measurable (alt_ml_eventIndicator A) := by
  exact Measurable.ite hA measurable_const measurable_const
def alt_ml_indicatorCount (I : Finset ι) (A : ι → Set Omega) (omega : Omega) : ℝ :=
  ∑ i ∈ I, alt_ml_eventIndicator (A i) omega
lemma alt_ml_indicatorCount_nonneg (I : Finset ι) (A : ι → Set Omega) (omega : Omega) :
    0 ≤ alt_ml_indicatorCount I A omega := by
  exact Finset.sum_nonneg fun i hi => alt_ml_eventIndicator_nonneg (A i) omega
lemma alt_ml_measurable_indicatorCount [MeasurableSpace Omega]
    (I : Finset ι) (A : ι → Set Omega)
    (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    Measurable (alt_ml_indicatorCount I A) := by
  classical
  unfold alt_ml_indicatorCount
  exact Finset.measurable_sum _ fun i hi => alt_ml_measurable_eventIndicator (hA i hi)
lemma alt_ml_indicatorCount_eq_card_filter (I : Finset ι) (A : ι → Set Omega) (omega : Omega) :
    alt_ml_indicatorCount I A omega = ((I.filter fun i => omega ∈ A i).card : ℝ) := by
  classical
  simp [alt_ml_indicatorCount, alt_ml_eventIndicator]
lemma alt_ml_one_le_indicatorCount_iff (I : Finset ι) (A : ι → Set Omega) (omega : Omega) :
    1 ≤ alt_ml_indicatorCount I A omega ↔ ∃ i ∈ I, omega ∈ A i := by
  classical
  rw [alt_ml_indicatorCount_eq_card_filter]
  norm_num
  exact Finset.filter_nonempty_iff
lemma alt_ml_indicatorCount_pos_iff (I : Finset ι) (A : ι → Set Omega) (omega : Omega) :
    0 < alt_ml_indicatorCount I A omega ↔ ∃ i ∈ I, omega ∈ A i := by
  rw [← alt_ml_one_le_indicatorCount_iff I A omega]
  rw [alt_ml_indicatorCount_eq_card_filter]
  norm_num
lemma alt_ml_indicatorCount_sq_expand (I : Finset ι) (A : ι → Set Omega) (omega : Omega) :
    alt_ml_indicatorCount I A omega ^ 2 =
      ∑ i ∈ I, ∑ j ∈ I, alt_ml_eventIndicator (A i ∩ A j) omega := by
  classical
  simp only [alt_ml_indicatorCount, pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simpa [mul_comm] using alt_ml_eventIndicator_mul (A i) (A j) omega
variable [MeasurableSpace Omega] {mu : Measure Omega}
lemma alt_ml_integral_eventIndicator [IsFiniteMeasure mu] {A : Set Omega}
    (hA : MeasurableSet A) :
    ∫ omega, alt_ml_eventIndicator A omega ∂mu = mu.real A := by
  change ∫ omega, A.indicator (fun _ => (1 : ℝ)) omega ∂mu = mu.real A
  rw [integral_indicator hA]
  simp
lemma alt_ml_integrable_indicatorCount [IsFiniteMeasure mu]
    (I : Finset ι) (A : ι → Set Omega) (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    Integrable (alt_ml_indicatorCount I A) mu := by
  apply integrable_finsetSum I
  intro i hi
  apply Integrable.of_bound (alt_ml_measurable_eventIndicator (hA i hi)).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun omega => by
    by_cases h : omega ∈ A i <;> simp [alt_ml_eventIndicator, h]
lemma alt_ml_integral_indicatorCount [IsFiniteMeasure mu]
    (I : Finset ι) (A : ι → Set Omega) (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    ∫ omega, alt_ml_indicatorCount I A omega ∂mu =
      ∑ i ∈ I, mu.real (A i) := by
  classical
  simp only [alt_ml_indicatorCount]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    exact alt_ml_integral_eventIndicator (hA i hi)
  · intro i hi
    apply Integrable.of_bound (alt_ml_measurable_eventIndicator (hA i hi)).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun omega => by
      by_cases h : omega ∈ A i <;> simp [alt_ml_eventIndicator, h]
lemma alt_ml_integrable_indicatorCount_sq [IsFiniteMeasure mu]
    (I : Finset ι) (A : ι → Set Omega) (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    Integrable (fun omega => alt_ml_indicatorCount I A omega ^ 2) mu := by
  rw [show (fun omega => alt_ml_indicatorCount I A omega ^ 2) =
      (fun omega => alt_ml_indicatorCount I A omega * alt_ml_indicatorCount I A omega) by
    funext omega
    rw [pow_two]]
  refine Integrable.of_bound (C := (I.card : ℝ) ^ 2) ?_ ?_
  · exact ((alt_ml_measurable_indicatorCount I A hA).mul
      (alt_ml_measurable_indicatorCount I A hA)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun omega => by
      rw [← pow_two, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (alt_ml_indicatorCount_nonneg I A omega)
        (by
          rw [alt_ml_indicatorCount_eq_card_filter]
          exact_mod_cast Finset.card_filter_le I _) 2
lemma alt_ml_integral_indicatorCount_sq [IsFiniteMeasure mu]
    (I : Finset ι) (A : ι → Set Omega) (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    ∫ omega, alt_ml_indicatorCount I A omega ^ 2 ∂mu =
      ∑ i ∈ I, ∑ j ∈ I, mu.real (A i ∩ A j) := by
  classical
  simp_rw [alt_ml_indicatorCount_sq_expand]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      exact alt_ml_integral_eventIndicator ((hA i hi).inter (hA j hj))
    · intro j hj
      apply Integrable.of_bound
        (alt_ml_measurable_eventIndicator ((hA i hi).inter (hA j hj))).aestronglyMeasurable 1
      exact Filter.Eventually.of_forall fun omega => by
        by_cases h : omega ∈ A i ∩ A j <;> simp [alt_ml_eventIndicator, h]
  · intro i hi
    apply integrable_finsetSum I
    intro j hj
    apply Integrable.of_bound
      (alt_ml_measurable_eventIndicator ((hA i hi).inter (hA j hj))).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun omega => by
      by_cases h : omega ∈ A i ∩ A j <;> simp [alt_ml_eventIndicator, h]
omit [MeasurableSpace Omega] in
lemma alt_ml_indicatorCount_positive_set (I : Finset ι) (A : ι → Set Omega) :
    {omega | 0 < alt_ml_indicatorCount I A omega} = ⋃ i ∈ I, A i := by
  classical
  ext omega
  simp [alt_ml_indicatorCount_pos_iff]
omit [MeasurableSpace Omega] in
lemma alt_ml_indicatorCount_one_le_set (I : Finset ι) (A : ι → Set Omega) :
    {omega | 1 ≤ alt_ml_indicatorCount I A omega} = ⋃ i ∈ I, A i := by
  classical
  ext omega
  simp [alt_ml_one_le_indicatorCount_iff]
lemma alt_ml_finite_secondMoment_mul (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) :
    (∑ i ∈ S, f i) ^ 2 ≤
      ((S.filter fun i => 0 < f i).card : ℝ) * ∑ i ∈ S, f i ^ 2 := by
  classical
  let g : ι → ℝ := fun i => if 0 < f i then 1 else 0
  have hfg : ∀ i ∈ S, f i * g i = f i := by
    intro i hi
    by_cases hpos : 0 < f i
    · simp [g, hpos]
    · have hz : f i = 0 := le_antisymm (not_lt.mp hpos) (hf i hi)
      simp [g, hz]
  have hg : ∑ i ∈ S, g i ^ 2 = ((S.filter fun i => 0 < f i).card : ℝ) := by
    simp [g]
  have hsum : ∑ i ∈ S, f i * g i = ∑ i ∈ S, f i :=
    Finset.sum_congr rfl hfg
  calc
    (∑ i ∈ S, f i) ^ 2 = (∑ i ∈ S, f i * g i) ^ 2 := by rw [hsum]
    _ ≤ (∑ i ∈ S, f i ^ 2) * ∑ i ∈ S, g i ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq S f g
    _ = ((S.filter fun i => 0 < f i).card : ℝ) * ∑ i ∈ S, f i ^ 2 := by
      rw [hg, mul_comm]
lemma alt_ml_finite_secondMoment_ratio (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) (hsecond : 0 < ∑ i ∈ S, f i ^ 2) :
    (∑ i ∈ S, f i) ^ 2 / (∑ i ∈ S, f i ^ 2) ≤
      ((S.filter fun i => 0 < f i).card : ℝ) := by
  rw [div_le_iff₀ hsecond]
  simpa [mul_comm] using alt_ml_finite_secondMoment_mul S f hf
lemma alt_ml_integral_mul_sq_le_integral_sq_mul_integral_sq
    (f g : Omega → ℝ)
    (hf : Integrable (fun omega => f omega ^ 2) mu)
    (hg : Integrable (fun omega => g omega ^ 2) mu)
    (hfg : Integrable (fun omega => f omega * g omega) mu) :
    (∫ omega, f omega * g omega ∂mu) ^ 2 ≤
      (∫ omega, f omega ^ 2 ∂mu) * (∫ omega, g omega ^ 2 ∂mu) := by
  have h_cauchy_schwarz :
      0 ≤ ∫ omega,
        (f omega -
          (∫ omega, f omega * g omega ∂mu) /
            (∫ omega, g omega ^ 2 ∂mu) * g omega) ^ 2 ∂mu :=
    integral_nonneg fun _ => sq_nonneg _
  by_cases h : ∫ omega, g omega ^ 2 ∂mu = 0 <;>
      simp only [h, sub_sq, mul_pow] at h_cauchy_schwarz ⊢
  · rw [integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _)] at h
    · have hgzero : g =ᵐ[mu] 0 := h.mono fun omega homega => by
        simp only [Pi.zero_apply]
        exact sq_eq_zero_iff.mp (by simpa using homega)
      have hfgzero : ∫ omega, f omega * g omega ∂mu = 0 := by
        apply integral_eq_zero_of_ae
        exact hgzero.mono fun omega homega => by simp [homega]
      simp [hfgzero]
    · exact hg
  · rw [integral_add, integral_sub] at h_cauchy_schwarz
    · simp only [div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm,
        integral_mul_const] at h_cauchy_schwarz ⊢
      simp only [← mul_assoc, integral_mul_const] at h_cauchy_schwarz ⊢
      have hfn : 0 ≤ ∫ omega, f omega ^ 2 ∂mu :=
        integral_nonneg fun omega => sq_nonneg (f omega)
      have hgn : 0 ≤ ∫ omega, g omega ^ 2 ∂mu :=
        integral_nonneg fun omega => sq_nonneg (g omega)
      nlinarith [inv_mul_cancel_left₀ h (∫ omega, f omega * g omega ∂mu),
        inv_mul_cancel₀ h]
    · exact hf
    · convert hfg.mul_const
        (2 * ((∫ omega, f omega * g omega ∂mu) /
          (∫ omega, g omega ^ 2 ∂mu))) using 2
      all_goals ring
    · refine Integrable.sub hf ?_
      convert hfg.mul_const
        (2 * ((∫ omega, f omega * g omega ∂mu) /
          (∫ omega, g omega ^ 2 ∂mu))) using 2
      all_goals ring
    · exact hg.const_mul _
theorem alt_ml_integral_secondMoment_mul [IsFiniteMeasure mu]
    (Z : Omega → ℝ) (hZ : 0 ≤ Z)
    (hZmeas : Measurable Z) (hZint : Integrable Z mu)
    (hZ2 : Integrable (fun omega => Z omega ^ 2) mu) :
    (∫ omega, Z omega ∂mu) ^ 2 ≤
      (∫ omega, Z omega ^ 2 ∂mu) * mu.real {omega | 0 < Z omega} := by
  let support : Set Omega := {omega | 0 < Z omega}
  let oneSupport : Omega → ℝ := alt_ml_eventIndicator support
  have hsupport : MeasurableSet support :=
    measurableSet_lt measurable_const hZmeas
  have hone : Integrable oneSupport mu := by
    apply Integrable.of_bound
      (alt_ml_measurable_eventIndicator hsupport).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun omega => by
      by_cases h : omega ∈ support <;> simp [alt_ml_eventIndicator, h]
  have hone2 : Integrable (fun omega => oneSupport omega ^ 2) mu :=
    hone.congr (Filter.Eventually.of_forall fun omega => by
      exact (alt_ml_eventIndicator_sq support omega).symm)
  have hprod : Integrable (fun omega => Z omega * oneSupport omega) mu :=
    hZint.mul_bdd (c := 1) (alt_ml_measurable_eventIndicator hsupport).aestronglyMeasurable
      (Filter.Eventually.of_forall fun omega => by
        by_cases h : omega ∈ support <;> simp [oneSupport, h, alt_ml_eventIndicator_of_mem, alt_ml_eventIndicator_of_not_mem])
  have hmul := alt_ml_integral_mul_sq_le_integral_sq_mul_integral_sq
    Z oneSupport hZ2 hone2 hprod
  have hfirst : (∫ omega, Z omega * oneSupport omega ∂mu) = ∫ omega, Z omega ∂mu := by
    apply integral_congr_ae
    filter_upwards with omega
    by_cases hpos : 0 < Z omega
    · simp [oneSupport, support, hpos, alt_ml_eventIndicator_of_mem]
    · have hz : Z omega = 0 := le_antisymm (not_lt.mp hpos) (hZ omega)
      simp [hz]
  have hsecond : (∫ omega, oneSupport omega ^ 2 ∂mu) = mu.real support := by
    calc
      (∫ omega, oneSupport omega ^ 2 ∂mu) = ∫ omega, oneSupport omega ∂mu := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun omega => alt_ml_eventIndicator_sq support omega
      _ = mu.real support := alt_ml_integral_eventIndicator hsupport
  simpa only [hfirst, hsecond, support] using hmul
theorem alt_ml_indicatorCount_secondMoment_bound [IsFiniteMeasure mu]
    (I : Finset ι) (A : ι → Set Omega) (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    (∑ i ∈ I, mu.real (A i)) ^ 2 ≤
      (∑ i ∈ I, ∑ j ∈ I, mu.real (A i ∩ A j)) *
        mu.real (⋃ i ∈ I, A i) := by
  have h := alt_ml_integral_secondMoment_mul (mu := mu) (alt_ml_indicatorCount I A)
    (alt_ml_indicatorCount_nonneg I A) (alt_ml_measurable_indicatorCount I A hA)
    (alt_ml_integrable_indicatorCount I A hA)
    (alt_ml_integrable_indicatorCount_sq I A hA)
  rwa [alt_ml_integral_indicatorCount I A hA, alt_ml_integral_indicatorCount_sq I A hA,
    alt_ml_indicatorCount_positive_set I A] at h
end
end AltMLSecondMoment
open Finset
theorem alt_ml_prod_sq_div_le (N : ℕ) (hN : 1 ≤ N) : ∀ S : Finset ℕ, (∀ n ∈ S, 2 ≤ n ∧ n ≤ N) →
    ∏ n ∈ S, ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ≤ 2 * (N : ℝ) / ((N : ℝ) + 1) := by
  induction N, hN using Nat.le_induction with
  | base =>
    intro S hS
    have hSe : S = ∅ := by
      ext n
      simp only [Finset.notMem_empty, iff_false]
      intro hn
      have := hS n hn
      omega
    subst hSe
    norm_num
  | succ N hN ih =>
    intro S hS
    have hS' : ∀ n ∈ S.erase (N + 1), 2 ≤ n ∧ n ≤ N := by
      intro n hn
      obtain ⟨hne, hn⟩ := Finset.mem_erase.1 hn
      have := hS n hn
      omega
    have h1 := ih _ hS'
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hmono : 2 * (N : ℝ) / (N + 1) ≤ 2 * ((N + 1 : ℕ) : ℝ) / (((N + 1 : ℕ) : ℝ) + 1) := by
      push_cast
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    by_cases hmem : N + 1 ∈ S
    · rw [← Finset.mul_prod_erase S _ hmem]
      have hfac : 0 ≤ ((N + 1 : ℕ) : ℝ) ^ 2 / (((N + 1 : ℕ) : ℝ) ^ 2 - 1) := by
        push_cast
        apply div_nonneg (by positivity)
        nlinarith
      calc ((N + 1 : ℕ) : ℝ) ^ 2 / (((N + 1 : ℕ) : ℝ) ^ 2 - 1) *
            ∏ x ∈ S.erase (N + 1), ((x : ℝ) ^ 2 / ((x : ℝ) ^ 2 - 1))
          ≤ ((N + 1 : ℕ) : ℝ) ^ 2 / (((N + 1 : ℕ) : ℝ) ^ 2 - 1) * (2 * (N : ℝ) / ((N : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left h1 hfac
        _ = 2 * ((N + 1 : ℕ) : ℝ) / (((N + 1 : ℕ) : ℝ) + 1) := by
            push_cast
            have hd : ((N : ℝ) + 1) ^ 2 - 1 = N * (N + 2) := by ring
            rw [hd]
            have hN0 : (N : ℝ) ≠ 0 := by positivity
            field_simp
            ring
    · rw [Finset.erase_eq_of_notMem hmem] at h1
      exact h1.trans hmono
theorem alt_ml_prod_primes_sq_div_le_two (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∏ p ∈ S, ((p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1)) ≤ 2 := by
  set N := max (S.sup id) 1 with hNdef
  have hN : 1 ≤ N := le_max_right _ _
  have h := alt_ml_prod_sq_div_le N hN S (fun n hn => ⟨(hS n hn).two_le,
    le_trans (Finset.le_sup (f := id) hn) (le_max_left _ _)⟩)
  refine h.trans ?_
  rw [div_le_iff₀ (by positivity)]
  linarith
theorem alt_ml_inv_one_sub_eq (p : ℕ) (hp : p.Prime) :
    (1 - 1 / (p : ℝ))⁻¹ = (1 + 1 / (p : ℝ)) * ((p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1)) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp2 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hp3 : (p : ℝ) + 1 ≠ 0 := by linarith
  have : (p : ℝ) ^ 2 - 1 = (p - 1) * (p + 1) := by ring
  rw [this]
  field_simp
theorem alt_ml_div_totient_eq (m : ℕ) (hm : 0 < m) :
    (m : ℝ) / Nat.totient m = ∏ p ∈ m.primeFactors, (1 - 1 / (p : ℝ))⁻¹ := by
  have hq := Nat.totient_eq_mul_prod_factors m
  have hr : (Nat.totient m : ℝ) = m * ∏ p ∈ m.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have := congrArg (fun x : ℚ => (x : ℝ)) hq
    push_cast at this
    exact this
  rw [hr, Finset.prod_inv_distrib]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  simp only [one_div]
  field_simp
theorem alt_ml_div_totient_le (d : ℕ) (hd : 0 < d) :
    (d : ℝ) / Nat.totient d ≤ 2 * ∑ e ∈ d.divisors, (1 : ℝ) / e := by
  rw [alt_ml_div_totient_eq d hd]
  have hprod : ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ))⁻¹ =
      (∏ p ∈ d.primeFactors, (1 + 1 / (p : ℝ))) *
        ∏ p ∈ d.primeFactors, ((p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    exact alt_ml_inv_one_sub_eq p (Nat.prime_of_mem_primeFactors hp)
  have h1 : ∏ p ∈ d.primeFactors, (1 + 1 / (p : ℝ)) ≤ ∑ e ∈ d.divisors, (1 : ℝ) / e := by
    rw [Finset.prod_one_add]
    have hinj : Set.InjOn (fun t : Finset ℕ => ∏ p ∈ t, p) (d.primeFactors.powerset : Set _) := by
      intro t1 ht1 t2 ht2 heq
      have hp1 : ∀ p ∈ t1, p.Prime := fun p hp =>
        Nat.prime_of_mem_primeFactors ((Finset.mem_powerset.1 ht1) hp)
      have hp2 : ∀ p ∈ t2, p.Prime := fun p hp =>
        Nat.prime_of_mem_primeFactors ((Finset.mem_powerset.1 ht2) hp)
      have := congrArg Nat.primeFactors heq
      simp only at this
      rwa [Nat.primeFactors_prod hp1, Nat.primeFactors_prod hp2] at this
    have heq : ∑ t ∈ d.primeFactors.powerset, ∏ p ∈ t, (1 / (p : ℝ)) =
        ∑ e ∈ d.primeFactors.powerset.image (fun t : Finset ℕ => ∏ p ∈ t, p), (1 : ℝ) / e := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro t _
      push_cast
      rw [Finset.prod_div_distrib, Finset.prod_const_one]
    rw [heq]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 he
      rw [Nat.mem_divisors]
      refine ⟨dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.mem_powerset.1 ht))
        (Nat.prod_primeFactors_dvd d), hd.ne'⟩
    · intro e _ _
      positivity
  have h2 := alt_ml_prod_primes_sq_div_le_two d.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have h0 : 0 ≤ ∏ p ∈ d.primeFactors, (1 + 1 / (p : ℝ)) :=
    Finset.prod_nonneg fun p _ => by positivity
  rw [hprod]
  calc (∏ p ∈ d.primeFactors, (1 + 1 / (p : ℝ))) *
        ∏ p ∈ d.primeFactors, ((p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1))
      ≤ (∏ p ∈ d.primeFactors, (1 + 1 / (p : ℝ))) * 2 := mul_le_mul_of_nonneg_left h2 h0
    _ ≤ (∑ e ∈ d.divisors, (1 : ℝ) / e) * 2 := mul_le_mul_of_nonneg_right h1 (by norm_num)
    _ = 2 * ∑ e ∈ d.divisors, (1 : ℝ) / e := mul_comm _ _
theorem alt_ml_sum_gcd_ratio_le (q K : ℕ) (hq : 0 < q) :
    ∑ h ∈ Icc 1 K, (Nat.gcd h q : ℝ) / Nat.totient (Nat.gcd h q) ≤ 4 * K := by
  have hstep : ∀ h ∈ Icc 1 K, (Nat.gcd h q : ℝ) / Nat.totient (Nat.gcd h q) ≤
      2 * ∑ e ∈ Icc 1 K, (if e ∣ h then (1 : ℝ) / e else 0) := by
    intro h hh
    obtain ⟨h1, hK⟩ := Finset.mem_Icc.1 hh
    have hh0 : h ≠ 0 := by omega
    refine (alt_ml_div_totient_le _ (Nat.gcd_pos_of_pos_right h hq)).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro e he
      have he' := Nat.dvd_trans (Nat.dvd_of_mem_divisors he) (Nat.gcd_dvd_left h q)
      have hle := Nat.le_of_dvd (by omega) he'
      have hpos := Nat.pos_of_mem_divisors he
      exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hpos, by omega⟩, he'⟩
    · intro e _ _
      positivity
  calc ∑ h ∈ Icc 1 K, (Nat.gcd h q : ℝ) / Nat.totient (Nat.gcd h q)
      ≤ ∑ h ∈ Icc 1 K, 2 * ∑ e ∈ Icc 1 K, (if e ∣ h then (1 : ℝ) / e else 0) :=
        Finset.sum_le_sum hstep
    _ = 2 * ∑ e ∈ Icc 1 K, ∑ h ∈ Icc 1 K, (if e ∣ h then (1 : ℝ) / e else 0) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ = 2 * ∑ e ∈ Icc 1 K, ((1 : ℝ) / e) * (((Icc 1 K).filter (fun h => e ∣ h)).card : ℝ) := by
        congr 1
        apply Finset.sum_congr rfl
        intro e _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ 2 * ∑ e ∈ Icc 1 K, ((1 : ℝ) / e) * ((K : ℝ) / e) := by
        gcongr with e he
        have hc : ((Icc 1 K).filter (fun h => e ∣ h)).card = K / e := by
          rw [← Nat.Ioc_filter_dvd_card_eq_div K e]
          rfl
        rw [hc]
        exact Nat.cast_div_le
    _ = 2 * K * ∑ e ∈ Icc 1 K, ((e : ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        field_simp
    _ ≤ 2 * K * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (K + 1)
        have hI : Icc 1 K = Ioo 0 (K + 1) := by
          ext e; simp only [Finset.mem_Icc, Finset.mem_Ioo]; omega
        rw [hI]
        refine h.trans ?_
        norm_num
    _ = 4 * K := by ring
theorem alt_ml_volumeReal_ball_eq (x : UnitAddCircle) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    volume.real (Metric.ball x ρ) = min 1 (2 * ρ) := by
  rw [measureReal_def]
  have hvolume : volume (Metric.ball x ρ) = ENNReal.ofReal (min 1 (2 * ρ)) := by
    rw [measure_congr AddCircle.closedBall_ae_eq_ball.symm, AddCircle.volume_closedBall]
  rw [hvolume, ENNReal.toReal_ofReal]
  exact le_min (by norm_num) (mul_nonneg (by norm_num) hρ)
def alt_ml_fiber (q : ℕ) (h : ℤ) : Finset (ℕ × ℕ) :=
  ((range q) ×ˢ (range q)).filter (fun ab : ℕ × ℕ =>
    Nat.Coprime ab.1 q ∧ Nat.Coprime ab.2 q ∧
    (ab.1 : ℤ) * ((q / Nat.gcd q q : ℕ) : ℤ) - (ab.2 : ℤ) * ((q / Nat.gcd q q : ℕ) : ℤ) ≡ h
      [ZMOD (Nat.lcm q q : ℤ)])
theorem alt_ml_card_fiber_le (q : ℕ) (hq : 0 < q) (n : ℕ) (s : ℤ) (hs : s = n ∨ s = -n) :
    ((alt_ml_fiber q s).card : ℝ) ≤
      (q : ℝ) * ((Nat.totient q : ℝ) / q) ^ 2 *
        ((Nat.gcd n q : ℝ) / Nat.totient (Nat.gcd n q)) := by
  have h1 : ((alt_ml_fiber q s).card : ℝ) ≤
      (if Int.gcd s (coprimePart q q) = 1 then 1 else 0) *
        ((Nat.gcd q q : ℝ) * ((Nat.totient q : ℝ) / q) * ((Nat.totient q : ℝ) / q) *
          ((coprimePart q q : ℝ) / Nat.totient (coprimePart q q)) *
          ((Int.gcd s (Nat.gcd q q) : ℝ) / Nat.totient (Int.gcd s (Nat.gcd q q)))) :=
    card_unit_pairs_le q q hq hq s
  have hcp : coprimePart q q = 1 := by
    simp [coprimePart, Nat.gcd_self, Nat.div_self hq]
  have hgs : Int.gcd s (Nat.gcd q q) = Nat.gcd n q := by
    rw [Nat.gcd_self]
    rcases hs with rfl | rfl
    · exact Int.gcd_natCast_natCast n q
    · rw [Int.neg_gcd]; exact Int.gcd_natCast_natCast n q
  rw [hcp, hgs] at h1
  simp only [Nat.cast_one, Int.gcd_one_right, if_true, one_mul, Nat.totient_one, div_one,
    mul_one, Nat.gcd_self] at h1
  exact h1.trans (le_of_eq (by ring))
theorem measure_Aq_ge : ∃ c : ℝ, 0 < c ∧ ∀ ψ : ℕ → ℝ, (∀ q, 0 ≤ ψ q) → ∀ q : ℕ, 0 < q →
    weight ψ q ≤ 1 / 2 → c * weight ψ q ≤ volume.real (Aq ψ q) := by
  classical
  set Cs : ℝ := 4 with hCsdef
  have hCs : (0 : ℝ) < Cs := by norm_num
  refine ⟨4 / (2 + 4 * Cs), by positivity, ?_⟩
  intro ψ hψ q hq hw
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set δ : ℝ := ψ q / q with hδdef
  have hδ0 : 0 ≤ δ := div_nonneg (hψ q) hqR.le
  set R : Finset ℕ := (range q).filter (fun a => Nat.Coprime a q) with hRdef
  have hRcard : (R.card : ℝ) = Nat.totient q := by
    rw [Nat.totient_eq_card_coprime]
    congr 2
    apply Finset.filter_congr
    intro a _
    exact Nat.coprime_comm
  set B : ℕ → Set UnitAddCircle := fun a => Metric.ball ((((a : ℝ) / q : ℝ)) : UnitAddCircle) δ
    with hBdef
  have hBmeas : ∀ a ∈ R, MeasurableSet (B a) := fun a _ => Metric.isOpen_ball.measurableSet
  have hsub : (⋃ a ∈ R, B a) ⊆ Aq ψ q := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨haq, hcop⟩ := Finset.mem_filter.1 ha
    rw [Aq, UnitAddCircle.mem_approxAddOrderOf_iff hq]
    refine ⟨a, Finset.mem_range.1 haq, hcop, ?_⟩
    have := hx
    rw [hBdef, Metric.mem_ball, dist_eq_norm] at this
    exact this
  have hw0 : 0 ≤ weight ψ q := by
    unfold weight; have := hψ q; positivity
  have hwdef : weight ψ q = (Nat.totient q : ℝ) * δ := by
    rw [weight, hδdef]; ring
  have hc2 : 4 / (2 + 4 * Cs) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  rcases hw0.lt_or_eq with hwpos | hwzero
  swap
  · rw [← hwzero, mul_zero]; exact measureReal_nonneg
  have hRne : R.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < R.card := by
      rw [hRcard]; exact_mod_cast Nat.totient_pos.2 hq
    exact_mod_cast this
  by_cases hδ : 1 / 2 ≤ δ
  · obtain ⟨a, ha⟩ := hRne
    have h1 : volume.real (B a) = 1 := by
      rw [hBdef]
      simp only
      rw [alt_ml_volumeReal_ball_eq _ _ hδ0, min_eq_left (by linarith)]
    have h2 : volume.real (B a) ≤ volume.real (Aq ψ q) := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro x hx
      apply hsub
      simp only [Set.mem_iUnion]
      exact ⟨a, ha, hx⟩
    calc 4 / (2 + 4 * Cs) * weight ψ q ≤ 2 * (1 / 2) :=
          mul_le_mul hc2 hw (le_of_lt hwpos) (by norm_num)
      _ = volume.real (B a) := by rw [h1]; norm_num
      _ ≤ volume.real (Aq ψ q) := h2
  push Not at hδ
  have hvolB : ∀ a, volume.real (B a) = 2 * δ := by
    intro a
    rw [hBdef]
    simp only
    rw [alt_ml_volumeReal_ball_eq _ _ hδ0, min_eq_right (by linarith)]
  have hfirst : ∑ a ∈ R, volume.real (B a) = 2 * weight ψ q := by
    simp only [hvolB, Finset.sum_const, nsmul_eq_mul, hRcard, hwdef]
    ring
  set P : Finset (ℕ × ℕ) := (R ×ˢ R).filter (fun ab : ℕ × ℕ => ab.1 ≠ ab.2 ∧
      ∃ k : ℤ, |(ab.1 : ℝ) / q - (ab.2 : ℝ) / q - k| < 2 * δ) with hPdef
  have hpoint : ∀ a ∈ R, ∀ b ∈ R, volume.real (B a ∩ B b) ≤
      (if a = b then 2 * δ else 0) +
        (if (a ≠ b ∧ ∃ k : ℤ, |(a : ℝ) / q - (b : ℝ) / q - k| < 2 * δ) then 2 * δ else 0) := by
    intro a _ b _
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, Set.inter_self, hvolB]
      have : 0 ≤ (if (a ≠ a ∧ ∃ k : ℤ, |(a : ℝ) / q - (a : ℝ) / q - k| < 2 * δ)
          then 2 * δ else 0) := by split_ifs <;> linarith
      linarith
    · rw [if_neg hab, zero_add]
      by_cases hne : (B a ∩ B b).Nonempty
      · have hnear : ∃ k : ℤ, |(a : ℝ) / q - (b : ℝ) / q - k| < 2 * δ := by
          obtain ⟨x, hxa, hxb⟩ := hne
          rw [hBdef, Metric.mem_ball, dist_eq_norm] at hxa hxb
          set t : ℝ := (a : ℝ) / q - (b : ℝ) / q with ht
          refine ⟨round t, ?_⟩
          have he : ((t : ℝ) : UnitAddCircle) =
              (x - ((((b : ℝ) / q : ℝ)) : UnitAddCircle)) -
                (x - ((((a : ℝ) / q : ℝ)) : UnitAddCircle)) := by
            rw [ht, AddCircle.coe_sub]
            abel
          have hn : ‖((t : ℝ) : UnitAddCircle)‖ < 2 * δ := by
            rw [he]
            calc _ ≤ ‖x - ((((b : ℝ) / q : ℝ)) : UnitAddCircle)‖ +
                  ‖x - ((((a : ℝ) / q : ℝ)) : UnitAddCircle)‖ := norm_sub_le _ _
              _ < δ + δ := add_lt_add hxb hxa
              _ = 2 * δ := by ring
          rw [UnitAddCircle.norm_eq] at hn
          exact hn
        rw [if_pos ⟨hab, hnear⟩]
        refine (measureReal_mono Set.inter_subset_left (measure_ne_top _ _)).trans ?_
        rw [hvolB]
      · rw [Set.not_nonempty_iff_eq_empty] at hne
        rw [hne, measureReal_empty]
        split_ifs <;> linarith
  have hsecond_raw : ∑ a ∈ R, ∑ b ∈ R, volume.real (B a ∩ B b) ≤
      2 * weight ψ q + 2 * δ * (P.card : ℝ) := by
    calc ∑ a ∈ R, ∑ b ∈ R, volume.real (B a ∩ B b)
        ≤ ∑ a ∈ R, ∑ b ∈ R, ((if a = b then 2 * δ else 0) +
          (if (a ≠ b ∧ ∃ k : ℤ, |(a : ℝ) / q - (b : ℝ) / q - k| < 2 * δ) then 2 * δ
            else 0)) :=
          Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hpoint a ha b hb
      _ = ∑ a ∈ R, 2 * δ + ∑ ab ∈ R ×ˢ R,
          (if (ab.1 ≠ ab.2 ∧ ∃ k : ℤ, |(ab.1 : ℝ) / q - (ab.2 : ℝ) / q - k| < 2 * δ)
            then 2 * δ else 0) := by
          rw [Finset.sum_product]
          simp only [Finset.sum_add_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_ite_eq R a (fun _ => 2 * δ), if_pos ha]
      _ = 2 * weight ψ q + 2 * δ * (P.card : ℝ) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
            Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hRcard, hwdef, hPdef]
          ring
  set K : ℕ := ⌊2 * ψ q⌋₊ with hKdef
  set wt : ℕ → ℝ := fun n => (Nat.gcd n q : ℝ) / Nat.totient (Nat.gcd n q) with hwt
  have hPsub : P ⊆ (Icc 1 K).biUnion
      (fun n => alt_ml_fiber q (n : ℤ) ∪ alt_ml_fiber q (-(n : ℤ))) := by
    intro ab hab
    rw [hPdef, Finset.mem_filter, Finset.mem_product] at hab
    obtain ⟨⟨ha, hb⟩, hne, k, hk⟩ := hab
    obtain ⟨haq, hacop⟩ := Finset.mem_filter.1 ha
    obtain ⟨hbq, hbcop⟩ := Finset.mem_filter.1 hb
    have haq' := Finset.mem_range.1 haq
    have hbq' := Finset.mem_range.1 hbq
    set h : ℤ := (ab.1 : ℤ) - ab.2 - k * q with hhdef
    have hhR : (h : ℝ) = q * ((ab.1 : ℝ) / q - (ab.2 : ℝ) / q - k) := by
      rw [hhdef]; push_cast; field_simp
    have habs : |(h : ℝ)| < 2 * ψ q := by
      rw [hhR, abs_mul, abs_of_pos hqR]
      calc (q : ℝ) * |(ab.1 : ℝ) / q - (ab.2 : ℝ) / q - k| < q * (2 * δ) :=
            mul_lt_mul_of_pos_left hk hqR
        _ = 2 * ψ q := by rw [hδdef]; field_simp
    have hK : h.natAbs ≤ K := by
      apply Nat.le_floor
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact habs.le
    have hh0 : h ≠ 0 := by
      intro h0
      apply hne
      have e : (ab.1 : ℤ) - ab.2 = k * q := by rw [hhdef] at h0; linarith
      have hq' : (0 : ℤ) < q := by exact_mod_cast hq
      have ha1 : (ab.1 : ℤ) < q := by exact_mod_cast haq'
      have hb1 : (ab.2 : ℤ) < q := by exact_mod_cast hbq'
      have ha0 : (0 : ℤ) ≤ ab.1 := by positivity
      have hb0 : (0 : ℤ) ≤ ab.2 := by positivity
      have hk0 : k = 0 := by
        rcases lt_trichotomy k 0 with hk | hk | hk
        · have : k * q ≤ -q := by nlinarith
          omega
        · exact hk
        · have : q ≤ k * q := by nlinarith
          omega
      rw [hk0, zero_mul] at e
      omega
    have hmem : ab ∈ alt_ml_fiber q h := by
      simp only [alt_ml_fiber, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      refine ⟨⟨haq', hbq'⟩, hacop, hbcop, ?_⟩
      rw [Nat.gcd_self, Nat.div_self hq, Nat.lcm_self, Int.modEq_iff_dvd]
      exact ⟨-k, by rw [hhdef]; push_cast; ring⟩
    rw [Finset.mem_biUnion]
    refine ⟨h.natAbs, Finset.mem_Icc.2 ⟨by omega, hK⟩, ?_⟩
    rcases lt_or_gt_of_ne hh0 with hneg | hpos
    · apply Finset.mem_union_right
      have : h = -((h.natAbs : ℕ) : ℤ) := by omega
      rw [← this]; exact hmem
    · apply Finset.mem_union_left
      have : h = ((h.natAbs : ℕ) : ℤ) := by omega
      rw [← this]; exact hmem
  set A0 : ℝ := (q : ℝ) * ((Nat.totient q : ℝ) / q) ^ 2 with hA0
  have hPcard : (P.card : ℝ) ≤ 2 * A0 * ∑ n ∈ Icc 1 K, wt n := by
    have h1 : P.card ≤ ∑ n ∈ Icc 1 K,
        ((alt_ml_fiber q (n : ℤ)).card + (alt_ml_fiber q (-(n : ℤ))).card) := by
      refine (Finset.card_le_card hPsub).trans ?_
      refine Finset.card_biUnion_le.trans ?_
      gcongr with n hn
      exact Finset.card_union_le _ _
    have h2 : (P.card : ℝ) ≤ ∑ n ∈ Icc 1 K,
        (((alt_ml_fiber q (n : ℤ)).card : ℝ) + ((alt_ml_fiber q (-(n : ℤ))).card : ℝ)) := by
      exact_mod_cast h1
    refine h2.trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    have e1 := alt_ml_card_fiber_le q hq n (n : ℤ) (Or.inl rfl)
    have e2 := alt_ml_card_fiber_le q hq n (-(n : ℤ)) (Or.inr rfl)
    rw [← hA0] at e1 e2
    have : 2 * A0 * wt n = A0 * wt n + A0 * wt n := by ring
    rw [this]
    exact add_le_add e1 e2
  have hsum : ∑ n ∈ Icc 1 K, wt n ≤ Cs * (2 * ψ q) := by
    have h1 := alt_ml_sum_gcd_ratio_le q K hq
    have hK : (K : ℝ) ≤ 2 * ψ q := by
      rw [hKdef]; exact Nat.floor_le (by have := hψ q; positivity)
    calc ∑ n ∈ Icc 1 K, wt n ≤ 4 * K := h1
      _ ≤ Cs * (2 * ψ q) := by rw [hCsdef]; linarith
  have hsecond : ∑ a ∈ R, ∑ b ∈ R, volume.real (B a ∩ B b) ≤
      (2 + 4 * Cs) * weight ψ q := by
    have hwsq : 8 * Cs * weight ψ q ^ 2 ≤ 4 * Cs * weight ψ q := by
      have : weight ψ q ^ 2 ≤ weight ψ q * (1 / 2) := by
        rw [sq]; exact mul_le_mul_of_nonneg_left hw hw0
      nlinarith
    have hA0nn : 0 ≤ A0 := by positivity
    have hoff : 2 * δ * (P.card : ℝ) ≤ 8 * Cs * weight ψ q ^ 2 := by
      calc 2 * δ * (P.card : ℝ) ≤ 2 * δ * (2 * A0 * (Cs * (2 * ψ q))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact hPcard.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
        _ = 8 * Cs * weight ψ q ^ 2 := by
            rw [hA0, weight, hδdef]
            field_simp
            ring
    linarith
  have hCS := alt_ml_indicatorCount_secondMoment_bound (mu := volume) R B hBmeas
  rw [hfirst] at hCS
  have hU : volume.real (⋃ a ∈ R, B a) ≤ volume.real (Aq ψ q) :=
    measureReal_mono hsub (measure_ne_top _ _)
  have h3 : (2 * weight ψ q) ^ 2 ≤ ((2 + 4 * Cs) * weight ψ q) * volume.real (Aq ψ q) :=
    hCS.trans (mul_le_mul hsecond hU measureReal_nonneg (by positivity))
  have h4 : 4 * weight ψ q ≤ (2 + 4 * Cs) * volume.real (Aq ψ q) := by
    have : weight ψ q * (4 * weight ψ q) ≤ weight ψ q * ((2 + 4 * Cs) * volume.real (Aq ψ q)) := by
      nlinarith
    exact le_of_mul_le_mul_left this hwpos
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  linarith
end DuffinSchaeffer
end Port24_Parts_MeasureLower

section Port24_Parts_Overlap
open MeasureTheory Finset
namespace DuffinSchaeffer
theorem ovl_ball_inter_le (x y : UnitAddCircle) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε) :
    volume.real (Metric.ball x δ ∩ Metric.ball y ε) ≤ 2 * min δ ε := by
  have key : ∀ (z : UnitAddCircle) (η : ℝ), 0 ≤ η → volume.real (Metric.ball z η) ≤ 2 * η := by
    intro z η hη
    calc volume.real (Metric.ball z η) ≤ volume.real (Metric.closedBall z η) :=
          measureReal_mono Metric.ball_subset_closedBall
      _ = min 1 (2 * η) := by
          rw [measureReal_def, AddCircle.volume_closedBall,
            ENNReal.toReal_ofReal (le_min zero_le_one (by linarith))]
      _ ≤ 2 * η := min_le_right _ _
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
  exact le_min ((measureReal_mono Set.inter_subset_left).trans (key x δ hδ))
    ((measureReal_mono Set.inter_subset_right).trans (key y ε hε))
theorem ovl_cover (ψ : ℕ → ℝ) (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    Aq ψ q ∩ Aq ψ r ⊆ ⋃ ab ∈ ((range q ×ˢ range r).filter (fun ab : ℕ × ℕ =>
        Nat.Coprime ab.1 q ∧ Nat.Coprime ab.2 r ∧
        dist (((ab.1 : ℝ) / q : ℝ) : UnitAddCircle) (((ab.2 : ℝ) / r : ℝ) : UnitAddCircle) <
          ψ q / q + ψ r / r)),
      Metric.ball (((ab.1 : ℝ) / q : ℝ) : UnitAddCircle) (ψ q / q) ∩
        Metric.ball (((ab.2 : ℝ) / r : ℝ) : UnitAddCircle) (ψ r / r) := by
  rintro x ⟨hx1, hx2⟩
  obtain ⟨b1, hb1, hxb1⟩ := mem_approx_add_orderOf_iff.1 hx1
  obtain ⟨b2, hb2, hxb2⟩ := mem_approx_add_orderOf_iff.1 hx2
  obtain ⟨a, ha, hag, rfl⟩ := (AddCircle.addOrderOf_eq_pos_iff hq).1 hb1
  obtain ⟨b, hb, hbg, rfl⟩ := (AddCircle.addOrderOf_eq_pos_iff hr).1 hb2
  simp only [mul_one] at hxb1 hxb2
  refine Set.mem_biUnion (x := (a, b)) ?_ ⟨hxb1, hxb2⟩
  refine mem_filter.2 ⟨mem_product.2 ⟨mem_range.2 ha, mem_range.2 hb⟩, hag, hbg, ?_⟩
  rw [Metric.mem_ball] at hxb1 hxb2
  calc dist _ _ ≤ dist (((a : ℝ) / q : ℝ) : UnitAddCircle) x +
        dist x (((b : ℝ) / r : ℝ) : UnitAddCircle) := dist_triangle _ _ _
    _ < _ := add_lt_add (by rw [dist_comm]; exact hxb1) hxb2
theorem ovl_arith (q r a b : ℕ) (hq : 0 < q) (hr : 0 < r) :
    (a : ℝ) / q - b / r =
      (((a : ℤ) * ((r / Nat.gcd q r : ℕ) : ℤ) - (b : ℤ) * ((q / Nat.gcd q r : ℕ) : ℤ) : ℤ) : ℝ) /
        (Nat.lcm q r : ℝ) := by
  have hg : 0 < Nat.gcd q r := Nat.gcd_pos_of_pos_left r hq
  have h1 : ((Nat.gcd q r : ℕ) : ℝ) * ((q / Nat.gcd q r : ℕ) : ℝ) = q := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_left q r)
  have h2 : ((Nat.gcd q r : ℕ) : ℝ) * ((r / Nat.gcd q r : ℕ) : ℝ) = r := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_right q r)
  have h3 : ((Nat.gcd q r : ℕ) : ℝ) * (Nat.lcm q r : ℝ) = q * r := by
    exact_mod_cast Nat.gcd_mul_lcm q r
  have hgR : ((Nat.gcd q r : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hL : (Nat.lcm q r : ℝ) = q * r / (Nat.gcd q r : ℕ) := by
    rw [eq_div_iff hgR, mul_comm]; exact h3
  have hq' : ((q / Nat.gcd q r : ℕ) : ℝ) = q / (Nat.gcd q r : ℕ) := by
    rw [eq_div_iff hgR, mul_comm]; exact h1
  have hr' : ((r / Nat.gcd q r : ℕ) : ℝ) = r / (Nat.gcd q r : ℕ) := by
    rw [eq_div_iff hgR, mul_comm]; exact h2
  rw [Int.cast_sub, Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast,
    Int.cast_natCast, Int.cast_natCast, hq', hr', hL]
  field_simp
theorem ovl_prod_Icc (N : ℕ) (hN : 1 ≤ N) :
    ∏ n ∈ Icc 2 N, (1 - 1 / (n : ℝ) ^ 2) = ((N : ℝ) + 1) / (2 * (N : ℝ)) := by
  induction N, hN using Nat.le_induction with
  | base => rw [Finset.Icc_eq_empty (by norm_num)]; norm_num
  | succ N hN ih =>
    rw [prod_Icc_succ_top (by omega), ih]
    have : (0:ℝ) < N := by exact_mod_cast hN
    push_cast
    have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
theorem ovl_prod_ge_half (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    (1:ℝ) / 2 ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ 2) := by
  set N := max (S.sup id) 1 with hN
  have hsub : S ⊆ Icc 2 N := fun p hp =>
    mem_Icc.2 ⟨hS p hp, le_max_of_le_left (le_sup (f := id) hp)⟩
  have hf0 : ∀ n ∈ Icc 2 N, 0 ≤ 1 - 1 / (n : ℝ) ^ 2 := by
    intro n hn
    have h2 : (2:ℝ) ≤ n := by exact_mod_cast (mem_Icc.1 hn).1
    rw [sub_nonneg, div_le_one (by positivity)]
    nlinarith
  have hf1 : ∀ n ∈ Icc 2 N, 1 - 1 / (n : ℝ) ^ 2 ≤ 1 := by
    intro n _
    exact sub_le_self _ (by positivity)
  have h := ovl_prod_Icc N (le_max_right _ _)
  rw [← prod_sdiff hsub] at h
  have hA : ∏ n ∈ Icc 2 N \ S, (1 - 1 / (n : ℝ) ^ 2) ≤ 1 :=
    prod_le_one (fun n hn => hf0 n (sdiff_subset hn)) (fun n hn => hf1 n (sdiff_subset hn))
  have hB : 0 ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ 2) := prod_nonneg fun p hp => hf0 p (hsub hp)
  have hNpos : (1:ℝ) ≤ N := by exact_mod_cast le_max_right (S.sup id) 1
  have hC : (1:ℝ) / 2 ≤ ((N : ℝ) + 1) / (2 * (N : ℝ)) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  calc (1:ℝ) / 2 ≤ ((N : ℝ) + 1) / (2 * (N : ℝ)) := hC
    _ = (∏ n ∈ Icc 2 N \ S, (1 - 1 / (n : ℝ) ^ 2)) * ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ 2) := h.symm
    _ ≤ 1 * ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hA hB
    _ = _ := one_mul _
theorem ovl_euler (m : ℕ) (hm : 0 < m) (X H : ℝ) (hXH : X ≤ H) :
    (m : ℝ) / Nat.totient m *
        ∏ p ∈ m.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ H), (1 - (1 : ℝ) / p) ≤
      2 * ∏ p ∈ m.primeFactors.filter (fun p : ℕ => X < (p : ℝ)), (1 + 1 / (p : ℝ)) := by
  have htot : (Nat.totient m : ℝ) = m * ∏ p ∈ m.primeFactors, (1 - (1 : ℝ) / p) := by
    have := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors m)
    push_cast at this
    simpa [one_div] using this
  have hpos : ∀ p ∈ m.primeFactors, 0 < 1 - (1 : ℝ) / p := by
    intro p hp
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  set S := m.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ H) with hSdef
  set A := ∏ p ∈ m.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ H), (1 - (1 : ℝ) / p) with hAdef
  set B := ∏ p ∈ S, (1 - (1 : ℝ) / p) with hBdef
  have hAB : ∏ p ∈ m.primeFactors, (1 - (1 : ℝ) / p) = A * B :=
    (prod_filter_mul_prod_filter_not _ _ _).symm
  have hA : 0 < A := prod_pos fun p hp => hpos p (mem_filter.1 hp).1
  have hB : 0 < B := prod_pos fun p hp => hpos p (mem_filter.1 hp).1
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hlhs : (m : ℝ) / Nat.totient m * A = 1 / B := by
    rw [htot, hAB]
    field_simp
  rw [hlhs, div_le_iff₀ hB]
  set T := m.primeFactors.filter (fun p : ℕ => X < (p : ℝ)) with hTdef
  have hST : S ⊆ T := by
    intro p hp
    rw [hSdef, mem_filter] at hp
    rw [hTdef, mem_filter]
    exact ⟨hp.1, lt_of_le_of_lt hXH (not_le.1 hp.2)⟩
  have hone : ∀ p ∈ T, (1:ℝ) ≤ 1 + 1 / (p : ℝ) := fun p _ => le_add_of_nonneg_right (by positivity)
  have hTS : (1:ℝ) ≤ ∏ p ∈ T \ S, (1 + 1 / (p : ℝ)) := by
    calc (1:ℝ) = ∏ _p ∈ T \ S, (1:ℝ) := prod_const_one.symm
      _ ≤ ∏ p ∈ T \ S, (1 + 1 / (p : ℝ)) :=
        prod_le_prod (fun _ _ => zero_le_one) (fun p hp => hone p (sdiff_subset hp))
  have hSnn : 0 ≤ ∏ p ∈ S, (1 + 1 / (p : ℝ)) := prod_nonneg fun p _ => by positivity
  have hQ : ∏ p ∈ S, (1 + 1 / (p : ℝ)) ≤ ∏ p ∈ T, (1 + 1 / (p : ℝ)) := by
    rw [← prod_sdiff hST]
    calc ∏ p ∈ S, (1 + 1 / (p : ℝ)) = 1 * ∏ p ∈ S, (1 + 1 / (p : ℝ)) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hTS hSnn
  have hSB : (∏ p ∈ S, (1 + 1 / (p : ℝ))) * B = ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ 2) := by
    rw [hBdef, ← prod_mul_distrib]
    refine prod_congr rfl fun p _ => ?_
    ring
  have hhalf := ovl_prod_ge_half S (fun p hp =>
    (Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1).two_le)
  calc (1:ℝ) ≤ 2 * ((∏ p ∈ S, (1 + 1 / (p : ℝ))) * B) := by rw [hSB]; linarith
    _ ≤ 2 * ((∏ p ∈ T, (1 + 1 / (p : ℝ))) * B) := by
        have := mul_le_mul_of_nonneg_right hQ hB.le
        linarith
    _ = 2 * (∏ p ∈ T, (1 + 1 / (p : ℝ))) * B := by ring
theorem measure_inter_Aq_le : ∃ C : ℝ, 0 < C ∧ ∀ ψ : ℕ → ℝ, (∀ q, 0 ≤ ψ q) →
    ∀ q r : ℕ, 0 < q → 0 < r → q ≠ r →
      volume.real (Aq ψ q ∩ Aq ψ r) ≤ C * weight ψ q * weight ψ r * Pfac ψ q r := by
  obtain ⟨Cs, hCs, hsieve⟩ := sieve_weighted_coprime
  refine ⟨16 * Cs, by positivity, ?_⟩
  intro ψ hψ q r hq hr hqr
  have hg : 0 < Nat.gcd q r := Nat.gcd_pos_of_pos_left r hq
  have hq' : 0 < q / Nat.gcd q r :=
    Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_left q r)) hg
  have hr' : 0 < r / Nat.gcd q r :=
    Nat.div_pos (Nat.le_of_dvd hr (Nat.gcd_dvd_right q r)) hg
  have hm : 0 < coprimePart q r := Nat.mul_pos hq' hr'
  have hm1 : coprimePart q r ≠ 1 := by
    intro h
    unfold coprimePart at h
    rw [mul_eq_one] at h
    have e1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left q r)
    have e2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right q r)
    rw [h.1, mul_one] at e1
    rw [h.2, mul_one] at e2
    exact hqr (e1.symm.trans e2)
  have hgR : (0:ℝ) < Nat.gcd q r := by exact_mod_cast hg
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hLpos : (0:ℝ) < Nat.lcm q r := by exact_mod_cast Nat.lcm_pos hq hr
  have hLR : (Nat.lcm q r : ℝ) = q * r / Nat.gcd q r := by
    have h3 : ((Nat.gcd q r : ℕ) : ℝ) * (Nat.lcm q r : ℝ) = q * r := by
      exact_mod_cast Nat.gcd_mul_lcm q r
    rw [eq_div_iff hgR.ne', mul_comm]; exact h3
  have hφm : (0:ℝ) < Nat.totient (coprimePart q r) := by exact_mod_cast Nat.totient_pos.2 hm
  have hδq0 : 0 ≤ ψ q / q := div_nonneg (hψ q) hqR.le
  have hδr0 : 0 ≤ ψ r / r := div_nonneg (hψ r) hrR.le
  set δq : ℝ := ψ q / q with hδq
  set δr : ℝ := ψ r / r with hδr
  set H : ℝ := (δq + δr) * (Nat.lcm q r : ℝ) with hH
  set N : ℕ := ⌊H⌋₊ with hN
  set K : ℝ := (Nat.gcd q r : ℝ) * ((Nat.totient q : ℝ) / q) * ((Nat.totient r : ℝ) / r) *
    ((coprimePart q r : ℝ) / Nat.totient (coprimePart q r)) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hH0 : 0 ≤ H := mul_nonneg (add_nonneg hδq0 hδr0) hLpos.le
  set P := (range q ×ˢ range r).filter (fun ab : ℕ × ℕ =>
        Nat.Coprime ab.1 q ∧ Nat.Coprime ab.2 r ∧
        dist (((ab.1 : ℝ) / q : ℝ) : UnitAddCircle) (((ab.2 : ℝ) / r : ℝ) : UnitAddCircle) <
          δq + δr) with hP
  have step1 : volume.real (Aq ψ q ∩ Aq ψ r) ≤ (P.card : ℝ) * (2 * min δq δr) := by
    calc volume.real (Aq ψ q ∩ Aq ψ r)
        ≤ volume.real (⋃ ab ∈ P, Metric.ball (((ab.1 : ℝ) / q : ℝ) : UnitAddCircle) δq ∩
            Metric.ball (((ab.2 : ℝ) / r : ℝ) : UnitAddCircle) δr) :=
          measureReal_mono (ovl_cover ψ q r hq hr) (measure_ne_top _ _)
      _ ≤ ∑ ab ∈ P, volume.real (Metric.ball (((ab.1 : ℝ) / q : ℝ) : UnitAddCircle) δq ∩
            Metric.ball (((ab.2 : ℝ) / r : ℝ) : UnitAddCircle) δr) :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _ab ∈ P, 2 * min δq δr := sum_le_sum fun ab _ => ovl_ball_inter_le _ _ hδq0 hδr0
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  set F : ℕ × Bool → Finset (ℕ × ℕ) := fun ns =>
    ((range q) ×ˢ (range r)).filter (fun ab : ℕ × ℕ =>
        Nat.Coprime ab.1 q ∧ Nat.Coprime ab.2 r ∧
        (ab.1 : ℤ) * ((r / Nat.gcd q r : ℕ) : ℤ) - (ab.2 : ℤ) * ((q / Nat.gcd q r : ℕ) : ℤ) ≡
          (if ns.2 then (ns.1 : ℤ) else -(ns.1 : ℤ)) [ZMOD (Nat.lcm q r : ℤ)]) with hF
  have hsub : P ⊆ (range (N + 1) ×ˢ (univ : Finset Bool)).biUnion F := by
    rintro ⟨a, b⟩ hab
    rw [hP, mem_filter] at hab
    obtain ⟨hab0, hc1, hc2, hd⟩ := hab
    simp only at hc1 hc2 hd
    set x : ℤ := (a : ℤ) * ((r / Nat.gcd q r : ℕ) : ℤ) - (b : ℤ) * ((q / Nat.gcd q r : ℕ) : ℤ)
      with hx
    have ht : (a : ℝ) / q - b / r = (x : ℝ) / (Nat.lcm q r : ℝ) := ovl_arith q r a b hq hr
    have hnorm : dist (((a : ℝ) / q : ℝ) : UnitAddCircle) (((b : ℝ) / r : ℝ) : UnitAddCircle) =
        |((a : ℝ) / q - b / r) - round ((a : ℝ) / q - b / r)| := by
      rw [dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]
    set k := round ((a : ℝ) / q - b / r) with hk
    set z : ℤ := x - k * (Nat.lcm q r : ℤ) with hz
    have hzR : (z : ℝ) = ((a : ℝ) / q - b / r - k) * Nat.lcm q r := by
      rw [hz]
      push_cast
      rw [ht]
      field_simp
    have habs : |(z : ℝ)| < H := by
      rw [hzR, abs_mul, abs_of_pos hLpos]
      rw [hnorm] at hd
      exact mul_lt_mul_of_pos_right hd hLpos
    have hnN : z.natAbs ≤ N := by
      apply Nat.le_floor
      have : ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [this]
      exact habs.le
    have hmod : x ≡ z [ZMOD (Nat.lcm q r : ℤ)] :=
      Int.modEq_iff_dvd.2 ⟨-k, by rw [hz]; ring⟩
    rw [mem_biUnion]
    by_cases h0 : 0 ≤ z
    · refine ⟨(z.natAbs, true), mem_product.2 ⟨mem_range.2 (by omega), mem_univ _⟩, ?_⟩
      rw [hF, mem_filter]
      refine ⟨hab0, hc1, hc2, ?_⟩
      have : ((z.natAbs : ℕ) : ℤ) = z := Int.natAbs_of_nonneg h0
      simp only [ite_true, this]
      exact hmod
    · refine ⟨(z.natAbs, false), mem_product.2 ⟨mem_range.2 (by omega), mem_univ _⟩, ?_⟩
      rw [hF, mem_filter]
      refine ⟨hab0, hc1, hc2, ?_⟩
      have : -((z.natAbs : ℕ) : ℤ) = z := by
        rw [Int.natCast_natAbs, abs_of_neg (not_le.1 h0), neg_neg]
      simp only [Bool.false_eq_true, ite_false, this]
      exact hmod
  set Bf : ℕ → ℝ := fun n => (if Nat.gcd n (coprimePart q r) = 1 then 1 else 0) *
      (K * ((Nat.gcd n (Nat.gcd q r) : ℝ) / Nat.totient (Nat.gcd n (Nat.gcd q r)))) with hBf
  have hBn : ∀ (n : ℕ) (s : Bool), ((F (n, s)).card : ℝ) ≤ Bf n := by
    intro n s
    have := card_unit_pairs_le q r hq hr (if s then (n : ℤ) else -(n : ℤ))
    have e1 : Int.gcd (if s then (n : ℤ) else -(n : ℤ)) ((coprimePart q r : ℕ) : ℤ) =
        Nat.gcd n (coprimePart q r) := by cases s <;> simp
    have e2 : Int.gcd (if s then (n : ℤ) else -(n : ℤ)) ((Nat.gcd q r : ℕ) : ℤ) =
        Nat.gcd n (Nat.gcd q r) := by cases s <;> simp
    rw [e1, e2] at this
    exact this
  have step2 : (P.card : ℝ) ≤ ∑ n ∈ range (N + 1), 2 * Bf n := by
    calc (P.card : ℝ) ≤ (((range (N + 1) ×ˢ (univ : Finset Bool)).biUnion F).card : ℝ) := by
          exact_mod_cast card_le_card hsub
      _ ≤ ∑ ns ∈ range (N + 1) ×ˢ (univ : Finset Bool), ((F ns).card : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ = ∑ n ∈ range (N + 1), ∑ s ∈ (univ : Finset Bool), ((F (n, s)).card : ℝ) :=
          sum_product _ _ _
      _ ≤ ∑ n ∈ range (N + 1), ∑ _s ∈ (univ : Finset Bool), Bf n :=
          sum_le_sum fun n _ => sum_le_sum fun s _ => hBn n s
      _ = ∑ n ∈ range (N + 1), 2 * Bf n := by
          refine sum_congr rfl fun n _ => ?_
          rw [sum_const, card_univ, Fintype.card_bool, nsmul_eq_mul]
          norm_num
  set S := ∑ h ∈ (Icc 1 ⌊H⌋₊).filter (fun h => Nat.Coprime h (coprimePart q r)),
    ((Nat.gcd h (Nat.gcd q r) : ℝ) / Nat.totient (Nat.gcd h (Nat.gcd q r))) with hS
  have step3 : ∑ n ∈ range (N + 1), 2 * Bf n = 2 * K * S := by
    have hfilt : (range (N + 1)).filter (fun n => Nat.Coprime n (coprimePart q r)) =
        (Icc 1 ⌊H⌋₊).filter (fun n => Nat.Coprime n (coprimePart q r)) := by
      ext n
      simp only [mem_filter, mem_range, mem_Icc]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨?_, by omega⟩, h2⟩
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · exact absurd (Nat.coprime_zero_left _ |>.1 h2) hm1
        · exact hpos
      · rintro ⟨⟨_, h1'⟩, h2⟩
        exact ⟨by omega, h2⟩
    rw [hS, ← hfilt, sum_filter, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    simp only [hBf, Nat.Coprime]
    split_ifs <;> ring
  have hPi0 : 0 ≤ ∏ p ∈ (coprimePart q r).primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ H),
      (1 - (1 : ℝ) / p) := prod_nonneg fun p hp => by
    have : (1:ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors (mem_filter.1 hp).1).one_lt.le
    rw [sub_nonneg, div_le_one (by linarith)]
    exact this
  have step4 : S ≤ Cs * H * ∏ p ∈ (coprimePart q r).primeFactors.filter
      (fun p : ℕ => (p : ℝ) ≤ H), (1 - (1 : ℝ) / p) := by
    by_cases h1 : 1 ≤ H
    · exact hsieve _ _ H hm hg h1
    · have hN0 : ⌊H⌋₊ = 0 := Nat.floor_eq_zero.2 (not_le.1 h1)
      rw [hS, hN0, Finset.Icc_eq_empty (by norm_num), filter_empty, sum_empty]
      exact mul_nonneg (mul_nonneg hCs.le hH0) hPi0
  have hmin : min δq δr * H ≤ 2 * δq * δr * Nat.lcm q r := by
    have : min δq δr * (δq + δr) ≤ 2 * δq * δr := by
      rcases le_total δq δr with h | h
      · rw [min_eq_left h]; nlinarith
      · rw [min_eq_right h]; nlinarith
    rw [hH, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right this hLpos.le
  have hid : K * δq * δr * Nat.lcm q r =
      weight ψ q * weight ψ r * ((coprimePart q r : ℝ) / Nat.totient (coprimePart q r)) := by
    rw [hK, hδq, hδr, hLR]
    unfold weight
    field_simp
  have hX : Mqr ψ q r / Nat.gcd q r ≤ H := by
    have hH' : H = (r * ψ q + q * ψ r) / Nat.gcd q r := by
      rw [hH, hδq, hδr, hLR]
      field_simp
    rw [hH']
    apply div_le_div_of_nonneg_right _ hgR.le
    unfold Mqr
    exact max_le (le_add_of_nonneg_right (mul_nonneg hqR.le (hψ r)))
      (le_add_of_nonneg_left (mul_nonneg hrR.le (hψ q)))
  have hE := ovl_euler (coprimePart q r) hm (Mqr ψ q r / Nat.gcd q r) H hX
  have hW0 : 0 ≤ weight ψ q * weight ψ r := by
    unfold weight
    have := hψ q
    have := hψ r
    positivity
  have hmin0 : 0 ≤ min δq δr := le_min hδq0 hδr0
  set Pi1 := ∏ p ∈ (coprimePart q r).primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ H),
      (1 - (1 : ℝ) / p) with hPi1
  calc volume.real (Aq ψ q ∩ Aq ψ r) ≤ (P.card : ℝ) * (2 * min δq δr) := step1
    _ ≤ (2 * K * S) * (2 * min δq δr) := by
        rw [← step3]; exact mul_le_mul_of_nonneg_right step2 (by positivity)
    _ ≤ (2 * K * (Cs * H * Pi1)) * (2 * min δq δr) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left step4 (by positivity)
    _ = 4 * Cs * K * Pi1 * (min δq δr * H) := by ring
    _ ≤ 4 * Cs * K * Pi1 * (2 * δq * δr * Nat.lcm q r) :=
        mul_le_mul_of_nonneg_left hmin (by positivity)
    _ = 8 * Cs * Pi1 * (K * δq * δr * Nat.lcm q r) := by ring
    _ = 8 * Cs * (weight ψ q * weight ψ r) *
          ((coprimePart q r : ℝ) / Nat.totient (coprimePart q r) * Pi1) := by rw [hid]; ring
    _ ≤ 8 * Cs * (weight ψ q * weight ψ r) * (2 * Pfac ψ q r) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ = 16 * Cs * weight ψ q * weight ψ r * Pfac ψ q r := by ring
end DuffinSchaeffer
end Port24_Parts_Overlap

section Port24_Parts_PairSum
open Finset
namespace DuffinSchaeffer
noncomputable def alt_tt (j : ℕ) : ℝ := Real.exp (Real.exp j)
theorem alt_tt_ge_two (j : ℕ) : 2 ≤ alt_tt j := by
  unfold alt_tt
  have h1 : (1 : ℝ) ≤ Real.exp j := Real.one_le_exp (Nat.cast_nonneg j)
  have h2 : Real.exp 1 ≤ Real.exp (Real.exp j) := Real.exp_le_exp.2 h1
  have h3 := Real.exp_one_gt_d9
  linarith
theorem alt_log_tt (j : ℕ) : Real.log (alt_tt j) = Real.exp j := by
  unfold alt_tt; exact Real.log_exp _
theorem alt_sum_split (S : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] (T : ℝ) :
    ∑ p ∈ S.filter P, (1 : ℝ) / p ≤
      ∑ p ∈ (S.filter P).filter (fun p : ℕ => (p : ℝ) < T), (1 : ℝ) / p +
        ∑ p ∈ S.filter (fun p : ℕ => T ≤ (p : ℝ)), (1 : ℝ) / p := by
  rw [← Finset.sum_filter_add_sum_filter_not (S.filter P) (fun p : ℕ => (p : ℝ) < T)]
  refine add_le_add le_rfl ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter, not_lt] at hp ⊢
    exact ⟨hp.1.1, hp.2⟩
  · intro p _ _
    positivity
theorem alt_sum_mid_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (s T : ℝ) (hs : 2 ≤ s)
    (hsT : s ≤ T) :
    ∑ p ∈ (S.filter (fun p : ℕ => s < (p : ℝ))).filter (fun p : ℕ => (p : ℝ) < T),
        (1 : ℝ) / p ≤ Real.log (Real.log T / Real.log s) + 100 / Real.log s := by
  refine le_trans ?_ (sum_inv_prime_Ioc_le s T hs hsT)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨⟨hpS, hsp⟩, hpT⟩ := hp
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨(Nat.floor_lt (by linarith)).2 hsp, Nat.le_floor hpT.le⟩, hS p hpS⟩
  · intro p _ _
    positivity
theorem alt_sum_low_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (T : ℝ) (hT : 2 ≤ T) :
    ∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) < T), (1 : ℝ) / p ≤
      1 / 2 + (Real.log (Real.log T / Real.log 2) + 100 / Real.log 2) := by
  have hmert := sum_inv_prime_Ioc_le 2 T le_rfl hT
  have hfl : ⌊(2 : ℝ)⌋₊ = 2 := by norm_num
  rw [hfl] at hmert
  have hsub : S.filter (fun p : ℕ => (p : ℝ) < T) ⊆
      {2} ∪ (Ioc 2 ⌊T⌋₊).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpS, hpT⟩ := Finset.mem_filter.1 hp
    have hp2 := (hS p hpS).two_le
    rcases Nat.eq_or_lt_of_le hp2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_singleton.2 h.symm)
    · refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨h, ?_⟩, hS p hpS⟩)
      exact Nat.le_floor hpT.le
  have hdisj : Disjoint ({2} : Finset ℕ) ((Ioc 2 ⌊T⌋₊).filter Nat.Prime) := by
    rw [Finset.disjoint_singleton_left]
    simp
  calc ∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) < T), (1 : ℝ) / p
      ≤ ∑ p ∈ {2} ∪ (Ioc 2 ⌊T⌋₊).filter Nat.Prime, (1 : ℝ) / p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ = 1 / 2 + ∑ p ∈ (Ioc 2 ⌊T⌋₊).filter Nat.Prime, (1 : ℝ) / p := by
        rw [Finset.sum_union hdisj, Finset.sum_singleton]
        norm_num
    _ ≤ 1 / 2 + (Real.log (Real.log T / Real.log 2) + 100 / Real.log 2) := by
        gcongr
theorem alt_Pfac_le (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (q r J : ℕ) (hq : 0 < q) (hr : 0 < r)
    (hJ : q * r ≤ J) :
    Pfac ψ q r ≤ Real.exp 200 + ∑ j ∈ range J,
      (if (Mqr ψ q r ≤ alt_tt j * Nat.gcd q r ∧ 10 ≤ Lsum (alt_tt j) q r)
        then Real.exp 158 * Real.exp j else 0) := by
  classical
  set g := Nat.gcd q r with hgdef
  have hg : 0 < g := Nat.gcd_pos_of_pos_left r hq
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  set m := coprimePart q r with hmdef
  set S := m.primeFactors with hSdef
  have hSprime : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hm0 : 0 < m := by
    rw [hmdef, coprimePart]
    apply Nat.mul_pos
    · exact Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_left q r)) hg
    · exact Nat.div_pos (Nat.le_of_dvd hr (Nat.gcd_dvd_right q r)) hg
  have hmJ : m ≤ J := by
    refine le_trans ?_ hJ
    rw [hmdef, coprimePart]
    exact Nat.mul_le_mul (Nat.div_le_self _ _) (Nat.div_le_self _ _)
  set s : ℝ := Mqr ψ q r / g with hsdef
  have hs0 : 0 ≤ s := by
    rw [hsdef, Mqr]
    have := hψ q
    exact div_nonneg (le_trans (by positivity) (le_max_left _ _)) hgR.le
  set σ : ℝ := ∑ p ∈ S.filter (fun p : ℕ => s < (p : ℝ)), (1 : ℝ) / p with hσdef
  have hsumnn : 0 ≤ ∑ j ∈ range J,
      (if (Mqr ψ q r ≤ alt_tt j * Nat.gcd q r ∧ 10 ≤ Lsum (alt_tt j) q r)
        then Real.exp 158 * Real.exp j else 0) := by
    apply Finset.sum_nonneg
    intro j _
    split_ifs <;> positivity
  have hP : Pfac ψ q r ≤ Real.exp σ := by
    have h := Real.prod_one_add_le_exp_sum (S.filter (fun p : ℕ => s < (p : ℝ)))
      (f := fun p : ℕ => 1 / (p : ℝ)) (fun p => by positivity)
    exact h
  by_cases hσ : σ < 200
  · have : Real.exp σ ≤ Real.exp 200 := Real.exp_le_exp.2 hσ.le
    linarith
  push Not at hσ
  set good : ℕ → Prop := fun j => 10 ≤ Lsum (alt_tt j) q r with hgood
  have hLsum_def : ∀ t : ℝ, Lsum t q r = ∑ p ∈ S.filter (fun p : ℕ => t ≤ (p : ℝ)), (1 : ℝ) / p :=
    fun t => rfl
  have hgood0 : good 0 := by
    show 10 ≤ Lsum (alt_tt 0) q r
    have hsplit := alt_sum_split S (fun p : ℕ => s < (p : ℝ)) (alt_tt 0)
    have hlow : ∑ p ∈ (S.filter (fun p : ℕ => s < (p : ℝ))).filter
        (fun p : ℕ => (p : ℝ) < alt_tt 0), (1 : ℝ) / p ≤ 1 / 2 := by
      have hsub : (S.filter (fun p : ℕ => s < (p : ℝ))).filter
          (fun p : ℕ => (p : ℝ) < alt_tt 0) ⊆ {2} := by
        intro p hp
        simp only [Finset.mem_filter] at hp
        obtain ⟨⟨hpS, _⟩, hpt⟩ := hp
        have h2 := (hSprime p hpS).two_le
        have ht0 : alt_tt 0 < 3 := by
          unfold alt_tt
          simp only [Nat.cast_zero, Real.exp_zero]
          have := Real.exp_one_lt_d9
          linarith
        have hp3 : (p : ℝ) < 3 := lt_trans hpt ht0
        have : p < 3 := by exact_mod_cast hp3
        exact Finset.mem_singleton.2 (by omega)
      calc _ ≤ ∑ p ∈ ({2} : Finset ℕ), (1 : ℝ) / p :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
        _ = 1 / 2 := by simp
    rw [hLsum_def]
    linarith
  have hgoodJ : ¬ good J := by
    show ¬ 10 ≤ Lsum (alt_tt J) q r
    rw [hLsum_def]
    have hempty : S.filter (fun p : ℕ => alt_tt J ≤ (p : ℝ)) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      intro p hp hle
      have hpm : p ≤ m := Nat.le_of_dvd hm0 (Nat.dvd_of_mem_primeFactors hp)
      have h1 : (J : ℝ) + 1 ≤ Real.exp J := by
        have := Real.add_one_le_exp (J : ℝ); linarith
      have h2 : Real.exp J + 1 ≤ Real.exp (Real.exp J) := by
        have := Real.add_one_le_exp (Real.exp J); linarith
      have h3 : (p : ℝ) ≤ J := by exact_mod_cast hpm.trans hmJ
      unfold alt_tt at hle
      linarith
    rw [hempty, Finset.sum_empty]
    norm_num
  set j := Nat.findGreatest good J with hjdef
  have hjgood : good j := Nat.findGreatest_spec (Nat.zero_le J) hgood0
  have hjJ : j < J := by
    rcases Nat.lt_or_ge j J with h | h
    · exact h
    · have : j = J := le_antisymm (Nat.findGreatest_le J) h
      rw [this] at hjgood
      exact absurd hjgood hgoodJ
  have hjnext : ¬ good (j + 1) :=
    Nat.findGreatest_is_greatest (Nat.lt_succ_self j) hjJ
  have hLnext : Lsum (alt_tt (j + 1)) q r < 10 := lt_of_not_ge hjnext
  have hsplitj := alt_sum_split S (fun p : ℕ => s < (p : ℝ)) (alt_tt (j + 1))
  rw [← hσdef, ← hLsum_def] at hsplitj
  have hlogt : ∀ i : ℕ, Real.log (alt_tt i) = Real.exp i := alt_log_tt
  have hexpj : Real.exp ((j : ℝ) + 1) = Real.exp 1 * Real.exp j := by
    rw [Real.exp_add, mul_comm]
  have hsj : s ≤ alt_tt j := by
    by_contra hcon
    push Not at hcon
    have hs2 : 2 ≤ s := le_trans (alt_tt_ge_two j) hcon.le
    have hmid : ∑ p ∈ (S.filter (fun p : ℕ => s < (p : ℝ))).filter
        (fun p : ℕ => (p : ℝ) < alt_tt (j + 1)), (1 : ℝ) / p ≤ 101 := by
      by_cases hsT : s ≤ alt_tt (j + 1)
      · refine (alt_sum_mid_le S hSprime s (alt_tt (j + 1)) hs2 hsT).trans ?_
        have hlogs : Real.exp j < Real.log s := by
          rw [← hlogt j]
          exact Real.log_lt_log (by linarith [alt_tt_ge_two j]) hcon
        have hej : (1 : ℝ) ≤ Real.exp j := Real.one_le_exp (Nat.cast_nonneg j)
        have h1 : Real.log (Real.log (alt_tt (j + 1)) / Real.log s) ≤ 1 := by
          rw [hlogt, Nat.cast_succ, hexpj]
          have hpos : 0 < Real.exp 1 * Real.exp j / Real.log s := div_pos (by positivity) (by linarith)
          have hle : Real.exp 1 * Real.exp j / Real.log s ≤ Real.exp 1 := by
            rw [div_le_iff₀ (by linarith)]
            have := Real.exp_pos 1
            nlinarith
          calc Real.log (Real.exp 1 * Real.exp j / Real.log s) ≤ Real.log (Real.exp 1) :=
                Real.log_le_log hpos hle
            _ = 1 := Real.log_exp 1
        have h2 : 100 / Real.log s ≤ 100 := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith
        linarith
      · push Not at hsT
        have hempty : (S.filter (fun p : ℕ => s < (p : ℝ))).filter
            (fun p : ℕ => (p : ℝ) < alt_tt (j + 1)) = ∅ := by
          apply Finset.filter_eq_empty_iff.2
          intro p hp hpt
          have := (Finset.mem_filter.1 hp).2
          linarith
        rw [hempty, Finset.sum_empty]
        norm_num
    linarith
  have hσj : σ ≤ 158 + j := by
    have hlow := alt_sum_low_le S hSprime (alt_tt (j + 1)) (alt_tt_ge_two (j + 1))
    have hsubset : ∑ p ∈ (S.filter (fun p : ℕ => s < (p : ℝ))).filter
        (fun p : ℕ => (p : ℝ) < alt_tt (j + 1)), (1 : ℝ) / p ≤
        ∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) < alt_tt (j + 1)), (1 : ℝ) / p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        simp only [Finset.mem_filter] at hp ⊢
        exact ⟨hp.1.1, hp.2⟩
      · intro p _ _
        positivity
    have hl2 := Real.log_two_gt_d9
    have hl2' : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have hlog2pos : 0 < Real.log 2 := by linarith
    have hmert : Real.log (Real.log (alt_tt (j + 1)) / Real.log 2) + 100 / Real.log 2 ≤
        j + 1 + 146 := by
      rw [hlogt, Real.log_div (Real.exp_pos _).ne' hlog2pos.ne', Real.log_exp]
      have h1 : -Real.log (Real.log 2) ≤ 1 := by
        have := Real.one_sub_inv_le_log_of_pos hlog2pos
        have hinv : (Real.log 2)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ hlog2pos (by norm_num)]
          linarith
        linarith
      have h2 : 100 / Real.log 2 ≤ 145 := by
        rw [div_le_iff₀ hlog2pos]
        linarith
      push_cast
      linarith
    linarith
  have hmem : j ∈ range J := Finset.mem_range.2 hjJ
  have hcond : Mqr ψ q r ≤ alt_tt j * Nat.gcd q r ∧ 10 ≤ Lsum (alt_tt j) q r := by
    refine ⟨?_, hjgood⟩
    rw [← hgdef]
    have := (div_le_iff₀ hgR).1 hsj
    linarith
  have hterm := Finset.single_le_sum (f := fun j => (if (Mqr ψ q r ≤ alt_tt j * Nat.gcd q r ∧
      10 ≤ Lsum (alt_tt j) q r) then Real.exp 158 * Real.exp j else 0))
    (fun i _ => by split_ifs <;> positivity) hmem
  simp only [hcond, and_self, if_true] at hterm
  have hPj : Pfac ψ q r ≤ Real.exp 158 * Real.exp j := by
    refine hP.trans ?_
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 hσj
  have := Real.exp_pos 200
  linarith
theorem alt_sum_exp_div_le (J : ℕ) :
    ∑ j ∈ range J, Real.exp j / alt_tt j ≤ 2 := by
  refine le_trans ?_ (sum_geometric_two_le J)
  apply Finset.sum_le_sum
  intro j _
  unfold alt_tt
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h1 : 2 * (j : ℝ) ≤ Real.exp j := by
    have := Real.quadratic_le_exp_of_nonneg hj
    nlinarith [sq_nonneg ((j : ℝ) - 1)]
  have h2 : Real.exp j / Real.exp (Real.exp j) ≤ Real.exp (-(j : ℝ)) := by
    rw [div_le_iff₀ (Real.exp_pos _), ← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith
  refine h2.trans ?_
  have h3 : Real.exp (-(j : ℝ)) = (Real.exp (-1)) ^ j := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [h3]
  apply pow_le_pow_left₀ (Real.exp_pos _).le
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  have := Real.exp_one_gt_d9
  norm_num
  linarith
theorem pair_sum_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : ℕ → ℝ), (∀ q, 0 ≤ ψ q) → ∀ X Y : ℕ, 1 ≤ X →
    ∑ q ∈ Icc X Y, weight ψ q ≤ 2 →
      ∑ q ∈ Icc X Y, ∑ r ∈ Icc X Y,
        (if q = r then 0 else weight ψ q * weight ψ r * Pfac ψ q r) ≤ C := by
  classical
  obtain ⟨C54, hC54, h54⟩ := prop54
  refine ⟨4 * Real.exp 200 + Real.exp 158 * C54 * 2, by positivity, ?_⟩
  intro ψ hψ X Y hX hsum
  set I := Icc X Y with hIdef
  set J := Y * Y with hJdef
  have hw : ∀ q, 0 ≤ weight ψ q := fun q => by
    unfold weight; have := hψ q; positivity
  set c : ℕ → ℝ := fun j => Real.exp 158 * Real.exp j with hcdef
  have hc : ∀ j, 0 ≤ c j := fun j => by positivity
  set B : ℕ → ℕ → ℕ → ℝ := fun j q r =>
    if (Mqr ψ q r ≤ alt_tt j * Nat.gcd q r ∧ 10 ≤ Lsum (alt_tt j) q r)
      then weight ψ q * weight ψ r else 0 with hBdef
  have hpt : ∀ q ∈ I, ∀ r ∈ I,
      (if q = r then 0 else weight ψ q * weight ψ r * Pfac ψ q r) ≤
        weight ψ q * weight ψ r * Real.exp 200 + ∑ j ∈ range J, c j * B j q r := by
    intro q hq r hr
    obtain ⟨hXq, hqY⟩ := Finset.mem_Icc.1 hq
    obtain ⟨hXr, hrY⟩ := Finset.mem_Icc.1 hr
    have hww := mul_nonneg (hw q) (hw r)
    have hBnn : ∀ j, 0 ≤ c j * B j q r := fun j => by
      apply mul_nonneg (hc j)
      rw [hBdef]; dsimp only; split_ifs
      · exact hww
      · exact le_rfl
    split_ifs with hqr
    · have := Finset.sum_nonneg (fun j (_ : j ∈ range J) => hBnn j)
      have : 0 ≤ weight ψ q * weight ψ r * Real.exp 200 := by positivity
      linarith
    · have hP := alt_Pfac_le ψ hψ q r J (by omega) (by omega) (Nat.mul_le_mul hqY hrY)
      calc weight ψ q * weight ψ r * Pfac ψ q r
          ≤ weight ψ q * weight ψ r * (Real.exp 200 + ∑ j ∈ range J,
              (if (Mqr ψ q r ≤ alt_tt j * Nat.gcd q r ∧ 10 ≤ Lsum (alt_tt j) q r)
                then Real.exp 158 * Real.exp j else 0)) := mul_le_mul_of_nonneg_left hP hww
        _ = weight ψ q * weight ψ r * Real.exp 200 + ∑ j ∈ range J, c j * B j q r := by
          rw [mul_add, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [hBdef, hcdef]
          dsimp only
          split_ifs <;> ring
  have hEt : ∀ j, ∑ q ∈ I, ∑ r ∈ I, B j q r =
      ∑ e ∈ Et ψ X Y (alt_tt j), weight ψ e.1 * weight ψ e.2 := by
    intro j
    rw [Et, Finset.sum_filter, Finset.sum_product]
  have hsq : (∑ q ∈ I, weight ψ q) ^ 2 ≤ 4 := by
    have h0 : 0 ≤ ∑ q ∈ I, weight ψ q := Finset.sum_nonneg fun q _ => hw q
    nlinarith
  calc ∑ q ∈ I, ∑ r ∈ I, (if q = r then 0 else weight ψ q * weight ψ r * Pfac ψ q r)
      ≤ ∑ q ∈ I, ∑ r ∈ I, (weight ψ q * weight ψ r * Real.exp 200 +
          ∑ j ∈ range J, c j * B j q r) :=
        Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun r hr => hpt q hq r hr
    _ = Real.exp 200 * (∑ q ∈ I, weight ψ q) ^ 2 +
          ∑ j ∈ range J, c j * ∑ q ∈ I, ∑ r ∈ I, B j q r := by
        simp only [Finset.sum_add_distrib]
        congr 1
        · rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro q _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro r _
          ring
        · calc ∑ q ∈ I, ∑ r ∈ I, ∑ j ∈ range J, c j * B j q r
              = ∑ q ∈ I, ∑ j ∈ range J, ∑ r ∈ I, c j * B j q r := by
                apply Finset.sum_congr rfl; intro q _; exact Finset.sum_comm
            _ = ∑ j ∈ range J, ∑ q ∈ I, ∑ r ∈ I, c j * B j q r := Finset.sum_comm
            _ = ∑ j ∈ range J, c j * ∑ q ∈ I, ∑ r ∈ I, B j q r := by
                apply Finset.sum_congr rfl; intro j _
                rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _
                rw [Finset.mul_sum]
    _ ≤ Real.exp 200 * 4 + ∑ j ∈ range J, c j * (C54 / alt_tt j) := by
        gcongr with j hj
        rw [hEt j]
        exact h54 ψ hψ X Y hX hsum (alt_tt j) (by linarith [alt_tt_ge_two j])
    _ = Real.exp 200 * 4 + Real.exp 158 * C54 * ∑ j ∈ range J, Real.exp j / alt_tt j := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        rw [hcdef]; dsimp only
        ring
    _ ≤ Real.exp 200 * 4 + Real.exp 158 * C54 * 2 := by
        gcongr
        exact alt_sum_exp_div_le J
    _ = 4 * Real.exp 200 + Real.exp 158 * C54 * 2 := by ring
end DuffinSchaeffer
end Port24_Parts_PairSum

section Port24_Parts_SecondMoment
open MeasureTheory Filter
namespace DuffinSchaeffer
theorem chungErdos_quadratic {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n)) (F : Finset ℕ)
    (t : ℝ) :
    0 ≤ ∑ n ∈ F, ∑ m ∈ F, μ.real (A n ∩ A m) - 2 * t * ∑ n ∈ F, μ.real (A n)
      + t ^ 2 * μ.real (⋃ n ∈ F, A n) := by
  set U := ⋃ n ∈ F, A n with hUdef
  have hU : MeasurableSet U := Finset.measurableSet_biUnion F (fun n _ => hA n)
  have hint : ∀ s : Set Ω, MeasurableSet s → Integrable (s.indicator (1 : Ω → ℝ)) μ :=
    fun s hs => (integrable_const (1 : ℝ)).indicator hs
  let g : Ω → ℝ := fun x =>
    (∑ n ∈ F, ∑ m ∈ F, (A n ∩ A m).indicator 1 x) - 2 * t * ∑ n ∈ F, (A n).indicator 1 x
      + t ^ 2 * U.indicator 1 x
  have hg : 0 ≤ ∫ x, g x ∂μ := by
    apply integral_nonneg
    intro x
    simp only [g, Pi.zero_apply]
    have hsq : (∑ n ∈ F, ∑ m ∈ F, (A n ∩ A m).indicator (1 : Ω → ℝ) x)
        = (∑ n ∈ F, (A n).indicator (1 : Ω → ℝ) x) ^ 2 := by
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
      by_cases hn : x ∈ A n <;> by_cases hm : x ∈ A m <;> simp [hn, hm]
    rw [hsq]
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx, Pi.one_apply]
      have := sq_nonneg (∑ n ∈ F, (A n).indicator (1 : Ω → ℝ) x - t)
      nlinarith
    · rw [Set.indicator_of_notMem hx]
      have h0 : ∑ n ∈ F, (A n).indicator (1 : Ω → ℝ) x = 0 := by
        refine Finset.sum_eq_zero fun n hn => Set.indicator_of_notMem ?_ _
        intro hxn
        exact hx (Set.mem_biUnion hn hxn)
      rw [h0]
      simp
  have hcalc : ∫ x, g x ∂μ = ∑ n ∈ F, ∑ m ∈ F, μ.real (A n ∩ A m)
      - 2 * t * ∑ n ∈ F, μ.real (A n) + t ^ 2 * μ.real U := by
    simp only [g]
    rw [integral_add, integral_sub, integral_const_mul, integral_const_mul,
      integral_finsetSum, integral_finsetSum, integral_indicator_one hU]
    · congr 2
      · refine Finset.sum_congr rfl fun n _ => ?_
        rw [integral_finsetSum]
        · exact Finset.sum_congr rfl fun m _ => integral_indicator_one ((hA n).inter (hA m))
        · exact fun m _ => hint _ ((hA n).inter (hA m))
      · congr 1
        exact Finset.sum_congr rfl fun n _ => integral_indicator_one (hA n)
    · exact fun n _ => hint _ (hA n)
    · exact fun n _ => integrable_finsetSum _ fun m _ => hint _ ((hA n).inter (hA m))
    · exact integrable_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ =>
        hint _ ((hA n).inter (hA m))
    · exact (integrable_finsetSum _ fun n _ => hint _ (hA n)).const_mul _
    · exact (integrable_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ =>
        hint _ ((hA n).inter (hA m))).sub
        ((integrable_finsetSum _ fun n _ => hint _ (hA n)).const_mul _)
    · exact (hint _ hU).const_mul _
  rw [← hcalc]
  exact hg
theorem one_div_le_measure_biUnion {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n)) (F : Finset ℕ)
    (C : ℝ) (hC : 0 < C) (hS : 0 < ∑ n ∈ F, μ.real (A n))
    (hD : ∑ n ∈ F, ∑ m ∈ F, μ.real (A n ∩ A m) ≤ C * (∑ n ∈ F, μ.real (A n)) ^ 2) :
    1 / C ≤ μ.real (⋃ n ∈ F, A n) := by
  set S := ∑ n ∈ F, μ.real (A n)
  set D := ∑ n ∈ F, ∑ m ∈ F, μ.real (A n ∩ A m)
  set V := μ.real (⋃ n ∈ F, A n)
  have hq : ∀ t : ℝ, 0 ≤ V * (t * t) + (-2 * S) * t + D := by
    intro t
    have := chungErdos_quadratic μ A hA F t
    nlinarith
  have hdisc := discrim_le_zero hq
  rw [discrim] at hdisc
  have hV : 0 ≤ V := measureReal_nonneg
  have h1 : S ^ 2 ≤ C * S ^ 2 * V := by nlinarith
  have h2 : 1 ≤ C * V := by
    have hS2 : 0 < S ^ 2 := by positivity
    nlinarith
  rw [div_le_iff₀ hC]
  linarith
theorem measure_limsup_ge_of_second_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (A : ℕ → Set Ω) (hA : ∀ n, MeasurableSet (A n)) (C : ℝ)
    (h : ∀ N : ℕ, ∃ F : Finset ℕ, (∀ n ∈ F, N ≤ n) ∧ 0 < ∑ n ∈ F, μ.real (A n) ∧
      ∑ n ∈ F, ∑ m ∈ F, μ.real (A n ∩ A m) ≤ C * (∑ n ∈ F, μ.real (A n)) ^ 2) :
    1 / C ≤ μ.real (limsup A atTop) := by
  rcases le_or_gt C 0 with hC | hC
  · exact le_trans (div_nonpos_of_nonneg_of_nonpos zero_le_one hC) measureReal_nonneg
  set V : ℕ → Set Ω := fun N => ⋃ i ≥ N, A i with hVdef
  have hlim : limsup A atTop = ⋂ N, V N := by
    rw [limsup_eq_iInf_iSup_of_nat]
    simp only [Set.iInf_eq_iInter, Set.iSup_eq_iUnion, V]
  have hanti : Antitone V := by
    intro a b hab x hx
    simp only [V, Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hi, hx⟩ := hx
    exact ⟨i, le_trans hab hi, hx⟩
  have hmeas : ∀ N, NullMeasurableSet (V N) μ := fun N =>
    (MeasurableSet.biUnion (Set.to_countable _) fun i _ => hA i).nullMeasurableSet
  have hmu : μ (limsup A atTop) = ⨅ N, μ (V N) := by
    rw [hlim, hanti.measure_iInter hmeas ⟨0, measure_ne_top μ _⟩]
  have hbound : ∀ N, ENNReal.ofReal (1 / C) ≤ μ (V N) := by
    intro N
    obtain ⟨F, hFN, hS, hD⟩ := h N
    have h1 := one_div_le_measure_biUnion μ A hA F C hC hS hD
    have hsub : (⋃ n ∈ F, A n) ⊆ V N := by
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨n, hn, hx⟩ := hx
      simp only [V, Set.mem_iUnion]
      exact ⟨n, hFN n hn, hx⟩
    calc ENNReal.ofReal (1 / C) ≤ ENNReal.ofReal (μ.real (⋃ n ∈ F, A n)) :=
          ENNReal.ofReal_le_ofReal h1
      _ = μ (⋃ n ∈ F, A n) := ENNReal.ofReal_toReal (measure_ne_top μ _)
      _ ≤ μ (V N) := measure_mono hsub
  have hfinal : ENNReal.ofReal (1 / C) ≤ μ (limsup A atTop) := by
    rw [hmu]
    exact le_iInf hbound
  rw [Measure.real]
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).1 hfinal
end DuffinSchaeffer
end Port24_Parts_SecondMoment

section Port24_Parts_Truncation
open MeasureTheory Filter Topology
namespace DuffinSchaeffer
theorem weight_nonneg (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (q : ℕ) : 0 ≤ weight ψ q := by
  unfold weight
  have := hψ q
  positivity
theorem exists_window (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q) (hle : ∀ q, weight ψ q ≤ 1 / 2)
    (h : ¬ Summable (weight ψ)) (N : ℕ) :
    ∃ Y : ℕ, 1 ≤ ∑ q ∈ Finset.Icc N Y, weight ψ q ∧ ∑ q ∈ Finset.Icc N Y, weight ψ q ≤ 2 := by
  have hw := weight_nonneg ψ hψ
  set S : ℕ → ℝ := fun M => ∑ q ∈ Finset.Ico N M, weight ψ q with hS
  have hex : ∃ M, 1 ≤ S M := by
    by_contra hne
    push Not at hne
    apply h
    refine summable_of_sum_range_le (c := ∑ q ∈ Finset.range N, weight ψ q + 1) hw ?_
    intro n
    rcases le_total N n with hNn | hnN
    · rw [← Finset.sum_range_add_sum_Ico _ hNn]
      have := hne n
      simp only [hS] at this
      linarith
    · have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hnN)
        (fun i _ _ => hw i)
      linarith
  classical
  let M := Nat.find hex
  have hM : 1 ≤ S M := Nat.find_spec hex
  have hNM : N < M := by
    by_contra hc
    push Not at hc
    have : S M = 0 := by
      simp only [hS]
      rw [Finset.Ico_eq_empty_of_le hc, Finset.sum_empty]
    linarith
  obtain ⟨Y, hY⟩ : ∃ Y, M = Y + 1 := ⟨M - 1, by omega⟩
  have hprev : ¬ 1 ≤ S Y := Nat.find_min hex (by omega)
  have hIcc : Finset.Icc N Y = Finset.Ico N (Y + 1) := (Finset.Ico_add_one_right_eq_Icc N Y).symm
  refine ⟨Y, ?_, ?_⟩
  · rw [hIcc]; rw [hY] at hM; exact hM
  · rw [hIcc, Finset.sum_Ico_succ_top (by omega)]
    have := hle Y
    simp only [hS] at hprev
    linarith
end DuffinSchaeffer
end Port24_Parts_Truncation

section Port24_Main
open MeasureTheory Filter Topology Finset
namespace DuffinSchaeffer
theorem bounded_divergence (ψ : ℕ → ℝ) (hψ : ∀ q, 0 ≤ ψ q)
    (hb : ∃ C : ℝ, ∀ q : ℕ, ψ q * q ≤ C) (hdiv : ¬ Summable (weight ψ)) :
    ∀ᵐ α : ℝ, Erdos999.IsApproximable ψ α := by
  obtain ⟨B, hB⟩ := hb
  let ψ' := fun q : ℕ => min (ψ q) (1 / 2)
  have hψ' (q : ℕ) : 0 ≤ ψ' q := le_min (hψ q) (by norm_num)
  have hhalf (q : ℕ) : ψ' q ≤ 1 / 2 := min_le_right _ _
  have hw' (q : ℕ) : weight ψ' q ≤ 1 / 2 := by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp [weight]
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hφ : (Nat.totient q : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
    rw [weight, div_le_iff₀ hq']
    calc (Nat.totient q : ℝ) * ψ' q ≤ (q : ℝ) * ψ' q := mul_le_mul_of_nonneg_right hφ (hψ' q)
      _ ≤ (q : ℝ) * (1 / 2) := mul_le_mul_of_nonneg_left (hhalf q) hq'.le
      _ = _ := mul_comm _ _
  have hdiv' : ¬ Summable (weight ψ') := by
    intro hs
    apply hdiv
    apply hs.congr_atTop
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * B),
      eventually_gt_atTop (0 : ℕ)] with q hqB hq
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hsmall : ψ q ≤ 1 / 2 := (le_of_mul_le_mul_right
      ((hB q).trans (show B ≤ 1 / 2 * q by linarith)) hq')
    simp only [weight, ψ', min_eq_left hsmall]
  have hradii : Tendsto (fun q : ℕ => ψ' q / q) atTop (𝓝 0) := by
    refine squeeze_zero (fun q => div_nonneg (hψ' q) (Nat.cast_nonneg q))
      (fun q => div_le_div_of_nonneg_right (hhalf q) (Nat.cast_nonneg q)) ?_
    exact tendsto_natCast_atTop_atTop.const_div_atTop (1 / 2 : ℝ)
  have hwnn : ∀ q, 0 ≤ weight ψ' q := fun q => by
    unfold weight; have := hψ' q; positivity
  obtain ⟨c, hc, hlow⟩ := measure_Aq_ge
  obtain ⟨C₁, hC₁, hov⟩ := measure_inter_Aq_le
  obtain ⟨C₂, hC₂, hps⟩ := pair_sum_bound
  set K : ℝ := (4 + C₁ * C₂) / c ^ 2 with hK
  have hKpos : 0 < K := by
    have : 0 ≤ C₁ * C₂ := mul_nonneg hC₁.le hC₂
    positivity
  have hwin : ∀ N : ℕ, ∃ F : Finset ℕ, (∀ n ∈ F, N ≤ n) ∧
      0 < ∑ n ∈ F, volume.real (Aq ψ' n) ∧
      ∑ n ∈ F, ∑ m ∈ F, volume.real (Aq ψ' n ∩ Aq ψ' m) ≤
        K * (∑ n ∈ F, volume.real (Aq ψ' n)) ^ 2 := by
    intro N
    obtain ⟨Y, h1, h2⟩ := exists_window ψ' hψ' hw' hdiv' (max N 1)
    set F := Icc (max N 1) Y with hF
    have hFpos : ∀ n ∈ F, 0 < n := fun n hn =>
      lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right N 1) (mem_Icc.1 hn).1)
    have hS1 : c ≤ ∑ n ∈ F, volume.real (Aq ψ' n) := by
      calc c ≤ c * ∑ n ∈ F, weight ψ' n := by nlinarith
        _ = ∑ n ∈ F, c * weight ψ' n := by rw [Finset.mul_sum]
        _ ≤ ∑ n ∈ F, volume.real (Aq ψ' n) :=
          Finset.sum_le_sum fun n hn => hlow ψ' hψ' n (hFpos n hn) (hw' n)
    have hS2 : ∑ n ∈ F, ∑ m ∈ F, volume.real (Aq ψ' n ∩ Aq ψ' m) ≤ 4 + C₁ * C₂ := by
      have hterm : ∀ n ∈ F, ∀ m ∈ F, volume.real (Aq ψ' n ∩ Aq ψ' m) ≤
          (if n = m then 2 * weight ψ' n else 0) +
            C₁ * (if n = m then 0 else weight ψ' n * weight ψ' m * Pfac ψ' n m) := by
        intro n hn m hm
        by_cases hnm : n = m
        · subst hnm
          simp only [ite_true, Set.inter_self, mul_zero, add_zero]
          exact volume_Aq_le ψ' hψ' n (hFpos n hn)
        · simp only [hnm, ite_false, zero_add]
          have := hov ψ' hψ' n m (hFpos n hn) (hFpos m hm) hnm
          linarith
      calc ∑ n ∈ F, ∑ m ∈ F, volume.real (Aq ψ' n ∩ Aq ψ' m)
          ≤ ∑ n ∈ F, ∑ m ∈ F, ((if n = m then 2 * weight ψ' n else 0) +
              C₁ * (if n = m then 0 else weight ψ' n * weight ψ' m * Pfac ψ' n m)) :=
            Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => hterm n hn m hm
        _ = ∑ n ∈ F, 2 * weight ψ' n + C₁ * ∑ n ∈ F, ∑ m ∈ F,
              (if n = m then 0 else weight ψ' n * weight ψ' m * Pfac ψ' n m) := by
            simp only [Finset.sum_add_distrib, Finset.mul_sum]
            congr 1
            refine Finset.sum_congr rfl fun n hn => ?_
            rw [Finset.sum_ite_eq F n (fun _ => 2 * weight ψ' n)]
            simp [hn]
        _ ≤ 4 + C₁ * C₂ := by
            have hA : ∑ n ∈ F, 2 * weight ψ' n ≤ 4 := by
              rw [← Finset.mul_sum]; linarith
            have hB := hps ψ' hψ' (max N 1) Y (le_max_right N 1) h2
            have hB' : C₁ * (∑ n ∈ F, ∑ m ∈ F,
                (if n = m then 0 else weight ψ' n * weight ψ' m * Pfac ψ' n m)) ≤ C₁ * C₂ :=
              mul_le_mul_of_nonneg_left hB hC₁.le
            linarith
    refine ⟨F, fun n hn => le_trans (le_max_left N 1) (mem_Icc.1 hn).1,
      lt_of_lt_of_le hc hS1, ?_⟩
    calc ∑ n ∈ F, ∑ m ∈ F, volume.real (Aq ψ' n ∩ Aq ψ' m) ≤ 4 + C₁ * C₂ := hS2
      _ = K * c ^ 2 := by rw [hK]; field_simp
      _ ≤ K * (∑ n ∈ F, volume.real (Aq ψ' n)) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hKpos.le
          exact pow_le_pow_left₀ hc.le hS1 2
  have hlim := measure_limsup_ge_of_second_moment (volume : Measure UnitAddCircle) (Aq ψ')
    (measurableSet_Aq ψ') K hwin
  rw [limsup_Aq_eq] at hlim
  set E := addWellApproximable UnitAddCircle (fun n => ψ' n / n) with hE
  have hEpos : volume E ≠ 0 := by
    intro h0
    have : volume.real E = 0 := by simp [Measure.real, h0]
    rw [this] at hlim
    have : 0 < 1 / K := by positivity
    linarith
  have hfull : ∀ᵐ x : UnitAddCircle, x ∈ E := by
    rcases AddCircle.addWellApproximable_ae_empty_or_univ (T := 1) (fun n => ψ' n / n)
        hradii with h | h
    · exact absurd (measure_eq_zero_iff_ae_notMem.2 h) hEpos
    · exact h
  have hmono : E ⊆ addWellApproximable UnitAddCircle (fun n => ψ n / n) :=
    addWellApproximable_mono fun n =>
      div_le_div_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg n)
  exact ae_approximable_of_ae_circle ψ (hfull.mono fun x hx => hmono hx)
end DuffinSchaeffer
end Port24_Main

open MeasureTheory

theorem OMA.solution : type_of% @Erdos999.erdos_999.variants.erdos := by
  intro f hf hb
  constructor
  · intro ha hs
    obtain ⟨x, hx, hnx⟩ := (ha.and (DuffinSchaeffer.ae_not_approximable_of_summable f hf hs)).exists
    exact hnx hx
  · exact DuffinSchaeffer.bounded_divergence f hf hb
