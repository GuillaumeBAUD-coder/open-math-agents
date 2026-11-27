import FormalConjectures.OEIS.«108866»
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Choose.Dvd

/-!
# Ordowski's weighted harmonic primality criterion

Credit: @marcusbuffett

Write F(n) for the rational expression in A108866. A finite binomial
identity and the vanishing of the quadratic power sum over a finite field
give the complete prime direction. This congruence strengthens Glaisher's
congruence and appears, for example, in F. Bencherif, R. Chellal and S. Zerroukhat,
Amelioration of Glaisher's Congruence (2016), https://hal.science/hal-01341168.

For even n the 2-adic valuation is exactly 1-v₂(n). For odd n>3, 3 never
divides the numerator. More generally a leading base-p digit determines
the residue of p^d F(n), d=floor(log_p n). In particular if n=m p^d
with 1<m<p, passing the proposed test requires p to divide the numerator of F(m).

For n=p^(b+r), the certificates compare terms indexed by multiples of p^b with
an integer polynomial modulo p^(r+1). The scale is lcm(1,...,p^r)/p^r;
divisibility by each denominator and every modular evaluation are checked
in the kernel. These certificates rule out every prime-power composite
with base at most 17.
-/

namespace OMA.R_OeisA108866_conjecture_R1
open Finset OeisA108866

private lemma binomialIdentity (n : ℕ) :
    let S (n : ℕ) : ℚ := ∑ k ∈ range n, (2:ℚ)^(k+1) / (k+1:ℚ)
    let summand (n k : ℕ) : ℚ := (1 + (n.choose k : ℚ)) / (k:ℚ)
    S n = ∑ k ∈ range n, summand n (k+1) := by
  intro S summand
  induction n with
  | zero => simp [S]
  | succ n ih =>
    have diff (k : ℕ) : summand (n+1) (k+1) = summand n (k+1) +
        ((n+1).choose (k+1):ℚ) / (n+1:ℚ) := by
      have h : (n+1:ℚ) * (n.choose k : ℚ) =
          ((n+1).choose (k+1) : ℚ) * (k+1:ℚ) := by exact_mod_cast Nat.add_one_mul_choose_eq n k
      unfold summand
      rw [Nat.choose_succ_succ']
      push_cast
      rw [Nat.choose_succ_succ'] at h
      push_cast at h
      field_simp
      linarith
    have hsum : (∑ k ∈ range n, ((n+1).choose (k+1):ℚ)) + 2 = 2^(n+1) := by
      have h := Nat.sum_range_choose (n+1)
      rw [sum_range_succ', sum_range_succ] at h
      simp at h
      exact_mod_cast (by omega : (∑ k ∈ range n, (n+1).choose (k+1)) + 2 = 2^(n+1))
    rw [show S (n+1) = S n + (2:ℚ)^(n+1)/(n+1:ℚ) by simp [S, sum_range_succ]]
    rw [ih, sum_range_succ]
    simp_rw [diff]
    rw [sum_add_distrib, ← sum_div]
    simp [summand, Nat.choose_self]
    field_simp
    linarith

private lemma unpaired {n : ℕ} (hn : 0 < n) :
    let summand (n k : ℕ) : ℚ := (1 + (n.choose k : ℚ)) / (k:ℚ)
    ratExpression n = ∑ k ∈ range (n-1), summand n (k+1) := by
  intro summand
  let S (n : ℕ) : ℚ := ∑ k ∈ range n, (2:ℚ)^(k+1) / (k+1:ℚ)
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  change (if m+1 > 0 then (-2:ℚ)/(m+1:ℕ) + S (m+1) else 0) = _
  rw [if_pos (by omega)]
  have hb : S (m+1) = ∑ k ∈ range (m+1), summand (m+1) (k+1) := binomialIdentity _
  rw [hb, sum_range_succ]
  simp [summand]
  ring

private lemma pairing {n : ℕ} (hn : 0 < n) :
    let paired (n k : ℕ) : ℚ := (1+(n.choose k:ℚ)) / ((k:ℚ) * ((n-k:ℕ):ℚ))
    2 * ratExpression n = (n:ℚ) * ∑ j ∈ range (n-1), paired n (j+1) := by
  intro paired
  let summand (n k : ℕ) : ℚ := (1 + (n.choose k : ℚ)) / (k:ℚ)
  rw [two_mul, unpaired hn]
  conv_lhs => rhs; rw [← sum_range_reflect]
  rw [← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro j hj
  have hj' := mem_range.mp hj
  have sk : n - 1 - 1 - j + 1 = n - (j+1) := by omega
  rw [sk]
  dsimp only [summand,paired]
  rw [Nat.choose_symm (by omega : j+1 ≤ n)]
  have e : ((n-(j+1):ℕ):ℚ) = (n:ℚ) - (j+1) := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hne : ((n-(j+1):ℕ):ℚ) ≠ 0 := by exact_mod_cast (by omega : n-(j+1) ≠ 0)
  push_cast
  field_simp
  rw [e]
  ring

private lemma res_add {p : ℕ} [Fact p.Prime] {x y : ℚ} {a b : ZMod p} :
    let Res (p : ℕ) [Fact p.Prime] (x : ℚ) (z : ZMod p) : Prop :=
      ¬ p ∣ x.den ∧ (x : ZMod p) = z
    ∀ (hx : Res p x a) (hy : Res p y b), Res p (x+y) (a+b) := by
  intro Res hx hy
  refine ⟨fun hd => (Fact.out : p.Prime).dvd_mul.mp (hd.trans (Rat.add_den_dvd x y)) |>.elim hx.1 hy.1, ?_⟩
  rw [Rat.cast_add_of_ne_zero (by simpa [ZMod.natCast_eq_zero_iff] using hx.1)
    (by simpa [ZMod.natCast_eq_zero_iff] using hy.1), hx.2, hy.2]

private lemma res_sum {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι) (f : ι → ℚ) (g : ι → ZMod p) :
    let Res (p : ℕ) [Fact p.Prime] (x : ℚ) (z : ZMod p) : Prop :=
      ¬ p ∣ x.den ∧ (x : ZMod p) = z
    ∀ (h : ∀ i ∈ s, Res p (f i) (g i)), Res p (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  intro Res h
  classical
  induction s using Finset.induction_on with
  | empty => simp [Res, (Fact.out : p.Prime).not_dvd_one]
  | insert x s hx ih =>
    rw [sum_insert hx, sum_insert hx]
    exact res_add (h _ (by simp)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

private lemma res_frac {p : ℕ} [Fact p.Prime] (a b : ℕ) (hb : ¬p ∣ b) :
    let Res (p : ℕ) [Fact p.Prime] (x : ℚ) (z : ZMod p) : Prop :=
      ¬ p ∣ x.den ∧ (x : ZMod p) = z
    Res p ((a:ℚ)/b) ((a:ZMod p)/b) := by
  intro Res
  have hz := (ZMod.natCast_eq_zero_iff b p).not.mpr hb
  have d : (((a:ℚ)/b).den : ℤ) ∣ (b:ℤ) := by
    simpa [Rat.divInt_eq_div] using Rat.den_dvd (a:ℤ) (b:ℤ)
  refine ⟨fun h => hb (h.trans (by exact_mod_cast d)), ?_⟩
  rw [Rat.cast_div_of_ne_zero (by simp) (by simpa using hz)]
  simp

private lemma inverseSquares {p : ℕ} [Fact p.Prime] (hp : 3 < p) : ∑ i ∈ range p, ((i:ZMod p)⁻¹)^2 = 0 := by
  rw [← Fin.sum_univ_eq_sum_range]
  have eqf (i : Fin p) : (ZMod.finEquiv p i : ZMod p) = (i.val : ZMod p) := by
    cases p with
    | zero => omega
    | succ p => exact (Fin.cast_val_eq_self _).symm
  simp_rw [← eqf]
  calc
    _ = ∑ v : ZMod p, v⁻¹^2 := Equiv.sum_comp (ZMod.finEquiv p).toEquiv _
    _ = ∑ v : ZMod p, v^2 := Equiv.sum_comp (Equiv.inv (ZMod p)) (fun v => v^2)
    _ = 0 := FiniteField.sum_pow_lt_card_sub_one _ _ (by rw [ZMod.card]; omega)

private lemma pairedRes {p : ℕ} [Fact p.Prime] (hp : 3 < p) :
    let paired (n k : ℕ) : ℚ := (1+(n.choose k:ℚ)) / ((k:ℚ) * ((n-k:ℕ):ℚ))
    let Res (p : ℕ) [Fact p.Prime] (x : ℚ) (z : ZMod p) : Prop :=
      ¬ p ∣ x.den ∧ (x : ZMod p) = z
    Res p (∑ j ∈ range (p-1), paired p (j+1)) 0 := by
  intro paired Res
  have hs (j : ℕ) (hj : j ∈ range (p-1)) :
      Res p (paired p (j+1)) (-(((j+1:ℕ):ZMod p)⁻¹)^2) := by
    have hj' := mem_range.mp hj
    let k := j+1
    have hk : 0 < k ∧ k < p := by dsimp [k]; omega
    have hd := (Fact.out : p.Prime).dvd_choose_self hk.1.ne' hk.2
    have hmk : ¬ p ∣ k*(p-k) := by
      rw [(Fact.out : p.Prime).dvd_mul]
      exact not_or_intro (Nat.not_dvd_of_pos_of_lt hk.1 hk.2)
        (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    have h := res_frac (1+p.choose k) (k*(p-k)) hmk
    change Res p (paired p k) (-((k:ZMod p)⁻¹)^2)
    unfold paired
    push_cast at h
    rw [(ZMod.natCast_eq_zero_iff ..).mpr hd, (Nat.cast_sub hk.2.le : ((p-k:ℕ):ZMod p) = _), ZMod.natCast_self, zero_sub] at h
    simpa [div_eq_mul_inv, pow_two] using h
  have hh := res_sum (range (p-1)) _ _ hs
  rw [sum_neg_distrib] at hh
  have he : p = (p-1)+1 := by omega
  have hh' := inverseSquares (p:=p) hp
  conv at hh' => lhs; arg 1; rw [he]
  rw [sum_range_succ'] at hh'
  simp only [Nat.cast_zero, inv_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at hh'
  rw [hh', neg_zero] at hh
  exact hh

private lemma val_num_iff {p : ℕ} [Fact p.Prime] {x : ℚ} (hx : x ≠ 0) {e : ℕ} (he : 0 < e) : p^e ∣ x.num.natAbs ↔ (e:ℤ) ≤ padicValRat p x := by
  have hp : p.Prime := Fact.out
  have hnum : x.num.natAbs ≠ 0 := by simpa using (Rat.num_ne_zero.mpr hx)
  rw [Nat.pow_dvd_iff_le_padicValNat hp.ne_one hnum, padicValRat_def, padicValInt]
  by_cases hden : p ∣ x.den
  · have hu : ¬ p ∣ x.num.natAbs := fun d => hp.not_dvd_one
      ((Nat.dvd_gcd d hden).trans (by simp [x.reduced.gcd_eq_one]))
    rw [padicValNat.eq_zero_of_not_dvd hu]
    omega
  · rw [padicValNat.eq_zero_of_not_dvd hden]
    omega

private lemma positive_of_res_zero {p : ℕ} [Fact p.Prime] {x : ℚ} (hx : x ≠ 0) :
    let Res (p : ℕ) [Fact p.Prime] (x : ℚ) (z : ZMod p) : Prop :=
      ¬ p ∣ x.den ∧ (x : ZMod p) = z
    ∀ (hz : Res p x 0), 0 < padicValRat p x := by
  intro Res hz
  have hd : (x.den : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff ..).not.mpr hz.1
  have hn := hz.2
  rw [Rat.cast_def, div_eq_zero_iff] at hn
  have hv := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp (hn.resolve_right hd)
  have hV : p^1 ∣ x.num.natAbs := by simpa [← Int.natCast_dvd] using hv
  have := (val_num_iff hx (by decide : 0 < 1)).mp hV
  omega

theorem prime_congruence {p : ℕ} [Fact p.Prime] (hp : 3 < p) : (ratExpression p).num ≡ 0 [ZMOD (p^2:ℤ)] := by
  let paired (n k : ℕ) : ℚ := (1+(n.choose k:ℚ)) / ((k:ℚ) * ((n-k:ℕ):ℚ))
  rw [Int.modEq_zero_iff_dvd]
  by_cases hzero : ratExpression p = 0
  · simp [hzero]
  let t := ∑ j ∈ range (p-1), paired p (j+1)
  have h : 2 * ratExpression p = (p:ℚ) * t := pairing (by omega)
  have ht : t ≠ 0 := by intro hz; rw [hz, mul_zero] at h; exact hzero (by linarith)
  have hv := positive_of_res_zero ht (pairedRes hp)
  have hV := congrArg (padicValRat p) h
  have hpp := (Fact.out : p.Prime)
  rw [padicValRat.mul (by norm_num) hzero, padicValRat.mul (by exact_mod_cast hpp.ne_zero) ht,
    padicValRat.self hpp.one_lt] at hV
  have h2 : padicValRat p 2 = 0 := by
    change padicValRat p ((2:ℕ):ℚ) = 0
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))]
    rfl
  rw [h2] at hV
  have hv' := (val_num_iff (p:=p) hzero (by decide : 0 < 2)).mpr (by omega)
  simpa [← Int.natCast_dvd] using hv'

private lemma S_pos {n : ℕ} (hn : 0 < n) :
    let S (n : ℕ) : ℚ := ∑ k ∈ range n, (2:ℚ)^(k+1) / (k+1:ℚ)
    0 < S n := by
  intro S
  apply sum_pos (fun _ _ => by positivity)
  exact ⟨0, mem_range.mpr hn⟩

private lemma expression_pos {n : ℕ} (hn : 1 < n) : 0 < ratExpression n := by
  let summand (n k : ℕ) : ℚ := (1 + (n.choose k : ℚ)) / (k:ℚ)
  rw [unpaired (by omega)]
  apply sum_pos
  · intro k hk
    dsimp only [summand]
    positivity
  · exact ⟨0, mem_range.mpr (by omega)⟩

theorem even_valuation {n : ℕ} (hn : 1 < n) (he : 2 ∣ n) : padicValRat 2 (ratExpression n) = 1 - (padicValNat 2 n : ℤ) := by
  let S (n : ℕ) : ℚ := ∑ k ∈ range n, (2:ℚ)^(k+1) / (k+1:ℚ)
  have hn0 : 0 < n := by omega
  have hq : (n:ℚ) ≠ 0 := by positivity
  have htwo : padicValRat 2 2 = 1 := padicValRat.self (by decide : 1 < 2)
  have hpos : 0 < padicValRat 2 (S n) := by
    apply padicValRat.sum_pos_of_pos _ (S_pos hn0).ne'
    intro i hi
    rw [padicValRat.div (by positivity) (by positivity), padicValRat.pow,
      htwo]
    rw [← Nat.cast_add_one]
    rw [padicValRat.of_nat]
    have hlt := (padicValNat_le_nat_log (p:=2) (i+1)).trans_lt (Nat.log_lt_self _ (by omega))
    omega
  have hnon := (expression_pos hn).ne'
  have hS := (S_pos hn0).ne'
  have hv := one_le_padicValNat_of_dvd hn0.ne' he
  have hA : padicValRat 2 ((-2:ℚ)/n) = 1 - (padicValNat 2 n : ℤ) := by
    rw [padicValRat.div (by norm_num) hq, padicValRat.neg,
      htwo, padicValRat.of_nat]
  have hre : ratExpression n = (-2:ℚ)/n + S n := by simp [ratExpression, hn0, S]
  rw [hre] at hnon ⊢
  rw [padicValRat.add_eq_of_lt hnon (div_ne_zero (by norm_num) hq) hS (by rw [hA]; omega), hA]

private lemma even_excluded {n : ℕ} (hn : 1 < n) (he : 2 ∣ n) : ¬ (ratExpression n).num ≡ 0 [ZMOD (n^2:ℤ)] := by
  rw [Int.modEq_zero_iff_dvd]
  intro hh
  have hd : 2 ∣ (ratExpression n).num.natAbs := by
    have he' : (2:ℤ) ∣ (n:ℤ) := by exact_mod_cast he
    have d := he'.trans ((dvd_pow_self (n:ℤ) (by decide : 2 ≠ 0)).trans hh)
    simpa [← Int.natCast_dvd] using d
  have hv := (val_num_iff (p:=2) (expression_pos hn).ne' (by decide : 0 < 1)).mp (by simpa using hd)
  rw [even_valuation hn he] at hv
  have := one_le_padicValNat_of_dvd (by omega : n ≠ 0) he
  omega

private lemma res_zero_of_num {p : ℕ} [Fact p.Prime] {x : ℚ} (hd : p ∣ x.num.natAbs) :
    let Res (p : ℕ) [Fact p.Prime] (x : ℚ) (z : ZMod p) : Prop :=
      ¬ p ∣ x.den ∧ (x : ZMod p) = z
    Res p x 0 := by
  intro Res
  refine ⟨fun hb => (Fact.out : p.Prime).not_dvd_one
    ((Nat.dvd_gcd hd hb).trans (by simp [x.reduced.gcd_eq_one])), ?_⟩
  have hi : (p:ℤ) ∣ x.num := by simpa [← Int.natCast_dvd] using hd
  simp [Rat.cast_def, (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr hi]

private lemma res_zero_of_pos {p : ℕ} [Fact p.Prime] {x : ℚ} (hv : 0 < padicValRat p x) :
    let Res (p : ℕ) [Fact p.Prime] (x : ℚ) (z : ZMod p) : Prop :=
      ¬ p ∣ x.den ∧ (x : ZMod p) = z
    Res p x 0 := by
  intro Res
  by_cases hz : x = 0
  · simp [hz, Res, (Fact.out : p.Prime).not_dvd_one]
  apply res_zero_of_num
  simpa using (val_num_iff hz (by decide : 0 < 1)).mpr (show (1:ℤ) ≤ padicValRat p x by omega)

private lemma res_neg {p : ℕ} [Fact p.Prime] {x : ℚ} {v : ZMod p} :
    let Res (p : ℕ) [Fact p.Prime] (x : ℚ) (z : ZMod p) : Prop :=
      ¬ p ∣ x.den ∧ (x : ZMod p) = z
    ∀ (hx : Res p x v), Res p (-x) (-v) := by
  intro Res hx
  exact ⟨by simpa using hx.1, by simpa using congrArg Neg.neg hx.2⟩

private lemma negligible {p : ℕ} [Fact p.Prime] {d k c : ℕ} (hk : 0 < k) (hc : 0 < c) (hd : ¬p^d ∣ k) :
    let Res (p : ℕ) [Fact p.Prime] (x : ℚ) (z : ZMod p) : Prop :=
      ¬ p ∣ x.den ∧ (x : ZMod p) = z
    Res p ((p:ℚ)^d * (c:ℚ) / k) 0 := by
  intro Res
  have hp : p.Prime := Fact.out
  have hq : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  apply res_zero_of_pos
  rw [padicValRat.div (mul_ne_zero (pow_ne_zero _ hq) (by positivity)) (by positivity),
    padicValRat.mul (pow_ne_zero _ hq) (by positivity), padicValRat.pow,
    padicValRat.self hp.one_lt, padicValRat.of_nat, padicValRat.of_nat]
  have h := (Nat.pow_dvd_iff_le_padicValNat hp.ne_one hk.ne').not.mp hd
  omega

private lemma scaledSum {p : ℕ} [Fact p.Prime] (d n : ℕ) (hn : n < p*p^d) :
    let S (n : ℕ) : ℚ := ∑ k ∈ range n, (2:ℚ)^(k+1) / (k+1:ℚ)
    let Res (p : ℕ) [Fact p.Prime] (x : ℚ) (z : ZMod p) : Prop :=
      ¬ p ∣ x.den ∧ (x : ZMod p) = z
    let leadingSum (p a : ℕ) [Fact p.Prime] : ZMod p :=
      ∑ k ∈ range a, (2:ZMod p)^(k+1) / (k+1:ZMod p)
    Res p ((p:ℚ)^d * S n) (leadingSum p (n/p^d)) := by
  intro S Res leadingSum
  have hp : p.Prime := Fact.out
  have hB := pow_pos hp.pos d
  induction n with
  | zero => simp [S, leadingSum, Res, hp.not_dvd_one]
  | succ n ih =>
    have hi := ih (by omega)
    rw [show S (n+1) = S n + (2:ℚ)^(n+1)/(n+1:ℚ) by simp [S, sum_range_succ], mul_add]
    by_cases hd : p^d ∣ n+1
    · have hs := Nat.succ_div_of_dvd hd
      have he : n+1 = p^d * (n/p^d+1) := by rw [← hs, Nat.mul_div_cancel' hd]
      have hl := (Nat.div_lt_iff_lt_mul hB).mpr hn
      rw [hs] at hl ⊢
      have nd := Nat.not_dvd_of_pos_of_lt (Nat.succ_pos _) hl
      have hfrac := res_frac (2^(n+1)) (n/p^d+1) nd
      have den : (n+1:ℚ) = (p:ℚ)^d * ((n/p^d:ℕ)+1:ℚ) := by exact_mod_cast he
      have hpq : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have eqn : (p:ℚ)^d * ((2:ℚ)^(n+1)/(n+1:ℚ)) = (2:ℚ)^(n+1)/((n/p^d:ℕ)+1:ℚ) := by
        rw [den]; field_simp
      have ez : (2:ZMod p)^(n+1) = 2^(n/p^d+1) := by rw [he, pow_mul, ZMod.pow_card_pow]
      push_cast at hfrac
      rw [ez] at hfrac
      rw [eqn]
      dsimp only [leadingSum]
      rw [sum_range_succ]
      exact res_add hi hfrac
    · rw [Nat.succ_div_of_not_dvd hd]
      have hv := negligible (p:=p) (k:=n+1) (c:=2^(n+1)) (by omega) (by positivity) hd
      have hh := res_add hi hv
      simpa [mul_div_assoc] using hh

private lemma scaledExpression {p : ℕ} [Fact p.Prime] (d n : ℕ) (hn : 0 < n) (hlt : n < p*p^d) :
    let Res (p : ℕ) [Fact p.Prime] (x : ℚ) (z : ZMod p) : Prop :=
      ¬ p ∣ x.den ∧ (x : ZMod p) = z
    let leadingSum (p a : ℕ) [Fact p.Prime] : ZMod p :=
      ∑ k ∈ range a, (2:ZMod p)^(k+1) / (k+1:ZMod p)
    let digitTest (p d n : ℕ) [Fact p.Prime] : ZMod p :=
      leadingSum p (n/p^d) - if p^d ∣ n then (2:ZMod p) / (n/p^d:ℕ) else 0
    Res p ((p:ℚ)^d * ratExpression n) (digitTest p d n) := by
  intro Res leadingSum digitTest
  let S (n : ℕ) : ℚ := ∑ k ∈ range n, (2:ℚ)^(k+1) / (k+1:ℚ)
  have h := scaledSum (p:=p) d n hlt
  have hB := pow_pos (Fact.out : p.Prime).pos d
  have hq : (n:ℚ) ≠ 0 := by positivity
  have corr : Res p ((p:ℚ)^d * (2/n)) (if p^d ∣ n then 2 / (n/p^d:ℕ) else 0) := by
    by_cases hd : p^d ∣ n
    · rw [if_pos hd]
      have hdiv := Nat.mul_div_cancel' hd
      have hnq : 0 < n / p^d := by by_contra! hz; rw [Nat.eq_zero_of_le_zero hz, mul_zero] at hdiv; omega
      have nd := Nat.not_dvd_of_pos_of_lt hnq ((Nat.div_lt_iff_lt_mul hB).mpr hlt)
      have he : (p:ℚ)^d * ((n/p^d:ℕ):ℚ) = (n:ℚ) := by exact_mod_cast hdiv
      have he' : (p:ℚ)^d * (2/n) = 2/((n/p^d:ℕ):ℚ) := by field_simp; linarith
      rw [he']
      simpa using res_frac 2 (n/p^d) nd
    · rw [if_neg hd]
      simpa [mul_div_assoc] using negligible (p:=p) hn (by decide : 0 < 2) hd
  have he : ratExpression n = S n - 2/n := by simp [ratExpression, S, hn]; ring
  dsimp only [digitTest]
  rw [he, mul_sub, sub_eq_add_neg, sub_eq_add_neg]
  exact res_add h (res_neg corr)

theorem necessaryDigit {p : ℕ} [Fact p.Prime] {n d : ℕ} (hn : 0 < n) (hlt : n < p*p^d) (hnum : p ∣ (ratExpression n).num.natAbs) :
    let leadingSum (p a : ℕ) [Fact p.Prime] : ZMod p :=
      ∑ k ∈ range a, (2:ZMod p)^(k+1) / (k+1:ZMod p)
    let digitTest (p d n : ℕ) [Fact p.Prime] : ZMod p :=
      leadingSum p (n/p^d) - if p^d ∣ n then (2:ZMod p) / (n/p^d:ℕ) else 0
    digitTest p d n = 0 := by
  intro leadingSum digitTest
  have hR := scaledExpression (p:=p) d n hn hlt
  have hx := res_zero_of_num hnum
  have hden : ((p:ℚ)^d).den = 1 := by rw [← Nat.cast_pow]; simp
  have hid : (((p:ℚ)^d * ratExpression n:ℚ):ZMod p) = digitTest p d n := hR.2
  rw [← hid, Rat.cast_mul_of_ne_zero (by rw [hden]; simp)
    (by simpa [ZMod.natCast_eq_zero_iff] using hx.1), hx.2, mul_zero]

private lemma exactBlock {p : ℕ} [Fact p.Prime] (d n : ℕ) :
    let S (n : ℕ) : ℚ := ∑ k ∈ range n, (2:ℚ)^(k+1) / (k+1:ℚ)
    let Res (p : ℕ) [Fact p.Prime] (x : ℚ) (z : ZMod p) : Prop :=
      ¬ p ∣ x.den ∧ (x : ZMod p) = z
    let baseSum (y : ℕ) (n : ℕ) : ℚ := ∑ k ∈ range n, (y:ℚ)^(k+1)/(k+1:ℚ)
    Res p ((p:ℚ)^d * S n - baseSum (2^(p^d)) (n/p^d)) 0 := by
  intro S Res baseSum
  have hp : p.Prime := Fact.out
  have hpq : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  induction n with
  | zero => simp [S, baseSum, Res, hp.not_dvd_one]
  | succ n ih =>
    rw [show S (n+1) = S n + (2:ℚ)^(n+1)/(n+1:ℚ) by simp [S, sum_range_succ], mul_add]
    by_cases hd : p^d ∣ n+1
    · have hs := Nat.succ_div_of_dvd hd
      have he : n+1 = p^d * (n/p^d+1) := by rw [← hs, Nat.mul_div_cancel' hd]
      rw [hs, show baseSum (2^p^d) (n/p^d+1) = baseSum (2^p^d) (n/p^d) +
        ((2:ℚ)^p^d)^(n/p^d+1)/((n/p^d:ℕ)+1:ℚ) by simp [baseSum, sum_range_succ]]
      have den : (n+1:ℚ) = (p:ℚ)^d * ((n/p^d:ℕ)+1:ℚ) := by exact_mod_cast he
      have eqn : (p:ℚ)^d * ((2:ℚ)^(n+1)/(n+1:ℚ)) =
          ((2:ℚ)^p^d)^(n/p^d+1)/((n/p^d:ℕ)+1:ℚ) := by
        rw [den, he, pow_mul]; field_simp
      rwa [eqn, add_sub_add_right_eq_sub]
    · rw [Nat.succ_div_of_not_dvd hd]
      have hv := negligible (p:=p) (k:=n+1) (c:=2^(n+1)) (by omega) (by positivity) hd
      have hh := res_add ih hv
      simpa [Res, S, baseSum, mul_div_assoc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hh

private lemma evalNine (y : ℕ) :
    let baseSum (y : ℕ) (n : ℕ) : ℚ := ∑ k ∈ range n, (y:ℚ)^(k+1)/(k+1:ℚ)
    let polynomial {R : Type} [Ring R] (y : R) : R :=
      2520*y + 1260*y^2 + 840*y^3 + 630*y^4 + 504*y^5 + 420*y^6 +
      360*y^7 + 315*y^8 + 280*y^9 - 560
    9 * baseSum y 9 - 2 = polynomial (y:ℚ) / 280 := by
  intro baseSum polynomial
  simp [baseSum, polynomial, sum_range_succ]
  ring

private lemma baseMod (b : ℕ) : (2:ZMod 27)^(3^b) = 2 ∨ (2:ZMod 27)^(3^b) = 8 ∨ (2:ZMod 27)^(3^b) = 26 := by
  induction b with
  | zero => norm_num
  | succ b ih =>
    rw [pow_succ, pow_mul]
    rcases ih with h|h|h <;> rw [h] <;> decide

private lemma valNine (b : ℕ) :
    let baseSum (y : ℕ) (n : ℕ) : ℚ := ∑ k ∈ range n, (y:ℚ)^(k+1)/(k+1:ℚ)
    padicValRat 3 (9 * baseSum (2^(3^b)) 9 - 2) = 2 := by
  intro baseSum
  let polynomial {R : Type} [Ring R] (y : R) : R :=
    2520*y + 1260*y^2 + 840*y^3 + 630*y^4 + 504*y^5 + 420*y^6 +
    360*y^7 + 315*y^8 + 280*y^9 - 560
  let y := 2^(3^b)
  let z : ℤ := polynomial (y:ℤ)
  have hz : (z:ZMod 27) = 18 := by
    change ((polynomial (y:ℤ):ℤ):ZMod 27) = _
    have he : ((polynomial (y:ℤ):ℤ):ZMod 27) = polynomial (y:ZMod 27) := by
      simp [polynomial]
    rw [he]
    change polynomial (((2^(3^b):ℕ):ZMod 27)) = _
    push_cast
    rcases baseMod b with h|h|h <;> rw [h] <;> decide
  have h27 : z ≡ 18 [ZMOD 27] := (ZMod.intCast_eq_intCast_iff ..).mp (by simpa using hz)
  change z % 27 = 18 % 27 at h27
  have hd9 : (9:ℤ) ∣ z := by omega
  have hd27 : ¬ (27:ℤ) ∣ z := by omega
  have hza : z.natAbs ≠ 0 := by intro h; simp_all
  have hd9' : 3^(2:ℕ) ∣ z.natAbs := by simpa [← Int.natCast_dvd] using hd9
  have hd27' : ¬ 3^(3:ℕ) ∣ z.natAbs := by simpa [← Int.natCast_dvd] using hd27
  have hlo := (Nat.pow_dvd_iff_le_padicValNat (by decide : 3≠1) hza).mp hd9'
  have hhi := (Nat.pow_dvd_iff_le_padicValNat (by decide : 3≠1) hza).not.mp hd27'
  have vz : padicValRat 3 (z:ℚ) = 2 := by
    rw [padicValRat.of_int]
    change (padicValNat 3 z.natAbs:ℤ) = 2
    omega
  have ve : padicValRat 3 280 = 0 := by
    change padicValRat 3 ((280:ℕ):ℚ) = 0
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (by decide : ¬3∣280)]
    rfl
  rw [evalNine]
  have eqz : polynomial ((y:ℕ):ℚ) = (z:ℚ) := by simp [z, polynomial]
  change padicValRat 3 (polynomial (y:ℚ) / 280) = 2
  rw [eqz, padicValRat.div (by exact_mod_cast (show z ≠ 0 by omega)) (by norm_num), vz, ve]
  decide

theorem threePowerVal (b : ℕ) : padicValRat 3 (ratExpression (3^(b+2))) = -(b:ℤ) := by
  let S (n : ℕ) : ℚ := ∑ k ∈ range n, (2:ℚ)^(k+1) / (k+1:ℚ)
  let Res (p : ℕ) [Fact p.Prime] (x : ℚ) (z : ZMod p) : Prop :=
    ¬ p ∣ x.den ∧ (x : ZMod p) = z
  let baseSum (y : ℕ) (n : ℕ) : ℚ := ∑ k ∈ range n, (y:ℚ)^(k+1)/(k+1:ℚ)
  let n := 3^(b+2)
  have hn : n = 3^b * 9 := by dsimp [n]; rw [pow_add]; norm_num
  have hbig : 1 < n := by rw [hn]; have := pow_pos (by decide : (0:ℕ) < 3) b; omega
  have hnq : (n:ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  let e : ℚ := (3:ℚ)^b * S n - baseSum (2^3^b) 9
  let t : ℚ := 9 * baseSum (2^3^b) 9 - 2
  have hE : Res 3 e 0 := by
    have h := exactBlock (p:=3) b n
    have divEq : n/3^b = 9 := by rw [hn, Nat.mul_div_cancel_left _ (by positivity)]
    simpa [e, Res, S, baseSum, divEq] using h
  have he : (n:ℚ) * ratExpression n = t + 9 * e := by
    have hr : ratExpression n = (-2:ℚ)/n + S n := by simp [ratExpression, S, show 0 < n by omega]
    have hn' : (n:ℚ) = (3:ℚ)^b * 9 := by exact_mod_cast hn
    dsimp [t, e]
    rw [hr, mul_add, show (n:ℚ)*(-2/n) = -2 by field_simp, hn']
    ring
  have vt : padicValRat 3 t = 2 := valNine b
  have hF := (expression_pos hbig).ne'
  have v : padicValRat 3 (t + 9*e) = 2 := by
    by_cases ze : e = 0
    · simpa [ze] using vt
    have ve := positive_of_res_zero ze hE
    have v9 : padicValRat 3 9 = 2 := by
      change padicValRat 3 (((3:ℕ):ℚ)^2) = 2
      rw [padicValRat.pow, padicValRat.self (by decide : 1 < 3)]
      norm_num
    have v9e := padicValRat.mul (p:=3) (by norm_num : (9:ℚ) ≠ 0) ze
    rw [padicValRat.add_eq_of_lt (he ▸ mul_ne_zero hnq hF)
      (by intro h; rw [h] at vt; simp at vt) (mul_ne_zero (by norm_num) ze) (by omega), vt]
  have hv : padicValRat 3 (n:ℚ) = (b:ℤ)+2 := by
    change padicValRat 3 (((3^(b+2):ℕ)):ℚ) = _
    rw [Nat.cast_pow, padicValRat.pow, padicValRat.self (by decide : 1 < 3)]
    push_cast
    ring
  rw [← he, padicValRat.mul hnq hF, hv] at v
  change padicValRat 3 (ratExpression n) = _
  omega

theorem three_not_dvd {n : ℕ} (hn : 3 < n) (hodd : ¬2 ∣ n) : ¬3 ∣ (ratExpression n).num.natAbs := by
  let leadingSum (p a : ℕ) [Fact p.Prime] : ZMod p :=
    ∑ k ∈ range a, (2:ZMod p)^(k+1) / (k+1:ZMod p)
  let digitTest (p d n : ℕ) [Fact p.Prime] : ZMod p :=
    leadingSum p (n/p^d) - if p^d ∣ n then (2:ZMod p) / (n/p^d:ℕ) else 0
  let d := Nat.log 3 n
  have hi := Nat.lt_pow_succ_log_self (by decide : 1 < 3) n
  change n < 3^(d+1) at hi
  rw [pow_succ, mul_comm] at hi
  have lo := Nat.pow_log_le_self 3 (by omega : n ≠ 0)
  change 3^d ≤ n at lo
  have hp : 0 < (3:ℕ)^d := by positivity
  have hl : 1 ≤ n/3^d := (Nat.le_div_iff_mul_le hp).mpr (by simpa using lo)
  have hu := (Nat.div_lt_iff_lt_mul hp).mpr hi
  intro hnum
  have h := necessaryDigit (p:=3) (d:=d) (by omega) hi hnum
  change digitTest 3 d n = 0 at h
  dsimp only [digitTest] at h
  by_cases hd : 3^d ∣ n
  · have he := Nat.mul_div_cancel' hd
    have he1 : n/3^d = 1 := by
      by_contra hh
      have hh2 : n/3^d = 2 := by omega
      rw [hh2, mul_comm] at he
      exact hodd ⟨_, he.symm⟩
    rw [he1, mul_one] at he
    have hd2 : 2 ≤ d := by
      by_contra! h
      interval_cases d <;> simp_all <;> omega
    let b := d-2
    have hb : d = b+2 := by dsimp [b]; omega
    have hval := (val_num_iff (p:=3) (expression_pos (by omega : 1<n)).ne' (by decide : 0<1)).mp
      (by simpa using hnum)
    rw [← he, hb, threePowerVal] at hval
    omega
  · rw [if_neg hd, sub_zero] at h
    rcases (show n/3^d = 1 ∨ n/3^d = 2 by omega) with he|he
    · exact (by dsimp [leadingSum]; decide +kernel : leadingSum 3 1 ≠ 0) (he ▸ h)
    · exact (by dsimp [leadingSum]; decide +kernel : leadingSum 3 2 ≠ 0) (he ▸ h)

private lemma factor_num {p n : ℕ} (hd : p ∣ n) (h : (ratExpression n).num ≡ 0 [ZMOD (n^2:ℤ)]) : p ∣ (ratExpression n).num.natAbs := by
  have hd' : (p:ℤ) ∣ (n:ℤ) := by exact_mod_cast hd
  have hh := hd'.trans ((dvd_pow_self (n:ℤ) (by decide : 2 ≠ 0)).trans (Int.modEq_zero_iff_dvd.mp h))
  simpa [← Int.natCast_dvd] using hh

private lemma res_small {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 0 < m) (hmp : m < p) :
    let Res (p : ℕ) [Fact p.Prime] (x : ℚ) (z : ZMod p) : Prop :=
      ¬ p ∣ x.den ∧ (x : ZMod p) = z
    let leadingSum (p a : ℕ) [Fact p.Prime] : ZMod p :=
      ∑ k ∈ range a, (2:ZMod p)^(k+1) / (k+1:ZMod p)
    Res p (ratExpression m) (leadingSum p m - 2/(m:ZMod p)) := by
  intro Res leadingSum
  let digitTest (p d n : ℕ) [Fact p.Prime] : ZMod p :=
    leadingSum p (n/p^d) - if p^d ∣ n then (2:ZMod p) / (n/p^d:ℕ) else 0
  simpa [digitTest, hm] using scaledExpression (p:=p) 0 m hm (by simpa using hmp)

theorem cofactor_obstruction {p : ℕ} [Fact p.Prime] {d m : ℕ} (hm : 0 < m) (hmp : m < p) (hd : p ∣ (ratExpression (p^d*m)).num.natAbs) : p ∣ (ratExpression m).num.natAbs := by
  let leadingSum (p a : ℕ) [Fact p.Prime] : ZMod p :=
    ∑ k ∈ range a, (2:ZMod p)^(k+1) / (k+1:ZMod p)
  let digitTest (p d n : ℕ) [Fact p.Prime] : ZMod p :=
    leadingSum p (n/p^d) - if p^d ∣ n then (2:ZMod p) / (n/p^d:ℕ) else 0
  have pp := pow_pos (Fact.out : p.Prime).pos d
  have hh := necessaryDigit (p:=p) (n:=p^d*m) (d:=d) (Nat.mul_pos pp hm)
    (by simpa [mul_comm] using (Nat.mul_lt_mul_left pp).mpr hmp) hd
  have he : p^d*m/p^d = m := Nat.mul_div_cancel_left _ pp
  change digitTest p d (p^d*m) = 0 at hh
  dsimp only [digitTest] at hh
  rw [if_pos (dvd_mul_right ..), he] at hh
  have hr := res_small hm hmp
  have hnum : ((ratExpression m:ℚ):ZMod p) = 0 := hr.2.trans hh
  rw [Rat.cast_def, div_eq_zero_iff] at hnum
  have hi := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp
    (hnum.resolve_right ((ZMod.natCast_eq_zero_iff ..).not.mpr hr.1))
  simpa [← Int.natCast_dvd] using hi

theorem clean_forces_power {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 1 < n) (ho : ¬2 ∣ n) :
    let leadingSum (p a : ℕ) [Fact p.Prime] : ZMod p :=
      ∑ k ∈ range a, (2:ZMod p)^(k+1) / (k+1:ZMod p)
    let clean (p : ℕ) [Fact p.Prime] : Prop := ∀ a : Fin p, 0 < a.val →
        leadingSum p a ≠ 0 ∧ (1 < a.val → ¬ 2 ∣ a.val → leadingSum p a - 2/(a.val:ZMod p) ≠ 0)
    ∀ (hc : clean p) (hnum : p ∣ (ratExpression n).num.natAbs), n = p^(Nat.log p n) := by
  intro leadingSum clean hc hnum
  let digitTest (p d n : ℕ) [Fact p.Prime] : ZMod p :=
    leadingSum p (n/p^d) - if p^d ∣ n then (2:ZMod p) / (n/p^d:ℕ) else 0
  let d := Nat.log p n
  have hp : p.Prime := Fact.out
  have lo := Nat.pow_log_le_self p (by omega : n ≠ 0)
  change p^d ≤ n at lo
  have hi := Nat.lt_pow_succ_log_self hp.one_lt n
  change n < p^(d+1) at hi
  rw [pow_succ, mul_comm] at hi
  have pp := pow_pos hp.pos d
  have hm := (Nat.le_div_iff_mul_le pp).mpr (show 1 * p^d ≤ n by simpa using lo)
  have hu := (Nat.div_lt_iff_lt_mul pp).mpr hi
  have h := necessaryDigit (p:=p) (d:=d) (by omega) hi hnum
  have H := hc ⟨n/p^d, hu⟩ hm
  change digitTest p d n = 0 at h
  dsimp only [digitTest] at h
  by_cases hd : p^d ∣ n
  · rw [if_pos hd] at h
    have he := Nat.mul_div_cancel' hd
    have hne : ¬ 2 ∣ n / p^d := by intro h; exact ho (he ▸ (h.trans (dvd_mul_left ..)))
    have he1 : n/p^d = 1 := by
      by_contra hf
      exact H.2 (by change 1 < n/p^d; omega) hne h
    rwa [he1, mul_one, eq_comm] at he
  · rw [if_neg hd, sub_zero] at h
    exact (H.1 h).elim

private lemma scanDigits_sound {p : ℕ} [Fact p.Prime] (t j : ℕ) :
    let leadingSum (p a : ℕ) [Fact p.Prime] : ZMod p :=
      ∑ k ∈ range a, (2:ZMod p)^(k+1) / (k+1:ZMod p)
    let scanDigits (p : ℕ) [Fact p.Prime] (t : ℕ) : ℕ → ZMod p → Bool :=
      Nat.rec (motive := fun _ => ℕ → ZMod p → Bool) (fun _ _ => true) (fun _ next j v =>
        let w := v + (2:ZMod p)^(j+1)/(j+1:ZMod p)
        decide (w ≠ 0 ∧ (1 < j+1 → ¬2 ∣ j+1 → w-2/(j+1:ZMod p) ≠ 0)) && next (j+1) w) t
    ∀ (ok : scanDigits p t j (leadingSum p j) = true) (k : ℕ) (hl : j < k) (hu : k ≤ j+t), leadingSum p k ≠ 0 ∧ (1 < k → ¬2 ∣ k → leadingSum p k-2/(k:ZMod p) ≠ 0) := by
  intro leadingSum scanDigits ok k hl hu
  induction t generalizing j with
  | zero => omega
  | succ t ih =>
    have he : leadingSum p (j+1) = leadingSum p j + (2:ZMod p)^(j+1)/(j+1:ZMod p) := by
      simp [leadingSum, Finset.sum_range_succ]
    simp only [scanDigits, ← he, Bool.and_eq_true, decide_eq_true_eq] at ok
    rcases Nat.eq_or_lt_of_le (show j+1 ≤ k by omega) with hk|hk
    · subst k; simpa using ok.1
    · exact ih _ ok.2 hk (by omega)

private lemma cleanOfCheck {p : ℕ} [Fact p.Prime] :
    let leadingSum (p a : ℕ) [Fact p.Prime] : ZMod p :=
      ∑ k ∈ range a, (2:ZMod p)^(k+1) / (k+1:ZMod p)
    let clean (p : ℕ) [Fact p.Prime] : Prop := ∀ a : Fin p, 0 < a.val →
        leadingSum p a ≠ 0 ∧ (1 < a.val → ¬ 2 ∣ a.val → leadingSum p a - 2/(a.val:ZMod p) ≠ 0)
    let scanDigits (p : ℕ) [Fact p.Prime] (t : ℕ) : ℕ → ZMod p → Bool :=
      Nat.rec (motive := fun _ => ℕ → ZMod p → Bool) (fun _ _ => true) (fun _ next j v =>
        let w := v + (2:ZMod p)^(j+1)/(j+1:ZMod p)
        decide (w ≠ 0 ∧ (1 < j+1 → ¬2 ∣ j+1 → w-2/(j+1:ZMod p) ≠ 0)) && next (j+1) w) t
    ∀ (ok : scanDigits p (p-1) 0 0 = true), clean p := by
  intro leadingSum clean scanDigits ok
  intro a ha
  have hs : scanDigits p (p-1) 0 (leadingSum p 0) = true := by simpa [leadingSum] using ok
  exact scanDigits_sound _ _ hs a.val ha (by have := a.isLt; omega)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 2000000 in
theorem clean_examples (p : ℕ) [Fact p.Prime] (hp : p ∈ ({7,11,17,43,61,71}:Finset ℕ)) :
    let leadingSum (p a : ℕ) [Fact p.Prime] : ZMod p :=
      ∑ k ∈ range a, (2:ZMod p)^(k+1) / (k+1:ZMod p)
    let clean (p : ℕ) [Fact p.Prime] : Prop := ∀ a : Fin p, 0 < a.val →
        leadingSum p a ≠ 0 ∧ (1 < a.val → ¬ 2 ∣ a.val → leadingSum p a - 2/(a.val:ZMod p) ≠ 0)
    clean p := by
  intro leadingSum clean
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with h|h|h|h|h|h <;> subst p <;> apply cleanOfCheck <;> decide +revert +kernel

private lemma horner_sum {R : Type} [CommRing R] (D : ℕ) (y : R) (t : ℕ) (a : R) :
    let horner {R : Type} [Ring R] (D : ℕ) (y : R) (t : ℕ) : R → R :=
      Nat.rec (motive := fun _ => R → R) (fun a => a)
        (fun j next a => next ((↑(D/(j+1))+a)*y)) t
    horner D y t a = (∑ j ∈ range t, (↑(D/(j+1)):R)*y^(j+1)) + a*y^t := by
  intro horner
  induction t generalizing a with
  | zero => simp [horner]
  | succ t ih =>
    change horner D y t ((↑(D/(t+1))+a)*y) = _
    rw [ih, sum_range_succ, pow_succ]; ring

private lemma polynomial_rat (A L y : ℕ) (hl : ∀ i : Fin A, i.val+1 ∣ A*L) :
    let baseSum (y : ℕ) (n : ℕ) : ℚ := ∑ k ∈ range n, (y:ℚ)^(k+1)/(k+1:ℚ)
    let horner {R : Type} [Ring R] (D : ℕ) (y : R) (t : ℕ) : R → R :=
      Nat.rec (motive := fun _ => R → R) (fun a => a)
        (fun j next a => next ((↑(D/(j+1))+a)*y)) t
    let blockPolynomial {R : Type} [Ring R] (A L : ℕ) (y : R) : R :=
      horner (A*L) y A 0 - 2 * L
    blockPolynomial A L (y:ℚ) = (A * baseSum y A - 2) * L := by
  intro baseSum horner blockPolynomial
  unfold blockPolynomial baseSum
  have hh : horner (A*L) (y:ℚ) A 0 = _ := horner_sum (A*L) (y:ℚ) A 0
  rw [hh, zero_mul, add_zero, sub_mul]
  conv_rhs => lhs; rw [mul_right_comm, mul_sum]
  congr 1
  apply sum_congr rfl
  intro j hj
  have h := Nat.div_mul_cancel (hl ⟨j,mem_range.mp hj⟩)
  have he : ((A*L/(j+1):ℕ):ℚ)*(j+1:ℚ) = (A:ℚ)*L := by exact_mod_cast h
  field_simp
  linear_combination ((y:ℚ)^(j+1)) * he

private lemma cyclic {M p : ℕ} (C : Finset (ZMod M)) (h0 : 2 ∈ C) (hStep : ∀ x ∈ C, x^p ∈ C) (b : ℕ) : (2:ZMod M)^(p^b) ∈ C := by
  induction b with
  | zero => simpa using h0
  | succ b ih => simpa [pow_succ, pow_mul] using hStep _ ih

private lemma castPoly {R : Type} [CommRing R] (A L y : ℕ) :
    let horner {R : Type} [Ring R] (D : ℕ) (y : R) (t : ℕ) : R → R :=
      Nat.rec (motive := fun _ => R → R) (fun a => a)
        (fun j next a => next ((↑(D/(j+1))+a)*y)) t
    let blockPolynomial {R : Type} [Ring R] (A L : ℕ) (y : R) : R :=
      horner (A*L) y A 0 - 2 * L
    ((blockPolynomial A L (y:ℤ):ℤ):R) = blockPolynomial A L (y:R) := by
  intro horner blockPolynomial
  have h1 : horner (A*L) (y:ℤ) A 0 = _ := horner_sum (A*L) (y:ℤ) A 0
  have h2 : horner (A*L) (y:R) A 0 = _ := horner_sum (A*L) (y:R) A 0
  simp only [blockPolynomial, h1, h2, zero_mul, add_zero, Int.cast_sub, Int.cast_mul,
    Int.cast_sum, Int.cast_pow, Int.cast_natCast, Int.cast_ofNat]

private lemma coverOfCheck {D A : ℕ} :
    let dividesThrough (D t : ℕ) : Bool :=
      Nat.rec true (fun j next => (D % (j+1) == 0) && next) t
    ∀ (ok : dividesThrough D A = true) (i : Fin A), i.val+1 ∣ D := by
  intro dividesThrough ok i
  induction A with
  | zero => exact i.elim0
  | succ A ih =>
    simp only [dividesThrough, Bool.and_eq_true, beq_iff_eq] at ok
    by_cases h : i.val < A
    · exact ih ok.2 ⟨i.val,h⟩
    · have he : i.val = A := by have := i.isLt; omega
      rw [he]
      exact Nat.dvd_of_mod_eq_zero ok.1

private lemma hornerMod_cast (D M y t a : ℕ) :
    let horner {R : Type} [Ring R] (D : ℕ) (y : R) (t : ℕ) : R → R :=
      Nat.rec (motive := fun _ => R → R) (fun a => a)
        (fun j next a => next ((↑(D/(j+1))+a)*y)) t
    let hornerMod (D M y t : ℕ) : ℕ → ℕ :=
      Nat.rec (motive := fun _ => ℕ → ℕ) id (fun j next a => next (((D/(j+1)%M+a)*y)%M)) t
    ((Nat.cast (hornerMod D M y t a)):ZMod M) = horner D (y:ZMod M) t (a:ZMod M) := by
  intro horner hornerMod
  induction t generalizing a with
  | zero => rfl
  | succ t ih =>
    change ((hornerMod D M y t (((D/(t+1)%M+a)*y)%M):ℕ):ZMod M) = horner D (y:ZMod M) t _
    rw [ih]
    simp

private lemma certOfCheck {A L M y : ℕ} :
    let horner {R : Type} [Ring R] (D : ℕ) (y : R) (t : ℕ) : R → R :=
      Nat.rec (motive := fun _ => R → R) (fun a => a)
        (fun j next a => next ((↑(D/(j+1))+a)*y)) t
    let blockPolynomial {R : Type} [Ring R] (A L : ℕ) (y : R) : R :=
      horner (A*L) y A 0 - 2 * L
    let hornerMod (D M y t : ℕ) : ℕ → ℕ :=
      Nat.rec (motive := fun _ => ℕ → ℕ) id (fun j next a => next (((D/(j+1)%M+a)*y)%M)) t
    ∀ (h : hornerMod (A*L) M y A 0 % M ≠ (2*L)%M), blockPolynomial A L (y:ZMod M) ≠ 0 := by
  intro horner blockPolynomial hornerMod h
  unfold blockPolynomial
  rw [sub_ne_zero]
  have hh := (ZMod.natCast_eq_natCast_iff ..).not.mpr h
  have he : ((hornerMod (A*L) M y A 0:ℕ):ZMod M) = horner (A*L) (y:ZMod M) A 0 := by simpa using hornerMod_cast (A*L) M y A 0
  rw [he] at hh
  simpa using hh

private lemma excludeBlock {p r L : ℕ} [Fact p.Prime] (hcover : ∀ i : Fin (p^r), i.val+1 ∣ p^r*L) :
    let horner {R : Type} [Ring R] (D : ℕ) (y : R) (t : ℕ) : R → R :=
      Nat.rec (motive := fun _ => R → R) (fun a => a)
        (fun j next a => next ((↑(D/(j+1))+a)*y)) t
    let blockPolynomial {R : Type} [Ring R] (A L : ℕ) (y : R) : R :=
      horner (A*L) y A 0 - 2 * L
    ∀ (hcert : ∀ b : ℕ, blockPolynomial (p^r) L ((2:ZMod (p^(r+1)))^(p^b)) ≠ 0) (b : ℕ), ¬ p ∣ (ratExpression (p^(b+r))).num.natAbs := by
  intro horner blockPolynomial hcert b
  let S (n : ℕ) : ℚ := ∑ k ∈ range n, (2:ℚ)^(k+1) / (k+1:ℚ)
  let Res (p : ℕ) [Fact p.Prime] (x : ℚ) (z : ZMod p) : Prop :=
    ¬ p ∣ x.den ∧ (x : ZMod p) = z
  let baseSum (y : ℕ) (n : ℕ) : ℚ := ∑ k ∈ range n, (y:ℚ)^(k+1)/(k+1:ℚ)
  intro hnum
  let A := p^r
  let B := p^b
  let n := p^(b+r)
  let y := 2^B
  let e : ℚ := (B:ℚ)*S n - baseSum y A
  have hp := (Fact.out : p.Prime)
  have hA : 0 < A := pow_pos hp.pos _
  have hB : 0 < B := pow_pos hp.pos _
  have hN : 0 < n := pow_pos hp.pos _
  have hn : n = B*A := pow_add ..
  have hE : Res p e 0 := by
    have hg := exactBlock (p:=p) b n
    have he : n / B = A := by rw [hn, Nat.mul_div_cancel_left _ hB]
    simpa [e, y, B, he, Res, S, baseSum] using hg
  have hRl := res_zero_of_num hnum
  have hBR : Res p (B:ℚ) (B:ZMod p) := ⟨by simp [hp.not_dvd_one], by simp⟩
  have hpr : Res p ((B:ℚ)*ratExpression n) 0 := by
    refine ⟨fun hd => hp.dvd_mul.mp (hd.trans (Rat.mul_den_dvd ..)) |>.elim hBR.1 hRl.1, ?_⟩
    rw [Rat.cast_mul_of_ne_zero (by simpa [ZMod.natCast_eq_zero_iff] using hBR.1)
      (by simpa [ZMod.natCast_eq_zero_iff] using hRl.1), hRl.2, mul_zero]
  let v : ℚ := (B:ℚ)*ratExpression n - e
  have hv : Res p v 0 := by simpa [v, sub_eq_add_neg] using res_add hpr (res_neg hE)
  let z := blockPolynomial A L (y:ℤ)
  have hc : (z:ZMod (p^(r+1))) ≠ 0 := by
    have hc' : (z:ZMod (p^(r+1))) = blockPolynomial A L (y:ZMod (p^(r+1))) := castPoly A L y
    rw [hc']
    simpa [A, B, y] using hcert b
  have hz : z ≠ 0 := fun h => hc (by rw [h]; simp)
  have hzq : (z:ℚ) ≠ 0 := by exact_mod_cast hz
  have heq : (z:ℚ) = v * (p:ℚ)^r * (L:ℚ) := by
    have hR : ratExpression n = (-2:ℚ)/n + S n := by simp [ratExpression, S, hN]
    have hNQ : (n:ℚ) = (B:ℚ)*A := by exact_mod_cast hn
    have hBQ : (B:ℚ) ≠ 0 := by positivity
    have hAQ : (A:ℚ) ≠ 0 := by positivity
    have hz' : (z:ℚ) = blockPolynomial A L (y:ℚ) := castPoly A L y
    have hp' : blockPolynomial A L (y:ℚ) = ((A:ℚ)*baseSum y A-2)*L := polynomial_rat A L y hcover
    rw [hz', hp']
    rw [← Nat.cast_pow]
    change _ = v * (A:ℚ) * L
    dsimp only [v,e]
    rw [hR, hNQ]
    field_simp
    ring
  have hnv : v ≠ 0 := fun h => hzq (by simp [heq, h])
  have hL : (L:ℚ) ≠ 0 := fun h => hzq (by simp [heq, h])
  have hpq : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hvp := positive_of_res_zero hnv hv
  have hvz := congrArg (padicValRat p) heq
  rw [padicValRat.mul (mul_ne_zero hnv (pow_ne_zero _ hpq)) hL, padicValRat.mul hnv (pow_ne_zero _ hpq),
    padicValRat.pow, padicValRat.self hp.one_lt, padicValRat.of_nat] at hvz
  have hh := (val_num_iff (p:=p) hzq (by omega : 0 < r+1)).mpr (by push_cast; omega)
  have hi : ((p:ℤ)^(r+1)) ∣ z := by simpa [← Int.natCast_dvd] using hh
  exact hc ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr (by exact_mod_cast hi))

private theorem certifiedPower {p r L : ℕ} [Fact p.Prime] (cs : List ℕ) :
    let cover (D t : ℕ) := Nat.rec true (fun j a => (D%(j+1)==0) && a) t
    let eval (D M y t : ℕ) : ℕ → ℕ :=
      Nat.rec (motive := fun _ => ℕ → ℕ) id (fun j next a => next (((D/(j+1)%M+a)*y)%M)) t
    let A := p^r
    let M := p^(r+1)
    cover (A*L) A = true → 2 ∈ cs →
    cs.all (fun c => cs.contains (c^p%M) && (eval (A*L) M c A 0 % M != (2*L)%M)) = true →
    ∀ b, ¬ p ∣ (ratExpression (p^(b+r))).num.natAbs := by
  intro cover eval A M hcov htwo hall b
  apply excludeBlock (p:=p) (r:=r) (L:=L) (coverOfCheck hcov) _ b
  intro e
  have hcs (c : ℕ) (hc : c ∈ cs) :
      c^p%M ∈ cs ∧ eval (A*L) M c A 0 % M ≠ (2*L)%M := by
    have h := List.all_eq_true.mp hall c hc
    simpa using h
  have he (j : ℕ) : ∃ c ∈ cs, (2:ZMod M)^(p^j) = (c:ZMod M) := by
    induction j with
    | zero => exact ⟨2, htwo, by simp⟩
    | succ j ih =>
      obtain ⟨c,hc,eqc⟩ := ih
      refine ⟨c^p%M,(hcs c hc).1,?_⟩
      rw [pow_succ, pow_mul, eqc]
      simp
  obtain ⟨c,hc,heq⟩ := he e
  change (let horner (D : ℕ) (y : ZMod M) (t : ℕ) : ZMod M → ZMod M :=
            Nat.rec (motive := fun _ => ZMod M → ZMod M) id
              (fun j next a => next ((↑(D/(j+1))+a)*y)) t
          horner (A*L) ((2:ZMod M)^p^e) A 0 - 2*L ≠ 0)
  rw [heq]
  exact certOfCheck (A:=A) (L:=L) (M:=M) (y:=c) (hcs c hc).2


set_option maxRecDepth 50000 in
private lemma power5 (b : ℕ) : ¬ 5 ∣ (ratExpression (5^(b+3))).num.natAbs := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact certifiedPower (p:=5) (r:=3) (L:=420590743023540522185944856832763355670515675214144)
    [2, 32, 57, 182] (by decide +kernel) (by decide) (by decide +kernel) b

set_option maxRecDepth 50000 in
private lemma power7 (b : ℕ) : ¬ 7 ∣ (ratExpression (7^(b+4))).num.natAbs := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact certifiedPower (p:=7) (r:=4) (L:=5808150844545837480409929216271000452478351935227351038534954247135032744256768073072557505598006643395084482749762601143676508114246473466709603130560612799705214901687322656554164361480372923854052108641710593713753829271112375921360999898554266587211204037180907356298433251812210411657153198011729803017023119179298452516949035398583162344279234854336752404479098508390229750278127887904527393794576169756104180872706020936865276197541618907814103615639488382046390182908649747796202684441843470474274909922949998012074826765153823681318089171256911533856094081688688507597521582492276436188330534317489615253018371944138998270137105563048012542228858381964242462570238258067275536175227118614366833398470119057094802593628439928194418143143687699144633273380004669664679304029644037068441680952006718778129084491058457400939743920936063408311106780270511851462174310765019218445811197201720255019662888200205008665843304674595339140470495949488735411614547703377261759405653955405523407891973752763152213069860128413215445502446923896052480000)
    [2, 128, 9585, 8556, 1353] (by decide +kernel) (by decide) (by decide +kernel) b

set_option maxRecDepth 50000 in
private lemma power11 (b : ℕ) : ¬ 11 ∣ (ratExpression (11^(b+3))).num.natAbs := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  exact certifiedPower (p:=11) (r:=3) (L:=202886754387449661311699674721346958928627222893200002621532168610004193716699960309604189578781587819360594410335827871457270937807426176703963174752278665685228564718996648564127696072055611129606096769405192353634204768347178586406076108018568430418916284138743786981525688609947120436646830451154600463811325194465387023925187046862295552480930623971357176526984571453300160517740506208872515600740679547546652803451905119291236116172162335625788925422924408099465334097394464817361219260775827760211416874816922202965438639950897174445783434323473127297375558836937968974720000)
    [2, 2048, 13906, 12575] (by decide +kernel) (by decide) (by decide +kernel) b

set_option maxRecDepth 50000 in
private lemma power13 (b : ℕ) : ¬ 13 ∣ (ratExpression (13^(b+3))).num.natAbs := by
  letI : Fact (Nat.Prime 13) := ⟨by decide⟩
  exact certifiedPower (p:=13) (r:=3) (L:=255600481635921776121397865798875248266716465250079887510957358715275653793778950976282018777601831126346220773052256150314385900773321416864028861205984863268125751264795779249998908887617478777605007554522841140505199226924732036350374846450711913174802395155487196909952491750736349453905492990816850141234267318011268295117656023785869470224564993434930014260262448626882823311597698350048012790763578762477579601853612230393143397733371341422530242095276477600472445628879379039141657879271441932593328413464454732818786603027170902416954077987995810666256772745087341519555930558984012698292971566252361810089666832383147346621392259456599488692718616457016388313841990552898581452461525250660125428102375989505134898168791609638902993248799505291919788601892610848835107701279279414260822254449654092484401600268479129283490112277134303396693129627930505229905398967866129427900495988534704240316426194492667910307238766238631615522560000)
    [2, 8192, 20191, 4812] (by decide +kernel) (by decide) (by decide +kernel) b

set_option maxRecDepth 50000 in
private lemma power17 (b : ℕ) : ¬ 17 ∣ (ratExpression (17^(b+3))).num.natAbs := by
  letI : Fact (Nat.Prime 17) := ⟨by decide⟩
  exact certifiedPower (p:=17) (r:=3) (L:=7171568305365952685871740100309244323240389040078024943528742437034363100469415813130359805951922566496638358459478418023932824878030153585034394438510894886052393560497423005537563960009532605262938712184393151472220252786930021603930619651185777381367251446681803413888251122826322211756579314887929248154113109906704456534605437848890952608416121307172280014174569130749952938196025735086022499262340616549324386256284696078630880358338898296724549049911692890384332771107205705102071505853953687172276475861368866156262998984685960622521121046318982422877564653937206350593891995331215473544506352530104476254476469924754314569232901649500942781137661859803773616154119243381289705606145234276529026133478472639989788282324365764282765132786241274386445956344747410263504750075344307900100576051613151596046343803028959957173798222448155980863044685780962334822900141127291864974531541124223525041227589935087429704938452532154426333881066461887004573958589139138154976810681671350426952312799688100553351947026466822997132012936177673964073224580777463268452132011799242670616465393782128799521433633581661364459245166816745220301771256946688744917044855557901724696467673673224455569451439181590842899256349644942715648768388252430788278969811931674452928109998081162910787258895058115081571765535199407452941695261176778852083742926053431295992120282394721125681297740663171460134233807310675893342294970704274804186183154032855641130704057317862697399864373840998758648958884946168520030269277425430330976876942936456254697235778149746825952590533352352764403568459785300986301406059501594185500912965973348554680376599630780527915720113173896088452761506640593329768476689321681910105133924060371447614855227793013245115438994754670940900491154896696793501083561169302046035765052618905298576381257702053138880570754822719648009776308492564894057052194953197177104659456875890539541299614421681728914075821823667129021475768012460191214803490608321307360504181647263808769258538078250443012277661621642465857378563151313395444188150409083252351373310145086714521719368490256557036804234569629413235995865600000)
    [2, 47551, 15761, 59978] (by decide +kernel) (by decide) (by decide +kernel) b

private lemma restrictions {n : ℕ} (hn : 3 < n) (hc : ¬ n.Prime) :
    let leadingSum (p a : ℕ) [Fact p.Prime] : ZMod p :=
      ∑ k ∈ range a, (2:ZMod p)^(k+1) / (k+1:ZMod p)
    let digitTest (p d n : ℕ) [Fact p.Prime] : ZMod p :=
      leadingSum p (n/p^d) - if p^d ∣ n then (2:ZMod p) / (n/p^d:ℕ) else 0
    let clean (p : ℕ) [Fact p.Prime] : Prop := ∀ a : Fin p, 0 < a.val →
        leadingSum p a ≠ 0 ∧ (1 < a.val → ¬ 2 ∣ a.val → leadingSum p a - 2/(a.val:ZMod p) ≠ 0)
    let passes (n : ℕ) : Prop := (ratExpression n).num ≡ 0 [ZMOD (n^2:ℤ)]
    let primePower (n : ℕ) : Prop := ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n = p^e
    let remaining (n : ℕ) : Prop :=
      ¬ 2 ∣ n ∧ ¬ 3 ∣ n ∧ ¬ primePower n ∧
      ∀ p (hp : p.Prime), p ∣ n →
        letI : Fact p.Prime := ⟨hp⟩
        ¬ clean p ∧ digitTest p (Nat.log p n) n = 0
    ∀ (hw : ¬ primePower n) (hh : passes n), remaining n := by
  intro leadingSum digitTest clean passes primePower remaining hw hh
  have ho : ¬2 ∣ n := fun hd => even_excluded (by omega) hd hh
  have ht : ¬3 ∣ n := fun hd => three_not_dvd hn ho (factor_num hd hh)
  refine ⟨ho, ht, hw, ?_⟩
  intro p hp hd
  letI : Fact p.Prime := ⟨hp⟩
  have hnum := factor_num hd hh
  have h := Nat.lt_pow_succ_log_self hp.one_lt n
  rw [pow_succ, mul_comm] at h
  refine ⟨?_, necessaryDigit (by omega) h hnum⟩
  intro hclean
  have he := clean_forces_power (by omega) ho hclean hnum
  have hx : 2 ≤ Nat.log p n := by
    by_contra! hlt
    rcases (show Nat.log p n = 0 ∨ Nat.log p n = 1 by omega) with h0|h1
    · rw [h0, pow_zero] at he; omega
    · rw [h1, pow_one] at he; exact hc (he ▸ hp)
  exact hw ⟨p, _, hp, hx, he⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 2000000 in
theorem smallPower {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) :
    let passes (n : ℕ) : Prop := (ratExpression n).num ≡ 0 [ZMOD (n^2:ℤ)]
    ∀ (hh : passes (p^e)), 17 < p := by
  intro passes hh
  have hpd : p ∣ p^e := dvd_pow_self _ (by omega)
  have hnum := factor_num hpd hh
  have pp : 2 ≤ p := hp.two_le
  have hn : 3 < p^e := by
    have ha := Nat.pow_le_pow_left pp e
    have hb := Nat.pow_le_pow_right (by decide : 0 < 2) he
    omega
  have htwo : p ≠ 2 := by
    rintro rfl
    exact even_excluded (by omega) hpd hh
  have hthree : p ≠ 3 := by
    rintro rfl
    exact three_not_dvd hn (fun h => even_excluded (by omega) h hh) hnum
  by_contra! hsmall
  have options : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 := by
    interval_cases p <;> norm_num at *
  rcases options with rfl|rfl|rfl|rfl|rfl
  · by_cases h : 3 ≤ e
    · obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le h
      rw [show e = b+3 by omega] at hnum
      exact power5 b hnum
    · have h2 : e = 2 := by omega
      subst e
      exact (by dsimp [passes, ratExpression]; decide +kernel : ¬ passes (5^2)) hh
  · by_cases h : 4 ≤ e
    · obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le h
      rw [show e = b+4 by omega] at hnum
      exact power7 b hnum
    · interval_cases e
      · exact (by dsimp [passes, ratExpression]; decide +kernel : ¬ passes (7^2)) hh
      · exact (by dsimp [passes, ratExpression]; decide +kernel : ¬ passes (7^3)) hh
  · by_cases h : 3 ≤ e
    · obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le h
      rw [show e = b+3 by omega] at hnum
      exact power11 b hnum
    · have h2 : e = 2 := by omega
      subst e
      exact (by dsimp [passes, ratExpression]; decide +kernel : ¬ passes (11^2)) hh
  · by_cases h : 3 ≤ e
    · obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le h
      rw [show e = b+3 by omega] at hnum
      exact power13 b hnum
    · have h2 : e = 2 := by omega
      subst e
      exact (by dsimp [passes, ratExpression]; decide +kernel : ¬ passes (13^2)) hh
  · by_cases h : 3 ≤ e
    · obtain ⟨b,hb⟩ := Nat.exists_eq_add_of_le h
      rw [show e = b+3 by omega] at hnum
      exact power17 b hnum
    · have h2 : e = 2 := by omega
      subst e
      exact (by dsimp [passes, ratExpression]; decide +kernel : ¬ passes (17^2)) hh

/-- Exclude prime powers with base prime greater than 17. -/
def H1 : Prop :=
  let passes (n : ℕ) : Prop := (ratExpression n).num ≡ 0 [ZMOD (n^2:ℤ)]
  ∀ p e : ℕ, p.Prime → 17 < p → 2 ≤ e → ¬ passes (p^e)

/-- For a prime larger than its cofactor, the only candidates for each fixed cofactor m>1 are prime divisors of the nonzero numerator of F(m). -/
def H2 : Prop :=
  let leadingSum (p a : ℕ) [Fact p.Prime] : ZMod p :=
    ∑ k ∈ range a, (2:ZMod p)^(k+1) / (k+1:ZMod p)
  let digitTest (p d n : ℕ) [Fact p.Prime] : ZMod p :=
    leadingSum p (n/p^d) - if p^d ∣ n then (2:ZMod p) / (n/p^d:ℕ) else 0
  let clean (p : ℕ) [Fact p.Prime] : Prop := ∀ a : Fin p, 0 < a.val →
      leadingSum p a ≠ 0 ∧ (1 < a.val → ¬ 2 ∣ a.val → leadingSum p a - 2/(a.val:ZMod p) ≠ 0)
  let passes (n : ℕ) : Prop := (ratExpression n).num ≡ 0 [ZMOD (n^2:ℤ)]
  let primePower (n : ℕ) : Prop := ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n = p^e
  let remaining (n : ℕ) : Prop :=
    ¬ 2 ∣ n ∧ ¬ 3 ∣ n ∧ ¬ primePower n ∧
    ∀ p (hp : p.Prime), p ∣ n →
      letI : Fact p.Prime := ⟨hp⟩
      ¬ clean p ∧ digitTest p (Nat.log p n) n = 0
  ∀ p m : ℕ, p.Prime → 1 < m → m < p → remaining (p*m) →
      p ∣ (ratExpression m).num.natAbs → ¬ passes (p*m)

/-- All prime divisors are at most the square root and survive the digit tests. -/
def H3 : Prop :=
  let leadingSum (p a : ℕ) [Fact p.Prime] : ZMod p :=
    ∑ k ∈ range a, (2:ZMod p)^(k+1) / (k+1:ZMod p)
  let digitTest (p d n : ℕ) [Fact p.Prime] : ZMod p :=
    leadingSum p (n/p^d) - if p^d ∣ n then (2:ZMod p) / (n/p^d:ℕ) else 0
  let clean (p : ℕ) [Fact p.Prime] : Prop := ∀ a : Fin p, 0 < a.val →
      leadingSum p a ≠ 0 ∧ (1 < a.val → ¬ 2 ∣ a.val → leadingSum p a - 2/(a.val:ZMod p) ≠ 0)
  let passes (n : ℕ) : Prop := (ratExpression n).num ≡ 0 [ZMOD (n^2:ℤ)]
  let primePower (n : ℕ) : Prop := ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n = p^e
  let remaining (n : ℕ) : Prop :=
    ¬ 2 ∣ n ∧ ¬ 3 ∣ n ∧ ¬ primePower n ∧
    ∀ p (hp : p.Prime), p ∣ n →
      letI : Fact p.Prime := ⟨hp⟩
      ¬ clean p ∧ digitTest p (Nat.log p n) n = 0
  ∀ n : ℕ, 3 < n → ¬ n.Prime → remaining n →
      (∀ p, p.Prime → p ∣ n → p ≤ n/p) → ¬ passes n

theorem main : H1 → H2 → H3 → type_of% @OeisA108866.conjecture := by
  let primePower (n : ℕ) : Prop := ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n = p^e
  intro hpower hlarge hsmooth n hn
  constructor
  · intro hh
    by_contra hc
    by_cases hw : primePower n
    · obtain ⟨p,e,hp,he,rfl⟩ := hw
      exact hpower p e hp (smallPower hp he hh) he hh
    have hr := restrictions hn hc hw hh
    by_cases hs : ∀ p, p.Prime → p ∣ n → p ≤ n/p
    · exact hsmooth n hn hc hr hs hh
    push Not at hs
    obtain ⟨p,hp,hd,hlt⟩ := hs
    letI : Fact p.Prime := ⟨hp⟩
    let m := n/p
    have he : p*m = n := Nat.mul_div_cancel' hd
    have hm : 1 < m := by
      by_contra! h
      change m ≤ 1 at h
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0|h1
      · rw [h0, mul_zero] at he; omega
      · rw [h1, mul_one] at he; exact hc (he ▸ hp)
    have hd' := factor_num hd hh
    have hnum := cofactor_obstruction (p:=p) (d:=1) (m:=m) (by omega) hlt
      (by simpa [pow_one, he] using hd')
    exact hlarge p m hp hm hlt (he ▸ hr) hnum (he ▸ hh)
  · intro hp
    letI : Fact n.Prime := ⟨hp⟩
    exact prime_congruence hn

end OMA.R_OeisA108866_conjecture_R1
