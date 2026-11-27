import FormalConjectures.OEIS.«7406»
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Prime cubes in numerators of reciprocal square sums

Credit: @marcusbuffett

Write H(t) for the sum of the reciprocal squares through t. For a prime p at
least five, the numerator at (t+1)p-1 is divisible by p precisely when the
numerator at t is divisible by p³. The full block of nonmultiples of p sums
to zero in the residue field. The same block decomposition at arbitrary
prefixes shows that a child can be divisible by p only if its parent was
divisible by p². Compare Jianqiang Zhao, Examples of finite p-divisible sets
of MHS, Example 2 (https://arxiv.org/abs/0806.4947).

The earlier R1 reduction distinguishes prime and composite indices. Here the
prime case and all candidate prime divisors below 2048 are discharged. The
two remaining hypotheses concern first digits and children of exceptional
prefixes, respectively. The final equivalence shows that both are necessary.
-/

namespace SquareHarmonic
open Finset

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
private lemma first_bound {p : ℕ} (hp : p.Prime) (hle : p ≤ 2047) (h7 : p ≠ 7) {t : ℕ}
    (ht : 0 < t) (htp : t < p) : ¬ p^2 ∣ OeisA7406.a t := by
  let h (n : ℕ) : ℚ := ∑ k ∈ Icc 1 n, (1 : ℚ) / (k : ℚ)^2

  have h_zero : h 0 = 0 := by simp [h]

  have h_succ (n : ℕ) : h (n+1) = h n + 1 / ((n+1 : ℕ) : ℚ)^2 := by
    dsimp only [h]
    rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega : 1 ≤ n+1),
      Finset.sum_insert (by simp), add_comm]
  let denom (i : ℕ) : ℕ := i.factorial^2

  let num : ℕ → ℕ := Nat.rec 0 (fun i last => last*(i+1)^2 + denom i)

  have denom_succ (i : ℕ) : denom (i+1) = denom i*(i+1)^2 := by
    simp [denom,Nat.factorial_succ,mul_pow,mul_comm]

  have h_fraction (i : ℕ) : h i = (Nat.cast (num i) : ℚ)/(Nat.cast (denom i) : ℚ) := by
    induction i with
    | zero => simp [num,h_zero]
    | succ i ih =>
      have hd : (Nat.cast (denom i) : ℚ) ≠ 0 := by dsimp [denom]; positivity
      rw [h_succ,ih,show num (i+1) = num i*(i+1)^2 + denom i by rfl,denom_succ]
      push_cast
      field_simp

  have num_dvd (i : ℕ) : OeisA7406.a i ∣ num i := by
    have hd : (Nat.cast (denom i) : ℤ) ≠ 0 := by dsimp [denom]; positivity
    have eq : h i = Rat.divInt (Nat.cast (num i) : ℤ) (Nat.cast (denom i) : ℤ) := by
      rw [h_fraction,Rat.divInt_eq_div]; push_cast; rfl
    have hv := Rat.num_dvd (Nat.cast (num i) : ℤ) hd
    rw [← eq] at hv
    change (h i).num.natAbs ∣ num i
    simpa using (Int.natAbs_dvd_natAbs.mpr hv)

  /- With modulus M, advance the numerator and denominator after clearing the
  factorial denominator. A successful scan excludes a zero numerator at each
  of the following k indices. -/
  let scan (M k : ℕ) : ℕ → ℕ → ℕ → Bool := Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → Bool) (fun _ _ _ => true) (fun _ next i u v =>
      let s := (i+1)^2
      let w := (u*s+v)%M
      w != 0 && next (i+1) w (v*s%M)) k

  have scan_sound {M : ℕ} (k i : ℕ)
      (ok : scan M k i (num i % M) (denom i % M)) :
      ∀ t, i < t → t ≤ i+k → ¬ M ∣ num t := by
    induction k generalizing i with
    | zero => omega
    | succ k ih =>
      change ((_ != 0) && scan M k (i+1) _ _) = true at ok
      simp only [Bool.and_eq_true, bne_iff_ne] at ok
      have ew : ((num i%M)*(i+1)^2 + denom i%M)%M = num (i+1)%M :=
        ((Nat.mod_modEq (num i) M).mul_right ((i+1)^2)).add (Nat.mod_modEq (denom i) M)
      have ed : ((denom i%M)*(i+1)^2)%M = denom (i+1)%M := by
        rw [denom_succ]
        exact (Nat.mod_modEq _ _).mul_right _
      rw [ew,ed] at ok
      intro t hlt hle
      rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with eq | more
      · subst t
        exact fun hd => ok.1 (Nat.mod_eq_zero_of_dvd hd)
      · exact ih (i+1) ok.2 t more (by omega)

  let firstLevel (p : ℕ) : Bool := !p.Prime || p == 7 || scan (p^2) (p-1) 0 0 (1%(p^2))

  let block (b : ℕ) : Bool := (List.range 16).all (fun i => firstLevel (16*b+i))

  have blocks (b : ℕ) (hb : b < 128) : block b = true := by
    dsimp only [block, firstLevel, scan]
    interval_cases b <;> as_aux_lemma => decide +kernel

  have scan_table (p : Fin 2048) : firstLevel p.val := by
    have hh := blocks (p.val/16) (by omega)
    obtain hv := List.all_eq_true.mp hh (p.val%16) (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
    simpa only [Nat.div_add_mod] using hv
  have chk := scan_table ⟨p,by omega⟩
  change firstLevel p = true at chk
  simp [firstLevel,hp,h7] at chk
  have z : scan (p^2) (p-1) 0 (num 0 % p^2) (denom 0 % p^2) := by
    simpa only [num, Nat.rec_zero, denom, Nat.factorial_zero, one_pow, Nat.zero_mod] using chk
  exact fun hd => scan_sound (p-1) 0 z t ht (by omega) (hd.trans (num_dvd t))

set_option maxRecDepth 6000 in
theorem local_data {p : ℕ} [Fact p.Prime] :
    (3 < p → p ∣ OeisA7406.a (p-1)) ∧
    (3 < p → ∀ t : ℕ, 0 < t → (p ∣ OeisA7406.a ((t+1)*p-1) ↔ p^3 ∣ OeisA7406.a t)) ∧
    (p ≤ 2047 → ∀ t : ℕ, 0 < t → ¬ p^3 ∣ OeisA7406.a t ∧ (p ≤ 3 → ¬ p ∣ OeisA7406.a t)) ∧
    (∀ t : ℕ, p ≤ t → p^3 ∣ OeisA7406.a t → p^2 ∣ OeisA7406.a (t/p)) := by
  let h (n : ℕ) : ℚ := ∑ k ∈ Icc 1 n, (1 : ℚ) / (k : ℚ)^2

  have h_zero : h 0 = 0 := by simp [h]

  have h_succ (n : ℕ) : h (n+1) = h n + 1 / ((n+1 : ℕ) : ℚ)^2 := by
    dsimp only [h]
    rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega : 1 ≤ n+1),
      Finset.sum_insert (by simp), add_comm]

  have h_pos {n : ℕ} (hn : 0 < n) : 0 < h n := by
    apply Finset.sum_pos
    · intro i hi
      have : 0 < i := (mem_Icc.mp hi).1
      positivity
    · exact ⟨1, mem_Icc.mpr ⟨le_rfl, hn⟩⟩



  let Res (x : ℚ) (z : ZMod p) : Prop :=
    ¬ p ∣ x.den ∧ (x : ZMod p) = z

  have res_add {x y : ℚ} {a b : ZMod p} (hx : Res x a) (hy : Res y b) :
      Res (x+y) (a+b) := by
    refine ⟨fun hd => (Fact.out : p.Prime).dvd_mul.mp (hd.trans (Rat.add_den_dvd x y)) |>.elim hx.1 hy.1, ?_⟩
    rw [Rat.cast_add_of_ne_zero (by simpa [ZMod.natCast_eq_zero_iff] using hx.1)
      (by simpa [ZMod.natCast_eq_zero_iff] using hy.1), hx.2, hy.2]

  have res_term {i : ℕ} (hi : ¬ p ∣ i) :
      Res ((1:ℚ) / (i:ℚ)^2) (((i:ZMod p)⁻¹)^2) := by
    have hip : (i : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff ..).not.mpr hi
    have hi0 : i ≠ 0 := by rintro rfl; simp at hi
    have eq : (1:ℚ) / (i:ℚ)^2 = ((i^2:ℕ):ℚ)⁻¹ := by push_cast; rw [one_div]
    rw [eq]
    refine ⟨?_, ?_⟩
    · rw [Rat.den_inv_of_ne_zero (by positivity)]
      simpa using (show ¬ p ∣ i^2 from fun d => hi ((Fact.out : p.Prime).dvd_of_dvd_pow d))
    · rw [Rat.cast_inv_of_ne_zero (q := ((i^2:ℕ):ℚ)) (by simpa using pow_ne_zero 2 hip)]
      simp [inv_pow]

  let rem (n : ℕ) : ℚ := h n - h (n/p) / (p:ℚ)^2

  have rem_res (n : ℕ) : Res (rem n)
      (∑ i ∈ range (n+1), ((i:ZMod p)⁻¹)^2) := by
    induction n with
    | zero =>
      simp [rem, h_zero, Res, (Fact.out : p.Prime).not_dvd_one]
    | succ n ih =>
      rw [sum_range_succ]
      by_cases hd : p ∣ n+1
      · have he : rem (n+1) = rem n := by
          have hq := Nat.succ_div_of_dvd hd
          have hn : (n+1:ℕ) = p * (n/p+1) := by
            rw [← hq, Nat.mul_div_cancel' hd]
          have cast : ((n+1:ℕ):ℚ) = (p:ℚ)*((n/p:ℕ)+1:ℚ) := by exact_mod_cast hn
          dsimp only [rem]
          rw [ hq, h_succ, h_succ]
          push_cast at cast ⊢
          rw [cast, mul_pow, one_div, mul_inv_rev]
          ring
        rw [he, (ZMod.natCast_eq_zero_iff ..).mpr hd]
        simpa using ih
      · have he : rem (n+1) = rem n + 1 / ((n+1:ℕ):ℚ)^2 := by
          dsimp only [rem]
          rw [ Nat.succ_div_of_not_dvd hd, h_succ]
          ring
        rw [he]
        exact res_add ih (res_term hd)

  have block_zero (hp : 3 < p) (q : ℕ) :
      ∑ i ∈ range (q*p), ((i:ZMod p)⁻¹)^2 = 0 := by
    have z : ∑ i ∈ range p, ((i:ZMod p)⁻¹)^2 = 0 := by
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
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih, zero_add]
      simpa using z

  have val_num_iff {x : ℚ} (hx : x ≠ 0) {e : ℕ} (he : 0 < e) :
      p^e ∣ x.num.natAbs ↔ (e:ℤ) ≤ padicValRat p x := by
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

  have nonneg_of_res {x : ℚ} {a : ZMod p} (hx : Res x a) :
      0 ≤ padicValRat p x := by
    rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hx.1]
    simp

  have positive_of_res_zero {x : ℚ} (hx : x ≠ 0) (hz : Res x 0) :
      0 < padicValRat p x := by
    have hd : (x.den : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff ..).not.mpr hz.1
    have hn := hz.2
    rw [Rat.cast_def, div_eq_zero_iff] at hn
    have hv := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp (hn.resolve_right hd)
    have hV : p^1 ∣ x.num.natAbs := by simpa [← Int.natCast_dvd] using hv
    have := (val_num_iff hx (by decide : 0 < 1)).mp hV
    omega

  have val_scale {t : ℕ} (ht : 0 < t) :
      padicValRat p (h t / (p:ℚ)^2) = padicValRat p (h t) - 2 := by
    have hp : p.Prime := Fact.out
    have hpr : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [padicValRat.div (h_pos ht).ne' (pow_ne_zero _ hpr),padicValRat.pow,
      padicValRat.self hp.one_lt]
    norm_num

  have val_split {n : ℕ} (hn : 0 < n) (ht : 0 < n/p)
      (hs : padicValRat p (h (n/p))-2 < padicValRat p (rem n) ∨ rem n = 0) :
      padicValRat p (h n) = padicValRat p (h (n/p))-2 := by
    have eq : h n = h (n/p)/(p:ℚ)^2 + rem n := by unfold rem; ring
    by_cases hz : rem n = 0
    · rw [eq, hz, add_zero, val_scale ht]
    have hp : p.Prime := Fact.out
    have hpr : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [eq, padicValRat.add_eq_of_lt (eq ▸ (h_pos hn).ne')
      (div_ne_zero (h_pos ht).ne' (pow_ne_zero _ hpr)) hz
      (by rw [val_scale ht]; exact hs.resolve_right hz), val_scale ht]

  have drop_two {n : ℕ} (ht : 0 < n/p) (hv : padicValRat p (h (n/p)) < 2) :
      padicValRat p (h n) = padicValRat p (h (n/p))-2 := by
    have hn : 0 < n := by contrapose! ht; simp [Nat.eq_zero_of_le_zero ht]
    have hi := nonneg_of_res (rem_res n)
    exact val_split hn ht (Or.inl (by omega))

  have full_res (hp : 3 < p) {q : ℕ} (hq : 0 < q) : Res (rem (q*p-1)) 0 := by
    have hpp : p.Prime := Fact.out
    have hn := Nat.mul_pos hq hpp.pos
    have R := rem_res (q*p-1)
    rw [show q*p-1+1=q*p by omega, block_zero hp q] at R
    exact R

  have prime_index (hp : 3 < p) : p ∣ OeisA7406.a (p-1) := by
    have hr := full_res hp (q:=1) (by decide)
    have R : Res (h (p-1)) 0 := by
      simpa [rem, Nat.div_eq_of_lt (by omega : p-1 < p), h_zero] using hr
    have ht := (h_pos (by omega : 0 < p-1)).ne'
    have vv := positive_of_res_zero ht R
    have := (val_num_iff ht (e:=1) (by decide)).mpr (by omega)
    simpa [OeisA7406.a,h] using this

  have prime_cube_iff (hp : 3 < p) {t : ℕ} (ht : 0 < t) :
      p ∣ OeisA7406.a ((t+1)*p-1) ↔ p^3 ∣ OeisA7406.a t := by
    let n := (t+1)*p-1
    have hn : 0 < n := by dsimp [n]; nlinarith [Nat.sub_add_cancel (by nlinarith : 1 ≤ (t+1)*p)]
    have hq : n/p = t := by
      have he : n = t*p+(p-1) := by dsimp [n]; rw [Nat.add_mul,one_mul]; omega
      rw [he,Nat.mul_comm t p,Nat.mul_add_div (by omega : 0 < p), Nat.div_eq_of_lt (by omega : p-1 < p),add_zero]
    have hr := full_res hp (q:=t+1) (by omega)
    change Res (rem n) 0 at hr
    have hnum (j : ℕ) (hj : 0 < j) (e : ℕ) (he : 0 < e) :
        p^e ∣ OeisA7406.a j ↔ (e:ℤ) ≤ padicValRat p (h j) :=
      val_num_iff (h_pos hj).ne' he
    change p ∣ OeisA7406.a n ↔ _
    rw [← pow_one p, hnum n hn 1 (by decide), pow_one, hnum t ht 3 (by decide)]
    push_cast
    have hqt : 0 < n/p := hq ▸ ht
    by_cases hz : rem n = 0
    · rw [val_split hn hqt (Or.inr hz),hq]; omega
    have hv := positive_of_res_zero hz hr
    by_cases large : 3 ≤ padicValRat p (h t)
    · simp only [large, iff_true]
      have eq : h n = h t/(p:ℚ)^2 + rem n := by unfold rem; rw [hq]; ring
      have low := padicValRat.min_le_padicValRat_add (p:=p) (eq ▸ (h_pos hn).ne')
      rw [val_scale ht] at low
      rw [eq]
      exact le_trans (le_min (by omega) (by omega)) low
    · rw [val_split hn hqt (Or.inl (by rw [hq]; omega)), hq]
      omega
  have small_bound (hp : p ≤ 2047) (h7 : p ≠ 7) (n : ℕ) (hn : 0 < n) :
      padicValRat p (h n) ≤ if p ≤ 3 then 0 else 1 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hnp : n < p
      · by_cases h3 : p ≤ 3
        · rw [if_pos h3]
          have pp : p.Prime := Fact.out
          interval_cases p <;> interval_cases n <;> decide +kernel
        · rw [if_neg h3]
          have hh := first_bound (Fact.out : p.Prime) hp h7 hn hnp
          have no := (val_num_iff (h_pos hn).ne' (e:=2) (by decide)).not.mp hh
          omega
      have pp : p.Prime := Fact.out
      have ht := Nat.div_pos (by omega : p ≤ n) pp.pos
      have hh := ih (n/p) (Nat.div_lt_self hn pp.one_lt) ht
      rw [drop_two ht (by split at hh <;> omega)]
      omega

  have seven_table : ∀ n : Fin 49, 0 < n.val →
      padicValRat 7 (h n.val) ≤ if n.val < 7 then 2 else 1 := by
    decide +kernel

  have seven_bound (eq7 : p = 7) (n : ℕ) (hn : 0 < n) :
      padicValRat 7 (h n) ≤ if n < 7 then 2 else 1 := by
    subst p
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hs : n < 49
      · exact seven_table ⟨n,hs⟩ hn
      have h7 := ih (n/7) (by omega) (by omega)
      rw [if_neg (by omega)] at h7 ⊢
      rw [drop_two (by omega : 0 < n/7) (by omega)]
      omega
  refine ⟨prime_index, fun hp t ht => prime_cube_iff hp ht, ?_, ?_⟩
  · intro hp t ht
    have ht' := (h_pos ht).ne'
    constructor
    · intro cube
      have hv := (val_num_iff ht' (e:=3) (by decide)).mp cube
      by_cases h7 : p = 7
      · have hh := seven_bound h7 t ht
        rw [h7] at hv
        split at hh <;> omega
      · have hh := small_bound hp h7 t ht
        split at hh <;> omega
    · intro h3 hd
      have hv := (val_num_iff ht' (e:=1) (by decide)).mp (by simpa [h,OeisA7406.a] using hd)
      have hh := small_bound hp (by omega) t ht
      rw [if_pos h3] at hh
      omega
  · intro t hpt cube
    have hp : p.Prime := Fact.out
    have ht : 0 < t := hp.pos.trans_le hpt
    have hq := Nat.div_pos hpt hp.pos
    have hv := (val_num_iff (h_pos ht).ne' (e:=3) (by decide)).mp cube
    apply (val_num_iff (h_pos hq).ne' (e:=2) (by decide)).mpr
    by_contra! low
    have eq := drop_two hq low
    omega

theorem prime_cube_iff {p : ℕ} [Fact p.Prime] (hp : 3 < p) {t : ℕ} (ht : 0 < t) :
    p ∣ OeisA7406.a ((t+1)*p-1) ↔ p^3 ∣ OeisA7406.a t :=
  local_data.2.1 hp t ht

end SquareHarmonic

namespace OMA.R_OeisA7406_conjecture_R2

open SquareHarmonic

/-- Check the nonzero prefixes consisting of a single base-p digit. -/
def H1 : Prop := ∀ p : ℕ, p.Prime → 2047 < p → ∀ t : ℕ, 0 < t → t < p →
  ¬ p^3 ∣ OeisA7406.a t

/-- Only parents whose numerator contains p² can have a child containing p³. -/
def H2 : Prop := ∀ p : ℕ, p.Prime → 2047 < p → ∀ t : ℕ, 0 < t → p^2 ∣ OeisA7406.a t →
  ∀ r : ℕ, r < p → ¬ p^3 ∣ OeisA7406.a (t*p+r)

theorem no_cube (root : H1) (child : H2) {p : ℕ} [Fact p.Prime]
    (t : ℕ) (ht : 0 < t) : ¬ p^3 ∣ OeisA7406.a t := by
  have hp : p.Prime := Fact.out
  by_cases small : p ≤ 2047
  · exact (local_data.2.2.1 small t ht).1
  by_cases digit : t < p
  · exact root p hp (by omega) t ht digit
  intro cube
  have hpt : p ≤ t := by omega
  have square := local_data.2.2.2 t hpt cube
  have nc := child p hp (by omega) (t/p) (Nat.div_pos hpt hp.pos) square (t%p) (Nat.mod_lt t hp.pos)
  rw [Nat.div_add_mod' t p] at nc
  exact nc cube

theorem main : H1 → H2 → type_of% @OeisA7406.conjecture := by
  intro root child n hn
  rw [OeisA89026.a]
  by_cases prime : n.Prime
  · rw [if_pos prime]
    let _ : Fact n.Prime := ⟨prime⟩
    exact Nat.gcd_eq_left (local_data.1 hn)
  rw [if_neg prime]
  apply Nat.coprime_iff_gcd_eq_one.mp
  apply Nat.coprime_of_dvd
  intro p hp hpn hpa
  let _ : Fact p.Prime := ⟨hp⟩
  by_cases small : p ≤ 3
  · exact (local_data.2.2.1 (by omega : p ≤ 2047) (n-1) (by omega)).2 small hpa
  obtain ⟨q, eq⟩ := hpn
  have hq : 1 < q := by
    by_contra! bad
    interval_cases q <;> simp_all
  have rep : n = ((q-1)+1)*p := by rw [Nat.sub_add_cancel (by omega),Nat.mul_comm]; exact eq
  rw [rep] at hpa
  exact no_cube root child (q-1) (by omega) ((prime_cube_iff (by omega : 3 < p) (by omega)).mp hpa)

/-- Each outstanding cube would give a composite counterexample at (t+1)p. -/
theorem necessary (original : type_of% @OeisA7406.conjecture) {p : ℕ}
    (hp : p.Prime) (hgt : 3 < p) {t : ℕ} (ht : 0 < t) : ¬ p^3 ∣ OeisA7406.a t := by
  let _ : Fact p.Prime := ⟨hp⟩
  intro cube
  have hc := (prime_cube_iff hgt ht).mpr cube
  have hn : 3 < (t+1)*p := by nlinarith
  have comp : ¬ ((t+1)*p).Prime := Nat.not_prime_mul (by omega) hp.ne_one
  have eq := original ((t+1)*p) hn
  rw [OeisA89026.a,if_neg comp] at eq
  apply hp.not_dvd_one
  rw [← eq]
  exact Nat.dvd_gcd (dvd_mul_left p (t+1)) hc

theorem equivalent : (type_of% @OeisA7406.conjecture) ↔ H1 ∧ H2 := by
  refine ⟨fun all => ⟨?_, ?_⟩, fun hh => main hh.1 hh.2⟩
  · intro p hp big t ht _
    exact necessary all hp (by omega) ht
  · intro p hp big t ht _ r _
    exact necessary all hp (by omega) (Nat.add_pos_left (Nat.mul_pos ht hp.pos) r)

end OMA.R_OeisA7406_conjecture_R2
