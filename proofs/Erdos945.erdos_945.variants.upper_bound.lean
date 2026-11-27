import FormalConjectures.ErdosProblems.«945»

/-! # An upper bound for a run of distinct divisor counts

Discard positions divisible by a square of a small prime. In each remaining
integer, a prime with large valuation must itself be large. Only a bounded
number of such primes fit in its factorization. The remaining valuations can
be recorded by their multiplicities.
-/
open Finset Filter Real
open Erdos945
namespace EU945

private lemma ap_card (b B d T : ℕ) (hc : d.Coprime B) :
    ((range T).filter fun t => d ∣ B*t+b).card ≤ T/d+1 := by
  have h := Finset.card_le_card_of_injOn (s := (range T).filter fun t => d ∣ B*t+b)
      (t := range (T/d+1)) (fun t => t/d) (by
        intro t ht
        have ht' := mem_range.mp (mem_filter.mp ht).1
        exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt ht')))) (by
        intro u hu v hv he
        have hm := (Nat.modEq_zero_iff_dvd.mpr (mem_filter.mp hu).2).trans
          (Nat.modEq_zero_iff_dvd.mpr (mem_filter.mp hv).2).symm
        have hr : u % d = v % d := Nat.ModEq.cancel_left_of_coprime hc
          (Nat.ModEq.add_right_cancel' b hm)
        change u/d = v/d at he
        have h1 := Nat.div_add_mod u d
        have h2 := Nat.div_add_mod v d
        rw [he, hr] at h1
        omega)
  simpa using h


private def values (H T : ℕ) : Finset ℕ :=
  (univ : Finset ((Fin T → Fin (H+1)) × Fin ((H+1)^T+1))).image
    (fun w => (∏ j : Fin T, (j.val+1) ^ (w.1 j).val) * w.2.val)

private lemma mem_values {m N : ℕ} (hm : 2 ≤ m) (hN : N ≠ 0) (hmax : N ≤ 2^(m^8))
    (hgood : ∀ q ∈ Ioc 1 (2^(m^2)), ¬q^2 ∣ N) : τ N ∈ values (m^8) (m^3) := by
  classical
  let H := m^8
  let T := m^3
  let e (p : ℕ) := N.factorization p
  let S := N.primeFactors
  let lo := S.filter fun p => e p < T
  let hi := S.filter fun p => ¬e p < T
  have hT : 2 ≤ T := by dsimp [T]; nlinarith [sq_nonneg (m-2:ℤ)]
  have hprod : (∏ p ∈ S, p^(e p)) = N := (Nat.prod_primeFactors_pow_factorization hN).symm
  have hp (p) (h : p ∈ S) := (Nat.mem_primeFactors.mp h).1
  have hepos (p) (h : p ∈ S) : 1 ≤ e p := ((hp p h).dvd_iff_one_le_factorization hN).mp (Nat.mem_primeFactors.mp h).2.1
  have hcard : S.card ≤ H := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    calc
      2^S.card = ∏ _ ∈ S, 2 := by simp
      _ ≤ ∏ p ∈ S, p^(e p) := Finset.prod_le_prod' (fun p h => (hp p h).two_le.trans (Nat.le_self_pow (by have := hepos p h; omega) _))
      _ ≤ _ := hprod.le.trans hmax
  have hval (p) (h : p ∈ S) : e p ≤ H := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    calc
      2^(e p) ≤ p^(e p) := Nat.pow_le_pow_left (hp p h).two_le _
      _ ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (Nat.ordProj_dvd _ _)
      _ ≤ _ := hmax
  have hhi : hi.card ≤ T := by
    have ha (p) (h : p ∈ hi) : 2^(m^2*T) ≤ p^e p := by
      obtain ⟨hpS,hpt⟩ := mem_filter.mp h
      have hbig : 2^(m^2) ≤ p := by
        by_contra! h
        exact hgood p (mem_Ioc.mpr ⟨(hp p hpS).one_lt,h.le⟩)
          (((hp p hpS).pow_dvd_iff_le_factorization hN).mpr (show 2 ≤ e p by omega))
      rw [pow_mul]
      exact (Nat.pow_le_pow_left hbig T).trans (Nat.pow_le_pow_right (hp p hpS).pos (by omega))
    have hpow : 2^(m^2*T*hi.card) ≤ 2^H := calc
      _ = ∏ _ ∈ hi, 2^(m^2*T) := by rw [prod_const,pow_mul]
      _ ≤ ∏ p ∈ hi, p^e p := Finset.prod_le_prod' ha
      _ ≤ ∏ p ∈ S, p^e p := Finset.prod_le_prod_of_subset_of_one_le (filter_subset _ _) (by intros; exact Nat.zero_le _) (by intro p h _; exact Nat.one_le_pow _ _ (hp p h).pos)
      _ ≤ _ := hprod.le.trans hmax
    have hh := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
    have hH : H = m^2*T*T := by dsimp [H,T]; ring
    rw [hH] at hh
    exact Nat.le_of_mul_le_mul_left hh (by dsimp [T]; positivity)
  let c (j : ℕ) := (lo.filter (fun p => e p = j)).card
  have hc (j) : c j ≤ H := (card_le_card (filter_subset _ _)).trans
    ((card_le_card (filter_subset _ _)).trans hcard)
  let v := ∏ p ∈ hi, (e p+1)
  have hv : v ≤ (H+1)^T := calc
    _ ≤ ∏ _ ∈ hi, (H+1) := Finset.prod_le_prod' (fun p h => Nat.succ_le_succ (hval p (mem_filter.mp h).1))
    _ = (H+1)^hi.card := by simp
    _ ≤ _ := Nat.pow_le_pow_right (by omega) hhi
  let w (j : Fin T) : Fin (H+1) := ⟨c j,by have := hc j; omega⟩
  refine mem_image.mpr ⟨(w, (⟨v,by omega⟩ : Fin ((H+1)^T+1))),mem_univ _,?_⟩
  change (∏ j : Fin T, (j.val+1) ^ c j.val) * v = τ N
  rw [Fin.prod_univ_eq_prod_range (fun j => (j+1)^c j)]
  have hlow := Finset.prod_fiberwise_of_maps_to' (s := lo) (t := range T) (g := e)
    (fun p h => mem_range.mpr (mem_filter.mp h).2) (fun j => j+1)
  simp only [prod_const] at hlow
  rw [show (∏ j ∈ range T, (j+1)^c j) = ∏ p ∈ lo, (e p + 1) from hlow,
    Erdos945.τ,Nat.card_divisors hN]
  exact prod_filter_mul_prod_filter_not _ _ _

private lemma squares (y : ℕ) (hy : 2 ≤ y) :
    (∑ q ∈ Ioc 1 y, ((q:ℝ)^2)⁻¹) ≤ 3/4 := by
  have hs : Ioc 1 y = insert 2 (Ioc 2 y) := by ext q; simp; omega
  rw [hs,sum_insert (by simp)]
  have h := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 2) (n := y) (by decide) hy
  norm_num at h ⊢
  linarith [inv_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) y)]

private lemma finite_bound {m n k : ℕ} (hm : 2 ≤ m) (hmax : n+k ≤ 2^(m^8))
    (hinj : (Set.Ioc n (n+k)).InjOn τ) :
    k ≤ 4*((m^8+1)^(m^3) * ((m^8+1)^(m^3)+1) + 2^(m^2)) := by
  classical
  let Y := 2^(m^2)
  let badq (q : ℕ) := (range k).filter fun t => q^2 ∣ t+(n+1)
  let bad := (Ioc 1 Y).biUnion badq
  let good := range k \ bad
  have hb : (bad.card : ℝ) ≤ (k:ℝ)*(3/4) + Y := by
    have hq (q) : ((badq q).card:ℝ) ≤ (k:ℝ)*((q:ℝ)^2)⁻¹+1 := by
      have h := ap_card (n+1) 1 (q^2) k (by simp)
      simp only [one_mul] at h
      calc
        _ ≤ ((k/(q^2) + 1 : ℕ):ℝ) := by exact_mod_cast h
        _ ≤ _ := by push_cast; rw [← div_eq_mul_inv]; gcongr; exact_mod_cast (Nat.cast_div_le (α:=ℝ) (m:=k) (n:=q^2))
    calc
      _ ≤ ∑ q ∈ Ioc 1 Y, ((badq q).card:ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ q ∈ Ioc 1 Y, ((k:ℝ)*((q:ℝ)^2)⁻¹+1) := sum_le_sum (fun q _ => hq q)
      _ ≤ _ := by
        rw [sum_add_distrib,←mul_sum]
        simp only [sum_const,nsmul_eq_mul,mul_one,Nat.card_Ioc]
        exact add_le_add (mul_le_mul_of_nonneg_left (squares Y (Nat.le_self_pow (by positivity) _)) (by positivity)) (by exact_mod_cast Nat.sub_le Y 1)
  have hg : good.card ≤ (values (m^8) (m^3)).card := by
    apply card_le_card_of_injOn (fun t => τ (t+(n+1)))
    · intro t ht
      obtain ⟨ht1,ht2⟩ := mem_sdiff.mp ht
      have ht3 := mem_range.mp ht1
      exact mem_values hm (by omega) (by omega) (fun q hq hd =>
        ht2 (mem_biUnion.mpr ⟨q,hq,mem_filter.mpr ⟨ht1,hd⟩⟩))
    · intro t ht u hu he
      have ht0 := mem_range.mp (mem_sdiff.mp ht).1
      have hu0 := mem_range.mp (mem_sdiff.mp hu).1
      have h := hinj (x₁ := t+(n+1)) ⟨by omega,by omega⟩ (x₂ := u+(n+1)) ⟨by omega,by omega⟩ he
      omega
  have hcard : (values (m^8) (m^3)).card ≤ (m^8+1)^(m^3)*((m^8+1)^(m^3)+1) := by
    simpa [values] using (card_image_le (s := (univ : Finset ((Fin (m^3) → Fin (m^8+1)) × Fin ((m^8+1)^(m^3)+1))))
      (f := fun w => (∏ j : Fin (m^3), (j.val+1) ^ (w.1 j).val) * w.2.val))
  have hpart := Finset.card_le_card_sdiff_add_card (s := range k) (t := bad)
  change (range k).card ≤ good.card + bad.card at hpart
  rw [card_range] at hpart
  have hr : (k:ℝ) ≤ ((m^8+1:ℕ):ℝ)^(m^3)*(((m^8+1:ℕ):ℝ)^(m^3)+1)+bad.card := by
    exact_mod_cast hpart.trans (Nat.add_le_add_right (hg.trans hcard) _)
  change k ≤ 4*((m^8+1)^(m^3) * ((m^8+1)^(m^3)+1) + Y)
  exact_mod_cast (show (k:ℝ) ≤ 4*(((m^8+1:ℕ):ℝ)^(m^3)*(((m^8+1:ℕ):ℝ)^(m^3)+1)+Y) by linarith)
private lemma global_bound {x m : ℕ} (hm : 2 ≤ m) (hx : x ≤ 2^(m^8)) :
    F x ≤ 12*((m^8+1)^(m^3))^2 := by
  apply csSup_le
  · exact ⟨0,0,by simp,by simp⟩
  · rintro k ⟨n,hn,hinj⟩
    let A := (m^8+1)^(m^3)
    have hA : 1 ≤ A := Nat.one_le_pow _ _ (by omega)
    have hm8 : 0 < m^8 := pow_pos (by omega) _
    have hY : 2^(m^2) ≤ A := by
      apply (Nat.pow_le_pow_left (show 2 ≤ m^8+1 by omega) _).trans
      apply Nat.pow_le_pow_right (by positivity)
      exact Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 3)
    have hn' : n+k ≤ x := by exact_mod_cast hn
    have h := finite_bound hm (hn'.trans hx) hinj
    change k ≤ 4*(A*(A+1)+2^(m^2)) at h
    change k ≤ 12*A^2
    nlinarith

end EU945

theorem OMA.solution : type_of% @Erdos945.erdos_945.variants.upper_bound := by
  apply Asymptotics.IsBigO.of_bound 30000
  filter_upwards [eventually_ge_atTop (16:ℕ)] with x hx
  have hx0 : (0:ℝ)<x := by exact_mod_cast (show 0 < x by omega)
  have hx16 : (16:ℝ) ≤ x := by exact_mod_cast hx
  have hex : ∃ m : ℕ, x ≤ 2^(m^8) := ⟨x, (Nat.le_of_lt (Nat.lt_two_pow_self : x < 2^x)).trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_self_pow (by decide) _))⟩
  let m := Nat.find hex
  have hmmax : x ≤ 2^(m^8) := Nat.find_spec hex
  have hm : 2 ≤ m := by
    by_contra! hh
    interval_cases m <;> norm_num at hmmax <;> omega
  have hprev : 2^((m-1)^8) < x := lt_of_not_ge (Nat.find_min hex (show m-1 < m by omega))
  have hm2 : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by linarith
  have hlogm := Real.log_pos (by linarith : 1 < (m:ℝ))
  have hlogx := Real.log_pos (by linarith : 1 < (x:ℝ))
  have hlog2 : 1/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2' : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hsmall : log x ≤ (m:ℝ)^8 := by
    have h := Real.log_le_log hx0 (show (x:ℝ) ≤ (2:ℝ)^(m^8) by exact_mod_cast hmmax)
    rw [log_pow,Nat.cast_pow] at h
    nlinarith [mul_le_mul_of_nonneg_left hlog2' (show 0 ≤ (m:ℝ)^8 by positivity)]
  have hlarge : (m:ℝ)^4 ≤ 32 * √(log x) := by
    have h := Real.log_lt_log (by positivity : 0 < (2:ℝ)^((m-1)^8))
      (show (2:ℝ)^((m-1)^8) < x by exact_mod_cast hprev)
    rw [log_pow,Nat.cast_pow,Nat.cast_sub (by omega : 1 ≤ m),Nat.cast_one] at h
    have ht : ((m:ℝ)/2)^8 ≤ ((m:ℝ)-1)^8 := pow_le_pow_left₀ (by positivity) (by linarith) _
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith only [ht,h, mul_le_mul_of_nonneg_left hlog2 (by positivity : 0 ≤ ((m:ℝ)-1)^8),
      Real.sq_sqrt hlogx.le,hlogx]
  have hll : log (log x) ≤ 8 * log m := by
    simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log hlogx hsmall
  have hlpos : 0 < log (log x) := by
    apply Real.log_pos
    have h := Real.log_le_log (by norm_num : (0:ℝ)<16) hx16
    have h16 := Real.log_pow (2:ℝ) 4
    norm_num at h16
    linarith
  have hsquare : (log m)^2 ≤ 4*(m:ℝ) := by
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hm0)
    rw [Real.log_sqrt hm0.le] at h
    have hh := pow_le_pow_left₀ hlogm.le (by linarith : log m ≤ 2*√(m:ℝ)) 2
    nlinarith [Real.sq_sqrt hm0.le]
  have hhF : log (F x) ≤ 22*(m:ℝ)^3*log m := by
    by_cases h0 : F x = 0
    · simp only [h0,Nat.cast_zero,Real.log_zero]
      positivity
    have h := Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero h0 : (0:ℝ) < F x)
      (show (F x:ℝ) ≤ 12*(((m:ℝ)^8+1)^(m^3))^2 by exact_mod_cast EU945.global_bound hm hmmax)
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow,Real.log_pow,Nat.cast_pow] at h
    have ht : (m:ℝ)^8+1 ≤ (m:ℝ)^9 := by
      have h8 : 1 ≤ (m:ℝ)^8 := one_le_pow₀ (by linarith)
      nlinarith [mul_le_mul_of_nonneg_right hm2 (show 0 ≤ (m:ℝ)^8 by positivity)]
    have h9 := Real.log_le_log (by positivity) ht
    rw [Real.log_pow] at h9
    have h12 : log 12 ≤ 4*log m := by
      have hh : (12:ℝ) ≤ (m:ℝ)^4 := (by norm_num : (12:ℝ) ≤ 2^4).trans (pow_le_pow_left₀ (by norm_num) hm2 _)
      simpa only [Real.log_pow,Nat.cast_ofNat] using Real.log_le_log (by norm_num) hh
    have h1 : 1 ≤ (m:ℝ)^3 := one_le_pow₀ (by linarith)
    norm_num at h h9
    nlinarith [mul_le_mul_of_nonneg_left h9 (show 0 ≤ (m:ℝ)^3 by positivity),
      mul_le_mul_of_nonneg_right h1 hlogm.le]
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg (F x)),
    abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hlpos.le)]
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hlpos).2
  have hmul := mul_le_mul hhF hll hlpos.le (by positivity)
  nlinarith [Real.sqrt_nonneg (log x), mul_le_mul_of_nonneg_left hsquare (show 0 ≤ (m:ℝ)^3 by positivity)]

