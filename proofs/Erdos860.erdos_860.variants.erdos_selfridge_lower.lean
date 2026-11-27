import FormalConjectures.ErdosProblems.«860»
/-! A Chinese remainder construction forces all eligible multiples into two small sets. -/
open Finset Filter Erdos860
namespace PrimeMatching

def primes (k : ℕ) := (Ico (k^4) ((k+1)^4)).filter Nat.Prime

lemma often_many : ∃ᶠ k : ℕ in atTop, 20*k^2 < (primes k).card := by
  by_contra! h
  obtain ⟨K,hK⟩ := eventually_atTop.mp h
  let f : ℕ → ℝ := {p : ℕ | p.Prime}.indicator (fun n => (1:ℝ)/n)
  let F := fun k => ∑ p ∈ primes k,(1:ℝ)/p
  have pos (j) : 0 ≤ f j := by simp only [f,Set.indicator_apply]; split_ifs <;> positivity
  have block (k) : ∑ p ∈ Ico (k^4) ((k+1)^4),f p = F k := by
    simp [f,F,primes,sum_filter,Set.indicator_apply]
  have summ : Summable F := by
    apply Summable.of_norm_bounded_eventually (hasSum_zeta_two.summable.mul_left (20:ℝ))
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop K,eventually_ge_atTop 1] with k hk hk1
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ F k by dsimp [F]; positivity)]
    calc
      F k ≤ ∑ p ∈ primes k, (1:ℝ)/(k:ℝ)^4 := by
        apply sum_le_sum; intro p hp
        exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (mem_Ico.mp (mem_filter.mp hp).1).1)
      _ ≤ (20*(k:ℝ)^2)*(1/(k:ℝ)^4) := by
        simp only [sum_const,nsmul_eq_mul]; gcongr; exact_mod_cast hK k hk
      _ = _ := by field_simp
  have blocks (t : ℕ) : ∑ i ∈ range (t^4), f i = ∑ j ∈ range t,F j := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Finset.sum_range_succ,← ih,← block,Finset.sum_range_add_sum_Ico f (Nat.pow_le_pow_left (by omega) _)]
  apply not_summable_one_div_on_primes
  apply summable_of_sum_range_le pos (c := ∑' k,F k)
  intro k
  have hle : k ≤ k^4 := by nlinarith only [Nat.le_self_pow (by decide : 4≠0) k]
  exact (sum_le_sum_of_subset_of_nonneg (range_mono hle) (fun i _ _ => pos i)).trans
    ((blocks k).le.trans (summ.sum_le_tsum _ (fun i _ => by dsimp [F]; positivity)))

lemma h_spec (n : ℕ) : ∀ m, 1 ≤ m → HasPrimeMultiples n m (h n) := by
  apply Nat.sInf_mem (s := {L : ℕ | ∀ m, 1 ≤ m → HasPrimeMultiples n m L})
  refine ⟨n * n.primeCounting + 1,fun m hm => ?_⟩
  let p := fun i : Fin n.primeCounting => Nat.nth Nat.Prime i.val
  let g := fun i : Fin n.primeCounting => ((m+i.val*n)/p i+1)*p i
  have interval (i) : m+i.val*n < g i ∧ g i ≤ m+(i.val+1)*n := by
    have hp := (Nat.prime_nth_prime i.val).pos
    change 0 < p i at hp
    have hpn : p i ≤ n := Nat.lt_succ_iff.mp (Nat.nth_lt_of_lt_count (n := n+1) i.isLt)
    have h1 := Nat.div_add_mod (m+i.val*n) (p i)
    have h2 := Nat.mod_lt (m+i.val*n) hp
    dsimp only [g]; rw [Nat.add_mul,one_mul,Nat.add_mul,one_mul,Nat.mul_comm ((m+i.val*n)/p i)]
    omega
  refine ⟨g,?_,fun i => ⟨by have := (interval i).1; omega,?_,dvd_mul_left ..⟩⟩
  · apply StrictMono.injective
    intro i j hij
    exact ((interval i).2.trans (Nat.add_le_add_left (Nat.mul_le_mul_right n hij) m)).trans_lt (interval j).1
  · have := (interval i).2.trans (Nat.add_le_add_left (Nat.mul_le_mul_right n i.isLt) m)
    rw [Nat.mul_comm n]; omega

lemma only_two {p x a : ℕ} (hx : 0 < x) (ha : a ≤ p) (hb : x < a+2*p)
    (hm : x ≡ a [MOD p]) : x=a ∨ x=a+p := by
  by_cases h : x < a
  · have hd := (Nat.modEq_iff_dvd' h.le).mp hm
    have := Nat.le_of_dvd (by omega : 0 < a-x) hd
    omega
  obtain ⟨j,hj⟩ := (Nat.modEq_iff_dvd' (by omega : a ≤ x)).mp hm.symm
  rcases j with _ | j
  · simp at hj; omega
  rcases j with _ | j
  · simp at hj; omega
  have he := Nat.mul_le_mul_left p (show 2 ≤ j+1+1 by omega)
  omega

lemma obstruction (k : ℕ) (hk : 1 ≤ k) (many : 20*k^2 < (primes k).card) :
    3*k^4-k^2 ≤ h ((k+1)^4) := by
  classical
  let n := (k+1)^4
  let A := primes k
  let L := 3*k^4-k^2
  let first := fun p : ℕ => k^4-p%k^2
  have hk2 : 0<k^2 := by positivity
  have h4 : k^2 ≤ k^4 := Nat.pow_le_pow_right hk (by decide : 2 ≤ 4)
  have props {p : ℕ} (hp : p ∈ A) : p.Prime ∧ k^4 ≤ p ∧ p<n := by
    obtain ⟨hh,pr⟩ := mem_filter.mp hp
    exact ⟨pr,mem_Ico.mp hh⟩
  have fst_le {p} (hp : p ∈ A) : first p ≤ p := (Nat.sub_le ..).trans (props hp).2.1
  let prodP := ∏ p ∈ A,p
  have hprod : 0 < prodP := prod_pos (fun p hp => (props hp).1.pos)
  let crt := Nat.chineseRemainderOfFinset (fun p => p-first p) id A (fun p hp => (props hp).1.ne_zero)
    (fun p hp q hq hn => (Nat.coprime_primes (props hp).1 (props hq).1).mpr hn)
  let m := crt.val+prodP
  have modm {p} (hp : p ∈ A) : p ∣ m+first p := by
    have hh := (crt.property p hp).add (dvd_prod_of_mem id hp).modEq_zero_nat
    change crt.val+prodP ≡ (p-first p)+0 [MOD p] at hh
    have eq := (hh.add_right (first p))
    rw [Nat.add_zero,Nat.sub_add_cancel (fst_le hp)] at eq
    exact Nat.modEq_zero_iff_dvd.mp (eq.trans (dvd_refl p).modEq_zero_nat)
  by_contra! hsmall
  obtain ⟨a,inj,ha⟩ := h_spec n m (by dsimp [m]; omega)
  let idx := fun p : A => (⟨Nat.count Nat.Prime p.val, (Nat.count_lt_count_succ_iff.mpr
    (props p.property).1).trans_le (Nat.count_monotone Nat.Prime (by have := (props p.property).2.2; omega :
      p.val+1 ≤ n+1))⟩ : Fin n.primeCounting)
  let z := fun p : A => a (idx p)-m
  let cut := ((range (k^2)).image (fun r => k^4-r)) ∪
    ((range (16*k^2)).image (fun s => k^4+k^2*s))
  have cut_card : cut.card ≤ 17*k^2 := by
    apply (card_union_le ..).trans
    have h1 := card_image_le (s := range (k^2)) (f := fun r => k^4-r)
    have h2 := card_image_le (s := range (16*k^2)) (f := fun s => k^4+k^2*s)
    simp only [card_range] at h1 h2; omega
  have hinj : Function.Injective z := by
    intro p q heq
    have h1 := (ha (idx p)).1
    have h2 := (ha (idx q)).1
    have hh : a (idx p)=a (idx q) := by dsimp [z] at heq; omega
    have hh' := congrArg (fun i : Fin n.primeCounting => Nat.nth Nat.Prime i.val) (inj hh)
    exact Subtype.ext (by simpa [idx,Nat.nth_count (props p.property).1,Nat.nth_count (props q.property).1] using hh')
  have in_cut (v : A) : z v ∈ cut := by
    let p := v.val
    have hp : p ∈ A := v.property
    have hb := props hp
    obtain ⟨hl,hu,hd⟩ := ha (idx v)
    have hprime : Nat.nth Nat.Prime (idx v).val = p := Nat.nth_count hb.1
    rw [hprime] at hd
    have hz : z v + m = a (idx v) := Nat.sub_add_cancel hl.le
    have hmod : z v ≡ first p [MOD p] := by
      exact Nat.ModEq.add_left_cancel (Nat.ModEq.refl m)
        (by simpa [Nat.add_comm m (z v),hz] using hd.modEq_zero_nat.trans (modm hp).zero_modEq_nat)
    have hr := Nat.mod_lt p hk2
    have hf : first p + p%k^2=k^4 := Nat.sub_add_cancel (hr.le.trans h4)
    have hbound : z v < first p+2*p := by
      change h n < 3*k^4-k^2 at hsmall
      omega
    rcases only_two (x := z v) (by dsimp [z]; omega) (fst_le hp) hbound hmod with hx | hx
    · exact mem_union_left _ (mem_image.mpr ⟨p%k^2,mem_range.mpr hr,hx.symm⟩)
    · have hpn : p < (16*k^2)*k^2 := by
        have he : (k+1)^4 ≤ (2*k)^4 := Nat.pow_le_pow_left (by omega) 4
        have hh : (2*k)^4 = (16*k^2)*k^2 := by ring
        exact hb.2.2.trans_le (he.trans_eq hh)
      refine mem_union_right _ (mem_image.mpr ⟨p/k^2,mem_range.mpr ((Nat.div_lt_iff_lt_mul hk2).mpr hpn),?_⟩)
      have hh := Nat.div_add_mod p (k^2)
      omega
  have cc := card_le_card_of_injOn z (s := univ) (t := cut) (fun p _ => in_cut p) hinj.injOn
  simp only [card_univ,Fintype.card_coe] at cc
  change 20*k^2 < A.card at many
  omega

end PrimeMatching

theorem OMA.solution : type_of% @Erdos860.erdos_860.variants.erdos_selfridge_lower := by
  intro ε hε
  obtain ⟨K,hK⟩ := exists_nat_gt (46 / ε)
  apply frequently_atTop.mpr
  intro b
  obtain ⟨k,hk,hmany⟩ := frequently_atTop.mp PrimeMatching.often_many (max (max 1 b) K)
  have hk1 : 1 ≤ k := by omega
  have hkb : b ≤ k := by omega
  have hreal : (1:ℝ) ≤ k := by exact_mod_cast hk1
  have hlarge : 46 ≤ ε*(k:ℝ) := by
    have hlt := (div_lt_iff₀ hε).mp (hK.trans_le (show (K:ℝ) ≤ (k:ℝ) by exact_mod_cast (show K ≤ k by omega)))
    linarith
  refine ⟨(k+1)^4,hkb.trans ((Nat.le_succ k).trans (Nat.le_self_pow (by decide) _)),?_⟩
  have ho := PrimeMatching.obstruction k hk1 hmany
  have h4 := Nat.pow_le_pow_right hk1 (by decide : 2 ≤ 4)
  have hs : k^2 ≤ 3*k^4 := by omega
  have hr : ((3*k^4-k^2 : ℕ):ℝ) ≤ h ((k+1)^4) := by exact_mod_cast ho
  apply le_trans _ hr
  rw [Nat.cast_sub hs]
  push_cast
  have h2 : (k:ℝ) ≤ (k:ℝ)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hreal) (show (0:ℝ) ≤ k by positivity)]
  have h3 : (k:ℝ)^2 ≤ (k:ℝ)^3 := by nlinarith [mul_le_mul_of_nonneg_right h2 (show (0:ℝ) ≤ k by positivity)]
  have hbound := mul_le_mul_of_nonneg_right hlarge (show (0:ℝ) ≤ (k:ℝ)^3 by positivity)
  have hmono := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show (0:ℝ) ≤ k by positivity)
    (show (k:ℝ) ≤ k+1 by linarith) 4) hε.le
  nlinarith only [hreal,h2,h3,hbound,hmono]
