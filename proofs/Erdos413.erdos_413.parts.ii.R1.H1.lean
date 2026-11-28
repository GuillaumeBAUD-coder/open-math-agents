import OMAReductions.R_Erdos413_erdos_413_parts_ii_R1
import Mathlib

/-!
# Proof of OMA.R_Erdos413_erdos_413_parts_ii_R1.H1

Omega-only specialization of Theorem 1.3 of C. F. Lau,
On the Number of Prime Factors of Consecutive Integers (arXiv:2604.15042, 2026):
there exist C > 0 and an infinite set S of natural numbers such that
for all n in S and 2 <= k < n, omega(n - k) <= C * log k.
-/

namespace Erdos413Moments
open Finset Real
open scoped BigOperators
noncomputable section
lemma w5 (n j:ℕ) :
    n.descFactorial j*n=n.descFactorial (j+1)+j*n.descFactorial j:=by
  by_cases hj:j≤ n
  · rw [Nat.descFactorial_succ]
    have hsub:n - j+j=n:=Nat.sub_add_cancel hj
    calc
      n.descFactorial j*n=n.descFactorial j*(n - j+j):=by rw [hsub]
      _=(n - j)*n.descFactorial j+j*n.descFactorial j:=by ring
  · push Not at hj
    have h1:n.descFactorial j=0:=Nat.descFactorial_eq_zero_iff_lt.mpr hj
    have h2:n.descFactorial (j+1)=0:=Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    rw [h1,h2]; simp
lemma yn (n s:ℕ) :
    n^s=∑ j∈Finset.range (s+1),Nat.stirlingSecond s j*n.descFactorial j:=by
  induction s with
  | zero=>simp
  | succ s ih =>
    rw [pow_succ,ih,sum_mul]
    have hrew:∀ j∈Finset.range (s+1),
        Nat.stirlingSecond s j*n.descFactorial j*n =
          Nat.stirlingSecond s j*n.descFactorial (j+1) +
          j*Nat.stirlingSecond s j*n.descFactorial j:=by
      intro j _
      rw [mul_assoc,w5]
      ring
    rw [sum_congr rfl hrew,sum_add_distrib]
    have h1:∑ j∈Finset.range (s+1),Nat.stirlingSecond s j*n.descFactorial (j+1) =
        ∑ j∈Finset.range (s+2),
          (if j=0 then 0 else Nat.stirlingSecond s (j - 1)*n.descFactorial j):=by
      symm
      rw [sum_range_succ']
      simp
    have h2:∑ j∈Finset.range (s+1),j*Nat.stirlingSecond s j*n.descFactorial j =
        ∑ j∈Finset.range (s+2),j*Nat.stirlingSecond s j*n.descFactorial j:=by
      symm
      rw [sum_range_succ,Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self s)]
      simp
    rw [h1,h2,← sum_add_distrib]
    refine sum_congr rfl fun j _=>?_
    cases j with
    | zero=>simp
    | succ j =>
      simp only [Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel,Nat.stirlingSecond_succ_succ]
      ring
lemma xa (m j:ℕ) :
    m.factorial*(m+j).descFactorial j=(m+j).factorial:=by
  induction j with
  | zero=>simp
  | succ j ih =>
    rw [show m+(j+1)=(m+j)+1 by omega]
    rw [Nat.succ_descFactorial_succ,Nat.factorial_succ]
    calc
      m.factorial*((m+j+1)*(m+j).descFactorial j)
          = (m+j+1)*(m.factorial*(m+j).descFactorial j):=by ring
      _=(m+j+1)*(m+j).factorial:=by rw [ih]
lemma yy (M:ℝ) :
    HasSum (fun m:ℕ=>M^m/ (m.factorial:ℝ)) (Real.exp M):=by
  rw [Real.exp_eq_exp_ℝ]
  simpa [div_eq_mul_inv,mul_comm] using NormedSpace.expSeries_div_hasSum_exp (𝔸:=ℝ) M
lemma ys (M:ℝ) (j:ℕ) :
    HasSum (fun n:ℕ=>(n.descFactorial j:ℝ)*(M^n/ (n.factorial:ℝ)))
      (M^j*Real.exp M):=by
  rw [← hasSum_nat_add_iff' j]
  have hzero:∑ i∈Finset.range j,(i.descFactorial j:ℝ)*(M^i/ (i.factorial:ℝ))=0:=by
    refine sum_eq_zero fun i hi=>?_
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr (Finset.mem_range.mp hi)]
    simp
  rw [hzero,sub_zero]
  have hterm:(fun m:ℕ=>((m+j).descFactorial j:ℝ)*(M^(m+j)/ ((m+j).factorial:ℝ))) =
      fun m:ℕ=>M^j*(M^m/ (m.factorial:ℝ)):=by
    ext m
    have hfac:(m.factorial:ℝ)*((m+j).descFactorial j:ℝ)=((m+j).factorial:ℝ):=by
      exact_mod_cast xa m j
    have hmne:(m.factorial:ℝ)≠0:=by positivity
    have hmj_ne:((m+j).factorial:ℝ)≠0:=by positivity
    rw [pow_add,← hfac]
    field_simp
  rw [hterm]
  exact (yy M).mul_left (M^j)
lemma wH (M:ℝ) (s:ℕ) :
    HasSum (fun n:ℕ=>(n:ℝ)^s*(M^n/ (n.factorial:ℝ)))
      ((∑ j∈Finset.range (s+1),(Nat.stirlingSecond s j:ℝ)*M^j)*Real.exp M):=by
  have hsum:HasSum (fun n:ℕ =>
      ∑ j∈Finset.range (s+1),
        (Nat.stirlingSecond s j:ℝ)*((n.descFactorial j:ℝ)*(M^n/ (n.factorial:ℝ))))
      (∑ j∈Finset.range (s+1),(Nat.stirlingSecond s j:ℝ)*(M^j*Real.exp M)) :=
    hasSum_sum fun j _=>(ys M j).mul_left _
  have hlhs:(fun n:ℕ =>
      ∑ j∈Finset.range (s+1),
        (Nat.stirlingSecond s j:ℝ)*((n.descFactorial j:ℝ)*(M^n/ (n.factorial:ℝ)))) =
      fun n:ℕ=>(n:ℝ)^s*(M^n/ (n.factorial:ℝ)):=by
    ext n
    have hcast:(n:ℝ)^s =
        ∑ j∈Finset.range (s+1),(Nat.stirlingSecond s j:ℝ)*(n.descFactorial j:ℝ):=by
      exact_mod_cast yn n s
    rw [hcast,sum_mul]
    refine sum_congr rfl fun j _=>by ring
  have hrhs:(∑ j∈Finset.range (s+1),(Nat.stirlingSecond s j:ℝ)*(M^j*Real.exp M)) =
      (∑ j∈Finset.range (s+1),(Nat.stirlingSecond s j:ℝ)*M^j)*Real.exp M:=by
    rw [sum_mul]
    refine sum_congr rfl fun j _=>by ring
  rwa [hlhs,hrhs] at hsum
lemma yo {M z:ℝ} (hM:0≤ M) (hz:0< z) (s:ℕ) :
    ∑ j∈Finset.range (s+1),(Nat.stirlingSecond s j:ℝ)*M^j ≤
      (s.factorial:ℝ)/ z^s*Real.exp (M*(Real.exp z - 1)):=by
  have h1:=(wH M s).mul_left (z^s/ (s.factorial:ℝ))
  have h2:=yy (M*Real.exp z)
  have hle_term:∀ n:ℕ,
      (z^s/ (s.factorial:ℝ))*((n:ℝ)^s*(M^n/ (n.factorial:ℝ))) ≤
        (M*Real.exp z)^n/ (n.factorial:ℝ):=by
    intro n
    have hpow:(z*(n:ℝ))^s/ (s.factorial:ℝ)≤ Real.exp (z*(n:ℝ)) :=
      Real.pow_div_factorial_le_exp _ (by positivity) s
    rw [mul_pow] at hpow
    have hrew:(z^s/ (s.factorial:ℝ))*((n:ℝ)^s*(M^n/ (n.factorial:ℝ))) =
        (z^s*(n:ℝ)^s/ (s.factorial:ℝ))*(M^n/ (n.factorial:ℝ)):=by ring
    rw [hrew]
    have hrhs_eq:(M*Real.exp z)^n/ (n.factorial:ℝ) =
        Real.exp (z*(n:ℝ))*(M^n/ (n.factorial:ℝ)):=by
      rw [mul_pow,← Real.exp_nat_mul,mul_comm (n:ℝ) z]; ring
    rw [hrhs_eq]
    exact mul_le_mul_of_nonneg_right hpow (by positivity)
  have hsum_le:(z^s/ (s.factorial:ℝ)) *
      ((∑ j∈Finset.range (s+1),(Nat.stirlingSecond s j:ℝ)*M^j)*Real.exp M) ≤
      Real.exp (M*Real.exp z) :=
    hasSum_le hle_term h1 h2
  have hpos:0< (z^s/ (s.factorial:ℝ))*Real.exp M:=by positivity
  have hB:(∑ j∈Finset.range (s+1),(Nat.stirlingSecond s j:ℝ)*M^j) *
      ((z^s/ (s.factorial:ℝ))*Real.exp M)≤ Real.exp (M*Real.exp z):=by
    linarith
  calc
    ∑ j∈Finset.range (s+1),(Nat.stirlingSecond s j:ℝ)*M^j
        ≤ Real.exp (M*Real.exp z)/ ((z^s/ (s.factorial:ℝ))*Real.exp M) :=
          (le_div_iff₀ hpos).mpr hB
    _=(s.factorial:ℝ)/ z^s*(Real.exp (M*Real.exp z)/ Real.exp M):=by
          have h1':z^s≠0:=by positivity
          have h2':(s.factorial:ℝ)≠0:=by positivity
          have h3':Real.exp M≠0:=(Real.exp_pos M).ne'
          field_simp
    _=(s.factorial:ℝ)/ z^s*Real.exp (M*(Real.exp z - 1)):=by
          rw [← Real.exp_sub]; congr 2; ring
lemma wc {s j:ℕ} (hs:3≤ s) (hj:j≤ s) :
    (Nat.stirlingSecond s j:ℝ)≤ (2*Real.exp 1*(s:ℝ)/ Real.log (s:ℝ))^s:=by
  have hlogs:0< Real.log (s:ℝ):=Real.log_pos (by exact_mod_cast (show 1< s by omega))
  have hz:0< (1/ 2 : ℝ)*Real.log (s:ℝ):=by positivity
  have hsingle:(Nat.stirlingSecond s j:ℝ) ≤
      ∑ i∈Finset.range (s+1),(Nat.stirlingSecond s i:ℝ)*(1 : ℝ)^i:=by
    have hmem:j∈Finset.range (s+1):=Finset.mem_range.mpr (by omega)
    simpa using single_le_sum (f:=fun i=>(Nat.stirlingSecond s i:ℝ)*(1 : ℝ)^i)
      (fun _ _=>by positivity) hmem
  refine hsingle.trans ((yo zero_le_one hz s).trans ?_)
  have hfac:(s.factorial:ℝ)≤ (s:ℝ)^s:=by exact_mod_cast Nat.factorial_le_pow s
  have hexp_half:Real.exp ((1/ 2 : ℝ)*Real.log (s:ℝ))≤ (s:ℝ):=by
    have hs_pos:(0 : ℝ)< s:=by positivity
    have h1:Real.exp ((1/ 2 : ℝ)*Real.log (s:ℝ))=Real.sqrt (s:ℝ):=by
      rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hs_pos,mul_comm]
    rw [h1]
    have hs1:(1 : ℝ)≤ s:=by exact_mod_cast (show 1≤ s by omega)
    calc Real.sqrt (s:ℝ)≤ Real.sqrt ((s:ℝ)^2):=Real.sqrt_le_sqrt (by nlinarith)
      _=(s:ℝ):=Real.sqrt_sq hs_pos.le
  have hexp_bound:Real.exp (1*(Real.exp ((1/ 2 : ℝ)*Real.log (s:ℝ)) - 1))≤ (Real.exp 1)^s:=by
    rw [← Real.exp_nat_mul,mul_one,one_mul]
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    (s.factorial:ℝ)/ ((1/ 2 : ℝ)*Real.log (s:ℝ))^s *
        Real.exp (1*(Real.exp ((1/ 2 : ℝ)*Real.log (s:ℝ)) - 1))
        ≤ (s:ℝ)^s/ ((1/ 2 : ℝ)*Real.log (s:ℝ))^s*(Real.exp 1)^s:=by gcongr
    _=(2*Real.exp 1*(s:ℝ)/ Real.log (s:ℝ))^s:=by
        rw [div_pow,mul_pow,mul_pow,mul_pow]
        have h2:(1/ 2 : ℝ)^s=((2 : ℝ)^s)⁻¹:=by rw [one_div,inv_pow]
        rw [h2]
        field_simp
lemma yQ {M:ℝ} (hM:0≤ M) {s:ℕ} (hs:1≤ s) :
    ∑ j∈Finset.range (s+1),(Nat.stirlingSecond s j:ℝ)*M^j ≤
      (Real.exp 1*((s:ℝ)+M))^s:=by
  rcases eq_or_lt_of_le hM with rfl | hMpos
  · have hzero:∑ j∈Finset.range (s+1),(Nat.stirlingSecond s j:ℝ)*(0 : ℝ)^j=0:=by
      refine sum_eq_zero fun j _=>?_
      cases j with
      | zero =>
        obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega:s≠0)
        simp
      | succ j=>simp
    rw [hzero]; positivity
  · have hspos:(0 : ℝ)< s:=by positivity
    let z:ℝ:=(s:ℝ)/ ((s:ℝ)+M)
    have hz_pos:0< z:=by positivity
    have h1z_pos:0< 1 - z:=by
      have : 1 - z=M/ ((s:ℝ)+M):=by dsimp [z]; field_simp; ring
      rw [this]; positivity
    have hexpz_le:Real.exp z≤ (1 - z)⁻¹:=by
      have h1:1 - z≤ Real.exp (-z):=by linarith [Real.add_one_le_exp (-z)]
      rw [Real.exp_neg] at h1
      rw [le_inv_comm₀ (Real.exp_pos z) h1z_pos]
      exact h1
    have hMe:M*(Real.exp z - 1)≤ (s:ℝ):=by
      have h1z:(1 - z)⁻¹ - 1=(s:ℝ)/ M:=by
        dsimp [z]
        have hsm:(s:ℝ)+M≠0:=by positivity
        field_simp [hsm,hMpos.ne']
        ring
      calc
        M*(Real.exp z - 1)≤ M*((1 - z)⁻¹ - 1):=by gcongr
        _=M*((s:ℝ)/ M):=by rw [h1z]
        _=(s:ℝ):=mul_div_cancel₀ _ hMpos.ne'
    have hfac:(s.factorial:ℝ)≤ (s:ℝ)^s:=by exact_mod_cast Nat.factorial_le_pow s
    refine (yo hM hz_pos s).trans ?_
    have hexp_s:Real.exp (M*(Real.exp z - 1))≤ (Real.exp 1)^s:=by
      rw [← Real.exp_nat_mul,mul_one]
      exact Real.exp_le_exp.mpr hMe
    calc
      (s.factorial:ℝ)/ z^s*Real.exp (M*(Real.exp z - 1))
          ≤ (s:ℝ)^s/ z^s*(Real.exp 1)^s:=by gcongr
      _=(Real.exp 1*((s:ℝ)+M))^s:=by
          dsimp [z]
          rw [div_pow,mul_pow]
          have hsne:(s:ℝ)^s≠0:=by positivity
          field_simp
lemma yV {α : Type*} [DecidableEq α] (P:Finset α) (h:α→ℝ) (j:ℕ) :
    ∑ T∈P.powersetCard (j+1),((j+1).factorial:ℝ)*∏ p∈T,h p =
      ∑ S∈P.powersetCard j,((j.factorial:ℝ)*∏ p∈S,h p)*(∑ q∈P \ S,h q):=by
  have hlhs:∑ T∈P.powersetCard (j+1),((j+1).factorial:ℝ)*∏ p∈T,h p =
      ∑ x∈(P.powersetCard (j+1)).sigma (fun T=>T),
        (j.factorial:ℝ)*h x.2*∏ p∈x.1.erase x.2,h p:=by
    rw [Finset.sum_sigma]
    refine sum_congr rfl fun T hT=>?_
    have hcard:T.card=j+1:=(mem_powersetCard.mp hT).2
    have hterm:∀ q∈T,
        (j.factorial:ℝ)*h q*∏ p∈T.erase q,h p =
          (j.factorial:ℝ)*∏ p∈T,h p:=by
      intro q hq
      rw [mul_assoc,Finset.mul_prod_erase T h hq]
    rw [sum_congr rfl hterm,sum_const,hcard,nsmul_eq_mul,
      Nat.factorial_succ,Nat.cast_mul]
    ring
  have hrhs:∑ S∈P.powersetCard j,((j.factorial:ℝ)*∏ p∈S,h p)*(∑ q∈P \ S,h q) =
      ∑ y∈(P.powersetCard j).sigma (fun S=>P \ S),
        (j.factorial:ℝ)*h y.2*∏ p∈y.1,h p:=by
    rw [Finset.sum_sigma]
    refine sum_congr rfl fun S _=>?_
    rw [mul_sum]
    refine sum_congr rfl fun q _=>by ring
  rw [hlhs,hrhs]
  refine Finset.sum_nbij' (fun x=>⟨x.1.erase x.2,x.2⟩) (fun y=>⟨insert y.2 y.1,y.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rcases Finset.mem_sigma.mp hx with ⟨hT,hqT⟩
    rcases mem_powersetCard.mp hT with ⟨hTP,hcard⟩
    refine Finset.mem_sigma.mpr ⟨mem_powersetCard.mpr ⟨(Finset.erase_subset _ _).trans hTP,?_⟩,
      Finset.mem_sdiff.mpr ⟨hTP hqT,Finset.notMem_erase _ _⟩⟩
    rw [Finset.card_erase_of_mem hqT,hcard,Nat.add_sub_cancel]
  · intro y hy
    rcases Finset.mem_sigma.mp hy with ⟨hS,hq⟩
    rcases mem_powersetCard.mp hS with ⟨hSP,hcard⟩
    rcases Finset.mem_sdiff.mp hq with ⟨hqP,hqS⟩
    refine Finset.mem_sigma.mpr ⟨mem_powersetCard.mpr ⟨Finset.insert_subset hqP hSP,?_⟩,
      Finset.mem_insert_self _ _⟩
    rw [Finset.card_insert_of_notMem hqS,hcard]
  · intro x hx
    rcases Finset.mem_sigma.mp hx with ⟨_,hqT⟩
    exact Sigma.ext (Finset.insert_erase hqT) (heq_of_eq rfl)
  · intro y hy
    rcases Finset.mem_sigma.mp hy with ⟨_,hq⟩
    rcases Finset.mem_sdiff.mp hq with ⟨_,hqS⟩
    exact Sigma.ext (Finset.erase_insert hqS) (heq_of_eq rfl)
  · intro _ _; rfl
lemma zP {α : Type*} [DecidableEq α]
    (P:Finset α) {h:α→ℝ} (hh:∀ p∈P,0≤ h p) (j:ℕ) :
    ∑ T∈P.powersetCard j,(j.factorial:ℝ)*∏ p∈T,h p≤ (∑ p∈P,h p)^j:=by
  induction j with
  | zero=>simp
  | succ j ih =>
    rw [yV]
    have h_le:∑ S∈P.powersetCard j,((j.factorial:ℝ)*∏ p∈S,h p)*(∑ q∈P \ S,h q) ≤
        ∑ S∈P.powersetCard j,((j.factorial:ℝ)*∏ p∈S,h p)*(∑ q∈P,h q):=by
      refine sum_le_sum fun S hS=>?_
      have hSP:S⊆P:=(mem_powersetCard.mp hS).1
      have hprod_nn:0≤ (j.factorial:ℝ)*∏ p∈S,h p :=
        mul_nonneg (by positivity) (prod_nonneg fun p hp=>hh p (hSP hp))
      exact mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun q hq _=>hh q hq)
        hprod_nn
    refine h_le.trans ?_
    rw [← sum_mul,pow_succ]
    exact mul_le_mul_of_nonneg_right ih (sum_nonneg hh)
lemma xk {α : Type*} [DecidableEq α] (P:Finset α) {f:α→ℝ}
    (hf:∀ p∈P,f p*f p=f p) (s:ℕ) :
    (∑ p∈P,f p)^s =
      ∑ j∈Finset.range (s+1),
        (Nat.stirlingSecond s j:ℝ) *
          ∑ T∈P.powersetCard j,(j.factorial:ℝ)*∏ p∈T,f p:=by
  let A:ℕ→ℝ:=fun j=>∑ T∈P.powersetCard j,(j.factorial:ℝ)*∏ p∈T,f p
  have hA_step:∀ j:ℕ,A j*(∑ q∈P,f q)=(j:ℝ)*A j+A (j+1):=by
    intro j
    dsimp only [A]
    rw [sum_mul]
    have hsplit:∀ S∈P.powersetCard j,
        ((j.factorial:ℝ)*∏ p∈S,f p)*(∑ q∈P,f q) =
          (j:ℝ)*((j.factorial:ℝ)*∏ p∈S,f p) +
          ((j.factorial:ℝ)*∏ p∈S,f p)*(∑ q∈P \ S,f q):=by
      intro S hS
      rcases mem_powersetCard.mp hS with ⟨hSP,hcard⟩
      rw [← Finset.sum_sdiff hSP,mul_add,add_comm]
      congr 1
      rw [mul_sum]
      have hterm:∀ q∈S,((j.factorial:ℝ)*∏ p∈S,f p)*f q =
          (j.factorial:ℝ)*∏ p∈S,f p:=by
        intro q hq
        rw [← Finset.mul_prod_erase S f hq]
        calc
          ((j.factorial:ℝ)*(f q*∏ p∈S.erase q,f p))*f q
              = (j.factorial:ℝ)*((f q*f q)*∏ p∈S.erase q,f p):=by ring
          _=(j.factorial:ℝ)*(f q*∏ p∈S.erase q,f p):=by rw [hf q (hSP hq)]
      rw [sum_congr rfl hterm,sum_const,hcard,nsmul_eq_mul]
    rw [sum_congr rfl hsplit,sum_add_distrib,← mul_sum,
      ← yV]
  change (∑ p∈P,f p)^s=∑ j∈Finset.range (s+1),(Nat.stirlingSecond s j:ℝ)*A j
  induction s with
  | zero=>simp [A]
  | succ s ih =>
    rw [pow_succ,ih,sum_mul]
    have hrew:∀ j∈Finset.range (s+1),
        (Nat.stirlingSecond s j:ℝ)*A j*(∑ p∈P,f p) =
          (Nat.stirlingSecond s j:ℝ)*A (j+1) +
          (j:ℝ)*(Nat.stirlingSecond s j:ℝ)*A j:=by
      intro j _
      rw [mul_assoc,hA_step]
      ring
    rw [sum_congr rfl hrew,sum_add_distrib]
    have h1:∑ j∈Finset.range (s+1),(Nat.stirlingSecond s j:ℝ)*A (j+1) =
        ∑ j∈Finset.range (s+2),
          (if j=0 then 0 else (Nat.stirlingSecond s (j - 1):ℝ)*A j):=by
      symm
      rw [sum_range_succ']
      simp
    have h2:∑ j∈Finset.range (s+1),(j:ℝ)*(Nat.stirlingSecond s j:ℝ)*A j =
        ∑ j∈Finset.range (s+2),(j:ℝ)*(Nat.stirlingSecond s j:ℝ)*A j:=by
      symm
      rw [sum_range_succ,Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self s)]
      simp
    rw [h1,h2,← sum_add_distrib]
    refine sum_congr rfl fun j _=>?_
    cases j with
    | zero=>simp
    | succ j =>
      simp only [Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel,Nat.stirlingSecond_succ_succ,
        Nat.cast_add,Nat.cast_mul]
      ring
lemma yW {T:Finset ℕ} (hT:∀ p∈T,p.Prime) (m:ℕ) :
    (∏ p∈T,(if p∣m then (1 : ℝ) else 0))=if (∏ p∈T,p)∣m then 1 else 0:=by
  classical
  have hiff:(∀ p∈T,p∣m)↔(∏ p∈T,p)∣m:=by
    constructor
    · intro h
      refine prod_primes_dvd m (fun p hp=>(hT p hp).prime) h
    · intro h p hp
      exact (dvd_prod_of_mem _ hp).trans h
  by_cases hall:∀ p∈T,p∣m
  · rw [if_pos (hiff.mp hall)]
    exact Finset.prod_eq_one fun p hp=>if_pos (hall p hp)
  · rw [if_neg (mt hiff.mpr hall)]
    push Not at hall
    rcases hall with ⟨p,hpT,hpndvd⟩
    exact Finset.prod_eq_zero hpT (if_neg hpndvd)
lemma wa {I:Finset ℕ} {ν X:ℕ→ℝ} {r:ℝ} (hν : ∀ n∈I,0≤ ν n)
    (hX:∀ n∈I,0≤ X n) (hr:0< r) (s:ℕ) :
    (∑ n∈I.filter (fun n=>r≤ X n),ν n) ≤
      (∑ n∈I,ν n*(X n)^s)/ r^s:=by
  rw [le_div_iff₀ (pow_pos hr s),sum_mul]
  calc
    ∑ n∈I.filter (fun n=>r≤ X n),ν n*r^s
        ≤ ∑ n∈I.filter (fun n=>r≤ X n),ν n*(X n)^s:=by
          refine sum_le_sum fun n hn=>?_
          rcases mem_filter.mp hn with ⟨hnI,hXr⟩
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hXr s) (hν n hnI)
    _≤ ∑ n∈I,ν n*(X n)^s:=by
          refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun n hn _=>?_
          exact mul_nonneg (hν n hn) (pow_nonneg (hX n hn) s)
lemma xF {I Kset:Finset ℕ} {ν : ℕ→ℝ} {bad:ℕ→ℕ→Prop}
    [∀ k,DecidablePred (bad k)]
    (hν : ∀ n∈I,0≤ ν n)
    (hunion:∑ k∈Kset,∑ n∈I.filter (bad k),ν n< ∑ n∈I,ν n) :
    ∃ n∈I,0< ν n∧∀ k∈Kset,¬bad k n:=by
  by_contra hnone
  push Not at hnone
  have hle:∑ n∈I,ν n≤ ∑ k∈Kset,∑ n∈I.filter (bad k),ν n:=by
    have hswap:∑ k∈Kset,∑ n∈I.filter (bad k),ν n =
        ∑ n∈I,∑ k∈Kset,(if bad k n then ν n else 0):=by
      simp_rw [sum_filter]
      exact sum_comm
    rw [hswap]
    refine sum_le_sum fun n hn=>?_
    rcases eq_or_lt_of_le (hν n hn) with h0 | hpos
    · rw [← h0]
      exact sum_nonneg fun k _=>by split_ifs <;> linarith
    · obtain ⟨k,hk,hbad⟩:=hnone n hn hpos
      have hsingle:=single_le_sum
        (f:=fun k=>if bad k n then ν n else 0)
        (fun j _=>by split_ifs; exact hν n hn; exact le_rfl) hk
      rwa [if_pos hbad] at hsingle
  linarith
end
end Erdos413Moments
namespace Erdos413Mertens
open Finset Filter Topology Complex Real
open scoped BigOperators
noncomputable section
def z5 (n:ℕ):Finset ℕ:=(Finset.Icc 1 n).filter Nat.Prime
def z2 (m n:ℕ):Finset ℕ:=(Finset.Ioc m n).filter Nat.Prime
lemma wd (n:ℕ):z5 n=Nat.primesLE n:=by
  ext p
  simp only [z5,mem_filter,mem_Icc,Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨_,h2⟩,hp⟩; exact ⟨h2,hp⟩
  · rintro ⟨h2,hp⟩; exact ⟨⟨hp.one_le,h2⟩,hp⟩
def theta (n:ℕ):ℝ:=∑ p∈z5 n,Real.log p
lemma v5:theta 0=0:=by simp [theta,z5]
lemma v1:theta 1=0:=by
  unfold theta z5
  have : (Finset.Icc 1 1).filter Nat.Prime=∅:=by decide
  rw [this,sum_empty]
lemma wW (n:ℕ) :
    theta (n+1) - theta n=if (n+1).Prime then Real.log (n+1 : ℕ) else 0:=by
  unfold theta z5
  have hsub:(Finset.Icc 1 (n+1)).filter Nat.Prime =
      if (n+1).Prime then insert (n+1) ((Finset.Icc 1 n).filter Nat.Prime)
      else (Finset.Icc 1 n).filter Nat.Prime:=by
    ext p
    split_ifs with hp
    · simp only [mem_filter,mem_Icc,mem_insert]
      constructor
      · rintro ⟨⟨h1,h2⟩,hpp⟩
        rcases eq_or_lt_of_le h2 with rfl | hlt
        · exact Or.inl rfl
        · exact Or.inr ⟨⟨h1,Nat.lt_succ_iff.mp hlt⟩,hpp⟩
      · rintro (rfl | ⟨⟨h1,h2⟩,hpp⟩)
        · exact ⟨⟨by omega,le_rfl⟩,hp⟩
        · exact ⟨⟨h1,by omega⟩,hpp⟩
    · simp only [mem_filter,mem_Icc]
      constructor
      · rintro ⟨⟨h1,h2⟩,hpp⟩
        have hne:p≠n+1:=fun h=>hp (h ▸ hpp)
        exact ⟨⟨h1,by omega⟩,hpp⟩
      · rintro ⟨⟨h1,h2⟩,hpp⟩
        exact ⟨⟨h1,by omega⟩,hpp⟩
  rw [hsub]
  split_ifs with hp
  · have hnot:n+1 ∉ (Finset.Icc 1 n).filter Nat.Prime:=by
      simp only [mem_filter,mem_Icc,not_and]; intro h; omega
    rw [sum_insert hnot]
    ring
  · ring
lemma wR (n:ℕ):theta n≤ (n:ℝ)*Real.log 4:=by
  unfold theta
  rw [wd]
  have hlog:∑ p∈Nat.primesLE n,Real.log (p:ℝ)=Real.log (primorial n:ℝ):=by
    rw [primorial_eq_prod_primesLE,Nat.cast_prod,Real.log_prod]
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primesLE hp).ne_zero
  rw [hlog]
  have hle:(primorial n:ℝ)≤ (4 : ℝ)^n:=by
    exact_mod_cast primorial_le_four_pow n
  calc
    Real.log (primorial n:ℝ)≤ Real.log ((4 : ℝ)^n) :=
      Real.log_le_log (by exact_mod_cast primorial_pos n) hle
    _=(n:ℝ)*Real.log 4:=Real.log_pow 4 n
lemma xW {m:ℕ} (hm:2≤ m) :
    (1 : ℝ)/ (m:ℝ)≤ Real.log (m:ℝ) - Real.log ((m - 1 : ℕ):ℝ):=by
  have hm0:(0 : ℝ)< m:=by exact_mod_cast (show 0< m by omega)
  have hm1:(0 : ℝ)< (m - 1 : ℕ):=by exact_mod_cast (show 0< m - 1 by omega)
  have hcast:((m - 1 : ℕ):ℝ)=(m:ℝ) - 1:=by
    simpa using Nat.cast_sub (R:=ℝ) (show 1≤ m by omega)
  have h:=Real.log_le_sub_one_of_pos (div_pos hm1 hm0)
  rw [Real.log_div hm1.ne' hm0.ne',hcast] at h
  have hsimp:((m:ℝ) - 1)/ (m:ℝ) - 1=-(1/ (m:ℝ)):=by field_simp; ring
  rw [hcast]
  linarith
lemma wt {a b:ℕ} (hab:a< b) (A f:ℕ→ℝ) :
    ∑ n∈Finset.Ioc a b,(A n - A (n - 1))*f n =
      A b*f b - A a*f (a+1) +
        ∑ n∈Finset.Ioc a (b - 1),A n*(f n - f (n+1)):=by
  induction b with
  | zero=>omega
  | succ k ih =>
    rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hab) with rfl | hlt
    · have hIoc:Finset.Ioc a (a+1)={a+1}:=by
        ext x; simp only [mem_Ioc,Finset.mem_singleton]; omega
      rw [hIoc,Finset.sum_singleton]
      simp only [Nat.add_sub_cancel,Finset.Ioc_eq_empty_of_le le_rfl,sum_empty,add_zero]
      ring
    · have hIoc:Finset.Ioc a (k+1)=insert (k+1) (Finset.Ioc a k):=by
        ext x; simp only [mem_Ioc,mem_insert]; omega
      have hnot:k+1 ∉ Finset.Ioc a k:=by simp
      have hIoc2:Finset.Ioc a k=insert k (Finset.Ioc a (k - 1)):=by
        ext x; simp only [mem_Ioc,mem_insert]; omega
      have hnot2:k ∉ Finset.Ioc a (k - 1):=by simp only [mem_Ioc]; omega
      rw [hIoc,sum_insert hnot,ih hlt]
      simp only [Nat.add_sub_cancel]
      rw [hIoc2,sum_insert hnot2]
      ring
lemma y9 (N:ℕ) (hN:1≤ N) :
    ∑ p∈z5 N,Real.log (p:ℝ)/ (p:ℝ)≤ Real.log 4*(1+Real.log N):=by
  rcases eq_or_lt_of_le hN with rfl | hN2
  · have h1:z5 1=∅:=by unfold z5; decide
    rw [h1,sum_empty,Nat.cast_one,Real.log_one,add_zero,mul_one]
    exact Real.log_nonneg (by norm_num)
  · have hsum_eq:∑ p∈z5 N,Real.log (p:ℝ)/ (p:ℝ) =
        ∑ n∈Finset.Ioc 1 N,(theta n - theta (n - 1))*((n:ℝ)⁻¹):=by
      have h1:∀ n∈Finset.Ioc 1 N,
          (theta n - theta (n - 1))*((n:ℝ)⁻¹) =
            if n.Prime then Real.log (n:ℝ)/ (n:ℝ) else 0:=by
        intro n hn
        have hn1:1≤ n:=by have:=(mem_Ioc.mp hn).1; omega
        have:=wW (n - 1)
        rw [Nat.sub_add_cancel hn1] at this
        rw [this]
        split_ifs <;> simp [div_eq_mul_inv]
      rw [sum_congr rfl h1,← sum_filter]
      congr 1
      ext p
      simp only [z5,mem_filter,mem_Icc,mem_Ioc]
      constructor
      · rintro ⟨⟨_,h2⟩,hp⟩; exact ⟨⟨hp.one_lt,h2⟩,hp⟩
      · rintro ⟨⟨h1,h2⟩,hp⟩; exact ⟨⟨by omega,h2⟩,hp⟩
    rw [hsum_eq,wt hN2 theta (fun n=>(n:ℝ)⁻¹),v1,zero_mul,sub_zero]
    have hfirst:theta N*((N:ℝ)⁻¹)≤ Real.log 4:=by
      have hNpos:(0 : ℝ)< N:=by positivity
      calc theta N*(N:ℝ)⁻¹≤ ((N:ℝ)*Real.log 4)*(N:ℝ)⁻¹:=by
            gcongr; exact wR N
        _=Real.log 4:=by field_simp
    have hmid:∑ n∈Finset.Ioc 1 (N - 1),theta n*((n:ℝ)⁻¹ - ((n+1 : ℕ):ℝ)⁻¹) ≤
        Real.log 4*Real.log N:=by
      have hterm:∀ n∈Finset.Ioc 1 (N - 1),
          theta n*((n:ℝ)⁻¹ - ((n+1 : ℕ):ℝ)⁻¹) ≤
            Real.log 4*(Real.log ((n+1 : ℕ):ℝ) - Real.log (n:ℝ)):=by
        intro n hn
        have hn1:1< n:=(mem_Ioc.mp hn).1
        have hn0:(0 : ℝ)< n:=by positivity
        have hdiff:(n:ℝ)⁻¹ - ((n+1 : ℕ):ℝ)⁻¹ =
            (1 : ℝ)/ ((n:ℝ)*((n+1 : ℕ):ℝ)):=by
          push_cast; field_simp; ring
        have hdiff_nn:0≤ (n:ℝ)⁻¹ - ((n+1 : ℕ):ℝ)⁻¹:=by rw [hdiff]; positivity
        calc
          theta n*((n:ℝ)⁻¹ - ((n+1 : ℕ):ℝ)⁻¹)
              ≤ ((n:ℝ)*Real.log 4)*((n:ℝ)⁻¹ - ((n+1 : ℕ):ℝ)⁻¹):=by
                gcongr; exact wR n
          _=Real.log 4*((1 : ℝ)/ ((n+1 : ℕ):ℝ)):=by
                rw [hdiff]; field_simp
          _≤ Real.log 4*(Real.log ((n+1 : ℕ):ℝ) - Real.log (n:ℝ)):=by
                have hinv:=xW (m:=n+1) (by omega)
                simp only [Nat.add_sub_cancel] at hinv
                exact mul_le_mul_of_nonneg_left hinv (Real.log_nonneg (by norm_num))
      refine (sum_le_sum hterm).trans ?_
      rw [← mul_sum]
      have htele:∑ n∈Finset.Ioc 1 (N - 1),(Real.log ((n+1 : ℕ):ℝ) - Real.log (n:ℝ)) ≤
          Real.log (N:ℝ):=by
        have h_eq:∀ k:ℕ,1≤ k →
            ∑ n∈Finset.Ioc 1 k,(Real.log ((n+1 : ℕ):ℝ) - Real.log (n:ℝ)) =
              Real.log ((k+1 : ℕ):ℝ) - Real.log 2:=by
          intro k hk
          induction k with
          | zero=>omega
          | succ m ih =>
            rcases eq_or_lt_of_le hk with h1 | hm
            · have hm0:m=0:=by omega
              subst hm0; simp
            · have hIoc:Finset.Ioc 1 (m+1)=insert (m+1) (Finset.Ioc 1 m):=by
                ext x; simp only [mem_Ioc,mem_insert]; omega
              rw [hIoc,sum_insert (by simp),ih (by omega)]
              ring
        rw [h_eq (N - 1) (by omega),Nat.sub_add_cancel (by omega)]
        linarith [Real.log_nonneg (by norm_num:(1 : ℝ)≤ 2)]
      exact mul_le_mul_of_nonneg_left htele (Real.log_nonneg (by norm_num))
    linarith
lemma yx:Real.log 4≤ 2:=by
  have h1:(4 : ℝ)≤ Real.exp 2:=by
    have h2:(2 : ℝ)≤ Real.exp 1:=by
      have:=Real.add_one_le_exp (1 : ℝ)
      linarith
    have hsq:(2 : ℝ)^2≤ (Real.exp 1)^2:=by gcongr
    rw [← Real.exp_nat_mul] at hsq
    norm_num at hsq ⊢
    exact hsq
  calc Real.log 4≤ Real.log (Real.exp 2):=Real.log_le_log (by norm_num) h1
    _=2:=Real.log_exp 2
lemma xO:Real.log 4< 3/ 2:=by
  have h1:(4 : ℝ)< Real.exp (3/ 2):=by
    have h2:(2.71 : ℝ)< Real.exp 1:=Real.exp_one_gt_d9.trans' (by norm_num)
    have h3:(4 : ℝ)^2< (Real.exp 1)^3:=by nlinarith [sq_nonneg (Real.exp 1)]
    have h4:(Real.exp (3/ 2 : ℝ))^2=(Real.exp 1)^3:=by
      rw [← Real.exp_nat_mul,← Real.exp_nat_mul]
      congr 1; norm_num
    nlinarith [Real.exp_pos (3/ 2 : ℝ)]
  calc Real.log 4< Real.log (Real.exp (3/ 2)):=Real.log_lt_log (by norm_num) h1
    _=3/ 2:=Real.log_exp (3/ 2)
lemma zC:(1/ 2 : ℝ)≤ Real.log 2:=by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1:Real.exp 1< 4:=Real.exp_one_lt_d9.trans (by norm_num)
  have hsq:(Real.exp (1/ 2 : ℝ))^2=Real.exp 1:=by
    rw [← Real.exp_nat_mul]; norm_num
  nlinarith [Real.exp_pos (1/ 2 : ℝ)]
lemma xM {M N:ℕ} (hM:2≤ M) (hMN:M≤ N) :
    ∑ p∈z2 M N,(1 : ℝ)/ (p:ℝ) ≤
      2*Real.log (Real.log (N:ℝ)/ Real.log (M:ℝ))+10:=by
  rcases eq_or_lt_of_le hMN with rfl | hlt
  · simp [z2]
  · let S:ℕ→ℝ:=fun n=>∑ p∈z5 n,Real.log (p:ℝ)/ (p:ℝ)
    have hS_succ:∀ n:ℕ,2≤ n →
        S n - S (n - 1)=if n.Prime then Real.log (n:ℝ)/ (n:ℝ) else 0:=by
      intro n hn
      unfold S z5
      have hsub:(Finset.Icc 1 n).filter Nat.Prime =
          if n.Prime then insert n ((Finset.Icc 1 (n - 1)).filter Nat.Prime)
          else (Finset.Icc 1 (n - 1)).filter Nat.Prime:=by
        ext p
        split_ifs with hp
        · simp only [mem_filter,mem_Icc,mem_insert]
          constructor
          · rintro ⟨⟨h1,h2⟩,hpp⟩
            rcases eq_or_lt_of_le h2 with rfl | hlt'
            · exact Or.inl rfl
            · exact Or.inr ⟨⟨h1,by omega⟩,hpp⟩
          · rintro (rfl | ⟨⟨h1,h2⟩,hpp⟩)
            · exact ⟨⟨by omega,le_rfl⟩,hp⟩
            · exact ⟨⟨h1,by omega⟩,hpp⟩
        · simp only [mem_filter,mem_Icc]
          constructor
          · rintro ⟨⟨h1,h2⟩,hpp⟩
            have hne:p≠n:=fun h=>hp (h ▸ hpp)
            exact ⟨⟨h1,by omega⟩,hpp⟩
          · rintro ⟨⟨h1,h2⟩,hpp⟩
            exact ⟨⟨h1,by omega⟩,hpp⟩
      rw [hsub]
      split_ifs with hp
      · have hnot:n ∉ (Finset.Icc 1 (n - 1)).filter Nat.Prime:=by
          simp only [mem_filter,mem_Icc,not_and]; intro h; omega
        rw [sum_insert hnot]; ring
      · ring
    have hsum_eq:∑ p∈z2 M N,(1 : ℝ)/ (p:ℝ) =
        ∑ n∈Finset.Ioc M N,(S n - S (n - 1))*(Real.log (n:ℝ))⁻¹:=by
      have h1:∀ n∈Finset.Ioc M N,
          (S n - S (n - 1))*(Real.log (n:ℝ))⁻¹ =
            if n.Prime then (1 : ℝ)/ (n:ℝ) else 0:=by
        intro n hn
        have hn2:2≤ n:=by have:=(mem_Ioc.mp hn).1; omega
        rw [hS_succ n hn2]
        split_ifs with hp
        · have hlog_ne:Real.log (n:ℝ)≠0 :=
            (Real.log_pos (by exact_mod_cast (show 1< n by omega))).ne'
          field_simp
        · simp
      rw [sum_congr rfl h1,← sum_filter]
      rfl
    rw [hsum_eq,wt hlt S (fun n=>(Real.log (n:ℝ))⁻¹)]
    have hS_M_nn:0≤ S M*(Real.log ((M+1 : ℕ):ℝ))⁻¹:=by
      apply mul_nonneg
      · exact sum_nonneg fun p hp=>div_nonneg (Real.log_nonneg (by
          exact_mod_cast (mem_filter.mp hp).2.one_le)) (by positivity)
      · exact inv_nonneg.mpr (Real.log_nonneg (by exact_mod_cast (show 1≤ M+1 by omega)))
    have hlogN_pos:0< Real.log (N:ℝ):=Real.log_pos (by exact_mod_cast (show 1< N by omega))
    have hlogM_pos:0< Real.log (M:ℝ):=Real.log_pos (by exact_mod_cast (show 1< M by omega))
    have hlog2_le_N:(1/ 2 : ℝ)≤ Real.log (N:ℝ) :=
      zC.trans (Real.log_le_log (by norm_num) (by exact_mod_cast (show 2≤ N by omega)))
    have hfirst:S N*(Real.log (N:ℝ))⁻¹≤ 6:=by
      have hSN:=y9 N (by omega)
      calc
        S N*(Real.log (N:ℝ))⁻¹
            ≤ (Real.log 4*(1+Real.log (N:ℝ)))*(Real.log (N:ℝ))⁻¹:=by gcongr
        _=Real.log 4*((Real.log (N:ℝ))⁻¹+1):=by field_simp
        _≤ 2*(2+1):=by
            have hinv:(Real.log (N:ℝ))⁻¹≤ 2:=by
              rw [inv_le_comm₀ hlogN_pos (by norm_num)]; linarith
            have hlog4:=yx
            nlinarith [Real.log_nonneg (by norm_num:(1 : ℝ)≤ 4)]
        _=6:=by norm_num
    have hmid:∑ n∈Finset.Ioc M (N - 1),
          S n*((Real.log (n:ℝ))⁻¹ - (Real.log ((n+1 : ℕ):ℝ))⁻¹) ≤
        2*Real.log (Real.log (N:ℝ)/ Real.log (M:ℝ))+4:=by
      have hterm:∀ n∈Finset.Ioc M (N - 1),
          S n*((Real.log (n:ℝ))⁻¹ - (Real.log ((n+1 : ℕ):ℝ))⁻¹) ≤
            2*((Real.log (n:ℝ))⁻¹ - (Real.log ((n+1 : ℕ):ℝ))⁻¹) +
            2*(Real.log (Real.log ((n+1 : ℕ):ℝ)) - Real.log (Real.log (n:ℝ))):=by
        intro n hn
        have hn2:2≤ n:=by have:=(mem_Ioc.mp hn).1; omega
        have hln:0< Real.log (n:ℝ):=Real.log_pos (by exact_mod_cast (show 1< n by omega))
        have hln1:0< Real.log ((n+1 : ℕ):ℝ) :=
          Real.log_pos (by exact_mod_cast (show 1< n+1 by omega))
        have hln_le:Real.log (n:ℝ)≤ Real.log ((n+1 : ℕ):ℝ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast (show n≤ n+1 by omega))
        have hdiff_nn:0≤ (Real.log (n:ℝ))⁻¹ - (Real.log ((n+1 : ℕ):ℝ))⁻¹:=by
          rw [sub_nonneg]; exact inv_anti₀ hln hln_le
        have hSn:S n≤ 2*(1+Real.log (n:ℝ)) :=
          (y9 n (by omega)).trans
            (mul_le_mul_of_nonneg_right yx (by linarith))
        have hlog_step:Real.log (n:ℝ)*((Real.log (n:ℝ))⁻¹ - (Real.log ((n+1 : ℕ):ℝ))⁻¹) ≤
            Real.log (Real.log ((n+1 : ℕ):ℝ)) - Real.log (Real.log (n:ℝ)):=by
          have h:=Real.log_le_sub_one_of_pos (div_pos hln hln1)
          rw [Real.log_div hln.ne' hln1.ne'] at h
          have heq:Real.log (n:ℝ)*((Real.log (n:ℝ))⁻¹ - (Real.log ((n+1 : ℕ):ℝ))⁻¹) =
              1 - Real.log (n:ℝ)/ Real.log ((n+1 : ℕ):ℝ):=by field_simp
          linarith
        calc
          S n*((Real.log (n:ℝ))⁻¹ - (Real.log ((n+1 : ℕ):ℝ))⁻¹)
              ≤ (2*(1+Real.log (n:ℝ)))*((Real.log (n:ℝ))⁻¹ - (Real.log ((n+1 : ℕ):ℝ))⁻¹):=by
                gcongr
          _=2*((Real.log (n:ℝ))⁻¹ - (Real.log ((n+1 : ℕ):ℝ))⁻¹) +
              2*(Real.log (n:ℝ)*((Real.log (n:ℝ))⁻¹ - (Real.log ((n+1 : ℕ):ℝ))⁻¹)):=by
                ring
          _≤ 2*((Real.log (n:ℝ))⁻¹ - (Real.log ((n+1 : ℕ):ℝ))⁻¹) +
              2*(Real.log (Real.log ((n+1 : ℕ):ℝ)) - Real.log (Real.log (n:ℝ))):=by
                gcongr
      refine (sum_le_sum hterm).trans ?_
      rw [sum_add_distrib,← mul_sum,← mul_sum]
      have htele_gen:∀ (f:ℕ→ℝ) (k:ℕ),M≤ k →
          ∑ n∈Finset.Ioc M k,(f (n+1) - f n) =
            if M=k then 0 else f (k+1) - f (M+1):=by
        intro f k hk
        induction k with
        | zero=>omega
        | succ j ih =>
          rcases eq_or_lt_of_le hk with rfl | hlt'
          · simp
          · rcases eq_or_lt_of_le (show M≤ j by omega) with rfl | hlt''
            · have hIoc:Finset.Ioc M (M+1)={M+1}:=by
                ext x; simp only [mem_Ioc,Finset.mem_singleton]; omega
              rw [hIoc,Finset.sum_singleton,if_neg (by omega)]
            · have hIoc:Finset.Ioc M (j+1)=insert (j+1) (Finset.Ioc M j):=by
                ext x; simp only [mem_Ioc,mem_insert]; omega
              rw [hIoc,sum_insert (by simp),ih (by omega),if_neg (by omega),if_neg (by omega)]
              ring
      have h_s1:∑ n∈Finset.Ioc M (N - 1),
          ((Real.log (n:ℝ))⁻¹ - (Real.log ((n+1 : ℕ):ℝ))⁻¹)≤ 2:=by
        have hrew:∑ n∈Finset.Ioc M (N - 1),
            ((Real.log (n:ℝ))⁻¹ - (Real.log ((n+1 : ℕ):ℝ))⁻¹) =
            -(∑ n∈Finset.Ioc M (N - 1),
              ((Real.log ((n+1 : ℕ):ℝ))⁻¹ - (Real.log (n:ℝ))⁻¹)):=by
          rw [← Finset.sum_neg_distrib]; congr 1; ext n; ring
        rw [hrew,htele_gen (fun n=>(Real.log (n:ℝ))⁻¹) (N - 1) (by omega)]
        split_ifs
        · norm_num
        · rw [Nat.sub_add_cancel (by omega)]
          have hln1:(1/ 2 : ℝ)≤ Real.log ((M+1 : ℕ):ℝ) :=
            zC.trans (Real.log_le_log (by norm_num) (by exact_mod_cast (show 2≤ M+1 by omega)))
          have hinv1:(Real.log ((M+1 : ℕ):ℝ))⁻¹≤ 2:=by
            rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
          have hinvN:0≤ (Real.log (N:ℝ))⁻¹:=inv_nonneg.mpr hlogN_pos.le
          linarith
      have h_s2:∑ n∈Finset.Ioc M (N - 1),
          (Real.log (Real.log ((n+1 : ℕ):ℝ)) - Real.log (Real.log (n:ℝ))) ≤
          Real.log (Real.log (N:ℝ)/ Real.log (M:ℝ)):=by
        rw [htele_gen (fun n=>Real.log (Real.log (n:ℝ))) (N - 1) (by omega)]
        split_ifs
        · exact Real.log_nonneg ((one_le_div hlogM_pos).mpr
            (Real.log_le_log (by positivity) (by exact_mod_cast hMN)))
        · rw [Nat.sub_add_cancel (by omega),Real.log_div hlogN_pos.ne' hlogM_pos.ne']
          have hmono:Real.log (Real.log (M:ℝ))≤ Real.log (Real.log ((M+1 : ℕ):ℝ)) :=
            Real.log_le_log hlogM_pos
              (Real.log_le_log (by positivity) (by exact_mod_cast (show M≤ M+1 by omega)))
          linarith
      linarith
    linarith
lemma yk {y z:ℝ} (hy:2≤ y) (hyz:y≤ z) :
    ∑ p∈z2 ⌊y⌋₊ ⌊z⌋₊,(1 : ℝ)/ (p:ℝ) ≤
      2*Real.log (Real.log z/ Real.log y)+12:=by
  have hM:2≤ ⌊y⌋₊:=Nat.le_floor hy
  have hMN:⌊y⌋₊≤ ⌊z⌋₊:=Nat.floor_mono hyz
  have hbase:=xM hM hMN
  have hlogM_pos:0< Real.log (⌊y⌋₊ : ℝ):=Real.log_pos (by exact_mod_cast (show 1< ⌊y⌋₊ by omega))
  have hlogy_pos:0< Real.log y:=Real.log_pos (by linarith)
  have hlogz_pos:0< Real.log z:=Real.log_pos (by linarith)
  have hlogN_pos:0< Real.log (⌊z⌋₊ : ℝ):=Real.log_pos (by exact_mod_cast (show 1< ⌊z⌋₊ by omega))
  have hy_le_Msq:y≤ ((⌊y⌋₊ : ℝ))^2:=by
    have h1:y< (⌊y⌋₊ : ℝ)+1:=Nat.lt_floor_add_one y
    have h2:(2 : ℝ)≤ (⌊y⌋₊ : ℝ):=by exact_mod_cast hM
    nlinarith
  have hlogy_le:Real.log y≤ 2*Real.log (⌊y⌋₊ : ℝ):=by
    calc Real.log y≤ Real.log ((⌊y⌋₊ : ℝ)^2):=Real.log_le_log (by linarith) hy_le_Msq
      _=2*Real.log (⌊y⌋₊ : ℝ):=by rw [Real.log_pow]; norm_num
  have hlogN_le:Real.log (⌊z⌋₊ : ℝ)≤ Real.log z :=
    Real.log_le_log (by exact_mod_cast (show 0< ⌊z⌋₊ by omega)) (Nat.floor_le (by linarith))
  have hratio:Real.log (⌊z⌋₊ : ℝ)/ Real.log (⌊y⌋₊ : ℝ)≤ 2*(Real.log z/ Real.log y):=by
    rw [div_le_iff₀ hlogM_pos]
    have h1:Real.log (⌊z⌋₊ : ℝ)*Real.log y≤ Real.log z*(2*Real.log (⌊y⌋₊ : ℝ)):=by
      gcongr
    have h2:2*(Real.log z/ Real.log y)*Real.log (⌊y⌋₊ : ℝ) =
        (Real.log z*(2*Real.log (⌊y⌋₊ : ℝ)))/ Real.log y:=by ring
    rw [h2,le_div_iff₀ hlogy_pos]
    exact h1
  have hlog_ratio:Real.log (Real.log (⌊z⌋₊ : ℝ)/ Real.log (⌊y⌋₊ : ℝ)) ≤
      Real.log (Real.log z/ Real.log y)+Real.log 2:=by
    calc
      Real.log (Real.log (⌊z⌋₊ : ℝ)/ Real.log (⌊y⌋₊ : ℝ))
          ≤ Real.log (2*(Real.log z/ Real.log y)) :=
            Real.log_le_log (div_pos hlogN_pos hlogM_pos) hratio
      _=Real.log (Real.log z/ Real.log y)+Real.log 2:=by
            rw [Real.log_mul (by norm_num) (div_pos hlogz_pos hlogy_pos).ne',add_comm]
  have hlog2_le:Real.log 2≤ 1:=by
    have:=Real.log_le_sub_one_of_pos (by norm_num:(0 : ℝ)< 2)
    linarith
  linarith
lemma yJ {z:ℝ} (hz:Real.exp 1≤ z) :
    ∑ p∈z5 ⌊z⌋₊,(1 : ℝ)/ (p:ℝ)≤ 2*Real.log (Real.log z)+15:=by
  have hz2:2≤ z:=by
    have:=Real.add_one_le_exp (1 : ℝ)
    linarith
  have hsplit:z5 ⌊z⌋₊=insert 2 (z2 2 ⌊z⌋₊):=by
    ext p
    simp only [z5,z2,mem_filter,mem_Icc,mem_Ioc,
      mem_insert]
    have h2z:2≤ ⌊z⌋₊:=Nat.le_floor hz2
    constructor
    · rintro ⟨⟨_,h2⟩,hp⟩
      rcases eq_or_lt_of_le hp.two_le with rfl | hgt
      · exact Or.inl rfl
      · exact Or.inr ⟨⟨hgt,h2⟩,hp⟩
    · rintro (rfl | ⟨⟨h1,h2⟩,hp⟩)
      · exact ⟨⟨by norm_num,h2z⟩,Nat.prime_two⟩
      · exact ⟨⟨by omega,h2⟩,hp⟩
  rw [hsplit,sum_insert (by simp [z2])]
  have h2:=yk (y:=2) (z:=z) le_rfl hz2
  simp only [show ⌊(2 : ℝ)⌋₊=2 by norm_num] at h2
  have hlogz_pos:0< Real.log z:=by
    have : 1≤ Real.log z:=by
      calc (1 : ℝ)=Real.log (Real.exp 1):=(Real.log_exp 1).symm
        _≤ Real.log z:=Real.log_le_log (Real.exp_pos 1) hz
    linarith
  have hlog2_pos:0< Real.log 2:=by linarith [zC]
  have hlog_div:Real.log (Real.log z/ Real.log 2)≤ Real.log (Real.log z)+1:=by
    rw [Real.log_div hlogz_pos.ne' hlog2_pos.ne']
    have : -Real.log (Real.log 2)≤ 1:=by
      rw [neg_le]
      have h1:Real.log (1/ 2 : ℝ)≤ Real.log (Real.log 2) :=
        Real.log_le_log (by norm_num) zC
      have h2':Real.log (1/ 2 : ℝ)=-Real.log 2:=by
        rw [one_div,Real.log_inv]
      have h3:Real.log 2≤ 1:=by linarith [Real.log_le_sub_one_of_pos (by norm_num:(0 : ℝ)< 2)]
      linarith
    linarith
  norm_num at h2 ⊢
  linarith
lemma xS {σ : ℝ} (hσ : 1< σ) :
    Summable (fun p:Nat.Primes=>(1 : ℝ)/ ((p:ℕ):ℝ)^σ):=by
  have hnat:Summable (fun n:ℕ=>(1 : ℝ)/ (n:ℝ)^σ):=by
    simpa [one_div] using Real.summable_nat_rpow_inv.mpr hσ
  exact hnat.comp_injective (fun a b h=>Subtype.ext h)
lemma w1 {x:ℝ} (hx:Real.exp 2≤ x) :
    ∑' p:Nat.Primes,(1 : ℝ)/ ((p:ℕ):ℝ)^(1+1/ Real.log x) ≤
      2*Real.log (Real.log x)+45:=by
  have hx1:Real.exp 1≤ x:=(Real.exp_le_exp.mpr (by norm_num)).trans hx
  have hx_pos:0< x:=(Real.exp_pos 2).trans_le hx
  have hlogx:2≤ Real.log x:=by
    calc (2 : ℝ)=Real.log (Real.exp 2):=(Real.log_exp 2).symm
      _≤ Real.log x:=Real.log_le_log (Real.exp_pos 2) hx
  have hσ : 1< 1+1/ Real.log x:=by
    have : 0< 1/ Real.log x:=by positivity
    linarith
  refine Real.tsum_le_of_sum_le (fun _=>by positivity) fun s=>?_
  let Nmax:ℕ:=s.sup (fun p:Nat.Primes=>(p:ℕ))
  obtain ⟨M,hM⟩ : ∃ M:ℕ,(Nmax:ℝ)≤ x^((2 : ℝ)^M):=by
    have hx2:(2 : ℝ)≤ x:=by
      have h1:(2 : ℝ)≤ Real.exp 1:=by linarith [Real.add_one_le_exp (1 : ℝ)]
      linarith
    refine ⟨Nmax,?_⟩
    have hpow:(Nmax:ℝ)≤ (2 : ℝ)^Nmax:=by
      exact_mod_cast Nat.lt_two_pow_self.le
    have h2:(2 : ℝ)^Nmax≤ (2 : ℝ)^(2^Nmax):=by
      gcongr; norm_num; exact Nat.lt_two_pow_self.le
    calc
      (Nmax:ℝ)≤ (2 : ℝ)^(2^Nmax):=hpow.trans h2
      _≤ x^(2^Nmax):=by gcongr
      _=x^((2 : ℝ)^Nmax):=by norm_cast
  have h_embed:∑ p∈s,(1 : ℝ)/ ((p:ℕ):ℝ)^(1+1/ Real.log x) ≤
      ∑ p∈z5 ⌊x^((2 : ℝ)^M)⌋₊,(1 : ℝ)/ (p:ℝ)^(1+1/ Real.log x):=by
    have h_img:∑ p∈s,(1 : ℝ)/ ((p:ℕ):ℝ)^(1+1/ Real.log x) =
        ∑ q∈s.image (fun p:Nat.Primes=>(p:ℕ)),
          (1 : ℝ)/ (q:ℝ)^(1+1/ Real.log x):=by
      rw [Finset.sum_image]
      intro a _ b _ hab; exact Subtype.ext hab
    rw [h_img]
    refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _=>by positivity)
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨p,hps,rfl⟩
    simp only [z5,mem_filter,mem_Icc]
    refine ⟨⟨p.prop.one_le,Nat.le_floor ?_⟩,p.prop⟩
    exact (Nat.cast_le.mpr (Finset.le_sup (f:=fun p:Nat.Primes=>(p:ℕ)) hps)).trans hM
  refine h_embed.trans ?_
  have h_split:∀ k:ℕ,
      ∑ p∈z5 ⌊x^((2 : ℝ)^k)⌋₊,(1 : ℝ)/ (p:ℝ)^(1+1/ Real.log x) =
        (∑ p∈z5 ⌊x⌋₊,(1 : ℝ)/ (p:ℝ)^(1+1/ Real.log x)) +
        ∑ m∈Finset.range k,
          ∑ p∈z2 ⌊x^((2 : ℝ)^m)⌋₊ ⌊x^((2 : ℝ)^(m+1))⌋₊,
            (1 : ℝ)/ (p:ℝ)^(1+1/ Real.log x):=by
    intro k
    induction k with
    | zero=>simp
    | succ k ih =>
      rw [sum_range_succ,← add_assoc,← ih]
      have hmono:⌊x^((2 : ℝ)^k)⌋₊≤ ⌊x^((2 : ℝ)^(k+1))⌋₊:=by
        apply Nat.floor_mono
        apply Real.rpow_le_rpow_of_exponent_le (by linarith [Real.add_one_le_exp (1 : ℝ)])
        have : (2 : ℝ)^k≤ (2 : ℝ)^(k+1):=by
          rw [pow_succ]; linarith [pow_nonneg (by norm_num:(0 : ℝ)≤ 2) k]
        exact this
      have hunion:z5 ⌊x^((2 : ℝ)^(k+1))⌋₊ =
          z5 ⌊x^((2 : ℝ)^k)⌋₊ ∪
          z2 ⌊x^((2 : ℝ)^k)⌋₊ ⌊x^((2 : ℝ)^(k+1))⌋₊:=by
        ext p
        simp only [z5,z2,mem_union,mem_filter,
          mem_Icc,mem_Ioc]
        constructor
        · rintro ⟨⟨h1,h2⟩,hp⟩
          by_cases hle:p≤ ⌊x^((2 : ℝ)^k)⌋₊
          · exact Or.inl ⟨⟨h1,hle⟩,hp⟩
          · exact Or.inr ⟨⟨by omega,h2⟩,hp⟩
        · rintro (⟨⟨h1,h2⟩,hp⟩ | ⟨⟨h1,h2⟩,hp⟩)
          · exact ⟨⟨h1,h2.trans hmono⟩,hp⟩
          · exact ⟨⟨hp.one_le,h2⟩,hp⟩
      have hdisj:Disjoint (z5 ⌊x^((2 : ℝ)^k)⌋₊)
          (z2 ⌊x^((2 : ℝ)^k)⌋₊ ⌊x^((2 : ℝ)^(k+1))⌋₊):=by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        simp only [z5,z2,mem_filter,mem_Icc,mem_Ioc] at hp1 hp2
        omega
      rw [hunion,Finset.sum_union hdisj]
  rw [h_split M]
  have h_part1:∑ p∈z5 ⌊x⌋₊,(1 : ℝ)/ (p:ℝ)^(1+1/ Real.log x) ≤
      2*Real.log (Real.log x)+15:=by
    refine (sum_le_sum fun p hp=>?_).trans (yJ hx1)
    have hp1:(1 : ℝ)≤ p:=by exact_mod_cast (mem_filter.mp hp).2.one_le
    have hpow:(p:ℝ)≤ (p:ℝ)^(1+1/ Real.log x):=by
      conv_lhs=>rw [← Real.rpow_one (p:ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le hp1 hσ.le
    exact one_div_le_one_div_of_le (by positivity) hpow
  have h_part2:∑ m∈Finset.range M,
      ∑ p∈z2 ⌊x^((2 : ℝ)^m)⌋₊ ⌊x^((2 : ℝ)^(m+1))⌋₊,
        (1 : ℝ)/ (p:ℝ)^(1+1/ Real.log x)≤ 30:=by
    have hblock:∀ m:ℕ,
        ∑ p∈z2 ⌊x^((2 : ℝ)^m)⌋₊ ⌊x^((2 : ℝ)^(m+1))⌋₊,
          (1 : ℝ)/ (p:ℝ)^(1+1/ Real.log x) ≤
        15*(1/ 2 : ℝ)^m:=by
      intro m
      have h2m_ge:(1 : ℝ)≤ (2 : ℝ)^m:=one_le_pow₀ (by norm_num)
      have hx2m_ge:2≤ x^((2 : ℝ)^m):=by
        have hx2:(2 : ℝ)≤ x:=by linarith [Real.add_one_le_exp (1 : ℝ)]
        calc (2 : ℝ)≤ x:=hx2
          _=x^(1 : ℝ):=(Real.rpow_one x).symm
          _≤ x^((2 : ℝ)^m):=Real.rpow_le_rpow_of_exponent_le (by linarith) h2m_ge
      have hx_le:x^((2 : ℝ)^m)≤ x^((2 : ℝ)^(m+1)):=by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith [Real.add_one_le_exp (1 : ℝ)])
        rw [pow_succ]; linarith
      have hfactor:∀ p∈z2 ⌊x^((2 : ℝ)^m)⌋₊ ⌊x^((2 : ℝ)^(m+1))⌋₊,
          (1 : ℝ)/ (p:ℝ)^(1+1/ Real.log x) ≤
            Real.exp (-((2 : ℝ)^m))*((1 : ℝ)/ (p:ℝ)):=by
        intro p hp
        have hp_gt:x^((2 : ℝ)^m)< (p:ℝ):=by
          have h1:⌊x^((2 : ℝ)^m)⌋₊< p:=(mem_Ioc.mp (mem_filter.mp hp).1).1
          have h2:(⌊x^((2 : ℝ)^m)⌋₊ : ℝ)+1≤ (p:ℝ):=by exact_mod_cast h1
          linarith [Nat.lt_floor_add_one (x^((2 : ℝ)^m))]
        have hp_pos:(0 : ℝ)< p:=by exact_mod_cast (mem_filter.mp hp).2.pos
        have hrhs_eq:(1 : ℝ)/ (p:ℝ)^(1+1/ Real.log x) =
            (p:ℝ)^(-(1/ Real.log x))*((1 : ℝ)/ (p:ℝ)):=by
          rw [Real.rpow_add hp_pos,Real.rpow_one,Real.rpow_neg hp_pos.le]
          field_simp
        rw [hrhs_eq]
        gcongr
        have h_rpow:(p:ℝ)^(-(1/ Real.log x))≤ (x^((2 : ℝ)^m))^(-(1/ Real.log x)):=by
          rw [Real.rpow_neg hp_pos.le,Real.rpow_neg (by linarith)]
          exact inv_anti₀ (by positivity) (Real.rpow_le_rpow (by linarith) hp_gt.le (by positivity))
        refine h_rpow.trans_eq ?_
        rw [← Real.rpow_mul hx_pos.le,Real.rpow_def_of_pos hx_pos]
        congr 1
        have hne:Real.log x≠0:=by linarith
        field_simp
      have hmert:=yk hx2m_ge hx_le
      have hratio:Real.log (x^((2 : ℝ)^(m+1)))/ Real.log (x^((2 : ℝ)^m))=2:=by
        rw [Real.log_rpow hx_pos,Real.log_rpow hx_pos,pow_succ]
        have hne1:Real.log x≠0:=by linarith
        have hne2:(2 : ℝ)^m≠0:=by positivity
        field_simp
      rw [hratio] at hmert
      have hlog2:Real.log 2≤ 1:=by
        linarith [Real.log_le_sub_one_of_pos (by norm_num:(0 : ℝ)< 2)]
      have h15:∑ p∈z2 ⌊x^((2 : ℝ)^m)⌋₊ ⌊x^((2 : ℝ)^(m+1))⌋₊,(1 : ℝ)/ (p:ℝ)≤ 15:=by
        linarith
      have hexp_le:Real.exp (-((2 : ℝ)^m))≤ (1/ 2 : ℝ)^m:=by
        have h2m:(m:ℝ)≤ (2 : ℝ)^m:=by
          exact_mod_cast Nat.lt_two_pow_self.le
        have h1:(1/ 2 : ℝ)^m=Real.exp (-(Real.log 2*(m:ℝ))):=by
          rw [Real.exp_neg,Real.exp_mul,Real.exp_log (by norm_num),Real.rpow_natCast,
            one_div,inv_pow]
        rw [h1]
        apply Real.exp_le_exp.mpr
        nlinarith [Nat.cast_nonneg (α:=ℝ) m]
      calc
        ∑ p∈z2 ⌊x^((2 : ℝ)^m)⌋₊ ⌊x^((2 : ℝ)^(m+1))⌋₊,
            (1 : ℝ)/ (p:ℝ)^(1+1/ Real.log x)
            ≤ ∑ p∈z2 ⌊x^((2 : ℝ)^m)⌋₊ ⌊x^((2 : ℝ)^(m+1))⌋₊,
              Real.exp (-((2 : ℝ)^m))*((1 : ℝ)/ (p:ℝ)) :=
              sum_le_sum hfactor
        _=Real.exp (-((2 : ℝ)^m)) *
              ∑ p∈z2 ⌊x^((2 : ℝ)^m)⌋₊ ⌊x^((2 : ℝ)^(m+1))⌋₊,(1 : ℝ)/ (p:ℝ):=by
              rw [← mul_sum]
        _≤ Real.exp (-((2 : ℝ)^m))*15:=mul_le_mul_of_nonneg_left h15 (Real.exp_pos _).le
        _≤ (1/ 2 : ℝ)^m*15:=by gcongr
        _=15*(1/ 2 : ℝ)^m:=mul_comm _ _
    refine (sum_le_sum fun m _=>hblock m).trans ?_
    rw [← mul_sum]
    have hgeom:∑ m∈Finset.range M,(1/ 2 : ℝ)^m≤ 2:=by
      rw [geom_sum_eq (by norm_num:(1/ 2 : ℝ)≠1)]
      have hnn:0≤ (1/ 2 : ℝ)^M:=by positivity
      have heq:((1/ 2 : ℝ)^M - 1)/ (1/ 2 - 1)=2*(1 - (1/ 2 : ℝ)^M):=by ring
      linarith
    linarith
  linarith
lemma xl :
    ∃ C> (0 : ℝ),∃ δ> (0 : ℝ),δ≤ 1/ 2 ∧
      ∀ z:ℂ,z≠0→‖z‖≤ δ→‖z*riemannZeta (1+z) - 1‖≤ C*‖z‖:=by
  have hO:=isBigO_riemannZeta_sub_one_div (F:=ℝ)
  rw [Asymptotics.isBigO_iff] at hO
  rcases hO with ⟨C0,hEv⟩
  rw [Metric.eventually_nhds_iff] at hEv
  rcases hEv with ⟨δ0,hδ0,hbound⟩
  refine ⟨max C0 1,by positivity,min (δ0/ 2) (1/ 2),by positivity,min_le_right _ _,?_⟩
  intro z hz hznorm
  have hdist:dist (1+z) (1 : ℂ)< δ0:=by
    rw [Complex.dist_eq,add_sub_cancel_left]
    exact lt_of_le_of_lt (hznorm.trans (min_le_left _ _)) (by linarith)
  have hb:=hbound hdist
  simp only [norm_one,mul_one] at hb
  have heq:z*riemannZeta (1+z) - 1=z*(riemannZeta (1+z) - 1/ ((1+z) - 1)):=by
    rw [add_sub_cancel_left]
    field_simp [hz]
  rw [heq,norm_mul]
  calc
    ‖z‖*‖riemannZeta (1+z) - 1/ ((1+z) - 1)‖≤ ‖z‖*C0:=by gcongr
    _≤ ‖z‖*max C0 1:=by gcongr; exact le_max_left _ _
    _=max C0 1*‖z‖:=mul_comm _ _
lemma xU :
    ∃ C> (0 : ℝ),∃ δ> (0 : ℝ),
      ∀ w₁ w₂ : ℂ,0< w₁.re→0< w₂.re→‖w₁‖≤ δ→‖w₂‖≤ δ →
        riemannZeta (1+w₁)≠0∧riemannZeta (1+w₂)≠0∧w₁+w₂≠0 ∧
        ‖riemannZeta (1+w₁+w₂)/ (riemannZeta (1+w₁)*riemannZeta (1+w₂)) -
            w₁*w₂/ (w₁+w₂)‖ ≤
          C*‖w₁*w₂/ (w₁+w₂)‖*(‖w₁‖+‖w₂‖):=by
  rcases xl with ⟨C0,hC0,δ0,hδ0,_,hZ⟩
  let δ : ℝ:=min (δ0/ 2) (1/ (4*C0))
  have hδ : 0< δ:=by positivity
  refine ⟨12*C0+1,by positivity,δ,hδ,?_⟩
  intro w₁ w₂ hw1re hw2re hw1n hw2n
  have hw1_ne:w₁≠0:=by intro h; rw [h] at hw1re; simp at hw1re
  have hw2_ne:w₂≠0:=by intro h; rw [h] at hw2re; simp at hw2re
  have hw12_ne:w₁+w₂≠0:=by
    intro h
    have hre:(w₁+w₂).re=0:=by rw [h]; simp
    rw [Complex.add_re] at hre
    linarith
  have hw1_le:‖w₁‖≤ δ0:=hw1n.trans ((min_le_left _ _).trans (by linarith))
  have hw2_le:‖w₂‖≤ δ0:=hw2n.trans ((min_le_left _ _).trans (by linarith))
  have hw12_le:‖w₁+w₂‖≤ δ0:=by
    calc ‖w₁+w₂‖≤ ‖w₁‖+‖w₂‖:=norm_add_le _ _
      _≤ δ+δ:=add_le_add hw1n hw2n
      _≤ δ0/ 2+δ0/ 2:=add_le_add (min_le_left _ _) (min_le_left _ _)
      _=δ0:=by ring
  set a₁:=w₁*riemannZeta (1+w₁)
  set a₂:=w₂*riemannZeta (1+w₂)
  set a₁₂:=(w₁+w₂)*riemannZeta (1+(w₁+w₂))
  have ha1:‖a₁ - 1‖≤ C0*‖w₁‖:=hZ w₁ hw1_ne hw1_le
  have ha2:‖a₂ - 1‖≤ C0*‖w₂‖:=hZ w₂ hw2_ne hw2_le
  have ha12:‖a₁₂ - 1‖≤ C0*‖w₁+w₂‖:=hZ (w₁+w₂) hw12_ne hw12_le
  have hCw1:C0*‖w₁‖≤ 1/ 4:=by
    calc C0*‖w₁‖≤ C0*(1/ (4*C0)):=mul_le_mul_of_nonneg_left (hw1n.trans (min_le_right _ _)) hC0.le
      _=1/ 4:=by field_simp
  have hCw2:C0*‖w₂‖≤ 1/ 4:=by
    calc C0*‖w₂‖≤ C0*(1/ (4*C0)):=mul_le_mul_of_nonneg_left (hw2n.trans (min_le_right _ _)) hC0.le
      _=1/ 4:=by field_simp
  have hna1_lb:1/ 2≤ ‖a₁‖:=by
    have htri:‖(1 : ℂ)‖≤ ‖a₁‖+‖1 - a₁‖:=by
      simpa [add_sub_cancel] using norm_add_le a₁ (1 - a₁)
    rw [norm_one,norm_sub_rev] at htri
    linarith
  have hna2_lb:1/ 2≤ ‖a₂‖:=by
    have htri:‖(1 : ℂ)‖≤ ‖a₂‖+‖1 - a₂‖:=by
      simpa [add_sub_cancel] using norm_add_le a₂ (1 - a₂)
    rw [norm_one,norm_sub_rev] at htri
    linarith
  have hna2_ub:‖a₂‖≤ 2:=by
    have htri:‖a₂‖≤ ‖(1 : ℂ)‖+‖a₂ - 1‖:=by
      simpa [add_sub_cancel] using norm_add_le (1 : ℂ) (a₂ - 1)
    rw [norm_one] at htri; linarith
  have ha1_ne:a₁≠0:=by intro h; rw [h,norm_zero] at hna1_lb; linarith
  have ha2_ne:a₂≠0:=by intro h; rw [h,norm_zero] at hna2_lb; linarith
  have hz1_ne:riemannZeta (1+w₁)≠0:=right_ne_zero_of_mul ha1_ne
  have hz2_ne:riemannZeta (1+w₂)≠0:=right_ne_zero_of_mul ha2_ne
  refine ⟨hz1_ne,hz2_ne,hw12_ne,?_⟩
  have hident:riemannZeta (1+w₁+w₂)/ (riemannZeta (1+w₁)*riemannZeta (1+w₂)) -
      w₁*w₂/ (w₁+w₂) =
      (w₁*w₂/ (w₁+w₂))*((a₁₂ - a₁*a₂)/ (a₁*a₂)):=by
    rw [add_assoc (1 : ℂ) w₁ w₂]
    dsimp only [a₁,a₂,a₁₂]
    field_simp [hw1_ne,hw2_ne,hw12_ne,hz1_ne,hz2_ne]
  have hnum:‖a₁₂ - a₁*a₂‖≤ 3*C0*(‖w₁‖+‖w₂‖):=by
    have hdecomp:a₁₂ - a₁*a₂=(a₁₂ - 1) - (a₁ - 1)*a₂ - (a₂ - 1):=by ring
    rw [hdecomp]
    have h1:‖a₁₂ - 1‖≤ C0*(‖w₁‖+‖w₂‖) :=
      ha12.trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) hC0.le)
    have h2:‖(a₁ - 1)*a₂‖≤ 2*C0*‖w₁‖:=by
      rw [norm_mul]
      calc ‖a₁ - 1‖*‖a₂‖≤ (C0*‖w₁‖)*2:=by gcongr
        _=2*C0*‖w₁‖:=by ring
    have htri:‖(a₁₂ - 1) - (a₁ - 1)*a₂ - (a₂ - 1)‖ ≤
        ‖a₁₂ - 1‖+‖(a₁ - 1)*a₂‖+‖a₂ - 1‖:=by
      calc ‖(a₁₂ - 1) - (a₁ - 1)*a₂ - (a₂ - 1)‖
          ≤ ‖(a₁₂ - 1) - (a₁ - 1)*a₂‖+‖a₂ - 1‖:=norm_sub_le _ _
        _≤ ‖a₁₂ - 1‖+‖(a₁ - 1)*a₂‖+‖a₂ - 1‖:=by gcongr; exact norm_sub_le _ _
    nlinarith [norm_nonneg w₁,norm_nonneg w₂]
  have hden:1/ 4≤ ‖a₁‖*‖a₂‖:=by nlinarith
  have hdiv:‖(a₁₂ - a₁*a₂)/ (a₁*a₂)‖≤ (12*C0+1)*(‖w₁‖+‖w₂‖):=by
    rw [norm_div,norm_mul,div_le_iff₀ (by positivity)]
    have hmul:(12*C0+1)*(‖w₁‖+‖w₂‖)*(1/ 4) ≤
        (12*C0+1)*(‖w₁‖+‖w₂‖)*(‖a₁‖*‖a₂‖) :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    linarith [norm_nonneg w₁,norm_nonneg w₂]
  calc
    ‖riemannZeta (1+w₁+w₂)/ (riemannZeta (1+w₁)*riemannZeta (1+w₂)) -
        w₁*w₂/ (w₁+w₂)‖
        = ‖w₁*w₂/ (w₁+w₂)‖*‖(a₁₂ - a₁*a₂)/ (a₁*a₂)‖:=by rw [hident,norm_mul]
    _≤ ‖w₁*w₂/ (w₁+w₂)‖*((12*C0+1)*(‖w₁‖+‖w₂‖)):=by gcongr
    _=(12*C0+1)*‖w₁*w₂/ (w₁+w₂)‖*(‖w₁‖+‖w₂‖):=by ring
lemma xN {z:ℂ} (hz:0≤ z.re) :
    ‖1 - Complex.exp (-z)‖≤ ‖z‖:=by
  have hderiv:∀ t∈Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s:ℝ=>Complex.exp (-(s:ℂ)*z)) (-z*Complex.exp (-(t:ℂ)*z)) t:=by
    intro t _
    have h1:HasDerivAt (fun s:ℝ=>-(s:ℂ)*z) (-z) t:=by
      have h0:HasDerivAt (fun s:ℝ=>(s:ℂ)) 1 t:=Complex.ofRealCLM.hasDerivAt
      simpa using (h0.neg.mul_const z)
    simpa [mul_comm] using h1.cexp
  have hint:IntervalIntegrable (fun t:ℝ=>-z*Complex.exp (-(t:ℂ)*z)) MeasureTheory.volume 0 1 :=
    (Continuous.intervalIntegrable (by fun_prop) 0 1)
  have hftc:=intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [Complex.ofReal_one,Complex.ofReal_zero,neg_zero,zero_mul,Complex.exp_zero,
    neg_one_mul] at hftc
  have h1:1 - Complex.exp (-z)=-(∫ t in (0 : ℝ)..1,-z*Complex.exp (-(t:ℂ)*z)):=by
    rw [hftc]; ring
  rw [h1,norm_neg]
  have hbound:∀ t∈Set.Ioc (0 : ℝ) 1,‖-z*Complex.exp (-(t:ℂ)*z)‖≤ ‖z‖:=by
    intro t ht
    rw [norm_mul,norm_neg,Complex.norm_exp]
    have hre:(-(t:ℂ)*z).re=-t*z.re:=by simp
    rw [hre]
    have hexp:Real.exp (-t*z.re)≤ 1:=Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
    nlinarith [norm_nonneg z]
  have hle:=intervalIntegral.norm_integral_le_of_norm_le_const (a:=(0 : ℝ)) (b:=1)
    (C:=‖z‖) (f:=fun t:ℝ=>-z*Complex.exp (-(t:ℂ)*z)) fun t ht=>by
      rw [Set.uIoc_of_le (by norm_num)] at ht
      exact hbound t ht
  simpa using hle
lemma zI {p:ℕ} (hp:1≤ p) {z:ℂ} (hz:0≤ z.re) :
    ‖1 - (p:ℂ)^(-z)‖≤ ‖z‖*Real.log (p:ℝ):=by
  have hp_pos:(0 : ℝ)< p:=by positivity
  have hpC:(p:ℂ)≠0:=by exact_mod_cast (show p≠0 by omega)
  have hcpow:(p:ℂ)^(-z)=Complex.exp (-(z*(Real.log (p:ℝ):ℂ))):=by
    rw [Complex.cpow_def_of_ne_zero hpC,← Complex.ofReal_natCast,← Complex.ofReal_log hp_pos.le]
    congr 1; ring
  rw [hcpow]
  have hre:0≤ (z*(Real.log (p:ℝ):ℂ)).re:=by
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_nonneg hz (Real.log_nonneg (by exact_mod_cast hp))
  calc
    ‖1 - Complex.exp (-(z*(Real.log (p:ℝ):ℂ)))‖
        ≤ ‖z*(Real.log (p:ℝ):ℂ)‖:=xN hre
    _=‖z‖*Real.log (p:ℝ):=by
        rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.log_nonneg (by exact_mod_cast hp))]
lemma xs {ι : Type*} (s:Finset ι) (a:ι→ℂ) :
    ‖(∏ i∈s,(1+a i)) - 1‖≤ (∏ i∈s,(1+‖a i‖)) - 1:=by
  classical
  induction s using Finset.induction_on with
  | empty=>simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.prod_insert hi]
    set P:=∏ j∈s,(1+a j)
    set Q:=∏ j∈s,(1+‖a j‖)
    have hQ1:1≤ Q:=Finset.one_le_prod fun j _=>by linarith [norm_nonneg (a j)]
    have hdecomp:(1+a i)*P - 1=(P - 1)+a i*(P - 1)+a i:=by ring
    rw [hdecomp]
    calc
      ‖(P - 1)+a i*(P - 1)+a i‖
          ≤ ‖(P - 1)+a i*(P - 1)‖+‖a i‖:=norm_add_le _ _
      _≤ ‖P - 1‖+‖a i*(P - 1)‖+‖a i‖:=by gcongr; exact norm_add_le _ _
      _=(1+‖a i‖)*‖P - 1‖+‖a i‖:=by rw [norm_mul]; ring
      _≤ (1+‖a i‖)*(Q - 1)+‖a i‖:=by gcongr
      _=(1+‖a i‖)*Q - 1:=by ring
lemma zO {ι : Type*} (s:Finset ι) {b:ι→ℝ} (hb:∀ i∈s,0≤ b i) :
    ∏ i∈s,(1+b i)≤ Real.exp (∑ i∈s,b i):=by
  rw [Real.exp_sum]
  exact prod_le_prod (fun i hi=>by linarith [hb i hi]) fun i _=>by
    linarith [Real.add_one_le_exp (b i)]
lemma y1 {ι : Type*} (s:Finset ι) (a:ι→ℂ) :
    ‖(∏ i∈s,(1+a i)) - 1‖≤ Real.exp (∑ i∈s,‖a i‖) - 1 :=
  (xs s a).trans
    (sub_le_sub_right (zO s fun _ _=>norm_nonneg _) 1)
lemma y2 {t:ℝ} (ht0:0≤ t) (ht1:t≤ 1) :
    Real.exp t - 1≤ 2*t:=by
  have hconv:Real.exp t≤ (1 - t)*Real.exp 0+t*Real.exp 1:=by
    have h1:=convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ)) (by linarith:0≤ 1 - t) ht0 (by ring)
    simpa [smul_eq_mul] using h1
  rw [Real.exp_zero,mul_one] at hconv
  have he3:Real.exp 1≤ 3:=Real.exp_one_lt_d9.le.trans (by norm_num)
  nlinarith
lemma xo {ι : Type*} [DecidableEq ι] (I:Finset ι) (u:ι→ℂ)
    (hu:∀ k∈I,1 - u k≠0) :
    (1 - ∑ k∈I,u k)/ (∏ k∈I,(1 - u k)) =
      1+∑ S∈I.powerset.filter (fun S=>2≤ S.card),
        (1 - (S.card:ℂ))*∏ k∈S,(u k/ (1 - u k)):=by
  let v:ι→ℂ:=fun k=>u k/ (1 - u k)
  have h1v:∀ k∈I,1+v k=(1 - u k)⁻¹:=by
    intro k hk; dsimp [v]; field_simp [hu k hk]; ring
  have huv:∀ k∈I,u k*(1+v k)=v k:=by
    intro k hk; rw [h1v k hk]; dsimp [v]; rw [div_eq_mul_inv]
  have hprod_ne:∏ k∈I,(1 - u k)≠0:=Finset.prod_ne_zero_iff.mpr hu
  have hprod_inv:(∏ k∈I,(1 - u k))⁻¹=∏ k∈I,(1+v k):=by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun k hk=>(h1v k hk).symm
  rw [div_eq_mul_inv,hprod_inv,sub_mul,one_mul,sum_mul]
  have hterm:∀ k∈I,u k*∏ j∈I,(1+v j)=v k*∏ j∈I.erase k,(1+v j):=by
    intro k hk
    rw [← Finset.mul_prod_erase I (fun j=>1+v j) hk,← mul_assoc,huv k hk]
  rw [sum_congr rfl hterm]
  rw [Finset.prod_one_add]
  have hsecond:∑ k∈I,v k*∏ j∈I.erase k,(1+v j) =
      ∑ S∈I.powerset,(S.card:ℂ)*∏ j∈S,v j:=by
    simp_rw [Finset.prod_one_add,mul_sum]
    have hswap:∑ k∈I,∑ T∈(I.erase k).powerset,v k*∏ j∈T,v j =
        ∑ S∈I.powerset,∑ k∈S,∏ j∈S,v j:=by
      trans ∑ S∈I.powerset,∑ k∈I,if k∈S then ∏ j∈S,v j else 0
      · rw [sum_comm]
        refine sum_congr rfl fun k hk=>?_
        rw [← sum_filter]
        refine Finset.sum_bij (fun T _=>insert k T) ?_ ?_ ?_ ?_
        · intro T hT
          rw [mem_filter,Finset.mem_powerset]
          have hT':=Finset.mem_powerset.mp hT
          exact ⟨Finset.insert_subset hk (hT'.trans (Finset.erase_subset k I)),
            Finset.mem_insert_self k T⟩
        · intro T₁ hT₁ T₂ hT₂ heq
          have hk1:k ∉ T₁:=fun h=>(Finset.mem_erase.mp (Finset.mem_powerset.mp hT₁ h)).1 rfl
          have hk2:k ∉ T₂:=fun h=>(Finset.mem_erase.mp (Finset.mem_powerset.mp hT₂ h)).1 rfl
          have:=congrArg (fun S=>S.erase k) heq
          simpa [Finset.erase_insert hk1,Finset.erase_insert hk2] using this
        · intro S hS
          rw [mem_filter,Finset.mem_powerset] at hS
          refine ⟨S.erase k,?_,Finset.insert_erase hS.2⟩
          rw [Finset.mem_powerset]
          exact Finset.erase_subset_erase k hS.1
        · intro T hT
          have hkT:k ∉ T:=fun h=>(Finset.mem_erase.mp (Finset.mem_powerset.mp hT h)).1 rfl
          rw [Finset.prod_insert hkT]
      · refine sum_congr rfl fun S hS=>?_
        rw [← sum_filter]
        have hfilt:I.filter (fun k=>k∈S)=S:=by
          ext k; simp only [mem_filter,and_iff_right_iff_imp]
          exact fun hk=>Finset.mem_powerset.mp hS hk
        rw [hfilt]
    rw [hswap]
    refine sum_congr rfl fun S _=>?_
    rw [sum_const,nsmul_eq_mul]
  rw [hsecond,← sum_sub_distrib]
  have hrew:∀ S∈I.powerset,
      (∏ k∈S,v k) - (S.card:ℂ)*(∏ k∈S,v k) =
        (1 - (S.card:ℂ))*(∏ k∈S,v k):=by
    intro S _; ring
  rw [sum_congr rfl hrew]
  have h_empty:∅∈I.powerset:=Finset.empty_mem_powerset I
  rw [← Finset.add_sum_erase _ _ h_empty]
  simp only [card_empty,Nat.cast_zero,sub_zero,Finset.prod_empty,mul_one]
  congr 1
  rw [← Finset.sum_filter_of_ne (p:=fun S=>2≤ S.card)]
  · congr 1
    ext S
    simp only [mem_filter,Finset.mem_erase,Finset.mem_powerset]
    constructor
    · rintro ⟨⟨_,hSI⟩,hcard⟩; exact ⟨hSI,hcard⟩
    · rintro ⟨hSI,hcard⟩
      exact ⟨⟨by intro h; subst h; simp at hcard,hSI⟩,hcard⟩
  · intro S hS hne
    have hS0:S≠∅:=(Finset.mem_erase.mp hS).1
    have hpos:1≤ S.card:=Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS0)
    by_contra hlt
    have h1:S.card=1:=by omega
    rw [h1] at hne
    simp at hne
lemma x4 {m:ℕ} (hm:1≤ m) :
    ∑' n:{n:ℕ // m< n},(1 : ℝ)/ ((n:ℕ):ℝ)^2≤ 1/ (m:ℝ):=by
  refine Real.tsum_le_of_sum_le (fun _=>by positivity) fun s=>?_
  let N:ℕ:=max m (s.sup (fun x:{n:ℕ // m< n}=>(x:ℕ)))
  have h_embed:∑ x∈s,(1 : ℝ)/ ((x:ℕ):ℝ)^2 ≤
      ∑ n∈Finset.Ioc m N,(1 : ℝ)/ (n:ℝ)^2:=by
    rw [show ∑ x∈s,(1 : ℝ)/ ((x:ℕ):ℝ)^2 =
        ∑ n∈s.image (fun x:{n:ℕ // m< n}=>(x:ℕ)),(1 : ℝ)/ (n:ℝ)^2 by
      rw [Finset.sum_image]
      intro a _ b _ h; exact Subtype.ext h]
    refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _=>by positivity)
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨x,hxs,rfl⟩
    exact mem_Ioc.mpr ⟨x.prop,le_trans (Finset.le_sup (f:=fun y:{n:ℕ // m< n}=>(y:ℕ)) hxs) (le_max_right _ _)⟩
  refine h_embed.trans ?_
  have htele:∑ n∈Finset.Ioc m N,(1 : ℝ)/ (n:ℝ)^2 ≤
      ∑ n∈Finset.Ioc m N,((1 : ℝ)/ ((n - 1 : ℕ):ℝ) - (1 : ℝ)/ (n:ℝ)):=by
    refine sum_le_sum fun n hn=>?_
    have hn_gt:m< n:=(mem_Ioc.mp hn).1
    have hn2:2≤ n:=by omega
    have hn0:(0 : ℝ)< n:=by positivity
    have hn1:(0 : ℝ)< (n - 1 : ℕ):=by exact_mod_cast (show 0< n - 1 by omega)
    have hcast:((n - 1 : ℕ):ℝ)=(n:ℝ) - 1:=by
      simpa using Nat.cast_sub (R:=ℝ) (show 1≤ n by omega)
    rw [hcast]
    have hdiff:(1 : ℝ)/ ((n:ℝ) - 1) - 1/ (n:ℝ)=1/ (((n:ℝ) - 1)*(n:ℝ)):=by
      have : (n:ℝ) - 1≠0:=by linarith
      field_simp; ring
    rw [hdiff]
    exact one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
  refine htele.trans ?_
  have h_eval:∀ k:ℕ,m≤ k →
      ∑ n∈Finset.Ioc m k,((1 : ℝ)/ ((n - 1 : ℕ):ℝ) - (1 : ℝ)/ (n:ℝ)) =
        (1 : ℝ)/ (m:ℝ) - (1 : ℝ)/ (k:ℝ):=by
    intro k hk
    induction k with
    | zero=>omega
    | succ j ih =>
      rcases eq_or_lt_of_le hk with rfl | hlt
      · simp
      · have hIoc:Finset.Ioc m (j+1)=insert (j+1) (Finset.Ioc m j):=by
          ext x; simp only [mem_Ioc,mem_insert]; omega
        rw [hIoc,sum_insert (by simp),ih (by omega)]
        simp only [Nat.add_sub_cancel]
        ring
  rw [h_eval N (le_max_left _ _)]
  have : 0≤ (1 : ℝ)/ (N:ℝ):=by positivity
  linarith
lemma xc (M:ℕ) :
    ∑ k∈Finset.Icc 2 M,(1 : ℝ)/ (k:ℝ)^2≤ 1:=by
  have h_le:∑ k∈Finset.Icc 2 M,(1 : ℝ)/ (k:ℝ)^2 ≤
      ∑ k∈Finset.Ioc 1 M,((1 : ℝ)/ ((k - 1 : ℕ):ℝ) - (1 : ℝ)/ (k:ℝ)):=by
    have hset:Finset.Icc 2 M=Finset.Ioc 1 M:=by
      ext k; simp only [mem_Icc,mem_Ioc]; omega
    rw [hset]
    refine sum_le_sum fun k hk=>?_
    have hk2:2≤ k:=by have:=(mem_Ioc.mp hk).1; omega
    have hk0:(0 : ℝ)< k:=by positivity
    have hcast:((k - 1 : ℕ):ℝ)=(k:ℝ) - 1:=by
      simpa using Nat.cast_sub (R:=ℝ) (show 1≤ k by omega)
    rw [hcast]
    have h1:(0 : ℝ)< (k:ℝ) - 1:=by
      have : (2 : ℝ)≤ k:=by exact_mod_cast hk2
      linarith
    have hdiff:(1 : ℝ)/ ((k:ℝ) - 1) - 1/ (k:ℝ)=1/ (((k:ℝ) - 1)*(k:ℝ)):=by
      field_simp; ring
    rw [hdiff]
    exact one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
  refine h_le.trans ?_
  rcases eq_or_ne M 0 with rfl | hM0
  · simp
  · have h_eval:∀ k:ℕ,1≤ k →
        ∑ n∈Finset.Ioc 1 k,((1 : ℝ)/ ((n - 1 : ℕ):ℝ) - (1 : ℝ)/ (n:ℝ)) =
          1 - (1 : ℝ)/ (k:ℝ):=by
      intro k hk
      induction k with
      | zero=>omega
      | succ j ih =>
        rcases eq_or_lt_of_le hk with h1 | hlt
        · have hj:j=0:=by omega
          subst hj; simp
        · have hIoc:Finset.Ioc 1 (j+1)=insert (j+1) (Finset.Ioc 1 j):=by
            ext x; simp only [mem_Ioc,mem_insert]; omega
          rw [hIoc,sum_insert (by simp),ih (by omega)]
          simp only [Nat.add_sub_cancel]
          ring
    rw [h_eval M (by omega)]
    have : 0≤ (1 : ℝ)/ (M:ℝ):=by positivity
    linarith
lemma xn {m:ℕ} (hm:1≤ m) :
    ((ArithmeticFunction.cardDistinctFactors m:ℕ):ℝ)≤ 2*Real.log (m:ℝ):=by
  have h2pow:2^(ArithmeticFunction.cardDistinctFactors m)≤ m:=by
    rw [ArithmeticFunction.cardDistinctFactors_apply]
    have hprod_le:∏ p∈m.primeFactors,2≤ ∏ p∈m.primeFactors,p :=
      prod_le_prod' fun p hp=>(Nat.prime_of_mem_primeFactors hp).two_le
    rw [prod_const] at hprod_le
    have hdiv:(∏ p∈m.primeFactors,p)∣m:=Nat.prod_primeFactors_dvd m
    exact hprod_le.trans (Nat.le_of_dvd (by omega) hdiv)
  have hlog:((ArithmeticFunction.cardDistinctFactors m:ℕ):ℝ)*Real.log 2≤ Real.log (m:ℝ):=by
    have hR:(2 : ℝ)^(ArithmeticFunction.cardDistinctFactors m)≤ (m:ℝ):=by
      exact_mod_cast h2pow
    calc
      ((ArithmeticFunction.cardDistinctFactors m:ℕ):ℝ)*Real.log 2
          = Real.log ((2 : ℝ)^(ArithmeticFunction.cardDistinctFactors m)):=(Real.log_pow 2 _).symm
      _≤ Real.log (m:ℝ):=Real.log_le_log (by positivity) hR
  nlinarith [zC,Nat.cast_nonneg (α:=ℝ) (ArithmeticFunction.cardDistinctFactors m)]
lemma xI {x:ℝ} (hx:1≤ x) :
    (primorial ⌊0.15*Real.log x⌋₊ : ℝ)≤ x^(0.25 : ℝ):=by
  have hlogx:0≤ Real.log x:=Real.log_nonneg hx
  have h1:(primorial ⌊0.15*Real.log x⌋₊ : ℝ)≤ (4 : ℝ)^⌊0.15*Real.log x⌋₊:=by
    exact_mod_cast primorial_le_four_pow ⌊0.15*Real.log x⌋₊
  refine h1.trans ?_
  rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num:(0 : ℝ)< 4),
    Real.rpow_def_of_pos (by linarith:(0 : ℝ)< x)]
  apply Real.exp_le_exp.mpr
  have hfl:(⌊0.15*Real.log x⌋₊ : ℝ)≤ 0.15*Real.log x:=Nat.floor_le (by positivity)
  have hlog4:=xO
  nlinarith [Real.log_nonneg (by norm_num:(1 : ℝ)≤ 4)]
end
end Erdos413Mertens
namespace Erdos413Bump
open MeasureTheory Complex Real Filter Set Topology
open scoped FourierTransform
noncomputable section
def phi (t:ℝ):ℝ:=expNegInvGlue t
lemma yR:ContDiff ℝ (⊤ : ℕ∞) phi :=
  expNegInvGlue.contDiff
lemma w3 (t:ℝ):0≤ phi t :=
  expNegInvGlue.nonneg t
lemma yr {t:ℝ} (ht:t≤ 0):phi t=0 :=
  expNegInvGlue.zero_of_nonpos ht
lemma wj {t:ℝ} (ht:0< t):0< phi t :=
  expNegInvGlue.pos_of_pos ht
lemma wK (t:ℝ):phi t≤ 1:=by
  unfold phi expNegInvGlue
  split_ifs with h
  · linarith
  · push Not at h
    have hinv:0< t⁻¹:=inv_pos.mpr h
    exact Real.exp_le_one_iff.mpr (by linarith)
private lemma xv {f:ℂ→ℂ} {t r:ℝ} (hr:0< r)
    (hf:DifferentiableOn ℂ f (Metric.ball (t:ℂ) r)) :
    ∀ m:ℕ,iteratedDeriv m (fun y:ℝ=>f (y:ℂ)) t=iteratedDeriv m f (t:ℂ):=by
  have h_ana:∀ m:ℕ,AnalyticOnNhd ℂ (iteratedDeriv m f) (Metric.ball (t:ℂ) r):=by
    intro m
    induction m with
    | zero=>simpa using hf.analyticOnNhd Metric.isOpen_ball
    | succ m ih =>
      have hsucc:iteratedDeriv (m+1) f=deriv (iteratedDeriv m f):=iteratedDeriv_succ
      rw [hsucc]
      exact ih.deriv
  have h_all:∀ m:ℕ,∀ y:ℝ,y∈Metric.ball t r →
      iteratedDeriv m (fun s:ℝ=>f (s:ℂ)) y=iteratedDeriv m f (y:ℂ):=by
    intro m
    induction m with
    | zero=>intro y _; simp
    | succ m ih =>
      intro y hy
      rw [iteratedDeriv_succ,iteratedDeriv_succ]
      have hyC:(y:ℂ)∈Metric.ball (t:ℂ) r:=by
        rw [Metric.mem_ball,Complex.dist_eq,← Complex.ofReal_sub,Complex.norm_real,
          Real.norm_eq_abs]
        simpa [Metric.mem_ball,Real.dist_eq] using hy
      have h_diff_m:DifferentiableAt ℂ (iteratedDeriv m f) (y:ℂ) :=
        (h_ana m (y:ℂ) hyC).differentiableAt
      have h_eq:(iteratedDeriv m (fun s:ℝ=>f (s:ℂ))) =ᶠ[𝓝 y]
          (fun s:ℝ=>iteratedDeriv m f (s:ℂ)):=by
        filter_upwards [Metric.isOpen_ball.mem_nhds hy] with s hs
        exact ih s hs
      rw [h_eq.deriv_eq]
      exact (h_diff_m.hasDerivAt.comp_ofReal).deriv
  intro m
  exact h_all m t (Metric.mem_ball_self hr)
private lemma yL {f:ℝ→ℝ} (hf:ContDiff ℝ (⊤ : ℕ∞) f) :
    ∀ m:ℕ,iteratedDeriv m (fun y:ℝ=>(f y:ℂ))=fun y:ℝ=>((iteratedDeriv m f y:ℝ):ℂ):=by
  intro m
  induction m with
  | zero=>ext y; simp
  | succ m ih =>
    ext y
    rw [iteratedDeriv_succ,iteratedDeriv_succ,ih]
    have hdiff:DifferentiableAt ℝ (iteratedDeriv m f) y :=
      hf.differentiable_iteratedDeriv m (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m)) y
    have hcomp:HasDerivAt (fun x:ℝ=>((iteratedDeriv m f x:ℝ):ℂ))
        ((deriv (iteratedDeriv m f) y:ℝ):ℂ) y:=by
      rw [hasDerivAt_iff_tendsto_slope]
      have hd:=hasDerivAt_iff_tendsto_slope.mp hdiff.hasDerivAt
      have hc:=(Complex.continuous_ofReal.tendsto (deriv (iteratedDeriv m f) y)).comp hd
      refine hc.congr fun s=>?_
      simp [slope_def_module,Complex.real_smul]
    exact hcomp.deriv
lemma yZ (m:ℕ) (t:ℝ) :
    |iteratedDeriv m phi t|≤ (9 : ℝ)^m*(m.factorial:ℝ)^2:=by
  have h_pos:∀ s:ℝ,0< s →
      |iteratedDeriv m phi s|≤ (9 : ℝ)^m*(m.factorial:ℝ)^2:=by
    intro s hs
    let fC:ℂ→ℂ:=fun z=>Complex.exp (-z⁻¹)
    have hR:0< s/ 2:=half_pos hs
    have h_nz:∀ z∈Metric.closedBall (s:ℂ) (s/ 2),s/ 2≤ z.re:=by
      intro z hz
      rw [Metric.mem_closedBall,Complex.dist_eq] at hz
      have hre:|(z - (s:ℂ)).re|≤ ‖z - (s:ℂ)‖:=Complex.abs_re_le_norm _
      simp only [Complex.sub_re,Complex.ofReal_re] at hre
      linarith [(abs_le.mp (hre.trans hz)).1]
    have h_diff_cb:∀ z∈Metric.closedBall (s:ℂ) (s/ 2),DifferentiableAt ℂ fC z:=by
      intro z hz
      have hre:0< z.re:=by linarith [h_nz z hz]
      have hne:z≠0:=by
        intro h0
        rw [h0] at hre
        simp at hre
      exact (((differentiableAt_id.inv hne).neg).cexp)
    have h_diffCl:DiffContOnCl ℂ fC (Metric.ball (s:ℂ) (s/ 2)):=by
      refine ⟨fun z hz=>(h_diff_cb z (Metric.ball_subset_closedBall hz)).differentiableWithinAt,
        ?_⟩
      rw [closure_ball (s:ℂ) hR.ne']
      exact fun z hz=>(h_diff_cb z hz).continuousAt.continuousWithinAt
    have h_sphere:∀ z∈Metric.sphere (s:ℂ) (s/ 2),
        ‖fC z‖≤ Real.exp (-(2/ (9*s))):=by
      intro z hz
      have hcb:z∈Metric.closedBall (s:ℂ) (s/ 2):=Metric.sphere_subset_closedBall hz
      have hre:s/ 2≤ z.re:=h_nz z hcb
      have hnorm:‖z‖≤ 3*s/ 2:=by
        have h1:‖z - (s:ℂ)‖=s/ 2:=by
          rw [Metric.mem_sphere,Complex.dist_eq] at hz; exact hz
        have h2:‖z‖≤ ‖z - (s:ℂ)‖+‖(s:ℂ)‖:=norm_le_norm_sub_add z (s:ℂ)
        rw [h1,Complex.norm_of_nonneg hs.le] at h2
        linarith
      have hnsq_pos:0< Complex.normSq z:=by
        rw [Complex.normSq_pos]
        intro h0
        rw [h0] at hre
        simp at hre
        linarith
      have hnsq_le:Complex.normSq z≤ 9*s^2/ 4:=by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [norm_nonneg z]
      rw [Complex.norm_exp,Complex.neg_re,Complex.inv_re]
      apply Real.exp_le_exp.mpr
      rw [neg_le_neg_iff]
      rw [div_le_div_iff₀ (by positivity) hnsq_pos]
      nlinarith
    have h_cauchy:=Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m hR h_diffCl
      h_sphere
    have h_eq_real:iteratedDeriv m (fun y:ℝ=>(phi y:ℂ)) s =
        iteratedDeriv m fC (s:ℂ):=by
      have h_ev:(fun y:ℝ=>(phi y:ℂ)) =ᶠ[𝓝 s] (fun y:ℝ=>fC (y:ℂ)):=by
        filter_upwards [lt_mem_nhds hs] with y hy
        simp [phi,expNegInvGlue,not_le.mpr hy,fC,Complex.ofReal_exp]
      rw [h_ev.iteratedDeriv_eq m]
      exact xv hR (fun z hz=>h_diffCl.1 z hz) m
    have h_ofReal:iteratedDeriv m (fun y:ℝ=>(phi y:ℂ)) s =
        ((iteratedDeriv m phi s:ℝ):ℂ) :=
      congrFun (yL yR m) s
    have h_norm_eq:|iteratedDeriv m phi s|=‖iteratedDeriv m fC (s:ℂ)‖:=by
      rw [← h_eq_real,h_ofReal,Complex.norm_real,Real.norm_eq_abs]
    rw [h_norm_eq]
    have hu:0< 2/ (9*s):=by positivity
    have hexp_inv:Real.exp (-(2/ (9*s))) ≤
        (m.factorial:ℝ)/ (2/ (9*s))^m:=by
      rw [Real.exp_neg,le_div_iff₀ (pow_pos hu m)]
      have hpow:(2/ (9*s))^m/ (m.factorial:ℝ)≤ Real.exp (2/ (9*s)) :=
        Real.pow_div_factorial_le_exp _ hu.le m
      have hfac:(0 : ℝ)< m.factorial:=by positivity
      have hexp_pos:0< Real.exp (2/ (9*s)):=Real.exp_pos _
      rw [inv_mul_eq_div,div_le_iff₀ hexp_pos]
      have:=(div_le_iff₀ hfac).mp hpow
      linarith
    calc
      ‖iteratedDeriv m fC (s:ℂ)‖
          ≤ (m.factorial:ℝ)*Real.exp (-(2/ (9*s)))/ (s/ 2)^m:=h_cauchy
      _≤ (m.factorial:ℝ)*((m.factorial:ℝ)/ (2/ (9*s))^m)/ (s/ 2)^m:=by
          gcongr
      _=(9 : ℝ)^m*(m.factorial:ℝ)^2:=by
          have hs0:s≠0:=hs.ne'
          have hprod:(2/ (9*s))^m*(s/ 2)^m=((9 : ℝ)^m)⁻¹:=by
            rw [← mul_pow,← inv_pow]
            congr 1; field_simp
          rw [mul_div_assoc,div_div,hprod,div_inv_eq_mul]
          ring
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have h_ev:phi =ᶠ[𝓝 t] (0 : ℝ→ℝ):=by
      filter_upwards [gt_mem_nhds ht] with y hy
      exact yr hy.le
    rw [h_ev.iteratedDeriv_eq m,iteratedDeriv_const_zero,abs_zero]
    positivity
  · have h_cont:Continuous (iteratedDeriv m phi) :=
      yR.continuous_iteratedDeriv m (by exact_mod_cast le_top)
    have h_zero_left:Tendsto (iteratedDeriv m phi) (𝓝[<] (0 : ℝ)) (𝓝 0):=by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      have h_ev:phi =ᶠ[𝓝 y] (0 : ℝ→ℝ):=by
        filter_upwards [gt_mem_nhds hy] with z hz
        exact yr hz.le
      rw [h_ev.iteratedDeriv_eq m,iteratedDeriv_const_zero]
    have h_val:iteratedDeriv m phi 0=0 :=
      tendsto_nhds_unique (h_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) h_zero_left
    rw [h_val,abs_zero]
    positivity
  · exact h_pos t ht
def zq (u:ℝ):ℝ:=phi (1/ 2 - u)*phi (1/ 2+u)
lemma yB:ContDiff ℝ (⊤ : ℕ∞) zq:=by
  unfold zq
  exact (yR.comp (contDiff_const.sub contDiff_id)).mul
    (yR.comp (contDiff_const.add contDiff_id))
lemma zt:Continuous zq:=yB.continuous
lemma yO (u:ℝ):0≤ zq u :=
  mul_nonneg (w3 _) (w3 _)
lemma wD (u:ℝ):zq u≤ 1:=by
  unfold zq
  have h1:=wK (1/ 2 - u)
  have h2:=wK (1/ 2+u)
  nlinarith [w3 (1/ 2 - u),w3 (1/ 2+u)]
lemma wn (u:ℝ):zq (-u)=zq u:=by
  unfold zq
  rw [sub_neg_eq_add,← sub_eq_add_neg,mul_comm]
lemma zm {u:ℝ} (hu:1/ 2≤ |u|):zq u=0:=by
  unfold zq
  rcases le_or_gt 0 u with h0 | h0
  · rw [abs_of_nonneg h0] at hu
    rw [yr (by linarith:1/ 2 - u≤ 0),zero_mul]
  · rw [abs_of_neg h0] at hu
    rw [yr (by linarith:1/ 2+u≤ 0),mul_zero]
lemma wr {u:ℝ} (hu:|u|< 1/ 2):0< zq u:=by
  unfold zq
  have h:=abs_lt.mp hu
  exact mul_pos (wj (by linarith)) (wj (by linarith))
lemma zS:HasCompactSupport zq:=by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=-(1/ 2 : ℝ)) (b:=1/ 2)) ?_
  intro u hu
  rw [Function.mem_support] at hu
  by_contra hnot
  apply hu
  apply zm
  rw [Set.mem_Icc,not_and_or,not_le,not_le] at hnot
  rcases hnot with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith
lemma ya (m:ℕ) {u:ℝ} (hu:1/ 2< |u|) :
    iteratedDeriv m zq u=0:=by
  have h_ev:zq =ᶠ[𝓝 u] (0 : ℝ→ℝ):=by
    have hopen:IsOpen {v:ℝ | 1/ 2< |v|}:=isOpen_lt continuous_const continuous_abs
    filter_upwards [hopen.mem_nhds hu] with v hv
    exact zm hv.le
  rw [h_ev.iteratedDeriv_eq m,iteratedDeriv_const_zero]
lemma xJ (m:ℕ) (u:ℝ) :
    |iteratedDeriv m zq u|≤ 2*(18 : ℝ)^m*(m.factorial:ℝ)^2:=by
  have hf:ContDiffAt ℝ m (fun v:ℝ=>phi (1/ 2 - v)) u :=
    ((yR.comp (contDiff_const.sub contDiff_id)).of_le (by exact_mod_cast le_top)).contDiffAt
  have hg:ContDiffAt ℝ m (fun v:ℝ=>phi (1/ 2+v)) u :=
    ((yR.comp (contDiff_const.add contDiff_id)).of_le (by exact_mod_cast le_top)).contDiffAt
  have hmul:iteratedDeriv m zq u =
      ∑ i∈Finset.range (m+1),
        (m.choose i:ℝ)*iteratedDeriv i (fun v:ℝ=>phi (1/ 2 - v)) u *
          iteratedDeriv (m - i) (fun v:ℝ=>phi (1/ 2+v)) u:=by
    change iteratedDeriv m (fun v:ℝ=>phi (1/ 2 - v)*phi (1/ 2+v)) u=_
    exact iteratedDeriv_fun_mul hf hg
  rw [hmul]
  have hterm:∀ i∈Finset.range (m+1),
      |(m.choose i:ℝ)*iteratedDeriv i (fun v:ℝ=>phi (1/ 2 - v)) u *
          iteratedDeriv (m - i) (fun v:ℝ=>phi (1/ 2+v)) u| ≤
        (9 : ℝ)^m*(m.factorial:ℝ)^2:=by
    intro i hi
    have him:i≤ m:=Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [iteratedDeriv_comp_const_sub,iteratedDeriv_comp_const_add]
    simp only [smul_eq_mul,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,Nat.abs_cast]
    have h1:=yZ i (1/ 2 - u)
    have h2:=yZ (m - i) (1/ 2+u)
    have hchoose:(m.choose i:ℝ)*(i.factorial:ℝ)*((m - i).factorial:ℝ) =
        (m.factorial:ℝ):=by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial him
    have hprod_fac:(i.factorial:ℝ)*((m - i).factorial:ℝ)≤ (m.factorial:ℝ):=by
      have hpos:(1 : ℝ)≤ (m.choose i:ℝ):=by
        exact_mod_cast Nat.choose_pos him
      nlinarith [Nat.factorial_pos i,Nat.factorial_pos (m - i)]
    calc
      (m.choose i:ℝ)*|iteratedDeriv i phi (1/ 2 - u)| *
          |iteratedDeriv (m - i) phi (1/ 2+u)|
          ≤ (m.choose i:ℝ)*((9 : ℝ)^i*(i.factorial:ℝ)^2) *
              ((9 : ℝ)^(m - i)*((m - i).factorial:ℝ)^2):=by
            gcongr
      _=(9 : ℝ)^(i+(m - i)) *
            ((m.choose i:ℝ)*(i.factorial:ℝ)*((m - i).factorial:ℝ)) *
            ((i.factorial:ℝ)*((m - i).factorial:ℝ)):=by
            rw [pow_add]; ring
      _=(9 : ℝ)^m*(m.factorial:ℝ) *
            ((i.factorial:ℝ)*((m - i).factorial:ℝ)):=by
            rw [Nat.add_sub_cancel' him,hchoose]
      _≤ (9 : ℝ)^m*(m.factorial:ℝ)*(m.factorial:ℝ):=by
            gcongr
      _=(9 : ℝ)^m*(m.factorial:ℝ)^2:=by ring
  calc
    |∑ i∈Finset.range (m+1),
        (m.choose i:ℝ)*iteratedDeriv i (fun v:ℝ=>phi (1/ 2 - v)) u *
          iteratedDeriv (m - i) (fun v:ℝ=>phi (1/ 2+v)) u|
        ≤ ∑ i∈Finset.range (m+1),
            |(m.choose i:ℝ)*iteratedDeriv i (fun v:ℝ=>phi (1/ 2 - v)) u *
              iteratedDeriv (m - i) (fun v:ℝ=>phi (1/ 2+v)) u| :=
          Finset.abs_sum_le_sum_abs _ _
    _≤ ∑ _i∈Finset.range (m+1),(9 : ℝ)^m*(m.factorial:ℝ)^2 :=
          Finset.sum_le_sum hterm
    _=((m+1 : ℕ):ℝ)*(9 : ℝ)^m*(m.factorial:ℝ)^2:=by
          simp [mul_assoc]
    _≤ (2*(2 : ℝ)^m)*(9 : ℝ)^m*(m.factorial:ℝ)^2:=by
          have hm2:(m+1 : ℕ)≤ 2*2^m:=by
            have h1:m< 2^m:=Nat.lt_two_pow_self
            have h2:1≤ 2^m:=Nat.one_le_pow m 2 (by norm_num)
            omega
          have hm2R:((m+1 : ℕ):ℝ)≤ 2*(2 : ℝ)^m:=by exact_mod_cast hm2
          gcongr
    _=2*(18 : ℝ)^m*(m.factorial:ℝ)^2:=by
          rw [show (18 : ℝ)=2*9 by norm_num,mul_pow]; ring
def yj:ℝ:=∫ v:ℝ,zq v^2
lemma yt:Integrable (fun v:ℝ=>zq v^2):=by
  refine (zt.pow 2).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a:=-(1/ 2 : ℝ)) (b:=1/ 2)) ?_
  intro u hu
  rw [Function.mem_support] at hu
  by_contra hnot
  apply hu
  have h0:zq u=0:=by
    apply zm
    rw [Set.mem_Icc,not_and_or,not_le,not_le] at hnot
    rcases hnot with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  simp [h0]
lemma yu:0< yj:=by
  unfold yj
  have hcont:Continuous (fun v:ℝ=>zq v^2):=zt.pow 2
  have hnonneg:∀ v:ℝ,0≤ zq v^2:=fun v=>sq_nonneg _
  have hpos0:0< zq 0^2:=sq_pos_of_pos (wr (by norm_num))
  exact MeasureTheory.integral_pos_of_integrable_nonneg_nonzero (x:=0) hcont yt
    hnonneg hpos0.ne'
def eta (u:ℝ):ℝ:=(∫ v:ℝ,zq v*zq (u - v))/ yj
lemma yX (u:ℝ):Integrable (fun v:ℝ=>zq v*zq (u - v)):=by
  refine (zt.mul (zt.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport ?_
  exact zS.mul_right
lemma wL (u:ℝ):0≤ eta u :=
  div_nonneg (integral_nonneg fun _=>mul_nonneg (yO _) (yO _)) yu.le
lemma wT:eta 0=1:=by
  unfold eta
  have h:(∫ v:ℝ,zq v*zq (0 - v))=yj:=by
    unfold yj
    congr 1; ext v
    rw [zero_sub,wn,sq]
  rw [h,div_self yu.ne']
lemma v2 (u:ℝ):eta (-u)=eta u:=by
  unfold eta
  congr 1
  rw [← integral_neg_eq_self (fun v:ℝ=>zq v*zq (-u - v))]
  congr 1; ext v
  rw [wn v,show -u - -v=-(u - v) by ring,wn]
lemma wY (u:ℝ):eta u≤ 1:=by
  unfold eta
  rw [div_le_one yu]
  have h_le:∀ v:ℝ,zq v*zq (u - v)≤ (zq v^2+zq (u - v)^2)/ 2:=by
    intro v
    nlinarith [sq_nonneg (zq v - zq (u - v))]
  have h_int2:Integrable (fun v:ℝ=>zq (u - v)^2):=by
    have:=yt.comp_sub_left u
    simpa using this
  have h_eq2:∫ v:ℝ,zq (u - v)^2=yj:=by
    unfold yj
    exact MeasureTheory.integral_sub_left_eq_self (fun v:ℝ=>zq v^2) volume u
  calc
    ∫ v:ℝ,zq v*zq (u - v)
        ≤ ∫ v:ℝ,(zq v^2+zq (u - v)^2)/ 2 :=
          integral_mono (yX u) ((yt.add h_int2).div_const 2) h_le
    _=((∫ v:ℝ,zq v^2)+∫ v:ℝ,zq (u - v)^2)/ 2:=by
          rw [integral_div,integral_add yt h_int2]
    _=yj:=by
          rw [h_eq2]; unfold yj; ring
lemma xf {u:ℝ} (hu:1≤ |u|):eta u=0:=by
  unfold eta
  have hzero:∀ v:ℝ,zq v*zq (u - v)=0:=by
    intro v
    by_cases hv:1/ 2≤ |v|
    · rw [zm hv,zero_mul]
    · push Not at hv
      have huv:1/ 2≤ |u - v|:=by
        have htri:|u|≤ |u - v|+|v|:=by
          simpa [sub_add_cancel] using abs_add_le (u - v) v
        linarith
      rw [zm huv,mul_zero]
  simp [hzero]
lemma wm:Continuous eta:=by
  unfold eta
  refine Continuous.div_const ?_ _
  refine continuous_of_dominated (bound:=fun v:ℝ=>zq v) ?_ ?_ ?_ ?_
  · intro u
    exact (yX u).1
  · intro u
    refine ae_of_all _ fun v=>?_
    rw [Real.norm_of_nonneg (mul_nonneg (yO _) (yO _))]
    nlinarith [yO v,wD (u - v)]
  · exact zt.integrable_of_hasCompactSupport zS
  · refine ae_of_all _ fun v=>?_
    exact continuous_const.mul (zt.comp (continuous_id.sub continuous_const))
lemma wf:HasCompactSupport eta:=by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=(-1 : ℝ)) (b:=1)) ?_
  intro u hu
  rw [Function.mem_support] at hu
  by_contra hnot
  apply hu
  apply xf
  rw [Set.mem_Icc,not_and_or,not_le,not_le] at hnot
  rcases hnot with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith
lemma wM:Integrable eta :=
  wm.integrable_of_hasCompactSupport wf
def yc (t:ℝ):ℝ:=∫ v:ℝ,zq v*Real.cos (t*v)
def zh (t:ℝ):ℝ:=(yc t)^2/ (2*Real.pi*yj)
lemma zw (t:ℝ):0≤ zh t :=
  div_nonneg (sq_nonneg _) (by positivity [Real.pi_pos,yu])
lemma wQ (t:ℝ):yc (-t)=yc t:=by
  unfold yc
  congr 1; ext v
  rw [neg_mul,Real.cos_neg]
lemma wU (t:ℝ):zh (-t)=zh t:=by
  unfold zh
  rw [wQ]
private lemma yi {μ : Measure ℝ} {f:ℝ→ℝ} :
    (∫ v:ℝ,(f v:ℂ) ∂μ)=((∫ v:ℝ,f v ∂μ : ℝ):ℂ) :=
  Complex.ofRealLI.integral_comp_comm f
lemma x1 (t:ℝ) :
    𝓕 (fun v:ℝ=>(zq v:ℂ)) (t/ (2*Real.pi))=(yc t:ℂ):=by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hpi:(2*Real.pi:ℝ)≠0:=by positivity
  have h_rew:∀ v:ℝ,
      Complex.exp (↑(-2*Real.pi*v*(t/ (2*Real.pi)))*Complex.I) • (zq v:ℂ) =
        ((zq v*Real.cos (t*v):ℝ):ℂ) - ((zq v*Real.sin (t*v):ℝ):ℂ)*Complex.I:=by
    intro v
    have harg:-2*Real.pi*v*(t/ (2*Real.pi))=-(t*v):=by field_simp
    rw [harg,smul_eq_mul,Complex.exp_mul_I]
    rw [← Complex.ofReal_cos,← Complex.ofReal_sin,Real.cos_neg,Real.sin_neg]
    push_cast
    ring
  simp_rw [h_rew]
  have h_cos_int:Integrable (fun v:ℝ=>((zq v*Real.cos (t*v):ℝ):ℂ)):=by
    refine ((zt.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport ?_).ofReal
    exact zS.mul_right
  have h_sin_int:Integrable (fun v:ℝ=>((zq v*Real.sin (t*v):ℝ):ℂ)*Complex.I):=by
    refine (((zt.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport ?_).ofReal).mul_const _
    exact zS.mul_right
  rw [integral_sub h_cos_int h_sin_int,integral_mul_const]
  have h_sin_zero:∫ v:ℝ,((zq v*Real.sin (t*v):ℝ):ℂ)=0:=by
    rw [yi]
    have hodd:∫ v:ℝ,zq v*Real.sin (t*v)=0:=by
      have hneg:∫ v:ℝ,zq (-v)*Real.sin (t*-v)=∫ v:ℝ,zq v*Real.sin (t*v) :=
        MeasureTheory.integral_neg_eq_self (fun v:ℝ=>zq v*Real.sin (t*v)) volume
      have hsimp:(fun v:ℝ=>zq (-v)*Real.sin (t*-v)) =
          fun v:ℝ=>-(zq v*Real.sin (t*v)):=by
        ext v; rw [wn,mul_neg,Real.sin_neg,mul_neg]
      rw [hsimp,integral_neg] at hneg
      linarith
    simp [hodd]
  rw [h_sin_zero,zero_mul,sub_zero,yi]
  rfl
lemma wl (t:ℝ) :
    𝓕 (fun u:ℝ=>(eta u:ℂ)) (t/ (2*Real.pi))=((2*Real.pi*zh t:ℝ):ℂ):=by
  have hpi:(2*Real.pi:ℝ)≠0:=by positivity
  rw [Real.fourier_real_eq_integral_exp_smul]
  have h_arg:∀ u:ℝ,
      Complex.exp (↑(-2*Real.pi*u*(t/ (2*Real.pi)))*Complex.I) • (eta u:ℂ) =
        Complex.exp (↑(-(t*u))*Complex.I)*(eta u:ℂ):=by
    intro u
    have h1:-2*Real.pi*u*(t/ (2*Real.pi))=-(t*u):=by field_simp
    rw [h1,smul_eq_mul]
  simp_rw [h_arg]
  let F2:ℝ→ℝ→ℂ:=fun u v =>
    Complex.exp (↑(-(t*u))*Complex.I)*((zq v*zq (u - v):ℝ):ℂ)
  have h_eta_def:∀ u:ℝ,
      Complex.exp (↑(-(t*u))*Complex.I)*(eta u:ℂ) =
        ((yj:ℂ)⁻¹)*∫ v:ℝ,F2 u v:=by
    intro u
    unfold eta
    rw [Complex.ofReal_div,div_eq_inv_mul,← mul_assoc,mul_comm _ ((yj:ℂ)⁻¹),mul_assoc]
    congr 1
    rw [← yi,← integral_const_mul]
  simp_rw [h_eta_def]
  rw [integral_const_mul]
  have h_prod_int:Integrable (Function.uncurry F2) (volume.prod volume):=by
    have hcont_F2:Continuous (Function.uncurry F2):=by
      have h1:Continuous (fun p:ℝ × ℝ=>Complex.exp (↑(-(t*p.1))*Complex.I)) :=
        Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp ((continuous_const.mul continuous_fst).neg)).mul continuous_const)
      have h2:Continuous (fun p:ℝ × ℝ=>((zq p.2*zq (p.1 - p.2):ℝ):ℂ)) :=
        Complex.continuous_ofReal.comp
          ((zt.comp continuous_snd).mul
            (zt.comp (continuous_fst.sub continuous_snd)))
      exact h1.mul h2
    refine hcont_F2.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact
      ((isCompact_Icc (a:=(-1 : ℝ)) (b:=1)).prod (isCompact_Icc (a:=-(1/ 2 : ℝ)) (b:=1/ 2))) ?_
    intro p hp
    rw [Function.mem_support] at hp
    have h_ne0:zq p.2*zq (p.1 - p.2)≠0:=by
      intro h0
      apply hp
      simp only [Function.uncurry,F2]
      rw [h0,Complex.ofReal_zero,mul_zero]
    have hp2:|p.2|< 1/ 2:=by
      by_contra hge; push Not at hge
      exact h_ne0 (by rw [zm hge,zero_mul])
    have hp12:|p.1 - p.2|< 1/ 2:=by
      by_contra hge; push Not at hge
      exact h_ne0 (by rw [zm hge,mul_zero])
    have hp1:|p.1|≤ 1:=by
      have htri:|p.1|≤ |p.1 - p.2|+|p.2|:=by
        simpa [sub_add_cancel] using abs_add_le (p.1 - p.2) p.2
      linarith
    exact ⟨abs_le.mp hp1,abs_le.mp hp2.le⟩
  rw [integral_integral_swap h_prod_int]
  have h_inner:∀ v:ℝ,
      (∫ u:ℝ,F2 u v) =
        Complex.exp (↑(-(t*v))*Complex.I)*(zq v:ℂ)*(yc t:ℂ):=by
    intro v
    simp only [F2]
    rw [← integral_add_right_eq_self (fun u:ℝ =>
        Complex.exp (↑(-(t*u))*Complex.I)*((zq v*zq (u - v):ℝ):ℂ)) v]
    have h_rew:∀ u:ℝ,
        Complex.exp (↑(-(t*(u+v)))*Complex.I)*((zq v*zq (u+v - v):ℝ):ℂ) =
          (Complex.exp (↑(-(t*v))*Complex.I)*(zq v:ℂ)) *
            (Complex.exp (↑(-(t*u))*Complex.I)*(zq u:ℂ)):=by
      intro u
      rw [add_sub_cancel_right,Complex.ofReal_mul]
      have hexp:Complex.exp (↑(-(t*(u+v)))*Complex.I) =
          Complex.exp (↑(-(t*v))*Complex.I)*Complex.exp (↑(-(t*u))*Complex.I):=by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [hexp]; ring
    simp_rw [h_rew,integral_const_mul]
    congr 1
    have h4:=x1 t
    rw [Real.fourier_real_eq_integral_exp_smul] at h4
    rw [← h4]
    congr 1; ext u
    have h1:-2*Real.pi*u*(t/ (2*Real.pi))=-(t*u):=by field_simp
    rw [h1,smul_eq_mul]
  simp_rw [h_inner,integral_mul_const]
  have h5:=x1 t
  rw [Real.fourier_real_eq_integral_exp_smul] at h5
  have h_outer:(∫ v:ℝ,Complex.exp (↑(-(t*v))*Complex.I)*(zq v:ℂ))=(yc t:ℂ):=by
    rw [← h5]
    congr 1; ext v
    have h1:-2*Real.pi*v*(t/ (2*Real.pi))=-(t*v):=by field_simp
    rw [h1,smul_eq_mul]
  rw [h_outer]
  unfold zh
  push_cast
  have hpiC:(2*(Real.pi:ℂ))≠0:=by exact_mod_cast hpi
  have hnormC:(yj:ℂ)≠0:=by exact_mod_cast yu.ne'
  field_simp
lemma ws:Continuous yc:=by
  have h:Continuous (fun t:ℝ=>(yc t:ℂ)):=by
    have hint:Integrable (fun v:ℝ=>(zq v:ℂ)) volume :=
      (zt.integrable_of_hasCompactSupport zS).ofReal
    have h1:Continuous (𝓕 (fun v:ℝ=>(zq v:ℂ))) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hint
    have h2:Continuous (fun t:ℝ=>𝓕 (fun v:ℝ=>(zq v:ℂ)) (t/ (2*Real.pi))) :=
      h1.comp (continuous_id.div_const _)
    simpa only [x1] using h2
  exact Complex.continuous_re.comp h
lemma zs:Continuous zh :=
  (ws.pow 2).div_const _
lemma xC (t:ℝ) :
    |yc t|≤ 8*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|):=by
  have h_pow:∀ m:ℕ,|t|^m*|yc t|≤ 2*(18 : ℝ)^m*(m.factorial:ℝ)^2:=by
    intro m
    have h_f:ContDiff ℝ (⊤ : ℕ∞) (fun v:ℝ=>(zq v:ℂ)) :=
      Complex.ofRealCLM.contDiff.comp yB
    have h_int:∀ k:ℕ,(k:ℕ∞)≤ ⊤→Integrable (iteratedDeriv k (fun v:ℝ=>(zq v:ℂ))):=by
      intro k _
      rw [yL yB k]
      refine ((yB.continuous_iteratedDeriv k (by exact_mod_cast le_top)).integrable_of_hasCompactSupport ?_).ofReal
      refine HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc (a:=-(1/ 2 : ℝ)) (b:=1/ 2)) ?_
      intro u hu
      rw [Function.mem_support] at hu
      by_contra hnot
      apply hu
      apply ya k
      rw [Set.mem_Icc,not_and_or,not_le,not_le] at hnot
      rcases hnot with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    have h_fd:=congrFun (Real.fourier_iteratedDeriv h_f h_int (n:=m) (by exact_mod_cast le_top)) (t/ (2*Real.pi))
    have h_norm_lhs:‖(2*Real.pi*Complex.I*(t/ (2*Real.pi):ℝ))^m •
        𝓕 (fun v:ℝ=>(zq v:ℂ)) (t/ (2*Real.pi))‖=|t|^m*|yc t|:=by
      rw [x1,smul_eq_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
      congr 1
      have harg:(2*(Real.pi:ℂ)*Complex.I*((t/ (2*Real.pi):ℝ):ℂ)) =
          (t:ℂ)*Complex.I:=by
        have hpi:(2*(Real.pi:ℂ))≠0:=by
          have : (2*Real.pi:ℝ)≠0:=by positivity
          exact_mod_cast this
        push_cast
        field_simp
      rw [harg,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
    rw [← h_norm_lhs,← h_fd]
    have h_bound:=VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
      (innerSL ℝ).toLinearMap₁₂ (iteratedDeriv m (fun v:ℝ=>(zq v:ℂ))) (t/ (2*Real.pi))
    refine h_bound.trans ?_
    have h_eq:∀ v:ℝ,‖iteratedDeriv m (fun u:ℝ=>(zq u:ℂ)) v‖ =
        |iteratedDeriv m zq v|:=by
      intro v
      rw [congrFun (yL yB m) v,Complex.norm_real,Real.norm_eq_abs]
    simp_rw [h_eq]
    have h_supp:∫ v:ℝ,|iteratedDeriv m zq v| =
        ∫ v in Set.Icc (-(1/ 2 : ℝ)) (1/ 2),|iteratedDeriv m zq v|:=by
      symm
      refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv=>?_
      have hgt:1/ 2< |v|:=by
        rw [Set.mem_Icc,not_and_or,not_le,not_le] at hv
        rcases hv with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_nonneg (by linarith)]; linarith
      rw [ya m hgt,abs_zero]
    rw [h_supp]
    have h_le:∫ v in Set.Icc (-(1/ 2 : ℝ)) (1/ 2),|iteratedDeriv m zq v| ≤
        ∫ _v in Set.Icc (-(1/ 2 : ℝ)) (1/ 2),(2*(18 : ℝ)^m*(m.factorial:ℝ)^2):=by
      refine setIntegral_mono_on ?_ (integrableOn_const (by simp)) measurableSet_Icc ?_
      · exact ((yB.continuous_iteratedDeriv m (by exact_mod_cast le_top)).abs).integrableOn_Icc
      · intro v _; exact xJ m v
    refine h_le.trans ?_
    rw [setIntegral_const,smul_eq_mul,Real.volume_real_Icc_of_le (by norm_num)]
    norm_num
  have h_le1:|yc t|≤ 1:=by
    unfold yc
    have h_abs_int:Integrable (fun v:ℝ=>|zq v*Real.cos (t*v)|):=by
      refine ((zt.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))).abs).integrable_of_hasCompactSupport ?_
      refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=-(1/ 2 : ℝ)) (b:=1/ 2)) ?_
      intro v hv
      rw [Function.mem_support] at hv
      by_contra hnot
      apply hv
      have h0:zq v=0:=by
        apply zm
        rw [Set.mem_Icc,not_and_or,not_le,not_le] at hnot
        rcases hnot with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_nonneg (by linarith)]; linarith
      simp [h0]
    calc
      |∫ v:ℝ,zq v*Real.cos (t*v)|
          ≤ ∫ v:ℝ,|zq v*Real.cos (t*v)|:=abs_integral_le_integral_abs
      _≤ ∫ v:ℝ,zq v:=by
          refine integral_mono h_abs_int
            (zt.integrable_of_hasCompactSupport zS) fun v=>?_
          rw [abs_mul,abs_of_nonneg (yO v)]
          nlinarith [yO v,Real.abs_cos_le_one (t*v)]
      _≤ 1:=by
          have h_supp:∫ v:ℝ,zq v=∫ v in Set.Icc (-(1/ 2 : ℝ)) (1/ 2),zq v:=by
            symm
            refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv=>?_
            apply zm
            rw [Set.mem_Icc,not_and_or,not_le,not_le] at hv
            rcases hv with h | h
            · rw [abs_of_neg (by linarith)]; linarith
            · rw [abs_of_nonneg (by linarith)]; linarith
          rw [h_supp]
          calc
            ∫ v in Set.Icc (-(1/ 2 : ℝ)) (1/ 2),zq v
                ≤ ∫ _v in Set.Icc (-(1/ 2 : ℝ)) (1/ 2),(1 : ℝ) :=
                  setIntegral_mono_on zt.integrableOn_Icc (integrableOn_const (by simp))
                    measurableSet_Icc (fun v _=>wD v)
            _=1:=by
                  rw [setIntegral_const,smul_eq_mul,Real.volume_real_Icc_of_le (by norm_num)]
                  norm_num
  by_cases ht:|t|< 72
  · have hsq:Real.sqrt |t|≤ 9:=by
      have h1:|t|≤ 9^2:=by linarith
      calc Real.sqrt |t|≤ Real.sqrt (9^2):=Real.sqrt_le_sqrt h1
        _=9:=by rw [Real.sqrt_sq (by norm_num)]
    have hexp:Real.exp (-(9/ 10 : ℝ))≤ Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|) :=
      Real.exp_le_exp.mpr (by linarith)
    have hnum:(1 : ℝ)≤ 8*Real.exp (-(9/ 10 : ℝ)):=by
      rw [Real.exp_neg,← div_eq_mul_inv]
      have he:Real.exp (9/ 10 : ℝ)≤ Real.exp 1:=Real.exp_le_exp.mpr (by norm_num)
      have he3:Real.exp 1< 3:=Real.exp_one_lt_d9.trans (by norm_num)
      have hpos:0< Real.exp (9/ 10 : ℝ):=Real.exp_pos _
      rw [one_le_div hpos]
      linarith
    nlinarith [h_le1,hexp,hnum]
  · push Not at ht
    have ht_pos:0< |t|:=by linarith
    let m:ℕ:=⌊Real.sqrt (|t|/ 72)⌋₊
    have hm_le:(m:ℝ)≤ Real.sqrt (|t|/ 72):=Nat.floor_le (Real.sqrt_nonneg _)
    have hm_gt:Real.sqrt (|t|/ 72) - 1< (m:ℝ):=by
      linarith [Nat.lt_floor_add_one (Real.sqrt (|t|/ 72))]
    have hm_sq:(m:ℝ)^2≤ |t|/ 72:=by
      calc (m:ℝ)^2≤ (Real.sqrt (|t|/ 72))^2:=by gcongr
        _=|t|/ 72:=Real.sq_sqrt (by positivity)
    have hfac_le:(m.factorial:ℝ)≤ (m:ℝ)^m:=by
      exact_mod_cast Nat.factorial_le_pow m
    have h_step:=h_pow m
    have h_div:|yc t|≤ 2*(1/ 4 : ℝ)^m:=by
      rw [← mul_le_mul_iff_right₀ (pow_pos ht_pos m)]
      calc
        |t|^m*|yc t|≤ 2*(18 : ℝ)^m*(m.factorial:ℝ)^2:=h_step
        _≤ 2*(18 : ℝ)^m*((m:ℝ)^m)^2:=by gcongr
        _=2*(18*(m:ℝ)^2)^m:=by
            rw [← pow_mul,mul_comm m 2,pow_mul,mul_pow]; ring
        _≤ 2*(18*(|t|/ 72))^m:=by gcongr
        _=|t|^m*(2*(1/ 4 : ℝ)^m):=by
            have hsimp:18*(|t|/ 72)=(1/ 4 : ℝ)*|t|:=by ring
            rw [hsimp,mul_pow]; ring
    have h_log4:(1/ 10 : ℝ)*Real.sqrt 72≤ Real.log 4:=by
      have hsq72:Real.sqrt 72< 9:=by
        rw [Real.sqrt_lt' (by norm_num)]; norm_num
      have hlog4:(1 : ℝ)≤ Real.log 4:=by
        rw [Real.le_log_iff_exp_le (by norm_num)]
        exact Real.exp_one_lt_d9.le.trans (by norm_num)
      linarith
    have h_rpow:(1/ 4 : ℝ)^m≤ 4*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|):=by
      rw [show (1/ 4 : ℝ)^m=Real.exp (-(Real.log 4*(m:ℝ))) by
        rw [Real.exp_neg,Real.exp_mul,Real.exp_log (by norm_num),Real.rpow_natCast,
          one_div,inv_pow]]
      rw [show (4 : ℝ)*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|) =
          Real.exp (Real.log 4+-(1/ 10 : ℝ)*Real.sqrt |t|) by
        rw [Real.exp_add,Real.exp_log (by norm_num)]]
      apply Real.exp_le_exp.mpr
      have hsqrt_div:Real.sqrt (|t|/ 72)=Real.sqrt |t|/ Real.sqrt 72 :=
        Real.sqrt_div (abs_nonneg t) 72
      have hlog4_pos:0< Real.log 4:=Real.log_pos (by norm_num)
      have hsq72_pos:0< Real.sqrt 72:=Real.sqrt_pos.mpr (by norm_num)
      have h1:Real.log 4*(Real.sqrt |t|/ Real.sqrt 72 - 1)≤ Real.log 4*(m:ℝ):=by
        rw [← hsqrt_div]
        exact mul_le_mul_of_nonneg_left hm_gt.le hlog4_pos.le
      have h2:(1/ 10 : ℝ)*Real.sqrt |t|≤ Real.log 4*(Real.sqrt |t|/ Real.sqrt 72):=by
        rw [mul_div_assoc',le_div_iff₀ hsq72_pos]
        have : (1/ 10 : ℝ)*Real.sqrt |t| * Real.sqrt 72 =
            ((1/ 10 : ℝ)*Real.sqrt 72)*Real.sqrt |t|:=by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right h_log4 (Real.sqrt_nonneg _)
      linarith
    linarith
def za:ℝ:=64/ (2*Real.pi*yj)
lemma zT:0< za:=by
  unfold za
  positivity [Real.pi_pos,yu]
lemma zj (t:ℝ) :
    zh t≤ za*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|):=by
  unfold zh za
  have h:=xC t
  have hsq:(yc t)^2≤ 64*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|):=by
    calc
      (yc t)^2=|yc t|^2:=(sq_abs _).symm
      _≤ (8*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|))^2:=by gcongr
      _=64*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|):=by
          rw [mul_pow,← Real.exp_nat_mul]; norm_num; ring_nf
  have hden:0< 2*Real.pi*yj:=by positivity [Real.pi_pos,yu]
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hsq hden.le
lemma zd {c:ℝ} (hc:0< c) (k:ℕ) :
    Integrable (fun t:ℝ=>(1+|t|)^k*Real.exp (-c*Real.sqrt |t|)):=by
  let n:ℕ:=2*k+4
  let M:ℝ:=max (2^k) (2^k*(n.factorial:ℝ)/ c^n)
  have h_dom:Integrable (fun t:ℝ=>(2*M)*(1+t^2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul (2*M)
  refine h_dom.mono' ?_ ?_
  · exact Continuous.aestronglyMeasurable (by fun_prop)
  · refine ae_of_all _ fun t=>?_
    rw [Real.norm_of_nonneg (by positivity)]
    by_cases ht:|t|≤ 1
    · have h1:(1+|t|)^k≤ 2^k:=by gcongr; linarith
      have h2:Real.exp (-c*Real.sqrt |t|)≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [Real.sqrt_nonneg |t|])
      have h3:t^2≤ 1:=by
        rw [← sq_abs t]; nlinarith [abs_nonneg t]
      have h4:(1/ 2 : ℝ)≤ (1+t^2)⁻¹:=by
        rw [one_div,inv_le_inv₀ (by positivity) (by positivity)]
        linarith
      have hM:(2 : ℝ)^k≤ M:=le_max_left _ _
      have hM0:0≤ M:=le_trans (by positivity) hM
      calc
        (1+|t|)^k*Real.exp (-c*Real.sqrt |t|)≤ 2^k*1:=by gcongr
        _=2^k:=mul_one _
        _≤ M:=hM
        _=(2*M)*(1/ 2):=by ring
        _≤ (2*M)*(1+t^2)⁻¹:=by gcongr
    · push Not at ht
      have h1:(1+|t|)^k≤ (2*|t|)^k:=by gcongr; linarith
      have hu:0< c*Real.sqrt |t|:=mul_pos hc (Real.sqrt_pos.mpr (by linarith))
      have hpow:(c*Real.sqrt |t|)^n/ (n.factorial:ℝ)≤ Real.exp (c*Real.sqrt |t|) :=
        Real.pow_div_factorial_le_exp _ hu.le n
      have hexp:Real.exp (-c*Real.sqrt |t|)≤ (n.factorial:ℝ)/ (c*Real.sqrt |t|)^n:=by
        rw [neg_mul,Real.exp_neg,le_div_iff₀ (pow_pos hu n),inv_mul_eq_div,
          div_le_iff₀ (Real.exp_pos _)]
        have:=(div_le_iff₀ (by positivity:(0 : ℝ)< n.factorial)).mp hpow
        linarith
      have hsqrt_pow:(Real.sqrt |t|)^n=|t|^(k+2):=by
        change (Real.sqrt |t|)^(2*(k+2))=|t|^(k+2)
        rw [pow_mul,Real.sq_sqrt (abs_nonneg t)]
      have h_tsq:1+t^2≤ 2*|t|^2:=by
        rw [sq_abs]; nlinarith [sq_abs t]
      have hM:2^k*(n.factorial:ℝ)/ c^n≤ M:=le_max_right _ _
      have hM0:0≤ M:=le_trans (by positivity) (le_max_left _ _)
      calc
        (1+|t|)^k*Real.exp (-c*Real.sqrt |t|)
            ≤ (2*|t|)^k*((n.factorial:ℝ)/ (c*Real.sqrt |t|)^n):=by gcongr
        _=(2^k*(n.factorial:ℝ)/ c^n)*(|t|^k/ |t|^(k+2)):=by
            rw [mul_pow,mul_pow,hsqrt_pow]; ring
        _=(2^k*(n.factorial:ℝ)/ c^n)*(|t|^2)⁻¹:=by
            have ht0:|t|≠0:=by linarith
            congr 1
            rw [pow_add]
            field_simp
        _≤ M*(|t|^2)⁻¹:=by gcongr
        _=(2*M)*(2*|t|^2)⁻¹:=by
            rw [mul_inv]; ring
        _≤ (2*M)*(1+t^2)⁻¹:=by gcongr
lemma yG:Integrable zh:=by
  refine ((zd (by norm_num:(0 : ℝ)< 1/ 5) 0).const_mul za).mono'
    zs.aestronglyMeasurable ?_
  refine ae_of_all _ fun t=>?_
  rw [Real.norm_of_nonneg (zw t),pow_zero,one_mul]
  exact zj t
lemma w4:Integrable (𝓕 (fun u:ℝ=>(eta u:ℂ))):=by
  have h1:Integrable (fun t:ℝ=>((2*Real.pi*zh t:ℝ):ℂ)) :=
    (yG.const_mul (2*Real.pi)).ofReal
  have hpi:(2*Real.pi:ℝ)≠0:=by positivity
  have h2:=h1.comp_mul_left' hpi
  refine h2.congr (ae_of_all _ fun ξ=>?_)
  have h:=wl (2*Real.pi*ξ)
  have hsimp:2*Real.pi*ξ/ (2*Real.pi)=ξ:=by field_simp
  rw [hsimp] at h
  exact h.symm
lemma xe (u:ℝ) :
    (eta u:ℂ)=∫ t:ℝ,(zh t:ℂ)*Complex.exp (-(Complex.I*t*u)):=by
  have h_inv:=(Complex.continuous_ofReal.comp wm).fourierInv_fourier_eq
    wM.ofReal w4
  have h_val:=congrFun h_inv (-u)
  simp only [Function.comp_apply,v2] at h_val
  rw [← h_val,Real.fourierInv_eq']
  have hpi:(0 : ℝ)< 2*Real.pi:=by positivity
  symm
  have hmul:=MeasureTheory.Measure.integral_comp_mul_left
    (fun t:ℝ=>(zh t:ℂ)*Complex.exp (-(Complex.I*t*u))) (2*Real.pi)
  rw [abs_inv,abs_of_pos hpi,eq_inv_smul_iff₀ hpi.ne'] at hmul
  rw [← hmul,Complex.real_smul,← integral_const_mul]
  congr 1; ext ξ
  have h_eq:=wl (2*Real.pi*ξ)
  have hsimp:2*Real.pi*ξ/ (2*Real.pi)=ξ:=by field_simp [hpi.ne']
  rw [hsimp] at h_eq
  change _=_ • 𝓕 (fun v:ℝ=>(eta v:ℂ)) ξ
  rw [h_eq,smul_eq_mul,real_inner_eq_re_inner]
  simp only [RCLike.inner_apply,conj_trivial,RCLike.re_to_real]
  push_cast
  have hexp:Complex.exp ((2*(Real.pi:ℂ)*(-↑u*↑ξ))*Complex.I) =
      Complex.exp (-(Complex.I*(2*↑Real.pi*↑ξ)*↑u)):=by
    congr 1; ring
  rw [hexp]; ring
lemma wG:∫ t:ℝ,zh t=1:=by
  have h:=xe 0
  rw [wT] at h
  simp only [Complex.ofReal_one,Complex.ofReal_zero,mul_zero,neg_zero,Complex.exp_zero,
    mul_one] at h
  rw [yi] at h
  exact_mod_cast h.symm
def zN (u:ℝ):ℝ:=Real.exp (-u)*eta u
lemma wN:zN 0=1:=by
  simp [zN,wT]
lemma y3 {u:ℝ} (hu:1≤ u):zN u=0:=by
  unfold zN
  rw [xf (by rw [abs_of_nonneg (by linarith)]; exact hu),mul_zero]
lemma xy {u:ℝ} (hu:0≤ u):|zN u|≤ 1:=by
  unfold zN
  rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (wL u))]
  have h1:Real.exp (-u)≤ 1:=Real.exp_le_one_iff.mpr (by linarith)
  nlinarith [Real.exp_pos (-u),wL u,wY u]
lemma xX (u:ℝ) :
    (zN u:ℂ) =
      ∫ t:ℝ,(zh t:ℂ)*Complex.exp (-((1+Complex.I*(t:ℂ))*(u:ℂ))):=by
  unfold zN
  rw [Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_neg,xe u,
    ← integral_const_mul]
  congr 1; ext t
  rw [← mul_assoc,mul_comm (Complex.exp (-(u:ℂ))) (zh t:ℂ),mul_assoc,← Complex.exp_add]
  congr 2
  ring
private def yN (u:ℝ):ℂ :=
  ∫ t:ℝ,(zh t:ℂ)*(1+Complex.I*(t:ℂ)) *
    Complex.exp (-((1+Complex.I*(t:ℂ))*(u:ℂ)))
private lemma yM (u:ℝ) (t:ℝ) :
    ‖(zh t:ℂ)*(1+Complex.I*(t:ℂ)) *
      Complex.exp (-((1+Complex.I*(t:ℂ))*(u:ℂ)))‖ ≤
      za*((1+|t|)*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|))*Real.exp (-u):=by
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (zw t),
    Complex.norm_exp]
  have hre:(-((1+Complex.I*(t:ℂ))*(u:ℂ))).re=-u:=by simp
  rw [hre]
  have h1:‖(1 : ℂ)+Complex.I*(t:ℂ)‖≤ 1+|t|:=by
    calc ‖(1 : ℂ)+Complex.I*(t:ℂ)‖≤ ‖(1 : ℂ)‖+‖Complex.I*(t:ℂ)‖:=norm_add_le _ _
      _=1+|t|:=by simp [Complex.norm_real]
  have h2:=zj t
  have hC0:0≤ za:=zT.le
  calc
    zh t*‖(1 : ℂ)+Complex.I*(t:ℂ)‖*Real.exp (-u)
        ≤ (za*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|))*(1+|t|)*Real.exp (-u):=by
          gcongr
    _=za*((1+|t|)*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|))*Real.exp (-u):=by
          ring
private lemma wI (u:ℝ):(yN u).im=0:=by
  have hconj:starRingEnd ℂ (yN u)=yN u:=by
    unfold yN
    rw [← integral_conj]
    rw [← integral_neg_eq_self (fun t:ℝ =>
        starRingEnd ℂ ((zh t:ℂ)*(1+Complex.I*(t:ℂ)) *
          Complex.exp (-((1+Complex.I*(t:ℂ))*(u:ℂ)))))]
    congr 1; ext t
    rw [map_mul,map_mul,Complex.conj_ofReal,wU,map_add,map_one,map_mul,
      Complex.conj_I,Complex.conj_ofReal,← Complex.exp_conj]
    simp only [map_neg,map_mul,map_add,map_one,Complex.conj_I,Complex.conj_ofReal,
      Complex.ofReal_neg]
    ring_nf
  exact Complex.conj_eq_iff_im.mp hconj
private lemma xz (u:ℝ) (hu:-1< u) :
    HasDerivAt (fun s:ℝ=>(zN s:ℂ)) (-yN u) u:=by
  have h_eq:(fun s:ℝ=>(zN s:ℂ)) =
      fun s:ℝ=>∫ t:ℝ,(zh t:ℂ)*Complex.exp ((-(1+Complex.I*(t:ℂ)))*(s:ℂ)):=by
    ext s; rw [xX]; congr 1; ext t; congr 2; ring
  rw [h_eq]
  have h_neg:-yN u=∫ t:ℝ,(zh t:ℂ)*(-(1+Complex.I*(t:ℂ)) *
      Complex.exp ((-(1+Complex.I*(t:ℂ)))*(u:ℂ))):=by
    unfold yN
    rw [← integral_neg]
    congr 1; ext t; ring_nf
  rw [h_neg]
  let F:ℝ→ℝ→ℂ:=fun s t =>
    (zh t:ℂ)*Complex.exp ((-(1+Complex.I*(t:ℂ)))*(s:ℂ))
  let F':ℝ→ℝ→ℂ:=fun s t =>
    (zh t:ℂ)*(-(1+Complex.I*(t:ℂ)) *
      Complex.exp ((-(1+Complex.I*(t:ℂ)))*(s:ℂ)))
  let bound:ℝ→ℝ:=fun t =>
    za*Real.exp 1*((1+|t|)^1*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|))
  have h_ball:Metric.ball u (u+1)∈𝓝 u:=Metric.ball_mem_nhds u (by linarith)
  have hC0:0≤ za:=zT.le
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=F) (F':=F') (bound:=bound)
    h_ball ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.Eventually.of_forall fun s=>Continuous.aestronglyMeasurable
      ((Complex.continuous_ofReal.comp zs).mul (by fun_prop))
  · refine ((zd (by norm_num:(0 : ℝ)< 1/ 5) 0).const_mul
        (za*Real.exp (-u))).mono'
      (Continuous.aestronglyMeasurable ((Complex.continuous_ofReal.comp zs).mul (by fun_prop))) ?_
    refine ae_of_all _ fun t=>?_
    simp only [F,norm_mul,Complex.norm_real,Real.norm_of_nonneg (zw t),
      Complex.norm_exp,pow_zero,one_mul]
    have hre:((-(1+Complex.I*(t:ℂ)))*(u:ℂ)).re=-u:=by simp
    rw [hre]
    have h2:=zj t
    nlinarith [Real.exp_pos (-u)]
  · exact Continuous.aestronglyMeasurable
      ((Complex.continuous_ofReal.comp zs).mul ((by fun_prop:Continuous fun t:ℝ=>-(1+Complex.I*(t:ℂ))).mul (by fun_prop)))
  · refine ae_of_all _ fun t s hs=>?_
    have hs_gt:-1< s:=by
      rw [Metric.mem_ball,Real.dist_eq] at hs
      linarith [(abs_lt.mp hs).1]
    simp only [F',norm_mul,norm_neg,Complex.norm_real,Real.norm_of_nonneg (zw t),
      Complex.norm_exp,bound,pow_one]
    have hre:((-(1+Complex.I*(t:ℂ)))*(s:ℂ)).re=-s:=by simp
    rw [hre]
    have h1:‖(1 : ℂ)+Complex.I*(t:ℂ)‖≤ 1+|t|:=by
      calc ‖(1 : ℂ)+Complex.I*(t:ℂ)‖≤ ‖(1 : ℂ)‖+‖Complex.I*(t:ℂ)‖:=norm_add_le _ _
        _=1+|t|:=by simp [Complex.norm_real]
    have h2:=zj t
    have h3:Real.exp (-s)≤ Real.exp 1:=Real.exp_le_exp.mpr (by linarith)
    calc
      zh t*(‖(1 : ℂ)+Complex.I*(t:ℂ)‖*Real.exp (-s))
          ≤ (za*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|))*((1+|t|)*Real.exp 1):=by
            gcongr
      _=za*Real.exp 1*((1+|t|)*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|)):=by ring
  · exact (zd (by norm_num:(0 : ℝ)< 1/ 5) 1).const_mul _
  · refine ae_of_all _ fun t s _=>?_
    have h1:HasDerivAt (fun x:ℝ=>(x:ℂ)) 1 s:=Complex.ofRealCLM.hasDerivAt
    have hlin:HasDerivAt (fun x:ℝ=>(-(1+Complex.I*(t:ℂ)))*(x:ℂ))
        (-(1+Complex.I*(t:ℂ))) s:=by
      simpa using h1.const_mul (-(1+Complex.I*(t:ℂ)))
    have hexp:=hlin.cexp
    have hcm:=hexp.const_mul (zh t:ℂ)
    exact hcm.congr_deriv (by dsimp only [F']; ring)
private lemma xQ (u:ℝ) (hu:-1< u) :
    HasDerivAt zN (-(yN u).re) u:=by
  have hC:=xz u hu
  rw [hasDerivAt_iff_tendsto_slope] at hC ⊢
  have hre:=(Complex.continuous_re.tendsto (-yN u)).comp hC
  refine hre.congr fun s=>?_
  simp only [Function.comp_apply,slope_def_module,Complex.real_smul,
    ← Complex.ofReal_sub,← Complex.ofReal_mul,Complex.ofReal_re,smul_eq_mul]
def c0:ℝ:=∫ u in Set.Ioi (0 : ℝ),(yN u).re^2
lemma wz:1≤ c0:=by
  have hC0:0≤ za:=zT.le
  have hg_cont:ContinuousOn (fun u:ℝ=>(yN u).re) (Set.Ici 0):=by
    have hcont:ContinuousOn yN (Set.Ici 0):=by
      refine continuousOn_of_dominated
        (bound:=fun t:ℝ=>za*((1+|t|)^1*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|)))
        ?_ ?_ ?_ ?_
      · intro u _
        exact Continuous.aestronglyMeasurable
          (((Complex.continuous_ofReal.comp zs).mul (by fun_prop)).mul (by fun_prop))
      · intro u hu
        refine ae_of_all _ fun t=>?_
        have h1:=yM u t
        have h2:Real.exp (-u)≤ 1:=Real.exp_le_one_iff.mpr (by linarith [Set.mem_Ici.mp hu])
        rw [pow_one]
        calc
          _≤ za*((1+|t|)*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|))*Real.exp (-u):=h1
          _≤ za*((1+|t|)*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|))*1:=by
              gcongr
          _=_:=mul_one _
      · exact (zd (by norm_num:(0 : ℝ)< 1/ 5) 1).const_mul _
      · refine ae_of_all _ fun t=>?_
        exact (continuous_const.mul (by fun_prop:Continuous fun u:ℝ =>
          Complex.exp (-((1+Complex.I*(t:ℂ))*(u:ℂ))))).continuousOn
    exact Complex.continuous_re.comp_continuousOn hcont
  have h_ftc:∫ u in (0 : ℝ)..1,(yN u).re=1:=by
    have hderiv:∀ u∈Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s:ℝ=>(-1 : ℝ)*zN s) (yN u).re u:=by
      intro u hu
      rw [Set.uIcc_of_le (by norm_num)] at hu
      have hd:=(xQ u (by linarith [hu.1])).const_mul (-1 : ℝ)
      simpa using hd
    have hint:IntervalIntegrable (fun u:ℝ=>(yN u).re) volume 0 1 :=
      (hg_cont.mono (by rw [Set.uIcc_of_le (by norm_num)]; exact fun x hx=>hx.1)).intervalIntegrable
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    rw [y3 le_rfl,wN]
    ring
  have h_cs:(∫ u in (0 : ℝ)..1,(yN u).re)^2≤ ∫ u in (0 : ℝ)..1,(yN u).re^2:=by
    have hint1:IntervalIntegrable (fun u:ℝ=>(yN u).re) volume 0 1 :=
      (hg_cont.mono (by rw [Set.uIcc_of_le (by norm_num)]; exact fun x hx=>hx.1)).intervalIntegrable
    have hint2:IntervalIntegrable (fun u:ℝ=>(yN u).re^2) volume 0 1 :=
      ((hg_cont.pow 2).mono (by rw [Set.uIcc_of_le (by norm_num)]; exact fun x hx=>hx.1)).intervalIntegrable
    have h0:0≤ ∫ u in (0 : ℝ)..1,((yN u).re - (∫ v in (0 : ℝ)..1,(yN v).re))^2:=by
      apply intervalIntegral.integral_nonneg (by norm_num)
      intro u _; exact sq_nonneg _
    set m:=∫ v in (0 : ℝ)..1,(yN v).re
    have hexp:(fun u:ℝ=>((yN u).re - m)^2) =
        fun u:ℝ=>(yN u).re^2 - (2*m)*(yN u).re+m^2:=by
      ext u; ring
    rw [hexp,intervalIntegral.integral_add (hint2.sub (hint1.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_sub hint2 (hint1.const_mul _),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const] at h0
    simp only [sub_zero,one_smul] at h0
    nlinarith
  have h_int_Ioi:IntegrableOn (fun u:ℝ=>(yN u).re^2) (Set.Ioi 0):=by
    let B:ℝ:=za*∫ t:ℝ,(1+|t|)^1*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|)
    have h_dom:IntegrableOn (fun u:ℝ=>B^2*Real.exp (-2*u)) (Set.Ioi 0) :=
      (integrableOn_exp_mul_Ioi (a:=-2) (by norm_num) 0).const_mul (B^2)
    refine h_dom.mono' ((hg_cont.pow 2).mono Set.Ioi_subset_Ici_self |>.aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun u _=>?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h_g_le:|(yN u).re|≤ B*Real.exp (-u):=by
      calc |(yN u).re|≤ ‖yN u‖:=Complex.abs_re_le_norm _
        _≤ ∫ t:ℝ,‖(zh t:ℂ)*(1+Complex.I*(t:ℂ)) *
              Complex.exp (-((1+Complex.I*(t:ℂ))*(u:ℂ)))‖ :=
            norm_integral_le_integral_norm _
        _≤ ∫ t:ℝ,za*((1+|t|)^1*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|))*Real.exp (-u):=by
            refine integral_mono ?_ ?_ (fun t=>by simpa [pow_one] using yM u t)
            · refine (((zd (by norm_num:(0 : ℝ)< 1/ 5) 1).const_mul za).mul_const (Real.exp (-u))).mono' ?_ ?_
              · exact (Continuous.aestronglyMeasurable
                  (((Complex.continuous_ofReal.comp zs).mul (by fun_prop)).mul (by fun_prop))).norm
              · refine ae_of_all _ fun t=>?_
                rw [norm_norm]
                simpa [pow_one] using yM u t
            · exact ((zd (by norm_num:(0 : ℝ)< 1/ 5) 1).const_mul za).mul_const _
        _=B*Real.exp (-u):=by
            rw [integral_mul_const,integral_const_mul]
    calc
      (yN u).re^2=|(yN u).re|^2:=(sq_abs _).symm
      _≤ (B*Real.exp (-u))^2:=by gcongr
      _=B^2*Real.exp (-2*u):=by rw [mul_pow,← Real.exp_nat_mul]; ring_nf
  have h_le_c0:∫ u in (0 : ℝ)..1,(yN u).re^2≤ c0:=by
    unfold c0
    rw [intervalIntegral.integral_of_le (by norm_num:(0 : ℝ)≤ 1)]
    exact MeasureTheory.setIntegral_mono_set h_int_Ioi
      (ae_of_all _ fun _=>sq_nonneg _)
      (Eventually.of_forall fun _ hu=>hu.1)
  rw [h_ftc,one_pow] at h_cs
  linarith
lemma zX:0< c0:=by linarith [wz]
lemma wg :
    ∫ t:ℝ,∫ t':ℝ,
      ((1+Complex.I*(t:ℂ))*(1+Complex.I*(t':ℂ)) /
        (2+Complex.I*((t:ℂ)+(t':ℂ)))) *
      (zh t:ℂ)*(zh t':ℂ)=(c0:ℂ):=by
  have hC0:0≤ za:=zT.le
  have h_laplace:∀ t t':ℝ,
      ∫ u in Set.Ioi (0 : ℝ),
        Complex.exp (-((2+Complex.I*((t:ℂ)+(t':ℂ)))*(u:ℂ))) =
        (2+Complex.I*((t:ℂ)+(t':ℂ)))⁻¹:=by
    intro t t'
    set α : ℂ:=2+Complex.I*((t:ℂ)+(t':ℂ))
    have hα_re : 0< α.re:=by simp [α]
    have hα_ne : α≠0:=by intro h; rw [h] at hα_re; simp at hα_re
    have h:=integral_exp_mul_complex_Ioi (a:=-α) (by simp [hα_re]) (0 : ℝ)
    simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,neg_div] at h
    have hsimp:-((1 : ℂ)/ -α)=α⁻¹:=by field_simp [hα_ne]
    rw [← hsimp,← h]
    congr 1; ext u; congr 1; ring
  let H:(ℝ × ℝ)→ℝ→ℂ:=fun p u =>
    (zh p.1 : ℂ)*(1+Complex.I*(p.1 : ℂ)) *
    (zh p.2 : ℂ)*(1+Complex.I*(p.2 : ℂ)) *
    Complex.exp (-((2+Complex.I*((p.1 : ℂ)+(p.2 : ℂ)))*(u:ℂ)))
  have h_H_int:Integrable (Function.uncurry H) ((volume.prod volume).prod (volume.restrict (Set.Ioi (0 : ℝ)))):=by
    let φ1 : ℝ→ℝ:=fun t=>za*((1+|t|)^1*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|))
    have hφ1 : Integrable φ1 volume :=
      (zd (by norm_num:(0 : ℝ)< 1/ 5) 1).const_mul za
    have hdom:Integrable (fun q:(ℝ × ℝ) × ℝ=>(φ1 q.1.1*φ1 q.1.2)*Real.exp (-2*q.2))
        ((volume.prod volume).prod (volume.restrict (Set.Ioi (0 : ℝ)))) :=
      (hφ1.mul_prod hφ1).mul_prod (integrableOn_exp_mul_Ioi (a:=-2) (by norm_num) 0)
    refine hdom.mono' (Continuous.aestronglyMeasurable ?_) ?_
    · have hc1:Continuous (fun q:(ℝ × ℝ) × ℝ=>(zh q.1.1 : ℂ)) :=
        Complex.continuous_ofReal.comp (zs.comp (continuous_fst.comp continuous_fst))
      have hc2:Continuous (fun q:(ℝ × ℝ) × ℝ=>(zh q.1.2 : ℂ)) :=
        Complex.continuous_ofReal.comp (zs.comp (continuous_snd.comp continuous_fst))
      exact (((hc1.mul (by fun_prop)).mul hc2).mul (by fun_prop)).mul (by fun_prop)
    · refine ae_of_all _ fun q=>?_
      simp only [Function.uncurry,H,norm_mul,Complex.norm_real,
        Real.norm_of_nonneg (zw _),Complex.norm_exp,φ1,pow_one]
      have hre:(-((2+Complex.I*((q.1.1 : ℂ)+(q.1.2 : ℂ)))*(q.2 : ℂ))).re=-2*q.2:=by
        simp
      rw [hre]
      have hb1:‖(1 : ℂ)+Complex.I*(q.1.1 : ℂ)‖≤ 1+|q.1.1|:=by
        calc ‖(1 : ℂ)+Complex.I*(q.1.1 : ℂ)‖≤ ‖(1 : ℂ)‖+‖Complex.I*(q.1.1 : ℂ)‖:=norm_add_le _ _
          _=1+|q.1.1|:=by simp [Complex.norm_real]
      have hb2:‖(1 : ℂ)+Complex.I*(q.1.2 : ℂ)‖≤ 1+|q.1.2|:=by
        calc ‖(1 : ℂ)+Complex.I*(q.1.2 : ℂ)‖≤ ‖(1 : ℂ)‖+‖Complex.I*(q.1.2 : ℂ)‖:=norm_add_le _ _
          _=1+|q.1.2|:=by simp [Complex.norm_real]
      have he1:=zj q.1.1
      have he2:=zj q.1.2
      have hnn1:=zw q.1.1
      have hnn2:=zw q.1.2
      calc
        zh q.1.1*‖1+Complex.I*(q.1.1 : ℂ)‖*zh q.1.2 *
            ‖1+Complex.I*(q.1.2 : ℂ)‖*Real.exp (-2*q.2)
            ≤ (za*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |q.1.1|))*(1+|q.1.1|) *
              (za*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |q.1.2|))*(1+|q.1.2|) *
              Real.exp (-2*q.2):=by gcongr
        _=za*((1+|q.1.1|)*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |q.1.1|)) *
              (za*((1+|q.1.2|)*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |q.1.2|))) *
              Real.exp (-2*q.2):=by ring
  have h_swap:=MeasureTheory.integral_integral_swap h_H_int
  have h_lhs:(∫ p:ℝ × ℝ,(∫ u in Set.Ioi (0 : ℝ),H p u) ∂(volume.prod volume)) =
      ∫ t:ℝ,∫ t':ℝ,
        ((1+Complex.I*(t:ℂ))*(1+Complex.I*(t':ℂ)) /
          (2+Complex.I*((t:ℂ)+(t':ℂ)))) *
        (zh t:ℂ)*(zh t':ℂ):=by
    have h_inner_p:∀ p:ℝ × ℝ,
        (∫ u in Set.Ioi (0 : ℝ),H p u) =
          ((1+Complex.I*(p.1 : ℂ))*(1+Complex.I*(p.2 : ℂ)) /
            (2+Complex.I*((p.1 : ℂ)+(p.2 : ℂ)))) *
          (zh p.1 : ℂ)*(zh p.2 : ℂ):=by
      intro p
      simp only [H,integral_const_mul,h_laplace]
      ring
    simp_rw [h_inner_p]
    rw [MeasureTheory.integral_prod _ (h_H_int.integral_prod_left.congr (ae_of_all _ h_inner_p))]
  have h_rhs:(∫ u in Set.Ioi (0 : ℝ),∫ p:ℝ × ℝ,H p u ∂(volume.prod volume))=(c0:ℂ):=by
    have h_inner_u:∀ u:ℝ,(∫ p:ℝ × ℝ,H p u ∂(volume.prod volume))=yN u^2:=by
      intro u
      have h_fact:∀ p:ℝ × ℝ,H p u =
          ((zh p.1 : ℂ)*(1+Complex.I*(p.1 : ℂ)) *
            Complex.exp (-((1+Complex.I*(p.1 : ℂ))*(u:ℂ)))) *
          ((zh p.2 : ℂ)*(1+Complex.I*(p.2 : ℂ)) *
            Complex.exp (-((1+Complex.I*(p.2 : ℂ))*(u:ℂ)))):=by
        intro p
        simp only [H]
        have hexp:Complex.exp (-((2+Complex.I*((p.1 : ℂ)+(p.2 : ℂ)))*(u:ℂ))) =
            Complex.exp (-((1+Complex.I*(p.1 : ℂ))*(u:ℂ))) *
            Complex.exp (-((1+Complex.I*(p.2 : ℂ))*(u:ℂ))):=by
          rw [← Complex.exp_add]; congr 1; ring
        rw [hexp]; ring
      let fu:ℝ→ℂ:=fun t =>
        (zh t:ℂ)*(1+Complex.I*(t:ℂ)) *
          Complex.exp (-((1+Complex.I*(t:ℂ))*(u:ℂ)))
      have h_fact':∀ p:ℝ × ℝ,H p u=fu p.1*fu p.2:=h_fact
      simp_rw [h_fact']
      rw [MeasureTheory.integral_prod_mul (f:=fu) (g:=fu),sq]
      rfl
    simp_rw [h_inner_u]
    unfold c0
    rw [← yi]
    congr 1; ext u
    have hre:yN u=((yN u).re:ℂ):=Complex.ext rfl (by simp [wI u])
    conv_lhs=>rw [hre]
    push_cast; rfl
  rw [← h_lhs,h_swap,h_rhs]
end
end Erdos413Bump
namespace Erdos413Sieve
open Finset Filter Topology Complex Real MeasureTheory
open Erdos413Bump Erdos413Mertens
open scoped BigOperators
noncomputable section
def yD (N:ℕ):ℝ:=0.15*Real.log (N:ℝ)
def z7 (N:ℕ):ℕ:=⌊yD N⌋₊
def z4 (N:ℕ):ℕ:=primorial (z7 N)
def ze (N:ℕ):ℝ:=∏ p∈z5 (z7 N),(1 - (1 : ℝ)/ (p:ℝ))⁻¹
def z0 (N:ℕ):ℕ:=⌊(Real.log (N:ℝ))^((1 : ℝ)/ 1000)⌋₊
def yI (N:ℕ):ℕ:=⌊(N:ℝ)^((1 : ℝ)/ 100)⌋₊
def Rk (A:ℝ) (N k:ℕ):ℝ :=
  if 1≤ k∧k≤ z0 N then
    (N:ℝ)^(1/ (100*(A+1)*(k:ℝ)^50))
  else
    yD N
def z9 (A:ℝ) (N:ℕ) (k:Fin (z0 N)):ℝ:=Rk A N (k.1+1)
def Tk (A:ℝ) (N k:ℕ):ℝ:=(N:ℝ)^(1/ (10*A*Real.log (k:ℝ)))
def z3 (N:ℕ):ℝ:=(Real.log (N:ℝ))^((1 : ℝ)/ 5)
lemma w6 (N:ℕ):0< z4 N:=primorial_pos _
lemma wZ (N:ℕ):Squarefree (z4 N):=squarefree_primorial _
lemma zr (N:ℕ):1≤ ze N:=by
  unfold ze
  refine Finset.one_le_prod fun p hp=>?_
  have hp2:(2 : ℝ)≤ (p:ℝ):=by exact_mod_cast (mem_filter.mp hp).2.two_le
  have h1:0< 1 - (1 : ℝ)/ (p:ℝ):=by
    have : (1 : ℝ)/ (p:ℝ)≤ 1/ 2:=one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have h2:1 - (1 : ℝ)/ (p:ℝ)≤ 1:=by
    have : 0≤ (1 : ℝ)/ (p:ℝ):=by positivity
    linarith
  exact one_le_inv₀ h1 |>.mpr h2
lemma wu (A:ℝ) (N:ℕ) (k:Fin (z0 N)) :
    z9 A N k=(N:ℝ)^(1/ (100*(A+1)*((k.1+1 : ℕ):ℝ)^50)):=by
  unfold z9 Rk
  rw [if_pos ⟨by omega,k.2⟩]
lemma xV (A:ℝ) {N:ℕ} (hN:1≤ N) (k:Fin (z0 N)) :
    Real.log (z9 A N k)=Real.log (N:ℝ)/ (100*(A+1)*((k.1+1 : ℕ):ℝ)^50):=by
  rw [wu,Real.log_rpow (by positivity),one_div_mul_eq_div]
lemma zk {m:ℕ} (_hm:m≠0) (N:ℕ) :
    Nat.Coprime m (z4 N)↔∀ p:ℕ,p.Prime→p∣m→z7 N< p:=by
  constructor
  · intro hcop p hp hpm
    by_contra hle
    push Not at hle
    have hpW:p∣z4 N:=hp.dvd_primorial_iff.mpr hle
    have hp1:p∣Nat.gcd m (z4 N):=Nat.dvd_gcd hpm hpW
    rw [hcop.gcd_eq_one] at hp1
    exact hp.ne_one (Nat.dvd_one.mp hp1)
  · intro h
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    let p:=(Nat.gcd m (z4 N)).minFac
    have hp:p.Prime:=Nat.minFac_prime hne
    have hpdvd:p∣Nat.gcd m (z4 N):=Nat.minFac_dvd _
    have hpm:p∣m:=hpdvd.trans (Nat.gcd_dvd_left _ _)
    have hpW:p∣z4 N:=hpdvd.trans (Nat.gcd_dvd_right _ _)
    have hle:p≤ z7 N:=hp.dvd_primorial_iff.mp hpW
    have hgt:z7 N< p:=h p hp hpm
    omega
def xD (A:ℝ) (N:ℕ) (k:Fin (z0 N)) (n:ℕ):ℝ :=
  ∑ d∈(n - (k.1+1)).divisors.filter (fun d=>Nat.Coprime d (z4 N)),
    ((ArithmeticFunction.moebius d:ℤ):ℝ) *
      zN (Real.log (d:ℝ)/ Real.log (z9 A N k))
def zl (A:ℝ) (N:ℕ) (n:ℕ):ℝ :=
  (if z4 N∣n then (1 : ℝ) else 0) *
    ∏ k:Fin (z0 N),(xD A N k n)^2
lemma yw (A:ℝ) (N n:ℕ):0≤ zl A N n:=by
  unfold zl
  refine mul_nonneg (by split_ifs <;> norm_num) ?_
  exact prod_nonneg fun k _=>sq_nonneg _
lemma xH {A:ℝ} {N n:ℕ} (h:0< zl A N n) :
    z4 N∣n:=by
  by_contra hndvd
  simp [zl,hndvd] at h
def xb (A:ℝ) (N v7 v6:ℕ):ℝ :=
  ∑ n∈Finset.Ioc N (2*N),
    zl A N n*(if v6∣n - v7 then (1 : ℝ) else 0)
def zY (A:ℝ) (N:ℕ):ℝ :=
  ∑ n∈Finset.Ioc N (2*N),zl A N n
lemma xZ (A:ℝ) (N v7:ℕ):xb A N v7 1=zY A N:=by
  simp [xb,zY]
lemma xK (A:ℝ) (N v7 v6:ℕ):0≤ xb A N v7 v6 :=
  sum_nonneg fun n _=>mul_nonneg (yw A N n) (by split_ifs <;> norm_num)
lemma wO (N L r₀ : ℕ) (hL:1≤ L) (hr₀ : r₀< L) :
    |(((Finset.Ioc N (2*N)).filter (fun n=>n % L=r₀)).card:ℝ) - (N:ℝ)/ (L:ℝ)|≤ 1:=by
  have hLpos:(0 : ℤ)< (L:ℤ):=by exact_mod_cast hL
  let q₁ : ℤ:=((N:ℤ) - (r₀ : ℤ))/ (L:ℤ)
  let q₂ : ℤ:=((2*N:ℤ) - (r₀ : ℤ))/ (L:ℤ)
  have hq₁_ge : -1≤ q₁:=by
    dsimp [q₁]
    rw [Int.le_ediv_iff_mul_le hLpos]
    have : (r₀ : ℤ)< (L:ℤ):=by exact_mod_cast hr₀
    omega
  have hcard:((Finset.Ioc N (2*N)).filter (fun n=>n % L=r₀)).card =
      (Finset.Ioc q₁ q₂).card:=by
    refine Finset.card_bij (fun n _=>((n/ L:ℕ):ℤ)) ?_ ?_ ?_
    · intro n hn
      rcases mem_filter.mp hn with ⟨hIoc,hmod⟩
      rcases mem_Ioc.mp hIoc with ⟨hgt,hle⟩
      have hdiv:n=(n/ L)*L+r₀:=by
        have:=Nat.div_add_mod n L
        rw [hmod] at this
        linarith
      have hdivZ:(n:ℤ)=((n/ L:ℕ):ℤ)*(L:ℤ)+(r₀ : ℤ):=by exact_mod_cast hdiv
      rw [mem_Ioc]
      constructor
      · dsimp [q₁]
        rw [Int.ediv_lt_iff_lt_mul hLpos]
        have hgtZ:(N:ℤ)< (n:ℤ):=by exact_mod_cast hgt
        linarith
      · dsimp [q₂]
        rw [Int.le_ediv_iff_mul_le hLpos]
        have hleZ:(n:ℤ)≤ 2*(N:ℤ):=by exact_mod_cast hle
        linarith
    · intro n₁ hn₁ n₂ hn₂ heq
      have hm1:n₁ % L=r₀:=(mem_filter.mp hn₁).2
      have hm2:n₂ % L=r₀:=(mem_filter.mp hn₂).2
      have hd:n₁/ L=n₂/ L:=by exact_mod_cast heq
      have h1:=Nat.div_add_mod n₁ L
      have h2:=Nat.div_add_mod n₂ L
      rw [hm1,hd] at h1
      rw [hm2] at h2
      omega
    · intro m hm
      rcases mem_Ioc.mp hm with ⟨hm1,hm2⟩
      have hm_nn:0≤ m:=by omega
      let n:ℕ:=m.toNat*L+r₀
      have hn_cast:(n:ℤ)=m*(L:ℤ)+(r₀ : ℤ):=by
        dsimp [n]
        have hm_eq:(m.toNat:ℤ)=m:=Int.toNat_of_nonneg hm_nn
        rw [hm_eq]
      have hgt:N< n:=by
        dsimp [q₁] at hm1
        rw [Int.ediv_lt_iff_lt_mul hLpos] at hm1
        omega
      have hle:n≤ 2*N:=by
        dsimp [q₂] at hm2
        rw [Int.le_ediv_iff_mul_le hLpos] at hm2
        omega
      have hmod:n % L=r₀:=by
        dsimp [n]
        rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hr₀]
      have hdiv:n/ L=m.toNat:=by
        dsimp [n]
        rw [mul_comm m.toNat L,Nat.mul_add_div (by omega:0< L),Nat.div_eq_of_lt hr₀,add_zero]
      refine ⟨n,mem_filter.mpr ⟨mem_Ioc.mpr ⟨hgt,hle⟩,hmod⟩,?_⟩
      rw [hdiv,Int.toNat_of_nonneg hm_nn]
  have hq_le:q₁≤ q₂:=by
    dsimp [q₁,q₂]
    exact Int.ediv_le_ediv hLpos (by omega)
  have hcard_int:(((Finset.Ioc N (2*N)).filter (fun n=>n % L=r₀)).card:ℤ)=q₂ - q₁:=by
    rw [hcard,Int.card_Ioc]
    exact Int.toNat_of_nonneg (by omega)
  have hrem1:((N:ℤ) - (r₀ : ℤ))=(L:ℤ)*q₁+((N:ℤ) - (r₀ : ℤ)) % (L:ℤ) :=
    (Int.mul_ediv_add_emod _ _).symm
  have hrem2:((2*N:ℤ) - (r₀ : ℤ))=(L:ℤ)*q₂+((2*N:ℤ) - (r₀ : ℤ)) % (L:ℤ) :=
    (Int.mul_ediv_add_emod _ _).symm
  have hr1_nn:0≤ ((N:ℤ) - (r₀ : ℤ)) % (L:ℤ):=Int.emod_nonneg _ hLpos.ne'
  have hr1_lt:((N:ℤ) - (r₀ : ℤ)) % (L:ℤ)< (L:ℤ):=Int.emod_lt_of_pos _ hLpos
  have hr2_nn:0≤ ((2*N:ℤ) - (r₀ : ℤ)) % (L:ℤ):=Int.emod_nonneg _ hLpos.ne'
  have hr2_lt:((2*N:ℤ) - (r₀ : ℤ)) % (L:ℤ)< (L:ℤ):=Int.emod_lt_of_pos _ hLpos
  have hdiff_int:(N:ℤ) - (q₂ - q₁)*(L:ℤ) =
      ((2*N:ℤ) - (r₀ : ℤ)) % (L:ℤ) - ((N:ℤ) - (r₀ : ℤ)) % (L:ℤ):=by
    linarith
  have hdiff_R:(((Finset.Ioc N (2*N)).filter (fun n=>n % L=r₀)).card:ℝ) - (N:ℝ)/ (L:ℝ) =
      ((((N:ℤ) - (r₀ : ℤ)) % (L:ℤ) - ((2*N:ℤ) - (r₀ : ℤ)) % (L:ℤ):ℤ):ℝ)/ (L:ℝ):=by
    have hcard_R:(((Finset.Ioc N (2*N)).filter (fun n=>n % L=r₀)).card:ℝ)=((q₂ - q₁ : ℤ):ℝ):=by
      exact_mod_cast hcard_int
    rw [hcard_R]
    have hLne:(L:ℝ)≠0:=by positivity
    rw [sub_eq_iff_eq_add,← add_div,eq_div_iff hLne]
    have hcast:((q₂ - q₁ : ℤ):ℝ)*(L:ℝ) =
        (N:ℝ)+((((N:ℤ) - (r₀ : ℤ)) % (L:ℤ) - ((2*N:ℤ) - (r₀ : ℤ)) % (L:ℤ):ℤ):ℝ):=by
      have : (q₂ - q₁)*(L:ℤ) =
          (N:ℤ)+(((N:ℤ) - (r₀ : ℤ)) % (L:ℤ) - ((2*N:ℤ) - (r₀ : ℤ)) % (L:ℤ)):=by
        linarith
      exact_mod_cast this
    linarith
  rw [hdiff_R,abs_div,abs_of_pos (by positivity:(0 : ℝ)< (L:ℝ)),div_le_one (by positivity)]
  have habs_int:|(((N:ℤ) - (r₀ : ℤ)) % (L:ℤ) - ((2*N:ℤ) - (r₀ : ℤ)) % (L:ℤ))|≤ (L:ℤ):=by
    rw [abs_le]; constructor <;> omega
  exact_mod_cast habs_int
lemma wi {a b:ℕ} (ha:Squarefree a) (hb:Squarefree b) :
    Squarefree (Nat.lcm a b):=by
  have ha0:a≠0:=ha.ne_zero
  have hb0:b≠0:=hb.ne_zero
  have hlcm0:Nat.lcm a b≠0:=Nat.lcm_ne_zero ha0 hb0
  rw [Nat.squarefree_iff_factorization_le_one hlcm0]
  intro p
  rw [Nat.factorization_lcm ha0 hb0,Finsupp.sup_apply]
  exact max_le ((Nat.squarefree_iff_factorization_le_one ha0).mp ha p)
    ((Nat.squarefree_iff_factorization_le_one hb0).mp hb p)
lemma yq {m d:ℕ} (hm:Squarefree m) :
    Nat.Coprime (m/ Nat.gcd m d) d:=by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  let p:=(Nat.gcd (m/ Nat.gcd m d) d).minFac
  have hp:p.Prime:=Nat.minFac_prime hne
  have hp1:p∣m/ Nat.gcd m d:=(Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)
  have hpd:p∣d:=(Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
  have hpm:p∣m:=hp1.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m d))
  have hpg:p∣Nat.gcd m d:=Nat.dvd_gcd hpm hpd
  have hpp:p*p∣m:=by
    have hmul:p*p∣(m/ Nat.gcd m d)*Nat.gcd m d:=mul_dvd_mul hp1 hpg
    rwa [Nat.div_mul_cancel (Nat.gcd_dvd_left m d)] at hmul
  exact hp.ne_one (Nat.isUnit_iff.mp (hm p hpp))
lemma x3 {m d:ℕ} (hm:Squarefree m) :
    Nat.Coprime (m/ Nat.gcd m d) (Nat.gcd m d) :=
  (yq hm).coprime_dvd_right (Nat.gcd_dvd_right m d)
lemma wX {ι : Type*} [DecidableEq ι] (s:Finset ι) (q a:ι→ℕ)
    (hqpos:∀ i∈s,0< q i)
    (hcop:Set.Pairwise (s:Set ι) fun i j=>Nat.Coprime (q i) (q j)) :
    ∃ r:ℕ,r< ∏ i∈s,q i ∧
      ∀ n:ℕ,(∀ i∈s,n ≡ a i [MOD q i])↔n % (∏ i∈s,q i)=r:=by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0,by norm_num,fun n=>?_⟩
    simp [Nat.mod_one]
  | insert i s hi ih =>
    have hqpos_s:∀ j∈s,0< q j:=fun j hj=>hqpos j (Finset.mem_insert_of_mem hj)
    have hcop_s:Set.Pairwise (s:Set ι) fun j k=>Nat.Coprime (q j) (q k) :=
      hcop.mono (by intro j hj; exact Finset.mem_insert_of_mem hj)
    obtain ⟨r_s,hrs_lt,hrs_iff⟩:=ih hqpos_s hcop_s
    have hcop_is:Nat.Coprime (q i) (∏ j∈s,q j):=by
      refine Nat.Coprime.prod_right fun j hj=>?_
      exact hcop (Finset.mem_insert_self i s) (Finset.mem_insert_of_mem hj)
        (fun h=>hi (h ▸ hj))
    let crt:=Nat.chineseRemainder hcop_is (a i) r_s
    have hprod_pos:0< q i*∏ j∈s,q j :=
      mul_pos (hqpos i (Finset.mem_insert_self i s)) (Finset.prod_pos hqpos_s)
    let r:=crt.val % (q i*∏ j∈s,q j)
    refine ⟨r,?_,fun n=>?_⟩
    · rw [Finset.prod_insert hi]; exact Nat.mod_lt _ hprod_pos
    · rw [Finset.prod_insert hi]
      have hcrt1:r ≡ a i [MOD q i] :=
        (Nat.ModEq.of_mul_right (∏ j∈s,q j) (Nat.mod_modEq crt.val _)).trans crt.prop.1
      have hcrt2:r ≡ r_s [MOD ∏ j∈s,q j] :=
        (Nat.ModEq.of_mul_left (q i) (Nat.mod_modEq crt.val _)).trans crt.prop.2
      constructor
      · intro hall
        have h1:n ≡ r [MOD q i] :=
          (hall i (Finset.mem_insert_self i s)).trans hcrt1.symm
        have h2:n ≡ r [MOD ∏ j∈s,q j]:=by
          have hns:n % (∏ j∈s,q j)=r_s :=
            (hrs_iff n).mp fun j hj=>hall j (Finset.mem_insert_of_mem hj)
          have hns_mod:n ≡ r_s [MOD ∏ j∈s,q j]:=by
            rw [Nat.ModEq,hns,Nat.mod_eq_of_lt hrs_lt]
          exact hns_mod.trans hcrt2.symm
        have hboth:n ≡ r [MOD q i*∏ j∈s,q j] :=
          (Nat.modEq_and_modEq_iff_modEq_mul hcop_is).mp ⟨h1,h2⟩
        rw [Nat.ModEq] at hboth
        rwa [Nat.mod_eq_of_lt (Nat.mod_lt _ hprod_pos)] at hboth
      · intro hmod j hj
        have hnr:n ≡ r [MOD q i*∏ j∈s,q j]:=by
          rw [Nat.ModEq,hmod,Nat.mod_eq_of_lt (Nat.mod_lt _ hprod_pos)]
        rcases mem_insert.mp hj with rfl | hjs
        · exact (Nat.ModEq.of_mul_right _ hnr).trans hcrt1
        · have hns:n ≡ r_s [MOD ∏ j∈s,q j]:=(Nat.ModEq.of_mul_left _ hnr).trans hcrt2
          have hns_eq:n % (∏ j∈s,q j)=r_s:=by
            rw [Nat.ModEq,Nat.mod_eq_of_lt hrs_lt] at hns; exact hns
          exact ((hrs_iff n).mpr hns_eq) j hjs
def xi (N v7 v6:ℕ) (dd:Fin (z0 N)→ℕ × ℕ):Prop :=
  (∀ k₁ k₂ : Fin (z0 N),k₁≠k₂ →
    Nat.Coprime (Nat.lcm (dd k₁).1 (dd k₁).2) (Nat.lcm (dd k₂).1 (dd k₂).2)) ∧
  (∀ k:Fin (z0 N),
    ((Nat.gcd (Nat.lcm (dd k).1 (dd k).2) v6:ℕ):ℤ)∣((v7:ℤ) - ((k.1+1 : ℕ):ℤ)))
lemma yH {n k m:ℕ} (hkn:k≤ n) :
    m∣n - k↔n ≡ k [MOD m]:=by
  constructor
  · intro h
    rcases h with ⟨t,ht⟩
    have hadd:n=k+m*t:=by omega
    rw [hadd,Nat.ModEq,Nat.add_mul_mod_self_left]
  · intro h
    have hZ:(m:ℤ)∣(n:ℤ) - (k:ℤ):=Nat.modEq_iff_dvd.mp h.symm
    have hcast:((n - k:ℕ):ℤ)=(n:ℤ) - (k:ℤ):=Int.ofNat_sub hkn
    rw [← hcast] at hZ
    exact Int.ofNat_dvd.mp hZ
private lemma xx {s:Finset ℕ} {z:ℤ}
    (hp:∀ q∈s,q.Prime) (hdvd:∀ q∈s,(q:ℤ)∣z) :
    ((∏ q∈s,q:ℕ):ℤ)∣z:=by
  classical
  induction s using Finset.induction_on with
  | empty=>simp
  | insert q s hqs ih =>
    rw [Finset.prod_insert hqs,Nat.cast_mul]
    have hq_pr:q.Prime:=hp q (Finset.mem_insert_self q s)
    have hcop_nat:Nat.Coprime q (∏ r∈s,r) :=
      Nat.Coprime.prod_right fun r hr =>
        (Nat.coprime_primes hq_pr (hp r (Finset.mem_insert_of_mem hr))).mpr (fun h=>hqs (h ▸ hr))
    have hcop_int:IsCoprime (q:ℤ) ((∏ r∈s,r:ℕ):ℤ) :=
      Nat.isCoprime_iff_coprime.mpr hcop_nat
    exact hcop_int.mul_dvd (hdvd q (Finset.mem_insert_self q s))
      (ih (fun r hr=>hp r (Finset.mem_insert_of_mem hr))
        (fun r hr=>hdvd r (Finset.mem_insert_of_mem hr)))
lemma wE {N v7 v6:ℕ}
    (hKw:z0 N< z7 N) (hKN:z0 N< N) (hkstarN:v7< N)
    (hdstar_sf:Squarefree v6) (hdstar_cop:Nat.Coprime v6 (z4 N))
    (dd:Fin (z0 N)→ℕ × ℕ)
    (hdd_sf:∀ k,Squarefree (dd k).1∧Squarefree (dd k).2)
    (hdd_cop:∀ k,Nat.Coprime (dd k).1 (z4 N)∧Nat.Coprime (dd k).2 (z4 N)) :
    let cond:ℕ→Prop:=fun n =>
      z4 N∣n∧v6∣n - v7∧∀ k:Fin (z0 N),Nat.lcm (dd k).1 (dd k).2∣n - (k.1+1)
    letI:Decidable (xi N v7 v6 dd):=Classical.propDecidable _
    if xi N v7 v6 dd then
      |(((Finset.Ioc N (2*N)).filter cond).card:ℝ) -
        ((N:ℝ)/ ((z4 N:ℝ)*(v6:ℝ))) *
          ∏ k:Fin (z0 N),
            ((Nat.gcd (Nat.lcm (dd k).1 (dd k).2) v6:ℝ) /
              (Nat.lcm (dd k).1 (dd k).2 : ℝ))|≤ 1
    else
      ((Finset.Ioc N (2*N)).filter cond).card=0:=by
  classical
  dsimp only
  let mk:Fin (z0 N)→ℕ:=fun k=>Nat.lcm (dd k).1 (dd k).2
  have hmk_sf:∀ k,Squarefree (mk k):=fun k=>wi (hdd_sf k).1 (hdd_sf k).2
  have hmk_pos:∀ k,0< mk k:=fun k=>Nat.pos_of_ne_zero (hmk_sf k).ne_zero
  have hmk_copW:∀ k,Nat.Coprime (mk k) (z4 N):=fun k=>by
    have hmul:Nat.Coprime ((dd k).1*(dd k).2) (z4 N):=(hdd_cop k).1.mul_left (hdd_cop k).2
    exact hmul.coprime_dvd_left (Nat.lcm_dvd_mul _ _)
  split_ifs with hcompat
  ·
    let qk:Fin (z0 N)→ℕ:=fun k=>mk k/ Nat.gcd (mk k) v6
    have hqk_pos:∀ k,0< qk k:=fun k =>
      Nat.div_pos (Nat.le_of_dvd (hmk_pos k) (Nat.gcd_dvd_left _ _))
        (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero (hmk_sf k).ne_zero (Nat.gcd_dvd_left _ _)))
    have hqk_cop_dstar:∀ k,Nat.Coprime (qk k) v6:=fun k =>
      yq (hmk_sf k)
    have hqk_cop_W:∀ k,Nat.Coprime (qk k) (z4 N):=fun k =>
      (hmk_copW k).coprime_dvd_left (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
    have hqk_pair:Set.Pairwise (Set.univ:Set (Fin (z0 N))) fun k₁ k₂ =>
        Nat.Coprime (qk k₁) (qk k₂):=by
      intro k₁ _ k₂ _ hne
      exact ((hcompat.1 k₁ k₂ hne).coprime_dvd_left (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))).coprime_dvd_right
        (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
    obtain ⟨r_q,hrq_lt,hrq_iff⟩:=wX Finset.univ qk (fun k=>k.1+1)
      (fun k _=>hqk_pos k) (by simpa using hqk_pair)
    let Q:ℕ:=∏ k:Fin (z0 N),qk k
    have hQ_pos:0< Q:=Finset.prod_pos fun k _=>hqk_pos k
    have hQ_cop_dstar:Nat.Coprime v6 Q :=
      Nat.Coprime.prod_right fun k _=>(hqk_cop_dstar k).symm
    have hWd_cop:Nat.Coprime (z4 N) (v6*Q) :=
      (hdstar_cop.symm).mul_right (Nat.Coprime.prod_right fun k _=>(hqk_cop_W k).symm)
    let crt1:=Nat.chineseRemainder hQ_cop_dstar v7 r_q
    let r1:=crt1.val % (v6*Q)
    have hdQ_pos:0< v6*Q:=mul_pos (Nat.pos_of_ne_zero hdstar_sf.ne_zero) hQ_pos
    let crt2:=Nat.chineseRemainder hWd_cop 0 r1
    let L:ℕ:=z4 N*(v6*Q)
    have hL_pos:0< L:=mul_pos (w6 N) hdQ_pos
    let r₀ : ℕ:=crt2.val % L
    have hr₀_lt : r₀< L:=Nat.mod_lt _ hL_pos
    have hfilter_eq:(Finset.Ioc N (2*N)).filter
        (fun n=>z4 N∣n∧v6∣n - v7∧∀ k:Fin (z0 N),mk k∣n - (k.1+1)) =
        (Finset.Ioc N (2*N)).filter (fun n=>n % L=r₀):=by
      ext n
      simp only [mem_filter,mem_Ioc]
      refine and_congr_right fun ⟨hn_gt,_⟩=>?_
      have hkstar_le:v7≤ n:=by omega
      have hk_le:∀ k:Fin (z0 N),k.1+1≤ n:=fun k=>by have:=k.2; omega
      have hcrt2_W:r₀ ≡ 0 [MOD z4 N] :=
        (Nat.ModEq.of_mul_right (v6*Q) (Nat.mod_modEq crt2.val L)).trans crt2.prop.1
      have hcrt2_dQ:r₀ ≡ r1 [MOD v6*Q] :=
        (Nat.ModEq.of_mul_left (z4 N) (Nat.mod_modEq crt2.val L)).trans crt2.prop.2
      have hcrt1_d:r1 ≡ v7 [MOD v6] :=
        (Nat.ModEq.of_mul_right Q (Nat.mod_modEq crt1.val (v6*Q))).trans crt1.prop.1
      have hcrt1_Q:r1 ≡ r_q [MOD Q] :=
        (Nat.ModEq.of_mul_left v6 (Nat.mod_modEq crt1.val (v6*Q))).trans crt1.prop.2
      constructor
      · rintro ⟨hW,hd,hmk_all⟩
        have hnW:n ≡ r₀ [MOD z4 N]:=by
          have : n ≡ 0 [MOD z4 N]:=Nat.modEq_zero_iff_dvd.mpr hW
          exact this.trans hcrt2_W.symm
        have hnd:n ≡ r1 [MOD v6] :=
          ((yH hkstar_le).mp hd).trans hcrt1_d.symm
        have hnQ:n ≡ r1 [MOD Q]:=by
          have hq_all:∀ k∈(Finset.univ:Finset (Fin (z0 N))),n ≡ k.1+1 [MOD qk k]:=by
            intro k _
            exact (yH (hk_le k)).mp
              ((Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (mk k) v6)).trans (hmk_all k))
          have hmodQ:n % Q=r_q:=(hrq_iff n).mp hq_all
          have hn_rq:n ≡ r_q [MOD Q]:=by
            rw [Nat.ModEq,hmodQ,Nat.mod_eq_of_lt hrq_lt]
          exact hn_rq.trans hcrt1_Q.symm
        have hndQ:n ≡ r₀ [MOD v6*Q] :=
          ((Nat.modEq_and_modEq_iff_modEq_mul hQ_cop_dstar).mp ⟨hnd,hnQ⟩).trans hcrt2_dQ.symm
        have hnL:n ≡ r₀ [MOD L] :=
          (Nat.modEq_and_modEq_iff_modEq_mul hWd_cop).mp ⟨hnW,hndQ⟩
        rw [Nat.ModEq,Nat.mod_eq_of_lt hr₀_lt] at hnL
        exact hnL
      · intro hmod
        have hnL:n ≡ r₀ [MOD L]:=by
          rw [Nat.ModEq,hmod,Nat.mod_eq_of_lt hr₀_lt]
        have hnW:n ≡ 0 [MOD z4 N]:=(Nat.ModEq.of_mul_right _ hnL).trans hcrt2_W
        have hndQ:n ≡ r1 [MOD v6*Q]:=(Nat.ModEq.of_mul_left _ hnL).trans hcrt2_dQ
        have hnd:n ≡ v7 [MOD v6]:=(Nat.ModEq.of_mul_right _ hndQ).trans hcrt1_d
        have hnQ:n ≡ r_q [MOD Q]:=(Nat.ModEq.of_mul_left _ hndQ).trans hcrt1_Q
        have hq_all:∀ k:Fin (z0 N),n ≡ k.1+1 [MOD qk k]:=by
          have hmodQ:n % Q=r_q:=by rw [Nat.ModEq,Nat.mod_eq_of_lt hrq_lt] at hnQ; exact hnQ
          intro k; exact (hrq_iff n).mpr hmodQ k (Finset.mem_univ k)
        refine ⟨Nat.modEq_zero_iff_dvd.mp hnW,(yH hkstar_le).mpr hnd,fun k=>?_⟩
        rw [yH (hk_le k)]
        have hmul_eq:qk k*Nat.gcd (mk k) v6=mk k :=
          Nat.div_mul_cancel (Nat.gcd_dvd_left (mk k) v6)
        rw [← hmul_eq]
        refine (Nat.modEq_and_modEq_iff_modEq_mul (x3 (hmk_sf k))).mp
          ⟨hq_all k,?_⟩
        have hng:n ≡ v7 [MOD Nat.gcd (mk k) v6] :=
          Nat.ModEq.of_dvd (Nat.gcd_dvd_right (mk k) v6) hnd
        have hkg:v7 ≡ k.1+1 [MOD Nat.gcd (mk k) v6]:=by
          rw [Nat.modEq_iff_dvd]
          have hdvd:=hcompat.2 k
          have hneg:=dvd_neg.mpr hdvd
          rwa [neg_sub] at hneg
        exact hng.trans hkg
    rw [hfilter_eq]
    have hL_eq:((N:ℝ)/ (L:ℝ)) =
        ((N:ℝ)/ ((z4 N:ℝ)*(v6:ℝ))) *
          ∏ k:Fin (z0 N),((Nat.gcd (mk k) v6:ℝ)/ (mk k:ℝ)):=by
      have hQ_cast:(Q:ℝ)=∏ k:Fin (z0 N),((mk k:ℝ)/ (Nat.gcd (mk k) v6:ℝ)):=by
        dsimp [Q]
        rw [Nat.cast_prod]
        refine Finset.prod_congr rfl fun k _=>?_
        exact Nat.cast_div (Nat.gcd_dvd_left _ _) (by
          have:=ne_zero_of_dvd_ne_zero (hmk_sf k).ne_zero (Nat.gcd_dvd_left (mk k) v6)
          exact_mod_cast this)
      have hL_cast:(L:ℝ)=((z4 N:ℝ)*(v6:ℝ))*(Q:ℝ):=by
        dsimp [L]; push_cast; ring
      rw [hL_cast,hQ_cast,div_mul_eq_div_div,div_eq_mul_inv,← Finset.prod_inv_distrib]
      congr 1
      refine Finset.prod_congr rfl fun k _=>by rw [inv_div]
    rw [← hL_eq]
    exact wO N L r₀ hL_pos hr₀_lt
  ·
    rw [Finset.card_eq_zero,filter_eq_empty_iff]
    intro n hn ⟨hW,hd,hmk_all⟩
    rcases mem_Ioc.mp hn with ⟨hn_gt,_⟩
    apply hcompat
    constructor
    · intro k₁ k₂ hne
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hgc
      let p:=(Nat.gcd (mk k₁) (mk k₂)).minFac
      have hp:p.Prime:=Nat.minFac_prime hgc
      have hp1:p∣mk k₁:=(Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)
      have hp2:p∣mk k₂:=(Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
      have hp_gt:z7 N< p:=(zk (hmk_sf k₁).ne_zero N).mp (hmk_copW k₁) p hp hp1
      have hd1:p∣n - (k₁.1+1):=hp1.trans (hmk_all k₁)
      have hd2:p∣n - (k₂.1+1):=hp2.trans (hmk_all k₂)
      have h1Z:(p:ℤ)∣(n:ℤ) - ((k₁.1+1 : ℕ):ℤ):=by
        rw [← Int.ofNat_sub (by have:=k₁.2; omega)]; exact Int.ofNat_dvd.mpr hd1
      have h2Z:(p:ℤ)∣(n:ℤ) - ((k₂.1+1 : ℕ):ℤ):=by
        rw [← Int.ofNat_sub (by have:=k₂.2; omega)]; exact Int.ofNat_dvd.mpr hd2
      have hdiffZ:(p:ℤ)∣((k₂.1+1 : ℕ):ℤ) - ((k₁.1+1 : ℕ):ℤ):=by
        have hsub:=dvd_sub h1Z h2Z
        have heq:((n:ℤ) - ((k₁.1+1 : ℕ):ℤ)) - ((n:ℤ) - ((k₂.1+1 : ℕ):ℤ)) =
            ((k₂.1+1 : ℕ):ℤ) - ((k₁.1+1 : ℕ):ℤ):=by ring
        rwa [heq] at hsub
      have hne_val:(k₁.1 : ℕ)≠k₂.1:=fun h=>hne (Fin.ext h)
      have hk1lt:=k₁.2; have hk2lt:=k₂.2
      rcases lt_or_gt_of_ne hne_val with hlt | hgt
      · have hpos:(0 : ℤ)< ((k₂.1+1 : ℕ):ℤ) - ((k₁.1+1 : ℕ):ℤ):=by omega
        have hle_p:=Int.le_of_dvd hpos hdiffZ
        omega
      · have hdiffZ':(p:ℤ)∣((k₁.1+1 : ℕ):ℤ) - ((k₂.1+1 : ℕ):ℤ):=by
          have hneg:=dvd_neg.mpr hdiffZ
          rwa [neg_sub] at hneg
        have hpos:(0 : ℤ)< ((k₁.1+1 : ℕ):ℤ) - ((k₂.1+1 : ℕ):ℤ):=by omega
        have hle_p:=Int.le_of_dvd hpos hdiffZ'
        omega
    · intro k
      set g:=Nat.gcd (mk k) v6
      have hg_sf:Squarefree g:=hdstar_sf.squarefree_of_dvd (Nat.gcd_dvd_right _ _)
      have hg_prod:∏ p∈g.primeFactors,p=g:=Nat.prod_primeFactors_of_squarefree hg_sf
      rw [← hg_prod]
      refine xx (fun p hp=>Nat.prime_of_mem_primeFactors hp) fun p hp=>?_
      have hpg:p∣g:=Nat.dvd_of_mem_primeFactors hp
      have hpmk:p∣mk k:=hpg.trans (Nat.gcd_dvd_left _ _)
      have hpd:p∣v6:=hpg.trans (Nat.gcd_dvd_right _ _)
      have h1Z:(p:ℤ)∣(n:ℤ) - ((k.1+1 : ℕ):ℤ):=by
        rw [← Int.ofNat_sub (by have:=k.2; omega)]
        exact Int.ofNat_dvd.mpr (hpmk.trans (hmk_all k))
      have h2Z:(p:ℤ)∣(n:ℤ) - (v7:ℤ):=by
        rw [← Int.ofNat_sub (by omega)]
        exact Int.ofNat_dvd.mpr (hpd.trans hd)
      have hdiff:=dvd_sub h1Z h2Z
      have heq:((n:ℤ) - ((k.1+1 : ℕ):ℤ)) - ((n:ℤ) - (v7:ℤ)) =
          (v7:ℤ) - ((k.1+1 : ℕ):ℤ):=by ring
      rwa [heq] at hdiff
def rho:Measure ℝ:=volume.withDensity (fun t=>ENNReal.ofReal (zh t))
def zn:Measure (ℝ × ℝ):=rho.prod rho
def PK (K:ℕ):Measure (Fin K→ℝ × ℝ):=Measure.pi (fun _:Fin K=>zn)
instance isProbabilityMeasure_rho:IsProbabilityMeasure rho:=by
  constructor
  unfold rho
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal yG
    (ae_of_all _ zw)]
  rw [wG,ENNReal.ofReal_one]
instance isProbabilityMeasure_rho2:IsProbabilityMeasure zn:=by
  unfold zn; infer_instance
instance isProbabilityMeasure_PK (K:ℕ):IsProbabilityMeasure (PK K):=by
  unfold PK; infer_instance
lemma xw {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f:ℝ→E) :
    ∫ t:ℝ,f t ∂rho=∫ t:ℝ,zh t • f t:=by
  unfold rho
  have hmeas:Measurable (fun t:ℝ=>ENNReal.ofReal (zh t)) :=
    ENNReal.measurable_ofReal.comp zs.measurable
  have hlt:∀ᵐ t ∂volume,ENNReal.ofReal (zh t)< ⊤ :=
    ae_of_all _ fun _=>ENNReal.ofReal_lt_top
  rw [integral_withDensity_eq_integral_toReal_smul hmeas hlt]
  congr 1; ext t
  rw [ENNReal.toReal_ofReal (zw t)]
lemma xp (f:ℝ→ℂ) :
    ∫ t:ℝ,f t ∂rho=∫ t:ℝ,(zh t:ℂ)*f t:=by
  rw [xw]
  simp_rw [Complex.real_smul]
lemma yz {d:ℕ} (hd:1≤ d) {R:ℝ} (_hR:1< R) :
    (zN (Real.log (d:ℝ)/ Real.log R):ℂ) =
      ∫ t:ℝ,(d:ℂ)^(-((1+Complex.I*(t:ℂ))/ (Real.log R:ℂ))) ∂rho:=by
  rw [xX,xp]
  congr 1; ext t
  congr 1
  have hd_pos:(0 : ℝ)< d:=by positivity
  have hdC:(d:ℂ)≠0:=by exact_mod_cast (show d≠0 by omega)
  rw [Complex.cpow_def_of_ne_zero hdC,← Complex.ofReal_natCast,← Complex.ofReal_log hd_pos.le]
  congr 1
  push_cast
  ring
def zA:ℝ:=za*∫ t:ℝ,(1+|t|)^0*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|)
lemma yC:0≤ zA:=by
  unfold zA
  exact mul_nonneg zT.le (integral_nonneg fun _=>by positivity)
lemma wS {T:ℝ} (_hT:0≤ T) :
    (rho {t:ℝ | T< |t|}).toReal≤ zA*Real.exp (-(1/ 10 : ℝ)*Real.sqrt T):=by
  have hmeas:MeasurableSet {t:ℝ | T< |t|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hfin:rho {t:ℝ | T< |t|}≠⊤:=measure_ne_top rho _
  have h1:(rho {t:ℝ | T< |t|}).toReal=∫ t in {t:ℝ | T< |t|},zh t:=by
    unfold rho
    rw [MeasureTheory.withDensity_apply _ hmeas]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal yG.integrableOn
      (ae_of_all _ zw)]
    exact ENNReal.toReal_ofReal (integral_nonneg fun _=>zw _)
  rw [h1]
  have hdom:Integrable (fun t:ℝ =>
      (za*Real.exp (-(1/ 10 : ℝ)*Real.sqrt T)) *
        ((1+|t|)^0*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|))) :=
    (zd (by norm_num:(0 : ℝ)< 1/ 10) 0).const_mul _
  calc
    ∫ t in {t:ℝ | T< |t|},zh t
        ≤ ∫ t in {t:ℝ | T< |t|},
            (za*Real.exp (-(1/ 10 : ℝ)*Real.sqrt T)) *
              ((1+|t|)^0*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|)):=by
          refine setIntegral_mono_on yG.integrableOn hdom.integrableOn hmeas fun t ht=>?_
          have hsqrt:Real.sqrt T≤ Real.sqrt |t|:=Real.sqrt_le_sqrt ht.le
          have hexp:Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|) ≤
              Real.exp (-(1/ 10 : ℝ)*Real.sqrt T)*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|):=by
            rw [← Real.exp_add]
            exact Real.exp_le_exp.mpr (by linarith)
          rw [pow_zero,one_mul]
          calc
            zh t≤ za*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|):=zj t
            _≤ za*(Real.exp (-(1/ 10 : ℝ)*Real.sqrt T) *
                  Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|)) :=
                mul_le_mul_of_nonneg_left hexp zT.le
            _=(za*Real.exp (-(1/ 10 : ℝ)*Real.sqrt T)) *
                  Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|):=by ring
    _≤ ∫ t:ℝ,(za*Real.exp (-(1/ 10 : ℝ)*Real.sqrt T)) *
            ((1+|t|)^0*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|)):=by
          refine setIntegral_le_integral hdom (ae_of_all _ fun _=>by positivity [zT])
    _=zA*Real.exp (-(1/ 10 : ℝ)*Real.sqrt T):=by
          rw [integral_const_mul]; unfold zA; ring
def zz (T:ℝ):Set (ℝ × ℝ):=Set.Icc (-T) T ×ˢ Set.Icc (-T) T
def y0 (K:ℕ) (T:ℝ):Set (Fin K→ℝ × ℝ):=Set.univ.pi (fun _:Fin K=>zz T)
lemma z6 (T:ℝ):MeasurableSet (zz T) :=
  measurableSet_Icc.prod measurableSet_Icc
lemma y8 (K:ℕ) (T:ℝ):MeasurableSet (y0 K T) :=
  MeasurableSet.univ_pi fun _=>z6 T
lemma wB (K:ℕ) {T:ℝ} (hT:0≤ T) :
    (PK K (y0 K T)ᶜ).toReal≤ 2*(K:ℝ)*zA*Real.exp (-(1/ 10 : ℝ)*Real.sqrt T):=by
  have hsub:(y0 K T)ᶜ⊆⋃ k:Fin K,{ω : Fin K→ℝ × ℝ | ω k ∉ zz T}:=by
    intro ω hω
    simp only [y0,Set.mem_compl_iff,Set.mem_univ_pi,not_forall] at hω
    rcases hω with ⟨k,hk⟩
    exact Set.mem_iUnion.mpr ⟨k,hk⟩
  have hsub1:(zz T)ᶜ⊆({p:ℝ × ℝ | T< |p.1|} ∪ {p:ℝ × ℝ | T< |p.2|}):=by
    intro p hp
    simp only [zz,Set.mem_compl_iff,Set.mem_prod,Set.mem_Icc,not_and_or,not_le] at hp
    rcases hp with (h | h) | (h | h)
    · exact Or.inl (lt_of_lt_of_le (by linarith:T< -p.1) (neg_le_abs p.1))
    · exact Or.inl (lt_of_lt_of_le h (le_abs_self p.1))
    · exact Or.inr (lt_of_lt_of_le (by linarith:T< -p.2) (neg_le_abs p.2))
    · exact Or.inr (lt_of_lt_of_le h (le_abs_self p.2))
  have hrho2_compl:zn (zz T)ᶜ≤ 2*rho {t:ℝ | T< |t|}:=by
    have hset1:{p:ℝ × ℝ | T< |p.1|}={t:ℝ | T< |t|} ×ˢ Set.univ:=by ext p; simp
    have hset2:{p:ℝ × ℝ | T< |p.2|}=Set.univ ×ˢ {t:ℝ | T< |t|}:=by ext p; simp
    calc
      zn (zz T)ᶜ≤ zn ({p:ℝ × ℝ | T< |p.1|} ∪ {p:ℝ × ℝ | T< |p.2|}) :=
        measure_mono hsub1
      _≤ zn {p:ℝ × ℝ | T< |p.1|}+zn {p:ℝ × ℝ | T< |p.2|}:=measure_union_le _ _
      _=zn ({t:ℝ | T< |t|} ×ˢ Set.univ)+zn (Set.univ ×ˢ {t:ℝ | T< |t|}):=by
          rw [hset1,hset2]
      _=rho {t:ℝ | T< |t|}*rho Set.univ+rho Set.univ*rho {t:ℝ | T< |t|}:=by
          unfold zn; rw [Measure.prod_prod,Measure.prod_prod]
      _=2*rho {t:ℝ | T< |t|}:=by rw [measure_univ,mul_one,one_mul,two_mul]
  have hPK_le:PK K (y0 K T)ᶜ≤ (K:ENNReal)*(2*rho {t:ℝ | T< |t|}):=by
    calc
      PK K (y0 K T)ᶜ≤ PK K (⋃ k:Fin K,{ω : Fin K→ℝ × ℝ | ω k ∉ zz T}) :=
        measure_mono hsub
      _≤ ∑ k:Fin K,PK K {ω : Fin K→ℝ × ℝ | ω k ∉ zz T}:=measure_iUnion_fintype_le _ _
      _=∑ _k:Fin K,zn (zz T)ᶜ:=by
          refine sum_congr rfl fun k _=>?_
          have hmp:=MeasureTheory.measurePreserving_eval (fun _:Fin K=>zn) k
          change PK K ((fun ω : Fin K→ℝ × ℝ=>ω k) ⁻¹' (zz T)ᶜ)=zn (zz T)ᶜ
          exact hmp.measure_preimage (z6 T).compl.nullMeasurableSet
      _=(K:ENNReal)*zn (zz T)ᶜ:=by simp [nsmul_eq_mul]
      _≤ (K:ENNReal)*(2*rho {t:ℝ | T< |t|}):=by gcongr
  have hfin:(K:ENNReal)*(2*rho {t:ℝ | T< |t|})≠⊤:=by
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top K)
      (ENNReal.mul_ne_top (by norm_num) (measure_ne_top rho _))
  calc
    (PK K (y0 K T)ᶜ).toReal
        ≤ ((K:ENNReal)*(2*rho {t:ℝ | T< |t|})).toReal :=
          ENNReal.toReal_mono hfin hPK_le
    _=(K:ℝ)*(2*(rho {t:ℝ | T< |t|}).toReal):=by
          rw [ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_natCast]
          norm_num
    _≤ (K:ℝ)*(2*(zA*Real.exp (-(1/ 10 : ℝ)*Real.sqrt T))):=by
          gcongr; exact wS hT
    _=2*(K:ℝ)*zA*Real.exp (-(1/ 10 : ℝ)*Real.sqrt T):=by ring
lemma wA (K:ℕ) (T:ℝ) :
    (PK K).restrict (y0 K T)=Measure.pi (fun _:Fin K=>zn.restrict (zz T)):=by
  unfold PK y0
  exact Measure.restrict_pi_pi (fun _:Fin K=>zn) (fun _:Fin K=>zz T)
def wk (A:ℝ) (N:ℕ) (k:Fin (z0 N)) (t:ℝ):ℂ :=
  (1+Complex.I*(t:ℂ))/ (Real.log (z9 A N k):ℂ)
def ukp (A:ℝ) (N:ℕ) (k:Fin (z0 N)) (p:ℕ) (x:ℝ × ℝ):ℂ :=
  ((p:ℂ)^(-wk A N k x.1)+(p:ℂ)^(-wk A N k x.2) -
    (p:ℂ)^(-(wk A N k x.1+wk A N k x.2)))/ (p:ℂ)
def Ep (A:ℝ) (N v7 v6 p:ℕ) (ω : Fin (z0 N)→ℝ × ℝ):ℂ :=
  if p∣v6 then
    (∏ k∈Finset.univ.filter (fun k:Fin (z0 N) =>
        (p:ℤ)∣((v7:ℤ) - ((k.1+1 : ℕ):ℤ))),
      (1 - (p:ℂ)^(-wk A N k (ω k).1))*(1 - (p:ℂ)^(-wk A N k (ω k).2)))/ (p:ℂ)
  else
    1 - ∑ k:Fin (z0 N),ukp A N k p (ω k)
lemma w9 (A:ℝ) (N:ℕ) (k:Fin (z0 N)) (t:ℝ) :
    (wk A N k t).re=1/ Real.log (z9 A N k):=by
  unfold wk
  rw [Complex.div_ofReal_re]
  simp
lemma yf {A:ℝ} {N:ℕ} {k:Fin (z0 N)} {p:ℕ} (hp:1≤ p) (t:ℝ) :
    ‖(p:ℂ)^(-wk A N k t)‖=(p:ℝ)^(-(1/ Real.log (z9 A N k))):=by
  have hp_pos:(0 : ℝ)< p:=by positivity
  rw [← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hp_pos,Complex.neg_re,w9]
lemma yP {N v7 p:ℕ} (hpK:z0 N< p)
    {k₁ k₂ : Fin (z0 N)}
    (h1:(p:ℤ)∣((v7:ℤ) - ((k₁.1+1 : ℕ):ℤ)))
    (h2:(p:ℤ)∣((v7:ℤ) - ((k₂.1+1 : ℕ):ℤ))):k₁=k₂:=by
  by_contra hne
  have hdiff:(p:ℤ)∣((k₂.1+1 : ℕ):ℤ) - ((k₁.1+1 : ℕ):ℤ):=by
    have hsub:=dvd_sub h1 h2
    have heq:((v7:ℤ) - ((k₁.1+1 : ℕ):ℤ)) - ((v7:ℤ) - ((k₂.1+1 : ℕ):ℤ)) =
        ((k₂.1+1 : ℕ):ℤ) - ((k₁.1+1 : ℕ):ℤ):=by ring
    rwa [heq] at hsub
  have hne_val:k₁.1≠k₂.1:=fun h=>hne (Fin.ext h)
  have hk1lt:=k₁.2; have hk2lt:=k₂.2
  rcases lt_or_gt_of_ne hne_val with hlt | hgt
  · have hpos:(0 : ℤ)< ((k₂.1+1 : ℕ):ℤ) - ((k₁.1+1 : ℕ):ℤ):=by omega
    have hle:=Int.le_of_dvd hpos hdiff
    omega
  · have hdiff':(p:ℤ)∣((k₁.1+1 : ℕ):ℤ) - ((k₂.1+1 : ℕ):ℤ):=by
      have hneg:=dvd_neg.mpr hdiff
      rwa [neg_sub] at hneg
    have hpos:(0 : ℤ)< ((k₁.1+1 : ℕ):ℤ) - ((k₂.1+1 : ℕ):ℤ):=by omega
    have hle:=Int.le_of_dvd hpos hdiff'
    omega
private def zU (N v7 v6 p:ℕ) :
    Finset (Finset (Fin (z0 N)) × Finset (Fin (z0 N))) :=
  let choicesFor:Fin (z0 N)→Finset (Finset (Fin (z0 N)) × Finset (Fin (z0 N))) :=
    fun k=>{({k},∅),(∅,{k}),({k},{k})}
  if p∣v6 then
    insert (∅,∅)
      ((Finset.univ.filter (fun k:Fin (z0 N) =>
          (p:ℤ)∣((v7:ℤ) - ((k.1+1 : ℕ):ℤ)))).biUnion choicesFor)
  else
    insert (∅,∅) (Finset.univ.biUnion choicesFor)
private def zx (A:ℝ) (N v6 p:ℕ) (ω : Fin (z0 N)→ℝ × ℝ)
    (c:Finset (Fin (z0 N)) × Finset (Fin (z0 N))):ℂ :=
  (if p∣v6 then ((p:ℂ)⁻¹) else 1) *
    (∏ k∈c.1,(-(p:ℂ)^(-wk A N k (ω k).1))) *
    (∏ k∈c.2,(-(p:ℂ)^(-wk A N k (ω k).2))) *
    (if p∣v6 then 1 else if (c.1 ∪ c.2).Nonempty then ((p:ℂ)⁻¹) else 1)
private lemma wo {A:ℝ} {N v7 v6 p:ℕ} (hpK:z0 N< p)
    (ω : Fin (z0 N)→ℝ × ℝ) :
    ∑ c∈zU N v7 v6 p,zx A N v6 p ω c=Ep A N v7 v6 p ω:=by
  classical
  let choicesFor:Fin (z0 N)→Finset (Finset (Fin (z0 N)) × Finset (Fin (z0 N))) :=
    fun k=>{({k},∅),(∅,{k}),({k},{k})}
  have hnot0:∀ S:Finset (Fin (z0 N)),(∅,∅) ∉ S.biUnion choicesFor:=by
    intro S hmem
    rcases Finset.mem_biUnion.mp hmem with ⟨k,_,hk⟩
    simp only [choicesFor,mem_insert,Finset.mem_singleton,Prod.mk.injEq] at hk
    rcases hk with ⟨h,_⟩ | ⟨_,h⟩ | ⟨h,_⟩
    · exact Finset.singleton_ne_empty k h.symm
    · exact Finset.singleton_ne_empty k h.symm
    · exact Finset.singleton_ne_empty k h.symm
  have hdisj:Set.PairwiseDisjoint (Set.univ:Set (Fin (z0 N))) choicesFor:=by
    intro k₁ _ k₂ _ hne
    show Disjoint (choicesFor k₁) (choicesFor k₂)
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    simp only [choicesFor,mem_insert,Finset.mem_singleton] at hc1 hc2
    rcases hc1 with rfl | rfl | rfl <;> rcases hc2 with h | h | h <;> simp at h
    · exact hne h
    · exact hne h
    · exact hne h
  have hsum_choices:∀ (k:Fin (z0 N)) (hd:p∣v6),
      ∑ c∈choicesFor k,zx A N v6 p ω c =
        ((-(p:ℂ)^(-wk A N k (ω k).1) - (p:ℂ)^(-wk A N k (ω k).2) +
          (p:ℂ)^(-(wk A N k (ω k).1+wk A N k (ω k).2)))/ (p:ℂ)):=by
    intro k hd
    have hne1:(({k}:Finset (Fin (z0 N))),(∅ : Finset (Fin (z0 N)))) ∉
        ({(∅,{k}),({k},{k})}:Finset (Finset (Fin (z0 N)) × Finset (Fin (z0 N)))):=by
      simp
    have hne2:((∅ : Finset (Fin (z0 N))),({k}:Finset (Fin (z0 N))))≠({k},{k}):=by
      simp
    dsimp only [choicesFor]
    rw [sum_insert hne1,Finset.sum_pair hne2]
    simp only [zx,hd,↓reduceIte,Finset.prod_singleton,Finset.prod_empty,mul_one]
    have hadd:(p:ℂ)^(-wk A N k (ω k).1)*(p:ℂ)^(-wk A N k (ω k).2) =
        (p:ℂ)^(-(wk A N k (ω k).1+wk A N k (ω k).2)):=by
      have hp0:(p:ℂ)≠0:=by exact_mod_cast (show p≠0 by omega)
      rw [← Complex.cpow_add _ _ hp0]; congr 1; ring
    rw [div_eq_mul_inv]
    linear_combination (p:ℂ)⁻¹*hadd
  have hsum_choices_nd:∀ (k:Fin (z0 N)) (hnd:¬ p∣v6),
      ∑ c∈choicesFor k,zx A N v6 p ω c=-ukp A N k p (ω k):=by
    intro k hnd
    have hne1:(({k}:Finset (Fin (z0 N))),(∅ : Finset (Fin (z0 N)))) ∉
        ({(∅,{k}),({k},{k})}:Finset (Finset (Fin (z0 N)) × Finset (Fin (z0 N)))):=by
      simp
    have hne2:((∅ : Finset (Fin (z0 N))),({k}:Finset (Fin (z0 N))))≠({k},{k}):=by
      simp
    dsimp only [choicesFor]
    rw [sum_insert hne1,Finset.sum_pair hne2]
    simp only [zx,hnd,↓reduceIte,Finset.prod_singleton,Finset.prod_empty,mul_one,one_mul,
      Finset.union_empty,Finset.empty_union,Finset.union_idempotent,Finset.singleton_nonempty]
    have hadd:(p:ℂ)^(-wk A N k (ω k).1)*(p:ℂ)^(-wk A N k (ω k).2) =
        (p:ℂ)^(-(wk A N k (ω k).1+wk A N k (ω k).2)):=by
      have hp0:(p:ℂ)≠0:=by exact_mod_cast (show p≠0 by omega)
      rw [← Complex.cpow_add _ _ hp0]; congr 1; ring
    unfold ukp
    rw [div_eq_mul_inv]
    linear_combination (p:ℂ)⁻¹*hadd
  unfold zU Ep
  split_ifs with hd
  · set S:=Finset.univ.filter (fun k:Fin (z0 N) =>
      (p:ℤ)∣((v7:ℤ) - ((k.1+1 : ℕ):ℤ)))
    rw [sum_insert (hnot0 S)]
    rw [Finset.sum_biUnion (fun a _ b _ h=>hdisj (Set.mem_univ a) (Set.mem_univ b) h)]
    have h0:zx A N v6 p ω (∅,∅)=(p:ℂ)⁻¹:=by
      simp [zx,hd]
    rw [h0]
    rcases S.eq_empty_or_nonempty with hSe | ⟨k₀,hk₀⟩
    · rw [hSe,sum_empty,Finset.prod_empty,add_zero,one_div]
    · have hS_sing:S={k₀}:=by
        ext k
        simp only [Finset.mem_singleton]
        constructor
        · intro hk
          exact yP hpK (mem_filter.mp hk).2 (mem_filter.mp hk₀).2
        · rintro rfl; exact hk₀
      rw [hS_sing,Finset.sum_singleton,Finset.prod_singleton,hsum_choices k₀ hd]
      have hadd:(p:ℂ)^(-wk A N k₀ (ω k₀).1)*(p:ℂ)^(-wk A N k₀ (ω k₀).2) =
          (p:ℂ)^(-(wk A N k₀ (ω k₀).1+wk A N k₀ (ω k₀).2)):=by
        have hp0:(p:ℂ)≠0:=by exact_mod_cast (show p≠0 by omega)
        rw [← Complex.cpow_add _ _ hp0]; congr 1; ring
      rw [div_eq_mul_inv,div_eq_mul_inv]
      linear_combination -(p:ℂ)⁻¹*hadd
  · rw [sum_insert (hnot0 Finset.univ)]
    rw [Finset.sum_biUnion (fun a _ b _ h=>hdisj (Set.mem_univ a) (Set.mem_univ b) h)]
    have h0:zx A N v6 p ω (∅,∅)=1:=by
      simp [zx,hd]
    rw [h0,sum_congr rfl (fun k _=>hsum_choices_nd k hd),Finset.sum_neg_distrib,
      ← sub_eq_add_neg]
end
end Erdos413Sieve
namespace Erdos413Sieve
open Finset Filter Topology Complex Real MeasureTheory
open Erdos413Bump Erdos413Mertens
open scoped BigOperators
noncomputable section
def zR (N v7 v6:ℕ) (dd:Fin (z0 N)→ℕ × ℕ):Prop :=
  (∀ k:Fin (z0 N),
      Squarefree (dd k).1∧Squarefree (dd k).2 ∧
      Nat.Coprime (dd k).1 (z4 N)∧Nat.Coprime (dd k).2 (z4 N)) ∧
  xi N v7 v6 dd
def y7 (A:ℝ) (N v7 v6:ℕ) (dd:Fin (z0 N)→ℕ × ℕ)
    (ω : Fin (z0 N)→ℝ × ℝ):ℂ :=
  letI:Decidable (zR N v7 v6 dd):=Classical.propDecidable _
  if zR N v7 v6 dd then
    ((v6:ℂ)⁻¹)*∏ k:Fin (z0 N),
      (((ArithmeticFunction.moebius (dd k).1 : ℤ):ℂ) *
       ((ArithmeticFunction.moebius (dd k).2 : ℤ):ℂ) *
       ((dd k).1 : ℂ)^(-wk A N k (ω k).1) *
       ((dd k).2 : ℂ)^(-wk A N k (ω k).2) *
       (((Nat.gcd (Nat.lcm (dd k).1 (dd k).2) v6:ℕ):ℂ) /
        ((Nat.lcm (dd k).1 (dd k).2 : ℕ):ℂ)))
  else 0
def zW (A:ℝ) (N v7 v6:ℕ) (ω : Fin (z0 N)→ℝ × ℝ):ℂ :=
  ∑' dd:Fin (z0 N)→ℕ × ℕ,y7 A N v7 v6 dd ω
lemma zZ (A:ℝ) (N v7 v6:ℕ) (dd:Fin (z0 N)→ℕ × ℕ)
    (ω : Fin (z0 N)→ℝ × ℝ) :
    ‖y7 A N v7 v6 dd ω‖=‖y7 A N v7 v6 dd 0‖:=by
  classical
  unfold y7
  split_ifs with h
  · simp only [norm_mul,norm_prod]
    congr 1
    refine Finset.prod_congr rfl fun k _=>?_
    have h1pos:1≤ (dd k).1:=Nat.pos_of_ne_zero (h.1 k).1.ne_zero
    have h2pos:1≤ (dd k).2:=Nat.pos_of_ne_zero (h.1 k).2.1.ne_zero
    simp only [norm_div,yf h1pos,yf h2pos]
  · rfl
lemma xh (A:ℝ) (N v7 v6:ℕ) (dd:Fin (z0 N)→ℕ × ℕ) :
    Continuous (y7 A N v7 v6 dd):=by
  classical
  unfold y7
  split_ifs with h
  · refine continuous_const.mul (continuous_finsetProd _ fun k _=>?_)
    have h1ne:((dd k).1 : ℂ)≠0:=by exact_mod_cast (h.1 k).1.ne_zero
    have h2ne:((dd k).2 : ℂ)≠0:=by exact_mod_cast (h.1 k).2.1.ne_zero
    have hwk1:Continuous (fun ω : Fin (z0 N)→ℝ × ℝ=>-wk A N k (ω k).1):=by
      unfold wk
      exact (((continuous_const.add (continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_fst.comp (continuous_apply k))))).div_const _).neg)
    have hwk2:Continuous (fun ω : Fin (z0 N)→ℝ × ℝ=>-wk A N k (ω k).2):=by
      unfold wk
      exact (((continuous_const.add (continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_snd.comp (continuous_apply k))))).div_const _).neg)
    have hc1:Continuous (fun ω : Fin (z0 N)→ℝ × ℝ=>((dd k).1 : ℂ)^(-wk A N k (ω k).1)):=by
      simp_rw [Complex.cpow_def_of_ne_zero h1ne]
      exact Complex.continuous_exp.comp (continuous_const.mul hwk1)
    have hc2:Continuous (fun ω : Fin (z0 N)→ℝ × ℝ=>((dd k).2 : ℂ)^(-wk A N k (ω k).2)):=by
      simp_rw [Complex.cpow_def_of_ne_zero h2ne]
      exact Complex.continuous_exp.comp (continuous_const.mul hwk2)
    exact ((continuous_const.mul hc1).mul hc2).mul continuous_const
  · exact continuous_const
private def zi {K:ℕ} (P:Finset ℕ)
    (f:P→Finset (Fin K) × Finset (Fin K)):Fin K→ℕ × ℕ :=
  fun k =>
    (∏ p∈P.attach.filter (fun p=>k∈(f p).1),(p:ℕ),
     ∏ p∈P.attach.filter (fun p=>k∈(f p).2),(p:ℕ))
private lemma x6 {s:Finset ℕ} (hs:∀ p∈s,p.Prime) :
    Squarefree (∏ p∈s,p):=by
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ fun p hp=>(hs p hp).squarefree
  intro p hp q hq hpq
  show IsRelPrime p q
  rw [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq
private lemma zF {s:Finset ℕ} (hs:∀ p∈s,p.Prime)
    {q:ℕ} (hq:q.Prime):q∣∏ p∈s,p↔q∈s:=by
  rw [hq.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨p,hps,hqp⟩
    have:=(Nat.prime_dvd_prime_iff_eq hq (hs p hps)).mp hqp
    rwa [this]
  · intro hqs; exact ⟨q,hqs,dvd_rfl⟩
private lemma yF {A:ℝ} {N v7 v6 y:ℕ}
    (_hKw:z0 N< z7 N)
    (hdstar_sf:Squarefree v6) (hdstar_cop:Nat.Coprime v6 (z4 N))
    (hdstar_le:v6≤ y)
    (f:z2 (z7 N) y→Finset (Fin (z0 N)) × Finset (Fin (z0 N)))
    (hf:∀ p:z2 (z7 N) y,f p∈zU N v7 v6 (p:ℕ))
    (ω : Fin (z0 N)→ℝ × ℝ) :
    zR N v7 v6 (zi (z2 (z7 N) y) f) ∧
    y7 A N v7 v6 (zi (z2 (z7 N) y) f) ω =
      ∏ p:z2 (z7 N) y,zx A N v6 (p:ℕ) ω (f p):=by
  classical
  let P:=z2 (z7 N) y
  have hP_prime:∀ p∈P,p.Prime:=fun p hp=>(mem_filter.mp hp).2
  have hP_gt:∀ p∈P,z7 N< p:=fun p hp=>(mem_Ioc.mp (mem_filter.mp hp).1).1
  let dd:=zi P f
  have hdd1_eq:∀ k:Fin (z0 N),
      (dd k).1=∏ p∈P.attach.filter (fun p=>k∈(f p).1),(p:ℕ):=fun _=>rfl
  have hdd2_eq:∀ k:Fin (z0 N),
      (dd k).2=∏ p∈P.attach.filter (fun p=>k∈(f p).2),(p:ℕ):=fun _=>rfl
  have hprod_image:∀ (S:Finset P),∏ p∈S,(p:ℕ)=∏ q∈S.image Subtype.val,q:=fun S=>by
    rw [Finset.prod_image]; intro a _ b _ h; exact Subtype.ext h
  have hdd1_sf:∀ k,Squarefree (dd k).1:=fun k=>by
    rw [hdd1_eq,hprod_image]
    refine x6 fun q hq=>?_
    rcases Finset.mem_image.mp hq with ⟨p,_,rfl⟩
    exact hP_prime p.1 p.2
  have hdd2_sf:∀ k,Squarefree (dd k).2:=fun k=>by
    rw [hdd2_eq,hprod_image]
    refine x6 fun q hq=>?_
    rcases Finset.mem_image.mp hq with ⟨p,_,rfl⟩
    exact hP_prime p.1 p.2
  have hdd1_dvd:∀ (k:Fin (z0 N)) (q:ℕ),q.Prime →
      (q∣(dd k).1↔∃ hq:q∈P,k∈(f ⟨q,hq⟩).1):=by
    intro k q hq
    rw [hdd1_eq,hprod_image,zF (fun r hr=>by
      rcases Finset.mem_image.mp hr with ⟨p,_,rfl⟩; exact hP_prime p.1 p.2) hq]
    simp only [Finset.mem_image,mem_filter,Finset.mem_attach,true_and,Subtype.exists]
    constructor
    · rintro ⟨r,hrP,hkr,rfl⟩; exact ⟨hrP,hkr⟩
    · rintro ⟨hqP,hkq⟩; exact ⟨q,hqP,hkq,rfl⟩
  have hdd2_dvd:∀ (k:Fin (z0 N)) (q:ℕ),q.Prime →
      (q∣(dd k).2↔∃ hq:q∈P,k∈(f ⟨q,hq⟩).2):=by
    intro k q hq
    rw [hdd2_eq,hprod_image,zF (fun r hr=>by
      rcases Finset.mem_image.mp hr with ⟨p,_,rfl⟩; exact hP_prime p.1 p.2) hq]
    simp only [Finset.mem_image,mem_filter,Finset.mem_attach,true_and,Subtype.exists]
    constructor
    · rintro ⟨r,hrP,hkr,rfl⟩; exact ⟨hrP,hkr⟩
    · rintro ⟨hqP,hkq⟩; exact ⟨q,hqP,hkq,rfl⟩
  have hf_card:∀ (p:P) (k₁ k₂ : Fin (z0 N)),
      k₁∈(f p).1 ∪ (f p).2→k₂∈(f p).1 ∪ (f p).2→k₁=k₂:=by
    intro p k₁ k₂ h1 h2
    have hfp:=hf p
    unfold zU at hfp
    split_ifs at hfp
    · simp only [mem_insert,Finset.mem_biUnion,mem_filter,Finset.mem_univ,
        true_and,Finset.mem_singleton] at hfp
      rcases hfp with h0 | ⟨k,_,h0 | h0 | h0⟩
      · rw [h0] at h1; simp at h1
      · rw [h0] at h1 h2; simp at h1 h2; exact h1.trans h2.symm
      · rw [h0] at h1 h2; simp at h1 h2; exact h1.trans h2.symm
      · rw [h0] at h1 h2; simp at h1 h2; exact h1.trans h2.symm
    · simp only [mem_insert,Finset.mem_biUnion,Finset.mem_univ,true_and,
        Finset.mem_singleton] at hfp
      rcases hfp with h0 | ⟨k,h0 | h0 | h0⟩
      · rw [h0] at h1; simp at h1
      · rw [h0] at h1 h2; simp at h1 h2; exact h1.trans h2.symm
      · rw [h0] at h1 h2; simp at h1 h2; exact h1.trans h2.symm
      · rw [h0] at h1 h2; simp at h1 h2; exact h1.trans h2.symm
  have hf_dvd:∀ (p:P) (k:Fin (z0 N)),(p:ℕ)∣v6 →
      k∈(f p).1 ∪ (f p).2→((p:ℕ):ℤ)∣((v7:ℤ) - ((k.1+1 : ℕ):ℤ)):=by
    intro p k hpd hk
    have hfp:=hf p
    unfold zU at hfp
    rw [if_pos hpd] at hfp
    simp only [mem_insert,Finset.mem_biUnion,mem_filter,Finset.mem_univ,
      true_and,Finset.mem_singleton] at hfp
    rcases hfp with h0 | ⟨k₀,hdvd,h0 | h0 | h0⟩
    · rw [h0] at hk; simp at hk
    · rw [h0] at hk; simp at hk; rwa [hk]
    · rw [h0] at hk; simp at hk; rwa [hk]
    · rw [h0] at hk; simp at hk; rwa [hk]
  have hvalid:zR N v7 v6 dd:=by
    refine ⟨fun k=>⟨hdd1_sf k,hdd2_sf k,?_,?_⟩,?_,?_⟩
    · rw [zk (hdd1_sf k).ne_zero N]
      intro q hq hqd
      rcases (hdd1_dvd k q hq).mp hqd with ⟨hqP,_⟩
      exact hP_gt q hqP
    · rw [zk (hdd2_sf k).ne_zero N]
      intro q hq hqd
      rcases (hdd2_dvd k q hq).mp hqd with ⟨hqP,_⟩
      exact hP_gt q hqP
    · intro k₁ k₂ hne
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hgc
      let q:=(Nat.gcd (Nat.lcm (dd k₁).1 (dd k₁).2) (Nat.lcm (dd k₂).1 (dd k₂).2)).minFac
      have hq:q.Prime:=Nat.minFac_prime hgc
      have hq1:q∣Nat.lcm (dd k₁).1 (dd k₁).2:=(Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)
      have hq2:q∣Nat.lcm (dd k₂).1 (dd k₂).2:=(Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
      have hq1':q∣(dd k₁).1∨q∣(dd k₁).2 :=
        hq.dvd_mul.mp (hq1.trans (Nat.lcm_dvd_mul _ _))
      have hq2':q∣(dd k₂).1∨q∣(dd k₂).2 :=
        hq.dvd_mul.mp (hq2.trans (Nat.lcm_dvd_mul _ _))
      have hmem1:∃ hqP:q∈P,k₁∈(f ⟨q,hqP⟩).1 ∪ (f ⟨q,hqP⟩).2:=by
        rcases hq1' with h | h
        · rcases (hdd1_dvd k₁ q hq).mp h with ⟨hqP,hm⟩
          exact ⟨hqP,Finset.mem_union_left _ hm⟩
        · rcases (hdd2_dvd k₁ q hq).mp h with ⟨hqP,hm⟩
          exact ⟨hqP,Finset.mem_union_right _ hm⟩
      have hmem2:∃ hqP:q∈P,k₂∈(f ⟨q,hqP⟩).1 ∪ (f ⟨q,hqP⟩).2:=by
        rcases hq2' with h | h
        · rcases (hdd1_dvd k₂ q hq).mp h with ⟨hqP,hm⟩
          exact ⟨hqP,Finset.mem_union_left _ hm⟩
        · rcases (hdd2_dvd k₂ q hq).mp h with ⟨hqP,hm⟩
          exact ⟨hqP,Finset.mem_union_right _ hm⟩
      rcases hmem1 with ⟨hqP,hm1⟩
      rcases hmem2 with ⟨_,hm2⟩
      exact hne (hf_card ⟨q,hqP⟩ k₁ k₂ hm1 hm2)
    · intro k
      set g:=Nat.gcd (Nat.lcm (dd k).1 (dd k).2) v6
      have hg_sf:Squarefree g:=hdstar_sf.squarefree_of_dvd (Nat.gcd_dvd_right _ _)
      rw [← Nat.prod_primeFactors_of_squarefree hg_sf]
      refine xx (fun q hq=>Nat.prime_of_mem_primeFactors hq) fun q hq=>?_
      have hqp:q.Prime:=Nat.prime_of_mem_primeFactors hq
      have hqg:q∣g:=Nat.dvd_of_mem_primeFactors hq
      have hqd:q∣v6:=hqg.trans (Nat.gcd_dvd_right _ _)
      have hqlcm:q∣Nat.lcm (dd k).1 (dd k).2:=hqg.trans (Nat.gcd_dvd_left _ _)
      have hq12:q∣(dd k).1∨q∣(dd k).2:=hqp.dvd_mul.mp (hqlcm.trans (Nat.lcm_dvd_mul _ _))
      rcases hq12 with h | h
      · rcases (hdd1_dvd k q hqp).mp h with ⟨hqP,hm⟩
        exact hf_dvd ⟨q,hqP⟩ k hqd (Finset.mem_union_left _ hm)
      · rcases (hdd2_dvd k q hqp).mp h with ⟨hqP,hm⟩
        exact hf_dvd ⟨q,hqP⟩ k hqd (Finset.mem_union_right _ hm)
  refine ⟨hvalid,?_⟩
  unfold y7
  rw [if_pos hvalid]
  have hdstar_eq:v6=∏ p∈P.filter (fun p=>p∣v6),p:=by
    conv_lhs=>rw [← Nat.prod_primeFactors_of_squarefree hdstar_sf]
    congr 1
    ext q
    simp only [Nat.mem_primeFactors,mem_filter,P,z2,mem_Ioc]
    constructor
    · rintro ⟨hq,hqd,hd0⟩
      have hq_gt:z7 N< q:=(zk hd0 N).mp hdstar_cop q hq hqd
      have hq_le:q≤ y:=(Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hqd).trans hdstar_le
      exact ⟨⟨⟨hq_gt,hq_le⟩,hq⟩,hqd⟩
    · rintro ⟨⟨⟨_,_⟩,hq⟩,hqd⟩
      exact ⟨hq,hqd,hdstar_sf.ne_zero⟩
  have hdstar_inv:((v6:ℂ)⁻¹) =
      ∏ p:P,(if (p:ℕ)∣v6 then ((p:ℂ)⁻¹) else 1):=by
    rw [Finset.prod_coe_sort P (fun p=>if p∣v6 then ((p:ℂ)⁻¹) else 1)]
    conv_lhs=>rw [hdstar_eq]
    rw [Nat.cast_prod,← Finset.prod_inv_distrib,Finset.prod_filter]
  have hfactor_mu_cpow:∀ (k:Fin (z0 N)) (t:ℝ) (S:Finset P),
      let m:=∏ p∈S,(p:ℕ)
      ((ArithmeticFunction.moebius m:ℤ):ℂ)*((m:ℕ):ℂ)^(-wk A N k t) =
        ∏ p∈S,(-(p:ℂ)^(-wk A N k t)):=by
    intro k t S
    induction S using Finset.induction_on with
    | empty=>simp
    | insert p S hpS ih =>
      simp only [Finset.prod_insert hpS]
      have hp_pr:(p:ℕ).Prime:=hP_prime p.1 p.2
      have hcop:Nat.Coprime (p:ℕ) (∏ q∈S,(q:ℕ)):=by
        refine Nat.Coprime.prod_right fun q hq=>?_
        have hne:(p:ℕ)≠(q:ℕ):=fun h=>hpS (Subtype.ext h ▸ hq)
        exact (Nat.coprime_primes hp_pr (hP_prime q.1 q.2)).mpr hne
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
        ArithmeticFunction.moebius_apply_prime hp_pr]
      have hcpow_mul:(((p:ℕ)*∏ q∈S,(q:ℕ):ℕ):ℂ)^(-wk A N k t) =
          ((p:ℕ):ℂ)^(-wk A N k t)*((∏ q∈S,(q:ℕ):ℕ):ℂ)^(-wk A N k t):=by
        rw [Nat.cast_mul,← Complex.ofReal_natCast,← Complex.ofReal_natCast,
          Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
          Complex.ofReal_natCast,Complex.ofReal_natCast]
      rw [hcpow_mul,Int.cast_mul,Int.cast_neg,Int.cast_one]
      linear_combination (-(p:ℂ)^(-wk A N k t))*ih
  have hfactor_gcd_lcm:∀ k:Fin (z0 N),
      (((Nat.gcd (Nat.lcm (dd k).1 (dd k).2) v6:ℕ):ℂ) /
       ((Nat.lcm (dd k).1 (dd k).2 : ℕ):ℂ)) =
        ∏ p:P,if k∈(f p).1 ∪ (f p).2 then
          (if (p:ℕ)∣v6 then (1 : ℂ) else ((p:ℂ)⁻¹)) else 1:=by
    intro k
    have hlcm_sf:Squarefree (Nat.lcm (dd k).1 (dd k).2):=wi (hdd1_sf k) (hdd2_sf k)
    have hlcm_eq:Nat.lcm (dd k).1 (dd k).2 =
        ∏ p∈P.attach.filter (fun p=>k∈(f p).1 ∪ (f p).2),(p:ℕ):=by
      rw [hprod_image,← Nat.prod_primeFactors_of_squarefree hlcm_sf]
      congr 1; ext q
      simp only [Nat.mem_primeFactors,Finset.mem_image,mem_filter,Finset.mem_attach,
        true_and,Subtype.exists]
      constructor
      · rintro ⟨hq,hqlcm,_⟩
        rcases hq.dvd_mul.mp (hqlcm.trans (Nat.lcm_dvd_mul _ _)) with h | h
        · rcases (hdd1_dvd k q hq).mp h with ⟨hqP,hm⟩
          exact ⟨q,hqP,Finset.mem_union_left _ hm,rfl⟩
        · rcases (hdd2_dvd k q hq).mp h with ⟨hqP,hm⟩
          exact ⟨q,hqP,Finset.mem_union_right _ hm,rfl⟩
      · rintro ⟨r,hrP,hrm,rfl⟩
        refine ⟨hP_prime r hrP,?_,hlcm_sf.ne_zero⟩
        rcases mem_union.mp hrm with h1 | h2
        · exact ((hdd1_dvd k r (hP_prime r hrP)).mpr ⟨hrP,h1⟩).trans (Nat.dvd_lcm_left _ _)
        · exact ((hdd2_dvd k r (hP_prime r hrP)).mpr ⟨hrP,h2⟩).trans (Nat.dvd_lcm_right _ _)
    have hgcd_eq:Nat.gcd (Nat.lcm (dd k).1 (dd k).2) v6 =
        ∏ p∈P.attach.filter (fun p=>k∈(f p).1 ∪ (f p).2∧(p:ℕ)∣v6),(p:ℕ):=by
      have hg_sf:Squarefree (Nat.gcd (Nat.lcm (dd k).1 (dd k).2) v6) :=
        hlcm_sf.squarefree_of_dvd (Nat.gcd_dvd_left _ _)
      rw [hprod_image,← Nat.prod_primeFactors_of_squarefree hg_sf]
      congr 1; ext q
      simp only [Nat.mem_primeFactors,Finset.mem_image,mem_filter,Finset.mem_attach,
        true_and,Subtype.exists]
      constructor
      · rintro ⟨hq,hqg,_⟩
        have hqlcm:q∣Nat.lcm (dd k).1 (dd k).2:=hqg.trans (Nat.gcd_dvd_left _ _)
        have hqd:q∣v6:=hqg.trans (Nat.gcd_dvd_right _ _)
        rcases hq.dvd_mul.mp (hqlcm.trans (Nat.lcm_dvd_mul _ _)) with h | h
        · rcases (hdd1_dvd k q hq).mp h with ⟨hqP,hm⟩
          exact ⟨q,hqP,⟨Finset.mem_union_left _ hm,hqd⟩,rfl⟩
        · rcases (hdd2_dvd k q hq).mp h with ⟨hqP,hm⟩
          exact ⟨q,hqP,⟨Finset.mem_union_right _ hm,hqd⟩,rfl⟩
      · rintro ⟨r,hrP,⟨hrm,hrd⟩,rfl⟩
        refine ⟨hP_prime r hrP,Nat.dvd_gcd ?_ hrd,hg_sf.ne_zero⟩
        rcases mem_union.mp hrm with h1 | h2
        · exact ((hdd1_dvd k r (hP_prime r hrP)).mpr ⟨hrP,h1⟩).trans (Nat.dvd_lcm_left _ _)
        · exact ((hdd2_dvd k r (hP_prime r hrP)).mpr ⟨hrP,h2⟩).trans (Nat.dvd_lcm_right _ _)
    rw [hgcd_eq,hlcm_eq,Nat.cast_prod,Nat.cast_prod,Finset.prod_filter,Finset.prod_filter,
      ← prod_div_distrib]
    refine Finset.prod_congr rfl fun p _=>?_
    have hp0:((p:ℕ):ℂ)≠0:=by exact_mod_cast (hP_prime p.1 p.2).ne_zero
    by_cases hk:k∈(f p).1 ∪ (f p).2 <;> by_cases hd:(p:ℕ)∣v6 <;> simp [hk,hd,hp0]
  have hprod_k:∀ k:Fin (z0 N),
      (((ArithmeticFunction.moebius (dd k).1 : ℤ):ℂ) *
       ((ArithmeticFunction.moebius (dd k).2 : ℤ):ℂ) *
       ((dd k).1 : ℂ)^(-wk A N k (ω k).1) *
       ((dd k).2 : ℂ)^(-wk A N k (ω k).2) *
       (((Nat.gcd (Nat.lcm (dd k).1 (dd k).2) v6:ℕ):ℂ) /
        ((Nat.lcm (dd k).1 (dd k).2 : ℕ):ℂ))) =
      ∏ p:P,
        ((if k∈(f p).1 then -(p:ℂ)^(-wk A N k (ω k).1) else 1) *
         (if k∈(f p).2 then -(p:ℂ)^(-wk A N k (ω k).2) else 1) *
         (if k∈(f p).1 ∪ (f p).2 then (if (p:ℕ)∣v6 then (1 : ℂ) else ((p:ℂ)⁻¹)) else 1)):=by
    intro k
    have h1:=hfactor_mu_cpow k (ω k).1 (P.attach.filter (fun p=>k∈(f p).1))
    have h2:=hfactor_mu_cpow k (ω k).2 (P.attach.filter (fun p=>k∈(f p).2))
    have h3:=hfactor_gcd_lcm k
    dsimp only at h1 h2
    have hrew:(((ArithmeticFunction.moebius (dd k).1 : ℤ):ℂ) *
        ((ArithmeticFunction.moebius (dd k).2 : ℤ):ℂ) *
        ((dd k).1 : ℂ)^(-wk A N k (ω k).1) *
        ((dd k).2 : ℂ)^(-wk A N k (ω k).2) *
        (((Nat.gcd (Nat.lcm (dd k).1 (dd k).2) v6:ℕ):ℂ) /
         ((Nat.lcm (dd k).1 (dd k).2 : ℕ):ℂ))) =
        ((((ArithmeticFunction.moebius (dd k).1 : ℤ):ℂ)*((dd k).1 : ℂ)^(-wk A N k (ω k).1)) *
         (((ArithmeticFunction.moebius (dd k).2 : ℤ):ℂ)*((dd k).2 : ℂ)^(-wk A N k (ω k).2))) *
        (((Nat.gcd (Nat.lcm (dd k).1 (dd k).2) v6:ℕ):ℂ) /
         ((Nat.lcm (dd k).1 (dd k).2 : ℕ):ℂ)):=by ring
    have hPatt:P.attach=Finset.univ:=by ext x; simp
    rw [hrew,h3,hdd1_eq,hdd2_eq,h1,h2,Finset.prod_filter,Finset.prod_filter,hPatt,
      ← prod_mul_distrib,← prod_mul_distrib]
  rw [hdstar_inv,Finset.prod_congr rfl (fun k _=>hprod_k k),Finset.prod_comm,
    ← prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _=>?_
  unfold zx
  rw [prod_mul_distrib,prod_mul_distrib]
  have h1p:(∏ k:Fin (z0 N),if k∈(f p).1 then -(p:ℂ)^(-wk A N k (ω k).1) else 1) =
      ∏ k∈(f p).1,(-(p:ℂ)^(-wk A N k (ω k).1)):=by
    rw [← Finset.prod_filter]; congr 1; ext k; simp
  have h2p:(∏ k:Fin (z0 N),if k∈(f p).2 then -(p:ℂ)^(-wk A N k (ω k).2) else 1) =
      ∏ k∈(f p).2,(-(p:ℂ)^(-wk A N k (ω k).2)):=by
    rw [← Finset.prod_filter]; congr 1; ext k; simp
  have h3p:(∏ k:Fin (z0 N),
      if k∈(f p).1 ∪ (f p).2 then (if (p:ℕ)∣v6 then (1 : ℂ) else ((p:ℂ)⁻¹)) else 1) =
      (if (p:ℕ)∣v6 then 1 else if ((f p).1 ∪ (f p).2).Nonempty then ((p:ℂ)⁻¹) else 1):=by
    rw [← Finset.prod_filter]
    have hfilt:Finset.univ.filter (fun k:Fin (z0 N)=>k∈(f p).1 ∪ (f p).2) =
        (f p).1 ∪ (f p).2:=by ext k; simp
    rw [hfilt]
    rcases ((f p).1 ∪ (f p).2).eq_empty_or_nonempty with he | ⟨k₀,hk₀⟩
    · rw [he,Finset.prod_empty]; simp
    · have hsing:(f p).1 ∪ (f p).2={k₀}:=by
        ext k; simp only [Finset.mem_singleton]
        exact ⟨fun hk=>hf_card p k k₀ hk hk₀,fun h=>h ▸ hk₀⟩
      rw [hsing,Finset.prod_singleton,if_pos (Finset.singleton_nonempty k₀)]
  rw [h1p,h2p,h3p]
  ring
end
end Erdos413Sieve
namespace Erdos413Sieve
open Finset Filter Topology Complex Real MeasureTheory
open Erdos413Bump Erdos413Mertens
open scoped BigOperators
noncomputable section
private lemma xm {N y:ℕ}
    {f₁ f₂ : z2 (z7 N) y→Finset (Fin (z0 N)) × Finset (Fin (z0 N))}
    (heq:zi (z2 (z7 N) y) f₁=zi (z2 (z7 N) y) f₂) :
    f₁=f₂:=by
  let P:=z2 (z7 N) y
  have hP_prime:∀ p∈P,p.Prime:=fun p hp=>(mem_filter.mp hp).2
  have hprod_image:∀ (S:Finset P),∏ p∈S,(p:ℕ)=∏ q∈S.image Subtype.val,q:=fun S=>by
    rw [Finset.prod_image]; intro a _ b _ h; exact Subtype.ext h
  funext p
  apply Prod.ext
  · ext k
    have hk:=congrArg (fun d=>(d k).1) heq
    have h1:(p:ℕ)∣(zi P f₁ k).1↔k∈(f₁ p).1:=by
      dsimp only [zi]
      rw [hprod_image,zF (fun r hr=>by
        rcases Finset.mem_image.mp hr with ⟨q,_,rfl⟩; exact hP_prime q.1 q.2) (hP_prime p.1 p.2)]
      simp only [Finset.mem_image,mem_filter,Finset.mem_attach,true_and,Subtype.exists]
      constructor
      · rintro ⟨q,hqP,hkq,hqp⟩
        have : (⟨q,hqP⟩ : P)=p:=Subtype.ext hqp
        rwa [← this]
      · intro hkp; exact ⟨p.1,p.2,hkp,rfl⟩
    have h2:(p:ℕ)∣(zi P f₂ k).1↔k∈(f₂ p).1:=by
      dsimp only [zi]
      rw [hprod_image,zF (fun r hr=>by
        rcases Finset.mem_image.mp hr with ⟨q,_,rfl⟩; exact hP_prime q.1 q.2) (hP_prime p.1 p.2)]
      simp only [Finset.mem_image,mem_filter,Finset.mem_attach,true_and,Subtype.exists]
      constructor
      · rintro ⟨q,hqP,hkq,hqp⟩
        have : (⟨q,hqP⟩ : P)=p:=Subtype.ext hqp
        rwa [← this]
      · intro hkp; exact ⟨p.1,p.2,hkp,rfl⟩
    rw [← h1,hk,h2]
  · ext k
    have hk:=congrArg (fun d=>(d k).2) heq
    have h1:(p:ℕ)∣(zi P f₁ k).2↔k∈(f₁ p).2:=by
      dsimp only [zi]
      rw [hprod_image,zF (fun r hr=>by
        rcases Finset.mem_image.mp hr with ⟨q,_,rfl⟩; exact hP_prime q.1 q.2) (hP_prime p.1 p.2)]
      simp only [Finset.mem_image,mem_filter,Finset.mem_attach,true_and,Subtype.exists]
      constructor
      · rintro ⟨q,hqP,hkq,hqp⟩
        have : (⟨q,hqP⟩ : P)=p:=Subtype.ext hqp
        rwa [← this]
      · intro hkp; exact ⟨p.1,p.2,hkp,rfl⟩
    have h2:(p:ℕ)∣(zi P f₂ k).2↔k∈(f₂ p).2:=by
      dsimp only [zi]
      rw [hprod_image,zF (fun r hr=>by
        rcases Finset.mem_image.mp hr with ⟨q,_,rfl⟩; exact hP_prime q.1 q.2) (hP_prime p.1 p.2)]
      simp only [Finset.mem_image,mem_filter,Finset.mem_attach,true_and,Subtype.exists]
      constructor
      · rintro ⟨q,hqP,hkq,hqp⟩
        have : (⟨q,hqP⟩ : P)=p:=Subtype.ext hqp
        rwa [← this]
      · intro hkp; exact ⟨p.1,p.2,hkp,rfl⟩
    rw [← h1,hk,h2]
private def Sy (N v7 v6 y:ℕ):Finset (Fin (z0 N)→ℕ × ℕ) :=
  (Fintype.piFinset (fun p:z2 (z7 N) y=>zU N v7 v6 (p:ℕ))).image
    (zi (z2 (z7 N) y))
private lemma xt {N v7 v6 y:ℕ}
    {dd:Fin (z0 N)→ℕ × ℕ} (hvalid:zR N v7 v6 dd)
    (hle:∀ k:Fin (z0 N),(dd k).1≤ y∧(dd k).2≤ y) :
    dd∈Sy N v7 v6 y:=by
  classical
  let P:=z2 (z7 N) y
  let f:∀ p:P,Finset (Fin (z0 N)) × Finset (Fin (z0 N)) :=
    fun p=>(Finset.univ.filter (fun k=>(p:ℕ)∣(dd k).1),
              Finset.univ.filter (fun k=>(p:ℕ)∣(dd k).2))
  have hP_prime:∀ p∈P,p.Prime:=fun p hp=>(mem_filter.mp hp).2
  have hf_mem:f∈Fintype.piFinset (fun p:P=>zU N v7 v6 (p:ℕ)):=by
    rw [Fintype.mem_piFinset]
    intro p
    have hp_pr:(p:ℕ).Prime:=hP_prime p.1 p.2
    have huniq:∀ k₁ k₂ : Fin (z0 N),
        k₁∈(f p).1 ∪ (f p).2→k₂∈(f p).1 ∪ (f p).2→k₁=k₂:=by
      intro k₁ k₂ h1 h2
      by_contra hne
      have hd1:(p:ℕ)∣Nat.lcm (dd k₁).1 (dd k₁).2:=by
        rcases mem_union.mp h1 with hm | hm
        · exact ((mem_filter.mp hm).2).trans (Nat.dvd_lcm_left _ _)
        · exact ((mem_filter.mp hm).2).trans (Nat.dvd_lcm_right _ _)
      have hd2:(p:ℕ)∣Nat.lcm (dd k₂).1 (dd k₂).2:=by
        rcases mem_union.mp h2 with hm | hm
        · exact ((mem_filter.mp hm).2).trans (Nat.dvd_lcm_left _ _)
        · exact ((mem_filter.mp hm).2).trans (Nat.dvd_lcm_right _ _)
      have hcop:=hvalid.2.1 k₁ k₂ hne
      have hpg:(p:ℕ)∣1:=by
        rw [← hcop.gcd_eq_one]; exact Nat.dvd_gcd hd1 hd2
      exact hp_pr.ne_one (Nat.dvd_one.mp hpg)
    rcases ((f p).1 ∪ (f p).2).eq_empty_or_nonempty with he | ⟨k₀,hk₀⟩
    · have h1:(f p).1=∅:=Finset.union_eq_empty.mp he |>.1
      have h2:(f p).2=∅:=Finset.union_eq_empty.mp he |>.2
      have hpair:f p=(∅,∅):=Prod.ext h1 h2
      rw [hpair]; unfold zU; split_ifs <;> exact Finset.mem_insert_self _ _
    · have hsing:(f p).1 ∪ (f p).2={k₀}:=by
        ext k; simp only [Finset.mem_singleton]
        exact ⟨fun hk=>huniq k k₀ hk hk₀,fun h=>h ▸ hk₀⟩
      have hcase:f p=({k₀},∅)∨f p=(∅,{k₀})∨f p=({k₀},{k₀}):=by
        have hsub1:(f p).1⊆{k₀}:=by rw [← hsing]; exact Finset.subset_union_left
        have hsub2:(f p).2⊆{k₀}:=by rw [← hsing]; exact Finset.subset_union_right
        rcases Finset.subset_singleton_iff.mp hsub1 with h1 | h1 <;>
          rcases Finset.subset_singleton_iff.mp hsub2 with h2 | h2
        · exfalso; rw [h1,h2,Finset.union_empty] at hsing
          exact Finset.singleton_ne_empty k₀ hsing.symm
        · exact Or.inr (Or.inl (Prod.ext h1 h2))
        · exact Or.inl (Prod.ext h1 h2)
        · exact Or.inr (Or.inr (Prod.ext h1 h2))
      unfold zU
      split_ifs with hpd
      · apply Finset.mem_insert_of_mem
        rw [Finset.mem_biUnion]
        refine ⟨k₀,mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
        · have hpk0:(p:ℕ)∣Nat.lcm (dd k₀).1 (dd k₀).2:=by
            rcases mem_union.mp hk₀ with hm | hm
            · exact ((mem_filter.mp hm).2).trans (Nat.dvd_lcm_left _ _)
            · exact ((mem_filter.mp hm).2).trans (Nat.dvd_lcm_right _ _)
          have hpg:((p:ℕ):ℤ)∣((Nat.gcd (Nat.lcm (dd k₀).1 (dd k₀).2) v6:ℕ):ℤ) :=
            Int.ofNat_dvd.mpr (Nat.dvd_gcd hpk0 hpd)
          exact hpg.trans (hvalid.2.2 k₀)
        · rcases hcase with h | h | h <;> simp [h]
      · apply Finset.mem_insert_of_mem
        rw [Finset.mem_biUnion]
        refine ⟨k₀,Finset.mem_univ _,?_⟩
        rcases hcase with h | h | h <;> simp [h]
  refine Finset.mem_image.mpr ⟨f,hf_mem,?_⟩
  ext k
  · dsimp only [zi]
    have hprod_img:∏ p∈P.attach.filter (fun p=>k∈(f p).1),(p:ℕ) =
        ∏ q∈(P.attach.filter (fun p=>k∈(f p).1)).image Subtype.val,q:=by
      rw [Finset.prod_image]; intro a _ b _ h; exact Subtype.ext h
    rw [hprod_img,← Nat.prod_primeFactors_of_squarefree (hvalid.1 k).1]
    congr 1; ext q
    simp only [Finset.mem_image,mem_filter,Finset.mem_attach,true_and,Subtype.exists,
      Nat.mem_primeFactors,f,Finset.mem_univ]
    constructor
    · rintro ⟨r,hrP,hrd,rfl⟩
      exact ⟨hP_prime r hrP,hrd,(hvalid.1 k).1.ne_zero⟩
    · rintro ⟨hq,hqd,hd0⟩
      have hq_gt:z7 N< q:=(zk hd0 N).mp (hvalid.1 k).2.2.1 q hq hqd
      have hq_le:q≤ y:=(Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hqd).trans (hle k).1
      exact ⟨q,mem_filter.mpr ⟨mem_Ioc.mpr ⟨hq_gt,hq_le⟩,hq⟩,hqd,rfl⟩
  · dsimp only [zi]
    have hprod_img:∏ p∈P.attach.filter (fun p=>k∈(f p).2),(p:ℕ) =
        ∏ q∈(P.attach.filter (fun p=>k∈(f p).2)).image Subtype.val,q:=by
      rw [Finset.prod_image]; intro a _ b _ h; exact Subtype.ext h
    rw [hprod_img,← Nat.prod_primeFactors_of_squarefree (hvalid.1 k).2.1]
    congr 1; ext q
    simp only [Finset.mem_image,mem_filter,Finset.mem_attach,true_and,Subtype.exists,
      Nat.mem_primeFactors,f,Finset.mem_univ]
    constructor
    · rintro ⟨r,hrP,hrd,rfl⟩
      exact ⟨hP_prime r hrP,hrd,(hvalid.1 k).2.1.ne_zero⟩
    · rintro ⟨hq,hqd,hd0⟩
      have hq_gt:z7 N< q:=(zk hd0 N).mp (hvalid.1 k).2.2.2 q hq hqd
      have hq_le:q≤ y:=(Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hqd).trans (hle k).2
      exact ⟨q,mem_filter.mpr ⟨mem_Ioc.mpr ⟨hq_gt,hq_le⟩,hq⟩,hqd,rfl⟩
private lemma xT {A:ℝ} {N v7 v6 y:ℕ}
    (hKw:z0 N< z7 N)
    (hdstar_sf:Squarefree v6) (hdstar_cop:Nat.Coprime v6 (z4 N))
    (hdstar_le:v6≤ y) (ω : Fin (z0 N)→ℝ × ℝ) :
    ∑ dd∈Sy N v7 v6 y,y7 A N v7 v6 dd ω =
      ∏ p∈z2 (z7 N) y,Ep A N v7 v6 p ω:=by
  classical
  unfold Sy
  rw [Finset.sum_image (fun f₁ _ f₂ _ h=>xm h)]
  have hrew:∀ f∈Fintype.piFinset (fun p:z2 (z7 N) y=>zU N v7 v6 (p:ℕ)),
      y7 A N v7 v6 (zi (z2 (z7 N) y) f) ω =
        ∏ p:z2 (z7 N) y,zx A N v6 (p:ℕ) ω (f p):=by
    intro f hf
    exact (yF hKw hdstar_sf hdstar_cop hdstar_le f
      (Fintype.mem_piFinset.mp hf) ω).2
  rw [sum_congr rfl hrew,← Finset.prod_univ_sum]
  have hprod_p:∏ p:z2 (z7 N) y,∑ c∈zU N v7 v6 (p:ℕ),
      zx A N v6 (p:ℕ) ω c =
      ∏ p:z2 (z7 N) y,Ep A N v7 v6 (p:ℕ) ω:=by
    refine Finset.prod_congr rfl fun p _=>?_
    have hp_gt:z7 N< (p:ℕ):=(mem_Ioc.mp (mem_filter.mp p.2).1).1
    exact wo (by omega) ω
  rw [hprod_p]
  exact Finset.prod_coe_sort (z2 (z7 N) y) (fun p=>Ep A N v7 v6 p ω)
lemma zV {A:ℝ} (hA:1≤ A) {N v7 v6:ℕ}
    (hN_exp2:Real.exp 2≤ (N:ℝ)) (hKw:z0 N< z7 N)
    (hR_gt1:∀ k:Fin (z0 N),1< z9 A N k)
    (hdstar_sf:Squarefree v6) (hdstar_cop:Nat.Coprime v6 (z4 N)) :
    Summable (fun dd:Fin (z0 N)→ℕ × ℕ=>‖y7 A N v7 v6 dd 0‖) ∧
    ∀ ω : Fin (z0 N)→ℝ × ℝ,
      ‖zW A N v7 v6 ω‖ ≤
        ((4 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
          Real.exp (3*(z0 N:ℝ)*(2*Real.log (Real.log (N:ℝ))+45)):=by
  classical
  set M_bound:ℝ:=((4 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
    Real.exp (3*(z0 N:ℝ)*(2*Real.log (Real.log (N:ℝ))+45))
  have hN1:1≤ N:=by
    have : (1 : ℝ)< (N:ℝ):=by linarith [Real.add_one_le_exp (2 : ℝ)]
    exact_mod_cast this.le
  have hlogN_pos:0< Real.log (N:ℝ):=by
    have : 2≤ Real.log (N:ℝ):=by
      calc (2 : ℝ)=Real.log (Real.exp 2):=(Real.log_exp 2).symm
        _≤ Real.log (N:ℝ):=Real.log_le_log (Real.exp_pos 2) hN_exp2
    linarith
  have hR_le_N:∀ k:Fin (z0 N),Real.log (z9 A N k)≤ Real.log (N:ℝ):=by
    intro k
    rw [xV A hN1 k]
    have hden:(1 : ℝ)≤ 100*(A+1)*((k.1+1 : ℕ):ℝ)^50:=by
      have hk1:(1 : ℝ)≤ ((k.1+1 : ℕ):ℝ):=by exact_mod_cast Nat.succ_pos k.1
      have hpow:(1 : ℝ)≤ ((k.1+1 : ℕ):ℝ)^50:=one_le_pow₀ hk1
      nlinarith
    exact div_le_self hlogN_pos.le hden
  have hSy_norm_le:∀ y:ℕ,v6≤ y →
      ∑ dd∈Sy N v7 v6 y,‖y7 A N v7 v6 dd 0‖≤ M_bound:=by
    intro y hy
    let P:=z2 (z7 N) y
    have hP_prime:∀ p∈P,p.Prime:=fun p hp=>(mem_filter.mp hp).2
    have hP_gt:∀ p∈P,z7 N< p:=fun p hp=>(mem_Ioc.mp (mem_filter.mp hp).1).1
    unfold Sy
    rw [Finset.sum_image (fun f₁ _ f₂ _ h=>xm h)]
    have hrew:∀ f∈Fintype.piFinset (fun p:P=>zU N v7 v6 (p:ℕ)),
        ‖y7 A N v7 v6 (zi P f) 0‖ =
          ∏ p:P,‖zx A N v6 (p:ℕ) 0 (f p)‖:=by
      intro f hf
      rw [(yF hKw hdstar_sf hdstar_cop hy f (Fintype.mem_piFinset.mp hf) 0).2,
        norm_prod]
    rw [sum_congr rfl hrew,
      ← Finset.prod_univ_sum (t:=fun p:P=>zU N v7 v6 (p:ℕ))
        (f:=fun p c=>‖zx A N v6 (p:ℕ) 0 c‖)]
    have hlocal:∀ p:P,
        ∑ c∈zU N v7 v6 (p:ℕ),‖zx A N v6 (p:ℕ) 0 c‖ ≤
          if (p:ℕ)∣v6 then (4 : ℝ)/ (p:ℝ)
          else 1+3*(z0 N:ℝ)/ ((p:ℝ)^(1+1/ Real.log (N:ℝ))):=by
      intro p
      have hp_pr:(p:ℕ).Prime:=hP_prime p.1 p.2
      have hp_pos:(0 : ℝ)< (p:ℝ):=by exact_mod_cast hp_pr.pos
      have hp_ge1:(1 : ℝ)≤ (p:ℝ):=by exact_mod_cast hp_pr.one_le
      have hp_gtK:z0 N< (p:ℕ):=by have:=hP_gt p.1 p.2; omega
      let choicesFor:Fin (z0 N)→Finset (Finset (Fin (z0 N)) × Finset (Fin (z0 N))) :=
        fun k=>{({k},∅),(∅,{k}),({k},{k})}
      have hnot0:∀ S:Finset (Fin (z0 N)),(∅,∅) ∉ S.biUnion choicesFor:=by
        intro S hm; rcases Finset.mem_biUnion.mp hm with ⟨k,_,hk⟩
        simp only [choicesFor,mem_insert,Finset.mem_singleton,Prod.mk.injEq] at hk
        rcases hk with ⟨h,_⟩ | ⟨_,h⟩ | ⟨h,_⟩
        · exact Finset.singleton_ne_empty k h.symm
        · exact Finset.singleton_ne_empty k h.symm
        · exact Finset.singleton_ne_empty k h.symm
      have hdisj:Set.PairwiseDisjoint (Set.univ:Set (Fin (z0 N))) choicesFor:=by
        intro k₁ _ k₂ _ hne; show Disjoint (choicesFor k₁) (choicesFor k₂); rw [Finset.disjoint_left]; intro c hc1 hc2
        simp only [choicesFor,mem_insert,Finset.mem_singleton] at hc1 hc2
        rcases hc1 with rfl | rfl | rfl <;> rcases hc2 with h | h | h <;> simp at h
        · exact hne h
        · exact hne h
        · exact hne h
      have hpow_le:∀ k:Fin (z0 N),
          ‖(p:ℂ)^(-wk A N k 0)‖≤ (p:ℝ)^(-(1/ Real.log (N:ℝ))):=by
        intro k
        rw [yf hp_pr.one_le]
        apply Real.rpow_le_rpow_of_exponent_le hp_ge1
        rw [neg_le_neg_iff]
        exact one_div_le_one_div_of_le (Real.log_pos (hR_gt1 k)) (hR_le_N k)
      have hpow_le1:∀ k:Fin (z0 N),‖(p:ℂ)^(-wk A N k 0)‖≤ 1:=by
        intro k
        refine (hpow_le k).trans ?_
        exact Real.rpow_le_one_of_one_le_of_nonpos hp_ge1 (by
          have : 0≤ 1/ Real.log (N:ℝ):=by positivity
          linarith)
      unfold zU
      split_ifs with hpd
      · set S:=Finset.univ.filter (fun k:Fin (z0 N) =>
          ((p:ℕ):ℤ)∣((v7:ℤ) - ((k.1+1 : ℕ):ℤ)))
        rw [sum_insert (hnot0 S),Finset.sum_biUnion
          (fun a _ b _ h=>hdisj (Set.mem_univ a) (Set.mem_univ b) h)]
        have h0:‖zx A N v6 (p:ℕ) 0 (∅,∅)‖=(1 : ℝ)/ (p:ℝ):=by
          simp [zx,hpd,one_div]
        rw [h0]
        rcases S.eq_empty_or_nonempty with hSe | ⟨k₀,hk₀⟩
        · rw [hSe,sum_empty,add_zero]
          exact div_le_div_of_nonneg_right (by norm_num:(1 : ℝ)≤ 4) hp_pos.le
        · have hS_sing:S={k₀}:=by
            ext k; simp only [Finset.mem_singleton]
            exact ⟨fun hk=>yP hp_gtK (mem_filter.mp hk).2 (mem_filter.mp hk₀).2,
              fun h=>h ▸ hk₀⟩
          rw [hS_sing,Finset.sum_singleton]
          have hne1:(({k₀}:Finset (Fin (z0 N))),(∅ : Finset (Fin (z0 N)))) ∉
              ({(∅,{k₀}),({k₀},{k₀})}:Finset (Finset (Fin (z0 N)) × Finset (Fin (z0 N)))):=by simp
          have hne2:((∅ : Finset (Fin (z0 N))),({k₀}:Finset (Fin (z0 N))))≠({k₀},{k₀}):=by simp
          dsimp only [choicesFor]
          rw [sum_insert hne1,Finset.sum_pair hne2]
          simp only [zx,hpd,↓reduceIte,Finset.prod_singleton,Finset.prod_empty,
            mul_one,norm_mul,norm_inv,norm_neg,Complex.norm_natCast,Pi.zero_apply,
            Prod.fst_zero,Prod.snd_zero]
          have hk01:=hpow_le1 k₀
          have h1:(p:ℝ)⁻¹*‖(p:ℂ)^(-wk A N k₀ 0)‖≤ (p:ℝ)⁻¹ :=
            mul_le_of_le_one_right (inv_nonneg.mpr hp_pos.le) hk01
          have h2:(p:ℝ)⁻¹*‖(p:ℂ)^(-wk A N k₀ 0)‖*‖(p:ℂ)^(-wk A N k₀ 0)‖≤ (p:ℝ)⁻¹ :=
            mul_le_of_le_one_right (by positivity) hk01 |>.trans h1
          rw [one_div,div_eq_mul_inv]
          linarith
      · rw [sum_insert (hnot0 Finset.univ),Finset.sum_biUnion
          (fun a _ b _ h=>hdisj (Set.mem_univ a) (Set.mem_univ b) h)]
        have h0:‖zx A N v6 (p:ℕ) 0 (∅,∅)‖=1:=by
          simp [zx,hpd]
        rw [h0]
        have hterm_k:∀ k:Fin (z0 N),
            ∑ c∈choicesFor k,‖zx A N v6 (p:ℕ) 0 c‖ ≤
              3/ ((p:ℝ)^(1+1/ Real.log (N:ℝ))):=by
          intro k
          have hne1:(({k}:Finset (Fin (z0 N))),(∅ : Finset (Fin (z0 N)))) ∉
              ({(∅,{k}),({k},{k})}:Finset (Finset (Fin (z0 N)) × Finset (Fin (z0 N)))):=by simp
          have hne2:((∅ : Finset (Fin (z0 N))),({k}:Finset (Fin (z0 N))))≠({k},{k}):=by simp
          dsimp only [choicesFor]
          rw [sum_insert hne1,Finset.sum_pair hne2]
          simp only [zx,hpd,↓reduceIte,Finset.prod_singleton,Finset.prod_empty,
            mul_one,one_mul,Finset.union_empty,Finset.empty_union,Finset.union_idempotent,
            Finset.singleton_nonempty,norm_mul,norm_inv,norm_neg,Complex.norm_natCast,
            Pi.zero_apply,Prod.fst_zero,Prod.snd_zero]
          have hpk:=hpow_le k
          have hpk1:=hpow_le1 k
          have h1:‖(p:ℂ)^(-wk A N k 0)‖*(p:ℝ)⁻¹ ≤
              (p:ℝ)^(-(1/ Real.log (N:ℝ)))*(p:ℝ)⁻¹:=by gcongr
          have h2:‖(p:ℂ)^(-wk A N k 0)‖*‖(p:ℂ)^(-wk A N k 0)‖*(p:ℝ)⁻¹ ≤
              (p:ℝ)^(-(1/ Real.log (N:ℝ)))*(p:ℝ)⁻¹:=by
            have : ‖(p:ℂ)^(-wk A N k 0)‖*‖(p:ℂ)^(-wk A N k 0)‖≤ ‖(p:ℂ)^(-wk A N k 0)‖ :=
              mul_le_of_le_one_right (norm_nonneg _) hpk1
            calc _≤ ‖(p:ℂ)^(-wk A N k 0)‖*(p:ℝ)⁻¹:=by gcongr
              _≤ (p:ℝ)^(-(1/ Real.log (N:ℝ)))*(p:ℝ)⁻¹:=h1
          have hrhs:(p:ℝ)^(-(1/ Real.log (N:ℝ)))*(p:ℝ)⁻¹ =
              1/ (p:ℝ)^(1+1/ Real.log (N:ℝ)):=by
            rw [Real.rpow_add hp_pos,Real.rpow_one,Real.rpow_neg hp_pos.le]
            field_simp
          rw [hrhs] at h1 h2
          linarith [show (3 : ℝ)/ (p:ℝ)^(1+1/ Real.log (N:ℝ)) =
            3*((1 : ℝ)/ (p:ℝ)^(1+1/ Real.log (N:ℝ))) by ring]
        have hsum_k:∑ k:Fin (z0 N),∑ c∈choicesFor k,‖zx A N v6 (p:ℕ) 0 c‖ ≤
            3*(z0 N:ℝ)/ (p:ℝ)^(1+1/ Real.log (N:ℝ)):=by
          calc
            _≤ ∑ _k:Fin (z0 N),3/ (p:ℝ)^(1+1/ Real.log (N:ℝ)) :=
                sum_le_sum fun k _=>hterm_k k
            _=(z0 N:ℝ)*(3/ (p:ℝ)^(1+1/ Real.log (N:ℝ))):=by simp
            _=3*(z0 N:ℝ)/ (p:ℝ)^(1+1/ Real.log (N:ℝ)):=by ring
        linarith
    have hprod_le:∏ p:P,∑ c∈zU N v7 v6 (p:ℕ),‖zx A N v6 (p:ℕ) 0 c‖ ≤
        ∏ p∈P,(if p∣v6 then (4 : ℝ)/ (p:ℝ)
          else 1+3*(z0 N:ℝ)/ (p:ℝ)^(1+1/ Real.log (N:ℝ))):=by
      rw [← Finset.prod_coe_sort P]
      exact prod_le_prod (fun _ _=>sum_nonneg fun _ _=>norm_nonneg _) (fun p _=>hlocal p)
    refine hprod_le.trans ?_
    rw [Finset.prod_ite]
    have hdstar_filt:P.filter (fun p=>p∣v6)=v6.primeFactors:=by
      ext q
      simp only [P,z2,mem_filter,mem_Ioc,Nat.mem_primeFactors]
      constructor
      · rintro ⟨⟨⟨_,_⟩,hq⟩,hqd⟩; exact ⟨hq,hqd,hdstar_sf.ne_zero⟩
      · rintro ⟨hq,hqd,hd0⟩
        have hgt:=(zk hd0 N).mp hdstar_cop q hq hqd
        have hle:=(Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hqd).trans hy
        exact ⟨⟨⟨hgt,hle⟩,hq⟩,hqd⟩
    have hpart1:∏ p∈P.filter (fun p=>p∣v6),(4 : ℝ)/ (p:ℝ) =
        (4 : ℝ)^v6.primeFactors.card/ (v6:ℝ):=by
      rw [hdstar_filt,prod_div_distrib,prod_const,← Nat.cast_prod,
        Nat.prod_primeFactors_of_squarefree hdstar_sf]
    rw [hpart1]
    have hpart2:∏ p∈P.filter (fun p=>¬ p∣v6),
          (1+3*(z0 N:ℝ)/ (p:ℝ)^(1+1/ Real.log (N:ℝ))) ≤
        Real.exp (3*(z0 N:ℝ)*(2*Real.log (Real.log (N:ℝ))+45)):=by
      refine (zO _ fun _ _=>by positivity).trans ?_
      apply Real.exp_le_exp.mpr
      have hsum_le:∑ p∈P.filter (fun p=>¬ p∣v6),
            3*(z0 N:ℝ)/ (p:ℝ)^(1+1/ Real.log (N:ℝ)) ≤
          3*(z0 N:ℝ) *
            ∑' p:Nat.Primes,(1 : ℝ)/ ((p:ℕ):ℝ)^(1+1/ Real.log (N:ℝ)):=by
        have hrew:∀ p:ℕ,3*(z0 N:ℝ)/ (p:ℝ)^(1+1/ Real.log (N:ℝ)) =
            3*(z0 N:ℝ)*((1 : ℝ)/ (p:ℝ)^(1+1/ Real.log (N:ℝ))):=fun p=>by ring
        simp_rw [hrew,← mul_sum]
        gcongr
        let toP:∀ q∈P.filter (fun p=>¬ p∣v6),Nat.Primes :=
          fun q hq=>⟨q,hP_prime q (mem_filter.mp hq).1⟩
        let S':Finset Nat.Primes:=(P.filter (fun p=>¬ p∣v6)).attach.image
          fun q=>toP q.1 q.2
        have hS':∑ p∈P.filter (fun p=>¬ p∣v6),
              (1 : ℝ)/ (p:ℝ)^(1+1/ Real.log (N:ℝ)) =
            ∑ p∈S',(1 : ℝ)/ ((p:ℕ):ℝ)^(1+1/ Real.log (N:ℝ)):=by
          refine Finset.sum_bij (fun p hp=>toP p hp) ?_ ?_ ?_ ?_
          · intro p hp; exact Finset.mem_image.mpr ⟨⟨p,hp⟩,Finset.mem_attach _ _,rfl⟩
          · intro a ha b hb h; exact congrArg Subtype.val h
          · intro q hq
            rcases Finset.mem_image.mp hq with ⟨⟨p,hp⟩,_,rfl⟩
            exact ⟨p,hp,rfl⟩
          · intro _ _; rfl
        rw [hS']
        have hσ : 1< 1+1/ Real.log (N:ℝ):=by linarith [div_pos one_pos hlogN_pos]
        exact (xS hσ).sum_le_tsum S' (fun _ _=>by positivity)
      exact hsum_le.trans (mul_le_mul_of_nonneg_left (w1 hN_exp2) (by positivity))
    exact mul_le_mul_of_nonneg_left hpart2 (by positivity)
  have hsummable:Summable (fun dd:Fin (z0 N)→ℕ × ℕ=>‖y7 A N v7 v6 dd 0‖):=by
    refine summable_of_sum_le (c:=M_bound) (fun _=>norm_nonneg _) fun s=>?_
    let y:ℕ:=max v6 (s.sup fun dd=>Finset.univ.sup fun k:Fin (z0 N)=>max (dd k).1 (dd k).2)
    have hsplit:∑ dd∈s,‖y7 A N v7 v6 dd 0‖ =
        ∑ dd∈s.filter (fun dd=>zR N v7 v6 dd),‖y7 A N v7 v6 dd 0‖:=by
      rw [sum_filter]
      refine sum_congr rfl fun dd _=>?_
      by_cases hv:zR N v7 v6 dd
      · rw [if_pos hv]
      · rw [if_neg hv]; unfold y7; rw [if_neg hv,norm_zero]
    rw [hsplit]
    have hsub:s.filter (fun dd=>zR N v7 v6 dd)⊆Sy N v7 v6 y:=by
      intro dd hdd
      rcases mem_filter.mp hdd with ⟨hdds,hvalid⟩
      refine xt hvalid fun k=>?_
      have h1:max (dd k).1 (dd k).2≤ y:=by
        calc max (dd k).1 (dd k).2
            ≤ Finset.univ.sup (fun j:Fin (z0 N)=>max (dd j).1 (dd j).2) :=
              Finset.le_sup (f:=fun j:Fin (z0 N)=>max (dd j).1 (dd j).2) (Finset.mem_univ k)
          _≤ s.sup (fun d=>Finset.univ.sup fun j:Fin (z0 N)=>max (d j).1 (d j).2) :=
              Finset.le_sup (f:=fun d:Fin (z0 N)→ℕ × ℕ =>
                Finset.univ.sup fun j:Fin (z0 N)=>max (d j).1 (d j).2) hdds
          _≤ y:=le_max_right _ _
      exact ⟨(le_max_left _ _).trans h1,(le_max_right _ _).trans h1⟩
    exact (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _=>norm_nonneg _).trans
      (hSy_norm_le y (le_max_left _ _))
  refine ⟨hsummable,fun ω=>?_⟩
  unfold zW
  have hsum_ω : Summable (fun dd=>‖y7 A N v7 v6 dd ω‖):=by
    simpa only [zZ] using hsummable
  calc
    ‖∑' dd,y7 A N v7 v6 dd ω‖
        ≤ ∑' dd,‖y7 A N v7 v6 dd ω‖:=norm_tsum_le_tsum_norm hsum_ω
    _=∑' dd,‖y7 A N v7 v6 dd 0‖:=by simp_rw [zZ]
    _≤ M_bound:=Real.tsum_le_of_sum_le (fun _=>norm_nonneg _) fun s=>by
        let y:ℕ:=max v6 (s.sup fun dd=>Finset.univ.sup fun k:Fin (z0 N)=>max (dd k).1 (dd k).2)
        have hsplit:∑ dd∈s,‖y7 A N v7 v6 dd 0‖ =
            ∑ dd∈s.filter (fun dd=>zR N v7 v6 dd),‖y7 A N v7 v6 dd 0‖:=by
          rw [sum_filter]
          refine sum_congr rfl fun dd _=>?_
          by_cases hv:zR N v7 v6 dd
          · rw [if_pos hv]
          · rw [if_neg hv]; unfold y7; rw [if_neg hv,norm_zero]
        rw [hsplit]
        have hsub:s.filter (fun dd=>zR N v7 v6 dd)⊆Sy N v7 v6 y:=by
          intro dd hdd
          rcases mem_filter.mp hdd with ⟨hdds,hvalid⟩
          refine xt hvalid fun k=>?_
          have h1:max (dd k).1 (dd k).2≤ y:=by
            calc max (dd k).1 (dd k).2
                ≤ Finset.univ.sup (fun j:Fin (z0 N)=>max (dd j).1 (dd j).2) :=
                  Finset.le_sup (f:=fun j:Fin (z0 N)=>max (dd j).1 (dd j).2) (Finset.mem_univ k)
              _≤ s.sup (fun d=>Finset.univ.sup fun j:Fin (z0 N)=>max (d j).1 (d j).2) :=
                  Finset.le_sup (f:=fun d:Fin (z0 N)→ℕ × ℕ =>
                    Finset.univ.sup fun j:Fin (z0 N)=>max (d j).1 (d j).2) hdds
              _≤ y:=le_max_right _ _
          exact ⟨(le_max_left _ _).trans h1,(le_max_right _ _).trans h1⟩
        exact (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _=>norm_nonneg _).trans
          (hSy_norm_le y (le_max_left _ _))
lemma wh {A:ℝ} (hA:1≤ A) {N v7 v6:ℕ}
    (hN_exp2:Real.exp 2≤ (N:ℝ)) (hKw:z0 N< z7 N)
    (hR_gt1:∀ k:Fin (z0 N),1< z9 A N k)
    (hdstar_sf:Squarefree v6) (hdstar_cop:Nat.Coprime v6 (z4 N))
    (ω : Fin (z0 N)→ℝ × ℝ) :
    Tendsto (fun y:ℕ=>∏ p∈z2 (z7 N) y,Ep A N v7 v6 p ω) atTop
      (𝓝 (zW A N v7 v6 ω)):=by
  classical
  have hsum_norm:Summable (fun dd=>‖y7 A N v7 v6 dd ω‖):=by
    simpa only [zZ] using
      (zV hA hN_exp2 hKw hR_gt1 hdstar_sf hdstar_cop).1
  have hhasSum:Tendsto (fun s:Finset (Fin (z0 N)→ℕ × ℕ) =>
      ∑ dd∈s,y7 A N v7 v6 dd ω) atTop (𝓝 (zW A N v7 v6 ω)) :=
    hsum_norm.of_norm.hasSum
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendsto_atTop] at hhasSum
  obtain ⟨s₀,hs₀⟩:=hhasSum ε hε
  let y₀ : ℕ:=max v6 (s₀.sup fun dd=>Finset.univ.sup fun k:Fin (z0 N)=>max (dd k).1 (dd k).2)
  refine ⟨y₀,fun y hy=>?_⟩
  rw [← xT hKw hdstar_sf hdstar_cop ((le_max_left _ _).trans hy)]
  have hsub:s₀.filter (fun dd=>zR N v7 v6 dd)⊆Sy N v7 v6 y:=by
    intro dd hdd
    rcases mem_filter.mp hdd with ⟨hdds,hvalid⟩
    refine xt hvalid fun k=>?_
    have h1:max (dd k).1 (dd k).2≤ y:=by
      calc max (dd k).1 (dd k).2
          ≤ Finset.univ.sup (fun j:Fin (z0 N)=>max (dd j).1 (dd j).2) :=
            Finset.le_sup (f:=fun j:Fin (z0 N)=>max (dd j).1 (dd j).2) (Finset.mem_univ k)
        _≤ s₀.sup (fun d=>Finset.univ.sup fun j:Fin (z0 N)=>max (d j).1 (d j).2) :=
            Finset.le_sup (f:=fun d:Fin (z0 N)→ℕ × ℕ =>
              Finset.univ.sup fun j:Fin (z0 N)=>max (d j).1 (d j).2) hdds
        _≤ y₀:=le_max_right _ _
        _≤ y:=hy
    exact ⟨(le_max_left _ _).trans h1,(le_max_right _ _).trans h1⟩
  have hsum_eq:∑ dd∈Sy N v7 v6 y,y7 A N v7 v6 dd ω =
      ∑ dd∈Sy N v7 v6 y ∪ s₀,y7 A N v7 v6 dd ω:=by
    refine Finset.sum_subset Finset.subset_union_left fun dd hdd hnot=>?_
    by_cases hv:zR N v7 v6 dd
    · exfalso
      rcases mem_union.mp hdd with h1 | h2
      · exact hnot h1
      · exact hnot (hsub (mem_filter.mpr ⟨h2,hv⟩))
    · unfold y7; rw [if_neg hv]
  rw [hsum_eq]
  exact hs₀ (Sy N v7 v6 y ∪ s₀) Finset.subset_union_right
lemma yT {A:ℝ} (hA:1≤ A) {N v7 v6:ℕ}
    (hN_exp2:Real.exp 2≤ (N:ℝ)) (hKw:z0 N< z7 N)
    (hKN:z0 N< N) (hkstarN:v7< N)
    (hR_gt1:∀ k:Fin (z0 N),1< z9 A N k)
    (hdstar_sf:Squarefree v6) (hdstar_cop:Nat.Coprime v6 (z4 N)) :
    ‖(xb A N v7 v6:ℂ) -
        (((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ)*∫ ω,zW A N v7 v6 ω ∂(PK (z0 N))‖ ≤
      ∏ k:Fin (z0 N),(z9 A N k)^2:=by
  classical
  let Dk:Fin (z0 N)→Finset ℕ:=fun k =>
    (Finset.Icc 1 ⌊z9 A N k⌋₊).filter (fun d=>Squarefree d∧Nat.Coprime d (z4 N))
  have hsieve_eq:∀ (k:Fin (z0 N)) (n:ℕ),n∈Finset.Ioc N (2*N) →
      xD A N k n =
        ∑ d∈Dk k,(if d∣n - (k.1+1) then
          ((ArithmeticFunction.moebius d:ℤ):ℝ) *
            zN (Real.log (d:ℝ)/ Real.log (z9 A N k)) else 0):=by
    intro k n hn
    have hnk_pos:0< n - (k.1+1):=by
      have:=(mem_Ioc.mp hn).1; have:=k.2; omega
    unfold xD
    rw [← sum_filter]
    refine Finset.sum_bij_ne_zero (fun d _ _=>d) ?_ ?_ ?_ ?_
    · intro d hd hne
      rcases mem_filter.mp hd with ⟨hd_div,hd_cop⟩
      have hd_dvd:d∣n - (k.1+1):=(Nat.mem_divisors.mp hd_div).1
      have hd_pos:1≤ d:=Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hnk_pos.ne' hd_dvd)
      have hsf:Squarefree d:=by
        rw [← ArithmeticFunction.moebius_ne_zero_iff_squarefree]
        intro hm0; apply hne; simp [hm0]
      have hd_le:d≤ ⌊z9 A N k⌋₊:=by
        have hlt:(d:ℝ)< z9 A N k:=by
          by_contra hge; push Not at hge
          apply hne
          have h1:1≤ Real.log (d:ℝ)/ Real.log (z9 A N k) :=
            (one_le_div (Real.log_pos (hR_gt1 k))).mpr
              (Real.log_le_log (by linarith [hR_gt1 k]) hge)
          rw [y3 h1,mul_zero]
        exact Nat.le_floor hlt.le
      exact mem_filter.mpr ⟨mem_filter.mpr
        ⟨mem_Icc.mpr ⟨hd_pos,hd_le⟩,hsf,hd_cop⟩,hd_dvd⟩
    · intro _ _ _ _ _ _ h; exact h
    · intro d hd hne
      rcases mem_filter.mp hd with ⟨hdDk,hd_dvd⟩
      rcases mem_filter.mp hdDk with ⟨_,_,hd_cop⟩
      exact ⟨d,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd_dvd,hnk_pos.ne'⟩,hd_cop⟩,hne,rfl⟩
    · intro _ _ _; rfl
  let Dbox:Finset (Fin (z0 N)→ℕ × ℕ):=Fintype.piFinset (fun k=>Dk k ×ˢ Dk k)
  let coeff:(Fin (z0 N)→ℕ × ℕ)→ℝ:=fun dd =>
    ∏ k:Fin (z0 N),
      (((ArithmeticFunction.moebius (dd k).1 : ℤ):ℝ) *
       ((ArithmeticFunction.moebius (dd k).2 : ℤ):ℝ) *
       zN (Real.log ((dd k).1 : ℝ)/ Real.log (z9 A N k)) *
       zN (Real.log ((dd k).2 : ℝ)/ Real.log (z9 A N k)))
  let cnt:(Fin (z0 N)→ℕ × ℕ)→ℕ:=fun dd =>
    ((Finset.Ioc N (2*N)).filter (fun n =>
      z4 N∣n∧v6∣n - v7 ∧
        ∀ k:Fin (z0 N),Nat.lcm (dd k).1 (dd k).2∣n - (k.1+1))).card
  have hPsum_expand:xb A N v7 v6=∑ dd∈Dbox,coeff dd*(cnt dd:ℝ):=by
    unfold xb zl
    have h_inner:∀ n∈Finset.Ioc N (2*N),
        ((if z4 N∣n then (1 : ℝ) else 0)*∏ k:Fin (z0 N),(xD A N k n)^2) *
          (if v6∣n - v7 then (1 : ℝ) else 0) =
        ∑ dd∈Dbox,coeff dd *
          (if z4 N∣n∧v6∣n - v7 ∧
              ∀ k:Fin (z0 N),Nat.lcm (dd k).1 (dd k).2∣n - (k.1+1) then 1 else 0):=by
      intro n hn
      have hsq:∀ k:Fin (z0 N),
          (xD A N k n)^2 =
            ∑ p∈Dk k ×ˢ Dk k,
              (((ArithmeticFunction.moebius p.1 : ℤ):ℝ) *
               ((ArithmeticFunction.moebius p.2 : ℤ):ℝ) *
               zN (Real.log (p.1 : ℝ)/ Real.log (z9 A N k)) *
               zN (Real.log (p.2 : ℝ)/ Real.log (z9 A N k))) *
              (if Nat.lcm p.1 p.2∣n - (k.1+1) then (1 : ℝ) else 0):=by
        intro k
        rw [hsieve_eq k n hn,sq,Finset.sum_mul_sum,← Finset.sum_product']
        refine sum_congr rfl fun p _=>?_
        by_cases h1:p.1∣n - (k.1+1) <;> by_cases h2:p.2∣n - (k.1+1)
        · have hlcm:Nat.lcm p.1 p.2∣n - (k.1+1):=Nat.lcm_dvd h1 h2
          simp only [h1,h2,hlcm,↓reduceIte]; ring
        · have hlcm:¬ Nat.lcm p.1 p.2∣n - (k.1+1):=fun h=>h2 ((Nat.dvd_lcm_right _ _).trans h)
          simp only [h1,h2,hlcm,↓reduceIte,mul_zero]
        · have hlcm:¬ Nat.lcm p.1 p.2∣n - (k.1+1):=fun h=>h1 ((Nat.dvd_lcm_left _ _).trans h)
          simp only [h1,h2,hlcm,↓reduceIte,mul_zero,zero_mul]
        · have hlcm:¬ Nat.lcm p.1 p.2∣n - (k.1+1):=fun h=>h1 ((Nat.dvd_lcm_left _ _).trans h)
          simp only [h1,h2,hlcm,↓reduceIte,mul_zero]
      rw [Finset.prod_congr rfl (fun k _=>hsq k),Finset.prod_univ_sum]
      change ((if z4 N∣n then (1 : ℝ) else 0)*∑ dd∈Dbox,_)*_=_
      rw [mul_sum,sum_mul]
      refine sum_congr rfl fun dd _=>?_
      rw [prod_mul_distrib]
      have hprod_ind:(∏ k:Fin (z0 N),
          if Nat.lcm (dd k).1 (dd k).2∣n - (k.1+1) then (1 : ℝ) else 0) =
          if ∀ k:Fin (z0 N),Nat.lcm (dd k).1 (dd k).2∣n - (k.1+1) then 1 else 0:=by
        by_cases hall:∀ k:Fin (z0 N),Nat.lcm (dd k).1 (dd k).2∣n - (k.1+1)
        · rw [if_pos hall]; exact Finset.prod_eq_one fun k _=>if_pos (hall k)
        · rw [if_neg hall]; push Not at hall
          rcases hall with ⟨k,hk⟩
          exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)
      rw [hprod_ind]
      dsimp only [coeff]
      by_cases h1:z4 N∣n <;> by_cases h2:v6∣n - v7 <;>
        by_cases h3:∀ k:Fin (z0 N),Nat.lcm (dd k).1 (dd k).2∣n - (k.1+1)
      · rw [if_pos h1,if_pos h2,if_pos h3,if_pos ⟨h1,h2,h3⟩]; ring
      · rw [if_pos h1,if_pos h2,if_neg h3,if_neg (fun h=>h3 h.2.2)]; ring
      · rw [if_pos h1,if_neg h2,if_pos h3,if_neg (fun h=>h2 h.2.1)]; ring
      · rw [if_pos h1,if_neg h2,if_neg h3,if_neg (fun h=>h2 h.2.1)]; ring
      · rw [if_neg h1,if_pos h2,if_pos h3,if_neg (fun h=>h1 h.1)]; ring
      · rw [if_neg h1,if_pos h2,if_neg h3,if_neg (fun h=>h1 h.1)]; ring
      · rw [if_neg h1,if_neg h2,if_pos h3,if_neg (fun h=>h1 h.1)]; ring
      · rw [if_neg h1,if_neg h2,if_neg h3,if_neg (fun h=>h1 h.1)]; ring
    rw [sum_congr rfl h_inner,sum_comm]
    refine sum_congr rfl fun dd _=>?_
    rw [← mul_sum]
    congr 1
    simp [cnt,Finset.sum_boole]
  let mainTerm:(Fin (z0 N)→ℕ × ℕ)→ℝ:=fun dd =>
    if xi N v7 v6 dd then
      coeff dd*((N:ℝ)/ ((z4 N:ℝ)*(v6:ℝ))) *
        ∏ k:Fin (z0 N),
          ((Nat.gcd (Nat.lcm (dd k).1 (dd k).2) v6:ℝ)/ (Nat.lcm (dd k).1 (dd k).2 : ℝ))
    else 0
  have hcrt_err:|xb A N v7 v6 - ∑ dd∈Dbox,mainTerm dd| ≤
      ∏ k:Fin (z0 N),(z9 A N k)^2:=by
    rw [hPsum_expand,← sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm_le:∀ dd∈Dbox,|coeff dd*(cnt dd:ℝ) - mainTerm dd|≤ 1:=by
      intro dd hdd
      have hdd_mem:∀ k,(dd k).1∈Dk k∧(dd k).2∈Dk k:=fun k =>
        Finset.mem_product.mp (Fintype.mem_piFinset.mp hdd k)
      have hdd_sf:∀ k,Squarefree (dd k).1∧Squarefree (dd k).2:=fun k =>
        ⟨(mem_filter.mp (hdd_mem k).1).2.1,(mem_filter.mp (hdd_mem k).2).2.1⟩
      have hdd_cop:∀ k,Nat.Coprime (dd k).1 (z4 N)∧Nat.Coprime (dd k).2 (z4 N):=fun k =>
        ⟨(mem_filter.mp (hdd_mem k).1).2.2,(mem_filter.mp (hdd_mem k).2).2.2⟩
      have hcoeff_le:|coeff dd|≤ 1:=by
        dsimp only [coeff]
        rw [Finset.abs_prod]
        refine Finset.prod_le_one (fun _ _=>abs_nonneg _) fun k _=>?_
        have h1pos:(1 : ℝ)≤ (dd k).1:=by
          exact_mod_cast (mem_Icc.mp (mem_filter.mp (hdd_mem k).1).1).1
        have h2pos:(1 : ℝ)≤ (dd k).2:=by
          exact_mod_cast (mem_Icc.mp (mem_filter.mp (hdd_mem k).2).1).1
        have hm1:|((ArithmeticFunction.moebius (dd k).1 : ℤ):ℝ)|≤ 1:=by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have hm2:|((ArithmeticFunction.moebius (dd k).2 : ℤ):ℝ)|≤ 1:=by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        have he1:|zN (Real.log ((dd k).1 : ℝ)/ Real.log (z9 A N k))|≤ 1 :=
          xy (div_nonneg (Real.log_nonneg h1pos) (Real.log_pos (hR_gt1 k)).le)
        have he2:|zN (Real.log ((dd k).2 : ℝ)/ Real.log (z9 A N k))|≤ 1 :=
          xy (div_nonneg (Real.log_nonneg h2pos) (Real.log_pos (hR_gt1 k)).le)
        rw [abs_mul,abs_mul,abs_mul]
        have h12:|((ArithmeticFunction.moebius (dd k).1 : ℤ):ℝ)| *
            |((ArithmeticFunction.moebius (dd k).2 : ℤ):ℝ)|≤ 1 :=
          mul_le_one₀ hm1 (abs_nonneg _) hm2
        have h123:|((ArithmeticFunction.moebius (dd k).1 : ℤ):ℝ)| *
            |((ArithmeticFunction.moebius (dd k).2 : ℤ):ℝ)| *
            |zN (Real.log ((dd k).1 : ℝ)/ Real.log (z9 A N k))|≤ 1 :=
          mul_le_one₀ h12 (abs_nonneg _) he1
        exact mul_le_one₀ h123 (abs_nonneg _) he2
      have hcrt:=wE hKw hKN hkstarN hdstar_sf hdstar_cop dd hdd_sf hdd_cop
      dsimp only [mainTerm]
      by_cases hcompat:xi N v7 v6 dd
      · rw [if_pos hcompat] at hcrt ⊢
        have hfact:coeff dd*(cnt dd:ℝ) -
            coeff dd*((N:ℝ)/ ((z4 N:ℝ)*(v6:ℝ))) *
              ∏ k:Fin (z0 N),
                ((Nat.gcd (Nat.lcm (dd k).1 (dd k).2) v6:ℝ)/ (Nat.lcm (dd k).1 (dd k).2 : ℝ)) =
            coeff dd*((cnt dd:ℝ) -
              ((N:ℝ)/ ((z4 N:ℝ)*(v6:ℝ))) *
                ∏ k:Fin (z0 N),
                  ((Nat.gcd (Nat.lcm (dd k).1 (dd k).2) v6:ℝ)/ (Nat.lcm (dd k).1 (dd k).2 : ℝ))):=by
          ring
        rw [hfact,abs_mul]
        exact mul_le_one₀ hcoeff_le (abs_nonneg _) hcrt
      · rw [if_neg hcompat] at hcrt ⊢
        have hcnt0:cnt dd=0:=hcrt
        simp [hcnt0]
    refine (sum_le_sum hterm_le).trans ?_
    rw [sum_const,nsmul_eq_mul,mul_one]
    dsimp only [Dbox]
    rw [Fintype.card_piFinset,Nat.cast_prod]
    refine prod_le_prod (fun _ _=>by positivity) fun k _=>?_
    rw [Finset.card_product,Nat.cast_mul,← sq]
    have hcard_le:((Dk k).card:ℝ)≤ z9 A N k:=by
      have h1:(Dk k).card≤ (Finset.Icc 1 ⌊z9 A N k⌋₊).card:=Finset.card_filter_le _ _
      rw [Nat.card_Icc,Nat.add_sub_cancel] at h1
      exact (Nat.cast_le.mpr h1).trans (Nat.floor_le (by linarith [hR_gt1 k]))
    nlinarith [Nat.cast_nonneg (α:=ℝ) (Dk k).card]
  have hmain_eq:((∑ dd∈Dbox,mainTerm dd:ℝ):ℂ) =
      (((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ)*∫ ω,zW A N v7 v6 ω ∂(PK (z0 N)):=by
    have hsum_norm:=(zV (v7:=v7) hA hN_exp2 hKw hR_gt1 hdstar_sf hdstar_cop).1
    have hint_each:∀ dd:Fin (z0 N)→ℕ × ℕ,
        Integrable (y7 A N v7 v6 dd) (PK (z0 N)):=by
      intro dd
      refine (integrable_const (‖y7 A N v7 v6 dd 0‖)).mono'
        (xh A N v7 v6 dd).aestronglyMeasurable ?_
      exact ae_of_all _ fun ω=>le_of_eq (zZ A N v7 v6 dd ω)
    have hint_norm_sum:Summable (fun dd=>∫ ω,‖y7 A N v7 v6 dd ω‖ ∂(PK (z0 N))):=by
      have hconst:∀ dd,∫ ω,‖y7 A N v7 v6 dd ω‖ ∂(PK (z0 N)) =
          ‖y7 A N v7 v6 dd 0‖:=fun dd=>by
        simp_rw [zZ]
        rw [integral_const]
        simp [measureReal_def]
      simp_rw [hconst]
      exact hsum_norm
    have hswap:∫ ω,zW A N v7 v6 ω ∂(PK (z0 N)) =
        ∑' dd,∫ ω,y7 A N v7 v6 dd ω ∂(PK (z0 N)) :=
      (MeasureTheory.integral_tsum_of_summable_integral_norm hint_each hint_norm_sum).symm
    have heval_int:∀ dd:Fin (z0 N)→ℕ × ℕ,
        ∫ ω,y7 A N v7 v6 dd ω ∂(PK (z0 N)) =
          if zR N v7 v6 dd then
            ((v6:ℂ)⁻¹)*(coeff dd:ℂ) *
              ∏ k:Fin (z0 N),
                (((Nat.gcd (Nat.lcm (dd k).1 (dd k).2) v6:ℕ):ℂ) /
                 ((Nat.lcm (dd k).1 (dd k).2 : ℕ):ℂ))
          else 0:=by
      intro dd
      unfold y7
      split_ifs with hv
      · rw [integral_const_mul]
        unfold PK
        rw [MeasureTheory.integral_fintype_prod_eq_prod (f:=fun (k:Fin (z0 N)) (x:ℝ × ℝ) =>
          ((ArithmeticFunction.moebius (dd k).1 : ℤ):ℂ) *
           ((ArithmeticFunction.moebius (dd k).2 : ℤ):ℂ) *
           ((dd k).1 : ℂ)^(-wk A N k x.1) *
           ((dd k).2 : ℂ)^(-wk A N k x.2) *
           (((Nat.gcd (Nat.lcm (dd k).1 (dd k).2) v6:ℕ):ℂ) /
            ((Nat.lcm (dd k).1 (dd k).2 : ℕ):ℂ)))]
        have hfactor_k:∀ k:Fin (z0 N),
            ∫ x:ℝ × ℝ,
              (((ArithmeticFunction.moebius (dd k).1 : ℤ):ℂ) *
               ((ArithmeticFunction.moebius (dd k).2 : ℤ):ℂ) *
               ((dd k).1 : ℂ)^(-wk A N k x.1) *
               ((dd k).2 : ℂ)^(-wk A N k x.2) *
               (((Nat.gcd (Nat.lcm (dd k).1 (dd k).2) v6:ℕ):ℂ) /
                ((Nat.lcm (dd k).1 (dd k).2 : ℕ):ℂ))) ∂zn =
              (((ArithmeticFunction.moebius (dd k).1 : ℤ):ℂ) *
               ((ArithmeticFunction.moebius (dd k).2 : ℤ):ℂ) *
               (zN (Real.log ((dd k).1 : ℝ)/ Real.log (z9 A N k)):ℂ) *
               (zN (Real.log ((dd k).2 : ℝ)/ Real.log (z9 A N k)):ℂ)) *
              (((Nat.gcd (Nat.lcm (dd k).1 (dd k).2) v6:ℕ):ℂ) /
               ((Nat.lcm (dd k).1 (dd k).2 : ℕ):ℂ)):=by
          intro k
          have h1pos:1≤ (dd k).1:=Nat.pos_of_ne_zero (hv.1 k).1.ne_zero
          have h2pos:1≤ (dd k).2:=Nat.pos_of_ne_zero (hv.1 k).2.1.ne_zero
          have hrew:(fun x:ℝ × ℝ =>
              (((ArithmeticFunction.moebius (dd k).1 : ℤ):ℂ) *
               ((ArithmeticFunction.moebius (dd k).2 : ℤ):ℂ) *
               ((dd k).1 : ℂ)^(-wk A N k x.1) *
               ((dd k).2 : ℂ)^(-wk A N k x.2) *
               (((Nat.gcd (Nat.lcm (dd k).1 (dd k).2) v6:ℕ):ℂ) /
                ((Nat.lcm (dd k).1 (dd k).2 : ℕ):ℂ)))) =
              fun x:ℝ × ℝ =>
                ((((ArithmeticFunction.moebius (dd k).1 : ℤ):ℂ) *
                  ((ArithmeticFunction.moebius (dd k).2 : ℤ):ℂ) *
                  (((Nat.gcd (Nat.lcm (dd k).1 (dd k).2) v6:ℕ):ℂ) /
                   ((Nat.lcm (dd k).1 (dd k).2 : ℕ):ℂ)))) *
                (((dd k).1 : ℂ)^(-wk A N k x.1)*((dd k).2 : ℂ)^(-wk A N k x.2)):=by
            ext x; ring
          rw [hrew,integral_const_mul]
          unfold zn
          rw [MeasureTheory.integral_prod_mul
              (f:=fun t:ℝ=>((dd k).1 : ℂ)^(-wk A N k t))
              (g:=fun t:ℝ=>((dd k).2 : ℂ)^(-wk A N k t))]
          simp only [wk]
          rw [← yz h1pos (hR_gt1 k),
            ← yz h2pos (hR_gt1 k)]
          ring
        rw [Finset.prod_congr rfl (fun k _=>hfactor_k k),prod_mul_distrib]
        dsimp only [coeff]
        push_cast
        ring
      · simp
    rw [hswap]
    simp_rw [heval_int]
    rw [tsum_eq_sum (s:=Dbox)]
    · rw [mul_sum,Complex.ofReal_sum]
      refine sum_congr rfl fun dd hdd=>?_
      have hdd_mem:∀ k,(dd k).1∈Dk k∧(dd k).2∈Dk k:=fun k =>
        Finset.mem_product.mp (Fintype.mem_piFinset.mp hdd k)
      have hdd_sf_cop:∀ k,Squarefree (dd k).1∧Squarefree (dd k).2 ∧
          Nat.Coprime (dd k).1 (z4 N)∧Nat.Coprime (dd k).2 (z4 N):=fun k =>
        ⟨(mem_filter.mp (hdd_mem k).1).2.1,(mem_filter.mp (hdd_mem k).2).2.1,
         (mem_filter.mp (hdd_mem k).1).2.2,(mem_filter.mp (hdd_mem k).2).2.2⟩
      dsimp only [mainTerm]
      by_cases hcompat:xi N v7 v6 dd
      · have hv:zR N v7 v6 dd:=⟨hdd_sf_cop,hcompat⟩
        rw [if_pos hcompat,if_pos hv]
        push_cast
        ring
      · have hnv:¬ zR N v7 v6 dd:=fun h=>hcompat h.2
        rw [if_neg hcompat,if_neg hnv]
        simp
    · intro dd hnot
      by_cases hv:zR N v7 v6 dd
      · rw [if_pos hv]
        have hex:∃ k:Fin (z0 N),¬ ((dd k).1∈Dk k∧(dd k).2∈Dk k):=by
          by_contra hall; push Not at hall
          apply hnot
          exact Fintype.mem_piFinset.mpr fun k=>Finset.mem_product.mpr (hall k)
        rcases hex with ⟨k,hk⟩
        have hzero_coeff:coeff dd=0:=by
          dsimp only [coeff]
          refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
          have h1pos:1≤ (dd k).1:=Nat.pos_of_ne_zero (hv.1 k).1.ne_zero
          have h2pos:1≤ (dd k).2:=Nat.pos_of_ne_zero (hv.1 k).2.1.ne_zero
          have hge:z9 A N k≤ ((dd k).1 : ℝ)∨z9 A N k≤ ((dd k).2 : ℝ):=by
            by_contra hlt; push Not at hlt
            apply hk
            exact ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨h1pos,Nat.le_floor hlt.1.le⟩,
              (hv.1 k).1,(hv.1 k).2.2.1⟩,
              mem_filter.mpr ⟨mem_Icc.mpr ⟨h2pos,Nat.le_floor hlt.2.le⟩,
              (hv.1 k).2.1,(hv.1 k).2.2.2⟩⟩
          rcases hge with h1 | h2
          · have h1':1≤ Real.log ((dd k).1 : ℝ)/ Real.log (z9 A N k) :=
              (one_le_div (Real.log_pos (hR_gt1 k))).mpr (Real.log_le_log (by linarith [hR_gt1 k]) h1)
            rw [y3 h1']; ring
          · have h2':1≤ Real.log ((dd k).2 : ℝ)/ Real.log (z9 A N k) :=
              (one_le_div (Real.log_pos (hR_gt1 k))).mpr (Real.log_le_log (by linarith [hR_gt1 k]) h2)
            rw [y3 h2']; ring
        rw [hzero_coeff]; simp
      · rw [if_neg hv]
  rw [← hmain_eq,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  exact hcrt_err
lemma yp {A:ℝ} (hA:1≤ A) {N v7 v6:ℕ}
    (hN_exp2:Real.exp 2≤ (N:ℝ)) (hKw:z0 N< z7 N)
    (hR_gt1:∀ k:Fin (z0 N),1< z9 A N k)
    (hdstar_sf:Squarefree v6) (hdstar_cop:Nat.Coprime v6 (z4 N)) :
    ‖(∫ ω,zW A N v7 v6 ω ∂(PK (z0 N))) -
        (∫ ω in y0 (z0 N) (z3 N),zW A N v7 v6 ω ∂(PK (z0 N)))‖ ≤
      ((4 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
        Real.exp (3*(z0 N:ℝ)*(2*Real.log (Real.log (N:ℝ))+45)) *
        (2*(z0 N:ℝ)*zA*Real.exp (-(1/ 10 : ℝ)*Real.sqrt (z3 N))):=by
  set M_bound:ℝ:=((4 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
    Real.exp (3*(z0 N:ℝ)*(2*Real.log (Real.log (N:ℝ))+45))
  have hF_bound:=(zV (v7:=v7) hA hN_exp2 hKw hR_gt1 hdstar_sf hdstar_cop).2
  have hF_meas:AEStronglyMeasurable (zW A N v7 v6) (PK (z0 N)):=by
    unfold zW
    exact AEStronglyMeasurable.tsum fun dd=>(xh A N v7 v6 dd).aestronglyMeasurable
  have hF_int:Integrable (zW A N v7 v6) (PK (z0 N)) :=
    (integrable_const M_bound).mono' hF_meas (ae_of_all _ hF_bound)
  have hsplit:(∫ ω,zW A N v7 v6 ω ∂(PK (z0 N))) -
      (∫ ω in y0 (z0 N) (z3 N),zW A N v7 v6 ω ∂(PK (z0 N))) =
      ∫ ω in (y0 (z0 N) (z3 N))ᶜ,zW A N v7 v6 ω ∂(PK (z0 N)):=by
    have hadd:=MeasureTheory.integral_add_compl (y8 (z0 N) (z3 N)) hF_int
    linear_combination -hadd
  rw [hsplit]
  have hT_nn:0≤ z3 N:=by
    unfold z3
    have hlogN:0≤ Real.log (N:ℝ):=by
      have : 2≤ Real.log (N:ℝ):=by
        calc (2 : ℝ)=Real.log (Real.exp 2):=(Real.log_exp 2).symm
          _≤ Real.log (N:ℝ):=Real.log_le_log (Real.exp_pos 2) hN_exp2
      linarith
    exact Real.rpow_nonneg hlogN _
  calc
    ‖∫ ω in (y0 (z0 N) (z3 N))ᶜ,zW A N v7 v6 ω ∂(PK (z0 N))‖
        ≤ ∫ ω in (y0 (z0 N) (z3 N))ᶜ,‖zW A N v7 v6 ω‖ ∂(PK (z0 N)) :=
          norm_integral_le_integral_norm _
    _≤ ∫ _ω in (y0 (z0 N) (z3 N))ᶜ,M_bound ∂(PK (z0 N)):=by
          refine setIntegral_mono_on hF_int.norm.integrableOn
            (integrableOn_const (measure_ne_top _ _)) (y8 _ _).compl fun ω _ =>
            hF_bound ω
    _=(PK (z0 N) (y0 (z0 N) (z3 N))ᶜ).toReal*M_bound:=by
          rw [setIntegral_const,smul_eq_mul,measureReal_def]
    _=M_bound*(PK (z0 N) (y0 (z0 N) (z3 N))ᶜ).toReal:=mul_comm _ _
    _≤ M_bound*(2*(z0 N:ℝ)*zA*Real.exp (-(1/ 10 : ℝ)*Real.sqrt (z3 N))):=by
          gcongr; exact wB (z0 N) hT_nn
end
end Erdos413Sieve
namespace Erdos413Sieve
open Finset Filter Topology Complex Real MeasureTheory
open Erdos413Bump Erdos413Mertens
open scoped BigOperators
noncomputable section
lemma yS {a:ℕ→ℂ} {b:ℕ→ℝ}
    (hb:∀ n,‖a n‖≤ b n) (hsum:Summable b) (w:ℕ) :
    ∃ L:ℂ,Tendsto (fun y:ℕ=>∏ n∈Finset.Ioc w y,(1+a n)) atTop (𝓝 L) ∧
      ‖L - 1‖≤ Real.exp (∑' n:{n:ℕ // w< n},b n) - 1:=by
  let P:ℕ→ℂ:=fun y=>∏ n∈Finset.Ioc w y,(1+a n)
  have hb_nn:∀ n,0≤ b n:=fun n=>(norm_nonneg (a n)).trans (hb n)
  have hP_bound:∀ y:ℕ,‖P y‖≤ Real.exp (∑' n:ℕ,b n):=by
    intro y
    dsimp only [P]
    rw [norm_prod]
    calc
      ∏ n∈Finset.Ioc w y,‖1+a n‖
          ≤ ∏ n∈Finset.Ioc w y,(1+b n):=by
            refine prod_le_prod (fun _ _=>norm_nonneg _) fun n _=>?_
            exact (norm_add_le _ _).trans (by rw [norm_one]; linarith [hb n])
      _≤ Real.exp (∑ n∈Finset.Ioc w y,b n):=zO _ fun n _=>hb_nn n
      _≤ Real.exp (∑' n:ℕ,b n):=Real.exp_le_exp.mpr (hsum.sum_le_tsum _ fun n _=>hb_nn n)
  have hCauchy:CauchySeq P:=by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    set M:=Real.exp (∑' n:ℕ,b n)
    have hM_pos:0< M:=Real.exp_pos _
    let δ : ℝ:=min 1 (ε/ (4*M))
    have hδ_pos : 0< δ:=by positivity
    have h_tail:∀ᶠ N₀ : ℕ in atTop,∀ y:ℕ,N₀≤ y→∑ n∈Finset.Ioc N₀ y,b n< δ:=by
      have h_tend:=hsum.hasSum.tendsto_sum_nat
      rw [Metric.tendsto_atTop] at h_tend
      obtain ⟨N₀,hN₀⟩:=h_tend (δ/ 2) (half_pos hδ_pos)
      refine Filter.eventually_atTop.mpr ⟨N₀,fun k hk y hy=>?_⟩
      have h1:|∑ i∈Finset.range (k+1),b i - ∑' i,b i|< δ/ 2 :=
        hN₀ (k+1) (by omega)
      have h2:|∑ i∈Finset.range (y+1),b i - ∑' i,b i|< δ/ 2 :=
        hN₀ (y+1) (by omega)
      have hIoc_eq:∑ n∈Finset.Ioc k y,b n =
          ∑ i∈Finset.range (y+1),b i - ∑ i∈Finset.range (k+1),b i:=by
        have hdisj:Disjoint (Finset.range (k+1)) (Finset.Ioc k y):=by
          rw [Finset.disjoint_left]; intro n h1 h2
          simp only [Finset.mem_range,mem_Ioc] at h1 h2; omega
        have hunion:Finset.range (k+1) ∪ Finset.Ioc k y=Finset.range (y+1):=by
          ext n; simp only [mem_union,Finset.mem_range,mem_Ioc]; omega
        rw [← hunion,Finset.sum_union hdisj]; ring
      rw [hIoc_eq]
      have hsub:|(∑ i∈Finset.range (y+1),b i) - ∑ i∈Finset.range (k+1),b i|< δ:=by
        have htri:=abs_sub_le (∑ i∈Finset.range (y+1),b i) (∑' i,b i) (∑ i∈Finset.range (k+1),b i)
        rw [abs_sub_comm (∑' i,b i)] at htri
        linarith
      exact (le_abs_self _).trans_lt hsub
    obtain ⟨N₁,hN₁⟩:=Filter.eventually_atTop.mp h_tail
    let N₂ : ℕ:=max w N₁
    refine ⟨N₂,fun y hy=>?_⟩
    rw [Complex.dist_eq]
    have hsplit:P y=P N₂*∏ n∈Finset.Ioc N₂ y,(1+a n):=by
      dsimp only [P]
      have hdisj:Disjoint (Finset.Ioc w N₂) (Finset.Ioc N₂ y):=by
        rw [Finset.disjoint_left]; intro n h1 h2
        simp only [mem_Ioc] at h1 h2; omega
      have hunion:Finset.Ioc w N₂ ∪ Finset.Ioc N₂ y=Finset.Ioc w y:=by
        ext n; simp only [mem_union,mem_Ioc]
        have : w≤ N₂:=le_max_left _ _
        omega
      rw [← hunion,Finset.prod_union hdisj]
    rw [hsplit,show P N₂*(∏ n∈Finset.Ioc N₂ y,(1+a n)) - P N₂ =
        P N₂*((∏ n∈Finset.Ioc N₂ y,(1+a n)) - 1) by ring,norm_mul]
    have hsum_small:∑ n∈Finset.Ioc N₂ y,b n< δ:=hN₁ N₂ (le_max_right _ _) y hy
    have hsum_le1:∑ n∈Finset.Ioc N₂ y,b n≤ 1:=hsum_small.le.trans (min_le_left _ _)
    have hsum_nn:0≤ ∑ n∈Finset.Ioc N₂ y,b n:=sum_nonneg fun n _=>hb_nn n
    have hpert:‖(∏ n∈Finset.Ioc N₂ y,(1+a n)) - 1‖≤ 2*δ:=by
      calc
        ‖(∏ n∈Finset.Ioc N₂ y,(1+a n)) - 1‖
            ≤ Real.exp (∑ n∈Finset.Ioc N₂ y,‖a n‖) - 1:=y1 _ _
        _≤ Real.exp (∑ n∈Finset.Ioc N₂ y,b n) - 1:=by
            gcongr; exact hb _
        _≤ 2*∑ n∈Finset.Ioc N₂ y,b n:=y2 hsum_nn hsum_le1
        _≤ 2*δ:=by linarith
    have hδ2 : 2*δ≤ ε/ (2*M):=by
      have : δ≤ ε/ (4*M):=min_le_right _ _
      linarith [show 2*(ε/ (4*M))=ε/ (2*M) by ring]
    calc
      ‖P N₂‖*‖(∏ n∈Finset.Ioc N₂ y,(1+a n)) - 1‖
          ≤ M*(2*δ):=mul_le_mul (hP_bound N₂) hpert (norm_nonneg _) hM_pos.le
      _≤ M*(ε/ (2*M)):=by gcongr
      _=ε/ 2:=by field_simp
      _< ε:=half_lt_self hε
  obtain ⟨L,hL⟩:=cauchySeq_tendsto_of_complete hCauchy
  refine ⟨L,hL,?_⟩
  have hsum_sub:Summable (fun n:{n:ℕ // w< n}=>b n.1) :=
    hsum.comp_injective (fun x y h=>Subtype.ext h)
  have h_le_y:∀ y:ℕ,‖P y - 1‖≤ Real.exp (∑' n:{n:ℕ // w< n},b n.1) - 1:=by
    intro y
    refine (y1 _ _).trans ?_
    apply sub_le_sub_right
    apply Real.exp_le_exp.mpr
    have h1:∑ n∈Finset.Ioc w y,‖a n‖≤ ∑ n∈Finset.Ioc w y,b n :=
      sum_le_sum fun n _=>hb n
    refine h1.trans ?_
    let S':Finset {n:ℕ // w< n}:=(Finset.Ioc w y).attach.map
      ⟨fun x=>⟨x.1,(mem_Ioc.mp x.2).1⟩,
        fun a b h=>by dsimp only at h; exact Subtype.ext (Subtype.mk.inj h)⟩
    have hS':∑ n∈Finset.Ioc w y,b n=∑ x∈S',b x.1:=by
      dsimp only [S']
      rw [Finset.sum_map]
      exact (Finset.sum_attach (Finset.Ioc w y) b).symm
    rw [hS']
    exact hsum_sub.sum_le_tsum S' fun x _=>hb_nn x.1
  have h_tend_norm:Tendsto (fun y=>‖P y - 1‖) atTop (𝓝 ‖L - 1‖) :=
    (hL.sub tendsto_const_nhds).norm
  exact le_of_tendsto h_tend_norm (Filter.Eventually.of_forall h_le_y)
private lemma x2 {w:ℕ} (hw:1≤ w) {S:Finset ℕ}
    (hS:∀ n∈S,w< n) :
    ∑ n∈S,(1 : ℝ)/ (n:ℝ)^2≤ 1/ (w:ℝ):=by
  have hsum_sub:Summable (fun n:{n:ℕ // w< n}=>(1 : ℝ)/ ((n:ℕ):ℝ)^2):=by
    have hnat:Summable (fun n:ℕ=>(1 : ℝ)/ (n:ℝ)^2):=by
      simp [one_div]
    exact hnat.comp_injective (fun a b h=>Subtype.ext h)
  let S':Finset {n:ℕ // w< n}:=S.attach.map
    ⟨fun q=>⟨q.1,hS q.1 q.2⟩,
      fun a b h=>by dsimp only at h; exact Subtype.ext (Subtype.mk.inj h)⟩
  have hS':∑ n∈S,(1 : ℝ)/ (n:ℝ)^2=∑ n∈S',(1 : ℝ)/ ((n:ℕ):ℝ)^2:=by
    dsimp only [S']
    rw [Finset.sum_map]
    exact (Finset.sum_attach S (fun n=>(1 : ℝ)/ (n:ℝ)^2)).symm
  rw [hS']
  exact (hsum_sub.sum_le_tsum S' fun _ _=>by positivity).trans (x4 hw)
def Gk (A:ℝ) (N:ℕ) (k:Fin (z0 N)) (x:ℝ × ℝ):ℂ :=
  limUnder atTop (fun y:ℕ=>∏ p∈z2 (z7 N) y,(1 - ukp A N k p x))
def kernel (x:ℝ × ℝ):ℂ :=
  ((1+Complex.I*(x.1 : ℂ))*(1+Complex.I*(x.2 : ℂ))) /
    (2+Complex.I*((x.1 : ℂ)+(x.2 : ℂ)))
lemma x7 (x:ℝ × ℝ) :
    ‖kernel x‖≤ (1+|x.1|)*(1+|x.2|)/ 2:=by
  unfold kernel
  rw [norm_div,norm_mul]
  have h1:‖(1 : ℂ)+Complex.I*(x.1 : ℂ)‖≤ 1+|x.1|:=by
    calc ‖(1 : ℂ)+Complex.I*(x.1 : ℂ)‖≤ ‖(1 : ℂ)‖+‖Complex.I*(x.1 : ℂ)‖:=norm_add_le _ _
      _=1+|x.1|:=by simp [Complex.norm_real]
  have h2:‖(1 : ℂ)+Complex.I*(x.2 : ℂ)‖≤ 1+|x.2|:=by
    calc ‖(1 : ℂ)+Complex.I*(x.2 : ℂ)‖≤ ‖(1 : ℂ)‖+‖Complex.I*(x.2 : ℂ)‖:=norm_add_le _ _
      _=1+|x.2|:=by simp [Complex.norm_real]
  have hden:2≤ ‖(2 : ℂ)+Complex.I*((x.1 : ℂ)+(x.2 : ℂ))‖:=by
    have hre:((2 : ℂ)+Complex.I*((x.1 : ℂ)+(x.2 : ℂ))).re=2:=by simp
    calc (2 : ℝ)=|((2 : ℂ)+Complex.I*((x.1 : ℂ)+(x.2 : ℂ))).re|:=by rw [hre]; norm_num
      _≤ ‖(2 : ℂ)+Complex.I*((x.1 : ℂ)+(x.2 : ℂ))‖:=Complex.abs_re_le_norm _
  calc
    ‖(1 : ℂ)+Complex.I*(x.1 : ℂ)‖*‖(1 : ℂ)+Complex.I*(x.2 : ℂ)‖ /
        ‖(2 : ℂ)+Complex.I*((x.1 : ℂ)+(x.2 : ℂ))‖
        ≤ (1+|x.1|)*(1+|x.2|)/ 2 :=
          div_le_div₀ (by positivity) (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) (by norm_num) hden
lemma ym:Continuous kernel:=by
  unfold kernel
  refine Continuous.div (by fun_prop) (by fun_prop) fun x=>?_
  intro h0
  have hre:((2 : ℂ)+Complex.I*((x.1 : ℂ)+(x.2 : ℂ))).re=2:=by simp
  rw [h0] at hre; simp at hre
lemma y6 {f:ℝ→ℝ} :
    Integrable f rho↔Integrable (fun t:ℝ=>zh t*f t) volume:=by
  unfold rho
  change Integrable f (volume.withDensity fun t=>((Real.toNNReal (zh t):NNReal):ENNReal))↔_
  rw [MeasureTheory.integrable_withDensity_iff_integrable_smul₀
    (zs.measurable.real_toNNReal).aemeasurable]
  refine ⟨fun h=>h.congr (ae_of_all _ fun t=>?_),fun h=>h.congr (ae_of_all _ fun t=>?_)⟩
  · change (Real.toNNReal (zh t):ℝ)*f t=zh t*f t
    rw [Real.coe_toNNReal _ (zw t)]
  · change zh t*f t=(Real.toNNReal (zh t):ℝ)*f t
    rw [Real.coe_toNNReal _ (zw t)]
lemma zQ:Integrable (fun t:ℝ=>1+|t|) rho:=by
  rw [y6]
  refine ((zd (by norm_num:(0 : ℝ)< 1/ 5) 1).const_mul za).mono'
    (zs.mul (continuous_const.add continuous_abs)).aestronglyMeasurable ?_
  refine ae_of_all _ fun t=>?_
  rw [Real.norm_of_nonneg (mul_nonneg (zw t) (by positivity)),pow_one]
  calc
    zh t*(1+|t|)≤ (za*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|))*(1+|t|) :=
      mul_le_mul_of_nonneg_right (zj t) (by positivity)
    _=za*((1+|t|)*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|)):=by ring
lemma zc:Integrable kernel zn:=by
  have hdom:Integrable (fun x:ℝ × ℝ=>(1+|x.1|)*(1+|x.2|)/ 2) zn :=
    (zQ.mul_prod zQ).div_const 2
  exact hdom.mono' ym.aestronglyMeasurable (ae_of_all _ x7)
lemma xq:∫ x:ℝ × ℝ,kernel x ∂zn=(c0:ℂ):=by
  unfold zn
  rw [MeasureTheory.integral_prod _ zc]
  simp_rw [xp]
  rw [← wg]
  congr 1; ext t
  rw [← integral_const_mul]
  congr 1; ext t'
  unfold kernel; ring
def z8:ℝ:=∫ x:ℝ × ℝ,‖kernel x‖ ∂zn
lemma x9:c0≤ z8:=by
  unfold z8
  have h:=norm_integral_le_integral_norm (μ:=zn) (f:=kernel)
  rw [xq,Complex.norm_real,Real.norm_of_nonneg zX.le] at h
  exact h
lemma y4:0< z8:=lt_of_lt_of_le zX x9
def zf:ℝ:=4*z8/ c0
lemma wP:4≤ zf:=by
  unfold zf
  rw [le_div_iff₀ zX]
  linarith [x9]
lemma zH:1≤ zf:=by linarith [wP]
def Nk (A:ℝ) (N:ℕ) (k:Fin (z0 N)):ℂ :=
  ∫ x in zz (z3 N),Gk A N k x ∂zn
lemma zp {A:ℝ} {N:ℕ} {k:Fin (z0 N)}
    (hw_pos:1≤ z7 N) (hR_gt1:1< z9 A N k) (x:ℝ × ℝ)
    (hz1:riemannZeta (1+wk A N k x.1)≠0)
    (hz2:riemannZeta (1+wk A N k x.2)≠0) :
    Tendsto (fun y:ℕ=>∏ p∈z2 (z7 N) y,(1 - ukp A N k p x)) atTop
      (𝓝 (Gk A N k x)) ∧
    ∃ C_gt:ℂ,‖C_gt - 1‖≤ Real.exp (16/ (z7 N:ℝ)) - 1 ∧
      Gk A N k x =
        (riemannZeta (1+wk A N k x.1+wk A N k x.2) /
          (riemannZeta (1+wk A N k x.1)*riemannZeta (1+wk A N k x.2))) *
        (∏ p∈z5 (z7 N),
          (1 - (p:ℂ)^(-(1+wk A N k x.1+wk A N k x.2))) /
            ((1 - (p:ℂ)^(-(1+wk A N k x.1)))*(1 - (p:ℂ)^(-(1+wk A N k x.2))))) *
        C_gt:=by
  set w₁:=wk A N k x.1
  set w₂:=wk A N k x.2
  have hw1_re:0< w₁.re:=by rw [w9]; exact div_pos one_pos (Real.log_pos hR_gt1)
  have hw2_re:0< w₂.re:=by rw [w9]; exact div_pos one_pos (Real.log_pos hR_gt1)
  have hw12_re:0< (w₁+w₂).re:=by rw [Complex.add_re]; linarith
  have h1w1_re:1< (1+w₁).re:=by simp [hw1_re]
  have h1w2_re:1< (1+w₂).re:=by simp [hw2_re]
  have h1w12_re:1< (1+w₁+w₂).re:=by simp; linarith
  let corr:ℕ→ℂ:=fun p =>
    if p.Prime then
      -(((p:ℂ)^(-(2+w₁+w₂))*(1 - (p:ℂ)^(-w₁))*(1 - (p:ℂ)^(-w₂))) /
        ((1 - (p:ℂ)^(-(1+w₁)))*(1 - (p:ℂ)^(-(1+w₂)))))
    else 0
  have hfactor_p:∀ (p:ℕ),p.Prime →
      (1 - (p:ℂ)^(-(1+w₁))≠0∧1 - (p:ℂ)^(-(1+w₂))≠0 ∧
        1 - (p:ℂ)^(-(1+w₁+w₂))≠0) ∧
      1 - ukp A N k p x =
        ((1 - (p:ℂ)^(-(1+w₁)))*(1 - (p:ℂ)^(-(1+w₂))) /
          (1 - (p:ℂ)^(-(1+w₁+w₂))))*(1+corr p) ∧
      ‖corr p‖≤ (16 : ℝ)/ (p:ℝ)^2:=by
    intro p hp
    have hp_pos:(0 : ℝ)< p:=by exact_mod_cast hp.pos
    have hp2:(2 : ℝ)≤ p:=by exact_mod_cast hp.two_le
    have hpC:(p:ℂ)≠0:=by exact_mod_cast hp.ne_zero
    have hnorm_w:∀ z:ℂ,0< z.re→‖(p:ℂ)^(-z)‖≤ 1:=fun z hz=>by
      rw [← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hp_pos,Complex.neg_re]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have hnorm_1w:∀ z:ℂ,0< z.re→‖(p:ℂ)^(-(1+z))‖≤ (p:ℝ)⁻¹:=fun z hz=>by
      rw [← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hp_pos,Complex.neg_re,
        Complex.add_re,Complex.one_re]
      calc (p:ℝ)^(-(1+z.re))≤ (p:ℝ)^(-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _=(p:ℝ)⁻¹:=Real.rpow_neg_one (p:ℝ)
    have hlb_1w:∀ z:ℂ,0< z.re→(1/ 2 : ℝ)≤ ‖1 - (p:ℂ)^(-(1+z))‖:=fun z hz=>by
      have htri:‖(1 : ℂ)‖≤ ‖1 - (p:ℂ)^(-(1+z))‖+‖(p:ℂ)^(-(1+z))‖:=by
        simpa [sub_add_cancel] using norm_add_le (1 - (p:ℂ)^(-(1+z))) ((p:ℂ)^(-(1+z)))
      rw [norm_one] at htri
      have hinv:(p:ℝ)⁻¹≤ 1/ 2:=by
        rw [one_div]; exact inv_anti₀ (by norm_num) hp2
      linarith [hnorm_1w z hz]
    have hne1:1 - (p:ℂ)^(-(1+w₁))≠0:=by
      intro h; have:=hlb_1w w₁ hw1_re; rw [h,norm_zero] at this; linarith
    have hne2:1 - (p:ℂ)^(-(1+w₂))≠0:=by
      intro h; have:=hlb_1w w₂ hw2_re; rw [h,norm_zero] at this; linarith
    have hne12:1 - (p:ℂ)^(-(1+w₁+w₂))≠0:=by
      intro h; rw [add_assoc (1 : ℂ) w₁ w₂] at h
      have:=hlb_1w (w₁+w₂) hw12_re; rw [h,norm_zero] at this; linarith
    refine ⟨⟨hne1,hne2,hne12⟩,?_,?_⟩
    ·
      set a:=(p:ℂ)^(-w₁)
      set b:=(p:ℂ)^(-w₂)
      set r:=(p:ℂ)⁻¹
      have hab:(p:ℂ)^(-(w₁+w₂))=a*b:=by
        dsimp [a,b]; rw [← Complex.cpow_add _ _ hpC]; congr 1; ring
      have hra:(p:ℂ)^(-(1+w₁))=r*a:=by
        dsimp [r,a]; rw [show -(1+w₁)=(-1 : ℂ)+(-w₁) by ring,Complex.cpow_add _ _ hpC,
          Complex.cpow_neg_one]
      have hrb:(p:ℂ)^(-(1+w₂))=r*b:=by
        dsimp [r,b]; rw [show -(1+w₂)=(-1 : ℂ)+(-w₂) by ring,Complex.cpow_add _ _ hpC,
          Complex.cpow_neg_one]
      have hrab:(p:ℂ)^(-(1+w₁+w₂))=r*a*b:=by
        dsimp [r,a,b]
        rw [show -(1+w₁+w₂)=((-1 : ℂ)+(-w₁))+(-w₂) by ring,
          Complex.cpow_add _ _ hpC,Complex.cpow_add _ _ hpC,Complex.cpow_neg_one]
      have hr2ab:(p:ℂ)^(-(2+w₁+w₂))=r^2*a*b:=by
        dsimp [r,a,b]
        rw [show -(2+w₁+w₂)=((-2 : ℂ)+(-w₁))+(-w₂) by ring,
          Complex.cpow_add _ _ hpC,Complex.cpow_add _ _ hpC]
        have hm2:(p:ℂ)^(-2 : ℂ)=((p:ℂ)⁻¹)^2:=by
          rw [show (-2 : ℂ)=(-(2 : ℕ):ℂ) by norm_num,Complex.cpow_neg,Complex.cpow_natCast,inv_pow]
        rw [hm2]
      have hukp:1 - ukp A N k p x=1 - r*a - r*b+r*a*b:=by
        unfold ukp
        change 1 - (a+b - (p:ℂ)^(-(w₁+w₂)))/ (p:ℂ)=_
        rw [hab,div_eq_mul_inv]; dsimp [r]; ring
      dsimp only [corr]
      rw [if_pos hp,hukp,hra,hrb,hrab,hr2ab]
      rw [hra] at hne1; rw [hrb] at hne2; rw [hrab] at hne12
      field_simp [hne1,hne2,hne12]
      ring
    ·
      dsimp only [corr]
      rw [if_pos hp,norm_neg,norm_div,norm_mul,norm_mul,norm_mul]
      have h1a:‖1 - (p:ℂ)^(-w₁)‖≤ 2:=by
        calc ‖1 - (p:ℂ)^(-w₁)‖≤ ‖(1 : ℂ)‖+‖(p:ℂ)^(-w₁)‖:=norm_sub_le _ _
          _≤ 1+1:=by rw [norm_one]; linarith [hnorm_w w₁ hw1_re]
          _=2:=by norm_num
      have h1b:‖1 - (p:ℂ)^(-w₂)‖≤ 2:=by
        calc ‖1 - (p:ℂ)^(-w₂)‖≤ ‖(1 : ℂ)‖+‖(p:ℂ)^(-w₂)‖:=norm_sub_le _ _
          _≤ 1+1:=by rw [norm_one]; linarith [hnorm_w w₂ hw2_re]
          _=2:=by norm_num
      have h2w:‖(p:ℂ)^(-(2+w₁+w₂))‖≤ (1 : ℝ)/ (p:ℝ)^2:=by
        rw [← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hp_pos,Complex.neg_re]
        have hre:(2+w₁+w₂).re=2+w₁.re+w₂.re:=by simp
        rw [hre]
        calc (p:ℝ)^(-(2+w₁.re+w₂.re))≤ (p:ℝ)^(-2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
          _=1/ (p:ℝ)^2:=by
              rw [show (-2 : ℝ)=-((2 : ℕ):ℝ) by norm_num,Real.rpow_neg hp_pos.le,
                Real.rpow_natCast,one_div]
      have hnum:‖(p:ℂ)^(-(2+w₁+w₂))‖*‖1 - (p:ℂ)^(-w₁)‖*‖1 - (p:ℂ)^(-w₂)‖ ≤
          4/ (p:ℝ)^2:=by
        calc _≤ (1/ (p:ℝ)^2)*2*2:=by gcongr
          _=4/ (p:ℝ)^2:=by ring
      have hden:(1/ 4 : ℝ)≤ ‖1 - (p:ℂ)^(-(1+w₁))‖*‖1 - (p:ℂ)^(-(1+w₂))‖:=by
        have:=hlb_1w w₁ hw1_re; have:=hlb_1w w₂ hw2_re; nlinarith
      calc
        _≤ (4/ (p:ℝ)^2)/ (1/ 4) :=
          div_le_div₀ (by positivity) hnum (by norm_num) hden
        _=16/ (p:ℝ)^2:=by ring
  have hsum_b:Summable (fun n:ℕ=>(16 : ℝ)/ (n:ℝ)^2):=by
    have hnat:Summable (fun n:ℕ=>(1 : ℝ)/ (n:ℝ)^2):=by
      simp [one_div]
    simpa [div_eq_mul_inv] using hnat.mul_left (16 : ℝ)
  have hcorr_le:∀ n:ℕ,‖corr n‖≤ (16 : ℝ)/ (n:ℝ)^2:=by
    intro n
    by_cases hn:n.Prime
    · exact (hfactor_p n hn).2.2
    · simp [corr,hn]; positivity
  obtain ⟨C_gt,hC_tend,hC_bound⟩:=yS hcorr_le hsum_b (z7 N)
  have hC_bound':‖C_gt - 1‖≤ Real.exp (16/ (z7 N:ℝ)) - 1:=by
    refine hC_bound.trans ?_
    apply sub_le_sub_right
    apply Real.exp_le_exp.mpr
    have htail:=x4 hw_pos
    have hrew:(∑' n:{n:ℕ // z7 N< n},(16 : ℝ)/ ((n:ℕ):ℝ)^2) =
        16*∑' n:{n:ℕ // z7 N< n},(1 : ℝ)/ ((n:ℕ):ℝ)^2:=by
      rw [← tsum_mul_left]; congr 1; ext n; ring
    rw [hrew]
    linarith [mul_le_mul_of_nonneg_left htail (by norm_num:(0 : ℝ)≤ 16),
      show (16 : ℝ)*(1/ (z7 N:ℝ))=16/ (z7 N:ℝ) by ring]
  have h_finite_eq:∀ y:ℕ,z7 N≤ y →
      ∏ p∈z2 (z7 N) y,(1 - ukp A N k p x) =
        ((∏ p∈Nat.primesBelow (y+1),(1 - (p:ℂ)^(-(1+w₁+w₂)))⁻¹) /
          ((∏ p∈Nat.primesBelow (y+1),(1 - (p:ℂ)^(-(1+w₁)))⁻¹) *
           (∏ p∈Nat.primesBelow (y+1),(1 - (p:ℂ)^(-(1+w₂)))⁻¹))) *
        (∏ p∈z5 (z7 N),
          (1 - (p:ℂ)^(-(1+w₁+w₂))) /
            ((1 - (p:ℂ)^(-(1+w₁)))*(1 - (p:ℂ)^(-(1+w₂))))) *
        (∏ n∈Finset.Ioc (z7 N) y,(1+corr n)):=by
    intro y hy
    have hsplit_below:Nat.primesBelow (y+1)=z5 (z7 N) ∪ z2 (z7 N) y:=by
      ext p
      simp only [Nat.mem_primesBelow,z5,z2,mem_union,mem_filter,
        mem_Icc,mem_Ioc]
      constructor
      · rintro ⟨hlt,hp⟩
        by_cases hle:p≤ z7 N
        · exact Or.inl ⟨⟨hp.one_le,hle⟩,hp⟩
        · exact Or.inr ⟨⟨by omega,by omega⟩,hp⟩
      · rintro (⟨⟨_,h2⟩,hp⟩ | ⟨⟨_,h2⟩,hp⟩)
        · exact ⟨by omega,hp⟩
        · exact ⟨by omega,hp⟩
    have hdisj:Disjoint (z5 (z7 N)) (z2 (z7 N) y):=by
      rw [Finset.disjoint_left]; intro p h1 h2
      simp only [z5,z2,mem_filter,mem_Icc,mem_Ioc] at h1 h2
      omega
    have hcorr_prod:∏ n∈Finset.Ioc (z7 N) y,(1+corr n) =
        ∏ p∈z2 (z7 N) y,(1+corr p):=by
      unfold z2
      rw [Finset.prod_filter]
      refine Finset.prod_congr rfl fun n _=>?_
      by_cases hn:n.Prime
      · rw [if_pos hn]
      · rw [if_neg hn]; simp [corr,hn]
    rw [hcorr_prod]
    have h1:(∏ p∈Nat.primesBelow (y+1),(1 - (p:ℂ)^(-(1+w₁+w₂)))⁻¹) /
        ((∏ p∈Nat.primesBelow (y+1),(1 - (p:ℂ)^(-(1+w₁)))⁻¹) *
         (∏ p∈Nat.primesBelow (y+1),(1 - (p:ℂ)^(-(1+w₂)))⁻¹)) =
        ∏ p∈Nat.primesBelow (y+1),
          ((1 - (p:ℂ)^(-(1+w₁)))*(1 - (p:ℂ)^(-(1+w₂))) /
            (1 - (p:ℂ)^(-(1+w₁+w₂)))):=by
      rw [← prod_mul_distrib,← prod_div_distrib]
      refine Finset.prod_congr rfl fun p hp=>?_
      have hne:=(hfactor_p p (Nat.prime_of_mem_primesBelow hp)).1
      field_simp [hne.1,hne.2.1,hne.2.2]
    rw [h1,hsplit_below,Finset.prod_union hdisj]
    have hcancel:(∏ p∈z5 (z7 N),
          ((1 - (p:ℂ)^(-(1+w₁)))*(1 - (p:ℂ)^(-(1+w₂))) /
            (1 - (p:ℂ)^(-(1+w₁+w₂))))) *
        (∏ p∈z5 (z7 N),
          ((1 - (p:ℂ)^(-(1+w₁+w₂))) /
            ((1 - (p:ℂ)^(-(1+w₁)))*(1 - (p:ℂ)^(-(1+w₂))))))=1:=by
      rw [← prod_mul_distrib]
      refine Finset.prod_eq_one fun p hp=>?_
      have hne:=(hfactor_p p (mem_filter.mp hp).2).1
      field_simp [hne.1,hne.2.1,hne.2.2]
      exact div_self (mul_ne_zero (mul_ne_zero hne.1 hne.2.1) hne.2.2)
    calc
      ∏ p∈z2 (z7 N) y,(1 - ukp A N k p x)
          = ∏ p∈z2 (z7 N) y,
              (((1 - (p:ℂ)^(-(1+w₁)))*(1 - (p:ℂ)^(-(1+w₂))) /
                (1 - (p:ℂ)^(-(1+w₁+w₂))))*(1+corr p)) :=
            Finset.prod_congr rfl fun p hp=>(hfactor_p p (mem_filter.mp hp).2).2.1
      _=(∏ p∈z2 (z7 N) y,
            ((1 - (p:ℂ)^(-(1+w₁)))*(1 - (p:ℂ)^(-(1+w₂))) /
              (1 - (p:ℂ)^(-(1+w₁+w₂))))) *
          (∏ p∈z2 (z7 N) y,(1+corr p)):=prod_mul_distrib
      _=_:=by
          linear_combination -(∏ p∈z2 (z7 N) y,
              ((1 - (p:ℂ)^(-(1+w₁)))*(1 - (p:ℂ)^(-(1+w₂))) /
                (1 - (p:ℂ)^(-(1+w₁+w₂))))) *
            (∏ p∈z2 (z7 N) y,(1+corr p))*hcancel
  have hz_tend1:Tendsto (fun y:ℕ=>∏ p∈Nat.primesBelow (y+1),(1 - (p:ℂ)^(-(1+w₁)))⁻¹)
      atTop (𝓝 (riemannZeta (1+w₁))) :=
    (riemannZeta_eulerProduct h1w1_re).comp (tendsto_add_atTop_nat 1)
  have hz_tend2:Tendsto (fun y:ℕ=>∏ p∈Nat.primesBelow (y+1),(1 - (p:ℂ)^(-(1+w₂)))⁻¹)
      atTop (𝓝 (riemannZeta (1+w₂))) :=
    (riemannZeta_eulerProduct h1w2_re).comp (tendsto_add_atTop_nat 1)
  have hz_tend12:Tendsto (fun y:ℕ=>∏ p∈Nat.primesBelow (y+1),(1 - (p:ℂ)^(-(1+w₁+w₂)))⁻¹)
      atTop (𝓝 (riemannZeta (1+w₁+w₂))) :=
    (riemannZeta_eulerProduct h1w12_re).comp (tendsto_add_atTop_nat 1)
  have h_tend_rhs:Tendsto (fun y:ℕ =>
      ((∏ p∈Nat.primesBelow (y+1),(1 - (p:ℂ)^(-(1+w₁+w₂)))⁻¹) /
        ((∏ p∈Nat.primesBelow (y+1),(1 - (p:ℂ)^(-(1+w₁)))⁻¹) *
         (∏ p∈Nat.primesBelow (y+1),(1 - (p:ℂ)^(-(1+w₂)))⁻¹))) *
      (∏ p∈z5 (z7 N),
        (1 - (p:ℂ)^(-(1+w₁+w₂))) /
          ((1 - (p:ℂ)^(-(1+w₁)))*(1 - (p:ℂ)^(-(1+w₂))))) *
      (∏ n∈Finset.Ioc (z7 N) y,(1+corr n))) atTop
      (𝓝 ((riemannZeta (1+w₁+w₂)/ (riemannZeta (1+w₁)*riemannZeta (1+w₂))) *
        (∏ p∈z5 (z7 N),
          (1 - (p:ℂ)^(-(1+w₁+w₂))) /
            ((1 - (p:ℂ)^(-(1+w₁)))*(1 - (p:ℂ)^(-(1+w₂)))))*C_gt)) :=
    ((hz_tend12.div (hz_tend1.mul hz_tend2) (mul_ne_zero hz1 hz2)).mul tendsto_const_nhds).mul hC_tend
  have h_tend_lhs:Tendsto (fun y:ℕ=>∏ p∈z2 (z7 N) y,(1 - ukp A N k p x)) atTop
      (𝓝 ((riemannZeta (1+w₁+w₂)/ (riemannZeta (1+w₁)*riemannZeta (1+w₂))) *
        (∏ p∈z5 (z7 N),
          (1 - (p:ℂ)^(-(1+w₁+w₂))) /
            ((1 - (p:ℂ)^(-(1+w₁)))*(1 - (p:ℂ)^(-(1+w₂)))))*C_gt)):=by
    refine h_tend_rhs.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (z7 N)] with y hy
    exact (h_finite_eq y hy).symm
  have hGk_eq:Gk A N k x =
      (riemannZeta (1+w₁+w₂)/ (riemannZeta (1+w₁)*riemannZeta (1+w₂))) *
      (∏ p∈z5 (z7 N),
        (1 - (p:ℂ)^(-(1+w₁+w₂))) /
          ((1 - (p:ℂ)^(-(1+w₁)))*(1 - (p:ℂ)^(-(1+w₂)))))*C_gt :=
    h_tend_lhs.limUnder_eq
  rw [← hGk_eq] at h_tend_lhs
  exact ⟨h_tend_lhs,C_gt,hC_bound',hGk_eq⟩
lemma wb {A:ℝ} {N:ℕ} {k:Fin (z0 N)}
    (hw1:1≤ z7 N) (hR_gt1:1< z9 A N k) (x:ℝ × ℝ) :
    ‖(∏ p∈z5 (z7 N),
        (1 - (p:ℂ)^(-(1+wk A N k x.1+wk A N k x.2))) /
          ((1 - (p:ℂ)^(-(1+wk A N k x.1)))*(1 - (p:ℂ)^(-(1+wk A N k x.2))))) -
        (ze N:ℂ)‖ ≤
      ze N*(Real.exp (8*‖wk A N k x.1‖*‖wk A N k x.2‖ *
        Real.log (z7 N:ℝ)*(1+Real.log (z7 N:ℝ))) - 1):=by
  set w₁:=wk A N k x.1
  set w₂:=wk A N k x.2
  have hw1_re:0< w₁.re:=by rw [w9]; exact div_pos one_pos (Real.log_pos hR_gt1)
  have hw2_re:0< w₂.re:=by rw [w9]; exact div_pos one_pos (Real.log_pos hR_gt1)
  let errp:ℕ→ℂ:=fun p =>
    -(((p:ℂ)⁻¹*(1 - (p:ℂ)^(-w₁))*(1 - (p:ℂ)^(-w₂))) /
      ((1 - (p:ℂ)^(-(1+w₁)))*(1 - (p:ℂ)^(-(1+w₂)))))
  have hterm:∀ p∈z5 (z7 N),
      (1 - (p:ℂ)^(-(1+w₁+w₂))) /
        ((1 - (p:ℂ)^(-(1+w₁)))*(1 - (p:ℂ)^(-(1+w₂)))) =
        (((1 - (1 : ℝ)/ (p:ℝ))⁻¹ : ℝ):ℂ)*(1+errp p) ∧
      ‖errp p‖≤ 4*‖w₁‖*‖w₂‖*(Real.log (p:ℝ))^2/ (p:ℝ):=by
    intro p hp
    have hp_pr:p.Prime:=(mem_filter.mp hp).2
    have hp_pos:(0 : ℝ)< p:=by exact_mod_cast hp_pr.pos
    have hp2:(2 : ℝ)≤ p:=by exact_mod_cast hp_pr.two_le
    have hpC:(p:ℂ)≠0:=by exact_mod_cast hp_pr.ne_zero
    have h1r_ne:(1 - (p:ℂ)⁻¹)≠0:=by
      have hreal:(1 : ℝ) - 1/ (p:ℝ)≠0:=by
        have : (1 : ℝ)/ (p:ℝ)≤ 1/ 2:=one_div_le_one_div_of_le (by norm_num) hp2
        linarith
      have hcast1:(1 : ℂ) - (p:ℂ)⁻¹=(((1 : ℝ) - 1/ (p:ℝ)):ℂ):=by
        push_cast; rw [one_div]
      rw [hcast1]; exact_mod_cast hreal
    have hlb:∀ z:ℂ,0< z.re→(1/ 2 : ℝ)≤ ‖1 - (p:ℂ)^(-(1+z))‖:=fun z hz=>by
      have htri:‖(1 : ℂ)‖≤ ‖1 - (p:ℂ)^(-(1+z))‖+‖(p:ℂ)^(-(1+z))‖:=by
        simpa [sub_add_cancel] using norm_add_le (1 - (p:ℂ)^(-(1+z))) ((p:ℂ)^(-(1+z)))
      rw [norm_one] at htri
      have hn:‖(p:ℂ)^(-(1+z))‖≤ (p:ℝ)⁻¹:=by
        rw [← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hp_pos,Complex.neg_re,
          Complex.add_re,Complex.one_re]
        calc (p:ℝ)^(-(1+z.re))≤ (p:ℝ)^(-1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
          _=(p:ℝ)⁻¹:=Real.rpow_neg_one (p:ℝ)
      have hinv:(p:ℝ)⁻¹≤ 1/ 2:=by rw [one_div]; exact inv_anti₀ (by norm_num) hp2
      linarith
    have hne1:1 - (p:ℂ)^(-(1+w₁))≠0:=by
      intro h; have:=hlb w₁ hw1_re; rw [h,norm_zero] at this; linarith
    have hne2:1 - (p:ℂ)^(-(1+w₂))≠0:=by
      intro h; have:=hlb w₂ hw2_re; rw [h,norm_zero] at this; linarith
    constructor
    · set a:=(p:ℂ)^(-w₁)
      set b:=(p:ℂ)^(-w₂)
      set r:=(p:ℂ)⁻¹
      have hra:(p:ℂ)^(-(1+w₁))=r*a:=by
        dsimp [r,a]; rw [show -(1+w₁)=(-1 : ℂ)+(-w₁) by ring,Complex.cpow_add _ _ hpC,
          Complex.cpow_neg_one]
      have hrb:(p:ℂ)^(-(1+w₂))=r*b:=by
        dsimp [r,b]; rw [show -(1+w₂)=(-1 : ℂ)+(-w₂) by ring,Complex.cpow_add _ _ hpC,
          Complex.cpow_neg_one]
      have hrab:(p:ℂ)^(-(1+w₁+w₂))=r*a*b:=by
        dsimp [r,a,b]
        rw [show -(1+w₁+w₂)=((-1 : ℂ)+(-w₁))+(-w₂) by ring,
          Complex.cpow_add _ _ hpC,Complex.cpow_add _ _ hpC,Complex.cpow_neg_one]
      have hcast:(((1 - (1 : ℝ)/ (p:ℝ))⁻¹ : ℝ):ℂ)=(1 - r)⁻¹:=by
        dsimp [r]; push_cast; rw [one_div]
      have herr_eq:errp p=-(r*(1 - a)*(1 - b)/ ((1 - r*a)*(1 - r*b))):=by
        dsimp only [errp,r,a,b]; rw [hra,hrb]
      rw [hcast,herr_eq,hra,hrb,hrab]
      rw [hra] at hne1; rw [hrb] at hne2
      field_simp [h1r_ne,hne1,hne2]
      ring
    · dsimp only [errp]
      rw [norm_neg,norm_div,norm_mul,norm_mul,norm_mul,norm_inv,Complex.norm_natCast]
      have h1:=zI hp_pr.one_le hw1_re.le
      have h2:=zI hp_pr.one_le hw2_re.le
      have hden:(1/ 4 : ℝ)≤ ‖1 - (p:ℂ)^(-(1+w₁))‖*‖1 - (p:ℂ)^(-(1+w₂))‖:=by
        have:=hlb w₁ hw1_re; have:=hlb w₂ hw2_re; nlinarith
      have hnum:(p:ℝ)⁻¹*‖1 - (p:ℂ)^(-w₁)‖*‖1 - (p:ℂ)^(-w₂)‖ ≤
          ‖w₁‖*‖w₂‖*(Real.log (p:ℝ))^2/ (p:ℝ):=by
        calc
          (p:ℝ)⁻¹*‖1 - (p:ℂ)^(-w₁)‖*‖1 - (p:ℂ)^(-w₂)‖
              ≤ (p:ℝ)⁻¹*(‖w₁‖*Real.log (p:ℝ))*(‖w₂‖*Real.log (p:ℝ)):=by gcongr
          _=‖w₁‖*‖w₂‖*(Real.log (p:ℝ))^2/ (p:ℝ):=by ring
      calc
        _≤ (‖w₁‖*‖w₂‖*(Real.log (p:ℝ))^2/ (p:ℝ))/ (1/ 4) :=
          div_le_div₀ (by positivity) hnum (by norm_num) hden
        _=4*‖w₁‖*‖w₂‖*(Real.log (p:ℝ))^2/ (p:ℝ):=by ring
  rw [Finset.prod_congr rfl (fun p hp=>(hterm p hp).1),prod_mul_distrib]
  have hWr:(∏ p∈z5 (z7 N),(((1 - (1 : ℝ)/ (p:ℝ))⁻¹ : ℝ):ℂ))=(ze N:ℂ):=by
    unfold ze; push_cast; rfl
  rw [hWr,show (ze N:ℂ)*(∏ p∈z5 (z7 N),(1+errp p)) - (ze N:ℂ) =
      (ze N:ℂ)*((∏ p∈z5 (z7 N),(1+errp p)) - 1) by ring,
    norm_mul,Complex.norm_real,Real.norm_of_nonneg (by linarith [zr N])]
  refine mul_le_mul_of_nonneg_left ?_ (by linarith [zr N])
  refine (y1 _ _).trans ?_
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  have hsum_le:∑ p∈z5 (z7 N),‖errp p‖ ≤
      4*‖w₁‖*‖w₂‖*Real.log (z7 N:ℝ) *
        ∑ p∈z5 (z7 N),Real.log (p:ℝ)/ (p:ℝ):=by
    have hstep:∀ p∈z5 (z7 N),
        ‖errp p‖≤ (4*‖w₁‖*‖w₂‖*Real.log (z7 N:ℝ))*(Real.log (p:ℝ)/ (p:ℝ)):=by
      intro p hp
      have hp_le:(p:ℝ)≤ (z7 N:ℝ):=by
        exact_mod_cast (mem_Icc.mp (mem_filter.mp hp).1).2
      have hp_pos:(0 : ℝ)< p:=by exact_mod_cast (mem_filter.mp hp).2.pos
      have hlogp_nn:0≤ Real.log (p:ℝ):=Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le)
      have hlogp_le:Real.log (p:ℝ)≤ Real.log (z7 N:ℝ):=Real.log_le_log hp_pos hp_le
      refine (hterm p hp).2.trans ?_
      have hsq:(Real.log (p:ℝ))^2≤ Real.log (z7 N:ℝ)*Real.log (p:ℝ):=by
        rw [sq]; exact mul_le_mul_of_nonneg_right hlogp_le hlogp_nn
      calc
        4*‖w₁‖*‖w₂‖*(Real.log (p:ℝ))^2/ (p:ℝ)
            ≤ 4*‖w₁‖*‖w₂‖*(Real.log (z7 N:ℝ)*Real.log (p:ℝ))/ (p:ℝ):=by gcongr
        _=(4*‖w₁‖*‖w₂‖*Real.log (z7 N:ℝ))*(Real.log (p:ℝ)/ (p:ℝ)):=by ring
    exact (sum_le_sum hstep).trans (by rw [← mul_sum])
  refine hsum_le.trans ?_
  have hm1:=y9 (z7 N) hw1
  have hlogw_nn:0≤ Real.log (z7 N:ℝ):=Real.log_nonneg (by exact_mod_cast hw1)
  have hm1':∑ p∈z5 (z7 N),Real.log (p:ℝ)/ (p:ℝ) ≤
      2*(1+Real.log (z7 N:ℝ)) :=
    hm1.trans (mul_le_mul_of_nonneg_right yx (by linarith))
  calc
    4*‖w₁‖*‖w₂‖*Real.log (z7 N:ℝ)*∑ p∈z5 (z7 N),Real.log (p:ℝ)/ (p:ℝ)
        ≤ 4*‖w₁‖*‖w₂‖*Real.log (z7 N:ℝ)*(2*(1+Real.log (z7 N:ℝ))):=by gcongr
    _=8*‖w₁‖*‖w₂‖*Real.log (z7 N:ℝ)*(1+Real.log (z7 N:ℝ)):=by ring
end
end Erdos413Sieve
namespace Erdos413Sieve
open Finset Filter Topology Complex Real MeasureTheory
open Erdos413Bump Erdos413Mertens
open scoped BigOperators
noncomputable section
private lemma yv:∀ m:ℕ,1≤ m→2^(m - 1)≤ m.factorial
  | 0,h=>by omega
  | 1,_=>by norm_num
  | m+2,_=>by
    have ih:=yv (m+1) (by omega)
    simp only [Nat.add_sub_cancel] at ih
    change 2^(m+1)≤ (m+2).factorial
    rw [pow_succ,Nat.factorial_succ]
    have h1:2≤ m+2:=by omega
    calc
      2^m*2=2*2^m:=mul_comm _ _
      _≤ (m+2)*(m+1).factorial:=Nat.mul_le_mul h1 ih
lemma x5 (K:ℕ) {x:ℝ} (hx0:0≤ x) (hKx:(K:ℝ)*x≤ 1) :
    ∑ S∈(Finset.univ:Finset (Fin K)).powerset.filter (fun S=>2≤ S.card),
      ((S.card:ℝ) - 1)*x^S.card≤ 2*((K:ℝ)*x)^2:=by
  have hgroup :
      ∑ S∈(Finset.univ:Finset (Fin K)).powerset.filter (fun S=>2≤ S.card),
        ((S.card:ℝ) - 1)*x^S.card =
      ∑ r∈Finset.Icc 2 K,((r:ℝ) - 1)*(Nat.choose K r:ℝ)*x^r:=by
    have hcard_eq:∀ r∈Finset.Icc 2 K,
        ∑ S∈((Finset.univ:Finset (Fin K)).powersetCard r),((S.card:ℝ) - 1)*x^S.card =
          ((r:ℝ) - 1)*(Nat.choose K r:ℝ)*x^r:=by
      intro r _
      have hconst:∀ S∈(Finset.univ:Finset (Fin K)).powersetCard r,
          ((S.card:ℝ) - 1)*x^S.card=((r:ℝ) - 1)*x^r:=fun S hS=>by
        rw [(mem_powersetCard.mp hS).2]
      rw [sum_congr rfl hconst,sum_const,Finset.card_powersetCard,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring
    rw [← sum_congr rfl hcard_eq]
    rw [← Finset.sum_biUnion]
    · congr 1
      ext S
      simp only [mem_filter,Finset.mem_powerset,Finset.mem_biUnion,mem_Icc,
        mem_powersetCard]
      constructor
      · rintro ⟨hS,h2⟩
        exact ⟨S.card,⟨h2,by simpa using Finset.card_le_univ S⟩,hS,rfl⟩
      · rintro ⟨r,⟨h2,_⟩,hS,rfl⟩
        exact ⟨hS,h2⟩
    · intro r₁ _ r₂ _ hne
      show Disjoint ((Finset.univ:Finset (Fin K)).powersetCard r₁)
        ((Finset.univ:Finset (Fin K)).powersetCard r₂)
      rw [Finset.disjoint_left]
      intro S h1 h2
      have c1:=(mem_powersetCard.mp h1).2
      have c2:=(mem_powersetCard.mp h2).2
      exact hne (c1.symm.trans c2)
  rw [hgroup]
  have hterm:∀ r∈Finset.Icc 2 K,
      ((r:ℝ) - 1)*(Nat.choose K r:ℝ)*x^r≤ ((K:ℝ)*x)^2*(1/ 2 : ℝ)^(r - 2):=by
    intro r hr
    have hr2:2≤ r:=(mem_Icc.mp hr).1
    have hchoose:(Nat.choose K r:ℝ)*(r.factorial:ℝ)≤ (K:ℝ)^r:=by
      have hnat:Nat.choose K r*r.factorial≤ K^r:=by
        rw [mul_comm,← Nat.descFactorial_eq_factorial_mul_choose]
        exact Nat.descFactorial_le_pow K r
      exact_mod_cast hnat
    have hfac_lb:((r:ℝ) - 1)*(2 : ℝ)^(r - 2)≤ (r.factorial:ℝ):=by
      have h1:r - 1≤ r:=Nat.sub_le r 1
      have h2:2^(r - 2)≤ (r - 1).factorial:=by
        have:=yv (r - 1) (by omega)
        simpa [Nat.sub_sub] using this
      have h3:(r - 1)*2^(r - 2)≤ r.factorial:=by
        have hr_fac:r*(r - 1).factorial=r.factorial:=Nat.mul_factorial_pred (by omega)
        calc
          (r - 1)*2^(r - 2)≤ r*(r - 1).factorial:=Nat.mul_le_mul h1 h2
          _=r.factorial:=hr_fac
      have hcast:(((r - 1 : ℕ):ℝ))=(r:ℝ) - 1:=by
        simpa using Nat.cast_sub (R:=ℝ) (show 1≤ r by omega)
      rw [← hcast]
      exact_mod_cast h3
    have hfac_pos:(0 : ℝ)< (r.factorial:ℝ):=by exact_mod_cast Nat.factorial_pos r
    have hcoeff:((r:ℝ) - 1)*(Nat.choose K r:ℝ)≤ (K:ℝ)^r/ (2 : ℝ)^(r - 2):=by
      rw [le_div_iff₀ (by positivity)]
      have hmul:((r:ℝ) - 1)*(2 : ℝ)^(r - 2)*(Nat.choose K r:ℝ) ≤
          (r.factorial:ℝ)*(Nat.choose K r:ℝ) :=
        mul_le_mul_of_nonneg_right hfac_lb (Nat.cast_nonneg _)
      linarith
    have hKx_r:((K:ℝ)*x)^r≤ ((K:ℝ)*x)^2:=by
      have hr_eq:r=2+(r - 2):=by omega
      conv_lhs=>rw [hr_eq,pow_add]
      have h1:((K:ℝ)*x)^(r - 2)≤ 1:=pow_le_one₀ (by positivity) hKx
      nlinarith [sq_nonneg ((K:ℝ)*x)]
    calc
      ((r:ℝ) - 1)*(Nat.choose K r:ℝ)*x^r
          ≤ ((K:ℝ)^r/ (2 : ℝ)^(r - 2))*x^r :=
            mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hx0 r)
      _=((K:ℝ)*x)^r*(1/ 2 : ℝ)^(r - 2):=by
            rw [mul_pow,one_div,inv_pow,div_eq_mul_inv]; ring
      _≤ ((K:ℝ)*x)^2*(1/ 2 : ℝ)^(r - 2) :=
            mul_le_mul_of_nonneg_right hKx_r (by positivity)
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  have hgeom:∑ r∈Finset.Icc 2 K,(1/ 2 : ℝ)^(r - 2)≤ 2:=by
    by_cases hK2:K< 2
    · have hemp:Finset.Icc 2 K=∅:=Finset.Icc_eq_empty (by omega)
      rw [hemp,sum_empty]; norm_num
    · have hbij:∑ r∈Finset.Icc 2 K,(1/ 2 : ℝ)^(r - 2) =
          ∑ m∈Finset.range (K - 1),(1/ 2 : ℝ)^m:=by
        refine Finset.sum_bij (fun r _=>r - 2) ?_ ?_ ?_ ?_
        · intro r hr; simp only [mem_Icc,Finset.mem_range] at hr ⊢; omega
        · intro r₁ hr₁ r₂ hr₂ h; simp only [mem_Icc] at hr₁ hr₂; omega
        · intro m hm; simp only [Finset.mem_range] at hm
          exact ⟨m+2,mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩
        · intro _ _; rfl
      rw [hbij,geom_sum_eq (by norm_num:(1/ 2 : ℝ)≠1)]
      have hnn:0≤ (1/ 2 : ℝ)^(K - 1):=by positivity
      have heq:((1/ 2 : ℝ)^(K - 1) - 1)/ (1/ 2 - 1)=2*(1 - (1/ 2 : ℝ)^(K - 1)):=by ring
      linarith
  calc
    ((K:ℝ)*x)^2*∑ r∈Finset.Icc 2 K,(1/ 2 : ℝ)^(r - 2)
        ≤ ((K:ℝ)*x)^2*2:=mul_le_mul_of_nonneg_left hgeom (sq_nonneg _)
    _=2*((K:ℝ)*x)^2:=mul_comm _ _
private lemma we {a a₀ b b₀ c:ℂ} {ε : ℝ}
    (hε0 : 0≤ ε) (hε1 : ε≤ 1/ 10)
    (ha:‖a - a₀‖≤ ε*‖a₀‖) (hb:‖b - b₀‖≤ ε*‖b₀‖) (hc:‖c - 1‖≤ ε) :
    ‖a*b*c - a₀*b₀‖≤ 4*ε*(‖a₀‖*‖b₀‖):=by
  have hnb:‖b‖≤ (1+ε)*‖b₀‖:=by
    have htri:‖b‖≤ ‖b₀‖+‖b - b₀‖:=by
      simpa [add_sub_cancel] using norm_add_le b₀ (b - b₀)
    linarith
  have hnc:‖c‖≤ 1+ε:=by
    have htri:‖c‖≤ ‖(1 : ℂ)‖+‖c - 1‖:=by
      simpa [add_sub_cancel] using norm_add_le (1 : ℂ) (c - 1)
    rw [norm_one] at htri; linarith
  have hdecomp:a*b*c - a₀*b₀ =
      (a - a₀)*b*c+a₀*(b - b₀)*c+a₀*b₀*(c - 1):=by ring
  rw [hdecomp]
  have h1:‖(a - a₀)*b*c‖≤ ε*(1+ε)^2*(‖a₀‖*‖b₀‖):=by
    rw [norm_mul,norm_mul]
    calc
      ‖a - a₀‖*‖b‖*‖c‖≤ (ε*‖a₀‖)*((1+ε)*‖b₀‖)*(1+ε):=by gcongr
      _=ε*(1+ε)^2*(‖a₀‖*‖b₀‖):=by ring
  have h2:‖a₀*(b - b₀)*c‖≤ ε*(1+ε)*(‖a₀‖*‖b₀‖):=by
    rw [norm_mul,norm_mul]
    calc
      ‖a₀‖*‖b - b₀‖*‖c‖≤ ‖a₀‖*(ε*‖b₀‖)*(1+ε):=by gcongr
      _=ε*(1+ε)*(‖a₀‖*‖b₀‖):=by ring
  have h3:‖a₀*b₀*(c - 1)‖≤ ε*(‖a₀‖*‖b₀‖):=by
    rw [norm_mul,norm_mul]
    calc
      ‖a₀‖*‖b₀‖*‖c - 1‖≤ ‖a₀‖*‖b₀‖*ε:=by gcongr
      _=ε*(‖a₀‖*‖b₀‖):=by ring
  have htri:‖(a - a₀)*b*c+a₀*(b - b₀)*c+a₀*b₀*(c - 1)‖ ≤
      ‖(a - a₀)*b*c‖+‖a₀*(b - b₀)*c‖+‖a₀*b₀*(c - 1)‖:=by
    calc
      _≤ ‖(a - a₀)*b*c+a₀*(b - b₀)*c‖+‖a₀*b₀*(c - 1)‖:=norm_add_le _ _
      _≤ _:=by gcongr; exact norm_add_le _ _
  have hcoeff:ε*(1+ε)^2+ε*(1+ε)+ε≤ 4*ε:=by
    have hsq:(1+ε)^2+(1+ε)+1≤ 4:=by nlinarith
    nlinarith
  calc
    ‖(a - a₀)*b*c+a₀*(b - b₀)*c+a₀*b₀*(c - 1)‖
        ≤ (ε*(1+ε)^2+ε*(1+ε)+ε)*(‖a₀‖*‖b₀‖):=by linarith
    _≤ 4*ε*(‖a₀‖*‖b₀‖):=mul_le_mul_of_nonneg_right hcoeff (by positivity)
def zK:ℝ :=
  (za*∫ t:ℝ,(1+|t|)^1*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|)) *
  (∫ t:ℝ,(1+|t|) ∂rho)
lemma xP {T:ℝ} (_hT:0≤ T) :
    ∫ x in (zz T)ᶜ,‖kernel x‖ ∂zn ≤
      zK*Real.exp (-(1/ 10 : ℝ)*Real.sqrt T):=by
  have h1_int:Integrable (fun t:ℝ=>(1+|t|)*zh t) volume:=by
    refine ((zd (by norm_num:(0 : ℝ)< 1/ 5) 1).const_mul za).mono'
      ((continuous_const.add continuous_abs).mul zs).aestronglyMeasurable ?_
    refine ae_of_all _ fun t=>?_
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (zw t)),pow_one]
    calc
      (1+|t|)*zh t≤ (1+|t|)*(za*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|)) :=
        mul_le_mul_of_nonneg_left (zj t) (by positivity)
      _=za*((1+|t|)*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|)):=by ring
  have h1_rho:Integrable (fun t:ℝ=>1+|t|) rho:=zQ
  have hdom:Integrable (fun x:ℝ × ℝ=>(1+|x.1|)*(1+|x.2|)/ 2) zn :=
    (h1_rho.mul_prod h1_rho).div_const 2
  have hsub1:(zz T)ᶜ⊆({t:ℝ | T< |t|} ×ˢ Set.univ) ∪ (Set.univ ×ˢ {t:ℝ | T< |t|}):=by
    intro p hp
    simp only [zz,Set.mem_compl_iff,Set.mem_prod,Set.mem_Icc,not_and_or,not_le,
      Set.mem_union,Set.mem_ofPred_eq,Set.mem_univ,and_true,true_and] at hp ⊢
    rcases hp with (h | h) | (h | h)
    · exact Or.inl (lt_of_lt_of_le (by linarith:T< -p.1) (neg_le_abs p.1))
    · exact Or.inl (lt_of_lt_of_le h (le_abs_self p.1))
    · exact Or.inr (lt_of_lt_of_le (by linarith:T< -p.2) (neg_le_abs p.2))
    · exact Or.inr (lt_of_lt_of_le h (le_abs_self p.2))
  have hmeas_t:MeasurableSet {t:ℝ | T< |t|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have h1_tail:∫ t in {t:ℝ | T< |t|},(1+|t|) ∂rho ≤
      (za*∫ t:ℝ,(1+|t|)^1*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|)) *
        Real.exp (-(1/ 10 : ℝ)*Real.sqrt T):=by
    have hrew:∫ t in {t:ℝ | T< |t|},(1+|t|) ∂rho =
        ∫ t in {t:ℝ | T< |t|},(1+|t|)*zh t:=by
      rw [← integral_indicator hmeas_t,xw,← integral_indicator hmeas_t]
      congr 1; ext t
      by_cases ht:t∈{t:ℝ | T< |t|} <;> simp [ht,smul_eq_mul,mul_comm]
    rw [hrew]
    have hdom1:Integrable (fun t:ℝ =>
        (za*Real.exp (-(1/ 10 : ℝ)*Real.sqrt T)) *
          ((1+|t|)^1*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|))) volume :=
      (zd (by norm_num:(0 : ℝ)< 1/ 10) 1).const_mul _
    calc
      ∫ t in {t:ℝ | T< |t|},(1+|t|)*zh t
          ≤ ∫ t in {t:ℝ | T< |t|},
              (za*Real.exp (-(1/ 10 : ℝ)*Real.sqrt T)) *
                ((1+|t|)^1*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|)):=by
            refine setIntegral_mono_on h1_int.integrableOn hdom1.integrableOn hmeas_t fun t ht=>?_
            have hsqrt:Real.sqrt T≤ Real.sqrt |t|:=Real.sqrt_le_sqrt ht.le
            have hexp:Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|) ≤
                Real.exp (-(1/ 10 : ℝ)*Real.sqrt T)*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|):=by
              rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
            rw [pow_one]
            calc
              (1+|t|)*zh t
                  ≤ (1+|t|)*(za*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|)) :=
                    mul_le_mul_of_nonneg_left (zj t) (by positivity)
              _≤ (1+|t|)*(za*(Real.exp (-(1/ 10 : ℝ)*Real.sqrt T) *
                    Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|))):=by
                    gcongr; exact zT.le
              _=(za*Real.exp (-(1/ 10 : ℝ)*Real.sqrt T)) *
                    ((1+|t|)*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|)):=by ring
      _≤ ∫ t:ℝ,(za*Real.exp (-(1/ 10 : ℝ)*Real.sqrt T)) *
              ((1+|t|)^1*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|)) :=
            setIntegral_le_integral hdom1 (ae_of_all _ fun _=>by positivity [zT])
      _=(za*∫ t:ℝ,(1+|t|)^1*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|)) *
              Real.exp (-(1/ 10 : ℝ)*Real.sqrt T):=by
            rw [integral_const_mul]; ring
  have hS1:∫ x in ({t:ℝ | T< |t|} ×ˢ Set.univ),((1+|x.1|)*(1+|x.2|)/ 2) ∂zn =
      ((∫ t in {t:ℝ | T< |t|},(1+|t|) ∂rho)*(∫ t:ℝ,(1+|t|) ∂rho))/ 2:=by
    rw [integral_div]
    congr 1
    unfold zn
    rw [← Measure.prod_restrict,Measure.restrict_univ]
    exact MeasureTheory.integral_prod_mul (fun t=>1+|t|) (fun t=>1+|t|)
  have hS2:∫ x in (Set.univ ×ˢ {t:ℝ | T< |t|}),((1+|x.1|)*(1+|x.2|)/ 2) ∂zn =
      ((∫ t:ℝ,(1+|t|) ∂rho)*(∫ t in {t:ℝ | T< |t|},(1+|t|) ∂rho))/ 2:=by
    rw [integral_div]
    congr 1
    unfold zn
    rw [← Measure.prod_restrict,Measure.restrict_univ]
    exact MeasureTheory.integral_prod_mul (fun t=>1+|t|) (fun t=>1+|t|)
  calc
    ∫ x in (zz T)ᶜ,‖kernel x‖ ∂zn
        ≤ ∫ x in (zz T)ᶜ,((1+|x.1|)*(1+|x.2|)/ 2) ∂zn :=
          setIntegral_mono_on zc.norm.integrableOn hdom.integrableOn
            (z6 T).compl fun x _=>x7 x
    _≤ ∫ x in (({t:ℝ | T< |t|} ×ˢ Set.univ) ∪ (Set.univ ×ˢ {t:ℝ | T< |t|})),
            ((1+|x.1|)*(1+|x.2|)/ 2) ∂zn :=
          setIntegral_mono_set hdom.integrableOn (ae_of_all _ fun _=>by positivity)
            (LE.le.eventuallyLE hsub1)
    _≤ (∫ x in ({t:ℝ | T< |t|} ×ˢ Set.univ),((1+|x.1|)*(1+|x.2|)/ 2) ∂zn) +
        (∫ x in (Set.univ ×ˢ {t:ℝ | T< |t|}),((1+|x.1|)*(1+|x.2|)/ 2) ∂zn):=by
          have hA_m:MeasurableSet ({t:ℝ | T< |t|} ×ˢ (Set.univ:Set ℝ)) :=
            hmeas_t.prod MeasurableSet.univ
          have hB_m:MeasurableSet ((Set.univ:Set ℝ) ×ˢ {t:ℝ | T< |t|}) :=
            MeasurableSet.univ.prod hmeas_t
          rw [← Set.union_sdiff_self,
            MeasureTheory.setIntegral_union disjoint_sdiff_self_right (hB_m.diff hA_m)
              hdom.integrableOn hdom.integrableOn]
          exact add_le_add le_rfl
            (setIntegral_mono_set hdom.integrableOn (ae_of_all _ fun _=>by positivity)
              (LE.le.eventuallyLE Set.sdiff_subset))
    _=(∫ t in {t:ℝ | T< |t|},(1+|t|) ∂rho)*(∫ t:ℝ,(1+|t|) ∂rho):=by
          rw [hS1,hS2]; ring
    _≤ zK*Real.exp (-(1/ 10 : ℝ)*Real.sqrt T):=by
          unfold zK
          have hnn:0≤ ∫ t:ℝ,(1+|t|) ∂rho:=integral_nonneg fun _=>by positivity
          calc
            (∫ t in {t:ℝ | T< |t|},(1+|t|) ∂rho)*(∫ t:ℝ,(1+|t|) ∂rho)
                ≤ ((za*∫ t:ℝ,(1+|t|)^1*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|)) *
                    Real.exp (-(1/ 10 : ℝ)*Real.sqrt T))*(∫ t:ℝ,(1+|t|) ∂rho) :=
                  mul_le_mul_of_nonneg_right h1_tail hnn
            _=_:=by ring
def zM (A:ℝ) (N:ℕ):Prop :=
  Real.exp 2≤ (N:ℝ) ∧
  16≤ z7 N ∧
  2≤ z0 N ∧
  z0 N< z7 N ∧
  z0 N< yI N ∧
  2*yI N< N ∧
  (∀ k:Fin (z0 N),yD N≤ z9 A N k∧1< z9 A N k) ∧
  (∀ k:Fin (z0 N),∀ x∈zz (z3 N),
    riemannZeta (1+wk A N k x.1)≠0 ∧
    riemannZeta (1+wk A N k x.2)≠0 ∧
    ‖Gk A N k x - (((ze N/ Real.log (z9 A N k):ℝ):ℂ)*kernel x)‖ ≤
      (ze N/ Real.log (z9 A N k))*‖kernel x‖*(Real.log (N:ℝ))^(-(7/ 10 : ℝ))) ∧
  (∀ k:Fin (z0 N),
    ‖Nk A N k - (((ze N/ Real.log (z9 A N k):ℝ):ℂ)*(c0:ℂ))‖ ≤
      (ze N/ Real.log (z9 A N k))*(z8+1)*(Real.log (N:ℝ))^(-(7/ 10 : ℝ))) ∧
  (4*(z8+1)/ c0)*(Real.log (N:ℝ))^(-(7/ 10 : ℝ))≤ 1/ 4 ∧
  (z0 N:ℝ)*((4*(z8+1)/ c0)*(Real.log (N:ℝ))^(-(7/ 10 : ℝ)))≤ 1/ 10 ∧
  8*zf*(z0 N:ℝ)≤ (z7 N:ℝ) ∧
  32*zf^2*(z0 N:ℝ)^2/ (z7 N:ℝ)≤ 1/ 10 ∧
  (N:ℝ)^((1 : ℝ)/ 5)*(∏ k:Fin (z0 N),(z9 A N k)^2) /
      ((N:ℝ)/ (z4 N:ℝ))*(2*Real.log (N:ℝ))^(z0 N) ≤
    (1/ 8 : ℝ)*Real.exp (-(1/ 40 : ℝ)*(Real.log (N:ℝ))^((1 : ℝ)/ 10)) ∧
  Real.exp (3*(z0 N:ℝ)*(2*Real.log (Real.log (N:ℝ))+45)) *
    (2*(z0 N:ℝ)*zA*Real.exp (-(1/ 10 : ℝ)*Real.sqrt (z3 N))) *
    (2*Real.log (N:ℝ))^(z0 N) ≤
    (1/ 8 : ℝ)*Real.exp (-(1/ 40 : ℝ)*(Real.log (N:ℝ))^((1 : ℝ)/ 10)) ∧
  Real.exp (-(1/ 40 : ℝ)*(Real.log (N:ℝ))^((1 : ℝ)/ 10))≤ 1/ 4
lemma wF {A:ℝ} (hA:1≤ A) {N:ℕ} (hN:1≤ N) :
    ∏ k:Fin (z0 N),(z9 A N k)^2≤ (N:ℝ)^((1 : ℝ)/ 20):=by
  have hNpos:(0 : ℝ)< N:=by positivity
  have hlogN_nn:0≤ Real.log (N:ℝ):=Real.log_nonneg (by exact_mod_cast hN)
  have hRpos:∀ k:Fin (z0 N),0< z9 A N k:=fun k=>by
    rw [wu]; exact Real.rpow_pos_of_pos hNpos _
  rw [← Real.exp_log (Finset.prod_pos fun k _=>sq_pos_of_pos (hRpos k)),
    Real.rpow_def_of_pos hNpos]
  apply Real.exp_le_exp.mpr
  rw [Real.log_prod fun k _=>(sq_pos_of_pos (hRpos k)).ne']
  have hsum_eq:∑ k:Fin (z0 N),Real.log ((z9 A N k)^2) =
      (2*Real.log (N:ℝ)/ (100*(A+1))) *
        ∑ k:Fin (z0 N),(1 : ℝ)/ ((k.1+1 : ℕ):ℝ)^50:=by
    rw [mul_sum]
    refine sum_congr rfl fun k _=>?_
    rw [Real.log_pow,xV A hN k,Nat.cast_ofNat,div_mul_div_comm,mul_one,← mul_div_assoc]
  rw [hsum_eq]
  have hsum50:∑ k:Fin (z0 N),(1 : ℝ)/ ((k.1+1 : ℕ):ℝ)^50≤ 2:=by
    have hIcc:∑ k:Fin (z0 N),(1 : ℝ)/ ((k.1+1 : ℕ):ℝ)^50 =
        ∑ m∈Finset.Icc 1 (z0 N),(1 : ℝ)/ (m:ℝ)^50:=by
      refine Finset.sum_bij (fun k _=>k.1+1) ?_ ?_ ?_ ?_
      · intro k _; exact mem_Icc.mpr ⟨by omega,k.2⟩
      · intro k₁ _ k₂ _ h; exact Fin.ext (by omega)
      · intro m hm
        rcases mem_Icc.mp hm with ⟨h1,h2⟩
        exact ⟨⟨m - 1,by omega⟩,Finset.mem_univ _,by dsimp; omega⟩
      · intro _ _; rfl
    rw [hIcc]
    by_cases hK0:z0 N=0
    · rw [hK0]; simp
    · have hsplit:Finset.Icc 1 (z0 N)=insert 1 (Finset.Icc 2 (z0 N)):=by
        ext m; simp only [mem_Icc,mem_insert]; omega
      rw [hsplit,sum_insert (by simp)]
      have h2le:∑ m∈Finset.Icc 2 (z0 N),(1 : ℝ)/ (m:ℝ)^50 ≤
          ∑ m∈Finset.Icc 2 (z0 N),(1 : ℝ)/ (m:ℝ)^2:=by
        refine sum_le_sum fun m hm=>?_
        have hm1:(1 : ℝ)≤ m:=by exact_mod_cast (show 1≤ m by have:=(mem_Icc.mp hm).1; omega)
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hm1 (by norm_num))
      have hsq:=xc (z0 N)
      norm_num at h2le hsq ⊢
      linarith
  have hA2:(2 : ℝ)≤ A+1:=by linarith
  have hfac:2*Real.log (N:ℝ)/ (100*(A+1))≤ Real.log (N:ℝ)/ 100:=by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc
    (2*Real.log (N:ℝ)/ (100*(A+1))) *
        ∑ k:Fin (z0 N),(1 : ℝ)/ ((k.1+1 : ℕ):ℝ)^50
        ≤ (Real.log (N:ℝ)/ 100)*2 :=
          mul_le_mul hfac hsum50 (sum_nonneg fun _ _=>by positivity) (by positivity)
    _≤ Real.log (N:ℝ)*(1/ 20):=by linarith
private lemma yh {α : ℝ} (hα : 0< α) :
    Tendsto (fun y:ℝ=>Real.log y/ y^α) atTop (𝓝 0) :=
  (isLittleO_log_rpow_atTop hα).tendsto_div_nhds_zero
private lemma xG {P:ℝ→Prop} (hP:∀ᶠ y:ℝ in atTop,P y) :
    ∀ᶠ N:ℕ in atTop,P (Real.log (N:ℝ)) :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually hP
private lemma xB {A C_z δ_z : ℝ} (hA:1≤ A) (hδz_pos : 0< δ_z) :
    ∀ᶠ L:ℝ in atTop,
      (2 : ℝ)≤ L ∧
      (200 : ℝ)≤ L ∧
      (2 : ℝ)≤ L^((1 : ℝ)/ 1000) ∧
      (16 : ℝ)≤ 0.15*L - 1 ∧
      L^((1 : ℝ)/ 1000)< 0.15*L - 1 ∧
      L^((1 : ℝ)/ 1000)< Real.exp (L/ 100) - 1 ∧
      2*Real.exp (L/ 100)< Real.exp L ∧
      0.15*L≤ Real.exp (L^((19 : ℝ)/ 20)/ (100*(A+1))) ∧
      1< L^((19 : ℝ)/ 20)/ (100*(A+1)) ∧
      200*(A+1)*L^(-(3/ 4 : ℝ))≤ δ_z ∧
      C_z*(400*(A+1)*L^(-(3/ 4 : ℝ)))≤ L^(-(7/ 10 : ℝ))/ 10 ∧
      8*(200*(A+1)*L^(-(3/ 4 : ℝ)))^2*Real.log L*(1+Real.log L) ≤
        min 1 (L^(-(7/ 10 : ℝ))/ 20) ∧
      16/ (0.1*L)≤ min 1 (L^(-(7/ 10 : ℝ))/ 20) ∧
      L^(-(7/ 10 : ℝ))≤ 1/ 4:=by
  have hrp_top:∀ p:ℝ,0< p→Tendsto (fun L:ℝ=>L^p) atTop atTop :=
    fun p hp=>tendsto_rpow_atTop hp
  have hrp_zero:∀ p:ℝ,0< p→Tendsto (fun L:ℝ=>L^(-p)) atTop (𝓝 0) :=
    fun p hp=>tendsto_rpow_neg_atTop hp
  have hpow_lt:∀ (c p q:ℝ),p< q→∀ᶠ L:ℝ in atTop,c*L^p≤ L^q:=by
    intro c p q hpq
    have h0:Tendsto (fun L:ℝ=>c*L^(-(q - p))) atTop (𝓝 0):=by
      simpa using (hrp_zero (q - p) (by linarith)).const_mul c
    filter_upwards [eventually_ge_atTop (1 : ℝ),h0.eventually (Iio_mem_nhds one_pos)] with L hL1 hlt
    have hLpos:0< L:=by linarith
    have hmul:L^(-(q - p))*L^q=L^p:=by
      rw [← Real.rpow_add hLpos]; congr 1; ring
    calc
      c*L^p=(c*L^(-(q - p)))*L^q:=by rw [← hmul]; ring
      _≤ 1*L^q:=mul_le_mul_of_nonneg_right hlt.le (Real.rpow_pos_of_pos hLpos _).le
      _=L^q:=one_mul _
  have hlog_le_rpow:∀ α : ℝ,0< α→∀ᶠ L:ℝ in atTop,Real.log L≤ L^α:=by
    intro α hα
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      (yh hα).eventually (Iio_mem_nhds one_pos)] with L hL1 hlt
    have hpos:0< L^α:=Real.rpow_pos_of_pos (by linarith) _
    exact (div_le_one hpos).mp hlt.le
  have c1:∀ᶠ L:ℝ in atTop,(2 : ℝ)≤ L:=eventually_ge_atTop 2
  have c2:∀ᶠ L:ℝ in atTop,(200 : ℝ)≤ L:=eventually_ge_atTop 200
  have c3:∀ᶠ L:ℝ in atTop,(2 : ℝ)≤ L^((1 : ℝ)/ 1000) :=
    (hrp_top _ (by norm_num)).eventually_ge_atTop 2
  have c4:∀ᶠ L:ℝ in atTop,(16 : ℝ)≤ 0.15*L - 1:=by
    filter_upwards [eventually_ge_atTop (200 : ℝ)] with L hL; linarith
  have c5:∀ᶠ L:ℝ in atTop,L^((1 : ℝ)/ 1000)< 0.15*L - 1:=by
    filter_upwards [eventually_ge_atTop (200 : ℝ),
      hpow_lt 10 ((1 : ℝ)/ 1000) 1 (by norm_num)] with L hL hlt
    rw [Real.rpow_one] at hlt; linarith
  have c6:∀ᶠ L:ℝ in atTop,L^((1 : ℝ)/ 1000)< Real.exp (L/ 100) - 1:=by
    filter_upwards [eventually_ge_atTop (200 : ℝ),
      hpow_lt 200 ((1 : ℝ)/ 1000) 1 (by norm_num)] with L hL hlt
    rw [Real.rpow_one] at hlt
    have hexp:=Real.add_one_le_exp (L/ 100)
    linarith
  have c7:∀ᶠ L:ℝ in atTop,2*Real.exp (L/ 100)< Real.exp L:=by
    filter_upwards [eventually_ge_atTop (200 : ℝ)] with L hL
    have h1:(2 : ℝ)< Real.exp (99/ 100*L):=by
      linarith [Real.add_one_le_exp (99/ 100*L)]
    calc
      2*Real.exp (L/ 100)< Real.exp (99/ 100*L)*Real.exp (L/ 100) :=
        mul_lt_mul_of_pos_right h1 (Real.exp_pos _)
      _=Real.exp L:=by rw [← Real.exp_add]; congr 1; ring
  have c8:∀ᶠ L:ℝ in atTop,0.15*L≤ Real.exp (L^((19 : ℝ)/ 20)/ (100*(A+1))):=by
    filter_upwards [eventually_ge_atTop (2 : ℝ),
      hlog_le_rpow ((1 : ℝ)/ 2) (by norm_num),
      hpow_lt (100*(A+1)) ((1 : ℝ)/ 2) ((19 : ℝ)/ 20) (by norm_num)] with L hL hlog hpow
    have hle:Real.log (0.15*L)≤ L^((19 : ℝ)/ 20)/ (100*(A+1)):=by
      have h1:Real.log (0.15*L)≤ Real.log L:=Real.log_le_log (by linarith) (by linarith)
      have h2:L^((1 : ℝ)/ 2)≤ L^((19 : ℝ)/ 20)/ (100*(A+1)):=by
        rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    calc
      0.15*L=Real.exp (Real.log (0.15*L)):=(Real.exp_log (by linarith)).symm
      _≤ Real.exp (L^((19 : ℝ)/ 20)/ (100*(A+1))):=Real.exp_le_exp.mpr hle
  have c9:∀ᶠ L:ℝ in atTop,1< L^((19 : ℝ)/ 20)/ (100*(A+1)):=by
    filter_upwards [(hrp_top ((19 : ℝ)/ 20) (by norm_num)).eventually_gt_atTop (100*(A+1))]
      with L hL
    exact (one_lt_div (by positivity)).mpr hL
  have c10:∀ᶠ L:ℝ in atTop,200*(A+1)*L^(-(3/ 4 : ℝ))≤ δ_z:=by
    have h0:Tendsto (fun L:ℝ=>200*(A+1)*L^(-(3/ 4 : ℝ))) atTop (𝓝 0):=by
      simpa using (hrp_zero (3/ 4) (by norm_num)).const_mul (200*(A+1))
    filter_upwards [h0.eventually (Iio_mem_nhds hδz_pos)] with L hL; exact hL.le
  have c11:∀ᶠ L:ℝ in atTop,
      C_z*(400*(A+1)*L^(-(3/ 4 : ℝ)))≤ L^(-(7/ 10 : ℝ))/ 10:=by
    filter_upwards [hpow_lt (10*C_z*(400*(A+1))) (-(3/ 4 : ℝ)) (-(7/ 10 : ℝ))
      (by norm_num)] with L hL
    linarith
  have c12:∀ᶠ L:ℝ in atTop,
      8*(200*(A+1)*L^(-(3/ 4 : ℝ)))^2*Real.log L*(1+Real.log L) ≤
        min 1 (L^(-(7/ 10 : ℝ))/ 20):=by
    have hsub:∀ᶠ L:ℝ in atTop,
        8*(200*(A+1)*L^(-(3/ 4 : ℝ)))^2*Real.log L*(1+Real.log L) ≤
          L^(-(7/ 10 : ℝ))/ 20:=by
      filter_upwards [eventually_ge_atTop (3 : ℝ),
        hlog_le_rpow ((1 : ℝ)/ 4) (by norm_num),
        hpow_lt (320*(200*(A+1))^2) (-1 : ℝ) (-(7/ 10 : ℝ)) (by norm_num)]
        with L hL hlog hpow
      have hLpos:0< L:=by linarith
      have hlog1:1≤ Real.log L:=by
        have : Real.exp 1≤ L:=by linarith [Real.exp_one_lt_d9]
        calc (1 : ℝ)=Real.log (Real.exp 1):=(Real.log_exp 1).symm
          _≤ Real.log L:=Real.log_le_log (Real.exp_pos 1) this
      have h1log:1+Real.log L≤ 2*L^((1 : ℝ)/ 4):=by linarith
      have hpow_comb:(L^(-(3/ 4 : ℝ)))^2*L^((1 : ℝ)/ 4)*L^((1 : ℝ)/ 4)=L^(-1 : ℝ):=by
        rw [← Real.rpow_natCast,← Real.rpow_mul hLpos.le,← Real.rpow_add hLpos,← Real.rpow_add hLpos]
        congr 1; norm_num
      calc
        8*(200*(A+1)*L^(-(3/ 4 : ℝ)))^2*Real.log L*(1+Real.log L)
            ≤ 8*(200*(A+1)*L^(-(3/ 4 : ℝ)))^2*L^((1 : ℝ)/ 4)*(2*L^((1 : ℝ)/ 4)):=by
              gcongr
        _=16*(200*(A+1))^2*((L^(-(3/ 4 : ℝ)))^2*L^((1 : ℝ)/ 4)*L^((1 : ℝ)/ 4)):=by
              ring
        _=16*(200*(A+1))^2*L^(-1 : ℝ):=by rw [hpow_comb]
        _≤ L^(-(7/ 10 : ℝ))/ 20:=by linarith
    filter_upwards [eventually_ge_atTop (2 : ℝ),hsub] with L hL hle
    have h1:L^(-(7/ 10 : ℝ))/ 20≤ 1:=by
      have : L^(-(7/ 10 : ℝ))≤ 1:=Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
      linarith
    exact le_min (hle.trans h1) hle
  have c13:∀ᶠ L:ℝ in atTop,16/ (0.1*L)≤ min 1 (L^(-(7/ 10 : ℝ))/ 20):=by
    filter_upwards [eventually_ge_atTop (200 : ℝ),
      hpow_lt 3200 (-1 : ℝ) (-(7/ 10 : ℝ)) (by norm_num)] with L hL hpow
    have hinv:16/ (0.1*L)=160*L^(-1 : ℝ):=by
      rw [Real.rpow_neg_one]; field_simp; ring
    rw [hinv]
    have hle20:160*L^(-1 : ℝ)≤ L^(-(7/ 10 : ℝ))/ 20:=by linarith
    have h1:L^(-(7/ 10 : ℝ))/ 20≤ 1:=by
      have : L^(-(7/ 10 : ℝ))≤ 1:=Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
      linarith
    exact le_min (hle20.trans h1) hle20
  have c14:∀ᶠ L:ℝ in atTop,L^(-(7/ 10 : ℝ))≤ 1/ 4:=by
    filter_upwards [(hrp_zero (7/ 10) (by norm_num)).eventually (Iio_mem_nhds (by norm_num:(0 : ℝ)< 1/ 4))]
      with L hL; exact hL.le
  filter_upwards [c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,c11,c12,c13,c14] with L
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14⟩
private lemma xA :
    ∀ᶠ L:ℝ in atTop,
      zK*Real.exp (-(1/ 10 : ℝ)*L^((1 : ℝ)/ 10))≤ L^(-(7/ 10 : ℝ)) ∧
      (4*(z8+1)/ c0)*L^(-(7/ 10 : ℝ))≤ 1/ 4 ∧
      L^((1 : ℝ)/ 1000)*((4*(z8+1)/ c0)*L^(-(7/ 10 : ℝ)))≤ 1/ 10 ∧
      8*zf*L^((1 : ℝ)/ 1000)≤ 0.1*L ∧
      32*zf^2*(L^((1 : ℝ)/ 1000))^2/ (0.1*L)≤ 1/ 10 ∧
      L^((1 : ℝ)/ 1000)*Real.log (2*L)+(1/ 40 : ℝ)*L^((1 : ℝ)/ 10)+Real.log 8 ≤
        (1/ 2 : ℝ)*L ∧
      3*L^((1 : ℝ)/ 1000)*(2*Real.log L+45) +
        Real.log (2*L^((1 : ℝ)/ 1000)*zA+1) +
        L^((1 : ℝ)/ 1000)*Real.log (2*L)+Real.log 8 ≤
        (3/ 40 : ℝ)*L^((1 : ℝ)/ 10) ∧
      Real.exp (-(1/ 40 : ℝ)*L^((1 : ℝ)/ 10))≤ 1/ 4:=by
  have hrp_top:∀ p:ℝ,0< p→Tendsto (fun L:ℝ=>L^p) atTop atTop :=
    fun p hp=>tendsto_rpow_atTop hp
  have hrp_zero:∀ p:ℝ,0< p→Tendsto (fun L:ℝ=>L^(-p)) atTop (𝓝 0) :=
    fun p hp=>tendsto_rpow_neg_atTop hp
  have hpow_lt:∀ (c p q:ℝ),p< q→∀ᶠ L:ℝ in atTop,c*L^p≤ L^q:=by
    intro c p q hpq
    have h0:Tendsto (fun L:ℝ=>c*L^(-(q - p))) atTop (𝓝 0):=by
      simpa using (hrp_zero (q - p) (by linarith)).const_mul c
    filter_upwards [eventually_ge_atTop (1 : ℝ),h0.eventually (Iio_mem_nhds one_pos)] with L hL1 hlt
    have hLpos:0< L:=by linarith
    have hmul:L^(-(q - p))*L^q=L^p:=by
      rw [← Real.rpow_add hLpos]; congr 1; ring
    calc
      c*L^p=(c*L^(-(q - p)))*L^q:=by rw [← hmul]; ring
      _≤ 1*L^q:=mul_le_mul_of_nonneg_right hlt.le (Real.rpow_pos_of_pos hLpos _).le
      _=L^q:=one_mul _
  have hlog_le_rpow:∀ α : ℝ,0< α→∀ᶠ L:ℝ in atTop,Real.log L≤ L^α:=by
    intro α hα
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      (yh hα).eventually (Iio_mem_nhds one_pos)] with L hL1 hlt
    have hpos:0< L^α:=Real.rpow_pos_of_pos (by linarith) _
    exact (div_le_one hpos).mp hlt.le
  have hlog8_le3:Real.log 8≤ 3:=by
    have h8:(8 : ℝ)≤ Real.exp 3:=by
      have h3:Real.exp 3=(Real.exp 1)^3:=by rw [← Real.exp_nat_mul]; norm_num
      rw [h3]
      calc (8 : ℝ)=2^3:=by norm_num
        _≤ (Real.exp 1)^3:=by gcongr; linarith [Real.add_one_le_exp (1 : ℝ)]
    calc Real.log 8≤ Real.log (Real.exp 3):=Real.log_le_log (by norm_num) h8
      _=3:=Real.log_exp 3
  have c15:∀ᶠ L:ℝ in atTop,
      zK*Real.exp (-(1/ 10 : ℝ)*L^((1 : ℝ)/ 10))≤ L^(-(7/ 10 : ℝ)):=by
    have hlog:∀ᶠ L:ℝ in atTop,Real.log L≤ (1/ 10 : ℝ)*L^((1 : ℝ)/ 10):=by
      filter_upwards [(yh (by norm_num:(0 : ℝ)< 1/ 10)).eventually
        (Iio_mem_nhds (by norm_num:(0 : ℝ)< 1/ 10)),eventually_ge_atTop (2 : ℝ)] with L hlt hL
      have hpos:0< L^((1 : ℝ)/ 10):=Real.rpow_pos_of_pos (by linarith) _
      exact (div_le_iff₀ hpos).mp hlt.le
    filter_upwards [eventually_ge_atTop (2 : ℝ),hlog,
      hpow_lt (max zK 1) (-1 : ℝ) (-(7/ 10 : ℝ)) (by norm_num)] with L hL hlog' hpow
    have hLpos:0< L:=by linarith
    have hexp:Real.exp (-(1/ 10 : ℝ)*L^((1 : ℝ)/ 10))≤ L^(-1 : ℝ):=by
      conv_rhs=>rw [Real.rpow_neg_one,← Real.exp_log hLpos,← Real.exp_neg]
      exact Real.exp_le_exp.mpr (by linarith)
    have hCnn:0≤ zK:=by
      unfold zK
      exact mul_nonneg (mul_nonneg zT.le (integral_nonneg fun _=>by positivity))
        (integral_nonneg fun _=>by positivity)
    calc
      zK*Real.exp (-(1/ 10 : ℝ)*L^((1 : ℝ)/ 10))
          ≤ max zK 1*L^(-1 : ℝ) :=
            mul_le_mul (le_max_left _ _) hexp (Real.exp_pos _).le (by positivity)
      _≤ L^(-(7/ 10 : ℝ)):=hpow
  have c16:∀ᶠ L:ℝ in atTop,(4*(z8+1)/ c0)*L^(-(7/ 10 : ℝ))≤ 1/ 4:=by
    have h0:Tendsto (fun L:ℝ=>(4*(z8+1)/ c0)*L^(-(7/ 10 : ℝ))) atTop (𝓝 0):=by
      simpa using (hrp_zero (7/ 10) (by norm_num)).const_mul (4*(z8+1)/ c0)
    filter_upwards [h0.eventually (Iio_mem_nhds (by norm_num:(0 : ℝ)< 1/ 4))] with L hL; exact hL.le
  have c17:∀ᶠ L:ℝ in atTop,
      L^((1 : ℝ)/ 1000)*((4*(z8+1)/ c0)*L^(-(7/ 10 : ℝ)))≤ 1/ 10:=by
    have h0:Tendsto (fun L:ℝ=>(4*(z8+1)/ c0)*L^(-(699/ 1000 : ℝ))) atTop (𝓝 0):=by
      simpa using (hrp_zero (699/ 1000) (by norm_num)).const_mul (4*(z8+1)/ c0)
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      h0.eventually (Iio_mem_nhds (by norm_num:(0 : ℝ)< 1/ 10))] with L hL hlt
    have hLpos:0< L:=by linarith
    have hadd:L^((1 : ℝ)/ 1000)*L^(-(7/ 10 : ℝ))=L^(-(699/ 1000 : ℝ)):=by
      rw [← Real.rpow_add hLpos]; congr 1; norm_num
    rw [show L^((1 : ℝ)/ 1000)*((4*(z8+1)/ c0)*L^(-(7/ 10 : ℝ))) =
        (4*(z8+1)/ c0)*(L^((1 : ℝ)/ 1000)*L^(-(7/ 10 : ℝ))) by ring,hadd]
    exact hlt.le
  have c18:∀ᶠ L:ℝ in atTop,8*zf*L^((1 : ℝ)/ 1000)≤ 0.1*L:=by
    filter_upwards [hpow_lt (80*zf) ((1 : ℝ)/ 1000) 1 (by norm_num)] with L hL
    rw [Real.rpow_one] at hL; linarith
  have c19:∀ᶠ L:ℝ in atTop,32*zf^2*(L^((1 : ℝ)/ 1000))^2/ (0.1*L)≤ 1/ 10:=by
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      hpow_lt (3200*zf^2) ((2 : ℝ)/ 1000) 1 (by norm_num)] with L hL hpow
    have hLpos:0< L:=by linarith
    have hsq:(L^((1 : ℝ)/ 1000))^2=L^((2 : ℝ)/ 1000):=by
      rw [← Real.rpow_natCast,← Real.rpow_mul hLpos.le]; congr 1; norm_num
    rw [hsq]
    rw [Real.rpow_one] at hpow
    rw [div_le_iff₀ (by linarith)]; linarith
  have c20:∀ᶠ L:ℝ in atTop,
      L^((1 : ℝ)/ 1000)*Real.log (2*L)+(1/ 40 : ℝ)*L^((1 : ℝ)/ 10)+Real.log 8 ≤
        (1/ 2 : ℝ)*L:=by
    filter_upwards [eventually_ge_atTop (20 : ℝ),
      hlog_le_rpow ((1 : ℝ)/ 100) (by norm_num),
      hpow_lt 12 ((11 : ℝ)/ 1000) 1 (by norm_num),
      hpow_lt 1 ((1 : ℝ)/ 10) 1 (by norm_num)] with L hL hlog h1 h2
    have hLpos:0< L:=by linarith
    have hlog2L:Real.log (2*L)≤ 2*L^((1 : ℝ)/ 100):=by
      rw [Real.log_mul (by norm_num) hLpos.ne']
      have hlog2:Real.log 2≤ 1:=by linarith [Real.log_le_sub_one_of_pos (by norm_num:(0 : ℝ)< 2)]
      have h1r:1≤ L^((1 : ℝ)/ 100):=Real.one_le_rpow (by linarith) (by norm_num)
      linarith
    have hprod:L^((1 : ℝ)/ 1000)*L^((1 : ℝ)/ 100)=L^((11 : ℝ)/ 1000):=by
      rw [← Real.rpow_add hLpos]; congr 1; norm_num
    rw [Real.rpow_one] at h1 h2
    have ht1:L^((1 : ℝ)/ 1000)*Real.log (2*L)≤ 2*L^((11 : ℝ)/ 1000):=by
      calc
        L^((1 : ℝ)/ 1000)*Real.log (2*L)
            ≤ L^((1 : ℝ)/ 1000)*(2*L^((1 : ℝ)/ 100)) :=
              mul_le_mul_of_nonneg_left hlog2L (Real.rpow_pos_of_pos hLpos _).le
        _=2*(L^((1 : ℝ)/ 1000)*L^((1 : ℝ)/ 100)):=by ring
        _=2*L^((11 : ℝ)/ 1000):=by rw [hprod]
    linarith
  have c21:∀ᶠ L:ℝ in atTop,
      3*L^((1 : ℝ)/ 1000)*(2*Real.log L+45) +
        Real.log (2*L^((1 : ℝ)/ 1000)*zA+1) +
        L^((1 : ℝ)/ 1000)*Real.log (2*L)+Real.log 8 ≤
        (3/ 40 : ℝ)*L^((1 : ℝ)/ 10):=by
    filter_upwards [eventually_ge_atTop (3 : ℝ),
      hlog_le_rpow ((1 : ℝ)/ 100) (by norm_num),
      hpow_lt (40*(150+2*zA)) ((11 : ℝ)/ 1000) ((1 : ℝ)/ 10) (by norm_num)]
      with L hL hlog hpow
    have hLpos:0< L:=by linarith
    have h1r1:1≤ L^((1 : ℝ)/ 1000):=Real.one_le_rpow (by linarith) (by norm_num)
    have h1r2:1≤ L^((1 : ℝ)/ 100):=Real.one_le_rpow (by linarith) (by norm_num)
    have hprod:L^((1 : ℝ)/ 1000)*L^((1 : ℝ)/ 100)=L^((11 : ℝ)/ 1000):=by
      rw [← Real.rpow_add hLpos]; congr 1; norm_num
    have hlog2L:Real.log (2*L)≤ 2*L^((1 : ℝ)/ 100):=by
      rw [Real.log_mul (by norm_num) hLpos.ne']
      have hlog2:Real.log 2≤ 1:=by linarith [Real.log_le_sub_one_of_pos (by norm_num:(0 : ℝ)< 2)]
      linarith
    have hlogC:Real.log (2*L^((1 : ℝ)/ 1000)*zA+1)≤ 2*zA*L^((11 : ℝ)/ 1000):=by
      have hle1:Real.log (2*L^((1 : ℝ)/ 1000)*zA+1)≤ 2*L^((1 : ℝ)/ 1000)*zA:=by
        have:=Real.log_le_sub_one_of_pos (by positivity [yC]:(0 : ℝ)< 2*L^((1 : ℝ)/ 1000)*zA+1)
        linarith
      have hle2:L^((1 : ℝ)/ 1000)≤ L^((11 : ℝ)/ 1000) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      nlinarith [yC]
    have hlog8:Real.log 8≤ 3*L^((11 : ℝ)/ 1000):=by
      have hge:1≤ L^((11 : ℝ)/ 1000):=Real.one_le_rpow (by linarith) (by norm_num)
      linarith
    have ht1:3*L^((1 : ℝ)/ 1000)*(2*Real.log L+45)≤ 141*L^((11 : ℝ)/ 1000):=by
      have h1:2*Real.log L+45≤ 47*L^((1 : ℝ)/ 100):=by linarith
      calc
        3*L^((1 : ℝ)/ 1000)*(2*Real.log L+45)
            ≤ 3*L^((1 : ℝ)/ 1000)*(47*L^((1 : ℝ)/ 100)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
        _=141*(L^((1 : ℝ)/ 1000)*L^((1 : ℝ)/ 100)):=by ring
        _=141*L^((11 : ℝ)/ 1000):=by rw [hprod]
    have ht3:L^((1 : ℝ)/ 1000)*Real.log (2*L)≤ 2*L^((11 : ℝ)/ 1000):=by
      calc
        L^((1 : ℝ)/ 1000)*Real.log (2*L)
            ≤ L^((1 : ℝ)/ 1000)*(2*L^((1 : ℝ)/ 100)) :=
              mul_le_mul_of_nonneg_left hlog2L (by positivity)
        _=2*(L^((1 : ℝ)/ 1000)*L^((1 : ℝ)/ 100)):=by ring
        _=2*L^((11 : ℝ)/ 1000):=by rw [hprod]
    have hsum_coef:(146+2*zA)*L^((11 : ℝ)/ 1000) ≤
        (150+2*zA)*L^((11 : ℝ)/ 1000):=by gcongr; norm_num
    have h1:141*L^((11 : ℝ)/ 1000)+2*zA*L^((11 : ℝ)/ 1000) +
        2*L^((11 : ℝ)/ 1000)+3*L^((11 : ℝ)/ 1000) =
        (146+2*zA)*L^((11 : ℝ)/ 1000):=by ring
    have h2:40*((150+2*zA)*L^((11 : ℝ)/ 1000)) =
        40*(150+2*zA)*L^((11 : ℝ)/ 1000):=by ring
    have h3:(0 : ℝ)≤ L^((1 : ℝ)/ 10):=by positivity
    linarith
  have c22:∀ᶠ L:ℝ in atTop,Real.exp (-(1/ 40 : ℝ)*L^((1 : ℝ)/ 10))≤ 1/ 4:=by
    filter_upwards [(hrp_top ((1 : ℝ)/ 10) (by norm_num)).eventually_ge_atTop (40*Real.log 4)] with L hL
    have hlog4:-(1/ 40 : ℝ)*L^((1 : ℝ)/ 10)≤ -Real.log 4:=by linarith
    calc
      Real.exp (-(1/ 40 : ℝ)*L^((1 : ℝ)/ 10))≤ Real.exp (-Real.log 4):=Real.exp_le_exp.mpr hlog4
      _=1/ 4:=by rw [Real.exp_neg,Real.exp_log (by norm_num),one_div]
  filter_upwards [c15,c16,c17,c18,c19,c20,c21,c22] with L h15 h16 h17 h18 h19 h20 h21 h22
  exact ⟨h15,h16,h17,h18,h19,h20,h21,h22⟩
private lemma wq {A C_z δ_z : ℝ} (hA:1≤ A) (hCz_pos:0< C_z)
    (hZratio:∀ w₁ w₂ : ℂ,0< w₁.re→0< w₂.re→‖w₁‖≤ δ_z→‖w₂‖≤ δ_z →
      riemannZeta (1+w₁)≠0∧riemannZeta (1+w₂)≠0∧w₁+w₂≠0 ∧
        ‖riemannZeta (1+w₁+w₂)/ (riemannZeta (1+w₁)*riemannZeta (1+w₂)) - w₁*w₂/ (w₁+w₂)‖ ≤
          C_z*‖w₁*w₂/ (w₁+w₂)‖*(‖w₁‖+‖w₂‖))
    {N:ℕ} (hL2:2≤ Real.log (N:ℝ)) (hw16:16≤ z7 N)
    (hw_lo:0.1*Real.log (N:ℝ)≤ (z7 N:ℝ))
    (hw_hi:(z7 N:ℝ)≤ 0.15*Real.log (N:ℝ))
    (k:Fin (z0 N)) (hR_gt1:1< z9 A N k)
    (hwk_bound:∀ t∈Set.Icc (-(z3 N)) (z3 N),
      ‖wk A N k t‖≤ 200*(A+1)*(Real.log (N:ℝ))^(-(3/ 4 : ℝ)))
    (hL_dz:200*(A+1)*(Real.log (N:ℝ))^(-(3/ 4 : ℝ))≤ δ_z)
    (hL_Cz:C_z*(400*(A+1)*(Real.log (N:ℝ))^(-(3/ 4 : ℝ))) ≤
      (Real.log (N:ℝ))^(-(7/ 10 : ℝ))/ 10)
    (hL_tiny:8*(200*(A+1)*(Real.log (N:ℝ))^(-(3/ 4 : ℝ)))^2 *
      Real.log (Real.log (N:ℝ))*(1+Real.log (Real.log (N:ℝ))) ≤
      min 1 ((Real.log (N:ℝ))^(-(7/ 10 : ℝ))/ 20))
    (hL_Cgt:16/ (0.1*Real.log (N:ℝ))≤ min 1 ((Real.log (N:ℝ))^(-(7/ 10 : ℝ))/ 20))
    (hL_07:(Real.log (N:ℝ))^(-(7/ 10 : ℝ))≤ 1/ 4)
    {x:ℝ × ℝ} (hx:x∈zz (z3 N)) :
    riemannZeta (1+wk A N k x.1)≠0 ∧
    riemannZeta (1+wk A N k x.2)≠0 ∧
    ‖Gk A N k x - (((ze N/ Real.log (z9 A N k):ℝ):ℂ)*kernel x)‖ ≤
      (ze N/ Real.log (z9 A N k))*‖kernel x‖*(Real.log (N:ℝ))^(-(7/ 10 : ℝ)):=by
  set L:=Real.log (N:ℝ)
  rcases hx with ⟨hx1,hx2⟩
  set w₁:=wk A N k x.1
  set w₂:=wk A N k x.2
  have hlogR_pos:0< Real.log (z9 A N k):=Real.log_pos hR_gt1
  have hw1_re:0< w₁.re:=by rw [w9]; positivity
  have hw2_re:0< w₂.re:=by rw [w9]; positivity
  have hw1_n:‖w₁‖≤ 200*(A+1)*L^(-(3/ 4 : ℝ)):=hwk_bound x.1 hx1
  have hw2_n:‖w₂‖≤ 200*(A+1)*L^(-(3/ 4 : ℝ)):=hwk_bound x.2 hx2
  obtain ⟨hz1,hz2,_,hz_err⟩:=hZratio w₁ w₂ hw1_re hw2_re (hw1_n.trans hL_dz) (hw2_n.trans hL_dz)
  refine ⟨hz1,hz2,?_⟩
  obtain ⟨_,C_gt,hCgt_err,hGk_eq⟩:=zp (by omega) hR_gt1 x hz1 hz2
  have hkern_eq:w₁*w₂/ (w₁+w₂)=((1/ Real.log (z9 A N k):ℝ):ℂ)*kernel x:=by
    have hlogC:(Real.log (z9 A N k):ℂ)≠0:=by exact_mod_cast hlogR_pos.ne'
    have hden_ne:(2 : ℂ)+Complex.I*((x.1 : ℂ)+(x.2 : ℂ))≠0:=by
      intro h0; have hre:((2 : ℂ)+Complex.I*((x.1 : ℂ)+(x.2 : ℂ))).re=2:=by simp
      rw [h0] at hre; simp at hre
    dsimp only [w₁,w₂]; unfold wk kernel
    push_cast
    have hsum:(1+Complex.I*(x.1 : ℂ))/ (Real.log (z9 A N k):ℂ) +
        (1+Complex.I*(x.2 : ℂ))/ (Real.log (z9 A N k):ℂ) =
        (2+Complex.I*((x.1 : ℂ)+(x.2 : ℂ)))/ (Real.log (z9 A N k):ℂ):=by ring
    rw [hsum]
    field_simp [hlogC,hden_ne]
  rw [hkern_eq] at hz_err
  set ε:=L^(-(7/ 10 : ℝ))/ 10
  have hε0 : 0≤ ε:=by positivity
  have hε1 : ε≤ 1/ 10:=by dsimp [ε]; linarith
  have ha_err:‖riemannZeta (1+w₁+w₂)/ (riemannZeta (1+w₁)*riemannZeta (1+w₂)) -
      ((1/ Real.log (z9 A N k):ℝ):ℂ)*kernel x‖ ≤
      ε*‖((1/ Real.log (z9 A N k):ℝ):ℂ)*kernel x‖:=by
    refine hz_err.trans ?_
    have hsum_w:‖w₁‖+‖w₂‖≤ 400*(A+1)*L^(-(3/ 4 : ℝ)):=by linarith
    calc
      C_z*‖((1/ Real.log (z9 A N k):ℝ):ℂ)*kernel x‖*(‖w₁‖+‖w₂‖)
          = (C_z*(‖w₁‖+‖w₂‖))*‖((1/ Real.log (z9 A N k):ℝ):ℂ)*kernel x‖:=by ring
      _≤ (C_z*(400*(A+1)*L^(-(3/ 4 : ℝ)))) *
            ‖((1/ Real.log (z9 A N k):ℝ):ℂ)*kernel x‖:=by gcongr
      _≤ ε*‖((1/ Real.log (z9 A N k):ℝ):ℂ)*kernel x‖:=by gcongr
  have hb_err:‖(∏ p∈z5 (z7 N),
        (1 - (p:ℂ)^(-(1+w₁+w₂))) /
          ((1 - (p:ℂ)^(-(1+w₁)))*(1 - (p:ℂ)^(-(1+w₂))))) - (ze N:ℂ)‖ ≤
      ε*‖(ze N:ℂ)‖:=by
    refine (wb (by omega) hR_gt1 x).trans ?_
    rw [Complex.norm_real,Real.norm_of_nonneg (by linarith [zr N]),mul_comm ε]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith [zr N])
    have hlogw_le:Real.log (z7 N:ℝ)≤ Real.log L :=
      Real.log_le_log (by exact_mod_cast (show 0< z7 N by omega)) (by linarith)
    have hlogw_nn:0≤ Real.log (z7 N:ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1≤ z7 N by omega))
    have hlogL_nn:0≤ Real.log L:=Real.log_nonneg (by linarith)
    have harg_le:8*‖w₁‖*‖w₂‖*Real.log (z7 N:ℝ)*(1+Real.log (z7 N:ℝ)) ≤
        min 1 (L^(-(7/ 10 : ℝ))/ 20):=by
      refine le_trans ?_ hL_tiny
      have h1:8*‖w₁‖*‖w₂‖*Real.log (z7 N:ℝ)*(1+Real.log (z7 N:ℝ)) ≤
          8*(200*(A+1)*L^(-(3/ 4 : ℝ)))*(200*(A+1)*L^(-(3/ 4 : ℝ))) *
            Real.log L*(1+Real.log L):=by gcongr
      exact h1.trans_eq (by ring)
    calc
      Real.exp (8*‖w₁‖*‖w₂‖*Real.log (z7 N:ℝ)*(1+Real.log (z7 N:ℝ))) - 1
          ≤ 2*(8*‖w₁‖*‖w₂‖*Real.log (z7 N:ℝ)*(1+Real.log (z7 N:ℝ))) :=
            y2 (by positivity) (harg_le.trans (min_le_left _ _))
      _≤ 2*(L^(-(7/ 10 : ℝ))/ 20):=by linarith [harg_le.trans (min_le_right _ _)]
      _=ε:=by dsimp [ε]; ring
  have hc_err:‖C_gt - 1‖≤ ε:=by
    refine hCgt_err.trans ?_
    have harg:16/ (z7 N:ℝ)≤ min 1 (L^(-(7/ 10 : ℝ))/ 20):=by
      refine le_trans ?_ hL_Cgt
      exact div_le_div_of_nonneg_left (by norm_num) (by linarith) hw_lo
    calc
      Real.exp (16/ (z7 N:ℝ)) - 1≤ 2*(16/ (z7 N:ℝ)) :=
        y2 (by positivity) (harg.trans (min_le_left _ _))
      _≤ 2*(L^(-(7/ 10 : ℝ))/ 20):=by linarith [harg.trans (min_le_right _ _)]
      _=ε:=by dsimp [ε]; ring
  have hcomb:=we hε0 hε1 ha_err hb_err hc_err
  have hrhs_eq:(((1/ Real.log (z9 A N k):ℝ):ℂ)*kernel x)*(ze N:ℂ) =
      (((ze N/ Real.log (z9 A N k):ℝ):ℂ)*kernel x):=by
    push_cast; ring
  rw [← hGk_eq,hrhs_eq] at hcomb
  refine hcomb.trans ?_
  rw [norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by linarith [zr N])]
  have heq4:4*ε*(1/ Real.log (z9 A N k)*‖kernel x‖*ze N) =
      (4/ 10 : ℝ)*((ze N/ Real.log (z9 A N k))*‖kernel x‖*L^(-(7/ 10 : ℝ))):=by
    dsimp [ε]; ring
  rw [heq4]
  have hnn:0≤ (ze N/ Real.log (z9 A N k))*‖kernel x‖*L^(-(7/ 10 : ℝ)):=by
    have:=zr N; positivity
  linarith
private lemma wp {A:ℝ} {N:ℕ}
    (hL2:2≤ Real.log (N:ℝ)) (hw16:16≤ z7 N)
    (k:Fin (z0 N)) (hR_gt1:1< z9 A N k)
    (hL_07:(Real.log (N:ℝ))^(-(7/ 10 : ℝ))≤ 1/ 4)
    (hL_ktail:zK*Real.exp (-(1/ 10 : ℝ)*(Real.log (N:ℝ))^((1 : ℝ)/ 10)) ≤
      (Real.log (N:ℝ))^(-(7/ 10 : ℝ)))
    (hGk_asymp:∀ x∈zz (z3 N),
      riemannZeta (1+wk A N k x.1)≠0 ∧
      riemannZeta (1+wk A N k x.2)≠0 ∧
      ‖Gk A N k x - (((ze N/ Real.log (z9 A N k):ℝ):ℂ)*kernel x)‖ ≤
        (ze N/ Real.log (z9 A N k))*‖kernel x‖*(Real.log (N:ℝ))^(-(7/ 10 : ℝ))) :
    ‖Nk A N k - (((ze N/ Real.log (z9 A N k):ℝ):ℂ)*(c0:ℂ))‖ ≤
      (ze N/ Real.log (z9 A N k))*(z8+1)*(Real.log (N:ℝ))^(-(7/ 10 : ℝ)):=by
  set L:=Real.log (N:ℝ)
  have hlogR_pos:0< Real.log (z9 A N k):=Real.log_pos hR_gt1
  have hWr_nn:0≤ ze N/ Real.log (z9 A N k):=by
    have:=zr N; positivity
  have hGk_meas:AEStronglyMeasurable (Gk A N k) (zn.restrict (zz (z3 N))):=by
    have hseq:∀ y:ℕ,AEStronglyMeasurable
        (fun x:ℝ × ℝ=>∏ p∈z2 (z7 N) y,(1 - ukp A N k p x))
        (zn.restrict (zz (z3 N))):=fun y=>by
      refine (continuous_finsetProd _ fun p hp=>?_).aestronglyMeasurable
      have hp_ne:(p:ℂ)≠0:=by exact_mod_cast (mem_filter.mp hp).2.ne_zero
      have hwk1:Continuous (fun x:ℝ × ℝ=>-wk A N k x.1):=by unfold wk; fun_prop
      have hwk2:Continuous (fun x:ℝ × ℝ=>-wk A N k x.2):=by unfold wk; fun_prop
      have hwk12:Continuous (fun x:ℝ × ℝ=>-(wk A N k x.1+wk A N k x.2)):=by unfold wk; fun_prop
      unfold ukp
      have hc1:Continuous (fun x:ℝ × ℝ=>(p:ℂ)^(-wk A N k x.1)):=by
        simp_rw [Complex.cpow_def_of_ne_zero hp_ne]; exact Complex.continuous_exp.comp (continuous_const.mul hwk1)
      have hc2:Continuous (fun x:ℝ × ℝ=>(p:ℂ)^(-wk A N k x.2)):=by
        simp_rw [Complex.cpow_def_of_ne_zero hp_ne]; exact Complex.continuous_exp.comp (continuous_const.mul hwk2)
      have hc12:Continuous (fun x:ℝ × ℝ=>(p:ℂ)^(-(wk A N k x.1+wk A N k x.2))):=by
        simp_rw [Complex.cpow_def_of_ne_zero hp_ne]; exact Complex.continuous_exp.comp (continuous_const.mul hwk12)
      exact continuous_const.sub (((hc1.add hc2).sub hc12).div_const _)
    refine aestronglyMeasurable_of_tendsto_ae atTop hseq ?_
    rw [ae_restrict_iff' (z6 _)]
    refine ae_of_all _ fun x hx=>?_
    exact (zp (by omega) hR_gt1 x
      (hGk_asymp x hx).1 (hGk_asymp x hx).2.1).1
  have hGk_int:IntegrableOn (Gk A N k) (zz (z3 N)) zn:=by
    have hdom:IntegrableOn (fun x:ℝ × ℝ =>
        (2*(ze N/ Real.log (z9 A N k)))*‖kernel x‖) (zz (z3 N)) zn :=
      (zc.norm.const_mul _).integrableOn
    refine hdom.mono' hGk_meas ?_
    rw [ae_restrict_iff' (z6 _)]
    refine ae_of_all _ fun x hx=>?_
    have hdiff:=(hGk_asymp x hx).2.2
    have htri:‖Gk A N k x‖ ≤
        ‖(((ze N/ Real.log (z9 A N k):ℝ):ℂ)*kernel x)‖ +
        ‖Gk A N k x - (((ze N/ Real.log (z9 A N k):ℝ):ℂ)*kernel x)‖:=by
      simpa [add_sub_cancel] using norm_add_le
        ((((ze N/ Real.log (z9 A N k):ℝ):ℂ)*kernel x))
        (Gk A N k x - (((ze N/ Real.log (z9 A N k):ℝ):ℂ)*kernel x))
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hWr_nn] at htri
    have hmul:(ze N/ Real.log (z9 A N k))*‖kernel x‖*L^(-(7/ 10 : ℝ)) ≤
        (ze N/ Real.log (z9 A N k))*‖kernel x‖ :=
      mul_le_of_le_one_right (mul_nonneg hWr_nn (norm_nonneg _)) (by linarith)
    linarith
  have hsplit:Nk A N k - (((ze N/ Real.log (z9 A N k):ℝ):ℂ)*(c0:ℂ)) =
      (∫ x in zz (z3 N),
        (Gk A N k x - (((ze N/ Real.log (z9 A N k):ℝ):ℂ)*kernel x)) ∂zn) -
      (((ze N/ Real.log (z9 A N k):ℝ):ℂ) *
        ∫ x in (zz (z3 N))ᶜ,kernel x ∂zn):=by
    unfold Nk
    rw [integral_sub hGk_int (zc.const_mul _).integrableOn,
      integral_const_mul,← xq]
    have hadd:=MeasureTheory.integral_add_compl (z6 (z3 N)) zc
    linear_combination (((ze N/ Real.log (z9 A N k):ℝ):ℂ))*hadd
  rw [hsplit]
  have h1:‖∫ x in zz (z3 N),
      (Gk A N k x - (((ze N/ Real.log (z9 A N k):ℝ):ℂ)*kernel x)) ∂zn‖ ≤
      (ze N/ Real.log (z9 A N k))*z8*L^(-(7/ 10 : ℝ)):=by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hint_diff:IntegrableOn (fun x =>
        ‖Gk A N k x - (((ze N/ Real.log (z9 A N k):ℝ):ℂ)*kernel x)‖)
        (zz (z3 N)) zn :=
      (hGk_int.sub (zc.const_mul _).integrableOn).norm
    have hdom2:Integrable (fun x:ℝ × ℝ =>
        ((ze N/ Real.log (z9 A N k))*L^(-(7/ 10 : ℝ)))*‖kernel x‖) zn :=
      zc.norm.const_mul _
    calc
      ∫ x in zz (z3 N),
          ‖Gk A N k x - (((ze N/ Real.log (z9 A N k):ℝ):ℂ)*kernel x)‖ ∂zn
          ≤ ∫ x in zz (z3 N),
              ((ze N/ Real.log (z9 A N k))*L^(-(7/ 10 : ℝ)))*‖kernel x‖ ∂zn:=by
            refine setIntegral_mono_on hint_diff hdom2.integrableOn (z6 _) fun x hx=>?_
            have:=(hGk_asymp x hx).2.2; linarith
      _≤ ∫ x:ℝ × ℝ,
              ((ze N/ Real.log (z9 A N k))*L^(-(7/ 10 : ℝ)))*‖kernel x‖ ∂zn :=
            setIntegral_le_integral hdom2 (ae_of_all _ fun _=>by positivity)
      _=(ze N/ Real.log (z9 A N k))*z8*L^(-(7/ 10 : ℝ)):=by
            rw [integral_const_mul]; unfold z8; ring
  have h2:‖(((ze N/ Real.log (z9 A N k):ℝ):ℂ) *
      ∫ x in (zz (z3 N))ᶜ,kernel x ∂zn)‖ ≤
      (ze N/ Real.log (z9 A N k))*L^(-(7/ 10 : ℝ)):=by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hWr_nn]
    refine mul_le_mul_of_nonneg_left ?_ hWr_nn
    have hT_nn:0≤ z3 N:=by unfold z3; positivity
    have hsqrtT:Real.sqrt (z3 N)=L^((1 : ℝ)/ 10):=by
      unfold z3
      rw [Real.sqrt_eq_rpow,← Real.rpow_mul (by linarith)]; congr 1; norm_num
    calc
      ‖∫ x in (zz (z3 N))ᶜ,kernel x ∂zn‖
          ≤ ∫ x in (zz (z3 N))ᶜ,‖kernel x‖ ∂zn:=norm_integral_le_integral_norm _
      _≤ zK*Real.exp (-(1/ 10 : ℝ)*Real.sqrt (z3 N)) :=
            xP hT_nn
      _=zK*Real.exp (-(1/ 10 : ℝ)*L^((1 : ℝ)/ 10)):=by rw [hsqrtT]
      _≤ L^(-(7/ 10 : ℝ)):=hL_ktail
  calc
    ‖(∫ x in zz (z3 N),
          (Gk A N k x - (((ze N/ Real.log (z9 A N k):ℝ):ℂ)*kernel x)) ∂zn) -
        (((ze N/ Real.log (z9 A N k):ℝ):ℂ) *
          ∫ x in (zz (z3 N))ᶜ,kernel x ∂zn)‖
        ≤ ‖∫ x in zz (z3 N),
            (Gk A N k x - (((ze N/ Real.log (z9 A N k):ℝ):ℂ)*kernel x)) ∂zn‖ +
          ‖(((ze N/ Real.log (z9 A N k):ℝ):ℂ) *
            ∫ x in (zz (z3 N))ᶜ,kernel x ∂zn)‖:=norm_sub_le _ _
    _≤ (ze N/ Real.log (z9 A N k))*z8*L^(-(7/ 10 : ℝ)) +
        (ze N/ Real.log (z9 A N k))*L^(-(7/ 10 : ℝ)):=add_le_add h1 h2
    _=(ze N/ Real.log (z9 A N k))*(z8+1)*L^(-(7/ 10 : ℝ)):=by ring
lemma xd {A:ℝ} (hA:1≤ A) :
    ∀ᶠ N:ℕ in atTop,zM A N:=by
  obtain ⟨C_z,hCz_pos,δ_z,hδz_pos,hZratio⟩:=xU
  filter_upwards [eventually_ge_atTop 2,
    xG (xB (C_z:=C_z) hA hδz_pos),
    xG xA] with N hN2 hL1 hL2_pack
  rcases hL1 with ⟨hL2,hL200,hL_K2,hL_w16,hL_Kw,hL_KKp,hL_2KpN,hL_wR,hL_logR1,
    hL_dz,hL_Cz,hL_tiny,hL_Cgt,hL_07⟩
  rcases hL2_pack with ⟨hL_ktail,hL_eps,hL_Keps,hL_8BK,hL_32B2,hL_crt,hL_trunc,hL_exp14⟩
  set L:=Real.log (N:ℝ)
  have hNpos:(0 : ℝ)< N:=by positivity
  have hN1:(1 : ℝ)≤ N:=by exact_mod_cast (show 1≤ N by omega)
  have hN_exp2:Real.exp 2≤ (N:ℝ):=by
    calc Real.exp 2≤ Real.exp L:=Real.exp_le_exp.mpr hL2
      _=(N:ℝ):=Real.exp_log hNpos
  have hw_lo:0.1*L≤ (z7 N:ℝ):=by
    unfold z7 yD
    have:=Nat.lt_floor_add_one (0.15*L)
    linarith
  have hw_hi:(z7 N:ℝ)≤ 0.15*L:=Nat.floor_le (by unfold yD; linarith)
  have hw16:16≤ z7 N:=by
    have : (16 : ℝ)≤ (z7 N:ℝ):=by
      unfold z7 yD
      linarith [Nat.lt_floor_add_one (0.15*L)]
    exact_mod_cast this
  have hK2:2≤ z0 N:=Nat.le_floor hL_K2
  have hK_le:(z0 N:ℝ)≤ L^((1 : ℝ)/ 1000):=Nat.floor_le (by positivity)
  have hKw:z0 N< z7 N:=by
    have : (z0 N:ℝ)< (z7 N:ℝ):=by
      unfold z7 yD
      linarith [Nat.lt_floor_add_one (0.15*L)]
    exact_mod_cast this
  have hKp_eq:(N:ℝ)^((1 : ℝ)/ 100)=Real.exp (L/ 100):=by
    rw [Real.rpow_def_of_pos hNpos]; congr 1; ring
  have hKKp:z0 N< yI N:=by
    have : (z0 N:ℝ)< (yI N:ℝ):=by
      unfold yI
      rw [hKp_eq]
      linarith [Nat.lt_floor_add_one (Real.exp (L/ 100))]
    exact_mod_cast this
  have h2KpN:2*yI N< N:=by
    have h1:(yI N:ℝ)≤ Real.exp (L/ 100):=by
      unfold yI; rw [← hKp_eq]; exact Nat.floor_le (by positivity)
    have h2:(2*(yI N:ℝ))< (N:ℝ):=by
      rw [← Real.exp_log hNpos]; linarith
    exact_mod_cast h2
  have hlogR_lb:∀ k:Fin (z0 N),
      L^((19 : ℝ)/ 20)/ (100*(A+1))≤ Real.log (z9 A N k):=by
    intro k
    rw [xV A (by omega) k]
    have hk_le:((k.1+1 : ℕ):ℝ)≤ L^((1 : ℝ)/ 1000) :=
      (Nat.cast_le.mpr k.2).trans hK_le
    have hk50:((k.1+1 : ℕ):ℝ)^50≤ L^((1 : ℝ)/ 20):=by
      calc
        ((k.1+1 : ℕ):ℝ)^50≤ (L^((1 : ℝ)/ 1000))^50:=by gcongr
        _=L^((1 : ℝ)/ 20):=by
            rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith)]; congr 1; norm_num
    have hden_le:100*(A+1)*((k.1+1 : ℕ):ℝ)^50≤ 100*(A+1)*L^((1 : ℝ)/ 20):=by
      gcongr
    have hL_split:L/ (100*(A+1)*L^((1 : ℝ)/ 20))=L^((19 : ℝ)/ 20)/ (100*(A+1)):=by
      have h1:L=L^((19 : ℝ)/ 20)*L^((1 : ℝ)/ 20):=by
        rw [← Real.rpow_add (by linarith)]; norm_num
      have hne:L^((1 : ℝ)/ 20)≠0:=(Real.rpow_pos_of_pos (by linarith) _).ne'
      calc
        L/ (100*(A+1)*L^((1 : ℝ)/ 20))
            = (L^((19 : ℝ)/ 20)*L^((1 : ℝ)/ 20))/ (100*(A+1)*L^((1 : ℝ)/ 20)):=by
              rw [← h1]
        _=L^((19 : ℝ)/ 20)/ (100*(A+1)):=by field_simp
    rw [← hL_split]
    exact div_le_div_of_nonneg_left (by linarith) (by positivity) hden_le
  have hR_cond:∀ k:Fin (z0 N),yD N≤ z9 A N k∧1< z9 A N k:=by
    intro k
    have hRpos:0< z9 A N k:=by rw [wu]; exact Real.rpow_pos_of_pos hNpos _
    have hlog1:1< Real.log (z9 A N k):=lt_of_lt_of_le hL_logR1 (hlogR_lb k)
    constructor
    · unfold yD
      calc
        0.15*L≤ Real.exp (L^((19 : ℝ)/ 20)/ (100*(A+1))):=hL_wR
        _≤ Real.exp (Real.log (z9 A N k)):=Real.exp_le_exp.mpr (hlogR_lb k)
        _=z9 A N k:=Real.exp_log hRpos
    · calc (1 : ℝ)< Real.exp 1:=by linarith [Real.add_one_le_exp (1 : ℝ)]
        _< Real.exp (Real.log (z9 A N k)):=Real.exp_lt_exp.mpr hlog1
        _=z9 A N k:=Real.exp_log hRpos
  have hwk_bound:∀ (k:Fin (z0 N)) (t:ℝ),t∈Set.Icc (-(z3 N)) (z3 N) →
      ‖wk A N k t‖≤ 200*(A+1)*L^(-(3/ 4 : ℝ)):=by
    intro k t ht
    have htabs:|t|≤ L^((1 : ℝ)/ 5):=abs_le.mpr ht
    have h1L:(1 : ℝ)≤ L^((1 : ℝ)/ 5):=Real.one_le_rpow (by linarith) (by norm_num)
    have hnum:‖(1 : ℂ)+Complex.I*(t:ℂ)‖≤ 2*L^((1 : ℝ)/ 5):=by
      calc
        ‖(1 : ℂ)+Complex.I*(t:ℂ)‖≤ ‖(1 : ℂ)‖+‖Complex.I*(t:ℂ)‖:=norm_add_le _ _
        _=1+|t|:=by simp [Complex.norm_real]
        _≤ 2*L^((1 : ℝ)/ 5):=by linarith
    have hlogR_pos:0< Real.log (z9 A N k):=Real.log_pos (hR_cond k).2
    unfold wk
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hlogR_pos.le]
    have hquot:(2*L^((1 : ℝ)/ 5))/ (L^((19 : ℝ)/ 20)/ (100*(A+1))) =
        200*(A+1)*L^(-(3/ 4 : ℝ)):=by
      have hsub:L^((1 : ℝ)/ 5)/ L^((19 : ℝ)/ 20)=L^(-(3/ 4 : ℝ)):=by
        rw [← Real.rpow_sub (by linarith)]; congr 1; norm_num
      rw [div_div_eq_mul_div,
        show 2*L^((1 : ℝ)/ 5)*(100*(A+1))/ L^((19 : ℝ)/ 20) =
          200*(A+1)*(L^((1 : ℝ)/ 5)/ L^((19 : ℝ)/ 20)) by ring,hsub]
    rw [← hquot]
    exact div_le_div₀ (by positivity) hnum (by positivity) (hlogR_lb k)
  have hGk_asymp:∀ k:Fin (z0 N),∀ x∈zz (z3 N),
      riemannZeta (1+wk A N k x.1)≠0 ∧
      riemannZeta (1+wk A N k x.2)≠0 ∧
      ‖Gk A N k x - (((ze N/ Real.log (z9 A N k):ℝ):ℂ)*kernel x)‖ ≤
        (ze N/ Real.log (z9 A N k))*‖kernel x‖*L^(-(7/ 10 : ℝ)):=fun k _ hx =>
    wq hA hCz_pos hZratio hL2 hw16 hw_lo hw_hi k (hR_cond k).2
      (hwk_bound k) hL_dz hL_Cz hL_tiny hL_Cgt hL_07 hx
  have hNk_asymp:∀ k:Fin (z0 N),
      ‖Nk A N k - (((ze N/ Real.log (z9 A N k):ℝ):ℂ)*(c0:ℂ))‖ ≤
        (ze N/ Real.log (z9 A N k))*(z8+1)*L^(-(7/ 10 : ℝ)):=fun k =>
    wp hL2 hw16 k (hR_cond k).2 hL_07 hL_ktail (hGk_asymp k)
  have hKeps:(z0 N:ℝ)*((4*(z8+1)/ c0)*L^(-(7/ 10 : ℝ)))≤ 1/ 10:=by
    refine le_trans ?_ hL_Keps
    gcongr
    have:=zX; have:=y4; positivity
  have h8BK:8*zf*(z0 N:ℝ)≤ (z7 N:ℝ):=by
    have hB0:0≤ zf:=by linarith [zH]
    calc
      8*zf*(z0 N:ℝ)≤ 8*zf*L^((1 : ℝ)/ 1000):=by gcongr
      _≤ 0.1*L:=hL_8BK
      _≤ (z7 N:ℝ):=hw_lo
  have h32B2:32*zf^2*(z0 N:ℝ)^2/ (z7 N:ℝ)≤ 1/ 10:=by
    refine le_trans ?_ hL_32B2
    have hB0:0≤ zf:=by linarith [zH]
    exact div_le_div₀ (by positivity) (by gcongr) (by linarith) hw_lo
  have hcrt_bound:(N:ℝ)^((1 : ℝ)/ 5)*(∏ k:Fin (z0 N),(z9 A N k)^2) /
        ((N:ℝ)/ (z4 N:ℝ))*(2*L)^(z0 N) ≤
      (1/ 8 : ℝ)*Real.exp (-(1/ 40 : ℝ)*L^((1 : ℝ)/ 10)):=by
    have hW_le:(z4 N:ℝ)≤ (N:ℝ)^(0.25 : ℝ):=xI hN1
    have hR2_le:∏ k:Fin (z0 N),(z9 A N k)^2≤ (N:ℝ)^((1 : ℝ)/ 20) :=
      wF hA (by omega)
    have hratio_le:(N:ℝ)^((1 : ℝ)/ 5)*(∏ k:Fin (z0 N),(z9 A N k)^2) /
          ((N:ℝ)/ (z4 N:ℝ))≤ Real.exp (-(1/ 2 : ℝ)*L):=by
      have h1:(N:ℝ)^((1 : ℝ)/ 5)*(∏ k:Fin (z0 N),(z9 A N k)^2) /
            ((N:ℝ)/ (z4 N:ℝ)) =
          ((N:ℝ)^((1 : ℝ)/ 5)*(∏ k:Fin (z0 N),(z9 A N k)^2)*(z4 N:ℝ))/ (N:ℝ):=by
        have hWne:(z4 N:ℝ)≠0:=by exact_mod_cast (w6 N).ne'
        field_simp
      rw [h1]
      calc
        ((N:ℝ)^((1 : ℝ)/ 5)*(∏ k:Fin (z0 N),(z9 A N k)^2)*(z4 N:ℝ))/ (N:ℝ)
            ≤ ((N:ℝ)^((1 : ℝ)/ 5)*(N:ℝ)^((1 : ℝ)/ 20)*(N:ℝ)^(0.25 : ℝ))/ (N:ℝ):=by
              gcongr
        _=(N:ℝ)^(-(1/ 2 : ℝ)):=by
              rw [← Real.rpow_add hNpos,← Real.rpow_add hNpos]
              conv_lhs=>rhs; rw [← Real.rpow_one (N:ℝ)]
              rw [← Real.rpow_sub hNpos]; congr 1; norm_num
        _=Real.exp (-(1/ 2 : ℝ)*L):=by
              rw [Real.rpow_def_of_pos hNpos]; congr 1; ring
    have h2L_pow:(2*L)^(z0 N)≤ Real.exp (L^((1 : ℝ)/ 1000)*Real.log (2*L)):=by
      have h2L_pos:0< 2*L:=by linarith only [hL2]
      rw [← Real.rpow_natCast,Real.rpow_def_of_pos h2L_pos]
      apply Real.exp_le_exp.mpr
      have hlog2L_nn:0≤ Real.log (2*L):=Real.log_nonneg (by linarith only [hL2])
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hK_le hlog2L_nn
    calc
      (N:ℝ)^((1 : ℝ)/ 5)*(∏ k:Fin (z0 N),(z9 A N k)^2) /
          ((N:ℝ)/ (z4 N:ℝ))*(2*L)^(z0 N)
          ≤ Real.exp (-(1/ 2 : ℝ)*L)*Real.exp (L^((1 : ℝ)/ 1000)*Real.log (2*L)) :=
            mul_le_mul hratio_le h2L_pow (by positivity) (Real.exp_pos _).le
      _=Real.exp (L^((1 : ℝ)/ 1000)*Real.log (2*L) - (1/ 2 : ℝ)*L):=by
            rw [← Real.exp_add]; congr 1; ring
      _≤ Real.exp (-Real.log 8 - (1/ 40 : ℝ)*L^((1 : ℝ)/ 10)) :=
            Real.exp_le_exp.mpr (by linarith only [hL_crt])
      _=(1/ 8 : ℝ)*Real.exp (-(1/ 40 : ℝ)*L^((1 : ℝ)/ 10)):=by
            rw [show -Real.log 8 - (1/ 40 : ℝ)*L^((1 : ℝ)/ 10) =
                -Real.log 8+(-(1/ 40 : ℝ)*L^((1 : ℝ)/ 10)) by ring,
              Real.exp_add,Real.exp_neg,Real.exp_log (by norm_num)]; ring
  have htrunc_bound :
      Real.exp (3*(z0 N:ℝ)*(2*Real.log L+45)) *
        (2*(z0 N:ℝ)*zA*Real.exp (-(1/ 10 : ℝ)*Real.sqrt (z3 N))) *
        (2*L)^(z0 N) ≤
      (1/ 8 : ℝ)*Real.exp (-(1/ 40 : ℝ)*L^((1 : ℝ)/ 10)):=by
    have hsqrtT:Real.sqrt (z3 N)=L^((1 : ℝ)/ 10):=by
      unfold z3
      rw [Real.sqrt_eq_rpow,← Real.rpow_mul (by linarith only [hL2])]; congr 1; norm_num
    rw [hsqrtT]
    have h1:Real.exp (3*(z0 N:ℝ)*(2*Real.log L+45)) ≤
        Real.exp (3*L^((1 : ℝ)/ 1000)*(2*Real.log L+45)):=by
      apply Real.exp_le_exp.mpr
      have hlogL_nn:0≤ Real.log L:=Real.log_nonneg (by linarith only [hL2])
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK_le (by norm_num)) (by linarith only [hlogL_nn])
    have h2:2*(z0 N:ℝ)*zA ≤
        Real.exp (Real.log (2*L^((1 : ℝ)/ 1000)*zA+1)):=by
      rw [Real.exp_log (by positivity [yC])]
      have hle:2*(z0 N:ℝ)*zA≤ 2*L^((1 : ℝ)/ 1000)*zA :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK_le (by norm_num)) yC
      linarith only [hle]
    have h3:(2*L)^(z0 N)≤ Real.exp (L^((1 : ℝ)/ 1000)*Real.log (2*L)):=by
      have h2L_pos:0< 2*L:=by linarith only [hL2]
      rw [← Real.rpow_natCast,Real.rpow_def_of_pos h2L_pos]
      apply Real.exp_le_exp.mpr
      have hlog2L_nn:0≤ Real.log (2*L):=Real.log_nonneg (by linarith only [hL2])
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hK_le hlog2L_nn
    calc
      Real.exp (3*(z0 N:ℝ)*(2*Real.log L+45)) *
          (2*(z0 N:ℝ)*zA*Real.exp (-(1/ 10 : ℝ)*L^((1 : ℝ)/ 10))) *
          (2*L)^(z0 N)
          = Real.exp (3*(z0 N:ℝ)*(2*Real.log L+45)) *
            (2*(z0 N:ℝ)*zA)*(2*L)^(z0 N) *
            Real.exp (-(1/ 10 : ℝ)*L^((1 : ℝ)/ 10)):=by ring
      _≤ Real.exp (3*L^((1 : ℝ)/ 1000)*(2*Real.log L+45)) *
            Real.exp (Real.log (2*L^((1 : ℝ)/ 1000)*zA+1)) *
            Real.exp (L^((1 : ℝ)/ 1000)*Real.log (2*L)) *
            Real.exp (-(1/ 10 : ℝ)*L^((1 : ℝ)/ 10)):=by
            gcongr; positivity [yC]
      _=Real.exp (3*L^((1 : ℝ)/ 1000)*(2*Real.log L+45) +
            Real.log (2*L^((1 : ℝ)/ 1000)*zA+1) +
            L^((1 : ℝ)/ 1000)*Real.log (2*L) - (1/ 10 : ℝ)*L^((1 : ℝ)/ 10)):=by
            rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]; congr 1; ring
      _≤ Real.exp (-Real.log 8 - (1/ 40 : ℝ)*L^((1 : ℝ)/ 10)) :=
            Real.exp_le_exp.mpr (by linarith only [hL_trunc])
      _=(1/ 8 : ℝ)*Real.exp (-(1/ 40 : ℝ)*L^((1 : ℝ)/ 10)):=by
            rw [show -Real.log 8 - (1/ 40 : ℝ)*L^((1 : ℝ)/ 10) =
                -Real.log 8+(-(1/ 40 : ℝ)*L^((1 : ℝ)/ 10)) by ring,
              Real.exp_add,Real.exp_neg,Real.exp_log (by norm_num)]; ring
  exact ⟨hN_exp2,hw16,hK2,hKw,hKKp,h2KpN,hR_cond,hGk_asymp,hNk_asymp,hL_eps,hKeps,
    h8BK,h32B2,hcrt_bound,htrunc_bound,hL_exp14⟩
end
end Erdos413Sieve
namespace Erdos413Sieve
open Finset Filter Topology Complex Real MeasureTheory
open Erdos413Bump Erdos413Mertens
open scoped BigOperators
noncomputable section
def vkp (A:ℝ) (N:ℕ) (k:Fin (z0 N)) (p:ℕ) (x:ℝ × ℝ):ℂ :=
  ukp A N k p x/ (1 - ukp A N k p x)
def Qp (A:ℝ) (N p:ℕ) (ω : Fin (z0 N)→ℝ × ℝ):ℂ :=
  (1 - ∑ k:Fin (z0 N),ukp A N k p (ω k)) /
    ∏ k:Fin (z0 N),(1 - ukp A N k p (ω k))
def zu (N v7 v6:ℕ) (k:Fin (z0 N)):Finset ℕ :=
  v6.primeFactors.filter (fun p=>(p:ℤ)∣((v7:ℤ) - ((k.1+1 : ℕ):ℤ)))
def zb (A:ℝ) (N v7 v6:ℕ) (k:Fin (z0 N)) (x:ℝ × ℝ):ℂ :=
  ∏ p∈zu N v7 v6 k,
    (1 - (p:ℂ)^(-wk A N k x.1))*(1 - (p:ℂ)^(-wk A N k x.2))
def Ik (A:ℝ) (N v7 v6:ℕ) (k:Fin (z0 N)):ℝ :=
  (1/ c0)*∫ x in zz (z3 N),‖kernel x‖*‖zb A N v7 v6 k x‖ ∂zn
def Fy (A:ℝ) (N v7 v6 y:ℕ) (ω : Fin (z0 N)→ℝ × ℝ):ℂ :=
  ((v6:ℂ)⁻¹) *
    (∏ k:Fin (z0 N),Gk A N k (ω k)*zb A N v7 v6 k (ω k)) *
    (∏ p∈(z2 (z7 N) y).filter (fun p=>¬ p∣v6),Qp A N p ω) *
    (∏ p∈v6.primeFactors,∏ k:Fin (z0 N),(1+vkp A N k p (ω k)))
lemma zD {A:ℝ} {N:ℕ} (hR:zM A N)
    (k:Fin (z0 N)) {p:ℕ} (hp_gt:z7 N< p) (x:ℝ × ℝ) :
    ‖ukp A N k p x‖≤ (3 : ℝ)/ (p:ℝ) ∧
    1 - ukp A N k p x≠0 ∧
    ‖vkp A N k p x‖≤ (4 : ℝ)/ (p:ℝ):=by
  have hp17:17≤ p:=by have:=hR.2.1; omega
  have hp_pos:(0 : ℝ)< p:=by positivity
  have hp1:(1 : ℝ)≤ p:=by exact_mod_cast (show 1≤ p by omega)
  have hlogR_pos:0< Real.log (z9 A N k):=Real.log_pos (hR.2.2.2.2.2.2.1 k).2
  have hcpow_le1:∀ t:ℝ,‖(p:ℂ)^(-wk A N k t)‖≤ 1:=fun t=>by
    rw [yf (by omega)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hp1 (neg_nonpos.mpr (by positivity))
  have hcpow12_le1:‖(p:ℂ)^(-(wk A N k x.1+wk A N k x.2))‖≤ 1:=by
    rw [← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hp_pos,Complex.neg_re,
      Complex.add_re,w9,w9]
    exact Real.rpow_le_one_of_one_le_of_nonpos hp1 (neg_nonpos.mpr (by positivity))
  have hukp:‖ukp A N k p x‖≤ (3 : ℝ)/ (p:ℝ):=by
    unfold ukp
    rw [norm_div,Complex.norm_natCast]
    have hnum:‖(p:ℂ)^(-wk A N k x.1)+(p:ℂ)^(-wk A N k x.2) -
        (p:ℂ)^(-(wk A N k x.1+wk A N k x.2))‖≤ 3:=by
      calc
        _≤ ‖(p:ℂ)^(-wk A N k x.1)+(p:ℂ)^(-wk A N k x.2)‖ +
            ‖(p:ℂ)^(-(wk A N k x.1+wk A N k x.2))‖:=norm_sub_le _ _
        _≤ ‖(p:ℂ)^(-wk A N k x.1)‖+‖(p:ℂ)^(-wk A N k x.2)‖ +
            ‖(p:ℂ)^(-(wk A N k x.1+wk A N k x.2))‖:=by gcongr; exact norm_add_le _ _
        _≤ 1+1+1:=by linarith [hcpow_le1 x.1,hcpow_le1 x.2,hcpow12_le1]
        _=3:=by norm_num
    exact div_le_div_of_nonneg_right hnum hp_pos.le
  have h1u_lb:(3/ 4 : ℝ)≤ ‖1 - ukp A N k p x‖:=by
    have htri:‖(1 : ℂ)‖≤ ‖1 - ukp A N k p x‖+‖ukp A N k p x‖:=by
      simpa [sub_add_cancel] using norm_add_le (1 - ukp A N k p x) (ukp A N k p x)
    rw [norm_one] at htri
    have hp3:(3 : ℝ)/ (p:ℝ)≤ 1/ 4:=by
      rw [div_le_div_iff₀ hp_pos (by norm_num)]
      have : (17 : ℝ)≤ p:=by exact_mod_cast hp17
      linarith
    linarith
  have h1u_ne:1 - ukp A N k p x≠0:=by
    intro h; rw [h,norm_zero] at h1u_lb; linarith
  have hvkp:‖vkp A N k p x‖≤ (4 : ℝ)/ (p:ℝ):=by
    unfold vkp
    rw [norm_div]
    calc
      ‖ukp A N k p x‖/ ‖1 - ukp A N k p x‖≤ ((3 : ℝ)/ (p:ℝ))/ (3/ 4) :=
        div_le_div₀ (by positivity) hukp (by norm_num) h1u_lb
      _=4/ (p:ℝ):=by ring
  exact ⟨hukp,h1u_ne,hvkp⟩
lemma xE {A:ℝ} {N:ℕ} (hR:zM A N)
    {p:ℕ} (hp_gt:z7 N< p) (ω : Fin (z0 N)→ℝ × ℝ) :
    ‖Qp A N p ω - 1‖≤ 32*(z0 N:ℝ)^2/ (p:ℝ)^2:=by
  have hne:∀ k∈(Finset.univ:Finset (Fin (z0 N))),1 - ukp A N k p (ω k)≠0 :=
    fun k _=>(zD hR k hp_gt (ω k)).2.1
  have hid:=xo Finset.univ (fun k=>ukp A N k p (ω k)) hne
  change Qp A N p ω=1+∑ S∈(Finset.univ:Finset (Fin (z0 N))).powerset.filter (fun S=>2≤ S.card),
    (1 - (S.card:ℂ))*∏ k∈S,vkp A N k p (ω k) at hid
  rw [hid,add_sub_cancel_left]
  refine (norm_sum_le _ _).trans ?_
  have hterm:∀ S∈(Finset.univ:Finset (Fin (z0 N))).powerset.filter (fun S=>2≤ S.card),
      ‖(1 - (S.card:ℂ))*∏ k∈S,vkp A N k p (ω k)‖ ≤
        ((S.card:ℝ) - 1)*((4 : ℝ)/ (p:ℝ))^S.card:=by
    intro S hS
    have h2:2≤ S.card:=(mem_filter.mp hS).2
    rw [norm_mul,norm_prod]
    have h1S:‖(1 : ℂ) - (S.card:ℂ)‖=(S.card:ℝ) - 1:=by
      have hcast:(1 : ℂ) - (S.card:ℂ)=(((1 - (S.card:ℝ):ℝ)):ℂ):=by push_cast; rfl
      rw [hcast,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast (show 1≤ S.card by omega)))]
      ring
    rw [h1S]
    refine mul_le_mul_of_nonneg_left ?_ (by
      have h2r:(2 : ℝ)≤ S.card:=by exact_mod_cast h2
      linarith)
    calc
      ∏ k∈S,‖vkp A N k p (ω k)‖≤ ∏ _k∈S,((4 : ℝ)/ (p:ℝ)) :=
        prod_le_prod (fun _ _=>norm_nonneg _) fun k _=>(zD hR k hp_gt (ω k)).2.2
      _=((4 : ℝ)/ (p:ℝ))^S.card:=prod_const _
  refine (sum_le_sum hterm).trans ?_
  have hKx:(z0 N:ℝ)*((4 : ℝ)/ (p:ℝ))≤ 1:=by
    have h8BK:=hR.2.2.2.2.2.2.2.2.2.2.2.1
    have hB1:=zH
    have hp_ge:(z7 N:ℝ)≤ (p:ℝ):=by exact_mod_cast hp_gt.le
    have hp_pos:(0 : ℝ)< p:=by have:=hR.2.1; exact_mod_cast (show 0< p by omega)
    rw [mul_div_assoc',div_le_one hp_pos]
    nlinarith [Nat.cast_nonneg (α:=ℝ) (z0 N)]
  have hsum:=x5 (z0 N) (by positivity) hKx
  refine hsum.trans_eq ?_; ring
lemma yb (A:ℝ) (N:ℕ) (k:Fin (z0 N)) {p:ℕ} (hp0:p≠0) :
    Continuous (fun x:ℝ × ℝ=>ukp A N k p x):=by
  have hp_ne:(p:ℂ)≠0:=by exact_mod_cast hp0
  unfold ukp wk
  have hc1:Continuous (fun x:ℝ × ℝ =>
      (p:ℂ)^(-((1+Complex.I*(x.1 : ℂ))/ (Real.log (z9 A N k):ℂ)))):=by
    simp_rw [Complex.cpow_def_of_ne_zero hp_ne]; fun_prop
  have hc2:Continuous (fun x:ℝ × ℝ =>
      (p:ℂ)^(-((1+Complex.I*(x.2 : ℂ))/ (Real.log (z9 A N k):ℂ)))):=by
    simp_rw [Complex.cpow_def_of_ne_zero hp_ne]; fun_prop
  have hc12:Continuous (fun x:ℝ × ℝ =>
      (p:ℂ)^(-(((1+Complex.I*(x.1 : ℂ))/ (Real.log (z9 A N k):ℂ)) +
        ((1+Complex.I*(x.2 : ℂ))/ (Real.log (z9 A N k):ℂ))))):=by
    simp_rw [Complex.cpow_def_of_ne_zero hp_ne]; fun_prop
  exact ((hc1.add hc2).sub hc12).div_const _
lemma yU {A:ℝ} {N:ℕ} (hR:zM A N)
    (k:Fin (z0 N)) {p:ℕ} (hp_gt:z7 N< p) :
    Continuous (fun x:ℝ × ℝ=>vkp A N k p x):=by
  have hp0:p≠0:=by have:=hR.2.1; omega
  have hu:=yb A N k hp0
  unfold vkp
  exact Continuous.div hu (continuous_const.sub hu) fun x =>
    (zD hR k hp_gt x).2.1
lemma zJ {A:ℝ} {N:ℕ} (hR:zM A N)
    (k:Fin (z0 N)) :
    AEStronglyMeasurable (Gk A N k) (zn.restrict (zz (z3 N))):=by
  have hseq:∀ y:ℕ,AEStronglyMeasurable
      (fun x:ℝ × ℝ=>∏ p∈z2 (z7 N) y,(1 - ukp A N k p x))
      (zn.restrict (zz (z3 N))):=fun y =>
    (continuous_finsetProd _ fun p hp =>
      continuous_const.sub (yb A N k (mem_filter.mp hp).2.ne_zero)).aestronglyMeasurable
  refine aestronglyMeasurable_of_tendsto_ae atTop hseq ?_
  rw [ae_restrict_iff' (z6 _)]
  refine ae_of_all _ fun x hx=>?_
  exact (zp (by have:=hR.2.1; omega) (hR.2.2.2.2.2.2.1 k).2 x
    (hR.2.2.2.2.2.2.2.1 k x hx).1 (hR.2.2.2.2.2.2.2.1 k x hx).2.1).1
lemma yA {A:ℝ} {N:ℕ} (hR:zM A N)
    (k:Fin (z0 N)) :
    AEStronglyMeasurable (fun ω : Fin (z0 N)→ℝ × ℝ=>Gk A N k (ω k))
      ((PK (z0 N)).restrict (y0 (z0 N) (z3 N))):=by
  have hseq:∀ y:ℕ,AEStronglyMeasurable
      (fun ω : Fin (z0 N)→ℝ × ℝ=>∏ p∈z2 (z7 N) y,(1 - ukp A N k p (ω k)))
      ((PK (z0 N)).restrict (y0 (z0 N) (z3 N))):=fun y =>
    (continuous_finsetProd _ fun p hp =>
      continuous_const.sub ((yb A N k (mem_filter.mp hp).2.ne_zero).comp
        (continuous_apply k))).aestronglyMeasurable
  refine aestronglyMeasurable_of_tendsto_ae atTop hseq ?_
  rw [ae_restrict_iff' (y8 _ _)]
  refine ae_of_all _ fun ω hω=>?_
  exact (zp (by have:=hR.2.1; omega) (hR.2.2.2.2.2.2.1 k).2 (ω k)
    (hR.2.2.2.2.2.2.2.1 k (ω k) (hω k (Set.mem_univ k))).1
    (hR.2.2.2.2.2.2.2.1 k (ω k) (hω k (Set.mem_univ k))).2.1).1
lemma y5 {A:ℝ} {N:ℕ} (hR:zM A N) (k:Fin (z0 N))
    {x:ℝ × ℝ} (hx:x∈zz (z3 N)) :
    ‖Gk A N k x‖≤ 2*(ze N/ Real.log (z9 A N k))*‖kernel x‖:=by
  have hlogR_pos:0< Real.log (z9 A N k):=Real.log_pos (hR.2.2.2.2.2.2.1 k).2
  have hM_nn:0≤ ze N/ Real.log (z9 A N k):=by have:=zr N; positivity
  have hL1:1≤ Real.log (N:ℝ):=by
    have : 2≤ Real.log (N:ℝ):=by
      calc (2 : ℝ)=Real.log (Real.exp 2):=(Real.log_exp 2).symm
        _≤ Real.log (N:ℝ):=Real.log_le_log (Real.exp_pos 2) hR.1
    linarith
  have hL07:(Real.log (N:ℝ))^(-(7/ 10 : ℝ))≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
  have hdiff:=(hR.2.2.2.2.2.2.2.1 k x hx).2.2
  have htri:‖Gk A N k x‖≤ (ze N/ Real.log (z9 A N k))*‖kernel x‖ +
      ‖Gk A N k x - (((ze N/ Real.log (z9 A N k):ℝ):ℂ)*kernel x)‖:=by
    have h0:=norm_add_le (((ze N/ Real.log (z9 A N k):ℝ):ℂ)*kernel x)
      (Gk A N k x - (((ze N/ Real.log (z9 A N k):ℝ):ℂ)*kernel x))
    rw [add_sub_cancel,norm_mul,Complex.norm_real,Real.norm_of_nonneg hM_nn] at h0
    exact h0
  have hmul:(ze N/ Real.log (z9 A N k))*‖kernel x‖*(Real.log (N:ℝ))^(-(7/ 10 : ℝ)) ≤
      (ze N/ Real.log (z9 A N k))*‖kernel x‖ :=
    mul_le_of_le_one_right (mul_nonneg hM_nn (norm_nonneg _)) hL07
  linarith
lemma x0 {A:ℝ} {N:ℕ} (hR:zM A N) (k:Fin (z0 N))
    {x:ℝ × ℝ} (hx:x∈zz (z3 N)) :
    ‖Gk A N k x‖≤ 2*(ze N/ Real.log (z9 A N k))*((1+z3 N)^2/ 2):=by
  have hlogR_pos:0< Real.log (z9 A N k):=Real.log_pos (hR.2.2.2.2.2.2.1 k).2
  have hM_nn:0≤ ze N/ Real.log (z9 A N k):=by have:=zr N; positivity
  have hT_nn:0≤ z3 N:=by
    unfold z3
    have : 2≤ Real.log (N:ℝ):=by
      calc (2 : ℝ)=Real.log (Real.exp 2):=(Real.log_exp 2).symm
        _≤ Real.log (N:ℝ):=Real.log_le_log (Real.exp_pos 2) hR.1
    positivity
  have hkern:‖kernel x‖≤ (1+z3 N)^2/ 2:=by
    have h1:|x.1|≤ z3 N:=abs_le.mpr hx.1
    have h2:|x.2|≤ z3 N:=abs_le.mpr hx.2
    calc ‖kernel x‖≤ (1+|x.1|)*(1+|x.2|)/ 2:=x7 _
      _≤ (1+z3 N)*(1+z3 N)/ 2:=by gcongr
      _=(1+z3 N)^2/ 2:=by ring
  exact (y5 hR k hx).trans (mul_le_mul_of_nonneg_left hkern (by positivity))
lemma zL (A:ℝ) (N v7 v6:ℕ) (k:Fin (z0 N)) :
    Continuous (zb A N v7 v6 k):=by
  unfold zb
  refine continuous_finsetProd _ fun p hp=>?_
  have hp_ne:(p:ℂ)≠0:=by
    exact_mod_cast (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).ne_zero
  unfold wk
  have hc1:Continuous (fun x:ℝ × ℝ =>
      (p:ℂ)^(-((1+Complex.I*(x.1 : ℂ))/ (Real.log (z9 A N k):ℂ)))):=by
    simp_rw [Complex.cpow_def_of_ne_zero hp_ne]; fun_prop
  have hc2:Continuous (fun x:ℝ × ℝ =>
      (p:ℂ)^(-((1+Complex.I*(x.2 : ℂ))/ (Real.log (z9 A N k):ℂ)))):=by
    simp_rw [Complex.cpow_def_of_ne_zero hp_ne]; fun_prop
  exact (continuous_const.sub hc1).mul (continuous_const.sub hc2)
lemma ye {A:ℝ} {N v7 v6:ℕ} (hR:zM A N)
    (k:Fin (z0 N)) (x:ℝ × ℝ) :
    ‖zb A N v7 v6 k x‖≤ (4 : ℝ)^(zu N v7 v6 k).card:=by
  have hlogR_pos:0< Real.log (z9 A N k):=Real.log_pos (hR.2.2.2.2.2.2.1 k).2
  unfold zb
  rw [norm_prod]
  calc
    ∏ p∈zu N v7 v6 k,
        ‖(1 - (p:ℂ)^(-wk A N k x.1))*(1 - (p:ℂ)^(-wk A N k x.2))‖
        ≤ ∏ _p∈zu N v7 v6 k,(4 : ℝ):=by
          refine prod_le_prod (fun _ _=>norm_nonneg _) fun p hp=>?_
          have hp_pr:=Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
          have hp1:(1 : ℝ)≤ p:=by exact_mod_cast hp_pr.one_le
          have h1:∀ t:ℝ,‖1 - (p:ℂ)^(-wk A N k t)‖≤ 2:=fun t=>by
            have hcp:‖(p:ℂ)^(-wk A N k t)‖≤ 1:=by
              rw [yf hp_pr.one_le]
              exact Real.rpow_le_one_of_one_le_of_nonpos hp1 (neg_nonpos.mpr (by positivity))
            calc ‖1 - (p:ℂ)^(-wk A N k t)‖≤ ‖(1 : ℂ)‖+‖(p:ℂ)^(-wk A N k t)‖:=norm_sub_le _ _
              _≤ 1+1:=by rw [norm_one]; linarith
              _=2:=by norm_num
          rw [norm_mul]
          nlinarith [h1 x.1,h1 x.2,norm_nonneg (1 - (p:ℂ)^(-wk A N k x.1)),
            norm_nonneg (1 - (p:ℂ)^(-wk A N k x.2))]
    _=(4 : ℝ)^(zu N v7 v6 k).card:=prod_const _
lemma yl {A:ℝ} (hA:1≤ A) {N:ℕ} (hR:zM A N) (k:Fin (z0 N)) :
    let εN:=(4*(z8+1)/ c0)*(Real.log (N:ℝ))^(-(7/ 10 : ℝ))
    (1/ 2 : ℝ)/ Real.log (N:ℝ)≤ ‖Nk A N k‖ ∧
    (c0/ 2)*(ze N/ Real.log (z9 A N k))≤ ‖Nk A N k‖ ∧
    (1+(Real.log (N:ℝ))^(-(7/ 10 : ℝ)))*(ze N/ Real.log (z9 A N k))*c0 ≤
      (1+εN)*‖Nk A N k‖ ∧
    ∫ x in zz (z3 N),‖Gk A N k x‖ ∂zn≤ zf*‖Nk A N k‖:=by
  dsimp only
  set L:=Real.log (N:ℝ)
  set εN:=(4*(z8+1)/ c0)*L^(-(7/ 10 : ℝ))
  have hN1:1≤ N:=by
    have : (1 : ℝ)< (N:ℝ):=by linarith [Real.add_one_le_exp (2 : ℝ),hR.1]
    exact_mod_cast this.le
  have hL2:2≤ L:=by
    calc (2 : ℝ)=Real.log (Real.exp 2):=(Real.log_exp 2).symm
      _≤ L:=Real.log_le_log (Real.exp_pos 2) hR.1
  have hlogR_pos:0< Real.log (z9 A N k):=Real.log_pos (hR.2.2.2.2.2.2.1 k).2
  have hlogR_le:Real.log (z9 A N k)≤ L:=by
    rw [xV A hN1 k]
    have hk1:(1 : ℝ)≤ ((k.1+1 : ℕ):ℝ)^50:=one_le_pow₀ (by exact_mod_cast Nat.succ_pos k.1)
    exact div_le_self (by linarith) (by nlinarith)
  have hWr_ge1:1≤ ze N:=zr N
  set M:=ze N/ Real.log (z9 A N k)
  have hM_pos:0< M:=by positivity
  have hNk_err:=hR.2.2.2.2.2.2.2.2.1 k
  have hε_le : εN≤ 1/ 4:=hR.2.2.2.2.2.2.2.2.2.1
  have hε_nn : 0≤ εN:=by have:=y4; have:=zX; positivity
  have hL07_le:L^(-(7/ 10 : ℝ))≤ εN/ 4:=by
    dsimp only [εN]
    have h1:(1 : ℝ)≤ (z8+1)/ c0:=by
      rw [one_le_div zX]; linarith [x9]
    have hnn:0≤ L^(-(7/ 10 : ℝ)):=by positivity
    have hrew:(4*(z8+1)/ c0)*L^(-(7/ 10 : ℝ))/ 4 =
        ((z8+1)/ c0)*L^(-(7/ 10 : ℝ)):=by ring
    nlinarith
  have hNk_lb_sharp:(1 - εN/ 4)*(M*c0)≤ ‖Nk A N k‖:=by
    have htri:‖((M:ℂ)*(c0:ℂ))‖ ≤
        ‖Nk A N k‖+‖Nk A N k - ((M:ℂ)*(c0:ℂ))‖:=by
      have:=norm_add_le (Nk A N k) (((M:ℂ)*(c0:ℂ)) - Nk A N k)
      rw [add_sub_cancel,norm_sub_rev] at this
      exact this
    rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg hM_pos.le,
      Real.norm_of_nonneg zX.le] at htri
    have hrew:M*(z8+1)*L^(-(7/ 10 : ℝ))=(εN/ 4)*(M*c0):=by
      dsimp only [εN]; field_simp [zX.ne']
    linarith
  have hNk_lb2:(c0/ 2)*M≤ ‖Nk A N k‖:=by
    have : c0/ 2*M≤ (1 - εN/ 4)*(M*c0):=by nlinarith [mul_pos hM_pos zX]
    linarith
  have hNk_lb1:(1/ 2 : ℝ)/ L≤ ‖Nk A N k‖:=by
    have hc01:1≤ c0:=wz
    have h1:(1/ 2 : ℝ)/ L≤ (c0/ 2)*M:=by
      dsimp only [M]
      have hdiv:(1 : ℝ)/ L≤ ze N/ Real.log (z9 A N k) :=
        div_le_div₀ (by linarith) hWr_ge1 hlogR_pos hlogR_le
      have hmul:(1/ 2 : ℝ)*(1/ L)≤ (c0/ 2)*(ze N/ Real.log (z9 A N k)) :=
        mul_le_mul (by linarith) hdiv (by positivity) (by positivity)
      linarith [show (1/ 2 : ℝ)/ L=(1/ 2 : ℝ)*(1/ L) by ring]
    linarith
  have hsharp:(1+L^(-(7/ 10 : ℝ)))*M*c0≤ (1+εN)*‖Nk A N k‖:=by
    have hprod:(1+εN/ 4)≤ (1+εN)*(1 - εN/ 4):=by nlinarith
    calc
      (1+L^(-(7/ 10 : ℝ)))*M*c0≤ (1+εN/ 4)*(M*c0):=by
        nlinarith [mul_pos hM_pos zX]
      _≤ (1+εN)*((1 - εN/ 4)*(M*c0)):=by
        nlinarith [mul_pos hM_pos zX]
      _≤ (1+εN)*‖Nk A N k‖:=mul_le_mul_of_nonneg_left hNk_lb_sharp (by linarith)
  have hGk_int:IntegrableOn (Gk A N k) (zz (z3 N)) zn:=by
    have hdom:IntegrableOn (fun x:ℝ × ℝ=>(2*M)*‖kernel x‖) (zz (z3 N)) zn :=
      (zc.norm.const_mul _).integrableOn
    refine hdom.mono' (zJ hR k) ?_
    rw [ae_restrict_iff' (z6 _)]
    exact ae_of_all _ fun x hx=>y5 hR k hx
  have hGk_int_le:∫ x in zz (z3 N),‖Gk A N k x‖ ∂zn≤ zf*‖Nk A N k‖:=by
    have hdom:Integrable (fun x:ℝ × ℝ=>(2*M)*‖kernel x‖) zn :=
      zc.norm.const_mul _
    calc
      ∫ x in zz (z3 N),‖Gk A N k x‖ ∂zn
          ≤ ∫ x in zz (z3 N),(2*M)*‖kernel x‖ ∂zn :=
            setIntegral_mono_on hGk_int.norm hdom.integrableOn (z6 _)
              fun x hx=>y5 hR k hx
      _≤ ∫ x:ℝ × ℝ,(2*M)*‖kernel x‖ ∂zn :=
            setIntegral_le_integral hdom (ae_of_all _ fun _=>by positivity)
      _=2*M*z8:=by rw [integral_const_mul]; unfold z8; ring
      _=zf*((c0/ 2)*M):=by unfold zf; field_simp [zX.ne']; ring
      _≤ zf*‖Nk A N k‖:=mul_le_mul_of_nonneg_left hNk_lb2 (by linarith [zH])
  exact ⟨hNk_lb1,hNk_lb2,hsharp,hGk_int_le⟩
lemma x8 {A:ℝ} (hA:1≤ A) {N v7 v6:ℕ}
    (hR:zM A N) (k:Fin (z0 N)) :
    ∫ x in zz (z3 N),‖Gk A N k x‖*‖zb A N v7 v6 k x‖ ∂zn ≤
      (1+(4*(z8+1)/ c0)*(Real.log (N:ℝ))^(-(7/ 10 : ℝ))) *
        ‖Nk A N k‖*Ik A N v7 v6 k:=by
  set L:=Real.log (N:ℝ)
  set M:=ze N/ Real.log (z9 A N k)
  have hlogR_pos:0< Real.log (z9 A N k):=Real.log_pos (hR.2.2.2.2.2.2.1 k).2
  have hM_pos:0< M:=by have:=zr N; positivity
  have hfac_cont:Continuous (zb A N v7 v6 k):=zL A N v7 v6 k
  have hfac_le:∀ x:ℝ × ℝ,‖zb A N v7 v6 k x‖≤ (4 : ℝ)^(zu N v7 v6 k).card :=
    ye hR k
  have hkern_fac_int:IntegrableOn (fun x=>‖kernel x‖*‖zb A N v7 v6 k x‖)
      (zz (z3 N)) zn:=by
    refine ((zc.norm.mul_const ((4 : ℝ)^(zu N v7 v6 k).card)).integrableOn).mono'
      (ym.norm.mul hfac_cont.norm).aestronglyMeasurable ?_
    refine ae_of_all _ fun x=>?_
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hfac_le x) (norm_nonneg _)
  have hGk_meas:AEStronglyMeasurable (Gk A N k) (zn.restrict (zz (z3 N))) :=
    zJ hR k
  have hGk_fac_int:IntegrableOn (fun x=>‖Gk A N k x‖*‖zb A N v7 v6 k x‖)
      (zz (z3 N)) zn:=by
    refine (hkern_fac_int.const_mul ((1+L^(-(7/ 10 : ℝ)))*M)).mono'
      (hGk_meas.norm.mul hfac_cont.norm.aestronglyMeasurable) ?_
    rw [ae_restrict_iff' (z6 _)]
    refine ae_of_all _ fun x hx=>?_
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    have hdiff:=(hR.2.2.2.2.2.2.2.1 k x hx).2.2
    have htri:‖Gk A N k x‖≤ (1+L^(-(7/ 10 : ℝ)))*M*‖kernel x‖:=by
      have h0:‖Gk A N k x‖≤ ‖((M:ℂ)*kernel x)‖+‖Gk A N k x - ((M:ℂ)*kernel x)‖:=by
        simpa [add_sub_cancel] using norm_add_le ((M:ℂ)*kernel x) (Gk A N k x - ((M:ℂ)*kernel x))
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hM_pos.le] at h0
      linarith
    have:=mul_le_mul_of_nonneg_right htri (norm_nonneg (zb A N v7 v6 k x))
    linarith
  have hsharp:=(yl hA hR k).2.2.1
  calc
    ∫ x in zz (z3 N),‖Gk A N k x‖*‖zb A N v7 v6 k x‖ ∂zn
        ≤ ∫ x in zz (z3 N),((1+L^(-(7/ 10 : ℝ)))*M) *
            (‖kernel x‖*‖zb A N v7 v6 k x‖) ∂zn:=by
          refine setIntegral_mono_on hGk_fac_int (hkern_fac_int.const_mul _) (z6 _) fun x hx=>?_
          have hdiff:=(hR.2.2.2.2.2.2.2.1 k x hx).2.2
          have htri:‖Gk A N k x‖≤ (1+L^(-(7/ 10 : ℝ)))*M*‖kernel x‖:=by
            have h0:‖Gk A N k x‖≤ ‖((M:ℂ)*kernel x)‖+‖Gk A N k x - ((M:ℂ)*kernel x)‖:=by
              simpa [add_sub_cancel] using norm_add_le ((M:ℂ)*kernel x) (Gk A N k x - ((M:ℂ)*kernel x))
            rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hM_pos.le] at h0
            linarith
          have:=mul_le_mul_of_nonneg_right htri (norm_nonneg (zb A N v7 v6 k x))
          linarith
    _=((1+L^(-(7/ 10 : ℝ)))*M*c0)*Ik A N v7 v6 k:=by
          rw [integral_const_mul]; unfold Ik; field_simp [zX.ne']
    _≤ ((1+(4*(z8+1)/ c0)*L^(-(7/ 10 : ℝ)))*‖Nk A N k‖)*Ik A N v7 v6 k:=by
          have hIk_nn:0≤ Ik A N v7 v6 k:=by
            unfold Ik
            exact mul_nonneg (by positivity [zX]) (setIntegral_nonneg (z6 _) fun _ _=>by positivity)
          exact mul_le_mul_of_nonneg_right hsharp hIk_nn
    _=(1+(4*(z8+1)/ c0)*L^(-(7/ 10 : ℝ)))*‖Nk A N k‖*Ik A N v7 v6 k:=rfl
lemma xL {A:ℝ} (hA:1≤ A) {N v7 v6:ℕ}
    (hR:zM A N) (hdstar_sf:Squarefree v6) (hdstar_cop:Nat.Coprime v6 (z4 N)) :
    Tendsto (fun y:ℕ=>∫ ω in y0 (z0 N) (z3 N),Fy A N v7 v6 y ω ∂(PK (z0 N)))
      atTop (𝓝 (∫ ω in y0 (z0 N) (z3 N),zW A N v7 v6 ω ∂(PK (z0 N)))):=by
  classical
  have hKw:z0 N< z7 N:=hR.2.2.2.1
  have hR_gt1:∀ k:Fin (z0 N),1< z9 A N k:=fun k=>(hR.2.2.2.2.2.2.1 k).2
  have hfact_box:∀ (y:ℕ),max (z7 N) v6≤ y →
      ∀ ω∈y0 (z0 N) (z3 N),
        ∃ Qtail:ℂ,‖Qtail - 1‖≤ Real.exp (32*(z0 N:ℝ)^2/ (y:ℝ)) - 1 ∧
          zW A N v7 v6 ω=Fy A N v7 v6 y ω*Qtail:=by
    intro y hy ω hω
    have hy_w:z7 N≤ y:=(le_max_left _ _).trans hy
    have hy_d:v6≤ y:=(le_max_right _ _).trans hy
    have hy_pos:1≤ y:=by have:=hR.2.1; omega
    let a:ℕ→ℂ:=fun p=>if p.Prime∧z7 N< p then Qp A N p ω - 1 else 0
    let b:ℕ→ℝ:=fun p=>32*(z0 N:ℝ)^2/ (p:ℝ)^2
    have ha_le:∀ n:ℕ,‖a n‖≤ b n:=by
      intro n
      dsimp only [a,b]
      split_ifs with h
      · exact xE hR h.2 ω
      · rw [norm_zero]; positivity
    have hb_sum:Summable b:=by
      have h1:Summable (fun n:ℕ=>(1 : ℝ)/ (n:ℝ)^2):=by
        simp [one_div]
      simpa [b,div_eq_mul_inv] using h1.mul_left (32*(z0 N:ℝ)^2)
    obtain ⟨Qtail,hQt_tend,hQt_bound⟩:=yS ha_le hb_sum y
    have hQt_bound':‖Qtail - 1‖≤ Real.exp (32*(z0 N:ℝ)^2/ (y:ℝ)) - 1:=by
      refine hQt_bound.trans ?_
      apply sub_le_sub_right
      apply Real.exp_le_exp.mpr
      have hrew:(∑' n:{n:ℕ // y< n},b n.1) =
          32*(z0 N:ℝ)^2*∑' n:{n:ℕ // y< n},(1 : ℝ)/ ((n:ℕ):ℝ)^2:=by
        rw [← tsum_mul_left]; congr 1; ext n; dsimp [b]; ring
      rw [hrew]
      have hts:=x4 hy_pos
      calc
        32*(z0 N:ℝ)^2*∑' n:{n:ℕ // y< n},(1 : ℝ)/ ((n:ℕ):ℝ)^2
            ≤ 32*(z0 N:ℝ)^2*(1/ (y:ℝ)) :=
              mul_le_mul_of_nonneg_left hts (by positivity)
        _=32*(z0 N:ℝ)^2/ (y:ℝ):=by ring
    refine ⟨Qtail,hQt_bound',?_⟩
    have hfinite:∀ z:ℕ,y≤ z →
        ∏ p∈z2 (z7 N) z,Ep A N v7 v6 p ω =
          ((v6:ℂ)⁻¹) *
          (∏ k:Fin (z0 N),
            (∏ p∈z2 (z7 N) z,(1 - ukp A N k p (ω k))) *
            zb A N v7 v6 k (ω k)) *
          (∏ p∈(z2 (z7 N) y).filter (fun p=>¬ p∣v6),Qp A N p ω) *
          (∏ p∈v6.primeFactors,∏ k:Fin (z0 N),(1+vkp A N k p (ω k))) *
          (∏ n∈Finset.Ioc y z,(1+a n)):=by
      intro z hz
      have hd_sub_y:v6.primeFactors=(z2 (z7 N) y).filter (fun p=>p∣v6):=by
        ext q
        simp only [Nat.mem_primeFactors,z2,mem_filter,mem_Ioc]
        constructor
        · rintro ⟨hq,hqd,hd0⟩
          exact ⟨⟨⟨(zk hd0 N).mp hdstar_cop q hq hqd,
            (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hqd).trans hy_d⟩,hq⟩,hqd⟩
        · rintro ⟨⟨_,hq⟩,hqd⟩; exact ⟨hq,hqd,hdstar_sf.ne_zero⟩
      have hd_sub_z:v6.primeFactors=(z2 (z7 N) z).filter (fun p=>p∣v6):=by
        ext q
        simp only [Nat.mem_primeFactors,z2,mem_filter,mem_Ioc]
        constructor
        · rintro ⟨hq,hqd,hd0⟩
          exact ⟨⟨⟨(zk hd0 N).mp hdstar_cop q hq hqd,
            (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hqd).trans (hy_d.trans hz)⟩,hq⟩,hqd⟩
        · rintro ⟨⟨_,hq⟩,hqd⟩; exact ⟨hq,hqd,hdstar_sf.ne_zero⟩
      have hEp_p:∀ p∈z2 (z7 N) z,
          Ep A N v7 v6 p ω =
            (∏ k:Fin (z0 N),(1 - ukp A N k p (ω k))) *
            (if p∣v6 then
              ((p:ℂ)⁻¹) *
              (∏ k∈Finset.univ.filter (fun k:Fin (z0 N) =>
                  (p:ℤ)∣((v7:ℤ) - ((k.1+1 : ℕ):ℤ))),
                (1 - (p:ℂ)^(-wk A N k (ω k).1))*(1 - (p:ℂ)^(-wk A N k (ω k).2))) *
              (∏ k:Fin (z0 N),(1+vkp A N k p (ω k)))
            else Qp A N p ω):=by
        intro p hp
        have hp_gt:z7 N< p:=(mem_Ioc.mp (mem_filter.mp hp).1).1
        have h1u_ne:∀ k:Fin (z0 N),1 - ukp A N k p (ω k)≠0:=fun k =>
          (zD hR k hp_gt (ω k)).2.1
        have hcancel:(∏ k:Fin (z0 N),(1 - ukp A N k p (ω k))) *
            (∏ k:Fin (z0 N),(1+vkp A N k p (ω k)))=1:=by
          rw [← prod_mul_distrib]
          refine Finset.prod_eq_one fun k _=>?_
          unfold vkp
          have hne:=h1u_ne k
          field_simp [hne]; ring
        unfold Ep
        split_ifs with hpd
        · rw [div_eq_mul_inv]
          linear_combination -(∏ k∈Finset.univ.filter (fun k:Fin (z0 N) =>
              (p:ℤ)∣((v7:ℤ) - ((k.1+1 : ℕ):ℤ))),
            (1 - (p:ℂ)^(-wk A N k (ω k).1))*(1 - (p:ℂ)^(-wk A N k (ω k).2))) *
            (p:ℂ)⁻¹*hcancel
        · unfold Qp
          have hprod_ne:∏ k:Fin (z0 N),(1 - ukp A N k p (ω k))≠0 :=
            Finset.prod_ne_zero_iff.mpr fun k _=>h1u_ne k
          field_simp [hprod_ne]
      rw [Finset.prod_congr rfl hEp_p,prod_mul_distrib,Finset.prod_comm,Finset.prod_ite]
      rw [← hd_sub_z]
      have hd_part:∏ p∈v6.primeFactors,
            (((p:ℂ)⁻¹) *
             (∏ k∈Finset.univ.filter (fun k:Fin (z0 N) =>
                 (p:ℤ)∣((v7:ℤ) - ((k.1+1 : ℕ):ℤ))),
               (1 - (p:ℂ)^(-wk A N k (ω k).1))*(1 - (p:ℂ)^(-wk A N k (ω k).2))) *
             (∏ k:Fin (z0 N),(1+vkp A N k p (ω k)))) =
          ((v6:ℂ)⁻¹) *
          (∏ k:Fin (z0 N),zb A N v7 v6 k (ω k)) *
          (∏ p∈v6.primeFactors,∏ k:Fin (z0 N),(1+vkp A N k p (ω k))):=by
        rw [prod_mul_distrib,prod_mul_distrib]
        have hd_inv:(∏ p∈v6.primeFactors,((p:ℂ)⁻¹))=(v6:ℂ)⁻¹:=by
          rw [Finset.prod_inv_distrib,← Nat.cast_prod,Nat.prod_primeFactors_of_squarefree hdstar_sf]
        have hfac_swap:(∏ p∈v6.primeFactors,
              ∏ k∈Finset.univ.filter (fun k:Fin (z0 N) =>
                  (p:ℤ)∣((v7:ℤ) - ((k.1+1 : ℕ):ℤ))),
                (1 - (p:ℂ)^(-wk A N k (ω k).1))*(1 - (p:ℂ)^(-wk A N k (ω k).2))) =
            ∏ k:Fin (z0 N),zb A N v7 v6 k (ω k):=by
          unfold zb zu
          simp_rw [Finset.prod_filter]
          exact Finset.prod_comm
        rw [hd_inv,hfac_swap]
      have hQ_part:∏ p∈(z2 (z7 N) z).filter (fun p=>¬ p∣v6),Qp A N p ω =
          (∏ p∈(z2 (z7 N) y).filter (fun p=>¬ p∣v6),Qp A N p ω) *
          (∏ n∈Finset.Ioc y z,(1+a n)):=by
        have hsplit:(z2 (z7 N) z).filter (fun p=>¬ p∣v6) =
            (z2 (z7 N) y).filter (fun p=>¬ p∣v6) ∪ z2 y z:=by
          ext p
          simp only [z2,mem_union,mem_filter,mem_Ioc]
          constructor
          · rintro ⟨⟨⟨h1,h2⟩,hp⟩,hnd⟩
            by_cases hle:p≤ y
            · exact Or.inl ⟨⟨⟨h1,hle⟩,hp⟩,hnd⟩
            · exact Or.inr ⟨⟨by omega,h2⟩,hp⟩
          · rintro (⟨⟨⟨h1,h2⟩,hp⟩,hnd⟩ | ⟨⟨h1,h2⟩,hp⟩)
            · exact ⟨⟨⟨h1,h2.trans hz⟩,hp⟩,hnd⟩
            · refine ⟨⟨⟨by omega,h2⟩,hp⟩,?_⟩
              intro hpd
              have hle:=(Nat.le_of_dvd (Nat.pos_of_ne_zero hdstar_sf.ne_zero) hpd).trans hy_d
              omega
        have hdisj:Disjoint ((z2 (z7 N) y).filter (fun p=>¬ p∣v6)) (z2 y z):=by
          rw [Finset.disjoint_left]; intro p h1 h2
          simp only [z2,mem_filter,mem_Ioc] at h1 h2; omega
        rw [hsplit,Finset.prod_union hdisj]
        congr 1
        unfold z2
        rw [Finset.prod_filter]
        refine Finset.prod_congr rfl fun n hn=>?_
        have hn_gt:z7 N< n:=by have:=(mem_Ioc.mp hn).1; omega
        dsimp only [a]
        by_cases hp:n.Prime
        · simp [hp,hn_gt]
        · simp [hp]
      rw [hd_part,hQ_part,prod_mul_distrib]
      ring
    have hlhs_tend:=wh (v7:=v7) hA hR.1 hKw hR_gt1 hdstar_sf hdstar_cop ω
    have hGk_tend:∀ k:Fin (z0 N),
        Tendsto (fun z:ℕ=>∏ p∈z2 (z7 N) z,(1 - ukp A N k p (ω k))) atTop
          (𝓝 (Gk A N k (ω k))):=fun k =>
      (zp (by have:=hR.2.1; omega) (hR_gt1 k) (ω k)
        (hR.2.2.2.2.2.2.2.1 k (ω k) (hω k (Set.mem_univ k))).1
        (hR.2.2.2.2.2.2.2.1 k (ω k) (hω k (Set.mem_univ k))).2.1).1
    have hprod_Gk_tend:Tendsto (fun z:ℕ =>
        ∏ k:Fin (z0 N),
          (∏ p∈z2 (z7 N) z,(1 - ukp A N k p (ω k)))*zb A N v7 v6 k (ω k))
        atTop (𝓝 (∏ k:Fin (z0 N),Gk A N k (ω k)*zb A N v7 v6 k (ω k))) :=
      tendsto_finsetProd _ fun k _=>(hGk_tend k).mul tendsto_const_nhds
    have hrhs_tend:Tendsto (fun z:ℕ =>
        ((v6:ℂ)⁻¹) *
        (∏ k:Fin (z0 N),
          (∏ p∈z2 (z7 N) z,(1 - ukp A N k p (ω k)))*zb A N v7 v6 k (ω k)) *
        (∏ p∈(z2 (z7 N) y).filter (fun p=>¬ p∣v6),Qp A N p ω) *
        (∏ p∈v6.primeFactors,∏ k:Fin (z0 N),(1+vkp A N k p (ω k))) *
        (∏ n∈Finset.Ioc y z,(1+a n)))
        atTop (𝓝 (Fy A N v7 v6 y ω*Qtail)):=by
      unfold Fy
      exact ((((tendsto_const_nhds.mul hprod_Gk_tend).mul tendsto_const_nhds).mul
        tendsto_const_nhds).mul hQt_tend)
    have hlhs_tend':Tendsto (fun z:ℕ=>∏ p∈z2 (z7 N) z,Ep A N v7 v6 p ω)
        atTop (𝓝 (Fy A N v7 v6 y ω*Qtail)):=by
      refine hrhs_tend.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop y] with z hz
      exact (hfinite z hz).symm
    exact tendsto_nhds_unique hlhs_tend hlhs_tend'
  have hF_bound:=(zV (v7:=v7) hA hR.1 hKw hR_gt1 hdstar_sf hdstar_cop).2
  set M_F:ℝ:=((4 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
    Real.exp (3*(z0 N:ℝ)*(2*Real.log (Real.log (N:ℝ))+45))
  have hF_meas:AEStronglyMeasurable (zW A N v7 v6) (PK (z0 N)):=by
    unfold zW
    exact AEStronglyMeasurable.tsum fun dd=>(xh A N v7 v6 dd).aestronglyMeasurable
  have hF_int:IntegrableOn (zW A N v7 v6) (y0 (z0 N) (z3 N)) (PK (z0 N)) :=
    ((integrable_const M_F).mono' hF_meas (ae_of_all _ hF_bound)).integrableOn
  set M_Fy:ℝ:=((v6:ℝ)⁻¹) *
    (∏ k:Fin (z0 N),(2*(ze N/ Real.log (z9 A N k))*((1+z3 N)^2/ 2)) *
      (4 : ℝ)^(zu N v7 v6 k).card) *
    Real.exp (32*(z0 N:ℝ)^2/ (z7 N:ℝ)) *
    Real.exp (4*(z0 N:ℝ)*(v6.primeFactors.card:ℝ)/ (z7 N:ℝ))
  have hM_Fy_nn:0≤ M_Fy:=by
    have hlog_pos:∀ k:Fin (z0 N),0< Real.log (z9 A N k):=fun k=>Real.log_pos (hR_gt1 k)
    have hW1:=zr N
    have hT_nn:0≤ z3 N:=by
      unfold z3
      have : 2≤ Real.log (N:ℝ):=by
        calc (2 : ℝ)=Real.log (Real.exp 2):=(Real.log_exp 2).symm
          _≤ Real.log (N:ℝ):=Real.log_le_log (Real.exp_pos 2) hR.1
      positivity
    dsimp only [M_Fy]
    refine mul_nonneg (mul_nonneg (mul_nonneg (by positivity) ?_) (Real.exp_pos _).le) (Real.exp_pos _).le
    exact prod_nonneg fun k _=>mul_nonneg (by have:=hlog_pos k; positivity) (by positivity)
  have hFy_bound:∀ y:ℕ,∀ ω∈y0 (z0 N) (z3 N),‖Fy A N v7 v6 y ω‖≤ M_Fy:=by
    intro y ω hω
    unfold Fy
    rw [norm_mul,norm_mul,norm_mul,norm_inv,Complex.norm_natCast,norm_prod,norm_prod,norm_prod]
    have hT_nn:0≤ z3 N:=by
      unfold z3
      have : 2≤ Real.log (N:ℝ):=by
        calc (2 : ℝ)=Real.log (Real.exp 2):=(Real.log_exp 2).symm
          _≤ Real.log (N:ℝ):=Real.log_le_log (Real.exp_pos 2) hR.1
      positivity
    have hpart1:∏ k:Fin (z0 N),‖Gk A N k (ω k)*zb A N v7 v6 k (ω k)‖ ≤
        ∏ k:Fin (z0 N),(2*(ze N/ Real.log (z9 A N k))*((1+z3 N)^2/ 2)) *
          (4 : ℝ)^(zu N v7 v6 k).card:=by
      refine prod_le_prod (fun _ _=>norm_nonneg _) fun k _=>?_
      rw [norm_mul]
      have hx:ω k∈zz (z3 N):=hω k (Set.mem_univ k)
      have hlogR_pos:0< Real.log (z9 A N k):=Real.log_pos (hR_gt1 k)
      have hM_nn:0≤ ze N/ Real.log (z9 A N k):=by have:=zr N; positivity
      exact mul_le_mul (x0 hR k hx) (ye hR k (ω k))
        (norm_nonneg _) (by positivity)
    have hpart2:∏ p∈(z2 (z7 N) y).filter (fun p=>¬ p∣v6),‖Qp A N p ω‖ ≤
        Real.exp (32*(z0 N:ℝ)^2/ (z7 N:ℝ)):=by
      have h1:∏ p∈(z2 (z7 N) y).filter (fun p=>¬ p∣v6),‖Qp A N p ω‖ ≤
          ∏ p∈(z2 (z7 N) y).filter (fun p=>¬ p∣v6),
            (1+32*(z0 N:ℝ)^2/ (p:ℝ)^2):=by
        refine prod_le_prod (fun _ _=>norm_nonneg _) fun p hp=>?_
        have hp_gt:z7 N< p:=(mem_Ioc.mp (mem_filter.mp (mem_filter.mp hp).1).1).1
        have htri:‖Qp A N p ω‖≤ ‖(1 : ℂ)‖+‖Qp A N p ω - 1‖:=by
          simpa [add_sub_cancel] using norm_add_le (1 : ℂ) (Qp A N p ω - 1)
        rw [norm_one] at htri
        linarith [xE hR hp_gt ω]
      refine h1.trans ((zO _ fun _ _=>by positivity).trans ?_)
      apply Real.exp_le_exp.mpr
      have hrew:∀ p:ℕ,32*(z0 N:ℝ)^2/ (p:ℝ)^2 =
          32*(z0 N:ℝ)^2*((1 : ℝ)/ (p:ℝ)^2):=fun p=>by ring
      simp_rw [hrew,← mul_sum]
      have hts:=x2 (w:=z7 N)
        (S:=(z2 (z7 N) y).filter (fun p=>¬ p∣v6)) (by have:=hR.2.1; omega)
        (fun p hp=>(mem_Ioc.mp (mem_filter.mp (mem_filter.mp hp).1).1).1)
      calc
        32*(z0 N:ℝ)^2*∑ p∈(z2 (z7 N) y).filter (fun p=>¬ p∣v6),(1 : ℝ)/ (p:ℝ)^2
            ≤ 32*(z0 N:ℝ)^2*(1/ (z7 N:ℝ)) :=
              mul_le_mul_of_nonneg_left hts (by positivity)
        _=32*(z0 N:ℝ)^2/ (z7 N:ℝ):=by ring
    have hpart3:∏ p∈v6.primeFactors,‖∏ k:Fin (z0 N),(1+vkp A N k p (ω k))‖ ≤
        Real.exp (4*(z0 N:ℝ)*(v6.primeFactors.card:ℝ)/ (z7 N:ℝ)):=by
      have h1:∀ p∈v6.primeFactors,
          ‖∏ k:Fin (z0 N),(1+vkp A N k p (ω k))‖ ≤
            Real.exp (4*(z0 N:ℝ)/ (z7 N:ℝ)):=by
        intro p hp
        have hp_pr:=Nat.prime_of_mem_primeFactors hp
        have hp_gt:z7 N< p :=
          (zk hdstar_sf.ne_zero N).mp hdstar_cop p hp_pr (Nat.dvd_of_mem_primeFactors hp)
        rw [norm_prod]
        calc
          ∏ k:Fin (z0 N),‖1+vkp A N k p (ω k)‖
              ≤ ∏ _k:Fin (z0 N),(1+(4 : ℝ)/ (p:ℝ)):=by
                refine prod_le_prod (fun _ _=>norm_nonneg _) fun k _=>?_
                exact (norm_add_le _ _).trans (by rw [norm_one]; linarith [(zD hR k hp_gt (ω k)).2.2])
          _≤ Real.exp (∑ _k:Fin (z0 N),(4 : ℝ)/ (p:ℝ)) :=
                zO _ fun _ _=>by positivity
          _=Real.exp ((z0 N:ℝ)*(4/ (p:ℝ))):=by simp [nsmul_eq_mul]
          _≤ Real.exp (4*(z0 N:ℝ)/ (z7 N:ℝ)):=by
                apply Real.exp_le_exp.mpr
                have hw_pos:(0 : ℝ)< z7 N:=by have:=hR.2.1; positivity
                have hp_ge:(z7 N:ℝ)≤ (p:ℝ):=by exact_mod_cast hp_gt.le
                have hdiv:(4 : ℝ)/ (p:ℝ)≤ 4/ (z7 N:ℝ) :=
                  div_le_div_of_nonneg_left (by norm_num) hw_pos hp_ge
                calc (z0 N:ℝ)*(4/ (p:ℝ))≤ (z0 N:ℝ)*(4/ (z7 N:ℝ)):=by gcongr
                  _=4*(z0 N:ℝ)/ (z7 N:ℝ):=by ring
      calc
        ∏ p∈v6.primeFactors,‖∏ k:Fin (z0 N),(1+vkp A N k p (ω k))‖
            ≤ ∏ _p∈v6.primeFactors,Real.exp (4*(z0 N:ℝ)/ (z7 N:ℝ)) :=
              prod_le_prod (fun _ _=>norm_nonneg _) h1
        _=Real.exp (∑ _p∈v6.primeFactors,4*(z0 N:ℝ)/ (z7 N:ℝ)):=(Real.exp_sum _ _).symm
        _=Real.exp (4*(z0 N:ℝ)*(v6.primeFactors.card:ℝ)/ (z7 N:ℝ)):=by
              rw [sum_const,nsmul_eq_mul]; congr 1; ring
    have hnn1:0≤ (v6:ℝ)⁻¹*∏ k:Fin (z0 N),‖Gk A N k (ω k)*zb A N v7 v6 k (ω k)‖ :=
      mul_nonneg (by positivity) (prod_nonneg fun _ _=>norm_nonneg _)
    have hnn2:0≤ ∏ p∈(z2 (z7 N) y).filter (fun p=>¬ p∣v6),‖Qp A N p ω‖ :=
      prod_nonneg fun _ _=>norm_nonneg _
    have hnn3:0≤ ∏ p∈v6.primeFactors,‖∏ k:Fin (z0 N),(1+vkp A N k p (ω k))‖ :=
      prod_nonneg fun _ _=>norm_nonneg _
    have hm1:(v6:ℝ)⁻¹*(∏ k:Fin (z0 N),‖Gk A N k (ω k)*zb A N v7 v6 k (ω k)‖) ≤
        (v6:ℝ)⁻¹*∏ k:Fin (z0 N),(2*(ze N/ Real.log (z9 A N k))*((1+z3 N)^2/ 2)) *
          (4 : ℝ)^(zu N v7 v6 k).card :=
      mul_le_mul_of_nonneg_left hpart1 (by positivity)
    have hm2:=mul_le_mul hm1 hpart2 hnn2 (by
      refine mul_nonneg (by positivity) (prod_nonneg fun k _=>?_)
      have:=Real.log_pos (hR_gt1 k); have:=zr N; positivity)
    exact mul_le_mul hm2 hpart3 hnn3 (by
      refine mul_nonneg (mul_nonneg (by positivity) (prod_nonneg fun k _=>?_)) (Real.exp_pos _).le
      have:=Real.log_pos (hR_gt1 k); have:=zr N; positivity)
  have hFy_int:∀ y:ℕ,IntegrableOn (Fy A N v7 v6 y) (y0 (z0 N) (z3 N)) (PK (z0 N)):=by
    intro y
    refine (integrableOn_const (C:=M_Fy) (measure_ne_top _ _)).mono' ?_ ?_
    · have hQp_cont:Continuous (fun ω : Fin (z0 N)→ℝ × ℝ =>
          ∏ p∈(z2 (z7 N) y).filter (fun p=>¬ p∣v6),Qp A N p ω):=by
        refine continuous_finsetProd _ fun p hp=>?_
        have hp_pr:=(mem_filter.mp (mem_filter.mp hp).1).2
        have hp_gt:z7 N< p:=(mem_Ioc.mp (mem_filter.mp (mem_filter.mp hp).1).1).1
        unfold Qp
        refine Continuous.div
          (continuous_const.sub (continuous_finsetSum _ fun k _ =>
            (yb A N k hp_pr.ne_zero).comp (continuous_apply k)))
          (continuous_finsetProd _ fun k _ =>
            continuous_const.sub ((yb A N k hp_pr.ne_zero).comp (continuous_apply k))) fun ω=>?_
        exact Finset.prod_ne_zero_iff.mpr fun k _=>(zD hR k hp_gt (ω k)).2.1
      have hv_cont:Continuous (fun ω : Fin (z0 N)→ℝ × ℝ =>
          ∏ p∈v6.primeFactors,∏ k:Fin (z0 N),(1+vkp A N k p (ω k))):=by
        refine continuous_finsetProd _ fun p hp=>continuous_finsetProd _ fun k _=>?_
        have hp_pr:=Nat.prime_of_mem_primeFactors hp
        have hp_gt:z7 N< p :=
          (zk hdstar_sf.ne_zero N).mp hdstar_cop p hp_pr (Nat.dvd_of_mem_primeFactors hp)
        exact continuous_const.add ((yU hR k hp_gt).comp (continuous_apply k))
      unfold Fy
      have hm1:AEStronglyMeasurable (fun ω=>∏ k:Fin (z0 N),Gk A N k (ω k)*zb A N v7 v6 k (ω k))
          ((PK (z0 N)).restrict (y0 (z0 N) (z3 N))) :=
        Finset.aestronglyMeasurable_fun_prod _ fun k _ =>
          (yA hR k).mul
            ((zL A N v7 v6 k).comp (continuous_apply k)).aestronglyMeasurable
      exact ((aestronglyMeasurable_const.mul hm1).mul hQp_cont.aestronglyMeasurable).mul hv_cont.aestronglyMeasurable
    · rw [ae_restrict_iff' (y8 _ _)]
      exact ae_of_all _ fun ω hω=>hFy_bound y ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h0:Tendsto (fun y:ℕ=>M_Fy*(Real.exp (32*(z0 N:ℝ)^2/ (y:ℝ)) - 1)) atTop (𝓝 0):=by
    have hdiv:Tendsto (fun y:ℕ=>32*(z0 N:ℝ)^2/ (y:ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hexp:Tendsto (fun y:ℕ=>Real.exp (32*(z0 N:ℝ)^2/ (y:ℝ)) - 1) atTop (𝓝 0):=by
      simpa using (Real.continuous_exp.tendsto 0).comp hdiv |>.sub (tendsto_const_nhds (x:=(1 : ℝ)))
    simpa using hexp.const_mul M_Fy
  rw [Metric.tendsto_atTop] at h0
  obtain ⟨Y₁,hY₁⟩:=h0 ε hε
  refine ⟨max Y₁ (max (z7 N) v6),fun y hy=>?_⟩
  rw [Complex.dist_eq,norm_sub_rev,← integral_sub hF_int (hFy_int y)]
  have hpt:∀ ω∈y0 (z0 N) (z3 N),
      ‖zW A N v7 v6 ω - Fy A N v7 v6 y ω‖ ≤
        M_Fy*(Real.exp (32*(z0 N:ℝ)^2/ (y:ℝ)) - 1):=by
    intro ω hω
    obtain ⟨Qtail,hQt_b,hEq⟩:=hfact_box y ((le_max_right _ _).trans hy) ω hω
    rw [hEq,show Fy A N v7 v6 y ω*Qtail - Fy A N v7 v6 y ω =
        Fy A N v7 v6 y ω*(Qtail - 1) by ring,norm_mul]
    exact mul_le_mul (hFy_bound y ω hω) hQt_b (norm_nonneg _) hM_Fy_nn
  have harg_nn:0≤ 32*(z0 N:ℝ)^2/ (y:ℝ):=by positivity
  have hexp_nn:0≤ M_Fy*(Real.exp (32*(z0 N:ℝ)^2/ (y:ℝ)) - 1) :=
    mul_nonneg hM_Fy_nn (by linarith [Real.add_one_le_exp (32*(z0 N:ℝ)^2/ (y:ℝ))])
  have hle_int:‖∫ ω in y0 (z0 N) (z3 N),(zW A N v7 v6 ω - Fy A N v7 v6 y ω)
      ∂(PK (z0 N))‖≤ M_Fy*(Real.exp (32*(z0 N:ℝ)^2/ (y:ℝ)) - 1):=by
    refine (norm_integral_le_integral_norm _).trans ?_
    calc
      ∫ ω in y0 (z0 N) (z3 N),‖zW A N v7 v6 ω - Fy A N v7 v6 y ω‖
          ∂(PK (z0 N))
          ≤ ∫ _ω in y0 (z0 N) (z3 N),
              M_Fy*(Real.exp (32*(z0 N:ℝ)^2/ (y:ℝ)) - 1) ∂(PK (z0 N)) :=
            setIntegral_mono_on (hF_int.sub (hFy_int y)).norm (integrableOn_const (measure_ne_top _ _))
              (y8 _ _) hpt
      _=((PK (z0 N) (y0 (z0 N) (z3 N))).toReal) *
            (M_Fy*(Real.exp (32*(z0 N:ℝ)^2/ (y:ℝ)) - 1)):=by
            rw [setIntegral_const,smul_eq_mul,measureReal_def]
      _≤ 1*(M_Fy*(Real.exp (32*(z0 N:ℝ)^2/ (y:ℝ)) - 1)):=by
            have hprob:(PK (z0 N) (y0 (z0 N) (z3 N))).toReal≤ 1:=by
              have hle1:PK (z0 N) (y0 (z0 N) (z3 N))≤ 1:=by
                calc PK (z0 N) (y0 (z0 N) (z3 N))≤ PK (z0 N) Set.univ :=
                      measure_mono (Set.subset_univ _)
                  _=1:=measure_univ
              exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).mpr hle1 |>.trans_eq ENNReal.toReal_one
            exact mul_le_mul_of_nonneg_right hprob hexp_nn
      _=M_Fy*(Real.exp (32*(z0 N:ℝ)^2/ (y:ℝ)) - 1):=one_mul _
  have hlt:=hY₁ y ((le_max_left _ _).trans hy)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hexp_nn] at hlt
  exact lt_of_le_of_lt hle_int hlt
lemma yY {A:ℝ} (hA:1≤ A) {N v7 v6:ℕ}
    (hR:zM A N) (hdstar_sf:Squarefree v6) (hdstar_cop:Nat.Coprime v6 (z4 N)) :
    ‖∫ ω in y0 (z0 N) (z3 N),zW A N v7 v6 ω ∂(PK (z0 N))‖ ≤
      2*((2 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
        (∏ k:Fin (z0 N),‖Nk A N k‖) *
        (∏ k∈Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty),
          Ik A N v7 v6 k) ∧
    (v6=1 →
      ‖(∫ ω in y0 (z0 N) (z3 N),zW A N v7 v6 ω ∂(PK (z0 N))) -
          ∏ k:Fin (z0 N),Nk A N k‖ ≤
        (1/ 5 : ℝ)*∏ k:Fin (z0 N),‖Nk A N k‖):=by
  classical
  set εN:=(4*(z8+1)/ c0)*(Real.log (N:ℝ))^(-(7/ 10 : ℝ))
  have hε_nn : 0≤ εN:=by have:=y4; have:=zX; positivity
  have hFy_bounds:∀ y:ℕ,max (z7 N) v6≤ y →
      ‖∫ ω in y0 (z0 N) (z3 N),Fy A N v7 v6 y ω ∂(PK (z0 N))‖ ≤
        2*((2 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
          (∏ k:Fin (z0 N),‖Nk A N k‖) *
          (∏ k∈Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty),
            Ik A N v7 v6 k) ∧
      (v6=1 →
        ‖(∫ ω in y0 (z0 N) (z3 N),Fy A N v7 v6 y ω ∂(PK (z0 N))) -
            ∏ k:Fin (z0 N),Nk A N k‖ ≤
          (1/ 5 : ℝ)*∏ k:Fin (z0 N),‖Nk A N k‖):=by
    intro y hy
    have hy_d:v6≤ y:=(le_max_right _ _).trans hy
    let P:=z2 (z7 N) y
    have hd_sub_y:v6.primeFactors=P.filter (fun p=>p∣v6):=by
      ext q
      simp only [Nat.mem_primeFactors,P,z2,mem_filter,mem_Ioc]
      constructor
      · rintro ⟨hq,hqd,hd0⟩
        exact ⟨⟨⟨(zk hd0 N).mp hdstar_cop q hq hqd,
          (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hqd).trans hy_d⟩,hq⟩,hqd⟩
      · rintro ⟨⟨_,hq⟩,hqd⟩; exact ⟨hq,hqd,hdstar_sf.ne_zero⟩
    let validS:P→Finset (Finset (Fin (z0 N))):=fun p =>
      if (p:ℕ)∣v6 then Finset.univ.powerset
      else insert ∅ ((Finset.univ:Finset (Fin (z0 N))).powerset.filter (fun S=>2≤ S.card))
    let coeffS:P→Finset (Fin (z0 N))→ℂ:=fun p S =>
      if (p:ℕ)∣v6 then 1
      else if S=∅ then 1 else 1 - (S.card:ℂ)
    let AllS:Finset (P→Finset (Fin (z0 N))):=Fintype.piFinset validS
    let Jk:(P→Finset (Fin (z0 N)))→Fin (z0 N)→ℂ:=fun S k =>
      ∫ x in zz (z3 N),
        (Gk A N k x*zb A N v7 v6 k x *
          ∏ p∈Finset.univ.filter (fun p:P=>k∈S p),vkp A N k (p:ℕ) x) ∂zn
    have hFy_expand:∀ ω : Fin (z0 N)→ℝ × ℝ,
        Fy A N v7 v6 y ω =
          ((v6:ℂ)⁻¹)*∑ S∈AllS,(∏ p:P,coeffS p (S p)) *
            ∏ k:Fin (z0 N),
              (Gk A N k (ω k)*zb A N v7 v6 k (ω k) *
                ∏ p∈Finset.univ.filter (fun p:P=>k∈S p),vkp A N k (p:ℕ) (ω k)):=by
      intro ω
      have hprod_p:(∏ p∈P.filter (fun p=>¬ p∣v6),Qp A N p ω) *
            (∏ p∈v6.primeFactors,∏ k:Fin (z0 N),(1+vkp A N k p (ω k))) =
          ∏ p:P,∑ S∈validS p,coeffS p S*∏ k∈S,vkp A N k (p:ℕ) (ω k):=by
        rw [hd_sub_y,mul_comm,← Finset.prod_ite,← Finset.prod_coe_sort P]
        refine Finset.prod_congr rfl fun p _=>?_
        have hp_gt:z7 N< (p:ℕ):=(mem_Ioc.mp (mem_filter.mp p.2).1).1
        dsimp only [validS,coeffS]
        split_ifs with hpd
        · simp only [one_mul]
          exact Finset.prod_one_add (s:=(Finset.univ:Finset (Fin (z0 N))))
            (f:=fun k=>vkp A N k (p:ℕ) (ω k))
        · have hne:∀ k∈(Finset.univ:Finset (Fin (z0 N))),1 - ukp A N k (p:ℕ) (ω k)≠0 :=
            fun k _=>(zD hR k hp_gt (ω k)).2.1
          have hid:=xo Finset.univ (fun k=>ukp A N k (p:ℕ) (ω k)) hne
          change Qp A N (p:ℕ) ω=1 +
            ∑ S∈(Finset.univ:Finset (Fin (z0 N))).powerset.filter (fun S=>2≤ S.card),
              (1 - (S.card:ℂ))*∏ k∈S,vkp A N k (p:ℕ) (ω k) at hid
          rw [hid,sum_insert (by simp)]
          simp only [↓reduceIte,Finset.prod_empty,mul_one]
          congr 1
          refine sum_congr rfl fun S hS=>?_
          have hne0:S≠∅:=by
            intro h; subst h; simp at hS
          rw [if_neg hne0]
      unfold Fy
      rw [mul_assoc (((v6:ℂ)⁻¹)*_),hprod_p,Finset.prod_univ_sum,mul_sum]
      rw [mul_sum]
      refine sum_congr rfl fun S _=>?_
      rw [prod_mul_distrib (f:=fun p:P=>coeffS p (S p))]
      have hswap:∏ p:P,∏ k∈S p,vkp A N k (p:ℕ) (ω k) =
          ∏ k:Fin (z0 N),∏ p∈Finset.univ.filter (fun p:P=>k∈S p),vkp A N k (p:ℕ) (ω k):=by
        have h1:∀ p:P,∏ k∈S p,vkp A N k (p:ℕ) (ω k) =
            ∏ k:Fin (z0 N),if k∈S p then vkp A N k (p:ℕ) (ω k) else 1:=fun p=>by
          rw [← Finset.prod_filter]; congr 1; ext k; simp
        simp_rw [h1]
        rw [Finset.prod_comm]
        refine Finset.prod_congr rfl fun k _=>by rw [Finset.prod_filter]
      rw [hswap]
      have hmul_k:(∏ k:Fin (z0 N),Gk A N k (ω k)*zb A N v7 v6 k (ω k)) *
            (∏ k:Fin (z0 N),∏ p∈Finset.univ.filter (fun p:P=>k∈S p),vkp A N k (p:ℕ) (ω k)) =
          ∏ k:Fin (z0 N),(Gk A N k (ω k)*zb A N v7 v6 k (ω k) *
            ∏ p∈Finset.univ.filter (fun p:P=>k∈S p),vkp A N k (p:ℕ) (ω k)) :=
        prod_mul_distrib.symm
      rw [← hmul_k]; ring
    have hterm_int:∀ S:P→Finset (Fin (z0 N)),
        IntegrableOn (fun ω : Fin (z0 N)→ℝ × ℝ =>
          (∏ p:P,coeffS p (S p)) *
            ∏ k:Fin (z0 N),
              (Gk A N k (ω k)*zb A N v7 v6 k (ω k) *
                ∏ p∈Finset.univ.filter (fun p:P=>k∈S p),vkp A N k (p:ℕ) (ω k)))
          (y0 (z0 N) (z3 N)) (PK (z0 N)):=by
      intro S
      refine Integrable.const_mul ?_ _
      have hcoord_le:∀ k:Fin (z0 N),∀ x∈zz (z3 N),
          ‖Gk A N k x*zb A N v7 v6 k x *
            ∏ p∈Finset.univ.filter (fun p:P=>k∈S p),vkp A N k (p:ℕ) x‖ ≤
          (2*(ze N/ Real.log (z9 A N k))*((1+z3 N)^2/ 2)) *
            (4 : ℝ)^(zu N v7 v6 k).card *
            ∏ p∈Finset.univ.filter (fun p:P=>k∈S p),((4 : ℝ)/ ((p:ℕ):ℝ)):=by
        intro k x hx
        rw [norm_mul,norm_mul,norm_prod]
        have hlogR_pos:0< Real.log (z9 A N k):=Real.log_pos (hR.2.2.2.2.2.2.1 k).2
        have hM_nn:0≤ ze N/ Real.log (z9 A N k):=by have:=zr N; positivity
        have hv_le:∏ p∈Finset.univ.filter (fun p:P=>k∈S p),‖vkp A N k (p:ℕ) x‖ ≤
            ∏ p∈Finset.univ.filter (fun p:P=>k∈S p),((4 : ℝ)/ ((p:ℕ):ℝ)):=by
          refine prod_le_prod (fun _ _=>norm_nonneg _) fun p _=>?_
          have hp_gt:z7 N< (p:ℕ):=(mem_Ioc.mp (mem_filter.mp p.2).1).1
          exact (zD hR k hp_gt x).2.2
        have h12:=mul_le_mul (x0 hR k hx)
          (ye (v7:=v7) (v6:=v6) hR k x)
          (norm_nonneg _) (by positivity)
        exact mul_le_mul h12 hv_le (prod_nonneg fun _ _=>norm_nonneg _) (by positivity)
      set C_S:ℝ:=∏ k:Fin (z0 N),
        (2*(ze N/ Real.log (z9 A N k))*((1+z3 N)^2/ 2)) *
          (4 : ℝ)^(zu N v7 v6 k).card *
          ∏ p∈Finset.univ.filter (fun p:P=>k∈S p),((4 : ℝ)/ ((p:ℕ):ℝ))
      refine (integrableOn_const (C:=C_S) (measure_ne_top _ _)).mono' ?_ ?_
      · refine Finset.aestronglyMeasurable_fun_prod _ fun k _=>?_
        have hv_c:Continuous (fun ω : Fin (z0 N)→ℝ × ℝ =>
            ∏ p∈Finset.univ.filter (fun p:P=>k∈S p),vkp A N k (p:ℕ) (ω k)):=by
          refine continuous_finsetProd _ fun p _=>?_
          have hp_gt:z7 N< (p:ℕ):=(mem_Ioc.mp (mem_filter.mp p.2).1).1
          exact (yU hR k hp_gt).comp (continuous_apply k)
        exact ((yA hR k).mul
          ((zL A N v7 v6 k).comp (continuous_apply k)).aestronglyMeasurable).mul
          hv_c.aestronglyMeasurable
      · rw [ae_restrict_iff' (y8 _ _)]
        refine ae_of_all _ fun ω hω=>?_
        rw [norm_prod]
        exact prod_le_prod (fun _ _=>norm_nonneg _) fun k _=>hcoord_le k (ω k) (hω k (Set.mem_univ k))
    have hint_Fy_eq:∫ ω in y0 (z0 N) (z3 N),Fy A N v7 v6 y ω ∂(PK (z0 N)) =
        ((v6:ℂ)⁻¹)*∑ S∈AllS,(∏ p:P,coeffS p (S p))*∏ k:Fin (z0 N),Jk S k:=by
      simp_rw [hFy_expand]
      rw [integral_const_mul,MeasureTheory.integral_finsetSum AllS fun S _=>hterm_int S]
      congr 1
      refine sum_congr rfl fun S _=>?_
      rw [integral_const_mul,wA,
        MeasureTheory.integral_fintype_prod_eq_prod (f:=fun (k:Fin (z0 N)) (x:ℝ × ℝ) =>
          Gk A N k x*zb A N v7 v6 k x *
            ∏ p∈Finset.univ.filter (fun p:P=>k∈S p),vkp A N k (p:ℕ) x)]
    have hJk_bound:∀ (S:P→Finset (Fin (z0 N))) (k:Fin (z0 N)),
        ‖Jk S k‖ ≤
          (if (zu N v7 v6 k).Nonempty then (1+εN)*Ik A N v7 v6 k else 1) *
          ‖Nk A N k‖ *
          ∏ p∈Finset.univ.filter (fun p:P=>k∈S p),(4*zf/ ((p:ℕ):ℝ)):=by
      intro S k
      set Spk:=Finset.univ.filter (fun p:P=>k∈S p)
      have hv_prod_le:∀ x:ℝ × ℝ,
          ‖∏ p∈Spk,vkp A N k (p:ℕ) x‖≤ ∏ p∈Spk,((4 : ℝ)/ ((p:ℕ):ℝ)):=fun x=>by
        rw [norm_prod]
        refine prod_le_prod (fun _ _=>norm_nonneg _) fun p _=>?_
        have hp_gt:z7 N< (p:ℕ):=(mem_Ioc.mp (mem_filter.mp p.2).1).1
        exact (zD hR k hp_gt x).2.2
      have hB1:1≤ zf:=zH
      have hB_prod_ge:∏ p∈Spk,((4 : ℝ)/ ((p:ℕ):ℝ)) ≤
          ∏ p∈Spk,(4*zf/ ((p:ℕ):ℝ)):=by
        refine prod_le_prod (fun _ _=>by positivity) fun p _=>?_
        have hp_pos:(0 : ℝ)< (p:ℕ):=by exact_mod_cast (mem_filter.mp p.2).2.pos
        exact div_le_div_of_nonneg_right (by linarith) hp_pos.le
      have hlogR_pos:0< Real.log (z9 A N k):=Real.log_pos (hR.2.2.2.2.2.2.1 k).2
      have hM_nn:0≤ ze N/ Real.log (z9 A N k):=by have:=zr N; positivity
      have hJk_int:IntegrableOn (fun x =>
            Gk A N k x*zb A N v7 v6 k x*∏ p∈Spk,vkp A N k (p:ℕ) x)
          (zz (z3 N)) zn:=by
        set C_Jk:ℝ :=
          (2*(ze N/ Real.log (z9 A N k))*((1+z3 N)^2/ 2)) *
            (4 : ℝ)^(zu N v7 v6 k).card *
            ∏ p∈Spk,((4 : ℝ)/ ((p:ℕ):ℝ))
        refine (integrableOn_const (C:=C_Jk) (measure_ne_top _ _)).mono' ?_ ?_
        · have hv_c:Continuous (fun x:ℝ × ℝ=>∏ p∈Spk,vkp A N k (p:ℕ) x) :=
            continuous_finsetProd _ fun p _ =>
              yU hR k (mem_Ioc.mp (mem_filter.mp p.2).1).1
          exact ((zJ hR k).mul
            (zL A N v7 v6 k).aestronglyMeasurable).mul hv_c.aestronglyMeasurable
        · rw [ae_restrict_iff' (z6 _)]
          refine ae_of_all _ fun x hx=>?_
          rw [norm_mul,norm_mul]
          exact mul_le_mul (mul_le_mul (x0 hR k hx) (ye hR k x)
            (norm_nonneg _) (by positivity)) (hv_prod_le x) (norm_nonneg _) (by positivity)
      by_cases hPk:(zu N v7 v6 k).Nonempty
      · rw [if_pos hPk]
        have hdom_int:IntegrableOn (fun x=>(∏ p∈Spk,((4 : ℝ)/ ((p:ℕ):ℝ))) *
              (‖Gk A N k x‖*‖zb A N v7 v6 k x‖)) (zz (z3 N)) zn:=by
          set C_dom:ℝ:=(∏ p∈Spk,((4 : ℝ)/ ((p:ℕ):ℝ))) *
            ((2*(ze N/ Real.log (z9 A N k))*((1+z3 N)^2/ 2)) *
              (4 : ℝ)^(zu N v7 v6 k).card)
          refine (integrableOn_const (C:=C_dom) (measure_ne_top _ _)).mono' ?_ ?_
          · exact aestronglyMeasurable_const.mul ((zJ hR k).norm.mul
              (zL A N v7 v6 k).norm.aestronglyMeasurable)
          · rw [ae_restrict_iff' (z6 _)]
            refine ae_of_all _ fun x hx=>?_
            rw [Real.norm_of_nonneg (mul_nonneg (prod_nonneg fun _ _=>by positivity)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)))]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul (x0 hR k hx) (ye hR k x) (norm_nonneg _) (by positivity))
              (prod_nonneg fun _ _=>by positivity)
        have hIk_nn:0≤ Ik A N v7 v6 k:=by
          unfold Ik
          exact mul_nonneg (by positivity [zX]) (setIntegral_nonneg (z6 _) fun _ _=>by positivity)
        calc
          ‖Jk S k‖≤ ∫ x in zz (z3 N),
              ‖Gk A N k x*zb A N v7 v6 k x*∏ p∈Spk,vkp A N k (p:ℕ) x‖ ∂zn :=
            norm_integral_le_integral_norm _
          _≤ ∫ x in zz (z3 N),(∏ p∈Spk,((4 : ℝ)/ ((p:ℕ):ℝ))) *
              (‖Gk A N k x‖*‖zb A N v7 v6 k x‖) ∂zn:=by
            refine setIntegral_mono_on hJk_int.norm hdom_int (z6 _) fun x _=>?_
            rw [norm_mul,norm_mul,mul_comm (∏ p∈Spk,((4 : ℝ)/ ((p:ℕ):ℝ)))]
            exact mul_le_mul_of_nonneg_left (hv_prod_le x) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          _=(∏ p∈Spk,((4 : ℝ)/ ((p:ℕ):ℝ))) *
              ∫ x in zz (z3 N),‖Gk A N k x‖*‖zb A N v7 v6 k x‖ ∂zn :=
            integral_const_mul _ _
          _≤ (∏ p∈Spk,(4*zf/ ((p:ℕ):ℝ))) *
              ((1+εN)*‖Nk A N k‖*Ik A N v7 v6 k) :=
            mul_le_mul hB_prod_ge (x8 hA hR k)
              (setIntegral_nonneg (z6 _) fun _ _=>by positivity)
              (prod_nonneg fun _ _=>by positivity [zH])
          _=(1+εN)*Ik A N v7 v6 k*‖Nk A N k‖ *
              ∏ p∈Spk,(4*zf/ ((p:ℕ):ℝ)):=by ring
      · rw [if_neg hPk,one_mul]
        have hPke:zu N v7 v6 k=∅:=Finset.not_nonempty_iff_eq_empty.mp hPk
        have hfac1:∀ x,zb A N v7 v6 k x=1:=fun x=>by
          unfold zb; rw [hPke,Finset.prod_empty]
        rcases Spk.eq_empty_or_nonempty with hSe | ⟨p₀,hp₀⟩
        ·
          have hJk_eq:Jk S k=Nk A N k:=by
            dsimp only [Jk]; unfold Nk
            refine setIntegral_congr_fun (z6 _) fun x _=>?_
            change Gk A N k x*zb A N v7 v6 k x*∏ p∈Spk,vkp A N k (p:ℕ) x=Gk A N k x
            rw [hfac1 x,hSe,Finset.prod_empty,mul_one,mul_one]
          rw [hJk_eq,hSe,Finset.prod_empty,mul_one]
        ·
          have hB_pull:zf*∏ p∈Spk,((4 : ℝ)/ ((p:ℕ):ℝ)) ≤
              ∏ p∈Spk,(4*zf/ ((p:ℕ):ℝ)):=by
            have hprod_mul:∏ p∈Spk,(4*zf/ ((p:ℕ):ℝ)) =
                zf^Spk.card*∏ p∈Spk,((4 : ℝ)/ ((p:ℕ):ℝ)):=by
              have hrew:∀ p:P,4*zf/ ((p:ℕ):ℝ)=zf*((4 : ℝ)/ ((p:ℕ):ℝ)) :=
                fun p=>by ring
              simp_rw [hrew,prod_mul_distrib,prod_const]
            rw [hprod_mul]
            have hcard1:1≤ Spk.card:=Finset.card_pos.mpr ⟨p₀,hp₀⟩
            have hBpow:zf≤ zf^Spk.card:=by
              conv_lhs=>rw [← pow_one zf]
              exact pow_le_pow_right₀ hB1 hcard1
            exact mul_le_mul_of_nonneg_right hBpow (prod_nonneg fun _ _=>by positivity)
          have hGk_int_norm:IntegrableOn (fun x=>‖Gk A N k x‖) (zz (z3 N)) zn:=by
            refine ((zc.norm.const_mul (2*(ze N/ Real.log (z9 A N k)))).integrableOn).mono'
              (zJ hR k).norm ?_
            rw [ae_restrict_iff' (z6 _)]
            refine ae_of_all _ fun x hx=>?_
            rw [Real.norm_of_nonneg (norm_nonneg _)]
            exact y5 hR k hx
          calc
            ‖Jk S k‖≤ ∫ x in zz (z3 N),
                ‖Gk A N k x*zb A N v7 v6 k x*∏ p∈Spk,vkp A N k (p:ℕ) x‖ ∂zn :=
              norm_integral_le_integral_norm _
            _≤ ∫ x in zz (z3 N),(∏ p∈Spk,((4 : ℝ)/ ((p:ℕ):ℝ)))*‖Gk A N k x‖ ∂zn:=by
              refine setIntegral_mono_on hJk_int.norm (hGk_int_norm.const_mul _) (z6 _) fun x _=>?_
              rw [hfac1 x,mul_one,norm_mul,mul_comm (∏ p∈Spk,((4 : ℝ)/ ((p:ℕ):ℝ)))]
              exact mul_le_mul_of_nonneg_left (hv_prod_le x) (norm_nonneg _)
            _=(∏ p∈Spk,((4 : ℝ)/ ((p:ℕ):ℝ)))*∫ x in zz (z3 N),‖Gk A N k x‖ ∂zn :=
              integral_const_mul _ _
            _≤ (∏ p∈Spk,((4 : ℝ)/ ((p:ℕ):ℝ)))*(zf*‖Nk A N k‖) :=
              mul_le_mul_of_nonneg_left (yl hA hR k).2.2.2
                (prod_nonneg fun _ _=>by positivity)
            _=‖Nk A N k‖*(zf*∏ p∈Spk,((4 : ℝ)/ ((p:ℕ):ℝ))):=by ring
            _≤ ‖Nk A N k‖*∏ p∈Spk,(4*zf/ ((p:ℕ):ℝ)) :=
              mul_le_mul_of_nonneg_left hB_pull (norm_nonneg _)
    have hprod_Jk:∀ S∈AllS,
        ‖(∏ p:P,coeffS p (S p))*∏ k:Fin (z0 N),Jk S k‖ ≤
          (1+εN)^(z0 N) *
          (∏ k:Fin (z0 N),‖Nk A N k‖) *
          (∏ k∈Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty),
            Ik A N v7 v6 k) *
          ∏ p:P,‖coeffS p (S p)‖*(4*zf/ ((p:ℕ):ℝ))^(S p).card:=by
      intro S _
      rw [norm_mul,norm_prod,norm_prod]
      have h1:∏ k:Fin (z0 N),‖Jk S k‖ ≤
          ∏ k:Fin (z0 N),
            ((if (zu N v7 v6 k).Nonempty then (1+εN)*Ik A N v7 v6 k else 1) *
             ‖Nk A N k‖ *
             ∏ p∈Finset.univ.filter (fun p:P=>k∈S p),(4*zf/ ((p:ℕ):ℝ))) :=
        prod_le_prod (fun _ _=>norm_nonneg _) fun k _=>hJk_bound S k
      rw [prod_mul_distrib,prod_mul_distrib] at h1
      have hswap_B:∏ k:Fin (z0 N),
            ∏ p∈Finset.univ.filter (fun p:P=>k∈S p),(4*zf/ ((p:ℕ):ℝ)) =
          ∏ p:P,(4*zf/ ((p:ℕ):ℝ))^(S p).card:=by
        have h2:∀ k:Fin (z0 N),
            ∏ p∈Finset.univ.filter (fun p:P=>k∈S p),(4*zf/ ((p:ℕ):ℝ)) =
            ∏ p:P,if k∈S p then (4*zf/ ((p:ℕ):ℝ)) else 1:=fun k=>by
          rw [Finset.prod_filter]
        simp_rw [h2]
        rw [Finset.prod_comm]
        refine Finset.prod_congr rfl fun p _=>?_
        rw [← Finset.prod_filter]
        have hf:Finset.univ.filter (fun k:Fin (z0 N)=>k∈S p)=S p:=by ext k; simp
        rw [hf,prod_const]
      have hIk_part:∏ k:Fin (z0 N),
            (if (zu N v7 v6 k).Nonempty then (1+εN)*Ik A N v7 v6 k else 1) ≤
          (1+εN)^(z0 N) *
            ∏ k∈Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty),
              Ik A N v7 v6 k:=by
        rw [← Finset.prod_filter,prod_mul_distrib,prod_const]
        have hle_card:(Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty)).card≤ z0 N:=by
          simpa using Finset.card_le_univ (Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty))
        have hpow:(1+εN)^(Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty)).card ≤
            (1+εN)^(z0 N):=pow_le_pow_right₀ (by linarith) hle_card
        exact mul_le_mul_of_nonneg_right hpow (prod_nonneg fun k _=>by
          unfold Ik; exact mul_nonneg (by positivity [zX])
            (setIntegral_nonneg (z6 _) fun _ _=>by positivity))
      rw [hswap_B] at h1
      have hcomb:∏ k:Fin (z0 N),‖Jk S k‖ ≤
          (1+εN)^(z0 N)*(∏ k:Fin (z0 N),‖Nk A N k‖) *
          (∏ k∈Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty),
            Ik A N v7 v6 k) *
          ∏ p:P,(4*zf/ ((p:ℕ):ℝ))^(S p).card:=by
        have h2:(∏ k:Fin (z0 N),
              (if (zu N v7 v6 k).Nonempty then (1+εN)*Ik A N v7 v6 k else 1)) *
            (∏ k:Fin (z0 N),‖Nk A N k‖) *
            (∏ p:P,(4*zf/ ((p:ℕ):ℝ))^(S p).card) ≤
            ((1+εN)^(z0 N) *
              ∏ k∈Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty),
                Ik A N v7 v6 k) *
            (∏ k:Fin (z0 N),‖Nk A N k‖) *
            (∏ p:P,(4*zf/ ((p:ℕ):ℝ))^(S p).card) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hIk_part (prod_nonneg fun _ _=>norm_nonneg _))
            (prod_nonneg fun _ _=>by have:=zH; positivity)
        linarith
      calc
        (∏ p:P,‖coeffS p (S p)‖)*(∏ k:Fin (z0 N),‖Jk S k‖)
            ≤ (∏ p:P,‖coeffS p (S p)‖) *
              ((1+εN)^(z0 N)*(∏ k:Fin (z0 N),‖Nk A N k‖) *
               (∏ k∈Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty),
                 Ik A N v7 v6 k) *
               ∏ p:P,(4*zf/ ((p:ℕ):ℝ))^(S p).card) :=
              mul_le_mul_of_nonneg_left hcomb (prod_nonneg fun _ _=>norm_nonneg _)
        _=(1+εN)^(z0 N)*(∏ k:Fin (z0 N),‖Nk A N k‖) *
              (∏ k∈Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty),
                Ik A N v7 v6 k) *
              ((∏ p:P,‖coeffS p (S p)‖)*∏ p:P,(4*zf/ ((p:ℕ):ℝ))^(S p).card):=by ring
        _=_:=by rw [← prod_mul_distrib]
    have hsum_AllS :
        ∑ S∈AllS,∏ p:P,‖coeffS p (S p)‖*(4*zf/ ((p:ℕ):ℝ))^(S p).card =
          ∏ p:P,∑ S∈validS p,‖coeffS p S‖*(4*zf/ ((p:ℕ):ℝ))^S.card :=
      (Finset.prod_univ_sum validS
        (fun p S=>‖coeffS p S‖*(4*zf/ ((p:ℕ):ℝ))^S.card)).symm
    have hlocal_p:∀ p:P,
        ∑ S∈validS p,‖coeffS p S‖*(4*zf/ ((p:ℕ):ℝ))^S.card ≤
          if (p:ℕ)∣v6 then (1+4*zf/ ((p:ℕ):ℝ))^(z0 N)
          else 1+32*zf^2*(z0 N:ℝ)^2/ ((p:ℕ):ℝ)^2:=by
      intro p
      have hp_gt:z7 N< (p:ℕ):=(mem_Ioc.mp (mem_filter.mp p.2).1).1
      dsimp only [validS,coeffS]
      split_ifs with hpd
      · simp only [norm_one,one_mul]
        have hbin:∑ S∈(Finset.univ:Finset (Fin (z0 N))).powerset,
              (4*zf/ ((p:ℕ):ℝ))^S.card =
            (1+4*zf/ ((p:ℕ):ℝ))^(z0 N):=by
          have h1:=Finset.prod_one_add (s:=(Finset.univ:Finset (Fin (z0 N))))
            (f:=fun _=>4*zf/ ((p:ℕ):ℝ))
          simp only [prod_const,Finset.card_univ,Fintype.card_fin] at h1
          exact h1.symm
        exact hbin.le
      · rw [sum_insert (by simp)]
        simp only [↓reduceIte,norm_one,card_empty,pow_zero,mul_one]
        gcongr
        have hterm_le:∀ S∈(Finset.univ:Finset (Fin (z0 N))).powerset.filter (fun S=>2≤ S.card),
            ‖if S=∅ then (1 : ℂ) else 1 - (S.card:ℂ)‖*(4*zf/ ((p:ℕ):ℝ))^S.card =
              ((S.card:ℝ) - 1)*(4*zf/ ((p:ℕ):ℝ))^S.card:=by
          intro S hS
          have h2:2≤ S.card:=(mem_filter.mp hS).2
          have hne0:S≠∅:=by intro h; subst h; simp at h2
          rw [if_neg hne0]
          have hcast:(1 : ℂ) - (S.card:ℂ)=(((1 - (S.card:ℝ):ℝ)):ℂ):=by push_cast; rfl
          rw [hcast,Complex.norm_real,Real.norm_eq_abs,
            abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast (show 1≤ S.card by omega)))]
          ring
        rw [sum_congr rfl hterm_le]
        have hKx:(z0 N:ℝ)*(4*zf/ ((p:ℕ):ℝ))≤ 1:=by
          have h8BK:=hR.2.2.2.2.2.2.2.2.2.2.2.1
          have hp_pos:(0 : ℝ)< (p:ℕ):=by have:=hR.2.1; exact_mod_cast (show 0< (p:ℕ) by omega)
          have hp_ge:(z7 N:ℝ)≤ ((p:ℕ):ℝ):=by exact_mod_cast hp_gt.le
          rw [mul_div_assoc',div_le_one hp_pos]
          nlinarith [zH,Nat.cast_nonneg (α:=ℝ) (z0 N)]
        refine (x5 (z0 N) (by positivity [zH]) hKx).trans_eq ?_
        ring
    have hprod_nd:∏ p∈P.filter (fun p=>¬ p∣v6),
          (1+32*zf^2*(z0 N:ℝ)^2/ (p:ℝ)^2) ≤
        Real.exp (1/ 10 : ℝ):=by
      refine (zO _ fun _ _=>by positivity [zH]).trans ?_
      apply Real.exp_le_exp.mpr
      have hsum_le:∑ p∈P.filter (fun p=>¬ p∣v6),
            32*zf^2*(z0 N:ℝ)^2/ (p:ℝ)^2 ≤
          32*zf^2*(z0 N:ℝ)^2/ (z7 N:ℝ):=by
        have hrew:∀ p:ℕ,32*zf^2*(z0 N:ℝ)^2/ (p:ℝ)^2 =
            (32*zf^2*(z0 N:ℝ)^2)*((1 : ℝ)/ (p:ℝ)^2):=fun p=>by ring
        simp_rw [hrew,← mul_sum]
        have hts_le:∑ p∈P.filter (fun p=>¬ p∣v6),(1 : ℝ)/ (p:ℝ)^2≤ 1/ (z7 N:ℝ) :=
          x2 (by have:=hR.2.1; omega)
            (fun p hp=>(mem_Ioc.mp (mem_filter.mp (mem_filter.mp hp).1).1).1)
        calc
          32*zf^2*(z0 N:ℝ)^2*∑ p∈P.filter (fun p=>¬ p∣v6),(1 : ℝ)/ (p:ℝ)^2
              ≤ 32*zf^2*(z0 N:ℝ)^2*(1/ (z7 N:ℝ)) :=
                mul_le_mul_of_nonneg_left hts_le (by positivity)
          _=32*zf^2*(z0 N:ℝ)^2/ (z7 N:ℝ):=by ring
      exact hsum_le.trans hR.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hprod_d:∏ p∈P.filter (fun p=>p∣v6),(1+4*zf/ (p:ℝ))^(z0 N) ≤
        (2 : ℝ)^v6.primeFactors.card:=by
      rw [← hd_sub_y]
      calc
        ∏ p∈v6.primeFactors,(1+4*zf/ (p:ℝ))^(z0 N)
            ≤ ∏ _p∈v6.primeFactors,(2 : ℝ):=by
              refine prod_le_prod (fun _ _=>by positivity [zH]) fun p hp=>?_
              have hp_pr:=Nat.prime_of_mem_primeFactors hp
              have hp_gt:z7 N< p :=
                (zk hdstar_sf.ne_zero N).mp hdstar_cop p hp_pr (Nat.dvd_of_mem_primeFactors hp)
              have hw_pos:(0 : ℝ)< z7 N:=by have:=hR.2.1; exact_mod_cast (show 0< z7 N by omega)
              have hp_ge:(z7 N:ℝ)≤ (p:ℝ):=by exact_mod_cast hp_gt.le
              have h1:1+4*zf/ (p:ℝ)≤ Real.exp (4*zf/ (p:ℝ)):=by
                linarith [Real.add_one_le_exp (4*zf/ (p:ℝ))]
              calc
                (1+4*zf/ (p:ℝ))^(z0 N)
                    ≤ (Real.exp (4*zf/ (p:ℝ)))^(z0 N) :=
                      pow_le_pow_left₀ (by positivity [zH]) h1 _
                _=Real.exp ((z0 N:ℝ)*(4*zf/ (p:ℝ))):=(Real.exp_nat_mul _ _).symm
                _≤ Real.exp (Real.log 2):=by
                      apply Real.exp_le_exp.mpr
                      have h8BK:=hR.2.2.2.2.2.2.2.2.2.2.2.1
                      have hhalf:(z0 N:ℝ)*(4*zf/ (p:ℝ))≤ 1/ 2:=by
                        rw [mul_div_assoc',div_le_iff₀ (by linarith:(0 : ℝ)< p)]
                        nlinarith [zH]
                      linarith [zC]
                _=2:=Real.exp_log (by norm_num)
        _=(2 : ℝ)^v6.primeFactors.card:=prod_const _
    have hprod_AllS_le :
        ∏ p:P,∑ S∈validS p,‖coeffS p S‖*(4*zf/ ((p:ℕ):ℝ))^S.card ≤
          Real.exp (1/ 10 : ℝ)*(2 : ℝ)^v6.primeFactors.card:=by
      have h1:∏ p:P,∑ S∈validS p,‖coeffS p S‖*(4*zf/ ((p:ℕ):ℝ))^S.card ≤
          ∏ p:P,(if (p:ℕ)∣v6 then (1+4*zf/ ((p:ℕ):ℝ))^(z0 N)
            else 1+32*zf^2*(z0 N:ℝ)^2/ ((p:ℕ):ℝ)^2) :=
        prod_le_prod (fun _ _=>sum_nonneg fun _ _=>by positivity [zH]) fun p _=>hlocal_p p
      have hcoe:(∏ p:P,(if (p:ℕ)∣v6 then (1+4*zf/ ((p:ℕ):ℝ))^(z0 N)
            else 1+32*zf^2*(z0 N:ℝ)^2/ ((p:ℕ):ℝ)^2)) =
          ∏ p∈P,(if p∣v6 then (1+4*zf/ (p:ℝ))^(z0 N)
            else 1+32*zf^2*(z0 N:ℝ)^2/ (p:ℝ)^2) :=
        Finset.prod_coe_sort P (fun p=>if p∣v6 then (1+4*zf/ (p:ℝ))^(z0 N)
          else 1+32*zf^2*(z0 N:ℝ)^2/ (p:ℝ)^2)
      rw [hcoe,Finset.prod_ite] at h1
      refine h1.trans ?_
      rw [mul_comm (Real.exp (1/ 10 : ℝ))]
      exact mul_le_mul hprod_d hprod_nd (prod_nonneg fun _ _=>by positivity [zH]) (by positivity)
    have h1eps_K:(1+εN)^(z0 N)≤ Real.exp (1/ 10 : ℝ):=by
      calc
        (1+εN)^(z0 N)≤ (Real.exp εN)^(z0 N) :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp εN]) _
        _=Real.exp ((z0 N:ℝ)*εN):=(Real.exp_nat_mul _ _).symm
        _≤ Real.exp (1/ 10 : ℝ):=Real.exp_le_exp.mpr hR.2.2.2.2.2.2.2.2.2.2.1
    have hexp_2:Real.exp (1/ 10 : ℝ)*Real.exp (1/ 10 : ℝ)≤ 2:=by
      rw [← Real.exp_add]
      have h1:=y2 (by norm_num:(0 : ℝ)≤ 1/ 10+1/ 10) (by norm_num)
      linarith
    constructor
    ·
      rw [hint_Fy_eq,norm_mul,norm_inv,Complex.norm_natCast]
      have hsum_norm:‖∑ S∈AllS,(∏ p:P,coeffS p (S p))*∏ k:Fin (z0 N),Jk S k‖ ≤
          (1+εN)^(z0 N)*(∏ k:Fin (z0 N),‖Nk A N k‖) *
          (∏ k∈Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty),
            Ik A N v7 v6 k) *
          (Real.exp (1/ 10 : ℝ)*(2 : ℝ)^v6.primeFactors.card):=by
        refine (norm_sum_le _ _).trans ?_
        refine (sum_le_sum hprod_Jk).trans ?_
        rw [← mul_sum,hsum_AllS]
        exact mul_le_mul_of_nonneg_left hprod_AllS_le (by
          refine mul_nonneg (mul_nonneg (by positivity) (prod_nonneg fun _ _=>norm_nonneg _))
            (prod_nonneg fun k _=>?_)
          unfold Ik; exact mul_nonneg (by positivity [zX])
            (setIntegral_nonneg (z6 _) fun _ _=>by positivity))
      have hprod_nn:0≤ (∏ k:Fin (z0 N),‖Nk A N k‖) *
          (∏ k∈Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty),
            Ik A N v7 v6 k) :=
        mul_nonneg (prod_nonneg fun _ _=>norm_nonneg _)
          (prod_nonneg fun k _=>by
            unfold Ik; exact mul_nonneg (by positivity [zX])
              (setIntegral_nonneg (z6 _) fun _ _=>by positivity))
      calc
        (v6:ℝ)⁻¹*‖∑ S∈AllS,(∏ p:P,coeffS p (S p))*∏ k:Fin (z0 N),Jk S k‖
            ≤ (v6:ℝ)⁻¹*((1+εN)^(z0 N)*(∏ k:Fin (z0 N),‖Nk A N k‖) *
                (∏ k∈Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty),
                  Ik A N v7 v6 k) *
                (Real.exp (1/ 10 : ℝ)*(2 : ℝ)^v6.primeFactors.card)) :=
              mul_le_mul_of_nonneg_left hsum_norm (by positivity)
        _=((1+εN)^(z0 N)*Real.exp (1/ 10 : ℝ)) *
            (((2 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
              ((∏ k:Fin (z0 N),‖Nk A N k‖) *
               ∏ k∈Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty),
                 Ik A N v7 v6 k)):=by ring
        _≤ (Real.exp (1/ 10 : ℝ)*Real.exp (1/ 10 : ℝ)) *
            (((2 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
              ((∏ k:Fin (z0 N),‖Nk A N k‖) *
               ∏ k∈Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty),
                 Ik A N v7 v6 k)):=by
              have h1:=mul_le_mul_of_nonneg_right h1eps_K (Real.exp_pos (1/ 10 : ℝ)).le
              exact mul_le_mul_of_nonneg_right h1 (mul_nonneg (by positivity) hprod_nn)
        _≤ 2*(((2 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
              ((∏ k:Fin (z0 N),‖Nk A N k‖) *
               ∏ k∈Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty),
                 Ik A N v7 v6 k)) :=
              mul_le_mul_of_nonneg_right hexp_2 (mul_nonneg (by positivity) hprod_nn)
        _=2*((2 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
              (∏ k:Fin (z0 N),‖Nk A N k‖) *
              (∏ k∈Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty),
                Ik A N v7 v6 k):=by ring
    ·
      intro hd1
      subst hd1
      rw [hint_Fy_eq]
      simp only [Nat.cast_one,inv_one,one_mul]
      let S0:P→Finset (Fin (z0 N)):=fun _=>∅
      have hS0_mem:S0∈AllS:=by
        rw [Fintype.mem_piFinset]
        intro p
        have hnd:¬ (p:ℕ)∣1:=by
          intro h; exact (mem_filter.mp p.2).2.ne_one (Nat.dvd_one.mp h)
        dsimp only [validS,S0]; rw [if_neg hnd]; exact Finset.mem_insert_self _ _
      have hS0_val:(∏ p:P,coeffS p (S0 p))*∏ k:Fin (z0 N),Jk S0 k =
          ∏ k:Fin (z0 N),Nk A N k:=by
        have hc0:∏ p:P,coeffS p (S0 p)=1:=Finset.prod_eq_one fun p _=>by
          dsimp only [coeffS,S0]; split_ifs <;> simp
        have hJk0:∀ k:Fin (z0 N),Jk S0 k=Nk A N k:=fun k=>by
          dsimp only [Jk,S0]; unfold Nk zb zu
          simp only [Nat.primeFactors_one,Finset.filter_empty,Finset.prod_empty,mul_one,
            Finset.notMem_empty,Finset.filter_false]
        rw [hc0,one_mul]
        exact Finset.prod_congr rfl fun k _=>hJk0 k
      rw [← Finset.add_sum_erase _ _ hS0_mem,hS0_val,add_sub_cancel_left]
      have hPk_empty:∀ k:Fin (z0 N),¬ (zu N v7 1 k).Nonempty:=fun k=>by
        unfold zu; simp
      have hterm_1:∀ S∈AllS.erase S0,
          ‖(∏ p:P,coeffS p (S p))*∏ k:Fin (z0 N),Jk S k‖ ≤
            (∏ k:Fin (z0 N),‖Nk A N k‖) *
            ∏ p:P,‖coeffS p (S p)‖*(4*zf/ ((p:ℕ):ℝ))^(S p).card:=by
        intro S _
        rw [norm_mul,norm_prod,norm_prod]
        have h1:∏ k:Fin (z0 N),‖Jk S k‖ ≤
            (∏ k:Fin (z0 N),‖Nk A N k‖) *
            ∏ p:P,(4*zf/ ((p:ℕ):ℝ))^(S p).card:=by
          have h2:∏ k:Fin (z0 N),‖Jk S k‖ ≤
              ∏ k:Fin (z0 N),(‖Nk A N k‖ *
                ∏ p∈Finset.univ.filter (fun p:P=>k∈S p),(4*zf/ ((p:ℕ):ℝ))):=by
            refine prod_le_prod (fun _ _=>norm_nonneg _) fun k _=>?_
            have hb:=hJk_bound S k
            rw [if_neg (hPk_empty k),one_mul] at hb
            exact hb
          rw [prod_mul_distrib] at h2
          refine h2.trans_eq ?_
          congr 1
          have h3:∀ k:Fin (z0 N),
              ∏ p∈Finset.univ.filter (fun p:P=>k∈S p),(4*zf/ ((p:ℕ):ℝ)) =
              ∏ p:P,if k∈S p then (4*zf/ ((p:ℕ):ℝ)) else 1:=fun k=>by
            rw [Finset.prod_filter]
          simp_rw [h3]; rw [Finset.prod_comm]
          refine Finset.prod_congr rfl fun p _=>?_
          rw [← Finset.prod_filter]
          have hf:Finset.univ.filter (fun k:Fin (z0 N)=>k∈S p)=S p:=by ext k; simp
          rw [hf,prod_const]
        calc
          (∏ p:P,‖coeffS p (S p)‖)*(∏ k:Fin (z0 N),‖Jk S k‖)
              ≤ (∏ p:P,‖coeffS p (S p)‖) *
                ((∏ k:Fin (z0 N),‖Nk A N k‖) *
                  ∏ p:P,(4*zf/ ((p:ℕ):ℝ))^(S p).card) :=
                mul_le_mul_of_nonneg_left h1 (prod_nonneg fun _ _=>norm_nonneg _)
          _=(∏ k:Fin (z0 N),‖Nk A N k‖) *
                ((∏ p:P,‖coeffS p (S p)‖)*∏ p:P,(4*zf/ ((p:ℕ):ℝ))^(S p).card):=by ring
          _=_:=by rw [← prod_mul_distrib]
      have hS0_term_val:(∏ p:P,‖coeffS p (S0 p)‖*(4*zf/ ((p:ℕ):ℝ))^(S0 p).card)=1 :=
        Finset.prod_eq_one fun p _=>by dsimp only [coeffS,S0]; split_ifs <;> simp
      have hsum_erase :
          ∑ S∈AllS.erase S0,∏ p:P,‖coeffS p (S p)‖*(4*zf/ ((p:ℕ):ℝ))^(S p).card =
            (∏ p:P,∑ S∈validS p,‖coeffS p S‖*(4*zf/ ((p:ℕ):ℝ))^S.card) - 1:=by
        have hadd:=Finset.add_sum_erase AllS
          (fun S=>∏ p:P,‖coeffS p (S p)‖*(4*zf/ ((p:ℕ):ℝ))^(S p).card) hS0_mem
        rw [hS0_term_val,hsum_AllS] at hadd
        linarith
      have hprod_le_exp:∏ p:P,∑ S∈validS p,‖coeffS p S‖*(4*zf/ ((p:ℕ):ℝ))^S.card ≤
          Real.exp (1/ 10 : ℝ):=by
        have h:=hprod_AllS_le
        simp only [Nat.primeFactors_one,card_empty,pow_zero,mul_one] at h
        exact h
      have hexp_15:Real.exp (1/ 10 : ℝ) - 1≤ 1/ 5:=by
        have:=y2 (by norm_num:(0 : ℝ)≤ 1/ 10) (by norm_num)
        linarith
      refine (norm_sum_le _ _).trans ((sum_le_sum hterm_1).trans ?_)
      rw [← mul_sum,hsum_erase,mul_comm]
      exact mul_le_mul_of_nonneg_right (by linarith) (prod_nonneg fun _ _=>norm_nonneg _)
  have htend:=xL (v7:=v7) hA hR hdstar_sf hdstar_cop
  constructor
  · exact le_of_tendsto htend.norm (by
      filter_upwards [Filter.eventually_ge_atTop (max (z7 N) v6)] with y hy
      exact (hFy_bounds y hy).1)
  · intro hd1
    exact le_of_tendsto (htend.sub tendsto_const_nhds).norm (by
      filter_upwards [Filter.eventually_ge_atTop (max (z7 N) v6)] with y hy
      exact (hFy_bounds y hy).2 hd1)
lemma xY {A:ℝ} (hA:1≤ A) {N:ℕ} (hR:zM A N) :
    (1/ 2 : ℝ)*((N:ℝ)/ (z4 N:ℝ))*(∏ k:Fin (z0 N),‖Nk A N k‖)≤ zY A N ∧
    0< zY A N:=by
  have hN1:1≤ N:=by
    have : (1 : ℝ)< (N:ℝ):=by linarith [Real.add_one_le_exp (2 : ℝ),hR.1]
    exact_mod_cast this.le
  have hNpos:(0 : ℝ)< N:=by positivity
  have hWpos:(0 : ℝ)< z4 N:=by exact_mod_cast w6 N
  have hKN:z0 N< N:=by
    have h1:=hR.2.2.2.2.1; have h2:=hR.2.2.2.2.2.1; omega
  have hR_gt1:∀ k:Fin (z0 N),1< z9 A N k:=fun k=>(hR.2.2.2.2.2.2.1 k).2
  have hprod_lb:((2*Real.log (N:ℝ))^(z0 N))⁻¹≤ ∏ k:Fin (z0 N),‖Nk A N k‖:=by
    have hLpos:0< Real.log (N:ℝ):=by
      have : 2≤ Real.log (N:ℝ):=by
        calc (2 : ℝ)=Real.log (Real.exp 2):=(Real.log_exp 2).symm
          _≤ Real.log (N:ℝ):=Real.log_le_log (Real.exp_pos 2) hR.1
      linarith
    calc
      ((2*Real.log (N:ℝ))^(z0 N))⁻¹
          = ∏ _k:Fin (z0 N),((1/ 2 : ℝ)/ Real.log (N:ℝ)):=by
            rw [prod_const,Finset.card_univ,Fintype.card_fin,← inv_pow]
            congr 1; field_simp
      _≤ ∏ k:Fin (z0 N),‖Nk A N k‖ :=
            prod_le_prod (fun _ _=>by positivity) fun k _=>(yl hA hR k).1
  have hprod_pos:0< ∏ k:Fin (z0 N),‖Nk A N k‖:=by
    have hLpos:0< Real.log (N:ℝ):=by
      have : 2≤ Real.log (N:ℝ):=by
        calc (2 : ℝ)=Real.log (Real.exp 2):=(Real.log_exp 2).symm
          _≤ Real.log (N:ℝ):=Real.log_le_log (Real.exp_pos 2) hR.1
      linarith
    exact lt_of_lt_of_le (by positivity) hprod_lb
  have hcrt:=yT hA hR.1 hR.2.2.2.1 hKN (by omega:0< N) hR_gt1
    squarefree_one (Nat.coprime_one_left _)
  rw [xZ] at hcrt
  have htrunc:=yp (v7:=0) hA hR.1 hR.2.2.2.1 hR_gt1
    squarefree_one (Nat.coprime_one_left _)
  simp only [Nat.primeFactors_one,card_empty,pow_zero,Nat.cast_one,div_one,one_mul] at htrunc
  have hbox:=(yY (v7:=0) hA hR squarefree_one (Nat.coprime_one_left _)).2 rfl
  have herr1:(∏ k:Fin (z0 N),(z9 A N k)^2) ≤
      (1/ 8 : ℝ)*((N:ℝ)/ (z4 N:ℝ))*(∏ k:Fin (z0 N),‖Nk A N k‖):=by
    have h1:=hR.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hN15:(1 : ℝ)≤ (N:ℝ)^((1 : ℝ)/ 5):=Real.one_le_rpow (by exact_mod_cast hN1) (by norm_num)
    have hexp1:Real.exp (-(1/ 40 : ℝ)*(Real.log (N:ℝ))^((1 : ℝ)/ 10))≤ 1:=by
      linarith [hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]
    have h2:(∏ k:Fin (z0 N),(z9 A N k)^2)/ ((N:ℝ)/ (z4 N:ℝ)) *
        (2*Real.log (N:ℝ))^(z0 N)≤ 1/ 8:=by
      have h3:(∏ k:Fin (z0 N),(z9 A N k)^2) ≤
          (N:ℝ)^((1 : ℝ)/ 5)*(∏ k:Fin (z0 N),(z9 A N k)^2):=by
        have hnn:0≤ ∏ k:Fin (z0 N),(z9 A N k)^2:=prod_nonneg fun _ _=>sq_nonneg _
        nlinarith
      have h4:(∏ k:Fin (z0 N),(z9 A N k)^2)/ ((N:ℝ)/ (z4 N:ℝ)) *
          (2*Real.log (N:ℝ))^(z0 N) ≤
          (N:ℝ)^((1 : ℝ)/ 5)*(∏ k:Fin (z0 N),(z9 A N k)^2) /
          ((N:ℝ)/ (z4 N:ℝ))*(2*Real.log (N:ℝ))^(z0 N):=by
        have hLpos:0< Real.log (N:ℝ):=by
          have : 2≤ Real.log (N:ℝ):=by
            calc (2 : ℝ)=Real.log (Real.exp 2):=(Real.log_exp 2).symm
              _≤ Real.log (N:ℝ):=Real.log_le_log (Real.exp_pos 2) hR.1
          linarith
        gcongr
      linarith
    have hLpos:0< Real.log (N:ℝ):=by
      have : 2≤ Real.log (N:ℝ):=by
        calc (2 : ℝ)=Real.log (Real.exp 2):=(Real.log_exp 2).symm
          _≤ Real.log (N:ℝ):=Real.log_le_log (Real.exp_pos 2) hR.1
      linarith
    have hpow_pos:0< (2*Real.log (N:ℝ))^(z0 N):=by positivity
    have h3:(∏ k:Fin (z0 N),(z9 A N k)^2) ≤
        (1/ 8 : ℝ)*((N:ℝ)/ (z4 N:ℝ))*((2*Real.log (N:ℝ))^(z0 N))⁻¹:=by
      rw [← div_eq_mul_inv,le_div_iff₀ hpow_pos]
      have h4:(∏ k:Fin (z0 N),(z9 A N k)^2)*(2*Real.log (N:ℝ))^(z0 N) /
          ((N:ℝ)/ (z4 N:ℝ))≤ 1/ 8:=by
        simpa [div_mul_eq_mul_div] using h2
      have:=(div_le_iff₀ (div_pos hNpos hWpos)).mp h4
      linarith
    calc
      (∏ k:Fin (z0 N),(z9 A N k)^2)
          ≤ (1/ 8 : ℝ)*((N:ℝ)/ (z4 N:ℝ))*((2*Real.log (N:ℝ))^(z0 N))⁻¹:=h3
      _≤ (1/ 8 : ℝ)*((N:ℝ)/ (z4 N:ℝ))*(∏ k:Fin (z0 N),‖Nk A N k‖) :=
          mul_le_mul_of_nonneg_left hprod_lb (by positivity)
  have herr2:((N:ℝ)/ (z4 N:ℝ)) *
      (Real.exp (3*(z0 N:ℝ)*(2*Real.log (Real.log (N:ℝ))+45)) *
        (2*(z0 N:ℝ)*zA*Real.exp (-(1/ 10 : ℝ)*Real.sqrt (z3 N)))) ≤
      (1/ 8 : ℝ)*((N:ℝ)/ (z4 N:ℝ))*(∏ k:Fin (z0 N),‖Nk A N k‖):=by
    have h1:=hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hexp1:Real.exp (-(1/ 40 : ℝ)*(Real.log (N:ℝ))^((1 : ℝ)/ 10))≤ 1:=by
      linarith [hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]
    have hLpos:0< Real.log (N:ℝ):=by
      have : 2≤ Real.log (N:ℝ):=by
        calc (2 : ℝ)=Real.log (Real.exp 2):=(Real.log_exp 2).symm
          _≤ Real.log (N:ℝ):=Real.log_le_log (Real.exp_pos 2) hR.1
      linarith
    have hpow_pos:0< (2*Real.log (N:ℝ))^(z0 N):=by positivity
    have h2:Real.exp (3*(z0 N:ℝ)*(2*Real.log (Real.log (N:ℝ))+45)) *
        (2*(z0 N:ℝ)*zA*Real.exp (-(1/ 10 : ℝ)*Real.sqrt (z3 N))) ≤
        (1/ 8 : ℝ)*((2*Real.log (N:ℝ))^(z0 N))⁻¹:=by
      rw [← div_eq_mul_inv,le_div_iff₀ hpow_pos]
      linarith
    calc
      ((N:ℝ)/ (z4 N:ℝ)) *
          (Real.exp (3*(z0 N:ℝ)*(2*Real.log (Real.log (N:ℝ))+45)) *
            (2*(z0 N:ℝ)*zA*Real.exp (-(1/ 10 : ℝ)*Real.sqrt (z3 N))))
          ≤ ((N:ℝ)/ (z4 N:ℝ))*((1/ 8 : ℝ)*((2*Real.log (N:ℝ))^(z0 N))⁻¹) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
      _=(1/ 8 : ℝ)*((N:ℝ)/ (z4 N:ℝ))*((2*Real.log (N:ℝ))^(z0 N))⁻¹:=by ring
      _≤ (1/ 8 : ℝ)*((N:ℝ)/ (z4 N:ℝ))*(∏ k:Fin (z0 N),‖Nk A N k‖) :=
            mul_le_mul_of_nonneg_left hprod_lb (by positivity)
  have hdiff_total:‖(zY A N:ℂ) - (((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ)*∏ k:Fin (z0 N),Nk A N k‖ ≤
      (9/ 20 : ℝ)*((N:ℝ)/ (z4 N:ℝ))*(∏ k:Fin (z0 N),‖Nk A N k‖):=by
    have hdecomp:(zY A N:ℂ) - (((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ)*∏ k:Fin (z0 N),Nk A N k =
        ((zY A N:ℂ) - (((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ)*∫ ω,zW A N 0 1 ω ∂(PK (z0 N))) +
        (((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ) *
          ((∫ ω,zW A N 0 1 ω ∂(PK (z0 N))) -
           (∫ ω in y0 (z0 N) (z3 N),zW A N 0 1 ω ∂(PK (z0 N)))) +
        (((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ) *
          ((∫ ω in y0 (z0 N) (z3 N),zW A N 0 1 ω ∂(PK (z0 N))) -
           ∏ k:Fin (z0 N),Nk A N k):=by ring
    rw [hdecomp]
    have htri:‖((zY A N:ℂ) - (((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ)*∫ ω,zW A N 0 1 ω ∂(PK (z0 N))) +
          (((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ) *
            ((∫ ω,zW A N 0 1 ω ∂(PK (z0 N))) -
             (∫ ω in y0 (z0 N) (z3 N),zW A N 0 1 ω ∂(PK (z0 N)))) +
          (((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ) *
            ((∫ ω in y0 (z0 N) (z3 N),zW A N 0 1 ω ∂(PK (z0 N))) -
             ∏ k:Fin (z0 N),Nk A N k)‖ ≤
        ‖(zY A N:ℂ) - (((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ)*∫ ω,zW A N 0 1 ω ∂(PK (z0 N))‖ +
        ((N:ℝ)/ (z4 N:ℝ)) *
          ‖(∫ ω,zW A N 0 1 ω ∂(PK (z0 N))) -
           (∫ ω in y0 (z0 N) (z3 N),zW A N 0 1 ω ∂(PK (z0 N)))‖ +
        ((N:ℝ)/ (z4 N:ℝ)) *
          ‖(∫ ω in y0 (z0 N) (z3 N),zW A N 0 1 ω ∂(PK (z0 N))) -
           ∏ k:Fin (z0 N),Nk A N k‖:=by
      calc
        _≤ ‖((zY A N:ℂ) - (((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ)*∫ ω,zW A N 0 1 ω ∂(PK (z0 N))) +
              (((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ) *
                ((∫ ω,zW A N 0 1 ω ∂(PK (z0 N))) -
                 (∫ ω in y0 (z0 N) (z3 N),zW A N 0 1 ω ∂(PK (z0 N))))‖ +
            ‖(((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ) *
              ((∫ ω in y0 (z0 N) (z3 N),zW A N 0 1 ω ∂(PK (z0 N))) -
               ∏ k:Fin (z0 N),Nk A N k)‖:=norm_add_le _ _
        _≤ ‖(zY A N:ℂ) - (((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ)*∫ ω,zW A N 0 1 ω ∂(PK (z0 N))‖ +
            ‖(((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ) *
              ((∫ ω,zW A N 0 1 ω ∂(PK (z0 N))) -
               (∫ ω in y0 (z0 N) (z3 N),zW A N 0 1 ω ∂(PK (z0 N))))‖ +
            ‖(((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ) *
              ((∫ ω in y0 (z0 N) (z3 N),zW A N 0 1 ω ∂(PK (z0 N))) -
               ∏ k:Fin (z0 N),Nk A N k)‖:=by gcongr; exact norm_add_le _ _
        _=_:=by
            rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
    have h2:((N:ℝ)/ (z4 N:ℝ)) *
        ‖(∫ ω,zW A N 0 1 ω ∂(PK (z0 N))) -
         (∫ ω in y0 (z0 N) (z3 N),zW A N 0 1 ω ∂(PK (z0 N)))‖ ≤
        (1/ 8 : ℝ)*((N:ℝ)/ (z4 N:ℝ))*(∏ k:Fin (z0 N),‖Nk A N k‖) :=
      (mul_le_mul_of_nonneg_left htrunc (by positivity)).trans herr2
    have h3:((N:ℝ)/ (z4 N:ℝ)) *
        ‖(∫ ω in y0 (z0 N) (z3 N),zW A N 0 1 ω ∂(PK (z0 N))) -
         ∏ k:Fin (z0 N),Nk A N k‖ ≤
        (1/ 5 : ℝ)*((N:ℝ)/ (z4 N:ℝ))*(∏ k:Fin (z0 N),‖Nk A N k‖):=by
      have:=mul_le_mul_of_nonneg_left hbox (by positivity:(0 : ℝ)≤ (N:ℝ)/ (z4 N:ℝ))
      linarith
    linarith [hcrt.trans herr1]
  have hZ_nn:0≤ zY A N:=by
    rw [← xZ (v7:=0)]; exact xK _ _ _ _
  have hmain_lb:(1/ 2 : ℝ)*((N:ℝ)/ (z4 N:ℝ))*(∏ k:Fin (z0 N),‖Nk A N k‖)≤ zY A N:=by
    have htri:‖(((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ)*∏ k:Fin (z0 N),Nk A N k‖ ≤
        ‖(zY A N:ℂ)‖ +
        ‖(zY A N:ℂ) - (((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ)*∏ k:Fin (z0 N),Nk A N k‖:=by
      have:=norm_add_le (zY A N:ℂ)
        ((((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ)*(∏ k:Fin (z0 N),Nk A N k) - (zY A N:ℂ))
      rw [add_sub_cancel,norm_sub_rev] at this
      exact this
    rw [norm_mul,norm_prod,Complex.norm_real,Complex.norm_real,
      Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg hZ_nn] at htri
    linarith [mul_pos (div_pos hNpos hWpos) hprod_pos]
  exact ⟨hmain_lb,lt_of_lt_of_le (by positivity) hmain_lb⟩
theorem yE {A:ℝ} (hA:1≤ A) {N v7 v6:ℕ}
    (hR:zM A N) (hkstarN:v7< N)
    (hdstar_sf:Squarefree v6) (hdstar_cop:Nat.Coprime v6 (z4 N))
    (hdstar_le:(v6:ℝ)≤ (N:ℝ)^((1 : ℝ)/ 5)) :
    xb A N v7 v6/ zY A N ≤
      4*((2 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
        (∏ k∈Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty),
          Ik A N v7 v6 k) +
      ((4 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
        Real.exp (-(1/ 40 : ℝ)*(Real.log (N:ℝ))^((1 : ℝ)/ 10)):=by
  have hNpos:(0 : ℝ)< N:=by linarith [Real.add_one_le_exp (2 : ℝ),hR.1]
  have hWpos:(0 : ℝ)< z4 N:=by exact_mod_cast w6 N
  have hd_pos:(0 : ℝ)< v6:=by exact_mod_cast Nat.pos_of_ne_zero hdstar_sf.ne_zero
  have hKN:z0 N< N:=by have:=hR.2.2.2.2.1; have:=hR.2.2.2.2.2.1; omega
  have hR_gt1:∀ k:Fin (z0 N),1< z9 A N k:=fun k=>(hR.2.2.2.2.2.2.1 k).2
  have hLpos:0< Real.log (N:ℝ):=by
    have : 2≤ Real.log (N:ℝ):=by
      calc (2 : ℝ)=Real.log (Real.exp 2):=(Real.log_exp 2).symm
        _≤ Real.log (N:ℝ):=Real.log_le_log (Real.exp_pos 2) hR.1
    linarith
  have hprod_lb:((2*Real.log (N:ℝ))^(z0 N))⁻¹≤ ∏ k:Fin (z0 N),‖Nk A N k‖:=by
    calc
      ((2*Real.log (N:ℝ))^(z0 N))⁻¹
          = ∏ _k:Fin (z0 N),((1/ 2 : ℝ)/ Real.log (N:ℝ)):=by
            rw [prod_const,Finset.card_univ,Fintype.card_fin,← inv_pow]
            congr 1; field_simp
      _≤ ∏ k:Fin (z0 N),‖Nk A N k‖ :=
            prod_le_prod (fun _ _=>by positivity) fun k _=>(yl hA hR k).1
  have hprod_pos:0< ∏ k:Fin (z0 N),‖Nk A N k‖:=lt_of_lt_of_le (by positivity) hprod_lb
  obtain ⟨hZ_lb,hZ_pos⟩:=xY hA hR
  have hcrt:=yT hA hR.1 hR.2.2.2.1 hKN hkstarN hR_gt1 hdstar_sf hdstar_cop
  have htrunc:=yp (v7:=v7) hA hR.1 hR.2.2.2.1 hR_gt1 hdstar_sf hdstar_cop
  have hbox:=(yY (v7:=v7) hA hR hdstar_sf hdstar_cop).1
  have hP_le:xb A N v7 v6 ≤
      (∏ k:Fin (z0 N),(z9 A N k)^2) +
      ((N:ℝ)/ (z4 N:ℝ)) *
        (((4 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
          Real.exp (3*(z0 N:ℝ)*(2*Real.log (Real.log (N:ℝ))+45)) *
          (2*(z0 N:ℝ)*zA*Real.exp (-(1/ 10 : ℝ)*Real.sqrt (z3 N)))) +
      ((N:ℝ)/ (z4 N:ℝ)) *
        (2*((2 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
          (∏ k:Fin (z0 N),‖Nk A N k‖) *
          (∏ k∈Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty),
            Ik A N v7 v6 k)):=by
    have hP_norm:xb A N v7 v6=‖(xb A N v7 v6:ℂ)‖:=by
      rw [Complex.norm_real,Real.norm_of_nonneg (xK _ _ _ _)]
    rw [hP_norm]
    have hdecomp:(xb A N v7 v6:ℂ) =
        ((xb A N v7 v6:ℂ) - (((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ)*∫ ω,zW A N v7 v6 ω ∂(PK (z0 N))) +
        (((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ) *
          ((∫ ω,zW A N v7 v6 ω ∂(PK (z0 N))) -
           (∫ ω in y0 (z0 N) (z3 N),zW A N v7 v6 ω ∂(PK (z0 N)))) +
        (((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ) *
          (∫ ω in y0 (z0 N) (z3 N),zW A N v7 v6 ω ∂(PK (z0 N))):=by ring
    rw [hdecomp]
    calc
      ‖_‖≤ ‖(xb A N v7 v6:ℂ) - (((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ)*∫ ω,zW A N v7 v6 ω ∂(PK (z0 N))‖ +
            ‖(((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ) *
              ((∫ ω,zW A N v7 v6 ω ∂(PK (z0 N))) -
               (∫ ω in y0 (z0 N) (z3 N),zW A N v7 v6 ω ∂(PK (z0 N))))‖ +
            ‖(((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ) *
              (∫ ω in y0 (z0 N) (z3 N),zW A N v7 v6 ω ∂(PK (z0 N)))‖:=by
            calc
              _≤ ‖((xb A N v7 v6:ℂ) - (((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ)*∫ ω,zW A N v7 v6 ω ∂(PK (z0 N))) +
                    (((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ) *
                      ((∫ ω,zW A N v7 v6 ω ∂(PK (z0 N))) -
                       (∫ ω in y0 (z0 N) (z3 N),zW A N v7 v6 ω ∂(PK (z0 N))))‖ +
                  ‖(((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ) *
                    (∫ ω in y0 (z0 N) (z3 N),zW A N v7 v6 ω ∂(PK (z0 N)))‖:=norm_add_le _ _
              _≤ _:=by gcongr; exact norm_add_le _ _
      _=‖(xb A N v7 v6:ℂ) - (((N:ℝ)/ (z4 N:ℝ):ℝ):ℂ)*∫ ω,zW A N v7 v6 ω ∂(PK (z0 N))‖ +
            ((N:ℝ)/ (z4 N:ℝ)) *
              ‖(∫ ω,zW A N v7 v6 ω ∂(PK (z0 N))) -
               (∫ ω in y0 (z0 N) (z3 N),zW A N v7 v6 ω ∂(PK (z0 N)))‖ +
            ((N:ℝ)/ (z4 N:ℝ)) *
              ‖∫ ω in y0 (z0 N) (z3 N),zW A N v7 v6 ω ∂(PK (z0 N))‖:=by
            rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
      _≤ _:=by
            gcongr
  set D:=(1/ 2 : ℝ)*((N:ℝ)/ (z4 N:ℝ))*(∏ k:Fin (z0 N),‖Nk A N k‖)
  have hD_pos:0< D:=by positivity
  have hdiv_le:xb A N v7 v6/ zY A N≤ xb A N v7 v6/ D :=
    div_le_div_of_nonneg_left (xK _ _ _ _) hD_pos hZ_lb
  refine hdiv_le.trans ((div_le_div_of_nonneg_right hP_le hD_pos.le).trans ?_)
  rw [add_div,add_div]
  have hpow_pos:0< (2*Real.log (N:ℝ))^(z0 N):=by positivity
  have h4j_ge1:(1 : ℝ)≤ (4 : ℝ)^v6.primeFactors.card:=one_le_pow₀ (by norm_num)
  have ht1:(∏ k:Fin (z0 N),(z9 A N k)^2)/ D ≤
      (1/ 4 : ℝ)*((4 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
        Real.exp (-(1/ 40 : ℝ)*(Real.log (N:ℝ))^((1 : ℝ)/ 10)):=by
    have h1:=hR.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hD_lb:(1/ 2 : ℝ)*((N:ℝ)/ (z4 N:ℝ))*((2*Real.log (N:ℝ))^(z0 N))⁻¹≤ D :=
      mul_le_mul_of_nonneg_left hprod_lb (by positivity)
    calc
      (∏ k:Fin (z0 N),(z9 A N k)^2)/ D
          ≤ (∏ k:Fin (z0 N),(z9 A N k)^2) /
              ((1/ 2 : ℝ)*((N:ℝ)/ (z4 N:ℝ))*((2*Real.log (N:ℝ))^(z0 N))⁻¹) :=
            div_le_div_of_nonneg_left (prod_nonneg fun _ _=>sq_nonneg _) (by positivity) hD_lb
      _=2*((∏ k:Fin (z0 N),(z9 A N k)^2)/ ((N:ℝ)/ (z4 N:ℝ)) *
            (2*Real.log (N:ℝ))^(z0 N)):=by
            field_simp [hNpos.ne',hWpos.ne',hpow_pos.ne']
      _≤ 2*(((4 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
            ((N:ℝ)^((1 : ℝ)/ 5)*(∏ k:Fin (z0 N),(z9 A N k)^2) /
              ((N:ℝ)/ (z4 N:ℝ))*(2*Real.log (N:ℝ))^(z0 N))):=by
            have hfac:1≤ ((4 : ℝ)^v6.primeFactors.card/ (v6:ℝ))*(N:ℝ)^((1 : ℝ)/ 5):=by
              rw [div_mul_eq_mul_div,one_le_div hd_pos]
              nlinarith
            have hnn:0≤ (∏ k:Fin (z0 N),(z9 A N k)^2)/ ((N:ℝ)/ (z4 N:ℝ)) *
                (2*Real.log (N:ℝ))^(z0 N):=by
              refine mul_nonneg (div_nonneg (prod_nonneg fun _ _=>sq_nonneg _) (by positivity)) (by positivity)
            have hrew:((4 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
                ((N:ℝ)^((1 : ℝ)/ 5)*(∏ k:Fin (z0 N),(z9 A N k)^2) /
                  ((N:ℝ)/ (z4 N:ℝ))*(2*Real.log (N:ℝ))^(z0 N)) =
                (((4 : ℝ)^v6.primeFactors.card/ (v6:ℝ))*(N:ℝ)^((1 : ℝ)/ 5)) *
                ((∏ k:Fin (z0 N),(z9 A N k)^2)/ ((N:ℝ)/ (z4 N:ℝ)) *
                  (2*Real.log (N:ℝ))^(z0 N)):=by ring
            rw [hrew]
            nlinarith
      _≤ 2*(((4 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
            ((1/ 8 : ℝ)*Real.exp (-(1/ 40 : ℝ)*(Real.log (N:ℝ))^((1 : ℝ)/ 10)))):=by
            gcongr
      _=(1/ 4 : ℝ)*((4 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
            Real.exp (-(1/ 40 : ℝ)*(Real.log (N:ℝ))^((1 : ℝ)/ 10)):=by ring
  have ht2:(((N:ℝ)/ (z4 N:ℝ)) *
        (((4 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
          Real.exp (3*(z0 N:ℝ)*(2*Real.log (Real.log (N:ℝ))+45)) *
          (2*(z0 N:ℝ)*zA*Real.exp (-(1/ 10 : ℝ)*Real.sqrt (z3 N)))))/ D ≤
      (1/ 4 : ℝ)*((4 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
        Real.exp (-(1/ 40 : ℝ)*(Real.log (N:ℝ))^((1 : ℝ)/ 10)):=by
    have h1:=hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hD_lb:(1/ 2 : ℝ)*((N:ℝ)/ (z4 N:ℝ))*((2*Real.log (N:ℝ))^(z0 N))⁻¹≤ D :=
      mul_le_mul_of_nonneg_left hprod_lb (by positivity)
    have hnum_nn:0≤ ((N:ℝ)/ (z4 N:ℝ)) *
        (((4 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
          Real.exp (3*(z0 N:ℝ)*(2*Real.log (Real.log (N:ℝ))+45)) *
          (2*(z0 N:ℝ)*zA*Real.exp (-(1/ 10 : ℝ)*Real.sqrt (z3 N)))):=by
      have:=yC; positivity
    calc
      _≤ (((N:ℝ)/ (z4 N:ℝ)) *
            (((4 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
              Real.exp (3*(z0 N:ℝ)*(2*Real.log (Real.log (N:ℝ))+45)) *
              (2*(z0 N:ℝ)*zA*Real.exp (-(1/ 10 : ℝ)*Real.sqrt (z3 N))))) /
          ((1/ 2 : ℝ)*((N:ℝ)/ (z4 N:ℝ))*((2*Real.log (N:ℝ))^(z0 N))⁻¹) :=
        div_le_div_of_nonneg_left hnum_nn (by positivity) hD_lb
      _=2*((4 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
            (Real.exp (3*(z0 N:ℝ)*(2*Real.log (Real.log (N:ℝ))+45)) *
              (2*(z0 N:ℝ)*zA*Real.exp (-(1/ 10 : ℝ)*Real.sqrt (z3 N))) *
              (2*Real.log (N:ℝ))^(z0 N)):=by
            field_simp [hNpos.ne',hWpos.ne',hpow_pos.ne']
      _≤ 2*((4 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
            ((1/ 8 : ℝ)*Real.exp (-(1/ 40 : ℝ)*(Real.log (N:ℝ))^((1 : ℝ)/ 10))):=by
            gcongr
      _=(1/ 4 : ℝ)*((4 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
            Real.exp (-(1/ 40 : ℝ)*(Real.log (N:ℝ))^((1 : ℝ)/ 10)):=by ring
  have ht3:(((N:ℝ)/ (z4 N:ℝ)) *
        (2*((2 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
          (∏ k:Fin (z0 N),‖Nk A N k‖) *
          (∏ k∈Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty),
            Ik A N v7 v6 k)))/ D =
      4*((2 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
        (∏ k∈Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty),
          Ik A N v7 v6 k):=by
    dsimp only [D]
    have hNW_ne:(N:ℝ)/ (z4 N:ℝ)≠0:=(div_pos hNpos hWpos).ne'
    field_simp [hNW_ne,hprod_pos.ne']; ring
  rw [ht3]
  have herr_nn:0≤ ((4 : ℝ)^v6.primeFactors.card/ (v6:ℝ)) *
      Real.exp (-(1/ 40 : ℝ)*(Real.log (N:ℝ))^((1 : ℝ)/ 10)):=by positivity
  linarith
end
end Erdos413Sieve
namespace Erdos413Sieve
open Finset Filter Topology Complex Real MeasureTheory
open Erdos413Bump Erdos413Mertens Erdos413Moments
open scoped BigOperators
noncomputable section
private lemma zG {T:Finset ℕ} (hT:∀ p∈T,p.Prime) :
    Squarefree (∏ p∈T,p)∧(∏ p∈T,p).primeFactors=T:=by
  have hsf:Squarefree (∏ p∈T,p):=by
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ fun p hp=>(hT p hp).squarefree
    intro p hp q hq hpq
    show IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hT p hp) (hT q hq)).mpr hpq
  refine ⟨hsf,?_⟩
  ext q
  simp only [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hq,hqd,_⟩
    rcases (hq.prime.dvd_finsetProd_iff id).mp hqd with ⟨p,hpT,hqp⟩
    have:=(Nat.prime_dvd_prime_iff_eq hq (hT p hpT)).mp hqp
    rwa [this]
  · intro hqT
    exact ⟨hT q hqT,dvd_prod_of_mem _ hqT,hsf.ne_zero⟩
private lemma yK {N:ℕ} {T:Finset ℕ}
    (hT:∀ p∈T,p.Prime∧z7 N< p) :
    Nat.Coprime (∏ p∈T,p) (z4 N):=by
  have hsf:=(zG fun p hp=>(hT p hp).1).1
  rw [zk hsf.ne_zero N]
  intro q hq hqd
  rcases (hq.prime.dvd_finsetProd_iff id).mp hqd with ⟨p,hpT,hqp⟩
  have heq:=(Nat.prime_dvd_prime_iff_eq hq (hT p hpT).1).mp hqp
  rw [heq]
  exact (hT p hpT).2
def xj:ℝ:=4*(z8/ c0)+5
lemma w0:0< xj:=by
  unfold xj
  have:=y4; have:=zX; positivity
theorem v4 {A:ℝ} (hA:1≤ A) :
    ∀ᶠ N:ℕ in atTop,
      zM A N ∧
      ∀ (v7 s j:ℕ),2≤ v7→v7≤ yI N →
        1≤ j→j≤ s→(s:ℝ)≤ 2*A*Real.log (v7:ℝ) →
        ∀ T∈(z2 ⌊Rk A N v7⌋₊ ⌊Tk A N v7⌋₊).powersetCard j,
          xb A N v7 (∏ p∈T,p)/ zY A N ≤
            xj*(8 : ℝ)^s/ (∏ p∈T,(p:ℝ)):=by
  have hL_4B:∀ᶠ N:ℕ in atTop,
      4000*(A+1)^2*(Real.log (N:ℝ))^(-(1/ 2 : ℝ))≤ c0/ z8:=by
    have h0:Tendsto (fun L:ℝ=>4000*(A+1)^2*L^(-(1/ 2 : ℝ))) atTop (𝓝 0):=by
      simpa using (tendsto_rpow_neg_atTop (by norm_num:(0 : ℝ)< 1/ 2)).const_mul (4000*(A+1)^2)
    have hpos:0< c0/ z8:=div_pos zX y4
    have hev:∀ᶠ L:ℝ in atTop,4000*(A+1)^2*L^(-(1/ 2 : ℝ))≤ c0/ z8:=by
      filter_upwards [h0.eventually (Iio_mem_nhds hpos)] with L hL; exact hL.le
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually hev
  filter_upwards [xd hA,hL_4B] with N hR h4B
  refine ⟨hR,fun v7 s j hkstar2 hkstarKp hj1 hjs hsA T hT=>?_⟩
  rcases mem_powersetCard.mp hT with ⟨hTsub,hTcard⟩
  set L:=Real.log (N:ℝ)
  have hNpos:(0 : ℝ)< N:=by linarith [Real.add_one_le_exp (2 : ℝ),hR.1]
  have hN1:(1 : ℝ)≤ N:=by linarith [Real.add_one_le_exp (2 : ℝ),hR.1]
  have hL2:2≤ L:=by
    calc (2 : ℝ)=Real.log (Real.exp 2):=(Real.log_exp 2).symm
      _≤ L:=Real.log_le_log (Real.exp_pos 2) hR.1
  have hT_info:∀ p∈T,p.Prime∧z7 N< p∧(p:ℝ)≤ Tk A N v7:=by
    intro p hp
    have hmem:=hTsub hp
    simp only [z2,mem_filter,mem_Ioc] at hmem
    refine ⟨hmem.2,?_,?_⟩
    · have hw_le:z7 N≤ ⌊Rk A N v7⌋₊:=by
        by_cases hcond:1≤ v7∧v7≤ z0 N
        · have hEq:Rk A N v7=z9 A N ⟨v7 - 1,by omega⟩:=by
            unfold z9; dsimp; congr 1; omega
          rw [hEq]; exact Nat.floor_mono (hR.2.2.2.2.2.2.1 ⟨v7 - 1,by omega⟩).1
        · unfold Rk; rw [if_neg hcond]; exact le_rfl
      omega
    · have hTk_pos:0≤ Tk A N v7:=by unfold Tk; positivity
      exact (Nat.cast_le.mpr hmem.1.2).trans (Nat.floor_le hTk_pos)
  set v6:=∏ p∈T,p
  obtain ⟨hdstar_sf,hdstar_pf⟩:=zG fun p hp=>(hT_info p hp).1
  have hdstar_cop:Nat.Coprime v6 (z4 N) :=
    yK fun p hp=>⟨(hT_info p hp).1,(hT_info p hp).2.1⟩
  have hdstar_card:v6.primeFactors.card=j:=by rw [hdstar_pf,hTcard]
  have hdstar_cast:(v6:ℝ)=∏ p∈T,(p:ℝ):=by dsimp [v6]; rw [Nat.cast_prod]
  have hdstar_pos:(0 : ℝ)< v6:=by exact_mod_cast Nat.pos_of_ne_zero hdstar_sf.ne_zero
  have hdstar_le:(v6:ℝ)≤ (N:ℝ)^((1 : ℝ)/ 5):=by
    have hlogk_pos:0< Real.log (v7:ℝ):=Real.log_pos (by exact_mod_cast (show 1< v7 by omega))
    have hTk_nn:0≤ Tk A N v7:=by unfold Tk; positivity
    calc
      (v6:ℝ)=∏ p∈T,(p:ℝ):=hdstar_cast
      _≤ ∏ _p∈T,Tk A N v7:=prod_le_prod (fun _ _=>by positivity) fun p hp=>(hT_info p hp).2.2
      _=(Tk A N v7)^j:=by rw [prod_const,hTcard]
      _=(N:ℝ)^((j:ℝ)/ (10*A*Real.log (v7:ℝ))):=by
            unfold Tk
            rw [← Real.rpow_natCast,← Real.rpow_mul hNpos.le]
            congr 1; ring
      _≤ (N:ℝ)^((1 : ℝ)/ 5):=by
            apply Real.rpow_le_rpow_of_exponent_le hN1
            rw [div_le_iff₀ (by positivity)]
            have hj_le_s:(j:ℝ)≤ (s:ℝ):=by exact_mod_cast hjs
            linarith
  have hkstarN:v7< N:=by have:=hR.2.2.2.2.2.1; omega
  have h51:=yE hA hR hkstarN hdstar_sf hdstar_cop hdstar_le
  rw [hdstar_card,hdstar_cast] at h51
  have herr_le:((4 : ℝ)^j/ ∏ p∈T,(p:ℝ)) *
        Real.exp (-(1/ 40 : ℝ)*L^((1 : ℝ)/ 10)) ≤
      (8 : ℝ)^s/ ∏ p∈T,(p:ℝ):=by
    have hexp1:Real.exp (-(1/ 40 : ℝ)*L^((1 : ℝ)/ 10))≤ 1:=by
      linarith [hR.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]
    have h48:(4 : ℝ)^j≤ (8 : ℝ)^s:=by
      calc (4 : ℝ)^j≤ (8 : ℝ)^j:=pow_le_pow_left₀ (by norm_num) (by norm_num) j
        _≤ (8 : ℝ)^s:=pow_le_pow_right₀ (by norm_num) hjs
    have hprod_pos:0< ∏ p∈T,(p:ℝ):=by rw [← hdstar_cast]; exact hdstar_pos
    calc
      ((4 : ℝ)^j/ ∏ p∈T,(p:ℝ))*Real.exp (-(1/ 40 : ℝ)*L^((1 : ℝ)/ 10))
          ≤ ((4 : ℝ)^j/ ∏ p∈T,(p:ℝ))*1 :=
            mul_le_mul_of_nonneg_left hexp1 (by positivity)
      _=(4 : ℝ)^j/ ∏ p∈T,(p:ℝ):=mul_one _
      _≤ (8 : ℝ)^s/ ∏ p∈T,(p:ℝ):=div_le_div_of_nonneg_right h48 hprod_pos.le
  by_cases hkK:v7≤ z0 N
  ·
    let k₀ : Fin (z0 N):=⟨v7 - 1,by omega⟩
    have hk0_eq:k₀.1+1=v7:=by dsimp [k₀]; omega
    have hPk_k0:zu N v7 v6 k₀=T:=by
      unfold zu
      rw [hdstar_pf]
      ext p; simp only [mem_filter,and_iff_left_iff_imp]
      intro _; rw [hk0_eq,sub_self]; exact dvd_zero _
    have hfilt_eq:Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty)={k₀}:=by
      ext k
      simp only [mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
      constructor
      · rintro ⟨p,hp⟩
        rcases mem_filter.mp hp with ⟨hp_pf,hpdvd⟩
        rw [hdstar_pf] at hp_pf
        have hpK:z0 N< p:=by have:=(hT_info p hp_pf).2.1; have:=hR.2.2.2.1; omega
        have hk0_dvd:(p:ℤ)∣((v7:ℤ) - ((k₀.1+1 : ℕ):ℤ)):=by
          rw [hk0_eq,sub_self]; exact dvd_zero _
        exact yP hpK hpdvd hk0_dvd
      · rintro rfl
        rw [hPk_k0]
        exact Finset.card_pos.mp (by omega)
    have hIk0_le:Ik A N v7 v6 k₀≤ (z8/ c0)*(4 : ℝ)^j:=by
      unfold Ik
      have hfac_le:∀ x:ℝ × ℝ,‖zb A N v7 v6 k₀ x‖≤ (4 : ℝ)^j:=fun x=>by
        have h:=ye (v7:=v7) (v6:=v6) hR k₀ x
        rwa [hPk_k0,hTcard] at h
      have hfac_c:Continuous (zb A N v7 v6 k₀):=zL A N v7 v6 k₀
      have hint_lhs:IntegrableOn (fun x=>‖kernel x‖*‖zb A N v7 v6 k₀ x‖)
          (zz (z3 N)) zn:=by
        refine (zc.norm.mul_const ((4 : ℝ)^j)).integrableOn.mono'
          (ym.norm.mul hfac_c.norm).aestronglyMeasurable ?_
        refine ae_of_all _ fun x=>?_
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
        exact mul_le_mul_of_nonneg_left (hfac_le x) (norm_nonneg _)
      calc
        (1/ c0)*∫ x in zz (z3 N),‖kernel x‖*‖zb A N v7 v6 k₀ x‖ ∂zn
            ≤ (1/ c0)*∫ x in zz (z3 N),‖kernel x‖*(4 : ℝ)^j ∂zn :=
              mul_le_mul_of_nonneg_left
                (setIntegral_mono_on hint_lhs (zc.norm.mul_const ((4 : ℝ)^j)).integrableOn
                  (z6 _) fun x _=>mul_le_mul_of_nonneg_left (hfac_le x) (norm_nonneg _))
                (by positivity [zX])
        _≤ (1/ c0)*∫ x:ℝ × ℝ,‖kernel x‖*(4 : ℝ)^j ∂zn :=
              mul_le_mul_of_nonneg_left
                (setIntegral_le_integral (zc.norm.mul_const ((4 : ℝ)^j))
                  (ae_of_all _ fun _=>by positivity))
                (by positivity [zX])
        _=(z8/ c0)*(4 : ℝ)^j:=by
              rw [integral_mul_const]; unfold z8; ring
    rw [hfilt_eq,Finset.prod_singleton] at h51
    have hprod_pos:0< ∏ p∈T,(p:ℝ):=by rw [← hdstar_cast]; exact hdstar_pos
    have hmain_le:4*((2 : ℝ)^j/ ∏ p∈T,(p:ℝ))*Ik A N v7 v6 k₀ ≤
        4*(z8/ c0)*(8 : ℝ)^s/ ∏ p∈T,(p:ℝ):=by
      have h8j:(2 : ℝ)^j*(4 : ℝ)^j=(8 : ℝ)^j:=by rw [← mul_pow]; norm_num
      have h8js:(8 : ℝ)^j≤ (8 : ℝ)^s:=pow_le_pow_right₀ (by norm_num) hjs
      calc
        4*((2 : ℝ)^j/ ∏ p∈T,(p:ℝ))*Ik A N v7 v6 k₀
            ≤ 4*((2 : ℝ)^j/ ∏ p∈T,(p:ℝ))*((z8/ c0)*(4 : ℝ)^j):=by
              gcongr
        _=4*(z8/ c0)*((2 : ℝ)^j*(4 : ℝ)^j)/ ∏ p∈T,(p:ℝ):=by ring
        _=4*(z8/ c0)*(8 : ℝ)^j/ ∏ p∈T,(p:ℝ):=by rw [h8j]
        _≤ 4*(z8/ c0)*(8 : ℝ)^s/ ∏ p∈T,(p:ℝ):=by
              have:=y4; have:=zX; gcongr
    have hC4B_ge:4*(z8/ c0)*(8 : ℝ)^s/ ∏ p∈T,(p:ℝ)+(8 : ℝ)^s/ ∏ p∈T,(p:ℝ) ≤
        xj*(8 : ℝ)^s/ ∏ p∈T,(p:ℝ):=by
      unfold xj
      have hnn:0≤ (8 : ℝ)^s/ ∏ p∈T,(p:ℝ):=by positivity
      linarith [show (4*(z8/ c0)+5)*(8 : ℝ)^s/ ∏ p∈T,(p:ℝ) =
        4*(z8/ c0)*(8 : ℝ)^s/ ∏ p∈T,(p:ℝ)+5*((8 : ℝ)^s/ ∏ p∈T,(p:ℝ)) by ring]
    linarith
  ·
    push Not at hkK
    have hIk_le1:∀ k∈Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty),
        Ik A N v7 v6 k≤ 1:=by
      intro k hk
      have hne:(zu N v7 v6 k).Nonempty:=(mem_filter.mp hk).2
      have hcard1:1≤ (zu N v7 v6 k).card:=Finset.card_pos.mpr hne
      have hlogR_lb:L^((19 : ℝ)/ 20)/ (100*(A+1))≤ Real.log (z9 A N k):=by
        have hN1_nat:1≤ N:=by exact_mod_cast hN1
        rw [xV A hN1_nat k]
        have hK_le:(z0 N:ℝ)≤ L^((1 : ℝ)/ 1000):=Nat.floor_le (by positivity)
        have hk_le:((k.1+1 : ℕ):ℝ)≤ L^((1 : ℝ)/ 1000):=(Nat.cast_le.mpr k.2).trans hK_le
        have hk50:((k.1+1 : ℕ):ℝ)^50≤ L^((1 : ℝ)/ 20):=by
          calc ((k.1+1 : ℕ):ℝ)^50≤ (L^((1 : ℝ)/ 1000))^50:=by gcongr
            _=L^((1 : ℝ)/ 20):=by
                rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith)]; congr 1; norm_num
        have hL_split:L/ (100*(A+1)*L^((1 : ℝ)/ 20))=L^((19 : ℝ)/ 20)/ (100*(A+1)):=by
          have h1:L=L^((19 : ℝ)/ 20)*L^((1 : ℝ)/ 20):=by
            rw [← Real.rpow_add (by linarith)]; norm_num
          have hneL:L^((1 : ℝ)/ 20)≠0:=(Real.rpow_pos_of_pos (by linarith) _).ne'
          calc
            L/ (100*(A+1)*L^((1 : ℝ)/ 20))
                = (L^((19 : ℝ)/ 20)*L^((1 : ℝ)/ 20))/ (100*(A+1)*L^((1 : ℝ)/ 20)):=by
                  rw [← h1]
            _=L^((19 : ℝ)/ 20)/ (100*(A+1)):=by field_simp
        rw [← hL_split]
        exact div_le_div_of_nonneg_left (by linarith) (by positivity) (by gcongr)
      have hfac_pt:∀ x∈zz (z3 N),‖zb A N v7 v6 k x‖≤ c0/ z8:=by
        intro x hx
        have hwk_le:∀ t∈Set.Icc (-(z3 N)) (z3 N),
            ‖wk A N k t‖≤ 200*(A+1)*L^(-(3/ 4 : ℝ)):=fun t ht=>by
          have htabs:|t|≤ L^((1 : ℝ)/ 5):=abs_le.mpr ht
          have h1L:(1 : ℝ)≤ L^((1 : ℝ)/ 5):=Real.one_le_rpow (by linarith) (by norm_num)
          have hnum:‖(1 : ℂ)+Complex.I*(t:ℂ)‖≤ 2*L^((1 : ℝ)/ 5):=by
            calc ‖(1 : ℂ)+Complex.I*(t:ℂ)‖≤ ‖(1 : ℂ)‖+‖Complex.I*(t:ℂ)‖:=norm_add_le _ _
              _=1+|t|:=by simp [Complex.norm_real]
              _≤ 2*L^((1 : ℝ)/ 5):=by linarith
          have hlogR_pos:0< Real.log (z9 A N k):=Real.log_pos (hR.2.2.2.2.2.2.1 k).2
          unfold wk
          rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hlogR_pos.le]
          have hquot:(2*L^((1 : ℝ)/ 5))/ (L^((19 : ℝ)/ 20)/ (100*(A+1))) =
              200*(A+1)*L^(-(3/ 4 : ℝ)):=by
            have hsub:L^((1 : ℝ)/ 5)/ L^((19 : ℝ)/ 20)=L^(-(3/ 4 : ℝ)):=by
              rw [← Real.rpow_sub (by linarith)]; congr 1; norm_num
            rw [div_div_eq_mul_div,
              show 2*L^((1 : ℝ)/ 5)*(100*(A+1))/ L^((19 : ℝ)/ 20) =
                200*(A+1)*(L^((1 : ℝ)/ 5)/ L^((19 : ℝ)/ 20)) by ring,hsub]
          rw [← hquot]
          exact div_le_div₀ (by positivity) hnum (by positivity) hlogR_lb
        have hlogR_pos:0< Real.log (z9 A N k):=Real.log_pos (hR.2.2.2.2.2.2.1 k).2
        have hterm_p:∀ p∈zu N v7 v6 k,
            ‖(1 - (p:ℂ)^(-wk A N k x.1))*(1 - (p:ℂ)^(-wk A N k x.2))‖≤ c0/ z8:=by
          intro p hp
          rcases mem_filter.mp hp with ⟨hp_pf,hpdvd⟩
          rw [hdstar_pf] at hp_pf
          have hp_pr:=(hT_info p hp_pf).1
          have hp_Tk:=(hT_info p hp_pf).2.2
          have hp_lt_kstar:p< v7:=by
            have hpos_diff:(0 : ℤ)< (v7:ℤ) - ((k.1+1 : ℕ):ℤ):=by have:=k.2; omega
            have hle_diff:=Int.le_of_dvd hpos_diff hpdvd
            have:=k.2; omega
          have hp_pos:(0 : ℝ)< p:=by exact_mod_cast hp_pr.pos
          have hlogp_nn:0≤ Real.log (p:ℝ):=Real.log_nonneg (by exact_mod_cast hp_pr.one_le)
          have hlogp_k:Real.log (p:ℝ)≤ Real.log (v7:ℝ) :=
            Real.log_le_log hp_pos (by exact_mod_cast hp_lt_kstar.le)
          have hlogp_T:Real.log (p:ℝ)≤ L/ (10*A*Real.log (v7:ℝ)):=by
            have hlogTk:Real.log (Tk A N v7)=L/ (10*A*Real.log (v7:ℝ)):=by
              unfold Tk; rw [Real.log_rpow hNpos,one_div_mul_eq_div]
            rw [← hlogTk]
            exact Real.log_le_log hp_pos hp_Tk
          have hlogk_pos:0< Real.log (v7:ℝ):=Real.log_pos (by exact_mod_cast (show 1< v7 by omega))
          have hlogp_sq:(Real.log (p:ℝ))^2≤ L/ 10:=by
            have hmul:(Real.log (p:ℝ))^2≤ Real.log (v7:ℝ)*(L/ (10*A*Real.log (v7:ℝ))):=by
              rw [sq]; exact mul_le_mul hlogp_k hlogp_T hlogp_nn hlogk_pos.le
            have hsimp:Real.log (v7:ℝ)*(L/ (10*A*Real.log (v7:ℝ)))=L/ (10*A):=by
              field_simp [hlogk_pos.ne']
            rw [hsimp] at hmul
            exact hmul.trans (div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith))
          have hw1_re:0≤ (wk A N k x.1).re:=by rw [w9]; positivity
          have hw2_re:0≤ (wk A N k x.2).re:=by rw [w9]; positivity
          have h1:=zI hp_pr.one_le hw1_re
          have h2:=zI hp_pr.one_le hw2_re
          have hL_comb:(L^(-(3/ 4 : ℝ)))^2*L=L^(-(1/ 2 : ℝ)):=by
            rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith)]
            conv_lhs=>rhs; rw [← Real.rpow_one L]
            rw [← Real.rpow_add (by linarith)]; congr 1; norm_num
          rw [norm_mul]
          calc
            ‖1 - (p:ℂ)^(-wk A N k x.1)‖*‖1 - (p:ℂ)^(-wk A N k x.2)‖
                ≤ (‖wk A N k x.1‖*Real.log (p:ℝ))*(‖wk A N k x.2‖*Real.log (p:ℝ)) :=
                  mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
            _=‖wk A N k x.1‖*‖wk A N k x.2‖*(Real.log (p:ℝ))^2:=by ring
            _≤ (200*(A+1)*L^(-(3/ 4 : ℝ)))*(200*(A+1)*L^(-(3/ 4 : ℝ)))*(L/ 10):=by
                  gcongr
                  · exact hwk_le x.1 hx.1
                  · exact hwk_le x.2 hx.2
            _=4000*(A+1)^2*((L^(-(3/ 4 : ℝ)))^2*L):=by ring
            _=4000*(A+1)^2*L^(-(1/ 2 : ℝ)):=by rw [hL_comb]
            _≤ c0/ z8:=h4B
        unfold zb
        rw [norm_prod]
        have hratio_le1:c0/ z8≤ 1:=(div_le_one y4).mpr x9
        calc
          ∏ p∈zu N v7 v6 k,
              ‖(1 - (p:ℂ)^(-wk A N k x.1))*(1 - (p:ℂ)^(-wk A N k x.2))‖
              ≤ ∏ _p∈zu N v7 v6 k,(c0/ z8) :=
                prod_le_prod (fun _ _=>norm_nonneg _) hterm_p
          _=(c0/ z8)^(zu N v7 v6 k).card:=prod_const _
          _≤ (c0/ z8)^1:=pow_le_pow_of_le_one (div_nonneg zX.le y4.le) hratio_le1 hcard1
          _=c0/ z8:=pow_one _
      have hfac_c:Continuous (zb A N v7 v6 k):=zL A N v7 v6 k
      have hint_lhs:IntegrableOn (fun x=>‖kernel x‖*‖zb A N v7 v6 k x‖)
          (zz (z3 N)) zn:=by
        refine (zc.norm.mul_const (c0/ z8)).integrableOn.mono'
          (ym.norm.mul hfac_c.norm).aestronglyMeasurable ?_
        rw [ae_restrict_iff' (z6 _)]
        refine ae_of_all _ fun x hx=>?_
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
        exact mul_le_mul_of_nonneg_left (hfac_pt x hx) (norm_nonneg _)
      unfold Ik
      calc
        (1/ c0)*∫ x in zz (z3 N),‖kernel x‖*‖zb A N v7 v6 k x‖ ∂zn
            ≤ (1/ c0)*∫ x in zz (z3 N),‖kernel x‖*(c0/ z8) ∂zn :=
              mul_le_mul_of_nonneg_left
                (setIntegral_mono_on hint_lhs (zc.norm.mul_const (c0/ z8)).integrableOn
                  (z6 _) fun x hx=>mul_le_mul_of_nonneg_left (hfac_pt x hx) (norm_nonneg _))
                (by positivity [zX])
        _≤ (1/ c0)*∫ x:ℝ × ℝ,‖kernel x‖*(c0/ z8) ∂zn :=
              mul_le_mul_of_nonneg_left
                (setIntegral_le_integral (zc.norm.mul_const (c0/ z8))
                  (ae_of_all _ fun _=>by positivity [zX,y4]))
                (by positivity [zX])
        _=1:=by
              rw [integral_mul_const]
              change (1/ c0)*(z8*(c0/ z8))=1
              field_simp [zX.ne',y4.ne']
    have hprod_Ik:∏ k∈Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty),
        Ik A N v7 v6 k≤ 1 :=
      Finset.prod_le_one (fun k _=>by
        unfold Ik; exact mul_nonneg (by positivity [zX])
          (setIntegral_nonneg (z6 _) fun _ _=>by positivity)) hIk_le1
    have hprod_pos:0< ∏ p∈T,(p:ℝ):=by rw [← hdstar_cast]; exact hdstar_pos
    have h28:(2 : ℝ)^j≤ (8 : ℝ)^s:=by
      calc (2 : ℝ)^j≤ (8 : ℝ)^j:=pow_le_pow_left₀ (by norm_num) (by norm_num) j
        _≤ (8 : ℝ)^s:=pow_le_pow_right₀ (by norm_num) hjs
    have hmain_le:4*((2 : ℝ)^j/ ∏ p∈T,(p:ℝ)) *
          (∏ k∈Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty),
            Ik A N v7 v6 k)≤ 4*(8 : ℝ)^s/ ∏ p∈T,(p:ℝ):=by
      calc
        4*((2 : ℝ)^j/ ∏ p∈T,(p:ℝ))*_
            ≤ 4*((2 : ℝ)^j/ ∏ p∈T,(p:ℝ))*1:=by gcongr
        _=4*(2 : ℝ)^j/ ∏ p∈T,(p:ℝ):=by ring
        _≤ 4*(8 : ℝ)^s/ ∏ p∈T,(p:ℝ):=by gcongr
    have hC4B_ge:4*(8 : ℝ)^s/ ∏ p∈T,(p:ℝ)+(8 : ℝ)^s/ ∏ p∈T,(p:ℝ) ≤
        xj*(8 : ℝ)^s/ ∏ p∈T,(p:ℝ):=by
      unfold xj
      have h1:0≤ 4*(z8/ c0)*((8 : ℝ)^s/ ∏ p∈T,(p:ℝ)):=by
        have:=y4; have:=zX; positivity
      linarith [show (4*(z8/ c0)+5)*(8 : ℝ)^s/ ∏ p∈T,(p:ℝ) =
        4*(z8/ c0)*((8 : ℝ)^s/ ∏ p∈T,(p:ℝ)) +
        4*(8 : ℝ)^s/ ∏ p∈T,(p:ℝ)+(8 : ℝ)^s/ ∏ p∈T,(p:ℝ) by ring]
    linarith
lemma wy {R:ℝ} (hR:Real.exp 1≤ R) (t:ℝ) :
    ∑ p∈z5 ⌊R⌋₊,(1/ (p:ℝ))*min 2 ((1+|t|)*Real.log (p:ℝ)/ Real.log R) ≤
      40*(1+Real.log (1+|t|)):=by
  have hR_pos:0< R:=(Real.exp_pos 1).trans_le hR
  have hR_ge2:2≤ R:=by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlogR_ge1:1≤ Real.log R:=by
    calc (1 : ℝ)=Real.log (Real.exp 1):=(Real.log_exp 1).symm
      _≤ Real.log R:=Real.log_le_log (Real.exp_pos 1) hR
  have hlogR_pos:0< Real.log R:=by linarith
  have h1t_ge1:1≤ 1+|t|:=by linarith [abs_nonneg t]
  have hlog1t_nn:0≤ Real.log (1+|t|):=Real.log_nonneg h1t_ge1
  set u:=Real.exp (2*Real.log R/ (1+|t|))
  have hlogu:Real.log u=2*Real.log R/ (1+|t|):=Real.log_exp _
  by_cases h1:R≤ u
  ·
    have h1t_le2:1+|t|≤ 2:=by
      have hlog_le:Real.log R≤ Real.log u:=Real.log_le_log hR_pos h1
      rw [hlogu,le_div_iff₀ (by linarith)] at hlog_le
      nlinarith
    have hR1:1≤ ⌊R⌋₊:=Nat.le_floor (by push_cast; linarith)
    calc
      ∑ p∈z5 ⌊R⌋₊,(1/ (p:ℝ))*min 2 ((1+|t|)*Real.log (p:ℝ)/ Real.log R)
          ≤ ∑ p∈z5 ⌊R⌋₊,((1+|t|)/ Real.log R)*(Real.log (p:ℝ)/ (p:ℝ)):=by
            refine sum_le_sum fun p _=>?_
            have hle:=min_le_right 2 ((1+|t|)*Real.log (p:ℝ)/ Real.log R)
            have hmul:=mul_le_mul_of_nonneg_left hle (by positivity:(0 : ℝ)≤ 1/ (p:ℝ))
            linarith [show (1/ (p:ℝ))*((1+|t|)*Real.log (p:ℝ)/ Real.log R) =
              ((1+|t|)/ Real.log R)*(Real.log (p:ℝ)/ (p:ℝ)) by ring]
      _=((1+|t|)/ Real.log R)*∑ p∈z5 ⌊R⌋₊,Real.log (p:ℝ)/ (p:ℝ):=by
            rw [← mul_sum]
      _≤ ((1+|t|)/ Real.log R)*(2*(1+Real.log (⌊R⌋₊ : ℝ))):=by
            gcongr
            have hm:=y9 ⌊R⌋₊ hR1
            have hnn:0≤ 1+Real.log (⌊R⌋₊ : ℝ):=by
              have : 0≤ Real.log (⌊R⌋₊ : ℝ):=Real.log_nonneg (by exact_mod_cast hR1)
              linarith
            exact hm.trans (mul_le_mul_of_nonneg_right yx hnn)
      _≤ (2/ Real.log R)*(2*(1+Real.log R)):=by
            have hfl:Real.log (⌊R⌋₊ : ℝ)≤ Real.log R :=
              Real.log_le_log (by exact_mod_cast (show 0< ⌊R⌋₊ by omega)) (Nat.floor_le hR_pos.le)
            gcongr
      _=4/ Real.log R+4:=by field_simp [hlogR_pos.ne']; ring
      _≤ 4/ 1+4:=by gcongr
      _≤ 40*(1+Real.log (1+|t|)):=by linarith
  · push Not at h1
    by_cases h2:u< 2
    ·
      have hlogR_lt:Real.log R≤ 1+|t|:=by
        have hlu:Real.log u≤ Real.log 2:=Real.log_le_log (Real.exp_pos _) h2.le
        have hlog2_le:Real.log 2≤ 1:=by
          linarith [Real.log_le_sub_one_of_pos (by norm_num:(0 : ℝ)< 2)]
        rw [hlogu,div_le_iff₀ (by linarith)] at hlu
        nlinarith
      calc
        ∑ p∈z5 ⌊R⌋₊,(1/ (p:ℝ))*min 2 ((1+|t|)*Real.log (p:ℝ)/ Real.log R)
            ≤ ∑ p∈z5 ⌊R⌋₊,(2 : ℝ)*(1/ (p:ℝ)):=by
              refine sum_le_sum fun p _=>?_
              have hle:=min_le_left 2 ((1+|t|)*Real.log (p:ℝ)/ Real.log R)
              have:=mul_le_mul_of_nonneg_left hle (by positivity:(0 : ℝ)≤ 1/ (p:ℝ))
              linarith
        _=2*∑ p∈z5 ⌊R⌋₊,(1 : ℝ)/ (p:ℝ):=by rw [← mul_sum]
        _≤ 2*(2*Real.log (Real.log R)+15):=by
              gcongr; exact yJ hR
        _≤ 2*(2*Real.log (1+|t|)+15):=by
              gcongr
        _≤ 40*(1+Real.log (1+|t|)):=by linarith
    ·
      push Not at h2
      have hu_fl:⌊u⌋₊≤ ⌊R⌋₊:=Nat.floor_mono h1.le
      have hsplit:z5 ⌊R⌋₊=z5 ⌊u⌋₊ ∪ z2 ⌊u⌋₊ ⌊R⌋₊:=by
        ext p
        simp only [z5,z2,mem_union,mem_filter,mem_Icc,mem_Ioc]
        constructor
        · rintro ⟨⟨h1p,h2p⟩,hp⟩
          by_cases hle:p≤ ⌊u⌋₊
          · exact Or.inl ⟨⟨h1p,hle⟩,hp⟩
          · exact Or.inr ⟨⟨by omega,h2p⟩,hp⟩
        · rintro (⟨⟨h1p,h2p⟩,hp⟩ | ⟨⟨_,h2p⟩,hp⟩)
          · exact ⟨⟨h1p,h2p.trans hu_fl⟩,hp⟩
          · exact ⟨⟨hp.one_le,h2p⟩,hp⟩
      have hdisj:Disjoint (z5 ⌊u⌋₊) (z2 ⌊u⌋₊ ⌊R⌋₊):=by
        rw [Finset.disjoint_left]; intro p hp1 hp2
        simp only [z5,z2,mem_filter,mem_Icc,mem_Ioc] at hp1 hp2
        omega
      rw [hsplit,Finset.sum_union hdisj]
      have hu1:1≤ ⌊u⌋₊:=Nat.le_floor (by push_cast; linarith)
      have hlow:∑ p∈z5 ⌊u⌋₊,(1/ (p:ℝ))*min 2 ((1+|t|)*Real.log (p:ℝ)/ Real.log R)≤ 12:=by
        have hlogu_ge:1/ 2≤ Real.log u :=
          zC.trans (Real.log_le_log (by norm_num) h2)
        calc
          ∑ p∈z5 ⌊u⌋₊,(1/ (p:ℝ))*min 2 ((1+|t|)*Real.log (p:ℝ)/ Real.log R)
              ≤ ∑ p∈z5 ⌊u⌋₊,((1+|t|)/ Real.log R)*(Real.log (p:ℝ)/ (p:ℝ)):=by
                refine sum_le_sum fun p _=>?_
                have hle:=min_le_right 2 ((1+|t|)*Real.log (p:ℝ)/ Real.log R)
                have:=mul_le_mul_of_nonneg_left hle (by positivity:(0 : ℝ)≤ 1/ (p:ℝ))
                linarith [show (1/ (p:ℝ))*((1+|t|)*Real.log (p:ℝ)/ Real.log R) =
                  ((1+|t|)/ Real.log R)*(Real.log (p:ℝ)/ (p:ℝ)) by ring]
          _=((1+|t|)/ Real.log R)*∑ p∈z5 ⌊u⌋₊,Real.log (p:ℝ)/ (p:ℝ):=by
                rw [← mul_sum]
          _≤ ((1+|t|)/ Real.log R)*(2*(1+Real.log (⌊u⌋₊ : ℝ))):=by
                gcongr
                have hm:=y9 ⌊u⌋₊ hu1
                have hnn:0≤ 1+Real.log (⌊u⌋₊ : ℝ):=by
                  have : 0≤ Real.log (⌊u⌋₊ : ℝ):=Real.log_nonneg (by exact_mod_cast hu1)
                  linarith
                exact hm.trans (mul_le_mul_of_nonneg_right yx hnn)
          _≤ ((1+|t|)/ Real.log R)*(2*(3*Real.log u)):=by
                have hfl:Real.log (⌊u⌋₊ : ℝ)≤ Real.log u :=
                  Real.log_le_log (by exact_mod_cast (show 0< ⌊u⌋₊ by omega)) (Nat.floor_le (by linarith))
                gcongr; linarith
          _=12:=by rw [hlogu]; field_simp [hlogR_pos.ne',(show 1+|t|≠0 by linarith)]; ring
      have hhigh:∑ p∈z2 ⌊u⌋₊ ⌊R⌋₊,(1/ (p:ℝ))*min 2 ((1+|t|)*Real.log (p:ℝ)/ Real.log R) ≤
          4*Real.log (1+|t|)+24:=by
        have hratio:Real.log R/ Real.log u≤ 1+|t|:=by
          rw [hlogu]
          have heq:Real.log R/ (2*Real.log R/ (1+|t|))=(1+|t|)/ 2:=by
            field_simp [hlogR_pos.ne',(show 1+|t|≠0 by linarith)]
          rw [heq]; linarith
        have hlogu_pos:0< Real.log u:=Real.log_pos (by linarith)
        calc
          ∑ p∈z2 ⌊u⌋₊ ⌊R⌋₊,(1/ (p:ℝ))*min 2 ((1+|t|)*Real.log (p:ℝ)/ Real.log R)
              ≤ ∑ p∈z2 ⌊u⌋₊ ⌊R⌋₊,(2 : ℝ)*(1/ (p:ℝ)):=by
                refine sum_le_sum fun p _=>?_
                have hle:=min_le_left 2 ((1+|t|)*Real.log (p:ℝ)/ Real.log R)
                have:=mul_le_mul_of_nonneg_left hle (by positivity:(0 : ℝ)≤ 1/ (p:ℝ))
                linarith
          _=2*∑ p∈z2 ⌊u⌋₊ ⌊R⌋₊,(1 : ℝ)/ (p:ℝ):=by rw [← mul_sum]
          _≤ 2*(2*Real.log (Real.log R/ Real.log u)+12):=by
                gcongr; exact yk h2 h1.le
          _≤ 2*(2*Real.log (1+|t|)+12):=by
                gcongr
          _=4*Real.log (1+|t|)+24:=by ring
      linarith
private lemma xu {v:ℝ} (hv:1≤ v) :
    Real.log (1+Real.log (1+v^2))≤ 4*Real.sqrt v:=by
  have hsqv_ge1:1≤ Real.sqrt v:=by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hv
  have hsqv_pos:0< Real.sqrt v:=by linarith
  have h1v2:1+v^2≤ (2*v)^2:=by nlinarith
  have hlog2_le:Real.log 2≤ 1:=by linarith [Real.log_le_sub_one_of_pos (by norm_num:(0 : ℝ)< 2)]
  have hlogv:Real.log (2*v)≤ 2*Real.sqrt v:=by
    have hv_eq:v=(Real.sqrt v)^2:=(Real.sq_sqrt (by linarith)).symm
    rw [Real.log_mul (by norm_num) (by linarith)]
    conv_lhs=>rhs; rw [hv_eq]
    rw [Real.log_pow]
    have hlogsq:Real.log (Real.sqrt v)≤ Real.sqrt v - 1:=Real.log_le_sub_one_of_pos hsqv_pos
    push_cast; linarith
  have hinner:1+Real.log (1+v^2)≤ 5*Real.sqrt v:=by
    have h1:Real.log (1+v^2)≤ 2*Real.log (2*v):=by
      calc Real.log (1+v^2)≤ Real.log ((2*v)^2):=Real.log_le_log (by positivity) h1v2
        _=2*Real.log (2*v):=by rw [Real.log_pow]; norm_num
    linarith
  have hlog5:Real.log 5≤ 3:=by
    have h5e3:(5 : ℝ)≤ Real.exp 3:=by
      have h3:Real.exp 3=(Real.exp 1)^3:=by rw [← Real.exp_nat_mul]; norm_num
      rw [h3]
      calc (5 : ℝ)≤ 2^3:=by norm_num
        _≤ (Real.exp 1)^3:=by gcongr; linarith [Real.add_one_le_exp (1 : ℝ)]
    calc Real.log 5≤ Real.log (Real.exp 3):=Real.log_le_log (by norm_num) h5e3
      _=3:=Real.log_exp 3
  have hinner_pos:0< 1+Real.log (1+v^2):=by
    have : 0≤ Real.log (1+v^2):=Real.log_nonneg (by nlinarith)
    linarith
  calc
    Real.log (1+Real.log (1+v^2))
        ≤ Real.log (5*Real.sqrt v):=Real.log_le_log hinner_pos hinner
    _=Real.log 5+Real.log (Real.sqrt v):=Real.log_mul (by norm_num) hsqv_pos.ne'
    _≤ 3+(Real.sqrt v - 1):=add_le_add hlog5 (Real.log_le_sub_one_of_pos hsqv_pos)
    _≤ 4*Real.sqrt v:=by linarith
def zg:ℝ:=9600
def xr:ℝ :=
  4*(∫ t':ℝ,(1+|t'|) ∂rho)*za *
    (∫ t:ℝ,(1+|t|)^1*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|))+1
lemma wv:0< xr:=by
  unfold xr
  have h1:0≤ ∫ t':ℝ,(1+|t'|) ∂rho:=integral_nonneg fun _=>by positivity
  have h2:0≤ ∫ t:ℝ,(1+|t|)^1*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|) :=
    integral_nonneg fun _=>by positivity
  have:=zT
  positivity
private lemma xg {s j:ℕ} (hs3:3≤ s) (hjs:j≤ s) (t:ℝ) :
    (1+|t|)*(1+Real.log (1+|t|))^j*zh t ≤
      za*(2*(60*Real.log (s:ℝ))^j) *
        ((1+|t|)^1*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|)):=by
  have hlogs_ge1:1≤ Real.log (s:ℝ):=by
    have hs_e:Real.exp 1≤ (s:ℝ):=by
      have he3:Real.exp 1≤ 3:=Real.exp_one_lt_d9.le.trans (by norm_num)
      have : (3 : ℝ)≤ (s:ℝ):=by exact_mod_cast hs3
      linarith
    calc (1 : ℝ)=Real.log (Real.exp 1):=(Real.log_exp 1).symm
      _≤ Real.log (s:ℝ):=Real.log_le_log (Real.exp_pos 1) hs_e
  have hnn_log:0≤ 1+Real.log (1+|t|):=by
    have : 0≤ Real.log (1+|t|):=Real.log_nonneg (by linarith [abs_nonneg t])
    linarith
  have hbase_ge1:1≤ 60*Real.log (s:ℝ):=by linarith
  have hpow_ge1:(1 : ℝ)≤ (60*Real.log (s:ℝ))^j:=one_le_pow₀ hbase_ge1
  have hkey:(1+Real.log (1+|t|))^j*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|) ≤
      (2*(60*Real.log (s:ℝ))^j)*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|):=by
    by_cases hbig:((40*((j+2 : ℕ):ℝ))^4)≤ |t|
    · set v:=Real.sqrt |t|
      have hv_ge:(40*((j+2 : ℕ):ℝ))^2≤ v:=by
        have h1:(40*((j+2 : ℕ):ℝ))^4=((40*((j+2 : ℕ):ℝ))^2)^2:=by ring
        rw [h1] at hbig
        calc (40*((j+2 : ℕ):ℝ))^2
            = Real.sqrt (((40*((j+2 : ℕ):ℝ))^2)^2):=(Real.sqrt_sq (by positivity)).symm
          _≤ Real.sqrt |t|:=Real.sqrt_le_sqrt hbig
      have hv_ge1:1≤ v:=by
        have : (1 : ℝ)≤ 40*((j+2 : ℕ):ℝ):=by
          have : (1 : ℝ)≤ ((j+2 : ℕ):ℝ):=by exact_mod_cast (show 1≤ j+2 by omega)
          linarith
        nlinarith
      have hsqv_ge:40*((j+2 : ℕ):ℝ)≤ Real.sqrt v:=by
        calc 40*((j+2 : ℕ):ℝ)
            = Real.sqrt ((40*((j+2 : ℕ):ℝ))^2):=(Real.sqrt_sq (by positivity)).symm
          _≤ Real.sqrt v:=Real.sqrt_le_sqrt hv_ge
      have ht_eq:|t|=v^2:=(Real.sq_sqrt (abs_nonneg t)).symm
      have hlog_bd:Real.log (1+Real.log (1+|t|))≤ 4*Real.sqrt v:=by
        rw [ht_eq]; exact xu hv_ge1
      have hj_log:(j:ℝ)*Real.log (1+Real.log (1+|t|))≤ (1/ 10 : ℝ)*v:=by
        have hj_le:(j:ℝ)≤ ((j+2 : ℕ):ℝ):=by exact_mod_cast (show j≤ j+2 by omega)
        have hv_sq:v=(Real.sqrt v)^2:=(Real.sq_sqrt (by linarith)).symm
        calc
          (j:ℝ)*Real.log (1+Real.log (1+|t|))
              ≤ (j:ℝ)*(4*Real.sqrt v):=mul_le_mul_of_nonneg_left hlog_bd (Nat.cast_nonneg j)
          _≤ ((1/ 10 : ℝ)*Real.sqrt v)*Real.sqrt v:=by
                have h1:4*(j:ℝ)≤ (1/ 10 : ℝ)*Real.sqrt v:=by linarith
                nlinarith [Real.sqrt_nonneg v]
          _=(1/ 10 : ℝ)*v:=by rw [mul_assoc,← sq,← hv_sq]
      have hpos_in:0< 1+Real.log (1+|t|):=by
        have : 0≤ Real.log (1+|t|):=Real.log_nonneg (by linarith [abs_nonneg t]); linarith
      calc
        (1+Real.log (1+|t|))^j*Real.exp (-(1/ 5 : ℝ)*v)
            = Real.exp ((j:ℝ)*Real.log (1+Real.log (1+|t|)) - (1/ 5 : ℝ)*v):=by
              rw [← Real.rpow_natCast,Real.rpow_def_of_pos hpos_in,← Real.exp_add]
              congr 1; ring
        _≤ Real.exp (-(1/ 10 : ℝ)*v):=Real.exp_le_exp.mpr (by linarith)
        _=1*Real.exp (-(1/ 10 : ℝ)*v):=(one_mul _).symm
        _≤ (2*(60*Real.log (s:ℝ))^j)*Real.exp (-(1/ 10 : ℝ)*v):=by
              gcongr; linarith
    · push Not at hbig
      have h40j_ge1:(1 : ℝ)≤ (40*((j+2 : ℕ):ℝ))^4:=by
        apply one_le_pow₀
        have : (1 : ℝ)≤ ((j+2 : ℕ):ℝ):=by exact_mod_cast (show 1≤ j+2 by omega)
        linarith
      have h1t_le:1+|t|≤ 2*(40*((j+2 : ℕ):ℝ))^4:=by linarith
      have hlog40:Real.log 40≤ 6:=by
        have h40e6:(40 : ℝ)≤ Real.exp 6:=by
          have h6:Real.exp 6=(Real.exp 1)^6:=by rw [← Real.exp_nat_mul]; norm_num
          rw [h6]
          calc (40 : ℝ)≤ 2^6:=by norm_num
            _≤ (Real.exp 1)^6:=by gcongr; linarith [Real.add_one_le_exp (1 : ℝ)]
        calc Real.log 40≤ Real.log (Real.exp 6):=Real.log_le_log (by norm_num) h40e6
          _=6:=Real.log_exp 6
      have hlog2:Real.log 2≤ 1:=by linarith [Real.log_le_sub_one_of_pos (by norm_num:(0 : ℝ)< 2)]
      have hj2_le_s2:((j+2 : ℕ):ℝ)≤ (s:ℝ)^2:=by
        have hnat:j+2≤ s^2:=by nlinarith
        exact_mod_cast hnat
      have hlogj2_le:Real.log ((j+2 : ℕ):ℝ)≤ 2*Real.log (s:ℝ):=by
        calc Real.log ((j+2 : ℕ):ℝ)≤ Real.log ((s:ℝ)^2) :=
              Real.log_le_log (by positivity) hj2_le_s2
          _=2*Real.log (s:ℝ):=by rw [Real.log_pow]; norm_num
      have h1log_le:1+Real.log (1+|t|)≤ 60*Real.log (s:ℝ):=by
        have h1:Real.log (1+|t|)≤ Real.log (2*(40*((j+2 : ℕ):ℝ))^4) :=
          Real.log_le_log (by linarith [abs_nonneg t]) h1t_le
        rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow,
          Real.log_mul (by norm_num) (by positivity)] at h1
        push_cast at h1 hlogj2_le
        linarith
      have hexp_le:Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|)≤ Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|) :=
        Real.exp_le_exp.mpr (by linarith [Real.sqrt_nonneg |t|])
      have hpow:(1+Real.log (1+|t|))^j≤ (60*Real.log (s:ℝ))^j :=
        pow_le_pow_left₀ hnn_log h1log_le j
      calc
        (1+Real.log (1+|t|))^j*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|)
            ≤ (60*Real.log (s:ℝ))^j*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|) :=
              mul_le_mul hpow hexp_le (Real.exp_pos _).le (by positivity)
        _≤ (2*(60*Real.log (s:ℝ))^j)*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|):=by
              gcongr; linarith
  rw [pow_one]
  calc
    (1+|t|)*(1+Real.log (1+|t|))^j*zh t
        ≤ (1+|t|)*(1+Real.log (1+|t|))^j*(za*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|)) :=
          mul_le_mul_of_nonneg_left (zj t) (mul_nonneg (by positivity) (pow_nonneg hnn_log j))
    _=za*(1+|t|)*((1+Real.log (1+|t|))^j*Real.exp (-(1/ 5 : ℝ)*Real.sqrt |t|)):=by
          ring
    _≤ za*(1+|t|)*((2*(60*Real.log (s:ℝ))^j)*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|)) :=
          mul_le_mul_of_nonneg_left hkey (mul_nonneg zT.le (by positivity))
    _=za*(2*(60*Real.log (s:ℝ))^j)*((1+|t|)*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|)):=by
          ring
private def zy (R t:ℝ) (p:ℕ):ℝ :=
  (1/ (p:ℝ))*min 2 ((1+|t|)*Real.log (p:ℝ)/ Real.log R)
private lemma wC (R:ℝ) (p:ℕ):Continuous (fun t:ℝ=>zy R t p):=by
  unfold zy
  exact continuous_const.mul
    (continuous_const.min (((continuous_const.add continuous_abs).mul continuous_const).div_const _))
private lemma yd {R:ℝ} (hlogR_pos:0< Real.log R) (t:ℝ) (p:ℕ) :
    0≤ zy R t p:=by
  unfold zy
  refine mul_nonneg (by positivity) (le_min (by norm_num) ?_)
  have hlogp:0≤ Real.log (p:ℝ):=by
    rcases eq_or_ne p 0 with rfl | hp0
    · simp
    · exact Real.log_nonneg (by exact_mod_cast Nat.pos_of_ne_zero hp0)
  positivity
private lemma wx {A:ℝ} {N v7 j:ℕ}
    (k₀ : Fin (z0 N)) (hk0_eq:k₀.1+1=v7)
    (hR_ge_e:Real.exp 1≤ z9 A N k₀)
    {T:Finset ℕ} (hT_pr:∀ p∈T,p.Prime) (hTcard:T.card=j) :
    (j.factorial:ℝ)*(4*((2 : ℝ)^j/ (∏ p∈T,(p:ℝ)))*Ik A N v7 (∏ p∈T,p) k₀) ≤
      2*(4 : ℝ)^j*(∫ t':ℝ,(1+|t'|) ∂rho) *
        ∫ t:ℝ,(1+|t|)*((j.factorial:ℝ)*∏ p∈T,zy (z9 A N k₀) t p) ∂rho:=by
  set R:=z9 A N k₀
  have hlogR_pos:0< Real.log R:=by
    calc (0 : ℝ)< 1:=by norm_num
      _=Real.log (Real.exp 1):=(Real.log_exp 1).symm
      _≤ Real.log R:=Real.log_le_log (Real.exp_pos 1) hR_ge_e
  have h1_rho:Integrable (fun t:ℝ=>1+|t|) rho:=zQ
  obtain ⟨_,hdstar_pf⟩:=zG hT_pr
  have hPk_k0:zu N v7 (∏ p∈T,p) k₀=T:=by
    unfold zu; rw [hdstar_pf]; ext p; simp only [mem_filter,and_iff_left_iff_imp]
    intro _; rw [hk0_eq,sub_self]; exact dvd_zero _
  have hfac_pt:∀ x:ℝ × ℝ,
      (1/ (∏ p∈T,(p:ℝ)))*‖zb A N v7 (∏ p∈T,p) k₀ x‖ ≤
        (2 : ℝ)^j*∏ p∈T,zy R x.1 p:=by
    intro x
    unfold zb
    rw [hPk_k0,norm_prod,← prod_const_one,← prod_div_distrib,← prod_mul_distrib]
    have h2j:(2 : ℝ)^j*∏ p∈T,zy R x.1 p=∏ p∈T,(2*zy R x.1 p):=by
      rw [prod_mul_distrib (f:=fun _=>(2 : ℝ)),prod_const,hTcard]
    rw [h2j]
    refine prod_le_prod (fun _ _=>by positivity) fun p hp=>?_
    have hp_pr:=hT_pr p hp
    have hp1:(1 : ℝ)≤ p:=by exact_mod_cast hp_pr.one_le
    have hcp_le1:∀ t:ℝ,‖(p:ℂ)^(-wk A N k₀ t)‖≤ 1:=fun t=>by
      rw [yf hp_pr.one_le]
      exact Real.rpow_le_one_of_one_le_of_nonpos hp1 (neg_nonpos.mpr (by positivity))
    have h2_b:‖1 - (p:ℂ)^(-wk A N k₀ x.2)‖≤ 2:=by
      calc ‖1 - (p:ℂ)^(-wk A N k₀ x.2)‖≤ ‖(1 : ℂ)‖+‖(p:ℂ)^(-wk A N k₀ x.2)‖:=norm_sub_le _ _
        _≤ 1+1:=by rw [norm_one]; linarith [hcp_le1 x.2]
        _=2:=by norm_num
    have h1_b:‖1 - (p:ℂ)^(-wk A N k₀ x.1)‖≤ min 2 ((1+|x.1|)*Real.log (p:ℝ)/ Real.log R):=by
      refine le_min ?_ ?_
      · calc ‖1 - (p:ℂ)^(-wk A N k₀ x.1)‖≤ ‖(1 : ℂ)‖+‖(p:ℂ)^(-wk A N k₀ x.1)‖:=norm_sub_le _ _
          _≤ 1+1:=by rw [norm_one]; linarith [hcp_le1 x.1]
          _=2:=by norm_num
      · have hw1_re:0≤ (wk A N k₀ x.1).re:=by rw [w9]; positivity
        have hlin:=zI hp_pr.one_le hw1_re
        have hwk_n:‖wk A N k₀ x.1‖≤ (1+|x.1|)/ Real.log R:=by
          unfold wk; rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hlogR_pos.le]
          gcongr
          calc ‖(1 : ℂ)+Complex.I*(x.1 : ℂ)‖≤ ‖(1 : ℂ)‖+‖Complex.I*(x.1 : ℂ)‖:=norm_add_le _ _
            _=1+|x.1|:=by simp [Complex.norm_real]
        have hlogp_nn:0≤ Real.log (p:ℝ):=Real.log_nonneg hp1
        calc ‖1 - (p:ℂ)^(-wk A N k₀ x.1)‖≤ ‖wk A N k₀ x.1‖*Real.log (p:ℝ):=hlin
          _≤ ((1+|x.1|)/ Real.log R)*Real.log (p:ℝ):=mul_le_mul_of_nonneg_right hwk_n hlogp_nn
          _=(1+|x.1|)*Real.log (p:ℝ)/ Real.log R:=by ring
    rw [norm_mul]
    unfold zy
    have hmul:‖1 - (p:ℂ)^(-wk A N k₀ x.1)‖*‖1 - (p:ℂ)^(-wk A N k₀ x.2)‖ ≤
        2*min 2 ((1+|x.1|)*Real.log (p:ℝ)/ Real.log R):=by
      have:=mul_le_mul h1_b h2_b (norm_nonneg _) (le_min (by norm_num) (by
        have : 0≤ Real.log (p:ℝ):=Real.log_nonneg hp1; positivity))
      linarith
    calc
      1/ (p:ℝ)*(‖1 - (p:ℂ)^(-wk A N k₀ x.1)‖*‖1 - (p:ℂ)^(-wk A N k₀ x.2)‖)
          ≤ 1/ (p:ℝ)*(2*min 2 ((1+|x.1|)*Real.log (p:ℝ)/ Real.log R)) :=
            mul_le_mul_of_nonneg_left hmul (by positivity)
      _=2*(1/ (p:ℝ)*min 2 ((1+|x.1|)*Real.log (p:ℝ)/ Real.log R)):=by ring
  have hgprod_le:∀ t:ℝ,∏ p∈T,zy R t p≤ (2 : ℝ)^j:=fun t=>by
    calc ∏ p∈T,zy R t p≤ ∏ _p∈T,(2 : ℝ):=by
          refine prod_le_prod (fun p _=>yd hlogR_pos t p) fun p hp=>?_
          unfold zy
          have hp1:(1 : ℝ)≤ (p:ℝ):=by exact_mod_cast (hT_pr p hp).one_le
          have h1p:(1 : ℝ)/ (p:ℝ)≤ 1:=div_le_one_of_le₀ hp1 (by positivity)
          have hmin:min 2 ((1+|t|)*Real.log (p:ℝ)/ Real.log R)≤ 2:=min_le_left _ _
          have hmin_nn:0≤ min 2 ((1+|t|)*Real.log (p:ℝ)/ Real.log R) :=
            le_min (by norm_num) (by have : 0≤ Real.log (p:ℝ):=Real.log_nonneg hp1; positivity)
          nlinarith
      _=(2 : ℝ)^j:=by rw [prod_const,hTcard]
  have hg1_int:Integrable (fun t:ℝ=>(1+|t|)*∏ p∈T,zy R t p) rho:=by
    refine (h1_rho.mul_const ((2 : ℝ)^j)).mono'
      ((continuous_const.add continuous_abs).mul (continuous_finsetProd T fun p _=>wC R p)).aestronglyMeasurable ?_
    refine ae_of_all _ fun t=>?_
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (prod_nonneg fun p _=>yd hlogR_pos t p))]
    exact mul_le_mul_of_nonneg_left (hgprod_le t) (by positivity)
  have hfac_c:Continuous (zb A N v7 (∏ p∈T,p) k₀) :=
    zL A N v7 (∏ p∈T,p) k₀
  have hlhs_int:IntegrableOn (fun x=>(1/ (∏ p∈T,(p:ℝ))) *
        (‖kernel x‖*‖zb A N v7 (∏ p∈T,p) k₀ x‖)) (zz (z3 N)) zn:=by
    refine (zc.norm.mul_const ((4 : ℝ)^j)).integrableOn.mono'
      (continuous_const.mul (ym.norm.mul hfac_c.norm)).aestronglyMeasurable ?_
    refine ae_of_all _ fun x=>?_
    rw [Real.norm_of_nonneg (by positivity)]
    have h1:(1/ (∏ p∈T,(p:ℝ)))*‖zb A N v7 (∏ p∈T,p) k₀ x‖≤ (4 : ℝ)^j:=by
      calc _≤ (2 : ℝ)^j*∏ p∈T,zy R x.1 p:=hfac_pt x
        _≤ (2 : ℝ)^j*(2 : ℝ)^j:=by gcongr; exact hgprod_le x.1
        _=(4 : ℝ)^j:=by rw [← mul_pow]; norm_num
    have:=mul_le_mul_of_nonneg_left h1 (norm_nonneg (kernel x))
    linarith
  have hrhs_int:Integrable (fun x:ℝ × ℝ =>
      ((2 : ℝ)^j/ 2)*(((1+|x.1|)*∏ p∈T,zy R x.1 p)*(1+|x.2|))) zn :=
    (hg1_int.mul_prod h1_rho).const_mul _
  have hprod_eval:∫ x:ℝ × ℝ,((2 : ℝ)^j/ 2)*(((1+|x.1|)*∏ p∈T,zy R x.1 p)*(1+|x.2|)) ∂zn =
      ((2 : ℝ)^j/ 2)*((∫ t:ℝ,(1+|t|)*∏ p∈T,zy R t p ∂rho)*(∫ t':ℝ,(1+|t'|) ∂rho)):=by
    rw [integral_const_mul]; congr 1
    unfold zn
    exact MeasureTheory.integral_prod_mul (fun t=>(1+|t|)*∏ p∈T,zy R t p) (fun t'=>1+|t'|)
  have hc0_inv:(1 : ℝ)/ c0≤ 1:=(div_le_one zX).mpr wz
  have hIk_step:(1/ (∏ p∈T,(p:ℝ)))*Ik A N v7 (∏ p∈T,p) k₀ ≤
      ((2 : ℝ)^j/ 2)*((∫ t:ℝ,(1+|t|)*∏ p∈T,zy R t p ∂rho)*(∫ t':ℝ,(1+|t'|) ∂rho)):=by
    unfold Ik
    have h1:(1/ (∏ p∈T,(p:ℝ)))*((1/ c0) *
          ∫ x in zz (z3 N),‖kernel x‖*‖zb A N v7 (∏ p∈T,p) k₀ x‖ ∂zn) ≤
        ∫ x in zz (z3 N),(1/ (∏ p∈T,(p:ℝ))) *
          (‖kernel x‖*‖zb A N v7 (∏ p∈T,p) k₀ x‖) ∂zn:=by
      rw [integral_const_mul]
      have hnn:0≤ (1/ (∏ p∈T,(p:ℝ))) *
          ∫ x in zz (z3 N),‖kernel x‖*‖zb A N v7 (∏ p∈T,p) k₀ x‖ ∂zn :=
        mul_nonneg (by positivity) (setIntegral_nonneg (z6 _) fun _ _=>by positivity)
      have hrew:(1/ (∏ p∈T,(p:ℝ)))*((1/ c0) *
            ∫ x in zz (z3 N),‖kernel x‖*‖zb A N v7 (∏ p∈T,p) k₀ x‖ ∂zn) =
          (1/ c0)*((1/ (∏ p∈T,(p:ℝ))) *
            ∫ x in zz (z3 N),‖kernel x‖*‖zb A N v7 (∏ p∈T,p) k₀ x‖ ∂zn):=by ring
      rw [hrew]
      nlinarith
    refine h1.trans ?_
    calc
      ∫ x in zz (z3 N),(1/ (∏ p∈T,(p:ℝ))) *
          (‖kernel x‖*‖zb A N v7 (∏ p∈T,p) k₀ x‖) ∂zn
          ≤ ∫ x in zz (z3 N),
              ((2 : ℝ)^j/ 2)*(((1+|x.1|)*∏ p∈T,zy R x.1 p)*(1+|x.2|)) ∂zn:=by
            refine setIntegral_mono_on hlhs_int hrhs_int.integrableOn (z6 _) fun x _=>?_
            have hk:=x7 x
            have hf:=hfac_pt x
            have hmul:=mul_le_mul hk hf (by positivity) (by positivity)
            linarith [show (1/ (∏ p∈T,(p:ℝ)))*(‖kernel x‖*‖zb A N v7 (∏ p∈T,p) k₀ x‖) =
              ‖kernel x‖*((1/ (∏ p∈T,(p:ℝ)))*‖zb A N v7 (∏ p∈T,p) k₀ x‖) by ring,
              show ((1+|x.1|)*(1+|x.2|)/ 2)*((2 : ℝ)^j*∏ p∈T,zy R x.1 p) =
              ((2 : ℝ)^j/ 2)*(((1+|x.1|)*∏ p∈T,zy R x.1 p)*(1+|x.2|)) by ring]
      _≤ ∫ x:ℝ × ℝ,
              ((2 : ℝ)^j/ 2)*(((1+|x.1|)*∏ p∈T,zy R x.1 p)*(1+|x.2|)) ∂zn :=
            setIntegral_le_integral hrhs_int (ae_of_all _ fun x =>
              mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (by positivity)
                (prod_nonneg fun p _=>yd hlogR_pos x.1 p)) (by positivity)))
      _=((2 : ℝ)^j/ 2)*((∫ t:ℝ,(1+|t|)*∏ p∈T,zy R t p ∂rho)*(∫ t':ℝ,(1+|t'|) ∂rho)) :=
            hprod_eval
  have hpull_fac:∫ t:ℝ,(1+|t|)*((j.factorial:ℝ)*∏ p∈T,zy R t p) ∂rho =
      (j.factorial:ℝ)*∫ t:ℝ,(1+|t|)*∏ p∈T,zy R t p ∂rho:=by
    rw [← integral_const_mul]; congr 1; ext t; ring
  rw [hpull_fac]
  have h4j:(2 : ℝ)^j*(2 : ℝ)^j=(4 : ℝ)^j:=by rw [← mul_pow]; norm_num
  have hrew1:(j.factorial:ℝ)*(4*((2 : ℝ)^j/ (∏ p∈T,(p:ℝ)))*Ik A N v7 (∏ p∈T,p) k₀) =
      ((j.factorial:ℝ)*4*(2 : ℝ)^j)*((1/ (∏ p∈T,(p:ℝ)))*Ik A N v7 (∏ p∈T,p) k₀):=by
    ring
  rw [hrew1]
  calc
    ((j.factorial:ℝ)*4*(2 : ℝ)^j)*((1/ (∏ p∈T,(p:ℝ)))*Ik A N v7 (∏ p∈T,p) k₀)
        ≤ ((j.factorial:ℝ)*4*(2 : ℝ)^j) *
          (((2 : ℝ)^j/ 2)*((∫ t:ℝ,(1+|t|)*∏ p∈T,zy R t p ∂rho)*(∫ t':ℝ,(1+|t'|) ∂rho))) :=
          mul_le_mul_of_nonneg_left hIk_step (by positivity)
    _=2*((2 : ℝ)^j*(2 : ℝ)^j)*(∫ t':ℝ,(1+|t'|) ∂rho) *
          ((j.factorial:ℝ)*∫ t:ℝ,(1+|t|)*∏ p∈T,zy R t p ∂rho):=by ring
    _=2*(4 : ℝ)^j*(∫ t':ℝ,(1+|t'|) ∂rho) *
          ((j.factorial:ℝ)*∫ t:ℝ,(1+|t|)*∏ p∈T,zy R t p ∂rho):=by rw [h4j]
private lemma ww {A:ℝ} {N v7 s j:ℕ}
    (k₀ : Fin (z0 N)) (hk0_eq:k₀.1+1=v7)
    (hR_ge_e:Real.exp 1≤ z9 A N k₀) (hs3:3≤ s) (hjs:j≤ s) :
    ∑ T∈(z2 (z7 N) ⌊z9 A N k₀⌋₊).powersetCard j,
        (j.factorial:ℝ)*(4*((2 : ℝ)^j/ (∏ p∈T,(p:ℝ)))*Ik A N v7 (∏ p∈T,p) k₀) ≤
      (xr - 1)*(zg*Real.log (s:ℝ))^s:=by
  set R:=z9 A N k₀
  set Pmed:=z2 (z7 N) ⌊R⌋₊
  have hlogR_pos:0< Real.log R:=by
    calc (0 : ℝ)< 1:=by norm_num
      _=Real.log (Real.exp 1):=(Real.log_exp 1).symm
      _≤ Real.log R:=Real.log_le_log (Real.exp_pos 1) hR_ge_e
  have hlogs_ge1:1≤ Real.log (s:ℝ):=by
    have hs_e:Real.exp 1≤ (s:ℝ):=by
      have he3:Real.exp 1≤ 3:=Real.exp_one_lt_d9.le.trans (by norm_num)
      have : (3 : ℝ)≤ (s:ℝ):=by exact_mod_cast hs3
      linarith
    calc (1 : ℝ)=Real.log (Real.exp 1):=(Real.log_exp 1).symm
      _≤ Real.log (s:ℝ):=Real.log_le_log (Real.exp_pos 1) hs_e
  have h1_rho:Integrable (fun t:ℝ=>1+|t|) rho:=zQ
  have hIk_bound_T:∀ T∈Pmed.powersetCard j,
      (j.factorial:ℝ)*(4*((2 : ℝ)^j/ (∏ p∈T,(p:ℝ)))*Ik A N v7 (∏ p∈T,p) k₀) ≤
        2*(4 : ℝ)^j*(∫ t':ℝ,(1+|t'|) ∂rho) *
          ∫ t:ℝ,(1+|t|)*((j.factorial:ℝ)*∏ p∈T,zy R t p) ∂rho:=by
    intro T hT
    rcases mem_powersetCard.mp hT with ⟨hTsub,hTcard⟩
    exact wx k₀ hk0_eq hR_ge_e (fun p hp=>(mem_filter.mp (hTsub hp)).2) hTcard
  refine (sum_le_sum hIk_bound_T).trans ?_
  rw [← mul_sum]
  have hint_T:∀ T∈Pmed.powersetCard j,
      Integrable (fun t:ℝ=>(1+|t|)*((j.factorial:ℝ)*∏ p∈T,zy R t p)) rho:=by
    intro T hT
    rcases mem_powersetCard.mp hT with ⟨hTsub,hTcard⟩
    have hT_pr:∀ p∈T,p.Prime:=fun p hp=>(mem_filter.mp (hTsub hp)).2
    refine (h1_rho.mul_const ((j.factorial:ℝ)*(2 : ℝ)^j)).mono'
      ((continuous_const.add continuous_abs).mul (continuous_const.mul (continuous_finsetProd T fun p _=>wC R p))).aestronglyMeasurable ?_
    refine ae_of_all _ fun t=>?_
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) (prod_nonneg fun p _=>yd hlogR_pos t p)))]
    have hprod2:∏ p∈T,zy R t p≤ (2 : ℝ)^j:=by
      calc ∏ p∈T,zy R t p≤ ∏ _p∈T,(2 : ℝ):=by
            refine prod_le_prod (fun p _=>yd hlogR_pos t p) fun p hp=>?_
            unfold zy
            have hp1:(1 : ℝ)≤ (p:ℝ):=by exact_mod_cast (hT_pr p hp).one_le
            have h1p:(1 : ℝ)/ (p:ℝ)≤ 1:=div_le_one_of_le₀ hp1 (by positivity)
            have hmin:min 2 ((1+|t|)*Real.log (p:ℝ)/ Real.log R)≤ 2:=min_le_left _ _
            have hmin_nn:0≤ min 2 ((1+|t|)*Real.log (p:ℝ)/ Real.log R) :=
              le_min (by norm_num) (by have : 0≤ Real.log (p:ℝ):=Real.log_nonneg hp1; positivity)
            nlinarith
        _=(2 : ℝ)^j:=by rw [prod_const,hTcard]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod2 (Nat.cast_nonneg _)) (by positivity)
  rw [← MeasureTheory.integral_finsetSum _ hint_T]
  have hpt_sum:∀ t:ℝ,
      (∑ T∈Pmed.powersetCard j,(1+|t|)*((j.factorial:ℝ)*∏ p∈T,zy R t p)) ≤
        (40 : ℝ)^j*((1+|t|)*(1+Real.log (1+|t|))^j):=by
    intro t
    rw [← mul_sum]
    have hfact:=zP Pmed (h:=zy R t)
      (fun p _=>yd hlogR_pos t p) j
    have hPmed_sub:Pmed⊆z5 ⌊R⌋₊:=by
      intro p hp
      simp only [Pmed,z2,z5,mem_filter,mem_Ioc,mem_Icc] at hp ⊢
      exact ⟨⟨hp.2.one_le,hp.1.2⟩,hp.2⟩
    have hsum_le:∑ p∈Pmed,zy R t p≤ 40*(1+Real.log (1+|t|)) :=
      (sum_le_sum_of_subset_of_nonneg hPmed_sub fun p _ _=>yd hlogR_pos t p).trans
        (wy hR_ge_e t)
    have hpow_le:(∑ p∈Pmed,zy R t p)^j≤ (40 : ℝ)^j*(1+Real.log (1+|t|))^j:=by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (sum_nonneg fun p _=>yd hlogR_pos t p) hsum_le j
    have:=mul_le_mul_of_nonneg_left (hfact.trans hpow_le) (by positivity:(0 : ℝ)≤ 1+|t|)
    linarith
  set I10:=∫ t:ℝ,(1+|t|)^1*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|)
  have hdom_10:Integrable (fun t:ℝ=>(1+|t|)^1*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|)) volume :=
    zd (by norm_num:(0 : ℝ)< 1/ 10) 1
  have hpt_exp:∀ t:ℝ,
      (1+|t|)*(1+Real.log (1+|t|))^j*zh t ≤
        za*(2*(60*Real.log (s:ℝ))^j) *
          ((1+|t|)^1*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|)) :=
    xg hs3 hjs
  have hint_rho_le :
      ∫ t:ℝ,(∑ T∈Pmed.powersetCard j,(1+|t|)*((j.factorial:ℝ)*∏ p∈T,zy R t p)) ∂rho ≤
        (40 : ℝ)^j*(za*(2*(60*Real.log (s:ℝ))^j)*I10):=by
    have hint_lhs_rho:Integrable (fun t:ℝ =>
        ∑ T∈Pmed.powersetCard j,(1+|t|)*((j.factorial:ℝ)*∏ p∈T,zy R t p)) rho :=
      MeasureTheory.integrable_finsetSum _ hint_T
    have hint_lhs_vol:Integrable (fun t:ℝ =>
        zh t*∑ T∈Pmed.powersetCard j,(1+|t|)*((j.factorial:ℝ)*∏ p∈T,zy R t p)) volume :=
      y6.mp hint_lhs_rho
    rw [xw]
    simp_rw [smul_eq_mul]
    have hdom_all:Integrable (fun t:ℝ =>
        ((40 : ℝ)^j*(za*(2*(60*Real.log (s:ℝ))^j))) *
          ((1+|t|)^1*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|))) volume :=
      hdom_10.const_mul _
    calc
      ∫ t:ℝ,zh t*(∑ T∈Pmed.powersetCard j,(1+|t|)*((j.factorial:ℝ)*∏ p∈T,zy R t p))
          ≤ ∫ t:ℝ,((40 : ℝ)^j*(za*(2*(60*Real.log (s:ℝ))^j))) *
              ((1+|t|)^1*Real.exp (-(1/ 10 : ℝ)*Real.sqrt |t|)):=by
            refine integral_mono hint_lhs_vol hdom_all fun t=>?_
            have h1:=mul_le_mul_of_nonneg_left (hpt_sum t) (zw t)
            have h2:=hpt_exp t
            have hrew:zh t*((40 : ℝ)^j*((1+|t|)*(1+Real.log (1+|t|))^j)) =
                (40 : ℝ)^j*((1+|t|)*(1+Real.log (1+|t|))^j*zh t):=by ring
            rw [hrew] at h1
            refine h1.trans ?_
            have:=mul_le_mul_of_nonneg_left h2 (by positivity:(0 : ℝ)≤ (40 : ℝ)^j)
            linarith
      _=(40 : ℝ)^j*(za*(2*(60*Real.log (s:ℝ))^j)*I10):=by
            rw [integral_const_mul]; ring
  have hmul_const:(4 : ℝ)^j*(40 : ℝ)^j*(60*Real.log (s:ℝ))^j =
      (zg*Real.log (s:ℝ))^j:=by
    unfold zg
    rw [← mul_pow,← mul_pow]; congr 1; ring
  have hpow_js:(zg*Real.log (s:ℝ))^j≤ (zg*Real.log (s:ℝ))^s:=by
    apply pow_le_pow_right₀ _ hjs
    unfold zg; linarith
  have hC_rew:4*(∫ t':ℝ,(1+|t'|) ∂rho)*za*I10=xr - 1:=by
    unfold xr; ring
  have hnn_int':0≤ ∫ t':ℝ,(1+|t'|) ∂rho:=integral_nonneg fun _=>by positivity
  have hnn_I10:0≤ I10:=integral_nonneg fun _=>by positivity
  calc
    2*(4 : ℝ)^j*(∫ t':ℝ,(1+|t'|) ∂rho) *
        ∫ t:ℝ,(∑ T∈Pmed.powersetCard j,(1+|t|)*((j.factorial:ℝ)*∏ p∈T,zy R t p)) ∂rho
        ≤ 2*(4 : ℝ)^j*(∫ t':ℝ,(1+|t'|) ∂rho) *
            ((40 : ℝ)^j*(za*(2*(60*Real.log (s:ℝ))^j)*I10)) :=
          mul_le_mul_of_nonneg_left hint_rho_le (by positivity)
    _=(4*(∫ t':ℝ,(1+|t'|) ∂rho)*za*I10) *
          ((4 : ℝ)^j*(40 : ℝ)^j*(60*Real.log (s:ℝ))^j):=by ring
    _=(xr - 1)*(zg*Real.log (s:ℝ))^j:=by rw [hC_rew,hmul_const]
    _≤ (xr - 1)*(zg*Real.log (s:ℝ))^s:=by
          have hC4C_sub:0≤ xr - 1:=by rw [← hC_rew]; have:=zT; positivity
          exact mul_le_mul_of_nonneg_left hpow_js hC4C_sub
theorem v3 {A:ℝ} (hA:1≤ A) :
    ∀ᶠ N:ℕ in atTop,
      zM A N ∧
      ∀ (v7 s j:ℕ),2≤ v7→v7≤ z0 N →
        3≤ s→1≤ j→j≤ s→(s:ℝ)≤ A*Real.log (v7:ℝ) →
        ∑ T∈(z2 (z7 N) ⌊Rk A N v7⌋₊).powersetCard j,
            (j.factorial:ℝ)*(xb A N v7 (∏ p∈T,p)/ zY A N) ≤
          xr*(zg*Real.log (s:ℝ))^s:=by
  have hL_err:∀ᶠ N:ℕ in atTop,
      (A*Real.log (Real.log (N:ℝ)))*Real.log (8*Real.log (Real.log (N:ℝ))+60) ≤
        (1/ 40 : ℝ)*(Real.log (N:ℝ))^((1 : ℝ)/ 10):=by
    have hev:∀ᶠ L:ℝ in atTop,
        (A*Real.log L)*Real.log (8*Real.log L+60)≤ (1/ 40 : ℝ)*L^((1 : ℝ)/ 10):=by
      have hlog:∀ᶠ L:ℝ in atTop,Real.log L≤ L^((1 : ℝ)/ 25):=by
        filter_upwards [eventually_ge_atTop (1 : ℝ),
          ((isLittleO_log_rpow_atTop (by norm_num:(0 : ℝ)< 1/ 25)).tendsto_div_nhds_zero).eventually
            (Iio_mem_nhds one_pos)] with L hL hlt
        exact (div_le_one (Real.rpow_pos_of_pos (by linarith) _)).mp hlt.le
      have hpow:∀ᶠ L:ℝ in atTop,40*A*68*L^((2 : ℝ)/ 25)≤ L^((1 : ℝ)/ 10):=by
        have h0:Tendsto (fun L:ℝ=>(40*A*68)*L^(-((1 : ℝ)/ 50))) atTop (𝓝 0):=by
          simpa using (tendsto_rpow_neg_atTop (by norm_num:(0 : ℝ)< 1/ 50)).const_mul (40*A*68)
        filter_upwards [eventually_ge_atTop (1 : ℝ),h0.eventually (Iio_mem_nhds one_pos)] with L hL hlt
        have hLpos:0< L:=by linarith
        have hmul:L^(-((1 : ℝ)/ 50))*L^((1 : ℝ)/ 10)=L^((2 : ℝ)/ 25):=by
          rw [← Real.rpow_add hLpos]; congr 1; norm_num
        calc
          40*A*68*L^((2 : ℝ)/ 25)
              = ((40*A*68)*L^(-((1 : ℝ)/ 50)))*L^((1 : ℝ)/ 10):=by rw [← hmul]; ring
          _≤ 1*L^((1 : ℝ)/ 10) :=
                mul_le_mul_of_nonneg_right hlt.le (Real.rpow_pos_of_pos hLpos _).le
          _=L^((1 : ℝ)/ 10):=one_mul _
      filter_upwards [eventually_ge_atTop (3 : ℝ),hlog,hpow] with L hL hlog' hpow'
      have hLpos:0< L:=by linarith
      have h1r:1≤ L^((1 : ℝ)/ 25):=Real.one_le_rpow (by linarith) (by norm_num)
      have hlogL_nn:0≤ Real.log L:=Real.log_nonneg (by linarith)
      have hlog_in_nn:0≤ Real.log (8*Real.log L+60):=Real.log_nonneg (by linarith)
      have hlog_in:Real.log (8*Real.log L+60)≤ 68*L^((1 : ℝ)/ 25):=by
        have h1:Real.log (8*Real.log L+60)≤ 8*Real.log L+60:=by
          linarith [Real.log_le_sub_one_of_pos (by linarith:0< 8*Real.log L+60)]
        linarith
      have hsq:L^((1 : ℝ)/ 25)*L^((1 : ℝ)/ 25)=L^((2 : ℝ)/ 25):=by
        rw [← Real.rpow_add hLpos]; congr 1; norm_num
      calc
        (A*Real.log L)*Real.log (8*Real.log L+60)
            ≤ (A*L^((1 : ℝ)/ 25))*(68*L^((1 : ℝ)/ 25)):=by gcongr
        _=A*68*(L^((1 : ℝ)/ 25)*L^((1 : ℝ)/ 25)):=by ring
        _=A*68*L^((2 : ℝ)/ 25):=by rw [hsq]
        _≤ (1/ 40 : ℝ)*L^((1 : ℝ)/ 10):=by linarith
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually hev
  filter_upwards [xd hA,hL_err] with N hR hL_err'
  refine ⟨hR,fun v7 s j hkstar2 hkstarK hs3 hj1 hjs hsA=>?_⟩
  set L:=Real.log (N:ℝ)
  have hNpos:(0 : ℝ)< N:=by linarith [Real.add_one_le_exp (2 : ℝ),hR.1]
  have hN1:(1 : ℝ)≤ N:=by linarith [Real.add_one_le_exp (2 : ℝ),hR.1]
  have hN1_nat:1≤ N:=by exact_mod_cast hN1
  have hL2:2≤ L:=by
    calc (2 : ℝ)=Real.log (Real.exp 2):=(Real.log_exp 2).symm
      _≤ L:=Real.log_le_log (Real.exp_pos 2) hR.1
  let k₀ : Fin (z0 N):=⟨v7 - 1,by omega⟩
  have hk0_eq:k₀.1+1=v7:=by dsimp [k₀]; omega
  set R:=z9 A N k₀
  have hRk_eq:Rk A N v7=R:=by
    dsimp [R]; unfold z9; rw [hk0_eq]
  rw [hRk_eq]
  have hR_ge_w:yD N≤ R:=(hR.2.2.2.2.2.2.1 k₀).1
  have hR_ge_e:Real.exp 1≤ R:=by
    have hw16:(16 : ℝ)≤ yD N:=by
      have : (16 : ℝ)≤ (z7 N:ℝ):=by exact_mod_cast hR.2.1
      have hfl:(z7 N:ℝ)≤ yD N:=Nat.floor_le (by unfold yD; linarith)
      linarith
    have he3:Real.exp 1≤ 3:=Real.exp_one_lt_d9.le.trans (by norm_num)
    linarith
  have hR_le_N:R≤ (N:ℝ):=by
    dsimp [R]; rw [wu]
    conv_rhs=>rw [← Real.rpow_one (N:ℝ)]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    have hk1:(1 : ℝ)≤ ((k₀.1+1 : ℕ):ℝ)^50:=one_le_pow₀ (by exact_mod_cast Nat.succ_pos k₀.1)
    rw [div_le_one (by positivity)]; nlinarith
  have hlogR_pos:0< Real.log R:=Real.log_pos (by linarith [Real.add_one_le_exp (1 : ℝ)])
  set Pmed:=z2 (z7 N) ⌊R⌋₊
  have hterm_51:∀ T∈Pmed.powersetCard j,
      (j.factorial:ℝ)*(xb A N v7 (∏ p∈T,p)/ zY A N) ≤
        (j.factorial:ℝ)*(4*((2 : ℝ)^j/ (∏ p∈T,(p:ℝ)))*Ik A N v7 (∏ p∈T,p) k₀) +
        (j.factorial:ℝ)*(((4 : ℝ)^j/ (∏ p∈T,(p:ℝ))) *
          Real.exp (-(1/ 40 : ℝ)*L^((1 : ℝ)/ 10))):=by
    intro T hT
    rcases mem_powersetCard.mp hT with ⟨hTsub,hTcard⟩
    have hT_info:∀ p∈T,p.Prime∧z7 N< p∧(p:ℝ)≤ R:=fun p hp=>by
      have hm:=hTsub hp
      simp only [Pmed,z2,mem_filter,mem_Ioc] at hm
      exact ⟨hm.2,hm.1.1,(Nat.cast_le.mpr hm.1.2).trans (Nat.floor_le (by linarith [Real.exp_pos 1]))⟩
    set v6:=∏ p∈T,p
    obtain ⟨hdstar_sf,hdstar_pf⟩:=zG fun p hp=>(hT_info p hp).1
    have hdstar_cop:Nat.Coprime v6 (z4 N) :=
      yK fun p hp=>⟨(hT_info p hp).1,(hT_info p hp).2.1⟩
    have hdstar_card:v6.primeFactors.card=j:=by rw [hdstar_pf,hTcard]
    have hdstar_cast:(v6:ℝ)=∏ p∈T,(p:ℝ):=by dsimp [v6]; rw [Nat.cast_prod]
    have hdstar_le:(v6:ℝ)≤ (N:ℝ)^((1 : ℝ)/ 5):=by
      calc
        (v6:ℝ)=∏ p∈T,(p:ℝ):=hdstar_cast
        _≤ ∏ _p∈T,R:=prod_le_prod (fun _ _=>by positivity) fun p hp=>(hT_info p hp).2.2
        _=R^j:=by rw [prod_const,hTcard]
        _=(N:ℝ)^((j:ℝ)/ (100*(A+1)*(v7:ℝ)^50)):=by
              dsimp [R]; rw [wu,hk0_eq,← Real.rpow_natCast,← Real.rpow_mul hNpos.le]
              congr 1; ring
        _≤ (N:ℝ)^((1 : ℝ)/ 5):=by
              apply Real.rpow_le_rpow_of_exponent_le hN1
              rw [div_le_iff₀ (by positivity)]
              have hj_le_s:(j:ℝ)≤ (s:ℝ):=by exact_mod_cast hjs
              have hlogk_le:Real.log (v7:ℝ)≤ (v7:ℝ):=by
                linarith [Real.log_le_sub_one_of_pos (by positivity:(0 : ℝ)< v7)]
              have hk_le50:(v7:ℝ)≤ (v7:ℝ)^50:=by
                conv_lhs=>rw [← pow_one (v7:ℝ)]
                exact pow_le_pow_right₀ (by exact_mod_cast (show 1≤ v7 by omega)) (by norm_num)
              nlinarith [show (0 : ℝ)≤ (v7:ℝ)^50 by positivity]
    have hkstarN:v7< N:=by have:=hR.2.2.2.2.1; have:=hR.2.2.2.2.2.1; omega
    have h51:=yE hA hR hkstarN hdstar_sf hdstar_cop hdstar_le
    rw [hdstar_card,hdstar_cast] at h51
    have hPk_k0:zu N v7 v6 k₀=T:=by
      unfold zu; rw [hdstar_pf]; ext p; simp only [mem_filter,and_iff_left_iff_imp]
      intro _; rw [hk0_eq,sub_self]; exact dvd_zero _
    have hfilt_eq:Finset.univ.filter (fun k:Fin (z0 N)=>(zu N v7 v6 k).Nonempty)={k₀}:=by
      ext k; simp only [mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
      constructor
      · rintro ⟨p,hp⟩
        rcases mem_filter.mp hp with ⟨hp_pf,hpdvd⟩
        rw [hdstar_pf] at hp_pf
        have hpK:z0 N< p:=by have:=(hT_info p hp_pf).2.1; have:=hR.2.2.2.1; omega
        exact yP hpK hpdvd (by rw [hk0_eq,sub_self]; exact dvd_zero _)
      · rintro rfl; rw [hPk_k0]; exact Finset.card_pos.mp (by omega)
    rw [hfilt_eq,Finset.prod_singleton] at h51
    have hmul:=mul_le_mul_of_nonneg_left h51 (Nat.cast_nonneg (α:=ℝ) j.factorial)
    linarith
  refine (sum_le_sum hterm_51).trans ?_
  rw [sum_add_distrib]
  have hlogs_ge1:1≤ Real.log (s:ℝ):=by
    have hs_e:Real.exp 1≤ (s:ℝ):=by
      have he3:Real.exp 1≤ 3:=Real.exp_one_lt_d9.le.trans (by norm_num)
      have : (3 : ℝ)≤ (s:ℝ):=by exact_mod_cast hs3
      linarith
    calc (1 : ℝ)=Real.log (Real.exp 1):=(Real.log_exp 1).symm
      _≤ Real.log (s:ℝ):=Real.log_le_log (Real.exp_pos 1) hs_e
  have hpow_s_ge1:(1 : ℝ)≤ (zg*Real.log (s:ℝ))^s:=by
    apply one_le_pow₀; unfold zg; linarith
  have herr_sum :
      ∑ T∈Pmed.powersetCard j,
          (j.factorial:ℝ)*(((4 : ℝ)^j/ (∏ p∈T,(p:ℝ))) *
            Real.exp (-(1/ 40 : ℝ)*L^((1 : ℝ)/ 10)))≤ 1:=by
    have hrew:∀ T∈Pmed.powersetCard j,
        (j.factorial:ℝ)*(((4 : ℝ)^j/ (∏ p∈T,(p:ℝ))) *
          Real.exp (-(1/ 40 : ℝ)*L^((1 : ℝ)/ 10))) =
        ((4 : ℝ)^j*Real.exp (-(1/ 40 : ℝ)*L^((1 : ℝ)/ 10))) *
          ((j.factorial:ℝ)*∏ p∈T,((1 : ℝ)/ (p:ℝ))):=fun T _=>by
      rw [prod_div_distrib,prod_const_one]; ring
    rw [sum_congr rfl hrew,← mul_sum]
    have hfact_sum:=zP Pmed (h:=fun p=>(1 : ℝ)/ (p:ℝ))
      (fun _ _=>by positivity) j
    have hPmed_le:∑ p∈Pmed,(1 : ℝ)/ (p:ℝ)≤ 2*Real.log L+15:=by
      have hsub:Pmed⊆z5 ⌊(N:ℝ)⌋₊:=by
        intro p hp
        simp only [Pmed,z2,z5,mem_filter,mem_Ioc,mem_Icc] at hp ⊢
        exact ⟨⟨hp.2.one_le,hp.1.2.trans (Nat.floor_mono hR_le_N)⟩,hp.2⟩
      exact (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _=>by positivity).trans
        (yJ (le_trans (Real.exp_le_exp.mpr (by norm_num)) hR.1))
    have hj_le_AL:(j:ℝ)≤ A*Real.log L:=by
      have hK_le:(z0 N:ℝ)≤ L^((1 : ℝ)/ 1000):=Nat.floor_le (by positivity)
      have hk_le:(v7:ℝ)≤ L:=by
        have h1:(v7:ℝ)≤ (z0 N:ℝ):=by exact_mod_cast hkstarK
        have h2:L^((1 : ℝ)/ 1000)≤ L:=by
          conv_rhs=>rw [← Real.rpow_one L]
          exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        linarith
      have hlogk:Real.log (v7:ℝ)≤ Real.log L:=Real.log_le_log (by positivity) hk_le
      have hj_s:(j:ℝ)≤ (s:ℝ):=by exact_mod_cast hjs
      nlinarith
    have hbase_ge1:(1 : ℝ)≤ 8*Real.log L+60:=by
      have : 0≤ Real.log L:=Real.log_nonneg (by linarith)
      linarith
    calc
      ((4 : ℝ)^j*Real.exp (-(1/ 40 : ℝ)*L^((1 : ℝ)/ 10))) *
          ∑ T∈Pmed.powersetCard j,(j.factorial:ℝ)*∏ p∈T,((1 : ℝ)/ (p:ℝ))
          ≤ ((4 : ℝ)^j*Real.exp (-(1/ 40 : ℝ)*L^((1 : ℝ)/ 10))) *
              (∑ p∈Pmed,(1 : ℝ)/ (p:ℝ))^j:=by gcongr
      _=(4*∑ p∈Pmed,(1 : ℝ)/ (p:ℝ))^j*Real.exp (-(1/ 40 : ℝ)*L^((1 : ℝ)/ 10)):=by
            rw [mul_pow]; ring
      _≤ (8*Real.log L+60)^j*Real.exp (-(1/ 40 : ℝ)*L^((1 : ℝ)/ 10)):=by
            have h1:4*∑ p∈Pmed,(1 : ℝ)/ (p:ℝ)≤ 8*Real.log L+60:=by linarith
            gcongr
      _=Real.exp ((j:ℝ)*Real.log (8*Real.log L+60) - (1/ 40 : ℝ)*L^((1 : ℝ)/ 10)):=by
            rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by linarith),← Real.exp_add]
            congr 1; ring
      _≤ Real.exp 0:=by
            apply Real.exp_le_exp.mpr
            have hlog_nn:0≤ Real.log (8*Real.log L+60):=Real.log_nonneg hbase_ge1
            have : (j:ℝ)*Real.log (8*Real.log L+60) ≤
                (A*Real.log L)*Real.log (8*Real.log L+60) :=
              mul_le_mul_of_nonneg_right hj_le_AL hlog_nn
            linarith
      _=1:=Real.exp_zero
  have hmain_sum :
      ∑ T∈Pmed.powersetCard j,
          (j.factorial:ℝ)*(4*((2 : ℝ)^j/ (∏ p∈T,(p:ℝ)))*Ik A N v7 (∏ p∈T,p) k₀) ≤
        (xr - 1)*(zg*Real.log (s:ℝ))^s :=
    ww k₀ hk0_eq hR_ge_e hs3 hjs
  linarith
end
end Erdos413Sieve
namespace Erdos413Main
open Finset Filter Topology Complex Real MeasureTheory
open Erdos413Bump Erdos413Mertens Erdos413Moments Erdos413Sieve
open scoped BigOperators
noncomputable section
def zo:ℝ:=max 100 (4*(xj+xr))
def z1:ℝ:=2*Real.log zo+4
def yg:ℝ:=4*Real.log (100*(z1+1))+2024
def zB:ℝ:=4*(Real.exp 1)^2*zg*z1
def zE:ℝ:=8*(Real.exp 1)^2*(z1+yg)
def w7:ℝ:=max 400 (2+zB+zE+20*z1)
lemma w8:100≤ zo:=le_max_left _ _
lemma wJ:0< zo:=by linarith [w8]
lemma zv:1≤ z1:=by
  unfold z1
  have hlog:0≤ Real.log zo:=Real.log_nonneg (by linarith [w8])
  linarith
lemma v0:0< yg:=by
  unfold yg
  have hlog:0≤ Real.log (100*(z1+1)):=Real.log_nonneg (by linarith [zv])
  linarith
lemma wV:0< w7:=by
  unfold w7
  exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
lemma w2 {N k:ℕ} (hR:zM z1 N)
    (hk2:2≤ k) (_hkKp:k≤ yI N) :
    ∑ p∈z2 ⌊Rk z1 N k⌋₊ ⌊Tk z1 N k⌋₊,(1 : ℝ)/ (p:ℝ) ≤
      yg*Real.log (k:ℝ):=by
  set L:=Real.log (N:ℝ)
  have hNpos:(0 : ℝ)< N:=by linarith [Real.add_one_le_exp (2 : ℝ),hR.1]
  have hN1_nat:1≤ N:=by
    have : (1 : ℝ)< N:=by linarith [Real.add_one_le_exp (2 : ℝ),hR.1]
    exact_mod_cast this.le
  have hL2:2≤ L:=by
    calc (2 : ℝ)=Real.log (Real.exp 2):=(Real.log_exp 2).symm
      _≤ L:=Real.log_le_log (Real.exp_pos 2) hR.1
  have hlogk_ge:1/ 2≤ Real.log (k:ℝ) :=
    zC.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hk2))
  have hlogk_pos:0< Real.log (k:ℝ):=by linarith
  by_cases horder:Rk z1 N k≤ Tk z1 N k
  · have hRk_ge_w:yD N≤ Rk z1 N k:=by
      by_cases hcond:1≤ k∧k≤ z0 N
      · have hEq:Rk z1 N k=z9 z1 N ⟨k - 1,by omega⟩:=by
          unfold z9; dsimp; congr 1; omega
        rw [hEq]; exact (hR.2.2.2.2.2.2.1 ⟨k - 1,by omega⟩).1
      · unfold Rk; rw [if_neg hcond]
    have hw_ge16:(16 : ℝ)≤ yD N:=by
      have : (16 : ℝ)≤ (z7 N:ℝ):=by exact_mod_cast hR.2.1
      have hfl:(z7 N:ℝ)≤ yD N:=Nat.floor_le (by unfold yD; linarith)
      linarith
    have hRk_ge2:2≤ Rk z1 N k:=by linarith
    have hmert:=yk hRk_ge2 horder
    have hlogTk_le:Real.log (Tk z1 N k)≤ L:=by
      unfold Tk
      rw [Real.log_rpow hNpos,one_div_mul_eq_div]
      apply div_le_self (by linarith)
      have hA:=zv
      nlinarith
    have hlogTk_pos:0< Real.log (Tk z1 N k):=by
      unfold Tk; rw [Real.log_rpow hNpos,one_div_mul_eq_div]
      have hA:=zv; positivity
    have hlogRk_pos:0< Real.log (Rk z1 N k):=Real.log_pos (by linarith)
    refine hmert.trans ?_
    by_cases hkK:k≤ z0 N
    ·
      have hlogRk:Real.log (Rk z1 N k)=L/ (100*(z1+1)*(k:ℝ)^50):=by
        have h1:Rk z1 N k=z9 z1 N ⟨k - 1,by omega⟩:=by
          unfold z9; dsimp; congr 1; omega
        rw [h1,xV z1 hN1_nat ⟨k - 1,by omega⟩]
        dsimp
        have hksub:k - 1+1=k:=by omega
        rw [hksub]
      have hratio:Real.log (Tk z1 N k)/ Real.log (Rk z1 N k) ≤
          100*(z1+1)*(k:ℝ)^50:=by
        rw [hlogRk,div_div_eq_mul_div,div_le_iff₀ (by linarith)]
        have h1:Real.log (Tk z1 N k)*(100*(z1+1)*(k:ℝ)^50) ≤
            L*(100*(z1+1)*(k:ℝ)^50) :=
          mul_le_mul_of_nonneg_right hlogTk_le (by have:=zv; positivity)
        linarith
      have hlog_ratio:Real.log (Real.log (Tk z1 N k)/ Real.log (Rk z1 N k)) ≤
          Real.log (100*(z1+1))+50*Real.log (k:ℝ):=by
        have h1:=Real.log_le_log (div_pos hlogTk_pos hlogRk_pos) hratio
        rw [Real.log_mul (by have:=zv; positivity) (by positivity),Real.log_pow] at h1
        push_cast at h1
        exact h1
      have hlogA_nn:0≤ Real.log (100*(z1+1)) :=
        Real.log_nonneg (by linarith [zv])
      unfold yg
      nlinarith
    ·
      push Not at hkK
      have hlogRk_ge1:1≤ Real.log (Rk z1 N k):=by
        have he3:Real.exp 1≤ 3:=Real.exp_one_lt_d9.le.trans (by norm_num)
        calc (1 : ℝ)=Real.log (Real.exp 1):=(Real.log_exp 1).symm
          _≤ Real.log (Rk z1 N k):=Real.log_le_log (Real.exp_pos 1) (by linarith)
      have hratio:Real.log (Tk z1 N k)/ Real.log (Rk z1 N k)≤ L :=
        (div_le_self hlogTk_pos.le hlogRk_ge1).trans hlogTk_le
      have hk_gt_rpow:L^((1 : ℝ)/ 1000)< (k:ℝ):=by
        have hfl:=Nat.lt_floor_add_one (L^((1 : ℝ)/ 1000))
        have hle:(z0 N:ℝ)+1≤ (k:ℝ):=by exact_mod_cast hkK
        unfold z0 at hle
        linarith
      have hlogL_le:Real.log L≤ 1000*Real.log (k:ℝ):=by
        have h1:=Real.log_le_log (Real.rpow_pos_of_pos (by linarith) _) hk_gt_rpow.le
        rw [Real.log_rpow (by linarith)] at h1
        linarith
      have hlog_ratio:Real.log (Real.log (Tk z1 N k)/ Real.log (Rk z1 N k)) ≤
          1000*Real.log (k:ℝ) :=
        (Real.log_le_log (div_pos hlogTk_pos hlogRk_pos) hratio).trans hlogL_le
      have hlogA_nn:0≤ Real.log (100*(z1+1)) :=
        Real.log_nonneg (by linarith [zv])
      unfold yg
      nlinarith
  ·
    push Not at horder
    have hfl:⌊Tk z1 N k⌋₊≤ ⌊Rk z1 N k⌋₊:=Nat.floor_mono horder.le
    have hemp:z2 ⌊Rk z1 N k⌋₊ ⌊Tk z1 N k⌋₊=∅:=by
      unfold z2
      rw [filter_eq_empty_iff]
      intro p hp
      have:=mem_Ioc.mp hp
      omega
    rw [hemp,sum_empty]
    exact mul_nonneg v0.le hlogk_pos.le
lemma xR :
    ∀ᶠ N:ℕ in atTop,
      ∃ n∈Finset.Ioc N (2*N),
        ∀ k:ℕ,2≤ k→k< n →
          ((ArithmeticFunction.cardDistinctFactors (n - k):ℕ):ℝ)≤ w7*Real.log (k:ℝ):=by
  filter_upwards [v4 zv,v3 zv] with N ⟨hR,h4B⟩ ⟨_,h4C⟩
  classical
  set L:=Real.log (N:ℝ)
  have hNpos:(0 : ℝ)< N:=by linarith [Real.add_one_le_exp (2 : ℝ),hR.1]
  have hL2:2≤ L:=by
    calc (2 : ℝ)=Real.log (Real.exp 2):=(Real.log_exp 2).symm
      _≤ L:=Real.log_le_log (Real.exp_pos 2) hR.1
  obtain ⟨_,hZ_pos⟩:=xY zv hR
  let Pmed:ℕ→Finset ℕ:=fun k=>z2 (z7 N) ⌊Rk z1 N k⌋₊
  let Plarge:ℕ→Finset ℕ:=fun k=>z2 ⌊Rk z1 N k⌋₊ ⌊Tk z1 N k⌋₊
  let Xmed:ℕ→ℕ→ℝ:=fun k n =>
    ∑ p∈Pmed k,if p∣n - k then (1 : ℝ) else 0
  let Xlarge:ℕ→ℕ→ℝ:=fun k n =>
    ∑ p∈Plarge k,if p∣n - k then (1 : ℝ) else 0
  let BadMed:ℕ→ℕ→Prop:=fun k n =>
    k≤ z0 N∧zB*Real.log (k:ℝ)≤ Xmed k n
  let BadLarge:ℕ→ℕ→Prop:=fun k n =>
    zE*Real.log (k:ℝ)≤ Xlarge k n
  have hs_props:∀ k:ℕ,2≤ k →
      let s:=⌈Real.log (zo*(k:ℝ)^2)⌉₊
      3≤ s∧(s:ℝ)≤ z1*Real.log (k:ℝ) ∧
        Real.exp (-(s:ℝ))≤ 1/ (zo*(k:ℝ)^2):=by
    intro k hk2
    dsimp only
    set s:=⌈Real.log (zo*(k:ℝ)^2)⌉₊
    have hlogk_ge:1/ 2≤ Real.log (k:ℝ) :=
      zC.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hk2))
    have hCk2_pos:0< zo*(k:ℝ)^2:=by
      have:=wJ; positivity
    have hCk2_ge:Real.exp 3≤ zo*(k:ℝ)^2:=by
      have he3:Real.exp 3≤ 27:=by
        have h1:Real.exp 1≤ 3:=Real.exp_one_lt_d9.le.trans (by norm_num)
        have h3:Real.exp 3=(Real.exp 1)^3:=by rw [← Real.exp_nat_mul]; norm_num
        rw [h3]
        calc (Real.exp 1)^3≤ 3^3:=pow_le_pow_left₀ (Real.exp_pos 1).le h1 3
          _=27:=by norm_num
      have hk4:(4 : ℝ)≤ (k:ℝ)^2:=by
        have : (2 : ℝ)≤ (k:ℝ):=by exact_mod_cast hk2
        nlinarith
      have:=w8
      nlinarith
    have hlog_ge3:3≤ Real.log (zo*(k:ℝ)^2):=by
      calc (3 : ℝ)=Real.log (Real.exp 3):=(Real.log_exp 3).symm
        _≤ Real.log (zo*(k:ℝ)^2):=Real.log_le_log (Real.exp_pos 3) hCk2_ge
    have hs3:3≤ s:=Nat.le_ceil _ |> fun h=>by
      have : (3 : ℝ)≤ (s:ℝ):=hlog_ge3.trans h
      exact_mod_cast this
    have hs_ub:(s:ℝ)≤ z1*Real.log (k:ℝ):=by
      have hlt:(s:ℝ)< Real.log (zo*(k:ℝ)^2)+1 :=
        Nat.ceil_lt_add_one (by linarith:0≤ Real.log (zo*(k:ℝ)^2))
      rw [Real.log_mul wJ.ne' (by positivity),Real.log_pow] at hlt
      push_cast at hlt
      have hlogC_nn:0≤ Real.log zo:=Real.log_nonneg (by linarith [w8])
      unfold z1
      nlinarith
    have hexp_le:Real.exp (-(s:ℝ))≤ 1/ (zo*(k:ℝ)^2):=by
      have hle:Real.log (zo*(k:ℝ)^2)≤ (s:ℝ):=Nat.le_ceil _
      calc
        Real.exp (-(s:ℝ))≤ Real.exp (-Real.log (zo*(k:ℝ)^2)) :=
          Real.exp_le_exp.mpr (by linarith)
        _=1/ (zo*(k:ℝ)^2):=by
          rw [Real.exp_neg,Real.exp_log hCk2_pos,one_div]
    exact ⟨hs3,hs_ub,hexp_le⟩
  have hMed_markov:∀ k∈Finset.Icc 2 (yI N),
      ∑ n∈Finset.Ioc N (2*N),(if BadMed k n then zl z1 N n else 0) ≤
        ((1/ 4 : ℝ)/ (k:ℝ)^2)*zY z1 N:=by
    classical
    intro k hk
    rcases mem_Icc.mp hk with ⟨hk2,_⟩
    by_cases hkK:k≤ z0 N
    · set s:=⌈Real.log (zo*(k:ℝ)^2)⌉₊
      obtain ⟨hs3,hsA,hexp_s⟩:=hs_props k hk2
      have hlogk_pos:0< Real.log (k:ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1< k by omega))
      have hlogs_pos:0< Real.log (s:ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1< s by omega))
      have hlam_pos:0< zB*Real.log (k:ℝ):=by
        unfold zB zg; have:=zv; positivity
      have hmoment :
          ∑ n∈Finset.Ioc N (2*N),zl z1 N n*(Xmed k n)^s ≤
            (xr*(4*Real.exp 1*zg*(s:ℝ))^s)*zY z1 N:=by
        have hexpand:∀ n∈Finset.Ioc N (2*N),
            (Xmed k n)^s =
              ∑ j∈Finset.Icc 1 s,(Nat.stirlingSecond s j:ℝ) *
                ∑ T∈(Pmed k).powersetCard j,(j.factorial:ℝ) *
                  if (∏ p∈T,p)∣n - k then (1 : ℝ) else 0:=by
          intro n _
          have h1:=xk (Pmed k) (f:=fun p=>if p∣n - k then (1 : ℝ) else 0)
            (fun p _=>by split_ifs <;> ring) s
          have hP_pr:∀ p∈Pmed k,p.Prime:=fun p hp=>(mem_filter.mp hp).2
          have h0:(Nat.stirlingSecond s 0 : ℝ)=0:=by
            have : Nat.stirlingSecond s 0=0:=by
              obtain ⟨m,hm⟩:=Nat.exists_eq_succ_of_ne_zero (by omega:s≠0)
              rw [hm,Nat.stirlingSecond_succ_zero]
            exact_mod_cast this
          have hrange:Finset.range (s+1)=insert 0 (Finset.Icc 1 s):=by
            ext j; simp only [Finset.mem_range,mem_insert,mem_Icc]; omega
          dsimp only [Xmed]
          rw [h1,hrange,sum_insert (by simp),h0,zero_mul,zero_add]
          refine sum_congr rfl fun j _=>?_
          congr 1
          refine sum_congr rfl fun T hT=>?_
          congr 1
          exact yW
            (fun p hp=>hP_pr p ((mem_powersetCard.mp hT).1 hp)) (n - k)
        calc
          ∑ n∈Finset.Ioc N (2*N),zl z1 N n*(Xmed k n)^s
              = ∑ n∈Finset.Ioc N (2*N),zl z1 N n *
                  ∑ j∈Finset.Icc 1 s,(Nat.stirlingSecond s j:ℝ) *
                    ∑ T∈(Pmed k).powersetCard j,(j.factorial:ℝ) *
                      if (∏ p∈T,p)∣n - k then (1 : ℝ) else 0 :=
                sum_congr rfl fun n hn=>by rw [hexpand n hn]
          _=∑ j∈Finset.Icc 1 s,(Nat.stirlingSecond s j:ℝ) *
                (∑ T∈(Pmed k).powersetCard j,(j.factorial:ℝ) *
                  (xb z1 N k (∏ p∈T,p)/ zY z1 N))*zY z1 N:=by
                conv_lhs=>arg 2; ext n; rw [mul_sum]
                rw [sum_comm]
                refine sum_congr rfl fun j _=>?_
                have hinner:∑ n∈Finset.Ioc N (2*N),
                    zl z1 N n*((Nat.stirlingSecond s j:ℝ) *
                      ∑ T∈(Pmed k).powersetCard j,(j.factorial:ℝ) *
                        if (∏ p∈T,p)∣n - k then (1 : ℝ) else 0) =
                    (Nat.stirlingSecond s j:ℝ) *
                      ∑ T∈(Pmed k).powersetCard j,(j.factorial:ℝ)*xb z1 N k (∏ p∈T,p):=by
                  have hrew:∀ n∈Finset.Ioc N (2*N),
                      zl z1 N n*((Nat.stirlingSecond s j:ℝ) *
                        ∑ T∈(Pmed k).powersetCard j,(j.factorial:ℝ) *
                          if (∏ p∈T,p)∣n - k then (1 : ℝ) else 0) =
                      (Nat.stirlingSecond s j:ℝ) *
                        ∑ T∈(Pmed k).powersetCard j,(j.factorial:ℝ) *
                          (zl z1 N n*if (∏ p∈T,p)∣n - k then (1 : ℝ) else 0):=fun n _=>by
                    rw [mul_sum,mul_sum,mul_sum]
                    refine sum_congr rfl fun T _=>by ring
                  rw [sum_congr rfl hrew,← mul_sum,sum_comm]
                  congr 1
                  refine sum_congr rfl fun T _=>?_
                  rw [← mul_sum]; rfl
                rw [hinner,mul_assoc]
                congr 1
                rw [sum_mul]
                refine sum_congr rfl fun T _=>?_
                field_simp [hZ_pos.ne']
          _≤ ∑ j∈Finset.Icc 1 s,
                ((2*Real.exp 1*(s:ℝ)/ Real.log (s:ℝ))^s *
                 (xr*(zg*Real.log (s:ℝ))^s))*zY z1 N:=by
                refine sum_le_sum fun j hj=>?_
                rcases mem_Icc.mp hj with ⟨hj1,hjs⟩
                have hst:=wc hs3 hjs
                have h4c:=h4C k s j hk2 hkK hs3 hj1 hjs hsA
                have hnn:0≤ ∑ T∈(Pmed k).powersetCard j,(j.factorial:ℝ) *
                    (xb z1 N k (∏ p∈T,p)/ zY z1 N) :=
                  sum_nonneg fun T _=>mul_nonneg (Nat.cast_nonneg _)
                    (div_nonneg (xK _ _ _ _) hZ_pos.le)
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul hst h4c hnn (by positivity)) hZ_pos.le
          _=(s:ℝ)*(xr*(2*Real.exp 1*zg*(s:ℝ))^s)*zY z1 N:=by
                rw [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul]
                have hmul:(2*Real.exp 1*(s:ℝ)/ Real.log (s:ℝ))^s*(zg*Real.log (s:ℝ))^s =
                    (2*Real.exp 1*zg*(s:ℝ))^s:=by
                  rw [← mul_pow]; congr 1; field_simp [hlogs_pos.ne']
                linarith [show (s:ℝ)*((2*Real.exp 1*(s:ℝ)/ Real.log (s:ℝ))^s *
                    (xr*(zg*Real.log (s:ℝ))^s)*zY z1 N) =
                    (s:ℝ)*(xr*((2*Real.exp 1*(s:ℝ)/ Real.log (s:ℝ))^s *
                      (zg*Real.log (s:ℝ))^s))*zY z1 N by ring,
                    congrArg (fun x=>(s:ℝ)*(xr*x)*zY z1 N) hmul]
          _≤ (xr*(4*Real.exp 1*zg*(s:ℝ))^s)*zY z1 N:=by
                have hs2s:(s:ℝ)≤ (2 : ℝ)^s:=by exact_mod_cast Nat.lt_two_pow_self.le
                have hpow4:(2 : ℝ)^s*(2*Real.exp 1*zg*(s:ℝ))^s =
                    (4*Real.exp 1*zg*(s:ℝ))^s:=by
                  rw [← mul_pow]; congr 1; ring
                have h1:(s:ℝ)*(2*Real.exp 1*zg*(s:ℝ))^s ≤
                    (4*Real.exp 1*zg*(s:ℝ))^s:=by
                  rw [← hpow4]
                  exact mul_le_mul_of_nonneg_right hs2s (by unfold zg; positivity)
                have:=mul_le_mul_of_nonneg_left h1 wv.le
                have:=mul_le_mul_of_nonneg_right this hZ_pos.le
                linarith
      have hmk:=wa (I:=Finset.Ioc N (2*N)) (ν:=zl z1 N)
        (X:=Xmed k) (fun n _=>yw z1 N n)
        (fun n _=>sum_nonneg fun _ _=>by split_ifs <;> norm_num) hlam_pos s
      rw [sum_filter] at hmk
      have hbad_le:∑ n∈Finset.Ioc N (2*N),(if BadMed k n then zl z1 N n else 0) ≤
          ∑ n∈Finset.Ioc N (2*N),
            (if zB*Real.log (k:ℝ)≤ Xmed k n then zl z1 N n else 0):=by
        refine sum_le_sum fun n _=>?_
        dsimp only [BadMed]
        by_cases h:zB*Real.log (k:ℝ)≤ Xmed k n <;> simp [hkK,h]
      refine hbad_le.trans ((sum_congr rfl fun n _=>by
        by_cases h:zB*Real.log (k:ℝ)≤ Xmed k n <;> simp [h]).le.trans (hmk.trans ?_))
      have hdiv_s:(4*Real.exp 1*zg*(s:ℝ))^s/ (zB*Real.log (k:ℝ))^s ≤
          Real.exp (-(s:ℝ)):=by
        rw [← div_pow]
        have hbase:(4*Real.exp 1*zg*(s:ℝ))/ (zB*Real.log (k:ℝ)) ≤
            Real.exp (-1):=by
          rw [div_le_iff₀ hlam_pos,Real.exp_neg]
          unfold zB
          have h1:(Real.exp 1)^2*(Real.exp 1)⁻¹=Real.exp 1:=by
            rw [sq,mul_assoc,mul_inv_cancel₀ (Real.exp_pos 1).ne',mul_one]
          have h2:Real.exp (-1)*(4*(Real.exp 1)^2*zg*z1*Real.log (k:ℝ)) =
              4*Real.exp 1*zg*(z1*Real.log (k:ℝ)):=by
            rw [Real.exp_neg]
            calc (Real.exp 1)⁻¹*(4*(Real.exp 1)^2*zg*z1*Real.log (k:ℝ))
                = 4*((Real.exp 1)^2*(Real.exp 1)⁻¹)*zg*(z1*Real.log (k:ℝ)):=by ring
              _=4*Real.exp 1*zg*(z1*Real.log (k:ℝ)):=by rw [h1]
          rw [← Real.exp_neg,h2]
          have hpos:0≤ 4*Real.exp 1*zg:=by unfold zg; positivity
          exact mul_le_mul_of_nonneg_left hsA hpos
        calc
          ((4*Real.exp 1*zg*(s:ℝ))/ (zB*Real.log (k:ℝ)))^s
              ≤ (Real.exp (-1))^s:=pow_le_pow_left₀ (by unfold zg; positivity) hbase s
          _=Real.exp (-(s:ℝ)):=by rw [← Real.exp_nat_mul]; congr 1; ring
      have hC_ratio:xr/ zo≤ 1/ 4:=by
        rw [div_le_div_iff₀ wJ (by norm_num)]
        have h1:4*(xj+xr)≤ zo:=le_max_right _ _
        linarith [w0]
      calc
        (∑ n∈Finset.Ioc N (2*N),zl z1 N n*(Xmed k n)^s) /
            (zB*Real.log (k:ℝ))^s
            ≤ ((xr*(4*Real.exp 1*zg*(s:ℝ))^s)*zY z1 N) /
                (zB*Real.log (k:ℝ))^s :=
              div_le_div_of_nonneg_right hmoment (by positivity)
        _=xr*((4*Real.exp 1*zg*(s:ℝ))^s /
              (zB*Real.log (k:ℝ))^s)*zY z1 N:=by ring
        _≤ xr*Real.exp (-(s:ℝ))*zY z1 N:=by
              have:=wv; gcongr
        _≤ xr*(1/ (zo*(k:ℝ)^2))*zY z1 N:=by
              have:=wv; gcongr
        _=((xr/ zo)/ (k:ℝ)^2)*zY z1 N:=by ring
        _≤ ((1/ 4 : ℝ)/ (k:ℝ)^2)*zY z1 N:=by gcongr
    ·
      have hzero:∑ n∈Finset.Ioc N (2*N),(if BadMed k n then zl z1 N n else 0)=0 :=
        sum_eq_zero fun n _=>by simp [BadMed,hkK]
      rw [hzero]; positivity
  have hLarge_markov:∀ k∈Finset.Icc 2 (yI N),
      ∑ n∈Finset.Ioc N (2*N),(if BadLarge k n then zl z1 N n else 0) ≤
        ((1/ 4 : ℝ)/ (k:ℝ)^2)*zY z1 N:=by
    classical
    intro k hk
    rcases mem_Icc.mp hk with ⟨hk2,hkKp⟩
    set s:=⌈Real.log (zo*(k:ℝ)^2)⌉₊
    obtain ⟨hs3,hsA,hexp_s⟩:=hs_props k hk2
    have hlogk_pos:0< Real.log (k:ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1< k by omega))
    have hlam_pos:0< zE*Real.log (k:ℝ):=by
      unfold zE; have:=zv; have:=v0; positivity
    set Mk:=∑ p∈Plarge k,(1 : ℝ)/ (p:ℝ)
    have hMk_nn:0≤ Mk:=sum_nonneg fun _ _=>by positivity
    have hMk_le:Mk≤ yg*Real.log (k:ℝ):=w2 hR hk2 hkKp
    have hmoment :
        ∑ n∈Finset.Ioc N (2*N),zl z1 N n*(Xlarge k n)^s ≤
          (xj*(8*Real.exp 1*((s:ℝ)+Mk))^s)*zY z1 N:=by
      have hexpand:∀ n∈Finset.Ioc N (2*N),
          (Xlarge k n)^s =
            ∑ j∈Finset.Icc 1 s,(Nat.stirlingSecond s j:ℝ) *
              ∑ T∈(Plarge k).powersetCard j,(j.factorial:ℝ) *
                if (∏ p∈T,p)∣n - k then (1 : ℝ) else 0:=by
        intro n _
        have h1:=xk (Plarge k) (f:=fun p=>if p∣n - k then (1 : ℝ) else 0)
          (fun p _=>by split_ifs <;> ring) s
        have hP_pr:∀ p∈Plarge k,p.Prime:=fun p hp=>(mem_filter.mp hp).2
        have h0:(Nat.stirlingSecond s 0 : ℝ)=0:=by
          have : Nat.stirlingSecond s 0=0:=by
            obtain ⟨m,hm⟩:=Nat.exists_eq_succ_of_ne_zero (by omega:s≠0)
            rw [hm,Nat.stirlingSecond_succ_zero]
          exact_mod_cast this
        have hrange:Finset.range (s+1)=insert 0 (Finset.Icc 1 s):=by
          ext j; simp only [Finset.mem_range,mem_insert,mem_Icc]; omega
        dsimp only [Xlarge]
        rw [h1,hrange,sum_insert (by simp),h0,zero_mul,zero_add]
        refine sum_congr rfl fun j _=>?_
        congr 1
        refine sum_congr rfl fun T hT=>?_
        congr 1
        exact yW
          (fun p hp=>hP_pr p ((mem_powersetCard.mp hT).1 hp)) (n - k)
      have hs2A:(s:ℝ)≤ 2*z1*Real.log (k:ℝ):=by
        have:=zv; nlinarith
      calc
        ∑ n∈Finset.Ioc N (2*N),zl z1 N n*(Xlarge k n)^s
            = ∑ n∈Finset.Ioc N (2*N),zl z1 N n *
                ∑ j∈Finset.Icc 1 s,(Nat.stirlingSecond s j:ℝ) *
                  ∑ T∈(Plarge k).powersetCard j,(j.factorial:ℝ) *
                    if (∏ p∈T,p)∣n - k then (1 : ℝ) else 0 :=
              sum_congr rfl fun n hn=>by rw [hexpand n hn]
        _=∑ j∈Finset.Icc 1 s,(Nat.stirlingSecond s j:ℝ) *
              (∑ T∈(Plarge k).powersetCard j,(j.factorial:ℝ) *
                (xb z1 N k (∏ p∈T,p)/ zY z1 N))*zY z1 N:=by
              conv_lhs=>arg 2; ext n; rw [mul_sum]
              rw [sum_comm]
              refine sum_congr rfl fun j _=>?_
              have hinner:∑ n∈Finset.Ioc N (2*N),
                  zl z1 N n*((Nat.stirlingSecond s j:ℝ) *
                    ∑ T∈(Plarge k).powersetCard j,(j.factorial:ℝ) *
                      if (∏ p∈T,p)∣n - k then (1 : ℝ) else 0) =
                  (Nat.stirlingSecond s j:ℝ) *
                    ∑ T∈(Plarge k).powersetCard j,(j.factorial:ℝ)*xb z1 N k (∏ p∈T,p):=by
                have hrew:∀ n∈Finset.Ioc N (2*N),
                    zl z1 N n*((Nat.stirlingSecond s j:ℝ) *
                      ∑ T∈(Plarge k).powersetCard j,(j.factorial:ℝ) *
                        if (∏ p∈T,p)∣n - k then (1 : ℝ) else 0) =
                    (Nat.stirlingSecond s j:ℝ) *
                      ∑ T∈(Plarge k).powersetCard j,(j.factorial:ℝ) *
                        (zl z1 N n*if (∏ p∈T,p)∣n - k then (1 : ℝ) else 0):=fun n _=>by
                  rw [mul_sum,mul_sum,mul_sum]
                  refine sum_congr rfl fun T _=>by ring
                rw [sum_congr rfl hrew,← mul_sum,sum_comm]
                congr 1
                refine sum_congr rfl fun T _=>?_
                rw [← mul_sum]; rfl
              rw [hinner,mul_assoc]
              congr 1
              rw [sum_mul]
              refine sum_congr rfl fun T _=>?_
              field_simp [hZ_pos.ne']
        _≤ ∑ j∈Finset.Icc 1 s,(Nat.stirlingSecond s j:ℝ) *
              (xj*(8 : ℝ)^s*Mk^j)*zY z1 N:=by
              refine sum_le_sum fun j hj=>?_
              rcases mem_Icc.mp hj with ⟨hj1,hjs⟩
              have hT_sum:∑ T∈(Plarge k).powersetCard j,(j.factorial:ℝ) *
                  (xb z1 N k (∏ p∈T,p)/ zY z1 N) ≤
                  xj*(8 : ℝ)^s*Mk^j:=by
                calc
                  ∑ T∈(Plarge k).powersetCard j,(j.factorial:ℝ) *
                      (xb z1 N k (∏ p∈T,p)/ zY z1 N)
                      ≤ ∑ T∈(Plarge k).powersetCard j,(j.factorial:ℝ) *
                          (xj*(8 : ℝ)^s/ (∏ p∈T,(p:ℝ))) :=
                        sum_le_sum fun T hT=>mul_le_mul_of_nonneg_left
                          (h4B k s j hk2 hkKp hj1 hjs hs2A T hT) (Nat.cast_nonneg _)
                  _=xj*(8 : ℝ)^s*∑ T∈(Plarge k).powersetCard j,
                        (j.factorial:ℝ)*∏ p∈T,((1 : ℝ)/ (p:ℝ)):=by
                        rw [mul_sum]
                        refine sum_congr rfl fun T _=>?_
                        rw [prod_div_distrib,prod_const_one]; ring
                  _≤ xj*(8 : ℝ)^s*Mk^j :=
                        mul_le_mul_of_nonneg_left
                          (zP (Plarge k) (h:=fun p=>(1 : ℝ)/ (p:ℝ))
                            (fun _ _=>by positivity) j) (by have:=w0; positivity)
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hT_sum (Nat.cast_nonneg _)) hZ_pos.le
        _=xj*(8 : ℝ)^s*(∑ j∈Finset.Icc 1 s,(Nat.stirlingSecond s j:ℝ)*Mk^j) *
              zY z1 N:=by
              rw [mul_sum,sum_mul]
              refine sum_congr rfl fun j _=>by ring
        _≤ xj*(8 : ℝ)^s*(∑ j∈Finset.range (s+1),(Nat.stirlingSecond s j:ℝ)*Mk^j) *
              zY z1 N:=by
              have hsub:Finset.Icc 1 s⊆Finset.range (s+1):=by
                intro j hj; simp only [mem_Icc,Finset.mem_range] at hj ⊢; omega
              have hle:=sum_le_sum_of_subset_of_nonneg hsub
                (f:=fun j=>(Nat.stirlingSecond s j:ℝ)*Mk^j) fun _ _ _=>by positivity
              have:=w0; gcongr
        _≤ xj*(8 : ℝ)^s*(Real.exp 1*((s:ℝ)+Mk))^s*zY z1 N:=by
              have hst:=yQ hMk_nn (by omega:1≤ s)
              have:=w0; gcongr
        _=(xj*(8*Real.exp 1*((s:ℝ)+Mk))^s)*zY z1 N:=by
              rw [mul_assoc xj,← mul_pow]; congr 2; ring
    have hmk:=wa (I:=Finset.Ioc N (2*N)) (ν:=zl z1 N)
      (X:=Xlarge k) (fun n _=>yw z1 N n)
      (fun n _=>sum_nonneg fun _ _=>by split_ifs <;> norm_num) hlam_pos s
    rw [sum_filter] at hmk
    refine hmk.trans ?_
    have hdiv_s:(8*Real.exp 1*((s:ℝ)+Mk))^s/ (zE*Real.log (k:ℝ))^s ≤
        Real.exp (-(s:ℝ)):=by
      rw [← div_pow]
      have hbase:(8*Real.exp 1*((s:ℝ)+Mk))/ (zE*Real.log (k:ℝ)) ≤
          Real.exp (-1):=by
        rw [div_le_iff₀ hlam_pos]
        unfold zE
        have h1:(Real.exp 1)^2*(Real.exp 1)⁻¹=Real.exp 1:=by
          rw [sq,mul_assoc,mul_inv_cancel₀ (Real.exp_pos 1).ne',mul_one]
        have h2:Real.exp (-1)*(8*(Real.exp 1)^2*(z1+yg)*Real.log (k:ℝ)) =
            8*Real.exp 1*((z1+yg)*Real.log (k:ℝ)):=by
          rw [Real.exp_neg]
          calc (Real.exp 1)⁻¹*(8*(Real.exp 1)^2*(z1+yg)*Real.log (k:ℝ))
              = 8*((Real.exp 1)^2*(Real.exp 1)⁻¹)*((z1+yg)*Real.log (k:ℝ)):=by ring
            _=8*Real.exp 1*((z1+yg)*Real.log (k:ℝ)):=by rw [h1]
        rw [h2]
        have hsum_le:(s:ℝ)+Mk≤ (z1+yg)*Real.log (k:ℝ):=by linarith
        exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
      calc
        ((8*Real.exp 1*((s:ℝ)+Mk))/ (zE*Real.log (k:ℝ)))^s
            ≤ (Real.exp (-1))^s:=pow_le_pow_left₀ (by positivity) hbase s
        _=Real.exp (-(s:ℝ)):=by rw [← Real.exp_nat_mul]; congr 1; ring
    have hC_ratio:xj/ zo≤ 1/ 4:=by
      rw [div_le_div_iff₀ wJ (by norm_num)]
      have h1:4*(xj+xr)≤ zo:=le_max_right _ _
      linarith [wv]
    calc
      (∑ n∈Finset.Ioc N (2*N),zl z1 N n*(Xlarge k n)^s) /
          (zE*Real.log (k:ℝ))^s
          ≤ ((xj*(8*Real.exp 1*((s:ℝ)+Mk))^s)*zY z1 N) /
              (zE*Real.log (k:ℝ))^s :=
            div_le_div_of_nonneg_right hmoment (by positivity)
      _=xj*((8*Real.exp 1*((s:ℝ)+Mk))^s /
            (zE*Real.log (k:ℝ))^s)*zY z1 N:=by ring
      _≤ xj*Real.exp (-(s:ℝ))*zY z1 N:=by
            have:=w0; gcongr
      _≤ xj*(1/ (zo*(k:ℝ)^2))*zY z1 N:=by
            have:=w0; gcongr
      _=((xj/ zo)/ (k:ℝ)^2)*zY z1 N:=by ring
      _≤ ((1/ 4 : ℝ)/ (k:ℝ)^2)*zY z1 N:=by gcongr
  let Bad:ℕ→ℕ→Prop:=fun k n=>BadMed k n∨BadLarge k n
  have hUnion :
      ∑ k∈Finset.Icc 2 (yI N),
        ∑ n∈Finset.Ioc N (2*N),(if Bad k n then zl z1 N n else 0) <
      ∑ n∈Finset.Ioc N (2*N),zl z1 N n:=by
    classical
    change _< zY z1 N
    have hper_k:∀ k∈Finset.Icc 2 (yI N),
        ∑ n∈Finset.Ioc N (2*N),(if Bad k n then zl z1 N n else 0) ≤
          ((1/ 2 : ℝ)*(1/ (k:ℝ)^2))*zY z1 N:=by
      intro k hk
      have hor:∑ n∈Finset.Ioc N (2*N),(if Bad k n then zl z1 N n else 0) ≤
          (∑ n∈Finset.Ioc N (2*N),(if BadMed k n then zl z1 N n else 0)) +
          (∑ n∈Finset.Ioc N (2*N),(if BadLarge k n then zl z1 N n else 0)):=by
        rw [← sum_add_distrib]
        refine sum_le_sum fun n _=>?_
        dsimp only [Bad]
        have hnn:=yw z1 N n
        (by_cases h1:BadMed k n <;> by_cases h2:BadLarge k n <;> simp [h1,h2]); linarith
      have hm:=hMed_markov k hk
      have hl:=hLarge_markov k hk
      have hsum_eq:((1/ 4 : ℝ)/ (k:ℝ)^2)*zY z1 N +
          ((1/ 4 : ℝ)/ (k:ℝ)^2)*zY z1 N =
          ((1/ 2 : ℝ)*(1/ (k:ℝ)^2))*zY z1 N:=by ring
      linarith
    calc
      ∑ k∈Finset.Icc 2 (yI N),
          ∑ n∈Finset.Ioc N (2*N),(if Bad k n then zl z1 N n else 0)
          ≤ ∑ k∈Finset.Icc 2 (yI N),((1/ 2 : ℝ)*(1/ (k:ℝ)^2))*zY z1 N :=
            sum_le_sum hper_k
      _=((1/ 2 : ℝ)*∑ k∈Finset.Icc 2 (yI N),(1 : ℝ)/ (k:ℝ)^2)*zY z1 N:=by
            rw [← sum_mul,← mul_sum]
      _≤ ((1/ 2 : ℝ)*1)*zY z1 N:=by
            have:=xc (yI N); gcongr
      _< zY z1 N:=by linarith
  have hUnion' :
      ∑ k∈Finset.Icc 2 (yI N),
        ∑ n∈(Finset.Ioc N (2*N)).filter (Bad k),zl z1 N n <
      ∑ n∈Finset.Ioc N (2*N),zl z1 N n:=by
    convert hUnion using 2 with k
    rw [sum_filter]
  obtain ⟨n,hn_mem,hnu_pos,hgood⟩:=xF
    (I:=Finset.Ioc N (2*N)) (Kset:=Finset.Icc 2 (yI N))
    (ν:=zl z1 N) (bad:=Bad)
    (fun m _=>yw z1 N m) hUnion'
  have hW_dvd_n:z4 N∣n:=xH hnu_pos
  rcases mem_Ioc.mp hn_mem with ⟨hn_gt,hn_le⟩
  refine ⟨n,hn_mem,fun k hk2 hkn=>?_⟩
  have hnk_pos:1≤ n - k:=by omega
  by_cases hkKp:k≤ yI N
  ·
    have hnotBad:¬ Bad k n:=hgood k (mem_Icc.mpr ⟨hk2,hkKp⟩)
    have hnotMed:¬ BadMed k n:=fun h=>hnotBad (Or.inl h)
    have hnotLarge:¬ BadLarge k n:=fun h=>hnotBad (Or.inr h)
    set PF:=(n - k).primeFactors
    have hcard_PF:ArithmeticFunction.cardDistinctFactors (n - k)=PF.card :=
      ArithmeticFunction.cardDistinctFactors_apply
    rw [hcard_PF]
    set S1:=PF.filter (fun p=>p≤ z7 N)
    set S2:=PF.filter (fun p=>z7 N< p∧p≤ ⌊Rk z1 N k⌋₊)
    set S3:=PF.filter (fun p=>⌊Rk z1 N k⌋₊< p∧p≤ ⌊Tk z1 N k⌋₊)
    set S4:=PF.filter (fun p=>⌊Tk z1 N k⌋₊< p)
    have hcover:PF⊆S1 ∪ S2 ∪ S3 ∪ S4:=by
      intro p hp
      simp only [S1,S2,S3,S4,mem_union,mem_filter]
      by_cases h1:p≤ z7 N
      · exact Or.inl (Or.inl (Or.inl ⟨hp,h1⟩))
      · by_cases h2:p≤ ⌊Rk z1 N k⌋₊
        · exact Or.inl (Or.inl (Or.inr ⟨hp,by omega,h2⟩))
        · by_cases h3:p≤ ⌊Tk z1 N k⌋₊
          · exact Or.inl (Or.inr ⟨hp,by omega,h3⟩)
          · exact Or.inr ⟨hp,by omega⟩
    have hcard_sum:(PF.card:ℝ)≤ (S1.card:ℝ)+(S2.card:ℝ)+(S3.card:ℝ)+(S4.card:ℝ):=by
      have hnat:PF.card≤ S1.card+S2.card+S3.card+S4.card:=by
        calc PF.card≤ (S1 ∪ S2 ∪ S3 ∪ S4).card:=card_le_card hcover
          _≤ (S1 ∪ S2 ∪ S3).card+S4.card:=card_union_le _ _
          _≤ (S1 ∪ S2).card+S3.card+S4.card:=by gcongr; exact card_union_le _ _
          _≤ S1.card+S2.card+S3.card+S4.card:=by gcongr; exact card_union_le _ _
      exact_mod_cast hnat
    have hS1:(S1.card:ℝ)≤ 2*Real.log (k:ℝ):=by
      have hsub:S1⊆k.primeFactors:=by
        intro p hp
        rcases mem_filter.mp hp with ⟨hpPF,hple⟩
        have hp_pr:p.Prime:=Nat.prime_of_mem_primeFactors hpPF
        have hp_nk:p∣n - k:=Nat.dvd_of_mem_primeFactors hpPF
        have hp_W:p∣z4 N:=hp_pr.dvd_primorial_iff.mpr hple
        have hp_n:p∣n:=hp_W.trans hW_dvd_n
        have hp_k:p∣k:=by
          have hadd:n - k+k=n:=Nat.sub_add_cancel hkn.le
          exact (Nat.dvd_add_right hp_nk).mp (hadd.symm ▸ hp_n)
        exact Nat.mem_primeFactors.mpr ⟨hp_pr,hp_k,by omega⟩
      have h1:(S1.card:ℝ)≤ (ArithmeticFunction.cardDistinctFactors k:ℝ):=by
        rw [ArithmeticFunction.cardDistinctFactors_apply]
        exact_mod_cast card_le_card hsub
      exact h1.trans (xn (by omega))
    have hS2:(S2.card:ℝ)≤ zB*Real.log (k:ℝ):=by
      by_cases hkK:k≤ z0 N
      · have hXlt:Xmed k n< zB*Real.log (k:ℝ):=by
          by_contra hge; push Not at hge; exact hnotMed ⟨hkK,hge⟩
        have hS2_eq:(S2.card:ℝ)=Xmed k n:=by
          dsimp only [Xmed,Pmed,S2,PF]
          rw [← sum_filter]
          simp only [sum_const,nsmul_eq_mul,mul_one]
          congr 2
          ext p
          simp only [z2,mem_filter,mem_Ioc,Nat.mem_primeFactors]
          constructor
          · rintro ⟨⟨hp,hpnk,_⟩,h1,h2⟩; exact ⟨⟨⟨h1,h2⟩,hp⟩,hpnk⟩
          · rintro ⟨⟨⟨h1,h2⟩,hp⟩,hpnk⟩; exact ⟨⟨hp,hpnk,by omega⟩,h1,h2⟩
        linarith
      · have hRk_eq:Rk z1 N k=yD N:=by unfold Rk; rw [if_neg (by omega)]
        have hemp:S2=∅:=by
          rw [filter_eq_empty_iff]
          intro p _; rw [hRk_eq]; unfold z7; omega
        rw [hemp,card_empty,Nat.cast_zero]
        unfold zB zg
        have hlogk:0≤ Real.log (k:ℝ):=Real.log_nonneg (by exact_mod_cast (show 1≤ k by omega))
        have:=zv; positivity
    have hS3:(S3.card:ℝ)≤ zE*Real.log (k:ℝ):=by
      have hXlt:Xlarge k n< zE*Real.log (k:ℝ):=by
        by_contra hge; push Not at hge; exact hnotLarge hge
      have hS3_eq:(S3.card:ℝ)=Xlarge k n:=by
        dsimp only [Xlarge,Plarge,S3,PF]
        rw [← sum_filter]
        simp only [sum_const,nsmul_eq_mul,mul_one]
        congr 2
        ext p
        simp only [z2,mem_filter,mem_Ioc,Nat.mem_primeFactors]
        constructor
        · rintro ⟨⟨hp,hpnk,_⟩,h1,h2⟩; exact ⟨⟨⟨h1,h2⟩,hp⟩,hpnk⟩
        · rintro ⟨⟨⟨h1,h2⟩,hp⟩,hpnk⟩; exact ⟨⟨hp,hpnk,by omega⟩,h1,h2⟩
      linarith
    have hS4:(S4.card:ℝ)≤ 20*z1*Real.log (k:ℝ):=by
      have hlogk_pos:0< Real.log (k:ℝ):=Real.log_pos (by exact_mod_cast (show 1< k by omega))
      have hTk_pos:0< Tk z1 N k:=by unfold Tk; exact Real.rpow_pos_of_pos hNpos _
      have hlogTk:Real.log (Tk z1 N k)=L/ (10*z1*Real.log (k:ℝ)):=by
        unfold Tk; rw [Real.log_rpow hNpos,one_div_mul_eq_div]
      have hprod_ge:(Tk z1 N k)^S4.card≤ (2*N:ℝ):=by
        have hsub:S4⊆PF:=filter_subset _ _
        have hprod_dvd:(∏ p∈S4,p)∣n - k :=
          (prod_dvd_prod_of_subset _ _ _ hsub).trans (Nat.prod_primeFactors_dvd (n - k))
        have hprod_le:(∏ p∈S4,p)≤ 2*N :=
          (Nat.le_of_dvd hnk_pos hprod_dvd).trans (by omega)
        have hprod_R:(∏ p∈S4,(p:ℝ))≤ (2*N:ℝ):=by
          rw [← Nat.cast_prod]; exact_mod_cast hprod_le
        calc
          (Tk z1 N k)^S4.card=∏ _p∈S4,Tk z1 N k:=(prod_const _).symm
          _≤ ∏ p∈S4,(p:ℝ):=by
                refine prod_le_prod (fun _ _=>hTk_pos.le) fun p hp=>?_
                have hgt:⌊Tk z1 N k⌋₊< p:=(mem_filter.mp hp).2
                have h1:(⌊Tk z1 N k⌋₊ : ℝ)+1≤ (p:ℝ):=by exact_mod_cast hgt
                linarith [Nat.lt_floor_add_one (Tk z1 N k)]
          _≤ (2*N:ℝ):=hprod_R
      have hlog_le:(S4.card:ℝ)*Real.log (Tk z1 N k)≤ 2*L:=by
        have h1:=Real.log_le_log (pow_pos hTk_pos _) hprod_ge
        rw [Real.log_pow,Real.log_mul (by norm_num) hNpos.ne'] at h1
        have hlog2:Real.log 2≤ 1:=by linarith [Real.log_le_sub_one_of_pos (by norm_num:(0 : ℝ)< 2)]
        linarith
      rw [hlogTk] at hlog_le
      have hden_pos:0< 10*z1*Real.log (k:ℝ):=by have:=zv; positivity
      have hmul:(S4.card:ℝ)*L≤ 2*L*(10*z1*Real.log (k:ℝ)):=by
        rw [← mul_div_assoc] at hlog_le
        exact (div_le_iff₀ hden_pos).mp hlog_le
      have hLpos:0< L:=by linarith
      nlinarith
    have hCf:2+zB+zE+20*z1≤ w7:=le_max_right _ _
    have hlogk_nn:0≤ Real.log (k:ℝ):=Real.log_nonneg (by exact_mod_cast (show 1≤ k by omega))
    nlinarith
  ·
    push Not at hkKp
    have hk_gt:(N:ℝ)^((1 : ℝ)/ 100)< (k:ℝ):=by
      have hfl:=Nat.lt_floor_add_one ((N:ℝ)^((1 : ℝ)/ 100))
      have hle:(yI N:ℝ)+1≤ (k:ℝ):=by exact_mod_cast hkKp
      unfold yI at hle
      linarith
    have hlogk_lb:L/ 100≤ Real.log (k:ℝ):=by
      have h1:=Real.log_le_log (Real.rpow_pos_of_pos hNpos _) hk_gt.le
      rw [Real.log_rpow hNpos] at h1
      linarith
    have hlog2:Real.log 2≤ 1:=by linarith [Real.log_le_sub_one_of_pos (by norm_num:(0 : ℝ)< 2)]
    have h2N:Real.log ((n - k:ℕ):ℝ)≤ 2*L:=by
      have hle:((n - k:ℕ):ℝ)≤ 2*(N:ℝ):=by exact_mod_cast (show n - k≤ 2*N by omega)
      calc Real.log ((n - k:ℕ):ℝ)≤ Real.log (2*(N:ℝ)):=Real.log_le_log (by positivity) hle
        _=Real.log 2+L:=Real.log_mul (by norm_num) hNpos.ne'
        _≤ 2*L:=by linarith
    have hom:=xn hnk_pos
    have h400:400≤ w7:=le_max_left _ _
    have hlogk_nn:0≤ Real.log (k:ℝ):=Real.log_nonneg (by exact_mod_cast (show 1≤ k by omega))
    nlinarith
theorem erdos_413_H1 :
    ∃ C:ℝ,0< C∧∃ S:Set ℕ,S.Infinite ∧
      ∀ n∈S,∀ k:ℕ,2≤ k→k< n →
        ((ArithmeticFunction.cardDistinctFactors (n - k):ℕ):ℝ)≤ C*Real.log (k:ℝ):=by
  let S:Set ℕ:={n:ℕ | ∀ k:ℕ,2≤ k→k< n →
    ((ArithmeticFunction.cardDistinctFactors (n - k):ℕ):ℝ)≤ w7*Real.log (k:ℝ)}
  refine ⟨w7,wV,S,?_,fun n hn=>hn⟩
  rw [Set.infinite_iff_exists_gt]
  intro M
  obtain ⟨N₀,hN₀⟩:=Filter.eventually_atTop.mp xR
  obtain ⟨n,hn_mem,hn_good⟩:=hN₀ (max M N₀) (le_max_right _ _)
  have hn_gt:M< n:=lt_of_le_of_lt (le_max_left _ _) (mem_Ioc.mp hn_mem).1
  exact ⟨n,hn_good,hn_gt⟩
end
end Erdos413Main

theorem OMA.solution : OMA.R_Erdos413_erdos_413_parts_ii_R1.H1 :=
  Erdos413Main.erdos_413_H1
