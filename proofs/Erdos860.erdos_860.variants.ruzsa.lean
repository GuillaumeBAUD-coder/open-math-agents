import FormalConjectures.ErdosProblems.«860»
/-! Digit cancellation for distinct multiples of primes in long intervals. -/
open Finset Filter Erdos860
namespace PrimeGrid

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

def digit (q p i : ℕ) := (p / q^i) % q
def term (q p i : ℕ) := digit q p i * q^i

lemma expansion (q p d : ℕ) :
    (∑ i : Fin d,term q p i.val) + p/q^d*q^d = p := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    have hh := congrArg (fun x : ℕ => x*q^d) (Nat.mod_add_div (p/q^d) q)
    simp only [Nat.add_mul] at hh
    dsimp only [term,digit]
    rw [pow_succ,← Nat.div_div_eq_div_mul]
    dsimp only [term,digit] at ih
    nlinarith only [hh,ih]

def band (x : ℕ) := (Ioc x (16*x)).filter Nat.Prime

lemma theta_gap : ∀ᶠ x : ℕ in atTop, (x:ℝ) ≤ Chebyshev.theta (16*x) - Chebyshev.theta x := by
  have hlim : Tendsto (fun x : ℕ => (16:ℝ)*x) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hlog := (isLittleO_log_rpow_atTop (r := 1/2) (by norm_num)).bound (c := (1:ℝ)/16) (by norm_num)
  have hlog' := Real.isLittleO_log_id_atTop.bound (c := (1:ℝ)/16) (by norm_num)
  filter_upwards [hlim.eventually hlog,(Filter.Tendsto.atTop_add hlim tendsto_const_nhds).eventually hlog',
    eventually_ge_atTop 1] with x hs hl hx
  have hn : (1:ℝ) ≤ x := by exact_mod_cast hx
  change ‖Real.log (16*(x:ℝ))‖ ≤ 1/16 * ‖(16*(x:ℝ))^(1/2:ℝ)‖ at hs
  change ‖Real.log (16*(x:ℝ)+1)‖ ≤ 1/16 * ‖16*(x:ℝ)+1‖ at hl
  rw [← Real.sqrt_eq_rpow,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] at hs
  have hs' := (le_abs_self (Real.log (16*x))).trans hs
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ 16*(x:ℝ)+1)] at hl
  have hl'' := (le_abs_self _).trans hl
  have hg := Chebyshev.theta_ge (16*x)
  push_cast at hg
  have hu := Chebyshev.theta_le_log4_mul_x (x := x) (by positivity)
  have ha := mul_le_mul_of_nonneg_left hs' (Real.sqrt_nonneg (16*x))
  have hr := Real.sq_sqrt (by positivity : (0:ℝ) ≤ 16*x)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by rw [show (4:ℝ) = (2:ℝ)^2 by norm_num,Real.log_pow]; norm_num
  rw [hlog4] at hu
  nlinarith only [hg,hu,ha,hr,hl'',mul_le_mul_of_nonneg_right (le_of_lt Real.log_two_gt_d9)
    (show (0:ℝ) ≤ x by positivity),hn]

lemma plentiful (D H C : ℕ) (hH : 0 < H) :
    ∀ᶠ q : ℕ in atTop, C*q^D < (band (H*q^(D+1))).card := by
  let X := fun q : ℕ => H*q^(D+1)
  have hX : Tendsto X atTop atTop := by
    apply tendsto_atTop_mono (f := id) _ tendsto_id
    intro q
    exact (Nat.le_self_pow (by omega : D+1 ≠ 0) q).trans (Nat.le_mul_of_pos_left _ hH)
  have hlog := Real.isLittleO_log_id_atTop.bound (c := 1/(2*((C:ℝ)+1)*(D+1))) (by positivity)
  filter_upwards [hX.eventually theta_gap,tendsto_natCast_atTop_atTop.eventually hlog,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2*(C+1)*Real.log (16*H)+1),
    eventually_ge_atTop 1] with q hg hl hq hq1
  have hq' : 0 < (q:ℝ) := by positivity
  have hx : 0 < X q := by dsimp [X]; positivity
  have heq : Chebyshev.theta (16*(X q)) - Chebyshev.theta (X q) =
      ∑ p ∈ band (X q),Real.log p := by
    rw [show (16*(X q):ℝ) = ((16*X q : ℕ):ℝ) by push_cast; rfl,sub_eq_iff_eq_add']
    simpa [Chebyshev.theta,band,sum_filter,← Nat.cast_mul] using
      (sum_Ioc_consecutive (fun p : ℕ => if p.Prime then Real.log p else 0)
        (show 0 ≤ X q by omega) (show X q ≤ 16*X q by omega)).symm
  rw [heq] at hg
  have hc : (X q : ℝ) ≤ (band (X q)).card * Real.log (16*X q) := by
    apply hg.trans
    calc
      _ ≤ ∑ _p ∈ band (X q),Real.log (16*X q) := by
        apply sum_le_sum; intro p hp
        exact Real.log_le_log (by exact_mod_cast (mem_filter.mp hp).2.pos)
          (by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hp).1).2)
      _ = _ := by simp
  have hlq := (le_abs_self (Real.log q)).trans hl
  simp only [id_eq,Real.norm_eq_abs,abs_of_nonneg hq'.le] at hlq
  have hlogX : Real.log (16*(X q:ℝ)) = Real.log (16*(H:ℝ))+(D+1)*Real.log q := by
    dsimp [X]; push_cast; rw [←mul_assoc,Real.log_mul (by positivity) (by positivity),Real.log_pow]; push_cast; ring
  have hq2 : (0:ℝ) < 2*((C:ℝ)+1)*(D+1) := by positivity
  have hlogq : 2*((C:ℝ)+1)*(D+1)*Real.log q ≤ q := by
    field_simp at hlq
    nlinarith only [hlq]
  have hres : (C:ℝ)*Real.log (16*(X q:ℝ)) < q := by
    rw [hlogX]
    nlinarith only [hq,hlogq,Real.log_nonneg (show 1 ≤ 16*(H:ℝ) by exact_mod_cast (show 1 ≤ 16*H by omega)),
      mul_nonneg (show (0:ℝ) ≤ D by positivity) (Real.log_nonneg (by exact_mod_cast hq1 : (1:ℝ) ≤ q)),
      Real.log_nonneg (by exact_mod_cast hq1 : (1:ℝ) ≤ q),hq']
  by_contra! hh
  have hcast : ((band (X q)).card:ℝ) ≤ (C:ℝ)*q^D := by exact_mod_cast hh
  have hc' := hc.trans (mul_le_mul_of_nonneg_right hcast (Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ 16*X q by omega))))
  have ha := mul_lt_mul_of_pos_right hres (pow_pos hq' D)
  have hXeq : (X q:ℝ) = H*((q:ℝ)^D*q) := by dsimp [X]; push_cast; rw [pow_succ]
  nth_rw 1 [hXeq] at hc'
  have HH : (1:ℝ) ≤ H := by exact_mod_cast hH
  nlinarith only [hc',ha,mul_le_mul_of_nonneg_right HH (show (0:ℝ) ≤ (q:ℝ)^D*q by positivity)]

def weight (q p D : ℕ) := ∑ i : Fin (D+1),i.val * term q p i.val

lemma weight_bound (q p D : ℕ) (hq : 0 < q) : weight q p D ≤ (D+1)*q^(D+1) := by
  have he := expansion q p (D+1)
  have hh := Nat.mod_add_div p (q^(D+1))
  rw [Nat.mul_comm (q^(D+1))] at hh
  have hs : (∑ i : Fin (D+1),term q p i.val) ≤ q^(D+1) := by
    have := Nat.mod_lt p (pow_pos hq (D+1)); omega
  apply le_trans _ (Nat.mul_le_mul_left (D+1) hs)
  rw [Finset.mul_sum]
  exact sum_le_sum fun i _ => Nat.mul_le_mul_right _ i.isLt.le

/-- The weighted digit sum cancels the j-th digit in the j-th available multiple. -/
lemma cancellation (q D : ℕ) (j : Fin (D+1)) (p r : ℕ)
    (ht : p / q^(D+1) = r / q^(D+1))
    (hd : ∀ i : Fin (D+1), i ≠ j → digit q p i = digit q r i) :
    j.val*p + weight q r D = j.val*r + weight q p D := by
  have he : ∀ u, j.val*u = (∑ i : Fin (D+1),j.val*term q u i.val) + j.val*(u/q^(D+1)*q^(D+1)) := by
    intro u
    rw [← Finset.mul_sum,← Nat.mul_add,expansion]
  rw [he p,he r,ht]
  dsimp only [weight]
  have hs : (∑ i : Fin (D+1), (j.val*term q p i.val + i.val*term q r i.val)) =
      ∑ i : Fin (D+1), (j.val*term q r i.val + i.val*term q p i.val) := by
    apply sum_congr rfl
    intro i _
    by_cases hi : i = j
    · subst i; omega
    · simp only [term,hd i hi]
  simp only [sum_add_distrib] at hs
  omega

lemma obstruct (q D n : ℕ) (hq : 0 < q)
    (hn : 16*((D+1)*q^(D+1)) ≤ n)
    (hmany : (D+1)*(16*(D+1)+1)*q^D < (band ((D+1)*q^(D+1))).card) :
    D*((D+1)*q^(D+1)) ≤ h n := by
  classical
  let X := (D+1)*q^(D+1)
  let A := band X
  let first := fun p => X-weight q p D
  have hX : 0 < X := by dsimp [X]; positivity
  have props {p : ℕ} (hp : p ∈ A) : p.Prime ∧ X < p ∧ p ≤ 16*X := by
    obtain ⟨hh,pr⟩ := mem_filter.mp hp
    exact ⟨pr,mem_Ioc.mp hh⟩
  have fst_le {p} (hp : p ∈ A) : first p ≤ p := (Nat.sub_le ..).trans (props hp).2.1.le
  let prodP := ∏ p ∈ A,p
  have hprod : 0 < prodP := prod_pos (fun p hp => (props hp).1.pos)
  let crt := Nat.chineseRemainderOfFinset (fun p => p-first p) id A (fun p hp => (props hp).1.ne_zero)
    (fun p hp r hr hn => (Nat.coprime_primes (props hp).1 (props hr).1).mpr hn)
  let m := crt.val+prodP
  have modm {p} (hp : p ∈ A) : p ∣ m+first p := by
    have hh := (crt.property p hp).add (dvd_prod_of_mem id hp).modEq_zero_nat
    change crt.val+prodP ≡ (p-first p)+0 [MOD p] at hh
    have eq := hh.add_right (first p)
    rw [Nat.add_zero,Nat.sub_add_cancel (fst_le hp)] at eq
    exact Nat.modEq_zero_iff_dvd.mp (eq.trans (dvd_refl p).modEq_zero_nat)
  by_contra! hsmall
  change h n < D*X at hsmall
  obtain ⟨a,inj,ha⟩ := h_spec n m (by dsimp [m]; omega)
  let idx := fun p : A => (⟨Nat.count Nat.Prime p.val, (Nat.count_lt_count_succ_iff.mpr
    (props p.property).1).trans_le (Nat.count_monotone Nat.Prime (by
      have := (props p.property).2.2.trans hn; omega : p.val+1 ≤ n+1))⟩ : Fin n.primeCounting)
  let z := fun p : A => a (idx p)-m
  have hinj : Function.Injective z := by
    intro p r heq
    have h1 := (ha (idx p)).1
    have h2 := (ha (idx r)).1
    have hh : a (idx p)=a (idx r) := by dsimp [z] at heq; omega
    have hh' := congrArg (fun i : Fin n.primeCounting => Nat.nth Nat.Prime i.val) (inj hh)
    exact Subtype.ext (by simpa [idx,Nat.nth_count (props p.property).1,Nat.nth_count (props r.property).1] using hh')
  have exists_index (v : A) : ∃ j : Fin (D+1), z v = first v + j.val*v.val := by
    let p := v.val
    have hp : p ∈ A := v.property
    obtain ⟨hl,hu,hd⟩ := ha (idx v)
    have hprime : Nat.nth Nat.Prime (idx v).val = p := Nat.nth_count (props hp).1
    rw [hprime] at hd
    have hz : z v + m = a (idx v) := Nat.sub_add_cancel hl.le
    have hmod : z v ≡ first p [MOD p] := by
      exact Nat.ModEq.add_left_cancel (Nat.ModEq.refl m)
        (by simpa [Nat.add_comm m (z v),hz] using hd.modEq_zero_nat.trans (modm hp).zero_modEq_nat)
    have hf : first p ≤ z v := by
      by_contra! hh
      have hh' := Nat.le_of_dvd (by omega : 0 < first p - z v) ((Nat.modEq_iff_dvd' hh.le).mp hmod)
      have := fst_le hp
      omega
    obtain ⟨j,hj⟩ := (Nat.modEq_iff_dvd' hf).mp hmod.symm
    rw [Nat.mul_comm] at hj
    refine ⟨⟨j,?_⟩,by change z v = first p+j*p; omega⟩
    by_contra! hh
    have := Nat.mul_le_mul (by omega : D ≤ j) (props hp).2.1.le
    omega
  choose j hj using exists_index
  let top := fun p : A => (⟨p.val/q^(D+1),by
    apply (Nat.div_lt_iff_lt_mul (pow_pos hq (D+1))).mpr
    have := (props p.property).2.2
    dsimp [X] at this
    rw [Nat.add_mul,one_mul,Nat.mul_assoc]
    have := pow_pos hq (D+1); omega⟩ : Fin (16*(D+1)+1))
  let dig := fun (p : A) (i : Fin D) =>
    (⟨digit q p ((j p).succAbove i),Nat.mod_lt _ hq⟩ : Fin q)
  let code := fun p : A => (j p,top p,dig p)
  have hc : Function.Injective code := by
    intro p r hpr
    obtain ⟨hj',ht,hd⟩ : j p=j r ∧ top p=top r ∧ dig p=dig r := by simpa [code] using hpr
    apply hinj
    have hc := cancellation q D (j p) p.val r.val (congrArg Fin.val ht) (by
      intro i hi
      obtain ⟨l,rfl⟩ := Fin.exists_succAbove_eq hi
      have hh := congrArg Fin.val (congrFun hd l)
      simpa [dig,← hj'] using hh)
    have hp := Nat.sub_add_cancel (weight_bound q p D hq)
    have hr := Nat.sub_add_cancel (weight_bound q r D hq)
    have ep := hj p
    have er := hj r
    rw [← hj'] at er
    dsimp only [first,X] at ep er
    omega
  have H := Fintype.card_le_of_injective code hc
  simp only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fin,Fintype.card_fun] at H
  change (D+1)*(16*(D+1)+1)*q^D < A.card at hmany
  rw [Nat.mul_assoc] at hmany
  omega

lemma step_bound (d : ℕ) : ∀ᶠ q : ℕ in atTop, (q+1)^d ≤ 2*q^d := by
  have ht : Tendsto (fun q : ℕ => ((1:ℝ)+1/(q:ℝ))^d) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ)) |>.add tendsto_one_div_atTop_nhds_zero_nat).pow d
  filter_upwards [ht.eventually_le_const (show (1:ℝ) < 2 by norm_num),eventually_ge_atTop 1] with q hq hpos
  have he := mul_le_mul_of_nonneg_right hq (show (0:ℝ) ≤ (q:ℝ)^d by positivity)
  rw [← mul_pow] at he
  have hh : (1+1/(q:ℝ))*q=q+1 := by field_simp
  rw [hh] at he
  exact_mod_cast he

lemma eventually_mul (c : ℕ) : ∀ᶠ n : ℕ in atTop, c*n ≤ h n := by
  let D := 32*c
  let f := fun q : ℕ => 16*((D+1)*q^(D+1))
  have mono : Monotone f := by intro a b hab; dsimp only [f]; gcongr
  have hp := plentiful D (D+1) ((D+1)*(16*(D+1)+1)) (by omega)
  obtain ⟨Q,hQ⟩ := eventually_atTop.mp (hp.and ((step_bound (D+1)).and (eventually_ge_atTop 1)))
  filter_upwards [eventually_ge_atTop (f Q)] with n hn
  have hex : ∃ q, n < f q := by
    refine ⟨n+1,?_⟩
    have hpow := Nat.le_self_pow (by omega : D+1≠0) (n+1)
    have hlt := Nat.le_mul_of_pos_left ((n+1)^(D+1)) (by omega : 0<D+1)
    dsimp [f]; omega
  have hz : Nat.find hex ≠ 0 := by
    intro he
    have hn' := Nat.find_spec hex
    rw [he] at hn'
    exact (not_lt_of_ge (le_trans (mono (Nat.zero_le Q)) hn)) hn'
  obtain ⟨q,hq⟩ := Nat.exists_eq_succ_of_ne_zero hz
  have hlo : f q ≤ n := le_of_not_gt (Nat.find_min hex (by omega : q < Nat.find hex))
  have hhi := Nat.find_spec hex
  rw [hq] at hhi
  have hqQ : Q ≤ q := by
    by_contra! hh
    exact (not_lt_of_ge (le_trans (mono hh) hn)) hhi
  obtain ⟨hm,hs,hq1⟩ := hQ q hqQ
  have ho := obstruct q D n hq1 hlo hm
  apply le_trans _ ho
  have HH := Nat.mul_le_mul_left (16*(D+1)) hs
  dsimp only [f] at hhi
  rw [← Nat.mul_assoc] at hhi
  have hnn : n ≤ 32*((D+1)*q^(D+1)) := by nlinarith only [hhi,HH]
  simpa [D,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_left c hnn

end PrimeGrid

theorem OMA.solution : type_of% @Erdos860.erdos_860.variants.ruzsa := by
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨c,hc⟩ := exists_nat_gt b
  filter_upwards [PrimeGrid.eventually_mul c,eventually_ge_atTop 1] with n hn hn1
  apply hc.le.trans
  apply (le_div_iff₀ (by positivity)).mpr
  exact_mod_cast hn
