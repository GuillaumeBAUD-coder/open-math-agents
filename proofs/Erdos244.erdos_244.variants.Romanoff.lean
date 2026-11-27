import FormalConjectures.ErdosProblems.«244»
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Chebyshev

/-! Positive lower density of sums of a prime and a power.

A two-residue sieve bounds collisions between two representations. The reciprocal
divisor weight of the difference of two powers is controlled by grouping its
divisors according to the multiplicative order of the base. Counting prime–power
pairs on geometric scales gives a uniform lower density bound. -/

noncomputable section
open Finset Filter Asymptotics
namespace PairWindows

private def bad (t p : ℕ) : Finset ℕ := {0, (p-t%p)%p}
private def rho (t p : ℕ) := (bad t p).card
private def mult (t d : ℕ) := ∏ p ∈ d.primeFactors, rho t p
private def localVal (t p r : ℕ) : ℝ := (rho t p:ℝ)/p - (if r ∈ bad t p then 1 else 0)
private def K (t d n : ℕ) : ℝ := ∏ p ∈ d.primeFactors, localVal t p (n%p)

private theorem bad_subset (t : ℕ) {p : ℕ} (hp : 0 < p) : bad t p ⊆ range p := by
  intro r hr
  rcases Finset.mem_insert.mp hr with h|h
  · simpa [h] using hp
  · exact Finset.mem_range.mpr ((Finset.mem_singleton.mp h).trans_lt (Nat.mod_lt _ hp))

private theorem val_bound (t : ℕ) {p : ℕ} (hp : p.Prime) (r : ℕ) : |localVal t p r| ≤ 1 := by
  have h : (rho t p:ℝ)/(p:ℝ) ≤ 1 := (div_le_one (by exact_mod_cast hp.pos)).2 (by
    exact_mod_cast (Finset.card_le_card (bad_subset t hp.pos)).trans_eq (Finset.card_range p))
  unfold localVal
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith [show (0:ℝ) ≤ (rho t p:ℝ)/p by positivity]

private theorem K_bound (t d n : ℕ) : |K t d n| ≤ 1 := by
  rw [K,Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun p hp => val_bound t (Nat.prime_of_mem_primeFactors hp) _)

private theorem K_prime (t : ℕ) {d n : ℕ} (hd : Squarefree d) (hn : n.Prime)
    (hnt : (n+t).Prime) (hlt : d < n) : K t d n = (mult t d:ℝ)/(d:ℝ) := by
  have no (p : ℕ) (hp : p ∈ d.primeFactors) : n%p ∉ bad t p := by
    have pp := Nat.prime_of_mem_primeFactors hp
    have pl := (Nat.le_of_dvd (Nat.pos_of_ne_zero hd.ne_zero) (Nat.dvd_of_mem_primeFactors hp)).trans_lt hlt
    intro h
    rcases Finset.mem_insert.mp h with zero|other
    · have e := (Nat.prime_dvd_prime_iff_eq pp hn).mp (Nat.dvd_of_mod_eq_zero zero)
      omega
    · have e := Finset.mem_singleton.mp other
      have dvd : p ∣ n+t := by
        apply Nat.dvd_of_mod_eq_zero
        rw [Nat.add_mod,e]
        by_cases ht : t%p=0
        · simp [ht]
        · have r := Nat.mod_lt t pp.pos
          rw [Nat.mod_eq_of_lt (show p-t%p < p by omega),Nat.sub_add_cancel r.le,Nat.mod_self]
      have eq := (Nat.prime_dvd_prime_iff_eq pp hnt).mp dvd
      omega
  unfold K mult
  push_cast
  calc
    _ = ∏ p ∈ d.primeFactors, ((rho t p:ℝ)/p) := by
      apply Finset.prod_congr rfl
      intro p hp
      simp [localVal,no p hp]
    _ = _ := by
      rw [Finset.prod_div_distrib]
      congr 1
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd]

private theorem crt_sum (P : Finset ℕ) (hp : ∀ p ∈ P, p.Prime) (start : ℕ)
    (g : ℕ → ℕ → ℝ) :
    ∑ i ∈ Finset.range (∏ p ∈ P, p), ∏ p ∈ P, g p ((start+i)%p) =
    ∏ p ∈ P, ∑ j ∈ Finset.range p, g p j := by
  classical
  let a (p : P) := p.val
  have hne (p : P) : a p ≠ 0 := (hp _ p.prop).ne_zero
  let (p : P) : NeZero (a p) := ⟨hne p⟩
  let m := ∏ p : P, a p
  have : NeZero m := ⟨Finset.prod_ne_zero_iff.mpr (fun p _ => hne p)⟩
  let e := ZMod.prodEquivPi a (fun i j hij => (Nat.coprime_primes (hp _ i.prop) (hp _ j.prop)).mpr
    (fun eq => hij (Subtype.ext eq)))
  let shift := Equiv.addLeft (start : ZMod m)
  let F (v : (p : P) → ZMod (a p)) := ∏ p, g p.val (v p).val
  have aux (q : ℕ) [NeZero q] (i : Fin q) : ZMod.finEquiv q i = (i.val : ZMod q) := by
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q => apply Fin.ext; exact (Nat.mod_eq_of_lt i.isLt).symm
  have eqg (i : Fin m) : F (e (shift (ZMod.finEquiv m i))) = ∏ p ∈ P, g p ((start+i.val)%p) := by
    change (∏ p : P, g p.val ((e ((start:ZMod m)+ZMod.finEquiv m i)) p).val) = _
    rw [aux, ← Nat.cast_add]
    rw [map_natCast]
    change (∏ p : P, g p.val (((start+i.val:ℕ) : ZMod (a p)).val)) = _
    simp only [ZMod.val_natCast]
    exact Finset.prod_coe_sort P (fun p => g p ((start+i.val)%p))
  have hm : m = ∏ p ∈ P, p := Finset.prod_coe_sort P id
  rw [← hm,← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ i : Fin m, F (e (shift (ZMod.finEquiv m i))) := Finset.sum_congr rfl (fun i _ => (eqg i).symm)
    _ = ∑ v, F v := Equiv.sum_comp (((ZMod.finEquiv m).toEquiv.trans shift).trans e.toEquiv) F
    _ = ∏ p : P, ∑ j : ZMod (a p), g p.val j.val := (Fintype.prod_sum (fun (p : P) (j : ZMod (a p)) => g p.val j.val)).symm
    _ = ∏ p : P, ∑ j ∈ Finset.range p.val, g p.val j := by
      apply Finset.prod_congr rfl
      intro p _
      rw [← Fin.sum_univ_eq_sum_range]
      symm
      calc
        _ = ∑ i : Fin (a p), g p.val (ZMod.finEquiv (a p) i).val := by
          apply Finset.sum_congr rfl
          intro i _
          rw [aux,ZMod.val_natCast,Nat.mod_eq_of_lt i.isLt]
        _ = _ := Equiv.sum_comp (ZMod.finEquiv (a p)).toEquiv (fun j => g p.val j.val)
    _ = _ := Finset.prod_coe_sort P (fun p => ∑ j ∈ Finset.range p, g p j)

private def cell (t d p r : ℕ) : ℝ := if p ∈ d.primeFactors then localVal t p r else 1

private theorem K_extend (t : ℕ) {d : ℕ} {P : Finset ℕ} (h : d.primeFactors ⊆ P) (n : ℕ) :
    K t d n = ∏ p ∈ P, cell t d p (n%p) := by
  calc
    _ = ∏ p ∈ d.primeFactors, cell t d p (n%p) := by
      apply Finset.prod_congr rfl
      intro p hp
      simp [cell,hp]
    _ = _ := Finset.prod_subset h (by intro p _ hp; simp [cell,hp])

private theorem indicators (t : ℕ) {p : ℕ} (hp : 0 < p) (x : ℝ) :
    (∑ r ∈ range p, if r ∈ bad t p then x else 0) = (rho t p:ℝ)*x := by
  rw [← Finset.sum_filter]
  have eq : (range p).filter (· ∈ bad t p) = bad t p := by
    ext r
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun h => bad_subset t hp h)
  simp [eq,rho]

private theorem local_zero (t : ℕ) {p : ℕ} (hp : 0 < p) :
    ∑ r ∈ range p, localVal t p r = 0 := by
  simp only [localVal,Finset.sum_sub_distrib,indicators t hp,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have h : (0:ℝ)<p := by exact_mod_cast hp
  field_simp
  ring

private theorem local_sq (t : ℕ) {p : ℕ} (hp : 0 < p) :
    ∑ r ∈ range p, localVal t p r * localVal t p r ≤ (rho t p:ℝ) := by
  let a := (rho t p:ℝ)/p
  have e (r : ℕ) : localVal t p r * localVal t p r =
      a^2 + (if r ∈ bad t p then 1-2*a else 0) := by
    unfold localVal; dsimp [a]; split_ifs <;> ring
  simp_rw [e]
  rw [Finset.sum_add_distrib,indicators t hp]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  dsimp [a]
  have h : (0:ℝ)<p := by exact_mod_cast hp
  field_simp
  nlinarith [sq_nonneg (rho t p:ℝ),mul_nonneg h.le (sq_nonneg (rho t p:ℝ))]

private def period (d e : ℕ) := ∏ p ∈ d.primeFactors ∪ e.primeFactors, p

private theorem period_property {d e : ℕ} (hd : Squarefree d) (he : Squarefree e) :
    0 < period d e ∧ period d e ≤ d*e := by
  let P := d.primeFactors ∪ e.primeFactors
  have pp (p) (hp : p ∈ P) : p.Prime :=
    (Finset.mem_union.mp hp).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors
  have h1 : 0 < period d e := Finset.prod_pos (fun p hp => (pp p hp).pos)
  have h2 : 0 < ∏ p ∈ d.primeFactors ∩ e.primeFactors, p :=
    Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hp).1).pos)
  refine ⟨h1, ?_⟩
  calc
    _ ≤ period d e * (∏ p ∈ d.primeFactors ∩ e.primeFactors, p) := Nat.le_mul_of_pos_right _ h2
    _ = d*e := by rw [period,Finset.prod_union_inter,Nat.prod_primeFactors_of_squarefree hd,Nat.prod_primeFactors_of_squarefree he]

private theorem block (t : ℕ) {d e : ℕ} (hd : Squarefree d) (he : Squarefree e) (start : ℕ) :
    ∑ i ∈ range (period d e), K t d (start+i)*K t e (start+i) ≤
      if d=e then (mult t d:ℝ) else 0 := by
  let P := d.primeFactors ∪ e.primeFactors
  have pp (p) (hp : p ∈ P) : p.Prime :=
    (Finset.mem_union.mp hp).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors
  let g (p r : ℕ) := cell t d p r * cell t e p r
  have ec (n : ℕ) : K t d n*K t e n = ∏ p ∈ P, g p (n%p) := by
    rw [K_extend t (P := P) Finset.subset_union_left, K_extend t (d := e) (P := P) Finset.subset_union_right,
      ← Finset.prod_mul_distrib]
  simp_rw [ec]
  change ∑ i ∈ range (∏ p ∈ P, p), _ ≤ _
  rw [crt_sum P pp start g]
  by_cases eq : d=e
  · subst e
    rw [if_pos rfl]
    change _ ≤ ((∏ p ∈ d.primeFactors, rho t p : ℕ):ℝ)
    push_cast
    dsimp [P]
    rw [Finset.union_idempotent]
    apply Finset.prod_le_prod
    · intro p _
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    · intro p hp
      simpa only [g,cell,if_pos hp] using local_sq t (Nat.prime_of_mem_primeFactors hp).pos
  · rw [if_neg eq]
    apply le_of_eq
    apply Finset.prod_eq_zero_iff.mpr
    have neq : d.primeFactors ≠ e.primeFactors := by
      intro hp
      have := congrArg (fun x : Finset ℕ => ∏ p ∈ x, p) hp
      simp [Nat.prod_primeFactors_of_squarefree hd,Nat.prod_primeFactors_of_squarefree he] at this
      contradiction
    obtain ⟨p,hp⟩ := Finset.ext_iff.not.mp neq |> Classical.not_forall.mp
    by_cases hpd : p ∈ d.primeFactors
    · have hpe : p ∉ e.primeFactors := by tauto
      have hm : p ∈ P := Finset.mem_union_left _ hpd
      exact ⟨p,hm,by simpa only [g,cell,if_pos hpd,if_neg hpe,mul_one] using local_zero t (pp p hm).pos⟩
    · have hpe : p ∈ e.primeFactors := by tauto
      have hm : p ∈ P := Finset.mem_union_right _ hpe
      exact ⟨p,hm,by simpa only [g,cell,if_neg hpd,if_pos hpe,one_mul] using local_zero t (pp p hm).pos⟩
private theorem interval_corr (t : ℕ) {d e : ℕ} (hd : Squarefree d) (he : Squarefree e) (start h : ℕ) :
    ∑ i ∈ range h, K t d (start+i)*K t e (start+i) ≤
      (if d=e then (h:ℝ)*mult t d/d else 0) + d*e := by
  let m := period d e
  have hm := (period_property hd he).1
  have hm0 : 0 < m := hm
  have hblocks (b : ℕ) :
      ∑ i ∈ range (b*m), K t d (start+i)*K t e (start+i) ≤ (b:ℝ)*(if d=e then (mult t d:ℝ) else 0) := by
    induction b with
    | zero => simp
    | succ b ih =>
      rw [Nat.succ_mul,Finset.sum_range_add,Nat.cast_succ,add_mul,one_mul]
      apply add_le_add ih
      simpa [Nat.add_assoc] using block t hd he (start+b*m)
  have hrest (b r : ℕ) : ∑ i ∈ range r, K t d (start+(b+i))*K t e (start+(b+i)) ≤ r := by
    calc
      _ ≤ ∑ i ∈ range r, (1:ℝ) := Finset.sum_le_sum fun i _ =>
        (le_abs_self _).trans (by rw [abs_mul]; exact
          (mul_le_mul (K_bound t d _) (K_bound t e _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
      _ = _ := by simp
  have hx : h/m*m+h%m = h := Nat.div_add_mod' h m
  conv_lhs => rw [← hx,Finset.sum_range_add]
  have H := add_le_add (hblocks (h/m)) (hrest (h/m*m) (h%m))
  apply H.trans
  have hr : ((h%m:ℕ):ℝ) ≤ (d:ℝ)*e := by
    exact_mod_cast (Nat.mod_lt h hm0).le.trans (period_property hd he).2
  apply add_le_add _ hr
  by_cases eq : d=e
  · subst e
    have hdm : m=d := by simp [m,period,Nat.prod_primeFactors_of_squarefree hd]
    simp only [if_true,hdm]
    rw [le_div_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hd.ne_zero : (0:ℝ) < d)]
    have hd' : ((h/d:ℕ):ℝ)*d ≤ h := by exact_mod_cast Nat.div_mul_le_self h d
    nlinarith [mul_le_mul_of_nonneg_right hd' (Nat.cast_nonneg (mult t d) : (0:ℝ) ≤ _)]
  · simp [eq]

private def divisorsTo (Q : ℕ) : Finset ℕ := (Icc 1 Q).filter Squarefree
private def mass (t Q : ℕ) : ℝ := ∑ d ∈ divisorsTo Q, (mult t d:ℝ)/(d:ℝ)
private def kernel (t Q n : ℕ) : ℝ := ∑ d ∈ divisorsTo Q, K t d n

private theorem energy (t start h Q : ℕ) :
    ∑ i ∈ range h, kernel t Q (start+i)^2 ≤ h*mass t Q + (Q:ℝ)^4 := by
  let D := divisorsTo Q
  have hd (d : ℕ) (h : d ∈ D) : d ≤ Q ∧ Squarefree d := by
    obtain ⟨h,h'⟩ := Finset.mem_filter.mp h
    exact ⟨(Finset.mem_Icc.mp h).2,h'⟩
  have hcard : D.card ≤ Q := (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
    (show (Icc 1 Q).card = Q by simp)
  have hsum (i : ℕ) : kernel t Q (start+i)^2 =
      ∑ d ∈ D, ∑ e ∈ D, K t d (start+i)*K t e (start+i) := by
    simp [kernel,D,pow_two,Finset.mul_sum,mul_comm]
  simp_rw [hsum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ d ∈ D, ∑ e ∈ D, ((if d=e then (h:ℝ)*mult t d/d else 0)+(Q:ℝ)^2) := by
      apply Finset.sum_le_sum
      intro d hD
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro e hE
      apply (interval_corr t (hd d hD).2 (hd e hE).2 start h).trans
      apply add_le_add le_rfl
      exact_mod_cast (Nat.mul_le_mul (hd d hD).1 (hd e hE).1).trans_eq (pow_two Q).symm
    _ = h * mass t Q + (D.card:ℝ)^2*Q^2 := by
      simp [Finset.sum_add_distrib, mass,← Finset.mul_sum,div_eq_mul_inv,D,mul_assoc,pow_two]
    _ ≤ _ := by
      apply add_le_add le_rfl
      calc
        _ ≤ (Q:ℝ)^2*Q^2 := by gcongr
        _ = _ := by ring

private def sfMass (Q : ℕ) : ℝ := ∑ d ∈ divisorsTo Q, 1/(d:ℝ)
private def zetaTwo : ℝ := ∑' n : ℕ, 1/(n:ℝ)^2

private theorem size_mass (Q : ℕ) : Real.log (Q+1 : ℕ) ≤ zetaTwo*sfMass Q := by
  classical
  let I := Finset.Icc 1 Q
  let D := divisorsTo Q
  choose a b eqn sf using Nat.sq_mul_squarefree
  let pair (n : ℕ) := (b n,a n)
  have hinj : Function.Injective pair := by
    intro n m h
    have eb : b n = b m := congrArg Prod.fst h
    have ea : a n = a m := congrArg Prod.snd h
    rw [←eqn n,eb,ea,eqn m]
  have sub : I.image pair ⊆ I ×ˢ D := by
    rintro u hu
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hn1,hnQ⟩ := Finset.mem_Icc.mp hn
    have e := eqn n
    have ha : 0 < a n := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at e; omega
    have hb : 0 < b n := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at e; omega
    have ha' := Nat.le_mul_of_pos_left (a n) (pow_pos hb 2)
    have hb' := Nat.le_mul_of_pos_right (b n ^ 2) ha
    have hb2 : b n ≤ b n^2 := by nlinarith
    change (b n,a n) ∈ I ×ˢ D
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hb,by dsimp; omega⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨ha,by dsimp; omega⟩,sf n⟩⟩
  let wt (u : ℕ × ℕ) : ℝ := (1/(u.1:ℝ)^2)*(1/(u.2:ℝ))
  calc
    _ ≤ (harmonic Q : ℝ) := log_add_one_le_harmonic Q
    _ = ∑ n ∈ I, wt (pair n) := by
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
      apply Finset.sum_congr rfl
      intro n _
      have e := eqn n
      dsimp [wt,pair]
      conv_lhs => rw [←e]
      push_cast
      simp [one_div,mul_comm]
    _ = ∑ u ∈ I.image pair, wt u := (Finset.sum_image hinj.injOn).symm
    _ ≤ ∑ u ∈ I ×ˢ D, wt u := Finset.sum_le_sum_of_subset_of_nonneg sub
        (fun _ _ _ => by dsimp [wt]; positivity)
    _ = (∑ b ∈ I, 1/(b:ℝ)^2)*sfMass Q := by
      rw [Finset.sum_product]
      simp [wt,D,sfMass,Finset.sum_mul,Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => by positivity)
      exact (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).sum_le_tsum I (fun _ _ => by positivity)

private def divMass (Q : ℕ) : ℝ := ∑ d ∈ divisorsTo Q, (d.divisors.card:ℝ)/d

private theorem square_mass (R : ℕ) :
    sfMass R ^ 2 ≤ zetaTwo*divMass (R^2) := by
  classical
  let D := divisorsTo R
  let E := divisorsTo (R^2)
  let I := Finset.Icc 1 R
  let g (x : ℕ×ℕ) := x.1.gcd x.2
  let u (x : ℕ×ℕ) := x.1/g x
  let v (x : ℕ×ℕ) := x.2/g x
  let d (x : ℕ×ℕ) := u x*v x
  let T := I ×ˢ (E.sigma fun k : ℕ => k.divisors)
  let embed (x : ℕ×ℕ) : ℕ × (Σ _ : ℕ, ℕ) := (g x,⟨d x,u x⟩)
  let w (y : ℕ × (Σ _ : ℕ, ℕ)) : ℝ := (1/(y.1:ℝ)^2)*(1/(y.2.1:ℝ))
  have gu (x : ℕ×ℕ) : g x*u x = x.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have gv (x : ℕ×ℕ) : g x*v x = x.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right ..)
  have dataFor {a : ℕ} (ha : a ∈ D) : 0 < a ∧ a ≤ R ∧ Squarefree a := by
    have z := Finset.mem_filter.mp ha
    exact ⟨(Finset.mem_Icc.mp z.1).1,(Finset.mem_Icc.mp z.1).2,z.2⟩
  have up (x : ℕ×ℕ) (hx : x ∈ D ×ˢ D) : 0 < u x := by
    have a := (dataFor (Finset.mem_product.mp hx).1).1
    by_contra! hz
    have ee := gu x
    rw [show u x=0 by omega,mul_zero] at ee
    omega
  have map {x : ℕ×ℕ} (hx : x ∈ D ×ˢ D) : embed x ∈ T := by
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hx
    obtain ⟨ap,ar,asf⟩ := dataFor ha
    obtain ⟨bp,br,bsf⟩ := dataFor hb
    have gp : 0 < g x := Nat.gcd_pos_of_pos_left _ ap
    have ga := Nat.le_of_dvd ap (Nat.gcd_dvd_left x.1 x.2)
    have ua := Nat.div_le_self x.1 (g x)
    have vb := Nat.div_le_self x.2 (g x)
    have dsf : Squarefree (d x) := (Nat.squarefree_mul (Nat.coprime_div_gcd_div_gcd gp)).mpr
      ⟨asf.squarefree_of_dvd (dvd_of_mul_left_dvd (gu x).dvd),bsf.squarefree_of_dvd (dvd_of_mul_left_dvd (gv x).dvd)⟩
    have dr : d x ≤ R^2 := by rw [pow_two]; exact Nat.mul_le_mul (ua.trans ar) (vb.trans br)
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨gp,ga.trans ar⟩,Finset.mem_sigma.mpr ⟨?_,?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero dsf.ne_zero,dr⟩,dsf⟩
    · exact Nat.mem_divisors.mpr ⟨dvd_mul_right _ _,dsf.ne_zero⟩
  have inj : Set.InjOn embed ↑(D ×ˢ D) := by
    intro x hx y hy e
    have eg : g x = g y := congrArg Prod.fst e
    have ed : u x*v x = u y*v y := congrArg (fun z => z.2.1) e
    have eu : u x = u y := congrArg (fun z => z.2.2) e
    rw [←eu] at ed
    have ev := Nat.eq_of_mul_eq_mul_left (up x hx) ed
    exact Prod.ext (by rw [←gu x,←gu y,eg,eu]) (by rw [←gv x,←gv y,eg,ev])
  have sub : (D ×ˢ D).image embed ⊆ T := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact map hx
  have wh (x : ℕ×ℕ) : w (embed x) = (1/(x.1:ℝ))*(1/(x.2:ℝ)) := by
    have eq : g x^2*d x=x.1*x.2 := by rw [←gu x,←gv x]; dsimp [d]; ring
    dsimp [w,embed]
    simp only [one_div,←mul_inv_rev]
    congr 1
    exact_mod_cast (show d x*g x^2=x.2*x.1 by simpa [mul_comm] using eq)
  calc
    _ = ∑ x ∈ D ×ˢ D, w (embed x) := by
      simp_rw [wh]
      rw [Finset.sum_product,pow_two]
      dsimp [sfMass,D]
      simp only [Finset.sum_mul,Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ y ∈ (D ×ˢ D).image embed, w y := (Finset.sum_image inj).symm
    _ ≤ ∑ y ∈ T, w y := Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by dsimp [w]; positivity)
    _ = (∑ i ∈ I, 1/(i:ℝ)^2)*(∑ k ∈ E, (k.divisors.card:ℝ)/k) := by
      rw [Finset.sum_product,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_sigma,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp [w,div_eq_mul_inv]
      ring
    _ ≤ zetaTwo*divMass (R^2) := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => by positivity)
      exact (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).sum_le_tsum I (fun _ _ => by positivity)

private def loss (t : ℕ) : ℝ := ∑ g ∈ t.divisors, (g.divisors.card:ℝ)/g

private theorem clean_mult {k t : ℕ} (hk : Squarefree k) (cop : k.Coprime t) :
    mult t k = k.divisors.card := by
  rw [mult,Nat.card_divisors hk.ne_zero]
  apply Finset.prod_congr rfl
  intro p hp
  have pp := Nat.prime_of_mem_primeFactors hp
  have pd := Nat.dvd_of_mem_primeFactors hp
  have npt : ¬ p ∣ t := by
    intro h
    exact pp.not_dvd_one (cop.gcd_eq_one ▸ Nat.dvd_gcd pd h)
  have z : t%p ≠ 0 := fun e => npt (Nat.dvd_of_mod_eq_zero e)
  have lt := Nat.mod_lt t pp.pos
  have r : (p-t%p)%p ≠ 0 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
  rw [Nat.factorization_eq_one_of_squarefree hk pp pd]
  simp [rho,bad,Ne.symm r]

private theorem divMass_le {t : ℕ} (ht : 0 < t) (Q : ℕ) :
    divMass Q ≤ loss t * mass t Q := by
  classical
  let D := divisorsTo Q
  let pair (d : ℕ) := (d.gcd t,d/d.gcd t)
  let w (p : ℕ × ℕ) : ℝ := ((p.1.divisors.card:ℝ)/p.1)*((mult t p.2:ℝ)/p.2)
  have ep (d : ℕ) : (pair d).1*(pair d).2=d := Nat.mul_div_cancel' (Nat.gcd_dvd_left ..)
  have inj : Function.Injective pair := by
    intro d e h
    simpa only [ep] using congrArg (fun p : ℕ × ℕ => p.1*p.2) h
  have into {d : ℕ} (hd : d ∈ D) : pair d ∈ t.divisors ×ˢ D := by
    obtain ⟨hds,hs⟩ := Finset.mem_filter.mp hd
    have sk : Squarefree (pair d).2 := hs.squarefree_of_dvd (dvd_of_mul_left_dvd (ep d).dvd)
    exact Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right ..,ht.ne'⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero sk.ne_zero,
        (Nat.div_le_self ..).trans (Finset.mem_Icc.mp hds).2⟩,sk⟩⟩
  have wh {d : ℕ} (hd : d ∈ D) : w (pair d)=(d.divisors.card:ℝ)/d := by
    have hs := (Finset.mem_filter.mp hd).2
    have sk := (Finset.mem_filter.mp (Finset.mem_product.mp (into hd)).2).2
    have cop : (pair d).1.Coprime (pair d).2 := Nat.coprime_of_squarefree_mul ((ep d).symm ▸ hs)
    have cnt : d.divisors.card = (pair d).1.divisors.card * (pair d).2.divisors.card := by
      simpa only [ep] using cop.card_divisors_mul
    dsimp only [w]
    rw [clean_mult sk (Nat.coprime_div_gcd_of_squarefree hs ht.ne'),div_mul_div_comm,cnt,Nat.cast_mul]
    congr 1
    exact_mod_cast ep d
  calc
    _ = ∑ p ∈ D.image pair, w p := by
      rw [Finset.sum_image inj.injOn]
      exact Finset.sum_congr rfl fun d hd => (wh hd).symm
    _ ≤ ∑ p ∈ t.divisors ×ˢ D, w p :=
      Finset.sum_le_sum_of_subset_of_nonneg (by rintro p hp; obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hp; exact into hd)
        (fun p _ _ => by dsimp [w]; positivity)
    _ = _ := by
      rw [Finset.sum_product]
      simp [w,loss,mass,D,Finset.sum_mul,Finset.mul_sum]
      exact Finset.sum_comm

private def pairs (t start h : ℕ) : Finset ℕ :=
  (range h).filter fun i => (start+i).Prime ∧ (start+i+t).Prime

private theorem pair_bound {t R start h : ℕ} (ht : 0 < t) (hR : 1 ≤ R)
    (hr : R^2 < start) (hh : (R^2)^4 ≤ h) :
    ((pairs t start h).card:ℝ) * Real.log (R+1:ℕ)^2 ≤
      (2*zetaTwo^3)*(h:ℝ)*loss t := by
  classical
  let M := mass t (R^2)
  let P := pairs t start h
  have hQ : 1 ≤ R^2 := Nat.one_le_pow _ _ hR
  have h1 : 1 ≤ M := by
    have hm : 1 ∈ divisorsTo (R^2) := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl,hQ⟩,by simp⟩
    have eq : (mult t 1:ℝ)/(1:ℝ)=1 := by simp [mult]
    rw [←eq]
    simpa only [Nat.cast_one,M,mass] using Finset.single_le_sum (f:=fun d : ℕ => (mult t d:ℝ)/(d:ℝ)) (fun d _ => by positivity) hm
  have cap : (P.card:ℝ)*M^2 ≤ h*M+((R^2:ℕ):ℝ)^4 := by
    calc
      _ = ∑ i ∈ P, kernel t (R^2) (start+i)^2 := by
        have same (i : ℕ) (hi : i ∈ P) : kernel t (R^2) (start+i) = M := by
          obtain ⟨_,hn,hn'⟩ := Finset.mem_filter.mp hi
          apply Finset.sum_congr rfl
          intro d hd
          obtain ⟨hb,hsf⟩ := Finset.mem_filter.mp hd
          exact K_prime t hsf hn hn' ((Finset.mem_Icc.mp hb).2.trans_lt (by omega))
        rw [Finset.sum_congr rfl (fun i hi => congrArg (·^2) (same i hi))]
        simp
      _ ≤ ∑ i ∈ range h, kernel t (R^2) (start+i)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..) (fun _ _ _ => sq_nonneg _)
      _ ≤ _ := energy t start h _
  have cp : (P.card:ℝ)*M ≤ 2*h := by
    apply (le_of_mul_le_mul_right _ (by linarith : 0 < M))
    have hh' : ((R^2:ℕ):ℝ)^4 ≤ h := by exact_mod_cast hh
    nlinarith [mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg h : (0:ℝ) ≤ _)]
  have hZ : 0 ≤ zetaTwo := tsum_nonneg fun _ => by positivity
  have hlog : 0 ≤ Real.log (R+1:ℕ) := Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 R)
  have hlog2 : Real.log (R+1:ℕ)^2 ≤ zetaTwo^3*(loss t*M) := by
    calc
      _ ≤ (zetaTwo * sfMass R)^2 := by nlinarith only [sq_le_sq' (by linarith [size_mass R]) (size_mass R)]
      _ = zetaTwo^2*sfMass R^2 := mul_pow .. 
      _ ≤ zetaTwo^2*(zetaTwo*divMass (R^2)) := by gcongr; exact square_mass R
      _ ≤ zetaTwo^2*(zetaTwo*(loss t*M)) := by gcongr; exact divMass_le ht _
      _ = _ := by ring
  have hL : 0 ≤ loss t := Finset.sum_nonneg fun _ _ => by positivity
  calc
    _ ≤ P.card*(zetaTwo^3*(loss t*M)) := by gcongr
    _ = (zetaTwo^3*loss t)*(P.card*M) := by ring
    _ ≤ (zetaTwo^3*loss t)*(2*h) := by gcongr
    _ = _ := by ring

private def recipDiv (n : ℕ) : ℝ := ∑ d ∈ n.divisors, 1/(d:ℝ)

private theorem loss_le_square (n : ℕ) : loss n ≤ recipDiv n^2 := by
  classical
  let D := n.divisors
  let S := D.sigma fun d => d.divisors
  let pair (z : Σ _ : ℕ, ℕ) : ℕ × ℕ := (z.2,z.1/z.2)
  let w (v : ℕ×ℕ) : ℝ := (1/(v.1:ℝ))*(1/(v.2:ℝ))
  have recon {z : Σ _ : ℕ, ℕ} (hz : z ∈ S) : (pair z).1*(pair z).2=z.1 :=
    Nat.mul_div_cancel' (Nat.mem_divisors.mp (Finset.mem_sigma.mp hz).2).1
  have sub : S.image pair ⊆ D ×ˢ D := by
    intro v hv
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hd,ha⟩ := Finset.mem_sigma.mp hz
    obtain ⟨dvd,d0⟩ := Nat.mem_divisors.mp hd
    obtain ⟨av,_⟩ := Nat.mem_divisors.mp ha
    exact Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨av.trans dvd,d0⟩,
      Nat.mem_divisors.mpr ⟨(Nat.div_dvd_of_dvd av).trans dvd,d0⟩⟩
  have inj : Set.InjOn pair ↑S := by
    intro x hx y hy he
    have ea := congrArg Prod.fst he
    have eb := congrArg (fun p : ℕ×ℕ => p.1*p.2) he
    change (pair x).1*(pair x).2=(pair y).1*(pair y).2 at eb
    rw [recon hx,recon hy] at eb
    cases x; cases y; simp_all [pair]
  calc
    _ = ∑ z ∈ S, w (pair z) := by
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro d hd
      have step a (ha : a∈d.divisors) : w (pair ⟨d,a⟩)=1/(d:ℝ) := by
        dsimp [w,pair]
        rw [div_mul_div_comm,one_mul,←Nat.cast_mul,Nat.mul_div_cancel' (Nat.mem_divisors.mp ha).1]
      rw [Finset.sum_congr rfl step]
      simp [div_eq_mul_inv]
    _ = ∑ p ∈ S.image pair, w p := (Finset.sum_image inj).symm
    _ ≤ ∑ p ∈ D ×ˢ D, w p := Finset.sum_le_sum_of_subset_of_nonneg sub (fun p _ _ => by dsimp [w]; positivity)
    _ = _ := by
      rw [Finset.sum_product,pow_two]
      simp [recipDiv,D,w,Finset.sum_mul,Finset.mul_sum]
      exact Finset.sum_comm

private theorem recip_times (n : ℕ) : recipDiv n*(n:ℝ)=(ArithmeticFunction.sigma 1 n:ℝ) := by
  rw [ArithmeticFunction.sigma_one_apply,Nat.cast_sum,recipDiv,Finset.sum_mul,← Nat.sum_div_divisors n (fun d => (d:ℝ))]
  apply Finset.sum_congr rfl
  intro d hd
  have e : (d:ℝ)*((n/d:ℕ):ℝ)=n := by exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1
  have pd : (d:ℝ)≠0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  field_simp
  linarith

private def primeF (p : ℕ) : ℝ := (p:ℝ)/((p:ℝ)-1)

private theorem recip_bound {n : ℕ} (hn : n ≠ 0) :
    recipDiv n ≤ ∏ p ∈ n.primeFactors, primeF p := by
  have posn : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  apply le_of_mul_le_mul_right _ posn
  rw [recip_times,ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn,Nat.cast_prod]
  have prodN : (∏ p ∈ n.primeFactors, (p:ℝ)^(n.factorization p))=n := by
    exact_mod_cast Nat.prod_factorization_pow_eq_self hn
  conv_rhs => rw [←prodN]
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_le_prod (fun _ _ => by positivity)
  intro p hp
  have pp := Nat.prime_of_mem_primeFactors hp
  have p1 : (1:ℝ)<p := by exact_mod_cast pp.one_lt
  simp only [Nat.mul_one,Nat.cast_sum,Nat.cast_pow,primeF]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  have eq := geom_sum_mul (p:ℝ) (n.factorization p+1)
  rw [pow_succ] at eq
  linarith

private theorem logtwo : (1/2:ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · convert Real.one_sub_inv_le_log_of_pos (x:=(2:ℝ)) (by norm_num) using 1
    norm_num
  · convert Real.log_le_sub_one_of_pos (x:=(2:ℝ)) (by norm_num) using 1
    norm_num

private theorem few_primes (x : ℝ) (hx : 1 < x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ)*Real.log x ≤ 6*x := by
  have hlog := Real.log_pos hx
  have hxs := Real.sqrt_nonneg x
  have hlogle : Real.log x ≤ 2*Real.sqrt x := by
    simpa [Real.sqrt_eq_rpow,div_eq_mul_inv,mul_comm] using
      Real.log_le_rpow_div (show 0 ≤ x by linarith) (show (0:ℝ)<1/2 by norm_num)
  have he : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  have H := Chebyshev.pi_le_log4_mul_div hx
  rw [Real.log_sqrt (by linarith),he] at H
  have hl : 0 < Real.log x/2 := by positivity
  have e : 2*Real.log 2*x/(Real.log x/2)*Real.log x = 4*Real.log 2*x := by field_simp; ring
  have h := mul_le_mul_of_nonneg_right H hlog.le
  rw [add_mul,e] at h
  nlinarith [mul_le_mul_of_nonneg_left hlogle hxs,Real.sq_sqrt (by linarith : 0≤x),
    mul_le_mul_of_nonneg_right logtwo.2 (by linarith : 0≤x)]

private theorem eventual_sparse : ∀ᶠ p : ℕ in atTop, 131072*p.primeCounting ≤ p := by
  have hl := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 786432
  filter_upwards [hl,eventually_ge_atTop 2] with p h h2
  have h' := few_primes p (by exact_mod_cast h2 : (1:ℝ)<p)
  rw [Nat.floor_natCast] at h'
  change (786432:ℝ) ≤ Real.log p at h
  exact_mod_cast (show (131072:ℝ)*p.primeCounting ≤ p by
    nlinarith [mul_le_mul_of_nonneg_left h (Nat.cast_nonneg p.primeCounting (α:=ℝ))])

private theorem one_linear (m : ℕ) {x : ℝ} (hx : 0≤x) (h1 : x≤1) :
    (1+x)^m ≤ 1+((2:ℝ)^m-1)*x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ,pow_succ]
    have h := mul_le_mul_of_nonneg_right ih (show 0≤1+x by linarith)
    have hm : 0≤(2:ℝ)^m-1 := sub_nonneg.mpr (one_le_pow₀ (by norm_num))
    nlinarith [mul_nonneg hm (mul_nonneg hx (sub_nonneg.mpr h1))]

private theorem prime_prod_bound : ∃ B : ℝ, 1≤B ∧ ∀ S : Finset ℕ,
    (∀ p ∈ S, p.Prime) → (∏ p ∈ S, primeF p^16) ≤ B*(S.card+1) := by
  classical
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp eventual_sparse
  let B : ℝ := ∏ p ∈ Nat.primesLE N, primeF p^16
  have f1 {p : ℕ} (hp : p.Prime) : 1 ≤ primeF p := by
    have h : (1:ℝ) < p := by exact_mod_cast hp.one_lt
    rw [primeF,le_div_iff₀ (by linarith)]
    linarith
  have B1 : 1 ≤ B := Finset.one_le_prod fun p hp => one_le_pow₀ (f1 (Nat.prime_of_mem_primesLE hp))
  refine ⟨B,B1,?_⟩
  intro S
  induction S using Finset.induction_on_max with
  | empty => simpa using B1
  | insert p S hmax ih =>
    intro H
    have pp := H p (Finset.mem_insert_self ..)
    have sm (a : ℕ) (ha : a∈S) : a.Prime := H a (Finset.mem_insert_of_mem ha)
    have hpS : p ∉ S := fun h => (hmax p h).false
    have into : insert p S ⊆ Nat.primesLE p := by
      intro a ha
      exact Nat.mem_primesLE.mpr ⟨(Finset.mem_insert.mp ha).elim (fun e => e.le) (fun m => (hmax _ m).le),H a ha⟩
    by_cases small : p < N
    · have intoN : insert p S ⊆ Nat.primesLE N := fun a ha =>
        Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp (into ha)).1.trans small.le,H a ha⟩
      apply (Finset.prod_le_prod_of_subset_of_one_le intoN (fun _ _ => by positivity)
        (fun a ha _ => one_le_pow₀ (f1 (Nat.prime_of_mem_primesLE ha)))).trans
      change B ≤ B*(_+1)
      nlinarith [mul_nonneg (show 0 ≤ B by linarith) (Nat.cast_nonneg (insert p S).card (α:=ℝ))]
    · have sz := (Finset.card_le_card into).trans_eq (Nat.primesLE_card_eq_primeCounting _)
      rw [Finset.card_insert_of_notMem hpS] at sz
      have sp := (Nat.mul_le_mul_left 131072 sz).trans (hN p (by omega))
      let m : ℝ := S.card+1
      have hm : 0 < m := by dsimp [m]; positivity
      have hsp : 131072*m ≤ (p:ℝ) := by dsimp [m]; exact_mod_cast sp
      have pm : 1 ≤ (p:ℝ)-1 := by
        have hp : (2:ℝ) ≤ p := by exact_mod_cast pp.two_le
        linarith
      have pf : primeF p = 1+1/((p:ℝ)-1) := by unfold primeF; field_simp; ring
      have ub : primeF p^16 ≤ 1+1/m := by
        rw [pf]
        apply (one_linear 16 (by positivity) ((div_le_one (by linarith)).mpr pm)).trans
        apply add_le_add_right
        rw [show (2:ℝ)^16-1=65535 by norm_num]
        rw [mul_one_div,div_le_div_iff₀ (by linarith) hm]
        dsimp [m] at *
        nlinarith [Nat.cast_nonneg S.card (α:=ℝ)]
      rw [Finset.prod_insert hpS,Finset.card_insert_of_notMem hpS,Nat.cast_add_one]
      change _ ≤ B*(m+1)
      calc
        _ ≤ (1+1/m)*(B*m) := mul_le_mul ub (ih sm) (Finset.prod_nonneg fun _ _ => by positivity)
          (by positivity)
        _ = _ := by field_simp

private theorem loss_slow : ∃ B : ℝ, 1≤B ∧ ∀ n : ℕ, n≠0 →
    loss n^8 ≤ B*(n.primeFactors.card+1) := by
  obtain ⟨B,B1,hB⟩ := prime_prod_bound
  refine ⟨B,B1,?_⟩
  intro n hn
  have h := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity : 0≤loss n) (loss_le_square n) 8
  have b := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity : 0≤recipDiv n) (recip_bound hn) 16
  calc
    _ ≤ recipDiv n^16 := by change loss n^8 ≤ recipDiv n^(2*8); rw [pow_mul]; exact h
    _ ≤ _ := b
    _ = ∏ p ∈ n.primeFactors, primeF p^16 := (Finset.prod_pow ..).symm
    _ ≤ _ := hB _ (fun _ => Nat.prime_of_mem_primeFactors)

private def ord (C d : ℕ) := orderOf (C : ZMod d)
private def blockProd (C K : ℕ) := ∏ j ∈ Icc 1 K, (C^j-1)
private def dw (s : ℕ) : ℝ := (s.divisors.card:ℝ)/s

private theorem ord_iff {C : ℕ} (hC : 1 < C) (s t : ℕ) :
    ord C s ∣ t ↔ s ∣ C^t-1 := by
  have cp : 1≤C^t := Nat.one_le_pow _ _ hC.le
  rw [←ZMod.natCast_eq_zero_iff (C^t-1),Nat.cast_sub cp,Nat.cast_pow,Nat.cast_one,sub_eq_zero]
  exact orderOf_dvd_iff_pow_eq_one

private theorem block_pos {C : ℕ} (hC : 1<C) (K : ℕ) : 0<blockProd C K := by
  apply Finset.prod_pos
  intro j hj
  exact Nat.sub_pos_of_lt (one_lt_pow₀ hC (by have := (Finset.mem_Icc.mp hj).1; omega))

private theorem block_mem {C s K : ℕ} (hC : 1 < C) (hpos : 0<ord C s)
    (hord : ord C s ≤ K) : s ∈ (blockProd C K).divisors := by
  apply Nat.mem_divisors.mpr
  refine ⟨((ord_iff hC s _).mp (dvd_refl _)).trans ?_,(block_pos hC _).ne'⟩
  exact Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨hpos,hord⟩)

private theorem block_card {C : ℕ} (hC : 1<C) (K : ℕ) :
    (blockProd C K).primeFactors.card ≤ C*K^2 := by
  let P := (blockProd C K).primeFactors
  have hp : 2^P.card ≤ blockProd C K := by
    calc
      _ = ∏ _p ∈ P, 2 := by simp
      _ ≤ ∏ p ∈ P, p := Finset.prod_le_prod' (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ _ := Nat.le_of_dvd (block_pos hC _) (Nat.prod_primeFactors_dvd _)
  have hbound : blockProd C K ≤ 2^(C*K^2) := by
    calc
      _ ≤ ∏ _j ∈ Icc 1 K,(2^C)^K := Finset.prod_le_prod' (fun j hj =>
        (Nat.sub_le ..).trans ((Nat.pow_le_pow_left (Nat.lt_pow_self (by decide : 1 < 2) (n:=C)).le _).trans
          (Nat.pow_le_pow_right (by positivity) (Finset.mem_Icc.mp hj).2)))
      _ = _ := by simp [←pow_mul,pow_two,Nat.mul_assoc]
  exact (pow_le_pow_iff_right₀ (by decide : 1<(2:ℕ))).mp (hp.trans hbound)

private theorem four_pow (j : ℕ) : (4:ℝ)^j = ((2:ℝ)^j)^2 := by
  calc
    _ = ((2:ℝ)*2)^j := by norm_num
    _ = _ := by rw [mul_pow,pow_two]

private theorem block_weight {C : ℕ} (hC : 1<C) : ∃ A : ℝ, 1 ≤ A ∧ ∀ j : ℕ,
    loss (blockProd C (4^j)) ≤ A*(2:ℝ)^j := by
  obtain ⟨B,B1,bound⟩ := loss_slow
  let A := B*((C:ℝ)+1)
  have A1 : 1≤A := one_le_mul_of_one_le_of_one_le B1 (by have := Nat.cast_nonneg C (α:=ℝ); linarith)
  refine ⟨A,A1,?_⟩
  intro j
  let K := (4:ℕ)^j
  have b := bound (blockProd C K) (block_pos hC _).ne'
  have card : ((blockProd C K).primeFactors.card:ℝ) ≤ C*(K:ℝ)^2 := by exact_mod_cast block_card hC K
  have r1 : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
  have eq : (K:ℝ)^2 = ((2:ℝ)^j)^4 := by dsimp [K]; push_cast; rw [four_pow]; ring
  have r48 : ((2:ℝ)^j)^4 ≤ ((2:ℝ)^j)^8 := pow_le_pow_right₀ r1 (by decide)
  have r18 : (1:ℝ) ≤ ((2:ℝ)^j)^8 := one_le_pow₀ r1
  apply le_of_pow_le_pow_left₀ (n:=8) (by decide) (mul_nonneg (by linarith) (by positivity))
  rw [mul_pow]
  calc
    _ ≤ B*((C:ℝ)*(K:ℝ)^2+1) := b.trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
    _ ≤ A*((2:ℝ)^j)^8 := by
      dsimp [A]
      rw [eq]
      have bb : 0 ≤ B*(C:ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
      nlinarith only [mul_le_mul_of_nonneg_left r48 bb,mul_le_mul_of_nonneg_left r18 (show 0≤B by linarith)]
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_self_pow₀ A1 (by decide)) (by positivity)
private theorem reciprocal_orders {C : ℕ} (hC : 1<C) :
    ∃ M : ℝ, 0<M ∧ ∀ S : Finset ℕ, (∀ s ∈ S, 0<ord C s) →
    (∑ s ∈ S, dw s/(ord C s:ℝ)) ≤ M := by
  classical
  obtain ⟨A,A1,weight⟩ := block_weight hC
  have ap : 0<A := by linarith
  have posw (s : ℕ) : 0≤dw s := by dsimp [dw]; positivity
  have graded (j : ℕ) (S : Finset ℕ)
      (hS : ∀ s ∈ S, 0<ord C s ∧ ord C s ≤ 4^j) :
      (∑ s ∈ S, dw s/(ord C s:ℝ)) ≤ A*(5-4/(2:ℝ)^j) := by
    induction j generalizing S with
    | zero =>
      have sub : S ⊆ (blockProd C (4^0)).divisors := fun s hs =>
        block_mem hC (hS s hs).1 (hS s hs).2
      have on (s : ℕ) (hs : s∈S) : ord C s=1 := by
        have v := hS s hs
        norm_num at v
        omega
      calc
        _ = ∑ s ∈ S, dw s := Finset.sum_congr rfl fun s hs => by rw [on s hs]; norm_num
        _ ≤ loss (blockProd C (4^0)) :=
          Finset.sum_le_sum_of_subset_of_nonneg sub (fun s _ _ => posw s)
        _ ≤ _ := by norm_num at *; exact weight 0 |>.trans_eq (by norm_num)
    | succ j ih =>
      let T := S.filter fun s => ord C s ≤ 4^j
      let U := S.filter fun s => ¬ord C s ≤ 4^j
      have hT := ih T (fun s hs => ⟨(hS s (Finset.mem_filter.mp hs).1).1,(Finset.mem_filter.mp hs).2⟩)
      have sub : U ⊆ (blockProd C (4^(j+1))).divisors := fun s hs =>
        block_mem hC (hS s (Finset.mem_filter.mp hs).1).1 (hS s (Finset.mem_filter.mp hs).1).2
      have hU : ∑ s ∈ U, dw s/(ord C s:ℝ) ≤ (A*2^(j+1))/(4:ℝ)^j := by
        calc
          _ ≤ ∑ s ∈ U, dw s/(4:ℝ)^j := by
            apply Finset.sum_le_sum
            intro s hs
            apply div_le_div_of_nonneg_left (posw _) (by positivity)
            exact_mod_cast (lt_of_not_ge (Finset.mem_filter.mp hs).2).le
          _ = (∑ s ∈ U, dw s)/(4:ℝ)^j := (Finset.sum_div ..).symm
          _ ≤ _ := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact (Finset.sum_le_sum_of_subset_of_nonneg sub (fun s _ _ => posw s)).trans (weight (j+1))
      rw [←Finset.sum_filter_add_sum_filter_not S (fun s => ord C s ≤ 4^j)]
      change _ ≤ _
      apply (add_le_add hT hU).trans
      rw [four_pow,pow_succ]
      apply le_of_eq
      field_simp
      ring
  refine ⟨5*A,by positivity,?_⟩
  intro S hs
  let L := S.sup (ord C)
  have b (s : ℕ) (hm : s ∈ S) : ord C s ≤ 4^L :=
    (Finset.le_sup (f:=ord C) hm).trans (Nat.lt_pow_self (by decide : 1<4)).le
  apply (graded L S (fun s hm => ⟨hs s hm,b s hm⟩)).trans
  have ha : 0 ≤ A*(4/(2:ℝ)^L) := by positivity
  linarith

private theorem loss_powers_avg {C : ℕ} (hC : 1<C) :
    ∃ M : ℝ, 0<M ∧ ∀ K : ℕ, (∑ t ∈ Icc 1 K, loss (C^t-1)) ≤ M*K := by
  classical
  obtain ⟨M,m0,orders⟩ := reciprocal_orders hC
  refine ⟨M,m0,?_⟩
  intro K
  let I := Icc 1 K
  let S := ((blockProd C K).divisors).filter fun s => 0<ord C s
  have same {t : ℕ} (ht : t ∈ I) :
      (C^t-1).divisors = S.filter fun s => ord C s ∣ t := by
    have tp := (Finset.mem_Icc.mp ht).1
    have cp : C^t-1 ≠ 0 := (Nat.sub_pos_of_lt (one_lt_pow₀ hC (by omega))).ne'
    ext s
    simp only [Finset.mem_filter]
    constructor
    · intro h
      have o := (ord_iff hC s t).mpr (Nat.mem_divisors.mp h).1
      have op : 0<ord C s := Nat.pos_of_dvd_of_pos o tp
      exact ⟨Finset.mem_filter.mpr ⟨block_mem hC op ((Nat.le_of_dvd tp o).trans (Finset.mem_Icc.mp ht).2),op⟩,o⟩
    · exact fun h => Nat.mem_divisors.mpr ⟨(ord_iff hC s t).mp h.2,cp⟩
  have howMany (s : ℕ) (hs : s∈S) :
      ((I.filter (fun t => ord C s ∣ t)).card:ℝ)*(dw s) ≤ K*(dw s/(ord C s:ℝ)) := by
    have op := (Finset.mem_filter.mp hs).2
    have cnt : (I.filter fun t => ord C s ∣ t).card = K/(ord C s) := by
      rw [←Nat.card_multiples' K (ord C s)]
      congr 1
      ext t
      simp only [I,Finset.mem_filter,Finset.mem_Icc,Finset.mem_range]
      omega
    rw [cnt]
    have op' : (0:ℝ)<ord C s := by exact_mod_cast op
    have h := Nat.div_mul_le_self K (ord C s)
    have he : ((K/ord C s:ℕ):ℝ)*(ord C s:ℝ) ≤ K := by exact_mod_cast h
    rw [←mul_div_assoc,le_div_iff₀ op']
    simpa [mul_assoc,mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_right he
      (show 0≤dw s by dsimp [dw]; positivity)
  calc
    _ = ∑ t ∈ I, ∑ s ∈ S, if ord C s ∣ t then dw s else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [loss,same ht,Finset.sum_filter]
      rfl
    _ = ∑ s ∈ S, ((I.filter fun t => ord C s ∣ t).card:ℝ)*dw s := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [←Finset.sum_filter]
      simp
    _ ≤ ∑ s ∈ S, (K:ℝ)*(dw s/(ord C s:ℝ)) := Finset.sum_le_sum howMany
    _ ≤ _ := by
      rw [←Finset.mul_sum,mul_comm M]
      exact mul_le_mul_of_nonneg_left (orders S (fun s hs => (Finset.mem_filter.mp hs).2)) (Nat.cast_nonneg _)
private theorem loss_mul {a b : ℕ} (cop : a.Coprime b) : loss (a*b)=loss a*loss b := by
  let F : ArithmeticFunction ℝ := ⟨dw,by simp [dw]⟩
  have mf : F.IsMultiplicative := by
    refine ⟨?_,?_⟩
    · change dw 1=1
      simp [dw]
    · intro m n c
      change dw (m*n)=dw m*dw n
      rw [dw,dw,dw,c.card_divisors_mul,Nat.cast_mul,Nat.cast_mul,div_mul_div_comm]
  let L : ArithmeticFunction ℝ := (ArithmeticFunction.zeta : ArithmeticFunction ℝ)*F
  have ml : L.IsMultiplicative := ArithmeticFunction.isMultiplicative_zeta.natCast.mul mf
  have e (v : ℕ) : L v=loss v := ArithmeticFunction.coe_zeta_mul_apply
  simpa only [e] using ml.map_mul_of_coprime cop

private theorem shifted_loss {C : ℕ} (hC : 1<C) :
    ∃ A : ℝ, 0<A ∧ ∀ k : ℕ,
      (∑ i ∈ Icc 1 k, ∑ d ∈ Icc 1 k, loss (C^i*(C^d-1))) ≤ A*k^2 := by
  obtain ⟨B,B1,slow⟩ := loss_slow
  obtain ⟨M,m0,avg⟩ := loss_powers_avg hC
  let D := B*(C.primeFactors.card+1)
  have dp : 0<D := by dsimp [D]; positivity
  have DI : 1 ≤ D := by dsimp [D]; nlinarith [mul_nonneg (show 0≤B by linarith) (Nat.cast_nonneg C.primeFactors.card (α:=ℝ))]
  have bounded (i : ℕ) (hi : 0 < i) : loss (C^i) ≤ D := by
    have h := slow (C^i) (pow_ne_zero _ (by omega))
    rw [Nat.primeFactors_pow _ hi.ne'] at h
    apply le_of_pow_le_pow_left₀ (n:=8) (by decide) dp.le
    exact h.trans (le_self_pow₀ DI (by decide))
  have cp (i d : ℕ) (hd : 0<d) : (C^i).Coprime (C^d-1) := by
    have w : (C^d).Coprime (C^d-1) := (Nat.coprime_self_sub_right (Nat.one_le_pow _ _ hC.le)).mpr (Nat.coprime_one_right _)
    exact ((Nat.Coprime.of_dvd_left (dvd_pow_self C hd.ne') w).pow_left _)
  refine ⟨D*M,mul_pos dp m0,?_⟩
  intro k
  calc
    _ ≤ ∑ i ∈ Icc 1 k, ∑ d ∈ Icc 1 k, D*loss (C^d-1) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro d hd
      rw [loss_mul (cp i d (Finset.mem_Icc.mp hd).1)]
      exact mul_le_mul_of_nonneg_right (bounded i (Finset.mem_Icc.mp hi).1)
        (Finset.sum_nonneg fun _ _ => by positivity)
    _ = (k:ℝ)*D*(∑ d ∈ Icc 1 k,loss (C^d-1)) := by
      simp [←Finset.mul_sum,mul_assoc]
    _ ≤ _ := by
      have z := mul_le_mul_of_nonneg_left (avg k) (show 0≤(k:ℝ)*D by positivity)
      nlinarith only [z]

private def Y (k : ℕ) : ℕ := (2^k)^16
private def band (k : ℕ) := Nat.primesLE (1024*Y k) \ Nat.primesLE (Y k)

private theorem logY (k : ℕ) : Real.log (Y k:ℝ)=16*k*Real.log 2 := by
  simp [Y,Real.log_pow]
  ring

private theorem Y_big : Tendsto Y atTop atTop := by
  have h : Tendsto (fun k : ℕ => (2:ℕ)^k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by decide)
  apply tendsto_atTop_mono (f:=fun k : ℕ => 2^k) _ h
  intro k
  exact Nat.le_self_pow (by decide) _

private theorem many_primes : ∀ᶠ x : ℝ in atTop,
    x*Real.log 2/4 ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ)*Real.log x := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [Real.isLittleO_log_id_atTop.bound (show 0 < Real.log 2/4 by positivity),
    eventually_ge_atTop (8:ℝ)] with x hx h8
  have xp : 0 < x := by linarith
  have logx := Real.log_nonneg (by linarith : (1:ℝ) ≤ x)
  simp only [Real.norm_eq_abs,id_eq,abs_of_nonneg logx,abs_of_pos xp] at hx
  have hlog : Real.log (x+2) ≤ Real.log 2 + Real.log x := by
    rw [← Real.log_mul (by norm_num) xp.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  have H := (div_le_iff₀ (Real.log_pos (by linarith : 1 < x))).mp
    (Chebyshev.pi_ge' (by linarith : 1 < x))
  nlinarith [mul_nonneg (sub_nonneg.mpr h8) hl.le]

private theorem band_size : ∀ᶠ k : ℕ in atTop,
    (Y k:ℝ) ≤ (band k).card*k ∧ (band k).card*(k:ℝ) ≤ 1024*(Y k:ℝ) := by
  have ty : Tendsto (fun k : ℕ => (Y k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp Y_big
  have tC : Tendsto (fun k : ℕ => (1024:ℝ)*(Y k:ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) ty
  filter_upwards [tC.eventually many_primes,Y_big.eventually_ge_atTop 1024,eventually_ge_atTop 1] with k hm hy hk
  have y1 : (1:ℝ)<Y k := by exact_mod_cast (show 1<Y k by omega)
  have hCy : (1:ℝ)<1024*(Y k:ℝ) := by linarith
  have floorC : ⌊(1024:ℝ)*(Y k:ℝ)⌋₊=1024*Y k := by exact_mod_cast (Nat.floor_natCast (1024*Y k) : _)
  rw [floorC] at hm
  have hu := few_primes (Y k) y1
  rw [Nat.floor_natCast] at hu
  have hU := few_primes (1024*(Y k:ℝ)) hCy
  rw [floorC] at hU
  have hL : Real.log (1024*(Y k:ℝ)) ≤ 2*Real.log (Y k:ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    linarith [Real.log_le_log (by norm_num : (0:ℝ)<1024) (show (1024:ℝ) ≤ Y k by exact_mod_cast hy)]
  have hlo : Real.log (Y k:ℝ) ≤ Real.log (1024*(Y k:ℝ)) := Real.log_le_log (by positivity) (by linarith)
  have sb : Nat.primesLE (Y k) ⊆ Nat.primesLE (1024*Y k) := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans (by omega),(Nat.mem_primesLE.mp hp).2⟩
  have eq : ((band k).card:ℝ)+(Y k).primeCounting=(1024*Y k).primeCounting := by
    exact_mod_cast (show (band k).card+(Y k).primeCounting=(1024*Y k).primeCounting by
      rw [←Nat.primesLE_card_eq_primeCounting,←Nat.primesLE_card_eq_primeCounting,band,Finset.card_sdiff_of_subset sb]
      exact Nat.sub_add_cancel (Finset.card_le_card sb))
  have hp := Nat.cast_nonneg (1024*Y k).primeCounting (α:=ℝ)
  have hb := Nat.cast_nonneg (band k).card (α:=ℝ)
  have e := congrArg (fun a : ℝ => a*Real.log (Y k:ℝ)) eq
  have hK1 : 8*(k:ℝ) ≤ Real.log (Y k:ℝ) := by rw [logY]; nlinarith [mul_le_mul_of_nonneg_right logtwo.1 (Nat.cast_nonneg k : (0:ℝ) ≤ _)]
  have hK2 : Real.log (Y k:ℝ) ≤ 16*(k:ℝ) := by rw [logY]; nlinarith [mul_le_mul_of_nonneg_right logtwo.2 (Nat.cast_nonneg k : (0:ℝ) ≤ _)]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hL hp,mul_le_mul_of_nonneg_right logtwo.1 (show 0≤(Y k:ℝ) by positivity),
      mul_le_mul_of_nonneg_left hK2 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hlo hp,mul_le_mul_of_nonneg_left hK1 hb,
      mul_nonneg (Nat.cast_nonneg (Y k).primeCounting : (0:ℝ) ≤ _) (Real.log_pos y1).le]
private theorem band_data {k p : ℕ} (hp : p ∈ band k) :
    p.Prime ∧ Y k < p ∧ p ≤ 1024*Y k := by
  obtain ⟨hy,hn⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨pr,pp⟩ := Nat.mem_primesLE.mp hy
  exact ⟨pp,lt_of_not_ge (fun h => hn (Nat.mem_primesLE.mpr ⟨h,pp⟩)),pr⟩


section
variable {α : Type*}
private def collisions (S : Finset α) (f : α → ℕ) :=
  (S ×ˢ S).filter fun x => f x.1=f x.2

private theorem fiber_count (S : Finset α) (f : α → ℕ) :
    S.card^2 ≤ (S.image f).card*(collisions S f).card := by
  classical
  let B := S.image f
  let F (v : ℕ) := S.filter (fun p => f p=v)
  have hsum : (∑ b ∈ B, (F b).card) = S.card :=
    (Finset.card_eq_sum_card_fiberwise (f:=f) (s:=S) (t:=B) fun _ hx => Finset.mem_image_of_mem f hx).symm
  have each (b : ℕ) : ((collisions S f).filter fun x => f x.1=b) = F b ×ˢ F b := by
    ext x
    simp only [collisions,F,Finset.mem_product,Finset.mem_filter]
    grind
  have eq : ∑ b ∈ B, (F b).card^2 = (collisions S f).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f:=fun x : α×α => f x.1) (s:=collisions S f) (t:=B)
      (fun x hx => Finset.mem_image_of_mem _ (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1)]
    simp_rw [each,Finset.card_product,pow_two]
  rw [←hsum,←eq]
  simpa only [Pi.one_apply,one_mul,one_pow,Finset.sum_const,smul_eq_mul,mul_one] using
    Finset.sum_mul_sq_le_sq_mul_sq (R:=ℕ) B 1 (fun b => (F b).card)


end

private def source (C k : ℕ) := band (C*k) ×ˢ Icc 1 k
private def rep (C : ℕ) (x : ℕ×ℕ) := x.1+C^x.2
private def result (C k : ℕ) := (source C k).image (rep C)
private def delta (C i d : ℕ) := C^i*(C^d-1)

private theorem reconstruct_sum {C : ℕ} (hC : 1<C) {p q i j : ℕ}
    (he : p+C^i=q+C^j) (hi : i<j) : p=q+delta C i (j-i) := by
  have e : C^j=C^i*C^(j-i) := by rw [←pow_add,Nat.add_sub_of_le hi.le]
  have one := Nat.one_le_pow (j-i) C hC.le
  have f : delta C i (j-i)+C^i = C^i*C^(j-i) := by
    rw [delta,←Nat.mul_succ,Nat.succ_eq_add_one,Nat.sub_add_cancel one]
  omega

private theorem ncollision {C : ℕ} (hC : 1<C) (k : ℕ) :
    (collisions (source C k) (rep C)).card ≤ (source C k).card+
    2*∑ i ∈ Icc 1 k, ∑ d ∈ Icc 1 k, (pairs (delta C i d) (Y (C*k)) (1024*Y (C*k)+1)).card := by
  classical
  let S := source C k
  let I := Icc 1 k
  let y := Y (C*k)
  let h := 1024*y+1
  let T := I.sigma fun i => I.sigma fun d => pairs (delta C i d) y h
  let code (x z : ℕ×ℕ) : Σ _ : ℕ, Σ _ : ℕ, ℕ := ⟨x.2,⟨z.2-x.2,z.1-y⟩⟩
  let tag (v : (ℕ×ℕ)×(ℕ×ℕ)) : (ℕ×ℕ) ⊕ (Bool × (Σ _ : ℕ, Σ _ : ℕ, ℕ)) :=
    if v.1.2=v.2.2 then .inl v.1 else if v.1.2<v.2.2 then .inr (true,code v.1 v.2)
    else .inr (false,code v.2 v.1)
  let recover (u : Σ _ : ℕ, Σ _ : ℕ, ℕ) : (ℕ×ℕ)×(ℕ×ℕ) :=
    ((y+u.2.2+delta C u.1 u.2.1,u.1),(y+u.2.2,u.1+u.2.1))
  let back : (ℕ×ℕ) ⊕ (Bool × (Σ _ : ℕ, Σ _ : ℕ, ℕ)) → (ℕ×ℕ)×(ℕ×ℕ) := fun v => match v with
    | .inl x => (x,x)
    | .inr (true,u) => recover u
    | .inr (false,u) => (recover u).swap
  have good {x z : ℕ×ℕ} (hx : x∈S) (hz : z∈S) (e : rep C x=rep C z) (lt : x.2<z.2) :
      code x z ∈ T ∧ recover (code x z)=(x,z) := by
    obtain ⟨xp,xi⟩ := Finset.mem_product.mp hx
    obtain ⟨zp,zi⟩ := Finset.mem_product.mp hz
    obtain ⟨pp,pl,pr⟩ := band_data xp
    obtain ⟨qp,ql,qr⟩ := band_data zp
    have ql' : y ≤ z.1 := ql.le
    have eq := reconstruct_sum hC e lt
    have dmem : z.2-x.2 ∈ I := Finset.mem_Icc.mpr ⟨by omega, (Nat.sub_le ..).trans (Finset.mem_Icc.mp zi).2⟩
    have el : y+(z.1-y)=z.1 := Nat.add_sub_of_le ql'
    have ej : x.2+(z.2-x.2)=z.2 := Nat.add_sub_of_le lt.le
    constructor
    · refine Finset.mem_sigma.mpr ⟨xi,Finset.mem_sigma.mpr ⟨dmem,Finset.mem_filter.mpr ⟨?_,?_,?_⟩⟩⟩
      · apply Finset.mem_range.mpr
        change z.1-y < 1024*y+1
        change z.1 ≤ 1024*y at qr
        omega
      · simpa only [code,el] using qp
      · simpa only [code,el,←eq] using pp
    · change ((y+(z.1-y)+delta C x.2 (z.2-x.2),x.2),(y+(z.1-y),x.2+(z.2-x.2)))=_
      simp only [el,ej,←eq]
  have mem {v : (ℕ×ℕ)×(ℕ×ℕ)} (hv : v∈collisions S (rep C)) :
      v.1∈S ∧ v.2∈S ∧ rep C v.1=rep C v.2 := by
    obtain ⟨h,e⟩ := Finset.mem_filter.mp hv
    exact ⟨(Finset.mem_product.mp h).1,(Finset.mem_product.mp h).2,e⟩
  have decode {v : (ℕ×ℕ)×(ℕ×ℕ)} (hv : v∈collisions S (rep C)) : back (tag v)=v := by
    obtain ⟨hx,hz,e⟩ := mem hv
    dsimp only [tag]
    split_ifs with l l'
    · have ev : v.1=v.2 := Prod.ext (by dsimp [rep] at e; rw [l] at e; omega) l
      exact Prod.ext rfl ev
    · exact (good hx hz e l').2
    · exact congrArg Prod.swap (good hz hx e.symm (by omega)).2
  have sb : (collisions S (rep C)).image tag ⊆ S.disjSum ((Finset.univ : Finset Bool) ×ˢ T) := by
    intro v hv
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hp,hq,e⟩ := mem hx
    dsimp only [tag]
    split_ifs with he hl
    · simpa using hp
    · simpa using (good hp hq e hl).1
    · simpa using (good hq hp e.symm (by omega)).1
  calc
    _ = ((collisions S (rep C)).image tag).card := (Finset.card_image_of_injOn (fun x hx z hz e =>
      (decode hx).symm.trans ((congrArg back e).trans (decode hz)))).symm
    _ ≤ _ := (Finset.card_le_card sb).trans_eq (by simp [T,I,h,y,S])

private theorem enough_results {C : ℕ} (hC : 1<C) :
    ∃ Q : ℝ, 0<Q ∧ ∀ᶠ k : ℕ in atTop, (Y (C*k):ℝ) ≤ Q*(result C k).card := by
  classical
  obtain ⟨A,ap,avg⟩ := shifted_loss hC
  let B := 1024+2*(8*zetaTwo^3)*1025*A
  let Q := (C:ℝ)^2*B
  have z0 : 0≤zetaTwo := tsum_nonneg fun _ => by positivity
  have bp : 0<B := by dsimp [B]; positivity
  have cp : (0:ℝ)<C := by exact_mod_cast (show 0<C by omega)
  have tc : Tendsto (fun k : ℕ => C*k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_left k (by omega : 0<C)) tendsto_id
  refine ⟨Q,mul_pos (sq_pos_of_pos cp) bp,?_⟩
  filter_upwards [tc.eventually band_size,eventually_ge_atTop 1] with k hb hk
  let L := C*k
  let y := Y L
  let R := (2:ℕ)^L
  let h := 1024*y+1
  let I := Icc 1 k
  let P (i d : ℕ) := pairs (delta C i d) y h
  have kpos : (0:ℝ)<k := by exact_mod_cast hk
  have r1 : 1<R := one_lt_pow₀ (by decide) (Nat.mul_ne_zero (by omega) (by omega))
  have y1 : (1:ℝ)≤y := by exact_mod_cast (show 0<y by dsimp [y,Y]; positivity)
  have y0 : (0:ℝ)<y := by linarith
  have yR : R^2<y := Nat.pow_lt_pow_right r1 (by decide)
  have yh : (R^2)^4 ≤ h := by
    rw [←pow_mul]
    have := Nat.pow_le_pow_right r1.le (by decide : 2*4 ≤ 16)
    change _ ≤ 1024*(R^16)+1
    omega
  have l : (k:ℝ)/2 ≤ Real.log (R+1:ℕ) := by
    have e : Real.log (R:ℝ)=L*Real.log 2 := by simp [R,Real.log_pow]
    have l := Real.log_le_log (by positivity : 0<(R:ℝ)) (show (R:ℝ) ≤ (R+1:ℕ) by exact_mod_cast Nat.le_succ R)
    have lk : (k:ℝ)≤L := by exact_mod_cast Nat.le_mul_of_pos_left k (Nat.zero_lt_of_lt hC)
    nlinarith [mul_le_mul_of_nonneg_left logtwo.1 (Nat.cast_nonneg L (α:=ℝ))]
  have k2 : (k:ℝ)^2 ≤ 4*Real.log (R+1:ℕ)^2 := by nlinarith [sq_le_sq' (by linarith) l]
  have hsum : (∑ i ∈ I,∑ d ∈ I,((P i d).card:ℝ)) ≤ (8*zetaTwo^3)*(h:ℝ)*A := by
    apply le_of_mul_le_mul_right _ (sq_pos_of_pos kpos)
    calc
      _ = ∑ i ∈ I, ∑ d ∈ I, ((P i d).card:ℝ)*k^2 := by simp only [Finset.sum_mul]
      _ ≤ ∑ i ∈ I, ∑ d ∈ I, (8*zetaTwo^3)*(h:ℝ)*loss (delta C i d) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro d hd
        have dt : 0<delta C i d := Nat.mul_pos (pow_pos (by omega) _) (Nat.sub_pos_of_lt
          (one_lt_pow₀ hC (by have := (Finset.mem_Icc.mp hd).1; omega)))
        have a := pair_bound dt r1.le yR yh
        change ((P i d).card:ℝ)*Real.log (R+1:ℕ)^2 ≤ _ at a
        nlinarith only [a,mul_le_mul_of_nonneg_left k2 (Nat.cast_nonneg (P i d).card (α:=ℝ))]
      _ = (8*zetaTwo^3)*(h:ℝ)*(∑ i ∈ I,∑ d ∈ I,loss (delta C i d)) := by simp only [Finset.mul_sum]
      _ ≤ _ := by
        have m := mul_le_mul_of_nonneg_left (avg k) (show 0≤8*zetaTwo^3*(h:ℝ) by positivity)
        dsimp [I,delta]
        nlinarith only [m]
  let S := source C k
  let D := collisions S (rep C)
  have size : (S.card:ℝ)=(band L).card*(k:ℝ) := by simp [S,source,Finset.card_product,L]
  have s0 : (y:ℝ) ≤ (C:ℝ)*S.card := by
    rw [size]
    have v := hb.1
    push_cast at v
    nlinarith only [v]
  have s1 : (S.card:ℝ) ≤ 1024*(y:ℝ) := by
    rw [size]
    apply le_trans _ hb.2
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact_mod_cast Nat.le_mul_of_pos_left k (Nat.zero_lt_of_lt hC)
  have d0 : (D.card:ℝ) ≤ B*(y:ℝ) := by
    have cl : (D.card:ℝ) ≤ S.card+2*∑ i ∈ I,∑ d ∈ I,((P i d).card:ℝ) := by exact_mod_cast ncollision hC k
    change (∑ i ∈ I,∑ d ∈ I,((P i d).card:ℝ)) ≤ (8*zetaTwo^3)*(h:ℝ)*A at hsum
    have hh : (h:ℝ) ≤ 1025*(y:ℝ) := by dsimp [h]; push_cast; linarith
    dsimp only [B]
    nlinarith only [cl,s1,hsum,mul_le_mul_of_nonneg_left hh (show 0≤8*zetaTwo^3*A by positivity)]
  have cs : (S.card:ℝ)^2 ≤ (result C k).card*(D.card:ℝ) := by exact_mod_cast fiber_count S (rep C)
  apply le_of_mul_le_mul_right _ y0
  dsimp only [Q]
  have u := mul_le_mul_of_nonneg_left cs (sq_nonneg (C:ℝ))
  have v := mul_le_mul_of_nonneg_left d0 (mul_nonneg (sq_nonneg (C:ℝ)) (Nat.cast_nonneg (result C k).card (α:=ℝ)))
  nlinarith only [u,v,pow_le_pow_left₀ y0.le s0 2]
private def represented (C : ℕ) : Set ℕ :=
  {v | ∃ p i : ℕ, p.Prime ∧ 2<p ∧ 0 < i ∧ v=p+C^i}

private noncomputable def upto (S : Set ℕ) (n : ℕ) : Finset ℕ := by
  classical exact (Finset.range n).filter (· ∈ S)

private theorem result_below {C k n : ℕ} (hC : 1<C) (hk : 1≤k)
    (big : 2048*Y (C*k) ≤ n) : result C k ⊆ upto (represented C) n := by
  classical
  intro v hv
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hp,hi⟩ := Finset.mem_product.mp hx
  obtain ⟨pp,pl,pr⟩ := band_data hp
  obtain ⟨ip,ik⟩ := Finset.mem_Icc.mp hi
  let y := Y (C*k)
  have y0 : 0<y := by dsimp [y,Y]; positivity
  have base : 2≤(2:ℕ)^(C*k) := one_lt_pow₀ (by decide : 1<(2:ℕ)) (Nat.mul_ne_zero (by omega : C≠0) (by omega : k≠0))
  have yp : (2:ℕ)^(C*k)≤y := Nat.le_self_pow (by decide) _
  have py : C^x.2≤y := by
    calc
      _ ≤ (2^C)^x.2 := Nat.pow_le_pow_left (Nat.lt_pow_self (by decide : 1<2)).le _
      _ ≤ (2^C)^k := Nat.pow_le_pow_right (by positivity) ik
      _ = 2^(C*k) := (pow_mul ..).symm
      _ ≤ _ := yp
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_range.mpr
    change x.1+C^x.2<n
    change x.1≤1024*y at pr
    change 2048*y≤n at big
    omega
  · exact ⟨x.1,x.2,pp,base.trans_lt (yp.trans_lt pl),ip,rfl⟩

private theorem positive_counts {C : ℕ} (hC : 1<C) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ n : ℕ in atTop, c*(n:ℝ)≤(upto (represented C) n).card := by
  obtain ⟨Q,qp,hQ⟩ := enough_results hC
  let b : ℕ := (2^C)^16
  have b1 : 1<b := one_lt_pow₀ (one_lt_pow₀ (by decide) (by omega : C≠0)) (by decide)
  have eq (k : ℕ) : Y (C*k)=b^k := by
    dsimp [Y,b]
    simp only [←pow_mul]
    congr 1
    ring
  let idx (n : ℕ) := Nat.log b (n/2048)
  have tend : Tendsto idx atTop atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro k
    refine ⟨b^k*2048,?_⟩
    intro n hn
    exact Nat.le_log_of_pow_le b1 ((Nat.le_div_iff_mul_le (by decide)).mpr hn)
  refine ⟨1/(2048*(b:ℝ)*Q),by positivity,?_⟩
  filter_upwards [tend.eventually hQ,tend.eventually_ge_atTop 1,eventually_ge_atTop 2048] with n hm hk hn
  let k := idx n
  have lo : 2048*Y (C*k)≤n := by
    rw [eq,mul_comm]
    exact (Nat.le_div_iff_mul_le (by decide)).mp (Nat.pow_log_le_self b (by omega : n/2048≠0))
  have hi : n ≤ 2048*b*Y (C*k) := by
    have a := (Nat.div_lt_iff_lt_mul (by decide : 0<2048)).mp (Nat.lt_pow_succ_log_self b1 (n/2048))
    change n < b^(k+1)*2048 at a
    rw [pow_succ] at a
    rw [eq]
    nlinarith only [a]
  have su : ((result C k).card:ℝ)≤(upto (represented C) n).card := by exact_mod_cast Finset.card_le_card (result_below hC hk lo)
  have hi' : (n:ℝ)≤2048*(b:ℝ)*(Y (C*k):ℝ) := by exact_mod_cast hi
  change (Y (C*k):ℝ)≤Q*(result C k).card at hm
  rw [one_div_mul_eq_div,div_le_iff₀ (by positivity)]
  nlinarith only [hi',mul_le_mul_of_nonneg_left hm (show 0≤2048*(b:ℝ) by positivity),
    mul_le_mul_of_nonneg_left su (show 0≤2048*(b:ℝ)*Q by positivity)]

private theorem density_real {S : Set ℕ} {c : ℝ} (hc : 0<c)
    (h : ∀ᶠ n : ℕ in atTop, c*n ≤ (upto S n).card) : 0 < S.lowerDensity := by
  classical
  apply hc.trans_le
  change c ≤ atTop.liminf (fun n : ℕ => S.partialDensity Set.univ n)
  apply le_liminf_of_le (IsBoundedUnder.isCoboundedUnder_ge (u:=fun n : ℕ => S.partialDensity Set.univ n)
    ⟨1,by simpa only [eventually_map] using (Eventually.of_forall (fun n : ℕ => Set.partialDensity_le_one S Set.univ n) : ∀ᶠ n : ℕ in atTop, S.partialDensity Set.univ n ≤ 1)⟩)
  filter_upwards [h,eventually_ge_atTop 1] with n hn h1
  have eq : (↑(upto S n):Set ℕ)=S ∩ Set.Iio n := by
    ext i
    simp [upto,and_comm]
  have ne : (0:ℝ)<n := by exact_mod_cast h1
  have eq' : (S ∩ Set.Iio n).ncard=(upto S n).card := by rw [←eq,Set.ncard_coe_finset]
  have en : (Set.Iio n).ncard=n := by rw [←Finset.coe_range,Set.ncard_coe_finset,Finset.card_range]
  simpa only [Set.partialDensity,Set.inter_univ,Set.univ_inter,eq',en] using (le_div_iff₀ ne).mpr hn

private theorem mono_upto {S T : Set ℕ} (h : S ⊆ T) (n : ℕ) : (upto S n).card ≤ (upto T n).card := by
  classical
  apply Finset.card_le_card
  intro a ha
  obtain ⟨ha,hS⟩ := Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨ha,h hS⟩

end PairWindows

theorem OMA.solution : type_of% @Erdos244.erdos_244.variants.Romanoff := by
  intro C hC
  obtain ⟨c,hc,lower⟩ := PairWindows.positive_counts hC
  apply PairWindows.density_real hc
  filter_upwards [lower] with n hn
  apply hn.trans
  exact_mod_cast PairWindows.mono_upto (S:=PairWindows.represented C)
    (T:={p + ⌊C^k⌋₊ | (p : ℕ) (k : ℕ) (_ : p.Prime)}) (by
      intro v hv
      obtain ⟨p,i,pp,_,_,e⟩ := hv
      exact ⟨p,i,pp,by simp [e]⟩) n