import FormalConjectures.ErdosProblems.«968»
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Chebyshev

/-! The total variation of normalized consecutive primes.

A two-residue sieve ensures that each geometric block contributes variation
at least proportional to the logarithm of its scale. The positivity of prime
gaps gives the corresponding upper bound. Summing over blocks and comparing
the index of a prime with its size gives the square-logarithmic order. -/

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


private theorem divisor_box (N : ℕ) (f : ℕ → ℕ → ℝ) (hf : ∀ a b, 0 ≤ f a b) :
    ∑ n ∈ Icc 1 N, ∑ a ∈ n.divisors, f a (n/a) ≤
    ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 (N/a), f a b := by
  classical
  let I := Icc 1 N
  let S := I.sigma fun n : ℕ => n.divisors
  let T := I.sigma fun a : ℕ => Icc 1 (N/a)
  let pair (z : Σ _ : ℕ, ℕ) : Σ _ : ℕ, ℕ := ⟨z.2,z.1/z.2⟩
  have recon {z : Σ _ : ℕ, ℕ} (hz : z ∈ S) : (pair z).1*(pair z).2=z.1 := by
    exact Nat.mul_div_cancel' (Nat.mem_divisors.mp (Finset.mem_sigma.mp hz).2).1
  have inj : Set.InjOn pair ↑S := by
    intro x hx y hy h
    have h₂ := congrArg Sigma.fst h
    have h₁ := congrArg (fun z : Σ _ : ℕ, ℕ => z.1*z.2) h
    change (pair x).1*(pair x).2=(pair y).1*(pair y).2 at h₁
    rw [recon hx, recon hy] at h₁
    cases x; cases y; simp_all [pair]
  have sub : S.image pair ⊆ T := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hxN,hxa⟩ := Finset.mem_sigma.mp hx
    obtain ⟨ha,hn⟩ := Nat.mem_divisors.mp hxa
    have a0 : 0 < x.2 := Nat.pos_of_mem_divisors hxa
    have aN := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ha
    have nN := (Finset.mem_Icc.mp hxN).2
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨a0,aN.trans nN⟩,
      Finset.mem_Icc.mpr ⟨Nat.div_pos aN a0,Nat.div_le_div_right nN⟩⟩
  calc
    _ = ∑ x ∈ S, f (pair x).1 (pair x).2 := by rw [Finset.sum_sigma]
    _ = ∑ z ∈ S.image pair, f z.1 z.2 := by rw [Finset.sum_image inj]
    _ ≤ ∑ z ∈ T, f z.1 z.2 := Finset.sum_le_sum_of_subset_of_nonneg sub (fun z _ _ => hf ..)
    _ = _ := by rw [Finset.sum_sigma]



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


private def Y (k : ℕ) : ℕ := (2^k)^16


private theorem logY (k : ℕ) : Real.log (Y k:ℝ)=16*k*Real.log 2 := by
  simp [Y,Real.log_pow]
  ring

private theorem Y_big : Tendsto Y atTop atTop := by
  have h : Tendsto (fun k : ℕ => (2:ℕ)^k) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt (by decide)
  apply tendsto_atTop_mono (f:=fun k : ℕ => 2^k) _ h
  intro k
  exact Nat.le_self_pow (by decide) _

private theorem logtwo : (1/2:ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · convert Real.one_sub_inv_le_log_of_pos (x:=(2:ℝ)) (by norm_num) using 1
    norm_num
  · convert Real.log_le_sub_one_of_pos (x:=(2:ℝ)) (by norm_num) using 1
    norm_num



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



set_option maxHeartbeats 800000 in
private theorem loss_two (H : ℕ) :
    ∑ s ∈ Icc 1 H, (s.divisors.card:ℝ)/(s:ℝ)^2 ≤ zetaTwo^2 := by
  let I := Icc 1 H
  have zbound (s : Finset ℕ) : ∑ a ∈ s, 1/(a:ℝ)^2 ≤ zetaTwo :=
    (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).sum_le_tsum s (fun _ _ => by positivity)
  have hZ : 0 ≤ zetaTwo := tsum_nonneg fun _ => by positivity
  calc
    _ = ∑ s ∈ I, ∑ a ∈ s.divisors, (1/(a:ℝ)^2)*(1/((s/a:ℕ):ℝ)^2) := by
      apply Finset.sum_congr rfl
      intro s hs
      have h (a : ℕ) (ha : a ∈ s.divisors) : (1/(a:ℝ)^2)*(1/((s/a:ℕ):ℝ)^2) = 1/(s:ℝ)^2 := by
        have e : (a:ℝ)*((s/a:ℕ):ℝ) = (s:ℝ) := by exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp ha).1
        rw [div_mul_div_comm,one_mul,←mul_pow,e]
      rw [Finset.sum_congr rfl h]
      simp [div_eq_mul_inv]
    _ ≤ ∑ a ∈ I, ∑ b ∈ Icc 1 (H/a), (1/(a:ℝ)^2)*(1/(b:ℝ)^2) :=
      divisor_box H (fun a b => (1/(a:ℝ)^2)*(1/(b:ℝ)^2)) (fun _ _ => by positivity)
    _ ≤ ∑ a ∈ I, (1/(a:ℝ)^2)*zetaTwo := by
      apply Finset.sum_le_sum
      intro a _
      rw [←Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (zbound _) (by positivity)
    _ ≤ _ := by rw [←Finset.sum_mul,pow_two]; exact mul_le_mul_of_nonneg_right (zbound I) hZ

set_option maxHeartbeats 800000 in
private theorem loss_one (H : ℕ) :
    ∑ s ∈ Icc 1 H, (s.divisors.card:ℝ)/(s:ℝ) ≤ (1+Real.log H)^2 := by
  classical
  let I := Icc 1 H
  have hsum : ∑ a ∈ I, (a:ℝ)⁻¹ ≤ 1+Real.log H := by
    simpa only [I,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using harmonic_le_one_add_log H
  have hn : 0 ≤ ∑ a ∈ I, (a:ℝ)⁻¹ := Finset.sum_nonneg fun _ _ => by positivity
  calc
    _ = ∑ s ∈ I, ∑ a ∈ s.divisors, (a:ℝ)⁻¹*((s/a:ℕ):ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro s _
      have h (a : ℕ) (ha : a ∈ s.divisors) : (a:ℝ)⁻¹*((s/a:ℕ):ℝ)⁻¹ = (s:ℝ)⁻¹ := by
        rw [← mul_inv]
        congr 1
        exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp ha).1
      rw [Finset.sum_congr rfl h]
      simp [div_eq_mul_inv]
    _ ≤ ∑ a ∈ I, ∑ b ∈ Icc 1 (H/a), (a:ℝ)⁻¹*(b:ℝ)⁻¹ :=
      divisor_box H (fun a b => (a:ℝ)⁻¹*(b:ℝ)⁻¹) (fun _ _ => by positivity)
    _ ≤ ∑ a ∈ I, (a:ℝ)⁻¹*∑ b ∈ I, (b:ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro a _
      rw [←Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (Nat.div_le_self ..)) (fun _ _ _ => by positivity)
    _ ≤ _ := by rw [←Finset.sum_mul,←sq]; exact pow_le_pow_left₀ hn hsum 2

private theorem multiples_window (a w s : ℕ) (hs : 0<s) :
    (((Ioc a (a+w)).filter (s ∣ ·)).card:ℝ) ≤ (w:ℝ)/s+1 := by
  classical
  let F (v : ℕ) := (Ioc 0 v).filter (s ∣ ·)
  let S := (Ioc a (a+w)).filter (s ∣ ·)
  have join : F a ∪ S = F (a+w) := by ext t; simp [F,S]; omega
  have dis : Disjoint (F a) S := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have h := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hx).1).2
    have h' := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hy).1).1
    omega
  have he := Finset.card_union_of_disjoint dis
  rw [join] at he
  dsimp [F] at he
  simp only [Nat.Ioc_filter_dvd_card_eq_div] at he
  have hu := Nat.div_mul_le_self (a+w) s
  have hl := Nat.mod_add_div a s
  rw [Nat.mul_comm s (a/s)] at hl
  have hm := Nat.mod_lt a hs
  have hnat : S.card*s ≤ w+s := by
    rw [he,Nat.add_mul] at hu
    omega
  have hreal : (S.card:ℝ)*s ≤ w+s := by exact_mod_cast hnat
  change (S.card:ℝ) ≤ _
  have hsp : (0:ℝ)<s := by exact_mod_cast hs
  calc
    _ ≤ ((w:ℝ)+s)/s := (le_div_iff₀ hsp).2 hreal
    _ = _ := by field_simp

private theorem loss_window (a w : ℕ) : ∑ t ∈ Ioc a (a+w), loss t ≤
    w*zetaTwo^2 + (1+Real.log (a+w:ℕ))^2 := by
  classical
  let I := Icc 1 (a+w)
  let J := Ioc a (a+w)
  let f (s : ℕ) : ℝ := (s.divisors.card:ℝ)/s
  have eq (t : ℕ) (ht : t∈J) : I.filter (· ∣ t)=t.divisors := by
    obtain ⟨hl,hu⟩ := Finset.mem_Ioc.mp ht
    ext s
    simp only [I,Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
    constructor
    · rintro ⟨_,hd⟩; exact ⟨hd,by omega⟩
    · rintro ⟨hd,_⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega),(Nat.le_of_dvd (by omega) hd).trans hu⟩,hd⟩
  have row (t : ℕ) (ht : t∈J) :
      loss t = ∑ s ∈ I, if s∣t then f s else 0 := by rw [←Finset.sum_filter,eq t ht]; rfl
  calc
    _ = ∑ t ∈ J, ∑ s ∈ I, if s∣t then f s else 0 := Finset.sum_congr rfl row
    _ = ∑ s ∈ I, ∑ t ∈ J, if s∣t then f s else 0 := Finset.sum_comm
    _ ≤ ∑ s ∈ I, ((w:ℝ)/s+1)*f s := by
      apply Finset.sum_le_sum
      intro s hs
      rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (multiples_window a w s (Finset.mem_Icc.mp hs).1) (by dsimp [f]; positivity)
    _ = (w:ℝ)*(∑ s ∈ I, (s.divisors.card:ℝ)/(s:ℝ)^2) + ∑ s ∈ I, f s := by
      rw [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _
      dsimp [f]; ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (loss_two _) (by positivity)) (loss_one _)


private def X (k : ℕ) : ℕ := 134217728*k*Y k

private theorem y_pos (k : ℕ) : 0 < Y k := by unfold Y; positivity

private theorem y_step (k : ℕ) : Y (k+1) = 65536*Y k := by
  unfold Y; rw [pow_succ 2 k,mul_pow]; ring

private theorem prime_upper : ∀ᶠ k : ℕ in atTop, ∀ i ≤ 65536*Y k, Nat.nth Nat.Prime i ≤ X k := by
  have yk (k : ℕ) : k ≤ Y k := (Nat.lt_two_pow_self.le.trans (Nat.le_self_pow (by decide : 16≠0) _))
  have xge (k : ℕ) (hk : 1≤k) : Y k ≤ X k := by unfold X; nlinarith [y_pos k]
  have xt : Tendsto X atTop atTop := tendsto_atTop_mono' atTop
    ((eventually_ge_atTop 1).mono fun k hk => xge k hk) Y_big
  have tx : Tendsto (fun k : ℕ => (X k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp xt
  filter_upwards [tx.eventually many_primes,Y_big.eventually_ge_atTop 134217728,eventually_ge_atTop 1] with k hm hy hk i hi
  rw [Nat.floor_natCast] at hm
  have xcube : X k ≤ Y k ^ 3 := by
    unfold X; rw [pow_succ,pow_two]; gcongr; exact yk k
  have y : (0:ℝ)<Y k := by exact_mod_cast y_pos k
  have kr : (0:ℝ)<k := by exact_mod_cast hk
  have x : (0:ℝ)<X k := by exact_mod_cast (y_pos k).trans_le (xge k hk)
  have hlog := Real.log_le_log x (show (X k:ℝ) ≤ (Y k:ℝ)^3 by exact_mod_cast xcube)
  rw [Real.log_pow,logY] at hlog
  norm_num at hlog
  have hlu : Real.log (X k:ℝ) ≤ 48*k := by nlinarith [mul_le_mul_of_nonneg_left logtwo.2 kr.le]
  have hcount : 65536*Y k < (X k).primeCounting := by
    by_contra! hc
    have hcr : ((X k).primeCounting:ℝ) ≤ 65536*(Y k:ℝ) := by exact_mod_cast hc
    have hxp : (X k:ℝ)=134217728*(k:ℝ)*(Y k:ℝ) := by simp [X]
    have lo := mul_le_mul_of_nonneg_left logtwo.1 x.le
    have up := mul_le_mul_of_nonneg_left hlu (Nat.cast_nonneg (X k).primeCounting (α:=ℝ))
    have mid := mul_le_mul_of_nonneg_right hcr (show (0:ℝ)≤48*k by positivity)
    have chain := hm.trans (up.trans mid)
    rw [hxp] at lo chain
    nlinarith only [lo,chain,mul_pos kr y]
  exact Nat.le_of_lt_succ (Nat.nth_lt_of_lt_count (hi.trans_lt hcount))

private def step (i : ℕ) : ℝ := Erdos968.u (i+1)-Erdos968.u i
private def gap (i : ℕ) : ℕ := Nat.nth Nat.Prime (i+1) - Nat.nth Nat.Prime i
private def variation (a b : ℕ) : ℝ := ∑ i ∈ Ico a b, |step i|

private theorem gap_eq (i : ℕ) : (gap i:ℝ)=Erdos968.u i + (i+2)*step i := by
  have h := (Nat.nth_strictMono Nat.infinite_setOfPred_prime) (Nat.lt_succ_self i)
  unfold gap step Erdos968.u
  rw [Nat.cast_sub h.le]
  push_cast
  field_simp
  ring

private theorem u_nonneg (i : ℕ) : 0 ≤ Erdos968.u i := by unfold Erdos968.u; positivity

private theorem u_bound {k i : ℕ} (hi : Y k ≤ i) (hp : Nat.nth Nat.Prime i ≤ X k) :
    Erdos968.u i ≤ 134217728*(k:ℝ) := by
  unfold Erdos968.u
  apply (div_le_iff₀ (by positivity)).2
  have h : (Nat.nth Nat.Prime i:ℝ) ≤ 134217728*(k:ℝ)*Y k := by exact_mod_cast hp
  have hy : (Y k:ℝ) ≤ i+1 := by exact_mod_cast (show Y k ≤ i+1 by omega)
  exact h.trans (mul_le_mul_of_nonneg_left hy (by positivity))

private theorem step_sum {a b : ℕ} (h : a≤b) : ∑ i ∈ Ico a b, step i = Erdos968.u b-Erdos968.u a := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ b hb ih => rw [Finset.sum_Ico_succ_top hb,ih,step]; ring

private theorem drift {a i b : ℕ} (ha : a ≤ i) (hb : i ≤ b) :
    |Erdos968.u i-Erdos968.u a| ≤ variation a b := by
  rw [←step_sum ha]
  exact (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Ico_subset_Ico_right hb) (fun _ _ _ => abs_nonneg _))


private theorem small_error (B q : ℝ) (hB : 0<B) (hq : 0<q) :
    ∀ᶠ k : ℕ in atTop, ∀ t : ℕ, 1≤t → (t:ℝ)≤B*k → (1+Real.log t)^2 ≤ q*k := by
  have tend : Tendsto (fun k : ℕ => B*(k:ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hB tendsto_natCast_atTop_atTop
  have dl := (Real.isLittleO_pow_log_id_atTop (n:=2)).bound (show 0<q/(4*B) by positivity)
  filter_upwards [tend.eventually dl,tend.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 1),
    eventually_ge_atTop 1] with k he hlarge hk t ht hb
  have k0 : (0:ℝ)<k := by exact_mod_cast hk
  have l0 : 0≤Real.log t := Real.log_nonneg (by exact_mod_cast ht)
  have l1 : Real.log t ≤ Real.log (B*k) := Real.log_le_log (by positivity) hb
  simp only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.log (B*k))),id_eq,abs_of_pos (mul_pos hB k0)] at he
  have e : q/(4*B)*(B*k)=q*k/4 := by field_simp
  rw [e] at he
  nlinarith only [he,pow_le_pow_left₀ (by linarith : 0 ≤ 1+Real.log t)
    (by linarith : 1+Real.log t ≤ 2*Real.log (B*k)) 2]

private noncomputable def smallSteps (M : ℕ) (v : ℝ) : Finset ℕ := by
  classical exact (Ico M (2*M)).filter fun i => |step i| *M ≤ 2*v

private theorem many_small {M : ℕ} {v : ℝ} (hm : 0<M) (hv : 0<v)
    (h : variation M (2*M) < v) : (M:ℝ) ≤ 2*(smallSteps M v).card := by
  classical
  let I := Ico M (2*M)
  let S := smallSteps M v
  let T := I \ S
  have sub : S⊆I := Finset.filter_subset ..
  have ht (i : ℕ) (hi : i∈T) : 2*v ≤ |step i| *M := by
    obtain ⟨hi,hn⟩ := Finset.mem_sdiff.mp hi
    exact le_of_lt (lt_of_not_ge fun he => hn (Finset.mem_filter.mpr ⟨hi,he⟩))
  have he : (T.card:ℝ)*(2*v) ≤ variation M (2*M)*M := by
    calc
      _ = ∑ _i ∈ T, 2*v := by simp
      _ ≤ ∑ i ∈ T, |step i| *M := Finset.sum_le_sum ht
      _ ≤ _ := by
        rw [←Finset.sum_mul]
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => abs_nonneg _)
  have c : T.card+S.card=M := (Finset.card_sdiff_add_card_eq_card sub).trans (by simp [I]; omega)
  have cr : (T.card:ℝ)+S.card=M := by exact_mod_cast c
  have cm := mul_lt_mul_of_pos_right h (show (0:ℝ)<M by exact_mod_cast hm)
  have ct : 2*(T.card:ℝ)<M := (mul_lt_mul_iff_left₀ hv).mp (by nlinarith only [he,cm])
  change (M:ℝ) ≤ 2*(S.card:ℝ)
  linarith

private theorem gap_window {M : ℕ} {v : ℝ} (_hm : 0<M) (hv : 0<v)
    (h : variation M (2*M) < v) {i : ℕ} (hi : i∈smallSteps M v) :
    ⌊Erdos968.u M-8*v⌋₊ < gap i ∧ gap i ≤ ⌊Erdos968.u M+8*v⌋₊+1 := by
  classical
  obtain ⟨hx,hd⟩ := Finset.mem_filter.mp hi
  obtain ⟨hl,hu⟩ := Finset.mem_Ico.mp hx
  have near := (drift hl hu.le).trans_lt h
  have ir : (i:ℝ)+2 ≤ 3*(M:ℝ) := by exact_mod_cast (show i+2≤3*M by omega)
  have diff : |(i+2:ℝ)*step i| ≤ 6*v := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤(i:ℝ)+2)]
    nlinarith only [hd,mul_le_mul_of_nonneg_right ir (abs_nonneg (step i))]
  have g0 : 0<gap i := Nat.sub_pos_of_lt ((Nat.nth_strictMono Nat.infinite_setOfPred_prime) (Nat.lt_succ_self i))
  obtain ⟨l,r⟩ := abs_lt.mp near
  obtain ⟨sl,sr⟩ := abs_le.mp diff
  constructor
  · apply (Nat.floor_lt' g0.ne').2
    rw [gap_eq]; linarith
  · apply Nat.le_succ_of_le
    apply Nat.le_floor
    rw [gap_eq]; linarith

private theorem sieve_steps {k a w : ℕ} (S : Finset ℕ)
    (hs : ∀ i∈S, Y k ≤ i ∧ Nat.nth Nat.Prime i ≤ X k ∧ gap i ∈ Ioc a (a+w))
    (hk : 1≤k) :
    (S.card:ℝ)*(k:ℝ)^2 ≤ 8*zetaTwo^3*(X k)*(w*zetaTwo^2+(1+Real.log (a+w:ℕ))^2) := by
  classical
  let R : ℕ := 2^k
  let M := Y k
  let H := X k
  let G := Ioc a (a+w)
  let P := G.sigma (fun t => pairs t M H)
  let tag (i : ℕ) : Σ _ : ℕ, ℕ := ⟨gap i,Nat.nth Nat.Prime i-M⟩
  have inj : Set.InjOn tag ↑S := by
    intro i hi j hj he
    have h := congrArg (fun z : Σ _ : ℕ, ℕ => z.2) he
    have hi' := (hs i hi).1.trans ((Nat.le_add_right i 2).trans (Nat.add_two_le_nth_prime i))
    have hj' := (hs j hj).1.trans ((Nat.le_add_right j 2).trans (Nat.add_two_le_nth_prime j))
    change Nat.nth Nat.Prime i-Y k=Nat.nth Nat.Prime j-Y k at h
    have eq : Nat.nth Nat.Prime i = Nat.nth Nat.Prime j := by omega
    exact (Nat.nth_strictMono (p:=Nat.Prime) Nat.infinite_setOfPred_prime).injective eq
  have sub : S.image tag ⊆ P := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hM,hH,hG⟩ := hs i hi
    have mp := hM.trans ((Nat.le_add_right i 2).trans (Nat.add_two_le_nth_prime i))
    have hh : Nat.nth Nat.Prime i-M<H := by
      dsimp [M,H]; have hy := y_pos k; omega
    have pn (n : ℕ) : (Nat.nth Nat.Prime n).Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n
    have succ := (Nat.nth_strictMono Nat.infinite_setOfPred_prime) (Nat.lt_succ_self i)
    refine Finset.mem_sigma.mpr ⟨hG,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh,?_,?_⟩⟩
    · simpa only [tag,M,Nat.add_sub_of_le mp] using pn i
    · simpa only [tag,M,gap,Nat.add_sub_of_le mp,Nat.add_sub_of_le succ.le] using pn (i+1)
  have cardn : S.card ≤ ∑ t ∈ G, (pairs t M H).card := by
    rw [←Finset.card_sigma,←Finset.card_image_of_injOn inj]; exact Finset.card_le_card sub
  have cardr : (S.card:ℝ) ≤ ∑ t ∈ G, ((pairs t M H).card:ℝ) := by exact_mod_cast cardn
  have r1 : 1<R := one_lt_pow₀ (by decide) (by omega : k≠0)
  have corners : R^2 < M ∧ (R^2)^4 ≤ H := by
    have e : (R^2)^4=R^8 := (pow_mul ..).symm
    have mh : M≤H := by dsimp [H,X,M]; nlinarith [y_pos k]
    exact ⟨pow_lt_pow_right₀ r1 (by decide : 2<16), e ▸ (pow_le_pow_right₀ r1.le (by decide : 8≤16)).trans mh⟩
  have lr : (k:ℝ)/2 ≤ Real.log (R+1:ℕ) := by
    have e : Real.log (R:ℝ) = k*Real.log 2 := by simp [R,Real.log_pow]
    have h := Real.log_le_log (by positivity : 0<(R:ℝ)) (by exact_mod_cast Nat.le_add_right R 1 : (R:ℝ) ≤ (R+1:ℕ))
    rw [e] at h
    nlinarith only [h,mul_le_mul_of_nonneg_left logtwo.1 (Nat.cast_nonneg k (α:=ℝ))]
  have z : 0≤zetaTwo := tsum_nonneg (fun _ => by positivity)
  have each (t : ℕ) (ht : t∈G) : ((pairs t M H).card:ℝ)* (k:ℝ)^2 ≤ 8*zetaTwo^3*(X k)*loss t := by
    have f := pair_bound (t:=t) (R:=R) (start:=M) (h:=H) (by have l := (Finset.mem_Ioc.mp ht).1; omega) r1.le corners.1 corners.2
    change _ ≤ _*(X k:ℝ)*_ at f
    have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) lr 2) (Nat.cast_nonneg (pairs t M H).card (α:=ℝ))
    nlinarith only [h,f]
  calc
    _ ≤ (∑ t ∈ G, ((pairs t M H).card:ℝ))*(k:ℝ)^2 := mul_le_mul_of_nonneg_right cardr (sq_nonneg _)
    _ ≤ ∑ t ∈ G, 8*zetaTwo^3*(X k)*loss t := by rw [Finset.sum_mul]; exact Finset.sum_le_sum each
    _ ≤ _ := by rw [←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (loss_window a w) (by positivity)


private theorem block_lower : ∃ δ : ℝ, 0<δ ∧ ∀ᶠ k : ℕ in atTop,
    δ*k ≤ variation (Y k) (2*Y k) := by
  let D := 1+8*zetaTwo^3*134217728
  let W := 1+zetaTwo^2
  let δ := 1/(1000*D*W)
  have z : (0:ℝ)≤zetaTwo := tsum_nonneg (fun _ => by positivity)
  have d1 : (1:ℝ)≤D := by exact le_add_of_nonneg_right (by positivity)
  have w1 : (1:ℝ)≤W := by exact le_add_of_nonneg_right (sq_nonneg _)
  have dp : 0<D := by linarith
  have wp : 0<W := by linarith
  have small : 0<δ := by dsimp [δ]; positivity
  have ds : δ≤1 := by
    apply (div_le_iff₀ (by positivity : 0<1000*D*W)).2
    nlinarith only [d1,w1,mul_nonneg (sub_nonneg.mpr d1) (sub_nonneg.mpr w1)]
  have kt : Tendsto (fun k : ℕ => δ*(k:ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop small tendsto_natCast_atTop_atTop
  refine ⟨δ,small,?_⟩
  filter_upwards [prime_upper,kt.eventually_ge_atTop 1,eventually_ge_atTop 1,
    small_error 134217739 δ (by norm_num) small] with k hp hv hk he
  by_contra! h
  let M := Y k
  let v := δ*(k:ℝ)
  let u := Erdos968.u M
  let S := smallSteps M v
  let a := ⌊u-8*v⌋₊
  let b := ⌊u+8*v⌋₊+1
  let w := b-a
  have mp : 0<M := y_pos k
  have kr : (0:ℝ)<k := by exact_mod_cast hk
  have vp : 0<v := mul_pos small kr
  have un : 0≤u := u_nonneg _
  have ub : u≤134217728*(k:ℝ) := u_bound le_rfl (hp M (by dsimp [M]; omega))
  have ab : a≤b := Nat.le_succ_of_le (Nat.floor_mono (by linarith : u-8*v≤u+8*v))
  have aw : a+w=b := Nat.add_sub_of_le ab
  have bl : (b:ℝ)≤u+8*v+1 := by dsimp [b]; push_cast; linarith [Nat.floor_le (by linarith : 0≤u+8*v)]
  have bound : (b:ℝ)≤134217739*k := by
    have s := mul_le_mul_of_nonneg_right ds kr.le
    dsimp [v] at bl; have kk : (1:ℝ)≤k := by exact_mod_cast hk
    linarith
  have err : (1+Real.log (a+w:ℕ))^2 ≤ v := by rw [aw]; exact he b (by dsimp [b]; omega) bound
  have width : (w:ℝ)≤18*v := by
    have lower := Nat.lt_floor_add_one (u-8*v)
    change _ < (a:ℝ)+1 at lower
    have wb : (a:ℝ)+w=b := by exact_mod_cast aw
    change 1≤v at hv
    linarith
  have mass : w*zetaTwo^2+(1+Real.log (a+w:ℕ))^2 ≤ 19*W*v := by
    have l := mul_le_mul_of_nonneg_right width (sq_nonneg zetaTwo)
    dsimp [W]
    nlinarith only [l,err,vp,sq_nonneg zetaTwo,mul_nonneg vp.le (sq_nonneg zetaTwo)]
  have count := many_small mp vp h
  change (M:ℝ) ≤ 2*(S.card:ℝ) at count
  have freq := sieve_steps (k:=k) (a:=a) (w:=w) S (by
    intro i hi
    obtain ⟨hmi,hiM⟩ := Finset.mem_Ico.mp (Finset.mem_filter.mp hi).1
    refine ⟨hmi,hp i (by change i<2*Y k at hiM; omega),?_⟩
    rw [aw]
    exact Finset.mem_Ioc.mpr (gap_window mp vp h hi)) hk
  have f : (8*zetaTwo^3*(X k):ℝ) ≤ D*(k:ℝ)*M := by
    have x : (X k:ℝ) = 134217728*(k:ℝ)*M := by simp [X,M]
    rw [x]; dsimp [D]
    nlinarith only [mul_nonneg kr.le (Nat.cast_nonneg M (α:=ℝ))]
  have frac : D*(k:ℝ)*M*(19*W*v) = (19/1000:ℝ)*M*(k:ℝ)^2 := by
    dsimp [v,δ]; field_simp
  have cap : (S.card:ℝ)*(k:ℝ)^2 ≤ (19/1000:ℝ)*M*(k:ℝ)^2 := by
    rw [←frac]
    exact freq.trans (mul_le_mul f mass (by positivity) (by positivity))
  have lo := mul_le_mul_of_nonneg_right count (sq_nonneg (k:ℝ))
  have m0 : (0:ℝ)<M := by exact_mod_cast mp
  nlinarith only [lo,cap,mul_pos m0 (sq_pos_of_pos kr)]


private theorem y_pow (k : ℕ) : Y k=65536^k := by
  induction k with
  | zero => simp [Y]
  | succ k ih => rw [y_step,ih,pow_succ,mul_comm]

private theorem y_mono : Monotone Y := by
  intro i j h; rw [y_pow,y_pow]; exact Nat.pow_le_pow_right (by decide) h

private theorem var_span {δ : ℝ} (hd : 0≤δ) {k : ℕ}
    (h : ∀ j≥k, δ*j ≤ variation (Y j) (2*Y j)) (L : ℕ) :
    L*(δ*k) ≤ variation (Y k) (Y (k+L)) := by
  induction L with
  | zero => simp [variation]
  | succ L ih =>
    have hj := h (k+L) (by omega)
    have hz : 2*Y (k+L) ≤ Y (k+L+1) := by rw [y_step]; omega
    have hpart : variation (Y (k+L)) (2*Y (k+L)) ≤ variation (Y (k+L)) (Y (k+L+1)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right hz) (fun _ _ _ => abs_nonneg _)
    have whole : variation (Y k) (Y (k+L)) + variation (Y (k+L)) (Y (k+L+1)) =
        variation (Y k) (Y (k+L+1)) := Finset.sum_Ico_consecutive _ (y_mono (by omega)) (y_mono (by omega))
    push_cast at hj ⊢
    rw [←Nat.add_assoc k L 1]
    nlinarith only [ih,hj,hpart,whole,mul_nonneg hd (Nat.cast_nonneg L (α:=ℝ))]

private def down : Set ℕ := {i | Erdos968.u i > Erdos968.u (i+1)}

private noncomputable def upto (S : Set ℕ) (n : ℕ) : Finset ℕ := by
  classical exact (range n).filter (· ∈ S)

private theorem down_ineq {a i H : ℕ} (ha : 0<a) (hi : a ≤ i)
    (hp : Nat.nth Nat.Prime i ≤ H) (dec : i∈down) :
    -step i ≤ (H:ℝ)/(a:ℝ)^2 := by
  have neg : step i<0 := sub_neg.mpr dec
  have e := gap_eq i
  have g0 := Nat.cast_nonneg (gap i) (α:=ℝ)
  have g : (-step i)*((i:ℝ)+2) ≤ Erdos968.u i := by linarith only [e,g0]
  have p : Erdos968.u i*((i:ℝ)+1) ≤ H := by
    unfold Erdos968.u; rw [div_mul_cancel₀ _ (by positivity)]; exact_mod_cast hp
  have s : (a:ℝ)^2 ≤ ((i:ℝ)+2)*(i+1) := by
    rw [sq]; apply mul_le_mul <;> first | positivity | exact_mod_cast (show a ≤ i+2 by omega) | exact_mod_cast (show a ≤ i+1 by omega)
  have ar : (0:ℝ)<a := by exact_mod_cast ha
  apply (le_div_iff₀ (sq_pos_of_pos ar)).2
  nlinarith only [mul_le_mul_of_nonneg_left s (neg_nonneg.mpr neg.le),
    mul_le_mul_of_nonneg_right g (by positivity : (0:ℝ) ≤ i+1),p]

private theorem var_upper {a b H : ℕ} (ha : 0<a) (hab : a≤b)
    (hp : ∀ i∈Ico a b, Nat.nth Nat.Prime i ≤ H) :
    variation a b ≤ Erdos968.u b+2*((H:ℝ)/(a:ℝ)^2)*(upto down b).card := by
  classical
  let I := Ico a b
  let c := 2*((H:ℝ)/(a:ℝ)^2)
  have cp : 0≤c := by dsimp [c]; positivity
  have each (i : ℕ) (hi : i∈I) : |step i| ≤ step i+(if i∈down then c else 0) := by
    by_cases h : i∈down
    · have neg : step i<0 := sub_neg.mpr h
      rw [if_pos h,abs_of_neg neg]
      have d := down_ineq ha (Finset.mem_Ico.mp hi).1 (hp i hi) h
      dsimp [c]; linarith
    · have nn : 0≤ step i := sub_nonneg.mpr (le_of_not_gt h)
      simp [h,abs_of_nonneg nn]
  have ct : (I.filter (·∈down)).card ≤ (upto down b).card := by
    apply Finset.card_le_card
    intro i hi
    obtain ⟨hy,hm⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Finset.mem_Ico.mp hy).2,hm⟩
  have ct' : ((I.filter (·∈down)).card:ℝ) ≤ (upto down b).card := by exact_mod_cast ct
  have e := Finset.sum_le_sum each
  rw [Finset.sum_add_distrib,←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,step_sum hab] at e
  change _ ≤ Erdos968.u b+c*(upto down b).card
  change variation a b ≤ _ at e
  linarith [mul_le_mul_of_nonneg_right ct' cp,u_nonneg a]



private theorem variation_nonneg (a b : ℕ) : 0 ≤ variation a b :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

private theorem upper_on_powers : ∃ A : ℝ, 0<A ∧
    ∀ᶠ j : ℕ in atTop, variation 0 (Y j) ≤ A*((j:ℝ)+1)^2 := by
  classical
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp prime_upper
  let C : ℝ := 134217728*131073
  let A := variation 0 (Y N)+C+1
  have cp : 0<C := by norm_num [C]
  have ac : C≤A := by dsimp [A]; linarith [variation_nonneg 0 (Y N)]
  have ap : 0<A := cp.trans_le ac
  refine ⟨A,ap,Filter.eventually_atTop.mpr ⟨N,?_⟩⟩
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    have hi : (1:ℝ)≤((N:ℝ)+1)^2 := by nlinarith [sq_nonneg (N:ℝ),Nat.cast_nonneg N (α:=ℝ)]
    have h := mul_le_mul_of_nonneg_left hi ap.le
    dsimp [A] at h ⊢; linarith
  | succ j hj ih =>
    have hp := hN j hj
    have y := y_pos j
    have yr : (0:ℝ)<Y j := by exact_mod_cast y
    have b := y_mono (Nat.le_succ j)
    have e := y_step j
    have hb : (Y (j+1):ℝ)=65536*(Y j:ℝ) := by exact_mod_cast e
    have hc : ((upto down (Y (j+1))).card:ℝ)≤Y (j+1) := by
      exact_mod_cast (Finset.card_le_card (Finset.filter_subset ..)).trans_eq (Finset.card_range (Y (j+1)))
    have H := var_upper (H:=X j) y b (by intro i hi; exact hp i ((Finset.mem_Ico.mp hi).2.le.trans_eq e))
    have uu := u_bound b (hp _ e.le)
    have x : (X j:ℝ)=134217728*(j:ℝ)*Y j := by simp [X]
    have r : 2*((X j:ℝ)/(Y j:ℝ)^2)*(Y (j+1):ℝ)=134217728*131072*(j:ℝ) := by rw [x,hb]; field_simp; ring
    have u : variation (Y j) (Y (j+1)) ≤ C*j := by
      have t := mul_le_mul_of_nonneg_left hc (show 0≤2*((X j:ℝ)/(Y j:ℝ)^2) by positivity)
      rw [r] at t
      dsimp [C]; linarith only [H,uu,t]
    have whole : variation 0 (Y j)+variation (Y j) (Y (j+1))=variation 0 (Y (j+1)) :=
      Finset.sum_Ico_consecutive _ (Nat.zero_le _) b
    push_cast
    nlinarith only [ih,u,whole,mul_le_mul_of_nonneg_right ac (Nat.cast_nonneg j (α:=ℝ)),ap,
      mul_nonneg ap.le (Nat.cast_nonneg j (α:=ℝ))]

private theorem cutoff_lt {j : ℕ} (hj : 2≤j) : X j < Y j ^ 2 := by
  let R : ℕ := 2^j
  have r : 4≤R := Nat.pow_le_pow_right (by decide : 0<2) hj
  have c : 134217728 ≤ R^15 := (by decide : 134217728≤4^15).trans (Nat.pow_le_pow_left r 15)
  have jr : j<R := Nat.lt_two_pow_self
  have smaller : 134217728*j<Y j := by
    change 134217728*j < R^16
    rw [show (16:ℕ)=15+1 by decide,pow_succ]
    exact lt_of_le_of_lt (Nat.mul_le_mul_right j c) (Nat.mul_lt_mul_of_pos_left jr (by positivity))
  change 134217728*j*Y j < _
  rw [sq]; exact Nat.mul_lt_mul_of_pos_right smaller (y_pos j)

private theorem compare_variation : ∃ A D : ℝ, ∀ᶠ x : ℕ in atTop,
    variation 0 (Nat.primeCounting' x) ≤ A*Real.log x ^ 2 ∧
    Real.log x ^ 2 ≤ D*variation 0 (Nat.primeCounting' x) := by
  obtain ⟨A,hA,ha⟩ := upper_on_powers
  obtain ⟨δ,hd,hδ⟩ := block_lower
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp hδ
  obtain ⟨P,hP⟩ := Filter.eventually_atTop.mp prime_upper
  obtain ⟨T,hT⟩ := Filter.eventually_atTop.mp ha
  let pick (x : ℕ) := Nat.log 65536 x/4
  have tend : Tendsto pick atTop atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro k; refine ⟨65536^(k*4),?_⟩
    intro n hn; exact (Nat.le_div_iff_mul_le (by decide)).mpr (Nat.le_log_of_pow_le (by decide) hn)
  refine ⟨A,16384/δ,?_⟩
  filter_upwards [tend.eventually_ge_atTop (N+P+T+1),eventually_ge_atTop 1] with x hk hx
  let k := pick x
  have k1 : 1≤k := by change _≤k at hk; omega
  have kr : (1:ℝ)≤k := by exact_mod_cast k1
  have low : Y (4*k) ≤ x := by
    rw [y_pow]
    apply (Nat.pow_le_pow_right (by decide : 0<65536) (show 4*k≤Nat.log 65536 x by dsimp [k,pick]; omega)).trans
    exact Nat.pow_log_le_self _ (by omega)
  have high : x≤Y (4*(k+1)) := by
    rw [y_pow]
    exact (Nat.lt_pow_succ_log_self (by decide : 1<65536) x).le.trans
      (Nat.pow_le_pow_right (by decide) (by dsimp [k,pick]; omega))
  have pi : Y (2*k) ≤ Nat.primeCounting' x := by
    have p := hP (2*k) (by change _≤k at hk; omega) (Y (2*k)) (by omega)
    have m := cutoff_lt (show 2≤2*k by omega)
    have e : Y (2*k)^2 = Y (4*k) := by rw [y_pow,y_pow,←pow_mul]; congr 1; ring
    have le := p.trans (m.le.trans (e ▸ low))
    simpa only [Nat.primeCounting'_nth_eq] using Nat.monotone_primeCounting' le
  have pn : Nat.primeCounting' x≤Y (4*(k+1)) := (Nat.count_le ..).trans high
  have vu : variation 0 (Nat.primeCounting' x) ≤ variation 0 (Y (4*(k+1))) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right pn) (fun _ _ _ => abs_nonneg _)
  have vl : variation (Y k) (Y (k+k)) ≤ variation 0 (Nat.primeCounting' x) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico (Nat.zero_le _) (by simpa [two_mul] using pi))
      (fun _ _ _ => abs_nonneg _)
  have vsmall := var_span hd.le (k:=k) (fun i hi => hN i (by change _≤k at hk; omega)) k
  have vlarge := hT (4*(k+1)) (by change _≤k at hk; omega)
  have lo : 32*(k:ℝ) ≤ Real.log x := by
    have e := Real.log_le_log (by exact_mod_cast y_pos (4*k) : (0:ℝ)<Y (4*k)) (by exact_mod_cast low : (Y (4*k):ℝ) ≤ x)
    rw [logY] at e; push_cast at e
    nlinarith only [e,mul_le_mul_of_nonneg_left logtwo.1 (Nat.cast_nonneg k (α:=ℝ))]
  have hi : Real.log x ≤ 128*(k:ℝ) := by
    have e := Real.log_le_log (by exact_mod_cast hx : (0:ℝ)<x) (by exact_mod_cast high : (x:ℝ) ≤ Y (4*(k+1)))
    rw [logY] at e; push_cast at e
    nlinarith only [e,logtwo.2,mul_le_mul_of_nonneg_left logtwo.2 (Nat.cast_nonneg k (α:=ℝ)),kr]
  push_cast at vlarge
  constructor
  · exact vu.trans (vlarge.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) 2) hA.le))
  · have sq := pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast hx)) hi 2
    have cap : δ*(Real.log x)^2 ≤ 16384*variation 0 (Nat.primeCounting' x) := by
      nlinarith only [mul_le_mul_of_nonneg_left sq hd.le,vsmall,vl]
    calc
      _ ≤ (16384*variation 0 (Nat.primeCounting' x))/δ := (le_div_iff₀ hd).2 (by linarith only [cap])
      _ = _ := by ring


end PairWindows

theorem OMA.solution : type_of% @Erdos968.erdos_968.variants.sum_abs_diff_isTheta_log_sq := by
  obtain ⟨A,D,h⟩ := PairWindows.compare_variation
  have nonneg (x : ℕ) : 0 ≤ ∑ n ∈ Finset.range (Nat.primeCounting' x), |Erdos968.u (n+1)-Erdos968.u n| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  constructor
  · apply Asymptotics.IsBigO.of_bound A
    filter_upwards [h] with x hx
    simpa only [Nat.Iio_eq_range,Real.norm_eq_abs,abs_of_nonneg (nonneg x),abs_of_nonneg (sq_nonneg (Real.log x)),
      PairWindows.variation,Nat.Ico_zero_eq_range,PairWindows.step] using hx.1
  · apply Asymptotics.IsBigO.of_bound D
    filter_upwards [h] with x hx
    simpa only [Nat.Iio_eq_range,Real.norm_eq_abs,abs_of_nonneg (nonneg x),abs_of_nonneg (sq_nonneg (Real.log x)),
      PairWindows.variation,Nat.Ico_zero_eq_range,PairWindows.step] using hx.2