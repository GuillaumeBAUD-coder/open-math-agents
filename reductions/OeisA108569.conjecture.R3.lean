import FormalConjectures.OEIS.«108569»

/-! The odd totient fixed points are characterized by a squarefree radical and a unique divisor. -/

-- Credit: @physbuzz
-- The previous cube-free reduction by @Tchikrazi gives the same passage from
-- the enumeration to odd witnesses. The radical/divisor criterion below also
-- reconstructs a witness from any pair satisfying its scalar equation.
namespace OMA.R_OeisA108569_conjecture_R3
open Finset

lemma same_ratio {x y : ℕ} (eq : x.primeFactors = y.primeFactors) :
    x.totient*y = y.totient*x := by
  have a := Nat.totient_mul_prod_primeFactors x
  rw [eq] at a
  have b := Nat.totient_mul_prod_primeFactors y
  let P := ∏ p ∈ y.primeFactors, p
  have pos : 0 < P := Finset.prod_pos fun _ h => Nat.pos_of_mem_primeFactors h
  apply Nat.eq_of_mul_eq_mul_right pos
  dsimp [P]
  calc
    _ = (x.totient*(∏ p ∈ y.primeFactors, p))*y := by ring
    _ = (y.totient*(∏ p ∈ y.primeFactors, p))*x := by rw [a,b]; ring
    _ = _ := by ring

lemma scale {t r : ℕ} (hr : 0 < r) (ht : 0 < t) (inc : t.primeFactors ⊆ r.primeFactors) :
    (t*r).totient = t*r.totient := by
  have sup : (t*r).primeFactors = r.primeFactors := by
    rw [Nat.primeFactors_mul ht.ne' hr.ne', Finset.union_eq_right.mpr inc]
  have h := same_ratio sup
  apply Nat.eq_of_mul_eq_mul_right hr
  calc
    _ = r.totient*(t*r) := h
    _ = _ := by ring

lemma squarefree_rad (n : ℕ) : Squarefree (∏ p ∈ n.primeFactors,p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun _ hp _ hq ne => ?_)
    fun _ hp => (Nat.prime_of_mem_primeFactors hp).squarefree
  exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
    (Nat.prime_of_mem_primeFactors hq)).mpr ne)

theorem normalize (n : ℕ) (hn : 1 < n) (odd : Odd n) (he : n.totient = (n+n.totient).totient) :
    ∃ R D : ℕ, R = ∏ p ∈ n.primeFactors,p ∧ 1 < R ∧ Odd R ∧ Squarefree R ∧ D ∣ R ∧
    D.Coprime (R+R.totient) ∧ R.totient*D = (R+R.totient).totient*D.totient := by
  let R := ∏ p ∈ n.primeFactors,p
  have Rd : R ∣ n := Nat.prod_primeFactors_dvd n
  have Rp : 0 < R := Finset.prod_pos fun _ h => Nat.pos_of_mem_primeFactors h
  have Rs : R.primeFactors = n.primeFactors := Nat.primeFactors_prod_primeFactors n
  have Rbig : 1 < R := by
    have mem : n.minFac ∈ R.primeFactors := by
      rw [Rs]
      exact Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd n,by omega⟩
    have le := Nat.le_of_mem_primeFactors mem
    have p := (Nat.minFac_prime (by omega : n≠1)).two_le
    omega
  let t := n/R
  have mult : t*R=n := Nat.div_mul_cancel Rd
  have tp : 0 < t := Nat.div_pos (Nat.le_of_dvd (by omega) Rd) Rp
  have tin : t.primeFactors ⊆ R.primeFactors := by
    rw [Rs]
    exact Nat.primeFactors_mono (Dvd.intro R mult) (by omega)
  have tot : n.totient = t*R.totient := by simpa only [mult] using scale Rp tp tin
  let U := R+R.totient
  have up : 0 < U := by dsimp [U]; omega
  let s := t.primeFactors \ U.primeFactors
  let D := ∏ p ∈ s,p
  have sin : s ⊆ t.primeFactors := Finset.sdiff_subset
  have Ds : D.primeFactors = s := Nat.primeFactors_prod fun p h => Nat.prime_of_mem_primeFactors (sin h)
  have dp : 0 < D := Finset.prod_pos fun _ h => Nat.pos_of_mem_primeFactors (sin h)
  have Dd : D ∣ R := by
    have h := Finset.prod_dvd_prod_of_subset s n.primeFactors (fun i => i) (by rw [← Rs]; exact sin.trans tin)
    exact h
  have cop : D.Coprime U := by
    apply (Nat.disjoint_primeFactors dp.ne' up.ne').mp
    rw [Ds]
    exact Finset.disjoint_left.mpr fun p h hu => (Finset.mem_sdiff.mp h).2 hu
  have support : (t*U).primeFactors = (D*U).primeFactors := by
    rw [Nat.primeFactors_mul tp.ne' up.ne',Nat.primeFactors_mul dp.ne' up.ne',Ds]
    ext p
    simp [s]
  have rel := same_ratio support
  rw [Nat.totient_mul cop] at rel
  have add : n+n.totient = t*U := by rw [tot,← mult]; dsimp [U]; ring
  rw [add,tot] at he
  rw [← he] at rel
  refine ⟨R,D,rfl,Rbig,odd.of_dvd_nat Rd,squarefree_rad n,Dd,cop,?_⟩
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos tp up)
  calc
    _ = (t*R.totient)*(D*U) := by ring
    _ = D.totient*U.totient*(t*U) := rel
    _ = _ := by ring

theorem reconstruct (R D : ℕ) (hr : 1 < R) (odd : Odd R) (hd : D ∣ R)
    (cop : D.Coprime (R+R.totient)) (eq : R.totient*D = (R+R.totient).totient*D.totient) :
    1 < D*R ∧ Odd (D*R) ∧ (D*R).totient = (D*R+(D*R).totient).totient := by
  have dp : 0 < D := Nat.pos_of_dvd_of_pos hd (by omega)
  have tot := scale (by omega : 0 < R) dp (Nat.primeFactors_mono hd (by omega))
  refine ⟨by nlinarith, (odd.of_dvd_nat hd).mul odd,?_⟩
  rw [tot,← Nat.mul_add,Nat.totient_mul cop]
  simpa [Nat.mul_comm] using eq


lemma greatest_in_other (s t : Finset ℕ) {p : ℕ} (hs : ∀ q ∈ s, q.Prime)
    (ht : ∀ q ∈ t, q.Prime) (mem : p ∈ s) (greatest : ∀ q ∈ s, q ≤ p)
    (eq : (∏ q ∈ s,q)*(∏ q ∈ t,(q-1)) = (∏ q ∈ t,q)*(∏ q ∈ s,(q-1))) : p ∈ t := by
  have pp := hs p mem
  have div := dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem (fun q : ℕ => q) mem) (∏ q ∈ t,(q-1))
  rw [eq] at div
  rcases pp.dvd_mul.mp div with d | d
  · obtain ⟨q,hq,hpq⟩ := (pp.prime.dvd_finsetProd_iff (fun q : ℕ => q)).mp d
    simpa [(Nat.prime_dvd_prime_iff_eq pp (ht q hq)).mp hpq] using hq
  · obtain ⟨q,hq,hpq⟩ := (pp.prime.dvd_finsetProd_iff (fun q : ℕ => q-1)).mp d
    have size := greatest q hq
    have low := (hs q hq).two_le
    have le := Nat.le_of_dvd (by omega : 0 < q-1) hpq
    omega

theorem support_unique (s t : Finset ℕ) (hs : ∀ q ∈ s, q.Prime) (ht : ∀ q ∈ t,q.Prime)
    (eq : (∏ q ∈ s,q)*(∏ q ∈ t,(q-1)) = (∏ q ∈ t,q)*(∏ q ∈ s,(q-1))) : s=t := by
  induction s using Finset.strongInductionOn generalizing t with
  | _ s ih =>
    by_cases nonempty : (s∪t).Nonempty
    · let p := (s∪t).max' nonempty
      have inp := Finset.max'_mem (s∪t) nonempty
      have ls (q : ℕ) (h : q ∈ s) : q ≤ p := Finset.le_max' _ q (Finset.mem_union_left t h)
      have lt (q : ℕ) (h : q ∈ t) : q ≤ p := Finset.le_max' _ q (Finset.mem_union_right s h)
      have both : p ∈ s ∧ p ∈ t := by
        rcases Finset.mem_union.mp inp with h|h
        · exact ⟨h,greatest_in_other s t hs ht h ls eq⟩
        · exact ⟨greatest_in_other t s ht hs h lt eq.symm,h⟩
      obtain ⟨a,b⟩ := both
      have prime := hs p a
      have eqp := eq
      rw [← Finset.mul_prod_erase s (fun q => q) a,← Finset.mul_prod_erase t (fun q => q-1) b,
        ← Finset.mul_prod_erase t (fun q => q) b,← Finset.mul_prod_erase s (fun q => q-1) a] at eqp
      have sub : (∏ q ∈ s.erase p,q)*(∏ q ∈ t.erase p,(q-1)) =
          (∏ q ∈ t.erase p,q)*(∏ q ∈ s.erase p,(q-1)) := by
        apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos prime.pos (by have := prime.two_le; omega : 0 < p-1))
        nlinarith only [eqp]
      have e := ih (s.erase p) (Finset.erase_ssubset a) (t.erase p)
        (fun q h => hs q (Finset.mem_of_mem_erase h)) (fun q h => ht q (Finset.mem_of_mem_erase h)) sub
      simpa [a,b] using congrArg (insert p) e
    · have z := Finset.not_nonempty_iff_eq_empty.mp nonempty
      simpa using (Finset.union_eq_empty.mp z).1.trans (Finset.union_eq_empty.mp z).2.symm

theorem unique_squarefree {d e : ℕ} (sd : Squarefree d) (se : Squarefree e)
    (eq : d*e.totient = e*d.totient) : d=e := by
  have phi (n : ℕ) (sq : Squarefree n) : n.totient = ∏ p ∈ n.primeFactors,(p-1) := by
    rw [Nat.totient_eq_div_primeFactors_mul,Nat.prod_primeFactors_of_squarefree sq]
    simp [Nat.div_self (Nat.pos_of_ne_zero sq.ne_zero)]
  rw [phi d sd,phi e se] at eq
  have supp : d.primeFactors = e.primeFactors := by
    apply support_unique _ _ (fun _ h => Nat.prime_of_mem_primeFactors h) (fun _ h => Nat.prime_of_mem_primeFactors h)
    simpa [Nat.prod_primeFactors_of_squarefree sd,Nat.prod_primeFactors_of_squarefree se] using eq
  rw [← Nat.prod_primeFactors_of_squarefree sd,← Nat.prod_primeFactors_of_squarefree se,supp]

/-- The divisor to test is unique for each squarefree radical. Its totient ratio
determines its primes successively, starting with the largest one. -/
lemma unique_divisor {R D E : ℕ} (hr : 0 < R) (sf : Squarefree R)
    (hd : D ∣ R) (he : E ∣ R)
    (deq : R.totient*D = (R+R.totient).totient*D.totient)
    (eeq : R.totient*E = (R+R.totient).totient*E.totient) : D=E := by
  apply unique_squarefree (sf.squarefree_of_dvd hd) (sf.squarefree_of_dvd he)
  apply Nat.eq_of_mul_eq_mul_left (Nat.totient_pos.mpr hr)
  calc
    R.totient*(D*E.totient) = (R.totient*D)*E.totient := by ring
    _ = (R.totient*E)*D.totient := by rw [deq,eeq]; ring
    _ = R.totient*(E*D.totient) := by ring


/-- With U = R+φ(R) and Q=R/gcd(R,U), the following three tests on R require
no auxiliary divisor. Failure of any one rules out every input with radical R. -/
lemma scalar_filter (R D : ℕ) (hr : 0 < R) (sf : Squarefree R) (hd : D ∣ R)
    (cop : D.Coprime (R+R.totient)) (eq : R.totient*D = (R+R.totient).totient*D.totient) :
    let U := R+R.totient
    let Q := R/R.gcd U
    R.totient ≤ U.totient ∧ U.totient ∣ R.totient*Q ∧ U.totient*Q.totient ≤ R.totient*Q := by
  let U := R+R.totient
  let g := R.gcd U
  let Q := R/g
  change R.totient ≤ U.totient ∧ U.totient ∣ R.totient*Q ∧ U.totient*Q.totient ≤ R.totient*Q
  have dp := Nat.pos_of_dvd_of_pos hd hr
  have dg : g ∣ R := Nat.gcd_dvd_left _ _
  have dc : D.Coprime g := cop.coprime_dvd_right (Nat.gcd_dvd_right _ _)
  have prod : g*Q = R := Nat.mul_div_cancel' dg
  have dQ : D ∣ Q := dc.dvd_of_dvd_mul_left (prod ▸ hd)
  obtain ⟨k,hk⟩ := dQ
  have qR : Q ∣ R := Dvd.intro_left g prod
  have qsf := sf.squarefree_of_dvd qR
  have dk : D.Coprime k := Nat.coprime_of_squarefree_mul (hk ▸ qsf)
  have first : R.totient ≤ U.totient := by
    refine le_of_mul_le_mul_right ?_ dp
    calc
      R.totient*D = U.totient*D.totient := eq
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.totient_le D)
  refine ⟨first,?_,?_⟩
  · exact (show U.totient ∣ R.totient*D from ⟨_,eq⟩).trans (Nat.mul_dvd_mul_left _ ⟨k,hk⟩)
  · rw [hk,Nat.totient_mul dk]
    calc
      U.totient*(D.totient*k.totient) = (R.totient*D)*k.totient := by rw [eq]; ring
      _ ≤ (R.totient*D)*k := Nat.mul_le_mul_left _ k.totient_le
      _ = _ := by ring

lemma totient_fold (A : List ℕ) (good : ∀ p ∈ A, p.Prime) :
    A.foldr (fun (p : ℕ) (s : ℕ × ℕ) => (p*s.1, (if s.1%p=0 then p else p-1)*s.2)) (1,1) = (A.prod,A.prod.totient) := by
  induction A with
  | nil => simp
  | cons p l ih =>
    have hp := good p List.mem_cons_self
    rw [List.foldr_cons,ih (fun q h => good q (List.mem_cons_of_mem p h)),List.prod_cons]
    by_cases h : p ∣ l.prod
    · simp [Nat.mod_eq_zero_of_dvd h,Nat.totient_mul_of_prime_of_dvd hp h]
    · have ne : l.prod%p ≠ 0 := fun e => h (Nat.dvd_of_mod_eq_zero e)
      simp [ne,Nat.totient_mul (hp.coprime_iff_not_dvd.mpr h),Nat.totient_prime hp]


private lemma certified_small_prime (p : ℕ)
    (h : if p ≤ 150 then p.Prime else p < 151^2 ∧ p.Coprime (Nat.factorial 150)) : p.Prime := by
  split at h
  · exact h
  · have least := (Nat.coprime_factorial_iff (by omega : p≠1)).mp h.2
    refine Nat.prime_def_le_sqrt.mpr ⟨by omega,?_⟩
    intro q hq rt div
    have le := Nat.minFac_le_of_dvd hq div
    have hp0 := h.1
    have lim := Nat.sqrt_lt.mpr (by simpa only [pow_two] using hp0)
    omega

private lemma sharp_block (start count R D : ℕ) (rows : List (List ℕ × List ℕ × List ℕ))
    (lo : start ≤ R) (hi : R < start+count) (gt : 1 < R) (odd : Odd R) (sf : Squarefree R)
    (hd : D ∣ R) (cop : D.Coprime (R+R.totient))
    (cert : ∀ t : Fin count, let a := start+t.val; let row := rows[t.val]!;
      let accept := fun p : ℕ => if p ≤ 150 then p.Prime else p < 151^2 ∧ p.Coprime (Nat.factorial 150);
      let X := row.1.foldr (fun (p : ℕ) (s : ℕ × ℕ) => (p*s.1, (if s.1%p=0 then p else p-1)*s.2)) (1,1);
      let Y := row.2.1.foldr (fun (p : ℕ) (s : ℕ × ℕ) => (p*s.1, (if s.1%p=0 then p else p-1)*s.2)) (1,1);
      let Z := row.2.2.foldr (fun (p : ℕ) (s : ℕ × ℕ) => (p*s.1, (if s.1%p=0 then p else p-1)*s.2)) (1,1);
      1 < a → a%2=1 → (∀ p ∈ row.1, accept p) ∧ (∀ p ∈ row.2.1, accept p) ∧
      (∀ p ∈ row.2.2, accept p) ∧ X.1 = a ∧ Y.1 = a+X.2 ∧ Z.1 = a/(a.gcd Y.1) ∧
      ¬(X.2 ≤ Y.2 ∧ Y.2 ∣ X.2*Z.1 ∧ Y.2*Z.2 ≤ X.2*Z.1)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  intro eq
  let t : Fin count := ⟨R-start,by omega⟩
  have top : start+t.val = R := by dsimp [t]; omega
  specialize cert t
  simp only [top] at cert
  obtain ⟨ha,hb,hc,hx,hy,hz,bad⟩ := cert gt (Nat.odd_iff.mp odd)
  rw [totient_fold _ (fun p h => certified_small_prime p (ha p h))] at hx hy bad
  rw [totient_fold _ (fun p h => certified_small_prime p (hb p h))] at hy hz bad
  rw [totient_fold _ (fun p h => certified_small_prime p (hc p h))] at hz bad
  simp only at hx hy hz bad
  rw [hx] at hy bad
  rw [hy] at hz bad
  rw [hz] at bad
  exact bad (scalar_filter R D (by omega) sf hd cop eq)
set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range0 (R D : ℕ) (lo : 0 ≤ R) (hi : R < 64) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 0 64 R D [([],[],[]),([],[],[]),([],[],[]),([3],[5],[3]),([],[],[]),([5],[3,3],[5]),([],[],[]),([7],[13],[7]),([],[],[]),([3,3],[3,5],[3]),([],[],[]),([11],[3,7],[11]),([],[],[]),([13],[5,5],[13]),([],[],[]),([3,5],[23],[3,5]),([],[],[]),([17],[3,11],[17]),([],[],[]),([19],[37],[19]),([],[],[]),([3,7],[3,11],[7]),([],[],[]),([23],[3,3,5],[23]),([],[],[]),([5,5],[3,3,5],[5]),([],[],[]),([3,3,3],[3,3,5],[3]),([],[],[]),([29],[3,19],[29]),([],[],[]),([31],[61],[31]),([],[],[]),([3,11],[53],[3,11]),([],[],[]),([5,7],[59],[5,7]),([],[],[]),([37],[73],[37]),([],[],[]),([3,13],[3,3,7],[13]),([],[],[]),([41],[3,3,3,3],[41]),([],[],[]),([43],[5,17],[43]),([],[],[]),([3,3,5],[3,23],[3,5]),([],[],[]),([47],[3,31],[47]),([],[],[]),([7,7],[7,13],[7]),([],[],[]),([3,17],[83],[3,17]),([],[],[]),([53],[3,5,7],[53]),([],[],[]),([5,11],[5,19],[11]),([],[],[]),([3,19],[3,31],[19]),([],[],[]),([59],[3,3,13],[59]),([],[],[]),([61],[11,11],[61]),([],[],[]),([3,3,7],[3,3,11],[7])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range64 (R D : ℕ) (lo : 64 ≤ R) (hi : R < 128) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 64 64 R D [([],[],[]),([5,13],[113],[5,13]),([],[],[]),([67],[7,19],[67]),([],[],[]),([3,23],[113],[3,23]),([],[],[]),([71],[3,47],[71]),([],[],[]),([73],[5,29],[73]),([],[],[]),([3,5,5],[5,23],[3,5]),([],[],[]),([7,11],[137],[7,11]),([],[],[]),([79],[157],[79]),([],[],[]),([3,3,3,3],[3,3,3,5],[3]),([],[],[]),([83],[3,5,11],[83]),([],[],[]),([5,17],[149],[5,17]),([],[],[]),([3,29],[11,13],[3,29]),([],[],[]),([89],[3,59],[89]),([],[],[]),([7,13],[163],[7,13]),([],[],[]),([3,31],[3,3,17],[31]),([],[],[]),([5,19],[167],[5,19]),([],[],[]),([97],[193],[97]),([],[],[]),([3,3,11],[3,53],[3,11]),([],[],[]),([101],[3,67],[101]),([],[],[]),([103],[5,41],[103]),([],[],[]),([3,5,7],[3,3,17],[5,7]),([],[],[]),([107],[3,71],[107]),([],[],[]),([109],[7,31],[109]),([],[],[]),([3,37],[3,61],[37]),([],[],[]),([113],[3,3,5,5],[113]),([],[],[]),([5,23],[7,29],[5,23]),([],[],[]),([3,3,13],[3,3,3,7],[13]),([],[],[]),([7,17],[5,43],[7,17]),([],[],[]),([11,11],[3,7,11],[11]),([],[],[]),([3,41],[7,29],[3,41]),([],[],[]),([5,5,5],[3,3,5,5],[5]),([],[],[]),([127],[11,23],[127])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range128 (R D : ℕ) (lo : 128 ≤ R) (hi : R < 192) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 128 64 R D [([],[],[]),([3,43],[3,71],[43]),([],[],[]),([131],[3,3,29],[131]),([],[],[]),([7,19],[241],[7,19]),([],[],[]),([3,3,3,5],[3,3,23],[3,5]),([],[],[]),([137],[3,7,13],[137]),([],[],[]),([139],[277],[139]),([],[],[]),([3,47],[233],[3,47]),([],[],[]),([11,13],[263],[11,13]),([],[],[]),([5,29],[257],[5,29]),([],[],[]),([3,7,7],[3,7,11],[7]),([],[],[]),([149],[3,3,3,11],[149]),([],[],[]),([151],[7,43],[151]),([],[],[]),([3,3,17],[3,83],[3,17]),([],[],[]),([5,31],[5,5,11],[31]),([],[],[]),([157],[313],[157]),([],[],[]),([3,53],[263],[3,53]),([],[],[]),([7,23],[293],[7,23]),([],[],[]),([163],[5,5,13],[163]),([],[],[]),([3,5,11],[5,7,7],[3,11]),([],[],[]),([167],[3,3,37],[167]),([],[],[]),([13,13],[5,5,13],[13]),([],[],[]),([3,3,19],[3,3,31],[19]),([],[],[]),([173],[3,5,23],[173]),([],[],[]),([5,5,7],[5,59],[5,7]),([],[],[]),([3,59],[293],[3,59]),([],[],[]),([179],[3,7,17],[179]),([],[],[]),([181],[19,19],[181]),([],[],[]),([3,61],[3,101],[61]),([],[],[]),([5,37],[7,47],[5,37]),([],[],[]),([11,17],[347],[11,17]),([],[],[]),([3,3,3,7],[3,3,3,11],[7]),([],[],[]),([191],[3,127],[191])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range192 (R D : ℕ) (lo : 192 ≤ R) (hi : R < 256) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 192 64 R D [([],[],[]),([193],[5,7,11],[193]),([],[],[]),([3,5,13],[3,97],[5,13]),([],[],[]),([197],[3,131],[197]),([],[],[]),([199],[397],[199]),([],[],[]),([3,67],[3,3,37],[67]),([],[],[]),([7,29],[7,53],[29]),([],[],[]),([5,41],[5,73],[41]),([],[],[]),([3,3,23],[3,113],[3,23]),([],[],[]),([11,19],[389],[11,19]),([],[],[]),([211],[421],[211]),([],[],[]),([3,71],[353],[3,71]),([],[],[]),([5,43],[383],[5,43]),([],[],[]),([7,31],[397],[7,31]),([],[],[]),([3,73],[3,11,11],[73]),([],[],[]),([13,17],[7,59],[13,17]),([],[],[]),([223],[5,89],[223]),([],[],[]),([3,3,5,5],[3,5,23],[3,5]),([],[],[]),([227],[3,151],[227]),([],[],[]),([229],[457],[229]),([],[],[]),([3,7,11],[3,3,3,13],[7,11]),([],[],[]),([233],[3,5,31],[233]),([],[],[]),([5,47],[419],[5,47]),([],[],[]),([3,79],[3,131],[79]),([],[],[]),([239],[3,3,53],[239]),([],[],[]),([241],[13,37],[241]),([],[],[]),([3,3,3,3,3],[3,3,3,3,5],[3]),([],[],[]),([5,7,7],[7,59],[5,7]),([],[],[]),([13,19],[463],[13,19]),([],[],[]),([3,83],[7,59],[3,83]),([],[],[]),([251],[3,167],[251]),([],[],[]),([11,23],[11,43],[23]),([],[],[]),([3,5,17],[383],[3,5,17])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range256 (R D : ℕ) (lo : 256 ≤ R) (hi : R < 320) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 256 64 R D [([],[],[]),([257],[3,3,3,19],[257]),([],[],[]),([7,37],[5,5,19],[7,37]),([],[],[]),([3,3,29],[3,11,13],[3,29]),([],[],[]),([263],[3,5,5,7],[263]),([],[],[]),([5,53],[11,43],[5,53]),([],[],[]),([3,89],[443],[3,89]),([],[],[]),([269],[3,179],[269]),([],[],[]),([271],[541],[271]),([],[],[]),([3,7,13],[3,139],[7,13]),([],[],[]),([5,5,11],[5,5,19],[11]),([],[],[]),([277],[7,79],[277]),([],[],[]),([3,3,31],[3,3,3,17],[31]),([],[],[]),([281],[3,11,17],[281]),([],[],[]),([283],[5,113],[283]),([],[],[]),([3,5,19],[3,11,13],[5,19]),([],[],[]),([7,41],[17,31],[7,41]),([],[],[]),([17,17],[3,11,17],[17]),([],[],[]),([3,97],[3,7,23],[97]),([],[],[]),([293],[3,3,5,13],[293]),([],[],[]),([5,59],[17,31],[5,59]),([],[],[]),([3,3,3,11],[3,3,53],[3,11]),([],[],[]),([13,23],[563],[13,23]),([],[],[]),([7,43],[7,79],[43]),([],[],[]),([3,101],[503],[3,101]),([],[],[]),([5,61],[5,109],[61]),([],[],[]),([307],[613],[307]),([],[],[]),([3,103],[3,3,3,19],[103]),([],[],[]),([311],[3,3,3,23],[311]),([],[],[]),([313],[5,5,5,5],[313]),([],[],[]),([3,3,5,7],[3,3,3,17],[5,7]),([],[],[]),([317],[3,211],[317]),([],[],[]),([11,29],[599],[11,29])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range320 (R D : ℕ) (lo : 320 ≤ R) (hi : R < 384) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 320 64 R D [([],[],[]),([3,107],[13,41],[3,107]),([],[],[]),([17,19],[13,47],[17,19]),([],[],[]),([5,5,13],[5,113],[5,13]),([],[],[]),([3,109],[3,181],[109]),([],[],[]),([7,47],[5,11,11],[7,47]),([],[],[]),([331],[661],[331]),([],[],[]),([3,3,37],[3,3,61],[37]),([],[],[]),([5,67],[599],[5,67]),([],[],[]),([337],[673],[337]),([],[],[]),([3,113],[563],[3,113]),([],[],[]),([11,31],[641],[11,31]),([],[],[]),([7,7,7],[7,7,13],[7]),([],[],[]),([3,5,23],[521],[3,5,23]),([],[],[]),([347],[3,3,7,11],[347]),([],[],[]),([349],[17,41],[349]),([],[],[]),([3,3,3,13],[3,3,3,3,7],[13]),([],[],[]),([353],[3,5,47],[353]),([],[],[]),([5,71],[5,127],[71]),([],[],[]),([3,7,17],[3,3,61],[7,17]),([],[],[]),([359],[3,239],[359]),([],[],[]),([19,19],[19,37],[19]),([],[],[]),([3,11,11],[11,53],[3,11]),([],[],[]),([5,73],[653],[5,73]),([],[],[]),([367],[733],[367]),([],[],[]),([3,3,41],[3,7,29],[3,41]),([],[],[]),([7,53],[683],[7,53]),([],[],[]),([373],[5,149],[373]),([],[],[]),([3,5,5,5],[5,5,23],[3,5]),([],[],[]),([13,29],[23,31],[13,29]),([],[],[]),([379],[757],[379]),([],[],[]),([3,127],[3,211],[127]),([],[],[]),([383],[3,3,5,17],[383])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range384 (R D : ℕ) (lo : 384 ≤ R) (hi : R < 448) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 384 64 R D [([],[],[]),([5,7,11],[5,5,5,5],[7,11]),([],[],[]),([3,3,43],[3,3,71],[43]),([],[],[]),([389],[3,7,37],[389]),([],[],[]),([17,23],[743],[17,23]),([],[],[]),([3,131],[653],[3,131]),([],[],[]),([5,79],[7,101],[5,79]),([],[],[]),([397],[13,61],[397]),([],[],[]),([3,7,19],[3,5,41],[7,19]),([],[],[]),([401],[3,3,89],[401]),([],[],[]),([13,31],[7,109],[13,31]),([],[],[]),([3,3,3,3,5],[3,3,3,23],[3,5]),([],[],[]),([11,37],[13,59],[11,37]),([],[],[]),([409],[19,43],[409]),([],[],[]),([3,137],[683],[3,137]),([],[],[]),([7,59],[761],[7,59]),([],[],[]),([5,83],[743],[5,83]),([],[],[]),([3,139],[3,3,7,11],[139]),([],[],[]),([419],[3,3,3,31],[419]),([],[],[]),([421],[29,29],[421]),([],[],[]),([3,3,47],[3,233],[3,47]),([],[],[]),([5,5,17],[5,149],[5,17]),([],[],[]),([7,61],[787],[7,61]),([],[],[]),([3,11,13],[3,223],[11,13]),([],[],[]),([431],[3,7,41],[431]),([],[],[]),([433],[5,173],[433]),([],[],[]),([3,5,29],[659],[3,5,29]),([],[],[]),([19,23],[7,7,17],[19,23]),([],[],[]),([439],[877],[439]),([],[],[]),([3,3,7,7],[3,3,7,11],[7]),([],[],[]),([443],[3,5,59],[443]),([],[],[]),([5,89],[797],[5,89]),([],[],[]),([3,149],[743],[3,149])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range448 (R D : ℕ) (lo : 448 ≤ R) (hi : R < 512) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 448 64 R D [([],[],[]),([449],[3,13,23],[449]),([],[],[]),([11,41],[23,37],[11,41]),([],[],[]),([3,151],[3,251],[151]),([],[],[]),([5,7,13],[743],[5,7,13]),([],[],[]),([457],[11,83],[457]),([],[],[]),([3,3,3,17],[3,3,83],[3,17]),([],[],[]),([461],[3,307],[461]),([],[],[]),([463],[5,5,37],[463]),([],[],[]),([3,5,31],[3,5,47],[31]),([],[],[]),([467],[3,311],[467]),([],[],[]),([7,67],[5,173],[7,67]),([],[],[]),([3,157],[3,3,3,29],[157]),([],[],[]),([11,43],[19,47],[11,43]),([],[],[]),([5,5,19],[5,167],[5,19]),([],[],[]),([3,3,53],[3,263],[3,53]),([],[],[]),([479],[3,11,29],[479]),([],[],[]),([13,37],[11,83],[13,37]),([],[],[]),([3,7,23],[3,3,83],[7,23]),([],[],[]),([5,97],[11,79],[5,97]),([],[],[]),([487],[7,139],[487]),([],[],[]),([3,163],[3,271],[163]),([],[],[]),([491],[3,3,109],[491]),([],[],[]),([17,29],[941],[17,29]),([],[],[]),([3,3,5,11],[3,5,7,7],[3,11]),([],[],[]),([7,71],[7,131],[71]),([],[],[]),([499],[997],[499]),([],[],[]),([3,167],[7,7,17],[3,167]),([],[],[]),([503],[3,5,67],[503]),([],[],[]),([5,101],[5,181],[101]),([],[],[]),([3,13,13],[3,3,7,13],[13]),([],[],[]),([509],[3,3,113],[509]),([],[],[]),([7,73],[23,41],[7,73])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range512 (R D : ℕ) (lo : 512 ≤ R) (hi : R < 576) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 512 64 R D [([],[],[]),([3,3,3,19],[3,3,3,31],[19]),([],[],[]),([5,103],[13,71],[5,103]),([],[],[]),([11,47],[977],[11,47]),([],[],[]),([3,173],[863],[3,173]),([],[],[]),([521],[3,347],[521]),([],[],[]),([523],[5,11,19],[523]),([],[],[]),([3,5,5,7],[3,3,5,17],[5,7]),([],[],[]),([17,31],[19,53],[17,31]),([],[],[]),([23,23],[3,3,5,23],[23]),([],[],[]),([3,3,59],[3,293],[3,59]),([],[],[]),([13,41],[1013],[13,41]),([],[],[]),([5,107],[7,137],[5,107]),([],[],[]),([3,179],[19,47],[3,179]),([],[],[]),([7,7,11],[7,137],[7,11]),([],[],[]),([541],[23,47],[541]),([],[],[]),([3,181],[3,7,43],[181]),([],[],[]),([5,109],[977],[5,109]),([],[],[]),([547],[1093],[547]),([],[],[]),([3,3,61],[3,3,101],[61]),([],[],[]),([19,29],[5,211],[19,29]),([],[],[]),([7,79],[1021],[7,79]),([],[],[]),([3,5,37],[3,281],[5,37]),([],[],[]),([557],[3,7,53],[557]),([],[],[]),([13,43],[1063],[13,43]),([],[],[]),([3,11,17],[881],[3,11,17]),([],[],[]),([563],[3,3,5,5,5],[563]),([],[],[]),([5,113],[1013],[5,113]),([],[],[]),([3,3,3,3,7],[3,3,3,3,11],[7]),([],[],[]),([569],[3,379],[569]),([],[],[]),([571],[7,163],[571]),([],[],[]),([3,191],[953],[3,191]),([],[],[]),([5,5,23],[5,7,29],[5,23])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range576 (R D : ℕ) (lo : 576 ≤ R) (hi : R < 640) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 576 64 R D [([],[],[]),([577],[1153],[577]),([],[],[]),([3,193],[3,3,107],[193]),([],[],[]),([7,83],[29,37],[7,83]),([],[],[]),([11,53],[1103],[11,53]),([],[],[]),([3,3,5,13],[3,3,97],[5,13]),([],[],[]),([587],[3,17,23],[587]),([],[],[]),([19,31],[1129],[19,31]),([],[],[]),([3,197],[983],[3,197]),([],[],[]),([593],[3,5,79],[593]),([],[],[]),([5,7,17],[11,89],[5,7,17]),([],[],[]),([3,199],[3,331],[199]),([],[],[]),([599],[3,3,7,19],[599]),([],[],[]),([601],[1201],[601]),([],[],[]),([3,3,67],[3,3,3,37],[67]),([],[],[]),([5,11,11],[5,11,19],[11]),([],[],[]),([607],[1213],[607]),([],[],[]),([3,7,29],[3,3,3,5,7],[29]),([],[],[]),([13,47],[1163],[13,47]),([],[],[]),([613],[5,5,7,7],[613]),([],[],[]),([3,5,41],[5,11,17],[3,41]),([],[],[]),([617],[3,3,137],[617]),([],[],[]),([619],[1237],[619]),([],[],[]),([3,3,3,23],[3,3,113],[3,23]),([],[],[]),([7,89],[1151],[7,89]),([],[],[]),([5,5,5,5],[3,3,5,5,5],[5]),([],[],[]),([3,11,19],[3,7,47],[11,19]),([],[],[]),([17,37],[5,241],[17,37]),([],[],[]),([631],[13,97],[631]),([],[],[]),([3,211],[3,3,3,3,13],[211]),([],[],[]),([5,127],[17,67],[5,127]),([],[],[]),([7,7,13],[7,163],[7,13]),([],[],[]),([3,3,71],[3,353],[3,71])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range640 (R D : ℕ) (lo : 640 ≤ R) (hi : R < 704) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 640 64 R D [([],[],[]),([641],[3,7,61],[641]),([],[],[]),([643],[5,257],[643]),([],[],[]),([3,5,43],[3,3,109],[5,43]),([],[],[]),([647],[3,431],[647]),([],[],[]),([11,59],[1229],[11,59]),([],[],[]),([3,7,31],[3,337],[7,31]),([],[],[]),([653],[3,3,5,29],[653]),([],[],[]),([5,131],[5,5,47],[131]),([],[],[]),([3,3,73],[3,3,11,11],[73]),([],[],[]),([659],[3,439],[659]),([],[],[]),([661],[1321],[661]),([],[],[]),([3,13,17],[3,349],[13,17]),([],[],[]),([5,7,19],[1097],[5,7,19]),([],[],[]),([23,29],[1283],[23,29]),([],[],[]),([3,223],[3,7,53],[223]),([],[],[]),([11,61],[31,41],[11,61]),([],[],[]),([673],[5,269],[673]),([],[],[]),([3,3,3,5,5],[3,3,5,23],[3,5]),([],[],[]),([677],[3,11,41],[677]),([],[],[]),([7,97],[5,251],[7,97]),([],[],[]),([3,227],[11,103],[3,227]),([],[],[]),([683],[3,5,7,13],[683]),([],[],[]),([5,137],[1229],[5,137]),([],[],[]),([3,229],[3,3,127],[229]),([],[],[]),([13,53],[13,101],[53]),([],[],[]),([691],[1381],[691]),([],[],[]),([3,3,7,11],[3,3,3,3,13],[7,11]),([],[],[]),([5,139],[29,43],[5,139]),([],[],[]),([17,41],[7,191],[17,41]),([],[],[]),([3,233],[1163],[3,233]),([],[],[]),([701],[3,467],[701]),([],[],[]),([19,37],[7,193],[19,37])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range704 (R D : ℕ) (lo : 704 ≤ R) (hi : R < 768) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 704 64 R D [([],[],[]),([3,5,47],[29,37],[3,5,47]),([],[],[]),([7,101],[1307],[7,101]),([],[],[]),([709],[13,109],[709]),([],[],[]),([3,3,79],[3,3,131],[79]),([],[],[]),([23,31],[1373],[23,31]),([],[],[]),([5,11,13],[5,239],[11,13]),([],[],[]),([3,239],[1193],[3,239]),([],[],[]),([719],[3,479],[719]),([],[],[]),([7,103],[31,43],[7,103]),([],[],[]),([3,241],[3,401],[241]),([],[],[]),([5,5,29],[5,257],[5,29]),([],[],[]),([727],[1453],[727]),([],[],[]),([3,3,3,3,3,3],[3,3,3,3,3,5],[3]),([],[],[]),([17,43],[23,61],[17,43]),([],[],[]),([733],[5,293],[733]),([],[],[]),([3,5,7,7],[3,3,7,17],[5,7]),([],[],[]),([11,67],[11,127],[67]),([],[],[]),([739],[7,211],[739]),([],[],[]),([3,13,19],[3,17,23],[13,19]),([],[],[]),([743],[3,3,3,5,11],[743]),([],[],[]),([5,149],[7,191],[5,149]),([],[],[]),([3,3,83],[3,7,59],[3,83]),([],[],[]),([7,107],[5,277],[7,107]),([],[],[]),([751],[19,79],[751]),([],[],[]),([3,251],[7,179],[3,251]),([],[],[]),([5,151],[5,271],[151]),([],[],[]),([757],[17,89],[757]),([],[],[]),([3,11,23],[11,109],[3,23]),([],[],[]),([761],[3,3,13,13],[761]),([],[],[]),([7,109],[17,83],[7,109]),([],[],[]),([3,3,5,17],[3,383],[3,5,17]),([],[],[]),([13,59],[7,11,19],[13,59])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range768 (R D : ℕ) (lo : 768 ≤ R) (hi : R < 832) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 768 64 R D [([],[],[]),([769],[29,53],[769]),([],[],[]),([3,257],[1283],[3,257]),([],[],[]),([773],[3,5,103],[773]),([],[],[]),([5,5,31],[5,5,5,11],[31]),([],[],[]),([3,7,37],[3,13,31],[7,37]),([],[],[]),([19,41],[1499],[19,41]),([],[],[]),([11,71],[1481],[11,71]),([],[],[]),([3,3,3,29],[3,3,11,13],[3,29]),([],[],[]),([5,157],[1409],[5,157]),([],[],[]),([787],[11,11,13],[787]),([],[],[]),([3,263],[13,101],[3,263]),([],[],[]),([7,113],[7,11,19],[113]),([],[],[]),([13,61],[17,89],[13,61]),([],[],[]),([3,5,53],[7,173],[3,5,53]),([],[],[]),([797],[3,3,3,59],[797]),([],[],[]),([17,47],[5,307],[17,47]),([],[],[]),([3,3,89],[3,443],[3,89]),([],[],[]),([11,73],[1523],[11,73]),([],[],[]),([5,7,23],[31,43],[5,7,23]),([],[],[]),([3,269],[17,79],[3,269]),([],[],[]),([809],[3,7,7,11],[809]),([],[],[]),([811],[1621],[811]),([],[],[]),([3,271],[3,11,41],[271]),([],[],[]),([5,163],[7,11,19],[5,163]),([],[],[]),([19,43],[11,11,13],[19,43]),([],[],[]),([3,3,7,13],[3,3,139],[7,13]),([],[],[]),([821],[3,547],[821]),([],[],[]),([823],[5,7,47],[823]),([],[],[]),([3,5,5,11],[5,5,7,7],[3,11]),([],[],[]),([827],[3,19,29],[827]),([],[],[]),([829],[1657],[829]),([],[],[]),([3,277],[3,461],[277])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range832 (R D : ℕ) (lo : 832 ≤ R) (hi : R < 896) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 832 64 R D [([],[],[]),([7,7,17],[5,7,43],[7,17]),([],[],[]),([5,167],[1499],[5,167]),([],[],[]),([3,3,3,31],[3,3,3,3,17],[31]),([],[],[]),([839],[3,13,43],[839]),([],[],[]),([29,29],[3,19,29],[29]),([],[],[]),([3,281],[23,61],[3,281]),([],[],[]),([5,13,13],[13,113],[5,13]),([],[],[]),([7,11,11],[11,137],[7,11]),([],[],[]),([3,283],[3,3,157],[283]),([],[],[]),([23,37],[31,53],[23,37]),([],[],[]),([853],[5,11,31],[853]),([],[],[]),([3,3,5,19],[3,3,11,13],[5,19]),([],[],[]),([857],[3,571],[857]),([],[],[]),([859],[17,101],[859]),([],[],[]),([3,7,41],[3,3,149],[7,41]),([],[],[]),([863],[3,5,5,23],[863]),([],[],[]),([5,173],[1553],[5,173]),([],[],[]),([3,17,17],[17,83],[3,17]),([],[],[]),([11,79],[17,97],[11,79]),([],[],[]),([13,67],[1663],[13,67]),([],[],[]),([3,3,97],[3,3,7,23],[97]),([],[],[]),([5,5,5,7],[5,5,59],[5,7]),([],[],[]),([877],[1753],[877]),([],[],[]),([3,293],[7,11,19],[3,293]),([],[],[]),([881],[3,587],[881]),([],[],[]),([883],[5,353],[883]),([],[],[]),([3,5,59],[19,71],[3,5,59]),([],[],[]),([887],[3,3,197],[887]),([],[],[]),([7,127],[5,7,47],[127]),([],[],[]),([3,3,3,3,11],[3,3,3,53],[3,11]),([],[],[]),([19,47],[1721],[19,47]),([],[],[]),([5,179],[1607],[5,179])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range896 (R D : ℕ) (lo : 896 ≤ R) (hi : R < 960) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 896 64 R D [([],[],[]),([3,13,23],[3,5,5,19],[13,23]),([],[],[]),([29,31],[37,47],[29,31]),([],[],[]),([17,53],[1733],[17,53]),([],[],[]),([3,7,43],[3,7,67],[43]),([],[],[]),([5,181],[5,5,5,13],[181]),([],[],[]),([907],[7,7,37],[907]),([],[],[]),([3,3,101],[3,503],[3,101]),([],[],[]),([911],[3,607],[911]),([],[],[]),([11,83],[1733],[11,83]),([],[],[]),([3,5,61],[3,3,5,31],[61]),([],[],[]),([7,131],[1697],[7,131]),([],[],[]),([919],[11,167],[919]),([],[],[]),([3,307],[3,7,73],[307]),([],[],[]),([13,71],[41,43],[13,71]),([],[],[]),([5,5,37],[5,7,47],[5,37]),([],[],[]),([3,3,103],[3,3,3,3,19],[103]),([],[],[]),([929],[3,619],[929]),([],[],[]),([7,7,19],[7,241],[7,19]),([],[],[]),([3,311],[1553],[3,311]),([],[],[]),([5,11,17],[3,3,5,5,7],[11,17]),([],[],[]),([937],[1873],[937]),([],[],[]),([3,313],[3,521],[313]),([],[],[]),([941],[3,3,11,19],[941]),([],[],[]),([23,41],[1823],[23,41]),([],[],[]),([3,3,3,5,7],[3,3,3,3,17],[5,7]),([],[],[]),([947],[3,631],[947]),([],[],[]),([13,73],[7,7,37],[13,73]),([],[],[]),([3,317],[1583],[3,317]),([],[],[]),([953],[3,5,127],[953]),([],[],[]),([5,191],[5,7,7,7],[191]),([],[],[]),([3,11,29],[37,41],[3,11,29]),([],[],[]),([7,137],[5,5,71],[7,137])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range960 (R D : ℕ) (lo : 960 ≤ R) (hi : R < 1024) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 960 64 R D [([],[],[]),([31,31],[31,61],[31]),([],[],[]),([3,3,107],[3,13,41],[3,107]),([],[],[]),([5,193],[1733],[5,193]),([],[],[]),([967],[1933],[967]),([],[],[]),([3,17,19],[3,5,103],[17,19]),([],[],[]),([971],[3,647],[971]),([],[],[]),([7,139],[1801],[7,139]),([],[],[]),([3,5,5,13],[3,5,97],[5,13]),([],[],[]),([977],[3,3,7,31],[977]),([],[],[]),([11,89],[11,13,13],[89]),([],[],[]),([3,3,109],[3,3,181],[109]),([],[],[]),([983],[3,5,131],[983]),([],[],[]),([5,197],[29,61],[5,197]),([],[],[]),([3,7,47],[3,3,3,3,19],[7,47]),([],[],[]),([23,43],[1913],[23,43]),([],[],[]),([991],[7,283],[991]),([],[],[]),([3,331],[3,19,29],[331]),([],[],[]),([5,199],[1787],[5,199]),([],[],[]),([997],[1993],[997]),([],[],[]),([3,3,3,37],[3,3,3,61],[37]),([],[],[]),([7,11,13],[1721],[7,11,13]),([],[],[]),([17,59],[1931],[17,59]),([],[],[]),([3,5,67],[3,7,73],[5,67]),([],[],[]),([19,53],[29,67],[19,53]),([],[],[]),([1009],[2017],[1009]),([],[],[]),([3,337],[3,3,11,17],[337]),([],[],[]),([1013],[3,3,3,3,5,5],[1013]),([],[],[]),([5,7,29],[7,241],[5,29]),([],[],[]),([3,3,113],[3,563],[3,113]),([],[],[]),([1019],[3,7,97],[1019]),([],[],[]),([1021],[13,157],[1021]),([],[],[]),([3,11,31],[3,541],[11,31])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range1024 (R D : ℕ) (lo : 1024 ≤ R) (hi : R < 1088) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 1024 64 R D [([],[],[]),([5,5,41],[5,5,73],[41]),([],[],[]),([13,79],[13,151],[79]),([],[],[]),([3,7,7,7],[3,7,7,11],[7]),([],[],[]),([1031],[3,3,229],[1031]),([],[],[]),([1033],[5,7,59],[1033]),([],[],[]),([3,3,5,23],[3,521],[3,5,23]),([],[],[]),([17,61],[1997],[17,61]),([],[],[]),([1039],[31,67],[1039]),([],[],[]),([3,347],[1733],[3,347]),([],[],[]),([7,149],[1931],[7,149]),([],[],[]),([5,11,19],[5,353],[11,19]),([],[],[]),([3,349],[3,7,83],[349]),([],[],[]),([1049],[3,3,233],[1049]),([],[],[]),([1051],[11,191],[1051]),([],[],[]),([3,3,3,3,13],[3,3,3,3,3,7],[13]),([],[],[]),([5,211],[5,379],[211]),([],[],[]),([7,151],[19,103],[7,151]),([],[],[]),([3,353],[41,43],[3,353]),([],[],[]),([1061],[3,7,101],[1061]),([],[],[]),([1063],[5,5,5,17],[1063]),([],[],[]),([3,5,71],[5,5,5,13],[3,71]),([],[],[]),([11,97],[2027],[11,97]),([],[],[]),([1069],[2137],[1069]),([],[],[]),([3,3,7,17],[3,3,3,61],[7,17]),([],[],[]),([29,37],[2081],[29,37]),([],[],[]),([5,5,43],[5,383],[5,43]),([],[],[]),([3,359],[11,163],[3,359]),([],[],[]),([13,83],[2063],[13,83]),([],[],[]),([23,47],[7,13,23],[47]),([],[],[]),([3,19,19],[3,19,31],[19]),([],[],[]),([5,7,31],[5,19,19],[7,31]),([],[],[]),([1087],[41,53],[1087])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range1088 (R D : ℕ) (lo : 1088 ≤ R) (hi : R < 1152) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 1088 64 R D [([],[],[]),([3,3,11,11],[3,11,53],[3,11]),([],[],[]),([1091],[3,727],[1091]),([],[],[]),([1093],[5,19,23],[1093]),([],[],[]),([3,5,73],[3,557],[5,73]),([],[],[]),([1097],[3,17,43],[1097]),([],[],[]),([7,157],[5,11,37],[7,157]),([],[],[]),([3,367],[3,13,47],[367]),([],[],[]),([1103],[3,3,5,7,7],[1103]),([],[],[]),([5,13,17],[1873],[5,13,17]),([],[],[]),([3,3,3,41],[3,3,7,29],[3,41]),([],[],[]),([1109],[3,739],[1109]),([],[],[]),([11,101],[2111],[11,101]),([],[],[]),([3,7,53],[3,3,193],[7,53]),([],[],[]),([5,223],[2003],[5,223]),([],[],[]),([1117],[7,11,29],[1117]),([],[],[]),([3,373],[3,3,3,3,23],[373]),([],[],[]),([19,59],[5,433],[19,59]),([],[],[]),([1123],[5,449],[1123]),([],[],[]),([3,3,5,5,5],[3,5,5,23],[3,5]),([],[],[]),([7,7,23],[7,293],[7,23]),([],[],[]),([1129],[37,61],[1129]),([],[],[]),([3,13,29],[3,601],[13,29]),([],[],[]),([11,103],[2153],[11,103]),([],[],[]),([5,227],[2039],[5,227]),([],[],[]),([3,379],[3,631],[379]),([],[],[]),([17,67],[5,439],[17,67]),([],[],[]),([7,163],[2113],[7,163]),([],[],[]),([3,3,127],[3,3,211],[127]),([],[],[]),([5,229],[11,11,17],[5,229]),([],[],[]),([31,37],[17,131],[31,37]),([],[],[]),([3,383],[1913],[3,383]),([],[],[]),([1151],[3,13,59],[1151])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range1152 (R D : ℕ) (lo : 1152 ≤ R) (hi : R < 1216) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 1152 64 R D [([],[],[]),([1153],[5,461],[1153]),([],[],[]),([3,5,7,11],[3,5,109],[7,11]),([],[],[]),([13,89],[2213],[13,89]),([],[],[]),([19,61],[2239],[19,61]),([],[],[]),([3,3,3,43],[3,3,3,71],[43]),([],[],[]),([1163],[3,5,5,31],[1163]),([],[],[]),([5,233],[7,13,23],[5,233]),([],[],[]),([3,389],[29,67],[3,389]),([],[],[]),([7,167],[5,433],[7,167]),([],[],[]),([1171],[2341],[1171]),([],[],[]),([3,17,23],[1877],[3,17,23]),([],[],[]),([5,5,47],[5,419],[5,47]),([],[],[]),([11,107],[2237],[11,107]),([],[],[]),([3,3,131],[3,653],[3,131]),([],[],[]),([1181],[3,787],[1181]),([],[],[]),([7,13,13],[13,163],[7,13]),([],[],[]),([3,5,79],[3,3,3,67],[5,79]),([],[],[]),([1187],[3,7,113],[1187]),([],[],[]),([29,41],[2309],[29,41]),([],[],[]),([3,397],[3,661],[397]),([],[],[]),([1193],[3,3,5,53],[1193]),([],[],[]),([5,239],[19,113],[5,239]),([],[],[]),([3,3,7,19],[3,3,5,41],[7,19]),([],[],[]),([11,109],[43,53],[11,109]),([],[],[]),([1201],[7,7,7,7],[1201]),([],[],[]),([3,401],[2003],[3,401]),([],[],[]),([5,241],[5,433],[241]),([],[],[]),([17,71],[13,179],[17,71]),([],[],[]),([3,13,31],[3,643],[13,31]),([],[],[]),([7,173],[2243],[7,173]),([],[],[]),([1213],[5,5,97],[1213]),([],[],[]),([3,3,3,3,3,5],[3,3,3,3,23],[3,5])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range1216 (R D : ℕ) (lo : 1216 ≤ R) (hi : R < 1280) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 1216 64 R D [([],[],[]),([1217],[3,811],[1217]),([],[],[]),([23,53],[17,139],[23,53]),([],[],[]),([3,11,37],[3,647],[11,37]),([],[],[]),([1223],[3,5,163],[1223]),([],[],[]),([5,5,7,7],[5,7,59],[5,7]),([],[],[]),([3,409],[3,3,227],[409]),([],[],[]),([1229],[3,3,3,7,13],[1229]),([],[],[]),([1231],[23,107],[1231]),([],[],[]),([3,3,137],[3,683],[3,137]),([],[],[]),([5,13,19],[2099],[5,13,19]),([],[],[]),([1237],[2473],[1237]),([],[],[]),([3,7,59],[3,3,5,43],[7,59]),([],[],[]),([17,73],[2393],[17,73]),([],[],[]),([11,113],[17,139],[11,113]),([],[],[]),([3,5,83],[1901],[3,5,83]),([],[],[]),([29,43],[2423],[29,43]),([],[],[]),([1249],[11,227],[1249]),([],[],[]),([3,3,139],[3,3,3,7,11],[139]),([],[],[]),([7,179],[11,211],[7,179]),([],[],[]),([5,251],[5,11,41],[251]),([],[],[]),([3,419],[7,13,23],[3,419]),([],[],[]),([1259],[3,839],[1259]),([],[],[]),([13,97],[19,127],[13,97]),([],[],[]),([3,421],[3,701],[421]),([],[],[]),([5,11,23],[3,5,11,13],[23]),([],[],[]),([7,181],[2347],[7,181]),([],[],[]),([3,3,3,47],[3,3,233],[3,47]),([],[],[]),([31,41],[7,353],[31,41]),([],[],[]),([19,67],[23,107],[19,67]),([],[],[]),([3,5,5,17],[5,383],[3,5,17]),([],[],[]),([1277],[3,23,37],[1277]),([],[],[]),([1279],[2557],[1279])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range1280 (R D : ℕ) (lo : 1280 ≤ R) (hi : R < 1344) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 1280 64 R D [([],[],[]),([3,7,61],[3,23,29],[7,61]),([],[],[]),([1283],[3,3,3,5,19],[1283]),([],[],[]),([5,257],[2309],[5,257]),([],[],[]),([3,3,11,13],[3,3,223],[11,13]),([],[],[]),([1289],[3,859],[1289]),([],[],[]),([1291],[29,89],[1291]),([],[],[]),([3,431],[2153],[3,431]),([],[],[]),([5,7,37],[17,127],[5,7,37]),([],[],[]),([1297],[2593],[1297]),([],[],[]),([3,433],[3,7,103],[433]),([],[],[]),([1301],[3,3,17,17],[1301]),([],[],[]),([1303],[5,521],[1303]),([],[],[]),([3,3,5,29],[3,659],[3,5,29]),([],[],[]),([1307],[3,13,67],[1307]),([],[],[]),([7,11,17],[2269],[7,11,17]),([],[],[]),([3,19,23],[3,701],[19,23]),([],[],[]),([13,101],[7,359],[13,101]),([],[],[]),([5,263],[17,139],[5,263]),([],[],[]),([3,439],[3,17,43],[439]),([],[],[]),([1319],[3,3,293],[1319]),([],[],[]),([1321],[19,139],[1321]),([],[],[]),([3,3,3,7,7],[3,3,3,7,11],[7]),([],[],[]),([5,5,53],[5,11,43],[5,53]),([],[],[]),([1327],[7,379],[1327]),([],[],[]),([3,443],[2213],[3,443]),([],[],[]),([11,11,11],[3,7,11,11],[11]),([],[],[]),([31,43],[2593],[31,43]),([],[],[]),([3,5,89],[2039],[3,5,89]),([],[],[]),([7,191],[2477],[7,191]),([],[],[]),([13,103],[11,233],[13,103]),([],[],[]),([3,3,149],[3,743],[3,149]),([],[],[]),([17,79],[2591],[17,79])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range1344 (R D : ℕ) (lo : 1344 ≤ R) (hi : R < 1408) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 1344 64 R D [([],[],[]),([5,269],[2417],[5,269]),([],[],[]),([3,449],[2243],[3,449]),([],[],[]),([19,71],[2609],[19,71]),([],[],[]),([7,193],[2503],[7,193]),([],[],[]),([3,11,41],[2153],[3,11,41]),([],[],[]),([5,271],[5,487],[271]),([],[],[]),([23,59],[2633],[23,59]),([],[],[]),([3,3,151],[3,3,251],[151]),([],[],[]),([1361],[3,907],[1361]),([],[],[]),([29,47],[11,241],[29,47]),([],[],[]),([3,5,7,13],[3,647],[5,7,13]),([],[],[]),([1367],[3,911],[1367]),([],[],[]),([37,37],[37,73],[37]),([],[],[]),([3,457],[3,761],[457]),([],[],[]),([1373],[3,3,5,61],[1373]),([],[],[]),([5,5,5,11],[5,5,5,19],[11]),([],[],[]),([3,3,3,3,17],[3,3,3,83],[3,17]),([],[],[]),([7,197],[5,7,73],[197]),([],[],[]),([1381],[11,251],[1381]),([],[],[]),([3,461],[7,7,47],[3,461]),([],[],[]),([5,277],[19,131],[5,277]),([],[],[]),([19,73],[2683],[19,73]),([],[],[]),([3,463],[3,3,257],[463]),([],[],[]),([13,107],[2663],[13,107]),([],[],[]),([7,199],[29,89],[7,199]),([],[],[]),([3,3,5,31],[3,3,5,47],[31]),([],[],[]),([11,127],[2657],[11,127]),([],[],[]),([1399],[2797],[1399]),([],[],[]),([3,467],[2333],[3,467]),([],[],[]),([23,61],[7,389],[23,61]),([],[],[]),([5,281],[5,5,101],[281]),([],[],[]),([3,7,67],[3,733],[7,67])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range1408 (R D : ℕ) (lo : 1408 ≤ R) (hi : R < 1472) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 1408 64 R D [([],[],[]),([1409],[3,3,313],[1409]),([],[],[]),([17,83],[7,389],[17,83]),([],[],[]),([3,3,157],[3,3,3,3,29],[157]),([],[],[]),([5,283],[2543],[5,283]),([],[],[]),([13,109],[2713],[13,109]),([],[],[]),([3,11,43],[3,3,251],[11,43]),([],[],[]),([7,7,29],[7,7,53],[29]),([],[],[]),([1423],[5,569],[1423]),([],[],[]),([3,5,5,19],[3,5,11,13],[5,19]),([],[],[]),([1427],[3,3,317],[1427]),([],[],[]),([1429],[2857],[1429]),([],[],[]),([3,3,3,53],[3,3,263],[3,53]),([],[],[]),([1433],[3,5,191],[1433]),([],[],[]),([5,7,41],[5,479],[7,41]),([],[],[]),([3,479],[2393],[3,479]),([],[],[]),([1439],[3,7,137],[1439]),([],[],[]),([11,131],[2741],[11,131]),([],[],[]),([3,13,37],[3,769],[13,37]),([],[],[]),([5,17,17],[17,149],[5,17]),([],[],[]),([1447],[11,263],[1447]),([],[],[]),([3,3,7,23],[3,3,3,83],[7,23]),([],[],[]),([1451],[3,967],[1451]),([],[],[]),([1453],[5,7,83],[1453]),([],[],[]),([3,5,97],[3,3,13,19],[5,97]),([],[],[]),([31,47],[2837],[31,47]),([],[],[]),([1459],[2917],[1459]),([],[],[]),([3,487],[3,811],[487]),([],[],[]),([7,11,19],[2543],[7,11,19]),([],[],[]),([5,293],[2633],[5,293]),([],[],[]),([3,3,163],[3,3,271],[163]),([],[],[]),([13,113],[29,97],[13,113]),([],[],[]),([1471],[17,173],[1471])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range1472 (R D : ℕ) (lo : 1472 ≤ R) (hi : R < 1536) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 1472 64 R D [([],[],[]),([3,491],[11,223],[3,491]),([],[],[]),([5,5,59],[5,17,31],[5,59]),([],[],[]),([7,211],[7,17,23],[211]),([],[],[]),([3,17,29],[5,5,5,19],[3,17,29]),([],[],[]),([1481],[3,3,7,47],[1481]),([],[],[]),([1483],[5,593],[1483]),([],[],[]),([3,3,3,5,11],[3,3,5,7,7],[3,11]),([],[],[]),([1487],[3,991],[1487]),([],[],[]),([1489],[13,229],[1489]),([],[],[]),([3,7,71],[3,3,7,37],[71]),([],[],[]),([1493],[3,5,199],[1493]),([],[],[]),([5,13,23],[2551],[5,13,23]),([],[],[]),([3,499],[3,3,277],[499]),([],[],[]),([1499],[3,3,3,3,37],[1499]),([],[],[]),([19,79],[5,7,83],[19,79]),([],[],[]),([3,3,167],[3,7,7,17],[3,167]),([],[],[]),([5,7,43],[7,359],[5,43]),([],[],[]),([11,137],[47,61],[11,137]),([],[],[]),([3,503],[7,359],[3,503]),([],[],[]),([1511],[3,19,53],[1511]),([],[],[]),([17,89],[23,127],[17,89]),([],[],[]),([3,5,101],[5,463],[3,101]),([],[],[]),([37,41],[2957],[37,41]),([],[],[]),([7,7,31],[7,397],[7,31]),([],[],[]),([3,3,13,13],[3,3,3,7,13],[13]),([],[],[]),([1523],[3,5,7,29],[1523]),([],[],[]),([5,5,61],[5,5,109],[61]),([],[],[]),([3,509],[2543],[3,509]),([],[],[]),([11,139],[2909],[11,139]),([],[],[]),([1531],[3061],[1531]),([],[],[]),([3,7,73],[3,17,47],[7,73]),([],[],[]),([5,307],[31,89],[5,307])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range1536 (R D : ℕ) (lo : 1536 ≤ R) (hi : R < 1600) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 1536 64 R D [([],[],[]),([29,53],[41,73],[29,53]),([],[],[]),([3,3,3,3,19],[3,3,3,3,31],[19]),([],[],[]),([23,67],[41,73],[23,67]),([],[],[]),([1543],[5,617],[1543]),([],[],[]),([3,5,103],[3,787],[5,103]),([],[],[]),([7,13,17],[2699],[7,13,17]),([],[],[]),([1549],[19,163],[1549]),([],[],[]),([3,11,47],[7,353],[3,11,47]),([],[],[]),([1553],[3,3,3,5,23],[1553]),([],[],[]),([5,311],[5,13,43],[311]),([],[],[]),([3,3,173],[3,863],[3,173]),([],[],[]),([1559],[3,1039],[1559]),([],[],[]),([7,223],[11,263],[7,223]),([],[],[]),([3,521],[19,137],[3,521]),([],[],[]),([5,313],[29,97],[5,313]),([],[],[]),([1567],[13,241],[1567]),([],[],[]),([3,523],[3,13,67],[523]),([],[],[]),([1571],[3,3,349],[1571]),([],[],[]),([11,11,13],[11,263],[11,13]),([],[],[]),([3,3,5,5,7],[3,3,3,5,17],[5,7]),([],[],[]),([19,83],[43,71],[19,83]),([],[],[]),([1579],[7,11,41],[1579]),([],[],[]),([3,17,31],[3,7,11,11],[17,31]),([],[],[]),([1583],[3,5,211],[1583]),([],[],[]),([5,317],[7,11,37],[5,317]),([],[],[]),([3,23,23],[23,113],[3,23]),([],[],[]),([7,227],[5,19,31],[7,227]),([],[],[]),([37,43],[29,107],[37,43]),([],[],[]),([3,3,3,59],[3,3,293],[3,59]),([],[],[]),([5,11,29],[3,5,181],[11,29]),([],[],[]),([1597],[31,103],[1597]),([],[],[]),([3,13,41],[3,853],[13,41])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range1600 (R D : ℕ) (lo : 1600 ≤ R) (hi : R < 1664) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 1600 64 R D [([],[],[]),([1601],[3,11,97],[1601]),([],[],[]),([7,229],[2971],[7,229]),([],[],[]),([3,5,107],[11,223],[3,5,107]),([],[],[]),([1607],[3,3,3,7,17],[1607]),([],[],[]),([1609],[3217],[1609]),([],[],[]),([3,3,179],[3,19,47],[3,179]),([],[],[]),([1613],[3,5,5,43],[1613]),([],[],[]),([5,17,19],[2767],[5,17,19]),([],[],[]),([3,7,7,11],[3,3,3,7,13],[7,11]),([],[],[]),([1619],[3,13,83],[1619]),([],[],[]),([1621],[7,463],[1621]),([],[],[]),([3,541],[3,17,53],[541]),([],[],[]),([5,5,5,13],[5,5,113],[5,13]),([],[],[]),([1627],[3253],[1627]),([],[],[]),([3,3,181],[3,3,7,43],[181]),([],[],[]),([7,233],[3023],[7,233]),([],[],[]),([23,71],[19,167],[23,71]),([],[],[]),([3,5,109],[3,7,7,17],[5,109]),([],[],[]),([1637],[3,1091],[1637]),([],[],[]),([11,149],[3119],[11,149]),([],[],[]),([3,547],[3,911],[547]),([],[],[]),([31,53],[3203],[31,53]),([],[],[]),([5,7,47],[2749],[5,7,47]),([],[],[]),([3,3,3,61],[3,3,3,101],[61]),([],[],[]),([17,97],[5,7,7,13],[17,97]),([],[],[]),([13,127],[3163],[13,127]),([],[],[]),([3,19,29],[3,887],[19,29]),([],[],[]),([5,331],[5,5,7,17],[331]),([],[],[]),([1657],[3313],[1657]),([],[],[]),([3,7,79],[3,5,173],[7,79]),([],[],[]),([11,151],[29,109],[11,151]),([],[],[]),([1663],[5,5,7,19],[1663])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range1664 (R D : ℕ) (lo : 1664 ≤ R) (hi : R < 1728) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 1664 64 R D [([],[],[]),([3,3,5,37],[3,3,281],[5,37]),([],[],[]),([1667],[3,11,101],[1667]),([],[],[]),([1669],[47,71],[1669]),([],[],[]),([3,557],[11,11,23],[3,557]),([],[],[]),([7,239],[7,443],[239]),([],[],[]),([5,5,67],[5,599],[5,67]),([],[],[]),([3,13,43],[3,5,179],[13,43]),([],[],[]),([23,73],[13,251],[23,73]),([],[],[]),([41,41],[3,3,3,3,41],[41]),([],[],[]),([3,3,11,17],[3,881],[3,11,17]),([],[],[]),([5,337],[13,233],[5,337]),([],[],[]),([7,241],[53,59],[7,241]),([],[],[]),([3,563],[29,97],[3,563]),([],[],[]),([19,89],[5,5,131],[19,89]),([],[],[]),([1693],[5,677],[1693]),([],[],[]),([3,5,113],[2591],[3,5,113]),([],[],[]),([1697],[3,3,13,29],[1697]),([],[],[]),([1699],[43,79],[1699]),([],[],[]),([3,3,3,3,3,7],[3,3,3,3,3,11],[7]),([],[],[]),([13,131],[13,251],[131]),([],[],[]),([5,11,31],[5,7,83],[11,31]),([],[],[]),([3,569],[2843],[3,569]),([],[],[]),([1709],[3,17,67],[1709]),([],[],[]),([29,59],[5,23,29],[59]),([],[],[]),([3,571],[3,3,317],[571]),([],[],[]),([5,7,7,7],[7,7,59],[5,7]),([],[],[]),([17,101],[31,107],[17,101]),([],[],[]),([3,3,191],[3,953],[3,191]),([],[],[]),([1721],[3,31,37],[1721]),([],[],[]),([1723],[5,13,53],[1723]),([],[],[]),([3,5,5,23],[5,521],[3,5,23]),([],[],[]),([11,157],[19,173],[11,157])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range1728 (R D : ℕ) (lo : 1728 ≤ R) (hi : R < 1792) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 1728 64 R D [([],[],[]),([7,13,19],[5,5,11,11],[7,13,19]),([],[],[]),([3,577],[3,31,31],[577]),([],[],[]),([1733],[3,3,5,7,11],[1733]),([],[],[]),([5,347],[3119],[5,347]),([],[],[]),([3,3,193],[3,3,3,107],[193]),([],[],[]),([37,47],[5,7,97],[37,47]),([],[],[]),([1741],[59,59],[1741]),([],[],[]),([3,7,83],[3,3,3,101],[7,83]),([],[],[]),([5,349],[3137],[5,349]),([],[],[]),([1747],[7,499],[1747]),([],[],[]),([3,11,53],[2789],[3,11,53]),([],[],[]),([17,103],[17,199],[103]),([],[],[]),([1753],[5,701],[1753]),([],[],[]),([3,3,3,5,13],[3,3,3,97],[5,13]),([],[],[]),([7,251],[3257],[7,251]),([],[],[]),([1759],[3517],[1759]),([],[],[]),([3,587],[7,419],[3,587]),([],[],[]),([41,43],[11,313],[41,43]),([],[],[]),([5,353],[19,167],[5,353]),([],[],[]),([3,19,31],[3,13,73],[19,31]),([],[],[]),([29,61],[3449],[29,61]),([],[],[]),([7,11,23],[11,281],[7,23]),([],[],[]),([3,3,197],[3,983],[3,197]),([],[],[]),([5,5,71],[5,5,127],[71]),([],[],[]),([1777],[11,17,19],[1777]),([],[],[]),([3,593],[2963],[3,593]),([],[],[]),([13,137],[3413],[13,137]),([],[],[]),([1783],[5,23,31],[1783]),([],[],[]),([3,5,7,17],[3,23,37],[5,7,17]),([],[],[]),([1787],[3,3,397],[1787]),([],[],[]),([1789],[7,7,73],[1789]),([],[],[]),([3,3,199],[3,3,331],[199])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range1792 (R D : ℕ) (lo : 1792 ≤ R) (hi : R < 1856) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 1792 64 R D [([],[],[]),([11,163],[3413],[11,163]),([],[],[]),([5,359],[7,461],[5,359]),([],[],[]),([3,599],[41,73],[3,599]),([],[],[]),([7,257],[5,23,29],[7,257]),([],[],[]),([1801],[13,277],[1801]),([],[],[]),([3,601],[3,7,11,13],[601]),([],[],[]),([5,19,19],[19,167],[5,19]),([],[],[]),([13,139],[3463],[13,139]),([],[],[]),([3,3,3,67],[3,3,3,3,37],[67]),([],[],[]),([1811],[3,17,71],[1811]),([],[],[]),([7,7,37],[5,5,7,19],[7,37]),([],[],[]),([3,5,11,11],[5,7,7,11],[3,11]),([],[],[]),([23,79],[3533],[23,79]),([],[],[]),([17,107],[5,19,37],[17,107]),([],[],[]),([3,607],[3,3,337],[607]),([],[],[]),([1823],[3,3,3,3,3,3,5],[1823]),([],[],[]),([5,5,73],[5,653],[5,73]),([],[],[]),([3,3,7,29],[3,3,3,3,5,7],[29]),([],[],[]),([31,59],[43,83],[31,59]),([],[],[]),([1831],[7,523],[1831]),([],[],[]),([3,13,47],[3,11,89],[13,47]),([],[],[]),([5,367],[3299],[5,367]),([],[],[]),([11,167],[13,269],[11,167]),([],[],[]),([3,613],[3,1021],[613]),([],[],[]),([7,263],[3413],[7,263]),([],[],[]),([19,97],[3571],[19,97]),([],[],[]),([3,3,5,41],[3,5,11,17],[3,41]),([],[],[]),([1847],[3,1231],[1847]),([],[],[]),([43,43],[5,17,43],[43]),([],[],[]),([3,617],[3083],[3,617]),([],[],[]),([17,109],[3581],[17,109]),([],[],[]),([5,7,53],[29,107],[5,7,53])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range1856 (R D : ℕ) (lo : 1856 ≤ R) (hi : R < 1920) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 1856 64 R D [([],[],[]),([3,619],[3,1031],[619]),([],[],[]),([11,13,13],[13,263],[11,13]),([],[],[]),([1861],[61,61],[1861]),([],[],[]),([3,3,3,3,23],[3,3,3,113],[3,23]),([],[],[]),([5,373],[7,479],[5,373]),([],[],[]),([1867],[3733],[1867]),([],[],[]),([3,7,89],[3,3,5,5,13],[7,89]),([],[],[]),([1871],[3,29,43],[1871]),([],[],[]),([1873],[5,7,107],[1873]),([],[],[]),([3,5,5,5,5],[5,5,5,23],[3,5]),([],[],[]),([1877],[3,3,3,139],[1877]),([],[],[]),([1879],[13,17,17],[1879]),([],[],[]),([3,3,11,19],[3,3,7,47],[11,19]),([],[],[]),([7,269],[3491],[7,269]),([],[],[]),([5,13,29],[3229],[5,13,29]),([],[],[]),([3,17,37],[3,1013],[17,37]),([],[],[]),([1889],[3,1259],[1889]),([],[],[]),([31,61],[3691],[31,61]),([],[],[]),([3,631],[3,1051],[631]),([],[],[]),([5,379],[3407],[5,379]),([],[],[]),([7,271],[3517],[7,271]),([],[],[]),([3,3,211],[3,3,3,3,3,13],[211]),([],[],[]),([1901],[3,7,181],[1901]),([],[],[]),([11,173],[3623],[11,173]),([],[],[]),([3,5,127],[3,971],[5,127]),([],[],[]),([1907],[3,31,41],[1907]),([],[],[]),([23,83],[47,79],[23,83]),([],[],[]),([3,7,7,13],[3,7,139],[7,13]),([],[],[]),([1913],[3,3,5,5,17],[1913]),([],[],[]),([5,383],[11,313],[5,383]),([],[],[]),([3,3,3,71],[3,3,353],[3,71]),([],[],[]),([19,101],[3719],[19,101])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range1920 (R D : ℕ) (lo : 1920 ≤ R) (hi : R < 1984) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 1920 64 R D [([],[],[]),([17,113],[47,79],[17,113]),([],[],[]),([3,641],[3203],[3,641]),([],[],[]),([5,5,7,11],[5,5,5,5,5],[7,11]),([],[],[]),([41,47],[3767],[41,47]),([],[],[]),([3,643],[3,3,3,7,17],[643]),([],[],[]),([1931],[3,3,3,11,13],[1931]),([],[],[]),([1933],[5,773],[1933]),([],[],[]),([3,3,5,43],[3,3,3,109],[5,43]),([],[],[]),([13,149],[47,79],[13,149]),([],[],[]),([7,277],[5,719],[7,277]),([],[],[]),([3,647],[53,61],[3,647]),([],[],[]),([29,67],[17,223],[29,67]),([],[],[]),([5,389],[13,269],[5,389]),([],[],[]),([3,11,59],[13,239],[3,11,59]),([],[],[]),([1949],[3,3,433],[1949]),([],[],[]),([1951],[47,83],[1951]),([],[],[]),([3,3,7,31],[3,3,337],[7,31]),([],[],[]),([5,17,23],[3,19,59],[5,17,23]),([],[],[]),([19,103],[3793],[19,103]),([],[],[]),([3,653],[13,251],[3,653]),([],[],[]),([37,53],[3833],[37,53]),([],[],[]),([13,151],[53,71],[13,151]),([],[],[]),([3,5,131],[5,601],[3,131]),([],[],[]),([7,281],[7,521],[281]),([],[],[]),([11,179],[23,163],[11,179]),([],[],[]),([3,3,3,73],[3,3,3,11,11],[73]),([],[],[]),([1973],[3,5,263],[1973]),([],[],[]),([5,5,79],[5,7,101],[5,79]),([],[],[]),([3,659],[37,89],[3,659]),([],[],[]),([1979],[3,1319],[1979]),([],[],[]),([7,283],[3673],[7,283]),([],[],[]),([3,661],[3,3,367],[661])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range1984 (R D : ℕ) (lo : 1984 ≤ R) (hi : R < 2048) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 1984 64 R D [([],[],[]),([5,397],[43,83],[5,397]),([],[],[]),([1987],[29,137],[1987]),([],[],[]),([3,3,13,17],[3,3,349],[13,17]),([],[],[]),([11,181],[17,223],[11,181]),([],[],[]),([1993],[5,797],[1993]),([],[],[]),([3,5,7,19],[3,953],[5,7,19]),([],[],[]),([1997],[3,11,11,11],[1997]),([],[],[]),([1999],[7,571],[1999]),([],[],[]),([3,23,29],[53,61],[3,23,29]),([],[],[]),([2003],[3,3,5,89],[2003]),([],[],[]),([5,401],[5,7,103],[401]),([],[],[]),([3,3,223],[3,3,7,53],[223]),([],[],[]),([7,7,41],[7,17,31],[7,41]),([],[],[]),([2011],[4021],[2011]),([],[],[]),([3,11,61],[3,3,3,7,17],[11,61]),([],[],[]),([5,13,31],[5,691],[13,31]),([],[],[]),([2017],[37,109],[2017]),([],[],[]),([3,673],[3,19,59],[673]),([],[],[]),([43,47],[59,67],[43,47]),([],[],[]),([7,17,17],[5,17,43],[7,17]),([],[],[]),([3,3,3,3,5,5],[3,3,3,5,23],[3,5]),([],[],[]),([2027],[3,7,193],[2027]),([],[],[]),([2029],[4057],[2029]),([],[],[]),([3,677],[17,199],[3,677]),([],[],[]),([19,107],[7,563],[19,107]),([],[],[]),([5,11,37],[5,5,139],[11,37]),([],[],[]),([3,7,97],[3,1063],[7,97]),([],[],[]),([2039],[3,3,3,151],[2039]),([],[],[]),([13,157],[7,13,43],[157]),([],[],[]),([3,3,227],[3,11,103],[3,227]),([],[],[]),([5,409],[3677],[5,409]),([],[],[]),([23,89],[7,569],[23,89])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range2048 (R D : ℕ) (lo : 2048 ≤ R) (hi : R < 2112) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 2048 64 R D [([],[],[]),([3,683],[3413],[3,683]),([],[],[]),([7,293],[3803],[7,293]),([],[],[]),([2053],[5,821],[2053]),([],[],[]),([3,5,137],[7,449],[3,5,137]),([],[],[]),([11,11,17],[11,347],[11,17]),([],[],[]),([29,71],[4019],[29,71]),([],[],[]),([3,3,229],[3,3,3,127],[229]),([],[],[]),([2063],[3,5,5,5,11],[2063]),([],[],[]),([5,7,59],[3457],[5,7,59]),([],[],[]),([3,13,53],[3,5,13,17],[53]),([],[],[]),([2069],[3,7,197],[2069]),([],[],[]),([19,109],[5,11,73],[19,109]),([],[],[]),([3,691],[3,1151],[691]),([],[],[]),([5,5,83],[5,743],[5,83]),([],[],[]),([31,67],[4057],[31,67]),([],[],[]),([3,3,3,7,11],[3,3,3,3,3,13],[7,11]),([],[],[]),([2081],[3,19,73],[2081]),([],[],[]),([2083],[5,7,7,17],[2083]),([],[],[]),([3,5,139],[3,1063],[5,139]),([],[],[]),([2087],[3,13,107],[2087]),([],[],[]),([2089],[4177],[2089]),([],[],[]),([3,17,41],[3371],[3,17,41]),([],[],[]),([7,13,23],[3677],[7,13,23]),([],[],[]),([5,419],[3767],[5,419]),([],[],[]),([3,3,233],[3,1163],[3,233]),([],[],[]),([2099],[3,1399],[2099]),([],[],[]),([11,191],[4001],[11,191]),([],[],[]),([3,701],[31,113],[3,701]),([],[],[]),([5,421],[5,757],[421]),([],[],[]),([7,7,43],[7,7,79],[43]),([],[],[]),([3,19,37],[3,5,227],[19,37]),([],[],[]),([2111],[3,3,7,67],[2111])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range2112 (R D : ℕ) (lo : 2112 ≤ R) (hi : R < 2176) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 2112 64 R D [([],[],[]),([2113],[5,5,13,13],[2113]),([],[],[]),([3,3,5,47],[3,29,37],[3,5,47]),([],[],[]),([29,73],[4133],[29,73]),([],[],[]),([13,163],[17,239],[13,163]),([],[],[]),([3,7,101],[3,3,3,3,41],[7,101]),([],[],[]),([11,193],[13,311],[11,193]),([],[],[]),([5,5,5,17],[5,5,149],[5,17]),([],[],[]),([3,709],[3,1181],[709]),([],[],[]),([2129],[3,3,11,43],[2129]),([],[],[]),([2131],[4261],[2131]),([],[],[]),([3,3,3,79],[3,3,3,131],[79]),([],[],[]),([5,7,61],[5,5,11,13],[7,61]),([],[],[]),([2137],[4273],[2137]),([],[],[]),([3,23,31],[3,1153],[23,31]),([],[],[]),([2141],[3,1427],[2141]),([],[],[]),([2143],[5,857],[2143]),([],[],[]),([3,5,11,13],[3,3,3,5,23],[11,13]),([],[],[]),([19,113],[23,181],[19,113]),([],[],[]),([7,307],[5,797],[7,307]),([],[],[]),([3,3,239],[3,1193],[3,239]),([],[],[]),([2153],[3,5,7,41],[2153]),([],[],[]),([5,431],[5,5,5,31],[431]),([],[],[]),([3,719],[3593],[3,719]),([],[],[]),([17,127],[5,5,167],[17,127]),([],[],[]),([2161],[29,149],[2161]),([],[],[]),([3,7,103],[3,1129],[7,103]),([],[],[]),([5,433],[17,229],[5,433]),([],[],[]),([11,197],[4127],[11,197]),([],[],[]),([3,3,241],[3,3,401],[241]),([],[],[]),([13,167],[23,181],[13,167]),([],[],[]),([41,53],[4253],[41,53]),([],[],[]),([3,5,5,29],[5,659],[3,5,29])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range2176 (R D : ℕ) (lo : 2176 ≤ R) (hi : R < 2240) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 2176 64 R D [([],[],[]),([7,311],[11,367],[7,311]),([],[],[]),([2179],[4357],[2179]),([],[],[]),([3,727],[3,7,173],[727]),([],[],[]),([37,59],[4271],[37,59]),([],[],[]),([5,19,23],[3769],[5,19,23]),([],[],[]),([3,3,3,3,3,3,3],[3,3,3,3,3,3,5],[3]),([],[],[]),([11,199],[11,379],[199]),([],[],[]),([7,313],[17,239],[7,313]),([],[],[]),([3,17,43],[3,3,3,131],[17,43]),([],[],[]),([5,439],[3947],[5,439]),([],[],[]),([13,13,13],[5,5,13,13],[13]),([],[],[]),([3,733],[3,3,11,37],[733]),([],[],[]),([31,71],[11,17,23],[31,71]),([],[],[]),([2203],[5,881],[2203]),([],[],[]),([3,3,5,7,7],[3,3,3,7,17],[5,7]),([],[],[]),([2207],[3,1471],[2207]),([],[],[]),([47,47],[3,31,47],[47]),([],[],[]),([3,11,67],[3,11,107],[67]),([],[],[]),([2213],[3,5,5,59],[2213]),([],[],[]),([5,443],[7,569],[5,443]),([],[],[]),([3,739],[3,1231],[739]),([],[],[]),([7,317],[5,823],[7,317]),([],[],[]),([2221],[4441],[2221]),([],[],[]),([3,3,13,19],[3,3,17,23],[13,19]),([],[],[]),([5,5,89],[5,797],[5,89]),([],[],[]),([17,131],[59,73],[17,131]),([],[],[]),([3,743],[47,79],[3,743]),([],[],[]),([23,97],[43,101],[23,97]),([],[],[]),([7,11,29],[7,13,43],[11,29]),([],[],[]),([3,5,149],[13,263],[3,5,149]),([],[],[]),([2237],[3,3,7,71],[2237]),([],[],[]),([2239],[11,11,37],[2239])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range2240 (R D : ℕ) (lo : 2240 ≤ R) (hi : R < 2304) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 2240 64 R D [([],[],[]),([3,3,3,83],[3,3,7,59],[3,83]),([],[],[]),([2243],[3,5,13,23],[2243]),([],[],[]),([5,449],[11,367],[5,449]),([],[],[]),([3,7,107],[3,3,17,23],[7,107]),([],[],[]),([13,173],[19,227],[13,173]),([],[],[]),([2251],[7,643],[2251]),([],[],[]),([3,751],[3,3,3,139],[751]),([],[],[]),([5,11,41],[3,5,257],[11,41]),([],[],[]),([37,61],[7,631],[37,61]),([],[],[]),([3,3,251],[3,7,179],[3,251]),([],[],[]),([7,17,19],[3989],[7,17,19]),([],[],[]),([31,73],[4423],[31,73]),([],[],[]),([3,5,151],[3,3,5,7,11],[151]),([],[],[]),([2267],[3,1511],[2267]),([],[],[]),([2269],[13,349],[2269]),([],[],[]),([3,757],[3,13,97],[757]),([],[],[]),([2273],[3,3,5,101],[2273]),([],[],[]),([5,5,7,13],[5,743],[5,7,13]),([],[],[]),([3,3,11,23],[3,11,109],[3,23]),([],[],[]),([43,53],[4463],[43,53]),([],[],[]),([2281],[4561],[2281]),([],[],[]),([3,761],[3803],[3,761]),([],[],[]),([5,457],[7,587],[5,457]),([],[],[]),([2287],[17,269],[2287]),([],[],[]),([3,7,109],[3,5,239],[7,109]),([],[],[]),([29,79],[5,5,179],[29,79]),([],[],[]),([2293],[5,7,131],[2293]),([],[],[]),([3,3,3,5,17],[3,3,383],[3,5,17]),([],[],[]),([2297],[3,1531],[2297]),([],[],[]),([11,11,19],[11,389],[11,19]),([],[],[]),([3,13,59],[3,1231],[13,59]),([],[],[]),([7,7,47],[5,7,11,11],[7,47])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range2304 (R D : ℕ) (lo : 2304 ≤ R) (hi : R < 2368) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 2304 64 R D [([],[],[]),([5,461],[5,829],[461]),([],[],[]),([3,769],[3,3,7,61],[769]),([],[],[]),([2309],[3,3,3,3,3,19],[2309]),([],[],[]),([2311],[4621],[2311]),([],[],[]),([3,3,257],[3,1283],[3,257]),([],[],[]),([5,463],[23,181],[5,463]),([],[],[]),([7,331],[4297],[7,331]),([],[],[]),([3,773],[3863],[3,773]),([],[],[]),([11,211],[4421],[11,211]),([],[],[]),([23,101],[4523],[23,101]),([],[],[]),([3,5,5,31],[3,5,5,47],[31]),([],[],[]),([13,179],[4463],[13,179]),([],[],[]),([17,137],[5,17,53],[137]),([],[],[]),([3,3,7,37],[3,3,13,31],[7,37]),([],[],[]),([2333],[3,5,311],[2333]),([],[],[]),([5,467],[13,17,19],[5,467]),([],[],[]),([3,19,41],[3,1259],[19,41]),([],[],[]),([2339],[3,1559],[2339]),([],[],[]),([2341],[31,151],[2341]),([],[],[]),([3,11,71],[19,197],[3,11,71]),([],[],[]),([5,7,67],[3929],[5,7,67]),([],[],[]),([2347],[13,19,19],[2347]),([],[],[]),([3,3,3,3,29],[3,3,3,11,13],[3,29]),([],[],[]),([2351],[3,1567],[2351]),([],[],[]),([13,181],[4513],[13,181]),([],[],[]),([3,5,157],[3,1201],[5,157]),([],[],[]),([2357],[3,1571],[2357]),([],[],[]),([7,337],[5,5,5,5,7],[337]),([],[],[]),([3,787],[3,3,19,23],[787]),([],[],[]),([17,139],[7,653],[17,139]),([],[],[]),([5,11,43],[5,809],[11,43]),([],[],[]),([3,3,263],[3,13,101],[3,263])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range2368 (R D : ℕ) (lo : 2368 ≤ R) (hi : R < 2432) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 2368 64 R D [([],[],[]),([23,103],[7,659],[23,103]),([],[],[]),([2371],[11,431],[2371]),([],[],[]),([3,7,113],[3,3,7,59],[113]),([],[],[]),([5,5,5,19],[5,5,167],[5,19]),([],[],[]),([2377],[7,7,97],[2377]),([],[],[]),([3,13,61],[3,19,67],[13,61]),([],[],[]),([2381],[3,3,23,23],[2381]),([],[],[]),([2383],[5,953],[2383]),([],[],[]),([3,3,5,53],[3,7,173],[3,5,53]),([],[],[]),([7,11,31],[53,79],[7,11,31]),([],[],[]),([2389],[17,281],[2389]),([],[],[]),([3,797],[7,569],[3,797]),([],[],[]),([2393],[3,5,11,29],[2393]),([],[],[]),([5,479],[59,73],[5,479]),([],[],[]),([3,17,47],[53,73],[3,17,47]),([],[],[]),([2399],[3,3,13,41],[2399]),([],[],[]),([7,7,7,7],[7,7,7,13],[7]),([],[],[]),([3,3,3,89],[3,3,443],[3,89]),([],[],[]),([5,13,37],[4133],[5,13,37]),([],[],[]),([29,83],[4703],[29,83]),([],[],[]),([3,11,73],[3,1283],[11,73]),([],[],[]),([2411],[3,1607],[2411]),([],[],[]),([19,127],[31,151],[19,127]),([],[],[]),([3,5,7,23],[3,13,89],[5,7,23]),([],[],[]),([2417],[3,3,3,179],[2417]),([],[],[]),([41,59],[7,677],[41,59]),([],[],[]),([3,3,269],[3,17,79],[3,269]),([],[],[]),([2423],[3,5,17,19],[2423]),([],[],[]),([5,5,97],[5,11,79],[5,97]),([],[],[]),([3,809],[13,311],[3,809]),([],[],[]),([7,347],[5,17,53],[7,347]),([],[],[]),([11,13,17],[19,229],[11,13,17])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range2432 (R D : ℕ) (lo : 2432 ≤ R) (hi : R < 2496) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 2432 64 R D [([],[],[]),([3,811],[3,7,193],[811]),([],[],[]),([5,487],[29,151],[5,487]),([],[],[]),([2437],[11,443],[2437]),([],[],[]),([3,3,271],[3,3,11,41],[271]),([],[],[]),([2441],[3,1627],[2441]),([],[],[]),([7,349],[23,197],[7,349]),([],[],[]),([3,5,163],[3,29,43],[5,163]),([],[],[]),([2447],[3,7,233],[2447]),([],[],[]),([31,79],[4789],[31,79]),([],[],[]),([3,19,43],[3,1321],[19,43]),([],[],[]),([11,223],[4673],[11,223]),([],[],[]),([5,491],[5,883],[491]),([],[],[]),([3,3,3,7,13],[3,3,3,139],[7,13]),([],[],[]),([2459],[3,11,149],[2459]),([],[],[]),([23,107],[4793],[23,107]),([],[],[]),([3,821],[11,373],[3,821]),([],[],[]),([5,17,29],[3,3,11,43],[5,17,29]),([],[],[]),([2467],[4933],[2467]),([],[],[]),([3,823],[3,3,457],[823]),([],[],[]),([7,353],[4583],[7,353]),([],[],[]),([2473],[5,23,43],[2473]),([],[],[]),([3,3,5,5,11],[3,5,5,7,7],[3,11]),([],[],[]),([2477],[3,13,127],[2477]),([],[],[]),([37,67],[5,971],[37,67]),([],[],[]),([3,827],[4133],[3,827]),([],[],[]),([13,191],[11,433],[13,191]),([],[],[]),([5,7,71],[5,7,7,17],[71]),([],[],[]),([3,829],[3,1381],[829]),([],[],[]),([19,131],[11,439],[19,131]),([],[],[]),([47,53],[19,257],[47,53]),([],[],[]),([3,3,277],[3,3,461],[277]),([],[],[]),([5,499],[7,641],[5,499])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range2496 (R D : ℕ) (lo : 2496 ≤ R) (hi : R < 2560) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 2496 64 R D [([],[],[]),([11,227],[67,71],[11,227]),([],[],[]),([3,7,7,17],[3,3,7,61],[7,17]),([],[],[]),([41,61],[13,13,29],[41,61]),([],[],[]),([2503],[5,7,11,13],[2503]),([],[],[]),([3,5,167],[3833],[3,5,167]),([],[],[]),([23,109],[19,257],[23,109]),([],[],[]),([13,193],[4813],[13,193]),([],[],[]),([3,3,3,3,31],[3,3,3,3,3,17],[31]),([],[],[]),([7,359],[59,79],[7,359]),([],[],[]),([5,503],[4523],[5,503]),([],[],[]),([3,839],[7,599],[3,839]),([],[],[]),([11,229],[4799],[11,229]),([],[],[]),([2521],[71,71],[2521]),([],[],[]),([3,29,29],[11,13,29],[3,29]),([],[],[]),([5,5,101],[5,5,181],[101]),([],[],[]),([7,19,19],[19,241],[7,19]),([],[],[]),([3,3,281],[3,23,61],[3,281]),([],[],[]),([2531],[3,7,241],[2531]),([],[],[]),([17,149],[13,13,29],[17,149]),([],[],[]),([3,5,13,13],[3,13,97],[5,13]),([],[],[]),([43,59],[4973],[43,59]),([],[],[]),([2539],[5077],[2539]),([],[],[]),([3,7,11,11],[3,3,3,11,13],[7,11]),([],[],[]),([2543],[3,3,5,113],[2543]),([],[],[]),([5,509],[23,199],[5,509]),([],[],[]),([3,3,283],[3,3,3,157],[283]),([],[],[]),([2549],[3,1699],[2549]),([],[],[]),([2551],[5101],[2551]),([],[],[]),([3,23,37],[3,7,197],[23,37]),([],[],[]),([5,7,73],[4283],[5,7,73]),([],[],[]),([2557],[5113],[2557]),([],[],[]),([3,853],[3,7,7,29],[853])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range2560 (R D : ℕ) (lo : 2560 ≤ R) (hi : R < 2624) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 2560 64 R D [([],[],[]),([13,197],[17,17,17],[13,197]),([],[],[]),([11,233],[19,257],[11,233]),([],[],[]),([3,3,3,5,19],[3,3,3,11,13],[5,19]),([],[],[]),([17,151],[4967],[17,151]),([],[],[]),([7,367],[5,953],[7,367]),([],[],[]),([3,857],[4283],[3,857]),([],[],[]),([31,83],[7,719],[31,83]),([],[],[]),([5,5,103],[5,13,71],[5,103]),([],[],[]),([3,859],[3,3,3,3,53],[859]),([],[],[]),([2579],[3,3,3,191],[2579]),([],[],[]),([29,89],[5,1009],[29,89]),([],[],[]),([3,3,7,41],[3,3,3,149],[7,41]),([],[],[]),([5,11,47],[3,5,5,59],[11,47]),([],[],[]),([13,199],[7,709],[13,199]),([],[],[]),([3,863],[19,227],[3,863]),([],[],[]),([2591],[3,11,157],[2591]),([],[],[]),([2593],[5,17,61],[2593]),([],[],[]),([3,5,173],[11,19,19],[3,5,173]),([],[],[]),([7,7,53],[7,683],[7,53]),([],[],[]),([23,113],[61,83],[23,113]),([],[],[]),([3,3,17,17],[3,17,83],[3,17]),([],[],[]),([19,137],[5051],[19,137]),([],[],[]),([5,521],[5,937],[521]),([],[],[]),([3,11,79],[3,3,463],[11,79]),([],[],[]),([2609],[3,37,47],[2609]),([],[],[]),([7,373],[29,167],[7,373]),([],[],[]),([3,13,67],[3,1399],[13,67]),([],[],[]),([5,523],[4703],[5,523]),([],[],[]),([2617],[5233],[2617]),([],[],[]),([3,3,3,97],[3,3,3,7,23],[97]),([],[],[]),([2621],[3,1747],[2621]),([],[],[]),([43,61],[37,139],[43,61])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range2624 (R D : ℕ) (lo : 2624 ≤ R) (hi : R < 2688) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 2624 64 R D [([],[],[]),([3,5,5,5,7],[3,3,5,5,17],[5,7]),([],[],[]),([37,71],[5147],[37,71]),([],[],[]),([11,239],[5009],[11,239]),([],[],[]),([3,877],[3,3,487],[877]),([],[],[]),([2633],[3,3,3,3,5,13],[2633]),([],[],[]),([5,17,31],[5,911],[17,31]),([],[],[]),([3,3,293],[3,7,11,19],[3,293]),([],[],[]),([7,13,29],[5,7,7,19],[13,29]),([],[],[]),([19,139],[5,5,5,41],[19,139]),([],[],[]),([3,881],[7,17,37],[3,881]),([],[],[]),([5,23,23],[7,23,29],[5,23]),([],[],[]),([2647],[67,79],[2647]),([],[],[]),([3,883],[3,1471],[883]),([],[],[]),([11,241],[5051],[11,241]),([],[],[]),([7,379],[7,19,37],[379]),([],[],[]),([3,3,5,59],[3,19,71],[3,5,59]),([],[],[]),([2657],[3,7,11,23],[2657]),([],[],[]),([2659],[13,409],[2659]),([],[],[]),([3,887],[11,13,31],[3,887]),([],[],[]),([2663],[3,5,5,71],[2663]),([],[],[]),([5,13,41],[5,7,131],[13,41]),([],[],[]),([3,7,127],[3,7,199],[127]),([],[],[]),([17,157],[5,1033],[17,157]),([],[],[]),([2671],[7,7,109],[2671]),([],[],[]),([3,3,3,3,3,11],[3,3,3,3,53],[3,11]),([],[],[]),([5,5,107],[5,7,137],[5,107]),([],[],[]),([2677],[53,101],[2677]),([],[],[]),([3,19,47],[3,5,17,17],[19,47]),([],[],[]),([7,383],[4973],[7,383]),([],[],[]),([2683],[5,29,37],[2683]),([],[],[]),([3,5,179],[7,587],[3,5,179]),([],[],[]),([2687],[3,3,3,199],[2687])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range2688 (R D : ℕ) (lo : 2688 ≤ R) (hi : R < 2752) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 2688 64 R D [([],[],[]),([2689],[19,283],[2689]),([],[],[]),([3,3,13,23],[3,3,5,5,19],[13,23]),([],[],[]),([2693],[3,5,359],[2693]),([],[],[]),([5,7,7,11],[5,5,5,5,7],[7,11]),([],[],[]),([3,29,31],[3,1459],[29,31]),([],[],[]),([2699],[3,7,257],[2699]),([],[],[]),([37,73],[67,79],[37,73]),([],[],[]),([3,17,53],[11,397],[3,17,53]),([],[],[]),([5,541],[5,7,139],[541]),([],[],[]),([2707],[5413],[2707]),([],[],[]),([3,3,7,43],[3,3,7,67],[43]),([],[],[]),([2711],[3,13,139],[2711]),([],[],[]),([2713],[5,5,7,31],[2713]),([],[],[]),([3,5,181],[3,5,277],[181]),([],[],[]),([11,13,19],[4877],[11,13,19]),([],[],[]),([2719],[5437],[2719]),([],[],[]),([3,907],[3,1511],[907]),([],[],[]),([7,389],[5051],[7,389]),([],[],[]),([5,5,109],[5,977],[5,109]),([],[],[]),([3,3,3,101],[3,3,503],[3,101]),([],[],[]),([2729],[3,17,107],[2729]),([],[],[]),([2731],[43,127],[2731]),([],[],[]),([3,911],[29,157],[3,911]),([],[],[]),([5,547],[4919],[5,547]),([],[],[]),([7,17,23],[13,373],[7,17,23]),([],[],[]),([3,11,83],[29,151],[3,11,83]),([],[],[]),([2741],[3,3,3,7,29],[2741]),([],[],[]),([13,211],[19,277],[13,211]),([],[],[]),([3,3,5,61],[3,3,3,5,31],[61]),([],[],[]),([41,67],[5387],[41,67]),([],[],[]),([2749],[23,239],[2749]),([],[],[]),([3,7,131],[3,3,479],[7,131])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range2752 (R D : ℕ) (lo : 2752 ≤ R) (hi : R < 2816) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 2752 64 R D [([],[],[]),([2753],[3,5,367],[2753]),([],[],[]),([5,19,29],[13,367],[5,19,29]),([],[],[]),([3,919],[3,1531],[919]),([],[],[]),([31,89],[5399],[31,89]),([],[],[]),([11,251],[5261],[11,251]),([],[],[]),([3,3,307],[3,3,7,73],[307]),([],[],[]),([5,7,79],[4637],[5,7,79]),([],[],[]),([2767],[11,503],[2767]),([],[],[]),([3,13,71],[3,1483],[13,71]),([],[],[]),([17,163],[31,173],[17,163]),([],[],[]),([47,59],[5441],[47,59]),([],[],[]),([3,5,5,37],[3,5,281],[5,37]),([],[],[]),([2777],[3,3,617],[2777]),([],[],[]),([7,397],[5,1031],[7,397]),([],[],[]),([3,3,3,103],[3,3,3,3,3,19],[103]),([],[],[]),([11,11,23],[11,11,43],[23]),([],[],[]),([5,557],[5009],[5,557]),([],[],[]),([3,929],[4643],[3,929]),([],[],[]),([2789],[3,11,13,13],[2789]),([],[],[]),([2791],[5581],[2791]),([],[],[]),([3,7,7,19],[3,5,7,41],[7,19]),([],[],[]),([5,13,43],[17,283],[5,13,43]),([],[],[]),([2797],[7,17,47],[2797]),([],[],[]),([3,3,311],[3,1553],[3,311]),([],[],[]),([2801],[3,1867],[2801]),([],[],[]),([2803],[5,19,59],[2803]),([],[],[]),([3,5,11,17],[5,19,43],[3,11,17]),([],[],[]),([7,401],[41,127],[7,401]),([],[],[]),([53,53],[3,5,7,53],[53]),([],[],[]),([3,937],[3,7,223],[937]),([],[],[]),([29,97],[5501],[29,97]),([],[],[]),([5,563],[61,83],[5,563])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range2816 (R D : ℕ) (lo : 2816 ≤ R) (hi : R < 2880) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 2816 64 R D [([],[],[]),([3,3,313],[3,3,521],[313]),([],[],[]),([2819],[3,1879],[2819]),([],[],[]),([7,13,31],[17,293],[7,13,31]),([],[],[]),([3,941],[4703],[3,941]),([],[],[]),([5,5,113],[5,1013],[5,113]),([],[],[]),([11,257],[5387],[11,257]),([],[],[]),([3,23,41],[13,353],[3,23,41]),([],[],[]),([19,149],[5,7,157],[19,149]),([],[],[]),([2833],[5,11,103],[2833]),([],[],[]),([3,3,3,3,5,7],[3,3,3,3,3,17],[5,7]),([],[],[]),([2837],[3,31,61],[2837]),([],[],[]),([17,167],[5,7,157],[17,167]),([],[],[]),([3,947],[4733],[3,947]),([],[],[]),([2843],[3,5,379],[2843]),([],[],[]),([5,569],[7,17,43],[5,569]),([],[],[]),([3,13,73],[3,5,5,61],[13,73]),([],[],[]),([7,11,37],[5009],[7,11,37]),([],[],[]),([2851],[5701],[2851]),([],[],[]),([3,3,317],[3,1583],[3,317]),([],[],[]),([5,571],[5,13,79],[571]),([],[],[]),([2857],[29,197],[2857]),([],[],[]),([3,953],[11,433],[3,953]),([],[],[]),([2861],[3,1907],[2861]),([],[],[]),([7,409],[47,113],[7,409]),([],[],[]),([3,5,191],[5,877],[3,191]),([],[],[]),([47,61],[17,331],[47,61]),([],[],[]),([19,151],[5569],[19,151]),([],[],[]),([3,3,11,29],[3,37,41],[3,11,29]),([],[],[]),([13,13,17],[7,13,59],[13,17]),([],[],[]),([5,5,5,23],[5,5,7,29],[5,23]),([],[],[]),([3,7,137],[3,3,3,167],[7,137]),([],[],[]),([2879],[3,19,101],[2879])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range2880 (R D : ℕ) (lo : 2880 ≤ R) (hi : R < 2944) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 2880 64 R D [([],[],[]),([43,67],[5653],[43,67]),([],[],[]),([3,31,31],[3,3,17,31],[31]),([],[],[]),([5,577],[5189],[5,577]),([],[],[]),([2887],[23,251],[2887]),([],[],[]),([3,3,3,107],[3,3,13,41],[3,107]),([],[],[]),([7,7,59],[7,761],[7,59]),([],[],[]),([11,263],[37,149],[11,263]),([],[],[]),([3,5,193],[3,7,211],[5,193]),([],[],[]),([2897],[3,1931],[2897]),([],[],[]),([13,223],[5563],[13,223]),([],[],[]),([3,967],[3,3,3,179],[967]),([],[],[]),([2903],[3,3,3,5,43],[2903]),([],[],[]),([5,7,83],[11,443],[5,7,83]),([],[],[]),([3,3,17,19],[3,3,5,103],[17,19]),([],[],[]),([2909],[3,7,277],[2909]),([],[],[]),([41,71],[5711],[41,71]),([],[],[]),([3,971],[23,211],[3,971]),([],[],[]),([5,11,53],[3,3,3,5,37],[11,53]),([],[],[]),([2917],[19,307],[2917]),([],[],[]),([3,7,139],[3,5,5,61],[7,139]),([],[],[]),([23,127],[5693],[23,127]),([],[],[]),([37,79],[11,521],[37,79]),([],[],[]),([3,3,5,5,13],[3,3,5,97],[5,13]),([],[],[]),([2927],[3,1951],[2927]),([],[],[]),([29,101],[17,337],[29,101]),([],[],[]),([3,977],[19,257],[3,977]),([],[],[]),([7,419],[5441],[7,419]),([],[],[]),([5,587],[5279],[5,587]),([],[],[]),([3,11,89],[7,11,61],[3,89]),([],[],[]),([2939],[3,3,653],[2939]),([],[],[]),([17,173],[5693],[17,173]),([],[],[]),([3,3,3,109],[3,3,3,181],[109])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range2944 (R D : ℕ) (lo : 2944 ≤ R) (hi : R < 3008) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 2944 64 R D [([],[],[]),([5,19,31],[5,1021],[19,31]),([],[],[]),([7,421],[7,11,71],[421]),([],[],[]),([3,983],[17,17,17],[3,983]),([],[],[]),([13,227],[7,809],[13,227]),([],[],[]),([2953],[5,1181],[2953]),([],[],[]),([3,5,197],[4523],[3,5,197]),([],[],[]),([2957],[3,3,3,3,73],[2957]),([],[],[]),([11,269],[5639],[11,269]),([],[],[]),([3,3,7,47],[3,3,3,3,3,19],[7,47]),([],[],[]),([2963],[3,5,5,79],[2963]),([],[],[]),([5,593],[5333],[5,593]),([],[],[]),([3,23,43],[3,3,5,107],[23,43]),([],[],[]),([2969],[3,1979],[2969]),([],[],[]),([2971],[13,457],[2971]),([],[],[]),([3,991],[3,13,127],[991]),([],[],[]),([5,5,7,17],[5,11,89],[5,7,17]),([],[],[]),([13,229],[29,197],[13,229]),([],[],[]),([3,3,331],[3,3,19,29],[331]),([],[],[]),([11,271],[13,19,23],[11,271]),([],[],[]),([19,157],[5791],[19,157]),([],[],[]),([3,5,199],[3,1523],[5,199]),([],[],[]),([29,103],[5843],[29,103]),([],[],[]),([7,7,61],[7,787],[7,61]),([],[],[]),([3,997],[3,11,151],[997]),([],[],[]),([41,73],[7,839],[41,73]),([],[],[]),([5,599],[5387],[5,599]),([],[],[]),([3,3,3,3,37],[3,3,3,3,61],[37]),([],[],[]),([2999],[3,1999],[2999]),([],[],[]),([3001],[17,353],[3001]),([],[],[]),([3,7,11,13],[3,1481],[7,11,13]),([],[],[]),([5,601],[5,23,47],[601]),([],[],[]),([31,97],[7,29,29],[31,97])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range3008 (R D : ℕ) (lo : 3008 ≤ R) (hi : R < 3072) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 3008 64 R D [([],[],[]),([3,17,59],[5,7,139],[3,17,59]),([],[],[]),([3011],[3,3,3,223],[3011]),([],[],[]),([23,131],[7,839],[23,131]),([],[],[]),([3,3,5,67],[3,3,7,73],[5,67]),([],[],[]),([7,431],[29,193],[7,431]),([],[],[]),([3019],[6037],[3019]),([],[],[]),([3,19,53],[3,7,233],[19,53]),([],[],[]),([3023],[3,5,13,31],[3023]),([],[],[]),([5,5,11,11],[5,5,11,19],[11]),([],[],[]),([3,1009],[3,41,41],[1009]),([],[],[]),([13,233],[5813],[13,233]),([],[],[]),([7,433],[5623],[7,433]),([],[],[]),([3,3,337],[3,3,3,11,17],[337]),([],[],[]),([5,607],[53,103],[5,607]),([],[],[]),([3037],[6073],[3037]),([],[],[]),([3,1013],[61,83],[3,1013]),([],[],[]),([3041],[3,2027],[3041]),([],[],[]),([17,179],[43,137],[17,179]),([],[],[]),([3,5,7,29],[3,7,11,19],[5,29]),([],[],[]),([11,277],[5807],[11,277]),([],[],[]),([3049],[7,13,67],[3049]),([],[],[]),([3,3,3,113],[3,3,563],[3,113]),([],[],[]),([43,71],[13,461],[43,71]),([],[],[]),([5,13,47],[19,277],[5,13,47]),([],[],[]),([3,1019],[11,463],[3,1019]),([],[],[]),([7,19,23],[5,1087],[7,19,23]),([],[],[]),([3061],[6121],[3061]),([],[],[]),([3,1021],[3,3,3,3,3,3,7],[1021]),([],[],[]),([5,613],[37,149],[5,613]),([],[],[]),([3067],[6133],[3067]),([],[],[]),([3,3,11,31],[3,3,541],[11,31]),([],[],[]),([37,83],[19,317],[37,83])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range3072 (R D : ℕ) (lo : 3072 ≤ R) (hi : R < 3136) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 3072 64 R D [([],[],[]),([7,439],[5701],[7,439]),([],[],[]),([3,5,5,41],[5,5,11,17],[3,41]),([],[],[]),([17,181],[7,23,37],[17,181]),([],[],[]),([3079],[47,131],[3079]),([],[],[]),([3,13,79],[3,13,127],[79]),([],[],[]),([3083],[3,3,5,137],[3083]),([],[],[]),([5,617],[31,179],[5,617]),([],[],[]),([3,3,7,7,7],[3,3,7,7,11],[7]),([],[],[]),([3089],[3,29,71],[3089]),([],[],[]),([11,281],[43,137],[11,281]),([],[],[]),([3,1031],[5153],[3,1031]),([],[],[]),([5,619],[19,293],[5,619]),([],[],[]),([19,163],[7,859],[19,163]),([],[],[]),([3,1033],[3,1721],[1033]),([],[],[]),([7,443],[11,523],[7,443]),([],[],[]),([29,107],[13,467],[29,107]),([],[],[]),([3,3,3,5,23],[3,3,521],[3,5,23]),([],[],[]),([13,239],[67,89],[13,239]),([],[],[]),([3109],[6217],[3109]),([],[],[]),([3,17,61],[3,3,13,43],[17,61]),([],[],[]),([11,283],[17,349],[11,283]),([],[],[]),([5,7,89],[5227],[5,7,89]),([],[],[]),([3,1039],[3,3,577],[1039]),([],[],[]),([3119],[3,3,3,3,7,11],[3119]),([],[],[]),([3121],[79,79],[3121]),([],[],[]),([3,3,347],[3,1733],[3,347]),([],[],[]),([5,5,5,5,5],[3,3,5,5,5,5],[5]),([],[],[]),([53,59],[6143],[53,59]),([],[],[]),([3,7,149],[3,3,5,109],[7,149]),([],[],[]),([31,101],[6131],[31,101]),([],[],[]),([13,241],[7,859],[13,241]),([],[],[]),([3,5,11,19],[3,5,5,61],[11,19])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range3136 (R D : ℕ) (lo : 3136 ≤ R) (hi : R < 3200) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 3136 64 R D [([],[],[]),([3137],[3,3,17,41],[3137]),([],[],[]),([43,73],[6163],[43,73]),([],[],[]),([3,3,349],[3,3,7,83],[349]),([],[],[]),([7,449],[7,7,7,17],[449]),([],[],[]),([5,17,37],[5449],[5,17,37]),([],[],[]),([3,1049],[7,7,107],[3,1049]),([],[],[]),([47,67],[5,1237],[47,67]),([],[],[]),([23,137],[6143],[23,137]),([],[],[]),([3,1051],[3,17,103],[1051]),([],[],[]),([5,631],[5,5,227],[631]),([],[],[]),([7,11,41],[5557],[7,11,41]),([],[],[]),([3,3,3,3,3,13],[3,3,3,3,3,3,7],[13]),([],[],[]),([29,109],[5,1237],[29,109]),([],[],[]),([3163],[5,5,11,23],[3163]),([],[],[]),([3,5,211],[3,5,17,19],[211]),([],[],[]),([3167],[3,2111],[3167]),([],[],[]),([3169],[6337],[3169]),([],[],[]),([3,7,151],[3,1657],[7,151]),([],[],[]),([19,167],[61,101],[19,167]),([],[],[]),([5,5,127],[5,17,67],[5,127]),([],[],[]),([3,3,353],[3,41,43],[3,353]),([],[],[]),([11,17,17],[17,347],[11,17]),([],[],[]),([3181],[6361],[3181]),([],[],[]),([3,1061],[5303],[3,1061]),([],[],[]),([5,7,7,13],[7,743],[5,7,13]),([],[],[]),([3187],[6373],[3187]),([],[],[]),([3,1063],[3,7,11,23],[1063]),([],[],[]),([3191],[3,3,709],[3191]),([],[],[]),([31,103],[13,13,37],[31,103]),([],[],[]),([3,3,5,71],[3,5,5,5,13],[3,71]),([],[],[]),([23,139],[23,271],[139]),([],[],[]),([7,457],[5,1187],[7,457])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range3200 (R D : ℕ) (lo : 3200 ≤ R) (hi : R < 3264) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 3200 64 R D [([],[],[]),([3,11,97],[3,3,569],[11,97]),([],[],[]),([3203],[3,5,7,61],[3203]),([],[],[]),([5,641],[5,1153],[641]),([],[],[]),([3,1069],[3,13,137],[1069]),([],[],[]),([3209],[3,3,23,31],[3209]),([],[],[]),([13,13,19],[13,463],[13,19]),([],[],[]),([3,3,3,7,17],[3,3,3,3,61],[7,17]),([],[],[]),([5,643],[5783],[5,643]),([],[],[]),([3217],[7,919],[3217]),([],[],[]),([3,29,37],[3,5,349],[29,37]),([],[],[]),([3221],[3,19,113],[3221]),([],[],[]),([11,293],[6143],[11,293]),([],[],[]),([3,5,5,43],[3,3,5,109],[5,43]),([],[],[]),([7,461],[5987],[7,461]),([],[],[]),([3229],[11,587],[3229]),([],[],[]),([3,3,359],[3,11,163],[3,359]),([],[],[]),([53,61],[6353],[53,61]),([],[],[]),([5,647],[11,23,23],[5,647]),([],[],[]),([3,13,83],[3,5,347],[13,83]),([],[],[]),([41,79],[6359],[41,79]),([],[],[]),([7,463],[7,859],[463]),([],[],[]),([3,23,47],[23,229],[3,47]),([],[],[]),([5,11,59],[3,5,7,53],[11,59]),([],[],[]),([17,191],[6287],[17,191]),([],[],[]),([3,3,19,19],[3,3,19,31],[19]),([],[],[]),([3251],[3,11,197],[3251]),([],[],[]),([3253],[5,1301],[3253]),([],[],[]),([3,5,7,31],[3,5,313],[7,31]),([],[],[]),([3257],[3,13,167],[3257]),([],[],[]),([3259],[7,7,7,19],[3259]),([],[],[]),([3,1087],[3,1811],[1087]),([],[],[]),([13,251],[6263],[13,251])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range3264 (R D : ℕ) (lo : 3264 ≤ R) (hi : R < 3328) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 3264 64 R D [([],[],[]),([5,653],[7,839],[5,653]),([],[],[]),([3,3,3,11,11],[3,3,11,53],[3,11]),([],[],[]),([7,467],[5,1213],[7,467]),([],[],[]),([3271],[31,211],[3271]),([],[],[]),([3,1091],[7,19,41],[3,1091]),([],[],[]),([5,5,131],[5,5,5,47],[131]),([],[],[]),([29,113],[11,11,53],[29,113]),([],[],[]),([3,1093],[3,3,607],[1093]),([],[],[]),([17,193],[6353],[17,193]),([],[],[]),([7,7,67],[5,7,173],[7,67]),([],[],[]),([3,3,5,73],[3,3,557],[5,73]),([],[],[]),([19,173],[13,491],[19,173]),([],[],[]),([11,13,23],[7,7,11,11],[13,23]),([],[],[]),([3,1097],[5483],[3,1097]),([],[],[]),([37,89],[7,13,71],[37,89]),([],[],[]),([5,659],[5927],[5,659]),([],[],[]),([3,7,157],[3,1723],[7,157]),([],[],[]),([3299],[3,3,733],[3299]),([],[],[]),([3301],[7,23,41],[3301]),([],[],[]),([3,3,367],[3,3,13,47],[367]),([],[],[]),([5,661],[5,29,41],[661]),([],[],[]),([3307],[17,389],[3307]),([],[],[]),([3,1103],[37,149],[3,1103]),([],[],[]),([7,11,43],[7,7,7,17],[11,43]),([],[],[]),([3313],[5,5,5,53],[3313]),([],[],[]),([3,5,13,17],[3,3,7,7,11],[5,13,17]),([],[],[]),([31,107],[73,89],[31,107]),([],[],[]),([3319],[6637],[3319]),([],[],[]),([3,3,3,3,41],[3,3,3,7,29],[3,41]),([],[],[]),([3323],[3,5,443],[3323]),([],[],[]),([5,5,7,19],[5,1097],[5,7,19]),([],[],[]),([3,1109],[23,241],[3,1109])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range3328 (R D : ℕ) (lo : 3328 ≤ R) (hi : R < 3392) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 3328 64 R D [([],[],[]),([3329],[3,7,317],[3329]),([],[],[]),([3331],[6661],[3331]),([],[],[]),([3,11,101],[5333],[3,11,101]),([],[],[]),([5,23,29],[3,1933],[5,23,29]),([],[],[]),([47,71],[79,83],[47,71]),([],[],[]),([3,3,7,53],[3,3,3,193],[7,53]),([],[],[]),([13,257],[11,11,53],[13,257]),([],[],[]),([3343],[5,7,191],[3343]),([],[],[]),([3,5,223],[3,3,569],[5,223]),([],[],[]),([3347],[3,23,97],[3347]),([],[],[]),([17,197],[5,1297],[17,197]),([],[],[]),([3,1117],[3,1861],[1117]),([],[],[]),([7,479],[6221],[7,479]),([],[],[]),([5,11,61],[5,1151],[11,61]),([],[],[]),([3,3,373],[3,3,3,3,3,23],[373]),([],[],[]),([3359],[3,2239],[3359]),([],[],[]),([3361],[11,13,47],[3361]),([],[],[]),([3,19,59],[3,23,79],[19,59]),([],[],[]),([5,673],[6053],[5,673]),([],[],[]),([7,13,37],[59,101],[7,13,37]),([],[],[]),([3,1123],[3,1871],[1123]),([],[],[]),([3371],[3,3,7,107],[3371]),([],[],[]),([3373],[5,19,71],[3373]),([],[],[]),([3,3,3,5,5,5],[3,3,5,5,23],[3,5]),([],[],[]),([11,307],[41,157],[11,307]),([],[],[]),([31,109],[6619],[31,109]),([],[],[]),([3,7,7,23],[3,3,7,83],[7,23]),([],[],[]),([17,199],[6551],[17,199]),([],[],[]),([5,677],[6089],[5,677]),([],[],[]),([3,1129],[3,3,3,11,19],[1129]),([],[],[]),([3389],[3,3,3,251],[3389]),([],[],[]),([3391],[6781],[3391])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range3392 (R D : ℕ) (lo : 3392 ≤ R) (hi : R < 3456) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 3392 64 R D [([],[],[]),([3,3,13,29],[3,3,601],[13,29]),([],[],[]),([5,7,97],[41,139],[5,7,97]),([],[],[]),([43,79],[6673],[43,79]),([],[],[]),([3,11,103],[3,7,7,37],[11,103]),([],[],[]),([19,179],[5,1321],[19,179]),([],[],[]),([41,83],[41,163],[83]),([],[],[]),([3,5,227],[13,401],[3,5,227]),([],[],[]),([3407],[3,3,757],[3407]),([],[],[]),([7,487],[5,5,11,23],[7,487]),([],[],[]),([3,3,379],[3,3,631],[379]),([],[],[]),([3413],[3,5,5,7,13],[3413]),([],[],[]),([5,683],[6143],[5,683]),([],[],[]),([3,17,67],[3,19,97],[17,67]),([],[],[]),([13,263],[6563],[13,263]),([],[],[]),([11,311],[6521],[11,311]),([],[],[]),([3,7,163],[3,1789],[7,163]),([],[],[]),([5,5,137],[5,1229],[5,137]),([],[],[]),([23,149],[41,163],[23,149]),([],[],[]),([3,3,3,127],[3,3,3,211],[127]),([],[],[]),([47,73],[11,613],[47,73]),([],[],[]),([3433],[5,1373],[3433]),([],[],[]),([3,5,229],[3,1753],[5,229]),([],[],[]),([7,491],[7,911],[491]),([],[],[]),([19,181],[6679],[19,181]),([],[],[]),([3,31,37],[3,1867],[31,37]),([],[],[]),([11,313],[6563],[11,313]),([],[],[]),([5,13,53],[13,457],[5,53]),([],[],[]),([3,3,383],[3,1913],[3,383]),([],[],[]),([3449],[3,11,11,19],[3449]),([],[],[]),([7,17,29],[7,877],[17,29]),([],[],[]),([3,1151],[11,523],[3,1151]),([],[],[]),([5,691],[5,11,113],[691])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range3456 (R D : ℕ) (lo : 3456 ≤ R) (hi : R < 3520) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 3456 64 R D [([],[],[]),([3457],[31,223],[3457]),([],[],[]),([3,1153],[3,17,113],[1153]),([],[],[]),([3461],[3,3,769],[3461]),([],[],[]),([3463],[5,5,277],[3463]),([],[],[]),([3,3,5,7,11],[3,3,5,109],[7,11]),([],[],[]),([3467],[3,2311],[3467]),([],[],[]),([3469],[7,991],[3469]),([],[],[]),([3,13,89],[3,1861],[13,89]),([],[],[]),([23,151],[13,521],[23,151]),([],[],[]),([5,5,139],[5,29,43],[5,139]),([],[],[]),([3,19,61],[3,1879],[19,61]),([],[],[]),([7,7,71],[7,7,131],[71]),([],[],[]),([59,59],[3,3,13,59],[59]),([],[],[]),([3,3,3,3,43],[3,3,3,3,71],[43]),([],[],[]),([5,17,41],[3,5,13,31],[17,41]),([],[],[]),([11,317],[17,17,23],[11,317]),([],[],[]),([3,1163],[5813],[3,1163]),([],[],[]),([3491],[3,13,179],[3491]),([],[],[]),([7,499],[6481],[7,499]),([],[],[]),([3,5,233],[5351],[3,5,233]),([],[],[]),([13,269],[7,7,137],[13,269]),([],[],[]),([3499],[6997],[3499]),([],[],[]),([3,3,389],[3,29,67],[3,389]),([],[],[]),([31,113],[6863],[31,113]),([],[],[]),([5,701],[5,13,97],[701]),([],[],[]),([3,7,167],[3,3,13,47],[7,167]),([],[],[]),([11,11,29],[11,599],[11,29]),([],[],[]),([3511],[7,17,59],[3511]),([],[],[]),([3,1171],[3,1951],[1171]),([],[],[]),([5,19,37],[31,197],[5,19,37]),([],[],[]),([3517],[13,541],[3517]),([],[],[]),([3,3,17,23],[3,1877],[3,17,23])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range3520 (R D : ℕ) (lo : 3520 ≤ R) (hi : R < 3584) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 3520 64 R D [([],[],[]),([7,503],[47,139],[7,503]),([],[],[]),([13,271],[6763],[13,271]),([],[],[]),([3,5,5,47],[5,29,37],[3,5,47]),([],[],[]),([3527],[3,2351],[3527]),([],[],[]),([3529],[7057],[3529]),([],[],[]),([3,11,107],[5651],[3,11,107]),([],[],[]),([3533],[3,3,5,157],[3533]),([],[],[]),([5,7,101],[5,1187],[7,101]),([],[],[]),([3,3,3,131],[3,3,653],[3,131]),([],[],[]),([3539],[3,7,337],[3539]),([],[],[]),([3541],[73,97],[3541]),([],[],[]),([3,1181],[5903],[3,1181]),([],[],[]),([5,709],[7,911],[5,709]),([],[],[]),([3547],[41,173],[3547]),([],[],[]),([3,7,13,13],[3,13,139],[7,13]),([],[],[]),([53,67],[6983],[53,67]),([],[],[]),([11,17,19],[7,919],[11,17,19]),([],[],[]),([3,3,5,79],[3,3,3,3,67],[5,79]),([],[],[]),([3557],[3,2371],[3557]),([],[],[]),([3559],[11,647],[3559]),([],[],[]),([3,1187],[17,349],[3,1187]),([],[],[]),([7,509],[11,601],[7,509]),([],[],[]),([5,23,31],[5,17,73],[23,31]),([],[],[]),([3,29,41],[5807],[3,29,41]),([],[],[]),([43,83],[7013],[43,83]),([],[],[]),([3571],[37,193],[3571]),([],[],[]),([3,3,397],[3,3,661],[397]),([],[],[]),([5,5,11,13],[5,5,239],[11,13]),([],[],[]),([7,7,73],[7,23,41],[7,73]),([],[],[]),([3,1193],[67,89],[3,1193]),([],[],[]),([3581],[3,7,11,31],[3581]),([],[],[]),([3583],[5,1433],[3583])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range3584 (R D : ℕ) (lo : 3584 ≤ R) (hi : R < 3648) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 3584 64 R D [([],[],[]),([3,5,239],[11,499],[3,5,239]),([],[],[]),([17,211],[6947],[17,211]),([],[],[]),([37,97],[5,1409],[37,97]),([],[],[]),([3,3,3,7,19],[3,3,3,5,41],[7,19]),([],[],[]),([3593],[3,5,479],[3593]),([],[],[]),([5,719],[29,223],[5,719]),([],[],[]),([3,11,109],[3,19,101],[11,109]),([],[],[]),([59,61],[7079],[59,61]),([],[],[]),([13,277],[31,223],[13,277]),([],[],[]),([3,1201],[3,3,23,29],[1201]),([],[],[]),([5,7,103],[6053],[5,7,103]),([],[],[]),([3607],[7213],[3607]),([],[],[]),([3,3,401],[3,2003],[3,401]),([],[],[]),([23,157],[7043],[23,157]),([],[],[]),([3613],[5,5,17,17],[3613]),([],[],[]),([3,5,241],[3,3,3,5,41],[241]),([],[],[]),([3617],[3,2411],[3617]),([],[],[]),([7,11,47],[6379],[7,11,47]),([],[],[]),([3,17,71],[5861],[3,17,71]),([],[],[]),([3623],[3,3,5,7,23],[3623]),([],[],[]),([5,5,5,29],[5,5,257],[5,29]),([],[],[]),([3,3,13,31],[3,3,643],[13,31]),([],[],[]),([19,191],[7,19,53],[191]),([],[],[]),([3631],[53,137],[3631]),([],[],[]),([3,7,173],[3,3,3,211],[7,173]),([],[],[]),([5,727],[13,503],[5,727]),([],[],[]),([3637],[7,1039],[3637]),([],[],[]),([3,1213],[3,43,47],[1213]),([],[],[]),([11,331],[11,631],[331]),([],[],[]),([3643],[5,31,47],[3643]),([],[],[]),([3,3,3,3,3,3,5],[3,3,3,3,3,23],[3,5]),([],[],[]),([7,521],[67,101],[7,521])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range3648 (R D : ℕ) (lo : 3648 ≤ R) (hi : R < 3712) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 3648 64 R D [([],[],[]),([41,89],[67,107],[41,89]),([],[],[]),([3,1217],[7,11,79],[3,1217]),([],[],[]),([13,281],[7013],[13,281]),([],[],[]),([5,17,43],[6343],[5,17,43]),([],[],[]),([3,23,53],[5,29,41],[3,23,53]),([],[],[]),([3659],[3,3,3,271],[3659]),([],[],[]),([7,523],[6793],[7,523]),([],[],[]),([3,3,11,37],[3,3,647],[11,37]),([],[],[]),([5,733],[19,347],[5,733]),([],[],[]),([19,193],[17,419],[19,193]),([],[],[]),([3,1223],[6113],[3,1223]),([],[],[]),([3671],[3,2447],[3671]),([],[],[]),([3673],[5,13,113],[3673]),([],[],[]),([3,5,5,7,7],[3,3,5,7,17],[5,7]),([],[],[]),([3677],[3,3,19,43],[3677]),([],[],[]),([13,283],[7,1009],[13,283]),([],[],[]),([3,3,409],[3,3,3,227],[409]),([],[],[]),([29,127],[7211],[29,127]),([],[],[]),([5,11,67],[5,5,11,23],[67]),([],[],[]),([3,1229],[6143],[3,1229]),([],[],[]),([7,17,31],[6569],[7,17,31]),([],[],[]),([3691],[11,11,61],[3691]),([],[],[]),([3,1231],[3,7,293],[1231]),([],[],[]),([5,739],[17,17,23],[5,739]),([],[],[]),([3697],[7393],[3697]),([],[],[]),([3,3,3,137],[3,3,683],[3,137]),([],[],[]),([3701],[3,2467],[3701]),([],[],[]),([7,23,23],[23,293],[7,23]),([],[],[]),([3,5,13,19],[3,1811],[5,13,19]),([],[],[]),([11,337],[37,191],[11,337]),([],[],[]),([3709],[7417],[3709]),([],[],[]),([3,1237],[3,3,3,229],[1237])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range3712 (R D : ℕ) (lo : 3712 ≤ R) (hi : R < 3776) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 3712 64 R D [([],[],[]),([47,79],[7,7,149],[47,79]),([],[],[]),([5,743],[41,163],[5,743]),([],[],[]),([3,3,7,59],[3,3,3,5,43],[7,59]),([],[],[]),([3719],[3,37,67],[3719]),([],[],[]),([61,61],[11,11,61],[61]),([],[],[]),([3,17,73],[3,7,7,41],[17,73]),([],[],[]),([5,5,149],[5,7,191],[5,149]),([],[],[]),([3727],[29,257],[3727]),([],[],[]),([3,11,113],[47,127],[3,11,113]),([],[],[]),([7,13,41],[11,601],[7,13,41]),([],[],[]),([3733],[5,1493],[3733]),([],[],[]),([3,3,5,83],[3,1901],[3,5,83]),([],[],[]),([37,101],[11,23,29],[37,101]),([],[],[]),([3739],[7477],[3739]),([],[],[]),([3,29,43],[3,3,677],[29,43]),([],[],[]),([19,197],[11,661],[19,197]),([],[],[]),([5,7,107],[19,331],[5,7,107]),([],[],[]),([3,1249],[3,2081],[1249]),([],[],[]),([23,163],[71,103],[23,163]),([],[],[]),([11,11,31],[11,641],[11,31]),([],[],[]),([3,3,3,139],[3,3,3,3,7,11],[139]),([],[],[]),([5,751],[5,7,193],[751]),([],[],[]),([13,17,17],[7,17,59],[13,17]),([],[],[]),([3,7,179],[3,3,5,131],[7,179]),([],[],[]),([3761],[3,23,109],[3761]),([],[],[]),([53,71],[11,673],[53,71]),([],[],[]),([3,5,251],[5,1153],[3,251]),([],[],[]),([3767],[3,3,3,3,3,31],[3767]),([],[],[]),([3769],[7537],[3769]),([],[],[]),([3,3,419],[3,7,13,23],[3,419]),([],[],[]),([7,7,7,11],[7,7,137],[7,11]),([],[],[]),([5,5,151],[5,5,271],[151])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range3776 (R D : ℕ) (lo : 3776 ≤ R) (hi : R < 3840) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 3776 64 R D [([],[],[]),([3,1259],[7,29,31],[3,1259]),([],[],[]),([3779],[3,11,229],[3779]),([],[],[]),([19,199],[5,13,113],[19,199]),([],[],[]),([3,13,97],[3,2029],[13,97]),([],[],[]),([5,757],[11,619],[5,757]),([],[],[]),([7,541],[7027],[7,541]),([],[],[]),([3,3,421],[3,3,701],[421]),([],[],[]),([17,223],[7,1049],[17,223]),([],[],[]),([3793],[5,37,41],[3793]),([],[],[]),([3,5,11,23],[5,11,101],[3,23]),([],[],[]),([3797],[3,2531],[3797]),([],[],[]),([29,131],[43,173],[29,131]),([],[],[]),([3,7,181],[3,1987],[7,181]),([],[],[]),([3803],[3,3,5,13,13],[3803]),([],[],[]),([5,761],[5,37,37],[761]),([],[],[]),([3,3,3,3,47],[3,3,3,233],[3,47]),([],[],[]),([13,293],[71,103],[13,293]),([],[],[]),([37,103],[7,1069],[37,103]),([],[],[]),([3,31,41],[3,19,109],[31,41]),([],[],[]),([5,7,109],[43,149],[5,7,109]),([],[],[]),([11,347],[19,383],[11,347]),([],[],[]),([3,19,67],[3,5,7,59],[19,67]),([],[],[]),([3821],[3,3,3,283],[3821]),([],[],[]),([3823],[5,11,139],[3823]),([],[],[]),([3,3,5,5,17],[3,5,383],[3,5,17]),([],[],[]),([43,89],[7523],[43,89]),([],[],[]),([7,547],[5,7,7,29],[547]),([],[],[]),([3,1277],[13,491],[3,1277]),([],[],[]),([3833],[3,5,7,73],[3833]),([],[],[]),([5,13,59],[6619],[5,13,59]),([],[],[]),([3,1279],[3,2131],[1279]),([],[],[]),([11,349],[13,563],[11,349])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range3840 (R D : ℕ) (lo : 3840 ≤ R) (hi : R < 3904) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 3840 64 R D [([],[],[]),([23,167],[59,127],[23,167]),([],[],[]),([3,3,7,61],[3,3,23,29],[7,61]),([],[],[]),([5,769],[6917],[5,769]),([],[],[]),([3847],[7,7,157],[3847]),([],[],[]),([3,1283],[11,11,53],[3,1283]),([],[],[]),([3851],[3,17,151],[3851]),([],[],[]),([3853],[5,23,67],[3853]),([],[],[]),([3,5,257],[5903],[3,5,257]),([],[],[]),([7,19,29],[7,983],[19,29]),([],[],[]),([17,227],[5,5,13,23],[17,227]),([],[],[]),([3,3,3,11,13],[3,3,3,223],[11,13]),([],[],[]),([3863],[3,5,5,103],[3863]),([],[],[]),([5,773],[17,409],[5,773]),([],[],[]),([3,1289],[17,379],[3,1289]),([],[],[]),([53,73],[23,331],[53,73]),([],[],[]),([7,7,79],[7,1021],[7,79]),([],[],[]),([3,1291],[3,3,3,239],[1291]),([],[],[]),([5,5,5,31],[5,5,5,5,11],[31]),([],[],[]),([3877],[7753],[3877]),([],[],[]),([3,3,431],[3,2153],[3,431]),([],[],[]),([3881],[3,13,199],[3881]),([],[],[]),([11,353],[11,673],[353]),([],[],[]),([3,5,7,37],[3,1871],[5,7,37]),([],[],[]),([13,13,23],[13,563],[13,23]),([],[],[]),([3889],[7,11,101],[3889]),([],[],[]),([3,1297],[3,2161],[1297]),([],[],[]),([17,229],[7541],[17,229]),([],[],[]),([5,19,41],[5,5,271],[19,41]),([],[],[]),([3,3,433],[3,3,7,103],[433]),([],[],[]),([7,557],[5,1447],[7,557]),([],[],[]),([47,83],[7673],[47,83]),([],[],[]),([3,1301],[7,929],[3,1301])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range3904 (R D : ℕ) (lo : 3904 ≤ R) (hi : R < 3968) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 3904 64 R D [([],[],[]),([5,11,71],[3,3,5,149],[11,71]),([],[],[]),([3907],[13,601],[3907]),([],[],[]),([3,1303],[3,13,167],[1303]),([],[],[]),([3911],[3,3,11,79],[3911]),([],[],[]),([7,13,43],[7,991],[13,43]),([],[],[]),([3,3,3,5,29],[3,3,659],[3,5,29]),([],[],[]),([3917],[3,7,373],[3917]),([],[],[]),([3919],[17,461],[3919]),([],[],[]),([3,1307],[47,139],[3,1307]),([],[],[]),([3923],[3,5,523],[3923]),([],[],[]),([5,5,157],[5,1409],[5,157]),([],[],[]),([3,7,11,17],[3,1949],[7,11,17]),([],[],[]),([3929],[3,3,3,3,97],[3929]),([],[],[]),([3931],[7,1123],[3931]),([],[],[]),([3,3,19,23],[3,3,701],[19,23]),([],[],[]),([5,787],[7079],[5,787]),([],[],[]),([31,127],[7717],[31,127]),([],[],[]),([3,13,101],[3,2113],[13,101]),([],[],[]),([7,563],[71,103],[7,563]),([],[],[]),([3943],[5,19,83],[3943]),([],[],[]),([3,5,263],[7,863],[3,5,263]),([],[],[]),([3947],[3,3,877],[3947]),([],[],[]),([11,359],[7529],[11,359]),([],[],[]),([3,3,439],[3,3,17,43],[439]),([],[],[]),([59,67],[31,251],[59,67]),([],[],[]),([5,7,113],[7,13,73],[5,113]),([],[],[]),([3,1319],[19,347],[3,1319]),([],[],[]),([37,107],[5,5,311],[37,107]),([],[],[]),([17,233],[7673],[17,233]),([],[],[]),([3,1321],[3,31,71],[1321]),([],[],[]),([5,13,61],[5,37,37],[13,61]),([],[],[]),([3967],[7933],[3967])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range3968 (R D : ℕ) (lo : 3968 ≤ R) (hi : R < 4032) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 3968 64 R D [([],[],[]),([3,3,3,3,7,7],[3,3,3,3,7,11],[7]),([],[],[]),([11,19,19],[19,389],[11,19]),([],[],[]),([29,137],[31,251],[29,137]),([],[],[]),([3,5,5,53],[5,7,173],[3,5,53]),([],[],[]),([41,97],[7817],[41,97]),([],[],[]),([23,173],[7,1109],[23,173]),([],[],[]),([3,1327],[3,3,11,67],[1327]),([],[],[]),([7,569],[19,389],[7,569]),([],[],[]),([5,797],[67,107],[5,797]),([],[],[]),([3,3,443],[3,2213],[3,443]),([],[],[]),([3989],[3,2659],[3989]),([],[],[]),([13,307],[79,97],[13,307]),([],[],[]),([3,11,11,11],[11,11,53],[3,11]),([],[],[]),([5,17,47],[3,3,3,257],[5,17,47]),([],[],[]),([7,571],[7417],[7,571]),([],[],[]),([3,31,43],[3,41,53],[31,43]),([],[],[]),([4001],[3,3,7,127],[4001]),([],[],[]),([4003],[5,1601],[4003]),([],[],[]),([3,3,5,89],[3,2039],[3,5,89]),([],[],[]),([4007],[3,2671],[4007]),([],[],[]),([19,211],[7789],[19,211]),([],[],[]),([3,7,191],[3,3,3,233],[7,191]),([],[],[]),([4013],[3,5,5,107],[4013]),([],[],[]),([5,11,73],[5,7,197],[11,73]),([],[],[]),([3,13,103],[3,5,431],[13,103]),([],[],[]),([4019],[3,3,19,47],[4019]),([],[],[]),([4021],[11,17,43],[4021]),([],[],[]),([3,3,3,149],[3,3,743],[3,149]),([],[],[]),([5,5,7,23],[5,31,43],[5,7,23]),([],[],[]),([4027],[8053],[4027]),([],[],[]),([3,17,79],[3,3,5,5,29],[17,79]),([],[],[]),([29,139],[5,1579],[29,139])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range4032 (R D : ℕ) (lo : 4032 ≤ R) (hi : R < 4096) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 4032 64 R D [([],[],[]),([37,109],[89,89],[37,109]),([],[],[]),([3,5,269],[37,167],[3,5,269]),([],[],[]),([11,367],[43,179],[11,367]),([],[],[]),([7,577],[5,1499],[7,577]),([],[],[]),([3,3,449],[3,2243],[3,449]),([],[],[]),([13,311],[7,1109],[13,311]),([],[],[]),([5,809],[19,383],[5,809]),([],[],[]),([3,19,71],[3,11,199],[19,71]),([],[],[]),([4049],[3,2699],[4049]),([],[],[]),([4051],[8101],[4051]),([],[],[]),([3,7,193],[3,13,163],[7,193]),([],[],[]),([5,811],[5,1459],[811]),([],[],[]),([4057],[7,19,61],[4057]),([],[],[]),([3,3,11,41],[3,2153],[3,11,41]),([],[],[]),([31,131],[19,419],[31,131]),([],[],[]),([17,239],[17,463],[239]),([],[],[]),([3,5,271],[3,5,5,83],[271]),([],[],[]),([7,7,83],[7,29,37],[7,83]),([],[],[]),([13,313],[13,601],[313]),([],[],[]),([3,23,59],[37,179],[3,23,59]),([],[],[]),([4073],[3,3,5,181],[4073]),([],[],[]),([5,5,163],[5,7,11,19],[5,163]),([],[],[]),([3,3,3,151],[3,3,3,251],[151]),([],[],[]),([4079],[3,2719],[4079]),([],[],[]),([7,11,53],[19,379],[7,11,53]),([],[],[]),([3,1361],[6803],[3,1361]),([],[],[]),([5,19,43],[7109],[5,19,43]),([],[],[]),([61,67],[13,619],[61,67]),([],[],[]),([3,29,47],[5,31,43],[3,29,47]),([],[],[]),([4091],[3,3,3,3,101],[4091]),([],[],[]),([4093],[5,1637],[4093]),([],[],[]),([3,3,5,7,13],[3,3,647],[5,7,13])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range4096 (R D : ℕ) (lo : 4096 ≤ R) (hi : R < 4160) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 4096 64 R D [([],[],[]),([17,241],[7937],[17,241]),([],[],[]),([4099],[7,1171],[4099]),([],[],[]),([3,1367],[6833],[3,1367]),([],[],[]),([11,373],[7823],[11,373]),([],[],[]),([5,821],[5,7,211],[821]),([],[],[]),([3,37,37],[3,37,61],[37]),([],[],[]),([7,587],[5,5,5,61],[7,587]),([],[],[]),([4111],[8221],[4111]),([],[],[]),([3,3,457],[3,3,761],[457]),([],[],[]),([5,823],[11,673],[5,823]),([],[],[]),([23,179],[29,277],[23,179]),([],[],[]),([3,1373],[6863],[3,1373]),([],[],[]),([13,317],[41,193],[13,317]),([],[],[]),([7,19,31],[37,199],[7,19,31]),([],[],[]),([3,5,5,5,11],[5,5,5,7,7],[3,11]),([],[],[]),([4127],[3,3,7,131],[4127]),([],[],[]),([4129],[23,359],[4129]),([],[],[]),([3,3,3,3,3,17],[3,3,3,3,83],[3,17]),([],[],[]),([4133],[3,5,19,29],[4133]),([],[],[]),([5,827],[43,173],[5,827]),([],[],[]),([3,7,197],[3,3,7,103],[197]),([],[],[]),([4139],[3,31,89],[4139]),([],[],[]),([41,101],[7,1163],[41,101]),([],[],[]),([3,1381],[3,3,13,59],[1381]),([],[],[]),([5,829],[7457],[5,829]),([],[],[]),([11,13,29],[7507],[11,13,29]),([],[],[]),([3,3,461],[3,7,7,47],[3,461]),([],[],[]),([7,593],[7703],[7,593]),([],[],[]),([4153],[5,11,151],[4153]),([],[],[]),([3,5,277],[3,3,7,101],[5,277]),([],[],[]),([4157],[3,17,163],[4157]),([],[],[]),([4159],[8317],[4159])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range4160 (R D : ℕ) (lo : 4160 ≤ R) (hi : R < 4224) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 4160 64 R D [([],[],[]),([3,19,73],[3,2251],[19,73]),([],[],[]),([23,181],[8123],[23,181]),([],[],[]),([5,7,7,17],[7,11,89],[5,7,17]),([],[],[]),([3,3,463],[3,3,3,257],[463]),([],[],[]),([11,379],[7949],[11,379]),([],[],[]),([43,97],[13,631],[43,97]),([],[],[]),([3,13,107],[3,2239],[13,107]),([],[],[]),([5,5,167],[5,1499],[5,167]),([],[],[]),([4177],[8353],[4177]),([],[],[]),([3,7,199],[3,5,19,23],[7,199]),([],[],[]),([37,113],[43,191],[37,113]),([],[],[]),([47,89],[8231],[47,89]),([],[],[]),([3,3,3,5,31],[3,3,3,5,47],[31]),([],[],[]),([53,79],[8243],[53,79]),([],[],[]),([59,71],[73,113],[59,71]),([],[],[]),([3,11,127],[3,2237],[11,127]),([],[],[]),([7,599],[31,251],[7,599]),([],[],[]),([5,839],[7547],[5,839]),([],[],[]),([3,1399],[3,3,3,7,37],[1399]),([],[],[]),([13,17,19],[5,1531],[13,17,19]),([],[],[]),([4201],[31,271],[4201]),([],[],[]),([3,3,467],[3,2333],[3,467]),([],[],[]),([5,29,29],[29,257],[5,29]),([],[],[]),([7,601],[37,211],[7,601]),([],[],[]),([3,23,61],[3,3,761],[23,61]),([],[],[]),([4211],[3,7,401],[4211]),([],[],[]),([11,383],[29,277],[11,383]),([],[],[]),([3,5,281],[5,1291],[3,281]),([],[],[]),([4217],[3,3,937],[4217]),([],[],[]),([4219],[11,13,59],[4219]),([],[],[]),([3,3,7,67],[3,3,733],[7,67]),([],[],[]),([41,103],[19,19,23],[41,103])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range4224 (R D : ℕ) (lo : 4224 ≤ R) (hi : R < 4288) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 4224 64 R D [([],[],[]),([5,5,13,13],[5,13,113],[5,13]),([],[],[]),([3,1409],[7043],[3,1409]),([],[],[]),([4229],[3,2819],[4229]),([],[],[]),([4231],[8461],[4231]),([],[],[]),([3,17,83],[6857],[3,17,83]),([],[],[]),([5,7,11,11],[5,5,5,5,11],[7,11]),([],[],[]),([19,223],[8233],[19,223]),([],[],[]),([3,3,3,157],[3,3,3,3,3,29],[157]),([],[],[]),([4241],[3,11,257],[4241]),([],[],[]),([4243],[5,1697],[4243]),([],[],[]),([3,5,283],[3,11,197],[5,283]),([],[],[]),([31,137],[11,757],[31,137]),([],[],[]),([7,607],[5,19,83],[7,607]),([],[],[]),([3,13,109],[3,2281],[13,109]),([],[],[]),([4253],[3,3,3,3,3,5,7],[4253]),([],[],[]),([5,23,37],[13,571],[5,23,37]),([],[],[]),([3,3,11,43],[3,3,3,251],[11,43]),([],[],[]),([4259],[3,17,167],[4259]),([],[],[]),([4261],[8521],[4261]),([],[],[]),([3,7,7,29],[3,3,3,5,7,7],[29]),([],[],[]),([5,853],[7673],[5,853]),([],[],[]),([17,251],[7,1181],[17,251]),([],[],[]),([3,1423],[3,2371],[1423]),([],[],[]),([4271],[3,3,13,73],[4271]),([],[],[]),([4273],[5,1709],[4273]),([],[],[]),([3,3,5,5,19],[3,3,5,11,13],[5,19]),([],[],[]),([7,13,47],[7589],[7,13,47]),([],[],[]),([11,389],[41,199],[11,389]),([],[],[]),([3,1427],[7,1019],[3,1427]),([],[],[]),([4283],[3,5,571],[4283]),([],[],[]),([5,857],[13,593],[5,857]),([],[],[]),([3,1429],[3,2381],[1429])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range4288 (R D : ℕ) (lo : 4288 ≤ R) (hi : R < 4352) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 4288 64 R D [([],[],[]),([4289],[3,3,953],[4289]),([],[],[]),([7,613],[7963],[7,613]),([],[],[]),([3,3,3,3,53],[3,3,3,263],[3,53]),([],[],[]),([5,859],[7727],[5,859]),([],[],[]),([4297],[13,661],[4297]),([],[],[]),([3,1433],[13,19,29],[3,1433]),([],[],[]),([11,17,23],[3,3,11,79],[17,23]),([],[],[]),([13,331],[8263],[13,331]),([],[],[]),([3,5,7,41],[3,5,5,83],[7,41]),([],[],[]),([59,73],[17,499],[59,73]),([],[],[]),([31,139],[7,17,71],[31,139]),([],[],[]),([3,3,479],[3,2393],[3,479]),([],[],[]),([19,227],[17,17,29],[19,227]),([],[],[]),([5,863],[7,1109],[5,863]),([],[],[]),([3,1439],[7193],[3,1439]),([],[],[]),([7,617],[5,7,229],[617]),([],[],[]),([29,149],[5,1693],[29,149]),([],[],[]),([3,11,131],[7,23,43],[3,11,131]),([],[],[]),([5,5,173],[5,1553],[5,173]),([],[],[]),([4327],[17,509],[4327]),([],[],[]),([3,3,13,37],[3,3,769],[13,37]),([],[],[]),([61,71],[19,449],[61,71]),([],[],[]),([7,619],[11,17,43],[7,619]),([],[],[]),([3,5,17,17],[17,383],[3,5,17]),([],[],[]),([4337],[3,7,7,59],[4337]),([],[],[]),([4339],[8677],[4339]),([],[],[]),([3,1447],[3,2411],[1447]),([],[],[]),([43,101],[8543],[43,101]),([],[],[]),([5,11,79],[5,1493],[11,79]),([],[],[]),([3,3,3,7,23],[3,3,3,3,83],[7,23]),([],[],[]),([4349],[3,13,223],[4349]),([],[],[]),([19,229],[5,19,89],[229])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range4352 (R D : ℕ) (lo : 4352 ≤ R) (hi : R < 4416) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 4352 64 R D [([],[],[]),([3,1451],[7253],[3,1451]),([],[],[]),([5,13,67],[7523],[5,13,67]),([],[],[]),([4357],[8713],[4357]),([],[],[]),([3,1453],[3,3,3,269],[1453]),([],[],[]),([7,7,89],[7,1151],[7,89]),([],[],[]),([4363],[5,5,349],[4363]),([],[],[]),([3,3,5,97],[3,3,3,13,19],[5,97]),([],[],[]),([11,397],[11,757],[397]),([],[],[]),([17,257],[5,1693],[17,257]),([],[],[]),([3,31,47],[3,2377],[31,47]),([],[],[]),([4373],[3,5,11,53],[4373]),([],[],[]),([5,5,5,5,7],[5,5,5,59],[5,7]),([],[],[]),([3,1459],[3,11,13,17],[1459]),([],[],[]),([29,151],[23,373],[29,151]),([],[],[]),([13,337],[47,179],[13,337]),([],[],[]),([3,3,487],[3,3,811],[487]),([],[],[]),([5,877],[7,7,7,23],[5,877]),([],[],[]),([41,107],[8627],[41,107]),([],[],[]),([3,7,11,19],[3,37,59],[7,11,19]),([],[],[]),([4391],[3,2927],[4391]),([],[],[]),([23,191],[8573],[23,191]),([],[],[]),([3,5,293],[53,127],[3,5,293]),([],[],[]),([4397],[3,3,977],[4397]),([],[],[]),([53,83],[8663],[53,83]),([],[],[]),([3,3,3,163],[3,3,3,271],[163]),([],[],[]),([7,17,37],[29,271],[7,17,37]),([],[],[]),([5,881],[5,5,317],[881]),([],[],[]),([3,13,113],[3,5,11,43],[13,113]),([],[],[]),([4409],[3,2939],[4409]),([],[],[]),([11,401],[13,647],[11,401]),([],[],[]),([3,1471],[3,3,19,43],[1471]),([],[],[]),([5,883],[13,13,47],[5,883])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range4416 (R D : ℕ) (lo : 4416 ≤ R) (hi : R < 4480) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 4416 64 R D [([],[],[]),([7,631],[7,1171],[631]),([],[],[]),([3,3,491],[3,11,223],[3,491]),([],[],[]),([4421],[3,7,421],[4421]),([],[],[]),([4423],[5,29,61],[4423]),([],[],[]),([3,5,5,59],[5,19,71],[3,5,59]),([],[],[]),([19,233],[7,1229],[19,233]),([],[],[]),([43,103],[8713],[43,103]),([],[],[]),([3,7,211],[3,7,331],[211]),([],[],[]),([11,13,31],[29,277],[11,13,31]),([],[],[]),([5,887],[79,101],[5,887]),([],[],[]),([3,3,17,29],[3,5,5,5,19],[3,17,29]),([],[],[]),([23,193],[8663],[23,193]),([],[],[]),([4441],[83,107],[4441]),([],[],[]),([3,1481],[11,673],[3,1481]),([],[],[]),([5,7,127],[7,11,97],[5,127]),([],[],[]),([4447],[8893],[4447]),([],[],[]),([3,1483],[3,7,353],[1483]),([],[],[]),([4451],[3,3,23,43],[4451]),([],[],[]),([61,73],[31,283],[61,73]),([],[],[]),([3,3,3,3,5,11],[3,3,3,5,7,7],[3,11]),([],[],[]),([4457],[3,2971],[4457]),([],[],[]),([7,7,7,13],[7,7,163],[7,13]),([],[],[]),([3,1487],[7433],[3,1487]),([],[],[]),([4463],[3,5,5,7,17],[4463]),([],[],[]),([5,19,47],[7,11,101],[5,19,47]),([],[],[]),([3,1489],[3,3,827],[1489]),([],[],[]),([41,109],[11,17,47],[41,109]),([],[],[]),([17,263],[8663],[17,263]),([],[],[]),([3,3,7,71],[3,3,3,7,37],[71]),([],[],[]),([5,5,179],[5,1607],[5,179]),([],[],[]),([11,11,37],[11,13,59],[11,37]),([],[],[]),([3,1493],[17,439],[3,1493])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range4480 (R D : ℕ) (lo : 4480 ≤ R) (hi : R < 4544) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 4480 64 R D [([],[],[]),([4481],[3,29,103],[4481]),([],[],[]),([4483],[5,11,163],[4483]),([],[],[]),([3,5,13,23],[3,3,733],[5,13,23]),([],[],[]),([7,641],[11,757],[7,641]),([],[],[]),([67,67],[7,19,67],[67]),([],[],[]),([3,3,499],[3,3,3,277],[499]),([],[],[]),([4493],[3,5,599],[4493]),([],[],[]),([5,29,31],[5,1571],[29,31]),([],[],[]),([3,1499],[59,127],[3,1499]),([],[],[]),([11,409],[23,373],[11,409]),([],[],[]),([7,643],[8353],[7,643]),([],[],[]),([3,19,79],[3,2437],[19,79]),([],[],[]),([5,17,53],[3,7,373],[5,17,53]),([],[],[]),([4507],[9013],[4507]),([],[],[]),([3,3,3,167],[3,3,7,7,17],[3,167]),([],[],[]),([13,347],[8663],[13,347]),([],[],[]),([4513],[5,5,19,19],[4513]),([],[],[]),([3,5,7,43],[3,7,311],[5,43]),([],[],[]),([4517],[3,3011],[4517]),([],[],[]),([4519],[7,1291],[4519]),([],[],[]),([3,11,137],[13,557],[3,11,137]),([],[],[]),([4523],[3,3,3,5,67],[4523]),([],[],[]),([5,5,181],[5,5,5,5,13],[181]),([],[],[]),([3,3,503],[3,7,359],[3,503]),([],[],[]),([7,647],[5,41,41],[7,647]),([],[],[]),([23,197],[37,239],[23,197]),([],[],[]),([3,1511],[7,13,83],[3,1511]),([],[],[]),([5,907],[41,199],[5,907]),([],[],[]),([13,349],[8713],[13,349]),([],[],[]),([3,17,89],[5,1471],[3,17,89]),([],[],[]),([19,239],[5,5,353],[19,239]),([],[],[]),([7,11,59],[71,113],[7,11,59])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range4544 (R D : ℕ) (lo : 4544 ≤ R) (hi : R < 4608) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 4544 64 R D [([],[],[]),([3,3,5,101],[3,5,463],[3,101]),([],[],[]),([4547],[3,7,433],[4547]),([],[],[]),([4549],[11,827],[4549]),([],[],[]),([3,37,41],[3,2477],[37,41]),([],[],[]),([29,157],[11,811],[29,157]),([],[],[]),([5,911],[5,11,149],[911]),([],[],[]),([3,7,7,31],[3,7,337],[7,31]),([],[],[]),([47,97],[5,5,359],[47,97]),([],[],[]),([4561],[7,1303],[4561]),([],[],[]),([3,3,3,13,13],[3,3,3,3,7,13],[13]),([],[],[]),([5,11,83],[3,5,523],[11,83]),([],[],[]),([4567],[9133],[4567]),([],[],[]),([3,1523],[23,331],[3,1523]),([],[],[]),([7,653],[17,499],[7,653]),([],[],[]),([17,269],[8861],[17,269]),([],[],[]),([3,5,5,61],[3,3,5,5,31],[61]),([],[],[]),([23,199],[8933],[23,199]),([],[],[]),([19,241],[11,809],[19,241]),([],[],[]),([3,3,509],[3,2543],[3,509]),([],[],[]),([4583],[3,5,13,47],[4583]),([],[],[]),([5,7,131],[5,23,67],[7,131]),([],[],[]),([3,11,139],[3,31,79],[11,139]),([],[],[]),([13,353],[7,1259],[13,353]),([],[],[]),([4591],[9181],[4591]),([],[],[]),([3,1531],[3,2551],[1531]),([],[],[]),([5,919],[7,1181],[5,919]),([],[],[]),([4597],[29,317],[4597]),([],[],[]),([3,3,7,73],[3,3,17,47],[7,73]),([],[],[]),([43,107],[11,823],[43,107]),([],[],[]),([4603],[5,7,263],[4603]),([],[],[]),([3,5,307],[3,2351],[5,307]),([],[],[]),([17,271],[79,113],[17,271])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range4608 (R D : ℕ) (lo : 4608 ≤ R) (hi : R < 4672) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 4608 64 R D [([],[],[]),([11,419],[11,17,47],[419]),([],[],[]),([3,29,53],[7523],[3,29,53]),([],[],[]),([7,659],[7,1223],[659]),([],[],[]),([5,13,71],[5,5,11,29],[13,71]),([],[],[]),([3,3,3,3,3,19],[3,3,3,3,3,31],[19]),([],[],[]),([31,149],[9059],[31,149]),([],[],[]),([4621],[9241],[4621]),([],[],[]),([3,23,67],[3,13,193],[23,67]),([],[],[]),([5,5,5,37],[5,5,7,47],[5,37]),([],[],[]),([7,661],[31,277],[7,661]),([],[],[]),([3,1543],[3,3,857],[1543]),([],[],[]),([11,421],[8831],[11,421]),([],[],[]),([41,113],[13,701],[41,113]),([],[],[]),([3,3,5,103],[3,3,787],[5,103]),([],[],[]),([4637],[3,11,281],[4637]),([],[],[]),([4639],[9277],[4639]),([],[],[]),([3,7,13,17],[3,5,463],[7,13,17]),([],[],[]),([4643],[3,5,619],[4643]),([],[],[]),([5,929],[61,137],[5,929]),([],[],[]),([3,1549],[3,29,89],[1549]),([],[],[]),([4649],[3,3,1033],[4649]),([],[],[]),([4651],[71,131],[4651]),([],[],[]),([3,3,11,47],[3,7,353],[3,11,47]),([],[],[]),([5,7,7,19],[7,1097],[5,7,19]),([],[],[]),([4657],[67,139],[4657]),([],[],[]),([3,1553],[7,1109],[3,1553]),([],[],[]),([59,79],[5,11,167],[59,79]),([],[],[]),([4663],[5,5,373],[4663]),([],[],[]),([3,5,311],[5,1429],[3,311]),([],[],[]),([13,359],[8963],[13,359]),([],[],[]),([7,23,29],[5,7,239],[23,29]),([],[],[]),([3,3,3,173],[3,3,863],[3,173])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range4672 (R D : ℕ) (lo : 4672 ≤ R) (hi : R < 4736) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 4672 64 R D [([],[],[]),([4673],[3,5,7,89],[4673]),([],[],[]),([5,5,11,17],[3,3,5,5,5,7],[11,17]),([],[],[]),([3,1559],[7793],[3,1559]),([],[],[]),([4679],[3,3119],[4679]),([],[],[]),([31,151],[9181],[31,151]),([],[],[]),([3,7,223],[3,31,79],[7,223]),([],[],[]),([5,937],[8429],[5,937]),([],[],[]),([43,109],[23,401],[43,109]),([],[],[]),([3,3,521],[3,19,137],[3,521]),([],[],[]),([4691],[3,53,59],[4691]),([],[],[]),([13,19,19],[19,463],[13,19]),([],[],[]),([3,5,313],[3,3,17,47],[5,313]),([],[],[]),([7,11,61],[8297],[7,11,61]),([],[],[]),([37,127],[5,1847],[37,127]),([],[],[]),([3,1567],[3,7,373],[1567]),([],[],[]),([4703],[3,3,5,11,19],[4703]),([],[],[]),([5,941],[5,1693],[941]),([],[],[]),([3,3,523],[3,3,13,67],[523]),([],[],[]),([17,277],[5,5,5,73],[17,277]),([],[],[]),([7,673],[7,1249],[673]),([],[],[]),([3,1571],[7853],[3,1571]),([],[],[]),([5,23,41],[3,3,3,5,61],[23,41]),([],[],[]),([53,89],[9293],[53,89]),([],[],[]),([3,11,11,13],[3,11,223],[11,13]),([],[],[]),([4721],[3,3,1049],[4721]),([],[],[]),([4723],[5,1889],[4723]),([],[],[]),([3,3,3,5,5,7],[3,3,3,3,5,17],[5,7]),([],[],[]),([29,163],[59,157],[29,163]),([],[],[]),([4729],[7,7,193],[4729]),([],[],[]),([3,19,83],[3,13,197],[19,83]),([],[],[]),([4733],[3,5,631],[4733]),([],[],[]),([5,947],[7,1217],[5,947])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range4736 (R D : ℕ) (lo : 4736 ≤ R) (hi : R < 4800) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 4736 64 R D [([],[],[]),([3,1579],[3,3,877],[1579]),([],[],[]),([7,677],[5,1759],[7,677]),([],[],[]),([11,431],[9041],[11,431]),([],[],[]),([3,3,17,31],[3,3,7,11,11],[17,31]),([],[],[]),([5,13,73],[59,139],[5,13,73]),([],[],[]),([47,101],[13,719],[47,101]),([],[],[]),([3,1583],[41,193],[3,1583]),([],[],[]),([4751],[3,3167],[4751]),([],[],[]),([7,7,97],[5,7,251],[7,97]),([],[],[]),([3,5,317],[7283],[3,5,317]),([],[],[]),([67,71],[9377],[67,71]),([],[],[]),([4759],[31,307],[4759]),([],[],[]),([3,3,23,23],[3,23,113],[3,23]),([],[],[]),([11,433],[31,293],[11,433]),([],[],[]),([5,953],[8573],[5,953]),([],[],[]),([3,7,227],[3,3,3,277],[7,227]),([],[],[]),([19,251],[13,23,31],[19,251]),([],[],[]),([13,367],[7,7,11,17],[13,367]),([],[],[]),([3,37,43],[3,23,113],[37,43]),([],[],[]),([5,5,191],[5,5,7,7,7],[191]),([],[],[]),([17,281],[9257],[17,281]),([],[],[]),([3,3,3,3,59],[3,3,3,293],[3,59]),([],[],[]),([7,683],[19,467],[7,683]),([],[],[]),([4783],[5,1913],[4783]),([],[],[]),([3,5,11,29],[5,5,281],[3,11,29]),([],[],[]),([4787],[3,3191],[4787]),([],[],[]),([4789],[61,157],[4789]),([],[],[]),([3,1597],[3,3,887],[1597]),([],[],[]),([4793],[3,3,3,5,71],[4793]),([],[],[]),([5,7,137],[8059],[5,7,137]),([],[],[]),([3,3,13,41],[3,3,853],[13,41]),([],[],[]),([4799],[3,7,457],[4799])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range4800 (R D : ℕ) (lo : 4800 ≤ R) (hi : R < 4864) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 4800 64 R D [([],[],[]),([4801],[9601],[4801]),([],[],[]),([3,1601],[53,151],[3,1601]),([],[],[]),([5,31,31],[5,5,11,31],[31]),([],[],[]),([11,19,23],[11,797],[19,23]),([],[],[]),([3,7,229],[3,5,503],[7,229]),([],[],[]),([17,283],[9323],[17,283]),([],[],[]),([4813],[5,5,5,7,11],[4813]),([],[],[]),([3,3,5,107],[3,11,223],[3,5,107]),([],[],[]),([4817],[3,13,13,19],[4817]),([],[],[]),([61,79],[7,23,59],[61,79]),([],[],[]),([3,1607],[29,277],[3,1607]),([],[],[]),([7,13,53],[13,659],[7,53]),([],[],[]),([5,5,193],[5,1733],[5,193]),([],[],[]),([3,1609],[3,7,383],[1609]),([],[],[]),([11,439],[9209],[11,439]),([],[],[]),([4831],[9661],[4831]),([],[],[]),([3,3,3,179],[3,3,19,47],[3,179]),([],[],[]),([5,967],[8699],[5,967]),([],[],[]),([7,691],[47,191],[7,691]),([],[],[]),([3,1613],[11,733],[3,1613]),([],[],[]),([47,103],[9533],[47,103]),([],[],[]),([29,167],[9491],[29,167]),([],[],[]),([3,5,17,19],[3,2383],[5,17,19]),([],[],[]),([37,131],[7,1361],[37,131]),([],[],[]),([13,373],[67,139],[13,373]),([],[],[]),([3,3,7,7,11],[3,3,3,3,7,13],[7,11]),([],[],[]),([23,211],[9473],[23,211]),([],[],[]),([5,971],[5,1747],[971]),([],[],[]),([3,1619],[8093],[3,1619]),([],[],[]),([43,113],[73,131],[43,113]),([],[],[]),([4861],[9721],[4861]),([],[],[]),([3,1621],[3,37,73],[1621])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range4864 (R D : ℕ) (lo : 4864 ≤ R) (hi : R < 4928) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 4864 64 R D [([],[],[]),([5,7,139],[13,17,37],[5,7,139]),([],[],[]),([31,157],[9547],[31,157]),([],[],[]),([3,3,541],[3,3,17,53],[541]),([],[],[]),([4871],[3,17,191],[4871]),([],[],[]),([11,443],[9293],[11,443]),([],[],[]),([3,5,5,5,13],[3,5,5,97],[5,13]),([],[],[]),([4877],[3,3251],[4877]),([],[],[]),([7,17,41],[8719],[7,17,41]),([],[],[]),([3,1627],[3,2711],[1627]),([],[],[]),([19,257],[9491],[19,257]),([],[],[]),([5,977],[11,17,47],[5,977]),([],[],[]),([3,3,3,181],[3,3,3,7,43],[181]),([],[],[]),([4889],[3,3259],[4889]),([],[],[]),([67,73],[9643],[67,73]),([],[],[]),([3,7,233],[3,3,853],[7,233]),([],[],[]),([5,11,89],[3,3,5,11,17],[89]),([],[],[]),([59,83],[7,7,197],[59,83]),([],[],[]),([3,23,71],[79,101],[3,23,71]),([],[],[]),([13,13,29],[13,23,31],[13,29]),([],[],[]),([4903],[5,37,53],[4903]),([],[],[]),([3,3,5,109],[3,3,7,7,17],[5,109]),([],[],[]),([7,701],[7,1301],[701]),([],[],[]),([4909],[9817],[4909]),([],[],[]),([3,1637],[7,7,167],[3,1637]),([],[],[]),([17,17,17],[3,11,17,17],[17]),([],[],[]),([5,983],[37,239],[5,983]),([],[],[]),([3,11,149],[7877],[3,11,149]),([],[],[]),([4919],[3,3,1093],[4919]),([],[],[]),([7,19,37],[23,383],[7,19,37]),([],[],[]),([3,3,547],[3,3,911],[547]),([],[],[]),([5,5,197],[5,29,61],[5,197]),([],[],[]),([13,379],[9463],[13,379])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range4928 (R D : ℕ) (lo : 4928 ≤ R) (hi : R < 4992) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 4928 64 R D [([],[],[]),([3,31,53],[3,2683],[31,53]),([],[],[]),([4931],[3,19,173],[4931]),([],[],[]),([4933],[5,1973],[4933]),([],[],[]),([3,5,7,47],[3,2381],[5,7,47]),([],[],[]),([4937],[3,3,1097],[4937]),([],[],[]),([11,449],[9419],[11,449]),([],[],[]),([3,3,3,3,61],[3,3,3,3,101],[61]),([],[],[]),([4943],[3,5,659],[4943]),([],[],[]),([5,23,43],[8641],[5,23,43]),([],[],[]),([3,17,97],[3,3,3,3,3,3,11],[17,97]),([],[],[]),([7,7,101],[7,1307],[7,101]),([],[],[]),([4951],[9901],[4951]),([],[],[]),([3,13,127],[3,2659],[13,127]),([],[],[]),([5,991],[5,1783],[991]),([],[],[]),([4957],[23,431],[4957]),([],[],[]),([3,3,19,29],[3,3,887],[19,29]),([],[],[]),([11,11,41],[11,23,37],[11,41]),([],[],[]),([7,709],[61,151],[7,709]),([],[],[]),([3,5,331],[3,3,5,13,13],[331]),([],[],[]),([4967],[3,7,11,43],[4967]),([],[],[]),([4969],[19,523],[4969]),([],[],[]),([3,1657],[3,11,251],[1657]),([],[],[]),([4973],[3,3,5,13,17],[4973]),([],[],[]),([5,5,199],[5,1787],[5,199]),([],[],[]),([3,3,7,79],[3,3,5,173],[7,79]),([],[],[]),([13,383],[73,131],[13,383]),([],[],[]),([17,293],[7,7,197],[17,293]),([],[],[]),([3,11,151],[3,3,887],[11,151]),([],[],[]),([5,997],[8969],[5,997]),([],[],[]),([4987],[9973],[4987]),([],[],[]),([3,1663],[3,17,163],[1663]),([],[],[]),([7,23,31],[8951],[7,23,31])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range4992 (R D : ℕ) (lo : 4992 ≤ R) (hi : R < 5056) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 4992 64 R D [([],[],[]),([4993],[5,1997],[4993]),([],[],[]),([3,3,3,5,37],[3,3,3,281],[5,37]),([],[],[]),([19,263],[11,883],[19,263]),([],[],[]),([4999],[13,769],[4999]),([],[],[]),([3,1667],[13,641],[3,1667]),([],[],[]),([5003],[3,5,23,29],[5003]),([],[],[]),([5,7,11,13],[5,19,83],[7,11,13]),([],[],[]),([3,1669],[3,3,3,3,103],[1669]),([],[],[]),([5009],[3,3,3,7,53],[5009]),([],[],[]),([5011],[11,911],[5011]),([],[],[]),([3,3,557],[3,11,11,23],[3,557]),([],[],[]),([5,17,59],[3,2909],[5,17,59]),([],[],[]),([29,173],[9833],[29,173]),([],[],[]),([3,7,239],[3,3,5,5,5,7],[239]),([],[],[]),([5021],[3,3347],[5021]),([],[],[]),([5023],[5,7,7,41],[5023]),([],[],[]),([3,5,5,67],[3,5,7,73],[5,67]),([],[],[]),([11,457],[9587],[11,457]),([],[],[]),([47,107],[5,7,283],[47,107]),([],[],[]),([3,3,13,43],[3,3,5,179],[13,43]),([],[],[]),([7,719],[9341],[7,719]),([],[],[]),([5,19,53],[8779],[5,19,53]),([],[],[]),([3,23,73],[3,5,547],[23,73]),([],[],[]),([5039],[3,3359],[5039]),([],[],[]),([71,71],[3,47,71],[71]),([],[],[]),([3,41,41],[7,29,41],[3,41]),([],[],[]),([5,1009],[29,313],[5,1009]),([],[],[]),([7,7,103],[7,31,43],[7,103]),([],[],[]),([3,3,3,11,17],[3,3,881],[3,11,17]),([],[],[]),([5051],[3,7,13,37],[5051]),([],[],[]),([31,163],[23,431],[31,163]),([],[],[]),([3,5,337],[3,29,89],[5,337])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range5056 (R D : ℕ) (lo : 5056 ≤ R) (hi : R < 5120) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 5056 64 R D [([],[],[]),([13,389],[11,883],[13,389]),([],[],[]),([5059],[67,151],[5059]),([],[],[]),([3,7,241],[3,2647],[7,241]),([],[],[]),([61,83],[67,149],[61,83]),([],[],[]),([5,1013],[13,701],[5,1013]),([],[],[]),([3,3,563],[3,29,97],[3,563]),([],[],[]),([37,137],[5,1993],[37,137]),([],[],[]),([11,461],[19,509],[11,461]),([],[],[]),([3,19,89],[3,41,67],[19,89]),([],[],[]),([5,5,7,29],[5,7,241],[5,29]),([],[],[]),([5077],[11,13,71],[5077]),([],[],[]),([3,1693],[3,7,13,31],[1693]),([],[],[]),([5081],[3,3,1129],[5081]),([],[],[]),([13,17,23],[41,227],[13,17,23]),([],[],[]),([3,3,5,113],[3,2591],[3,5,113]),([],[],[]),([5087],[3,3391],[5087]),([],[],[]),([7,727],[5,1889],[7,727]),([],[],[]),([3,1697],[17,499],[3,1697]),([],[],[]),([11,463],[11,883],[463]),([],[],[]),([5,1019],[89,103],[5,1019]),([],[],[]),([3,1699],[3,19,149],[1699]),([],[],[]),([5099],[3,3,11,103],[5099]),([],[],[]),([5101],[101,101],[5101]),([],[],[]),([3,3,3,3,3,3,7],[3,3,3,3,3,3,11],[7]),([],[],[]),([5,1021],[5,11,167],[1021]),([],[],[]),([5107],[7,1459],[5107]),([],[],[]),([3,13,131],[3,13,211],[131]),([],[],[]),([19,269],[5,1987],[19,269]),([],[],[]),([5113],[5,5,409],[5113]),([],[],[]),([3,5,11,31],[3,3,5,167],[11,31]),([],[],[]),([7,17,43],[7,1307],[17,43]),([],[],[]),([5119],[29,353],[5119])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range5120 (R D : ℕ) (lo : 5120 ≤ R) (hi : R < 5184) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 5120 64 R D [([],[],[]),([3,3,569],[3,2843],[3,569]),([],[],[]),([47,109],[10091],[47,109]),([],[],[]),([5,5,5,41],[5,5,5,73],[41]),([],[],[]),([3,1709],[8543],[3,1709]),([],[],[]),([23,223],[17,19,31],[23,223]),([],[],[]),([7,733],[89,107],[7,733]),([],[],[]),([3,29,59],[17,17,29],[3,59]),([],[],[]),([5,13,79],[13,683],[5,79]),([],[],[]),([11,467],[97,101],[11,467]),([],[],[]),([3,3,571],[3,3,3,317],[571]),([],[],[]),([53,97],[10133],[53,97]),([],[],[]),([37,139],[10111],[37,139]),([],[],[]),([3,5,7,7,7],[3,3,7,7,17],[5,7]),([],[],[]),([5147],[3,47,73],[5147]),([],[],[]),([19,271],[10009],[19,271]),([],[],[]),([3,17,101],[7,1193],[3,17,101]),([],[],[]),([5153],[3,3,5,229],[5153]),([],[],[]),([5,1031],[5,5,7,53],[1031]),([],[],[]),([3,3,3,191],[3,3,953],[3,191]),([],[],[]),([7,11,67],[11,829],[7,67]),([],[],[]),([13,397],[23,431],[13,397]),([],[],[]),([3,1721],[7,1229],[3,1721]),([],[],[]),([5,1033],[9293],[5,1033]),([],[],[]),([5167],[10333],[5167]),([],[],[]),([3,1723],[3,3,3,11,29],[1723]),([],[],[]),([5171],[3,3,3,383],[5171]),([],[],[]),([7,739],[9601],[7,739]),([],[],[]),([3,3,5,5,23],[3,5,521],[3,5,23]),([],[],[]),([31,167],[7,1451],[31,167]),([],[],[]),([5179],[10357],[5179]),([],[],[]),([3,11,157],[3,2767],[11,157]),([],[],[]),([71,73],[10223],[71,73])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range5184 (R D : ℕ) (lo : 5184 ≤ R) (hi : R < 5248) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 5184 64 R D [([],[],[]),([5,17,61],[5,5,19,19],[17,61]),([],[],[]),([3,7,13,19],[3,2593],[7,13,19]),([],[],[]),([5189],[3,3,1153],[5189]),([],[],[]),([29,179],[5,5,11,37],[29,179]),([],[],[]),([3,3,577],[3,3,31,31],[577]),([],[],[]),([5,1039],[13,719],[5,1039]),([],[],[]),([5197],[19,547],[5197]),([],[],[]),([3,1733],[8663],[3,1733]),([],[],[]),([7,743],[7,7,197],[743]),([],[],[]),([11,11,43],[11,19,47],[11,43]),([],[],[]),([3,5,347],[7,17,67],[3,5,347]),([],[],[]),([41,127],[10247],[41,127]),([],[],[]),([5209],[11,947],[5209]),([],[],[]),([3,3,3,193],[3,3,3,3,107],[193]),([],[],[]),([13,401],[17,19,31],[13,401]),([],[],[]),([5,7,149],[11,797],[5,7,149]),([],[],[]),([3,37,47],[3,2843],[37,47]),([],[],[]),([17,307],[5,7,17,17],[307]),([],[],[]),([23,227],[10193],[23,227]),([],[],[]),([3,1741],[3,3,967],[1741]),([],[],[]),([5,5,11,19],[5,5,353],[11,19]),([],[],[]),([5227],[10453],[5227]),([],[],[]),([3,3,7,83],[3,3,3,3,101],[7,83]),([],[],[]),([5231],[3,11,317],[5231]),([],[],[]),([5233],[5,7,13,23],[5233]),([],[],[]),([3,5,349],[3,3,3,3,3,3,11],[5,349]),([],[],[]),([5237],[3,3491],[5237]),([],[],[]),([13,13,31],[7,13,109],[13,31]),([],[],[]),([3,1747],[3,41,71],[1747]),([],[],[]),([7,7,107],[5,7,277],[7,107]),([],[],[]),([5,1049],[9437],[5,1049]),([],[],[]),([3,3,11,53],[3,2789],[3,11,53])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range5248 (R D : ℕ) (lo : 5248 ≤ R) (hi : R < 5312) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 5248 64 R D [([],[],[]),([29,181],[10289],[29,181]),([],[],[]),([59,89],[5,19,109],[59,89]),([],[],[]),([3,17,103],[3,17,167],[103]),([],[],[]),([5,1051],[5,31,61],[1051]),([],[],[]),([7,751],[11,887],[7,751]),([],[],[]),([3,1753],[3,23,127],[1753]),([],[],[]),([5261],[3,3,7,167],[5261]),([],[],[]),([19,277],[13,787],[19,277]),([],[],[]),([3,3,3,3,5,13],[3,3,3,3,97],[5,13]),([],[],[]),([23,229],[7,13,113],[23,229]),([],[],[]),([11,479],[13,773],[11,479]),([],[],[]),([3,7,251],[3,3,919],[7,251]),([],[],[]),([5273],[3,5,19,37],[5273]),([],[],[]),([5,5,211],[5,5,379],[211]),([],[],[]),([3,1759],[3,3,977],[1759]),([],[],[]),([5279],[3,3,3,17,23],[5279]),([],[],[]),([5281],[59,179],[5281]),([],[],[]),([3,3,587],[3,7,419],[3,587]),([],[],[]),([5,7,151],[5,1777],[7,151]),([],[],[]),([17,311],[10247],[17,311]),([],[],[]),([3,41,43],[3,3,31,31],[41,43]),([],[],[]),([11,13,37],[7,1373],[11,13,37]),([],[],[]),([67,79],[53,197],[67,79]),([],[],[]),([3,5,353],[8111],[3,5,353]),([],[],[]),([5297],[3,3,11,107],[5297]),([],[],[]),([7,757],[5,7,281],[757]),([],[],[]),([3,3,19,31],[3,3,13,73],[19,31]),([],[],[]),([5303],[3,5,7,101],[5303]),([],[],[]),([5,1061],[5,23,83],[1061]),([],[],[]),([3,29,61],[3,3,3,3,107],[29,61]),([],[],[]),([5309],[3,3539],[5309]),([],[],[]),([47,113],[10463],[47,113])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range5312 (R D : ℕ) (lo : 5312 ≤ R) (hi : R < 5376) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 5312 64 R D [([],[],[]),([3,7,11,23],[3,11,241],[7,23]),([],[],[]),([5,1063],[73,131],[5,1063]),([],[],[]),([13,409],[7,1459],[13,409]),([],[],[]),([3,3,3,197],[3,3,983],[3,197]),([],[],[]),([17,313],[10313],[17,313]),([],[],[]),([5323],[5,2129],[5323]),([],[],[]),([3,5,5,71],[5,5,5,5,13],[3,71]),([],[],[]),([7,761],[9887],[7,761]),([],[],[]),([73,73],[5,29,73],[73]),([],[],[]),([3,1777],[3,3,3,7,47],[1777]),([],[],[]),([5333],[3,3,3,5,79],[5333]),([],[],[]),([5,11,97],[5,5,367],[11,97]),([],[],[]),([3,3,593],[3,2963],[3,593]),([],[],[]),([19,281],[97,107],[19,281]),([],[],[]),([7,7,109],[7,17,83],[7,109]),([],[],[]),([3,13,137],[3,19,151],[13,137]),([],[],[]),([5,1069],[59,163],[5,1069]),([],[],[]),([5347],[17,17,37],[5347]),([],[],[]),([3,1783],[3,2971],[1783]),([],[],[]),([5351],[3,3,29,41],[5351]),([],[],[]),([53,101],[61,173],[53,101]),([],[],[]),([3,3,5,7,17],[3,3,23,37],[5,7,17]),([],[],[]),([11,487],[17,601],[11,487]),([],[],[]),([23,233],[10463],[23,233]),([],[],[]),([3,1787],[8933],[3,1787]),([],[],[]),([31,173],[17,619],[31,173]),([],[],[]),([5,29,37],[9397],[5,29,37]),([],[],[]),([3,1789],[3,11,271],[1789]),([],[],[]),([7,13,59],[5,23,83],[7,13,59]),([],[],[]),([41,131],[11,31,31],[41,131]),([],[],[]),([3,3,3,199],[3,3,3,331],[199]),([],[],[]),([5,5,5,43],[5,5,383],[5,43])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range5376 (R D : ℕ) (lo : 5376 ≤ R) (hi : R < 5440) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 5376 64 R D [([],[],[]),([19,283],[10453],[19,283]),([],[],[]),([3,11,163],[3,13,13,17],[11,163]),([],[],[]),([5381],[3,17,211],[5381]),([],[],[]),([7,769],[97,103],[7,769]),([],[],[]),([3,5,359],[73,113],[3,5,359]),([],[],[]),([5387],[3,3,3,3,7,19],[5387]),([],[],[]),([17,317],[5,2089],[17,317]),([],[],[]),([3,3,599],[3,41,73],[3,599]),([],[],[]),([5393],[3,5,719],[5393]),([],[],[]),([5,13,83],[7,31,43],[5,13,83]),([],[],[]),([3,7,257],[3,3,941],[7,257]),([],[],[]),([5399],[3,59,61],[5399]),([],[],[]),([11,491],[10301],[11,491]),([],[],[]),([3,1801],[3,3001],[1801]),([],[],[]),([5,23,47],[3,23,137],[5,47]),([],[],[]),([5407],[11,983],[5407]),([],[],[]),([3,3,601],[3,3,7,11,13],[601]),([],[],[]),([7,773],[11,11,83],[7,773]),([],[],[]),([5413],[5,5,433],[5413]),([],[],[]),([3,5,19,19],[3,11,13,19],[5,19]),([],[],[]),([5417],[3,23,157],[5417]),([],[],[]),([5419],[10837],[5419]),([],[],[]),([3,13,139],[3,41,71],[13,139]),([],[],[]),([11,17,29],[3,3301],[11,17,29]),([],[],[]),([5,5,7,31],[5,5,19,19],[7,31]),([],[],[]),([3,3,3,3,67],[3,3,3,3,3,37],[67]),([],[],[]),([61,89],[10709],[61,89]),([],[],[]),([5431],[10861],[5431]),([],[],[]),([3,1811],[11,823],[3,1811]),([],[],[]),([5,1087],[7,11,127],[5,1087]),([],[],[]),([5437],[83,131],[5437]),([],[],[]),([3,7,7,37],[3,7,13,31],[7,37])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range5440 (R D : ℕ) (lo : 5440 ≤ R) (hi : R < 5504) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 5440 64 R D [([],[],[]),([5441],[3,3,3,13,31],[5441]),([],[],[]),([5443],[5,7,311],[5443]),([],[],[]),([3,3,5,11,11],[3,5,7,7,11],[3,11]),([],[],[]),([13,419],[10463],[13,419]),([],[],[]),([5449],[17,641],[5449]),([],[],[]),([3,23,79],[3,3,3,7,47],[23,79]),([],[],[]),([7,19,41],[29,337],[7,19,41]),([],[],[]),([5,1091],[5,13,151],[1091]),([],[],[]),([3,17,107],[8849],[3,17,107]),([],[],[]),([53,103],[47,229],[53,103]),([],[],[]),([43,127],[10753],[43,127]),([],[],[]),([3,3,607],[3,3,3,337],[607]),([],[],[]),([5,1093],[9833],[5,1093]),([],[],[]),([7,11,71],[7,1381],[11,71]),([],[],[]),([3,1823],[13,701],[3,1823]),([],[],[]),([5471],[3,7,521],[5471]),([],[],[]),([13,421],[10513],[13,421]),([],[],[]),([3,5,5,73],[3,5,557],[5,73]),([],[],[]),([5477],[3,3,1217],[5477]),([],[],[]),([5479],[10957],[5479]),([],[],[]),([3,3,3,7,29],[3,3,3,3,3,5,7],[29]),([],[],[]),([5483],[3,5,17,43],[5483]),([],[],[]),([5,1097],[71,139],[5,1097]),([],[],[]),([3,31,59],[3,7,7,61],[31,59]),([],[],[]),([11,499],[19,19,29],[11,499]),([],[],[]),([17,17,19],[13,17,47],[17,19]),([],[],[]),([3,1831],[3,3,3,3,113],[1831]),([],[],[]),([5,7,157],[9239],[5,7,157]),([],[],[]),([23,239],[10733],[23,239]),([],[],[]),([3,3,13,47],[3,3,11,89],[13,47]),([],[],[]),([5501],[3,19,193],[5501]),([],[],[]),([5503],[5,31,71],[5503])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range5504 (R D : ℕ) (lo : 5504 ≤ R) (hi : R < 5568) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 5504 64 R D [([],[],[]),([3,5,367],[3,3,937],[5,367]),([],[],[]),([5507],[3,3671],[5507]),([],[],[]),([7,787],[5,5,409],[7,787]),([],[],[]),([3,11,167],[8831],[3,11,167]),([],[],[]),([37,149],[37,293],[149]),([],[],[]),([5,1103],[9923],[5,1103]),([],[],[]),([3,3,613],[3,3,1021],[613]),([],[],[]),([5519],[3,13,283],[5519]),([],[],[]),([5521],[61,181],[5521]),([],[],[]),([3,7,263],[3,3,3,3,107],[7,263]),([],[],[]),([5,5,13,17],[5,1873],[5,13,17]),([],[],[]),([5527],[7,1579],[5527]),([],[],[]),([3,19,97],[3,5,599],[19,97]),([],[],[]),([5531],[3,3,1229],[5531]),([],[],[]),([11,503],[61,173],[11,503]),([],[],[]),([3,3,3,5,41],[3,3,5,11,17],[3,41]),([],[],[]),([7,7,113],[7,7,11,19],[113]),([],[],[]),([29,191],[10859],[29,191]),([],[],[]),([3,1847],[7,1319],[3,1847]),([],[],[]),([23,241],[79,137],[23,241]),([],[],[]),([5,1109],[11,907],[5,1109]),([],[],[]),([3,43,43],[3,43,71],[43]),([],[],[]),([31,179],[10889],[31,179]),([],[],[]),([7,13,61],[9871],[7,13,61]),([],[],[]),([3,3,617],[3,3083],[3,617]),([],[],[]),([5,11,101],[3,5,7,7,13],[11,101]),([],[],[]),([5557],[11113],[5557]),([],[],[]),([3,17,109],[3,5,601],[17,109]),([],[],[]),([67,83],[10973],[67,83]),([],[],[]),([5563],[5,5,5,89],[5563]),([],[],[]),([3,5,7,53],[3,2687],[5,7,53]),([],[],[]),([19,293],[79,137],[19,293])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range5568 (R D : ℕ) (lo : 5568 ≤ R) (hi : R < 5632) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 5568 64 R D [([],[],[]),([5569],[7,37,43],[5569]),([],[],[]),([3,3,619],[3,3,1031],[619]),([],[],[]),([5573],[3,5,743],[5573]),([],[],[]),([5,5,223],[5,2003],[5,223]),([],[],[]),([3,11,13,13],[3,13,223],[11,13]),([],[],[]),([7,797],[5,19,109],[7,797]),([],[],[]),([5581],[11161],[5581]),([],[],[]),([3,1861],[3,7,443],[1861]),([],[],[]),([5,1117],[13,773],[5,1117]),([],[],[]),([37,151],[10987],[37,151]),([],[],[]),([3,3,3,3,3,23],[3,3,3,3,113],[3,23]),([],[],[]),([5591],[3,3727],[5591]),([],[],[]),([7,17,47],[10009],[7,17,47]),([],[],[]),([3,5,373],[3,2857],[5,373]),([],[],[]),([29,193],[10973],[29,193]),([],[],[]),([11,509],[59,181],[11,509]),([],[],[]),([3,1867],[3,3,17,61],[1867]),([],[],[]),([13,431],[47,229],[13,431]),([],[],[]),([5,19,59],[9781],[5,19,59]),([],[],[]),([3,3,7,89],[3,3,3,5,5,13],[7,89]),([],[],[]),([71,79],[11069],[71,79]),([],[],[]),([31,181],[7,11,11,13],[31,181]),([],[],[]),([3,1871],[47,199],[3,1871]),([],[],[]),([5,1123],[10103],[5,1123]),([],[],[]),([41,137],[11057],[41,137]),([],[],[]),([3,1873],[3,3121],[1873]),([],[],[]),([7,11,73],[9941],[7,11,73]),([],[],[]),([5623],[5,13,173],[5623]),([],[],[]),([3,3,5,5,5,5],[3,5,5,5,23],[3,5]),([],[],[]),([17,331],[13,839],[17,331]),([],[],[]),([13,433],[11,983],[13,433]),([],[],[]),([3,1877],[11,853],[3,1877])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range5632 (R D : ℕ) (lo : 5632 ≤ R) (hi : R < 5696) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 5632 64 R D [([],[],[]),([43,131],[11093],[43,131]),([],[],[]),([5,7,7,23],[7,31,43],[5,7,23]),([],[],[]),([3,1879],[3,31,101],[1879]),([],[],[]),([5639],[3,3,7,179],[5639]),([],[],[]),([5641],[29,389],[5641]),([],[],[]),([3,3,3,11,19],[3,3,3,7,47],[11,19]),([],[],[]),([5,1129],[7,1451],[5,1129]),([],[],[]),([5647],[23,491],[5647]),([],[],[]),([3,7,269],[3,3,5,197],[7,269]),([],[],[]),([5651],[3,3767],[5651]),([],[],[]),([5653],[5,7,17,19],[5653]),([],[],[]),([3,5,13,29],[3,3,3,3,103],[5,13,29]),([],[],[]),([5657],[3,3,3,419],[5657]),([],[],[]),([5659],[11317],[5659]),([],[],[]),([3,3,17,37],[3,3,1013],[17,37]),([],[],[]),([7,809],[23,457],[7,809]),([],[],[]),([5,11,103],[5,1949],[11,103]),([],[],[]),([3,1889],[7,19,71],[3,1889]),([],[],[]),([5669],[3,3779],[5669]),([],[],[]),([53,107],[53,211],[107]),([],[],[]),([3,31,61],[3,11,281],[31,61]),([],[],[]),([5,5,227],[5,2039],[5,227]),([],[],[]),([7,811],[41,257],[7,811]),([],[],[]),([3,3,631],[3,3,1051],[631]),([],[],[]),([13,19,23],[10433],[13,19,23]),([],[],[]),([5683],[5,2273],[5683]),([],[],[]),([3,5,379],[3,2903],[5,379]),([],[],[]),([11,11,47],[11,977],[11,47]),([],[],[]),([5689],[31,367],[5689]),([],[],[]),([3,7,271],[3,13,229],[7,271]),([],[],[]),([5693],[3,3,5,11,23],[5693]),([],[],[]),([5,17,67],[7,13,109],[5,17,67])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range5696 (R D : ℕ) (lo : 5696 ≤ R) (hi : R < 5760) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 5696 64 R D [([],[],[]),([3,3,3,211],[3,3,3,3,3,3,13],[211]),([],[],[]),([41,139],[13,863],[41,139]),([],[],[]),([5701],[13,877],[5701]),([],[],[]),([3,1901],[13,17,43],[3,1901]),([],[],[]),([5,7,163],[53,181],[5,7,163]),([],[],[]),([13,439],[19,577],[13,439]),([],[],[]),([3,11,173],[7,1307],[3,11,173]),([],[],[]),([5711],[3,3,3,3,3,47],[5711]),([],[],[]),([29,197],[23,487],[29,197]),([],[],[]),([3,3,5,127],[3,3,971],[5,127]),([],[],[]),([5717],[3,37,103],[5717]),([],[],[]),([7,19,43],[5,7,293],[19,43]),([],[],[]),([3,1907],[9533],[3,1907]),([],[],[]),([59,97],[7,1613],[59,97]),([],[],[]),([5,5,229],[5,11,11,17],[5,229]),([],[],[]),([3,23,83],[5,1867],[3,23,83]),([],[],[]),([17,337],[5,2221],[17,337]),([],[],[]),([11,521],[17,643],[11,521]),([],[],[]),([3,3,7,7,13],[3,3,7,139],[7,13]),([],[],[]),([5,31,37],[5,2011],[31,37]),([],[],[]),([5737],[7,11,149],[5737]),([],[],[]),([3,1913],[73,131],[3,1913]),([],[],[]),([5741],[3,43,89],[5741]),([],[],[]),([5743],[5,2297],[5743]),([],[],[]),([3,5,383],[13,677],[3,5,383]),([],[],[]),([7,821],[10667],[7,821]),([],[],[]),([5749],[11497],[5749]),([],[],[]),([3,3,3,3,71],[3,3,3,353],[3,71]),([],[],[]),([11,523],[10973],[11,523]),([],[],[]),([5,1151],[5,19,109],[1151]),([],[],[]),([3,19,101],[3,3119],[19,101]),([],[],[]),([13,443],[13,23,37],[443])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range5760 (R D : ℕ) (lo : 5760 ≤ R) (hi : R < 5824) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 5760 64 R D [([],[],[]),([7,823],[17,17,37],[7,823]),([],[],[]),([3,17,113],[13,719],[3,17,113]),([],[],[]),([5,1153],[11,23,41],[5,1153]),([],[],[]),([73,79],[11383],[73,79]),([],[],[]),([3,3,641],[3,3203],[3,641]),([],[],[]),([29,199],[5,31,73],[29,199]),([],[],[]),([23,251],[11273],[23,251]),([],[],[]),([3,5,5,7,11],[3,5,5,109],[7,11]),([],[],[]),([53,109],[11393],[53,109]),([],[],[]),([5779],[7,13,127],[5779]),([],[],[]),([3,41,47],[9461],[3,41,47]),([],[],[]),([5783],[3,3,5,257],[5783]),([],[],[]),([5,13,89],[10009],[5,13,89]),([],[],[]),([3,3,643],[3,3,3,3,7,17],[643]),([],[],[]),([7,827],[5,7,307],[827]),([],[],[]),([5791],[37,313],[5791]),([],[],[]),([3,1931],[7,7,197],[3,1931]),([],[],[]),([5,19,61],[5,7,17,17],[19,61]),([],[],[]),([11,17,31],[10597],[11,17,31]),([],[],[]),([3,1933],[3,3221],[1933]),([],[],[]),([5801],[3,3,1289],[5801]),([],[],[]),([7,829],[10771],[7,829]),([],[],[]),([3,3,3,5,43],[3,3,3,3,109],[5,43]),([],[],[]),([5807],[3,7,7,79],[5807]),([],[],[]),([37,157],[5,5,457],[37,157]),([],[],[]),([3,13,149],[3,3121],[13,149]),([],[],[]),([5813],[3,5,5,5,31],[5813]),([],[],[]),([5,1163],[10463],[5,1163]),([],[],[]),([3,7,277],[3,17,179],[7,277]),([],[],[]),([11,23,23],[11,23,43],[23]),([],[],[]),([5821],[7,1663],[5821]),([],[],[]),([3,3,647],[3,53,61],[3,647])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range5824 (R D : ℕ) (lo : 5824 ≤ R) (hi : R < 5888) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 5824 64 R D [([],[],[]),([5,5,233],[5,7,13,23],[5,233]),([],[],[]),([5827],[43,271],[5827]),([],[],[]),([3,29,67],[3,5,5,127],[29,67]),([],[],[]),([7,7,7,17],[5,7,7,43],[7,17]),([],[],[]),([19,307],[11,1031],[19,307]),([],[],[]),([3,5,389],[7,1277],[3,5,389]),([],[],[]),([13,449],[11213],[13,449]),([],[],[]),([5839],[11677],[5839]),([],[],[]),([3,3,11,59],[3,13,239],[3,11,59]),([],[],[]),([5843],[3,5,19,41],[5843]),([],[],[]),([5,7,167],[9829],[5,7,167]),([],[],[]),([3,1949],[9743],[3,1949]),([],[],[]),([5849],[3,7,557],[5849]),([],[],[]),([5851],[11701],[5851]),([],[],[]),([3,1951],[3,3251],[1951]),([],[],[]),([5,1171],[5,7,7,43],[1171]),([],[],[]),([5857],[13,17,53],[5857]),([],[],[]),([3,3,3,7,31],[3,3,3,337],[7,31]),([],[],[]),([5861],[3,3907],[5861]),([],[],[]),([11,13,41],[10663],[11,13,41]),([],[],[]),([3,5,17,23],[8681],[3,5,17,23]),([],[],[]),([5867],[3,3911],[5867]),([],[],[]),([5869],[11,11,97],[5869]),([],[],[]),([3,19,103],[3,3181],[19,103]),([],[],[]),([7,839],[11,991],[7,839]),([],[],[]),([5,5,5,47],[5,5,419],[5,47]),([],[],[]),([3,3,653],[3,13,251],[3,653]),([],[],[]),([5879],[3,3919],[5879]),([],[],[]),([5881],[19,619],[5881]),([],[],[]),([3,37,53],[3,3209],[37,53]),([],[],[]),([5,11,107],[3,3,3,3,5,5,5],[11,107]),([],[],[]),([7,29,29],[7,29,53],[29])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range5888 (R D : ℕ) (lo : 5888 ≤ R) (hi : R < 5952) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 5888 64 R D [([],[],[]),([3,13,151],[3,3163],[13,151]),([],[],[]),([43,137],[41,283],[43,137]),([],[],[]),([71,83],[11633],[71,83]),([],[],[]),([3,3,5,131],[3,5,601],[3,131]),([],[],[]),([5897],[3,3931],[5897]),([],[],[]),([17,347],[5,2287],[17,347]),([],[],[]),([3,7,281],[3,3,3,7,7,7],[281]),([],[],[]),([5903],[3,5,787],[5903]),([],[],[]),([5,1181],[5,5,5,5,17],[1181]),([],[],[]),([3,11,179],[9467],[3,11,179]),([],[],[]),([19,311],[11489],[19,311]),([],[],[]),([23,257],[7,17,97],[23,257]),([],[],[]),([3,3,3,3,73],[3,3,3,3,11,11],[73]),([],[],[]),([5,7,13,13],[13,743],[5,7,13]),([],[],[]),([61,97],[11677],[61,97]),([],[],[]),([3,1973],[7,1409],[3,1973]),([],[],[]),([31,191],[11621],[31,191]),([],[],[]),([5923],[5,23,103],[5923]),([],[],[]),([3,5,5,79],[3,3,3,5,67],[5,79]),([],[],[]),([5927],[3,3,3,439],[5927]),([],[],[]),([7,7,11,11],[7,11,137],[7,11]),([],[],[]),([3,3,659],[3,37,89],[3,659]),([],[],[]),([17,349],[7,31,53],[17,349]),([],[],[]),([5,1187],[59,181],[5,1187]),([],[],[]),([3,1979],[13,761],[3,1979]),([],[],[]),([5939],[3,37,107],[5939]),([],[],[]),([13,457],[101,113],[13,457]),([],[],[]),([3,7,283],[3,3109],[7,283]),([],[],[]),([5,29,41],[3,5,5,139],[29,41]),([],[],[]),([19,313],[31,373],[19,313]),([],[],[]),([3,3,661],[3,3,3,367],[661]),([],[],[]),([11,541],[11351],[11,541])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range5952 (R D : ℕ) (lo : 5952 ≤ R) (hi : R < 6016) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 5952 64 R D [([],[],[]),([5953],[5,2381],[5953]),([],[],[]),([3,5,397],[3,3041],[5,397]),([],[],[]),([7,23,37],[10709],[7,23,37]),([],[],[]),([59,101],[11,1069],[59,101]),([],[],[]),([3,1987],[3,7,11,43],[1987]),([],[],[]),([67,89],[79,149],[67,89]),([],[],[]),([5,1193],[10733],[5,1193]),([],[],[]),([3,3,3,13,17],[3,3,3,349],[13,17]),([],[],[]),([47,127],[5,13,181],[47,127]),([],[],[]),([7,853],[11083],[7,853]),([],[],[]),([3,11,181],[3,3191],[11,181]),([],[],[]),([5,5,239],[5,19,113],[5,239]),([],[],[]),([43,139],[61,193],[43,139]),([],[],[]),([3,1993],[3,3,3,3,3,41],[1993]),([],[],[]),([5981],[3,3,3,443],[5981]),([],[],[]),([31,193],[11743],[31,193]),([],[],[]),([3,3,5,7,19],[3,3,953],[5,7,19]),([],[],[]),([5987],[3,13,307],[5987]),([],[],[]),([53,113],[11813],[53,113]),([],[],[]),([3,1997],[67,149],[3,1997]),([],[],[]),([13,461],[29,397],[13,461]),([],[],[]),([5,11,109],[5,2063],[11,109]),([],[],[]),([3,1999],[3,3331],[1999]),([],[],[]),([7,857],[5,17,131],[7,857]),([],[],[]),([17,353],[11633],[17,353]),([],[],[]),([3,3,23,29],[3,53,61],[3,23,29]),([],[],[]),([5,1201],[5,2161],[1201]),([],[],[]),([6007],[41,293],[6007]),([],[],[]),([3,2003],[17,19,31],[3,2003]),([],[],[]),([6011],[3,4007],[6011]),([],[],[]),([7,859],[11161],[7,859]),([],[],[]),([3,5,401],[5,19,97],[3,401])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range6016 (R D : ℕ) (lo : 6016 ≤ R) (hi : R < 6080) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 6016 64 R D [([],[],[]),([11,547],[23,499],[11,547]),([],[],[]),([13,463],[31,373],[13,463]),([],[],[]),([3,3,3,223],[3,3,3,7,53],[223]),([],[],[]),([19,317],[7,7,239],[19,317]),([],[],[]),([5,5,241],[5,5,433],[241]),([],[],[]),([3,7,7,41],[3,3,7,149],[7,41]),([],[],[]),([6029],[3,4019],[6029]),([],[],[]),([37,163],[11863],[37,163]),([],[],[]),([3,2011],[3,3,1117],[2011]),([],[],[]),([5,17,71],[3,5,701],[17,71]),([],[],[]),([6037],[12073],[6037]),([],[],[]),([3,3,11,61],[3,3,3,3,7,17],[11,61]),([],[],[]),([7,863],[11213],[7,863]),([],[],[]),([6043],[5,2417],[6043]),([],[],[]),([3,5,13,31],[3,5,5,7,17],[13,31]),([],[],[]),([6047],[3,29,139],[6047]),([],[],[]),([23,263],[11813],[23,263]),([],[],[]),([3,2017],[3,3361],[2017]),([],[],[]),([6053],[3,3,5,269],[6053]),([],[],[]),([5,7,173],[17,599],[5,7,173]),([],[],[]),([3,3,673],[3,3,19,59],[673]),([],[],[]),([73,83],[7,1709],[73,83]),([],[],[]),([11,19,29],[17,653],[11,19,29]),([],[],[]),([3,43,47],[3,3,1103],[43,47]),([],[],[]),([5,1213],[7,1559],[5,1213]),([],[],[]),([6067],[11,1103],[6067]),([],[],[]),([3,7,17,17],[3,3,17,61],[7,17]),([],[],[]),([13,467],[107,109],[13,467]),([],[],[]),([6073],[5,7,347],[6073]),([],[],[]),([3,3,3,3,3,5,5],[3,3,3,3,5,23],[3,5]),([],[],[]),([59,103],[67,179],[59,103]),([],[],[]),([6079],[12157],[6079])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range6080 (R D : ℕ) (lo : 6080 ≤ R) (hi : R < 6144) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 6080 64 R D [([],[],[]),([3,2027],[10133],[3,2027]),([],[],[]),([7,11,79],[47,229],[7,11,79]),([],[],[]),([5,1217],[10949],[5,1217]),([],[],[]),([3,2029],[3,3,7,7,23],[2029]),([],[],[]),([6089],[3,3,3,11,41],[6089]),([],[],[]),([6091],[13,937],[6091]),([],[],[]),([3,3,677],[3,17,199],[3,677]),([],[],[]),([5,23,53],[3,3557],[5,23,53]),([],[],[]),([7,13,67],[19,571],[7,13,67]),([],[],[]),([3,19,107],[3,5,661],[19,107]),([],[],[]),([6101],[3,7,7,83],[6101]),([],[],[]),([17,359],[11831],[17,359]),([],[],[]),([3,5,11,37],[3,5,599],[11,37]),([],[],[]),([31,197],[11987],[31,197]),([],[],[]),([41,149],[23,523],[41,149]),([],[],[]),([3,3,7,97],[3,3,1063],[7,97]),([],[],[]),([6113],[3,5,5,163],[6113]),([],[],[]),([5,1223],[11003],[5,1223]),([],[],[]),([3,2039],[10193],[3,2039]),([],[],[]),([29,211],[13,13,71],[29,211]),([],[],[]),([6121],[12241],[6121]),([],[],[]),([3,13,157],[3,11,13,23],[157]),([],[],[]),([5,5,5,7,7],[5,5,7,59],[5,7]),([],[],[]),([11,557],[13,29,31],[11,557]),([],[],[]),([3,3,3,227],[3,3,11,103],[3,227]),([],[],[]),([6131],[3,61,67],[6131]),([],[],[]),([6133],[5,11,223],[6133]),([],[],[]),([3,5,409],[3,13,241],[5,409]),([],[],[]),([17,19,19],[13,19,47],[17,19]),([],[],[]),([7,877],[5,43,53],[7,877]),([],[],[]),([3,23,89],[17,19,31],[3,23,89]),([],[],[]),([6143],[3,3,3,5,7,13],[6143])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range6144 (R D : ℕ) (lo : 6144 ≤ R) (hi : R < 6208) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 6144 64 R D [([],[],[]),([5,1229],[11057],[5,1229]),([],[],[]),([3,3,683],[3,3413],[3,683]),([],[],[]),([11,13,43],[67,167],[11,13,43]),([],[],[]),([6151],[12301],[6151]),([],[],[]),([3,7,293],[3,3,29,37],[7,293]),([],[],[]),([5,1231],[5,5,443],[1231]),([],[],[]),([47,131],[53,229],[47,131]),([],[],[]),([3,2053],[3,11,311],[2053]),([],[],[]),([61,101],[12161],[61,101]),([],[],[]),([6163],[5,5,17,29],[6163]),([],[],[]),([3,3,5,137],[3,7,449],[3,5,137]),([],[],[]),([7,881],[11447],[7,881]),([],[],[]),([31,199],[12109],[31,199]),([],[],[]),([3,11,11,17],[11,881],[3,11,17]),([],[],[]),([6173],[3,5,823],[6173]),([],[],[]),([5,5,13,19],[5,2099],[5,13,19]),([],[],[]),([3,29,71],[23,439],[3,29,71]),([],[],[]),([37,167],[5,11,13,17],[37,167]),([],[],[]),([7,883],[7,11,149],[883]),([],[],[]),([3,3,3,229],[3,3,3,3,127],[229]),([],[],[]),([5,1237],[31,359],[5,1237]),([],[],[]),([23,269],[43,281],[23,269]),([],[],[]),([3,2063],[10313],[3,2063]),([],[],[]),([41,151],[73,167],[41,151]),([],[],[]),([11,563],[11813],[11,563]),([],[],[]),([3,5,7,59],[3,41,73],[5,7,59]),([],[],[]),([6197],[3,3,3,3,3,3,17],[6197]),([],[],[]),([6199],[7,7,11,23],[6199]),([],[],[]),([3,3,13,53],[3,3,5,13,17],[53]),([],[],[]),([6203],[3,5,827],[6203]),([],[],[]),([5,17,73],[11,983],[5,17,73]),([],[],[]),([3,2069],[10343],[3,2069])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range6208 (R D : ℕ) (lo : 6208 ≤ R) (hi : R < 6272) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 6208 64 R D [([],[],[]),([7,887],[5,5,461],[7,887]),([],[],[]),([6211],[12421],[6211]),([],[],[]),([3,19,109],[3,7,13,37],[19,109]),([],[],[]),([5,11,113],[3,5,23,31],[11,113]),([],[],[]),([6217],[12433],[6217]),([],[],[]),([3,3,691],[3,3,1151],[691]),([],[],[]),([6221],[3,11,13,29],[6221]),([],[],[]),([7,7,127],[5,7,7,47],[127]),([],[],[]),([3,5,5,83],[5,1901],[3,5,83]),([],[],[]),([13,479],[7,1709],[13,479]),([],[],[]),([6229],[12457],[6229]),([],[],[]),([3,31,67],[3,43,79],[31,67]),([],[],[]),([23,271],[7,37,47],[23,271]),([],[],[]),([5,29,43],[10939],[5,29,43]),([],[],[]),([3,3,3,3,7,11],[3,3,3,3,3,3,13],[7,11]),([],[],[]),([17,367],[5,41,59],[17,367]),([],[],[]),([79,79],[79,157],[79]),([],[],[]),([3,2081],[101,103],[3,2081]),([],[],[]),([5,1249],[17,661],[5,1249]),([],[],[]),([6247],[13,31,31],[6247]),([],[],[]),([3,2083],[3,3,13,89],[2083]),([],[],[]),([7,19,47],[13,863],[7,19,47]),([],[],[]),([13,13,37],[11,13,83],[13,37]),([],[],[]),([3,3,5,139],[3,3,1063],[5,139]),([],[],[]),([6257],[3,43,97],[6257]),([],[],[]),([11,569],[11939],[11,569]),([],[],[]),([3,2087],[10433],[3,2087]),([],[],[]),([6263],[3,5,5,167],[6263]),([],[],[]),([5,7,179],[41,257],[5,7,179]),([],[],[]),([3,2089],[3,59,59],[2089]),([],[],[]),([6269],[3,3,7,199],[6269]),([],[],[]),([6271],[12541],[6271])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range6272 (R D : ℕ) (lo : 6272 ≤ R) (hi : R < 6336) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 6272 64 R D [([],[],[]),([3,3,17,41],[3,3371],[3,17,41]),([],[],[]),([5,5,251],[5,5,11,41],[251]),([],[],[]),([6277],[12553],[6277]),([],[],[]),([3,7,13,23],[3,47,67],[7,13,23]),([],[],[]),([11,571],[11981],[11,571]),([],[],[]),([61,103],[79,157],[61,103]),([],[],[]),([3,5,419],[9629],[3,5,419]),([],[],[]),([6287],[3,3,11,127],[6287]),([],[],[]),([19,331],[7,1747],[19,331]),([],[],[]),([3,3,3,233],[3,3,1163],[3,233]),([],[],[]),([7,29,31],[7,1619],[29,31]),([],[],[]),([5,1259],[47,241],[5,1259]),([],[],[]),([3,2099],[7,1499],[3,2099]),([],[],[]),([6299],[3,13,17,19],[6299]),([],[],[]),([6301],[12601],[6301]),([],[],[]),([3,11,191],[10103],[3,11,191]),([],[],[]),([5,13,97],[7,1559],[5,13,97]),([],[],[]),([7,17,53],[11299],[7,17,53]),([],[],[]),([3,3,701],[3,31,113],[3,701]),([],[],[]),([6311],[3,7,601],[6311]),([],[],[]),([59,107],[17,733],[59,107]),([],[],[]),([3,5,421],[3,3,5,5,43],[421]),([],[],[]),([6317],[3,4211],[6317]),([],[],[]),([71,89],[12479],[71,89]),([],[],[]),([3,7,7,43],[3,7,7,67],[43]),([],[],[]),([6323],[3,3,5,281],[6323]),([],[],[]),([5,5,11,23],[3,5,5,11,13],[23]),([],[],[]),([3,3,19,37],[3,3,5,227],[19,37]),([],[],[]),([6329],[3,4219],[6329]),([],[],[]),([13,487],[12163],[13,487]),([],[],[]),([3,2111],[61,173],[3,2111]),([],[],[]),([5,7,181],[5,2131],[7,181])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range6336 (R D : ℕ) (lo : 6336 ≤ R) (hi : R < 6400) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 6336 64 R D [([],[],[]),([6337],[19,23,29],[6337]),([],[],[]),([3,2113],[3,7,503],[2113]),([],[],[]),([17,373],[19,647],[17,373]),([],[],[]),([6343],[5,43,59],[6343]),([],[],[]),([3,3,3,5,47],[3,3,29,37],[3,5,47]),([],[],[]),([11,577],[12107],[11,577]),([],[],[]),([7,907],[5,2357],[7,907]),([],[],[]),([3,29,73],[3,3461],[29,73]),([],[],[]),([6353],[3,5,7,11,11],[6353]),([],[],[]),([5,31,41],[5,23,97],[31,41]),([],[],[]),([3,13,163],[3,5,683],[13,163]),([],[],[]),([6359],[3,3,3,3,157],[6359]),([],[],[]),([6361],[12721],[6361]),([],[],[]),([3,3,7,101],[3,3,3,3,3,41],[7,101]),([],[],[]),([5,19,67],[11117],[5,19,67]),([],[],[]),([6367],[7,17,107],[6367]),([],[],[]),([3,11,193],[3,41,83],[11,193]),([],[],[]),([23,277],[23,541],[277]),([],[],[]),([6373],[5,2549],[6373]),([],[],[]),([3,5,5,5,17],[5,5,383],[3,5,17]),([],[],[]),([7,911],[7,19,89],[911]),([],[],[]),([6379],[12757],[6379]),([],[],[]),([3,3,709],[3,3,1181],[709]),([],[],[]),([13,491],[12263],[13,491]),([],[],[]),([5,1277],[11489],[5,1277]),([],[],[]),([3,2129],[29,367],[3,2129]),([],[],[]),([6389],[3,4259],[6389]),([],[],[]),([7,11,83],[11311],[7,11,83]),([],[],[]),([3,2131],[3,53,67],[2131]),([],[],[]),([5,1279],[37,311],[5,1279]),([],[],[]),([6397],[11,1163],[6397]),([],[],[]),([3,3,3,3,79],[3,3,3,3,131],[79])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range6400 (R D : ℕ) (lo : 6400 ≤ R) (hi : R < 6464) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 6400 64 R D [([],[],[]),([37,173],[7,7,257],[37,173]),([],[],[]),([19,337],[12451],[19,337]),([],[],[]),([3,5,7,61],[3,5,619],[7,61]),([],[],[]),([43,149],[13,971],[43,149]),([],[],[]),([13,17,29],[5,2357],[13,17,29]),([],[],[]),([3,2137],[3,3,1187],[2137]),([],[],[]),([11,11,53],[11,1103],[11,53]),([],[],[]),([5,1283],[7,17,97],[5,1283]),([],[],[]),([3,3,23,31],[3,3,1153],[23,31]),([],[],[]),([7,7,131],[7,1697],[7,131]),([],[],[]),([6421],[12841],[6421]),([],[],[]),([3,2141],[7,11,139],[3,2141]),([],[],[]),([5,5,257],[5,2309],[5,257]),([],[],[]),([6427],[12853],[6427]),([],[],[]),([3,2143],[3,3571],[2143]),([],[],[]),([59,109],[5,2539],[59,109]),([],[],[]),([7,919],[11941],[7,919]),([],[],[]),([3,3,5,11,13],[3,3,3,3,5,23],[11,13]),([],[],[]),([41,157],[7,1811],[41,157]),([],[],[]),([47,137],[5,2539],[47,137]),([],[],[]),([3,19,113],[3,3491],[19,113]),([],[],[]),([17,379],[12491],[17,379]),([],[],[]),([5,1289],[11597],[5,1289]),([],[],[]),([3,7,307],[3,3373],[7,307]),([],[],[]),([6449],[3,3,1433],[6449]),([],[],[]),([6451],[7,19,97],[6451]),([],[],[]),([3,3,3,239],[3,3,1193],[3,239]),([],[],[]),([5,1291],[5,23,101],[1291]),([],[],[]),([11,587],[109,113],[11,587]),([],[],[]),([3,2153],[47,229],[3,2153]),([],[],[]),([7,13,71],[7,31,53],[13,71]),([],[],[]),([23,281],[13,971],[23,281])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range6464 (R D : ℕ) (lo : 6464 ≤ R) (hi : R < 6528) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 6464 64 R D [([],[],[]),([3,5,431],[5,7,283],[3,431]),([],[],[]),([29,223],[11,1153],[29,223]),([],[],[]),([6469],[17,761],[6469]),([],[],[]),([3,3,719],[3,3593],[3,719]),([],[],[]),([6473],[3,5,863],[6473]),([],[],[]),([5,5,7,37],[5,17,127],[5,7,37]),([],[],[]),([3,17,127],[3,31,113],[17,127]),([],[],[]),([11,19,31],[7,1697],[11,19,31]),([],[],[]),([6481],[13,997],[6481]),([],[],[]),([3,2161],[3,13,277],[2161]),([],[],[]),([5,1297],[7,1667],[5,1297]),([],[],[]),([13,499],[11,11,103],[13,499]),([],[],[]),([3,3,7,103],[3,3,1129],[7,103]),([],[],[]),([6491],[3,4327],[6491]),([],[],[]),([43,151],[11,1163],[43,151]),([],[],[]),([3,5,433],[3,31,107],[5,433]),([],[],[]),([73,89],[41,313],[73,89]),([],[],[]),([67,97],[5,17,151],[67,97]),([],[],[]),([3,11,197],[17,613],[3,11,197]),([],[],[]),([7,929],[12071],[7,929]),([],[],[]),([5,1301],[5,2341],[1301]),([],[],[]),([3,3,3,241],[3,3,3,401],[241]),([],[],[]),([23,283],[12713],[23,283]),([],[],[]),([17,383],[13,971],[17,383]),([],[],[]),([3,13,167],[3,3499],[13,167]),([],[],[]),([5,1303],[19,617],[5,1303]),([],[],[]),([7,7,7,19],[7,7,241],[7,19]),([],[],[]),([3,41,53],[59,181],[3,41,53]),([],[],[]),([6521],[3,3,3,3,7,23],[6521]),([],[],[]),([11,593],[23,541],[11,593]),([],[],[]),([3,3,5,5,29],[3,5,659],[3,5,29]),([],[],[]),([61,107],[7,7,263],[61,107])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range6528 (R D : ℕ) (lo : 6528 ≤ R) (hi : R < 6592) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 6528 64 R D [([],[],[]),([6529],[11,1187],[6529]),([],[],[]),([3,7,311],[3,3,17,67],[7,311]),([],[],[]),([47,139],[11,1171],[47,139]),([],[],[]),([5,1307],[11,1069],[5,1307]),([],[],[]),([3,2179],[3,3631],[2179]),([],[],[]),([13,503],[17,739],[13,503]),([],[],[]),([31,211],[12841],[31,211]),([],[],[]),([3,3,727],[3,3,7,173],[727]),([],[],[]),([5,7,11,17],[5,31,67],[7,11,17]),([],[],[]),([6547],[13093],[6547]),([],[],[]),([3,37,59],[3,5,5,11,13],[37,59]),([],[],[]),([6551],[3,11,397],[6551]),([],[],[]),([6553],[5,2621],[6553]),([],[],[]),([3,5,19,23],[3,7,463],[5,19,23]),([],[],[]),([79,83],[12953],[79,83]),([],[],[]),([7,937],[5,5,487],[7,937]),([],[],[]),([3,3,3,3,3,3,3,3],[3,3,3,3,3,3,3,5],[3]),([],[],[]),([6563],[3,5,5,5,5,7],[6563]),([],[],[]),([5,13,101],[5,2273],[13,101]),([],[],[]),([3,11,199],[3,11,11,29],[199]),([],[],[]),([6569],[3,29,151],[6569]),([],[],[]),([6571],[17,773],[6571]),([],[],[]),([3,7,313],[3,19,181],[7,313]),([],[],[]),([5,5,263],[5,17,139],[5,263]),([],[],[]),([6577],[7,1879],[6577]),([],[],[]),([3,3,17,43],[3,3,3,3,131],[17,43]),([],[],[]),([6581],[3,41,107],[6581]),([],[],[]),([29,227],[12911],[29,227]),([],[],[]),([3,5,439],[3,3,19,59],[5,439]),([],[],[]),([7,941],[12227],[7,941]),([],[],[]),([11,599],[12569],[11,599]),([],[],[]),([3,13,13,13],[3,3,7,13,13],[13])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range6592 (R D : ℕ) (lo : 6592 ≤ R) (hi : R < 6656) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 6592 64 R D [([],[],[]),([19,347],[12821],[19,347]),([],[],[]),([5,1319],[11867],[5,1319]),([],[],[]),([3,3,733],[3,3,3,11,37],[733]),([],[],[]),([6599],[3,53,83],[6599]),([],[],[]),([7,23,41],[109,109],[7,23,41]),([],[],[]),([3,31,71],[3,13,277],[31,71]),([],[],[]),([5,1321],[5,2377],[1321]),([],[],[]),([6607],[73,181],[6607]),([],[],[]),([3,2203],[3,3671],[2203]),([],[],[]),([11,601],[12611],[11,601]),([],[],[]),([17,389],[12821],[17,389]),([],[],[]),([3,3,3,5,7,7],[3,3,3,3,7,17],[5,7]),([],[],[]),([13,509],[12713],[13,509]),([],[],[]),([6619],[7,31,61],[6619]),([],[],[]),([3,2207],[11,17,59],[3,2207]),([],[],[]),([37,179],[83,157],[37,179]),([],[],[]),([5,5,5,53],[5,5,11,43],[5,53]),([],[],[]),([3,47,47],[47,233],[3,47]),([],[],[]),([7,947],[5,23,107],[7,947]),([],[],[]),([19,349],[5,2579],[19,349]),([],[],[]),([3,3,11,67],[3,3,11,107],[67]),([],[],[]),([5,1327],[11939],[5,1327]),([],[],[]),([6637],[13,1021],[6637]),([],[],[]),([3,2213],[13,23,37],[3,2213]),([],[],[]),([29,229],[5,5,521],[29,229]),([],[],[]),([7,13,73],[11827],[7,13,73]),([],[],[]),([3,5,443],[10181],[3,5,443]),([],[],[]),([17,17,23],[17,743],[17,23]),([],[],[]),([61,109],[19,691],[61,109]),([],[],[]),([3,3,739],[3,3,1231],[739]),([],[],[]),([6653],[3,5,887],[6653]),([],[],[]),([5,11,11,11],[5,11,11,19],[11])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range6656 (R D : ℕ) (lo : 6656 ≤ R) (hi : R < 6720) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 6656 64 R D [([],[],[]),([3,7,317],[3,3,3,3,3,43],[7,317]),([],[],[]),([6659],[3,23,193],[6659]),([],[],[]),([6661],[7,11,173],[6661]),([],[],[]),([3,2221],[3,3701],[2221]),([],[],[]),([5,31,43],[5,2341],[31,43]),([],[],[]),([59,113],[13163],[59,113]),([],[],[]),([3,3,3,13,19],[3,3,3,17,23],[13,19]),([],[],[]),([7,953],[7,29,61],[953]),([],[],[]),([6673],[5,17,157],[6673]),([],[],[]),([3,5,5,89],[5,2039],[3,5,89]),([],[],[]),([11,607],[47,271],[11,607]),([],[],[]),([6679],[19,19,37],[6679]),([],[],[]),([3,17,131],[37,293],[3,17,131]),([],[],[]),([41,163],[13163],[41,163]),([],[],[]),([5,7,191],[5,13,173],[7,191]),([],[],[]),([3,3,743],[3,47,79],[3,743]),([],[],[]),([6689],[3,7,7,7,13],[6689]),([],[],[]),([6691],[13381],[6691]),([],[],[]),([3,23,97],[3,3,1213],[23,97]),([],[],[]),([5,13,103],[67,173],[5,13,103]),([],[],[]),([37,181],[13177],[37,181]),([],[],[]),([3,7,11,29],[3,7,479],[11,29]),([],[],[]),([6701],[3,3,1489],[6701]),([],[],[]),([6703],[5,7,383],[6703]),([],[],[]),([3,3,5,149],[3,13,263],[3,5,149]),([],[],[]),([19,353],[13043],[19,353]),([],[],[]),([6709],[13417],[6709]),([],[],[]),([3,2237],[53,211],[3,2237]),([],[],[]),([7,7,137],[5,5,7,71],[7,137]),([],[],[]),([5,17,79],[23,509],[5,17,79]),([],[],[]),([3,2239],[3,7,13,41],[2239]),([],[],[]),([6719],[3,3,1493],[6719])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range6720 (R D : ℕ) (lo : 6720 ≤ R) (hi : R < 6784) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 6720 64 R D [([],[],[]),([11,13,47],[12241],[11,13,47]),([],[],[]),([3,3,3,3,83],[3,3,3,7,59],[3,83]),([],[],[]),([5,5,269],[5,2417],[5,269]),([],[],[]),([7,31,31],[31,397],[7,31]),([],[],[]),([3,2243],[11213],[3,2243]),([],[],[]),([53,127],[37,359],[53,127]),([],[],[]),([6733],[5,2693],[6733]),([],[],[]),([3,5,449],[17,607],[3,5,449]),([],[],[]),([6737],[3,3,3,499],[6737]),([],[],[]),([23,293],[13163],[23,293]),([],[],[]),([3,3,7,107],[3,3,3,17,23],[7,107]),([],[],[]),([11,613],[19,677],[11,613]),([],[],[]),([5,19,71],[5,2357],[19,71]),([],[],[]),([3,13,173],[3,5,5,5,29],[13,173]),([],[],[]),([17,397],[5,2617],[17,397]),([],[],[]),([43,157],[53,251],[43,157]),([],[],[]),([3,2251],[3,11,11,31],[2251]),([],[],[]),([5,7,193],[11,1033],[5,7,193]),([],[],[]),([29,233],[29,457],[233]),([],[],[]),([3,3,751],[3,3,3,3,139],[751]),([],[],[]),([6761],[3,4507],[6761]),([],[],[]),([6763],[5,5,541],[6763]),([],[],[]),([3,5,11,41],[5,1993],[3,11,41]),([],[],[]),([67,101],[13367],[67,101]),([],[],[]),([7,967],[5,7,359],[967]),([],[],[]),([3,37,61],[3,3697],[37,61]),([],[],[]),([13,521],[7,11,13,13],[521]),([],[],[]),([5,5,271],[5,5,487],[271]),([],[],[]),([3,3,3,251],[3,3,7,179],[3,251]),([],[],[]),([6779],[3,4519],[6779]),([],[],[]),([6781],[71,191],[6781]),([],[],[]),([3,7,17,19],[3,3413],[7,17,19])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range6784 (R D : ℕ) (lo : 6784 ≤ R) (hi : R < 6848) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 6784 64 R D [([],[],[]),([5,23,59],[3,3,1321],[5,23,59]),([],[],[]),([11,617],[11,11,107],[617]),([],[],[]),([3,31,73],[3,7,23,23],[31,73]),([],[],[]),([6791],[3,3,3,503],[6791]),([],[],[]),([6793],[5,11,13,19],[6793]),([],[],[]),([3,3,5,151],[3,3,3,5,7,11],[151]),([],[],[]),([7,971],[11,31,37],[7,971]),([],[],[]),([13,523],[13063],[13,523]),([],[],[]),([3,2267],[7,1619],[3,2267]),([],[],[]),([6803],[3,5,907],[6803]),([],[],[]),([5,1361],[5,31,79],[1361]),([],[],[]),([3,2269],[3,19,199],[2269]),([],[],[]),([11,619],[31,419],[11,619]),([],[],[]),([7,7,139],[7,1801],[7,139]),([],[],[]),([3,3,757],[3,3,13,97],[757]),([],[],[]),([5,29,47],[3,3989],[5,29,47]),([],[],[]),([17,401],[13217],[17,401]),([],[],[]),([3,2273],[11,1033],[3,2273]),([],[],[]),([19,359],[5,7,379],[19,359]),([],[],[]),([6823],[5,2729],[6823]),([],[],[]),([3,5,5,7,13],[3,5,647],[5,7,13]),([],[],[]),([6827],[3,3,37,41],[6827]),([],[],[]),([6829],[7,1951],[6829]),([],[],[]),([3,3,3,11,23],[3,3,11,109],[3,23]),([],[],[]),([6833],[3,5,911],[6833]),([],[],[]),([5,1367],[7,7,251],[5,1367]),([],[],[]),([3,43,53],[3,3,3,5,83],[43,53]),([],[],[]),([7,977],[5,2539],[7,977]),([],[],[]),([6841],[13681],[6841]),([],[],[]),([3,2281],[3,3,7,181],[2281]),([],[],[]),([5,37,37],[7,37,47],[5,37]),([],[],[]),([41,167],[13487],[41,167])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range6848 (R D : ℕ) (lo : 6848 ≤ R) (hi : R < 6912) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 6848 64 R D [([],[],[]),([3,3,761],[3,3803],[3,761]),([],[],[]),([13,17,31],[12611],[13,17,31]),([],[],[]),([7,11,89],[11,1103],[7,89]),([],[],[]),([3,5,457],[3,3,3,389],[5,457]),([],[],[]),([6857],[3,7,653],[6857]),([],[],[]),([19,19,19],[19,19,37],[19]),([],[],[]),([3,2287],[3,37,103],[2287]),([],[],[]),([6863],[3,3,5,5,61],[6863]),([],[],[]),([5,1373],[11,1123],[5,1373]),([],[],[]),([3,3,7,109],[3,3,5,239],[7,109]),([],[],[]),([6869],[3,19,241],[6869]),([],[],[]),([6871],[7,13,151],[6871]),([],[],[]),([3,29,79],[3,3,1249],[29,79]),([],[],[]),([5,5,5,5,11],[5,5,5,5,19],[11]),([],[],[]),([13,23,23],[23,563],[13,23]),([],[],[]),([3,2293],[3,3821],[2293]),([],[],[]),([7,983],[53,241],[7,983]),([],[],[]),([6883],[5,2753],[6883]),([],[],[]),([3,3,3,3,5,17],[3,3,3,383],[3,5,17]),([],[],[]),([71,97],[11,1237],[71,97]),([],[],[]),([83,83],[3,5,11,83],[83]),([],[],[]),([3,2297],[11483],[3,2297]),([],[],[]),([61,113],[13613],[61,113]),([],[],[]),([5,7,197],[7,1657],[5,197]),([],[],[]),([3,11,11,19],[3,7,11,47],[11,19]),([],[],[]),([6899],[3,3,3,7,73],[6899]),([],[],[]),([67,103],[13633],[67,103]),([],[],[]),([3,3,13,59],[3,3,1231],[13,59]),([],[],[]),([5,1381],[5,5,7,71],[1381]),([],[],[]),([6907],[19,727],[6907]),([],[],[]),([3,7,7,47],[3,3,3,3,7,19],[7,47]),([],[],[]),([6911],[3,17,271],[6911])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range6912 (R D : ℕ) (lo : 6912 ≤ R) (hi : R < 6976) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 6912 64 R D [([],[],[]),([31,223],[7,7,277],[31,223]),([],[],[]),([3,5,461],[5,13,163],[3,461]),([],[],[]),([6917],[3,3,29,53],[6917]),([],[],[]),([11,17,37],[31,409],[11,17,37]),([],[],[]),([3,3,769],[3,3,3,7,61],[769]),([],[],[]),([7,23,43],[7,13,137],[23,43]),([],[],[]),([5,5,277],[5,19,131],[5,277]),([],[],[]),([3,2309],[7,17,97],[3,2309]),([],[],[]),([13,13,41],[13,1013],[13,41]),([],[],[]),([29,239],[5,2719],[29,239]),([],[],[]),([3,2311],[3,3851],[2311]),([],[],[]),([5,19,73],[12119],[5,19,73]),([],[],[]),([7,991],[79,163],[7,991]),([],[],[]),([3,3,3,257],[3,3,1283],[3,257]),([],[],[]),([11,631],[13241],[11,631]),([],[],[]),([53,131],[71,193],[53,131]),([],[],[]),([3,5,463],[3,3547],[5,463]),([],[],[]),([6947],[3,11,421],[6947]),([],[],[]),([6949],[13,1069],[6949]),([],[],[]),([3,7,331],[3,3637],[7,331]),([],[],[]),([17,409],[13,17,61],[409]),([],[],[]),([5,13,107],[12043],[5,13,107]),([],[],[]),([3,3,773],[3,3863],[3,773]),([],[],[]),([6959],[3,4639],[6959]),([],[],[]),([6961],[13921],[6961]),([],[],[]),([3,11,211],[3,61,61],[11,211]),([],[],[]),([5,7,199],[11717],[5,7,199]),([],[],[]),([6967],[13933],[6967]),([],[],[]),([3,23,101],[11369],[3,23,101]),([],[],[]),([6971],[3,3,1549],[6971]),([],[],[]),([19,367],[71,191],[19,367]),([],[],[]),([3,3,5,5,31],[3,3,5,5,47],[31])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range6976 (R D : ℕ) (lo : 6976 ≤ R) (hi : R < 7040) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 6976 64 R D [([],[],[]),([6977],[3,4651],[6977]),([],[],[]),([7,997],[5,2591],[7,997]),([],[],[]),([3,13,179],[3,11,11,31],[13,179]),([],[],[]),([6983],[3,5,7,7,19],[6983]),([],[],[]),([5,11,127],[5,5,13,37],[11,127]),([],[],[]),([3,17,137],[17,23,29],[3,137]),([],[],[]),([29,241],[13709],[29,241]),([],[],[]),([6991],[11,31,41],[6991]),([],[],[]),([3,3,3,7,37],[3,3,3,13,31],[7,37]),([],[],[]),([5,1399],[41,307],[5,1399]),([],[],[]),([6997],[7,1999],[6997]),([],[],[]),([3,2333],[107,109],[3,2333]),([],[],[]),([7001],[3,13,359],[7001]),([],[],[]),([47,149],[7,1973],[47,149]),([],[],[]),([3,5,467],[10733],[3,5,467]),([],[],[]),([7,7,11,13],[7,1721],[7,11,13]),([],[],[]),([43,163],[19,727],[43,163]),([],[],[]),([3,3,19,41],[3,3,1259],[19,41]),([],[],[]),([7013],[3,5,5,11,17],[7013]),([],[],[]),([5,23,61],[5,2459],[23,61]),([],[],[]),([3,2339],[11,1063],[3,2339]),([],[],[]),([7019],[3,4679],[7019]),([],[],[]),([7,17,59],[12589],[7,17,59]),([],[],[]),([3,2341],[3,47,83],[2341]),([],[],[]),([5,5,281],[5,5,5,101],[281]),([],[],[]),([7027],[13,23,47],[7027]),([],[],[]),([3,3,11,71],[3,19,197],[3,11,71]),([],[],[]),([79,89],[5,7,397],[79,89]),([],[],[]),([13,541],[13513],[13,541]),([],[],[]),([3,5,7,67],[3,19,179],[5,7,67]),([],[],[]),([31,227],[41,337],[31,227]),([],[],[]),([7039],[7,2011],[7039])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range7040 (R D : ℕ) (lo : 7040 ≤ R) (hi : R < 7104) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 7040 64 R D [([],[],[]),([3,2347],[3,3911],[2347]),([],[],[]),([7043],[3,3,5,313],[7043]),([],[],[]),([5,1409],[7,1811],[5,1409]),([],[],[]),([3,3,3,3,3,29],[3,3,3,3,11,13],[3,29]),([],[],[]),([7,19,53],[5,17,149],[7,19,53]),([],[],[]),([11,641],[13451],[11,641]),([],[],[]),([3,2351],[7,23,73],[3,2351]),([],[],[]),([5,17,83],[3,3,1367],[5,17,83]),([],[],[]),([7057],[11,1283],[7057]),([],[],[]),([3,13,181],[3,3793],[13,181]),([],[],[]),([23,307],[13,1061],[23,307]),([],[],[]),([7,1009],[7,1873],[1009]),([],[],[]),([3,3,5,157],[3,3,1201],[5,157]),([],[],[]),([37,191],[13907],[37,191]),([],[],[]),([7069],[67,211],[7069]),([],[],[]),([3,2357],[11783],[3,2357]),([],[],[]),([11,643],[103,131],[11,643]),([],[],[]),([5,5,283],[5,2543],[5,283]),([],[],[]),([3,7,337],[3,7,23,23],[337]),([],[],[]),([7079],[3,3,11,11,13],[7079]),([],[],[]),([73,97],[7,1999],[73,97]),([],[],[]),([3,3,787],[3,3,3,19,23],[787]),([],[],[]),([5,13,109],[12269],[5,13,109]),([],[],[]),([19,373],[7,11,179],[19,373]),([],[],[]),([3,17,139],[3,5,13,59],[17,139]),([],[],[]),([7,1013],[13163],[7,1013]),([],[],[]),([41,173],[89,157],[41,173]),([],[],[]),([3,5,11,43],[3,5,17,41],[11,43]),([],[],[]),([47,151],[13997],[47,151]),([],[],[]),([31,229],[53,263],[31,229]),([],[],[]),([3,3,3,263],[3,3,13,101],[3,263]),([],[],[]),([7103],[3,5,947],[7103])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range7104 (R D : ℕ) (lo : 7104 ≤ R) (hi : R < 7168) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 7104 64 R D [([],[],[]),([5,7,7,29],[7,7,241],[5,29]),([],[],[]),([3,23,103],[3,5,773],[23,103]),([],[],[]),([7109],[3,7,677],[7109]),([],[],[]),([13,547],[13,1051],[547]),([],[],[]),([3,2371],[3,3,3,439],[2371]),([],[],[]),([5,1423],[7,31,59],[5,1423]),([],[],[]),([11,647],[13577],[11,647]),([],[],[]),([3,3,7,113],[3,3,3,7,59],[113]),([],[],[]),([7121],[3,47,101],[7121]),([],[],[]),([17,419],[7,1973],[17,419]),([],[],[]),([3,5,5,5,19],[3,5,5,11,13],[5,19]),([],[],[]),([7127],[3,4751],[7127]),([],[],[]),([7129],[53,269],[7129]),([],[],[]),([3,2377],[3,17,233],[2377]),([],[],[]),([7,1019],[13241],[7,1019]),([],[],[]),([5,1427],[37,347],[5,1427]),([],[],[]),([3,3,13,61],[3,3,19,67],[13,61]),([],[],[]),([11,11,59],[11,1229],[11,59]),([],[],[]),([37,193],[13,23,47],[37,193]),([],[],[]),([3,2381],[11903],[3,2381]),([],[],[]),([5,1429],[13,23,43],[5,1429]),([],[],[]),([7,1021],[13267],[7,1021]),([],[],[]),([3,2383],[3,11,19,19],[2383]),([],[],[]),([7151],[3,3,7,227],[7151]),([],[],[]),([23,311],[89,157],[23,311]),([],[],[]),([3,3,3,5,53],[3,3,7,173],[3,5,53]),([],[],[]),([17,421],[13877],[17,421]),([],[],[]),([7159],[103,139],[7159]),([],[],[]),([3,7,11,31],[3,17,211],[7,11,31]),([],[],[]),([13,19,29],[11,1201],[13,19,29]),([],[],[]),([5,1433],[12893],[5,1433]),([],[],[]),([3,2389],[3,3,1327],[2389])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range7168 (R D : ℕ) (lo : 7168 ≤ R) (hi : R < 7232) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 7168 64 R D [([],[],[]),([67,107],[5,2833],[67,107]),([],[],[]),([71,101],[37,383],[71,101]),([],[],[]),([3,3,797],[3,7,569],[3,797]),([],[],[]),([5,5,7,41],[5,5,479],[7,41]),([],[],[]),([7177],[31,463],[7177]),([],[],[]),([3,2393],[7,1709],[3,2393]),([],[],[]),([43,167],[14153],[43,167]),([],[],[]),([11,653],[71,193],[11,653]),([],[],[]),([3,5,479],[101,109],[3,5,479]),([],[],[]),([7187],[3,3,1597],[7187]),([],[],[]),([7,13,79],[5,13,197],[7,79]),([],[],[]),([3,3,17,47],[3,53,73],[3,17,47]),([],[],[]),([7193],[3,5,7,137],[7193]),([],[],[]),([5,1439],[11,11,107],[5,1439]),([],[],[]),([3,2399],[67,179],[3,2399]),([],[],[]),([23,313],[7,7,7,41],[23,313]),([],[],[]),([19,379],[5,2801],[19,379]),([],[],[]),([3,7,7,7,7],[3,7,7,7,11],[7]),([],[],[]),([5,11,131],[3,5,827],[11,131]),([],[],[]),([7207],[7,29,71],[7207]),([],[],[]),([3,3,3,3,89],[3,3,3,443],[3,89]),([],[],[]),([7211],[3,11,19,23],[7211]),([],[],[]),([7213],[5,5,577],[7213]),([],[],[]),([3,5,13,37],[3,3557],[5,13,37]),([],[],[]),([7,1031],[13397],[7,1031]),([],[],[]),([7219],[14437],[7219]),([],[],[]),([3,29,83],[11813],[3,29,83]),([],[],[]),([31,233],[13,1091],[31,233]),([],[],[]),([5,5,17,17],[5,17,149],[5,17]),([],[],[]),([3,3,11,73],[3,3,1283],[11,73]),([],[],[]),([7229],[3,61,79],[7229]),([],[],[]),([7,1033],[31,433],[7,1033])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range7232 (R D : ℕ) (lo : 7232 ≤ R) (hi : R < 7296) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 7232 64 R D [([],[],[]),([3,2411],[17,709],[3,2411]),([],[],[]),([5,1447],[47,277],[5,1447]),([],[],[]),([7237],[41,353],[7237]),([],[],[]),([3,19,127],[3,5,5,157],[19,127]),([],[],[]),([13,557],[13913],[13,557]),([],[],[]),([7243],[5,2897],[7243]),([],[],[]),([3,3,5,7,23],[3,3,13,89],[5,7,23]),([],[],[]),([7247],[3,4831],[7247]),([],[],[]),([11,659],[13829],[11,659]),([],[],[]),([3,2417],[43,281],[3,2417]),([],[],[]),([7253],[3,5,967],[7253]),([],[],[]),([5,1451],[5,7,373],[1451]),([],[],[]),([3,41,59],[11897],[3,41,59]),([],[],[]),([7,17,61],[47,277],[7,17,61]),([],[],[]),([53,137],[11,1303],[53,137]),([],[],[]),([3,3,3,269],[3,3,17,79],[3,269]),([],[],[]),([5,1453],[17,769],[5,1453]),([],[],[]),([13,13,43],[13,1063],[13,43]),([],[],[]),([3,2423],[12113],[3,2423]),([],[],[]),([11,661],[11,13,97],[661]),([],[],[]),([7,1039],[23,587],[7,1039]),([],[],[]),([3,5,5,97],[3,3,5,13,19],[5,97]),([],[],[]),([19,383],[14153],[19,383]),([],[],[]),([29,251],[109,131],[29,251]),([],[],[]),([3,3,809],[3,13,311],[3,809]),([],[],[]),([7283],[3,5,971],[7283]),([],[],[]),([5,31,47],[5,13,197],[31,47]),([],[],[]),([3,7,347],[3,3,31,41],[7,347]),([],[],[]),([37,197],[5,19,151],[37,197]),([],[],[]),([23,317],[14243],[23,317]),([],[],[]),([3,11,13,17],[3,3,1237],[11,13,17]),([],[],[]),([5,1459],[13127],[5,1459])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range7296 (R D : ℕ) (lo : 7296 ≤ R) (hi : R < 7360) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 7296 64 R D [([],[],[]),([7297],[14593],[7297]),([],[],[]),([3,3,811],[3,3,7,193],[811]),([],[],[]),([7,7,149],[7,1931],[7,149]),([],[],[]),([67,109],[14431],[67,109]),([],[],[]),([3,5,487],[3,7,13,41],[5,487]),([],[],[]),([7307],[3,4871],[7307]),([],[],[]),([7309],[47,311],[7309]),([],[],[]),([3,2437],[3,31,131],[2437]),([],[],[]),([71,103],[97,149],[71,103]),([],[],[]),([5,7,11,19],[5,13,179],[7,11,19]),([],[],[]),([3,3,3,271],[3,3,3,11,41],[271]),([],[],[]),([13,563],[7,7,7,41],[13,563]),([],[],[]),([7321],[11,11,11,11],[7321]),([],[],[]),([3,2441],[12203],[3,2441]),([],[],[]),([5,5,293],[5,2633],[5,293]),([],[],[]),([17,431],[14207],[17,431]),([],[],[]),([3,7,349],[3,5,13,59],[7,349]),([],[],[]),([7331],[3,3,3,3,181],[7331]),([],[],[]),([7333],[5,7,419],[7333]),([],[],[]),([3,3,5,163],[3,3,29,43],[5,163]),([],[],[]),([11,23,29],[3,11,409],[23,29]),([],[],[]),([41,179],[19,761],[41,179]),([],[],[]),([3,2447],[13,941],[3,2447]),([],[],[]),([7,1049],[43,317],[7,1049]),([],[],[]),([5,13,113],[12721],[5,13,113]),([],[],[]),([3,31,79],[3,19,211],[31,79]),([],[],[]),([7349],[3,3,23,71],[7349]),([],[],[]),([7351],[61,241],[7351]),([],[],[]),([3,3,19,43],[3,3,1321],[19,43]),([],[],[]),([5,1471],[5,2647],[1471]),([],[],[]),([7,1051],[7,1951],[1051]),([],[],[]),([3,11,223],[3,3,3,19,23],[11,223])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range7360 (R D : ℕ) (lo : 7360 ≤ R) (hi : R < 7424) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 7360 64 R D [([],[],[]),([17,433],[7,2039],[17,433]),([],[],[]),([37,199],[43,337],[37,199]),([],[],[]),([3,5,491],[5,37,61],[3,491]),([],[],[]),([53,139],[14543],[53,139]),([],[],[]),([7369],[14737],[7369]),([],[],[]),([3,3,3,3,7,13],[3,3,3,3,139],[7,13]),([],[],[]),([73,101],[13,19,59],[73,101]),([],[],[]),([5,5,5,59],[5,5,17,31],[5,59]),([],[],[]),([3,2459],[19,647],[3,2459]),([],[],[]),([47,157],[5,41,71],[47,157]),([],[],[]),([11,11,61],[11,31,41],[11,61]),([],[],[]),([3,23,107],[7,1721],[3,23,107]),([],[],[]),([5,7,211],[5,5,7,71],[211]),([],[],[]),([83,89],[17,859],[83,89]),([],[],[]),([3,3,821],[3,11,373],[3,821]),([],[],[]),([19,389],[5,5,5,5,23],[19,389]),([],[],[]),([7393],[5,2957],[7393]),([],[],[]),([3,5,17,29],[10979],[3,5,17,29]),([],[],[]),([13,569],[61,233],[13,569]),([],[],[]),([7,7,151],[7,19,103],[7,151]),([],[],[]),([3,2467],[3,4111],[2467]),([],[],[]),([11,673],[29,487],[11,673]),([],[],[]),([5,1481],[5,5,13,41],[1481]),([],[],[]),([3,3,823],[3,3,3,457],[823]),([],[],[]),([31,239],[14549],[31,239]),([],[],[]),([7411],[14821],[7411]),([],[],[]),([3,7,353],[3,3,3,431],[7,353]),([],[],[]),([5,1483],[11,1213],[5,1483]),([],[],[]),([7417],[7,13,163],[7417]),([],[],[]),([3,2473],[3,13,317],[2473]),([],[],[]),([41,181],[14621],[41,181]),([],[],[]),([13,571],[17,839],[13,571])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range7424 (R D : ℕ) (lo : 7424 ≤ R) (hi : R < 7488) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 7424 64 R D [([],[],[]),([3,3,3,5,5,11],[3,3,5,5,7,7],[3,11]),([],[],[]),([7,1061],[17,811],[7,1061]),([],[],[]),([17,19,23],[5,2753],[17,19,23]),([],[],[]),([3,2477],[7,29,61],[3,2477]),([],[],[]),([7433],[3,5,991],[7433]),([],[],[]),([5,1487],[17,787],[5,1487]),([],[],[]),([3,37,67],[3,17,239],[37,67]),([],[],[]),([43,173],[11,31,43],[173]),([],[],[]),([7,1063],[19,727],[7,1063]),([],[],[]),([3,3,827],[3,4133],[3,827]),([],[],[]),([5,1489],[13397],[5,1489]),([],[],[]),([11,677],[14207],[11,677]),([],[],[]),([3,13,191],[3,4003],[13,191]),([],[],[]),([7451],[3,4967],[7451]),([],[],[]),([29,257],[14621],[29,257]),([],[],[]),([3,5,7,71],[3,5,7,103],[71]),([],[],[]),([7457],[3,3,1657],[7457]),([],[],[]),([7459],[7,2131],[7459]),([],[],[]),([3,3,829],[3,3,1381],[829]),([],[],[]),([17,439],[29,499],[17,439]),([],[],[]),([5,1493],[7,19,101],[5,1493]),([],[],[]),([3,19,131],[3,4049],[19,131]),([],[],[]),([7,11,97],[13229],[7,11,97]),([],[],[]),([31,241],[17,863],[31,241]),([],[],[]),([3,47,53],[7,17,103],[3,47,53]),([],[],[]),([5,5,13,23],[5,2551],[5,13,23]),([],[],[]),([7477],[19,787],[7477]),([],[],[]),([3,3,3,277],[3,3,3,461],[277]),([],[],[]),([7481],[3,4987],[7481]),([],[],[]),([7,1069],[29,479],[7,1069]),([],[],[]),([3,5,499],[3,3823],[5,499]),([],[],[]),([7487],[3,7,23,31],[7487])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range7488 (R D : ℕ) (lo : 7488 ≤ R) (hi : R < 7552) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 7488 64 R D [([],[],[]),([7489],[17,881],[7489]),([],[],[]),([3,11,227],[12011],[3,11,227]),([],[],[]),([59,127],[19,19,41],[59,127]),([],[],[]),([5,1499],[13487],[5,1499]),([],[],[]),([3,3,7,7,17],[3,3,3,7,61],[7,17]),([],[],[]),([7499],[3,4999],[7499]),([],[],[]),([13,577],[7,29,71],[13,577]),([],[],[]),([3,41,61],[3,3,1367],[41,61]),([],[],[]),([5,19,79],[13121],[5,19,79]),([],[],[]),([7507],[15013],[7507]),([],[],[]),([3,2503],[3,43,97],[2503]),([],[],[]),([7,29,37],[7,13,149],[29,37]),([],[],[]),([11,683],[11,1303],[683]),([],[],[]),([3,3,5,167],[3,3833],[3,5,167]),([],[],[]),([7517],[3,5011],[7517]),([],[],[]),([73,103],[89,167],[73,103]),([],[],[]),([3,23,109],[3,4091],[23,109]),([],[],[]),([7523],[3,5,17,59],[7523]),([],[],[]),([5,5,7,43],[5,7,359],[5,43]),([],[],[]),([3,13,193],[3,5,809],[13,193]),([],[],[]),([7529],[3,3,7,239],[7529]),([],[],[]),([17,443],[17,859],[443]),([],[],[]),([3,3,3,3,3,31],[3,3,3,3,3,3,17],[31]),([],[],[]),([5,11,137],[3,5,5,173],[11,137]),([],[],[]),([7537],[15073],[7537]),([],[],[]),([3,7,359],[3,3,5,263],[7,359]),([],[],[]),([7541],[3,11,457],[7541]),([],[],[]),([19,397],[17,863],[19,397]),([],[],[]),([3,5,503],[11,1051],[3,5,503]),([],[],[]),([7547],[3,3,3,13,43],[7547]),([],[],[]),([7549],[31,487],[7549]),([],[],[]),([3,3,839],[3,7,599],[3,839])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range7552 (R D : ℕ) (lo : 7552 ≤ R) (hi : R < 7616) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 7552 64 R D [([],[],[]),([7,13,83],[13457],[7,13,83]),([],[],[]),([5,1511],[5,2719],[1511]),([],[],[]),([3,11,229],[3,7,577],[11,229]),([],[],[]),([7559],[3,5039],[7559]),([],[],[]),([7561],[15121],[7561]),([],[],[]),([3,2521],[3,4201],[2521]),([],[],[]),([5,17,89],[3,53,83],[5,17,89]),([],[],[]),([7,23,47],[23,593],[7,47]),([],[],[]),([3,3,29,29],[3,11,13,29],[3,29]),([],[],[]),([67,113],[13,1151],[67,113]),([],[],[]),([7573],[5,13,233],[7573]),([],[],[]),([3,5,5,101],[5,5,463],[3,101]),([],[],[]),([7577],[3,5051],[7577]),([],[],[]),([11,13,53],[13,1063],[11,53]),([],[],[]),([3,7,19,19],[3,5,19,41],[7,19]),([],[],[]),([7583],[3,3,5,337],[7583]),([],[],[]),([5,37,41],[5,17,157],[37,41]),([],[],[]),([3,3,3,281],[3,3,23,61],[3,281]),([],[],[]),([7589],[3,5059],[7589]),([],[],[]),([7591],[17,19,47],[7591]),([],[],[]),([3,2531],[12653],[3,2531]),([],[],[]),([5,7,7,31],[5,7,19,19],[7,31]),([],[],[]),([71,107],[15017],[71,107]),([],[],[]),([3,17,149],[5,2467],[3,17,149]),([],[],[]),([11,691],[17,853],[11,691]),([],[],[]),([7603],[5,3041],[7603]),([],[],[]),([3,3,5,13,13],[3,3,13,97],[5,13]),([],[],[]),([7607],[3,11,461],[7607]),([],[],[]),([7,1087],[5,5,5,113],[7,1087]),([],[],[]),([3,43,59],[3,3,19,73],[43,59]),([],[],[]),([23,331],[107,139],[23,331]),([],[],[]),([5,1523],[71,193],[5,1523])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range7616 (R D : ℕ) (lo : 7616 ≤ R) (hi : R < 7680) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 7616 64 R D [([],[],[]),([3,2539],[3,4231],[2539]),([],[],[]),([19,401],[7,29,73],[19,401]),([],[],[]),([7621],[15241],[7621]),([],[],[]),([3,3,7,11,11],[3,3,3,3,11,13],[7,11]),([],[],[]),([5,5,5,61],[5,5,5,109],[61]),([],[],[]),([29,263],[13,1151],[29,263]),([],[],[]),([3,2543],[12713],[3,2543]),([],[],[]),([13,587],[11,31,43],[13,587]),([],[],[]),([17,449],[19,19,41],[17,449]),([],[],[]),([3,5,509],[11699],[3,5,509]),([],[],[]),([7,1091],[14177],[7,1091]),([],[],[]),([7639],[15277],[7639]),([],[],[]),([3,3,3,283],[3,3,3,3,157],[283]),([],[],[]),([7643],[3,5,1019],[7643]),([],[],[]),([5,11,139],[5,2633],[11,139]),([],[],[]),([3,2549],[12743],[3,2549]),([],[],[]),([7649],[3,5099],[7649]),([],[],[]),([7,1093],[7,2029],[1093]),([],[],[]),([3,2551],[3,3,13,109],[2551]),([],[],[]),([5,1531],[5,5,19,29],[1531]),([],[],[]),([13,19,31],[67,211],[13,19,31]),([],[],[]),([3,3,23,37],[3,3,7,197],[23,37]),([],[],[]),([47,163],[7,17,127],[47,163]),([],[],[]),([79,97],[109,139],[79,97]),([],[],[]),([3,5,7,73],[3,11,337],[5,7,73]),([],[],[]),([11,17,41],[3,3,3,521],[11,17,41]),([],[],[]),([7669],[7,7,313],[7669]),([],[],[]),([3,2557],[3,4261],[2557]),([],[],[]),([7673],[3,3,5,11,31],[7673]),([],[],[]),([5,5,307],[5,31,89],[5,307]),([],[],[]),([3,3,853],[3,3,7,7,29],[853]),([],[],[]),([7,1097],[5,2851],[7,1097])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range7680 (R D : ℕ) (lo : 7680 ≤ R) (hi : R < 7744) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 7680 64 R D [([],[],[]),([7681],[15361],[7681]),([],[],[]),([3,13,197],[3,4129],[13,197]),([],[],[]),([5,29,53],[3,3,19,79],[5,29,53]),([],[],[]),([7687],[15373],[7687]),([],[],[]),([3,11,233],[12329],[3,11,233]),([],[],[]),([7691],[3,3,1709],[7691]),([],[],[]),([7,7,157],[5,7,11,37],[7,157]),([],[],[]),([3,3,3,3,5,19],[3,3,3,3,11,13],[5,19]),([],[],[]),([43,179],[15173],[43,179]),([],[],[]),([7699],[89,173],[7699]),([],[],[]),([3,17,151],[3,3,3,463],[17,151]),([],[],[]),([7703],[3,5,13,79],[7703]),([],[],[]),([5,23,67],[13513],[5,23,67]),([],[],[]),([3,7,367],[3,37,109],[7,367]),([],[],[]),([13,593],[14813],[13,593]),([],[],[]),([11,701],[47,313],[11,701]),([],[],[]),([3,3,857],[3,4283],[3,857]),([],[],[]),([5,1543],[13883],[5,1543]),([],[],[]),([7717],[11,23,61],[7717]),([],[],[]),([3,31,83],[3,11,383],[31,83]),([],[],[]),([7,1103],[11,1303],[7,1103]),([],[],[]),([7723],[5,3089],[7723]),([],[],[]),([3,5,5,103],[3,5,787],[5,103]),([],[],[]),([7727],[3,3,17,101],[7727]),([],[],[]),([59,131],[15269],[59,131]),([],[],[]),([3,3,859],[3,3,3,3,3,53],[859]),([],[],[]),([11,19,37],[61,233],[11,19,37]),([],[],[]),([5,7,13,17],[12343],[5,7,13,17]),([],[],[]),([3,2579],[12893],[3,2579]),([],[],[]),([71,109],[15299],[71,109]),([],[],[]),([7741],[113,137],[7741]),([],[],[]),([3,29,89],[12671],[3,29,89])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range7744 (R D : ℕ) (lo : 7744 ≤ R) (hi : R < 7808) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 7744 64 R D [([],[],[]),([5,1549],[7,11,181],[5,1549]),([],[],[]),([61,127],[15307],[61,127]),([],[],[]),([3,3,3,7,41],[3,3,3,3,149],[7,41]),([],[],[]),([23,337],[19,797],[23,337]),([],[],[]),([7753],[5,7,443],[7753]),([],[],[]),([3,5,11,47],[5,2287],[3,11,47]),([],[],[]),([7757],[3,5171],[7757]),([],[],[]),([7759],[59,263],[7759]),([],[],[]),([3,13,199],[3,43,97],[13,199]),([],[],[]),([7,1109],[14411],[7,1109]),([],[],[]),([5,1553],[89,157],[5,1553]),([],[],[]),([3,3,863],[3,19,227],[3,863]),([],[],[]),([17,457],[5,23,131],[17,457]),([],[],[]),([19,409],[5,3023],[19,409]),([],[],[]),([3,2591],[12953],[3,2591]),([],[],[]),([5,5,311],[5,5,13,43],[311]),([],[],[]),([7,11,101],[23,599],[7,11,101]),([],[],[]),([3,2593],[3,29,149],[2593]),([],[],[]),([31,251],[7,37,59],[31,251]),([],[],[]),([43,181],[67,229],[43,181]),([],[],[]),([3,3,5,173],[3,11,19,19],[3,5,173]),([],[],[]),([13,599],[13,1151],[599]),([],[],[]),([7789],[37,421],[7789]),([],[],[]),([3,7,7,53],[3,3,7,193],[7,53]),([],[],[]),([7793],[3,5,1039],[7793]),([],[],[]),([5,1559],[13,13,83],[5,1559]),([],[],[]),([3,23,113],[5,5,509],[3,23,113]),([],[],[]),([11,709],[14879],[11,709]),([],[],[]),([29,269],[5,3061],[29,269]),([],[],[]),([3,3,3,17,17],[3,3,17,83],[3,17]),([],[],[]),([5,7,223],[23,571],[5,7,223]),([],[],[]),([37,211],[11,11,127],[37,211])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range7808 (R D : ℕ) (lo : 7808 ≤ R) (hi : R < 7872) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 7808 64 R D [([],[],[]),([3,19,137],[3,5,7,11,11],[19,137]),([],[],[]),([73,107],[15443],[73,107]),([],[],[]),([13,601],[15013],[13,601]),([],[],[]),([3,5,521],[5,5,479],[3,521]),([],[],[]),([7817],[3,3,3,3,193],[7817]),([],[],[]),([7,1117],[5,2903],[7,1117]),([],[],[]),([3,3,11,79],[3,3,3,463],[11,79]),([],[],[]),([7823],[3,5,7,149],[7823]),([],[],[]),([5,5,313],[5,29,97],[5,313]),([],[],[]),([3,2609],[13043],[3,2609]),([],[],[]),([7829],[3,17,307],[7829]),([],[],[]),([41,191],[13,1187],[41,191]),([],[],[]),([3,7,373],[3,4099],[7,373]),([],[],[]),([5,1567],[23,613],[5,1567]),([],[],[]),([17,461],[7,13,167],[17,461]),([],[],[]),([3,3,13,67],[3,3,1399],[13,67]),([],[],[]),([7841],[3,5227],[7841]),([],[],[]),([11,23,31],[11,13,101],[23,31]),([],[],[]),([3,5,523],[3,4007],[5,523]),([],[],[]),([7,19,59],[103,137],[7,19,59]),([],[],[]),([47,167],[5,19,163],[47,167]),([],[],[]),([3,2617],[3,7,7,89],[2617]),([],[],[]),([7853],[3,3,5,349],[7853]),([],[],[]),([5,1571],[5,11,257],[1571]),([],[],[]),([3,3,3,3,97],[3,3,3,3,7,23],[97]),([],[],[]),([29,271],[17,907],[29,271]),([],[],[]),([7,1123],[14593],[7,1123]),([],[],[]),([3,2621],[13103],[3,2621]),([],[],[]),([5,11,11,13],[5,11,239],[11,13]),([],[],[]),([7867],[15733],[7867]),([],[],[]),([3,43,61],[3,13,331],[43,61]),([],[],[]),([17,463],[15263],[17,463])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range7872 (R D : ℕ) (lo : 7872 ≤ R) (hi : R < 7936) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 7872 64 R D [([],[],[]),([7873],[5,47,67],[7873]),([],[],[]),([3,3,5,5,5,7],[3,3,3,5,5,17],[5,7]),([],[],[]),([7877],[3,59,89],[7877]),([],[],[]),([7879],[7,2251],[7879]),([],[],[]),([3,37,71],[3,59,73],[37,71]),([],[],[]),([7883],[3,5,1051],[7883]),([],[],[]),([5,19,83],[13789],[5,19,83]),([],[],[]),([3,11,239],[12647],[3,11,239]),([],[],[]),([7,7,7,23],[7,7,293],[7,23]),([],[],[]),([13,607],[59,257],[13,607]),([],[],[]),([3,3,877],[3,3,3,487],[877]),([],[],[]),([5,1579],[14207],[5,1579]),([],[],[]),([53,149],[31,503],[53,149]),([],[],[]),([3,2633],[13163],[3,2633]),([],[],[]),([7901],[3,23,229],[7901]),([],[],[]),([7,1129],[17,863],[7,1129]),([],[],[]),([3,5,17,31],[3,3,3,3,5,29],[17,31]),([],[],[]),([7907],[3,3,7,251],[7907]),([],[],[]),([11,719],[79,191],[11,719]),([],[],[]),([3,3,3,293],[3,3,7,11,19],[3,293]),([],[],[]),([41,193],[31,503],[41,193]),([],[],[]),([5,1583],[14243],[5,1583]),([],[],[]),([3,7,13,29],[3,7,569],[13,29]),([],[],[]),([7919],[3,5279],[7919]),([],[],[]),([89,89],[3,59,89],[89]),([],[],[]),([3,19,139],[3,4297],[19,139]),([],[],[]),([5,5,317],[5,7,11,37],[5,317]),([],[],[]),([7927],[83,191],[7927]),([],[],[]),([3,3,881],[3,7,17,37],[3,881]),([],[],[]),([7,11,103],[14051],[7,11,103]),([],[],[]),([7933],[5,19,167],[7933]),([],[],[]),([3,5,23,23],[23,521],[3,5,23])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range7936 (R D : ℕ) (lo : 7936 ≤ R) (hi : R < 8000) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 7936 64 R D [([],[],[]),([7937],[3,11,13,37],[7937]),([],[],[]),([17,467],[5,3079],[17,467]),([],[],[]),([3,2647],[3,11,401],[2647]),([],[],[]),([13,13,47],[13,1163],[13,47]),([],[],[]),([5,7,227],[29,461],[5,7,227]),([],[],[]),([3,3,883],[3,3,1471],[883]),([],[],[]),([7949],[3,7,757],[7949]),([],[],[]),([7951],[15901],[7951]),([],[],[]),([3,11,241],[3,3,13,109],[11,241]),([],[],[]),([5,37,43],[11,19,67],[5,37,43]),([],[],[]),([73,109],[15733],[73,109]),([],[],[]),([3,7,379],[3,5,7,7,17],[379]),([],[],[]),([19,419],[5,19,163],[419]),([],[],[]),([7963],[5,5,7,7,13],[7963]),([],[],[]),([3,3,3,5,59],[3,3,19,71],[3,5,59]),([],[],[]),([31,257],[15647],[31,257]),([],[],[]),([13,613],[15313],[13,613]),([],[],[]),([3,2657],[37,359],[3,2657]),([],[],[]),([7,17,67],[41,349],[7,17,67]),([],[],[]),([5,5,11,29],[3,5,5,181],[11,29]),([],[],[]),([3,2659],[3,3,7,211],[2659]),([],[],[]),([79,101],[31,509],[79,101]),([],[],[]),([23,347],[31,503],[23,347]),([],[],[]),([3,3,887],[3,11,13,31],[3,887]),([],[],[]),([5,1597],[14369],[5,1597]),([],[],[]),([7,7,163],[7,2113],[7,163]),([],[],[]),([3,2663],[13313],[3,2663]),([],[],[]),([61,131],[15791],[61,131]),([],[],[]),([7993],[5,23,139],[7993]),([],[],[]),([3,5,13,41],[3,3,5,263],[13,41]),([],[],[]),([11,727],[11,19,73],[727]),([],[],[]),([19,421],[15559],[19,421])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range8000 (R D : ℕ) (lo : 8000 ≤ R) (hi : R < 8064) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 8000 64 R D [([],[],[]),([3,3,7,127],[3,3,7,199],[127]),([],[],[]),([53,151],[15803],[53,151]),([],[],[]),([5,1601],[5,43,67],[1601]),([],[],[]),([3,17,157],[3,7,619],[17,157]),([],[],[]),([8009],[3,19,281],[8009]),([],[],[]),([8011],[37,433],[8011]),([],[],[]),([3,2671],[3,4451],[2671]),([],[],[]),([5,7,229],[13487],[5,7,229]),([],[],[]),([8017],[16033],[8017]),([],[],[]),([3,3,3,3,3,3,11],[3,3,3,3,3,53],[3,11]),([],[],[]),([13,617],[15413],[13,617]),([],[],[]),([71,113],[29,547],[71,113]),([],[],[]),([3,5,5,107],[5,11,223],[3,5,107]),([],[],[]),([23,349],[15683],[23,349]),([],[],[]),([7,31,37],[11,1319],[7,31,37]),([],[],[]),([3,2677],[3,3,1487],[2677]),([],[],[]),([29,277],[15761],[29,277]),([],[],[]),([5,1607],[19,761],[5,1607]),([],[],[]),([3,3,19,47],[3,3,5,17,17],[19,47]),([],[],[]),([8039],[3,23,233],[8039]),([],[],[]),([11,17,43],[29,509],[11,17,43]),([],[],[]),([3,7,383],[3,3,23,61],[7,383]),([],[],[]),([5,1609],[31,467],[5,1609]),([],[],[]),([13,619],[7,47,47],[13,619]),([],[],[]),([3,2683],[3,17,263],[2683]),([],[],[]),([83,97],[15923],[83,97]),([],[],[]),([8053],[5,3221],[8053]),([],[],[]),([3,3,5,179],[3,7,587],[3,5,179]),([],[],[]),([7,1151],[14957],[7,1151]),([],[],[]),([8059],[71,227],[8059]),([],[],[]),([3,2687],[7,19,101],[3,2687]),([],[],[]),([11,733],[15383],[11,733])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range8064 (R D : ℕ) (lo : 8064 ≤ R) (hi : R < 8128) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 8064 64 R D [([],[],[]),([5,1613],[23,631],[5,1613]),([],[],[]),([3,2689],[3,4481],[2689]),([],[],[]),([8069],[3,3,11,163],[8069]),([],[],[]),([7,1153],[14983],[7,1153]),([],[],[]),([3,3,3,13,23],[3,3,3,5,5,19],[13,23]),([],[],[]),([5,5,17,19],[5,2767],[5,17,19]),([],[],[]),([41,197],[11,1447],[41,197]),([],[],[]),([3,2693],[13463],[3,2693]),([],[],[]),([8081],[3,5387],[8081]),([],[],[]),([59,137],[15971],[59,137]),([],[],[]),([3,5,7,7,11],[3,5,7,109],[7,11]),([],[],[]),([8087],[3,3,3,599],[8087]),([],[],[]),([8089],[7,2311],[8089]),([],[],[]),([3,3,29,31],[3,3,1459],[29,31]),([],[],[]),([8093],[3,5,13,83],[8093]),([],[],[]),([5,1619],[7,2081],[5,1619]),([],[],[]),([3,2699],[103,131],[3,2699]),([],[],[]),([7,13,89],[5,2887],[7,13,89]),([],[],[]),([8101],[17,953],[8101]),([],[],[]),([3,37,73],[3,43,103],[37,73]),([],[],[]),([5,1621],[5,2917],[1621]),([],[],[]),([11,11,67],[11,11,127],[67]),([],[],[]),([3,3,17,53],[3,11,397],[3,17,53]),([],[],[]),([8111],[3,5407],[8111]),([],[],[]),([7,19,61],[14593],[7,19,61]),([],[],[]),([3,5,541],[3,5,829],[541]),([],[],[]),([8117],[3,7,773],[8117]),([],[],[]),([23,353],[29,547],[23,353]),([],[],[]),([3,2707],[3,13,347],[2707]),([],[],[]),([8123],[3,3,5,19,19],[8123]),([],[],[]),([5,5,5,5,13],[5,5,5,113],[5,13]),([],[],[]),([3,3,3,7,43],[3,3,3,7,67],[43])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range8128 (R D : ℕ) (lo : 8128 ≤ R) (hi : R < 8192) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 8128 64 R D [([],[],[]),([11,739],[13,1193],[11,739]),([],[],[]),([47,173],[61,263],[47,173]),([],[],[]),([3,2711],[13553],[3,2711]),([],[],[]),([5,1627],[14639],[5,1627]),([],[],[]),([79,103],[7,11,11,19],[79,103]),([],[],[]),([3,2713],[3,3,11,137],[2713]),([],[],[]),([7,1163],[7,17,127],[1163]),([],[],[]),([17,479],[15791],[17,479]),([],[],[]),([3,3,5,181],[3,3,5,277],[181]),([],[],[]),([8147],[3,5431],[8147]),([],[],[]),([29,281],[59,271],[29,281]),([],[],[]),([3,11,13,19],[3,4157],[11,13,19]),([],[],[]),([31,263],[67,239],[31,263]),([],[],[]),([5,7,233],[13723],[5,7,233]),([],[],[]),([3,2719],[3,23,197],[2719]),([],[],[]),([41,199],[7,2297],[41,199]),([],[],[]),([8161],[19,859],[8161]),([],[],[]),([3,3,907],[3,3,1511],[907]),([],[],[]),([5,23,71],[3,5,5,191],[23,71]),([],[],[]),([8167],[16333],[8167]),([],[],[]),([3,7,389],[3,3,3,5,5,19],[7,389]),([],[],[]),([8171],[3,13,419],[8171]),([],[],[]),([11,743],[31,503],[11,743]),([],[],[]),([3,5,5,109],[3,5,7,7,17],[5,109]),([],[],[]),([13,17,37],[79,191],[13,17,37]),([],[],[]),([8179],[11,1487],[8179]),([],[],[]),([3,3,3,3,101],[3,3,3,503],[3,101]),([],[],[]),([7,7,167],[5,7,433],[7,167]),([],[],[]),([5,1637],[11,13,103],[5,1637]),([],[],[]),([3,2729],[7,1949],[3,2729]),([],[],[]),([19,431],[17,937],[19,431]),([],[],[]),([8191],[16381],[8191])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range8192 (R D : ℕ) (lo : 8192 ≤ R) (hi : R < 8256) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 8192 64 R D [([],[],[]),([3,2731],[3,3,37,41],[2731]),([],[],[]),([5,11,149],[3,5,941],[11,149]),([],[],[]),([7,1171],[15217],[7,1171]),([],[],[]),([3,3,911],[3,29,157],[3,911]),([],[],[]),([59,139],[5,7,463],[59,139]),([],[],[]),([13,631],[11,1433],[13,631]),([],[],[]),([3,5,547],[3,3,11,127],[5,547]),([],[],[]),([29,283],[16103],[29,283]),([],[],[]),([8209],[16417],[8209]),([],[],[]),([3,7,17,23],[3,5,829],[7,17,23]),([],[],[]),([43,191],[16193],[43,191]),([],[],[]),([5,31,53],[5,7,7,59],[31,53]),([],[],[]),([3,3,11,83],[3,29,151],[3,11,83]),([],[],[]),([8219],[3,5479],[8219]),([],[],[]),([8221],[41,401],[8221]),([],[],[]),([3,2741],[71,193],[3,2741]),([],[],[]),([5,5,7,47],[5,2749],[5,7,47]),([],[],[]),([19,433],[13,1231],[19,433]),([],[],[]),([3,13,211],[3,4423],[13,211]),([],[],[]),([8231],[3,3,31,59],[8231]),([],[],[]),([8233],[5,37,89],[8233]),([],[],[]),([3,3,3,5,61],[3,3,3,3,5,31],[61]),([],[],[]),([8237],[3,17,17,19],[8237]),([],[],[]),([7,11,107],[13,1123],[7,11,107]),([],[],[]),([3,41,67],[3,4507],[41,67]),([],[],[]),([8243],[3,5,7,157],[8243]),([],[],[]),([5,17,97],[14389],[5,17,97]),([],[],[]),([3,2749],[3,3,3,509],[2749]),([],[],[]),([73,113],[11,1483],[73,113]),([],[],[]),([37,223],[37,439],[223]),([],[],[]),([3,3,7,131],[3,3,3,479],[7,131]),([],[],[]),([5,13,127],[14303],[5,13,127])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range8256 (R D : ℕ) (lo : 8256 ≤ R) (hi : R < 8320) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 8256 64 R D [([],[],[]),([23,359],[13,17,73],[23,359]),([],[],[]),([3,2753],[13763],[3,2753]),([],[],[]),([11,751],[15761],[11,751]),([],[],[]),([8263],[5,5,661],[8263]),([],[],[]),([3,5,19,29],[3,4099],[5,19,29]),([],[],[]),([7,1181],[103,149],[7,1181]),([],[],[]),([8269],[23,719],[8269]),([],[],[]),([3,3,919],[3,3,1531],[919]),([],[],[]),([8273],[3,5,1103],[8273]),([],[],[]),([5,5,331],[5,5,5,7,17],[331]),([],[],[]),([3,31,89],[3,4519],[31,89]),([],[],[]),([17,487],[5,13,13,19],[17,487]),([],[],[]),([7,7,13,13],[7,13,163],[7,13]),([],[],[]),([3,11,251],[37,359],[3,11,251]),([],[],[]),([5,1657],[17,877],[5,1657]),([],[],[]),([8287],[16573],[8287]),([],[],[]),([3,3,3,307],[3,3,3,7,73],[307]),([],[],[]),([8291],[3,5527],[8291]),([],[],[]),([8293],[5,31,107],[8293]),([],[],[]),([3,5,7,79],[3,4013],[5,7,79]),([],[],[]),([8297],[3,5531],[8297]),([],[],[]),([43,193],[16363],[43,193]),([],[],[]),([3,2767],[3,3,29,53],[2767]),([],[],[]),([19,19,23],[7,7,17,19],[19,23]),([],[],[]),([5,11,151],[5,2861],[11,151]),([],[],[]),([3,3,13,71],[3,3,1483],[13,71]),([],[],[]),([7,1187],[5,5,617],[7,1187]),([],[],[]),([8311],[11,1511],[8311]),([],[],[]),([3,17,163],[3,11,409],[17,163]),([],[],[]),([5,1663],[13,1151],[5,1663]),([],[],[]),([8317],[16633],[8317]),([],[],[]),([3,47,59],[5,2731],[3,47,59])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range8320 (R D : ℕ) (lo : 8320 ≤ R) (hi : R < 8384) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 8320 64 R D [([],[],[]),([53,157],[16433],[53,157]),([],[],[]),([7,29,41],[7,7,307],[29,41]),([],[],[]),([3,3,5,5,37],[3,3,5,281],[5,37]),([],[],[]),([11,757],[15887],[11,757]),([],[],[]),([8329],[16657],[8329]),([],[],[]),([3,2777],[13883],[3,2777]),([],[],[]),([13,641],[67,239],[13,641]),([],[],[]),([5,1667],[53,283],[5,1667]),([],[],[]),([3,7,397],[3,4363],[7,397]),([],[],[]),([31,269],[11,1489],[31,269]),([],[],[]),([19,439],[5,5,11,59],[19,439]),([],[],[]),([3,3,3,3,103],[3,3,3,3,3,3,19],[103]),([],[],[]),([5,1669],[15017],[5,1669]),([],[],[]),([17,491],[16187],[17,491]),([],[],[]),([3,11,11,23],[11,11,109],[3,23]),([],[],[]),([7,1193],[37,419],[7,1193]),([],[],[]),([8353],[5,13,257],[8353]),([],[],[]),([3,5,557],[7,31,59],[3,5,557]),([],[],[]),([61,137],[83,199],[61,137]),([],[],[]),([13,643],[16063],[13,643]),([],[],[]),([3,3,929],[3,4643],[3,929]),([],[],[]),([8363],[3,5,5,223],[8363]),([],[],[]),([5,7,239],[7,2011],[5,239]),([],[],[]),([3,2789],[73,191],[3,2789]),([],[],[]),([8369],[3,7,797],[8369]),([],[],[]),([11,761],[15971],[11,761]),([],[],[]),([3,2791],[3,4651],[2791]),([],[],[]),([5,5,5,67],[5,5,599],[5,67]),([],[],[]),([8377],[11,1523],[8377]),([],[],[]),([3,3,7,7,19],[3,3,5,7,41],[7,19]),([],[],[]),([17,17,29],[17,941],[17,29]),([],[],[]),([83,101],[7,23,103],[83,101])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range8384 (R D : ℕ) (lo : 8384 ≤ R) (hi : R < 8448) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 8384 64 R D [([],[],[]),([3,5,13,43],[3,4139],[5,13,43]),([],[],[]),([8387],[3,5591],[8387]),([],[],[]),([8389],[19,883],[8389]),([],[],[]),([3,2797],[3,59,79],[2797]),([],[],[]),([7,11,109],[107,139],[7,11,109]),([],[],[]),([5,23,73],[14731],[5,23,73]),([],[],[]),([3,3,3,311],[3,3,1553],[3,311]),([],[],[]),([37,227],[5,3307],[37,227]),([],[],[]),([31,271],[29,569],[31,271]),([],[],[]),([3,2801],[11,19,67],[3,2801]),([],[],[]),([5,41,41],[5,41,73],[41]),([],[],[]),([7,1201],[15607],[7,1201]),([],[],[]),([3,2803],[3,3,3,3,173],[2803]),([],[],[]),([13,647],[7,2309],[13,647]),([],[],[]),([47,179],[13,1277],[47,179]),([],[],[]),([3,3,5,11,17],[3,5,19,43],[3,11,17]),([],[],[]),([19,443],[7,2339],[19,443]),([],[],[]),([8419],[113,149],[8419]),([],[],[]),([3,7,401],[3,3,13,113],[7,401]),([],[],[]),([8423],[3,5,1123],[8423]),([],[],[]),([5,5,337],[5,13,233],[5,337]),([],[],[]),([3,53,53],[53,263],[3,53]),([],[],[]),([8429],[3,3,1873],[8429]),([],[],[]),([8431],[13,1297],[8431]),([],[],[]),([3,3,937],[3,3,7,223],[937]),([],[],[]),([5,7,241],[5,17,167],[7,241]),([],[],[]),([11,13,59],[89,173],[11,13,59]),([],[],[]),([3,29,97],[3,3,5,307],[29,97]),([],[],[]),([23,367],[16493],[23,367]),([],[],[]),([8443],[5,11,307],[8443]),([],[],[]),([3,5,563],[12941],[3,5,563]),([],[],[]),([8447],[3,3,1877],[8447])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range8448 (R D : ℕ) (lo : 8448 ≤ R) (hi : R < 8512) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 8448 64 R D [([],[],[]),([7,17,71],[7,11,197],[17,71]),([],[],[]),([3,3,3,313],[3,3,3,521],[313]),([],[],[]),([79,107],[23,727],[79,107]),([],[],[]),([5,19,89],[7,2113],[5,19,89]),([],[],[]),([3,2819],[17,829],[3,2819]),([],[],[]),([11,769],[16139],[11,769]),([],[],[]),([8461],[16921],[8461]),([],[],[]),([3,7,13,31],[3,4261],[7,13,31]),([],[],[]),([5,1693],[15233],[5,1693]),([],[],[]),([8467],[7,41,59],[8467]),([],[],[]),([3,3,941],[3,4703],[3,941]),([],[],[]),([43,197],[16703],[43,197]),([],[],[]),([37,229],[7,2383],[37,229]),([],[],[]),([3,5,5,113],[5,2591],[3,5,113]),([],[],[]),([7,7,173],[7,2243],[7,173]),([],[],[]),([61,139],[16759],[61,139]),([],[],[]),([3,11,257],[7,29,67],[3,11,257]),([],[],[]),([17,499],[16451],[17,499]),([],[],[]),([5,1697],[15269],[5,1697]),([],[],[]),([3,3,23,41],[3,13,353],[3,23,41]),([],[],[]),([13,653],[11,1483],[13,653]),([],[],[]),([7,1213],[11,1433],[7,1213]),([],[],[]),([3,19,149],[3,17,271],[19,149]),([],[],[]),([5,1699],[15287],[5,1699]),([],[],[]),([29,293],[16673],[29,293]),([],[],[]),([3,2833],[3,4721],[2833]),([],[],[]),([8501],[3,3,1889],[8501]),([],[],[]),([11,773],[16223],[11,773]),([],[],[]),([3,3,3,3,3,5,7],[3,3,3,3,3,3,17],[5,7]),([],[],[]),([47,181],[16787],[47,181]),([],[],[]),([67,127],[5,5,673],[67,127]),([],[],[]),([3,2837],[13,1091],[3,2837])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range8512 (R D : ℕ) (lo : 8512 ≤ R) (hi : R < 8576) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 8512 64 R D [([],[],[]),([8513],[3,5,5,227],[8513]),([],[],[]),([5,13,131],[5,13,227],[131]),([],[],[]),([3,17,167],[13829],[3,17,167]),([],[],[]),([7,1217],[5,3163],[7,1217]),([],[],[]),([8521],[17041],[8521]),([],[],[]),([3,3,947],[3,4733],[3,947]),([],[],[]),([5,5,11,31],[5,5,7,83],[11,31]),([],[],[]),([8527],[17053],[8527]),([],[],[]),([3,2843],[61,233],[3,2843]),([],[],[]),([19,449],[5,3319],[19,449]),([],[],[]),([7,23,53],[89,173],[7,23,53]),([],[],[]),([3,5,569],[11,29,41],[3,5,569]),([],[],[]),([8537],[3,3,7,271],[8537]),([],[],[]),([8539],[17077],[8539]),([],[],[]),([3,3,13,73],[3,3,5,5,61],[13,73]),([],[],[]),([8543],[3,5,17,67],[8543]),([],[],[]),([5,1709],[15377],[5,1709]),([],[],[]),([3,7,11,37],[3,4289],[7,11,37]),([],[],[]),([83,103],[13,1301],[83,103]),([],[],[]),([17,503],[7,23,103],[17,503]),([],[],[]),([3,2851],[3,4751],[2851]),([],[],[]),([5,29,59],[3,29,173],[5,59]),([],[],[]),([43,199],[47,359],[43,199]),([],[],[]),([3,3,3,317],[3,3,1583],[3,317]),([],[],[]),([7,1223],[23,691],[7,1223]),([],[],[]),([8563],[5,5,5,137],[8563]),([],[],[]),([3,5,571],[3,5,5,5,5,7],[571]),([],[],[]),([13,659],[101,163],[13,659]),([],[],[]),([11,19,41],[13,1213],[11,19,41]),([],[],[]),([3,2857],[3,3,3,23,23],[2857]),([],[],[]),([8573],[3,3,3,5,127],[8573]),([],[],[]),([5,5,7,7,7],[5,7,7,59],[5,7])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range8576 (R D : ℕ) (lo : 8576 ≤ R) (hi : R < 8640) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 8576 64 R D [([],[],[]),([3,3,953],[3,11,433],[3,953]),([],[],[]),([23,373],[16763],[23,373]),([],[],[]),([8581],[131,131],[8581]),([],[],[]),([3,2861],[14303],[3,2861]),([],[],[]),([5,17,101],[3,3,3,3,5,37],[17,101]),([],[],[]),([31,277],[101,167],[31,277]),([],[],[]),([3,7,409],[3,5,29,31],[7,409]),([],[],[]),([11,11,71],[11,1481],[11,71]),([],[],[]),([13,661],[7,7,337],[13,661]),([],[],[]),([3,3,5,191],[3,5,877],[3,191]),([],[],[]),([8597],[3,11,521],[8597]),([],[],[]),([8599],[29,593],[8599]),([],[],[]),([3,47,61],[3,3,3,523],[47,61]),([],[],[]),([7,1229],[15971],[7,1229]),([],[],[]),([5,1721],[5,19,163],[1721]),([],[],[]),([3,19,151],[3,7,23,29],[19,151]),([],[],[]),([8609],[3,3,1913],[8609]),([],[],[]),([79,109],[5,3407],[79,109]),([],[],[]),([3,3,3,11,29],[3,3,37,41],[3,11,29]),([],[],[]),([5,1723],[37,419],[5,1723]),([],[],[]),([7,1231],[17,941],[7,1231]),([],[],[]),([3,13,13,17],[3,13,349],[13,17]),([],[],[]),([37,233],[11,1543],[37,233]),([],[],[]),([8623],[5,3449],[8623]),([],[],[]),([3,5,5,5,23],[5,5,521],[3,5,23]),([],[],[]),([8627],[3,3,3,3,3,71],[8627]),([],[],[]),([8629],[17257],[8629]),([],[],[]),([3,3,7,137],[3,3,3,3,167],[7,137]),([],[],[]),([89,97],[19,29,31],[89,97]),([],[],[]),([5,11,157],[5,5,5,7,17],[11,157]),([],[],[]),([3,2879],[37,389],[3,2879]),([],[],[]),([53,163],[113,151],[53,163])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range8640 (R D : ℕ) (lo : 8640 ≤ R) (hi : R < 8704) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 8640 64 R D [([],[],[]),([8641],[11,1571],[8641]),([],[],[]),([3,43,67],[3,4729],[43,67]),([],[],[]),([5,7,13,19],[13829],[5,7,13,19]),([],[],[]),([8647],[17293],[8647]),([],[],[]),([3,3,31,31],[3,3,3,17,31],[31]),([],[],[]),([41,211],[17,17,59],[41,211]),([],[],[]),([17,509],[97,173],[17,509]),([],[],[]),([3,5,577],[3,4421],[5,577]),([],[],[]),([11,787],[83,199],[11,787]),([],[],[]),([7,1237],[5,5,643],[7,1237]),([],[],[]),([3,2887],[3,17,283],[2887]),([],[],[]),([8663],[3,3,5,5,7,11],[8663]),([],[],[]),([5,1733],[31,503],[5,1733]),([],[],[]),([3,3,3,3,107],[3,3,3,13,41],[3,107]),([],[],[]),([8669],[3,5779],[8669]),([],[],[]),([13,23,29],[16063],[13,23,29]),([],[],[]),([3,7,7,59],[3,3,5,7,43],[7,59]),([],[],[]),([5,5,347],[5,3119],[5,347]),([],[],[]),([8677],[7,37,67],[8677]),([],[],[]),([3,11,263],[31,449],[3,11,263]),([],[],[]),([8681],[3,3,3,643],[8681]),([],[],[]),([19,457],[7,19,127],[457]),([],[],[]),([3,3,5,193],[3,3,7,211],[5,193]),([],[],[]),([7,17,73],[19,821],[7,17,73]),([],[],[]),([8689],[17377],[8689]),([],[],[]),([3,2897],[7,2069],[3,2897]),([],[],[]),([8693],[3,5,19,61],[8693]),([],[],[]),([5,37,47],[15319],[5,37,47]),([],[],[]),([3,13,223],[3,5,5,11,17],[13,223]),([],[],[]),([8699],[3,3,1933],[8699]),([],[],[]),([7,11,113],[7,2203],[11,113]),([],[],[]),([3,3,967],[3,3,3,3,179],[967])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range8704 (R D : ℕ) (lo : 8704 ≤ R) (hi : R < 8768) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 8704 64 R D [([],[],[]),([5,1741],[5,13,241],[1741]),([],[],[]),([8707],[11,1583],[8707]),([],[],[]),([3,2903],[23,631],[3,2903]),([],[],[]),([31,281],[71,241],[31,281]),([],[],[]),([8713],[5,5,17,41],[8713]),([],[],[]),([3,5,7,83],[3,4217],[5,7,83]),([],[],[]),([23,379],[17033],[23,379]),([],[],[]),([8719],[7,47,53],[8719]),([],[],[]),([3,3,3,17,19],[3,3,3,5,103],[17,19]),([],[],[]),([11,13,61],[15923],[11,13,61]),([],[],[]),([5,5,349],[5,3137],[5,349]),([],[],[]),([3,2909],[14543],[3,2909]),([],[],[]),([7,29,43],[5,7,11,41],[29,43]),([],[],[]),([8731],[19,919],[8731]),([],[],[]),([3,41,71],[11,1303],[3,41,71]),([],[],[]),([5,1747],[11,1429],[5,1747]),([],[],[]),([8737],[101,173],[8737]),([],[],[]),([3,3,971],[3,23,211],[3,971]),([],[],[]),([8741],[3,5827],[8741]),([],[],[]),([7,1249],[16231],[7,1249]),([],[],[]),([3,5,11,53],[5,29,89],[3,11,53]),([],[],[]),([8747],[3,7,7,7,17],[8747]),([],[],[]),([13,673],[17,23,43],[13,673]),([],[],[]),([3,2917],[3,4861],[2917]),([],[],[]),([8753],[3,3,5,389],[8753]),([],[],[]),([5,17,103],[17,29,31],[5,103]),([],[],[]),([3,3,7,139],[3,3,5,5,61],[7,139]),([],[],[]),([19,461],[11,1549],[19,461]),([],[],[]),([8761],[7,2503],[8761]),([],[],[]),([3,23,127],[3,19,251],[23,127]),([],[],[]),([5,1753],[15773],[5,1753]),([],[],[]),([11,797],[43,389],[11,797])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range8768 (R D : ℕ) (lo : 8768 ≤ R) (hi : R < 8832) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 8768 64 R D [([],[],[]),([3,37,79],[3,5,7,137],[37,79]),([],[],[]),([7,7,179],[7,11,211],[7,179]),([],[],[]),([31,283],[19,907],[31,283]),([],[],[]),([3,3,3,5,5,13],[3,3,3,5,97],[5,13]),([],[],[]),([67,131],[17,1021],[67,131]),([],[],[]),([8779],[97,181],[8779]),([],[],[]),([3,2927],[14633],[3,2927]),([],[],[]),([8783],[3,5,1171],[8783]),([],[],[]),([5,7,251],[5,2957],[7,251]),([],[],[]),([3,29,101],[14387],[3,29,101]),([],[],[]),([11,17,47],[3,7,769],[11,17,47]),([],[],[]),([59,149],[5,5,5,139],[59,149]),([],[],[]),([3,3,977],[3,19,257],[3,977]),([],[],[]),([5,1759],[7,7,17,19],[5,1759]),([],[],[]),([19,463],[109,157],[19,463]),([],[],[]),([3,7,419],[3,3,5,307],[7,419]),([],[],[]),([13,677],[13,1301],[677]),([],[],[]),([8803],[5,7,503],[8803]),([],[],[]),([3,5,587],[103,131],[3,5,587]),([],[],[]),([8807],[3,3,19,103],[8807]),([],[],[]),([23,383],[7,2459],[23,383]),([],[],[]),([3,3,11,89],[3,7,11,61],[3,89]),([],[],[]),([7,1259],[16361],[7,1259]),([],[],[]),([5,41,43],[5,13,239],[41,43]),([],[],[]),([3,2939],[7,2099],[3,2939]),([],[],[]),([8819],[3,5879],[8819]),([],[],[]),([8821],[13,23,59],[8821]),([],[],[]),([3,17,173],[14327],[3,17,173]),([],[],[]),([5,5,353],[5,19,167],[5,353]),([],[],[]),([7,13,97],[15739],[7,13,97]),([],[],[]),([3,3,3,3,109],[3,3,3,3,181],[109]),([],[],[]),([8831],[3,7,29,29],[8831])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range8832 (R D : ℕ) (lo : 8832 ≤ R) (hi : R < 8896) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 8832 64 R D [([],[],[]),([11,11,73],[11,1523],[11,73]),([],[],[]),([3,5,19,31],[3,5,877],[19,31]),([],[],[]),([8837],[3,43,137],[8837]),([],[],[]),([8839],[11,1607],[8839]),([],[],[]),([3,7,421],[3,7,661],[421]),([],[],[]),([37,239],[23,757],[37,239]),([],[],[]),([5,29,61],[5,11,283],[29,61]),([],[],[]),([3,3,983],[3,17,17,17],[3,983]),([],[],[]),([8849],[3,17,347],[8849]),([],[],[]),([53,167],[17483],[53,167]),([],[],[]),([3,13,227],[3,4759],[13,227]),([],[],[]),([5,7,11,23],[5,11,257],[7,23]),([],[],[]),([17,521],[89,193],[17,521]),([],[],[]),([3,2953],[3,7,19,37],[2953]),([],[],[]),([8861],[3,3,11,179],[8861]),([],[],[]),([8863],[5,5,709],[8863]),([],[],[]),([3,3,5,197],[3,4523],[3,5,197]),([],[],[]),([8867],[3,23,257],[8867]),([],[],[]),([7,7,181],[7,2347],[7,181]),([],[],[]),([3,2957],[14783],[3,2957]),([],[],[]),([19,467],[41,421],[19,467]),([],[],[]),([5,5,5,71],[5,5,5,127],[71]),([],[],[]),([3,11,269],[23,619],[3,11,269]),([],[],[]),([13,683],[113,151],[13,683]),([],[],[]),([83,107],[17573],[83,107]),([],[],[]),([3,3,3,7,47],[3,3,3,3,3,3,19],[7,47]),([],[],[]),([5,1777],[59,271],[5,1777]),([],[],[]),([8887],[7,2539],[8887]),([],[],[]),([3,2963],[14813],[3,2963]),([],[],[]),([17,523],[43,401],[17,523]),([],[],[]),([8893],[5,3557],[8893]),([],[],[]),([3,5,593],[43,317],[3,5,593])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range8896 (R D : ℕ) (lo : 8896 ≤ R) (hi : R < 8960) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 8896 64 R D [([],[],[]),([7,31,41],[16097],[7,31,41]),([],[],[]),([11,809],[16979],[11,809]),([],[],[]),([3,3,23,43],[3,3,3,5,107],[23,43]),([],[],[]),([29,307],[17471],[29,307]),([],[],[]),([5,13,137],[11,23,61],[5,13,137]),([],[],[]),([3,2969],[14843],[3,2969]),([],[],[]),([59,151],[17609],[59,151]),([],[],[]),([7,19,67],[43,373],[7,19,67]),([],[],[]),([3,2971],[3,4951],[2971]),([],[],[]),([5,1783],[61,263],[5,1783]),([],[],[]),([37,241],[97,181],[37,241]),([],[],[]),([3,3,991],[3,3,13,127],[991]),([],[],[]),([11,811],[17021],[11,811]),([],[],[]),([8923],[5,43,83],[8923]),([],[],[]),([3,5,5,7,17],[3,5,23,37],[5,7,17]),([],[],[]),([79,113],[17,1039],[79,113]),([],[],[]),([8929],[7,2551],[8929]),([],[],[]),([3,13,229],[3,4801],[13,229]),([],[],[]),([8933],[3,3,5,397],[8933]),([],[],[]),([5,1787],[7,2297],[5,1787]),([],[],[]),([3,3,3,331],[3,3,3,19,29],[331]),([],[],[]),([7,1277],[5,3319],[7,1277]),([],[],[]),([8941],[17881],[8941]),([],[],[]),([3,11,271],[3,7,683],[11,271]),([],[],[]),([5,1789],[16097],[5,1789]),([],[],[]),([23,389],[17483],[23,389]),([],[],[]),([3,19,157],[3,5,971],[19,157]),([],[],[]),([8951],[3,3,3,3,13,17],[8951]),([],[],[]),([7,1279],[11,1511],[7,1279]),([],[],[]),([3,3,5,199],[3,3,1523],[5,199]),([],[],[]),([13,13,53],[13,13,101],[53]),([],[],[]),([17,17,31],[17,19,53],[17,31])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range8960 (R D : ℕ) (lo : 8960 ≤ R) (hi : R < 9024) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 8960 64 R D [([],[],[]),([3,29,103],[3,67,73],[29,103]),([],[],[]),([8963],[3,5,5,239],[8963]),([],[],[]),([5,11,163],[5,3089],[11,163]),([],[],[]),([3,7,7,61],[3,7,23,29],[7,61]),([],[],[]),([8969],[3,3,1993],[8969]),([],[],[]),([8971],[7,11,233],[8971]),([],[],[]),([3,3,997],[3,3,11,151],[997]),([],[],[]),([5,5,359],[5,7,461],[5,359]),([],[],[]),([47,191],[7,2531],[47,191]),([],[],[]),([3,41,73],[3,17,17,17],[41,73]),([],[],[]),([7,1283],[16673],[7,1283]),([],[],[]),([13,691],[61,283],[13,691]),([],[],[]),([3,5,599],[7,7,281],[3,5,599]),([],[],[]),([11,19,43],[16547],[11,19,43]),([],[],[]),([89,101],[17789],[89,101]),([],[],[]),([3,3,3,3,3,37],[3,3,3,3,3,61],[37]),([],[],[]),([17,23,23],[23,743],[17,23]),([],[],[]),([5,7,257],[15139],[5,7,257]),([],[],[]),([3,2999],[11,29,47],[3,2999]),([],[],[]),([8999],[3,7,857],[8999]),([],[],[]),([9001],[47,383],[9001]),([],[],[]),([3,3001],[3,3,1667],[3001]),([],[],[]),([5,1801],[5,7,463],[1801]),([],[],[]),([9007],[18013],[9007]),([],[],[]),([3,3,7,11,13],[3,3,1481],[7,11,13]),([],[],[]),([9011],[3,6007],[9011]),([],[],[]),([9013],[5,5,7,103],[9013]),([],[],[]),([3,5,601],[3,3,5,307],[601]),([],[],[]),([71,127],[17837],[71,127]),([],[],[]),([29,311],[11,1609],[29,311]),([],[],[]),([3,31,97],[3,13,379],[31,97]),([],[],[]),([7,1289],[7,2393],[1289])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range9024 (R D : ℕ) (lo : 9024 ≤ R) (hi : R < 9088) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 9024 64 R D [([],[],[]),([5,5,19,19],[5,19,167],[5,19]),([],[],[]),([3,3,17,59],[3,5,7,139],[3,17,59]),([],[],[]),([9029],[3,13,463],[9029]),([],[],[]),([11,821],[17231],[11,821]),([],[],[]),([3,3011],[15053],[3,3011]),([],[],[]),([5,13,139],[7,2237],[5,13,139]),([],[],[]),([7,1291],[19,883],[7,1291]),([],[],[]),([3,23,131],[14759],[3,23,131]),([],[],[]),([9041],[3,3,7,7,41],[9041]),([],[],[]),([9043],[5,3617],[9043]),([],[],[]),([3,3,3,5,67],[3,3,3,7,73],[5,67]),([],[],[]),([83,109],[17903],[83,109]),([],[],[]),([9049],[18097],[9049]),([],[],[]),([3,7,431],[3,3,1579],[7,431]),([],[],[]),([11,823],[23,751],[11,823]),([],[],[]),([5,1811],[5,3259],[1811]),([],[],[]),([3,3019],[3,3,3,13,43],[3019]),([],[],[]),([9059],[3,3,3,11,61],[9059]),([],[],[]),([13,17,41],[16741],[13,17,41]),([],[],[]),([3,3,19,53],[3,3,7,233],[19,53]),([],[],[]),([5,7,7,37],[7,17,127],[5,7,37]),([],[],[]),([9067],[18133],[9067]),([],[],[]),([3,3023],[7,17,127],[3,3023]),([],[],[]),([47,193],[17903],[47,193]),([],[],[]),([43,211],[29,617],[43,211]),([],[],[]),([3,5,5,11,11],[5,5,7,7,11],[3,11]),([],[],[]),([29,313],[47,379],[29,313]),([],[],[]),([7,1297],[5,3371],[7,1297]),([],[],[]),([3,3,1009],[3,3,41,41],[1009]),([],[],[]),([31,293],[7,2549],[31,293]),([],[],[]),([5,23,79],[41,389],[5,23,79]),([],[],[]),([3,13,233],[3,5,977],[13,233])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range9088 (R D : ℕ) (lo : 9088 ≤ R) (hi : R < 9152) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 9088 64 R D [([],[],[]),([61,149],[7,17,151],[61,149]),([],[],[]),([9091],[18181],[9091]),([],[],[]),([3,7,433],[3,4759],[7,433]),([],[],[]),([5,17,107],[3,67,79],[5,17,107]),([],[],[]),([11,827],[17,1021],[11,827]),([],[],[]),([3,3,3,337],[3,3,3,3,11,17],[337]),([],[],[]),([19,479],[5,3541],[19,479]),([],[],[]),([9103],[5,11,331],[9103]),([],[],[]),([3,5,607],[3,4651],[5,607]),([],[],[]),([7,1301],[11,29,53],[7,1301]),([],[],[]),([9109],[18217],[9109]),([],[],[]),([3,3037],[3,3,7,241],[3037]),([],[],[]),([13,701],[83,211],[13,701]),([],[],[]),([5,1823],[47,349],[5,1823]),([],[],[]),([3,3,1013],[3,61,83],[3,1013]),([],[],[]),([11,829],[127,137],[11,829]),([],[],[]),([7,1303],[7,41,59],[1303]),([],[],[]),([3,3041],[23,661],[3,3041]),([],[],[]),([5,5,5,73],[5,5,653],[5,73]),([],[],[]),([9127],[18253],[9127]),([],[],[]),([3,17,179],[5,5,593],[3,17,179]),([],[],[]),([23,397],[7,2549],[23,397]),([],[],[]),([9133],[5,13,281],[9133]),([],[],[]),([3,3,5,7,29],[3,3,7,11,19],[5,29]),([],[],[]),([9137],[3,6091],[9137]),([],[],[]),([13,19,37],[5,17,199],[13,19,37]),([],[],[]),([3,11,277],[3,3,3,3,181],[11,277]),([],[],[]),([41,223],[67,269],[41,223]),([],[],[]),([5,31,59],[5,3221],[31,59]),([],[],[]),([3,3049],[3,5081],[3049]),([],[],[]),([7,1307],[5,43,79],[7,1307]),([],[],[]),([9151],[18301],[9151])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range9152 (R D : ℕ) (lo : 9152 ≤ R) (hi : R < 9216) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 9152 64 R D [([],[],[]),([3,3,3,3,113],[3,3,3,563],[3,113]),([],[],[]),([5,1831],[5,5,659],[1831]),([],[],[]),([9157],[18313],[9157]),([],[],[]),([3,43,71],[3,3,3,557],[43,71]),([],[],[]),([9161],[3,31,197],[9161]),([],[],[]),([7,7,11,17],[7,2269],[7,11,17]),([],[],[]),([3,5,13,47],[3,3,3,503],[5,13,47]),([],[],[]),([89,103],[18143],[89,103]),([],[],[]),([53,173],[59,307],[53,173]),([],[],[]),([3,3,1019],[3,11,463],[3,1019]),([],[],[]),([9173],[3,5,1223],[9173]),([],[],[]),([5,5,367],[5,3299],[5,367]),([],[],[]),([3,7,19,23],[3,4643],[7,19,23]),([],[],[]),([67,137],[5,3631],[67,137]),([],[],[]),([9181],[7,43,61],[9181]),([],[],[]),([3,3061],[3,5101],[3061]),([],[],[]),([5,11,167],[3,5,5,211],[11,167]),([],[],[]),([9187],[19,967],[9187]),([],[],[]),([3,3,1021],[3,3,3,3,3,3,3,7],[1021]),([],[],[]),([7,13,101],[37,443],[7,13,101]),([],[],[]),([29,317],[18041],[29,317]),([],[],[]),([3,5,613],[3,7,11,61],[5,613]),([],[],[]),([17,541],[17837],[17,541]),([],[],[]),([9199],[18397],[9199]),([],[],[]),([3,3067],[3,19,269],[3067]),([],[],[]),([9203],[3,3,5,409],[9203]),([],[],[]),([5,7,263],[15493],[5,7,263]),([],[],[]),([3,3,3,11,31],[3,3,3,541],[11,31]),([],[],[]),([9209],[3,7,877],[9209]),([],[],[]),([61,151],[18211],[61,151]),([],[],[]),([3,37,83],[3,5039],[37,83]),([],[],[]),([5,19,97],[16127],[5,19,97])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range9216 (R D : ℕ) (lo : 9216 ≤ R) (hi : R < 9280) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 9216 64 R D [([],[],[]),([13,709],[17713],[13,709]),([],[],[]),([3,7,439],[3,5,5,193],[7,439]),([],[],[]),([9221],[3,3,3,683],[9221]),([],[],[]),([23,401],[67,269],[23,401]),([],[],[]),([3,3,5,5,41],[3,5,5,11,17],[3,41]),([],[],[]),([9227],[3,6151],[9227]),([],[],[]),([11,839],[17609],[11,839]),([],[],[]),([3,17,181],[3,19,263],[17,181]),([],[],[]),([7,1319],[61,281],[7,1319]),([],[],[]),([5,1847],[16619],[5,1847]),([],[],[]),([3,3079],[3,7,733],[3079]),([],[],[]),([9239],[3,3,2053],[9239]),([],[],[]),([9241],[18481],[9241]),([],[],[]),([3,3,13,79],[3,3,13,127],[79]),([],[],[]),([5,43,43],[43,383],[5,43]),([],[],[]),([7,1321],[17167],[7,1321]),([],[],[]),([3,3083],[15413],[3,3083]),([],[],[]),([11,29,29],[29,599],[11,29]),([],[],[]),([19,487],[47,383],[19,487]),([],[],[]),([3,5,617],[13,1091],[3,5,617]),([],[],[]),([9257],[3,3,11,11,17],[9257]),([],[],[]),([47,197],[5,5,17,43],[47,197]),([],[],[]),([3,3,3,7,7,7],[3,3,3,7,7,11],[7]),([],[],[]),([59,157],[18311],[59,157]),([],[],[]),([5,17,109],[7,2311],[5,17,109]),([],[],[]),([3,3089],[15443],[3,3089]),([],[],[]),([13,23,31],[17189],[13,23,31]),([],[],[]),([73,127],[13,17,83],[73,127]),([],[],[]),([3,11,281],[107,139],[3,11,281]),([],[],[]),([5,5,7,53],[5,29,107],[5,7,53]),([],[],[]),([9277],[18553],[9277]),([],[],[]),([3,3,1031],[3,5153],[3,1031])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range9280 (R D : ℕ) (lo : 9280 ≤ R) (hi : R < 9344) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 9280 64 R D [([],[],[]),([9281],[3,23,269],[9281]),([],[],[]),([9283],[5,47,79],[9283]),([],[],[]),([3,5,619],[3,3,3,17,31],[5,619]),([],[],[]),([37,251],[18287],[37,251]),([],[],[]),([7,1327],[5,3449],[7,1327]),([],[],[]),([3,19,163],[3,71,71],[19,163]),([],[],[]),([9293],[3,3,5,7,59],[9293]),([],[],[]),([5,11,13,13],[5,13,239],[11,13]),([],[],[]),([3,3,1033],[3,3,1721],[1033]),([],[],[]),([17,547],[5,3607],[17,547]),([],[],[]),([71,131],[18401],[71,131]),([],[],[]),([3,7,443],[3,3,3,541],[7,443]),([],[],[]),([5,1861],[5,17,197],[1861]),([],[],[]),([41,227],[7,2621],[41,227]),([],[],[]),([3,29,107],[5,3049],[3,29,107]),([],[],[]),([9311],[3,3,2069],[9311]),([],[],[]),([67,139],[13,13,109],[67,139]),([],[],[]),([3,3,3,3,5,23],[3,3,3,521],[3,5,23]),([],[],[]),([7,11,11,11],[11,11,137],[7,11]),([],[],[]),([9319],[18637],[9319]),([],[],[]),([3,13,239],[3,5011],[13,239]),([],[],[]),([9323],[3,5,11,113],[9323]),([],[],[]),([5,5,373],[5,7,479],[5,373]),([],[],[]),([3,3109],[3,3,11,157],[3109]),([],[],[]),([19,491],[18149],[19,491]),([],[],[]),([7,31,43],[7,19,127],[31,43]),([],[],[]),([3,3,17,61],[3,3,3,13,43],[17,61]),([],[],[]),([5,1867],[107,157],[5,1867]),([],[],[]),([9337],[71,263],[9337]),([],[],[]),([3,11,283],[3,4993],[11,283]),([],[],[]),([9341],[3,13,479],[9341]),([],[],[]),([9343],[5,37,101],[9343])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range9344 (R D : ℕ) (lo : 9344 ≤ R) (hi : R < 9408) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 9344 64 R D [([],[],[]),([3,5,7,89],[3,4523],[5,7,89]),([],[],[]),([13,719],[11,23,71],[13,719]),([],[],[]),([9349],[7,2671],[9349]),([],[],[]),([3,3,1039],[3,3,3,577],[1039]),([],[],[]),([47,199],[18461],[47,199]),([],[],[]),([5,1871],[5,7,13,37],[1871]),([],[],[]),([3,3119],[31,503],[3,3119]),([],[],[]),([7,7,191],[7,2477],[7,191]),([],[],[]),([11,23,37],[11,1571],[23,37]),([],[],[]),([3,3121],[3,7,743],[3121]),([],[],[]),([5,1873],[19,887],[5,1873]),([],[],[]),([17,19,29],[17431],[17,19,29]),([],[],[]),([3,3,3,347],[3,3,1733],[3,347]),([],[],[]),([9371],[3,6247],[9371]),([],[],[]),([7,13,103],[73,229],[7,13,103]),([],[],[]),([3,5,5,5,5,5],[5,5,5,5,23],[3,5]),([],[],[]),([9377],[3,7,19,47],[9377]),([],[],[]),([83,113],[19,977],[83,113]),([],[],[]),([3,53,59],[15413],[3,53,59]),([],[],[]),([11,853],[17903],[11,853]),([],[],[]),([5,1877],[16889],[5,1877]),([],[],[]),([3,3,7,149],[3,3,3,5,109],[7,149]),([],[],[]),([41,229],[83,223],[41,229]),([],[],[]),([9391],[7,2683],[9391]),([],[],[]),([3,31,101],[3,7,733],[31,101]),([],[],[]),([5,1879],[11,29,53],[5,1879]),([],[],[]),([9397],[18793],[9397]),([],[],[]),([3,13,241],[3,31,163],[13,241]),([],[],[]),([7,17,79],[16889],[7,17,79]),([],[],[]),([9403],[5,3761],[9403]),([],[],[]),([3,3,5,11,19],[3,3,5,5,61],[11,19]),([],[],[]),([23,409],[31,593],[23,409])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range9408 (R D : ℕ) (lo : 9408 ≤ R) (hi : R < 9472) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 9408 64 R D [([],[],[]),([97,97],[97,193],[97]),([],[],[]),([3,3137],[15683],[3,3137]),([],[],[]),([9413],[3,5,5,251],[9413]),([],[],[]),([5,7,269],[13,23,53],[5,7,269]),([],[],[]),([3,43,73],[3,5,1031],[43,73]),([],[],[]),([9419],[3,3,7,13,23],[9419]),([],[],[]),([9421],[83,227],[9421]),([],[],[]),([3,3,3,349],[3,3,3,7,83],[349]),([],[],[]),([5,5,13,29],[5,3229],[5,13,29]),([],[],[]),([11,857],[17987],[11,857]),([],[],[]),([3,7,449],[3,3,5,7,47],[449]),([],[],[]),([9431],[3,6287],[9431]),([],[],[]),([9433],[5,7,7,7,11],[9433]),([],[],[]),([3,5,17,37],[3,31,151],[5,17,37]),([],[],[]),([9437],[3,3,3,3,233],[9437]),([],[],[]),([9439],[43,439],[9439]),([],[],[]),([3,3,1049],[3,7,7,107],[3,1049]),([],[],[]),([7,19,71],[7,7,347],[19,71]),([],[],[]),([5,1889],[23,739],[5,1889]),([],[],[]),([3,47,67],[3,7,739],[47,67]),([],[],[]),([11,859],[11,11,149],[859]),([],[],[]),([13,727],[41,443],[13,727]),([],[],[]),([3,23,137],[43,359],[3,23,137]),([],[],[]),([5,31,61],[5,3331],[31,61]),([],[],[]),([7,7,193],[7,2503],[7,193]),([],[],[]),([3,3,1051],[3,3,17,103],[1051]),([],[],[]),([9461],[3,7,17,53],[9461]),([],[],[]),([9463],[5,5,757],[9463]),([],[],[]),([3,5,631],[3,5,967],[631]),([],[],[]),([9467],[3,6311],[9467]),([],[],[]),([17,557],[5,3673],[17,557]),([],[],[]),([3,7,11,41],[3,67,71],[7,11,41])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range9472 (R D : ℕ) (lo : 9472 ≤ R) (hi : R < 9536) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 9472 64 R D [([],[],[]),([9473],[3,3,5,421],[9473]),([],[],[]),([5,5,379],[5,3407],[5,379]),([],[],[]),([3,3,3,3,3,3,13],[3,3,3,3,3,3,3,7],[13]),([],[],[]),([9479],[3,71,89],[9479]),([],[],[]),([19,499],[5,7,17,31],[19,499]),([],[],[]),([3,29,109],[3,31,167],[29,109]),([],[],[]),([5,7,271],[5,31,103],[7,271]),([],[],[]),([53,179],[18743],[53,179]),([],[],[]),([3,3163],[3,3,7,251],[3163]),([],[],[]),([9491],[3,3,3,19,37],[9491]),([],[],[]),([11,863],[59,307],[11,863]),([],[],[]),([3,3,5,211],[3,3,5,17,19],[211]),([],[],[]),([9497],[3,13,487],[9497]),([],[],[]),([7,23,59],[5,47,73],[7,23,59]),([],[],[]),([3,3167],[71,223],[3,3167]),([],[],[]),([13,17,43],[11,1597],[13,17,43]),([],[],[]),([5,1901],[5,11,311],[1901]),([],[],[]),([3,3169],[3,5281],[3169]),([],[],[]),([37,257],[5,5,7,107],[37,257]),([],[],[]),([9511],[23,827],[9511]),([],[],[]),([3,3,7,151],[3,3,1657],[7,151]),([],[],[]),([5,11,173],[3,5,1093],[11,173]),([],[],[]),([31,307],[7,2671],[31,307]),([],[],[]),([3,19,167],[3,5,1033],[19,167]),([],[],[]),([9521],[3,11,577],[9521]),([],[],[]),([89,107],[7,2693],[89,107]),([],[],[]),([3,5,5,127],[3,5,971],[5,127]),([],[],[]),([7,1361],[23,769],[7,1361]),([],[],[]),([13,733],[18313],[13,733]),([],[],[]),([3,3,3,353],[3,3,41,43],[3,353]),([],[],[]),([9533],[3,5,31,41],[9533]),([],[],[]),([5,1907],[17159],[5,1907])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range9536 (R D : ℕ) (lo : 9536 ≤ R) (hi : R < 9600) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 9536 64 R D [([],[],[]),([3,11,17,17],[17,881],[3,11,17]),([],[],[]),([9539],[3,6359],[9539]),([],[],[]),([7,29,47],[7,2467],[29,47]),([],[],[]),([3,3181],[3,3,3,19,31],[3181]),([],[],[]),([5,23,83],[3,37,151],[5,23,83]),([],[],[]),([9547],[61,313],[9547]),([],[],[]),([3,3,1061],[3,5303],[3,1061]),([],[],[]),([9551],[3,6367],[9551]),([],[],[]),([41,233],[37,509],[41,233]),([],[],[]),([3,5,7,7,13],[3,7,647],[5,7,13]),([],[],[]),([19,503],[18593],[19,503]),([],[],[]),([11,11,79],[11,17,97],[11,79]),([],[],[]),([3,3187],[3,47,113],[3187]),([],[],[]),([73,131],[127,149],[73,131]),([],[],[]),([5,1913],[7,2459],[5,1913]),([],[],[]),([3,3,1063],[3,3,7,11,23],[1063]),([],[],[]),([7,1367],[5,11,17,19],[7,1367]),([],[],[]),([17,563],[19,977],[17,563]),([],[],[]),([3,3191],[7,43,53],[3,3191]),([],[],[]),([5,5,383],[5,11,313],[5,383]),([],[],[]),([61,157],[29,653],[61,157]),([],[],[]),([3,31,103],[3,5233],[31,103]),([],[],[]),([11,13,67],[11,37,43],[13,67]),([],[],[]),([7,37,37],[5,5,19,37],[7,37]),([],[],[]),([3,3,3,5,71],[3,3,5,5,5,13],[3,71]),([],[],[]),([9587],[3,7,11,83],[9587]),([],[],[]),([43,223],[18913],[43,223]),([],[],[]),([3,23,139],[3,23,227],[139]),([],[],[]),([53,181],[11,1723],[53,181]),([],[],[]),([5,19,101],[5,3359],[19,101]),([],[],[]),([3,7,457],[3,5023],[7,457]),([],[],[]),([29,331],[18839],[29,331])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range9600 (R D : ℕ) (lo : 9600 ≤ R) (hi : R < 9664) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 9600 64 R D [([],[],[]),([9601],[7,13,211],[9601]),([],[],[]),([3,3,11,97],[3,3,3,569],[11,97]),([],[],[]),([5,17,113],[3,5591],[5,17,113]),([],[],[]),([13,739],[37,499],[13,739]),([],[],[]),([3,3203],[67,239],[3,3203]),([],[],[]),([7,1373],[7,2549],[1373]),([],[],[]),([9613],[5,5,769],[9613]),([],[],[]),([3,5,641],[5,7,421],[3,641]),([],[],[]),([59,163],[19013],[59,163]),([],[],[]),([9619],[19237],[9619]),([],[],[]),([3,3,1069],[3,3,13,137],[1069]),([],[],[]),([9623],[3,5,1283],[9623]),([],[],[]),([5,5,5,7,11],[5,5,5,5,5,5],[7,11]),([],[],[]),([3,3209],[61,263],[3,3209]),([],[],[]),([9629],[3,7,7,131],[9629]),([],[],[]),([9631],[11,17,103],[9631]),([],[],[]),([3,13,13,19],[3,13,17,23],[13,19]),([],[],[]),([5,41,47],[3,5,11,103],[41,47]),([],[],[]),([23,419],[37,509],[23,419]),([],[],[]),([3,3,3,3,7,17],[3,3,3,3,3,61],[7,17]),([],[],[]),([31,311],[13,31,47],[311]),([],[],[]),([9643],[5,7,19,29],[9643]),([],[],[]),([3,5,643],[3,13,379],[5,643]),([],[],[]),([11,877],[79,233],[11,877]),([],[],[]),([9649],[23,839],[9649]),([],[],[]),([3,3217],[3,3,1787],[3217]),([],[],[]),([7,7,197],[5,7,7,73],[197]),([],[],[]),([5,1931],[5,5,5,139],[1931]),([],[],[]),([3,3,29,37],[3,3,5,349],[29,37]),([],[],[]),([13,743],[19,977],[13,743]),([],[],[]),([9661],[139,139],[9661]),([],[],[]),([3,3221],[16103],[3,3221])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range9664 (R D : ℕ) (lo : 9664 ≤ R) (hi : R < 9728) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 9664 64 R D [([],[],[]),([5,1933],[17393],[5,1933]),([],[],[]),([7,1381],[131,137],[7,1381]),([],[],[]),([3,11,293],[13,1193],[3,11,293]),([],[],[]),([19,509],[5,53,71],[19,509]),([],[],[]),([17,569],[73,257],[17,569]),([],[],[]),([3,3,5,5,43],[3,3,3,5,109],[5,43]),([],[],[]),([9677],[3,6451],[9677]),([],[],[]),([9679],[13,1489],[9679]),([],[],[]),([3,7,461],[3,3,3,563],[7,461]),([],[],[]),([23,421],[127,149],[23,421]),([],[],[]),([5,13,149],[103,163],[5,13,149]),([],[],[]),([3,3229],[3,5381],[3229]),([],[],[]),([9689],[3,3,2153],[9689]),([],[],[]),([11,881],[11,41,41],[881]),([],[],[]),([3,3,3,359],[3,3,11,163],[3,359]),([],[],[]),([5,7,277],[16319],[5,7,277]),([],[],[]),([9697],[11,41,43],[9697]),([],[],[]),([3,53,61],[3,3,7,11,23],[53,61]),([],[],[]),([89,109],[5,23,167],[89,109]),([],[],[]),([31,313],[11,1733],[31,313]),([],[],[]),([3,5,647],[107,139],[3,5,647]),([],[],[]),([17,571],[67,281],[17,571]),([],[],[]),([7,19,73],[5,13,269],[7,19,73]),([],[],[]),([3,3,13,83],[3,3,5,347],[13,83]),([],[],[]),([11,883],[43,431],[11,883]),([],[],[]),([5,29,67],[17107],[5,29,67]),([],[],[]),([3,41,79],[3,3,3,3,197],[41,79]),([],[],[]),([9719],[3,11,19,31],[9719]),([],[],[]),([9721],[19441],[9721]),([],[],[]),([3,7,463],[3,7,727],[463]),([],[],[]),([5,5,389],[5,13,269],[5,389]),([],[],[]),([71,137],[19,1013],[71,137])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range9728 (R D : ℕ) (lo : 9728 ≤ R) (hi : R < 9792) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 9728 64 R D [([],[],[]),([3,3,23,47],[3,23,229],[3,47]),([],[],[]),([37,263],[19163],[37,263]),([],[],[]),([9733],[5,17,229],[9733]),([],[],[]),([3,5,11,59],[5,5,5,5,23],[3,11,59]),([],[],[]),([7,13,107],[11,1579],[7,13,107]),([],[],[]),([9739],[19477],[9739]),([],[],[]),([3,17,191],[13,1217],[3,17,191]),([],[],[]),([9743],[3,3,5,433],[9743]),([],[],[]),([5,1949],[13,19,71],[5,1949]),([],[],[]),([3,3,3,19,19],[3,3,3,19,31],[19]),([],[],[]),([9749],[3,67,97],[9749]),([],[],[]),([7,7,199],[7,29,89],[7,199]),([],[],[]),([3,3251],[16253],[3,3251]),([],[],[]),([5,1951],[5,3511],[1951]),([],[],[]),([11,887],[18617],[11,887]),([],[],[]),([3,3253],[3,3,13,139],[3253]),([],[],[]),([43,227],[13,1481],[43,227]),([],[],[]),([13,751],[29,647],[13,751]),([],[],[]),([3,3,5,7,31],[3,3,5,313],[7,31]),([],[],[]),([9767],[3,17,383],[9767]),([],[],[]),([9769],[7,2791],[9769]),([],[],[]),([3,3257],[19,857],[3,3257]),([],[],[]),([29,337],[19181],[29,337]),([],[],[]),([5,5,17,23],[3,5,19,59],[5,17,23]),([],[],[]),([3,3259],[3,5431],[3259]),([],[],[]),([7,11,127],[7,2477],[11,127]),([],[],[]),([9781],[31,631],[9781]),([],[],[]),([3,3,1087],[3,3,1811],[1087]),([],[],[]),([5,19,103],[7,2447],[5,19,103]),([],[],[]),([9787],[23,23,37],[9787]),([],[],[]),([3,13,251],[3,19,277],[13,251]),([],[],[]),([9791],[3,61,107],[9791])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range9792 (R D : ℕ) (lo : 9792 ≤ R) (hi : R < 9856) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 9792 64 R D [([],[],[]),([7,1399],[18181],[7,1399]),([],[],[]),([3,5,653],[17,883],[3,5,653]),([],[],[]),([97,101],[7,17,163],[97,101]),([],[],[]),([41,239],[19319],[41,239]),([],[],[]),([3,3,3,3,11,11],[3,3,3,11,53],[3,11]),([],[],[]),([9803],[3,5,1307],[9803]),([],[],[]),([5,37,53],[17293],[5,37,53]),([],[],[]),([3,7,467],[3,3,29,59],[7,467]),([],[],[]),([17,577],[5,5,761],[17,577]),([],[],[]),([9811],[7,2803],[9811]),([],[],[]),([3,3271],[3,3,23,79],[3271]),([],[],[]),([5,13,151],[5,41,83],[13,151]),([],[],[]),([9817],[29,677],[9817]),([],[],[]),([3,3,1091],[3,7,19,41],[3,1091]),([],[],[]),([7,23,61],[113,157],[7,23,61]),([],[],[]),([11,19,47],[43,421],[11,19,47]),([],[],[]),([3,5,5,131],[5,5,601],[3,131]),([],[],[]),([31,317],[43,449],[31,317]),([],[],[]),([9829],[11,1787],[9829]),([],[],[]),([3,29,113],[16103],[3,29,113]),([],[],[]),([9833],[3,3,5,19,23],[9833]),([],[],[]),([5,7,281],[5,7,11,43],[281]),([],[],[]),([3,3,1093],[3,3,3,607],[1093]),([],[],[]),([9839],[3,7,937],[9839]),([],[],[]),([13,757],[18913],[13,757]),([],[],[]),([3,17,193],[3,73,73],[17,193]),([],[],[]),([5,11,179],[3,3,5,13,29],[11,179]),([],[],[]),([43,229],[19423],[43,229]),([],[],[]),([3,7,7,67],[3,7,733],[7,67]),([],[],[]),([9851],[3,3,11,199],[9851]),([],[],[]),([59,167],[7,11,11,23],[59,167]),([],[],[]),([3,3,3,5,73],[3,3,3,557],[5,73])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range9856 (R D : ℕ) (lo : 9856 ≤ R) (hi : R < 9920) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 9856 64 R D [([],[],[]),([9857],[3,6571],[9857]),([],[],[]),([9859],[19717],[9859]),([],[],[]),([3,19,173],[3,5351],[19,173]),([],[],[]),([7,1409],[18311],[7,1409]),([],[],[]),([5,1973],[41,433],[5,1973]),([],[],[]),([3,11,13,23],[3,3,3,3,11,17],[13,23]),([],[],[]),([71,139],[59,331],[71,139]),([],[],[]),([9871],[19,1039],[9871]),([],[],[]),([3,3,1097],[3,5483],[3,1097]),([],[],[]),([5,5,5,79],[5,5,7,101],[5,79]),([],[],[]),([7,17,83],[17749],[7,17,83]),([],[],[]),([3,37,89],[3,5,23,47],[37,89]),([],[],[]),([41,241],[7,11,11,23],[41,241]),([],[],[]),([9883],[5,59,67],[9883]),([],[],[]),([3,5,659],[15149],[3,5,659]),([],[],[]),([9887],[3,3,13,13,13],[9887]),([],[],[]),([11,29,31],[18289],[11,29,31]),([],[],[]),([3,3,7,157],[3,3,1723],[7,157]),([],[],[]),([13,761],[19013],[13,761]),([],[],[]),([5,1979],[17807],[5,1979]),([],[],[]),([3,3299],[16493],[3,3299]),([],[],[]),([19,521],[19259],[19,521]),([],[],[]),([9901],[19801],[9901]),([],[],[]),([3,3301],[3,5501],[3301]),([],[],[]),([5,7,283],[16673],[5,7,283]),([],[],[]),([9907],[19813],[9907]),([],[],[]),([3,3,3,367],[3,3,3,13,47],[367]),([],[],[]),([11,17,53],[3,59,103],[11,17,53]),([],[],[]),([23,431],[19373],[23,431]),([],[],[]),([3,5,661],[3,5,1013],[661]),([],[],[]),([47,211],[19577],[47,211]),([],[],[]),([7,13,109],[5,3539],[7,13,109])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range9920 (R D : ℕ) (lo : 9920 ≤ R) (hi : R < 9984) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 9920 64 R D [([],[],[]),([3,3307],[3,3,11,167],[3307]),([],[],[]),([9923],[3,3,3,3,5,7,7],[9923]),([],[],[]),([5,5,397],[5,43,83],[5,397]),([],[],[]),([3,3,1103],[3,37,149],[3,1103]),([],[],[]),([9929],[3,6619],[9929]),([],[],[]),([9931],[19861],[9931]),([],[],[]),([3,7,11,43],[3,7,23,31],[11,43]),([],[],[]),([5,1987],[19,941],[5,1987]),([],[],[]),([19,523],[19333],[19,523]),([],[],[]),([3,3313],[3,5521],[3313]),([],[],[]),([9941],[3,3,47,47],[9941]),([],[],[]),([61,163],[7,53,53],[61,163]),([],[],[]),([3,3,5,13,17],[3,3,3,7,7,11],[5,13,17]),([],[],[]),([7,7,7,29],[7,7,7,53],[29]),([],[],[]),([9949],[101,197],[9949]),([],[],[]),([3,31,107],[3,5437],[31,107]),([],[],[]),([37,269],[17,1153],[37,269]),([],[],[]),([5,11,181],[5,47,73],[11,181]),([],[],[]),([3,3319],[3,5531],[3319]),([],[],[]),([23,433],[19463],[23,433]),([],[],[]),([7,1423],[18493],[7,1423]),([],[],[]),([3,3,3,3,3,41],[3,3,3,3,7,29],[3,41]),([],[],[]),([5,1993],[79,227],[5,1993]),([],[],[]),([9967],[31,643],[9967]),([],[],[]),([3,3323],[37,449],[3,3323]),([],[],[]),([13,13,59],[7,11,13,19],[13,59]),([],[],[]),([9973],[5,3989],[9973]),([],[],[]),([3,5,5,7,19],[3,5,953],[5,7,19]),([],[],[]),([11,907],[19037],[11,907]),([],[],[]),([17,587],[5,7,7,79],[17,587]),([],[],[]),([3,3,1109],[3,23,241],[3,1109]),([],[],[]),([67,149],[19751],[67,149])] lo hi gt odd sf hd cop
  decide +kernel

set_option maxRecDepth 60000 in
set_option maxHeartbeats 6000000 in
private lemma range9984 (R D : ℕ) (lo : 9984 ≤ R) (hi : R < 10001) (gt : 1 < R) (odd : Odd R)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  apply sharp_block 9984 17 R D [([],[],[]),([5,1997],[7,17,151],[5,1997]),([],[],[]),([3,3329],[11,17,89],[3,3329]),([],[],[]),([7,1427],[5,3709],[7,1427]),([],[],[]),([97,103],[73,271],[97,103]),([],[],[]),([3,3331],[3,7,13,61],[3331]),([],[],[]),([5,1999],[17987],[5,1999]),([],[],[]),([13,769],[19213],[13,769]),([],[],[]),([3,3,11,101],[3,5333],[3,11,101]),([],[],[])] lo hi gt odd sf hd cop
  decide +kernel
lemma small_radicals (R D : ℕ) (gt : 1 < R) (odd : Odd R) (bound : R ≤ 10000)
    (sf : Squarefree R) (hd : D ∣ R) (cop : D.Coprime (R+R.totient)) :
    R.totient*D ≠ (R+R.totient).totient*D.totient := by
  by_cases h78 : R < 4992
  · by_cases h39 : R < 2496
    · by_cases h19 : R < 1216
      · by_cases h9 : R < 576
        · by_cases h4 : R < 256
          · by_cases h2 : R < 128
            · by_cases h1 : R < 64
              · exact range0 R D (by omega) (by omega) gt odd sf hd cop
              · exact range64 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h3 : R < 192
              · exact range128 R D (by omega) (by omega) gt odd sf hd cop
              · exact range192 R D (by omega) (by omega) gt odd sf hd cop
          · by_cases h6 : R < 384
            · by_cases h5 : R < 320
              · exact range256 R D (by omega) (by omega) gt odd sf hd cop
              · exact range320 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h7 : R < 448
              · exact range384 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h8 : R < 512
                · exact range448 R D (by omega) (by omega) gt odd sf hd cop
                · exact range512 R D (by omega) (by omega) gt odd sf hd cop
        · by_cases h14 : R < 896
          · by_cases h11 : R < 704
            · by_cases h10 : R < 640
              · exact range576 R D (by omega) (by omega) gt odd sf hd cop
              · exact range640 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h12 : R < 768
              · exact range704 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h13 : R < 832
                · exact range768 R D (by omega) (by omega) gt odd sf hd cop
                · exact range832 R D (by omega) (by omega) gt odd sf hd cop
          · by_cases h16 : R < 1024
            · by_cases h15 : R < 960
              · exact range896 R D (by omega) (by omega) gt odd sf hd cop
              · exact range960 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h17 : R < 1088
              · exact range1024 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h18 : R < 1152
                · exact range1088 R D (by omega) (by omega) gt odd sf hd cop
                · exact range1152 R D (by omega) (by omega) gt odd sf hd cop
      · by_cases h29 : R < 1856
        · by_cases h24 : R < 1536
          · by_cases h21 : R < 1344
            · by_cases h20 : R < 1280
              · exact range1216 R D (by omega) (by omega) gt odd sf hd cop
              · exact range1280 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h22 : R < 1408
              · exact range1344 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h23 : R < 1472
                · exact range1408 R D (by omega) (by omega) gt odd sf hd cop
                · exact range1472 R D (by omega) (by omega) gt odd sf hd cop
          · by_cases h26 : R < 1664
            · by_cases h25 : R < 1600
              · exact range1536 R D (by omega) (by omega) gt odd sf hd cop
              · exact range1600 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h27 : R < 1728
              · exact range1664 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h28 : R < 1792
                · exact range1728 R D (by omega) (by omega) gt odd sf hd cop
                · exact range1792 R D (by omega) (by omega) gt odd sf hd cop
        · by_cases h34 : R < 2176
          · by_cases h31 : R < 1984
            · by_cases h30 : R < 1920
              · exact range1856 R D (by omega) (by omega) gt odd sf hd cop
              · exact range1920 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h32 : R < 2048
              · exact range1984 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h33 : R < 2112
                · exact range2048 R D (by omega) (by omega) gt odd sf hd cop
                · exact range2112 R D (by omega) (by omega) gt odd sf hd cop
          · by_cases h36 : R < 2304
            · by_cases h35 : R < 2240
              · exact range2176 R D (by omega) (by omega) gt odd sf hd cop
              · exact range2240 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h37 : R < 2368
              · exact range2304 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h38 : R < 2432
                · exact range2368 R D (by omega) (by omega) gt odd sf hd cop
                · exact range2432 R D (by omega) (by omega) gt odd sf hd cop
    · by_cases h58 : R < 3712
      · by_cases h48 : R < 3072
        · by_cases h43 : R < 2752
          · by_cases h41 : R < 2624
            · by_cases h40 : R < 2560
              · exact range2496 R D (by omega) (by omega) gt odd sf hd cop
              · exact range2560 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h42 : R < 2688
              · exact range2624 R D (by omega) (by omega) gt odd sf hd cop
              · exact range2688 R D (by omega) (by omega) gt odd sf hd cop
          · by_cases h45 : R < 2880
            · by_cases h44 : R < 2816
              · exact range2752 R D (by omega) (by omega) gt odd sf hd cop
              · exact range2816 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h46 : R < 2944
              · exact range2880 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h47 : R < 3008
                · exact range2944 R D (by omega) (by omega) gt odd sf hd cop
                · exact range3008 R D (by omega) (by omega) gt odd sf hd cop
        · by_cases h53 : R < 3392
          · by_cases h50 : R < 3200
            · by_cases h49 : R < 3136
              · exact range3072 R D (by omega) (by omega) gt odd sf hd cop
              · exact range3136 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h51 : R < 3264
              · exact range3200 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h52 : R < 3328
                · exact range3264 R D (by omega) (by omega) gt odd sf hd cop
                · exact range3328 R D (by omega) (by omega) gt odd sf hd cop
          · by_cases h55 : R < 3520
            · by_cases h54 : R < 3456
              · exact range3392 R D (by omega) (by omega) gt odd sf hd cop
              · exact range3456 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h56 : R < 3584
              · exact range3520 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h57 : R < 3648
                · exact range3584 R D (by omega) (by omega) gt odd sf hd cop
                · exact range3648 R D (by omega) (by omega) gt odd sf hd cop
      · by_cases h68 : R < 4352
        · by_cases h63 : R < 4032
          · by_cases h60 : R < 3840
            · by_cases h59 : R < 3776
              · exact range3712 R D (by omega) (by omega) gt odd sf hd cop
              · exact range3776 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h61 : R < 3904
              · exact range3840 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h62 : R < 3968
                · exact range3904 R D (by omega) (by omega) gt odd sf hd cop
                · exact range3968 R D (by omega) (by omega) gt odd sf hd cop
          · by_cases h65 : R < 4160
            · by_cases h64 : R < 4096
              · exact range4032 R D (by omega) (by omega) gt odd sf hd cop
              · exact range4096 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h66 : R < 4224
              · exact range4160 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h67 : R < 4288
                · exact range4224 R D (by omega) (by omega) gt odd sf hd cop
                · exact range4288 R D (by omega) (by omega) gt odd sf hd cop
        · by_cases h73 : R < 4672
          · by_cases h70 : R < 4480
            · by_cases h69 : R < 4416
              · exact range4352 R D (by omega) (by omega) gt odd sf hd cop
              · exact range4416 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h71 : R < 4544
              · exact range4480 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h72 : R < 4608
                · exact range4544 R D (by omega) (by omega) gt odd sf hd cop
                · exact range4608 R D (by omega) (by omega) gt odd sf hd cop
          · by_cases h75 : R < 4800
            · by_cases h74 : R < 4736
              · exact range4672 R D (by omega) (by omega) gt odd sf hd cop
              · exact range4736 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h76 : R < 4864
              · exact range4800 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h77 : R < 4928
                · exact range4864 R D (by omega) (by omega) gt odd sf hd cop
                · exact range4928 R D (by omega) (by omega) gt odd sf hd cop
  · by_cases h117 : R < 7488
    · by_cases h97 : R < 6208
      · by_cases h87 : R < 5568
        · by_cases h82 : R < 5248
          · by_cases h80 : R < 5120
            · by_cases h79 : R < 5056
              · exact range4992 R D (by omega) (by omega) gt odd sf hd cop
              · exact range5056 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h81 : R < 5184
              · exact range5120 R D (by omega) (by omega) gt odd sf hd cop
              · exact range5184 R D (by omega) (by omega) gt odd sf hd cop
          · by_cases h84 : R < 5376
            · by_cases h83 : R < 5312
              · exact range5248 R D (by omega) (by omega) gt odd sf hd cop
              · exact range5312 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h85 : R < 5440
              · exact range5376 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h86 : R < 5504
                · exact range5440 R D (by omega) (by omega) gt odd sf hd cop
                · exact range5504 R D (by omega) (by omega) gt odd sf hd cop
        · by_cases h92 : R < 5888
          · by_cases h89 : R < 5696
            · by_cases h88 : R < 5632
              · exact range5568 R D (by omega) (by omega) gt odd sf hd cop
              · exact range5632 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h90 : R < 5760
              · exact range5696 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h91 : R < 5824
                · exact range5760 R D (by omega) (by omega) gt odd sf hd cop
                · exact range5824 R D (by omega) (by omega) gt odd sf hd cop
          · by_cases h94 : R < 6016
            · by_cases h93 : R < 5952
              · exact range5888 R D (by omega) (by omega) gt odd sf hd cop
              · exact range5952 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h95 : R < 6080
              · exact range6016 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h96 : R < 6144
                · exact range6080 R D (by omega) (by omega) gt odd sf hd cop
                · exact range6144 R D (by omega) (by omega) gt odd sf hd cop
      · by_cases h107 : R < 6848
        · by_cases h102 : R < 6528
          · by_cases h99 : R < 6336
            · by_cases h98 : R < 6272
              · exact range6208 R D (by omega) (by omega) gt odd sf hd cop
              · exact range6272 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h100 : R < 6400
              · exact range6336 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h101 : R < 6464
                · exact range6400 R D (by omega) (by omega) gt odd sf hd cop
                · exact range6464 R D (by omega) (by omega) gt odd sf hd cop
          · by_cases h104 : R < 6656
            · by_cases h103 : R < 6592
              · exact range6528 R D (by omega) (by omega) gt odd sf hd cop
              · exact range6592 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h105 : R < 6720
              · exact range6656 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h106 : R < 6784
                · exact range6720 R D (by omega) (by omega) gt odd sf hd cop
                · exact range6784 R D (by omega) (by omega) gt odd sf hd cop
        · by_cases h112 : R < 7168
          · by_cases h109 : R < 6976
            · by_cases h108 : R < 6912
              · exact range6848 R D (by omega) (by omega) gt odd sf hd cop
              · exact range6912 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h110 : R < 7040
              · exact range6976 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h111 : R < 7104
                · exact range7040 R D (by omega) (by omega) gt odd sf hd cop
                · exact range7104 R D (by omega) (by omega) gt odd sf hd cop
          · by_cases h114 : R < 7296
            · by_cases h113 : R < 7232
              · exact range7168 R D (by omega) (by omega) gt odd sf hd cop
              · exact range7232 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h115 : R < 7360
              · exact range7296 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h116 : R < 7424
                · exact range7360 R D (by omega) (by omega) gt odd sf hd cop
                · exact range7424 R D (by omega) (by omega) gt odd sf hd cop
    · by_cases h137 : R < 8768
      · by_cases h127 : R < 8128
        · by_cases h122 : R < 7808
          · by_cases h119 : R < 7616
            · by_cases h118 : R < 7552
              · exact range7488 R D (by omega) (by omega) gt odd sf hd cop
              · exact range7552 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h120 : R < 7680
              · exact range7616 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h121 : R < 7744
                · exact range7680 R D (by omega) (by omega) gt odd sf hd cop
                · exact range7744 R D (by omega) (by omega) gt odd sf hd cop
          · by_cases h124 : R < 7936
            · by_cases h123 : R < 7872
              · exact range7808 R D (by omega) (by omega) gt odd sf hd cop
              · exact range7872 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h125 : R < 8000
              · exact range7936 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h126 : R < 8064
                · exact range8000 R D (by omega) (by omega) gt odd sf hd cop
                · exact range8064 R D (by omega) (by omega) gt odd sf hd cop
        · by_cases h132 : R < 8448
          · by_cases h129 : R < 8256
            · by_cases h128 : R < 8192
              · exact range8128 R D (by omega) (by omega) gt odd sf hd cop
              · exact range8192 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h130 : R < 8320
              · exact range8256 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h131 : R < 8384
                · exact range8320 R D (by omega) (by omega) gt odd sf hd cop
                · exact range8384 R D (by omega) (by omega) gt odd sf hd cop
          · by_cases h134 : R < 8576
            · by_cases h133 : R < 8512
              · exact range8448 R D (by omega) (by omega) gt odd sf hd cop
              · exact range8512 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h135 : R < 8640
              · exact range8576 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h136 : R < 8704
                · exact range8640 R D (by omega) (by omega) gt odd sf hd cop
                · exact range8704 R D (by omega) (by omega) gt odd sf hd cop
      · by_cases h147 : R < 9408
        · by_cases h142 : R < 9088
          · by_cases h139 : R < 8896
            · by_cases h138 : R < 8832
              · exact range8768 R D (by omega) (by omega) gt odd sf hd cop
              · exact range8832 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h140 : R < 8960
              · exact range8896 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h141 : R < 9024
                · exact range8960 R D (by omega) (by omega) gt odd sf hd cop
                · exact range9024 R D (by omega) (by omega) gt odd sf hd cop
          · by_cases h144 : R < 9216
            · by_cases h143 : R < 9152
              · exact range9088 R D (by omega) (by omega) gt odd sf hd cop
              · exact range9152 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h145 : R < 9280
              · exact range9216 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h146 : R < 9344
                · exact range9280 R D (by omega) (by omega) gt odd sf hd cop
                · exact range9344 R D (by omega) (by omega) gt odd sf hd cop
        · by_cases h152 : R < 9728
          · by_cases h149 : R < 9536
            · by_cases h148 : R < 9472
              · exact range9408 R D (by omega) (by omega) gt odd sf hd cop
              · exact range9472 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h150 : R < 9600
              · exact range9536 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h151 : R < 9664
                · exact range9600 R D (by omega) (by omega) gt odd sf hd cop
                · exact range9664 R D (by omega) (by omega) gt odd sf hd cop
          · by_cases h154 : R < 9856
            · by_cases h153 : R < 9792
              · exact range9728 R D (by omega) (by omega) gt odd sf hd cop
              · exact range9792 R D (by omega) (by omega) gt odd sf hd cop
            · by_cases h155 : R < 9920
              · exact range9856 R D (by omega) (by omega) gt odd sf hd cop
              · by_cases h156 : R < 9984
                · exact range9920 R D (by omega) (by omega) gt odd sf hd cop
                · exact range9984 R D (by omega) (by omega) gt odd sf hd cop

/-- Beyond the checked radical bound, exclude squarefree odd fixed points. -/
def H1 : Prop := ∀ R : ℕ, 10000 < R → Odd R → Squarefree R →
    R.totient ≠ (R+R.totient).totient

/-- Beyond the same bound, the remaining divisor is nontrivial and must be coprime
to the shifted radical. The two scalar conditions exclude radicals before any divisor needs to be tested. -/
def H2 : Prop := ∀ R : ℕ, 10000 < R → Odd R → Squarefree R →
    let U := R+R.totient
    let Q := R/(R.gcd U)
    U.totient ∣ R.totient*Q → U.totient*Q.totient ≤ R.totient*Q → R.totient < U.totient →
    ∀ D : ℕ, 1 < D → D ∣ R → D.Coprime (R+R.totient) →
      R.totient*D ≠ (R+R.totient).totient*D.totient

theorem main : H1 → H2 → type_of% @OeisA108569.conjecture := by
  intro h₁ h₂
  have noOdd (n : ℕ) (hn : 1 < n) (odd : Odd n) (ha : OeisA108569.A n) : False := by
    obtain ⟨R,D,_,gt,oddR,sf,hd,cop,eq⟩ := normalize n hn odd ha.2
    by_cases cap : R ≤ 10000
    · exact small_radicals R D gt oddR cap sf hd cop eq
    have dg : 0 < D := Nat.pos_of_dvd_of_pos hd (by omega)
    by_cases one : D=1
    · subst D
      apply h₁ R (by omega) oddR sf
      simpa using eq
    have tests := scalar_filter R D (by omega) sf hd cop eq
    have lt : R.totient < (R+R.totient).totient := by
      have dt := Nat.totient_lt D (by omega : 1 < D)
      have up := Nat.totient_pos.mpr (by omega : 0 < R+R.totient)
      have strict := Nat.mul_lt_mul_of_pos_left dt up
      rw [← eq] at strict
      exact (Nat.mul_lt_mul_right dg).mp strict
    exact h₂ R (by omega) oddR sf tests.2.1 tests.2.2 lt D (by omega) hd cop eq
  intro i hi
  change Even (Nat.nth OeisA108569.A i)
  by_contra he
  have ne : Nat.nth OeisA108569.A i ≠ 0 := by
    intro eq
    exact he (eq ▸ Even.zero)
  have mem := Nat.nth_mem_of_ne_zero ne
  have gt : 1 < Nat.nth OeisA108569.A i := by
    have pos := mem.1
    by_contra! le
    have one : Nat.nth OeisA108569.A i = 1 := by omega
    have idx := Nat.count_nth (Nat.lt_card_toFinset_of_nth_ne_zero ne)
    rw [one,show Nat.count OeisA108569.A 1 = 0 by decide] at idx
    omega
  exact noOdd _ gt (Nat.not_even_iff_odd.mp he) mem

end OMA.R_OeisA108569_conjecture_R3
