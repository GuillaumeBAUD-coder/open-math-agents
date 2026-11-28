import OMAReductions.R_OeisA245211_conjecture_R3

/-!
A Lean certificate for the least-prime 433 classification for OEIS A245211.
The earlier two exact Python searches and many of the Lucas certificates are due
to DomTheDeveloper (ProofPlaygrond, A245211, least-prime-443). The parent
reduction formalized the divisor budget and the cut gcd. Here the calculations
are reduced with the kernel and linked to the original divisor-sum definition.

At a fixed point the full moment factors into local weighted geometric sums.
After choosing the least prime, enumerate a sorted multiset of remaining positive
exponents with their divisor budget. A forced prime divides the reduced numerator
of the prefix moment. Small-modulus obstructions, a monotone rational bound and
exact recovery of the last prime complete the finite search. The integer tables
select potential witnesses and trial widths; every elimination uses their checked
arithmetic properties. Degenerate large-exponent tails are dispatched by
separating the rational part of the leading prime-power moment.

The threshold 433 applies to the least prime factor.
-/

namespace Div245
open Finset OeisA245211

/- The common moment identities are from the parent reduction by @DomTheDeveloper. -/
theorem moment_eq {x : ℕ} (hx : x ≠ 0) :
    (∑ d ∈ x.divisors, d * d.divisors.card) = a x + x * x.divisors.card := by
  conv_lhs => rw [← Nat.insert_self_properDivisors hx, sum_insert Nat.self_notMem_properDivisors]
  simp [a, add_comm]

theorem moment_mul {x y : ℕ} (h : x.Coprime y) :
    (∑ d ∈ (x*y).divisors, d * d.divisors.card) = (∑ d ∈ x.divisors, d * d.divisors.card) * (∑ d ∈ y.divisors, d * d.divisors.card) := by
  rw [h.divisors_mul, sum_map]
  change (∑ z ∈ (x.divisors ×ˢ y.divisors).attach,
    z.val.1 * z.val.2 * (z.val.1 * z.val.2).divisors.card) = _
  rw [sum_attach (f := fun z : ℕ × ℕ => z.1*z.2*(z.1*z.2).divisors.card),
    sum_product, sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [((h.coprime_dvd_left (Nat.dvd_of_mem_divisors hi)).coprime_dvd_right
    (Nat.dvd_of_mem_divisors hj)).card_divisors_mul]
  ring

theorem a_pos {x : ℕ} (hx : 1 < x) : 0 < a x := by
  have h := Finset.single_le_sum (f := fun d : ℕ => d*d.divisors.card)
    (fun _ _ => Nat.zero_le _) (Nat.one_mem_properDivisors_iff_one_lt.mpr hx)
  change 1 ≤ _
  simpa [a] using h

theorem card_pos {x : ℕ} (hx : 0 < x) : 0 < x.divisors.card :=
  Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hx.ne'⟩

theorem card_two {x : ℕ} (hx : 1 < x) : 2 ≤ x.divisors.card := by
  have h := card_pos (by omega : 0 < x)
  have h' : x.divisors.card ≠ 1 := fun e => (by omega : x ≠ 1) ((Nat.divisors_card_eq_one_iff x).mp e)
  omega

theorem card_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (p^e).divisors.card = e+1 := by simp [Nat.divisors_prime_pow hp]


theorem cut_balance {x y : ℕ} (hx : 0 < x) (hy : 0 < y)
    (hc : x.Coprime y) (hf : a (x*y) = x*y) :
    (∑ d ∈ x.divisors, d * d.divisors.card) * a y + y * y.divisors.card * a x = x*y := by
  have h := moment_mul hc
  rw [moment_eq (Nat.mul_pos hx hy).ne', hf, hc.card_divisors_mul, moment_eq hy.ne'] at h
  rw [moment_eq hx.ne'] at h ⊢
  nlinarith only [h]


theorem prime_moment {p : ℕ} (hp : p.Prime) : (∑ d ∈ p.divisors, d * d.divisors.card) = 2*p+1 := by
  simp [hp.divisors, Ne.symm hp.ne_one, mul_comm, add_comm]


theorem moment_fixed {n : ℕ} (hn : 0 < n) (hf : a n = n) :
    (∑ d ∈ n.divisors, d * d.divisors.card) = n*(n.divisors.card+1) := by
  rw [moment_eq hn.ne', hf]
  ring

theorem moment_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (∑ d ∈ (p^e).divisors, d*d.divisors.card) =
      ∑ j ∈ Finset.range (e+1), (j+1)*p^j := by
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro j _
  change p^j*(p^j).divisors.card = _
  rw [card_pow hp]
  ring

end Div245

open Finset OeisA245211
namespace Div245

theorem pattern_products (L : List (ℕ × ℕ))
    (hs : L.Pairwise (fun z w => z.1 < w.1))
    (hp : ∀ z ∈ L, z.1.Prime) :
    ((L.map (fun z : ℕ × ℕ => z.1^z.2)).prod).divisors.card =
        (L.map (fun z => z.2+1)).prod ∧
    (∑ d ∈ ((L.map (fun z : ℕ × ℕ => z.1^z.2)).prod).divisors, d*d.divisors.card) =
        (L.map (fun z => ∑ j ∈ Finset.range (z.2+1), (j+1)*z.1^j)).prod := by
  induction L with
  | nil => simp
  | cons z L ih =>
    obtain ⟨hz,ht⟩ := List.pairwise_cons.mp hs
    have hpz := hp z (List.mem_cons_self ..)
    have hpt : ∀ w ∈ L, w.1.Prime := fun w hw => hp w (List.mem_cons_of_mem _ hw)
    obtain ⟨hD,hM⟩ := ih ht hpt
    have hc : (z.1^z.2).Coprime ((L.map (fun w => w.1^w.2)).prod) := by
      apply Nat.coprime_list_prod_right_iff.mpr
      intro t h
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp h
      exact Nat.coprime_pow_primes _ _ hpz (hpt w hw) (hz w hw).ne
    simp only [List.map_cons, List.prod_cons, hc.card_divisors_mul, moment_mul hc,
      card_pow hpz, moment_pow hpz, hD, hM, and_self]

theorem fixed_pattern {n : ℕ} (hn : 1 < n) (hf : a n = n) :
    ∃ L : List (ℕ × ℕ),
      L.Pairwise (fun z w => z.1 < w.1) ∧
      (∀ z ∈ L, z.1.Prime ∧ 0 < z.2 ∧ z.2 = n.factorization z.1 ∧ n.minFac ≤ z.1) ∧
      (∃ e, (n.minFac,e) ∈ L) ∧
      n = (L.map (fun z : ℕ × ℕ => z.1^z.2)).prod ∧
      n.divisors.card = (L.map (fun z => z.2+1)).prod ∧
      (L.map (fun z => ∑ j ∈ Finset.range (z.2+1), (j+1)*z.1^j)).prod =
        n*((L.map (fun z => z.2+1)).prod+1) := by
  let S := n.primeFactors.sort
  let L := S.map (fun p => (p,n.factorization p))
  have hn0 : n ≠ 0 := by omega
  have hs : L.Pairwise (fun z w => z.1 < w.1) :=
    List.pairwise_map.mpr n.primeFactors.sortedLT_sort.pairwise
  have hp : ∀ z ∈ L, z.1.Prime ∧ 0 < z.2 ∧ z.2 = n.factorization z.1 ∧ n.minFac ≤ z.1 := by
    intro z hz
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hz
    have h := Nat.mem_primeFactors.mp ((n.primeFactors.mem_sort _).mp hp)
    exact ⟨h.1, h.1.factorization_pos_of_dvd hn0 h.2.1, rfl, Nat.minFac_le_of_dvd h.1.two_le h.2.1⟩
  have hmin : n.minFac ∈ S := (n.primeFactors.mem_sort _).mpr
    (Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd n, hn0⟩)
  have hN : n = (L.map (fun z : ℕ × ℕ => z.1^z.2)).prod := by
    change n = ((S.map (fun p => (p,n.factorization p))).map _).prod
    simp only [List.map_map]
    exact (Nat.prod_primeFactors_pow_factorization hn0).trans
      ((n.primeFactors.prod_map_toList (fun p => p^n.factorization p)).symm.trans
        (((n.primeFactors.sort_perm_toList (· ≤ ·)).map (fun p => p^n.factorization p)).prod_eq.symm))
  obtain ⟨hD,hM⟩ := pattern_products L hs (fun z hz => (hp z hz).1)
  rw [← hN] at hD hM
  exact ⟨L,hs,hp,⟨_,List.mem_map.mpr ⟨_,hmin,rfl⟩⟩,hN,hD,
    hM.symm.trans (by rw [moment_fixed (by omega) hf, hD])⟩

end Div245

/- Prime-factor closure and a finite classification of squarefree divisor-moment fixed points. -/

namespace Div245
open Finset OeisA245211

/-- The full moment and divisor count for a product of distinct primes. -/
theorem squarefree_product_data (s : Finset ℕ) (hp : ∀ p ∈ s, Nat.Prime p) :
    (∑ d ∈ (∏ p ∈ s, p).divisors, d*d.divisors.card) = (∏ p ∈ s, (2*p+1)) ∧
    (∏ p ∈ s, p).divisors.card = 2^s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hs ih =>
    have hP := hp p (mem_insert_self _ _)
    have hQ : ∀ q ∈ s, Nat.Prime q := fun q hq => hp q (mem_insert_of_mem hq)
    have hc : p.Coprime (∏ q ∈ s, q) := Nat.coprime_prod_right_iff.mpr fun q hq =>
      (Nat.coprime_primes hP (hQ q hq)).mpr (fun h => hs (h ▸ hq))
    obtain ⟨hM,hD⟩ := ih hQ
    rw [prod_insert hs, prod_insert hs, card_insert_of_notMem hs, moment_mul hc,
      prime_moment hP, hM, hc.card_divisors_mul, hD]
    exact ⟨rfl, by simp [hP.divisors, Ne.symm hP.ne_one, pow_succ, mul_comm]⟩

/-- A set closed under prime divisors of 2p+1 above the least prime contains
the entire support of a squarefree fixed point. -/
theorem squarefree_support_closed {n : ℕ} (hn : 1 < n) (hsq : Squarefree n) (hf : a n = n)
    (C : Finset ℕ) (start : n.minFac ∈ C)
    (closed : ∀ p ∈ C, ∀ q ∈ (2*p+1).primeFactors, n.minFac ≤ q → q ∈ C) :
    n.primeFactors ⊆ C := by
  let S := n.primeFactors ∩ C
  let R := n.primeFactors \ S
  let x := ∏ p ∈ S, p
  let y := ∏ p ∈ R, p
  have hS {p} (h : p ∈ S) : p ∈ n.primeFactors := (mem_inter.mp h).1
  have hR {p} (h : p ∈ R) : p ∈ n.primeFactors := (mem_sdiff.mp h).1
  have ps {p} (h : p ∈ S) := Nat.prime_of_mem_primeFactors (hS h)
  have pr {p} (h : p ∈ R) := Nat.prime_of_mem_primeFactors (hR h)
  have xpos : 0 < x := Finset.prod_pos fun p h => (ps h).pos
  have ypos : 0 < y := Finset.prod_pos fun p h => (pr h).pos
  have hxy : x*y=n := by
    change (∏ p ∈ S,p)*(∏ p ∈ n.primeFactors \ S,p)=n
    rw [mul_comm, prod_sdiff (show S ⊆ n.primeFactors from fun _ h => hS h),
      Nat.prod_primeFactors_of_squarefree hsq]
  have cop : x.Coprime y := Nat.coprime_prod_left_iff.mpr fun p hp =>
    Nat.coprime_prod_right_iff.mpr fun q hq => (Nat.coprime_primes (ps hp) (pr hq)).mpr
      fun h => (mem_sdiff.mp hq).2 (h ▸ hp)
  have p0 := Nat.minFac_prime (show n ≠ 1 by omega)
  have pS : n.minFac ∈ S := mem_inter.mpr ⟨p0.mem_primeFactors (Nat.minFac_dvd _) (by omega), start⟩
  have x1 := p0.one_lt.trans_le (Nat.le_of_dvd xpos (Finset.dvd_prod_of_mem (fun p : ℕ => p) pS))
  intro t ht
  by_contra hnot
  have htr : t ∈ R := mem_sdiff.mpr ⟨ht, fun h => hnot (mem_inter.mp h).2⟩
  have y1 := (pr htr).one_lt.trans_le
    (Nat.le_of_dvd ypos (Finset.dvd_prod_of_mem (fun p : ℕ => p) htr))
  have cut := OMA.R_OeisA245211_conjecture_R3.cut_gcd x1 y1 cop (by simpa only [hxy] using hf)
  have M := (squarefree_product_data S fun _ h => ps h).1
  change (∑ d ∈ x.divisors, d*d.divisors.card) = _ at M
  rw [M] at cut
  have cm : y.Coprime (∏ p ∈ S, (2*p+1)) := Nat.coprime_prod_left_iff.mpr fun q hq =>
    Nat.coprime_prod_right_iff.mpr fun p hp => (pr hq).coprime_iff_not_dvd.mpr fun divides =>
      (mem_sdiff.mp hq).2 (mem_inter.mpr ⟨hR hq, closed p (mem_inter.mp hp).2 q
        ((pr hq).mem_primeFactors divides (by omega))
        (Nat.minFac_le_of_dvd (pr hq).two_le (Nat.dvd_of_mem_primeFactors (hR hq)))⟩)
  rw [cm.gcd_eq_one] at cut
  have := card_pos xpos
  omega

/-- Squarefree fixed points whose least prime is at most 433 are completely classified. -/
theorem squarefree_fixed_433 {n : ℕ} (hn : 1 < n) (bound : n.minFac ≤ 433)
    (hsq : Squarefree n) (hf : a n = n) : n = 21 := by
  let C (p : ℕ) : Finset ℕ :=
    if p = 2 then {2, 3, 5, 7, 11, 13, 19, 23, 47} else
    if p = 3 then {3, 5, 7, 11, 13, 19, 23, 47} else
    if p = 5 then {5, 11, 13, 19, 23, 47} else
    if p = 11 then {11, 13, 19, 23, 47} else
    if p = 23 then {23, 47} else
    if p = 29 then {29, 59} else
    if p = 41 then {41, 67, 83, 167} else
    if p = 53 then {53, 107} else
    if p = 83 then {83, 167} else
    if p = 89 then {89, 179, 359, 443, 719, 887, 1439, 2879} else
    if p = 113 then {113, 227} else
    if p = 131 then {131, 263} else
    if p = 173 then {173, 347} else
    if p = 179 then {179, 359, 443, 719, 887, 1439, 2879} else
    if p = 191 then {191, 383} else
    if p = 233 then {233, 467} else
    if p = 239 then {239, 479} else
    if p = 251 then {251, 503} else
    if p = 281 then {281, 563} else
    if p = 293 then {293, 587} else
    if p = 359 then {359, 443, 719, 887, 1439, 2879} else
    if p = 419 then {419, 839} else
    if p = 431 then {431, 863} else
    {p}
  have check : (List.range 434).all (fun p => if p.Prime then decide
      (p ∈ C p ∧ ((C p).biUnion (fun u => (2*u+1).primeFactors.filter (p ≤ ·))) ⊆ C p ∧
      ((C p).powerset.filter (fun s => (∏ u ∈ s, (2*u+1)) = (∏ u ∈ s, u)*(2^s.card+1) ∧
        (∏ u ∈ s, u) ≠ 21)) = ∅)
      else true) = true := by decide +kernel
  have hcheck := List.all_eq_true.mp check n.minFac (List.mem_range.mpr (by omega))
  rw [if_pos (Nat.minFac_prime (show n ≠ 1 by omega))] at hcheck
  obtain ⟨start,edges,good⟩ := of_decide_eq_true hcheck
  have sub := squarefree_support_closed hn hsq hf (C n.minFac) start (fun u hu q hq hle =>
    edges (Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_filter.mpr ⟨hq,hle⟩⟩))
  have product := Nat.prod_primeFactors_of_squarefree hsq
  obtain ⟨mom,count⟩ := squarefree_product_data n.primeFactors
    (fun _ h => Nat.prime_of_mem_primeFactors h)
  rw [product] at mom count
  have eq := moment_fixed (show 0<n by omega) hf
  rw [mom,count] at eq
  by_contra ne
  have bad : n.primeFactors ∈ (C n.minFac).powerset.filter (fun s =>
      (∏ u ∈ s, (2*u+1)) = (∏ u ∈ s, u)*(2^s.card+1) ∧ (∏ u ∈ s, u) ≠ 21) :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr sub, by simpa only [product] using And.intro eq ne⟩
  rw [good] at bad
  exact Finset.notMem_empty _ bad

end Div245

/- Modular obstructions to a fixed divisor moment. -/
namespace Div245
open Finset

theorem poly_mod_congr {u v m : ℕ} (h : u ≡ v [MOD m]) (e : ℕ) :
    (∑ j ∈ range (e+1), (j+1)*u^j) ≡ (∑ j ∈ range (e+1), (j+1)*v^j) [MOD m] := by
  induction e with
  | zero => simp; rfl
  | succ e ih =>
    rw [Finset.sum_range_succ _ (e+1), Finset.sum_range_succ _ (e+1)]
    exact ih.add ((h.pow (e+1)).mul_left _)

theorem eligible_power (q : ℕ) (hq : q.Coprime 6) : q^24 ≡ 1 [MOD 288] := by
  have h : (q%288).Coprime 6 := by
    rw [Nat.coprime_iff_gcd_eq_one] at *
    exact (((Nat.mod_modEq q 288).of_dvd (by decide : 6 ∣ 288)).gcd_eq).trans hq
  have htab : ∀ i : Fin 288, i.val.Coprime 6 → i.val^24 % 288 = 1 := by decide +kernel
  exact ((Nat.mod_modEq q 288).symm.pow 24).trans (htab ⟨_, Nat.mod_lt q (by decide)⟩ h)

theorem normalized_product {L : List (ℕ × ℕ)} (m : ℕ) (hm : m ∣ 288)
    (hu : ∀ z ∈ L, z.1.Coprime 6)
    (hM : (L.map (fun z => ∑ j ∈ range (z.2+1), (j+1)*z.1^j)).prod =
      (L.map (fun z => z.1^z.2)).prod * ((L.map (fun z => z.2+1)).prod+1)) :
    (L.map (fun z => (∑ j ∈ range (z.2+1), (j+1)*z.1^j) * z.1^(23*z.2))).prod
      ≡ ((L.map (fun z => z.2+1)).prod+1) [MOD m] := by
  have aux (S : List (ℕ × ℕ)) (good : ∀ z ∈ S, z.1.Coprime 6) :
      (S.map (fun z => z.1^z.2)).prod * (S.map (fun z => z.1^(23*z.2))).prod ≡ 1 [MOD m] := by
    induction S with
    | nil => rfl
    | cons z S ih =>
      have hp := ((eligible_power z.1 (good z (by simp))).of_dvd hm).pow z.2
      rw [← pow_mul, one_pow] at hp
      simp only [List.map_cons, List.prod_cons]
      rw [mul_mul_mul_comm, ← pow_add, show z.2+23*z.2=24*z.2 by omega]
      simpa using hp.mul (ih (fun w hw => good w (List.mem_cons_of_mem _ hw)))
  rw [List.prod_map_mul, hM]
  rw [mul_right_comm, Nat.mul_comm _ ((L.map (fun z => z.2+1)).prod+1)]
  simpa using (aux L hu).mul_left ((L.map (fun z => z.2+1)).prod+1)

theorem normalized_residue {L : List (ℕ × ℕ)} {m : ℕ} (hm : m ∣ 288) (hpos : 0 < m)
    (hu : ∀ z ∈ L, z.1.Coprime 6)
    (hM : (L.map (fun z => ∑ j ∈ range (z.2+1), (j+1)*z.1^j)).prod =
      (L.map (fun z => z.1^z.2)).prod * ((L.map (fun z => z.2+1)).prod+1)) :
    let vals := fun e : ℕ => ((List.range m).filter (fun q => q^24 % m == 1 % m)).map
      (fun q => ((∑ j ∈ range (e+1), (j+1)*q^j) * q^(23*e)) % m)
    let poss := fun es : List ℕ => es.foldr (fun e (s : List ℕ) =>
      ((vals e).flatMap (fun v => s.map (fun x => v*x%m))).eraseDups) [1%m]
    ((L.map (fun z => z.2+1)).prod+1) % m ∈ poss (L.map Prod.snd) := by
  intro vals poss
  let f (z : ℕ × ℕ) := (∑ j ∈ range (z.2+1), (j+1)*z.1^j) * z.1^(23*z.2)
  have inc (S : List (ℕ × ℕ)) (good : ∀ z ∈ S, z.1.Coprime 6) :
      (S.map f).prod % m ∈ poss (S.map Prod.snd) := by
    induction S with
    | nil => simp [poss]
    | cons z S ih =>
      have hp := (eligible_power z.1 (good z (by simp))).of_dvd hm
      have hq : z.1 % m ≡ z.1 [MOD m] := Nat.mod_modEq _ _
      have hv : f z % m ∈ vals z.2 := by
        apply List.mem_map.mpr
        refine ⟨z.1 % m, List.mem_filter.mpr ⟨List.mem_range.mpr (Nat.mod_lt _ hpos), ?_⟩, ?_⟩
        · exact beq_iff_eq.mpr ((hq.pow 24).trans hp)
        · exact (poly_mod_congr hq z.2).mul (hq.pow (23*z.2))
      change _ ∈ List.eraseDups _
      rw [List.mem_eraseDups]
      apply List.mem_flatMap.mpr
      refine ⟨_,hv,List.mem_map.mpr ⟨_,ih (fun w hw => good w (List.mem_cons_of_mem _ hw)),?_⟩⟩
      exact (Nat.mul_mod ..).symm
  have h := inc L hu
  have hh : (L.map f).prod % m = _ := normalized_product m hm hu hM
  rwa [hh] at h

end Div245

/- Bounded even exponent lists for square inputs. -/
namespace Div245

theorem even_pattern_length {es : List ℕ} (he : ∀ e ∈ es, 2 ≤ e)
    (hb : (es.map (·+1)).prod ≤ 864) : es.length ≤ 6 := by
  have low (s : List ℕ) (hs : ∀ e ∈ s, 2 ≤ e) : 3^s.length ≤ (s.map (·+1)).prod := by
    induction s with
    | nil => simp
    | cons e s ih =>
      simp only [List.length_cons, pow_succ', List.map_cons, List.prod_cons]
      exact Nat.mul_le_mul (by have := hs e (by simp); omega)
        (ih (fun j hj => hs j (List.mem_cons_of_mem _ hj)))
  by_contra! hh
  have := (Nat.pow_le_pow_right (by decide : 0 < 3) (show 7 ≤ es.length by omega)).trans
    ((low es he).trans hb)
  norm_num at this

theorem even_pattern_mem {es : List ℕ} {B k : ℕ} (he : ∀ e ∈ es, 0 < e ∧ Even e)
    (hb : (es.map (·+1)).prod ≤ B) (hl : es.length ≤ k) :
    let gen := Nat.rec (motive := fun _ => ℕ → List (List ℕ)) (fun _ => [[]])
      (fun _ tail b => [] :: (List.range ((b-1)/2)).flatMap (fun i =>
        let e := 2*(i+1)
        (tail (b/(e+1))).map (e::·))) k
    es ∈ gen B := by
  induction k generalizing es B with
  | zero => have : es = [] := List.eq_nil_of_length_eq_zero (by omega); subst es; simp
  | succ k ih =>
    cases es with
    | nil => exact List.mem_cons_self ..
    | cons e es =>
      have ho := he e (by simp)
      obtain ⟨j,hj⟩ := ho.2
      have rep : e = 2*((j-1)+1) := by omega
      have hpos : 0 < (es.map (·+1)).prod :=
        List.prod_pos (by intro x hx; obtain ⟨z,_,rfl⟩ := List.mem_map.mp hx; omega)
      change (e+1)*(es.map (·+1)).prod ≤ B at hb
      have hbe : e+1 ≤ B := (Nat.le_mul_of_pos_right _ hpos).trans hb
      apply List.mem_cons_of_mem
      apply List.mem_flatMap.mpr
      refine ⟨j-1,List.mem_range.mpr (by omega),?_⟩
      apply List.mem_map.mpr
      refine ⟨es, ?_, by rw [← rep]⟩
      rw [← rep]
      apply ih (fun j hj => he j (List.mem_cons_of_mem _ hj))
      · exact (Nat.le_div_iff_mul_le (by omega : 0 < e+1)).mpr (by rwa [Nat.mul_comm])
      · simpa only [List.length_cons, Nat.add_le_add_iff_right] using hl

end Div245

namespace Div245
open Finset

/- No list of at least three even positive exponents with divisor count at most 864
    can satisfy the moment identity on bases coprime to six. -/
set_option maxRecDepth 32000 in
set_option maxHeartbeats 10000000 in
theorem no_even_pattern (L : List (ℕ × ℕ)) (hu : ∀ z ∈ L, z.1.Coprime 6)
    (he : ∀ z ∈ L, 0 < z.2 ∧ Even z.2) (hL : 3 ≤ L.length)
    (hD : (L.map (fun z => z.2+1)).prod ≤ 864)
    (hM : (L.map (fun z => ∑ j ∈ range (z.2+1), (j+1)*z.1^j)).prod =
      (L.map (fun z => z.1^z.2)).prod * ((L.map (fun z => z.2+1)).prod+1)) : False := by
  let es := L.map Prod.snd
  let gen := Nat.rec (motive := fun _ => ℕ → List (List ℕ)) (fun _ => [[]])
    (fun _ tail b => [] :: (List.range ((b-1)/2)).flatMap (fun i =>
      let e := 2*(i+1)
      (tail (b/(e+1))).map (e::·))) 6
  let vals (m e : ℕ) := ((List.range m).filter (fun q => q^24 % m == 1 % m)).map
    (fun q => ((∑ j ∈ range (e+1), (j+1)*q^j) * q^(23*e)) % m)
  let poss (m : ℕ) (s : List ℕ) := s.foldr (fun e (t : List ℕ) =>
    ((vals m e).flatMap (fun v => t.map (fun x => v*x%m))).eraseDups) [1%m]
  let mods := [3,2,4,8,9,16,32]
  let test (s : List ℕ) := s.length < 3 || mods.any (fun m =>
    !(poss m s).contains (((s.map (·+1)).prod+1) % m))
  have check : (gen 864).all test := by decide +kernel
  have ev : ∀ e ∈ es, 0 < e ∧ Even e := by
    intro e hm
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hm
    exact he z hz
  have e2 : ∀ e ∈ es, 2 ≤ e := by
    intro e hm
    obtain ⟨h,⟨i,hi⟩⟩ := ev e hm
    omega
  have bd : (es.map (·+1)).prod ≤ 864 := by simpa [es,List.map_map,Function.comp_def] using hD
  have len : 3 ≤ es.length := by simpa [es] using hL
  have ht := List.all_eq_true.mp check es (even_pattern_mem ev bd (even_pattern_length e2 bd))
  change (decide (es.length < 3) || mods.any _) = true at ht
  rcases Bool.or_eq_true_iff.mp ht with absurd | wit
  · exact (by omega : ¬es.length < 3) (of_decide_eq_true absurd)
  · obtain ⟨m,hm,r⟩ := List.any_eq_true.mp wit
    have oks : mods.all (fun x => decide (x ∣ 288 ∧ 0 < x)) := by decide
    obtain ⟨hd,hp⟩ := of_decide_eq_true (List.all_eq_true.mp oks m hm)
    have incl := normalized_residue hd hp hu hM
    change _ ∈ poss m es at incl
    have htarg : (es.map (·+1)).prod = (L.map (fun z => z.2+1)).prod := by
      simp [es,List.map_map,Function.comp_def]
    rw [← htarg] at incl
    have := List.contains_iff_mem.mpr incl
    simp_all

end Div245

/- A parity restriction for nonsquare exponent patterns. -/
namespace Div245
open Finset

theorem moment_triangular_mod_two (e : ℕ) :
    (∑ j ∈ range (e+1), (j+1)) % 2 = if e%4 < 2 then 1 else 0 := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases hs : e < 4
    · interval_cases e <;> decide
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 4 ≤ e)
      have hpre := ih k (by omega)
      have shift : (∑ j ∈ range (4+k+1), (j+1)) =
          (∑ j ∈ range (k+1), (j+1)) + 2*(2*k+7) := by
        rw [show 4+k+1 = k+1+1+1+1+1 by omega,
          sum_range_succ _ (k+1+1+1+1), sum_range_succ _ (k+1+1+1),
          sum_range_succ _ (k+1+1), sum_range_succ _ (k+1)]
        omega
      rw [shift, show (4+k)%4 = k%4 by omega]
      omega

theorem nonsquare_parity {L : List (ℕ × ℕ)} (hu : ∀ z ∈ L, z.1.Coprime 6)
    (oddExponent : ∃ z ∈ L, Odd z.2)
    (hM : (L.map (fun z => ∑ j ∈ range (z.2+1), (j+1)*z.1^j)).prod =
      (L.map (fun z => z.1^z.2)).prod * ((L.map (fun z => z.2+1)).prod+1)) :
    ∀ z ∈ L, z.2%4 < 2 := by
  obtain ⟨w,hw,k,hk⟩ := oddExponent
  let D := (L.map (fun z => z.2+1)).prod
  have wd : w.2+1 ∣ D := List.dvd_prod (List.mem_map.mpr ⟨w, hw, rfl⟩)
  have hd : 2 ∣ D := (show 2 ∣ w.2+1 from ⟨k+1, by omega⟩).trans wd
  have hi := normalized_product 2 (by decide) hu hM
  let f (z : ℕ × ℕ) := (∑ j ∈ range (z.2+1), (j+1)*z.1^j)*z.1^(23*z.2)
  change (L.map f).prod % 2 = (D+1)%2 at hi
  intro z hz
  by_contra! hbad
  have hp : z.1 ≡ 1 [MOD 2] := by
    have hc : z.1.Coprime 2 := (hu z hz).of_dvd_right (by decide : 2 ∣ 6)
    have hn := Nat.prime_two.coprime_iff_not_dvd.mp hc.symm
    change z.1%2 = 1
    omega
  have e := poly_mod_congr hp z.2
  change _ % 2 = _ % 2 at e
  simp only [one_pow, mul_one] at e
  rw [moment_triangular_mod_two, if_neg (by omega)] at e
  have d : 2 ∣ f z := dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero e) _
  have hzero := Nat.mod_eq_zero_of_dvd (d.trans (List.dvd_prod (List.mem_map.mpr ⟨z,hz,rfl⟩)))
  omega

end Div245

/- Arithmetic reduction of a fixed point to its least prime and the remaining prime powers. -/

open Finset OeisA245211
namespace Div245

theorem bridge_no_pure {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (h : (∑ j ∈ range (e+1), (j+1)*p^j) = p^e*(e+2)) : False := by
  have hv (i : ℕ) : (∑ j ∈ range (i+1), (j+1)*p^j) % p = 1 := by
    induction i with
    | zero => simp [Nat.mod_eq_of_lt hp.one_lt]
    | succ i ih =>
      have hd : p ∣ (i+1+1)*p^(i+1) := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) _
      rw [sum_range_succ, Nat.add_mod, ih, Nat.mod_eq_zero_of_dvd hd, add_zero,
        Nat.mod_eq_of_lt hp.one_lt]
  have hd : p ∣ p^e*(e+2) := dvd_mul_of_dvd_left (dvd_pow_self p he.ne') _
  have hv' := hv e
  rw [h, Nat.mod_eq_zero_of_dvd hd] at hv'
  omega

theorem bridge_cofactor_budget {p m : ℕ} (hp : 1 < p) (hm : 1 < m)
    (hfix : a (p*m) = p*m) : m.divisors.card < p := by
  let f := fun d : ℕ => d * d.divisors.card
  have hlt : m < p*m := by nlinarith
  have hm' : m ∈ (p*m).properDivisors :=
    Nat.mem_properDivisors.mpr ⟨dvd_mul_left _ _, hlt⟩
  have h1 : 1 ∈ (p*m).properDivisors := Nat.one_mem_properDivisors_iff_one_lt.mpr (by omega)
  have h1' : 1 ∈ (p*m).properDivisors.erase m :=
    mem_erase.mpr ⟨by omega, h1⟩
  have hs := single_le_sum (f := f) (fun _ _ => Nat.zero_le _) h1'
  have ht := sum_erase_add (p*m).properDivisors f hm'
  change (∑ d ∈ (p*m).properDivisors, f d) = p*m at hfix
  rw [hfix] at ht
  have hf : f 1 = 1 := by simp [f]
  rw [hf] at hs
  change _ + m * m.divisors.card = p*m at ht
  have hstrict : m * m.divisors.card < p*m := by omega
  rw [Nat.mul_comm p m] at hstrict
  exact (Nat.mul_lt_mul_left (by omega : 0 < m)).mp hstrict

theorem bridge_no_pattern4912 {a p : ℕ} (es : List ℕ) (hb : p ≤ 433)
    (h : a*(es.map (·+1)).prod < p) : ¬(a::es).Perm [4,9,12] := by
  intro perm
  have D := (perm.map (fun e => e+1)).prod_eq
  change (a+1)*(es.map (·+1)).prod = 650 at D
  have hm := perm.mem_iff.mp (show a ∈ a::es from List.mem_cons_self)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl|rfl|rfl <;> omega

theorem bridge_four {L : List (ℕ × ℕ)} (h : ∀ z ∈ L, 0 < z.2) :
    2^L.length ≤ (L.map (fun z => z.2+1)).prod := by
  induction L with
  | nil => simp
  | cons z L ih =>
    simp only [List.length_cons, pow_succ', List.map_cons, List.prod_cons]
    exact Nat.mul_le_mul (by have := h z (List.mem_cons_self ..); omega)
      (ih (fun w hw => h w (List.mem_cons_of_mem _ hw)))

theorem problem_bridge {n : ℕ} (hn : 1 < n) (bound : n.minFac ≤ 433)
    (hf : OeisA245211.a n = n) (ne : n ≠ 21) :
    ∃ (a : ℕ) (L : List (ℕ × ℕ)),
      let p := n.minFac
      let E := (L.map (fun z => z.2+1)).prod
      let D := (a+1)*E
      p.Prime ∧ 3 < p ∧ 0 < a ∧ a%4 < 2 ∧ 2 ≤ L.length ∧
      L.Pairwise (fun z w => z.1 < w.1) ∧
      (∀ z ∈ L, z.1.Prime ∧ p < z.1 ∧ 0 < z.2 ∧ z.2%4 < 2 ∧ z.1.Coprime p.factorial) ∧
      (1 < a ∨ ∃ z ∈ L, 1 < z.2) ∧ D ≤ 2*(p-1) ∧ a*E < p ∧
      ¬(a :: L.map Prod.snd).Perm [4,9,12] ∧
      n = p^a*(L.map (fun z => z.1^z.2)).prod ∧
      (∑ j ∈ range (a+1), (j+1)*p^j)*(L.map (fun z => ∑ j ∈ range (z.2+1), (j+1)*z.1^j)).prod =
        (p^a*(D+1))*(L.map (fun z => z.1^z.2)).prod := by
  obtain ⟨K,hs,hdat,hmin,hN,hD,hM⟩ := fixed_pattern hn hf
  cases K with
  | nil => simp at hmin
  | cons z L =>
    obtain ⟨p,a⟩ := z
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp hs
    have data0 := hdat (p,a) (List.mem_cons_self ..)
    obtain ⟨e,hm⟩ := hmin
    have heq : n.minFac = p := by
      rcases List.mem_cons.mp hm with h|h
      · exact congrArg Prod.fst h
      · have ht : p < n.minFac := head (n.minFac,e) h
        have hb : n.minFac ≤ p := data0.2.2.2
        omega
    let K := (p,a)::L
    let E := (L.map (fun z => z.2+1)).prod
    let Y := (L.map (fun z => z.1^z.2)).prod
    have hp : p.Prime := data0.1
    have ha : 0<a := data0.2.1
    have hpb : p≤433 := heq ▸ bound
    have ht (z) (hz : z ∈ L) := hdat z (List.mem_cons_of_mem _ hz)
    have hpow : n = p^a*Y := hN
    have hcount : n.divisors.card = (a+1)*E := hD
    have hfix : (K.map (fun z => ∑ j ∈ range (z.2+1), (j+1)*z.1^j)).prod =
        (K.map (fun z => z.1^z.2)).prod * ((K.map (fun z => z.2+1)).prod+1) := hM.trans (congrArg (· * _) hN)
    have hlen : 2 ≤ L.length := by
      cases L with
      | nil =>
        exfalso
        apply bridge_no_pure hp ha
        simpa [K, Nat.add_assoc] using hfix
      | cons z L =>
        cases L with
        | nil =>
          exfalso
          obtain ⟨q,b⟩ := z
          have hz : (q,b) ∈ [(q,b)] := by simp
          have hn' : n=p^a*q^b := by simpa [Y] using hpow
          apply ne
          apply hn'.trans
          apply OMA.R_OeisA245211_conjecture_R3.two_prime_through_439 hp (ht _ hz).1
            (head _ hz) (by omega) ha (ht _ hz).2.1
          rwa [←hn']
        | cons w tl => simp
    have h48 : 4 ≤ E := (Nat.pow_le_pow_right (by decide : 0<2) hlen).trans
      (bridge_four (fun z hz => (ht z hz).2.1))
    have hY : 0 < Y := by
      by_contra! h
      have hzero : Y=0 := by omega
      rw [hzero, mul_zero] at hpow
      omega
    have hY' : 1 < Y := by
      let z := L[0]'(by omega)
      have hz : z ∈ L := List.getElem_mem ..
      have hd : z.1^z.2 ∣ Y := List.dvd_prod (List.mem_map.mpr ⟨z,hz,rfl⟩)
      exact (Nat.one_lt_pow (ht z hz).2.1.ne' (ht z hz).1.one_lt).trans_le (Nat.le_of_dvd hY hd)
    have hc : p.Coprime Y := by
      apply Nat.coprime_list_prod_right_iff.mpr
      intro d hd
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hd
      exact ((Nat.coprime_primes hp (ht z hz).1).mpr (head z hz).ne).pow_right _
    have feed : n = p*(p^(a-1)*Y) := by
      rw [hpow, ←mul_assoc, ←pow_succ', Nat.sub_add_cancel ha]
    have sharp : a*E < p := by
      have hgt : 1 < p^(a-1)*Y := hY'.trans_le (Nat.le_mul_of_pos_left Y (pow_pos hp.pos _))
      have raw := bridge_cofactor_budget hp.one_lt hgt (feed ▸ hf)
      rw [(hc.pow_left _).card_divisors_mul, card_pow hp, Nat.sub_add_cancel ha] at raw
      have htD := (pattern_products L tail (fun z hz => (ht z hz).1)).1
      simpa only [show Y.divisors.card = E from htD] using raw
    have h3 : 3 < p := by have := Nat.le_mul_of_pos_left E ha; omega
    have h6 (z) (hz : z ∈ K) : z.1.Coprime 6 := by
      have zprime := (hdat z hz).1
      have hq : 3 < z.1 := h3.trans_le (heq ▸ (hdat z hz).2.2.2)
      apply zprime.coprime_iff_not_dvd.mpr
      intro hd
      change z.1 ∣ 2*3 at hd
      rcases zprime.dvd_mul.mp hd with hd|hd <;> have := Nat.le_of_dvd (by decide) hd <;> omega
    have count := OMA.R_OeisA245211_conjecture_R3.divisor_count_bound (by omega : 0<n)
      hp (heq ▸ Nat.minFac_dvd n) hf
    have count' : (a+1)*E ≤ 2*(p-1) := hcount ▸ count
    have oddExp : ∃ z ∈ K, Odd z.2 := by
      by_contra! h
      apply no_even_pattern K h6 (fun z hz => ⟨(hdat z hz).2.1, ?_⟩)
        (by simpa [K] using hlen) (by change (a+1)*E≤864; omega) hfix
      exact (Nat.even_or_odd z.2).resolve_right (h z hz)
    have parity := nonsquare_parity h6 oddExp hfix
    have hQ : ¬ Squarefree n := fun h => ne (squarefree_fixed_433 hn bound h hf)
    rw [Nat.squarefree_iff_prime_squarefree] at hQ
    push Not at hQ
    obtain ⟨q,hq,hqq⟩ := hQ
    have qd : q ∣ n := (dvd_mul_right q q).trans hqq
    have qdiv : q ∣ (K.map (fun z => z.1^z.2)).prod := hN ▸ qd
    obtain ⟨b,hb,hd⟩ := (Prime.dvd_prod_iff hq.prime).mp qdiv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hb
    have eq : q=w.1 := (Nat.prime_dvd_prime_iff_eq hq (hdat w hw).1).mp (hq.dvd_of_dvd_pow hd)
    have ex2 : 2 ≤ n.factorization w.1 := ((hdat w hw).1.pow_dvd_iff_le_factorization (by omega)).mp
      (by simpa [pow_two,←eq] using hqq)
    have heavy : 1<a ∨ ∃ z ∈ L, 1<z.2 := by
      have h2 : 1<w.2 := by rw [(hdat w hw).2.2.1]; omega
      rcases List.mem_cons.mp hw with rfl|hh
      · exact Or.inl h2
      · exact Or.inr ⟨_,hh,h2⟩
    refine ⟨a,L,?_⟩
    simp only [heq]
    refine ⟨hp,h3,ha,parity (p,a) (List.mem_cons_self ..),hlen,tail,?_,heavy,count',sharp,?_,hpow,?_⟩
    · intro z hz
      have hz' := (ht z hz).1
      refine ⟨hz',head z hz,(ht z hz).2.1,parity z (List.mem_cons_of_mem _ hz),?_⟩
      exact hz'.coprime_iff_not_dvd.mpr (fun hd => (head z hz).not_ge (hz'.dvd_factorial.mp hd))
    · apply bridge_no_pattern4912 _ hpb
      simpa [List.map_map,Function.comp_def,E] using sharp
    · change _ = (p^a*((a+1)*E+1))*Y
      calc
        _ = (p^a*Y)*((a+1)*E+1) := hfix
        _ = _ := by ring

end Div245

/- Exhaustive generation of exponent lists with a multiplicative divisor budget. -/
namespace Div245

theorem admissible_pattern_length {es : List ℕ} (he : ∀ e ∈ es, 0 < e)
    (hb : (es.map (·+1)).prod ≤ 864) : es.length ≤ 9 := by
  have low (s : List ℕ) (hs : ∀ e ∈ s, 0 < e) : 2^s.length ≤ (s.map (·+1)).prod := by
    induction s with
    | nil => simp
    | cons e s ih =>
      simp only [List.length_cons,pow_succ',List.map_cons,List.prod_cons]
      exact Nat.mul_le_mul (by have := hs e (by simp); omega)
        (ih (fun j hj => hs j (List.mem_cons_of_mem _ hj)))
  by_contra! hh
  have := (Nat.pow_le_pow_right (by decide : 0 < 2) (show 10 ≤ es.length by omega)).trans
    ((low es he).trans hb)
  norm_num at this

theorem admissible_pattern_mem {es : List ℕ} {B k : ℕ} (F : ℕ → Bool)
    (he : ∀ e ∈ es, 0 < e ∧ F e = true)
    (hb : (es.map (·+1)).prod ≤ B) (hl : es.length ≤ k) :
    let gen := Nat.rec (motive := fun _ => ℕ → List (List ℕ)) (fun _ => [[]])
      (fun _ tail b => [] :: ((List.range (b-1)).filter (fun i => F (i+1))).flatMap (fun i =>
        (tail (b/(i+2))).map ((i+1)::·))) k
    es ∈ gen B := by
  induction k generalizing es B with
  | zero => have : es = [] := List.eq_nil_of_length_eq_zero (by omega); subst es; simp
  | succ k ih =>
    cases es with
    | nil => exact List.mem_cons_self ..
    | cons e es =>
      have ho := he e (by simp)
      have hpos : 0 < (es.map (·+1)).prod :=
        List.prod_pos (by intro x hx; obtain ⟨z,_,rfl⟩ := List.mem_map.mp hx; omega)
      change (e+1)*(es.map (·+1)).prod ≤ B at hb
      have hbe : e+1 ≤ B := (Nat.le_mul_of_pos_right _ hpos).trans hb
      obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ho.1.ne'
      apply List.mem_cons_of_mem
      apply List.mem_flatMap.mpr
      refine ⟨i,List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),ho.2⟩,?_⟩
      apply List.mem_map.mpr
      refine ⟨es, ?_, rfl⟩
      apply ih (fun j hj => he j (List.mem_cons_of_mem _ hj))
      · exact (Nat.le_div_iff_mul_le (by omega : 0 < i+2)).mpr (by rwa [Nat.mul_comm])
      · simpa only [List.length_cons, Nat.add_le_add_iff_right] using hl

end Div245

/- Numerical steps for removing prime-power factors from the moment equation. -/
namespace Div245
open Finset

theorem raw_leaf {q e U V : ℕ} (hq : Nat.Prime q) (he : 0 < e) (hU : 0 < U) (_hV : 0 < V)
    (bal : U * (∑ i ∈ Finset.range (e+1), (i+1)*q^i) = V*q^e) :
    0 < V-U*(e+1) ∧ q = (e*U-1)/(V-U*(e+1))+1 := by
  let B := fun j => ∑ i ∈ Finset.range j, (i+1)*q^i
  have step (j : ℕ) : B (j+1) = B j+(j+1)*q^j := Finset.sum_range_succ _ _
  have tail (j : ℕ) : (j+1)*q^(j+1) ≤ q*B (j+1) ∧ q*B (j+1) < (j+1)*q^(j+1)+B (j+1) := by
    induction j with
    | zero => simp [B]
    | succ j ih =>
      rw [step (j+1), pow_succ q (j+1)]
      constructor
      · nlinarith only [Nat.zero_le (q*B (j+1))]
      · nlinarith only [ih.2, Nat.zero_le (q^(j+1))]
  obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
  have t : e*q^e ≤ q*B e ∧ q*B e < e*q^e+B e := hi ▸ tail i
  have Bpos : 0 < B e := by
    have h := Finset.single_le_sum (s := Finset.range e) (f := fun i => (i+1)*q^i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr he : 0 ∈ Finset.range e)
    have h' : 1 ≤ B e := by simpa [B] using h
    omega
  change U*B (e+1)=V*q^e at bal
  rw [step] at bal
  have ltV : U*(e+1)<V := by
    apply (Nat.mul_lt_mul_right (pow_pos hq.pos e)).mp
    nlinarith only [bal, Nat.mul_pos hU Bpos]
  let g := V-U*(e+1)
  have gpos : 0<g := Nat.sub_pos_of_lt ltV
  have eqg : g+U*(e+1)=V := Nat.sub_add_cancel ltV.le
  have core : q^e*g=U*B e := by nlinarith only [congrArg (· * q^e) eqg, bal]
  have cross : (q^e)*(q*g)=U*(q*B e) := by
    calc _ = q*((q^e)*g) := by ring
         _ = _ := by rw [core]; ring
  have lower : e*U ≤ q*g := by
    apply (Nat.mul_le_mul_left_iff (pow_pos hq.pos e)).mp
    rw [cross]
    simpa only [mul_assoc,mul_left_comm,mul_comm] using Nat.mul_le_mul_left U t.1
  have upper : q*g < e*U+g := by
    apply (Nat.mul_lt_mul_left (pow_pos hq.pos e)).mp
    rw [cross, Nat.mul_add, core]
    simpa only [Nat.mul_add,mul_assoc,mul_left_comm,mul_comm] using
      Nat.mul_lt_mul_of_pos_left t.2 hU
  have q1 := Nat.sub_add_cancel (show 1 ≤ q from hq.pos)
  have eq := congrArg (· * g) q1
  have hE := Nat.mul_pos he hU
  have left : (q-1)*g ≤ e*U-1 := by nlinarith only [eq,upper,Nat.sub_add_cancel hE]
  have right : e*U-1 < (q-1+1)*g := by rw [q1]; omega
  exact ⟨gpos, by change q = (e*U-1)/g+1; rw [Nat.div_eq_of_lt_le left right,q1]⟩

theorem raw_forced {U V : ℕ} (L : List (ℕ×ℕ)) (hU : 0 < U)
    (hp : ∀ z ∈ L, Nat.Prime z.1)
    (bal : U*(L.map (fun z => ∑ i ∈ Finset.range (z.2+1), (i+1)*z.1^i)).prod =
      V*(L.map (fun z => z.1^z.2)).prod) :
    U/(U.gcd V) ∣ (L.map (fun z => z.1^z.2)).prod ∧
    ∀ r : ℕ, r.Prime → r ∣ U/(U.gcd V) → ∃ z ∈ L, z.1 = r := by
  let A := (L.map (fun z => ∑ i ∈ Finset.range (z.2+1), (i+1)*z.1^i)).prod
  let B := (L.map (fun z => z.1^z.2)).prod
  let g := U.gcd V
  have hg : 0 < g := Nat.gcd_pos_of_pos_left V hU
  have red : (U/g)*A = (V/g)*B := by
    apply Nat.eq_of_mul_eq_mul_left hg
    rw [← mul_assoc, ← mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_left U V),
      Nat.mul_div_cancel' (Nat.gcd_dvd_right U V)]
    exact bal
  have force : U/g ∣ B := (Nat.coprime_div_gcd_div_gcd hg).dvd_of_dvd_mul_left ⟨A,red.symm⟩
  refine ⟨force, fun r hr hrd => ?_⟩
  obtain ⟨b,hb,hd⟩ := _root_.Prime.dvd_prod_iff hr.prime |>.mp (hrd.trans force)
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hb
  exact ⟨z,hz,((Nat.prime_dvd_prime_iff_eq hr (hp z hz)).mp (hr.dvd_of_dvd_pow hd)).symm⟩

theorem raw_erase {U V : ℕ} (L : List (ℕ×ℕ)) (z : ℕ×ℕ) (hz : z ∈ L)
    (bal : U*(L.map (fun w => ∑ i ∈ Finset.range (w.2+1), (i+1)*w.1^i)).prod =
      V*(L.map (fun w => w.1^w.2)).prod) :
    (U*(∑ i ∈ Finset.range (z.2+1), (i+1)*z.1^i))*
      ((L.erase z).map (fun w => ∑ i ∈ Finset.range (w.2+1), (i+1)*w.1^i)).prod =
    (V*z.1^z.2)*((L.erase z).map (fun w => w.1^w.2)).prod := by
  have P := List.perm_cons_erase hz
  rw [(P.map (fun w => ∑ i ∈ Finset.range (w.2+1), (i+1)*w.1^i)).prod_eq,
    (P.map (fun w => w.1^w.2)).prod_eq] at bal
  simpa only [List.map_cons,List.prod_cons,mul_assoc] using bal

end Div245

/- Integer envelope for the normalized divisor moment of a prime-power pattern. -/

namespace Div245

open Finset

/-- Cross-multiplied monotonicity of T_e(p)/p^e; valid even at trial
values q that are composite. -/
theorem local_envelope {p q : ℕ} (h : q ≤ p) (e : ℕ) :
    (∑ j ∈ range (e+1), (j+1)*p^j)*q^e ≤
      (∑ j ∈ range (e+1), (j+1)*q^j)*p^e := by
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have le : j ≤ e := by have := Finset.mem_range.mp hj; omega
  have hq : q^e=q^j*q^(e-j) := (pow_add q j (e-j)) ▸ congrArg (q^·) (by omega : e=j+(e-j))
  have hp : p^e=p^j*p^(e-j) := (pow_add p j (e-j)) ▸ congrArg (p^·) (by omega : e=j+(e-j))
  rw [hq,hp]
  calc
    (j+1)*p^j*(q^j*q^(e-j)) = ((j+1)*p^j*q^j)*q^(e-j) := by ring
    _ ≤ ((j+1)*p^j*q^j)*p^(e-j) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)
    _ = _ := by ring

/-- For every list of prime-power slots, assigning the same trial base q
to every unfilled slot gives an upper bound for the normalized moment tail. -/
theorem pattern_envelope (q : ℕ) (L : List (ℕ×ℕ)) (least : ∀ s ∈ L, q ≤ s.1) :
    (L.map (fun s => ∑ j ∈ range (s.2+1), (j+1)*s.1^j)).prod * q^(L.map Prod.snd).sum ≤
    (L.map (fun s => ∑ j ∈ range (s.2+1), (j+1)*q^j)).prod * (L.map (fun s => s.1^s.2)).prod := by
  induction L with
  | nil => simp
  | cons s l ih =>
    have a := local_envelope (least s (by simp)) s.2
    have b := ih (fun t ht => least t (List.mem_cons_of_mem _ ht))
    have ab := Nat.mul_le_mul a b
    simp only [List.map_cons,List.prod_cons,List.sum_cons,pow_add]
    exact le_trans (le_of_eq (by ac_rfl)) (ab.trans_eq (by ac_rfl))

end Div245

/- A certified finite search of normalized prime-power moment equations. -/
namespace Div245
open Finset

theorem raw_bound (T : ℕ → ℕ → ℕ)
    (hT : ∀ p e, T p e = ∑ j ∈ range (e+1), (j+1)*p^j)
    {L : List (ℕ × ℕ)} {s : List ℕ} {U V q : ℕ}
    (perm : s.Perm (L.map Prod.snd))
    (hp : ∀ z ∈ L, z.1.Prime)
    (bal : U*(L.map (fun z => T z.1 z.2)).prod = V*(L.map (fun z => z.1^z.2)).prod)
    (least : ∀ z ∈ L, q ≤ z.1) :
    V*q^s.sum ≤ U*(s.map (T q)).prod := by
  have h := pattern_envelope q L least
  simp only [← hT] at h
  rw [← perm.sum_eq] at h
  have hm : (s.map (T q)).prod = (L.map (fun z => T q z.2)).prod := by
    simpa [List.map_map, Function.comp_def] using (perm.map (T q)).prod_eq
  rw [← hm] at h
  have pos : 0 < (L.map (fun z : ℕ×ℕ => z.1^z.2)).prod := by
    apply List.prod_pos
    intro a ha
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ha
    exact pow_pos (hp z hz).pos _
  apply Nat.le_of_mul_le_mul_right ?_ pos
  calc
    V*q^s.sum*(L.map (fun z : ℕ×ℕ => z.1^z.2)).prod =
        (V*(L.map (fun z : ℕ×ℕ => z.1^z.2)).prod)*q^s.sum := by ac_rfl
    _ ≤ _ := by rw [← bal]; simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left U h

theorem raw_strict (T : ℕ → ℕ → ℕ)
    (hT : ∀ p e, T p e = ∑ j ∈ range (e+1), (j+1)*p^j)
    {L : List (ℕ×ℕ)} {s : List ℕ} {U V : ℕ}
    (perm : s.Perm (L.map Prod.snd)) (hs : L ≠ [])
    (hp : ∀ z ∈ L, 0<z.1 ∧ 0<z.2) (hu : 0<U)
    (bal : U*(L.map (fun z => T z.1 z.2)).prod = V*(L.map (fun z => z.1^z.2)).prod) :
    U*(s.map (·+1)).prod < V := by
  have local' (p e : ℕ) (he : 0 < e) : (e+1)*p^e < T p e := by
    rw [hT, sum_range_succ]
    have h := Finset.single_le_sum (s := range e) (f := fun j => (j+1)*p^j)
      (fun _ _ => Nat.zero_le _) (mem_range.mpr he : 0 ∈ range e)
    simp at h
    omega
  have hm := (perm.map (·+1)).prod_eq
  simp only [List.map_map, Function.comp_def] at hm
  rw [hm]
  have prodlt (K : List (ℕ×ℕ)) (hn : K ≠ []) (hK : ∀ z ∈ K, 0<z.1 ∧ 0<z.2) :
      (K.map (fun z => (z.2+1)*z.1^z.2)).prod < (K.map (fun z => T z.1 z.2)).prod := by
    induction K with
    | nil => exact (hn rfl).elim
    | cons z K ih =>
      have hz := hK z (by simp)
      have lt := local' z.1 z.2 hz.2
      cases K with
      | nil => simpa using lt
      | cons y ys =>
        have tl := ih (by simp) (fun a ha => hK a (List.mem_cons_of_mem _ ha))
        exact Nat.mul_lt_mul_of_lt_of_lt lt tl
  have lt := prodlt L hs hp
  rw [List.prod_map_mul] at lt
  have h := (Nat.mul_lt_mul_left hu).mpr lt
  rw [bal, ← Nat.mul_assoc] at h
  exact Nat.lt_of_mul_lt_mul_right h

theorem raw_node (T : ℕ → ℕ → ℕ)
    (hT : ∀ p e, T p e = ∑ j ∈ range (e+1), (j+1)*p^j)
    (pick : ℕ → ℕ) (cert : ℕ → Bool) (hcert : ∀ t, cert (pick t) = true → (pick t).Prime) (width : ℕ) (child : ℕ → ℕ → Bool)
    {L : List (ℕ×ℕ)} {s : List ℕ} {U V lo A : ℕ}
    (perm : s.Perm (L.map Prod.snd))
    (hp : ∀ z ∈ L, z.1.Prime ∧ 0<z.2 ∧ lo ≤ z.1 ∧ z.1.Coprime A)
    (hU : 0<U) (hV : 0<V)
    (bal : U*(L.map (fun z => T z.1 z.2)).prod = V*(L.map (fun z => z.1^z.2)).prod)
    (hc : ∀ z ∈ L, child z.1 z.2 = true) :
    let upperTest := fun t => decide (V*t^s.sum ≤ U*(s.map (T t)).prod)
    let F := U/U.gcd V
    let r := pick F
    let branch :=  fun q => s.any (child q)
    (match s with
    | [] => U == V
    | [e] =>
        let q := (e*U-1)/(V-U*(e+1))+1
        decide (lo ≤ q ∧ q.Coprime A ∧ U*T q e = V*q^e)
    | _::_::_ =>
        if V ≤ U*(s.map (·+1)).prod ∨ ¬ F.Coprime A then false
        else if !upperTest lo then false
        else if cert r = true ∧ r ∣ F then decide (lo ≤ r ∧ r.Coprime A) && branch r
        else upperTest (lo+width) || (List.range width).any (fun i =>
          let q := lo+i
          decide (q.Coprime A) && branch q)) = true := by
  intro upperTest F r branch
  have prime' := fun z hz => (hp z hz).1
  have choose (z : ℕ×ℕ) (hz : z ∈ L) : branch z.1 = true :=
    List.any_eq_true.mpr ⟨z.2,perm.mem_iff.mpr (List.mem_map.mpr ⟨z,hz,rfl⟩),hc z hz⟩
  have upper {q : ℕ} (h : ∀ z ∈ L, q ≤ z.1) : upperTest q = true :=
    decide_eq_true (raw_bound T hT perm prime' bal h)
  cases s with
  | nil =>
    have hh := List.map_eq_nil_iff.mp perm.symm.eq_nil
    subst L
    simpa using bal
  | cons e es =>
    cases es with
    | nil =>
      have hh := perm.length_eq
      cases L with
      | nil => simp at hh
      | cons z L =>
        have h0 : L=[] := by simpa using hh.symm
        subst L
        have hz := hp z (by simp)
        have ez : e = z.2 := by simpa using perm.mem_iff.mp (List.mem_cons_self .. : e ∈ [e])
        subst e
        simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at bal
        have hb := raw_leaf hz.1 hz.2.1 hU hV (by simpa only [hT] using bal)
        dsimp only
        rw [← hb.2]
        exact decide_eq_true ⟨hz.2.2.1,hz.2.2.2,bal⟩
    | cons b bs =>
      have hs : L ≠ [] := by intro h; subst L; simp at perm
      have hlt := raw_strict T hT perm hs (fun z hz => ⟨(hp z hz).1.pos,(hp z hz).2.1⟩) hU bal
      have hf := raw_forced L hU prime' (by simpa only [hT] using bal)
      have cp : F.Coprime A := Nat.Coprime.coprime_dvd_left hf.1
        (Nat.coprime_list_prod_left_iff.mpr (fun t ht => by
          obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ht
          exact ((hp z hz).2.2.2).pow_left _))
      have ol := upper (fun z hz => (hp z hz).2.2.1)
      simp only [if_neg (not_or.mpr ⟨hlt.not_ge,not_not.mpr cp⟩), ol, Bool.not_true, Bool.false_eq_true, if_false]
      split
      next h =>
        obtain ⟨z,hz,heq⟩ := hf.2 r (hcert F h.1) h.2
        rw [← heq, choose z hz]
        simpa using And.intro (hp z hz).2.2.1 (hp z hz).2.2.2
      next _ =>
        by_cases lt : ∃ z ∈ L, z.1 < lo+width
        · obtain ⟨z,hz,hl⟩ := lt
          have hz' := hp z hz
          have H : lo+(z.1-lo)=z.1 := by omega
          rw [Bool.or_eq_true]
          right
          apply List.any_eq_true.mpr
          refine ⟨z.1-lo,List.mem_range.mpr (by omega),?_⟩
          rw [H,choose z hz]
          simpa using hz'.2.2.2
        · have hh := upper (q:=lo+width) (by simpa only [not_exists,not_and,not_lt] using lt)
          simp [hh]
end Div245

/- Recursive search and prime-power elimination. -/
namespace Div245
open Finset

def scanStep (T : ℕ → ℕ → ℕ) (pick : ℕ → ℕ) (cert : ℕ → Bool)
    (W : ℕ → List ℕ → ℕ → ℕ → ℕ) (gate : ℕ → List ℕ → ℕ → ℕ → Bool) (lo : ℕ) :=
  fun (_ : ℕ) (recur : List ℕ → ℕ → ℕ → ℕ → Bool) (s : List ℕ) (U V A : ℕ) =>
      let result := 
        let upperTest := fun t => decide (V*t^s.sum ≤ U*(s.map (T t)).prod)
        let F := U/U.gcd V
        let r := pick F
        let branch :=  fun q => s.any (fun e => recur (s.erase e) (U*T q e) (V*q^e) (A*q))
        (match s with
        | [] => U == V
        | [e] =>
            let q := (e*U-1)/(V-U*(e+1))+1
            decide (lo ≤ q ∧ q.Coprime A ∧ U*T q e = V*q^e)
        | _::_::_ =>
            if V ≤ U*(s.map (·+1)).prod ∨ ¬ F.Coprime A then false
            else if !upperTest lo then false
            else if cert r = true ∧ r ∣ F then decide (lo ≤ r ∧ r.Coprime A) && branch r
            else upperTest (lo+(W lo s U V)) || (List.range (W lo s U V)).any (fun i =>
              let q := lo+i
              decide (q.Coprime A) && branch q))
      gate lo s U V && result

theorem scan_complete
    (T : ℕ → ℕ → ℕ) (hT : ∀ p e, T p e = ∑ j ∈ range (e+1), (j+1)*p^j)
    (pick : ℕ → ℕ) (cert : ℕ → Bool) (hcert : ∀ t, cert (pick t)=true → (pick t).Prime)
    (W : ℕ → List ℕ → ℕ → ℕ → ℕ) (gate : ℕ → List ℕ → ℕ → ℕ → Bool)
    (gate_ok : ∀ (lo : ℕ) (s : List ℕ) (U V : ℕ) (L : List (ℕ×ℕ)),
      s.Perm (L.map Prod.snd) → (∀ z ∈ L, z.1.Prime ∧ lo ≤ z.1) →
      U*(L.map (fun z => T z.1 z.2)).prod = V*(L.map (fun z => z.1^z.2)).prod →
      gate lo s U V = true)
    (lo : ℕ) (k : ℕ) (s : List ℕ) (U V A : ℕ) (L : List (ℕ×ℕ))
    (perm : s.Perm (L.map Prod.snd)) (nd : L.Pairwise (fun u v => u.1 ≠ v.1))
    (hp : ∀ z ∈ L, z.1.Prime ∧ 0<z.2 ∧ lo ≤ z.1 ∧ z.1.Coprime A)
    (hU : 0<U) (hV : 0<V)
    (bal : U*(L.map (fun z => T z.1 z.2)).prod = V*(L.map (fun z => z.1^z.2)).prod) :
    Nat.rec (motive := fun _ => List ℕ → ℕ → ℕ → ℕ → Bool) (fun _ _ _ _ => true) (scanStep T pick cert W gate lo) k s U V A = true := by
  let step := scanStep T pick cert W gate lo
  change Nat.rec (motive := fun _ => List ℕ → ℕ → ℕ → ℕ → Bool) (fun _ _ _ _ => true) step k s U V A = true
  induction k generalizing s U V A L with
  | zero => rfl
  | succ k ih =>
    let recur := Nat.rec (motive := fun _ => List ℕ → ℕ → ℕ → ℕ → Bool) (fun _ _ _ _ => true) step k
    let child (q e : ℕ) := recur (s.erase e) (U*T q e) (V*q^e) (A*q)
    have good (z : ℕ×ℕ) (hz : z ∈ L) : child z.1 z.2 = true := by
      have pm := List.perm_cons_erase hz
      have pe := perm.trans (pm.map Prod.snd)
      have ez : z.2 ∈ s := perm.mem_iff.mpr (List.mem_map.mpr ⟨z,hz,rfl⟩)
      have p' := (List.perm_cons_erase ez).symm.trans pe
      have nd' := pm.pairwise nd (fun h => h.symm)
      have ⟨sep,tailnd⟩ := List.pairwise_cons.mp nd'
      have hz' := hp z hz
      have pos : 0 < T z.1 z.2 := by
        rw [hT]
        have h := Finset.single_le_sum (s:=range (z.2+1)) (f:=fun j => (j+1)*z.1^j)
          (fun _ _ => Nat.zero_le _) (mem_range.mpr (Nat.succ_pos _) : 0 ∈ range (z.2+1))
        change 1 ≤ _
        simpa using h
      apply ih _ _ _ _ (L.erase z) p'.cons_inv tailnd
      · intro t ht
        have ht' := hp t (List.mem_of_mem_erase ht)
        exact ⟨ht'.1,ht'.2.1,ht'.2.2.1,ht'.2.2.2.mul_right ((Nat.coprime_primes ht'.1 hz'.1).mpr (sep t ht).symm)⟩
      · exact Nat.mul_pos hU pos
      · exact Nat.mul_pos hV (pow_pos hz'.1.pos _)
      · simp only [hT] at bal ⊢
        exact raw_erase L z hz bal
    have node := raw_node T hT pick cert hcert (W lo s U V) child perm hp hU hV bal good
    have hg := gate_ok lo s U V L perm (fun z hz => ⟨(hp z hz).1,(hp z hz).2.2.1⟩) bal
    apply Bool.and_eq_true_iff.mpr
    refine ⟨hg,?_⟩
    cases s with
    | nil => exact node
    | cons e es => cases es <;> exact node

end Div245

/- Enumerating admissible exponent multisets after choosing the least prime. -/
namespace Div245
open Finset OeisA245211

def weight (p e : ℕ) : ℕ :=
  (Nat.rec (motive := fun _ => ℕ×ℕ) (1,1)
    (fun i v => let w := v.1*p; (w,v.2+(i+2)*w)) e).2

theorem weight_spec (p e : ℕ) : weight p e = ∑ j ∈ range (e+1), (j+1)*p^j := by
  let f := fun e => Nat.rec (motive := fun _ => ℕ×ℕ) (1,1)
    (fun i v => let w := v.1*p; (w,v.2+(i+2)*w)) e
  have v (i : ℕ) : (f i).1=p^i ∧ (f i).2=∑ j ∈ range (i+1), (j+1)*p^j := by
    induction i with
    | zero => simp [f]
    | succ i ih =>
      change (f i).1*p = p^(i+1) ∧ (f i).2+(i+2)*((f i).1*p) = _
      rw [ih.1,ih.2,Finset.sum_range_succ _ (i+1),pow_succ]
      exact ⟨rfl,rfl⟩
  exact (v e).2

def exponentLists : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, _, _ => [[]]
  | k+1, B, lb => [] :: ((List.range (B-1)).filter
      (fun i => decide (lb ≤ i+1 ∧ (i+1)%4 < 2))).flatMap (fun i =>
        (exponentLists k (B/(i+2)) (i+1)).map ((i+1)::·))

theorem exponentLists_mem {k B lb : ℕ} {s : List ℕ}
    (he : ∀ e ∈ s, 0 < e ∧ lb ≤ e ∧ e%4 < 2)
    (hb : (s.map (·+1)).prod ≤ B) (hlen : s.length ≤ k) (hs : s.Pairwise (· ≤ ·)) :
    s ∈ exponentLists k B lb := by
  induction k generalizing s B lb with
  | zero => have eq : s=[] := List.eq_nil_of_length_eq_zero (by omega); subst s; simp [exponentLists]
  | succ k ih =>
    cases s with
    | nil => exact List.mem_cons_self ..
    | cons e s =>
      obtain ⟨hmin,ht⟩ := List.pairwise_cons.mp hs
      obtain ⟨ep,ge,mod⟩ := he e (by simp)
      obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ep.ne'
      change (i+2)*(s.map (·+1)).prod ≤ B at hb
      have pos : 0 < (s.map (·+1)).prod := List.prod_pos (by
        intro v hv; obtain ⟨e,_,rfl⟩ := List.mem_map.mp hv; omega)
      have hig := (Nat.le_mul_of_pos_right (i+2) pos).trans hb
      apply List.mem_cons_of_mem
      apply List.mem_flatMap.mpr
      refine ⟨i,List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),decide_eq_true ⟨ge,mod⟩⟩,?_⟩
      apply List.mem_map.mpr
      refine ⟨s,?_,rfl⟩
      apply ih _ (Nat.le_div_iff_mul_le (by omega : 0 < i+2) |>.mpr (by rwa [mul_comm])) (by simpa using hlen) ht
      intro e h
      have H := he e (List.mem_cons_of_mem _ h)
      exact ⟨H.1,hmin e h,H.2.2⟩

def rootList (p : ℕ) : List (ℕ × List ℕ) :=
  ((List.range ((p-1)/4)).filter (fun i => (i+1)%4 < 2)).flatMap (fun i =>
    (exponentLists 9 ((p-1)/(i+1)) 1).filterMap (fun s =>
      if 2 ≤ s.length ∧ (1 < i+1 ∨ s.any (1 < ·)) then some (i+1,s) else none))

theorem roots_cover {n : ℕ} (hn : 1 < n) (bound : n.minFac ≤ 433) (hf : a n=n) (ne : n ≠ 21) :
    ∃ (a : ℕ) (s : List ℕ) (L : List (ℕ×ℕ)),
      (a,s) ∈ rootList n.minFac ∧ s.Perm (L.map Prod.snd) ∧
      L.Pairwise (fun u v => u.1 < v.1) ∧
      (∀ z ∈ L, z.1.Prime ∧ 0 < z.2 ∧ n.minFac+1 ≤ z.1 ∧ z.1.Coprime n.minFac.factorial) ∧
      weight n.minFac a * (L.map (fun z => weight z.1 z.2)).prod =
        (n.minFac^a*((a+1)*(s.map (·+1)).prod+1)) * (L.map (fun z => z.1^z.2)).prod := by
  obtain ⟨a,L,prime,large,apos,amod,hlen,order,hL,heavy,bd,sharp,_,_,bal⟩ := problem_bridge hn bound hf ne
  let s := (L.map Prod.snd).mergeSort
  have perm : s.Perm (L.map Prod.snd) := List.mergeSort_perm .. 
  have sort : s.Pairwise (· ≤ ·) := by
    have h := List.pairwise_mergeSort (le := fun x y : ℕ => decide (x ≤ y))
      (by intro x y z h1 h2; exact decide_eq_true (le_trans (of_decide_eq_true h1) (of_decide_eq_true h2)))
      (by intro x y; simp; omega) (L.map Prod.snd)
    simpa only [decide_eq_true_eq] using h
  have hslen : s.length = L.length := by simpa using perm.length_eq
  have hb := (perm.map (·+1)).prod_eq
  simp only [List.map_map, Function.comp_def] at hb
  rw [← hb] at bd sharp bal
  have he (e : ℕ) (h : e ∈ s) : 0 < e ∧ 1 ≤ e ∧ e%4 < 2 := by
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp (perm.mem_iff.mp h)
    have H := hL z hz
    exact ⟨H.2.2.1,H.2.2.1,H.2.2.2.1⟩
  have minProd : 4 ≤ (s.map (·+1)).prod := by
    have hh : 2 ≤ s.length := by omega
    obtain ⟨e,f,t,eq⟩ : ∃ e f t, s=e::f::t := by
      cases hs0 : s with
      | nil => rw [hs0] at hh; simp at hh
      | cons e l => cases ht0 : l with
        | nil => rw [hs0,ht0] at hh; simp at hh
        | cons f t => exact ⟨_,_,_,rfl⟩
    have epos := (he e (by simp [eq])).1
    have fpos := (he f (by simp [eq])).1
    have tpos : 0 < (t.map (·+1)).prod := List.prod_pos (by
      intro v h; obtain ⟨j,_,rfl⟩ := List.mem_map.mp h; omega)
    rw [eq]
    exact Nat.mul_le_mul (by omega : 2 ≤ e+1) (show 2 ≤ (f+1)*(t.map (·+1)).prod from
      (by omega : 2 ≤ f+1).trans (Nat.le_mul_of_pos_right _ tpos))
  have ha4 := Nat.mul_le_mul_left a minProd
  have hbudget : (s.map (·+1)).prod ≤ (n.minFac-1)/a :=
    (Nat.le_div_iff_mul_le apos).mpr (by rw [mul_comm]; omega)
  have big : (s.map (·+1)).prod ≤ (a+1)*(s.map (·+1)).prod := Nat.le_mul_of_pos_left _ (Nat.succ_pos a)
  have sl := admissible_pattern_length (fun e h => (he e h).1) (by omega)
  refine ⟨a,s,L,?_,perm,order,?_,?_⟩
  · obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero apos.ne'
    apply List.mem_flatMap.mpr
    refine ⟨i,List.mem_filter.mpr ⟨List.mem_range.mpr ?_,decide_eq_true amod⟩,?_⟩
    · have h4 : (i+1)*4 ≤ n.minFac-1 := by omega
      have := (Nat.le_div_iff_mul_le (by decide : 0 < 4)).mpr h4
      omega
    apply List.mem_filterMap.mpr
    refine ⟨s,exponentLists_mem he hbudget sl sort,?_⟩
    have hH : 1 < i+1 ∨ s.any (1 < ·) = true := heavy.imp_right (fun ⟨z,hz,h⟩ =>
      List.any_eq_true.mpr ⟨z.2,perm.mem_iff.mpr (List.mem_map.mpr ⟨z,hz,rfl⟩),decide_eq_true h⟩)
    rw [if_pos (And.intro (show 2 ≤ s.length by omega) hH)]
  · intro z hz
    have h := hL z hz
    exact ⟨h.1,h.2.2.1,h.2.1,h.2.2.2.2⟩
  · simpa only [weight_spec] using bal

end Div245

/- Modular Horner filters for a partially specified prime-power factorization.
The residue sieve adapts DomTheDeveloper's least-prime-433 integer search. -/
namespace Div245
open Finset

theorem small_mod_inverse {q m : ℕ} (hm : 0 < m) (h : q.Coprime m) :
    ∃ z < m, z.Coprime m ∧ q*z ≡ 1 [MOD m] := by
  let t := q^(m.totient-1)
  have hpow : q*t = q^m.totient := by
    have hs := Nat.totient_pos.mpr hm
    rw [show m.totient = m.totient-1+1 by omega] at ⊢
    simp [t,pow_succ']
  have hr : q*(t%m) ≡ 1 [MOD m] :=
    ((Nat.mod_modEq t m).mul_left q).trans (hpow ▸ Nat.ModEq.pow_totient h)
  exact ⟨t%m,Nat.mod_lt _ hm,Nat.coprime_of_mul_modEq_one q (by rwa [mul_comm]),hr⟩

theorem horner_weight_sound (q z m e : ℕ) (h : q*z ≡ 1 [MOD m]) :
    let W := Nat.rec (motive := fun _ => ℕ) (1%m) (fun i r => (i+2+z*r)%m) e
    (∑ j ∈ range (e+1), (j+1)*q^j) ≡ q^e*W [MOD m] := by
  dsimp only
  induction e with
  | zero => simpa using (Nat.mod_modEq 1 m).symm
  | succ e ih =>
    let r := Nat.rec (motive := fun _ => ℕ) (1%m) (fun i v => (i+2+z*v)%m) e
    change _ ≡ q^e*r [MOD m] at ih
    rw [sum_range_succ _ (e+1)]
    change _ ≡ q^(e+1)*((e+2+z*r)%m) [MOD m]
    calc
      _ ≡ q^e*r + (e+2)*q^(e+1) [MOD m] := ih.add (Nat.ModEq.refl _)
      _ ≡ q^e*r*(q*z) + (e+2)*q^(e+1) [MOD m] := by
        simpa using (h.symm.mul_left (q^e*r)).add_right ((e+2)*q^(e+1))
      _ = q^(e+1)*(e+2+z*r) := by rw [pow_succ]; ring
      _ ≡ _ [MOD m] := (Nat.mod_modEq _ m).symm.mul_left _

/-- The choices can be shared across many nodes. They need only contain the
Horner value for each possible inverse residue, and need not be exact. -/
theorem general_mod_witness (m U V goal : ℕ) (L : List (ℕ × ℕ)) (hm : 0 < m)
    (hu : ∀ s ∈ L, s.1.Coprime m)
    (bal : U*(L.map (fun s => ∑ j ∈ range (s.2+1), (j+1)*s.1^j)).prod =
      (goal*V)*(L.map (fun s => s.1^s.2)).prod)
    (C : ℕ → List ℕ)
    (covers : ∀ e ∈ L.map Prod.snd, ∀ z < m, z.Coprime m →
      Nat.rec (motive := fun _ => ℕ) (1%m) (fun i r => (i+2+z*r)%m) e ∈ C e) :
    ∃ rs : List ℕ, List.Forall₂ (fun e v => v ∈ C e) (L.map Prod.snd) rs ∧
      U*rs.prod ≡ goal*V [MOD m] := by
  let T (s : ℕ × ℕ) := ∑ j ∈ range (s.2+1), (j+1)*s.1^j
  let N (s : ℕ × ℕ) := s.1^s.2
  let hor (z e : ℕ) := Nat.rec (motive := fun _ => ℕ) (1%m) (fun i r => (i+2+z*r)%m) e
  have aux (S : List (ℕ × ℕ)) (hS : ∀ s ∈ S, s ∈ L) :
      ∃ rs : List ℕ, List.Forall₂ (fun e v => v ∈ C e) (S.map Prod.snd) rs ∧
        (S.map T).prod ≡ (S.map N).prod * rs.prod [MOD m] := by
    induction S with
    | nil => exact ⟨[], .nil, by simp; rfl⟩
    | cons s S ih =>
      have sm := hS s (by simp)
      obtain ⟨rs,hr,hs⟩ := ih (fun t ht => hS t (List.mem_cons_of_mem _ ht))
      obtain ⟨z,zlt,zc,zinv⟩ := small_mod_inverse hm (hu s sm)
      have mem : hor z s.2 ∈ C s.2 := covers s.2 (List.mem_map.mpr ⟨s,sm,rfl⟩) z zlt zc
      refine ⟨hor z s.2 :: rs,.cons mem hr,?_⟩
      simp only [List.map_cons,List.prod_cons]
      have he : T s ≡ N s*hor z s.2 [MOD m] := horner_weight_sound _ _ _ _ zinv
      simpa only [mul_mul_mul_comm (N s) (hor z s.2)] using he.mul hs
  obtain ⟨rs,mem,ht⟩ := aux L (fun _ h => h)
  refine ⟨rs,mem,?_⟩
  have hc : m.Coprime (L.map N).prod := Nat.coprime_list_prod_right_iff.mpr (by
    intro t th
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp th
    exact ((hu s hs).pow_left _).symm)
  apply Nat.ModEq.cancel_left_of_coprime hc
  calc
    _ = U*((L.map N).prod*rs.prod) := by ring
    _ ≡ U*(L.map T).prod [MOD m] := ht.symm.mul_left _
    _ = (L.map N).prod*(goal*V) := bal.trans (by ring)

theorem general_mod_filter_perm (m U V goal : ℕ) (L : List (ℕ × ℕ)) (hm : 0 < m)
    (hu : ∀ s ∈ L, s.1.Coprime m)
    (bal : U*(L.map (fun s => ∑ j ∈ range (s.2+1), (j+1)*s.1^j)).prod =
      (goal*V)*(L.map (fun s => s.1^s.2)).prod)
    (C : ℕ → List ℕ)
    (covers : ∀ e ∈ L.map Prod.snd, ∀ z < m, z.Coprime m →
      Nat.rec (motive := fun _ => ℕ) (1%m) (fun i r => (i+2+z*r)%m) e ∈ C e) (es : List ℕ) (perm : es.Perm (L.map Prod.snd)) :
    let step (e : ℕ) (t : Option (List ℕ)) :=
      if t.isNone && (C e).any (fun v => v.Coprime m) then none else
        let old := t.getD (List.range m)
        let new := ((C e).flatMap (fun v => old.map (fun x => v*x%m))).eraseDups
        if new.length == m then none else some new
    let reach := es.foldr step (some [1%m])
    (match reach with
      | none => decide (U.gcd m ∣ goal*V)
      | some xs => xs.any (fun r => (U*r)%m == (goal*V)%m)) = true := by
  let step (e : ℕ) (t : Option (List ℕ)) :=
    if t.isNone && (C e).any (fun v => v.Coprime m) then none else
      let old := t.getD (List.range m)
      let new := ((C e).flatMap (fun v => old.map (fun x => v*x%m))).eraseDups
      if new.length == m then none else some new
  let reach (es : List ℕ) := es.foldr step (some [1%m])
  obtain ⟨rs,hr,hres⟩ := general_mod_witness m U V goal L hm hu bal C covers
  have present {es vs : List ℕ} (cover : List.Forall₂ (fun e v => v ∈ C e) es vs)
      (xs : List ℕ) (eq : reach es = some xs) : vs.prod%m ∈ xs := by
    induction cover generalizing xs with
    | nil => change some [1%m] = some xs at eq; cases eq; simp
    | @cons e v es vs hv hvs ih =>
      change step e (reach es) = some xs at eq
      have inside : vs.prod%m ∈ (reach es).getD (List.range m) := by
        cases ht : reach es with
        | none => exact List.mem_range.mpr (Nat.mod_lt _ hm)
        | some ys => exact ih ys ht
      unfold step at eq
      split at eq <;> try contradiction
      dsimp only at eq
      split at eq <;> try contradiction
      cases eq
      apply List.mem_eraseDups.mpr
      apply List.mem_flatMap.mpr
      exact ⟨v,hv,List.mem_map.mpr ⟨vs.prod%m,inside,by simp [Nat.mul_mod]⟩⟩
  obtain ⟨vs,hvs,hper⟩ := List.perm_comp_forall₂ perm hr
  rw [←hper.prod_eq] at hres
  change (match reach es with
    | none => decide (U.gcd m ∣ goal*V)
    | some xs => xs.any (fun r => (U*r)%m == (goal*V)%m)) = true
  cases ht : reach es with
  | none =>
    apply decide_eq_true
    apply Nat.modEq_zero_iff_dvd.mp
    exact ((hres.of_dvd (Nat.gcd_dvd_right _ _)).symm).trans
      (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) _))
  | some xs =>
    apply List.any_eq_true.mpr
    exact ⟨_,present hvs xs ht,beq_iff_eq.mpr (((Nat.mod_modEq vs.prod m).mul_left U).trans hres)⟩

theorem general_mod_filter_from (m U V goal : ℕ) (L : List (ℕ × ℕ)) (hm : 0 < m)
    (hu : ∀ s ∈ L, s.1.Coprime m)
    (bal : U*(L.map (fun s => ∑ j ∈ range (s.2+1), (j+1)*s.1^j)).prod =
      (goal*V)*(L.map (fun s => s.1^s.2)).prod)
    (C : ℕ → List ℕ)
    (covers : ∀ e ∈ L.map Prod.snd, ∀ z < m, z.Coprime m →
      Nat.rec (motive := fun _ => ℕ) (1%m) (fun i r => (i+2+z*r)%m) e ∈ C e) :
    let step (e : ℕ) (t : Option (List ℕ)) :=
      if t.isNone && (C e).any (fun v => v.Coprime m) then none else
        let old := t.getD (List.range m)
        let new := ((C e).flatMap (fun v => old.map (fun x => v*x%m))).eraseDups
        if new.length == m then none else some new
    let reach := (L.map Prod.snd).foldr step (some [1%m])
    (match reach with
      | none => decide (U.gcd m ∣ goal*V)
      | some xs => xs.any (fun r => (U*r)%m == (goal*V)%m)) = true :=
  general_mod_filter_perm m U V goal L hm hu bal C covers _ (.refl _)

theorem general_mod_filter (m U V goal : ℕ) (L : List (ℕ × ℕ)) (hm : 0 < m)
    (hu : ∀ s ∈ L, s.1.Coprime m)
    (bal : U*(L.map (fun s => ∑ j ∈ range (s.2+1), (j+1)*s.1^j)).prod =
      (goal*V)*(L.map (fun s => s.1^s.2)).prod)
    (es : List ℕ) (perm : es.Perm (L.map Prod.snd)) :
    let W (z e : ℕ) := Nat.rec (motive := fun _ => ℕ) (1%m) (fun i r => (i+2+z*r)%m) e
    let C (e : ℕ) := (((List.range m).filter (fun z => z.Coprime m)).map (fun z => W z e)).eraseDups
    let step (e : ℕ) (t : Option (List ℕ)) :=
      if t.isNone && (C e).any (fun v => v.Coprime m) then none else
        let old := t.getD (List.range m)
        let new := ((C e).flatMap (fun v => old.map (fun x => v*x%m))).eraseDups
        if new.length == m then none else some new
    let reach := es.foldr step (some [1%m])
    (match reach with
      | none => decide (U.gcd m ∣ goal*V)
      | some xs => xs.any (fun r => (U*r)%m == (goal*V)%m)) = true := by
  intro W C
  apply general_mod_filter_perm m U V goal L hm hu bal C _ es perm
  intro e he z hz hc
  apply List.mem_eraseDups.mpr
  exact List.mem_map.mpr ⟨z, List.mem_filter.mpr ⟨List.mem_range.mpr hz, decide_eq_true hc⟩, rfl⟩

end Div245

/- Arithmetic tables and the certified search. Numeric hints are always checked at the node that uses them. -/
namespace Div245
open Finset

def witnessPool : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,107,109,113,127,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,227,229,233,239,257,263,269,277,281,283,293,311,313,317,337,347,353,359,367,373,383,389,397,401,409,419,421,431,439,443,457,461,463,467,479,487,491,503,509,521,523,557,563,569,577,587,593,599,601,617,641,647,653,659,661,673,677,683,691,719,727,733,751,757,773,797,809,811,821,827,839,853,859,863,881,887,907,929,941,947,977,983,1013,1019,1021,1039,1051,1123,1151,1153,1171,1201,1229,1277,1283,1297,1321,1361,1373,1433,1439,1447,1471,1481,1493,1499,1543,1553,1579,1601,1607,1619,1669,1709,1721,1777,1783,1789,1867,1931,1997,2003,2083,2179,2267,2269,2281,2341,2411,2417,2441,2477,2521,2659,2677,2683,2687,2699,2777,2803,2843,2879,2927,2963,3001,3019,3083,3209,3217,3253,3373,3449,3539,3547,3821,3847,3863,3917,3989,4003,4091,4093,4129,4133,4157,4241,4363,4397,4441,4519,4729,4733,4787,5011,5147,5279,5351,5407,5431,5503,5791,5857,5861,6053,6091,6841,6869,7019,7237,7307,7591,8147,8761,8923,8963,8999,9007,9013,9157,9439,9623,10337,10529,10559,10589,10691,11969,12373,12421,12911,12923,13613,13873,14051,14149,14449,14557,15073,15161,15383,15439,15683,16067,18257,18443,18973,19181,19891,19993,20509,20611,20879,21089,21379,21737,21751,22013,22571,23131,23417,24223,24547,24631,24943,25847,26293,26879,27449,28351,28771,28949,30211,30253,30323,31511,32191,34057,34549,35933,37061,43399,43781,45827,46703,46889,47137,50543,52567,53569,56299,57427,57467,59233,60647,61291,61553,65173,70709,71867,72547,75937,76099,77617,79193,79769,81043,81097,86599,86711,90619,92251,92401,96377,96823,96893,100153,101599,102107,106411,115693,117979,119653,122273,123059,129281,133379,133417,134947,137131,141241,141499,144451,146513,148949,163997,165553,188017,188197,193147,216577,217463,234809,244547,246119,277741,280219,281947,297809,335381,343177,369319,406397,417581,432137,438169,480107,565163,586213,612109,612643,626317,630433,651731,685093,712183,727021,752789,756641,773867,779101,980137,1032841,1034503,1087451,1183157,1288249,1316921,1324361,1339669,1361401,1383301,1576723,1834799,2053201,2139757,2155171,2203589,2523217,2755463,2811659,2817709,2879803,3298811,3321037,3372641,3617069,3617951,3669599,3964733,4446433,4471171,4536179,4636711,5053693,5537881,5547277,5839291,5986961,6201863,6468031,6861697,7083499,7098943,7212319,7522901,7710161,8330963,9072359,10545211,12688981,12741733,14397319,15308633,18244067,21873097,23601373,24352957,24505219,30401537,30978047,32586551,33730001,33825601,33926887,40471693,42897313,48575101,50901259,53244353,62431921,63017483,63271267,65173103,65580481,66052783,67621321,74718443,75879569,79866529,93807871,95298881,105518341,132852787,136306273,138561641,142009289,151916899,155323757,160962157,168668873,172225117,179044939,179415311,185468441,190597763,207911719,246020669,261672379,279509459,339268871,383342923,517881713,590572933,615806327,744163223,825906901,1169845093,1182320609,1506537079,2036050361,2191766131,2581316131,2624279201,2840185781,2898677407,3354113509,4576002647,4847190743,4929079429,5680371563,6144547567,6569011187,6845751949,7631124997,8098937527,8260528891,8502578369,10776932423,12747358969,15376226549,17603588341,18826432871,23164549021,24219708673,26301193573,28986774071,30301253953,32008271723,37652865743,50363928533,51467697121,58695306629,61150311611,65110972211,102058480283,105679530977,117390613259,131022650417,154783264061,167687167009,214805549993,234787945631,274952110187,398871487529,408716967719,555240796003,581776445227,595861556993,797742975059,826629447841,1302219444221,1596161396191,1719798921283,1951101465767,2725310640323,3094619080181,3478412888521,4139134143421,4775975935363,7088352000427,8559853947041,9752308271351,10417755553769,13974006881147,14359373551063,19103903741453,20835511107539,22374118403621,33311847537949,44748236807243,63062515328887,81284033392921,150212655155791,182731447799029,319593384716803,635927379490849,1150081090216307,1647238560869113,2807016441703633,3812570706782993,8036300276545637,30486691755424187,44854364709863143,51284105359262441,89706325036871947,196491150919254311,725799727597058927,3498950330708810221,5778784727260815889,14635092528104565487,17640717292851439867,78478332842421863213,86560917171794057467,206708690767055535173,321290896024828567001,920314054593070719437,1880508400376490752657,1883836937069958237217,2168949226838008152479,3826786260314991211367,4844271667741331987201,5124623469105161024569,5525347040369568803507,60407435754889924251403,128718467849545940154241,1493245581621988783545433,2771892741557562936922373,11278310349707882455928579,80757992885189113465213993,1387366555902446403685366447,251341629210651754903736062193,59737124597292648185414913209393,183450530871106267013736211463173,285498811742277931917137438827867,535822240852170004076631088649327,542512058959614745217387126772353,1295309273607968370700398258494227,978421835301554251632360872955392545223,7043093065953921339195010511780395502167,10037566653262838460593813688652541806393,51614441682848567194150820050144397020481,2544456102028701855435052121524386993552097,6591642899211909277635103388839711484157169,12313323426068810258421045085179151336457802703,21759099163796972141780651325712249354887750413,21942162254588833528538249689440133713390636446077,6855613849526198207150406319489725644984945053774794671,966925188529564263993895916700986439713150768980132286531,84026314384070513234463880358495204042562939860627507203821761291,196561891946625316608425590812136130631488792108315348157158819267,262826251005741883539713937612151569908334640758626608520084941393,107032548358919427693327257148782884618685660222072551941378726306878698528344822341221,1104999373555695655228644798455003043045395612543828686530929624300378786997003359907683405568943]

def witnessIndex (t : ℕ) : ℕ :=
  if t < 49081925123953953557047 then
    if t < 4929079429 then
      if t < 2879 then
        if t < 359 then
          if t < 167 then
            if t < 59 then
              if t < 47 then
                if t = 23 then 8 else 0
              else if t = 47 then 14 else
                0
            else if t = 59 then 16 else
              if t < 107 then
                if t = 83 then 22 else 0
              else if t = 107 then 26 else
                0
          else if t = 167 then 36 else
            if t < 263 then
              if t < 227 then
                if t = 179 then 38 else 0
              else if t = 227 then 45 else
                0
            else if t = 263 then 50 else
              if t = 347 then 60 else 0
        else if t = 359 then 62 else
          if t < 587 then
            if t < 479 then
              if t < 467 then
                if t = 383 then 65 else 0
              else if t = 467 then 78 else
                0
            else if t = 479 then 79 else
              if t < 563 then
                if t = 503 then 82 else 0
              else if t = 563 then 87 else
                0
          else if t = 587 then 90 else
            if t < 863 then
              if t < 839 then
                if t = 719 then 104 else 0
              else if t = 839 then 115 else
                0
            else if t = 863 then 118 else
              if t = 1439 then 145 else 0
      else if t = 2879 then 186 else
        if t < 237002261 then
          if t < 65580481 then
            if t < 43720321 then
              if t < 483169 then
                if t = 146053 then 7 else 0
              else if t = 483169 then 9 else
                0
            else if t = 43720321 then 165 else
              if t < 63017483 then
                if t = 53244353 then 463 else 0
              else if t = 63017483 then 465 else
                0
          else if t = 65580481 then 468 else
            if t < 105518341 then
              if t < 86003807 then
                if t = 79866529 then 473 else 0
              else if t = 86003807 then 232 else
                0
            else if t = 105518341 then 476 else
              if t = 148775173 then 217 else 0
        else if t = 237002261 then 138 else
          if t < 1141804901 then
            if t < 436321793 then
              if t < 339268871 then
                if t = 291123193 then 68 else 0
              else if t = 339268871 then 494 else
                0
            else if t = 436321793 then 93 else
              if t < 825906901 then
                if t = 590572933 then 497 else 0
              else if t = 825906901 then 500 else
                0
          else if t = 1141804901 then 153 else
            if t < 4136458369 then
              if t < 2624279201 then
                if t = 1182320609 then 502 else 0
              else if t = 2624279201 then 507 else
                0
            else if t = 4136458369 then 161 else
              if t = 4441044193 then 36 else 0
    else if t = 4929079429 then 513 else
      if t < 33567528520599583 then
        if t < 30301253953 then
          if t < 16012774117 then
            if t < 9840647893 then
              if t < 8752883221 then
                if t = 7998242209 then 81 else 0
              else if t = 8752883221 then 107 else
                0
            else if t = 9840647893 then 176 else
              if t < 15376226549 then
                if t = 10776932423 then 522 else 0
              else if t = 15376226549 then 524 else
                0
          else if t = 16012774117 then 126 else
            if t < 24219708673 then
              if t < 23958967919 then
                if t = 21553864847 then 67 else 0
              else if t = 23958967919 then 271 else
                0
            else if t = 24219708673 then 528 else
              if t = 25937778949 then 63 else 0
        else if t = 30301253953 then 531 else
          if t < 117390613259 then
            if t < 58695306629 then
              if t < 51467697121 then
                if t = 35937827329 then 294 else 0
              else if t = 51467697121 then 535 else
                0
            else if t = 58695306629 then 536 else
              if t < 87885386881 then
                if t = 79407368353 then 89 else 0
              else if t = 87885386881 then 244 else
                0
          else if t = 117390613259 then 541 else
            if t < 925325831809 then
              if t < 826629447841 then
                if t = 167687167009 then 544 else 0
              else if t = 826629447841 then 554 else
                0
            else if t = 925325831809 then 229 else
              if t = 11409736151344987 then 273 else 0
      else if t = 33567528520599583 then 478 else
        if t < 816756997050845951203 then
          if t < 78478332842421863213 then
            if t < 18540524095493500147 then
              if t < 7673499757945271287 then
                if t = 7258524516452639693 then 353 else 0
              else if t = 7673499757945271287 then 343 else
                0
            else if t = 18540524095493500147 then 364 else
              if t < 60568888486637611063 then
                if t = 30281576126618046103 then 220 else 0
              else if t = 60568888486637611063 then 248 else
                0
          else if t = 78478332842421863213 then 596 else
            if t < 206708690767055535173 then
              if t < 157978731934229489089 then
                if t = 86560917171794057467 then 597 else 0
              else if t = 157978731934229489089 then 304 else
                0
            else if t = 206708690767055535173 then 598 else
              if t = 321290896024828567001 then 599 else 0
        else if t = 816756997050845951203 then 331 else
          if t < 2147767397734500229249 then
            if t < 1713590209716498536641 then
              if t < 945938289746091443881 then
                if t = 920314054593070719437 then 600 else 0
              else if t = 945938289746091443881 then 347 else
                0
            else if t = 1713590209716498536641 then 107 else
              if t = 1891884315773207693659 then 367 else 0
          else if t = 2147767397734500229249 then 529 else
            if t < 3321492140250112929323 then
              if t < 2295407966297662736581 then
                if t = 2175379767111025975853 then 461 else 0
              else if t = 2295407966297662736581 then 339 else
                0
            else if t = 3321492140250112929323 then 88 else
              if t = 3732893566943963764663 then 129 else 0
  else if t = 49081925123953953557047 then 184 else
    if t < 1295309273607968370700398258494227 then
      if t < 64759081175304360319553411521 then
        if t < 18702491064238011493655719 then
          if t < 2771892741557562936922373 then
            if t < 242951944188731333369347 then
              if t < 128718467849545940154241 then
                if t = 60407435754889924251403 then 608 else 0
              else if t = 128718467849545940154241 then 609 else
                0
            else if t = 242951944188731333369347 then 315 else
              if t < 1400969294066055605592223 then
                if t = 442413679186808168105281 then 311 else 0
              else if t = 1400969294066055605592223 then 105 else
                0
          else if t = 2771892741557562936922373 then 611 else
            if t < 10584971249173752318186307 then
              if t < 6587003849607279040020173 then
                if t = 5906651059556759518621403 then 280 else 0
              else if t = 6587003849607279040020173 then 394 else
                0
            else if t = 10584971249173752318186307 then 436 else
              if t = 14783831712828429538102891 then 416 else 0
        else if t = 18702491064238011493655719 then 516 else
          if t < 14139206291326773519477874087 then
            if t < 4598973724804293203264795239 then
              if t < 2307855668468764624513726333 then
                if t = 1566308637243893215934604907 then 238 else 0
              else if t = 2307855668468764624513726333 then 148 else
                0
            else if t = 4598973724804293203264795239 then 140 else
              if t < 9393338530198612112523993259 then
                if t = 4617269645964179326424153359 then 188 else 0
              else if t = 9393338530198612112523993259 then 40 else
                0
          else if t = 14139206291326773519477874087 then 96 else
            if t < 28203632572748259430441470337 then
              if t < 18835856843277845230872719467 then
                if t = 14525758687140665798199574753 then 442 else 0
              else if t = 18835856843277845230872719467 then 65 else
                0
            else if t = 28203632572748259430441470337 then 496 else
              if t = 48871223004494007033573379451 then 413 else 0
      else if t = 64759081175304360319553411521 then 84 else
        if t < 94520369816899037987564797079659 then
          if t < 2046711459910507326617650129351 then
            if t < 271470865719051332912130721387 then
              if t < 251341629210651754903736062193 then
                if t = 84420692772290168898140046233 then 100 else 0
              else if t = 251341629210651754903736062193 then 615 else
                0
            else if t = 271470865719051332912130721387 then 210 else
              if t < 1872679802220114940939823098027 then
                if t = 1428694141859127181344356262439 then 86 else 0
              else if t = 1872679802220114940939823098027 then 370 else
                0
          else if t = 2046711459910507326617650129351 then 131 else
            if t < 59730318530503792254774275686567 then
              if t < 48795181919394697209753746896219 then
                if t = 22547172401151657976654983513031 then 483 else 0
              else if t = 48795181919394697209753746896219 then 348 else
                0
            else if t = 59730318530503792254774275686567 then 119 else
              if t = 59737124597292648185414913209393 then 616 else 0
        else if t = 94520369816899037987564797079659 then 235 else
          if t < 404658629364440909062938446689481 then
            if t < 129830457836044118268132561142279 then
              if t < 116556499959428119088461936576729 then
                if t = 97590760357385510060762580813679 then 368 else 0
              else if t = 116556499959428119088461936576729 then 573 else
                0
            else if t = 129830457836044118268132561142279 then 135 else
              if t = 285498811742277931917137438827867 then 618 else 0
          else if t = 404658629364440909062938446689481 then 545 else
            if t < 809317258730765655062946851616179 then
              if t < 542512058959614745217387126772353 then
                if t = 535822240852170004076631088649327 then 619 else 0
              else if t = 542512058959614745217387126772353 then 620 else
                0
            else if t = 809317258730765655062946851616179 then 602 else
              if t = 1085024117919229490434774253544707 then 310 else 0
    else if t = 1295309273607968370700398258494227 then 621 else
      if t < 512421042177411553973269718552714480703457249191691228957 then
        if t < 21942162254588833528538249689440133713390636446077 then
          if t < 980240008928045191484034840632341433 then
            if t < 28464289427306319171061324702306091 then
              if t < 14844819404615886150962862445591073 then
                if t = 10250990473007666159540261537444851 then 316 else 0
              else if t = 14844819404615886150962862445591073 then 514 else
                0
            else if t = 28464289427306319171061324702306091 then 290 else
              if t < 704874619352457019966932560735319953 then
                if t = 65540653920247352439548027911015313 then 575 else 0
              else if t = 704874619352457019966932560735319953 then 67 else
                0
          else if t = 980240008928045191484034840632341433 then 51 else
            if t < 5701237573659750880600680846937521241498896415813 then
              if t < 151554438293723473063103590663593738195508912601 then
                if t = 76687320965866004934515079827887348273 then 338 else 0
              else if t = 151554438293723473063103590663593738195508912601 then 228 else
                0
            else if t = 5701237573659750880600680846937521241498896415813 then 562 else
              if t = 17631905465723025258668822303289310981886016783733 then 307 else 0
        else if t = 21942162254588833528538249689440133713390636446077 then 630 else
          if t < 31256566762997468691536760709259949459505464857225421949 then
            if t < 67827396300041118835123719170646624597892162459092157 then
              if t < 5460414043290747267909288507733140402795991442448253 then
                if t = 1144668841161390357589773810442968295737004032896557 then 231 else 0
              else if t = 5460414043290747267909288507733140402795991442448253 then 84 else
                0
            else if t = 67827396300041118835123719170646624597892162459092157 then 103 else
              if t < 5532814378719807215479260666360488418603248897113147189 then
                if t = 491729044785757214401919733116018340436294532484980773 then 520 else 0
              else if t = 5532814378719807215479260666360488418603248897113147189 then 402 else
                0
          else if t = 31256566762997468691536760709259949459505464857225421949 then 218 else
            if t < 154748663622935106336597706075796368801906653776575461709 then
              if t < 54004668358414534379925553857547965918788564432120936869 then
                if t = 44281156893788553576302335036563148595745193519885170463 then 626 else 0
              else if t = 54004668358414534379925553857547965918788564432120936869 then 108 else
                0
            else if t = 154748663622935106336597706075796368801906653776575461709 then 76 else
              if t = 464952147384778540323123503532985342729263769765297513813 then 578 else 0
      else if t = 512421042177411553973269718552714480703457249191691228957 then 82 else
        if t < 18961603859321011764912772840970823946342952956996225329819937440851 then
          if t < 997998800099564865641500904781903220146115073157489959128360117 then
            if t < 144655683785001510700095542067704531521020970271632348831374647 then
              if t < 12320297498930567528484829674219839609647612000765552055706829 then
                if t = 1044629310980995374400386805499234928122306394688239743989669 then 103 else 0
              else if t = 12320297498930567528484829674219839609647612000765552055706829 then 63 else
                0
            else if t = 144655683785001510700095542067704531521020970271632348831374647 then 168 else
              if t < 551973519021857121271367943468616089396920100232370578238483269 then
                if t = 430645560270828759371775053235047996193630588095006671621238351 then 106 else 0
              else if t = 551973519021857121271367943468616089396920100232370578238483269 then 75 else
                0
          else if t = 997998800099564865641500904781903220146115073157489959128360117 then 472 else
            if t < 196561891946625316608425590812136130631488792108315348157158819267 then
              if t < 84026314384070513234463880358495204042562939860627507203821761291 then
                if t = 1933670619401360698564891152559167109772300414565997015245219853 then 184 else 0
              else if t = 84026314384070513234463880358495204042562939860627507203821761291 then 633 else
                0
            else if t = 196561891946625316608425590812136130631488792108315348157158819267 then 634 else
              if t = 3123383298401663432753546422264664727369285893299628873155306340351 then 183 else 0
        else if t = 18961603859321011764912772840970823946342952956996225329819937440851 then 389 else
          if t < 133575142675315683699443380239997260139484593956001264495119212879150908624045945634711344728943 then
            if t < 1961682437173846416682124486554074251243551264284106993751850689416142328213847551082603 then
              if t < 1002076123313318897666547481692941484565750951258209214533898876206114799354581692935003 then
                if t = 27920775912976275081056459470371368493193072892135350649184868792750790873055244662283 then 498 else 0
              else if t = 1002076123313318897666547481692941484565750951258209214533898876206114799354581692935003 then 87 else
                0
            else if t = 1961682437173846416682124486554074251243551264284106993751850689416142328213847551082603 then 95 else
              if t = 28676109780557753513480679987535373748023231337232358771393083117286896315808169342408799584823 then 121 else 0
          else if t = 133575142675315683699443380239997260139484593956001264495119212879150908624045945634711344728943 then 346 else
            if t < 2711523315979382797379784681314516033127847104787744630395250529707451494370598398298883056974693193420058786744979662357372297 then
              if t < 119423019558631941251094767638016708023800357627692540791021138533126238017233271901757703278558056207 then
                if t = 1104999373555695655228644798455003043045395612543828686530929624300378786997003359907683405568943 then 637 else 0
              else if t = 119423019558631941251094767638016708023800357627692540791021138533126238017233271901757703278558056207 then 152 else
                0
            else if t = 2711523315979382797379784681314516033127847104787744630395250529707451494370598398298883056974693193420058786744979662357372297 then 157 else
              if t = 304154027500985502429216944604452514070065952733465713953023976967129770851531077599153110272510365082059265537358311596203074982009189790535868566777076318795256939233153857554357994368982981456888935335805924553404665709846949 then 74 else 0

def witness (F : ℕ) : ℕ := witnessPool.getD (witnessIndex F) 2

def hashState (s : List ℕ) (U V : ℕ) : ℕ := s.foldl (fun h e => (113*h+e)%1000000007) ((101*U+V)%1000000007)

def modHint (t : ℕ) : ℕ :=
  if t < 480067066 then
    if t < 208820251 then
      if t < 119692737 then
        if t < 49440548 then
          if t < 17496822 then
            if t < 11574315 then
              if t = 6153654 then 9 else 0
            else if t = 11574315 then 27 else
              if t = 13755601 then 3 else 0
          else if t = 17496822 then 3 else
            if t < 36231148 then
              if t = 21215703 then 3 else 0
            else if t = 36231148 then 27 else
              0
        else if t = 49440548 then 3 else
          if t < 68679507 then
            if t < 62195170 then
              if t = 60345058 then 3 else 0
            else if t = 62195170 then 9 else
              if t = 62860554 then 3 else 0
          else if t = 68679507 then 27 else
            if t < 84523196 then
              if t = 82070420 then 27 else 0
            else if t = 84523196 then 9 else
              0
      else if t = 119692737 then 3 else
        if t < 163550892 then
          if t < 141509987 then
            if t < 127989445 then
              if t = 127444315 then 3 else 0
            else if t = 127989445 then 3 else
              if t = 133500064 then 9 else 0
          else if t = 141509987 then 3 else
            if t < 148510134 then
              if t = 146314431 then 3 else 0
            else if t = 148510134 then 3 else
              0
        else if t = 163550892 then 3 else
          if t < 188641171 then
            if t < 181019775 then
              if t = 178189191 then 8 else 0
            else if t = 181019775 then 3 else
              if t = 181886021 then 3 else 0
          else if t = 188641171 then 3 else
            if t < 200214524 then
              if t = 196626116 then 3 else 0
            else if t = 200214524 then 3 else
              0
    else if t = 208820251 then 3 else
      if t < 325583417 then
        if t < 284465137 then
          if t < 265146051 then
            if t < 222604339 then
              if t = 211300739 then 3 else 0
            else if t = 222604339 then 3 else
              if t = 246524465 then 3 else 0
          else if t = 265146051 then 3 else
            if t < 279312805 then
              if t = 265548125 then 27 else 0
            else if t = 279312805 then 3 else
              0
        else if t = 284465137 then 3 else
          if t < 300435974 then
            if t < 294773317 then
              if t = 287460761 then 3 else 0
            else if t = 294773317 then 3 else
              if t = 298172481 then 9 else 0
          else if t = 300435974 then 3 else
            if t < 323814792 then
              if t = 311525878 then 3 else 0
            else if t = 323814792 then 3 else
              0
      else if t = 325583417 then 27 else
        if t < 413177936 then
          if t < 382935628 then
            if t < 364183467 then
              if t = 349605994 then 3 else 0
            else if t = 364183467 then 27 else
              if t = 366286827 then 27 else 0
          else if t = 382935628 then 3 else
            if t < 396995896 then
              if t = 387968408 then 3 else 0
            else if t = 396995896 then 3 else
              0
        else if t = 413177936 then 9 else
          if t < 459960051 then
            if t < 434633123 then
              if t = 415197123 then 3 else 0
            else if t = 434633123 then 3 else
              0
          else if t = 459960051 then 3 else
            if t < 478613995 then
              if t = 461326648 then 3 else 0
            else if t = 478613995 then 3 else
              0
  else if t = 480067066 then 3 else
    if t < 739154297 then
      if t < 634025128 then
        if t < 574911373 then
          if t < 540434035 then
            if t < 527128752 then
              if t = 506864859 then 3 else 0
            else if t = 527128752 then 27 else
              if t = 534000112 then 27 else 0
          else if t = 540434035 then 3 else
            if t < 554272285 then
              if t = 551078140 then 9 else 0
            else if t = 554272285 then 3 else
              0
        else if t = 574911373 then 27 else
          if t < 630715606 then
            if t < 618589226 then
              if t = 585254164 then 3 else 0
            else if t = 618589226 then 3 else
              if t = 628148198 then 3 else 0
          else if t = 630715606 then 27 else
            if t < 633836969 then
              if t = 632667540 then 9 else 0
            else if t = 633836969 then 27 else
              0
      else if t = 634025128 then 9 else
        if t < 689672742 then
          if t < 683542147 then
            if t < 660468297 then
              if t = 653497253 then 3 else 0
            else if t = 660468297 then 3 else
              if t = 679143994 then 9 else 0
          else if t = 683542147 then 27 else
            if t < 688558436 then
              if t = 686516110 then 3 else 0
            else if t = 688558436 then 3 else
              0
        else if t = 689672742 then 3 else
          if t < 729993725 then
            if t < 700123481 then
              if t = 698374717 then 9 else 0
            else if t = 700123481 then 3 else
              0
          else if t = 729993725 then 3 else
            if t < 738964978 then
              if t = 730623899 then 3 else 0
            else if t = 738964978 then 9 else
              0
    else if t = 739154297 then 3 else
      if t < 911097229 then
        if t < 832735496 then
          if t < 789048981 then
            if t < 747360864 then
              if t = 745265695 then 3 else 0
            else if t = 747360864 then 3 else
              if t = 769688133 then 3 else 0
          else if t = 789048981 then 3 else
            if t < 811048420 then
              if t = 801861426 then 3 else 0
            else if t = 811048420 then 27 else
              0
        else if t = 832735496 then 27 else
          if t < 882692886 then
            if t < 844279877 then
              if t = 834527031 then 3 else 0
            else if t = 844279877 then 3 else
              if t = 861876936 then 3 else 0
          else if t = 882692886 then 3 else
            if t < 899813401 then
              if t = 898136186 then 3 else 0
            else if t = 899813401 then 3 else
              0
      else if t = 911097229 then 3 else
        if t < 988084632 then
          if t < 972818527 then
            if t < 927970890 then
              if t = 926166647 then 3 else 0
            else if t = 927970890 then 3 else
              if t = 940041511 then 3 else 0
          else if t = 972818527 then 3 else
            if t < 977213804 then
              if t = 973742064 then 3 else 0
            else if t = 977213804 then 9 else
              0
        else if t = 988084632 then 3 else
          if t < 993137643 then
            if t < 990568733 then
              if t = 988694920 then 9 else 0
            else if t = 990568733 then 3 else
              0
          else if t = 993137643 then 27 else
            if t < 998391585 then
              if t = 997834539 then 3 else 0
            else if t = 998391585 then 27 else
              0

def spanHint (t : ℕ) : ℕ :=
  if t < 476352295 then
    if t < 463493115 then
      if t = 224616780 then 7732 else 0
    else if t = 463493115 then 236 else
      0
  else if t = 476352295 then 624 else
    if t < 994287701 then
      if t = 703793775 then 4802 else 0
    else if t = 994287701 then 2813 else
      0

def width (_lo : ℕ) (s : List ℕ) (U V : ℕ) := spanHint (hashState s U V)

def modularTest (m : ℕ) (es : List ℕ) (U V : ℕ) : Bool :=
  let W (z e : ℕ) := Nat.rec (motive := fun _ => ℕ) (1%m) (fun i r => (i+2+z*r)%m) e
  let C (e : ℕ) := (((List.range m).filter (fun z => z.Coprime m)).map (fun z => W z e)).eraseDups
  let step (e : ℕ) (t : Option (List ℕ)) :=
    if t.isNone && (C e).any (fun v => v.Coprime m) then none else
      let old := t.getD (List.range m)
      let new := ((C e).flatMap (fun v => old.map (fun x => v*x%m))).eraseDups
      if new.length == m then none else some new
  let reach := es.foldr step (some [1%m])
  (match reach with
    | none => decide (U.gcd m ∣ V)
    | some xs => xs.any (fun r => (U*r)%m == (V)%m))

def gate (lo : ℕ) (s : List ℕ) (U V : ℕ) : Bool :=
  let m := modHint (hashState s U V)
  if 0 < m ∧ m < lo then modularTest m s U V else true


def scan (lo : ℕ) (k : ℕ) (s : List ℕ) (U V A : ℕ) : Bool :=
  Nat.rec (motive := fun _ => List ℕ → ℕ → ℕ → ℕ → Bool) (fun _ _ _ _ => true)
    (scanStep weight witness (fun _ => true) width gate lo) k s U V A

def analyticRow (p a : ℕ) (s : List ℕ) : Bool :=
  (s == [1,1] && decide (11 ≤ a)) ||
  ((a::s).any (fun e => decide (21 ≤ e ∧ e ≤ 45 ∧ 197 ≤ p ∧ 8*e+3 ≤ p) &&
    (((a::s).erase e) == [1,1,1]))) ||
  (s == [1,4] && ((p==251 && a==25) || (p==389 && a==37)))

def rootCheck (p : ℕ) : Bool :=
  (rootList p).all (fun t => analyticRow p t.1 t.2 ||
    !scan (p+1) 9 t.2 (weight p t.1)
      (p^t.1*((t.1+1)*(t.2.map (·+1)).prod+1)) p.factorial)

end Div245

/- Soundness of the modular gate. -/
namespace Div245
theorem gate_spec (lo : ℕ) (s : List ℕ) (U V : ℕ) (L : List (ℕ×ℕ))
    (perm : s.Perm (L.map Prod.snd)) (hp : ∀ z ∈ L, z.1.Prime ∧ lo ≤ z.1)
    (bal : U*(L.map (fun z => weight z.1 z.2)).prod = V*(L.map (fun z => z.1^z.2)).prod) :
    gate lo s U V = true := by
  let m := modHint (hashState s U V)
  change (if 0 < m ∧ m < lo then modularTest m s U V else true) = true
  split
  next h =>
    have c (z : ℕ×ℕ) (hz : z ∈ L) : z.1.Coprime m := by
      apply (hp z hz).1.coprime_iff_not_dvd.mpr
      intro d
      have le := Nat.le_of_dvd h.1 d
      have := (hp z hz).2
      omega
    have hh := general_mod_filter m U V 1 L h.1 c (by simpa only [one_mul,weight_spec] using bal) s perm
    let W (z e : ℕ) := Nat.rec (motive := fun _ => ℕ) (1%m) (fun i r => (i+2+z*r)%m) e
    let C (e : ℕ) := (((List.range m).filter (fun z => z.Coprime m)).map (fun z => W z e)).eraseDups
    let step (e : ℕ) (t : Option (List ℕ)) :=
      if t.isNone && (C e).any (fun v => v.Coprime m) then none else
        let old := t.getD (List.range m)
        let new := ((C e).flatMap (fun v => old.map (fun x => v*x%m))).eraseDups
        if new.length == m then none else some new
    let reach := s.foldr step (some [1%m])
    change (match reach with
      | none => decide (U.gcd m ∣ V)
      | some xs => xs.any (fun r => (U*r)%m == V%m)) = true
    have hmod : (match reach with
      | none => decide (U.gcd m ∣ 1*V)
      | some xs => xs.any (fun r => (U*r)%m == (1*V)%m)) = true := by
      cases hreach : reach with
      | none => dsimp only [reach,step,C,W] at hreach; simpa only [hreach] using hh
      | some xs => dsimp only [reach,step,C,W] at hreach; simpa only [hreach] using hh
    cases hr : reach <;> simpa only [hr,one_mul] using hmod
  next _ => rfl

end Div245

/- An affine closed formula for the moment of a prime power. -/

namespace Div245
open Finset

theorem weighted_closed_exact (p a : ℕ) (hp : 1<p) :
    (p-1)^2*(∑ j ∈ range (a+1), (j+1)*p^j)=((a+1)*p^2-(a+2)*p)*p^a+1 := by
  have hd : (p-1)^2+2*p=p^2+1 := by
    obtain ⟨u,hu⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p≠0)
    subst p
    simp
    ring
  have hw (e : ℕ) : (p-1)^2*(∑ j ∈ range (e+1), (j+1)*p^j)+(e+2)*p*p^e =
      (e+1)*p^2*p^e+1 := by
    induction e with
    | zero => simpa using hd
    | succ e ih =>
      rw [sum_range_succ _ (e+1),pow_succ p e]
      have hx := congrArg (fun i => i*((e+2)*p*p^e)) hd
      nlinarith only [ih,hx]
  let H := (a+1)*p^2-(a+2)*p
  have hsmall : a+2 ≤ (a+1)*p := by
    have h := Nat.mul_le_mul_left (a+1) (by omega : 2≤p)
    omega
  have hcoef : (a+2)*p ≤ (a+1)*p^2 := by
    simpa only [pow_two, mul_assoc] using Nat.mul_le_mul_right p hsmall
  have hh : H+(a+2)*p = (a+1)*p^2 := Nat.sub_add_cancel hcoef
  have hx := congrArg (fun k => k*p^a) hh
  change (p-1)^2*(∑ j ∈ range (a+1), (j+1)*p^j)=H*p^a+1
  nlinarith only [hw a,hx]

theorem weighted_closed_affine (p a : ℕ) (hp : 1<p) (ha : a+1<p) :
    ∃ H : ℕ, (p-1)^2*(∑ j ∈ range (a+1), (j+1)*p^j)=H*p^a+1 ∧ H+1≤p^3 := by
  refine ⟨(a+1)*p^2-(a+2)*p,weighted_closed_exact p a hp,?_⟩
  have hh' := Nat.mul_lt_mul_of_pos_right ha (show 0<p^2 by positivity)
  rw [show p^3=p*p^2 by ring]
  omega

theorem affine_gap_lower {N d g h k : ℕ} (he : d*g+h=N*k) (hp : 0<h)
    (hh : 2*h≤N) : N≤2*(d*g) := by
  have hk : 0<k := by by_contra! hz; simp [show k=0 by omega] at he; omega
  have hi := Nat.le_mul_of_pos_right N hk
  omega

theorem affine_gap_multiple {N d U H B c : ℕ} (hN : 0<N) (hU : d*U=H*N+1)
    (hle : c*U≤B*N) : ∃ k, d*(B*N-c*U)+c=N*k := by
  have i := Nat.mul_le_mul_left d hle
  have eq := congrArg (c*·) hU
  have ib : c*H ≤ d*B := by
    apply Nat.le_of_mul_le_mul_right _ hN
    nlinarith only [i,eq]
  refine ⟨d*B-c*H,?_⟩
  have z := congrArg (d*·) (Nat.sub_add_cancel hle)
  have w := congrArg (N*·) (Nat.sub_add_cancel ib)
  nlinarith only [eq,z,w]

end Div245

/- Bounding and checking small exponents with two simple factors. -/

namespace Div245
open Finset

theorem simple_root_data {q r U V : ℕ} (hq : 0<q) (hqr : q≤r) (hu : 0<U)
    (balance : U*((2*q+1)*(2*r+1))=V*(q*r)) :
    let g := V-4*U
    0<g ∧ q≤5*U/g ∧ r = U*(2*q+1)/(g*q-2*U) := by
  let g := V-4*U
  have rp : 0<r := by omega
  have low : 4*U<V := by
    apply Nat.lt_of_mul_lt_mul_right (a:=q*r)
    have j := Nat.mul_lt_mul_of_pos_left (by nlinarith only [Nat.zero_le q,Nat.zero_le r] :
      4*(q*r)<(2*q+1)*(2*r+1)) hu
    nlinarith only [j,balance]
  have ge : g+4*U=V := Nat.sub_add_cancel low.le
  have hc : (g*q)*r=U*(2*q+2*r+1) := by
    have j := congrArg (fun v => v*(q*r)) ge
    nlinarith only [j,balance]
  have gp : 0<g := by dsimp [g]; omega
  refine ⟨gp,(Nat.le_div_iff_mul_le gp).mpr ?_,?_⟩
  · apply Nat.le_of_mul_le_mul_right _ rp
    have i := Nat.mul_le_mul_left U (by omega : 2*q+2*r+1≤5*r)
    nlinarith only [hc,i]
  · have hi : 2*U<g*q := by
      apply Nat.lt_of_mul_lt_mul_right (a:=r)
      nlinarith only [hc,hu, Nat.zero_le (U*q)]
    have eq := congrArg (·*r) (Nat.sub_add_cancel hi.le)
    have h : U*(2*q+1)=(g*q-2*U)*r := by nlinarith only [hc,eq]
    change r=U*(2*q+1)/(g*q-2*U)
    rw [h, Nat.mul_div_cancel_left _ (by omega)]

theorem simple_weighted_upper {p e : ℕ} (he : e+1≤p) :
    (∑ j ∈ range (e+1), (j+1)*p^j) ≤ (e+2)*p^e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_range_succ _ (e+1)]
    have prev := ih (by omega)
    have ub := Nat.mul_le_mul_right (p^e) he
    rw [pow_succ' p e]
    nlinarith only [prev,ub]

theorem simple_root_ceiling {p a q r : ℕ} (ha : 0<a) (hpq : p<q) (hqr : q≤r)
    (balance : (∑ j ∈ range (a+1), (j+1)*p^j)*((2*q+1)*(2*r+1)) =
      ((4*a+5)*p^a)*(q*r)) : p ≤ 10*(a+2) := by
  by_contra! high
  obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  have hp : 0<p := by omega
  let M := ∑ j ∈ range (b+1), (j+1)*p^j
  let N := p^(b+1)
  let U := M+(b+2)*N
  let B := 4*(b+1)+5
  have ub : M≤(b+2)*p^b := simple_weighted_upper (by omega)
  have ub' : 8*M≤N := by
    have h := Nat.mul_le_mul_right (p^b) (by omega : 8*(b+2)≤p)
    change 8*M≤p^(b+1)
    rw [pow_succ']
    nlinarith only [ub,h]
  have hu : 0<U := by
    dsimp only [U]
    have hN : 0<N := pow_pos hp _
    positivity
  rw [sum_range_succ _ (b+1)] at balance
  have bounds := simple_root_data (by omega : 0<q) hqr hu balance
  have gq := (Nat.le_div_iff_mul_le bounds.1).mp bounds.2.1
  let g := B*N-4*U
  change q*g≤5*U at gq
  have ge : g+4*U=B*N := Nat.sub_add_cancel (by
    have j := bounds.1
    change 0<B*N-4*U at j
    omega)
  have hg : N≤2*g := by
    dsimp only [U,B] at ge
    nlinarith only [ge,ub']
  have hu' : U≤(b+3)*N := by dsimp only [U]; nlinarith only [ub']
  have cancel : q ≤ 10*(b+3) := by
    apply Nat.le_of_mul_le_mul_right _ (pow_pos hp (b+1))
    change q*N ≤ 10*(b+3)*N
    have i := Nat.mul_le_mul_left q hg
    nlinarith only [i,gq,hu']
  omega

theorem simple_root_floor {p a q r : ℕ} (ha : 0<a) (hp : 0<p) (hq : 0<q) (hqr : q≤r)
    (balance : (∑ j ∈ range (a+1), (j+1)*p^j)*((2*q+1)*(2*r+1)) =
      ((4*a+5)*p^a)*(q*r)) : 4*a<p := by
  obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  let A := ∑ j ∈ range (b+1), (j+1)*p^j
  let N := p^(b+1)
  let U := A+(b+2)*N
  have hu : 0<U := by dsimp only [U]; have h : 0<N := pow_pos hp _; positivity
  rw [sum_range_succ _ (b+1)] at balance
  have gap := (simple_root_data hq hqr hu balance).1
  change 0<(4*(b+1)+5)*N-4*U at gap
  have ua : (b+1)*p^b ≤ A := Finset.single_le_sum
    (f:=fun j : ℕ => (j+1)*p^j) (fun _ _ => Nat.zero_le _) (by simp)
  have gm := Nat.lt_of_sub_pos gap
  dsimp only [U] at gm
  apply Nat.lt_of_mul_lt_mul_right (a:=p^b)
  have hn : N=p*p^b := pow_succ' p b
  nlinarith only [gm,ua,hn]

set_option maxRecDepth 65000 in
set_option maxHeartbeats 1000000 in
theorem small_exponent_two_simple_impossible {p a q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p<q) (hqr : q<r) (ha : 0<a) (ha' : a≤10)
    (balance : (∑ j ∈ range (a+1), (j+1)*p^j)*((2*q+1)*(2*r+1)) =
      ((4*a+5)*p^a)*(q*r)) : False := by
  let W := fun p a : ℕ => ∑ j ∈ range (a+1), (j+1)*p^j
  let U := W p a
  let B := 4*a+5
  let V := B*p^a
  let g := V-4*U
  have hu : 0<U := by
    have h := Finset.single_le_sum (f:=fun j : ℕ => (j+1)*p^j) (fun _ _ => Nat.zero_le _)
      (show 0 ∈ range (a+1) by simp)
    simp only [Nat.zero_add, pow_zero, mul_one] at h
    change 0<∑ j ∈ range (a+1), (j+1)*p^j
    omega
  have lower := simple_root_floor ha hp.pos hq.pos hqr.le balance
  have upper := simple_root_ceiling ha hpq hqr.le balance
  have data := simple_root_data hq.pos hqr.le hu balance
  change 0<g ∧ q≤5*U/g ∧ r=U*(2*q+1)/(g*q-2*U) at data
  let d := U.gcd (p-1).factorial
  have hd : d ∣ B := by
    have dU : d ∣ U := Nat.gcd_dvd_left _ _
    have dF : d ∣ (p-1).factorial := Nat.gcd_dvd_right _ _
    have cp (t : ℕ) (ht : t.Prime) (hle : p≤t) : d.Coprime t :=
      (ht.coprime_factorial_of_lt (by have := hp.two_le; omega : p-1<t)).symm.coprime_dvd_left dF
    have div : d ∣ B*(p^a*(q*r)) := by
      rw [←mul_assoc,←balance]
      exact dU.trans (dvd_mul_right _ _)
    exact (((cp p hp le_rfl).pow_right a).mul_right ((cp q hq hpq.le).mul_right
      (cp r hr (hpq.trans hqr).le))).dvd_of_dvd_mul_right div
  let cases : List (ℕ×ℕ×ℕ×ℕ) := [(5, 1, 11, 1), (11, 1, 23, 7), (17, 4, 438159, 1305), (23, 4, 1449507, 78633), (37, 4, 9577599, 1046985), (43, 9, 5133339619765363, 72938610349111), (47, 8, 218431420317317, 7291925215889), (47, 9, 11409736151344987, 245404791833499), (53, 9, 33567528520599583, 1020193181489121)]
  have scan : (List.range 121).all (fun t => (List.range 11).all (fun e =>
      let m := W t e
      let b := 4*e+5
      let k := b*t^e-4*m
      if t.Prime ∧ 0<e ∧ 4*e<t ∧ 0<k ∧ t<5*m/k ∧ Nat.gcd m (t-1).factorial ∣ b then
        cases.contains (t,e,m,k) else true)) = true := by decide +kernel
  have row := List.all_eq_true.mp (List.all_eq_true.mp scan p (List.mem_range.mpr (by omega)))
    a (List.mem_range.mpr (by omega))
  change (if p.Prime ∧ 0<a ∧ 4*a<p ∧ 0<g ∧ p<5*U/g ∧ d ∣ B then cases.contains (p,a,U,g) else true)=true at row
  rw [if_pos ⟨hp,ha,lower,data.1,hpq.trans_le data.2.1,hd⟩] at row
  have mem := List.contains_iff_mem.mp row
  have scan' : cases.all (fun z =>
      let u := z.2.2.1
      let k := z.2.2.2
      (List.range (5*u/k+1)).all (fun s =>
        let t := u*(2*s+1)/(k*s-2*u)
        decide (¬(z.1<s ∧ k*s*t=u*(2*s+2*t+1) ∧ s<t ∧ s.Prime ∧ t.Prime)))) = true := by decide +kernel
  have row' := List.all_eq_true.mp scan' _ mem
  have stop := List.all_eq_true.mp row' q (List.mem_range.mpr (Nat.lt_succ_of_le data.2.1))
  have bad := of_decide_eq_true stop
  change ¬(p<q ∧ g*q*(U*(2*q+1)/(g*q-2*U))=U*(2*q+2*(U*(2*q+1)/(g*q-2*U))+1) ∧
    q<U*(2*q+1)/(g*q-2*U) ∧ q.Prime ∧ (U*(2*q+1)/(g*q-2*U)).Prime) at bad
  rw [←data.2.2] at bad
  apply bad ⟨hpq,?_,hqr,hq,hr⟩
  have ge : g+4*U=V := Nat.sub_add_cancel (by have := data.1; dsimp only [g] at this; omega)
  have j := congrArg (fun i => i*(q*r)) ge
  change U*((2*q+1)*(2*r+1))=V*(q*r) at balance
  nlinarith only [j,balance]

end Div245

/- Bounding the two simple factors after a large repeated prime power. -/

namespace Div245
open Finset

theorem two_simple_affine_bounds {N U d H B q r : ℕ} (hn : 8≤N)
    (hd : d*U=H*N+1) (hq : 0<q) (hqr : q≤r)
    (balance : U*((2*q+1)*(2*r+1))=(B*N)*(q*r)) :
    q ≤ 10*(H+1) ∧ (4*(2*q+1)≤N → r ≤ 2*(H+1)*(2*q+1)) ∧
      N ∣ (2*q+1)*(2*r+1) := by
  let s := 2*q+1
  let t := 2*r+1
  let g := B*N-4*U
  have npos : 0<N := by omega
  have rpos : 0<r := by omega
  have qrpos := Nat.mul_pos hq rpos
  have blo : 4*U ≤ B*N := by
    apply Nat.le_of_mul_le_mul_right _ qrpos
    have i : 4*(q*r)≤(2*q+1)*(2*r+1) := by nlinarith only [Nat.zero_le q,Nat.zero_le r]
    have j := Nat.mul_le_mul_left U i
    nlinarith only [balance,j]
  have ge : g+4*U=B*N := Nat.sub_add_cancel blo
  have gc : (g*q)*r=U*(2*q+2*r+1) := by
    have j := congrArg (fun v => v*(q*r)) ge
    nlinarith only [balance,j]
  obtain ⟨k,hk⟩ := affine_gap_multiple npos hd blo
  have gsize : N≤2*(d*g) := affine_gap_lower hk (by decide) (by omega)
  have gq : g*q≤5*U := by
    apply Nat.le_of_mul_le_mul_right _ rpos
    have j := Nat.mul_le_mul_left U (by omega : 2*q+2*r+1≤5*r)
    nlinarith only [gc,j]
  have ub : d*U≤(H+1)*N := by nlinarith only [hd,hn]
  have qb : q ≤ 10*(H+1) := by
    apply Nat.le_of_mul_le_mul_right _ npos
    have i := Nat.mul_le_mul_right q gsize
    have j := Nat.mul_le_mul_left (2*d) gq
    nlinarith only [i,j,ub]
  refine ⟨qb,?_,?_⟩
  · intro hn'
    let h := (B*q)*N-(2*s)*U
    have low : (2*s)*U≤(B*q)*N := by
      apply Nat.le_of_mul_le_mul_right _ rpos
      dsimp only [s]
      nlinarith only [balance, Nat.zero_le (U*(2*q+1))]
    have he : h+(2*s)*U=(B*q)*N := Nat.sub_add_cancel low
    have hc : h*r=U*s := by
      have j := congrArg (·*r) he
      dsimp only [s] at j ⊢
      nlinarith only [balance,j]
    obtain ⟨l,hl⟩ := affine_gap_multiple npos hd low
    have hs : 0<2*s := by dsimp [s]; omega
    have hsize : N≤2*(d*h) := affine_gap_lower hl hs (by dsimp only [s]; omega)
    apply Nat.le_of_mul_le_mul_right _ npos
    have i := Nat.mul_le_mul_right r hsize
    have j := congrArg (d*·) hc
    have m := Nat.mul_le_mul_right s ub
    change r*N≤2*(H+1)*s*N
    nlinarith only [i,j,m]
  · change N ∣ s*t
    have b : U*(s*t)=(B*N)*(q*r) := balance
    have k := congrArg (d*·) b
    have k' := congrArg (·*(s*t)) hd
    have eq : (H*N)*(s*t)+(s*t)=N*(d*B*(q*r)) := by nlinarith only [k,k']
    have dvd : N ∣ (H*N)*(s*t)+(s*t) := ⟨_,eq⟩
    exact (Nat.dvd_add_right (dvd_mul_of_dvd_left (dvd_mul_left N H) _)).mp dvd

theorem large_exponent_two_simple_impossible {p a q r : ℕ} (ha : 11≤a) (hap : 4*a<p)
    (hq : 0<q) (hqr : q≤r)
    (balance : (∑ j ∈ range (a+1), (j+1)*p^j)*((2*q+1)*(2*r+1)) =
      ((4*a+5)*p^a)*(q*r)) : False := by
  have hp : 45≤p := by omega
  have ppos : 0<p := by omega
  let N := p^a
  let U := ∑ j ∈ range (a+1), (j+1)*p^j
  obtain ⟨H,hd,hub⟩ := weighted_closed_affine p a (by omega) (by omega)
  have nlow (e : ℕ) (he : e≤a) : p^e≤N := Nat.pow_le_pow_right ppos he
  have hn : 8≤N := by have h := nlow 1 (by omega); simp only [pow_one] at h; omega
  obtain ⟨qb,rb,dvd⟩ := two_simple_affine_bounds hn hd hq hqr balance
  have u3 : 0 < p^3 := pow_pos ppos _
  have u6 : 0 < p^6 := pow_pos ppos _
  have s3 : 2*q+1 ≤ 21*p^3 := by omega
  have pp : 1785 < p^2 := by
    have h := Nat.pow_le_pow_left hp 2
    norm_num at h
    omega
  have cut : 4*(2*q+1)≤N := by
    calc
      _ ≤ 84*p^3 := by omega
      _ ≤ p^2*p^3 := Nat.mul_le_mul_right _ (by omega)
      _ = p^5 := by ring
      _ ≤ N := nlow 5 (by omega)
  have rb' := rb cut
  have r6 : r≤42*p^6 := calc
    r ≤ 2*(H+1)*(2*q+1) := rb'
    _ ≤ 2*p^3*(21*p^3) := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hub) s3
    _ = 42*p^6 := by ring
  have t6 : 2*r+1≤85*p^6 := by omega
  have hi : (2*q+1)*(2*r+1)<N := calc
    _ ≤ (21*p^3)*(85*p^6) := Nat.mul_le_mul s3 t6
    _ = 1785*p^9 := by ring
    _ < p^2*p^9 := Nat.mul_lt_mul_of_pos_right pp (pow_pos ppos _)
    _ = p^11 := by ring
    _ ≤ N := nlow 11 ha
  exact (Nat.not_dvd_of_pos_of_lt (Nat.mul_pos (by omega) (by omega)) hi) dvd

/-- Three ordered primes with only the first exponent possibly repeated never
satisfy the divisor moment identity. There is no bound on the primes or the exponent. -/
theorem two_simple_impossible {p a q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p<q) (hqr : q<r) (ha : 0<a)
    (balance : (∑ j ∈ range (a+1), (j+1)*p^j)*((2*q+1)*(2*r+1)) =
      ((4*a+5)*p^a)*(q*r)) : False := by
  by_cases sm : a≤10
  · exact small_exponent_two_simple_impossible hp hq hr hpq hqr ha sm balance
  · exact large_exponent_two_simple_impossible (by omega)
      (simple_root_floor ha hp.pos hq.pos hqr.le balance) hq.pos hqr.le balance

end Div245

/- Exhaustion of the three repeated exponents 4, 4, 13 for least prime at most 433. -/
namespace Div245
open Finset

theorem weighted_tail_local (t e : ℕ) (ht : 1 < t) (he : 0 < e) :
    let A := ∑ j ∈ range e, (j+1)*t^j
    (t-1)*A < e*t^e ∧ e*t^e ≤ t*A := by
  let A (e : ℕ) := ∑ j ∈ range e, (j+1)*t^j
  have hrec (k : ℕ) : A (k+1)=A k+(k+1)*t^k := Finset.sum_range_succ (fun j => (j+1)*t^j) k
  have hi (k : ℕ) (hk : 0 < k) : (t-1)*A k < k*t^k := by
    induction k with
    | zero => omega
    | succ k ih =>
      rw [hrec, pow_succ t k]
      have t1 : t-1+1=t := by omega
      have hpos := pow_pos (by omega : 0<t) k
      by_cases hk' : 0<k
      · have prev := ih hk'
        nlinarith only [prev,hpos,congrArg (fun i => i*((k+1)*t^k)) t1]
      · have z : k=0 := by omega
        subst k
        simp [A]
        omega
  refine ⟨hi e he,?_⟩
  change e*t^e ≤ t*A e
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
  rw [hrec, pow_succ t k]
  nlinarith only [Nat.zero_le (t*A k)]

/-- With two remaining prime slots the sorted second prime q is bounded above.
Here u/v is the full fixed-point target divided by the accumulated prefix. -/
theorem two_slot_cap {q r b c u v : ℕ} (hq : 1<q) (hr : q≤r) (hb : 0<b) (hc : 0<c)
    (hu : 0<u)
    (hf : u*((∑ j ∈ range (b+1), (j+1)*q^j)*(∑ j ∈ range (c+1), (j+1)*r^j)) =
           v*(q^b*r^c)) :
    0 < v-(b+1)*(c+1)*u ∧ q ≤ 2*v/(v-(b+1)*(c+1)*u) := by
  let A := ∑ j ∈ range b, (j+1)*q^j
  let B := ∑ j ∈ range c, (j+1)*r^j
  let P := (b+1)*q^b
  let Q := (c+1)*r^c
  rw [sum_range_succ _ b,sum_range_succ _ c] at hf
  change u*((A+P)*(B+Q))=v*(q^b*r^c) at hf
  have hq' := weighted_tail_local q b hq hb
  have hr' := weighted_tail_local r c (by omega) hc
  change (q-1)*A<b*q^b ∧ b*q^b≤q*A at hq'
  change (r-1)*B<c*r^c ∧ c*r^c≤r*B at hr'
  have ha : 0<A := by
    have h := Nat.mul_pos hb (pow_pos (by omega : 0<q) b)
    have hh := hq'.2
    by_contra! hz; rw [show A=0 by omega, Nat.mul_zero] at hh; omega
  have hP : 0<P := Nat.mul_pos (by omega) (pow_pos (by omega : 0<q) b)
  have hQ : 0<Q := Nat.mul_pos (by omega) (pow_pos (by omega : 0<r) c)
  have htop : P*Q < (A+P)*(B+Q) := by
    have h := Nat.mul_lt_mul_of_pos_right (by omega : P<A+P) hQ
    exact h.trans_le (Nat.mul_le_mul_left _ (by omega))
  have pq : 0<q^b*r^c := Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _)
  have prod : (b+1)*(c+1)*u < v := by
    apply Nat.lt_of_mul_lt_mul_right (a:=q^b*r^c)
    calc
      ((b+1)*(c+1)*u)*(q^b*r^c)=u*(P*Q) := by dsimp [P,Q]; ring
      _ < u*((A+P)*(B+Q)) := (Nat.mul_lt_mul_left hu).mpr htop
      _ = v*(q^b*r^c) := hf
  have lA : q*A ≤ A+P := by
    have e := congrArg (fun i => i*A) (show q-1+1=q by omega)
    dsimp [P]
    nlinarith only [hq'.1,e,Nat.zero_le (q^b)]
  have lB : q*B ≤ B+Q := by
    have e := congrArg (fun i => i*B) (show r-1+1=r by omega)
    have qe := Nat.mul_le_mul_right B hr
    dsimp [Q]
    nlinarith only [hr'.1,e,qe,Nat.zero_le (r^c)]
  have tailub : q*(A+P)*(B+Q) ≤ 2*((A+P)*(B+Q))+q*(P*Q) := by
    have a := Nat.mul_le_mul_right (B+Q) lA
    have b := Nat.mul_le_mul_left P lB
    have c := Nat.mul_le_mul_right (B+Q) (show P ≤ A+P by omega)
    nlinarith only [a,b,c]
  let g := v-(b+1)*(c+1)*u
  have vg : g+(b+1)*(c+1)*u=v := Nat.sub_add_cancel prod.le
  refine ⟨by omega, (Nat.le_div_iff_mul_le (by omega)).mpr ?_⟩
  change q*g ≤ 2*v
  apply Nat.le_of_mul_le_mul_right ?_ pq
  have z := Nat.mul_le_mul_left u tailub
  have ze := congrArg (fun i => q*i*(q^b*r^c)) vg
  have hfe := congrArg (fun i => q*i) hf
  dsimp [P,Q] at z hf hfe
  nlinarith only [z,ze,hfe,hf]


end Div245

/- Two residual mixed tails with exponents one and four. -/

namespace Div245
open Finset

theorem affine_mixed_gate {N U d H B b c q r Q S R K : ℕ}
    (n : 0<N) (u : 0<U) (bpos : 0<b) (cpos : 0<c) (Bpos : 0<B)
    (qr : q≤r) (q1 : 1<q) (pr : r.Prime)
    (aff : d*U=H*N+1) (kpos : 0<K) (kb : K∣d*B) (kc : K∣c+1)
    (qtest : 2*(B*N)/(B*N-(b+1)*(c+1)*U)≤Q)
    (sbound : (∑ j ∈ range (b+1),(j+1)*Q^j)≤S) (ntest : 2*((c+1)*S)≤N)
    (rtest : 2*c*(H+1)*S<(2*K-1)*R)
    (small : S*(∑ j ∈ range (c+1),(j+1)*R^j)<N)
    (balance : U*((∑ j ∈ range (b+1),(j+1)*q^j)*(∑ j ∈ range (c+1),(j+1)*r^j))
      = (B*N)*(q^b*r^c)) : False := by
  let W := fun t e : ℕ => ∑ j ∈ range (e+1),(j+1)*t^j
  let s := W q b
  let t := W r c
  have positive (z e : ℕ) : 0<W z e := by
    have i := single_le_sum (f:=fun j : ℕ => (j+1)*z^j) (fun _ _ => Nat.zero_le _)
      (show 0∈range (e+1) by simp)
    simp only [Nat.zero_add,pow_zero,mul_one] at i
    change 0<∑ j ∈ range (e+1),(j+1)*z^j
    omega
  have mono (x y e : ℕ) (h : x≤y) : W x e≤W y e :=
    sum_le_sum (fun j _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h j))
  have qc := (two_slot_cap q1 qr bpos cpos u balance).2.trans qtest
  have sb : s≤S := (mono q Q b qc).trans sbound
  have sp : 0<s := positive _ _
  have tp : 0<t := positive _ _
  change U*(s*t)=(B*N)*(q^b*r^c) at balance
  let V := (B*q^b)*N
  let g := V-(U*s)*(c+1)
  have last : (U*s)*(∑ j ∈ range (c+1),(j+1)*r^j)=V*r^c := by
    change (U*s)*t= (B*q^b)*N*r^c
    nlinarith only [balance]
  have leaf := raw_leaf pr cpos (Nat.mul_pos u sp)
    (show 0<V by dsimp [V]; positivity) last
  change 0<g ∧ r = (c*(U*s)-1)/g+1 at leaf
  have lo : (U*s)*(c+1)≤V := by have h := leaf.1; dsimp only [g] at h; omega
  have ge : g+(U*s)*(c+1)=V := Nat.sub_add_cancel lo
  let h := (c+1)*s
  have hlo : h*U≤(B*q^b)*N := by dsimp only [h]; change _≤V; rwa [show (c+1)*s*U=U*s*(c+1) by ring]
  obtain ⟨k,hk₀⟩ := affine_gap_multiple n aff hlo
  have hk : d*g+h=N*k := by
    convert hk₀ using 1
    dsimp only [g,h,V]
    ring_nf
  have ck : k+h*H=d*(B*q^b) := by
    apply Nat.eq_of_mul_eq_mul_left n
    have j := congrArg (d*·) ge
    have i := congrArg (h*·) aff
    dsimp only [V] at j
    dsimp only [h] at i hk ⊢
    nlinarith only [j,i,hk]
  have dv1 : K∣d*(B*q^b) := by rw [←mul_assoc]; exact dvd_mul_of_dvd_left kb _
  have dv2 : K∣h*H := dvd_mul_of_dvd_left (dvd_mul_of_dvd_left kc _) _
  have dvk : K∣k := (Nat.dvd_add_left dv2).mp (ck ▸ dv1)
  have ph : 0<h := Nat.mul_pos (by omega) sp
  have pk : 0<k := by by_contra! z; rw [show k=0 by omega,mul_zero] at hk; omega
  have kk : K≤k := Nat.le_of_dvd pk dvk
  have nn : 2*h≤N := (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (c+1) sb)).trans ntest
  have db : (2*K-1)*N≤2*(d*g) := by
    have y := Nat.mul_le_mul_left N kk
    have z := congrArg (·*N) (show 2*K-1+1=2*K by omega)
    nlinarith only [hk,y,z,nn]
  have remain : (r-1)*g ≤ c*(U*s) := by
    have le := Nat.div_mul_le_self (c*(U*s)-1) g
    have substR : r-1=(c*(U*s)-1)/g := by omega
    rw [substR]
    omega
  have mU : d*U≤(H+1)*N := by nlinarith only [aff,n]
  have pre : (r-1)*(2*K-1)≤2*c*(H+1)*S := by
    apply Nat.le_of_mul_le_mul_right _ n
    have i := Nat.mul_le_mul_left (r-1) db
    have j := Nat.mul_le_mul_left (2*d) remain
    have m := Nat.mul_le_mul_left (2*c*s) mU
    have v := Nat.mul_le_mul_left (2*c*(H+1)*N) sb
    nlinarith only [i,j,m,v]
  have rR : r≤R := by
    have z := pre.trans_lt rtest
    rw [Nat.mul_comm (r-1)] at z
    have := Nat.lt_of_mul_lt_mul_left z
    omega
  have st := (Nat.mul_le_mul sb (mono r R c rR)).trans_lt small
  have j := congrArg (d*·) balance
  have i := congrArg (·*(s*t)) aff
  have eq : (H*N)*(s*t)+(s*t)=N*(d*B*(q^b*r^c)) := by nlinarith only [j,i]
  have div : N∣(H*N)*(s*t)+(s*t) := ⟨_,eq⟩
  exact (Nat.not_dvd_of_pos_of_lt (Nat.mul_pos sp tp) st)
    ((Nat.dvd_add_right (dvd_mul_of_dvd_left (dvd_mul_left N H) _)).mp div)

theorem two_mixed_roots_impossible {p a b c q r : ℕ}
    (pa : (p=251 ∧ a=25) ∨ (p=389 ∧ a=37))
    (bc : (b=1 ∧ c=4) ∨ (b=4 ∧ c=1)) (qr : q≤r) (q1 : 1<q) (hr : r.Prime)
    (balance : (∑ j ∈ range (a+1),(j+1)*p^j)*
      ((∑ j ∈ range (b+1),(j+1)*q^j)*(∑ j ∈ range (c+1),(j+1)*r^j))
      = ((10*(a+1)+1)*p^a)*(q^b*r^c)) : False := by
  rcases pa with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> rcases bc with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · apply affine_mixed_gate (d:=62500) (H:=1631249) (Q:=3262500) (K:=5)
        (S:=6525001) (R:=9461251450001) (qr:=qr) (q1:=q1) (pr:=hr) (balance:=balance) <;> decide +kernel
  · apply affine_mixed_gate (d:=62500) (H:=1631249) (Q:=3262500) (K:=2)
        (S:=566463840196953806725275001) (R:=616029426214187264813736563587501) (qr:=qr) (q1:=q1) (pr:=hr) (balance:=balance) <;> decide +kernel
  · apply affine_mixed_gate (d:=150544) (H:=5735027) (Q:=16401) (K:=1)
        (S:=32803) (R:=1505008987873) (qr:=qr) (q1:=q1) (pr:=hr) (balance:=balance) <;> decide +kernel
  · apply affine_mixed_gate (d:=150544) (H:=5735027) (Q:=16401) (K:=2)
        (S:=361803282759856015) (R:=1383301304746461014662281) (qr:=qr) (q1:=q1) (pr:=hr) (balance:=balance) <;> decide +kernel

end Div245

/- Upper bounds for three unknown simple prime factors of a fixed point. -/
namespace Div245
open Finset

theorem many_sizes (R : List ℕ) (q : ℕ) (hq : 0 < q) (hr : ∀ r ∈ R, q ≤ r) :
    let F := (R.map (fun r => 2*r+1)).prod
    let Q := R.prod
    0 < Q ∧ 2^R.length*Q ≤ F ∧ F ≤ 3^R.length*Q ∧
      q*F ≤ (q*2^R.length+3^R.length)*Q := by
  induction R with
  | nil => simp
  | cons r R ih =>
    let F := (R.map (fun x => 2*x+1)).prod
    let Q := R.prod
    obtain ⟨pos,low,hi,corr⟩ := ih (fun t ht => hr t (List.mem_cons_of_mem _ ht))
    have qr := hr r (List.mem_cons_self ..)
    have rpos := hq.trans_le qr
    change 0 < r*Q ∧ 2^(R.length+1)*(r*Q) ≤ (2*r+1)*F ∧
      (2*r+1)*F ≤ 3^(R.length+1)*(r*Q) ∧
      q*((2*r+1)*F) ≤ (q*2^(R.length+1)+3^(R.length+1))*(r*Q)
    rw [pow_succ', pow_succ']
    refine ⟨Nat.mul_pos rpos pos, ?_, ?_, ?_⟩
    · calc _ = (2*r)*(2^R.length*Q) := by ring
           _ ≤ _ := Nat.mul_le_mul (by omega) low
    · calc _ ≤ (3*r)*(3^R.length*Q) := Nat.mul_le_mul (by omega) hi
           _ = _ := by ring
    · calc _ = 2*r*(q*F)+q*F := by ring
           _ ≤ 2*r*((q*2^R.length+3^R.length)*Q)+r*(3^R.length*Q) :=
             Nat.add_le_add (Nat.mul_le_mul_left _ corr) (Nat.mul_le_mul qr hi)
           _ = _ := by ring

theorem many_cut {P A f B : ℕ} (R : List ℕ) (q : ℕ) (hq : 0 < q)
    (hr : ∀ r ∈ R, q ≤ r) (hf : 0 < f) (small : 2*2^R.length*f ≤ P)
    (bal : (P*A+f)*(R.map (fun r => 2*r+1)).prod = P*B*R.prod) :
    2^R.length*A < B ∧
    ∀ g, 0<g → 2^R.length*A+g ≤ B → q*g ≤ 2*(A+f)*3^R.length := by
  let d := 2^R.length
  let c := 3^R.length
  let F := (R.map (fun r => 2*r+1)).prod
  let Q := R.prod
  obtain ⟨hQ,lower,_,upper⟩ := many_sizes R q hq hr
  have hd : 0 < d := pow_pos (by decide) _
  have hP : 0 < P := lt_of_lt_of_le (Nat.mul_pos (Nat.mul_pos (by decide) hd) hf) small
  have hl : (P*A+f)*d ≤ P*B := by
    apply Nat.le_of_mul_le_mul_right (c:=Q) _ hQ
    rw [mul_assoc, ←bal]
    exact Nat.mul_le_mul_left _ lower
  have pos : d*A < B := by
    by_contra! h
    have hle := Nat.mul_le_mul_left P h
    have := Nat.mul_pos hf hd
    nlinarith only [hl, hle, this]
  refine ⟨pos,?_⟩
  intro g hg hgb
  change d*A+g ≤ B at hgb
  have hu : q*P*B ≤ (P*A+f)*(q*d+c) := by
    apply Nat.le_of_mul_le_mul_right (c:=Q) _ hQ
    calc _ = q*(P*B*Q) := by ring
         _ = q*((P*A+f)*F) := by rw [bal]
         _ = (P*A+f)*(q*F) := by ring
         _ ≤ (P*A+f)*((q*d+c)*Q) := Nat.mul_le_mul_left _ upper
         _ = _ := by ring
  have hei := (Nat.mul_le_mul_left (q*P) hgb).trans hu
  have hf2 : 2*d*f ≤ P*g := small.trans (Nat.le_mul_of_pos_right P hg)
  have hf3 := Nat.mul_le_mul_right q hf2
  have hfc := Nat.mul_le_mul_right c (Nat.le_mul_of_pos_left f hP)
  apply Nat.le_of_mul_le_mul_left (c:=P) _ hP
  change P*(q*g) ≤ P*(2*(A+f)*c)
  nlinarith only [hei, hf3,hfc]

theorem many_three {P H B q r s : ℕ} (hq : 0 < q) (hqr : q ≤ r) (hrs : r ≤ s)
    (hbal : (P*H+1)*((2*q+1)*(2*r+1)*(2*s+1))=P*B*(q*r*s))
    (cert : let g := B-8*H
            let t := 54*(H+1)/g
            let J := 2*t+1
            let u := 18*(H+1)*J
            let K := J*(2*u+1)
            let v := 6*(H+1)*K
            0<g ∧ 16≤P ∧ 8*J≤P ∧ 4*K≤P ∧ K*(2*v+1)<P) : False := by
  let g := B-8*H
  let t := 54*(H+1)/g
  let J := 2*t+1
  let u := 18*(H+1)*J
  let K := J*(2*u+1)
  let v := 6*(H+1)*K
  obtain ⟨hg,h16,h8,h4,final⟩ := cert
  have hr := hq.trans_le hqr
  have hs := hr.trans_le hrs
  have hqs := hqr.trans hrs
  have hstart : (P*H+1)*([q,r,s].map (fun r => 2*r+1)).prod = P*B*[q,r,s].prod := by
    simpa [mul_assoc] using hbal
  have c1 := many_cut [q,r,s] q hq (by simpa using And.intro hqr hqs)
    (by decide : 0<1) (by exact h16) hstart
  have hqt : q≤t := by
    apply (Nat.le_div_iff_mul_le hg).mpr
    have hg' : 8*H+g ≤ B := by dsimp [g]; have := c1.1; change 8*H<B at this; omega
    have h := c1.2 g hg hg'
    change q*g ≤ 2*(H+1)*27 at h
    change q*g ≤ 54*(H+1)
    omega
  let j := 2*q+1
  have hj : j ≤ J := by dsimp [j,J]; omega
  have start2 : (P*(H*j)+j)*([r,s].map (fun r => 2*r+1)).prod = P*(B*q)*[r,s].prod := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,mul_one]
    dsimp [j]
    linear_combination hbal
  have c2 := many_cut [r,s] r hr (by simpa) (by dsimp [j]; omega)
    ((Nat.mul_le_mul_left 8 hj).trans h8) start2
  have hru : r ≤ u := by
    have h := c2.2 1 (by decide) c2.1
    change r*1 ≤ 2*(H*j+j)*9 at h
    calc r ≤ 18*(H+1)*j := by nlinarith only [h]
         _ ≤ u := Nat.mul_le_mul_left _ hj
  let k := j*(2*r+1)
  have hk : k ≤ K := Nat.mul_le_mul hj (by omega)
  have start3 : (P*(H*k)+k)*([s].map (fun r => 2*r+1)).prod = P*(B*(q*r))*[s].prod := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,mul_one]
    dsimp [k,j]
    linear_combination hbal
  have c3 := many_cut [s] s hs (by simp) (by dsimp [k,j]; positivity)
    ((Nat.mul_le_mul_left 4 hk).trans h4) start3
  have hsv : s ≤ v := by
    have h := c3.2 1 (by decide) c3.1
    change s*1 ≤ 2*(H*k+k)*3 at h
    calc s ≤ 6*(H+1)*k := by nlinarith only [h]
         _ ≤ v := Nat.mul_le_mul_left _ hk
  let F := k*(2*s+1)
  have hF : F<P := (Nat.mul_le_mul hk (by omega : 2*s+1≤2*v+1)).trans_lt final
  have posF : 0<F := by dsimp [F,k,j]; positivity
  have hsum : P*(H*F)+F = P*(B*(q*r*s)) := by dsimp [F,k,j]; linear_combination hbal
  have hd : P ∣ F := (Nat.dvd_add_iff_right (dvd_mul_right P (H*F))).mpr
    (hsum ▸ dvd_mul_right P _)
  exact (not_le_of_gt hF) (Nat.le_of_dvd posF hd)


theorem many_simple_cutoff {p a H : ℕ} {L : List (ℕ×ℕ)}
    (aff : (p-1)^2*(∑ j ∈ range (a+1), (j+1)*p^j)=H*p^a+1)
    (pos : ∀ z ∈ L, 0 < z.1) (ord : L.Pairwise (fun z w => z.1 < w.1))
    (simple : L.map Prod.snd = [1,1,1])
    (balance : (∑ j ∈ range (a+1), (j+1)*p^j)*
      (L.map (fun z => ∑ j ∈ range (z.2+1), (j+1)*z.1^j)).prod =
      (p^a*((a+1)*(L.map (fun z => z.2+1)).prod+1))*(L.map (fun z => z.1^z.2)).prod)
    (cert : let P := p^a
            let B := (p-1)^2*(8*(a+1)+1)
            let g := B-8*H
            let t := 54*(H+1)/g
            let J := 2*t+1
            let u := 18*(H+1)*J
            let K := J*(2*u+1)
            let v := 6*(H+1)*K
            0<g ∧ 16≤P ∧ 8*J≤P ∧ 4*K≤P ∧ K*(2*v+1)<P) : False := by
  have repr : ∃ q r s, L=[(q,1),(r,1),(s,1)] := by
    match L with
    | [(q,e),(r,b),(s,c)] =>
      simp at simple
      obtain ⟨rfl,rfl,rfl⟩ := simple
      exact ⟨q,r,s,rfl⟩
    | [] | [_] | [_,_] | _::_::_::_::_ => simp at simple
  obtain ⟨q,r,s,rfl⟩ := repr
  simp [List.pairwise_cons] at ord
  have qpos := pos (q,1) (by simp)
  let U := ∑ j ∈ range (a+1), (j+1)*p^j
  change (p-1)^2*U=H*p^a+1 at aff
  have h : U*((2*q+1)*(2*r+1)*(2*s+1)) =
      (p^a*(8*(a+1)+1))*(q*r*s) := by
    simpa [U,Finset.sum_range_succ, Nat.mul_comm, Nat.add_comm, Nat.mul_left_comm,Nat.mul_assoc]
      using balance
  apply many_three qpos ord.1.1.le ord.2.le _ cert
  have mult := congrArg ((p-1)^2*·) h
  rw [show p^a*H=H*p^a by ac_rfl, ← aff]
  linear_combination mult

theorem many_certificate {p a : ℕ} (hp : 197≤p) (ha : 21≤a) (hmax : a≤45)
    (hsep : 8*a+3 ≤ p) :
    let H := (a+1)*p^2-(a+2)*p
    let B := (p-1)^2*(8*(a+1)+1)
    let g := B-8*H
    let t := 54*(H+1)/g
    let J := 2*t+1
    let u := 18*(H+1)*J
    let K := J*(2*u+1)
    let v := 6*(H+1)*K
    0<g ∧ 16≤p^a ∧ 8*J≤p^a ∧ 4*K≤p^a ∧ K*(2*v+1)<p^a := by
  intro H B g t J u K v
  have ppos : 0<p := by omega
  have pl : 1≤p := by omega
  have hbase : (a+2)*p ≤ (a+1)*p^2 := by
    have hlow := Nat.mul_le_mul_left (a+1) (by omega : 2≤p)
    have := Nat.mul_le_mul_right p (by omega : a+2≤(a+1)*p)
    nlinarith only [this]
  have hind : H+(a+2)*p = (a+1)*p^2 := Nat.sub_add_cancel hbase
  have hlim : H+1 ≤ 46*p^2 := by
    have lo := Nat.mul_le_mul_right (p^2) (by omega : a+1≤46)
    have pos := Nat.mul_pos (by omega : 0<a+2) ppos
    omega
  have gap : p ≤ g := by
    have hh : (p-1)^2+2*p=p^2+1 := by
      have h := Nat.sub_add_cancel pl
      nlinarith only [congrArg (fun v : ℕ => v^2) h,h]
    have he := congrArg (·*(8*(a+1)+1)) hh
    have hl := Nat.mul_le_mul_right p hsep
    have hb : p+8*H ≤ B := by dsimp [B]; nlinarith only [he,hl,hind]
    dsimp [g]
    omega
  have htg : t*g≤54*(H+1) := Nat.div_mul_le_self _ _
  have ht : t ≤ 2500*p := by
    apply Nat.le_of_mul_le_mul_right (c:=p) _ ppos
    calc t*p ≤ t*g := Nat.mul_le_mul_left _ gap
         _ ≤ 54*(H+1) := htg
         _ ≤ 54*(46*p^2) := Nat.mul_le_mul_left _ hlim
         _ ≤ 2500*p*p := by nlinarith only [Nat.zero_le (p*p)]
  have hj : J ≤ 5001*p := by dsimp [J]; omega
  have hu : u ≤ 4140828*p^3 := by
    calc u ≤ 18*(46*p^2)*(5001*p) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hlim) hj
         _ = _ := by ring
  have hratio {w b m : ℕ} (hm : 0 < m) (hw : w≤b*m) : 2*w+1 ≤ (2*b+1)*m := by
    nlinarith only [hw,hm]
  have hk : K ≤ 41416566657*p^4 := by
    calc K ≤ (5001*p)*((2*4140828+1)*p^3) := Nat.mul_le_mul hj (hratio (pow_pos ppos _) hu)
         _ = _ := by ring
  have hv : v ≤ 11430972397332*p^6 := by
    calc v ≤ 6*(46*p^2)*(41416566657*p^4) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hlim) hk
         _ = _ := by ring
  have hF : K*(2*v+1)<p^a := by
    calc K*(2*v+1) ≤ (41416566657*p^4)*((2*11430972397332+1)*p^6) :=
           Nat.mul_le_mul hk (hratio (pow_pos ppos _) hv)
         _ = 946863260496897150484905*p^10 := by ring
         _ < (197^11)*p^10 := Nat.mul_lt_mul_of_pos_right (by decide) (pow_pos ppos _)
         _ ≤ (p^11)*p^10 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hp _)
         _ = p^21 := by ring
         _ ≤ p^a := Nat.pow_le_pow_right ppos ha
  have hjp : 0<J := by dsimp [J]; omega
  have hup : 0<u := Nat.mul_pos (Nat.mul_pos (by decide) (Nat.succ_pos _)) hjp
  have hkp : 0<K := Nat.mul_pos hjp (Nat.succ_pos _)
  have hvp : 2 ≤ v := by
    have hv6 : 6 ≤ v :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 6 (Nat.succ_le_succ (Nat.zero_le H))) hkp
    exact (by decide : 2 ≤ 6).trans hv6
  have kl := Nat.mul_le_mul_left J (by omega : 2≤2*u+1)
  have fl := Nat.mul_le_mul_left K (by omega : 4≤2*v+1)
  change J*2 ≤ K at kl
  have ps : 197 ≤ p^a := hp.trans (by simpa using (Nat.pow_le_pow_right ppos (by omega : 1≤a)))
  exact ⟨ppos.trans_le gap,by omega,by omega,by omega,hF⟩

theorem many_simple_rows {p a : ℕ} (row : (p,a) ∈ [(197,24),(223,21),(223,24),(239,21),(257,24),(283,33),(293,24),(347,33),(349,24),(349,36),(359,33),(367,33),(379,33),(419,33),(419,45),(431,45),(433,24)])
    {L : List (ℕ×ℕ)} (pos : ∀ z ∈ L, 0 < z.1)
    (ord : L.Pairwise (fun z w => z.1 < w.1)) (simple : L.map Prod.snd = [1,1,1])
    (balance : (∑ j ∈ range (a+1), (j+1)*p^j)*
      (L.map (fun z => ∑ j ∈ range (z.2+1), (j+1)*z.1^j)).prod =
      (p^a*((a+1)*(L.map (fun z => z.2+1)).prod+1))*(L.map (fun z => z.1^z.2)).prod) : False := by

  apply many_simple_cutoff (weighted_closed_exact p a (by
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row
    omega)) pos ord simple balance
  apply many_certificate <;> simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at row <;> omega

theorem many_one_heavy (S : List (ℕ×ℕ)) (e : ℕ) (elo : 21≤e) (ehi : e≤45)
    (base : ∀ z ∈ S, z.2=e → 197≤z.1 ∧ 8*e+3 ≤ z.1)
    (pos : ∀ z ∈ S, 0<z.1) (ord : S.Pairwise (fun z w => z.1<w.1))
    (exps : (S.map Prod.snd).Perm [e,1,1,1])
    (balance : (S.map (fun z => ∑ j ∈ range (z.2+1), (j+1)*z.1^j)).prod =
      (S.map (fun z => z.1^z.2)).prod*((S.map (fun z => z.2+1)).prod+1)) : False := by
  have em : e ∈ S.map Prod.snd := exps.mem_iff.mpr (by simp)
  obtain ⟨⟨q,b⟩,hq,hb⟩ := List.mem_map.mp em
  change b=e at hb
  subst b
  let L := S.erase (q,e)
  have pm : S.Perm ((q,e)::L) := List.perm_cons_erase hq
  have ed : (L.map Prod.snd).Perm [1,1,1] := ((pm.map Prod.snd).symm.trans exps).cons_inv
  have ls : L.map Prod.snd = [1,1,1] := (List.perm_replicate (n:=3) (a:=1)).mp ed
  have hh := base _ hq rfl
  apply many_simple_cutoff (weighted_closed_exact q e (by have := hh.1; change 197≤q at this; omega))
    (fun z hz => pos z (List.mem_of_mem_erase hz)) (ord.sublist List.erase_sublist) ls _
    (many_certificate hh.1 elo ehi hh.2)
  rw [(pm.map (fun z => ∑ j ∈ range (z.2+1), (j+1)*z.1^j)).prod_eq,
      (pm.map (fun z => z.1^z.2)).prod_eq,(pm.map (fun z => z.2+1)).prod_eq] at balance
  simp only [List.map_cons, List.prod_cons] at balance
  exact balance.trans (by ring)

end Div245

/- Connecting the analytic exclusions to the computed root rows. -/

namespace Div245

theorem analytic_row_impossible {p a : ℕ} {s : List ℕ} {L : List (ℕ×ℕ)}
    (pm : s.Perm (L.map Prod.snd)) (ord : L.Pairwise (fun z w => z.1<w.1))
    (hp : p.Prime) (ha : 0<a) (pr : ∀ z ∈ L, z.1.Prime ∧ p<z.1)
    (bal : weight p a * (L.map (fun z => weight z.1 z.2)).prod =
      (p^a*((a+1)*(s.map (·+1)).prod+1))*(L.map (fun z => z.1^z.2)).prod)
    (row : analyticRow p a s = true) : False := by
  have pair (h : s=[1,1] ∨ (s=[1,4] ∧ ((p=251 ∧ a=25) ∨ (p=389 ∧ a=37)))) : False := by
    have hl : L.length=2 := by
      have he := pm.length_eq
      simp only [List.length_map] at he
      rcases h with e|⟨e,_⟩ <;> subst s <;> simpa using he.symm
    rcases L with _|⟨⟨q,b⟩,L⟩ <;> simp only [List.length_nil,List.length_cons] at hl
    · omega
    rcases L with _|⟨⟨r,c⟩,L⟩ <;> simp only [List.length_nil,List.length_cons] at hl
    · omega
    have hn : L=[] := List.length_eq_zero_iff.mp (by omega)
    subst L
    have qd := pr (q,b) (by simp)
    have rd := pr (r,c) (by simp)
    have oq : q<r := (List.pairwise_cons.mp ord).1 (r,c) (by simp)
    change s.Perm [b,c] at pm
    simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at bal
    rcases h with rfl|⟨rfl,pa⟩
    · have eq := (List.perm_replicate (n:=2) (a:=1)).mp pm.symm
      change [b,c]=[1,1] at eq
      simp only [List.cons.injEq,and_true] at eq
      obtain ⟨rfl,rfl⟩ := eq
      apply two_simple_impossible hp qd.1 rd.1 qd.2 oq ha
      have w1 (t : ℕ) : weight t 1=2*t+1 := by simp [weight]; ring
      rw [w1 q,w1 r,weight_spec] at bal
      exact bal.trans (by simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]; ring)
    · have eq := List.perm_pair.mp pm.symm
      simp only [List.cons.injEq,and_true] at eq
      apply two_mixed_roots_impossible pa eq oq.le qd.1.one_lt rd.1
      simp_rw [weight_spec] at bal
      exact bal.trans (by simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]; ring)
  simp only [analyticRow,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,List.any_eq_true] at row
  rcases row with (h|h)|h
  · exact pair (.inl h.1)
  · obtain ⟨e,he,⟨⟨elo,ehi,pl,pe⟩,erase⟩⟩ := h
    apply many_one_heavy ((p,a)::L) e elo ehi
    · intro z hz _
      rcases List.mem_cons.mp hz with rfl|hz
      · exact ⟨pl,pe⟩
      · exact ⟨pl.trans (pr z hz).2.le,pe.trans (pr z hz).2.le⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl|hz
      · exact hp.pos
      · exact (pr z hz).1.pos
    · exact List.pairwise_cons.mpr ⟨fun z hz => (pr z hz).2,ord⟩
    · have ep := List.perm_cons_erase he
      rw [erase] at ep
      exact (pm.cons a).symm.trans ep
    · have he := (pm.map (fun i => i+1)).prod_eq
      simp only [List.map_map, Function.comp_def] at he
      simp only [List.map_cons,List.prod_cons]
      simp_rw [←weight_spec]
      rw [←he]
      exact bal.trans (by ring)
  · exact pair (.inr h)

end Div245

/- A shared Lucas certificate graph for forced prime factors. The verifier
uses binary modular powering and records shared predecessor factors only once. -/
namespace Div245

theorem prime_of_factorial_window (p w : ℕ) (hp : 1 < p) (size : p < (w+1)^2)
    (cop : p.gcd w.factorial = 1) : p.Prime := by
  by_contra hn
  have sq := Nat.minFac_sq_le_self (by omega : 0 < p) hn
  have prime := Nat.minFac_prime (by omega : p ≠ 1)
  have small : p.minFac ≤ w := by
    by_contra! contra
    have h := Nat.pow_le_pow_left (by omega : w+1 ≤ p.minFac) 2
    omega
  have h := Nat.dvd_gcd (Nat.minFac_dvd p) (Nat.dvd_factorial prime.pos small)
  rw [cop, Nat.dvd_one] at h
  exact prime.ne_one h

theorem bounded_pow_mod (p a k e : ℕ) (hk : e < 2^k) :
    (Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 1%p)
      (fun _ f t => (f (t/2)^2*(if t%2=0 then 1 else a))%p) k e) = a^e%p := by
  induction k generalizing e with
  | zero =>
    have : e=0 := by simpa using hk
    subst e
    simp
  | succ k ih =>
    have h : e/2 < 2^k := (Nat.div_lt_iff_lt_mul (by decide : 0<2)).mpr (by simpa [pow_succ] using hk)
    change ((_ : ℕ)^2*(if e%2=0 then 1 else a))%p = a^e%p
    rw [ih _ h]
    have he : e = e/2*2 + e%2 := by omega
    conv_rhs => rw [he,pow_add,pow_mul]
    have ha : (if e%2=0 then 1 else a) = a^(e%2) := by
      split <;> rename_i hbit
      · simp [hbit]
      · simp [show e%2=1 by omega]
    rw [ha]
    exact ((Nat.mod_modEq _ _).pow 2).mul_right _

/-- Each non-leaf row contains the candidate, a Lucas witness, and the
complete factorization of its predecessor. The strict decreases justify sharing. -/
theorem lucas_graph (rows : List (ℕ × ℕ × List ℕ)) :
    let pool := rows.map Prod.fst
    let power (p a e : ℕ) := Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 1%p)
      (fun _ f t => (f (t/2)^2*(if t%2=0 then 1 else a))%p) (p.log2+1) e
    let check (row : ℕ × ℕ × List ℕ) :=
      let (p,a,fs) := row
      if a=0 then
        if p ≤ 12 then decide p.Prime else
          let w := if p ≤ 142 then 12 else 142
          decide (1 < p ∧ p < (w+1)^2 ∧ p.gcd w.factorial = 1)
      else
        decide (1<p ∧ p < 2^(p.log2+1) ∧ fs.prod=p-1) &&
        (power p a (p-1) == 1) &&
        fs.eraseDups.all (fun q => q < p && pool.contains q && power p a ((p-1)/q) != 1)
    rows.all check = true → ∀ r ∈ pool, Nat.Prime r := by
  intro pool power check ok r
  induction r using Nat.strong_induction_on with
  | h p ih =>
    intro mem
    obtain ⟨⟨t,a,fs⟩,hr,ht⟩ := List.mem_map.mp mem
    change t=p at ht
    subst t
    have row := List.all_eq_true.mp ok _ hr
    change (if a=0 then _ else _) = true at row
    split at row
    · split at row
      · exact of_decide_eq_true row
      · obtain ⟨positive,bound,cop⟩ := of_decide_eq_true row
        exact prime_of_factorial_window _ _ positive bound cop
    · obtain ⟨h0, tests⟩ := Bool.and_eq_true_iff.mp row
      obtain ⟨bounds, full⟩ := Bool.and_eq_true_iff.mp h0
      obtain ⟨hp,limit,hprod⟩ := of_decide_eq_true bounds
      have child (q : ℕ) (hq : q ∈ fs) := List.all_eq_true.mp tests q (List.mem_eraseDups.mpr hq)
      have fact (q : ℕ) (hq : q ∈ fs) : q.Prime := by
        obtain ⟨both,_⟩ := Bool.and_eq_true_iff.mp (child q hq)
        obtain ⟨lt,known⟩ := Bool.and_eq_true_iff.mp both
        exact ih q (of_decide_eq_true lt) (List.contains_iff_mem.mp known)
      have bridge (e : ℕ) (he : e ≤ p) :
          (a : ZMod p)^e = 1 ↔ power p a e = 1 := by
        rw [← Nat.cast_pow, ← Nat.cast_one (R := ZMod p), ZMod.natCast_eq_natCast_iff']
        have calcPow : power p a e = a^e%p := bounded_pow_mod p a _ e (he.trans_lt limit)
        rw [calcPow, Nat.mod_eq_of_lt hp]
      apply lucas_primality p (a : ZMod p) ((bridge (p-1) (by omega)).mpr (beq_iff_eq.mp full))
      intro q hq hd
      have memq := (Nat.mem_primeFactorsList (by omega : p-1 ≠ 0)).mpr ⟨hq,hd⟩
      have hqf := (Nat.primeFactorsList_unique hprod fact).mem_iff.mpr memq
      have neq := (Bool.and_eq_true_iff.mp (child q hqf)).2
      intro contra
      have eq := (bridge ((p-1)/q) ((Nat.div_le_self _ _).trans (by omega))).mp contra
      simp [eq] at neq

end Div245

/- Shared Lucas graph for the integer search. The certificates include entries provided by DomTheDeveloper. Numeric checks are separated into small batches. -/
namespace Div245

private def forcedLucasCheck (pool : List ℕ) (row : ℕ × ℕ × List ℕ) : Bool :=
  let power (p a e : ℕ) := Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 1%p)
    (fun _ f t => (f (t/2)^2*(if t%2=0 then 1 else a))%p) (p.log2+1) e
  let (p,a,fs) := row
  if a=0 then
    if p ≤ 12 then decide p.Prime else
      let w := if p ≤ 142 then 12 else 142
      decide (1 < p ∧ p < (w+1)^2 ∧ p.gcd w.factorial = 1)
  else
    decide (1<p ∧ p < 2^(p.log2+1) ∧ fs.prod=p-1) &&
    (power p a (p-1) == 1) &&
    fs.eraseDups.all (fun q => q < p && pool.contains q && power p a ((p-1)/q) != 1)

private def forcedBatch00 : List (ℕ × ℕ × List ℕ) := [
    (2,0,[]),
    (3,0,[]),
    (5,0,[]),
    (7,0,[]),
    (11,0,[]),
    (13,0,[]),
    (17,0,[]),
    (19,0,[]),
    (23,0,[]),
    (29,0,[]),
    (31,0,[]),
    (37,0,[]),
    (41,0,[]),
    (43,0,[]),
    (47,0,[]),
    (53,0,[]),
    (59,0,[]),
    (61,0,[]),
    (67,0,[]),
    (71,0,[]),
    (73,0,[]),
    (79,0,[]),
    (83,0,[]),
    (89,0,[])]

private def forcedBatch01 : List (ℕ × ℕ × List ℕ) := [
    (97,0,[]),
    (101,0,[]),
    (107,0,[]),
    (109,0,[]),
    (113,0,[]),
    (127,0,[]),
    (137,0,[]),
    (139,0,[]),
    (149,0,[]),
    (151,0,[]),
    (157,0,[]),
    (163,0,[]),
    (167,0,[]),
    (173,0,[]),
    (179,0,[]),
    (181,0,[]),
    (191,0,[]),
    (193,0,[]),
    (197,0,[]),
    (199,0,[]),
    (211,0,[]),
    (227,0,[]),
    (229,0,[]),
    (233,0,[])]

private def forcedBatch02 : List (ℕ × ℕ × List ℕ) := [
    (239,0,[]),
    (257,0,[]),
    (263,0,[]),
    (269,0,[]),
    (277,0,[]),
    (281,0,[]),
    (283,0,[]),
    (293,0,[]),
    (311,0,[]),
    (313,0,[]),
    (317,0,[]),
    (337,0,[]),
    (347,0,[]),
    (353,0,[]),
    (359,0,[]),
    (367,0,[]),
    (373,0,[]),
    (383,0,[]),
    (389,0,[]),
    (397,0,[]),
    (401,0,[]),
    (409,0,[]),
    (419,0,[]),
    (421,0,[])]

private def forcedBatch03 : List (ℕ × ℕ × List ℕ) := [
    (431,0,[]),
    (439,0,[]),
    (443,0,[]),
    (457,0,[]),
    (461,0,[]),
    (463,0,[]),
    (467,0,[]),
    (479,0,[]),
    (487,0,[]),
    (491,0,[]),
    (503,0,[]),
    (509,0,[]),
    (521,0,[]),
    (523,0,[]),
    (557,0,[]),
    (563,0,[]),
    (569,0,[]),
    (577,0,[]),
    (587,0,[]),
    (593,0,[]),
    (599,0,[]),
    (601,0,[]),
    (617,0,[]),
    (641,0,[])]

private def forcedBatch04 : List (ℕ × ℕ × List ℕ) := [
    (647,0,[]),
    (653,0,[]),
    (659,0,[]),
    (661,0,[]),
    (673,0,[]),
    (677,0,[]),
    (683,0,[]),
    (691,0,[]),
    (719,0,[]),
    (727,0,[]),
    (733,0,[]),
    (751,0,[]),
    (757,0,[]),
    (773,0,[]),
    (797,0,[]),
    (809,0,[]),
    (811,0,[]),
    (821,0,[]),
    (827,0,[]),
    (839,0,[]),
    (853,0,[]),
    (859,0,[]),
    (863,0,[]),
    (881,0,[])]

private def forcedBatch05 : List (ℕ × ℕ × List ℕ) := [
    (887,0,[]),
    (907,0,[]),
    (929,0,[]),
    (941,0,[]),
    (947,0,[]),
    (977,0,[]),
    (983,0,[]),
    (1013,0,[]),
    (1019,0,[]),
    (1021,0,[]),
    (1039,0,[]),
    (1051,0,[]),
    (1123,0,[]),
    (1151,0,[]),
    (1153,0,[]),
    (1171,0,[]),
    (1201,0,[]),
    (1229,0,[]),
    (1277,0,[]),
    (1283,0,[]),
    (1297,0,[]),
    (1321,0,[]),
    (1361,0,[]),
    (1373,0,[])]

private def forcedBatch06 : List (ℕ × ℕ × List ℕ) := [
    (1433,0,[]),
    (1439,0,[]),
    (1447,0,[]),
    (1471,0,[]),
    (1481,0,[]),
    (1493,0,[]),
    (1499,0,[]),
    (1543,0,[]),
    (1553,0,[]),
    (1579,0,[]),
    (1601,0,[]),
    (1607,0,[]),
    (1619,0,[]),
    (1669,0,[]),
    (1709,0,[]),
    (1721,0,[]),
    (1777,0,[]),
    (1783,0,[]),
    (1789,0,[]),
    (1867,0,[]),
    (1931,0,[]),
    (1997,0,[]),
    (2003,0,[]),
    (2083,0,[])]

private def forcedBatch07 : List (ℕ × ℕ × List ℕ) := [
    (2179,0,[]),
    (2267,0,[]),
    (2269,0,[]),
    (2281,0,[]),
    (2341,0,[]),
    (2411,0,[]),
    (2417,0,[]),
    (2441,0,[]),
    (2477,0,[]),
    (2521,0,[]),
    (2659,0,[]),
    (2677,0,[]),
    (2683,0,[]),
    (2687,0,[]),
    (2699,0,[]),
    (2777,0,[]),
    (2803,0,[]),
    (2843,0,[]),
    (2879,0,[]),
    (2927,0,[]),
    (2963,0,[]),
    (3001,0,[]),
    (3019,0,[]),
    (3083,0,[])]

private def forcedBatch08 : List (ℕ × ℕ × List ℕ) := [
    (3209,0,[]),
    (3217,0,[]),
    (3253,0,[]),
    (3373,0,[]),
    (3449,0,[]),
    (3539,0,[]),
    (3547,0,[]),
    (3821,0,[]),
    (3847,0,[]),
    (3863,0,[]),
    (3917,0,[]),
    (3989,0,[]),
    (4003,0,[]),
    (4091,0,[]),
    (4093,0,[]),
    (4129,0,[]),
    (4133,0,[]),
    (4157,0,[]),
    (4241,0,[]),
    (4363,0,[]),
    (4397,0,[]),
    (4441,0,[]),
    (4519,0,[]),
    (4729,0,[])]

private def forcedBatch09 : List (ℕ × ℕ × List ℕ) := [
    (4733,0,[]),
    (4787,0,[]),
    (5011,0,[]),
    (5147,0,[]),
    (5279,0,[]),
    (5351,0,[]),
    (5407,0,[]),
    (5431,0,[]),
    (5503,0,[]),
    (5791,0,[]),
    (5857,0,[]),
    (5861,0,[]),
    (6053,0,[]),
    (6091,0,[]),
    (6841,0,[]),
    (6869,0,[]),
    (7019,0,[]),
    (7237,0,[]),
    (7307,0,[]),
    (7591,0,[]),
    (8147,0,[]),
    (8761,0,[]),
    (8923,0,[]),
    (8963,0,[])]

private def forcedBatch10 : List (ℕ × ℕ × List ℕ) := [
    (8999,0,[]),
    (9007,0,[]),
    (9013,0,[]),
    (9157,0,[]),
    (9439,0,[]),
    (9623,0,[]),
    (10337,0,[]),
    (10529,0,[]),
    (10559,0,[]),
    (10589,0,[]),
    (10691,0,[]),
    (11969,0,[]),
    (12373,0,[]),
    (12421,0,[]),
    (12911,0,[]),
    (12923,0,[]),
    (13613,0,[]),
    (13873,0,[]),
    (14051,0,[]),
    (14149,0,[]),
    (14449,0,[]),
    (14557,0,[]),
    (15073,0,[]),
    (15161,0,[])]

private def forcedBatch11 : List (ℕ × ℕ × List ℕ) := [
    (15383,0,[]),
    (15439,0,[]),
    (15683,0,[]),
    (16067,0,[]),
    (18257,0,[]),
    (18443,0,[]),
    (18973,0,[]),
    (19181,0,[]),
    (19891,0,[]),
    (19993,0,[]),
    (20509,2,[2,2,3,1709]),
    (20611,2,[2,3,3,5,229]),
    (20879,11,[2,11,13,73]),
    (21089,3,[2,2,2,2,2,659]),
    (21379,2,[2,3,7,509]),
    (21737,6,[2,2,2,11,13,19]),
    (21751,3,[2,3,5,5,5,29]),
    (22013,2,[2,2,5503]),
    (22571,6,[2,5,37,61]),
    (23131,3,[2,3,3,5,257]),
    (23417,3,[2,2,2,2927]),
    (24223,3,[2,3,11,367]),
    (24547,2,[2,3,4091]),
    (24631,3,[2,3,5,821])]

private def forcedBatch12 : List (ℕ × ℕ × List ℕ) := [
    (24943,5,[2,3,4157]),
    (25847,5,[2,12923]),
    (26293,6,[2,2,3,7,313]),
    (26879,13,[2,89,151]),
    (27449,3,[2,2,2,47,73]),
    (28351,6,[2,3,3,3,3,5,5,7]),
    (28771,2,[2,3,5,7,137]),
    (28949,2,[2,2,7237]),
    (30211,2,[2,3,5,19,53]),
    (30253,2,[2,2,3,2521]),
    (30323,2,[2,15161]),
    (31511,7,[2,5,23,137]),
    (32191,6,[2,3,5,29,37]),
    (34057,5,[2,2,2,3,3,11,43]),
    (34549,2,[2,2,3,2879]),
    (35933,2,[2,2,13,691]),
    (37061,2,[2,2,5,17,109]),
    (43399,13,[2,3,3,2411]),
    (43781,2,[2,2,5,11,199]),
    (45827,2,[2,11,2083]),
    (46703,5,[2,19,1229]),
    (46889,3,[2,2,2,5861]),
    (47137,5,[2,2,2,2,2,3,491]),
    (50543,5,[2,37,683])]

private def forcedBatch13 : List (ℕ × ℕ × List ℕ) := [
    (52567,3,[2,3,8761]),
    (53569,19,[2,2,2,2,2,2,3,3,3,31]),
    (56299,10,[2,3,11,853]),
    (57427,2,[2,3,17,563]),
    (57467,2,[2,59,487]),
    (59233,5,[2,2,2,2,2,3,617]),
    (60647,5,[2,30323]),
    (61291,3,[2,3,3,3,5,227]),
    (61553,3,[2,2,2,2,3847]),
    (65173,2,[2,2,3,5431]),
    (70709,2,[2,2,11,1607]),
    (71867,2,[2,35933]),
    (72547,2,[2,3,107,113]),
    (75937,10,[2,2,2,2,2,3,7,113]),
    (76099,7,[2,3,11,1153]),
    (77617,10,[2,2,2,2,3,3,7,7,11]),
    (79193,3,[2,2,2,19,521]),
    (79769,3,[2,2,2,13,13,59]),
    (81043,5,[2,3,13,1039]),
    (81097,5,[2,2,2,3,31,109]),
    (86599,3,[2,3,3,17,283]),
    (86711,7,[2,5,13,23,29]),
    (90619,3,[2,3,11,1373]),
    (92251,2,[2,3,3,5,5,5,41])]

private def forcedBatch14 : List (ℕ × ℕ × List ℕ) := [
    (92401,34,[2,2,2,2,3,5,5,7,11]),
    (96377,3,[2,2,2,7,1721]),
    (96823,5,[2,3,3,3,11,163]),
    (96893,2,[2,2,24223]),
    (100153,5,[2,2,2,3,3,13,107]),
    (101599,11,[2,3,7,41,59]),
    (102107,2,[2,19,2687]),
    (106411,2,[2,3,5,3547]),
    (115693,2,[2,2,3,31,311]),
    (117979,10,[2,3,7,53,53]),
    (119653,2,[2,2,3,13,13,59]),
    (122273,3,[2,2,2,2,2,3821]),
    (123059,2,[2,13,4733]),
    (129281,3,[2,2,2,2,2,2,2,2,5,101]),
    (133379,2,[2,7,7,1361]),
    (133417,5,[2,2,2,3,3,17,109]),
    (134947,13,[2,3,3,3,3,7,7,17]),
    (137131,3,[2,3,5,7,653]),
    (141241,19,[2,2,2,3,5,11,107]),
    (141499,13,[2,3,3,7,1123]),
    (144451,2,[2,3,3,3,5,5,107]),
    (146513,3,[2,2,2,2,9157]),
    (148949,2,[2,2,23,1619]),
    (163997,5,[2,2,7,5857])]

private def forcedBatch15 : List (ℕ × ℕ × List ℕ) := [
    (165553,5,[2,2,2,2,3,3449]),
    (188017,5,[2,2,2,2,3,3917]),
    (188197,2,[2,2,3,15683]),
    (193147,2,[2,3,32191]),
    (216577,5,[2,2,2,2,2,2,2,2,2,3,3,47]),
    (217463,5,[2,7,7,7,317]),
    (234809,3,[2,2,2,7,7,599]),
    (244547,2,[2,122273]),
    (246119,11,[2,123059]),
    (277741,2,[2,2,3,3,5,1543]),
    (280219,10,[2,3,46703]),
    (281947,2,[2,3,7,7,7,137]),
    (297809,3,[2,2,2,2,7,2659]),
    (335381,2,[2,2,5,41,409]),
    (343177,5,[2,2,2,3,79,181]),
    (369319,6,[2,3,61553]),
    (406397,2,[2,2,101599]),
    (417581,2,[2,2,5,20879]),
    (432137,3,[2,2,2,19,2843]),
    (438169,11,[2,2,2,3,18257]),
    (480107,2,[2,11,139,157]),
    (565163,2,[2,13,21737]),
    (586213,2,[2,2,3,11,4441]),
    (612109,2,[2,2,3,3,7,7,347])]

private def forcedBatch16 : List (ℕ × ℕ × List ℕ) := [
    (612643,2,[2,3,102107]),
    (626317,2,[2,2,3,19,41,67]),
    (630433,5,[2,2,2,2,2,3,3,11,199]),
    (651731,2,[2,5,65173]),
    (685093,5,[2,2,3,37,1543]),
    (712183,10,[2,3,29,4093]),
    (727021,2,[2,2,3,3,5,7,577]),
    (752789,2,[2,2,188197]),
    (756641,6,[2,2,2,2,2,5,4729]),
    (773867,2,[2,97,3989]),
    (779101,2,[2,2,3,5,5,7,7,53]),
    (980137,5,[2,2,2,3,3,13613]),
    (1032841,7,[2,2,2,3,3,5,19,151]),
    (1034503,5,[2,3,7,24631]),
    (1087451,7,[2,5,5,7,13,239]),
    (1183157,2,[2,2,13,61,373]),
    (1288249,17,[2,2,2,3,13,4129]),
    (1316921,12,[2,2,2,5,11,41,73]),
    (1324361,3,[2,2,2,5,113,293]),
    (1339669,2,[2,2,3,3,11,17,199]),
    (1361401,11,[2,2,2,3,5,5,2269]),
    (1383301,6,[2,2,3,3,5,5,29,53]),
    (1576723,2,[2,3,7,7,31,173]),
    (1834799,7,[2,7,83,1579])]

private def forcedBatch17 : List (ℕ × ℕ × List ℕ) := [
    (2053201,7,[2,2,2,2,3,5,5,29,59]),
    (2139757,2,[2,2,3,17,17,617]),
    (2155171,2,[2,3,5,19,19,199]),
    (2203589,2,[2,2,593,929]),
    (2523217,10,[2,2,2,2,3,52567]),
    (2755463,5,[2,17,81043]),
    (2811659,2,[2,19,23,3217]),
    (2817709,2,[2,2,3,234809]),
    (2879803,3,[2,3,3,139,1151]),
    (3298811,2,[2,5,107,3083]),
    (3321037,2,[2,2,3,3,92251]),
    (3372641,3,[2,2,2,2,2,5,107,197]),
    (3617069,10,[2,2,7,13,19,523]),
    (3617951,14,[2,5,5,7,10337]),
    (3669599,13,[2,1834799]),
    (3964733,2,[2,2,47,21089]),
    (4446433,5,[2,2,2,2,2,3,3,15439]),
    (4471171,11,[2,3,5,11,17,797]),
    (4536179,2,[2,17,133417]),
    (4636711,6,[2,3,3,3,5,13,1321]),
    (5053693,2,[2,2,3,7,17,3539]),
    (5537881,7,[2,2,2,3,3,5,15383]),
    (5547277,2,[2,2,3,3,7,22013]),
    (5839291,12,[2,3,3,3,3,3,3,3,3,5,89])]

private def forcedBatch18 : List (ℕ × ℕ × List ℕ) := [
    (5986961,3,[2,2,2,2,5,7,10691]),
    (6201863,5,[2,193,16067]),
    (6468031,21,[2,3,3,5,71867]),
    (6861697,5,[2,2,2,2,2,2,2,3,107,167]),
    (7083499,3,[2,3,983,1201]),
    (7098943,3,[2,3,1183157]),
    (7212319,11,[2,3,17,70709]),
    (7522901,2,[2,2,5,5,7,11,977]),
    (7710161,3,[2,2,2,2,5,96377]),
    (8330963,2,[2,167,24943]),
    (9072359,7,[2,4536179]),
    (10545211,15,[2,3,3,5,13,9013]),
    (12688981,2,[2,2,3,5,79,2677]),
    (12741733,5,[2,2,3,3,3,117979]),
    (14397319,6,[2,3,3,3,13,20509]),
    (15308633,3,[2,2,2,463,4133]),
    (18244067,2,[2,19,480107]),
    (21873097,5,[2,2,2,3,3,7,43399]),
    (23601373,5,[2,2,3,17,115693]),
    (24352957,2,[2,2,3,3,37,47,389]),
    (24505219,2,[2,3,3,1361401]),
    (30401537,3,[2,2,2,2,2,2,2,2,2,2,11,2699]),
    (30978047,5,[2,11,17,113,733]),
    (32586551,7,[2,5,5,651731])]

private def forcedBatch19 : List (ℕ × ℕ × List ℕ) := [
    (33730001,3,[2,2,2,2,5,5,5,5,3373]),
    (33825601,7,[2,2,2,2,2,2,3,3,3,3,3,3,5,5,29]),
    (33926887,3,[2,3,3,7,23,23,509]),
    (40471693,2,[2,2,3,3372641]),
    (42897313,5,[2,2,2,2,2,3,3,148949]),
    (48575101,10,[2,2,3,5,5,7,23131]),
    (50901259,2,[2,3,683,12421]),
    (53244353,3,[2,2,2,2,2,2,7,157,757]),
    (62431921,11,[2,2,2,2,3,3,5,86711]),
    (63017483,2,[2,11,31,92401]),
    (63271267,3,[2,3,10545211]),
    (65173103,5,[2,32586551]),
    (65580481,26,[2,2,2,2,2,2,3,3,5,7,3253]),
    (66052783,5,[2,3,3,3669599]),
    (67621321,7,[2,2,2,3,3,5,13,14449]),
    (74718443,2,[2,29,1288249]),
    (75879569,3,[2,2,2,2,17,31,8999]),
    (79866529,11,[2,2,2,2,2,3,7,157,757]),
    (93807871,6,[2,3,5,13,17,14149]),
    (95298881,6,[2,2,2,2,2,2,5,297809]),
    (105518341,2,[2,2,3,3,5,586213]),
    (132852787,2,[2,3,11,71,28351]),
    (136306273,5,[2,2,2,2,2,3,17,17,17,17,17]),
    (138561641,6,[2,2,2,5,7,47,10529])]

private def forcedBatch20 : List (ℕ × ℕ × List ℕ) := [
    (142009289,3,[2,2,2,29,612109]),
    (151916899,2,[2,3,7,3617069]),
    (155323757,2,[2,2,7,5547277]),
    (160962157,2,[2,2,3,3,4471171]),
    (168668873,3,[2,2,2,29,727021]),
    (172225117,2,[2,2,3,3,3,3,7,75937]),
    (179044939,2,[2,3,3,3,239,13873]),
    (179415311,11,[2,5,1499,11969]),
    (185468441,3,[2,2,2,5,4636711]),
    (190597763,2,[2,95298881]),
    (207911719,7,[2,3,3,3,7,19,28949]),
    (246020669,2,[2,2,17,3617951]),
    (261672379,2,[2,3,11,3964733]),
    (279509459,2,[2,5407,25847]),
    (339268871,13,[2,5,33926887]),
    (383342923,2,[2,3,3,3,7098943]),
    (517881713,3,[2,2,2,2,107,113,2677]),
    (590572933,2,[2,2,3,23,2139757]),
    (615806327,5,[2,347,443,2003]),
    (744163223,5,[2,11,33825601]),
    (825906901,11,[2,2,3,5,5,7,13,30253]),
    (1169845093,5,[2,2,3,3,3,3,13,277741]),
    (1182320609,3,[2,2,2,2,2,7,7,41,53,347]),
    (1506537079,6,[2,3,43,5839291])]

private def forcedBatch21 : List (ℕ × ℕ × List ℕ) := [
    (2036050361,3,[2,2,2,5,50901259]),
    (2191766131,3,[2,3,3,5,24352957]),
    (2581316131,2,[2,3,5,41,233,9007]),
    (2624279201,3,[2,2,2,2,2,5,5,1447,2267]),
    (2840185781,3,[2,2,5,142009289]),
    (2898677407,6,[2,3,467,1034503]),
    (3354113509,6,[2,2,3,279509459]),
    (4576002647,5,[2,83,1123,24547]),
    (4847190743,5,[2,191,12688981]),
    (4929079429,6,[2,2,3,3,7,13,73,20611]),
    (5680371563,2,[2,2840185781]),
    (6144547567,10,[2,3,23,59,167,4519]),
    (6569011187,2,[2,23,43,3321037]),
    (6845751949,6,[2,2,3,7,29,31,269,337]),
    (7631124997,6,[2,2,3,11,67,149,5791]),
    (8098937527,5,[2,3,53,197,129281]),
    (8260528891,3,[2,3,5,23,73,163997]),
    (8502578369,3,[2,2,2,2,2,2,132852787]),
    (10776932423,5,[2,313,1789,9623]),
    (12747358969,13,[2,2,2,3,31,929,18443]),
    (15376226549,2,[2,2,31,283,438169]),
    (17603588341,7,[2,2,3,3,5,13,7522901]),
    (18826432871,7,[2,5,7,37,563,12911]),
    (23164549021,2,[2,2,3,3,3,5,42897313])]

private def forcedBatch22 : List (ℕ × ℕ × List ℕ) := [
    (24219708673,5,[2,2,2,2,2,2,2,2,3,29,1087451]),
    (26301193573,2,[2,2,3,2191766131]),
    (28986774071,26,[2,5,2898677407]),
    (30301253953,5,[2,2,2,2,2,2,3,23,6861697]),
    (32008271723,2,[2,7,317,7212319]),
    (37652865743,5,[2,18826432871]),
    (50363928533,2,[2,2,199,63271267]),
    (51467697121,29,[2,2,2,2,2,3,5,7,1709,8963]),
    (58695306629,2,[2,2,7,31,67621321]),
    (61150311611,2,[2,5,43,859,165553]),
    (65110972211,2,[2,5,18973,343177]),
    (102058480283,2,[2,11,53569,86599]),
    (105679530977,3,[2,2,2,2,2,41,107,752789]),
    (117390613259,2,[2,58695306629]),
    (131022650417,3,[2,2,2,2,7,1169845093]),
    (154783264061,3,[2,2,5,27449,281947]),
    (167687167009,7,[2,2,2,2,2,3,47,89,417581]),
    (214805549993,3,[2,2,2,11,293,8330963]),
    (234787945631,7,[2,5,7,3354113509]),
    (274952110187,2,[2,13,19,353,1576723]),
    (398871487529,3,[2,2,2,67,744163223]),
    (408716967719,7,[2,29,5351,1316921]),
    (555240796003,5,[2,3,3,3,3,23,53,2811659]),
    (581776445227,2,[2,3,563,172225117])]

private def forcedBatch23 : List (ℕ × ℕ × List ℕ) := [
    (595861556993,3,[2,2,2,2,2,2,2,2,13,179044939]),
    (797742975059,2,[2,398871487529]),
    (826629447841,13,[2,2,2,2,2,3,5,7,246020669]),
    (1302219444221,2,[2,2,5,65110972211]),
    (1596161396191,12,[2,3,5,47,89,127,100153]),
    (1719798921283,3,[2,3,13,13,3001,565163]),
    (1951101465767,5,[2,107,14557,626317]),
    (2725310640323,2,[2,31,283,155323757]),
    (3094619080181,7,[2,2,5,23,79,139,612643]),
    (3478412888521,11,[2,2,2,3,5,28986774071]),
    (4139134143421,6,[2,2,3,5,409,168668873]),
    (4775975935363,2,[2,3,3,3,19891,4446433]),
    (7088352000427,2,[2,3,3,17,23164549021]),
    (8559853947041,3,[2,2,2,2,2,5,11,157,30978047]),
    (9752308271351,7,[2,5,5,41,61291,77617]),
    (10417755553769,3,[2,2,2,1302219444221]),
    (13974006881147,2,[2,13,71,22571,335381]),
    (14359373551063,3,[2,3,3,797742975059]),
    (19103903741453,2,[2,2,4775975935363]),
    (20835511107539,2,[2,10417755553769]),
    (22374118403621,2,[2,2,5,71,797,1867,10589]),
    (33311847537949,2,[2,2,3,7,193147,2053201]),
    (44748236807243,2,[2,22374118403621]),
    (63062515328887,3,[2,3,3,46889,74718443])]

private def forcedBatch24 : List (ℕ × ℕ × List ℕ) := [
    (81284033392921,11,[2,2,2,3,3,5,19,31,383342923]),
    (150212655155791,6,[2,3,3,5,29,29,14051,141241]),
    (182731447799029,10,[2,2,3,3,3,3,277,2036050361]),
    (319593384716803,7,[2,3,7,188017,40471693]),
    (635927379490849,7,[2,2,2,2,2,3,4397,1506537079]),
    (1150081090216307,2,[2,211,2725310640323]),
    (1647238560869113,5,[2,2,2,3,43,1596161396191]),
    (2807016441703633,5,[2,2,2,2,3,3,191,102058480283]),
    (3812570706782993,5,[2,2,2,2,7,11,3094619080181]),
    (8036300276545637,2,[2,2,7307,274952110187]),
    (30486691755424187,2,[2,19,67,593,15073,1339669]),
    (44854364709863143,3,[2,3,7,19,21379,34549,76099]),
    (51284105359262441,3,[2,2,2,5,7,23,1032841,7710161]),
    (89706325036871947,3,[2,3,13,1150081090216307]),
    (196491150919254311,7,[2,5,7,2807016441703633]),
    (725799727597058927,5,[2,7,661,2083,37652865743]),
    (3498950330708810221,6,[2,2,3,3,5,23,97,173,50363928533]),
    (5778784727260815889,14,[2,2,2,2,3,3,83,139,3478412888521]),
    (14635092528104565487,3,[2,3,138561641,17603588341]),
    (17640717292851439867,11,[2,3,5053693,581776445227]),
    (78478332842421863213,2,[2,2,53,233,4363,56299,6468031]),
    (86560917171794057467,2,[2,3,3,3,3,127,293,14359373551063]),
    (206708690767055535173,2,[2,2,263,196491150919254311]),
    (321290896024828567001,6,[2,2,2,5,5,5,83,89,281,154783264061])]

private def forcedBatch25 : List (ℕ × ℕ × List ℕ) := [
    (920314054593070719437,2,[2,2,317,725799727597058927]),
    (1880508400376490752657,3,[2,2,2,2,509,33730001,6845751949]),
    (1883836937069958237217,15,[2,2,2,2,2,3,5147,3812570706782993]),
    (2168949226838008152479,7,[2,134947,8036300276545637]),
    (3826786260314991211367,5,[2,5986961,319593384716803]),
    (4844271667741331987201,3,[2,2,2,2,2,2,2,2,5,5,13,12373,369319,12741733]),
    (5124623469105161024569,13,[2,2,2,3,3,3,1777,43781,141499,2155171]),
    (5525347040369568803507,2,[2,90619,30486691755424187]),
    (60407435754889924251403,2,[2,3,3,263,947,3019,23417,190597763]),
    (128718467849545940154241,11,[2,2,2,2,2,2,2,3,3,5,73,6841,44748236807243]),
    (1493245581621988783545433,10,[2,2,2,3,3,7,7,2817709,150212655155791]),
    (2771892741557562936922373,2,[2,2,863,93807871,8559853947041]),
    (11278310349707882455928579,2,[2,29,73,151,17640717292851439867]),
    (80757992885189113465213993,5,[2,2,2,3,137,1013,133379,980137,185468441]),
    (1387366555902446403685366447,3,[2,3,13,1277,8098937527,1719798921283]),
    (251341629210651754903736062193,3,[2,2,2,2,149,18244067,5778784727260815889]),
    (59737124597292648185414913209393,3,[2,2,2,2,227,15308633,4576002647,234787945631]),
    (183450530871106267013736211463173,2,[2,2,3,5407,5537881,261672379,1951101465767]),
    (285498811742277931917137438827867,2,[2,3,409,30401537,3826786260314991211367]),
    (535822240852170004076631088649327,5,[2,179415311,1493245581621988783545433]),
    (542512058959614745217387126772353,3,[2,2,2,2,2,2,2,29,257,269,144451,14635092528104565487]),
    (1295309273607968370700398258494227,2,[2,3,685093,6144547567,51284105359262441]),
    (978421835301554251632360872955392545223,5,[2,7,14397319,2581316131,1880508400376490752657]),
    (7043093065953921339195010511780395502167,3,[2,3,31511,2203589,3298811,5124623469105161024569])]

private def forcedBatch26 : List (ℕ × ℕ × List ℕ) := [
    (10037566653262838460593813688652541806393,5,[2,2,2,3,61,113,1439,7631124997,5525347040369568803507]),
    (51614441682848567194150820050144397020481,3,[2,2,2,2,2,2,5,24505219,65173103,4847190743,20835511107539]),
    (2544456102028701855435052121524386993552097,7,[2,2,2,2,2,3,11,73,408716967719,80757992885189113465213993]),
    (6591642899211909277635103388839711484157169,19,[2,2,2,2,3,3,3,3,13,2523217,32008271723,4844271667741331987201]),
    (12313323426068810258421045085179151336457802703,3,[2,3,11,137,217463,555240796003,11278310349707882455928579]),
    (21759099163796972141780651325712249354887750413,2,[2,2,11,30211,773867,9752308271351,2168949226838008152479]),
    (21942162254588833528538249689440133713390636446077,2,[2,2,3,7,193,1383301,978421835301554251632360872955392545223]),
    (6855613849526198207150406319489725644984945053774794671,7,[2,5,137,406397,12313323426068810258421045085179151336457802703]),
    (966925188529564263993895916700986439713150768980132286531,2,[2,5,7,167,23601373,19103903741453,183450530871106267013736211463173]),
    (84026314384070513234463880358495204042562939860627507203821761291,2,[2,5,157,347,7088352000427,21759099163796972141780651325712249354887750413]),
    (196561891946625316608425590812136130631488792108315348157158819267,2,[2,151,359,432137,81284033392921,51614441682848567194150820050144397020481]),
    (262826251005741883539713937612151569908334640758626608520084941393,5,[2,2,2,2,3,101,941,62431921,131022650417,7043093065953921339195010511780395502167]),
    (107032548358919427693327257148782884618685660222072551941378726306878698528344822341221,2,[2,2,3,3,3,5,31,71,26879,12747358969,262826251005741883539713937612151569908334640758626608520084941393]),
    (1104999373555695655228644798455003043045395612543828686530929624300378786997003359907683405568943,6,[2,3,3,23,421,59233,107032548358919427693327257148782884618685660222072551941378726306878698528344822341221])]

private def forcedRows : List (ℕ × ℕ × List ℕ) :=
  forcedBatch00 ++ forcedBatch01 ++ forcedBatch02 ++ forcedBatch03 ++ forcedBatch04 ++ forcedBatch05 ++ forcedBatch06 ++ forcedBatch07 ++ forcedBatch08 ++ forcedBatch09 ++ forcedBatch10 ++ forcedBatch11 ++ forcedBatch12 ++ forcedBatch13 ++ forcedBatch14 ++ forcedBatch15 ++ forcedBatch16 ++ forcedBatch17 ++ forcedBatch18 ++ forcedBatch19 ++ forcedBatch20 ++ forcedBatch21 ++ forcedBatch22 ++ forcedBatch23 ++ forcedBatch24 ++ forcedBatch25 ++ forcedBatch26

private def forcedPrimes : List ℕ := forcedRows.map Prod.fst

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck00 : forcedBatch00.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck01 : forcedBatch01.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck02 : forcedBatch02.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck03 : forcedBatch03.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck04 : forcedBatch04.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck05 : forcedBatch05.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck06 : forcedBatch06.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck07 : forcedBatch07.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck08 : forcedBatch08.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck09 : forcedBatch09.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck10 : forcedBatch10.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck11 : forcedBatch11.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck12 : forcedBatch12.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck13 : forcedBatch13.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck14 : forcedBatch14.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck15 : forcedBatch15.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck16 : forcedBatch16.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck17 : forcedBatch17.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck18 : forcedBatch18.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck19 : forcedBatch19.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck20 : forcedBatch20.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck21 : forcedBatch21.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck22 : forcedBatch22.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck23 : forcedBatch23.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck24 : forcedBatch24.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck25 : forcedBatch25.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem forcedCheck26 : forcedBatch26.all (forcedLucasCheck forcedPrimes) = true := by decide +kernel

private def forcedNames : List ℕ :=
      [2, 3, 5, 7, 11, 13, 17, 19, 23, 29,
      31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
      73, 79, 83, 89, 97, 101, 107, 109, 113, 127,
      137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
      191, 193, 197, 199, 211, 227, 229, 233, 239, 257,
      263, 269, 277, 281, 283, 293, 311, 313, 317, 337,
      347, 353, 359, 367, 373, 383, 389, 397, 401, 409,
      419, 421, 431, 439, 443, 457, 461, 463, 467, 479,
      487, 491, 503, 509, 521, 523, 557, 563, 569, 577,
      587, 593, 599, 601, 617, 641, 647, 653, 659, 661,
      673, 677, 683, 691, 719, 727, 733, 751, 757, 773,
      797, 809, 811, 821, 827, 839, 853, 859, 863, 881,
      887, 907, 929, 941, 947, 977, 983, 1013, 1019, 1021,
      1039, 1051, 1123, 1151, 1153, 1171, 1201, 1229, 1277, 1283,
      1297, 1321, 1361, 1373, 1433, 1439, 1447, 1471, 1481, 1493,
      1499, 1543, 1553, 1579, 1601, 1607, 1619, 1669, 1709, 1721,
      1777, 1783, 1789, 1867, 1931, 1997, 2003, 2083, 2179, 2267,
      2269, 2281, 2341, 2411, 2417, 2441, 2477, 2521, 2659, 2677,
      2683, 2687, 2699, 2777, 2803, 2843, 2879, 2927, 2963, 3001,
      3019, 3083, 3209, 3217, 3253, 3373, 3449, 3539, 3547, 3821,
      3847, 3863, 3917, 3989, 4003, 4091, 4093, 4129, 4133, 4157,
      4241, 4363, 4397, 4441, 4519, 4729, 4733, 4787, 5011, 5147,
      5279, 5351, 5407, 5431, 5503, 5791, 5857, 5861, 6053, 6091,
      6841, 6869, 7019, 7237, 7307, 7591, 8147, 8761, 8923, 8963,
      8999, 9007, 9013, 9157, 9439, 9623, 10337, 10529, 10559, 10589,
      10691, 11969, 12373, 12421, 12911, 12923, 13613, 13873, 14051, 14149,
      14449, 14557, 15073, 15161, 15383, 15439, 15683, 16067, 18257, 18443,
      18973, 19181, 19891, 19993, 20509, 20611, 20879, 21089, 21379, 21737,
      21751, 22013, 22571, 23131, 23417, 24223, 24547, 24631, 24943, 25847,
      26293, 26879, 27449, 28351, 28771, 28949, 30211, 30253, 30323, 31511,
      32191, 34057, 34549, 35933, 37061, 43399, 43781, 45827, 46703, 46889,
      47137, 50543, 52567, 53569, 56299, 57427, 57467, 59233, 60647, 61291,
      61553, 65173, 70709, 71867, 72547, 75937, 76099, 77617, 79193, 79769,
      81043, 81097, 86599, 86711, 90619, 92251, 92401, 96377, 96823, 96893,
      100153, 101599, 102107, 106411, 115693, 117979, 119653, 122273, 123059, 129281,
      133379, 133417, 134947, 137131, 141241, 141499, 144451, 146513, 148949, 163997,
      165553, 188017, 188197, 193147, 216577, 217463, 234809, 244547, 246119, 277741,
      280219, 281947, 297809, 335381, 343177, 369319, 406397, 417581, 432137, 438169,
      480107, 565163, 586213, 612109, 612643, 626317, 630433, 651731, 685093, 712183,
      727021, 752789, 756641, 773867, 779101, 980137, 1032841, 1034503, 1087451, 1183157,
      1288249, 1316921, 1324361, 1339669, 1361401, 1383301, 1576723, 1834799, 2053201, 2139757,
      2155171, 2203589, 2523217, 2755463, 2811659, 2817709, 2879803, 3298811, 3321037, 3372641,
      3617069, 3617951, 3669599, 3964733, 4446433, 4471171, 4536179, 4636711, 5053693, 5537881,
      5547277, 5839291, 5986961, 6201863, 6468031, 6861697, 7083499, 7098943, 7212319, 7522901,
      7710161, 8330963, 9072359, 10545211, 12688981, 12741733, 14397319, 15308633, 18244067, 21873097,
      23601373, 24352957, 24505219, 30401537, 30978047, 32586551, 33730001, 33825601, 33926887, 40471693,
      42897313, 48575101, 50901259, 53244353, 62431921, 63017483, 63271267, 65173103, 65580481, 66052783,
      67621321, 74718443, 75879569, 79866529, 93807871, 95298881, 105518341, 132852787, 136306273, 138561641,
      142009289, 151916899, 155323757, 160962157, 168668873, 172225117, 179044939, 179415311, 185468441, 190597763,
      207911719, 246020669, 261672379, 279509459, 339268871, 383342923, 517881713, 590572933, 615806327, 744163223,
      825906901, 1169845093, 1182320609, 1506537079, 2036050361, 2191766131, 2581316131, 2624279201, 2840185781, 2898677407,
      3354113509, 4576002647, 4847190743, 4929079429, 5680371563, 6144547567, 6569011187, 6845751949, 7631124997, 8098937527,
      8260528891, 8502578369, 10776932423, 12747358969, 15376226549, 17603588341, 18826432871, 23164549021, 24219708673, 26301193573,
      28986774071, 30301253953, 32008271723, 37652865743, 50363928533, 51467697121, 58695306629, 61150311611, 65110972211, 102058480283,
      105679530977, 117390613259, 131022650417, 154783264061, 167687167009, 214805549993, 234787945631, 274952110187, 398871487529, 408716967719,
      555240796003, 581776445227, 595861556993, 797742975059, 826629447841, 1302219444221, 1596161396191, 1719798921283, 1951101465767, 2725310640323,
      3094619080181, 3478412888521, 4139134143421, 4775975935363, 7088352000427, 8559853947041, 9752308271351, 10417755553769, 13974006881147, 14359373551063,
      19103903741453, 20835511107539, 22374118403621, 33311847537949, 44748236807243, 63062515328887, 81284033392921, 150212655155791, 182731447799029, 319593384716803,
      635927379490849, 1150081090216307, 1647238560869113, 2807016441703633, 3812570706782993, 8036300276545637, 30486691755424187, 44854364709863143, 51284105359262441, 89706325036871947,
      196491150919254311, 725799727597058927, 3498950330708810221, 5778784727260815889, 14635092528104565487, 17640717292851439867, 78478332842421863213, 86560917171794057467, 206708690767055535173, 321290896024828567001,
      920314054593070719437, 1880508400376490752657, 1883836937069958237217, 2168949226838008152479, 3826786260314991211367, 4844271667741331987201, 5124623469105161024569, 5525347040369568803507, 60407435754889924251403, 128718467849545940154241,
      1493245581621988783545433, 2771892741557562936922373, 11278310349707882455928579, 80757992885189113465213993, 1387366555902446403685366447, 251341629210651754903736062193, 59737124597292648185414913209393, 183450530871106267013736211463173, 285498811742277931917137438827867, 535822240852170004076631088649327,
      542512058959614745217387126772353, 1295309273607968370700398258494227, 978421835301554251632360872955392545223, 7043093065953921339195010511780395502167, 10037566653262838460593813688652541806393, 51614441682848567194150820050144397020481, 2544456102028701855435052121524386993552097, 6591642899211909277635103388839711484157169, 12313323426068810258421045085179151336457802703, 21759099163796972141780651325712249354887750413,
      21942162254588833528538249689440133713390636446077, 6855613849526198207150406319489725644984945053774794671, 966925188529564263993895916700986439713150768980132286531, 84026314384070513234463880358495204042562939860627507203821761291, 196561891946625316608425590812136130631488792108315348157158819267, 262826251005741883539713937612151569908334640758626608520084941393, 107032548358919427693327257148782884618685660222072551941378726306878698528344822341221, 1104999373555695655228644798455003043045395612543828686530929624300378786997003359907683405568943]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 3000000 in
private theorem forced_names : forcedPrimes = forcedNames := by decide +kernel

private theorem forced_join {α : Type} {f : α → Bool} {x y : List α} (hx : x.all f = true) (hy : y.all f = true) : (x ++ y).all f = true := by rw [List.all_append, hx, hy]; rfl

set_option maxRecDepth 24000 in
set_option maxHeartbeats 3000000 in
private theorem forced_checked : forcedRows.all (forcedLucasCheck forcedPrimes) = true :=
  (forced_join forcedCheck00 (forced_join forcedCheck01 (forced_join forcedCheck02 (forced_join forcedCheck03 (forced_join forcedCheck04 (forced_join forcedCheck05 (forced_join forcedCheck06 (forced_join forcedCheck07 (forced_join forcedCheck08 (forced_join forcedCheck09 (forced_join forcedCheck10 (forced_join forcedCheck11 (forced_join forcedCheck12 (forced_join forcedCheck13 (forced_join forcedCheck14 (forced_join forcedCheck15 (forced_join forcedCheck16 (forced_join forcedCheck17 (forced_join forcedCheck18 (forced_join forcedCheck19 (forced_join forcedCheck20 (forced_join forcedCheck21 (forced_join forcedCheck22 (forced_join forcedCheck23 (forced_join forcedCheck24 (forced_join forcedCheck25 forcedCheck26))))))))))))))))))))))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 3000000 in
theorem forced_pool_prime (p : ℕ) (hp : p ∈
      [2, 3, 5, 7, 11, 13, 17, 19, 23, 29,
      31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
      73, 79, 83, 89, 97, 101, 107, 109, 113, 127,
      137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
      191, 193, 197, 199, 211, 227, 229, 233, 239, 257,
      263, 269, 277, 281, 283, 293, 311, 313, 317, 337,
      347, 353, 359, 367, 373, 383, 389, 397, 401, 409,
      419, 421, 431, 439, 443, 457, 461, 463, 467, 479,
      487, 491, 503, 509, 521, 523, 557, 563, 569, 577,
      587, 593, 599, 601, 617, 641, 647, 653, 659, 661,
      673, 677, 683, 691, 719, 727, 733, 751, 757, 773,
      797, 809, 811, 821, 827, 839, 853, 859, 863, 881,
      887, 907, 929, 941, 947, 977, 983, 1013, 1019, 1021,
      1039, 1051, 1123, 1151, 1153, 1171, 1201, 1229, 1277, 1283,
      1297, 1321, 1361, 1373, 1433, 1439, 1447, 1471, 1481, 1493,
      1499, 1543, 1553, 1579, 1601, 1607, 1619, 1669, 1709, 1721,
      1777, 1783, 1789, 1867, 1931, 1997, 2003, 2083, 2179, 2267,
      2269, 2281, 2341, 2411, 2417, 2441, 2477, 2521, 2659, 2677,
      2683, 2687, 2699, 2777, 2803, 2843, 2879, 2927, 2963, 3001,
      3019, 3083, 3209, 3217, 3253, 3373, 3449, 3539, 3547, 3821,
      3847, 3863, 3917, 3989, 4003, 4091, 4093, 4129, 4133, 4157,
      4241, 4363, 4397, 4441, 4519, 4729, 4733, 4787, 5011, 5147,
      5279, 5351, 5407, 5431, 5503, 5791, 5857, 5861, 6053, 6091,
      6841, 6869, 7019, 7237, 7307, 7591, 8147, 8761, 8923, 8963,
      8999, 9007, 9013, 9157, 9439, 9623, 10337, 10529, 10559, 10589,
      10691, 11969, 12373, 12421, 12911, 12923, 13613, 13873, 14051, 14149,
      14449, 14557, 15073, 15161, 15383, 15439, 15683, 16067, 18257, 18443,
      18973, 19181, 19891, 19993, 20509, 20611, 20879, 21089, 21379, 21737,
      21751, 22013, 22571, 23131, 23417, 24223, 24547, 24631, 24943, 25847,
      26293, 26879, 27449, 28351, 28771, 28949, 30211, 30253, 30323, 31511,
      32191, 34057, 34549, 35933, 37061, 43399, 43781, 45827, 46703, 46889,
      47137, 50543, 52567, 53569, 56299, 57427, 57467, 59233, 60647, 61291,
      61553, 65173, 70709, 71867, 72547, 75937, 76099, 77617, 79193, 79769,
      81043, 81097, 86599, 86711, 90619, 92251, 92401, 96377, 96823, 96893,
      100153, 101599, 102107, 106411, 115693, 117979, 119653, 122273, 123059, 129281,
      133379, 133417, 134947, 137131, 141241, 141499, 144451, 146513, 148949, 163997,
      165553, 188017, 188197, 193147, 216577, 217463, 234809, 244547, 246119, 277741,
      280219, 281947, 297809, 335381, 343177, 369319, 406397, 417581, 432137, 438169,
      480107, 565163, 586213, 612109, 612643, 626317, 630433, 651731, 685093, 712183,
      727021, 752789, 756641, 773867, 779101, 980137, 1032841, 1034503, 1087451, 1183157,
      1288249, 1316921, 1324361, 1339669, 1361401, 1383301, 1576723, 1834799, 2053201, 2139757,
      2155171, 2203589, 2523217, 2755463, 2811659, 2817709, 2879803, 3298811, 3321037, 3372641,
      3617069, 3617951, 3669599, 3964733, 4446433, 4471171, 4536179, 4636711, 5053693, 5537881,
      5547277, 5839291, 5986961, 6201863, 6468031, 6861697, 7083499, 7098943, 7212319, 7522901,
      7710161, 8330963, 9072359, 10545211, 12688981, 12741733, 14397319, 15308633, 18244067, 21873097,
      23601373, 24352957, 24505219, 30401537, 30978047, 32586551, 33730001, 33825601, 33926887, 40471693,
      42897313, 48575101, 50901259, 53244353, 62431921, 63017483, 63271267, 65173103, 65580481, 66052783,
      67621321, 74718443, 75879569, 79866529, 93807871, 95298881, 105518341, 132852787, 136306273, 138561641,
      142009289, 151916899, 155323757, 160962157, 168668873, 172225117, 179044939, 179415311, 185468441, 190597763,
      207911719, 246020669, 261672379, 279509459, 339268871, 383342923, 517881713, 590572933, 615806327, 744163223,
      825906901, 1169845093, 1182320609, 1506537079, 2036050361, 2191766131, 2581316131, 2624279201, 2840185781, 2898677407,
      3354113509, 4576002647, 4847190743, 4929079429, 5680371563, 6144547567, 6569011187, 6845751949, 7631124997, 8098937527,
      8260528891, 8502578369, 10776932423, 12747358969, 15376226549, 17603588341, 18826432871, 23164549021, 24219708673, 26301193573,
      28986774071, 30301253953, 32008271723, 37652865743, 50363928533, 51467697121, 58695306629, 61150311611, 65110972211, 102058480283,
      105679530977, 117390613259, 131022650417, 154783264061, 167687167009, 214805549993, 234787945631, 274952110187, 398871487529, 408716967719,
      555240796003, 581776445227, 595861556993, 797742975059, 826629447841, 1302219444221, 1596161396191, 1719798921283, 1951101465767, 2725310640323,
      3094619080181, 3478412888521, 4139134143421, 4775975935363, 7088352000427, 8559853947041, 9752308271351, 10417755553769, 13974006881147, 14359373551063,
      19103903741453, 20835511107539, 22374118403621, 33311847537949, 44748236807243, 63062515328887, 81284033392921, 150212655155791, 182731447799029, 319593384716803,
      635927379490849, 1150081090216307, 1647238560869113, 2807016441703633, 3812570706782993, 8036300276545637, 30486691755424187, 44854364709863143, 51284105359262441, 89706325036871947,
      196491150919254311, 725799727597058927, 3498950330708810221, 5778784727260815889, 14635092528104565487, 17640717292851439867, 78478332842421863213, 86560917171794057467, 206708690767055535173, 321290896024828567001,
      920314054593070719437, 1880508400376490752657, 1883836937069958237217, 2168949226838008152479, 3826786260314991211367, 4844271667741331987201, 5124623469105161024569, 5525347040369568803507, 60407435754889924251403, 128718467849545940154241,
      1493245581621988783545433, 2771892741557562936922373, 11278310349707882455928579, 80757992885189113465213993, 1387366555902446403685366447, 251341629210651754903736062193, 59737124597292648185414913209393, 183450530871106267013736211463173, 285498811742277931917137438827867, 535822240852170004076631088649327,
      542512058959614745217387126772353, 1295309273607968370700398258494227, 978421835301554251632360872955392545223, 7043093065953921339195010511780395502167, 10037566653262838460593813688652541806393, 51614441682848567194150820050144397020481, 2544456102028701855435052121524386993552097, 6591642899211909277635103388839711484157169, 12313323426068810258421045085179151336457802703, 21759099163796972141780651325712249354887750413,
      21942162254588833528538249689440133713390636446077, 6855613849526198207150406319489725644984945053774794671, 966925188529564263993895916700986439713150768980132286531, 84026314384070513234463880358495204042562939860627507203821761291, 196561891946625316608425590812136130631488792108315348157158819267, 262826251005741883539713937612151569908334640758626608520084941393, 107032548358919427693327257148782884618685660222072551941378726306878698528344822341221, 1104999373555695655228644798455003043045395612543828686530929624300378786997003359907683405568943]) : p.Prime := by
  apply lucas_graph forcedRows forced_checked p
  change p ∈ forcedPrimes
  rw [forced_names]
  exact hp

end Div245

/- Every genuine exponent pattern passes the arithmetical filters. -/
namespace Div245
open Finset

theorem witness_prime (F : ℕ) : (witness F).Prime := by
  unfold witness
  by_cases hi : witnessIndex F < witnessPool.length
  · rw [List.getD_eq_getElem witnessPool 2 hi]
    exact forced_pool_prime _ (List.getElem_mem (l:=witnessPool) hi)
  · rw [List.getD_eq_default witnessPool 2 (by omega)]
    exact Nat.prime_two

theorem true_scan (p a : ℕ) (s : List ℕ) (L : List (ℕ×ℕ)) (hp : p.Prime)
    (perm : s.Perm (L.map Prod.snd)) (nd : L.Pairwise (fun u v => u.1 < v.1))
    (hl : ∀ z ∈ L, z.1.Prime ∧ 0 < z.2 ∧ p+1 ≤ z.1 ∧ z.1.Coprime p.factorial)
    (bal : weight p a * (L.map (fun z => weight z.1 z.2)).prod =
      (p^a*((a+1)*(s.map (·+1)).prod+1))*(L.map (fun z => z.1^z.2)).prod) :
    scan (p+1) 9 s (weight p a) (p^a*((a+1)*(s.map (·+1)).prod+1)) p.factorial = true := by
  have pos : 0 < weight p a := by
    rw [weight_spec]
    change 1 ≤ _
    have h := Finset.single_le_sum (s:=range (a+1)) (f:=fun j => (j+1)*p^j)
      (fun _ _ => Nat.zero_le _) (mem_range.mpr (Nat.succ_pos _) : 0 ∈ range (a+1))
    simpa using h
  exact scan_complete weight weight_spec witness (fun _ => true) (fun F _ => witness_prime F)
    width gate gate_spec (p+1) 9 s _ _ p.factorial L perm (nd.imp (fun h => Nat.ne_of_lt h))
    hl pos (Nat.mul_pos (pow_pos hp.pos _) (Nat.succ_pos _)) bal

end Div245

/- Kernel certificates, one for each possible least prime. -/
namespace Div245

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_2 : rootCheck 2 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_3 : rootCheck 3 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_5 : rootCheck 5 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_7 : rootCheck 7 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_11 : rootCheck 11 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_13 : rootCheck 13 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_17 : rootCheck 17 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_19 : rootCheck 19 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_23 : rootCheck 23 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_29 : rootCheck 29 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_31 : rootCheck 31 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_37 : rootCheck 37 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_41 : rootCheck 41 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_43 : rootCheck 43 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_47 : rootCheck 47 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_53 : rootCheck 53 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_59 : rootCheck 59 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_61 : rootCheck 61 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_67 : rootCheck 67 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_71 : rootCheck 71 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_73 : rootCheck 73 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_79 : rootCheck 79 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_83 : rootCheck 83 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_89 : rootCheck 89 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_97 : rootCheck 97 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_101 : rootCheck 101 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_103 : rootCheck 103 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_107 : rootCheck 107 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_109 : rootCheck 109 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_113 : rootCheck 113 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_127 : rootCheck 127 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_131 : rootCheck 131 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_137 : rootCheck 137 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_139 : rootCheck 139 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_149 : rootCheck 149 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_151 : rootCheck 151 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_157 : rootCheck 157 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_163 : rootCheck 163 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_167 : rootCheck 167 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_173 : rootCheck 173 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_179 : rootCheck 179 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_181 : rootCheck 181 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_191 : rootCheck 191 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_193 : rootCheck 193 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_197 : rootCheck 197 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_199 : rootCheck 199 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_211 : rootCheck 211 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_223 : rootCheck 223 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_227 : rootCheck 227 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_229 : rootCheck 229 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_233 : rootCheck 233 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_239 : rootCheck 239 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_241 : rootCheck 241 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_251 : rootCheck 251 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_257 : rootCheck 257 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_263 : rootCheck 263 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_269 : rootCheck 269 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_271 : rootCheck 271 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_277 : rootCheck 277 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_281 : rootCheck 281 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_283 : rootCheck 283 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_293 : rootCheck 293 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_307 : rootCheck 307 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_311 : rootCheck 311 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_313 : rootCheck 313 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_317 : rootCheck 317 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_331 : rootCheck 331 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_337 : rootCheck 337 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_347 : rootCheck 347 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_349 : rootCheck 349 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_353 : rootCheck 353 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_359 : rootCheck 359 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_367 : rootCheck 367 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_373 : rootCheck 373 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_379 : rootCheck 379 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_383 : rootCheck 383 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_389 : rootCheck 389 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_397 : rootCheck 397 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_401 : rootCheck 401 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_409 : rootCheck 409 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_419 : rootCheck 419 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_421 : rootCheck 421 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_431 : rootCheck 431 = true := by decide +kernel

set_option maxRecDepth 64000 in
set_option maxHeartbeats 16000000 in
private theorem checked_433 : rootCheck 433 = true := by decide +kernel

set_option maxRecDepth 16000 in
theorem arithmetic_433 {p : ℕ} (hp : p.Prime) (bound : p≤433) : rootCheck p = true := by
  have list : (List.range 434).filter (fun r => decide r.Prime) = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433] := by decide +kernel
  have h : p ∈ (List.range 434).filter (fun r => decide r.Prime) := List.mem_filter.mpr ⟨List.mem_range.mpr (show p<434 by omega), decide_eq_true hp⟩
  rw [list] at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact checked_2
  · exact checked_3
  · exact checked_5
  · exact checked_7
  · exact checked_11
  · exact checked_13
  · exact checked_17
  · exact checked_19
  · exact checked_23
  · exact checked_29
  · exact checked_31
  · exact checked_37
  · exact checked_41
  · exact checked_43
  · exact checked_47
  · exact checked_53
  · exact checked_59
  · exact checked_61
  · exact checked_67
  · exact checked_71
  · exact checked_73
  · exact checked_79
  · exact checked_83
  · exact checked_89
  · exact checked_97
  · exact checked_101
  · exact checked_103
  · exact checked_107
  · exact checked_109
  · exact checked_113
  · exact checked_127
  · exact checked_131
  · exact checked_137
  · exact checked_139
  · exact checked_149
  · exact checked_151
  · exact checked_157
  · exact checked_163
  · exact checked_167
  · exact checked_173
  · exact checked_179
  · exact checked_181
  · exact checked_191
  · exact checked_193
  · exact checked_197
  · exact checked_199
  · exact checked_211
  · exact checked_223
  · exact checked_227
  · exact checked_229
  · exact checked_233
  · exact checked_239
  · exact checked_241
  · exact checked_251
  · exact checked_257
  · exact checked_263
  · exact checked_269
  · exact checked_271
  · exact checked_277
  · exact checked_281
  · exact checked_283
  · exact checked_293
  · exact checked_307
  · exact checked_311
  · exact checked_313
  · exact checked_317
  · exact checked_331
  · exact checked_337
  · exact checked_347
  · exact checked_349
  · exact checked_353
  · exact checked_359
  · exact checked_367
  · exact checked_373
  · exact checked_379
  · exact checked_383
  · exact checked_389
  · exact checked_397
  · exact checked_401
  · exact checked_409
  · exact checked_419
  · exact checked_421
  · exact checked_431
  · exact checked_433

end Div245

/- Completion of the finite least-prime classification. -/
namespace Div245
open Finset OeisA245211

theorem rootList_pos {p a : ℕ} {s : List ℕ} (hr : (a,s) ∈ rootList p) : 0 < a := by
  obtain ⟨i,_,h⟩ := List.mem_flatMap.mp hr
  obtain ⟨v,_,hh⟩ := List.mem_filterMap.mp h
  split at hh
  next _ => cases hh; omega
  next _ => simp at hh

theorem classify_from_tables
    (arith : ∀ p, Nat.Prime p → p ≤ 433 → rootCheck p = true)
    (sound : ∀ (p a : ℕ) (s : List ℕ) (L : List (ℕ×ℕ)), p.Prime →
      s.Perm (L.map Prod.snd) → L.Pairwise (fun u v => u.1 < v.1) →
      (∀ z ∈ L, z.1.Prime ∧ 0 < z.2 ∧ p+1 ≤ z.1 ∧ z.1.Coprime p.factorial) →
      weight p a * (L.map (fun z => weight z.1 z.2)).prod =
        (p^a*((a+1)*(s.map (·+1)).prod+1))*(L.map (fun z => z.1^z.2)).prod →
      scan (p+1) 9 s (weight p a) (p^a*((a+1)*(s.map (·+1)).prod+1)) p.factorial = true)
    {n : ℕ} (hn : 1<n) (bound : n.minFac ≤ 433) (hf : a n=n) :
    n=21 := by
  by_contra ne
  obtain ⟨e,s,L,root,perm,ord,hL,bal⟩ := roots_cover hn bound hf ne
  have hp := Nat.minFac_prime (show n≠1 by omega)
  have acc := arith n.minFac hp bound
  have ok := List.all_eq_true.mp acc (e,s) root
  have real := sound n.minFac e s L hp perm ord hL bal
  have hr : analyticRow n.minFac e s = true := by
    simpa only [real, Bool.not_true,Bool.or_false] using ok
  exact analytic_row_impossible perm ord hp (rootList_pos root)
    (fun z hz => ⟨(hL z hz).1,(hL z hz).2.2.1⟩) bal hr

end Div245

namespace Div245

/-- The unique fixed point among integers greater than one whose least prime
factor is at most 433. -/
theorem fixed_433 {n : ℕ} (hn : 1 < n) (bound : n.minFac ≤ 433)
    (hf : OeisA245211.a n = n) : n = 21 :=
  classify_from_tables (fun _ hp hb => arithmetic_433 hp hb) true_scan hn bound hf

theorem fixed_433_iff {n : ℕ} (hn : 1 < n) (bound : n.minFac ≤ 433) :
    OeisA245211.a n = n ↔ n = 21 := by
  refine ⟨fixed_433 hn bound,?_⟩
  rintro rfl
  decide +kernel

end Div245

theorem OMA.solution : OMA.R_OeisA245211_conjecture_R3.H1 := by
  intro n hn bound _ _ _ _ hf
  exact Div245.fixed_433 hn bound hf
