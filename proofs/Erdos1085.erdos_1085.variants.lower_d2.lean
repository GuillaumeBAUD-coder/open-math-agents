import FormalConjectures.ErdosProblems.«1085»
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Data.Nat.Choose.Factorization

/-! # Erdős's planar lattice construction for the unit-distance lower bound

We count distinct small prime divisors of integers of the form i²+1 and select conjugate
Gaussian factors independently. Translating the resulting equal-length vectors within a
square grid gives the lower bound for every sufficiently large point count. Credit: @JaviSoto. -/
/- # A polynomial supply of split primes from a short interval of quadratic values -/

namespace OMA.PrimeSupply1085
open Finset

private abbrev arg (X i : ℕ) := 2*(X+i)
private abbrev norm (X i : ℕ) := (arg X i)^2+1

private theorem root_mod {X i p e : ℕ} (he : 0 < e) (h : p^e ∣ norm X i) :
    (arg X i : ZMod p)^2 = -1 := by
  have hdiv : p ∣ norm X i := (dvd_pow_self p he.ne').trans h
  have eq := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  simpa only [norm, Nat.cast_add, Nat.cast_pow, Nat.cast_one, add_eq_zero_iff_eq_neg] using eq

/-- Two roots of the same sign modulo p are congruent modulo the
whole prime power. The other factor in the difference of squares is
nonzero modulo the odd prime p. -/
private theorem same_root {X p e i j : ℕ} (hp : p.Prime) (hn : p ≠ 2) (he : 0 < e)
    (hi : p^e ∣ norm X i) (hj : p^e ∣ norm X j)
    (hs : (arg X i : ZMod p) = arg X j) : i % p^e = j % p^e := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hp2 : (2 : ZMod p) ≠ 0 := by
    change ((2 : ℕ) : ZMod p) ≠ 0
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact fun h => hn ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one)
  have hr := root_mod he hi
  have hnr : (arg X i : ZMod p) ≠ 0 := by
    intro h; simp [h] at hr
  have hc : ¬ (p : ℤ) ∣ 2*((arg X i : ℤ) + (arg X j : ℤ)) := by
    intro h
    have eq := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_add, Int.cast_natCast] at eq
    rw [← hs, ← two_mul] at eq
    exact (mul_ne_zero hp2 (mul_ne_zero hp2 hnr)) eq
  have hdi : (p:ℤ)^e ∣ (norm X i : ℤ) := by exact_mod_cast hi
  have hdj : (p:ℤ)^e ∣ (norm X j : ℤ) := by exact_mod_cast hj
  have hd : (p:ℤ)^e ∣ ((j:ℤ)-i)*(2*((arg X i:ℤ)+(arg X j:ℤ))) := by
    rw [show ((j:ℤ)-i)*(2*((arg X i:ℤ)+(arg X j:ℤ))) =
      (norm X j:ℤ)-(norm X i:ℤ) by simp only [norm,arg]; push_cast; ring]
    exact dvd_sub hdj hdi
  have diff := (Nat.prime_iff_prime_int.mp hp).pow_dvd_of_dvd_mul_right e hc hd
  have hmod := (ZMod.intCast_eq_intCast_iff_dvd_sub (i:ℤ) (j:ℤ) (p^e)).mpr
    (by exact_mod_cast diff)
  exact (ZMod.natCast_eq_natCast_iff' i j (p^e)).mp (by simpa using hmod)

private theorem root_count (X L p e : ℕ) (hp : p.Prime) (hn : p ≠ 2) (he : 0 < e) :
    ((range L).filter (fun i => p^e ∣ norm X i)).card ≤ 2*(L/(p^e)+1) := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let A := (range L).filter (fun i => p^e ∣ norm X i)
  change A.card ≤ _
  by_cases hempty : A.Nonempty
  · obtain ⟨j,hj⟩ := hempty
    let z := (arg X j : ZMod p)
    let S : Finset (ZMod p) := {z,-z}
    let f (i : ℕ) := (i/(p^e), (arg X i : ZMod p))
    have hjroot := root_mod he (mem_filter.mp hj).2
    have hmem (i : ℕ) (hi : i ∈ A) : f i ∈ (range (L/(p^e)+1)).product S := by
      have hmod := root_mod he (mem_filter.mp hi).2
      obtain h|h := sq_eq_sq_iff_eq_or_eq_neg.mp (hmod.trans hjroot.symm)
      all_goals
        refine mem_product.mpr ⟨mem_range.mpr ?_,?_⟩
        · exact Nat.lt_succ_of_le (Nat.div_le_div_right (mem_range.mp (mem_filter.mp hi).1).le)
        · simpa [f,S,z] using (show (arg X i : ZMod p) = arg X j ∨
              (arg X i : ZMod p) = - (arg X j : ZMod p) from by tauto)
    have hc := card_le_card_of_injOn f hmem (by
      intro i hi i' hi' eq
      have heq : i/(p^e) = i'/(p^e) := congrArg Prod.fst eq
      have hcong := same_root hp hn he (mem_filter.mp hi).2 (mem_filter.mp hi').2
        (congrArg Prod.snd eq)
      have h1 := Nat.mod_add_div i (p^e)
      have h2 := Nat.mod_add_div i' (p^e)
      rw [hcong,heq] at h1
      omega)
    have hs : S.card ≤ 2 := card_le_two
    have hc' : A.card ≤ (range (L/p^e+1)).card*S.card :=
      hc.trans_eq (Finset.card_product _ _)
    rw [card_range] at hc'
    simpa [mul_comm] using hc'.trans (Nat.mul_le_mul_left _ hs)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hempty]

private theorem val_product (X L M p : ℕ) (hp : p.Prime) (hn : p ≠ 2) (hLM : L ≤ M)
    (hb : ∀ i ∈ range L, norm X i ≤ M) :
    (∏ i ∈ range L, norm X i).factorization p ≤ 2*L.factorial.factorization p + 2*Nat.log p M := by
  classical
  let E := Ico 1 (Nat.log p M+1)
  have heq (i : ℕ) (hi : i ∈ range L) :
      (norm X i).factorization p = (E.filter (fun e => p^e ∣ norm X i)).card :=
    Nat.factorization_eq_card_pow_dvd_of_lt hp (Nat.zero_lt_succ _)
      ((hb _ hi).trans_lt (Nat.lt_pow_succ_log_self hp.one_lt _))
  have hsum : (∑ i ∈ range L, (norm X i).factorization p) =
      ∑ e ∈ E, ((range L).filter (fun i => p^e ∣ norm X i)).card := by
    calc
      _ = ∑ i ∈ range L, (E.filter (fun e => p^e ∣ norm X i)).card := sum_congr rfl heq
      _ = _ := by simp only [Finset.card_filter]; rw [sum_comm]
  rw [Nat.factorization_prod (fun _ _ => Nat.succ_ne_zero _), Finsupp.finsetSum_apply, hsum]
  have hfac : L.factorial.factorization p = ∑ e ∈ E, L/p^e :=
    Nat.factorization_factorial hp (lt_of_le_of_lt (Nat.log_mono_right hLM) (Nat.lt_succ_self _))
  calc
    _ ≤ ∑ e ∈ E, 2*(L/p^e+1) := sum_le_sum (fun e h => root_count _ _ _ _ hp hn (mem_Ico.mp h).1)
    _ = _ := by simp [mul_add,sum_add_distrib,← mul_sum,← hfac,E,Nat.card_Ico,mul_comm (Nat.log p M) 2]

private theorem part_prod_le (S : Finset ℕ) (n : ℕ) (hn : n ≠ 0) :
    ∏ p ∈ S, p^n.factorization p ≤ n := by
  classical
  let T := S ∩ n.primeFactors
  have h : ∏ p ∈ T, p^n.factorization p = ∏ p ∈ S, p^n.factorization p := by
    apply prod_subset inter_subset_left
    intro p hp hpt
    have hpn : p ∉ n.primeFactors := fun h => hpt (mem_inter.mpr ⟨hp,h⟩)
    have hz : n.factorization p = 0 := Finsupp.notMem_support_iff.mp
      (show p ∉ n.factorization.support by simpa using hpn)
    simp [hz]
  rw [← h]
  refine (Finset.prod_le_prod_of_subset_of_one_le' (show T ⊆ n.primeFactors from inter_subset_right)
    (fun p hp _ => Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors hp).pos)).trans_eq
    (Nat.prod_primeFactors_pow_factorization hn).symm

private theorem factor_exists {X L p : ℕ} (hp : p.Prime) (h : p ∣ ∏ i ∈ range L, norm X i) :
    ∃ i ∈ range L, p ∣ norm X i :=
  (hp.prime.dvd_finsetProd_iff _).mp h

private theorem number_bound (X L M : ℕ) (hLM : L ≤ M) (hM : M ≠ 0)
    (hb : ∀ i ∈ range L, norm X i ≤ M) :
    let W := ∏ i ∈ range L, norm X i
    W ≤ L.factorial ^ 2 * M ^ (2*W.primeFactors.card) := by
  classical
  let W := ∏ i ∈ range L, norm X i
  have hW : W ≠ 0 := prod_ne_zero_iff.mpr (fun _ _ => Nat.succ_ne_zero _)
  have wp (p : ℕ) (hpp : p ∈ W.primeFactors) :
      p^W.factorization p ≤ (p^L.factorial.factorization p)^2*M^2 := by
    have hp := Nat.prime_of_mem_primeFactors hpp
    have hn : p ≠ 2 := by
      rintro rfl
      obtain ⟨i,_,hd⟩ := factor_exists hp (Nat.dvd_of_mem_primeFactors hpp)
      have hv : norm X i % 2 = 1 := by simp [norm,arg,Nat.add_mod,Nat.pow_mod]
      have := Nat.mod_eq_zero_of_dvd hd
      omega
    have hval := val_product X L M p hp hn hLM hb
    calc
      _ ≤ p^(2*L.factorial.factorization p+2*Nat.log p M) :=
        Nat.pow_le_pow_right hp.pos hval
      _ = (p^L.factorial.factorization p)^2*(p^Nat.log p M)^2 := by
        rw [pow_add, ← pow_mul, ← pow_mul, mul_comm 2 (L.factorial.factorization p),
          mul_comm 2 (Nat.log p M)]
      _ ≤ _ := by gcongr; exact Nat.pow_log_le_self _ hM
  change W ≤ _
  calc
    W = ∏ p ∈ W.primeFactors, p^W.factorization p := Nat.prod_primeFactors_pow_factorization hW
    _ ≤ ∏ p ∈ W.primeFactors, ((p^L.factorial.factorization p)^2*M^2) := Finset.prod_le_prod' wp
    _ = (∏ p ∈ W.primeFactors, p^L.factorial.factorization p)^2 * M^(2*W.primeFactors.card) := by
      rw [prod_mul_distrib,prod_pow,prod_const,pow_mul]
    _ ≤ _ := by gcongr; exact part_prod_le _ _ L.factorial_ne_zero

/-- At least k different split primes occur among the quadratic values
at 8k consecutive even inputs near 2k⁴. -/
theorem prime_supply (k : ℕ) (hk : 8 ≤ k) : ∃ S : Finset ℕ, S.card = k ∧
    ∀ p ∈ S, p.Prime ∧ p % 4 = 1 ∧ p ≤ k^10 ∧ ∃ i ≤ k^5, p ∣ i^2+1 := by
  classical
  let X := k^4
  let L := 8*k
  let M := k^10
  let W := ∏ i ∈ range L, norm X i
  have hkpos : 0 < k := by omega
  have hW : W ≠ 0 := prod_ne_zero_iff.mpr (fun _ _ => Nat.succ_ne_zero _)
  have hLk : L ≤ k^2 := by
    calc L ≤ k*k := Nat.mul_le_mul_right k hk
         _ = _ := by ring
  have hLX : L ≤ X := hLk.trans (Nat.pow_le_pow_right hkpos (by decide : 2 ≤ 4))
  have hLM : L ≤ M := hLk.trans (Nat.pow_le_pow_right hkpos (by decide : 2 ≤ 10))
  have hu (i : ℕ) (hi : i ∈ range L) : arg X i < k^5 := by
    have hi' := mem_range.mp hi
    calc arg X i < 4*X := by dsimp [arg]; omega
         _ ≤ k*X := Nat.mul_le_mul_right _ (by omega)
         _ = _ := by dsimp [X]; ring
  have hbounds (i : ℕ) (hi : i ∈ range L) : norm X i ≤ M := by
    have hsq := Nat.pow_lt_pow_left (hu i hi) (by decide : 2≠0)
    change (arg X i)^2+1 ≤ k^10
    calc _ ≤ (k^5)^2 := hsq
         _ = _ := by ring
  have hLpow : L.factorial ≤ k^(2*L) := by
    calc L.factorial ≤ L^L := Nat.factorial_le_pow _
         _ ≤ (k^2)^L := Nat.pow_le_pow_left hLk _
         _ = _ := (pow_mul _ _ _).symm
  have hlow : k^(8*L) ≤ W := by
    calc k^(8*L) = ∏ i ∈ range L, k^8 := by simp [pow_mul]
         _ ≤ W := by
           apply Finset.prod_le_prod'
           intro i _
           change k^8 ≤ (2*(k^4+i))^2+1
           nlinarith [Nat.zero_le (k^4*i), Nat.zero_le (i^2)]
  have hcount : k ≤ W.primeFactors.card := by
    by_contra! h
    have hbound := number_bound X L M hLM (pow_ne_zero _ hkpos.ne') hbounds
    change W ≤ L.factorial^2 * M^(2*W.primeFactors.card) at hbound
    have high : W ≤ k^(4*L+20*k) := by
      calc W ≤ _ := hbound
           _ ≤ (k^(2*L))^2*(k^10)^(2*k) := by
             apply Nat.mul_le_mul (Nat.pow_le_pow_left hLpow 2)
             exact Nat.pow_le_pow_right (pow_pos hkpos _) (by omega)
           _ = _ := by rw [← pow_mul,← pow_mul,← pow_add]; congr 1; ring
    exact (Nat.pow_lt_pow_right (show 1<k by omega)
      (show 4*L+20*k < 8*L by dsimp [L]; omega)).not_ge (hlow.trans high)
  obtain ⟨S,hS,hcard⟩ := exists_subset_card_eq hcount
  refine ⟨S,hcard,?_⟩
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors (hS hp)
  obtain ⟨i,hi,hdiv⟩ := factor_exists hpp (Nat.dvd_of_mem_primeFactors (hS hp))
  have hn : p ≠ 2 := by
    rintro rfl
    have h := Nat.mod_eq_zero_of_dvd hdiv
    simp [norm,arg,Nat.add_mod,Nat.pow_mod] at h
  have h4 : p % 4 = 1 := by
    let _ : Fact p.Prime := ⟨hpp⟩
    have he := @ZMod.mod_four_ne_three_of_sq_eq_neg_one p _ _ (root_mod (e:=1) (by decide)
      (by simpa using hdiv))
    have hodd := hpp.mod_two_eq_one_iff_ne_two.mpr hn
    omega
  exact ⟨hpp,h4,(Nat.le_of_dvd (Nat.zero_lt_succ _) hdiv).trans (hbounds i hi),
    arg X i,(hu i hi).le,hdiv⟩

end OMA.PrimeSupply1085

/- Products of primes congruent to one modulo four have many representations
as sums of two squares, by independent choices of conjugate Gaussian factors. -/

namespace OMA.Gaussian1085

/-- Gaussian multiplication by `a + bi`, in integer coordinates. -/
private def gm (a b : ℤ) (u : ℤ × ℤ) : ℤ × ℤ :=
  (a*u.1 - b*u.2, b*u.1 + a*u.2)

private theorem gm_norm (a b : ℤ) (u : ℤ × ℤ) :
    (gm a b u).1 ^ 2 + (gm a b u).2 ^ 2 =
      (a ^ 2 + b ^ 2) * (u.1 ^ 2 + u.2 ^ 2) := by
  unfold gm
  ring

private theorem gm_injective (a b : ℤ) (h : a ^ 2 + b ^ 2 ≠ 0) :
    Function.Injective (gm a b) := by
  rintro ⟨x,y⟩ ⟨u,v⟩ he
  have h₀ : a*x-b*y = a*u-b*v := congrArg Prod.fst he
  have h₁ : b*x+a*y = b*u+a*v := congrArg Prod.snd he
  have hx : (a^2+b^2)*(x-u) = 0 := by linear_combination a*h₀ + b*h₁
  have hy : (a^2+b^2)*(y-v) = 0 := by linear_combination -b*h₀ + a*h₁
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left h))
    (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left h))

/-- If the two conjugate products agree, their common prime norm divides the
imaginary part of the squared factor times the old norm. -/
private theorem incompatible {a b p N : ℕ} {v w : ℤ × ℤ}
    (hab : a^2+b^2=p) (hN : v.1^2+v.2^2=(N : ℤ)) (h : ¬p ∣ 2*a*b*N) :
    gm a b v ≠ gm a (-(b:ℤ)) w := by
  obtain ⟨x,y⟩ := v
  obtain ⟨u,v⟩ := w
  intro he
  have h₀ : (a:ℤ)*x-b*y = a*u-(-b)*v := congrArg Prod.fst he
  have h₁ : (b:ℤ)*x+a*y = (-b)*u+a*v := congrArg Prod.snd he
  have hu : ((a:ℤ)^2+b^2)*u = (a^2-b^2)*x - 2*a*b*y := by
    linear_combination -(a:ℤ)*h₀ + (b:ℤ)*h₁
  have hv : ((a:ℤ)^2+b^2)*v = 2*a*b*x+(a^2-b^2)*y := by
    linear_combination -(b:ℤ)*h₀ - (a:ℤ)*h₁
  have hh : 2*(a:ℤ)*b*(x^2+y^2)=((a:ℤ)^2+b^2)*(v*x-u*y) := by
    linear_combination y*hu-x*hv
  have hpi : (a:ℤ)^2+b^2=p := by exact_mod_cast hab
  change x^2+y^2=(N:ℤ) at hN
  rw [hN,hpi] at hh
  have hd : (p:ℤ) ∣ 2*(a:ℤ)*b*N := ⟨_,hh⟩
  exact h (by exact_mod_cast hd)

theorem many_vectors (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p % 4 = 1) :
    ∃ D : Finset (ℤ × ℤ), 2 ^ S.card ≤ D.card ∧
      ∀ x ∈ D, x.1 ^ 2 + x.2 ^ 2 = ((∏ p ∈ S, p : ℕ) : ℤ) := by
  classical
  induction S using Finset.induction with
  | empty =>
    refine ⟨{(1,0)}, by simp, ?_⟩
    simp
  | @insert p S hpS ih =>
    obtain ⟨hp,hm⟩ := hS p (Finset.mem_insert_self ..)
    have hS' : ∀ q ∈ S, q.Prime ∧ q % 4 = 1 := fun q hq =>
      hS q (Finset.mem_insert_of_mem hq)
    obtain ⟨D,hcard,hnorm⟩ := ih hS'
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨a,b,hab⟩ := Nat.Prime.sq_add_sq (p:=p) (by omega)
    have ha : a ≠ 0 := by
      rintro rfl
      exact hp.prime.not_isSquare ⟨b, by simpa [pow_two] using hab.symm⟩
    have hb : b ≠ 0 := by
      rintro rfl
      exact hp.prime.not_isSquare ⟨a, by simpa [pow_two] using hab.symm⟩
    have ha' : a < p := by
      nlinarith [Nat.one_le_iff_ne_zero.mpr hb, Nat.le_self_pow (by decide : 2 ≠ 0) a]
    have hb' : b < p := by
      nlinarith [Nat.one_le_iff_ne_zero.mpr ha, Nat.le_self_pow (by decide : 2 ≠ 0) b]
    have hN : ¬ p ∣ ∏ q ∈ S, q := by
      intro hd
      obtain ⟨q,hq,hpq⟩ := (hp.prime.dvd_finsetProd_iff id).mp hd
      exact hpS ((Nat.prime_dvd_prime_iff_eq hp (hS' q hq).1).mp hpq ▸ hq)
    have hnodiv : ¬ p ∣ 2*a*b*(∏ q ∈ S, q) := by
      simp only [Nat.Prime.dvd_mul hp, not_or]
      exact ⟨⟨⟨fun h => by have := Nat.le_of_dvd (by decide : 0<2) h; omega,
        fun h => (Nat.not_le.mpr ha') (Nat.le_of_dvd (Nat.pos_of_ne_zero ha) h)⟩,
        fun h => (Nat.not_le.mpr hb') (Nat.le_of_dvd (Nat.pos_of_ne_zero hb) h)⟩,hN⟩
    have hnormab : (a:ℤ)^2+b^2=p := by exact_mod_cast hab
    have hp0 : (p:ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hinj₁ := gm_injective (a:ℤ) b (hnormab ▸ hp0)
    have hinj₂ := gm_injective (a:ℤ) (-b) (by simpa [hnormab] using hp0)
    have hd : Disjoint (D.image (gm a b)) (D.image (gm a (-b))) := by
      rw [Finset.disjoint_left]
      intro z hz hz'
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨y,_,hy⟩ := Finset.mem_image.mp hz'
      exact incompatible hab (hnorm x hx) hnodiv hy.symm
    refine ⟨D.image (gm a b) ∪ D.image (gm a (-b)), ?_,?_⟩
    · rw [Finset.card_union_of_disjoint hd,Finset.card_image_of_injective _ hinj₁,
        Finset.card_image_of_injective _ hinj₂,Finset.card_insert_of_notMem hpS,pow_succ]
      omega
    · intro x hx
      rw [Finset.prod_insert hpS,Nat.cast_mul]
      rcases Finset.mem_union.mp hx with hx | hx <;>
        obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx <;>
        simp [gm_norm,hnormab,hnorm y hy]

end OMA.Gaussian1085

/- Translating equal-norm lattice vectors inside a square produces many unit distances. -/

namespace OMA.UnitGrid1085

open Finset
open scoped EuclideanGeometry Classical

private noncomputable def pt (t : ℝ) (z : ℤ × ℤ) : ℝ² :=
  !₂[(z.1 : ℝ) / t, (z.2 : ℝ) / t]

private theorem pt_inj {t : ℝ} (ht : t ≠ 0) : Function.Injective (pt t) := by
  intro a b he
  have h₁ := congrArg (fun z : ℝ² => z 0) he
  have h₂ := congrArg (fun z : ℝ² => z 1) he
  apply Prod.ext
  · have : (a.1 : ℝ)/t = (b.1 : ℝ)/t := by simpa [pt] using h₁
    exact_mod_cast (div_left_inj' ht).mp this
  · have : (a.2 : ℝ)/t = (b.2 : ℝ)/t := by simpa [pt] using h₂
    exact_mod_cast (div_left_inj' ht).mp this

private theorem translated_dist {M : ℕ} (hM : 0 < M) (p d : ℤ × ℤ)
    (hn : d.1^2 + d.2^2 = (M : ℤ)) :
    dist (pt (Real.sqrt M) p) (pt (Real.sqrt M) (p+d)) = 1 := by
  have hr : (0 : ℝ) < Real.sqrt M := by positivity
  have hsum : (d.1 : ℝ)^2 + (d.2 : ℝ)^2 = M := by exact_mod_cast hn
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  apply (Real.sqrt_eq_iff_eq_sq (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num)).mpr
  simp [pt, add_div]
  field_simp [hr.ne']
  simpa [sq_abs, Real.sq_sqrt (show (0 : ℝ) ≤ M by positivity)] using hsum

private theorem le_extremal (Q : Finset ℝ²) (n : ℕ) (hQ : Q.card = n) :
    unitDistNum Q ≤ Erdos1085.f 2 n := by
  unfold Erdos1085.f
  refine le_ciSup₂ (f := fun (T : Finset ℝ²) (_ : T.card = n) => unitDistNum T) ?_ Q hQ
  refine ⟨n.choose 2, ?_⟩
  intro k hk
  rcases Set.mem_iUnion.mp hk with ⟨T,h⟩
  obtain ⟨hc,rfl⟩ := Set.mem_range.mp h
  simpa only [hc] using unitDistNum_le_choose_two T

/-- The available grid uses at most 9m² points. Each of its m² starting sites can
be translated along each supplied vector; only the two orientations can coincide. -/
theorem grid (D : Finset (ℤ × ℤ)) (M m n : ℕ) (hM : 0 < M) (hm : M ≤ m^2)
    (space : 9*m^2 ≤ n) (norm : ∀ d ∈ D, d.1^2 + d.2^2 = (M : ℤ)) :
    m^2 * D.card ≤ 2 * Erdos1085.f 2 n := by
  classical
  let t : ℝ := Real.sqrt M
  have ht : t ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hM)).ne'
  let B : Finset ℤ := Ico 0 (m : ℤ)
  let K : Finset ℤ := Ico (-(m : ℤ)) (2*m)
  let Q₀ := (K ×ˢ K).image (pt t)
  have kc : K.card = 3*m := by simp [K, Int.card_Ico]; omega
  have bc : B.card = m := by simp [B, Int.card_Ico]
  have budget : Q₀.card ≤ n := by
    have h : Q₀.card ≤ K.card*K.card := card_image_le.trans_eq (card_product K K)
    rw [kc] at h
    nlinarith
  obtain ⟨Q,sub,hQ⟩ := Infinite.exists_superset_card_eq Q₀ n budget
  let U := Q.sym2.filter fun e => dist e.out.1 e.out.2 = 1
  let ordered (e : Sym2 ℝ²) : Finset (ℝ² × ℝ²) := {e.out,e.out.swap}
  have lift {a b : ℝ²} (ha : a ∈ Q) (hb : b ∈ Q) (h : dist a b = 1) :
      (a,b) ∈ U.biUnion ordered := by
    let e := Sym2.mk a b
    have he : Sym2.mk e.out.1 e.out.2 = Sym2.mk a b := e.out_eq
    have cases := Sym2.eq_iff.mp he
    apply mem_biUnion.mpr
    refine ⟨e,mem_filter.mpr ⟨mk_mem_sym2_iff.mpr ⟨ha,hb⟩,?_⟩,?_⟩
    · rcases cases with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;> simp_all [dist_comm]
    · rcases cases with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · exact mem_insert_self _ _ |> (fun H => (show e.out = (a,b) from Prod.ext h₁ h₂) ▸ H)
      · exact mem_insert_of_mem (mem_singleton.mpr (Prod.ext h₂.symm h₁.symm))
  let enc (pd : (ℤ × ℤ) × (ℤ × ℤ)) := (pt t pd.1, pt t (pd.1 + pd.2))
  have enc_inj : Function.Injective enc := by
    rintro ⟨p,d⟩ ⟨q,e⟩ he
    have h₁ : p = q := pt_inj ht (congrArg Prod.fst he)
    have h₂ : p+d = q+e := pt_inj ht (congrArg Prod.snd he)
    subst q
    exact Prod.ext rfl (add_left_cancel h₂)
  have send : ∀ pd ∈ (B ×ˢ B) ×ˢ D, enc pd ∈ U.biUnion ordered := by
    rintro ⟨p,d⟩ hpd
    obtain ⟨hp,hd⟩ := mem_product.mp hpd
    obtain ⟨hx,hy⟩ := mem_product.mp hp
    have hx' : 0 ≤ p.1 ∧ p.1 < (m : ℤ) := mem_Ico.mp hx
    have hy' : 0 ≤ p.2 ∧ p.2 < (m : ℤ) := mem_Ico.mp hy
    have hn := norm d hd
    have mm : (M : ℤ) ≤ (m : ℤ)^2 := by exact_mod_cast hm
    have extents (x y : ℤ) (hs : x^2+y^2 = M) : -(m : ℤ) ≤ x ∧ x ≤ m := by
      constructor
      · by_contra! bad
        nlinarith [sq_nonneg y, mul_pos (by omega : 0 < -(m:ℤ)-x) (by omega : 0 < (m:ℤ)-x)]
      · by_contra! bad
        nlinarith [sq_nonneg y, mul_pos (by omega : 0 < x-(m:ℤ)) (by omega : 0 < x+(m:ℤ))]
    have dx := extents d.1 d.2 hn
    have dy := extents d.2 d.1 (by rwa [add_comm])
    apply lift
    · apply sub (mem_image.mpr ⟨p,mem_product.mpr ⟨mem_Ico.mpr (by omega),mem_Ico.mpr (by omega)⟩,rfl⟩)
    · apply sub (mem_image.mpr ⟨p+d,mem_product.mpr ⟨mem_Ico.mpr ?_,mem_Ico.mpr ?_⟩,rfl⟩)
      · change -(m:ℤ) ≤ p.1+d.1 ∧ p.1+d.1 < 2*m
        omega
      · change -(m:ℤ) ≤ p.2+d.2 ∧ p.2+d.2 < 2*m
        omega
    · exact translated_dist hM p d hn
  have lower := card_le_card_of_injOn enc send enc_inj.injOn
  simp only [card_product,bc] at lower
  have upper : (U.biUnion ordered).card ≤ U.card*2 := calc
    _ ≤ ∑ e ∈ U, (ordered e).card := card_biUnion_le
    _ ≤ ∑ _e ∈ U, 2 := sum_le_sum (fun e _ => card_le_two)
    _ = _ := by simp
  change (U.biUnion ordered).card ≤ (unitDistNum Q)*2 at upper
  nlinarith only [lower,upper,le_extremal Q n hQ]

end OMA.UnitGrid1085

/- Turning the finite lattice bound into the lower exponent in dimension two. -/
namespace OMA.UnitGrid1085

open Real Filter
open scoped Topology

private lemma grid_side (n : ℕ) (hn : 256 ≤ n) :
    let m := n.sqrt / 3
    9*m^2 ≤ n ∧ n ≤ 36*m^2 ∧ n.sqrt ≤ m^2 := by
  let m := n.sqrt/3
  have hroot : 16 ≤ n.sqrt := Nat.le_sqrt.mpr hn
  have hlo : 3*m ≤ n.sqrt := by dsimp [m]; omega
  have hhi : n.sqrt+1 ≤ 3*m+3 := by dsimp [m]; omega
  have hm : 5 ≤ m := by dsimp [m]; omega
  refine ⟨?_,?_,?_⟩
  · calc 9*m^2 = (3*m)^2 := by ring
         _ ≤ n.sqrt^2 := Nat.pow_le_pow_left hlo _
         _ ≤ n := Nat.sqrt_le' _
  · calc n ≤ (n.sqrt+1)^2 := (Nat.lt_succ_sqrt' _).le
         _ ≤ (3*m+3)^2 := Nat.pow_le_pow_left hhi _
         _ ≤ 36*m^2 := by nlinarith
  · change n.sqrt ≤ m^2
    nlinarith [Nat.mul_le_mul_right m hm]

theorem lower_of_grid
    (grid : ∀ k : ℕ, 8 ≤ k → ∀ m n : ℕ, k^(10*k) ≤ m^2 → 9*m^2 ≤ n →
      m^2 * 2^k ≤ 2*Erdos1085.f 2 n) :
    type_of% @Erdos1085.erdos_1085.variants.lower_d2 := by
  refine ⟨log 2 / 160, by positivity, ?_⟩
  have htop : Tendsto (fun n : ℕ => log (n:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht := htop.eventually (Real.isLittleO_log_id_atTop.bound
    (by norm_num : (0:ℝ) < 1/1000))
  filter_upwards [eventually_ge_atTop 256, (tendsto_log_atTop.comp htop).eventually_ge_atTop 1,
    htop.eventually_ge_atTop 1, ht] with n hn hLL hL hsmall
  let L := log (n:ℝ)
  let H := log L
  change 1 ≤ H at hLL
  change 1 ≤ L at hL
  change ‖H‖ ≤ (1/1000:ℝ) * ‖L‖ at hsmall
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ H),
    abs_of_nonneg (by linarith : 0 ≤ L)] at hsmall
  have hH : 0 < H := by linarith
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  let k : ℕ := ⌊L/(40*H)⌋₊
  have hden : 0 < 40*H := by positivity
  have hk : 16 ≤ k := by
    apply Nat.le_floor
    apply (le_div_iff₀ hden).mpr
    norm_num
    linarith
  have hkpos : 0 < (k:ℝ) := by exact_mod_cast (by omega : 0<k)
  have hku : (k:ℝ)*(40*H) ≤ L :=
    (le_div_iff₀ hden).mp (Nat.floor_le (div_nonneg (by linarith : 0≤L) hden.le))
  have hkl : L < ((k:ℝ)+1)*(40*H) :=
    (div_lt_iff₀ hden).mp (Nat.lt_floor_add_one _)
  have hkL : (k:ℝ) ≤ L := by nlinarith
  have hlog : log (k:ℝ) ≤ H := log_le_log hkpos hkL
  have hp : (k^(10*k))^2 ≤ n := by
    have h' : (((k:ℝ)^(10*k))^2) ≤ (n:ℝ) := by
      apply (log_le_log_iff (by positivity) hnpos).mp
      rw [log_pow,log_pow]
      change (2:ℝ)*((↑(10*k):ℝ)*log (k:ℝ)) ≤ L
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hlog hkpos.le]
    exact_mod_cast h'
  have hnear := Nat.le_sqrt.mpr (by simpa [pow_two] using hp)
  obtain ⟨hspace, hnside, hside⟩ := grid_side n hn
  let m := n.sqrt/3
  have count := grid k (by omega) m n (hnear.trans hside) hspace
  have hpower : (n:ℝ) ^ (log 2 / 160 / H) < (2:ℝ)^(k-7) := by
    rw [rpow_def_of_pos hnpos]
    conv_rhs => rw [← Real.exp_log (by norm_num : (0:ℝ)<2), ← Real.exp_nat_mul]
    apply exp_lt_exp.mpr
    change L * (log 2 / 160 / H) < _
    rw [Nat.cast_sub (by omega : 7 ≤ k)]
    push_cast
    have hlog2 : 0 < log 2 := log_pos (by norm_num)
    have hh : L / H < 160 * ((k:ℝ)-7) := by
      apply (div_lt_iff₀ hH).mpr
      have hkr : (16:ℝ) ≤ k := by exact_mod_cast hk
      nlinarith [mul_le_mul_of_nonneg_right hkr hH.le]
    calc L * (log 2 / 160 / H) = (L / H) * (log 2/160) := by ring
         _ < (160 * ((k:ℝ)-7)) * (log 2/160) := by gcongr
         _ = _ := by ring
  have hsplit : (2:ℝ)^k = (2:ℝ)^(k-7)*128 := by
    calc (2:ℝ)^k = (2:ℝ)^((k-7)+7) := by rw [Nat.sub_add_cancel (by omega : 7≤k)]
         _ = _ := by rw [pow_add]; norm_num
  have hc : (m:ℝ)^2*(2:ℝ)^k ≤ 2*(Erdos1085.f 2 n : ℝ) := by exact_mod_cast count
  have hns : (n:ℝ) ≤ 36*(m:ℝ)^2 := by exact_mod_cast hnside
  change (n:ℝ) ^ (1 + log 2/160/H) < _
  rw [rpow_add hnpos,rpow_one]
  have h₁ := mul_lt_mul_of_pos_left hpower hnpos
  have h₂ := mul_le_mul_of_nonneg_right hns (by positivity : 0 ≤ (2:ℝ)^(k-7))
  rw [hsplit] at hc
  nlinarith

end OMA.UnitGrid1085

theorem OMA.solution : type_of% @Erdos1085.erdos_1085.variants.lower_d2 := by
  apply OMA.UnitGrid1085.lower_of_grid
  intro k hk m n fits space
  obtain ⟨S,size,primes⟩ := OMA.PrimeSupply1085.prime_supply k hk
  obtain ⟨D,hd,hn⟩ := OMA.Gaussian1085.many_vectors S (fun p hp =>
    ⟨(primes p hp).1,(primes p hp).2.1⟩)
  let M := ∏ p ∈ S, p
  have hM : 0 < M := Finset.prod_pos (fun p hp => (primes p hp).1.pos)
  have hsize : M ≤ k^(10*k) := calc
    M ≤ ∏ _p ∈ S, k^10 := Finset.prod_le_prod' (fun p hp => (primes p hp).2.2.1)
    _ = k^(10*k) := by simp [size,← pow_mul]
  rw [size] at hd
  exact (Nat.mul_le_mul_left _ hd).trans (OMA.UnitGrid1085.grid D M m n hM (hsize.trans fits) space hn)
