import OMAReductions.R_Erdos964_erdos_964_variants_eberhard_R1
import Mathlib

/-! Eberhard’s explicit coefficient construction for a prescribed divisor ratio.
Credit: @marcusbuffett. Mathematical source: arXiv:2505.00727. -/

namespace Explicit964

private def τ (n : ℕ) := n.divisors.card

private theorem tau_mul {a b : ℕ} (h : a.Coprime b) : τ (a*b) = τ a * τ b :=
  h.card_divisors_mul

private theorem tau_pow {p : ℕ} (hp : p.Prime) (n : ℕ) : τ (p^n) = n+1 := by
  simp [τ, Nat.divisors_prime_pow hp]

private theorem cop_small {p n d : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hd : ¬ p ∣ d) :
    p.Coprime (n+d) := hp.coprime_iff_not_dvd.mpr (fun h => hd ((Nat.dvd_add_right hpn).mp h))

private theorem cop35 (i j : ℕ) : (3^i).Coprime (5^j) :=
  (show Nat.Coprime 3 5 by decide).pow_left i |>.pow_right j

private theorem tau235 (h i j : ℕ) : τ (2^h * (3^i * 5^j)) = (h+1)*(i+1)*(j+1) := by
  rw [tau_mul, tau_mul (cop35 i j),tau_pow (by decide : Nat.Prime 2),
    tau_pow (by decide : Nat.Prime 3), tau_pow (by decide : Nat.Prime 5)]
  · ring
  · exact (((show Nat.Coprime 2 3 by decide).pow_right i).mul_right
      ((show Nat.Coprime 2 5 by decide).pow_right j)).pow_left h

private theorem cop_poly {b : ℕ} (i j : ℕ) (e : 0 < i) (e' : 0 < j) (h : b = 3^i * 5^j) :
    3 ∣ b ∧ 5 ∣ b := by
  subst b
  exact ⟨dvd_mul_of_dvd_left (dvd_pow_self 3 (by omega)) _,
    dvd_mul_of_dvd_right (dvd_pow_self 5 (by omega)) _⟩

private theorem six_counts (i j y z : ℕ) (hi : 0 < i) (hj : 0 < j) :
    let b := 3^i*5^j
    let s := 4*b+1
    let t := 2*b+1
    τ ((4*b) * 3^y) = 3*(i+y+1)*(j+1) ∧
    τ ((2*t)*3^y) = 2*τ t*(y+1) ∧
    τ (s*5^z) = τ s*(z+1) ∧
    τ ((2*b)*5^z) = 2*(i+1)*(j+z+1) := by
  dsimp only
  set b := 3^i*5^j with hb
  have ⟨h3,h5⟩ := cop_poly i j hi hj hb
  have ht : Nat.Coprime 3 (2*b+1) :=
    cop_small (by decide) (dvd_mul_of_dvd_right h3 2) (by decide)
  have hs : Nat.Coprime 5 (4*b+1) :=
    cop_small (by decide) (dvd_mul_of_dvd_right h5 4) (by decide)
  have ho : Nat.Coprime 2 (2*b+1) :=
    cop_small (by decide) (dvd_mul_right 2 b) (by decide)
  refine ⟨?_,?_,?_,?_⟩
  · rw [show 4*b*3^y=2^2*(3^(i+y)*5^j) by rw [hb,pow_add]; ring, tau235]
  · rw [tau_mul (((show Nat.Coprime 3 2 by decide).mul_right ht).pow_left y).symm,
      tau_mul ho,tau_pow (by decide : Nat.Prime 3),show τ 2=2 by decide]
  · rw [tau_mul (hs.pow_left z).symm, tau_pow (by decide : Nat.Prime 5)]
  · rw [show 2*b*5^z=2^1*(3^i*5^(j+z)) by rw [hb,pow_add]; ring,tau235]

private theorem weight_identity (k l : ℕ) :
    let i := 2*k+1
    let j := 2*l+1
    let y := 2*k
    let z := 2*l
    (4 : ℚ)*(y+1)*(i+1)*(j+z+1)/(3*(i+y+1)*(j+1)*(z+1)) =
      4*(k+1)/(3*(l+1)) := by
  dsimp
  push_cast
  field_simp; ring

private theorem synchronize {a b c d e f : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f) :
    ∃ t : Fin 3 → ℕ, (∀ i, 0 < t i) ∧
      let q := (a*c*f : ℚ)/(b*d*e)
      (a*t 0 : ℚ)/(b*t 1) = q ∧
      (c*t 1 : ℚ)/(d*t 2) = q ∧
      (e*t 0 : ℚ)/(f*t 2) = q := by
  let t : Fin 3 → ℕ := ![a*c*f^2,a*d*e*f,b*d*e^2]
  refine ⟨t,?_,?_⟩
  · intro i
    fin_cases i <;> dsimp [t] <;> positivity
  · dsimp [t]
    push_cast
    refine ⟨?_,?_,?_⟩ <;> field_simp

private theorem three_fresh (B : ℕ) : ∃ p : Fin 3 → ℕ,
    (∀ i, (p i).Prime ∧ B < p i) ∧ StrictMono p := by
  obtain ⟨p,hp,pp⟩ := Nat.exists_infinite_primes (B+1)
  obtain ⟨r,hr,pr⟩ := Nat.exists_infinite_primes (p+1)
  obtain ⟨s,hs,ps⟩ := Nat.exists_infinite_primes (r+1)
  use ![p,r,s]
  constructor
  · intro i
    fin_cases i
    · exact ⟨pp, show B < p by omega⟩
    · exact ⟨pr, show B < r by omega⟩
    · exact ⟨ps, show B < s by omega⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> (simp_all <;> omega)

private def difference (a b : ℕ) := if a > b then a-b else b-a

private def good (A r : Fin 3 → ℕ) : Prop :=
  (∀ i, 0 < A i ∧ 0 < r i ∧ (r i).Coprime (A i)) ∧ StrictMono A ∧
    ∀ i j, i ≠ j → (r i).Coprime (r j) ∧ (r i).Coprime (difference (A i) (A j))

private theorem augment (A r : Fin 3 → ℕ) (U V : Fin 3 → Fin 3 → ℕ)
    (hg : good A r) (t : Fin 3 → ℕ) (ht : ∀ i, 0 < t i) :
    ∃ R : Fin 3 → ℕ, good A R ∧ ∀ i j, 0 < U i j → 0 < V i j →
      τ (U i j * R i) = τ (U i j * r i) * t i ∧
      τ (V i j * R j) = τ (V i j * r j) * t j := by
  classical
  let W := fun ij : Fin 3 × Fin 3 => max (U ij.1 ij.2) (V ij.1 ij.2)
  let B := Finset.univ.sup A + Finset.univ.sup r + Finset.univ.sup W
  have hA (i : Fin 3) : A i ≤ B := by
    have := Finset.le_sup (f:=A) (Finset.mem_univ i)
    dsimp [B]; omega
  have hr (i : Fin 3) : r i ≤ B := by
    have := Finset.le_sup (f:=r) (Finset.mem_univ i)
    dsimp [B]; omega
  have hw (i j : Fin 3) : max (U i j) (V i j) ≤ B := by
    have h : W (i,j) ≤ Finset.univ.sup W := Finset.le_sup (Finset.mem_univ _)
    change W (i,j) ≤ _
    dsimp only [B]; omega
  obtain ⟨p,hp,hinc⟩ := three_fresh B
  let v := fun i => p i ^ (t i-1)
  have fresh (i : Fin 3) (n : ℕ) (hn : 0 < n) (hnB : n ≤ B) : (v i).Coprime n :=
    ((hp i).1.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt hn (hnB.trans_lt (hp i).2))).pow_left _
  refine ⟨fun i => r i * v i, ⟨?_,hg.2.1,?_⟩,?_⟩
  · intro i
    exact ⟨(hg.1 i).1,Nat.mul_pos (hg.1 i).2.1 (pow_pos (hp i).1.pos _),
      (hg.1 i).2.2.mul_left (fresh i _ (hg.1 i).1 (hA i))⟩
  · intro i j hij
    have hpair := hg.2.2 i j hij
    have hpi := fresh i _ (hg.1 j).2.1 (hr j)
    have hpj := fresh j _ (hg.1 i).2.1 (hr i)
    have hsep : (v i).Coprime (v j) :=
      (((Nat.coprime_primes (hp i).1 (hp j).1).mpr (hinc.injective.ne hij)).pow_left _).pow_right _
    have hd : A i ≠ A j := hg.2.1.injective.ne hij
    have hdpos : 0 < difference (A i) (A j) := by unfold difference; split <;> omega
    have hdb : difference (A i) (A j) ≤ B := by
      have := hA i; have := hA j
      unfold difference; split <;> omega
    exact ⟨(hpair.1.mul_left hpi).mul_right (hpj.symm.mul_left hsep),
      hpair.2.mul_left (fresh i _ hdpos hdb)⟩
  · intro i j hu hv
    have factor (l : Fin 3) (n : ℕ) (hn : 0 < n) (hnB : n ≤ B) :
        τ (n * (r l * v l)) = τ (n * r l) * t l := by
      have hc := ((fresh l _ hn hnB).mul_right (fresh l _ (hg.1 l).2.1 (hr l))).symm
      rw [← mul_assoc,tau_mul hc,show τ (v l) = t l by
        change τ ((p l) ^ (t l - 1)) = t l
        rw [tau_pow (hp l).1]; have := ht l; omega]
    exact ⟨factor i _ hu ((le_max_left _ _).trans (hw i j)),
      factor j _ hv ((le_max_right _ _).trans (hw i j))⟩

private theorem positive_tau {n : ℕ} (hn : 0 < n) : 0 < τ n :=
  Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn.ne'⟩

private theorem ratio_form {q : ℚ} (hq : 0 < q) : ∃ k l : ℕ,
    q = 4*(k+1)/(3*(l+1)) := by
  let s := 3*q/4
  have hs : 0 < s := by dsimp [s]; positivity
  have hn := Rat.num_pos.mpr hs
  have hd := s.pos
  refine ⟨s.num.toNat-1,s.den-1,?_⟩
  have hn' : (s.num.toNat : ℚ) = s.num := by exact_mod_cast Int.toNat_of_nonneg hn.le
  have h1 : (↑(s.num.toNat-1) : ℚ)+1 = s.num := by
    rw [← hn']; exact_mod_cast (show s.num.toNat-1+1=s.num.toNat by omega)
  have h2 : (↑(s.den-1) : ℚ)+1 = s.den := by
    exact_mod_cast (show s.den-1+1=s.den by omega)
  rw [h1,h2]
  have he := s.num_div_den
  change (↑s.num : ℚ)/s.den = 3*q/4 at he
  have hden : (s.den : ℚ) ≠ 0 := by positivity
  field_simp at he ⊢
  linarith

private theorem build (k l : ℕ) :
    ∃ A R : Fin 3 → ℕ, ∃ U V : Fin 3 → Fin 3 → ℕ, good A R ∧
    ∀ i j, i < j → 0 < U i j ∧ 0 < V i j ∧
      (∀ x : ℕ, U i j * (A i*x+1) = V i j * (A j*x+1)+1) ∧
      (τ (U i j*R i) : ℚ)/τ (V i j*R j) = 4*(k+1)/(3*(l+1)) := by
  let i := 2*k+1
  let j := 2*l+1
  let y := 2*k
  let z := 2*l
  let b := 3^i*5^j
  let s := 4*b+1
  let v := 2*b+1
  let A : Fin 3 → ℕ := ![4*b,s,2*v]
  let r : Fin 3 → ℕ := ![1,3^y,5^z]
  let U : Fin 3 → Fin 3 → ℕ := ![![1,s,v],![1,1,2*v],![1,1,1]]
  let V : Fin 3 → Fin 3 → ℕ := ![![1,4*b,2*b],![1,1,s],![1,1,1]]
  have hi : 0 < i := Nat.succ_pos _
  have hj : 0 < j := Nat.succ_pos _
  have hb : 0 < b := by dsimp [b]; positivity
  have hs : 0 < s := Nat.succ_pos _
  have hv : 0 < v := Nat.succ_pos _
  have ⟨h3,h5⟩ := cop_poly i j hi hj (rfl : b = _)
  have hs3 : Nat.Coprime 3 s := cop_small (by decide) (dvd_mul_of_dvd_right h3 4) (by decide)
  have hv5 : Nat.Coprime 5 v := cop_small (by decide) (dvd_mul_of_dvd_right h5 2) (by decide)
  have g : good A r := by
    refine ⟨?_,?_,?_⟩
    · intro u
      fin_cases u
      · exact ⟨by change 0 < 4*b; positivity,show 0 < 1 by decide,Nat.coprime_one_left _⟩
      · exact ⟨hs,pow_pos (by decide) _,hs3.pow_left _⟩
      · exact ⟨by change 0 < 2*v; positivity, pow_pos (by decide) _,
          (((show Nat.Coprime 5 2 by decide).mul_right hv5).pow_left _)⟩
    · intro u w huw
      fin_cases u <;> fin_cases w <;> simp_all [A,s,v] <;> omega
    · intro u w huw
      have d01 : difference (4*b) s = 1 := by unfold difference s; split <;> omega
      have d10 : difference s (4*b) = 1 := by unfold difference s; split <;> omega
      have d02 : difference (4*b) (2*v) = 2 := by dsimp [v,difference]; split <;> omega
      have d20 : difference (2*v) (4*b) = 2 := by dsimp [v,difference]; split <;> omega
      have d12 : difference s (2*v) = 1 := by dsimp [s,v,difference]; split <;> omega
      have d21 : difference (2*v) s = 1 := by dsimp [s,v,difference]; split <;> omega
      fin_cases u <;> fin_cases w <;> first | exact (huw rfl).elim |
        simp [A,r,d01,d10,d02,d20,d12,d21] <;>
        first | exact cop35 y z | exact (cop35 y z).symm | exact (show Odd 5 by decide).pow
  obtain ⟨d2,d3,d4,d6⟩ := six_counts i j y z hi hj
  change τ (4*b*3^y) = _ at d2
  change τ (2*v*3^y) = 2*τ v*(y+1) at d3
  change τ (s*5^z) = τ s * (z+1) at d4
  change τ (2*b*5^z) = _ at d6
  have hts := positive_tau hs
  have htv := positive_tau hv
  have raw :
      ((τ s : ℚ)*τ (2*v*3^y)*τ (2*b*5^z)) /
        (τ (4*b*3^y)*τ (s*5^z)*τ v) = 4*(k+1)/(3*(l+1)) := by
    rw [d2,d3,d4,d6,← weight_identity k l]
    push_cast
    simp only [i,j,y,z,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    field_simp
    ring
  obtain ⟨t,ht,t01,t12,t02⟩ := synchronize hts
    (positive_tau (n:=4*b*3^y) (by positivity))
    (positive_tau (n:=2*v*3^y) (by positivity))
    (positive_tau (n:=s*5^z) (by positivity)) htv
    (positive_tau (n:=2*b*5^z) (by positivity))
  obtain ⟨R,hR,hcounts⟩ := augment A r U V g t ht
  refine ⟨A,R,U,V,hR,?_⟩
  intro u w huw
  have cases3 : (u=0 ∧ w=1) ∨ (u=1 ∧ w=2) ∨ (u=0 ∧ w=2) := by
    fin_cases u <;> fin_cases w <;> simp at huw ⊢
  rcases cases3 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have hp : 0 < 4*b := by positivity
    obtain ⟨cu,cw⟩ := hcounts 0 1 hs hp
    refine ⟨hs,hp,fun x => ?_,?_⟩
    · change (4*b+1)*(4*b*x+1)=4*b*((4*b+1)*x+1)+1
      ring
    · rw [cu,cw,← raw]; push_cast
      change (τ (s*1) : ℚ)*t 0/(τ (4*b*3^y)*t 1) = _
      rw [mul_one]; exact t01
  · have hp : 0 < 2*v := by positivity
    obtain ⟨cu,cw⟩ := hcounts 1 2 hp hs
    refine ⟨hp,hs,fun x => ?_,?_⟩
    · change (2*(2*b+1))*((4*b+1)*x+1)=(4*b+1)*((2*(2*b+1))*x+1)+1
      ring
    · rw [cu,cw,← raw]; push_cast
      exact t12
  · have hp : 0 < 2*b := by positivity
    obtain ⟨cu,cw⟩ := hcounts 0 2 hv hp
    refine ⟨hv,hp,fun x => ?_,?_⟩
    · change (2*b+1)*(4*b*x+1)=2*b*((2*(2*b+1))*x+1)+1
      ring
    · rw [cu,cw,← raw]; push_cast
      change (τ (v*1) : ℚ)*t 0/(τ (2*b*5^z)*t 2) = _
      rw [mul_one]; exact t02

theorem coefficients :
  ∀ q : ℚ, 0 < q → ∃ A r : Fin 3 → ℕ, ∃ U V : Fin 3 → Fin 3 → ℕ,
    ((∀ i, 0 < A i ∧ 0 < r i ∧ (r i).Coprime (A i)) ∧ StrictMono A ∧
     (∀ i j, i ≠ j → (r i).Coprime (r j) ∧
       (r i).Coprime (if A i > A j then A i - A j else A j - A i))) ∧
    ∀ i j, i < j → 0 < U i j ∧ 0 < V i j ∧
      (∀ x : ℕ, U i j * (A i*x+1) = V i j * (A j*x+1)+1) ∧
      (((U i j * r i).divisors.card : ℚ) / (V i j * r j).divisors.card) = q := by
  intro q hq
  obtain ⟨k,l,hkl⟩ := ratio_form hq
  rw [hkl]
  exact build k l

end Explicit964

theorem OMA.solution : OMA.R_Erdos964_erdos_964_variants_eberhard_R1.H2 := Explicit964.coefficients
