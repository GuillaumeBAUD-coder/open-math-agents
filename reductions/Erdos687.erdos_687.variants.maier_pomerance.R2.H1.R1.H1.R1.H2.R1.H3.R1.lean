import OMAReductions.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H2_R1
import Mathlib

-- Reduction Erdos687.erdos_687.variants.maier_pomerance.R2.H1.R1.H1.R1.H2.R1.H3.R1 of step Erdos687.erdos_687.variants.maier_pomerance.R2.H1.R1.H1.R1.H2.R1.H3
-- Credit: @carterleffen

/-!
# Canonical-key partition and stopped-tree decoupling for compact-error geometry

Splits the stopped-tree geometric alternative (Sections 7-9 and 11 of *A quadratic bound
for Jacobsthal's function*, 2026) into two pure-Mathlib hypotheses over the logarithmic-bin
first-stop family `F`:

* `H1`: Stopped-tree reference upper bound. At every nonempty even admissible node `u` whose
  smallest prime `m` lies in `[exp(K (log w)^3), exp(b K (log w)^3)]` and whose ratio
  `g(u) / e(m)` lies in `[2, 11/5]`, the stopped reference polynomial below `u` is at most
  `(33/100) * v(Nat.primesLE m) * (Y / D u)`.
* `H2`: Compact error mass bound outside stopped prefixes. There exist scale-independent
  stopping parameters `(Clen, C, x, rho)` such that for every `K > 0`, eventually for every
  residue assignment `a`, the bad compact words in `T` with no stopped prefix have reciprocal
  weight at most `delta / B^2`.

Inside `main`, we directly prove the logarithmic bin partition, prefix-free first-stop
minimality, replacement invariance under swapping the first-tagged prime with any aligned
prime in its bin, the disjoint canonical-key fiber partition of `F`, all arithmetic and
length-exponent window inequalities `h(m, q, s, t, r)`, and the canonical-key sign dichotomy.
-/

namespace OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H2_R1_H3_R1
open Filter Finset Real
open scoped Classical

def H1 : Prop := ∀ K b : ℝ, 0<K → 1<b → ∀ᶠ z : ℝ in atTop,
  let L := log z; let Y := ⌊z^2/L^2⌋₊; let w := L/(log L)^2
  let P := (Icc (⌊w⌋₊+1) ⌊z⌋₊).filter Nat.Prime
  let Q := (range (⌊w⌋₊+1)).filter Nat.Prime
  let v := fun S : Finset ℕ => ∏ p∈S,(1-(p:ℝ)⁻¹)
  let μ := Y*v Q; let D := fun d : Finset ℕ => ∏ p∈d,(p:ℝ)
  let g := fun d => log (Y/D d)/log w+2-1/100; let e := fun p : ℕ => log p/log w
  let T := P.powerset.filter fun d => ∀ p∈d, let A := d.filter (p ≤ ·)
    Even A.card → max (2*e p) (e p+2) ≤ g A
  let I := fun u d : Finset ℕ => u⊆d ∧ ∀ p∈u,∀ q∈d\u,q<p
  ∀ u∈T, ∀ hu : u.Nonempty, Even u.card →
    let m := u.min' hu
    exp (K*(log w)^3) ≤ m → (m:ℝ) ≤ exp (b*K*(log w)^3) → 2 ≤ g u/e m → g u/e m ≤ 11/5 →
    μ*(∑ d∈T.filter (I u),(-1:ℝ)^d.card/D d) ≤ (33/100*v (Nat.primesLE m))*((Y:ℝ)/D u)

def H2 : Prop := ∀ k ε δ d : ℝ, 3≤k → 0<ε → 0<δ → 0<d → d≤1/4 →
 ∃ Clen C x ρ : ℝ, 1≤Clen ∧ 0≤C ∧ 0<x ∧ x≤1 ∧ 10<ρ ∧ ∀ K : ℝ, 0<K → ∀ᶠ z : ℝ in atTop,
  let L := log z; let Y := ⌊z^2/L^2⌋₊; let w := L/(log L)^2; let B := L/log w
  let Q := Nat.primesLE ⌊w⌋₊; let P := Nat.primesLE ⌊z⌋₊ \ Q
  let μ := Y*(∏ p∈Q,(1-(p:ℝ)⁻¹)); let D := fun s : Finset ℕ => ∏ p∈s,(p:ℝ)
  let g := fun s => log (Y/D s)/log w+2-1/100; let e := fun p : ℕ => log p/log w
  let T := P.powerset.filter fun s => ∀ p∈s, Even (s.filter (p≤·)).card →
    max (2*e p) (e p+2) ≤ g (s.filter (p≤·))
  let M := ⌈log (z/w)/log (1+x)⌉₊; let δl := log (z/w)/(M:ℝ)
  let lo := fun i : ℕ => w*exp (i*δl); let lab := fun p : ℕ => min (M-1) (⌈log ((p:ℝ)/w)/δl⌉₊-1)
  let rep := fun p : ℕ => 1+((lab p:ℝ)+1)*δl/log w
  let gr := fun s : Finset ℕ => log Y/log w+2-1/100-∑ p∈s,rep p
  let J := fun i : ℕ => Nat.primesLE ⌊w*exp ((i+1)*δl)⌋₊ \ Nat.primesLE ⌊lo i⌋₊
  ∀ a : ℕ → ℕ,
  let al := fun (r : ℚ) (p : ℕ) => (r.den:ZMod p)*(a p:ZMod p)=(r.num:ZMod p)
  let own := fun (i : ℕ) (r : ℚ) => (r.den:ℝ) ≤ w^C ∧ |(r.num:ℝ)| ≤ Y*w^(C+2) ∧
    (1-d)*((J i).card:ℝ) ≤ ((J i).filter (al r)).card
  let tg := fun (p : ℕ) (r : ℚ) => exp (w^((1:ℝ)/4)*log w) ≤ lo (lab p) ∧
    own (lab p) r ∧ (∀ r',own (lab p) r' → r ≤ r') ∧ al r p
  let S := fun u : Finset ℕ => u.Nonempty ∧ Even u.card ∧ (u.card:ℝ) ≤ Clen*log B ∧
    (∀ p∈u, Even (u.filter (p≤·)).card → max (2*rep p) (rep p+2)+6*Clen*x ≤ gr (u.filter (p≤·))) ∧
    (∀ m∈u, (∀ q∈u,m ≤ q) → 2*K*(log w)^2 ≤ rep m ∧ rep m ≤ 2*ρ*K*(log w)^2 ∧
      206/100 ≤ gr u/rep m ∧ gr u/rep m ≤ 216/100) ∧
    (∃ p∈u, ∃ r : ℚ, tg p r ∧ (∀ q∈u,p<q → ∀ r',¬tg q r') ∧
      (u.filter (fun q => lab q=lab p)).card=1 ∧ ∀ q∈u,al r q)
  let E := T.filter fun u => ∀ p∈u, ¬S (u.filter (p≤·))
  let A := E.filter fun u => g u ≤ k ∧ ε < |(((Icc 1 Y).filter (fun n =>
    (∀ p∈u,n≡a p [MOD p]) ∧ ∀ p∈Q,¬(n≡a p [MOD p]))).card:ℝ)/(μ/D u)-1|
  B^2*(∑ u∈A,(D u)⁻¹) ≤ δ

section

private lemma range_primes_eq (n : ℕ) :
    (range (n + 1)).filter Nat.Prime = Nat.primesLE n := by
  ext p
  simp only [mem_filter, mem_range, Nat.mem_primesLE]
  exact ⟨fun ⟨h1, h2⟩ => ⟨by omega, h2⟩, fun ⟨h1, h2⟩ => ⟨by omega, h2⟩⟩

private lemma icc_primes_eq (a b : ℕ) :
    (Icc (a + 1) b).filter Nat.Prime = Nat.primesLE b \ Nat.primesLE a := by
  ext p
  simp only [mem_filter, mem_Icc, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨⟨h2, hp⟩, fun ⟨h3, _⟩ => by omega⟩
  · rintro ⟨⟨h2, hp⟩, hnot⟩
    refine ⟨⟨?_, h2⟩, hp⟩
    by_contra hlt
    exact hnot ⟨by omega, hp⟩

private lemma prod_primes_pos {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    0 < ∏ p ∈ s, p :=
  Finset.prod_pos fun p hp => (hs p hp).pos

private lemma prod_primes_squarefree {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
    rw [Finset.prod_insert hat]
    have ha : a.Prime := hs a (mem_insert_self a t)
    have ht : ∀ p ∈ t, p.Prime := fun p hp => hs p (mem_insert_of_mem hp)
    have hcop : a.Coprime (∏ p ∈ t, p) := by
      refine Nat.Coprime.prod_right fun p hp => ?_
      exact (Nat.coprime_primes ha (ht p hp)).mpr (fun h => hat (h ▸ hp))
    exact (Nat.squarefree_mul hcop).mpr ⟨ha.squarefree, ih ht⟩

private lemma primeFactors_prod_primes {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    (∏ p ∈ s, p).primeFactors = s := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
    rw [Finset.prod_insert hat]
    have ha : a.Prime := hs a (mem_insert_self a t)
    have ht : ∀ p ∈ t, p.Prime := fun p hp => hs p (mem_insert_of_mem hp)
    rw [Nat.primeFactors_mul ha.ne_zero (prod_primes_pos ht).ne', ha.primeFactors, ih ht]
    ext x
    simp

private lemma prod_insert_prime_props {s : Finset ℕ} {p : ℕ}
    (hp : p.Prime) (hs : ∀ x ∈ s, x.Prime) (hns : p ∉ s) :
    Squarefree (p * ∏ x ∈ s, x) ∧ (p * ∏ x ∈ s, x).primeFactors = insert p s := by
  have h1 : ∀ x ∈ insert p s, x.Prime := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hp
    · exact hs x hx
  have hprod : p * ∏ x ∈ s, x = ∏ x ∈ insert p s, x :=
    (Finset.prod_insert (f := fun x : ℕ => x) hns).symm
  rw [hprod]
  exact ⟨prod_primes_squarefree h1, primeFactors_prod_primes h1⟩

private lemma prefix_eq_filter_min {u d : Finset ℕ}
    (hI : u ⊆ d ∧ ∀ p ∈ u, ∀ q ∈ d \ u, q < p) (hu : u.Nonempty) :
    u = d.filter (u.min' hu ≤ ·) := by
  ext x
  simp only [mem_filter]
  constructor
  · intro hx
    exact ⟨hI.1 hx, Finset.min'_le u x hx⟩
  · rintro ⟨hxd, hmx⟩
    by_contra hxu
    have hlt := hI.2 (u.min' hu) (Finset.min'_mem u hu) x (Finset.mem_sdiff.mpr ⟨hxd, hxu⟩)
    omega

private lemma filter_ge_is_prefix {d : Finset ℕ} {p : ℕ} (hp : p ∈ d) :
    (d.filter (p ≤ ·) ⊆ d ∧ ∀ x ∈ d.filter (p ≤ ·), ∀ y ∈ d \ d.filter (p ≤ ·), y < x) ∧
    (d.filter (p ≤ ·)).Nonempty ∧
    ∀ hne : (d.filter (p ≤ ·)).Nonempty, (d.filter (p ≤ ·)).min' hne = p := by
  refine ⟨⟨filter_subset _ _, ?_⟩, ⟨p, mem_filter.mpr ⟨hp, le_rfl⟩⟩, ?_⟩
  · intro x hx y hy
    have hx' := (mem_filter.mp hx).2
    have hy' : ¬ (p ≤ y) := fun h =>
      (Finset.mem_sdiff.mp hy).2 (mem_filter.mpr ⟨(Finset.mem_sdiff.mp hy).1, h⟩)
    omega
  · intro hne
    apply le_antisymm
    · exact Finset.min'_le _ p (mem_filter.mpr ⟨hp, le_rfl⟩)
    · exact (mem_filter.mp (Finset.min'_mem _ hne)).2

private lemma prefix_total {u₁ u₂ d : Finset ℕ}
    (h₁ : u₁ ⊆ d ∧ ∀ p ∈ u₁, ∀ q ∈ d \ u₁, q < p)
    (h₂ : u₂ ⊆ d ∧ ∀ p ∈ u₂, ∀ q ∈ d \ u₂, q < p) :
    (u₁ ⊆ u₂ ∧ ∀ p ∈ u₁, ∀ q ∈ u₂ \ u₁, q < p) ∨
    (u₂ ⊆ u₁ ∧ ∀ p ∈ u₂, ∀ q ∈ u₁ \ u₂, q < p) := by
  by_cases he₁ : u₁.Nonempty
  · by_cases he₂ : u₂.Nonempty
    · rw [prefix_eq_filter_min h₁ he₁, prefix_eq_filter_min h₂ he₂]
      rcases le_total (u₁.min' he₁) (u₂.min' he₂) with hle | hle
      · right
        refine ⟨fun x hx => mem_filter.mpr ⟨(mem_filter.mp hx).1, hle.trans (mem_filter.mp hx).2⟩, ?_⟩
        intro p hp q hq
        have hp' := (mem_filter.mp hp).2
        have hq' : ¬ (u₂.min' he₂ ≤ q) := fun h =>
          (Finset.mem_sdiff.mp hq).2 (mem_filter.mpr ⟨(mem_filter.mp (Finset.mem_sdiff.mp hq).1).1, h⟩)
        omega
      · left
        refine ⟨fun x hx => mem_filter.mpr ⟨(mem_filter.mp hx).1, hle.trans (mem_filter.mp hx).2⟩, ?_⟩
        intro p hp q hq
        have hp' := (mem_filter.mp hp).2
        have hq' : ¬ (u₁.min' he₁ ≤ q) := fun h =>
          (Finset.mem_sdiff.mp hq).2 (mem_filter.mpr ⟨(mem_filter.mp (Finset.mem_sdiff.mp hq).1).1, h⟩)
        omega
    · rw [Finset.not_nonempty_iff_eq_empty] at he₂
      subst he₂
      right
      exact ⟨empty_subset _, fun _ hp => by simp at hp⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at he₁
    subst he₁
    left
    exact ⟨empty_subset _, fun _ hp => by simp at hp⟩

private lemma filter_ge_filter_ge {d : Finset ℕ} {p q : ℕ} (hpq : p ≤ q) :
    (d.filter (p ≤ ·)).filter (q ≤ ·) = d.filter (q ≤ ·) := by
  ext x
  simp only [mem_filter]
  exact ⟨fun ⟨⟨hd, _⟩, hq⟩ => ⟨hd, hq⟩, fun ⟨hd, hq⟩ => ⟨⟨hd, hpq.trans hq⟩, hq⟩⟩

private lemma prefix_filter_eq {u d : Finset ℕ} {p : ℕ}
    (hI : u ⊆ d ∧ ∀ x ∈ u, ∀ y ∈ d \ u, y < x) (hp : p ∈ u) :
    d.filter (p ≤ ·) = u.filter (p ≤ ·) := by
  ext x
  simp only [mem_filter]
  constructor
  · rintro ⟨hxd, hpx⟩
    refine ⟨?_, hpx⟩
    by_contra hxu
    have hlt := hI.2 p hp x (Finset.mem_sdiff.mpr ⟨hxd, hxu⟩)
    omega
  · rintro ⟨hxu, hpx⟩
    exact ⟨hI.1 hxu, hpx⟩

private lemma stop_family_props {T : Finset (Finset ℕ)}
    (hTclosed : ∀ u d, d ∈ T → (u ⊆ d ∧ ∀ p ∈ u, ∀ q ∈ d \ u, q < p) → u ∈ T)
    (S : Finset ℕ → Prop) (hSne : ∀ u, S u → u.Nonempty)
    (F E : Finset (Finset ℕ))
    (hFdef : ∀ u, u ∈ F ↔ u ∈ T ∧ S u ∧ ∀ p ∈ u, u.filter (p ≤ ·) ≠ u → ¬ S (u.filter (p ≤ ·)))
    (hEdef : ∀ d, d ∈ E ↔ d ∈ T ∧ ∀ u ∈ F, ¬ (u ⊆ d ∧ ∀ p ∈ u, ∀ q ∈ d \ u, q < p)) :
    let I := fun u d : Finset ℕ => u ⊆ d ∧ ∀ p ∈ u, ∀ q ∈ d \ u, q < p
    F ⊆ T ∧
    (∀ u ∈ F, S u ∧ ∀ v ∈ F, I v u → v = u) ∧
    (∀ d, d ∈ E ↔ d ∈ T ∧ ∀ p ∈ d, ¬ S (d.filter (p ≤ ·))) ∧
    T \ E = F.biUnion (fun u => T.filter (I u)) ∧
    (F : Set (Finset ℕ)).PairwiseDisjoint (fun u => T.filter (I u)) := by
  intro I
  have hFsub : F ⊆ T := fun u hu => (hFdef u).mp hu |>.1
  have hFpf : ∀ u ∈ F, S u ∧ ∀ v ∈ F, I v u → v = u := by
    intro u hu
    have hu' := ((hFdef u).mp hu).2
    refine ⟨hu'.1, ?_⟩
    intro v hv hIvu
    have hvS : S v := ((hFdef v).mp hv).2.1
    have hvne : v.Nonempty := hSne v hvS
    have hveq := prefix_eq_filter_min hIvu hvne
    have hmin_mem : v.min' hvne ∈ u := hIvu.1 (Finset.min'_mem v hvne)
    by_contra hne
    rw [hveq] at hne
    exact hu'.2 (v.min' hvne) hmin_mem hne (hveq ▸ hvS)
  have hEeq : ∀ d, d ∈ E ↔ d ∈ T ∧ ∀ p ∈ d, ¬ S (d.filter (p ≤ ·)) := by
    intro d
    rw [hEdef d]
    refine and_congr_right fun hdT => ⟨?_, ?_⟩
    · intro hno p hp hSp
      let good := d.filter fun q => S (d.filter (q ≤ ·))
      have hgood : good.Nonempty := ⟨p, mem_filter.mpr ⟨hp, hSp⟩⟩
      let pmax := good.max' hgood
      have hpmax_mem : pmax ∈ good := Finset.max'_mem good hgood
      have hpmax_d : pmax ∈ d := (mem_filter.mp hpmax_mem).1
      have hSpmax : S (d.filter (pmax ≤ ·)) := (mem_filter.mp hpmax_mem).2
      let v := d.filter (pmax ≤ ·)
      have hvI : I v d := (filter_ge_is_prefix hpmax_d).1
      have hvT : v ∈ T := hTclosed v d hdT hvI
      have hvF : v ∈ F := by
        refine (hFdef v).mpr ⟨hvT, hSpmax, ?_⟩
        intro q hq hqne hSq
        have hqd : q ∈ d := (mem_filter.mp hq).1
        have hpq : pmax ≤ q := (mem_filter.mp hq).2
        have hfeq : v.filter (q ≤ ·) = d.filter (q ≤ ·) := filter_ge_filter_ge hpq
        rw [hfeq] at hqne hSq
        have hqle : q ≤ pmax := Finset.le_max' good q (mem_filter.mpr ⟨hqd, hSq⟩)
        have hqp : q = pmax := le_antisymm hqle hpq
        subst hqp
        exact hqne rfl
      exact hno v hvF hvI
    · intro hno u hu hIud
      have hune : u.Nonempty := hSne u (hFpf u hu).1
      have hueq := prefix_eq_filter_min hIud hune
      have hm : u.min' hune ∈ d := hIud.1 (Finset.min'_mem u hune)
      exact hno (u.min' hune) hm (hueq ▸ (hFpf u hu).1)
  have hDisj : (F : Set (Finset ℕ)).PairwiseDisjoint (fun u => T.filter (I u)) := by
    intro u₁ hu₁ u₂ hu₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro d hd₁ hd₂
    have hI₁ := (mem_filter.mp hd₁).2
    have hI₂ := (mem_filter.mp hd₂).2
    rcases prefix_total hI₁ hI₂ with h₁₂ | h₂₁
    · exact hne ((hFpf u₂ hu₂).2 u₁ hu₁ h₁₂)
    · exact hne ((hFpf u₁ hu₁).2 u₂ hu₂ h₂₁).symm
  have hUnion : T \ E = F.biUnion (fun u => T.filter (I u)) := by
    ext d
    rw [Finset.mem_sdiff, hEdef d, mem_biUnion]
    constructor
    · rintro ⟨hdT, hnot⟩
      have hex : ∃ u ∈ F, I u d := by
        by_contra hall
        exact hnot ⟨hdT, fun u hu hI => hall ⟨u, hu, hI⟩⟩
      obtain ⟨u, hu, hIud⟩ := hex
      exact ⟨u, hu, mem_filter.mpr ⟨hdT, hIud⟩⟩
    · rintro ⟨u, hu, hd⟩
      have hd' := mem_filter.mp hd
      exact ⟨hd'.1, fun ⟨_, hall⟩ => hall u hu hd'.2⟩
  exact ⟨hFsub, hFpf, hEeq, hUnion, hDisj⟩

private lemma log_bin_basic {w z x : ℝ}
    (hw : 1 < w) (hwz : w < z) (hx : 0 < x) (hx1 : x ≤ 1)
    (hspan : log (1 + x) ≤ log (z / w)) :
    let M := ⌈log (z / w) / log (1 + x)⌉₊
    let δl := log (z / w) / (M : ℝ)
    let lo := fun i : ℕ => w * exp ((i : ℝ) * δl)
    let lab := fun p : ℕ => min (M - 1) (⌈log ((p : ℝ) / w) / δl⌉₊ - 1)
    let J := fun i : ℕ => Nat.primesLE ⌊w * exp (((i : ℝ) + 1) * δl)⌋₊ \ Nat.primesLE ⌊lo i⌋₊
    let P := Nat.primesLE ⌊z⌋₊ \ Nat.primesLE ⌊w⌋₊
    0 < M ∧ 0 < δl ∧ δl ≤ log (1 + x) ∧ δl ≤ x ∧
    x / 4 ≤ exp δl - 1 ∧ exp δl - 1 ≤ 1 ∧
    lo 0 = w ∧ lo M = z ∧
    (∀ i j : ℕ, i < j → lo i < lo j) ∧
    (∀ i : ℕ, (1 + (exp δl - 1)) * lo i = w * exp (((i : ℝ) + 1) * δl)) ∧
    (∀ p ∈ P, lab p < M ∧ lo (lab p) < (p : ℝ) ∧ (p : ℝ) ≤ w * exp (((lab p : ℝ) + 1) * δl) ∧
      p ∈ J (lab p) ∧ log (p : ℝ) / log w ≤ 1 + ((lab p : ℝ) + 1) * δl / log w ∧
      (1 + ((lab p : ℝ) + 1) * δl / log w) - log (p : ℝ) / log w ≤ x / log w) ∧
    (∀ i < M, ∀ p ∈ J i, p ∈ P ∧ lab p = i ∧
      lo i < (p : ℝ) ∧ (p : ℝ) ≤ w * exp (((i : ℝ) + 1) * δl)) := by
  intro M δl lo lab J P
  have hw0 : 0 < w := zero_lt_one.trans hw
  have hz0 : 0 < z := hw0.trans hwz
  have hlogw : 0 < log w := log_pos hw
  have hspan_pos : 0 < log (z / w) := log_pos ((one_lt_div hw0).mpr hwz)
  have hlog1x : 0 < log (1 + x) := log_pos (by linarith)
  have hMpos : 0 < M := Nat.ceil_pos.mpr (div_pos hspan_pos hlog1x)
  have hMposR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
  have hδpos : 0 < δl := div_pos hspan_pos hMposR
  have hMδ : (M : ℝ) * δl = log (z / w) := by
    dsimp only [δl]
    field_simp [hMposR.ne']
  have hδle_log : δl ≤ log (1 + x) := by
    have hc : log (z / w) / log (1 + x) ≤ (M : ℝ) := Nat.le_ceil _
    have hm : log (z / w) ≤ (M : ℝ) * log (1 + x) := (div_le_iff₀ hlog1x).mp hc
    exact (div_le_iff₀ hMposR).mpr (by linarith)
  have hlog1x_le : log (1 + x) ≤ x := by
    have h := log_le_sub_one_of_pos (show 0 < 1 + x by linarith)
    linarith
  have hδle_x : δl ≤ x := hδle_log.trans hlog1x_le
  have hδge_half : log (1 + x) / 2 ≤ δl := by
    have hc : (M : ℝ) < log (z / w) / log (1 + x) + 1 :=
      Nat.ceil_lt_add_one (div_pos hspan_pos hlog1x).le
    have hm : (M : ℝ) * log (1 + x) < log (z / w) + log (1 + x) := by
      have := mul_lt_mul_of_pos_right hc hlog1x
      rwa [add_mul, one_mul, div_mul_cancel₀ _ hlog1x.ne'] at this
    exact (le_div_iff₀ hMposR).mpr (by nlinarith)
  have ht_lo : x / 4 ≤ exp δl - 1 := by
    have h1 := one_sub_inv_le_log_of_pos (show 0 < 1 + x by linarith)
    have h2 : 1 - (1 + x)⁻¹ = x / (1 + x) := by
      have hp : (1 + x : ℝ) ≠ 0 := by linarith
      field_simp [hp]
      ring
    rw [h2] at h1
    have h3 : x / 2 ≤ x / (1 + x) := div_le_div_of_nonneg_left hx.le (by linarith) (by linarith)
    have h4 := add_one_le_exp δl
    linarith
  have ht_hi : exp δl - 1 ≤ 1 := by
    have h1 : exp δl ≤ exp (log (1 + x)) := exp_le_exp.mpr hδle_log
    rw [exp_log (by linarith)] at h1
    linarith
  have hlo0 : lo 0 = w := by simp [lo]
  have hloM : lo M = z := by
    dsimp only [lo]
    rw [hMδ, exp_log (div_pos hz0 hw0)]
    field_simp [hw0.ne']
  have hlo_mono : ∀ i j : ℕ, i < j → lo i < lo j := by
    intro i j hij
    dsimp only [lo]
    have hijR : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
    exact mul_lt_mul_of_pos_left (exp_lt_exp.mpr (mul_lt_mul_of_pos_right hijR hδpos)) hw0
  have hupper : ∀ i : ℕ, (1 + (exp δl - 1)) * lo i = w * exp (((i : ℝ) + 1) * δl) := by
    intro i
    dsimp only [lo]
    rw [show (1 + (exp δl - 1) : ℝ) = exp δl by ring,
      show (((i : ℝ) + 1) * δl) = (i : ℝ) * δl + δl by ring, exp_add]
    ring
  have hP_props : ∀ p ∈ P, lab p < M ∧ lo (lab p) < (p : ℝ) ∧
      (p : ℝ) ≤ w * exp (((lab p : ℝ) + 1) * δl) ∧ p ∈ J (lab p) ∧
      log (p : ℝ) / log w ≤ 1 + ((lab p : ℝ) + 1) * δl / log w ∧
      (1 + ((lab p : ℝ) + 1) * δl / log w) - log (p : ℝ) / log w ≤ x / log w := by
    intro p hp
    have hp' := Finset.mem_sdiff.mp hp
    have hpz_nat : p ≤ ⌊z⌋₊ := (Nat.mem_primesLE.mp hp'.1).1
    have hp_prime : p.Prime := (Nat.mem_primesLE.mp hp'.1).2
    have hpw_nat : ¬ (p ≤ ⌊w⌋₊) := fun h => hp'.2 (Nat.mem_primesLE.mpr ⟨h, hp_prime⟩)
    have hpw : w < (p : ℝ) := (Nat.floor_lt hw0.le).mp (by omega)
    have hpz : (p : ℝ) ≤ z := (Nat.le_floor_iff hz0.le).mp hpz_nat
    have hpw0 : 0 < (p : ℝ) / w := div_pos (hw0.trans hpw) hw0
    have hcoord_pos : 0 < log ((p : ℝ) / w) / δl :=
      div_pos (log_pos ((one_lt_div hw0).mpr hpw)) hδpos
    have hcoord_le : log ((p : ℝ) / w) / δl ≤ (M : ℝ) := by
      refine (div_le_iff₀ hδpos).mpr ?_
      rw [hMδ]
      exact log_le_log hpw0 (div_le_div_of_nonneg_right hpz hw0.le)
    have hceil_pos : 0 < ⌈log ((p : ℝ) / w) / δl⌉₊ := Nat.ceil_pos.mpr hcoord_pos
    have hceil_le : ⌈log ((p : ℝ) / w) / δl⌉₊ ≤ M := Nat.ceil_le.mpr hcoord_le
    have hlab_eq : lab p = ⌈log ((p : ℝ) / w) / δl⌉₊ - 1 := min_eq_right (by omega)
    have hlab_lt : lab p < M := by omega
    have hlabR : (lab p : ℝ) = (⌈log ((p : ℝ) / w) / δl⌉₊ : ℝ) - 1 := by
      rw [hlab_eq, Nat.cast_sub (by omega : 1 ≤ ⌈log ((p : ℝ) / w) / δl⌉₊), Nat.cast_one]
    have hcl : (lab p : ℝ) < log ((p : ℝ) / w) / δl := by
      rw [hlabR]
      linarith [Nat.ceil_lt_add_one hcoord_pos.le]
    have hch : log ((p : ℝ) / w) / δl ≤ (lab p : ℝ) + 1 := by
      rw [hlabR]
      linarith [Nat.le_ceil (log ((p : ℝ) / w) / δl)]
    have hmul_lo : (lab p : ℝ) * δl < log ((p : ℝ) / w) := (lt_div_iff₀ hδpos).mp hcl
    have hmul_hi : log ((p : ℝ) / w) ≤ ((lab p : ℝ) + 1) * δl := (div_le_iff₀ hδpos).mp hch
    have hplo : lo (lab p) < (p : ℝ) := by
      have h1 := exp_lt_exp.mpr hmul_lo
      rw [exp_log hpw0, lt_div_iff₀ hw0] at h1
      dsimp only [lo]
      linarith
    have hphi : (p : ℝ) ≤ w * exp (((lab p : ℝ) + 1) * δl) := by
      have h1 := exp_le_exp.mpr hmul_hi
      rw [exp_log hpw0, div_le_iff₀ hw0] at h1
      linarith
    have hpJ : p ∈ J (lab p) := by
      rw [Finset.mem_sdiff]
      refine ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (by positivity)).mpr hphi, hp_prime⟩, ?_⟩
      intro hmem
      have hle := (Nat.le_floor_iff (by positivity)).mp (Nat.mem_primesLE.mp hmem).1
      linarith
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.pos
    have hlog_eq : log ((p : ℝ) / w) = log (p : ℝ) - log w := log_div hp0.ne' hw0.ne'
    have hrep_ge : log (p : ℝ) / log w ≤ 1 + ((lab p : ℝ) + 1) * δl / log w := by
      rw [hlog_eq] at hmul_hi
      rw [one_add_div hlogw.ne']
      exact div_le_div_of_nonneg_right (by linarith) hlogw.le
    have hrep_diff : (1 + ((lab p : ℝ) + 1) * δl / log w) - log (p : ℝ) / log w ≤ x / log w := by
      rw [hlog_eq] at hmul_lo
      have h1 : (log w + ((lab p : ℝ) + 1) * δl) - log (p : ℝ) < δl := by nlinarith
      have h2 : (1 + ((lab p : ℝ) + 1) * δl / log w) - log (p : ℝ) / log w =
          ((log w + ((lab p : ℝ) + 1) * δl) - log (p : ℝ)) / log w := by
        field_simp [hlogw.ne']
      rw [h2]
      exact div_le_div_of_nonneg_right (h1.le.trans hδle_x) hlogw.le
    exact ⟨hlab_lt, hplo, hphi, hpJ, hrep_ge, hrep_diff⟩
  have hJ_props : ∀ i < M, ∀ p ∈ J i, p ∈ P ∧ lab p = i ∧
      lo i < (p : ℝ) ∧ (p : ℝ) ≤ w * exp (((i : ℝ) + 1) * δl) := by
    intro i hi p hp
    have hp' := Finset.mem_sdiff.mp hp
    have hp_prime : p.Prime := (Nat.mem_primesLE.mp hp'.1).2
    have hphi : (p : ℝ) ≤ w * exp (((i : ℝ) + 1) * δl) :=
      (Nat.le_floor_iff (by positivity)).mp (Nat.mem_primesLE.mp hp'.1).1
    have hplo_not : ¬ (p ≤ ⌊lo i⌋₊) := fun h => hp'.2 (Nat.mem_primesLE.mpr ⟨h, hp_prime⟩)
    have hplo : lo i < (p : ℝ) := (Nat.floor_lt (by positivity)).mp (by omega)
    have hlo_ge : w ≤ lo i := by
      rw [← hlo0]
      rcases eq_or_lt_of_le (Nat.zero_le i) with rfl | h0i
      · exact le_rfl
      · exact (hlo_mono 0 i h0i).le
    have hhi_le : w * exp (((i : ℝ) + 1) * δl) ≤ z := by
      have h1 : lo (i + 1) = w * exp (((i : ℝ) + 1) * δl) := by
        simp only [lo, Nat.cast_add, Nat.cast_one]
      rw [← h1, ← hloM]
      rcases eq_or_lt_of_le (show i + 1 ≤ M by omega) with heq | hlt
      · rw [heq]
      · exact (hlo_mono (i + 1) M hlt).le
    have hpP : p ∈ P := by
      rw [Finset.mem_sdiff]
      refine ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hz0.le).mpr (hphi.trans hhi_le), hp_prime⟩, ?_⟩
      intro hmem
      have hle := (Nat.le_floor_iff hw0.le).mp (Nat.mem_primesLE.mp hmem).1
      linarith
    have hpw0 : 0 < (p : ℝ) / w := div_pos (hw0.trans (hlo_ge.trans_lt hplo)) hw0
    have hcoord_lo : (i : ℝ) < log ((p : ℝ) / w) / δl := by
      refine (lt_div_iff₀ hδpos).mpr ?_
      have h1 : exp ((i : ℝ) * δl) < (p : ℝ) / w :=
        (lt_div_iff₀ hw0).mpr (by dsimp only [lo] at hplo; linarith)
      have h2 := log_lt_log (exp_pos _) h1
      rwa [log_exp] at h2
    have hcoord_hi : log ((p : ℝ) / w) / δl ≤ (i : ℝ) + 1 := by
      refine (div_le_iff₀ hδpos).mpr ?_
      have h1 : (p : ℝ) / w ≤ exp (((i : ℝ) + 1) * δl) := (div_le_iff₀ hw0).mpr (by linarith)
      have h2 := log_le_log hpw0 h1
      rwa [log_exp] at h2
    have hceil_eq : ⌈log ((p : ℝ) / w) / δl⌉₊ = i + 1 := by
      apply le_antisymm
      · exact Nat.ceil_le.mpr (by exact_mod_cast hcoord_hi)
      · have : i < ⌈log ((p : ℝ) / w) / δl⌉₊ := Nat.lt_ceil.mpr hcoord_lo
        omega
    have hlab_eq : lab p = i := by
      dsimp only [lab]
      rw [hceil_eq, Nat.add_sub_cancel]
      exact min_eq_right (by omega)
    exact ⟨hpP, hlab_eq, hplo, hphi⟩
  exact ⟨hMpos, hδpos, hδle_log, hδle_x, ht_lo, ht_hi, hlo0, hloM, hlo_mono, hupper, hP_props, hJ_props⟩

private lemma tendsto_w_atTop :
    Tendsto (fun z : ℝ => log z / (log (log z)) ^ 2) atTop atTop := by
  have h1 : Tendsto (fun L : ℝ => L / (log L) ^ 2) atTop atTop := by
    have ho : (fun L : ℝ => (log L) ^ 2) =o[atTop] (fun L : ℝ => L ^ ((1 : ℝ) / 2)) := by
      simpa only [rpow_ofNat] using isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 1 / 2) (by norm_num)
    have hhalf : Tendsto (fun L : ℝ => L ^ ((1 : ℝ) / 2)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num)
    refine tendsto_atTop_mono' atTop ?_ hhalf
    filter_upwards [ho.bound (show (0 : ℝ) < 1 by norm_num), eventually_gt_atTop (exp 1)] with L hL hLe
    have hL0 : 0 < L := (exp_pos 1).trans hLe
    have hlogL : 0 < log L := by
      have hlt := log_lt_log (exp_pos 1) hLe
      rw [log_exp] at hlt
      linarith
    have hsq : 0 < (log L) ^ 2 := sq_pos_of_pos hlogL
    have hbound : (log L) ^ 2 ≤ L ^ ((1 : ℝ) / 2) := by
      simpa only [norm_eq_abs, abs_of_pos hsq, abs_of_pos (rpow_pos_of_pos hL0 _), one_mul] using hL
    have hmul : L ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2) = L := by
      rw [← rpow_add hL0]
      norm_num
    rw [le_div_iff₀ hsq]
    nlinarith [rpow_pos_of_pos hL0 ((1 : ℝ) / 2)]
  exact h1.comp tendsto_log_atTop

private lemma scale_eventually (Clen C K ρ x W : ℝ) (N : ℕ)
    (_hClen : 1 ≤ Clen) (hK : 0 < K) (hρ : 1 < ρ) (hx : 0 < x) :
    ∀ᶠ z : ℝ in atTop,
      let L := log z; let Y := ⌊z ^ 2 / L ^ 2⌋₊; let w := L / (log L) ^ 2; let B := L / log w
      1 < w ∧ W ≤ w ∧ (N : ℝ) ≤ w ∧ w < z ∧ 0 < Y ∧
      log (1 + x) ≤ log (z / w) ∧ log B ≤ 2 * log w ∧
      2 * ρ * K * (log w) ^ 2 < w ^ ((1 : ℝ) / 4) ∧
      C < w ^ ((1 : ℝ) / 4) ∧
      x / log w ≤ K * (log w) ^ 2 ∧
      (2 * Clen * x + 2 + x / log w) / (K * (log w) ^ 2) ≤ 1 / 100 ∧
      (216 / 100) * (x / log w) / (K * (log w) ^ 2) ≤ 1 / 100 ∧
      (199 / 100) / (K * (log w) ^ 2) ≤ 1 / 100 := by
  have hwT := tendsto_w_atTop
  have hlogwT : Tendsto (fun z : ℝ => log (log z / (log (log z)) ^ 2)) atTop atTop :=
    tendsto_log_atTop.comp hwT
  have hw4T : Tendsto (fun z : ℝ => (log z / (log (log z)) ^ 2) ^ ((1 : ℝ) / 4)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hwT
  have ho_w : (fun w : ℝ => (log w) ^ 2) =o[atTop] (fun w : ℝ => w ^ ((1 : ℝ) / 4)) := by
    simpa only [rpow_ofNat] using isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 1 / 4) (by norm_num)
  have hρK : 0 < 2 * ρ * K := by positivity
  have hw_gap : ∀ᶠ w : ℝ in atTop, 2 * ρ * K * (log w) ^ 2 < w ^ ((1 : ℝ) / 4) := by
    filter_upwards [ho_w.bound (show (0 : ℝ) < 1 / (4 * ρ * K) by positivity),
      eventually_gt_atTop (1 : ℝ)] with w hw h1
    have hlog0 : 0 ≤ (log w) ^ 2 := sq_nonneg (log w)
    have hp4 : 0 < w ^ ((1 : ℝ) / 4) := rpow_pos_of_pos (zero_lt_one.trans h1) _
    rw [norm_eq_abs, norm_eq_abs, abs_of_nonneg hlog0, abs_of_pos hp4] at hw
    have hlt : 1 / (4 * ρ * K) < 1 / (2 * ρ * K) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    have hm := mul_lt_mul_of_pos_left
      (lt_of_le_of_lt hw (mul_lt_mul_of_pos_right hlt hp4)) hρK
    have hsimp : 2 * ρ * K * (1 / (2 * ρ * K) * w ^ ((1 : ℝ) / 4)) = w ^ ((1 : ℝ) / 4) := by
      field_simp [hρK.ne']
    linarith
  have ho_L : (fun L : ℝ => (log L) ^ 2) =o[atTop] (fun L : ℝ => L ^ ((1 : ℝ) / 2)) := by
    simpa only [rpow_ofNat] using isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 1 / 2) (by norm_num)
  have hlogB_ev : ∀ᶠ L : ℝ in atTop,
      (log L) ^ 2 ≤ L ^ ((1 : ℝ) / 2) ∧ 1 < L ∧ 1 < log L := by
    filter_upwards [ho_L.bound (show (0 : ℝ) < 1 by norm_num),
      eventually_gt_atTop (exp 2)] with L hL hLe
    have hL0 : 0 < L := (exp_pos 2).trans hLe
    have hlogL : 2 < log L := by
      have := log_lt_log (exp_pos 2) hLe
      rwa [log_exp] at this
    have hbound : (log L) ^ 2 ≤ L ^ ((1 : ℝ) / 2) := by
      simpa only [norm_eq_abs, abs_of_nonneg (sq_nonneg (log L)),
        abs_of_pos (rpow_pos_of_pos hL0 _), one_mul] using hL
    exact ⟨hbound, (by linarith [add_one_le_exp (2 : ℝ)] : 1 < L), by linarith⟩
  have hz_over_log : ∀ᶠ z : ℝ in atTop, (1 + x) * log z < z ∧ (log z) ^ 2 ≤ z ^ 2 := by
    have hoz : (fun z : ℝ => log z) =o[atTop] (fun z : ℝ => z) := by
      simpa only [rpow_one] using isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hoz.bound (show (0 : ℝ) < 1 / (2 * (1 + x)) by positivity),
      eventually_gt_atTop (exp 1)] with z hz hze
    have hz0 : 0 < z := (exp_pos 1).trans hze
    have hlogz : 0 < log z := by
      have hlt := log_lt_log (exp_pos 1) hze
      rw [log_exp] at hlt
      linarith
    rw [norm_eq_abs, norm_eq_abs, abs_of_pos hlogz, abs_of_pos hz0] at hz
    have h1 : (1 + x) * log z < z := by
      have hmul := mul_le_mul_of_nonneg_left hz (show 0 ≤ 1 + x by linarith)
      have hsimp : (1 + x) * (1 / (2 * (1 + x)) * z) = z / 2 := by
        have hp : (1 + x : ℝ) ≠ 0 := by linarith
        field_simp [hp]
      linarith
    have h2 : log z ≤ z := (log_le_sub_one_of_pos hz0).trans (by linarith)
    exact ⟨h1, by nlinarith⟩
  let Mlog := max 1 (max (x / K) (max (100 * (2 * Clen * x + 2 + x) / K)
    (max (100 * (216 / 100) * x / K) (100 * (199 / 100) / K))))
  filter_upwards [hwT.eventually_gt_atTop (max 1 (max W (N : ℝ))),
    hlogwT.eventually_ge_atTop (max Mlog 1),
    hw4T.eventually_gt_atTop C,
    hwT.eventually hw_gap,
    tendsto_log_atTop.eventually hlogB_ev,
    hz_over_log] with z hw_gt hlogw_ge hw4C hwgap hLB hzlog
  dsimp only
  set L := log z
  set Y := ⌊z ^ 2 / L ^ 2⌋₊
  set w := L / (log L) ^ 2
  set B := L / log w
  have hw1 : 1 < w := (le_max_left _ _).trans_lt hw_gt
  have hwW : W ≤ w := ((le_max_left _ _).trans (le_max_right _ _)).trans hw_gt.le
  have hwN : (N : ℝ) ≤ w := ((le_max_right _ _).trans (le_max_right _ _)).trans hw_gt.le
  have hw0 : 0 < w := zero_lt_one.trans hw1
  have hlogw1 : 1 ≤ log w := (le_max_right _ _).trans hlogw_ge
  have hlogwM : Mlog ≤ log w := (le_max_left _ _).trans hlogw_ge
  have hlogw0 : 0 < log w := by linarith
  have hL1 : 1 < L := hLB.2.1
  have hL0 : 0 < L := zero_lt_one.trans hL1
  have hlogL1 : 1 < log L := hLB.2.2
  have hw_le_L : w ≤ L := div_le_self hL0.le (by nlinarith)
  have hwz : w < z := by
    have h1 : L < (1 + x) * L := by nlinarith
    exact hw_le_L.trans_lt (h1.trans hzlog.1)
  have hYpos : 0 < Y := Nat.floor_pos.mpr ((one_le_div (sq_pos_of_pos hL0)).mpr hzlog.2)
  have hspan : log (1 + x) ≤ log (z / w) := by
    refine log_le_log (by linarith) ?_
    rw [le_div_iff₀ hw0]
    exact (mul_le_mul_of_nonneg_left hw_le_L (by linarith)).trans hzlog.1.le
  have hlogB : log B ≤ 2 * log w := by
    have hBL : B ≤ L := div_le_self hL0.le hlogw1
    have hB0 : 0 < B := div_pos hL0 hlogw0
    have hLhalf_le_w : L ^ ((1 : ℝ) / 2) ≤ w := by
      have hsq : 0 < (log L) ^ 2 := sq_pos_of_pos (by linarith)
      rw [le_div_iff₀ hsq]
      have hmul : L ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2) = L := by
        rw [← rpow_add hL0]; norm_num
      nlinarith [rpow_pos_of_pos hL0 ((1 : ℝ) / 2), hLB.1]
    have hlog_half : log (L ^ ((1 : ℝ) / 2)) ≤ log w :=
      log_le_log (rpow_pos_of_pos hL0 _) hLhalf_le_w
    rw [log_rpow hL0] at hlog_half
    have hlogBL : log B ≤ log L := log_le_log hB0 hBL
    linarith
  have hlogw_sq_ge : log w ≤ (log w) ^ 2 := by nlinarith
  have hKlogw2 : 0 < K * (log w) ^ 2 := by positivity
  have hx_over_logw : x / log w ≤ x := div_le_self hx.le hlogw1
  have hc1 : x / log w ≤ K * (log w) ^ 2 := by
    have hm : x / K ≤ log w := ((le_max_left _ _).trans (le_max_right _ _)).trans hlogwM
    have h1 : x ≤ log w * K := (div_le_iff₀ hK).mp hm
    have h2 : K * log w ≤ K * (log w) ^ 2 := mul_le_mul_of_nonneg_left hlogw_sq_ge hK.le
    linarith
  have hc2 : (2 * Clen * x + 2 + x / log w) / (K * (log w) ^ 2) ≤ 1 / 100 := by
    have hm : 100 * (2 * Clen * x + 2 + x) / K ≤ log w :=
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hlogwM
    have h1 : 100 * (2 * Clen * x + 2 + x) ≤ log w * K := (div_le_iff₀ hK).mp hm
    have h2 : K * log w ≤ K * (log w) ^ 2 := mul_le_mul_of_nonneg_left hlogw_sq_ge hK.le
    rw [div_le_iff₀ hKlogw2]
    linarith
  have hc3 : (216 / 100) * (x / log w) / (K * (log w) ^ 2) ≤ 1 / 100 := by
    have hm : 100 * (216 / 100) * x / K ≤ log w :=
      ((le_max_left _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))).trans hlogwM
    have h1 : 100 * (216 / 100) * x ≤ log w * K := (div_le_iff₀ hK).mp hm
    have h2 : K * log w ≤ K * (log w) ^ 2 := mul_le_mul_of_nonneg_left hlogw_sq_ge hK.le
    rw [div_le_iff₀ hKlogw2]
    nlinarith
  have hc4 : (199 / 100) / (K * (log w) ^ 2) ≤ 1 / 100 := by
    have hm : 100 * (199 / 100) / K ≤ log w :=
      ((le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _)))).trans hlogwM
    have h1 : 100 * (199 / 100) ≤ log w * K := (div_le_iff₀ hK).mp hm
    have h2 : K * log w ≤ K * (log w) ^ 2 := mul_le_mul_of_nonneg_left hlogw_sq_ge hK.le
    rw [div_le_iff₀ hKlogw2]
    linarith
  exact ⟨hw1, hwW, hwN, hwz, hYpos, hspan, hlogB, hwgap, hw4C, hc1, hc2, hc3, hc4⟩

private lemma swap_order_iso {u : Finset ℕ} {p₀ p' : ℕ} {lab : ℕ → ℕ} {lo : ℕ → ℝ}
    (hp₀ : p₀ ∈ u)
    (hlo_mono : ∀ i j : ℕ, i < j → lo i < lo j)
    (hbounds : ∀ q ∈ u, lo (lab q) < (q : ℝ) ∧ (q : ℝ) ≤ lo (lab q + 1))
    (hp'_lab : lab p' = lab p₀)
    (hp'_bounds : lo (lab p₀) < (p' : ℝ) ∧ (p' : ℝ) ≤ lo (lab p₀ + 1))
    (hsingle : (u.filter (fun q => lab q = lab p₀)).card = 1) :
    let φ := fun q : ℕ => if q = p₀ then p' else q
    (∀ q ∈ u, q ≠ p₀ → lab q ≠ lab p₀) ∧
    p' ∉ u.erase p₀ ∧
    u.image φ = insert p' (u.erase p₀) ∧
    (∀ x ∈ u, ∀ y ∈ u, x < y ↔ φ x < φ y) ∧
    (∀ x ∈ u, lab (φ x) = lab x) ∧
    (∀ x ∈ u, (u.image φ).filter (φ x ≤ ·) = (u.filter (x ≤ ·)).image φ) ∧
    Set.InjOn φ u := by
  intro φ
  have hne_lab : ∀ q ∈ u, q ≠ p₀ → lab q ≠ lab p₀ := by
    intro q hqu hqne hlab
    have hsub : ({p₀, q} : Finset ℕ) ⊆ u.filter (fun r => lab r = lab p₀) := by
      intro r hr
      rcases mem_insert.mp hr with rfl | hr
      · exact mem_filter.mpr ⟨hp₀, rfl⟩
      · rw [mem_singleton.mp hr]
        exact mem_filter.mpr ⟨hqu, hlab⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_pair hqne.symm, hsingle] at hcard
    omega
  have hp'_not_erase : p' ∉ u.erase p₀ := by
    intro hm
    exact hne_lab p' (mem_erase.mp hm).2 (mem_erase.mp hm).1 hp'_lab
  have himg : u.image φ = insert p' (u.erase p₀) := by
    ext x
    simp only [mem_image, mem_insert, mem_erase, φ]
    constructor
    · rintro ⟨q, hq, rfl⟩
      by_cases h : q = p₀
      · left; simp [h]
      · right; simp [h, hq]
    · rintro (rfl | ⟨hne, hxu⟩)
      · exact ⟨p₀, hp₀, by simp⟩
      · exact ⟨x, hxu, by simp [hne]⟩
  have hord : ∀ x ∈ u, ∀ y ∈ u, x < y ↔ φ x < φ y := by
    have hlt_lab : ∀ q ∈ u, q ≠ p₀ → (p₀ < q → lab p₀ < lab q) ∧ (q < p₀ → lab q < lab p₀) := by
      intro q hq hqne
      have hqlab := hne_lab q hq hqne
      constructor
      · intro hlt
        by_contra hge
        have hle : lab q + 1 ≤ lab p₀ := by omega
        have h1 : lo (lab q + 1) ≤ lo (lab p₀) := by
          rcases eq_or_lt_of_le hle with heq | hlt'
          · rw [heq]
          · exact (hlo_mono _ _ hlt').le
        have hltR : (p₀ : ℝ) < (q : ℝ) := by exact_mod_cast hlt
        linarith [(hbounds q hq).2, (hbounds p₀ hp₀).1]
      · intro hlt
        by_contra hge
        have hle : lab p₀ + 1 ≤ lab q := by omega
        have h1 : lo (lab p₀ + 1) ≤ lo (lab q) := by
          rcases eq_or_lt_of_le hle with heq | hlt'
          · rw [heq]
          · exact (hlo_mono _ _ hlt').le
        have hltR : (q : ℝ) < (p₀ : ℝ) := by exact_mod_cast hlt
        linarith [(hbounds p₀ hp₀).2, (hbounds q hq).1]
    have hlt_of_lab : ∀ q ∈ u, q ≠ p₀ → (lab p₀ < lab q → p' < q) ∧ (lab q < lab p₀ → q < p') := by
      intro q hq hqne
      constructor
      · intro hlt
        have hle : lab p₀ + 1 ≤ lab q := by omega
        have h1 : lo (lab p₀ + 1) ≤ lo (lab q) := by
          rcases eq_or_lt_of_le hle with heq | hlt'
          · rw [heq]
          · exact (hlo_mono _ _ hlt').le
        have hltR : (p' : ℝ) < (q : ℝ) := by linarith [hp'_bounds.2, (hbounds q hq).1]
        exact_mod_cast hltR
      · intro hlt
        have hle : lab q + 1 ≤ lab p₀ := by omega
        have h1 : lo (lab q + 1) ≤ lo (lab p₀) := by
          rcases eq_or_lt_of_le hle with heq | hlt'
          · rw [heq]
          · exact (hlo_mono _ _ hlt').le
        have hltR : (q : ℝ) < (p' : ℝ) := by linarith [hp'_bounds.1, (hbounds q hq).2]
        exact_mod_cast hltR
    intro x hx y hy
    dsimp only [φ]
    by_cases hxp : x = p₀
    · rw [hxp]
      by_cases hyp : y = p₀
      · rw [hyp]; simp
      · rw [if_pos rfl, if_neg hyp]
        constructor
        · intro hlt
          exact (hlt_of_lab y hy hyp).1 ((hlt_lab y hy hyp).1 hlt)
        · intro hlt
          rcases lt_trichotomy p₀ y with h | heq | h
          · exact h
          · exact False.elim (hyp heq.symm)
          · have := (hlt_of_lab y hy hyp).2 ((hlt_lab y hy hyp).2 h)
            omega
    · by_cases hyp : y = p₀
      · rw [hyp, if_neg hxp, if_pos rfl]
        constructor
        · intro hlt
          exact (hlt_of_lab x hx hxp).2 ((hlt_lab x hx hxp).2 hlt)
        · intro hlt
          rcases lt_trichotomy x p₀ with h | heq | h
          · exact h
          · exact False.elim (hxp heq)
          · have := (hlt_of_lab x hx hxp).1 ((hlt_lab x hx hxp).1 h)
            omega
      · rw [if_neg hxp, if_neg hyp]
  have hinj : Set.InjOn φ u := by
    intro x hx y hy hxy
    rcases lt_trichotomy x y with h | h | h
    · have := (hord x hx y hy).mp h; omega
    · exact h
    · have := (hord y hy x hx).mp h; omega
  have hlab_pres : ∀ x ∈ u, lab (φ x) = lab x := by
    intro x _
    dsimp only [φ]
    split_ifs with h
    · rw [h, hp'_lab]
    · rfl
  have hfilt : ∀ x ∈ u, (u.image φ).filter (φ x ≤ ·) = (u.filter (x ≤ ·)).image φ := by
    intro x hx
    ext y
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨⟨q, hq, rfl⟩, hle⟩
      refine ⟨q, ⟨hq, ?_⟩, rfl⟩
      by_contra hlt
      have := (hord q hq x hx).mp (by omega)
      omega
    · rintro ⟨q, ⟨hq, hle⟩, rfl⟩
      refine ⟨⟨q, hq, rfl⟩, ?_⟩
      rcases eq_or_lt_of_le hle with rfl | hlt
      · exact le_rfl
      · exact ((hord x hx q hq).mp hlt).le
  exact ⟨hne_lab, hp'_not_erase, himg, hord, hlab_pres, hfilt, hinj⟩

private lemma band_window_transfer
    {w x Clen K δl t s uval gr_u g_u e_m rep_m : ℝ} {Y p₀ q m : ℕ}
    (hx : 0 < x) (hlogw : 0 < log w) (hδx : δl ≤ x) (ht_def : t = exp δl - 1)
    (hs0 : 0 < s) (hY0 : (0 : ℝ) < (Y : ℝ)) (hp₀0 : (0 : ℝ) < (p₀ : ℝ))
    (hq0 : (0 : ℝ) < (q : ℝ)) (_hm_pos : (0 : ℝ) < (m : ℝ))
    (huval : uval ∈ Set.Icc s ((1 + t) * s))
    (hp₀_lo : s ≤ (p₀ : ℝ)) (hp₀_hi : (p₀ : ℝ) ≤ (1 + t) * s)
    (hg_def : g_u = log ((Y : ℝ) / ((p₀ : ℝ) * (q : ℝ))) / log w + 2 - 1 / 100)
    (he_def : e_m = log (m : ℝ) / log w)
    (hgu_gr_lo : 0 ≤ g_u - gr_u) (hgu_gr_hi : g_u - gr_u ≤ 2 * Clen * x)
    (hrepm_ge : e_m ≤ rep_m) (hrepm_diff : rep_m - e_m ≤ x / log w)
    (hem_lo : K * (log w) ^ 2 ≤ e_m) (hK : 0 < K)
    (hwin_lo : 206 / 100 ≤ gr_u / rep_m) (hwin_hi : gr_u / rep_m ≤ 216 / 100)
    (hxc2 : (2 * Clen * x + 2 + x / log w) / (K * (log w) ^ 2) ≤ 1 / 100)
    (hxc3 : (216 / 100) * (x / log w) / (K * (log w) ^ 2) ≤ 1 / 100)
    (hClen : 1 ≤ Clen) (ht_ge0 : 0 ≤ t) :
    log ((Y : ℝ) / (uval * (q : ℝ))) / log (m : ℝ) ∈ Set.Icc (203 / 100) (219 / 100) := by
  have huval0 : 0 < uval := hs0.trans_le huval.1
  have h1t : 0 < 1 + t := by linarith only [ht_ge0]
  have hup : (p₀ : ℝ) / uval ≤ 1 + t := by
    rw [div_le_iff₀ huval0]
    exact hp₀_hi.trans (mul_le_mul_of_nonneg_left huval.1 h1t.le)
  have hlo : (1 + t)⁻¹ ≤ (p₀ : ℝ) / uval := by
    rw [le_div_iff₀ huval0]
    have hmul := mul_le_mul_of_nonneg_left huval.2 (inv_nonneg.mpr h1t.le)
    have hsimp : (1 + t)⁻¹ * ((1 + t) * s) = s := by field_simp [h1t.ne']
    linarith only [hmul, hsimp, hp₀_lo]
  have hlog1t : log (1 + t) ≤ x := by
    rw [ht_def, show (1 + (exp δl - 1) : ℝ) = exp δl by ring, log_exp]
    exact hδx
  have hratio : |log ((p₀ : ℝ) / uval)| ≤ x := by
    rw [abs_le]
    constructor
    · have h := log_le_log (inv_pos.mpr h1t) hlo; rw [log_inv] at h; linarith only [h, hlog1t]
    · exact (log_le_log (div_pos hp₀0 huval0) hup).trans hlog1t
  have hlog_split : log ((Y : ℝ) / (uval * (q : ℝ))) / log w =
      (g_u - (2 - 1 / 100)) + log ((p₀ : ℝ) / uval) / log w := by
    rw [hg_def]
    have hprod_eq : (Y : ℝ) / (uval * (q : ℝ)) =
        ((Y : ℝ) / ((p₀ : ℝ) * (q : ℝ))) * ((p₀ : ℝ) / uval) := by
      field_simp [huval0.ne', hq0.ne', hp₀0.ne']
    rw [hprod_eq, log_mul (div_pos hY0 (mul_pos hp₀0 hq0)).ne' (div_pos hp₀0 huval0).ne', add_div]
    ring
  have hnum_diff : |log ((Y : ℝ) / (uval * (q : ℝ))) / log w - gr_u| ≤ 2 * Clen * x + 2 + x / log w := by
    rw [hlog_split]
    have h1 : (g_u - (2 - 1 / 100)) + log ((p₀ : ℝ) / uval) / log w - gr_u =
        (g_u - gr_u) - (2 - 1 / 100) + log ((p₀ : ℝ) / uval) / log w := by ring
    rw [h1]
    have h2 : |log ((p₀ : ℝ) / uval) / log w| ≤ x / log w := by
      rw [abs_div, abs_of_pos hlogw]
      exact div_le_div_of_nonneg_right hratio hlogw.le
    have h3 := abs_le.mp h2
    rw [abs_le]
    constructor <;> linarith only [h3.1, h3.2, hgu_gr_lo, hgu_gr_hi]
  have hKlogw2 : 0 < K * (log w) ^ 2 := by positivity
  have hem_pos : 0 < e_m := hKlogw2.trans_le hem_lo
  have hrepm_pos : 0 < rep_m := hem_pos.trans_le hrepm_ge
  have hquot_eq : log ((Y : ℝ) / (uval * (q : ℝ))) / log (m : ℝ) =
      (log ((Y : ℝ) / (uval * (q : ℝ))) / log w) / e_m := by
    rw [he_def]; field_simp [hlogw.ne']
  have hdiff_id : (log ((Y : ℝ) / (uval * (q : ℝ))) / log w) / e_m - gr_u / rep_m =
      (log ((Y : ℝ) / (uval * (q : ℝ))) / log w - gr_u) / e_m +
      (gr_u / rep_m) * ((rep_m - e_m) / e_m) := by
    field_simp [hem_pos.ne', hrepm_pos.ne']; ring
  have herr1 : |(log ((Y : ℝ) / (uval * (q : ℝ))) / log w - gr_u) / e_m| ≤ 1 / 100 := by
    rw [abs_div, abs_of_pos hem_pos]
    have hnn : 0 ≤ 2 * Clen * x + 2 + x / log w := by positivity
    exact (div_le_div_of_nonneg_right hnum_diff hem_pos.le).trans
      ((div_le_div_of_nonneg_left hnn hKlogw2 hem_lo).trans hxc2)
  have herr2_lo : 0 ≤ (gr_u / rep_m) * ((rep_m - e_m) / e_m) :=
    mul_nonneg (by linarith only [hwin_lo]) (div_nonneg (sub_nonneg.mpr hrepm_ge) hem_pos.le)
  have herr2_hi : (gr_u / rep_m) * ((rep_m - e_m) / e_m) ≤ 1 / 100 := by
    have h1 : (gr_u / rep_m) * ((rep_m - e_m) / e_m) ≤ (216 / 100) * ((x / log w) / e_m) :=
      mul_le_mul hwin_hi (div_le_div_of_nonneg_right hrepm_diff hem_pos.le)
        (div_nonneg (sub_nonneg.mpr hrepm_ge) hem_pos.le) (by norm_num)
    have h2 : (216 / 100) * ((x / log w) / e_m) = (216 / 100) * (x / log w) / e_m := by ring
    rw [h2] at h1
    exact h1.trans ((div_le_div_of_nonneg_left (by positivity) hKlogw2 hem_lo).trans hxc3)
  rw [hquot_eq]
  have h1 := abs_le.mp herr1
  exact ⟨by linarith only [h1.1, hdiff_id, hwin_lo, herr2_lo],
    by linarith only [h1.2, hdiff_id, hwin_hi, herr2_hi]⟩

private lemma replacement_S_iff
    {u v : Finset ℕ} {p₀ p' : ℕ} {r : ℚ}
    {Clen B x K ρ logw : ℝ}
    {lab : ℕ → ℕ} {rep : ℕ → ℝ} {gr : Finset ℕ → ℝ}
    {tg : ℕ → ℚ → Prop} {al : ℚ → ℕ → Prop}
    (hv : v ⊆ u) (hp₀ : p₀ ∈ u)
    (φ : ℕ → ℕ) (hφ_p₀ : φ p₀ = p') (hφ_ne : ∀ y ∈ u, y ≠ p₀ → φ y = y)
    (hord : ∀ x ∈ u, ∀ y ∈ u, x < y ↔ φ x < φ y)
    (hinj : Set.InjOn φ u)
    (hlab_pres : ∀ y ∈ u, lab (φ y) = lab y)
    (hrep_pres : ∀ y ∈ u, rep (φ y) = rep y)
    (hgr_pres : ∀ s ⊆ u, gr (s.image φ) = gr s)
    (htg_uniq : ∀ {p : ℕ} {r₁ r₂ : ℚ}, tg p r₁ → tg p r₂ → r₁ = r₂)
    (htg₀ : tg p₀ r) (htg_p' : tg p' r)
    (hfirst₀ : ∀ q ∈ u, p₀ < q → ∀ r', ¬ tg q r')
    (hal_p₀ : al r p₀) (hal_p' : al r p') (hp'lab : lab p' = lab p₀) :
    let S := fun s : Finset ℕ => s.Nonempty ∧ Even s.card ∧ (s.card : ℝ) ≤ Clen * log B ∧
      (∀ p ∈ s, Even (s.filter (p ≤ ·)).card → max (2 * rep p) (rep p + 2) + 6 * Clen * x ≤ gr (s.filter (p ≤ ·))) ∧
      (∀ m ∈ s, (∀ q ∈ s, m ≤ q) → 2 * K * logw ^ 2 ≤ rep m ∧ rep m ≤ 2 * ρ * K * logw ^ 2 ∧
        206 / 100 ≤ gr s / rep m ∧ gr s / rep m ≤ 216 / 100) ∧
      (∃ p ∈ s, ∃ r₁ : ℚ, tg p r₁ ∧ (∀ q ∈ s, p < q → ∀ r', ¬ tg q r') ∧
        (s.filter (fun q => lab q = lab p)).card = 1 ∧ ∀ q ∈ s, al r₁ q)
    S (v.image φ) ↔ S v := by
  intro S
  have hfirst_uniq : ∀ {s : Finset ℕ} {p₁ p₂ : ℕ} {r₁ r₂ : ℚ},
      p₁ ∈ s → tg p₁ r₁ → (∀ q ∈ s, p₁ < q → ∀ r', ¬ tg q r') →
      p₂ ∈ s → tg p₂ r₂ → (∀ q ∈ s, p₂ < q → ∀ r', ¬ tg q r') →
      p₁ = p₂ ∧ r₁ = r₂ := by
    intro s p₁ p₂ r₁ r₂ hp₁ ht₁ hf₁ hp₂ ht₂ hf₂
    rcases lt_trichotomy p₁ p₂ with h | rfl | h
    · exact False.elim (hf₁ p₂ hp₂ h r₂ ht₂)
    · exact ⟨rfl, htg_uniq ht₁ ht₂⟩
    · exact False.elim (hf₂ p₁ hp₁ h r₁ ht₁)
  have htg_iff : ∀ y ∈ u, ∀ r' : ℚ, tg (φ y) r' ↔ tg y r' := by
    intro y hy r'
    by_cases hy0 : y = p₀
    · rw [hy0, hφ_p₀]
      exact ⟨fun ht => (htg_uniq ht htg_p') ▸ htg₀, fun ht => (htg_uniq ht htg₀) ▸ htg_p'⟩
    · rw [hφ_ne y hy hy0]
  have hcard_v : (v.image φ).card = v.card := Finset.card_image_of_injOn (hinj.mono hv)
  have hne_v : (v.image φ).Nonempty ↔ v.Nonempty := Finset.image_nonempty
  have hfilt_v : ∀ y ∈ v, (v.image φ).filter (φ y ≤ ·) = (v.filter (y ≤ ·)).image φ := by
    intro y hy
    ext z
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨⟨a', ha', rfl⟩, hle⟩
      refine ⟨a', ⟨ha', ?_⟩, rfl⟩
      by_contra hlt
      have h1 := (hord a' (hv ha') y (hv hy)).mp (by omega)
      omega
    · rintro ⟨a', ⟨ha', hle⟩, rfl⟩
      refine ⟨⟨a', ha', rfl⟩, ?_⟩
      rcases eq_or_lt_of_le hle with rfl | hlt
      · exact le_rfl
      · exact ((hord y (hv hy) a' (hv ha')).mp hlt).le
  have hsafe_iff :
      (∀ y ∈ v.image φ, Even ((v.image φ).filter (y ≤ ·)).card →
        max (2 * rep y) (rep y + 2) + 6 * Clen * x ≤ gr ((v.image φ).filter (y ≤ ·))) ↔
      (∀ y ∈ v, Even (v.filter (y ≤ ·)).card →
        max (2 * rep y) (rep y + 2) + 6 * Clen * x ≤ gr (v.filter (y ≤ ·))) := by
    constructor
    · intro h y hy hEven
      have h1 := h (φ y) (mem_image_of_mem φ hy)
      rw [hfilt_v y hy, Finset.card_image_of_injOn (hinj.mono ((filter_subset _ _).trans hv)),
        hrep_pres y (hv hy), hgr_pres _ ((filter_subset _ _).trans hv)] at h1
      exact h1 hEven
    · intro h y hy hEven
      obtain ⟨a', ha', rfl⟩ := mem_image.mp hy
      rw [hfilt_v a' ha', Finset.card_image_of_injOn (hinj.mono ((filter_subset _ _).trans hv))] at hEven
      rw [hfilt_v a' ha', hrep_pres a' (hv ha'), hgr_pres _ ((filter_subset _ _).trans hv)]
      exact h a' ha' hEven
  have hwin_iff :
      (∀ m' ∈ v.image φ, (∀ y ∈ v.image φ, m' ≤ y) →
        2 * K * logw ^ 2 ≤ rep m' ∧ rep m' ≤ 2 * ρ * K * logw ^ 2 ∧
        206 / 100 ≤ gr (v.image φ) / rep m' ∧ gr (v.image φ) / rep m' ≤ 216 / 100) ↔
      (∀ m' ∈ v, (∀ y ∈ v, m' ≤ y) →
        2 * K * logw ^ 2 ≤ rep m' ∧ rep m' ≤ 2 * ρ * K * logw ^ 2 ∧
        206 / 100 ≤ gr v / rep m' ∧ gr v / rep m' ≤ 216 / 100) := by
    constructor
    · intro h m' hm' hle
      have hle' : ∀ y ∈ v.image φ, φ m' ≤ y := by
        intro y hy
        obtain ⟨a', ha', rfl⟩ := mem_image.mp hy
        rcases eq_or_lt_of_le (hle a' ha') with rfl | hlt
        · exact le_rfl
        · exact ((hord m' (hv hm') a' (hv ha')).mp hlt).le
      have h1 := h (φ m') (mem_image_of_mem φ hm') hle'
      rwa [hrep_pres m' (hv hm'), hgr_pres v hv] at h1
    · intro h m' hm' hle
      obtain ⟨a', ha', rfl⟩ := mem_image.mp hm'
      have hle' : ∀ y ∈ v, a' ≤ y := by
        intro y hy
        by_contra hlt
        have h1 := (hord y (hv hy) a' (hv ha')).mp (by omega)
        have h2 := hle (φ y) (mem_image_of_mem φ hy)
        omega
      rw [hrep_pres a' (hv ha'), hgr_pres v hv]
      exact h a' ha' hle'
  have htag_iff :
      (∃ p ∈ v.image φ, ∃ r₁ : ℚ, tg p r₁ ∧ (∀ y ∈ v.image φ, p < y → ∀ r', ¬ tg y r') ∧
        ((v.image φ).filter (fun y => lab y = lab p)).card = 1 ∧ ∀ y ∈ v.image φ, al r₁ y) ↔
      (∃ p ∈ v, ∃ r₁ : ℚ, tg p r₁ ∧ (∀ y ∈ v, p < y → ∀ r', ¬ tg y r') ∧
        (v.filter (fun y => lab y = lab p)).card = 1 ∧ ∀ y ∈ v, al r₁ y) := by
    by_cases hp₀v : p₀ ∈ v
    · have hφ_p'v : p' ∈ v.image φ := hφ_p₀ ▸ mem_image_of_mem φ hp₀v
      have hfirst_v : ∀ y ∈ v, p₀ < y → ∀ r', ¬ tg y r' :=
        fun y hy hlt r' => hfirst₀ y (hv hy) hlt r'
      have hfirst_v' : ∀ y ∈ v.image φ, p' < y → ∀ r', ¬ tg y r' := by
        intro y hy hlt r'
        obtain ⟨a', ha', rfl⟩ := mem_image.mp hy
        have hlt' : p₀ < a' := (hord p₀ hp₀ a' (hv ha')).mpr (by rw [hφ_p₀]; exact hlt)
        exact (htg_iff a' (hv ha') r').not.mpr (hfirst_v a' ha' hlt' r')
      have hcard_lab_eq : ((v.image φ).filter (fun y => lab y = lab p')).card =
          (v.filter (fun y => lab y = lab p₀)).card := by
        have hfeq : (v.image φ).filter (fun y => lab y = lab p') =
            (v.filter (fun y => lab y = lab p₀)).image φ := by
          ext z
          simp only [mem_filter, mem_image]
          constructor
          · rintro ⟨⟨a', ha', rfl⟩, hlab⟩
            exact ⟨a', ⟨ha', by rw [← hlab_pres a' (hv ha'), hlab, hp'lab]⟩, rfl⟩
          · rintro ⟨a', ⟨ha', hlab⟩, rfl⟩
            exact ⟨⟨a', ha', rfl⟩, by rw [hlab_pres a' (hv ha'), hlab, hp'lab]⟩
        rw [hfeq, Finset.card_image_of_injOn (hinj.mono ((filter_subset _ _).trans hv))]
      constructor
      · rintro ⟨p₁, hp₁, r₁, htg₁, hfr₁, hsc₁, hal₁⟩
        obtain ⟨hp_eq, hr_eq⟩ := hfirst_uniq hp₁ htg₁ hfr₁ hφ_p'v htg_p' hfirst_v'
        rw [hp_eq] at hsc₁; rw [hr_eq] at hal₁
        refine ⟨p₀, hp₀v, r, htg₀, hfirst_v, hcard_lab_eq ▸ hsc₁, ?_⟩
        intro y hy
        by_cases hy0 : y = p₀
        · rw [hy0]; exact hal_p₀
        · have := hal₁ (φ y) (mem_image_of_mem φ hy)
          rwa [hφ_ne y (hv hy) hy0] at this
      · rintro ⟨p₁, hp₁, r₁, htg₁, hfr₁, hsc₁, hal₁⟩
        obtain ⟨hp_eq, hr_eq⟩ := hfirst_uniq hp₁ htg₁ hfr₁ hp₀v htg₀ hfirst_v
        rw [hp_eq] at hsc₁; rw [hr_eq] at hal₁
        refine ⟨p', hφ_p'v, r, htg_p', hfirst_v', hcard_lab_eq.trans hsc₁, ?_⟩
        intro y hy
        obtain ⟨a', ha', rfl⟩ := mem_image.mp hy
        by_cases ha0 : a' = p₀
        · rw [ha0, hφ_p₀]; exact hal_p'
        · rw [hφ_ne a' (hv ha') ha0]; exact hal₁ a' ha'
    · have hid : v.image φ = v := by
        ext y
        simp only [mem_image]
        constructor
        · rintro ⟨a', ha', rfl⟩
          rw [hφ_ne a' (hv ha') (fun h => hp₀v (h ▸ ha'))]; exact ha'
        · intro hy
          exact ⟨y, hy, hφ_ne y (hv hy) (fun h => hp₀v (h ▸ hy))⟩
      rw [hid]
  dsimp only [S]
  rw [hne_v, hcard_v, hsafe_iff, hwin_iff, htag_iff]

private lemma fixed_scale_transfer
    {Clen C d K ρ x W z : ℝ} {N : ℕ}
    (hClen : 1 ≤ Clen) (hK : 0 < K) (_hρ : 1 < ρ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hw1 : 1 < log z / (log (log z)) ^ 2)
    (hwW : W ≤ log z / (log (log z)) ^ 2)
    (hwN : (N : ℝ) ≤ log z / (log (log z)) ^ 2)
    (hwz : log z / (log (log z)) ^ 2 < z)
    (hYpos : 0 < ⌊z ^ 2 / (log z) ^ 2⌋₊)
    (hspan : log (1 + x) ≤ log (z / (log z / (log (log z)) ^ 2)))
    (hlogB : log (log z / log (log z / (log (log z)) ^ 2)) ≤ 2 * log (log z / (log (log z)) ^ 2))
    (hwgap : 2 * ρ * K * (log (log z / (log (log z)) ^ 2)) ^ 2 < (log z / (log (log z)) ^ 2) ^ ((1 : ℝ) / 4))
    (hw4C : C < (log z / (log (log z)) ^ 2) ^ ((1 : ℝ) / 4))
    (hxc1 : x / log (log z / (log (log z)) ^ 2) ≤ K * (log (log z / (log (log z)) ^ 2)) ^ 2)
    (hxc2 : (2 * Clen * x + 2 + x / log (log z / (log (log z)) ^ 2)) /
      (K * (log (log z / (log (log z)) ^ 2)) ^ 2) ≤ 1 / 100)
    (hxc3 : (216 / 100) * (x / log (log z / (log (log z)) ^ 2)) /
      (K * (log (log z / (log (log z)) ^ 2)) ^ 2) ≤ 1 / 100)
    (hxc4 : (199 / 100) / (K * (log (log z / (log (log z)) ^ 2)) ^ 2) ≤ 1 / 100)
    (a : ℕ → ℕ)
    (hzRef :
      let L := log z; let Y := ⌊z ^ 2 / L ^ 2⌋₊; let w := L / (log L) ^ 2
      let P := (Icc (⌊w⌋₊ + 1) ⌊z⌋₊).filter Nat.Prime
      let Q := (range (⌊w⌋₊ + 1)).filter Nat.Prime
      let v := fun S : Finset ℕ => ∏ p ∈ S, (1 - (p : ℝ)⁻¹)
      let μ := Y * v Q; let D := fun d : Finset ℕ => ∏ p ∈ d, (p : ℝ)
      let g := fun d => log (Y / D d) / log w + 2 - 1 / 100; let e := fun p : ℕ => log p / log w
      let T := P.powerset.filter fun d => ∀ p ∈ d, let A := d.filter (p ≤ ·)
        Even A.card → max (2 * e p) (e p + 2) ≤ g A
      let I := fun u d : Finset ℕ => u ⊆ d ∧ ∀ p ∈ u, ∀ q ∈ d \ u, q < p
      ∀ u ∈ T, ∀ hu : u.Nonempty, Even u.card →
        let m := u.min' hu
        exp (K * (log w) ^ 3) ≤ m → (m : ℝ) ≤ exp ((2 * ρ) * K * (log w) ^ 3) →
        2 ≤ g u / e m → g u / e m ≤ 11 / 5 →
        μ * (∑ d ∈ T.filter (I u), (-1 : ℝ) ^ d.card / D d) ≤
          (33 / 100 * v (Nat.primesLE m)) * ((Y : ℝ) / D u))
    {k ε δ : ℝ}
    (hzMass :
      let L := log z; let Y := ⌊z ^ 2 / L ^ 2⌋₊; let w := L / (log L) ^ 2; let B := L / log w
      let Q := Nat.primesLE ⌊w⌋₊; let P := Nat.primesLE ⌊z⌋₊ \ Q
      let μ := Y * (∏ p ∈ Q, (1 - (p : ℝ)⁻¹)); let D := fun s : Finset ℕ => ∏ p ∈ s, (p : ℝ)
      let g := fun s => log (Y / D s) / log w + 2 - 1 / 100; let e := fun p : ℕ => log p / log w
      let T := P.powerset.filter fun s => ∀ p ∈ s, Even (s.filter (p ≤ ·)).card →
        max (2 * e p) (e p + 2) ≤ g (s.filter (p ≤ ·))
      let M := ⌈log (z / w) / log (1 + x)⌉₊; let δl := log (z / w) / (M : ℝ)
      let lo := fun i : ℕ => w * exp (i * δl); let lab := fun p : ℕ => min (M - 1) (⌈log ((p : ℝ) / w) / δl⌉₊ - 1)
      let rep := fun p : ℕ => 1 + ((lab p : ℝ) + 1) * δl / log w
      let gr := fun s : Finset ℕ => log Y / log w + 2 - 1 / 100 - ∑ p ∈ s, rep p
      let J := fun i : ℕ => Nat.primesLE ⌊w * exp ((i + 1) * δl)⌋₊ \ Nat.primesLE ⌊lo i⌋₊
      let al := fun (r : ℚ) (p : ℕ) => (r.den : ZMod p) * (a p : ZMod p) = (r.num : ZMod p)
      let own := fun (i : ℕ) (r : ℚ) => (r.den : ℝ) ≤ w ^ C ∧ |(r.num : ℝ)| ≤ Y * w ^ (C + 2) ∧
        (1 - d) * ((J i).card : ℝ) ≤ ((J i).filter (al r)).card
      let tg := fun (p : ℕ) (r : ℚ) => exp (w ^ ((1 : ℝ) / 4) * log w) ≤ lo (lab p) ∧
        own (lab p) r ∧ (∀ r', own (lab p) r' → r ≤ r') ∧ al r p
      let S := fun u : Finset ℕ => u.Nonempty ∧ Even u.card ∧ (u.card : ℝ) ≤ Clen * log B ∧
        (∀ p ∈ u, Even (u.filter (p ≤ ·)).card → max (2 * rep p) (rep p + 2) + 6 * Clen * x ≤ gr (u.filter (p ≤ ·))) ∧
        (∀ m ∈ u, (∀ q ∈ u, m ≤ q) → 2 * K * (log w) ^ 2 ≤ rep m ∧ rep m ≤ 2 * ρ * K * (log w) ^ 2 ∧
          206 / 100 ≤ gr u / rep m ∧ gr u / rep m ≤ 216 / 100) ∧
        (∃ p ∈ u, ∃ r : ℚ, tg p r ∧ (∀ q ∈ u, p < q → ∀ r', ¬ tg q r') ∧
          (u.filter (fun q => lab q = lab p)).card = 1 ∧ ∀ q ∈ u, al r q)
      let E := T.filter fun u => ∀ p ∈ u, ¬ S (u.filter (p ≤ ·))
      let A := E.filter fun u => g u ≤ k ∧ ε < |(((Icc 1 Y).filter (fun n =>
        (∀ p ∈ u, n ≡ a p [MOD p]) ∧ ∀ p ∈ Q, ¬ (n ≡ a p [MOD p]))).card : ℝ) / (μ / D u) - 1|
      B ^ 2 * (∑ u ∈ A, (D u)⁻¹) ≤ δ) :
    let L := log z; let Y := ⌊z ^ 2 / L ^ 2⌋₊; let w := L / (log L) ^ 2; let B := L / log w
    let P := (Icc (⌊w⌋₊ + 1) ⌊z⌋₊).filter Nat.Prime
    let Q := (range (⌊w⌋₊ + 1)).filter Nat.Prime
    let v := fun S : Finset ℕ => ∏ p ∈ S, (1 - (p : ℝ)⁻¹)
    let μ := Y * v Q; let D := fun d : Finset ℕ => ∏ p ∈ d, (p : ℝ)
    let g := fun d => log (Y / D d) / log w + 2 - 1 / 100; let e := fun p : ℕ => log p / log w
    let T := P.powerset.filter fun d => ∀ p ∈ d, let A := d.filter (p ≤ ·)
      Even A.card → max (2 * e p) (e p + 2) ≤ g A
    let Z := fun d S : Finset ℕ => (Icc 1 Y).filter fun n =>
      (∀ p ∈ d, n ≡ a p [MOD p]) ∧ ∀ p ∈ S, ¬ (n ≡ a p [MOD p])
    let I := fun u d : Finset ℕ => u ⊆ d ∧ ∀ p ∈ u, ∀ q ∈ d \ u, q < p
    (∃ F ⊆ T, (∀ u ∈ F, u.Nonempty ∧ Even u.card ∧ ∀ v ∈ F, I v u → v = u) ∧
      let E := T.filter fun d => ∀ u ∈ F, ¬ I u d
      let A := E.filter fun d => g d ≤ k ∧ ε < |(Z d Q).card / (μ / D d) - 1|
      B ^ 2 * (∑ u ∈ A, (D u)⁻¹) ≤ δ ∧
      μ * (∑ d ∈ T \ E, (-1 : ℝ) ^ d.card / D d) ≤
        ∑ u ∈ F, ((Z u (Q ∪ P.filter (fun p => ∀ q ∈ u, p < q))).card : ℝ)) ∨
    ∃ (m q : ℕ) (s t : ℝ) (r : ℚ),
      let J := Nat.primesLE ⌊(1 + t) * s⌋₊ \ Nat.primesLE ⌊s⌋₊
      let A := fun p : ℕ => (r.den : ZMod p) * (a p : ZMod p) = (r.num : ZMod p)
      let G := J.filter A
      let h := m.Prime ∧ N ≤ m ∧ exp (K * (log w) ^ 3) ≤ m ∧
        (m : ℝ) ≤ exp ((2 * ρ) * K * (log w) ^ 3) ∧ exp (w ^ ((1 : ℝ) / 4) * log w) ≤ s ∧
        x / 4 ≤ t ∧ t ≤ 1 ∧ 0 < Y ∧ 0 < q ∧ (r.den : ℝ) ≤ w ^ C ∧ |(r.num : ℝ)| ≤ Y * w ^ (C + 2) ∧
        (∀ u ∈ Set.Icc s ((1 + t) * s), log (Y / (u * q)) / log m ∈ Set.Icc (203 / 100) (219 / 100)) ∧
        (∀ u ∈ q.primeFactors, m ≤ u ∧ A u) ∧
        (∀ p ∈ J, m ≤ p ∧ Squarefree (p * q) ∧ r.den.Coprime p) ∧ (1 - d) * (J.card : ℝ) ≤ G.card
      W ≤ w ∧ h ∧ (∑ p ∈ G, ((Z (p * q).primeFactors ((range m).filter Nat.Prime)).card : ℝ)) <
        (33 / 100 * v (Nat.primesLE m)) * (∑ p ∈ G, (Y : ℝ) / ((p : ℝ) * q)) := by
  set L := log z
  set Y := ⌊z ^ 2 / L ^ 2⌋₊
  set w := L / (log L) ^ 2
  set B := L / log w
  set P := (Icc (⌊w⌋₊ + 1) ⌊z⌋₊).filter Nat.Prime
  set Q := (range (⌊w⌋₊ + 1)).filter Nat.Prime
  let v := fun S : Finset ℕ => ∏ p ∈ S, (1 - (p : ℝ)⁻¹)
  set μ := (Y : ℝ) * v Q
  let D := fun s : Finset ℕ => ∏ p ∈ s, (p : ℝ)
  let g := fun s : Finset ℕ => log ((Y : ℝ) / D s) / log w + 2 - 1 / 100
  let e := fun p : ℕ => log (p : ℝ) / log w
  let T := P.powerset.filter fun s => ∀ p ∈ s, Even (s.filter (p ≤ ·)).card →
    max (2 * e p) (e p + 2) ≤ g (s.filter (p ≤ ·))
  let I := fun u s : Finset ℕ => u ⊆ s ∧ ∀ p ∈ u, ∀ q ∈ s \ u, q < p
  let Z := fun u S : Finset ℕ => (Icc 1 Y).filter fun n =>
    (∀ p ∈ u, n ≡ a p [MOD p]) ∧ ∀ p ∈ S, ¬ (n ≡ a p [MOD p])
  have hQeq : Q = Nat.primesLE ⌊w⌋₊ := range_primes_eq ⌊w⌋₊
  have hPeq : P = Nat.primesLE ⌊z⌋₊ \ Nat.primesLE ⌊w⌋₊ := icc_primes_eq ⌊w⌋₊ ⌊z⌋₊
  have hw0 : 0 < w := zero_lt_one.trans hw1
  have hlogw : 0 < log w := log_pos hw1
  set M := ⌈log (z / w) / log (1 + x)⌉₊
  set δl := log (z / w) / (M : ℝ)
  set t := exp δl - 1
  let lo := fun i : ℕ => w * exp ((i : ℝ) * δl)
  let lab := fun p : ℕ => min (M - 1) (⌈log ((p : ℝ) / w) / δl⌉₊ - 1)
  let rep := fun p : ℕ => 1 + ((lab p : ℝ) + 1) * δl / log w
  let gr := fun s : Finset ℕ => log (Y : ℝ) / log w + 2 - 1 / 100 - ∑ p ∈ s, rep p
  let J := fun i : ℕ => Nat.primesLE ⌊w * exp (((i : ℝ) + 1) * δl)⌋₊ \ Nat.primesLE ⌊lo i⌋₊
  obtain ⟨_hMpos, _hδpos, _hδlog, hδx, ht_lo, ht_hi, _hlo0, _hloM, hlo_mono, hupper, hP_bin, hJ_bin⟩ :=
    log_bin_basic hw1 hwz hx hx1 hspan
  have hP_bin' : ∀ p ∈ P, lab p < M ∧ lo (lab p) < (p : ℝ) ∧
      (p : ℝ) ≤ w * exp (((lab p : ℝ) + 1) * δl) ∧ p ∈ J (lab p) ∧
      e p ≤ rep p ∧ rep p - e p ≤ x / log w := by
    intro p hp; rw [hPeq] at hp; exact hP_bin p hp
  have hJ_bin' : ∀ i < M, ∀ p ∈ J i, p ∈ P ∧ lab p = i ∧
      lo i < (p : ℝ) ∧ (p : ℝ) ≤ w * exp (((i : ℝ) + 1) * δl) := by
    intro i hi p hp; have h := hJ_bin i hi p hp; rw [← hPeq] at h; exact h
  have hlo_succ : ∀ i : ℕ, w * exp (((i : ℝ) + 1) * δl) = lo (i + 1) := by
    intro i; simp only [lo, Nat.cast_add, Nat.cast_one]
  have hP_prime : ∀ p ∈ P, p.Prime := fun p hp => (mem_filter.mp hp).2
  have hg_sub_gr : ∀ s ⊆ P, g s - gr s = ∑ p ∈ s, (rep p - e p) := by
    intro s hs
    have hDpos : 0 < D s := Finset.prod_pos fun p hp => by exact_mod_cast (hP_prime p (hs hp)).pos
    have hY0 : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hYpos
    have hlogD : log (D s) = ∑ p ∈ s, log (p : ℝ) := by
      dsimp only [D]; rw [Real.log_prod]
      intro p hp; exact_mod_cast (hP_prime p (hs hp)).ne_zero
    have hg_eq : g s = log (Y : ℝ) / log w + 2 - 1 / 100 - ∑ p ∈ s, e p := by
      dsimp only [g, e]
      rw [log_div hY0.ne' hDpos.ne', hlogD, sub_div, Finset.sum_div]; ring
    rw [hg_eq]; dsimp only [gr]; rw [Finset.sum_sub_distrib]; ring
  have hTclosed : ∀ u s, s ∈ T → I u s → u ∈ T := by
    intro u s hs hIus
    have hs' := mem_filter.mp hs
    refine mem_filter.mpr ⟨mem_powerset.mpr (hIus.1.trans (mem_powerset.mp hs'.1)), ?_⟩
    intro p hp
    rw [← prefix_filter_eq hIus hp]
    exact hs'.2 p (hIus.1 hp)
  let al := fun (r : ℚ) (p : ℕ) => (r.den : ZMod p) * (a p : ZMod p) = (r.num : ZMod p)
  let own := fun (i : ℕ) (r : ℚ) => (r.den : ℝ) ≤ w ^ C ∧ |(r.num : ℝ)| ≤ (Y : ℝ) * w ^ (C + 2) ∧
    (1 - d) * ((J i).card : ℝ) ≤ ((J i).filter (al r)).card
  let tg := fun (p : ℕ) (r : ℚ) => exp (w ^ ((1 : ℝ) / 4) * log w) ≤ lo (lab p) ∧
    own (lab p) r ∧ (∀ r', own (lab p) r' → r ≤ r') ∧ al r p
  let S := fun u : Finset ℕ => u.Nonempty ∧ Even u.card ∧ (u.card : ℝ) ≤ Clen * log B ∧
    (∀ p ∈ u, Even (u.filter (p ≤ ·)).card → max (2 * rep p) (rep p + 2) + 6 * Clen * x ≤ gr (u.filter (p ≤ ·))) ∧
    (∀ m ∈ u, (∀ q ∈ u, m ≤ q) → 2 * K * (log w) ^ 2 ≤ rep m ∧ rep m ≤ 2 * ρ * K * (log w) ^ 2 ∧
      206 / 100 ≤ gr u / rep m ∧ gr u / rep m ≤ 216 / 100) ∧
    (∃ p ∈ u, ∃ r : ℚ, tg p r ∧ (∀ q ∈ u, p < q → ∀ r', ¬ tg q r') ∧
      (u.filter (fun q => lab q = lab p)).card = 1 ∧ ∀ q ∈ u, al r q)
  set F := T.filter fun u => S u ∧ ∀ p ∈ u, u.filter (p ≤ ·) ≠ u → ¬ S (u.filter (p ≤ ·))
  set E := T.filter fun s => ∀ u ∈ F, ¬ I u s
  obtain ⟨hFsub, hFpf, hEeq, hTE_union, hTE_disj⟩ :=
    stop_family_props hTclosed S (fun _ h => h.1) F E
      (fun u => by simp only [F, mem_filter])
      (fun d => by simp only [E, mem_filter, I])
  have hMass_a : B ^ 2 * (∑ u ∈ E.filter fun u => g u ≤ k ∧ ε < |(Z u Q).card / (μ / D u) - 1|,
      (D u)⁻¹) ≤ δ := by
    have hT_eq : T = (Nat.primesLE ⌊z⌋₊ \ Nat.primesLE ⌊w⌋₊).powerset.filter fun s =>
        ∀ p ∈ s, Even (s.filter (p ≤ ·)).card → max (2 * e p) (e p + 2) ≤ g (s.filter (p ≤ ·)) := by
      ext s; simp only [T, hPeq, mem_filter, mem_powerset]
    have hμ_eq : μ = (Y : ℝ) * ∏ p ∈ Nat.primesLE ⌊w⌋₊, (1 - (p : ℝ)⁻¹) := by
      simp only [μ, v, hQeq]
    have hA_eq :
        E.filter (fun u => g u ≤ k ∧ ε < |(Z u Q).card / (μ / D u) - 1|) =
        (((Nat.primesLE ⌊z⌋₊ \ Nat.primesLE ⌊w⌋₊).powerset.filter fun s =>
          ∀ p ∈ s, Even (s.filter (p ≤ ·)).card → max (2 * e p) (e p + 2) ≤ g (s.filter (p ≤ ·))).filter
          (fun u => ∀ p ∈ u, ¬ S (u.filter (p ≤ ·)))).filter
          (fun u => g u ≤ k ∧ ε < |(((Icc 1 Y).filter (fun n =>
            (∀ p ∈ u, n ≡ a p [MOD p]) ∧ ∀ p ∈ Nat.primesLE ⌊w⌋₊, ¬ (n ≡ a p [MOD p]))).card : ℝ) /
            (((Y : ℝ) * ∏ p ∈ Nat.primesLE ⌊w⌋₊, (1 - (p : ℝ)⁻¹)) / D u) - 1|) := by
      ext u
      simp only [mem_filter, hEeq u, hT_eq, hμ_eq, Z, hQeq]
    rw [hA_eq]
    exact hzMass
  clear hzMass
  revert hzRef
  have htg_uniq : ∀ {p : ℕ} {r₁ r₂ : ℚ}, tg p r₁ → tg p r₂ → r₁ = r₂ :=
    fun h₁ h₂ => le_antisymm (h₁.2.2.1 _ h₂.2.1) (h₂.2.2.1 _ h₁.2.1)
  have hfirst_uniq : ∀ {u : Finset ℕ} {p₁ p₂ : ℕ} {r₁ r₂ : ℚ},
      p₁ ∈ u → tg p₁ r₁ → (∀ q ∈ u, p₁ < q → ∀ r', ¬ tg q r') →
      p₂ ∈ u → tg p₂ r₂ → (∀ q ∈ u, p₂ < q → ∀ r', ¬ tg q r') →
      p₁ = p₂ ∧ r₁ = r₂ := by
    intro u p₁ p₂ r₁ r₂ hp₁ ht₁ hf₁ hp₂ ht₂ hf₂
    rcases lt_trichotomy p₁ p₂ with h | rfl | h
    · exact False.elim (hf₁ p₂ hp₂ h r₂ ht₂)
    · exact ⟨rfl, htg_uniq ht₁ ht₂⟩
    · exact False.elim (hf₂ p₁ hp₁ h r₁ ht₁)
  have hS_imp_T : ∀ u ⊆ P, S u → u ∈ T := by
    intro u huP hSu
    refine mem_filter.mpr ⟨mem_powerset.mpr huP, ?_⟩
    intro p hp hEven
    have hsafe := hSu.2.2.2.1 p hp hEven
    have hAp : u.filter (p ≤ ·) ⊆ P := (filter_subset _ _).trans huP
    have hdiff : g (u.filter (p ≤ ·)) - gr (u.filter (p ≤ ·)) =
        ∑ q ∈ u.filter (p ≤ ·), (rep q - e q) := hg_sub_gr _ hAp
    have hdiff_nn : 0 ≤ ∑ q ∈ u.filter (p ≤ ·), (rep q - e q) :=
      Finset.sum_nonneg fun q hq => sub_nonneg.mpr (hP_bin' q (hAp hq)).2.2.2.2.1
    have hrep_p : e p ≤ rep p := (hP_bin' p (huP hp)).2.2.2.2.1
    have hmax_le : max (2 * e p) (e p + 2) ≤ max (2 * rep p) (rep p + 2) :=
      max_le_max (by linarith) (by linarith)
    have h6 : 0 ≤ 6 * Clen * x := by positivity
    linarith
  have hS_data : ∀ u ∈ F, ∀ hu : u.Nonempty,
      let m := u.min' hu
      ∀ p₀ ∈ u, ∀ r : ℚ,
      tg p₀ r → (∀ q ∈ u, p₀ < q → ∀ r', ¬ tg q r') →
      (u.filter (fun q => lab q = lab p₀)).card = 1 → (∀ q ∈ u, al r q) →
      let i := lab p₀
      let s := lo i
      let q := ∏ y ∈ u.erase p₀, y
      let J' := Nat.primesLE ⌊(1 + t) * s⌋₊ \ Nat.primesLE ⌊s⌋₊
      let G := J'.filter (al r)
      m.Prime ∧ m ∈ u.erase p₀ ∧ m ∈ q.primeFactors ∧ N ≤ m ∧
      exp (K * (log w) ^ 3) ≤ (m : ℝ) ∧ (m : ℝ) ≤ exp (2 * ρ * K * (log w) ^ 3) ∧
      exp (w ^ ((1 : ℝ) / 4) * log w) ≤ s ∧ x / 4 ≤ t ∧ t ≤ 1 ∧
      0 < Y ∧ 0 < q ∧ (r.den : ℝ) ≤ w ^ C ∧ |(r.num : ℝ)| ≤ (Y : ℝ) * w ^ (C + 2) ∧
      (∀ uval ∈ Set.Icc s ((1 + t) * s),
        log ((Y : ℝ) / (uval * (q : ℝ))) / log (m : ℝ) ∈ Set.Icc (203 / 100) (219 / 100)) ∧
      (∀ y ∈ q.primeFactors, m ≤ y ∧ al r y) ∧
      (∀ p ∈ J', m ≤ p ∧ Squarefree (p * q) ∧ r.den.Coprime p) ∧
      (1 - d) * (J'.card : ℝ) ≤ (G.card : ℝ) ∧
      J' = J i ∧
      (∀ p' ∈ G, insert p' (u.erase p₀) = (p' * q).primeFactors ∧
        insert p' (u.erase p₀) ∈ F ∧
        p' ∈ insert p' (u.erase p₀) ∧
        tg p' r ∧ (∀ y ∈ insert p' (u.erase p₀), p' < y → ∀ r', ¬ tg y r') ∧
        ((insert p' (u.erase p₀)).erase p' = u.erase p₀) ∧
        (∀ hne : (insert p' (u.erase p₀)).Nonempty, (insert p' (u.erase p₀)).min' hne = m)) := by
    intro u huF hu m p₀ hp₀ r htg₀ hfirst₀ hsingle₀ hal₀ i s q J' G
    have huT : u ∈ T := hFsub huF
    have huP : u ⊆ P := mem_powerset.mp (mem_filter.mp huT).1
    have hSu : S u := (mem_filter.mp huF).2.1
    have hmin_mem : m ∈ u := Finset.min'_mem u hu
    have hmin_le : ∀ y ∈ u, m ≤ y := fun y hy => Finset.min'_le u y hy
    have hwin := hSu.2.2.2.2.1 m hmin_mem hmin_le
    have hmP : m ∈ P := huP hmin_mem
    have hm_prime : m.Prime := hP_prime m hmP
    have hm_bin := hP_bin' m hmP
    have hp₀_bin := hP_bin' p₀ (huP hp₀)
    have hJ'_eq : J' = J i := by dsimp only [J', J, s, t]; rw [hupper i]
    have hmw : w < (m : ℝ) := by
      have hm_sdiff := Finset.mem_sdiff.mp (hPeq ▸ hmP)
      have hnot : ¬ (m ≤ ⌊w⌋₊) := fun h => hm_sdiff.2 (Nat.mem_primesLE.mpr ⟨h, hm_prime⟩)
      exact (Nat.floor_lt hw0.le).mp (by omega)
    have hNm : N ≤ m := by exact_mod_cast (hwN.trans_lt hmw).le
    have hem_hi : e m ≤ 2 * ρ * K * (log w) ^ 2 := hm_bin.2.2.2.2.1.trans hwin.2.1
    have hem_lo : K * (log w) ^ 2 ≤ e m := by linarith [hwin.1, hm_bin.2.2.2.2.2, hxc1]
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_prime.pos
    have hm_exp_lo : exp (K * (log w) ^ 3) ≤ (m : ℝ) := by
      have h1 : K * (log w) ^ 3 ≤ log (m : ℝ) := by
        have := (le_div_iff₀ hlogw).mp hem_lo
        linarith [show K * (log w) ^ 2 * log w = K * (log w) ^ 3 by ring]
      simpa only [exp_log hm_pos] using exp_le_exp.mpr h1
    have hm_exp_hi : (m : ℝ) ≤ exp (2 * ρ * K * (log w) ^ 3) := by
      have h1 : log (m : ℝ) ≤ 2 * ρ * K * (log w) ^ 3 := by
        have := (div_le_iff₀ hlogw).mp hem_hi
        linarith [show 2 * ρ * K * (log w) ^ 2 * log w = 2 * ρ * K * (log w) ^ 3 by ring]
      simpa only [exp_log hm_pos] using exp_le_exp.mpr h1
    have hm_lt_s : (m : ℝ) < s := by
      have h2 : exp (2 * ρ * K * (log w) ^ 3) < exp (w ^ ((1 : ℝ) / 4) * log w) := by
        refine exp_lt_exp.mpr ?_
        have := mul_lt_mul_of_pos_right hwgap hlogw
        linarith [show 2 * ρ * K * (log w) ^ 2 * log w = 2 * ρ * K * (log w) ^ 3 by ring]
      exact hm_exp_hi.trans_lt (h2.trans_le htg₀.1)
    have hm_ne_p₀ : m ≠ p₀ := by
      intro heq; rw [heq] at hm_lt_s; linarith [hp₀_bin.2.1]
    have hm_erase : m ∈ u.erase p₀ := mem_erase.mpr ⟨hm_ne_p₀, hmin_mem⟩
    have herase_prime : ∀ y ∈ u.erase p₀, y.Prime := fun y hy => hP_prime y (huP (mem_erase.mp hy).2)
    have hq_pos : 0 < q := prod_primes_pos herase_prime
    have hq_pf : q.primeFactors = u.erase p₀ := primeFactors_prod_primes herase_prime
    have hm_pf : m ∈ q.primeFactors := hq_pf ▸ hm_erase
    have hq_all : ∀ y ∈ q.primeFactors, m ≤ y ∧ al r y := by
      intro y hy; rw [hq_pf] at hy
      exact ⟨hmin_le y (mem_erase.mp hy).2, hal₀ y (mem_erase.mp hy).2⟩
    have hswap_base : ∀ y ∈ u, y ≠ p₀ → lab y ≠ i := by
      intro y hyu hyne hlab
      have hsub : ({p₀, y} : Finset ℕ) ⊆ u.filter (fun z => lab z = i) := by
        intro z hz
        rcases mem_insert.mp hz with rfl | hz
        · exact mem_filter.mpr ⟨hp₀, rfl⟩
        · rw [mem_singleton.mp hz]; exact mem_filter.mpr ⟨hyu, hlab⟩
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_pair hyne.symm, hsingle₀] at hcard; omega
    have hJ'_all : ∀ p ∈ J', m ≤ p ∧ Squarefree (p * q) ∧ r.den.Coprime p := by
      intro p hp; rw [hJ'_eq] at hp
      obtain ⟨hpP, hplab, hplo, _⟩ := hJ_bin' i hp₀_bin.1 p hp
      have hp_prime : p.Prime := hP_prime p hpP
      have hmp : m ≤ p := by exact_mod_cast (hm_lt_s.trans hplo).le
      have hp_not_erase : p ∉ u.erase p₀ := fun hmem =>
        hswap_base p (mem_erase.mp hmem).2 (mem_erase.mp hmem).1 hplab
      have hsq : Squarefree (p * q) := (prod_insert_prime_props hp_prime herase_prime hp_not_erase).1
      have hcop : r.den.Coprime p := by
        have hden_lt : (r.den : ℝ) < (p : ℝ) := by
          have h2 : w ^ C < exp (w ^ ((1 : ℝ) / 4) * log w) := by
            rw [rpow_def_of_pos hw0]
            exact exp_lt_exp.mpr (by rw [mul_comm]; exact mul_lt_mul_of_pos_right hw4C hlogw)
          exact htg₀.2.1.1.trans_lt (h2.trans_le (htg₀.1.trans hplo.le))
        exact (hp_prime.coprime_iff_not_dvd.mpr
          (Nat.not_dvd_of_pos_of_lt r.pos (by exact_mod_cast hden_lt))).symm
      exact ⟨hmp, hsq, hcop⟩
    have hband : ∀ uval ∈ Set.Icc s ((1 + t) * s),
        log ((Y : ℝ) / (uval * (q : ℝ))) / log (m : ℝ) ∈ Set.Icc (203 / 100) (219 / 100) := by
      intro uval huval
      have hs0 : 0 < s := by dsimp only [s, lo]; positivity
      have hDu_eq : D u = (p₀ : ℝ) * (q : ℝ) := by
        dsimp only [D, q]
        rw [Nat.cast_prod, ← Finset.mul_prod_erase u (fun y => (y : ℝ)) hp₀]
      have hgu_gr_lo : 0 ≤ g u - gr u := by
        rw [hg_sub_gr u huP]
        exact Finset.sum_nonneg fun y hy => sub_nonneg.mpr (hP_bin' y (huP hy)).2.2.2.2.1
      have hgu_gr_hi : g u - gr u ≤ 2 * Clen * x := by
        rw [hg_sub_gr u huP]
        have h1 : ∑ y ∈ u, (rep y - e y) ≤ ∑ _y ∈ u, (x / log w) :=
          Finset.sum_le_sum fun y hy => (hP_bin' y (huP hy)).2.2.2.2.2
        rw [Finset.sum_const, nsmul_eq_mul] at h1
        have h2 : (u.card : ℝ) * (x / log w) ≤ (Clen * log B) * (x / log w) :=
          mul_le_mul_of_nonneg_right hSu.2.2.1 (div_nonneg hx.le hlogw.le)
        have h3 : Clen * log B * (x / log w) ≤ Clen * (2 * log w) * (x / log w) := by
          have := mul_le_mul_of_nonneg_left hlogB (show 0 ≤ Clen * (x / log w) by positivity)
          linarith only [this]
        have h4 : Clen * (2 * log w) * (x / log w) = 2 * Clen * x := by field_simp [hlogw.ne']
        linarith only [h1, h2, h3, h4]
      exact band_window_transfer hx hlogw hδx rfl hs0 (by exact_mod_cast hYpos)
        (by exact_mod_cast (hP_prime p₀ (huP hp₀)).pos) (by exact_mod_cast hq_pos) hm_pos
        huval hp₀_bin.2.1.le (by dsimp only [s, t]; rw [hupper i]; exact hp₀_bin.2.2.1)
        (by dsimp only [g]; rw [hDu_eq]) rfl hgu_gr_lo hgu_gr_hi
        hm_bin.2.2.2.2.1 hm_bin.2.2.2.2.2 hem_lo hK hwin.2.2.1 hwin.2.2.2 hxc2 hxc3 hClen
        (by linarith only [ht_lo, hx])
    have hrepl : ∀ p' ∈ G, insert p' (u.erase p₀) = (p' * q).primeFactors ∧
        insert p' (u.erase p₀) ∈ F ∧
        p' ∈ insert p' (u.erase p₀) ∧
        tg p' r ∧ (∀ y ∈ insert p' (u.erase p₀), p' < y → ∀ r', ¬ tg y r') ∧
        ((insert p' (u.erase p₀)).erase p' = u.erase p₀) ∧
        (∀ hne : (insert p' (u.erase p₀)).Nonempty, (insert p' (u.erase p₀)).min' hne = m) := by
      intro p' hp'G
      have hp'J' : p' ∈ J' := (mem_filter.mp hp'G).1
      have hp'al : al r p' := (mem_filter.mp hp'G).2
      have hp'J : p' ∈ J i := hJ'_eq ▸ hp'J'
      obtain ⟨hp'P, hp'lab, hp'lo, hp'hi⟩ := hJ_bin' i hp₀_bin.1 p' hp'J
      have hp'_bounds : lo (lab p₀) < (p' : ℝ) ∧ (p' : ℝ) ≤ lo (lab p₀ + 1) := by
        rw [← hlo_succ]; exact ⟨hp'lo, hp'hi⟩
      have hu_bounds : ∀ y ∈ u, lo (lab y) < (y : ℝ) ∧ (y : ℝ) ≤ lo (lab y + 1) := by
        intro y hy; rw [← hlo_succ]; exact ⟨(hP_bin' y (huP hy)).2.1, (hP_bin' y (huP hy)).2.2.1⟩
      have hIso := swap_order_iso hp₀ hlo_mono hu_bounds hp'lab hp'_bounds hsingle₀
      set φ := fun y : ℕ => if y = p₀ then p' else y
      have hp'_not_erase : p' ∉ u.erase p₀ := hIso.2.1
      have himg : u.image φ = insert p' (u.erase p₀) := hIso.2.2.1
      have hord : ∀ x ∈ u, ∀ y ∈ u, x < y ↔ φ x < φ y := hIso.2.2.2.1
      have hlab_pres : ∀ x ∈ u, lab (φ x) = lab x := hIso.2.2.2.2.1
      have hfilt : ∀ x ∈ u, (u.image φ).filter (φ x ≤ ·) = (u.filter (x ≤ ·)).image φ := hIso.2.2.2.2.2.1
      have hinj : Set.InjOn φ u := hIso.2.2.2.2.2.2
      have hφ_p₀ : φ p₀ = p' := by simp [φ]
      have hφ_ne : ∀ y ∈ u, y ≠ p₀ → φ y = y := fun y _ hy => if_neg hy
      have hrep_pres : ∀ y ∈ u, rep (φ y) = rep y := fun y hy => by
        dsimp only [rep]; rw [hlab_pres y hy]
      have hgr_pres : ∀ v ⊆ u, gr (v.image φ) = gr v := by
        intro v hv; dsimp only [gr]
        rw [Finset.sum_image (hinj.mono hv)]
        congr 1
        exact Finset.sum_congr rfl fun y hy => hrep_pres y (hv hy)
      have htg_p' : tg p' r := by
        dsimp only [tg]; rw [hp'lab]; exact ⟨htg₀.1, htg₀.2.1, htg₀.2.2.1, hp'al⟩
      have htg_iff : ∀ y ∈ u, ∀ r' : ℚ, tg (φ y) r' ↔ tg y r' := by
        intro y hy r'
        by_cases hy0 : y = p₀
        · rw [hy0, hφ_p₀]
          exact ⟨fun ht => (htg_uniq ht htg_p') ▸ htg₀, fun ht => (htg_uniq ht htg₀) ▸ htg_p'⟩
        · rw [hφ_ne y hy hy0]
      have hu'_eq_pf : insert p' (u.erase p₀) = (p' * q).primeFactors :=
        (prod_insert_prime_props (hP_prime p' hp'P) herase_prime hp'_not_erase).2.symm
      have hu'_P : insert p' (u.erase p₀) ⊆ P := by
        intro y hy
        rcases mem_insert.mp hy with rfl | hy
        · exact hp'P
        · exact huP (mem_erase.mp hy).2
      have hS_pres : ∀ v ⊆ u, (S (v.image φ) ↔ S v) := fun v hv =>
        replacement_S_iff hv hp₀ φ hφ_p₀ hφ_ne hord hinj hlab_pres hrep_pres hgr_pres
          htg_uniq htg₀ htg_p' hfirst₀ htg₀.2.2.2 hp'al hp'lab
      have hu'_S : S (insert p' (u.erase p₀)) := by
        rw [← himg]; exact (hS_pres u Subset.rfl).mpr hSu
      have hu'_T : insert p' (u.erase p₀) ∈ T := hS_imp_T _ hu'_P hu'_S
      have hu'_F : insert p' (u.erase p₀) ∈ F := by
        refine mem_filter.mpr ⟨hu'_T, hu'_S, ?_⟩
        intro y hy hyne hSy
        rw [← himg] at hy hyne hSy
        obtain ⟨a', ha', rfl⟩ := mem_image.mp hy
        rw [hfilt a' ha'] at hyne hSy
        have hane : u.filter (a' ≤ ·) ≠ u := fun heq => hyne (by rw [heq])
        have hSa := (hS_pres (u.filter (a' ≤ ·)) (filter_subset _ _)).mp hSy
        exact (mem_filter.mp huF).2.2 a' ha' hane hSa
      have hfirst_u' : ∀ y ∈ insert p' (u.erase p₀), p' < y → ∀ r', ¬ tg y r' := by
        intro y hy hlt r'
        rw [← himg] at hy
        obtain ⟨a', ha', rfl⟩ := mem_image.mp hy
        have hlt' : p₀ < a' := (hord p₀ hp₀ a' ha').mpr (by rw [hφ_p₀]; exact hlt)
        exact (htg_iff a' ha' r').not.mpr (hfirst₀ a' ha' hlt' r')
      have herase_u' : (insert p' (u.erase p₀)).erase p' = u.erase p₀ :=
        Finset.erase_insert hp'_not_erase
      have hmin_u' : ∀ hne : (insert p' (u.erase p₀)).Nonempty,
          (insert p' (u.erase p₀)).min' hne = m := by
        intro hne
        apply le_antisymm
        · exact Finset.min'_le _ m (mem_insert_of_mem hm_erase)
        · apply Finset.le_min'
          intro y hy
          rcases mem_insert.mp hy with hy_eq | hy
          · rw [hy_eq]; exact (hJ'_all p' hp'J').1
          · exact hmin_le y (mem_erase.mp hy).2
      exact ⟨hu'_eq_pf, hu'_F, mem_insert_self _ _, htg_p', hfirst_u', herase_u', hmin_u'⟩
    have hown_card : (1 - d) * (J'.card : ℝ) ≤ (G.card : ℝ) := by
      dsimp only [G]; rw [hJ'_eq]; exact htg₀.2.1.2.2
    exact ⟨hm_prime, hm_erase, hm_pf, hNm, hm_exp_lo, hm_exp_hi, htg₀.1, ht_lo, ht_hi,
      hYpos, hq_pos, htg₀.2.1.1, htg₀.2.1.2.1, hband, hq_all, hJ'_all, hown_card, hJ'_eq, hrepl⟩
  intro hzRef
  let keyOf : Finset ℕ → ℕ × ℕ × ℝ × ℝ × ℚ := fun u =>
    if h : ∃ hu : u.Nonempty, ∃ p₀ ∈ u, ∃ r : ℚ, tg p₀ r ∧ (∀ q ∈ u, p₀ < q → ∀ r', ¬ tg q r') then
      let hu := h.choose
      let p₀ := h.choose_spec.choose
      let r := h.choose_spec.choose_spec.2.choose
      (u.min' hu, ∏ y ∈ u.erase p₀, y, lo (lab p₀), t, r)
    else (0, 0, 0, 0, 0)
  have hkeyOf_eq : ∀ {u : Finset ℕ} (hu : u.Nonempty) {p₀ : ℕ} {r : ℚ},
      p₀ ∈ u → tg p₀ r → (∀ q ∈ u, p₀ < q → ∀ r', ¬ tg q r') →
      keyOf u = (u.min' hu, ∏ y ∈ u.erase p₀, y, lo (lab p₀), t, r) := by
    intro u hu p₀ r hp₀ htg₀ hfirst₀
    have hex : ∃ hu : u.Nonempty, ∃ p₀ ∈ u, ∃ r : ℚ, tg p₀ r ∧ (∀ q ∈ u, p₀ < q → ∀ r', ¬ tg q r') :=
      ⟨hu, p₀, hp₀, r, htg₀, hfirst₀⟩
    dsimp only [keyOf]
    rw [dif_pos hex]
    obtain ⟨hp_eq, hr_eq⟩ := hfirst_uniq hex.choose_spec.choose_spec.1
      hex.choose_spec.choose_spec.2.choose_spec.1 hex.choose_spec.choose_spec.2.choose_spec.2
      hp₀ htg₀ hfirst₀
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ (Prod.ext rfl hr_eq)))
    · dsimp only; rw [hp_eq]
    · dsimp only; rw [hp_eq]
  let Ks := F.image keyOf
  by_cases hBadKey : ∃ κ ∈ Ks,
      let m := κ.1; let q := κ.2.1; let s := κ.2.2.1; let t' := κ.2.2.2.1; let r := κ.2.2.2.2
      let J' := Nat.primesLE ⌊(1 + t') * s⌋₊ \ Nat.primesLE ⌊s⌋₊
      let G := J'.filter (al r)
      (∑ p ∈ G, ((Z (p * q).primeFactors ((range m).filter Nat.Prime)).card : ℝ)) <
        (33 / 100 * v (Nat.primesLE m)) * (∑ p ∈ G, (Y : ℝ) / ((p : ℝ) * (q : ℝ)))
  · right
    obtain ⟨κ, hκKs, hκBad⟩ := hBadKey
    obtain ⟨u, huF, rfl⟩ := mem_image.mp hκKs
    have hSu : S u := (mem_filter.mp huF).2.1
    have hu : u.Nonempty := hSu.1
    obtain ⟨p₀, hp₀, r, htg₀, hfirst₀, hsingle₀, hal₀⟩ := hSu.2.2.2.2.2
    rw [hkeyOf_eq hu hp₀ htg₀ hfirst₀] at hκBad
    obtain ⟨hm_prime, _, _, hNm, hm_exp_lo, hm_exp_hi, htg1, ht_lo', ht_hi',
      hYpos', hq_pos, hrden, hrnum, hband, hq_all, hJ'_all, hown_card, _, _⟩ :=
      hS_data u huF hu p₀ hp₀ r htg₀ hfirst₀ hsingle₀ hal₀
    refine ⟨u.min' hu, ∏ y ∈ u.erase p₀, y, lo (lab p₀), t, r, hwW, ?_, hκBad⟩
    exact ⟨hm_prime, hNm, hm_exp_lo, hm_exp_hi, htg1, ht_lo', ht_hi', hYpos', hq_pos,
      hrden, hrnum, hband, hq_all, hJ'_all, hown_card⟩
  · left
    have hGoodKey : ∀ κ ∈ Ks,
        let m := κ.1; let q := κ.2.1; let s := κ.2.2.1; let t' := κ.2.2.2.1; let r := κ.2.2.2.2
        let J' := Nat.primesLE ⌊(1 + t') * s⌋₊ \ Nat.primesLE ⌊s⌋₊
        let G := J'.filter (al r)
        (33 / 100 * v (Nat.primesLE m)) * (∑ p ∈ G, (Y : ℝ) / ((p : ℝ) * (q : ℝ))) ≤
          (∑ p ∈ G, ((Z (p * q).primeFactors ((range m).filter Nat.Prime)).card : ℝ)) :=
      fun κ hκ => not_lt.mp fun hlt => hBadKey ⟨κ, hκ, hlt⟩
    refine ⟨F, hFsub, ?_, hMass_a, ?_⟩
    · intro u huF
      have hSu := (hFpf u huF).1
      exact ⟨hSu.1, hSu.2.1, (hFpf u huF).2⟩
    · have hLHS_split : μ * (∑ d ∈ T \ E, (-1 : ℝ) ^ d.card / D d) =
          ∑ u ∈ F, μ * (∑ d ∈ T.filter (I u), (-1 : ℝ) ^ d.card / D d) := by
        rw [hTE_union, Finset.sum_biUnion hTE_disj, Finset.mul_sum]
      rw [hLHS_split]
      have hF_fib : ∀ κ ∈ Ks,
          (∑ u ∈ F.filter (fun u => keyOf u = κ), μ * (∑ d ∈ T.filter (I u), (-1 : ℝ) ^ d.card / D d)) ≤
          (∑ u ∈ F.filter (fun u => keyOf u = κ),
            ((Z u (Q ∪ P.filter (fun p => ∀ y ∈ u, p < y))).card : ℝ)) := by
        intro κ hκKs
        obtain ⟨u₀, hu₀F, rfl⟩ := mem_image.mp hκKs
        have hSu₀ : S u₀ := (mem_filter.mp hu₀F).2.1
        have hu₀ : u₀.Nonempty := hSu₀.1
        obtain ⟨p₀, hp₀, r, htg₀, hfirst₀, hsingle₀, hal₀⟩ := hSu₀.2.2.2.2.2
        have hkeq := hkeyOf_eq hu₀ hp₀ htg₀ hfirst₀
        set m := u₀.min' hu₀
        set q := ∏ y ∈ u₀.erase p₀, y
        set s := lo (lab p₀)
        set J' := Nat.primesLE ⌊(1 + t) * s⌋₊ \ Nat.primesLE ⌊s⌋₊
        set G := J'.filter (al r)
        obtain ⟨hm_prime, _, _, _, hm_exp_lo, hm_exp_hi, _, _, _,
          _, _, _, _, hband, _, hJ'_all, _, hJ'_eq, hrepl⟩ :=
          hS_data u₀ hu₀F hu₀ p₀ hp₀ r htg₀ hfirst₀ hsingle₀ hal₀
        have hu₀P : u₀ ⊆ P := mem_powerset.mp (mem_filter.mp (hFsub hu₀F)).1
        have hfib_eq : F.filter (fun u => keyOf u = keyOf u₀) = G.image (fun p => (p * q).primeFactors) := by
          ext u
          simp only [mem_filter, mem_image, hkeq]
          constructor
          · rintro ⟨huF, hukey⟩
            have hSu : S u := (mem_filter.mp huF).2.1
            have hu : u.Nonempty := hSu.1
            obtain ⟨p₁, hp₁, r₁, htg₁, hfirst₁, _, _⟩ := hSu.2.2.2.2.2
            rw [hkeyOf_eq hu hp₁ htg₁ hfirst₁] at hukey
            have hq_eq : ∏ y ∈ u.erase p₁, y = q := congrArg (fun z' => z'.2.1) hukey
            have hs_eq : lo (lab p₁) = s := congrArg (fun z' => z'.2.2.1) hukey
            have hr_eq : r₁ = r := congrArg (fun z' => z'.2.2.2.2) hukey
            rw [hr_eq] at htg₁
            have hlab_eq : lab p₁ = lab p₀ := by
              rcases lt_trichotomy (lab p₁) (lab p₀) with h | h | h
              · linarith [hlo_mono _ _ h]
              · exact h
              · linarith [hlo_mono _ _ h]
            have hp₁P : p₁ ∈ P := (mem_powerset.mp (mem_filter.mp (hFsub huF)).1) hp₁
            have hp₁J' : p₁ ∈ J' := by
              change p₁ ∈ Nat.primesLE ⌊(1 + t) * lo (lab p₀)⌋₊ \ Nat.primesLE ⌊lo (lab p₀)⌋₊
              rw [hJ'_eq, ← hlab_eq]; exact (hP_bin' p₁ hp₁P).2.2.2.1
            have hp₁G : p₁ ∈ G := mem_filter.mpr ⟨hp₁J', htg₁.2.2.2⟩
            refine ⟨p₁, hp₁G, ?_⟩
            have hu_erase_prime : ∀ y ∈ u.erase p₁, y.Prime :=
              fun y hy => hP_prime y ((mem_powerset.mp (mem_filter.mp (hFsub huF)).1) (mem_erase.mp hy).2)
            have hu₀_erase_prime : ∀ y ∈ u₀.erase p₀, y.Prime :=
              fun y hy => hP_prime y (hu₀P (mem_erase.mp hy).2)
            have herase_eq : u.erase p₁ = u₀.erase p₀ := by
              rw [← primeFactors_prod_primes hu_erase_prime, hq_eq, primeFactors_prod_primes hu₀_erase_prime]
            rw [← (hrepl p₁ hp₁G).1, ← herase_eq, Finset.insert_erase hp₁]
          · rintro ⟨p', hp'G, rfl⟩
            obtain ⟨hpf, hu'F, hp'mem, htg', hfirst', herase', hmin'⟩ := hrepl p' hp'G
            rw [← hpf]
            have hne' : (insert p' (u₀.erase p₀)).Nonempty := ⟨p', hp'mem⟩
            refine ⟨hu'F, ?_⟩
            rw [hkeyOf_eq hne' hp'mem htg' hfirst', hmin' hne', herase']
            have hlab' : lab p' = lab p₀ :=
              (hJ_bin' (lab p₀) (hP_bin' p₀ (hu₀P hp₀)).1 p' (hJ'_eq ▸ (mem_filter.mp hp'G).1)).2.1
            simp only [hlab', m, q, s]
        have hinjG : Set.InjOn (fun p : ℕ => (p * q).primeFactors) G := by
          intro p₁ hp₁ p₂ hp₂ heq
          dsimp only [q] at heq
          rw [← (hrepl p₁ hp₁).1, ← (hrepl p₂ hp₂).1] at heq
          have hp₁_mem : p₁ ∈ insert p₂ (u₀.erase p₀) := heq ▸ mem_insert_self _ _
          rcases mem_insert.mp hp₁_mem with rfl | hmem
          · rfl
          · have hsq := (hJ'_all p₁ (mem_filter.mp hp₁).1).2.1
            have hp₁_prime : p₁.Prime :=
              hP_prime p₁ (hJ_bin' _ (hP_bin' p₀ (hu₀P hp₀)).1 p₁ (hJ'_eq ▸ (mem_filter.mp hp₁).1)).1
            exact False.elim (hp₁_prime.ne_one (Nat.isUnit_iff.mp
              (hsq p₁ (mul_dvd_mul_left p₁ (Finset.dvd_prod_of_mem _ hmem)))))
        rw [hfib_eq, Finset.sum_image hinjG, Finset.sum_image hinjG]
        have hBadK := hGoodKey (keyOf u₀) hκKs
        rw [hkeq] at hBadK
        have hRef_step :
            (∑ p ∈ G, μ * (∑ d ∈ T.filter (I (p * q).primeFactors), (-1 : ℝ) ^ d.card / D d)) ≤
            (33 / 100 * v (Nat.primesLE m)) * (∑ p ∈ G, (Y : ℝ) / ((p : ℝ) * (q : ℝ))) := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun p hpG => ?_
          obtain ⟨hpf, hu'F, hp'mem, _, _, _, hmin'⟩ := hrepl p hpG
          have hu'T : (p * q).primeFactors ∈ T := hFsub (hpf ▸ hu'F)
          have hu'ne : (p * q).primeFactors.Nonempty := hpf ▸ ⟨p, hp'mem⟩
          have hu'even : Even (p * q).primeFactors.card := (hFpf _ (hpf ▸ hu'F)).1.2.1
          have hmin_eq : (p * q).primeFactors.min' hu'ne = m := by
            have h1 := hmin' (hpf.symm ▸ hu'ne)
            simpa only [hpf] using h1
          have hsq : Squarefree (p * q) := (hJ'_all p (mem_filter.mp hpG).1).2.1
          have hD_eq : D (p * q).primeFactors = (p : ℝ) * (q : ℝ) := by
            dsimp only [D]
            rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq, Nat.cast_mul]
          have hp_bounds : (p : ℝ) ∈ Set.Icc s ((1 + t) * s) := by
            have h := hJ_bin' (lab p₀) (hP_bin' p₀ (hu₀P hp₀)).1 p (hJ'_eq ▸ (mem_filter.mp hpG).1)
            refine ⟨h.2.2.1.le, ?_⟩
            dsimp only [s, t]; rw [hupper (lab p₀)]; exact h.2.2.2
          have hband_p := hband (p : ℝ) hp_bounds
          have hlogm_ge : K * (log w) ^ 3 ≤ log (m : ℝ) := by
            have := log_le_log (exp_pos _) hm_exp_lo; rwa [log_exp] at this
          have hlogm_pos : 0 < log (m : ℝ) := lt_of_lt_of_le (by positivity) hlogm_ge
          have hgu_em : g (p * q).primeFactors / e m =
              log ((Y : ℝ) / ((p : ℝ) * (q : ℝ))) / log (m : ℝ) + (199 / 100) * (log w / log (m : ℝ)) := by
            dsimp only [g, e]; rw [hD_eq]; field_simp [hlogw.ne', hlogm_pos.ne']; ring
          have hterm_pos : 0 < (199 / 100) * (log w / log (m : ℝ)) := by positivity
          have hterm_le : (199 / 100) * (log w / log (m : ℝ)) ≤ 1 / 100 := by
            have h1 : log w / log (m : ℝ) ≤ 1 / (K * (log w) ^ 2) := by
              rw [div_le_div_iff₀ hlogm_pos (by positivity), one_mul]
              linarith only [hlogm_ge, show log w * (K * (log w) ^ 2) = K * (log w) ^ 3 by ring]
            have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 199 / 100 by norm_num)
            have h3 : (199 / 100) * (1 / (K * (log w) ^ 2)) = (199 / 100) / (K * (log w) ^ 2) := by ring
            linarith only [h2, h3, hxc4]
          have hge2 : 2 ≤ g (p * q).primeFactors / e m := by linarith only [hgu_em, hterm_pos, hband_p.1]
          have hle115 : g (p * q).primeFactors / e m ≤ 11 / 5 := by linarith only [hgu_em, hterm_le, hband_p.2]
          have href_p : μ * (∑ d ∈ T.filter (I (p * q).primeFactors), (-1 : ℝ) ^ d.card / D d) ≤
              (33 / 100 * v (Nat.primesLE ((p * q).primeFactors.min' hu'ne))) *
              ((Y : ℝ) / D (p * q).primeFactors) :=
            hzRef (p * q).primeFactors hu'T hu'ne hu'even
              (by rwa [hmin_eq]) (by rwa [hmin_eq]) (by rwa [hmin_eq]) (by rwa [hmin_eq])
          rw [hmin_eq, hD_eq] at href_p
          exact href_p
        have hRHS_eq :
            (∑ p ∈ G, ((Z (p * q).primeFactors ((range m).filter Nat.Prime)).card : ℝ)) =
            (∑ p ∈ G, ((Z (p * q).primeFactors (Q ∪ P.filter (fun r' => ∀ y ∈ (p * q).primeFactors, r' < y))).card : ℝ)) := by
          refine Finset.sum_congr rfl fun p hpG => ?_
          obtain ⟨hpf, hu'F, hp'mem, _, _, _, hmin'⟩ := hrepl p hpG
          have hu'ne : (p * q).primeFactors.Nonempty := hpf ▸ ⟨p, hp'mem⟩
          have hmin_eq : (p * q).primeFactors.min' hu'ne = m := by
            have h1 := hmin' (hpf.symm ▸ hu'ne)
            simpa only [hpf] using h1
          have hmP : m ∈ P :=
            (mem_powerset.mp (mem_filter.mp (hFsub (hpf ▸ hu'F))).1) (hmin_eq ▸ Finset.min'_mem _ hu'ne)
          have hset_eq : (range m).filter Nat.Prime =
              Q ∪ P.filter (fun r' => ∀ y ∈ (p * q).primeFactors, r' < y) := by
            ext r'
            simp only [mem_filter, mem_range, mem_union, Q, P, mem_Icc]
            have hm_bounds := (mem_filter.mp hmP).1
            have hm_lo : ⌊w⌋₊ + 1 ≤ m := (mem_Icc.mp hm_bounds).1
            have hm_hi : m ≤ ⌊z⌋₊ := (mem_Icc.mp hm_bounds).2
            constructor
            · rintro ⟨hr'm, hr'p⟩
              by_cases hr'w : r' < ⌊w⌋₊ + 1
              · exact Or.inl ⟨hr'w, hr'p⟩
              · refine Or.inr ⟨⟨⟨Nat.le_of_not_lt hr'w, Nat.le_trans (Nat.le_of_lt hr'm) hm_hi⟩, hr'p⟩, ?_⟩
                intro y hy
                exact Nat.lt_of_lt_of_le hr'm (hmin_eq ▸ Finset.min'_le _ y hy)
            · rintro (⟨hr'w, hr'p⟩ | ⟨⟨⟨_, _⟩, hr'p⟩, hlt⟩)
              · exact ⟨Nat.lt_of_lt_of_le hr'w hm_lo, hr'p⟩
              · exact ⟨hlt m (hmin_eq ▸ Finset.min'_mem _ hu'ne), hr'p⟩
          rw [hset_eq]
        exact hRef_step.trans (hBadK.trans_eq hRHS_eq)
      have hF_part : F = Ks.biUnion (fun κ => F.filter (fun u => keyOf u = κ)) := by
        ext u
        simp only [Ks, mem_biUnion, mem_image, mem_filter]
        exact ⟨fun huF => ⟨keyOf u, ⟨u, huF, rfl⟩, huF, rfl⟩, fun ⟨_, _, huF, _⟩ => huF⟩
      have hF_disj : (Ks : Set (ℕ × ℕ × ℝ × ℝ × ℚ)).PairwiseDisjoint
          (fun κ => F.filter (fun u => keyOf u = κ)) := by
        intro κ₁ _ κ₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro u h1 h2
        exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
      conv_lhs => rw [hF_part, Finset.sum_biUnion hF_disj]
      conv_rhs => rw [hF_part, Finset.sum_biUnion hF_disj]
      exact Finset.sum_le_sum fun κ hκ => hF_fib κ hκ

end

theorem main : H1 → H2 → OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H2_R1.H3 := by
  intro hRef hMass k ε δ hk hε hδ d hd hd14 N
  obtain ⟨Clen, C, x, ρ, hClen, hC, hx, hx1, hρ, hMassK⟩ := hMass k ε δ d hk hε hδ hd hd14
  refine ⟨C, hC, ?_⟩
  intro K hK
  refine ⟨2 * ρ, x, by linarith, hx, ?_⟩
  intro W
  filter_upwards [hRef K (2 * ρ) hK (by linarith), hMassK K hK,
    scale_eventually Clen C K ρ x W N hClen hK (by linarith) hx] with z hzRef hzMass hzScale
  obtain ⟨hw1, hwW, hwN, hwz, hYpos, hspan, hlogB, hwgap, hw4C, hxc1, hxc2, hxc3, hxc4⟩ := hzScale
  dsimp only
  intro a
  exact fixed_scale_transfer hClen hK (by linarith) hx hx1
    hw1 hwW hwN hwz hYpos hspan hlogB hwgap hw4C hxc1 hxc2 hxc3 hxc4 a hzRef (hzMass a)

end OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H2_R1_H3_R1
