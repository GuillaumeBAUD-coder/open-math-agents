import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H3_R1

/-!
A Fermat-prime exponent chain from 65537, and the simple-prime cutoff in the 3967 family.
The factors of the eleventh and twelfth Fermat numbers are tabulated by Richard P. Brent,
Factorization of Fermat numbers, https://maths-people.anu.edu.au/brent/pd/rpb161tr.pdf .
The factors of 65537^16+1 were retrieved from FactorDB and also found by GNU factor.
The unitary-divisor balance and its prime-factor product are from the earlier reduction by
Adam McCarter. The predecessor step supplied the common seven-prime simple core.
-/

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H1.R1.H3.R1.H1.R1 of step Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H1.R1.H3.R1.H1
-- Credit: @connoranderson

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H3_R1_H1_R1

def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 152 → q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31) →
    607 ∣ n → 223 ∣ n → ¬ 433 ∣ n → ¬ 991 ∣ n → ¬ 1213 ∣ n → ¬ 1783 ∣ n →
    3967 ∣ n →
    (64 ∣ padicValNat 2 n ∨
      (padicValNat 2 n % 32 = 16 ∧ 65537 ∣ n ∧ 0 < n.factorization 65537 ∧
       (128 ∣ n.factorization 65537 ∨ (n.factorization 65537 % 32 = 16 ∧
          4365089 ∈ S ∧ Even (n.factorization 4365089) ∧
          38899171806337 ∈ S ∧ 731762088686190817 ∈ S)))) →
    n.factorization 3967 = 1 →
    (∀ q : ℕ, q.Prime → n.factorization q = 1 →
      q ∉ ({3, 5, 7, 19, 31, 223, 607, 3967} : Finset ℕ) → 5057 ≤ q) →
    padicValNat 2 n ≤ A

def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 152 → q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31) →
    607 ∣ n → 223 ∣ n → ¬ 433 ∣ n → ¬ 991 ∣ n → ¬ 1213 ∣ n → ¬ 1783 ∣ n →
    3967 ∣ n →
    (64 ∣ padicValNat 2 n ∨
      (padicValNat 2 n % 32 = 16 ∧ 65537 ∣ n ∧ 0 < n.factorization 65537 ∧
        128 ∣ n.factorization 65537)) →
    3967 ∈ S → S.card ≤ 4 →
    padicValNat 2 n % 4096 ≠ 2048 → padicValNat 2 n % 8192 ≠ 4096 →
    padicValNat 2 n ≤ A

open Finset
open OMA.R_Erdos1052_erdos_1052_R1

private lemma plus_dvd {n p q : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hp : p.Prime) (hnp : p∣n) (hq : q.Prime) (hq2 : q≠2)
    (hv : q ∣ 1+p^n.factorization p) : q∣n := by
  have mem := Nat.mem_primeFactors.mpr ⟨hp,hnp,h.2.ne'⟩
  have hs := Finset.dvd_prod_of_mem (fun r => 1+r^n.factorization r) mem
  rw [prod_eq_two_mul h] at hs
  exact (hq.dvd_mul.mp (hv.trans hs)).resolve_left
    (fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h))

private lemma mod_power {b p k r e : ℕ} [NeZero p] (hk : e%k=r)
    (hb : (b:ZMod p)^k=1) (hr : 1+(b:ZMod p)^r=0) :
    p ∣ 1+b^e := by
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_pow]
  have he : e=r+k*(e/k) := by rw [←hk,Nat.mod_add_div]
  rw [he,pow_add,pow_mul,hb,one_pow,mul_one]
  exact hr

/-- Admissibility of the squareful-prime set already excludes 257. -/
private lemma no257 {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (S : Finset ℕ)
    (hS : ∀ p, p∈S ↔ p.Prime ∧ p≠2 ∧ p^2∣n)
    (hA : ∀ z∈S, 128≤z ∧ S.card+3≤z)
    (hB : ∏ z∈S, (((z:ℚ)+1)/((z:ℚ)-2-(S.card:ℚ))) ≤ 2101/2097)
    (h43 : ¬43∣n) : ¬257∣n := by
  intro hd
  have hq : Nat.Prime 257 := by norm_num
  by_cases hSq : 257∈S
  · have lower (z : ℕ) (hz : z∈S) : 1 ≤ ((z:ℚ)+1)/((z:ℚ)-2-(S.card:ℚ)) := by
      have hq' : (S.card:ℚ)+3≤z := by exact_mod_cast (hA z hz).2
      have hc : 0≤(S.card:ℚ) := by positivity
      rw [le_div_iff₀ (by linarith)]
      linarith
    have hsub : {257} ⊆ S := Finset.singleton_subset_iff.mpr hSq
    have hh := Finset.prod_le_prod_of_subset_of_one_le hsub
      (fun z hz => (zero_le_one.trans (lower z (hsub hz))))
      (fun z hz _ => lower z hz)
    simp only [Finset.prod_singleton] at hh
    have hh' := hh.trans hB
    have hb : (S.card:ℚ)+3≤257 := by exact_mod_cast (hA 257 hSq).2
    have hc : 0≤(S.card:ℚ) := by positivity
    norm_num at hh'
    rw [div_le_iff₀ (by linarith)] at hh'
    linarith
  · have hf : n.factorization 257=1 := by
      have hp := hq.factorization_pos_of_dvd h.2.ne' hd
      by_contra! hh
      apply hSq
      exact (hS _).mpr ⟨hq,by decide,(hq.pow_dvd_iff_le_factorization h.2.ne').mpr (by omega)⟩
    apply h43 (plus_dvd h hq hd (by norm_num) (by decide) ?_)
    rw [hf]; decide

theorem squareful_budget (S : Finset ℕ) (hA : ∀ z∈S, 128≤z ∧ S.card+3≤z)
    (hB : ∏ z∈S, (((z:ℚ)+1)/((z:ℚ)-2-(S.card:ℚ))) ≤ 2101/2097)
    {p : ℕ} (hp : p∈S) : 2101*S.card+6299 ≤ 4*p := by
  have lower (z : ℕ) (hz : z∈S) : 1 ≤ ((z:ℚ)+1)/((z:ℚ)-2-(S.card:ℚ)) := by
    have hq' : (S.card:ℚ)+3≤z := by exact_mod_cast (hA z hz).2
    have hc : 0≤(S.card:ℚ) := by positivity
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hs : {p} ⊆ S := Finset.singleton_subset_iff.mpr hp
  have H := Finset.prod_le_prod_of_subset_of_one_le hs
    (fun z hz => zero_le_one.trans (lower z (hs hz))) (fun z hz _ => lower z hz)
  simp only [Finset.prod_singleton] at H
  have H' := H.trans hB
  have hq' : (S.card:ℚ)+3≤p := by exact_mod_cast (hA p hp).2
  rw [div_le_iff₀ (by linarith)] at H'
  exact_mod_cast (show 2101*(S.card:ℚ)+6299≤4*(p:ℚ) by linarith)

theorem simple_below {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (S : Finset ℕ)
    (hS : ∀ p, p∈S ↔ p.Prime ∧ p≠2 ∧ p^2∣n)
    (hA : ∀ z∈S, 128≤z ∧ S.card+3≤z)
    (hB : ∏ z∈S, (((z:ℚ)+1)/((z:ℚ)-2-(S.card:ℚ))) ≤ 2101/2097)
    {p : ℕ} (hp : p.Prime) (hodd : p≠2) (hd : p∣n) (hlt : p<2100) :
    n.factorization p=1 := by
  have hpos := hp.factorization_pos_of_dvd h.2.ne' hd
  by_contra! hh
  have hx := (hS p).mpr ⟨hp,hodd,(hp.pow_dvd_iff_le_factorization h.2.ne').mpr (by omega)⟩
  have ha := Finset.card_pos.mpr ⟨p,hx⟩
  have hb := squareful_budget S hA hB hx
  omega

theorem forced_fermat_exponent {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (S : Finset ℕ) (hS : ∀ p, p∈S ↔ p.Prime ∧ p≠2 ∧ p^2∣n)
    (hA : ∀ z∈S, 128≤z ∧ S.card+3≤z)
    (hB : ∏ z∈S, (((z:ℚ)+1)/((z:ℚ)-2-(S.card:ℚ))) ≤ 2101/2097)
    (h19 : 19∣n) (hsmall : ∀ q:ℕ, q.Prime → q∣n → q<152 →
      q=2 ∨ q=3 ∨ q=5 ∨ q=7 ∨ q=19 ∨ q=31)
    (ha : padicValNat 2 n % 32=16) :
    65537 ∣ n ∧ 0<n.factorization 65537 ∧ 16∣n.factorization 65537 := by
  have no (q : ℕ) (hq : q.Prime) (hql : q<152)
      (hc : ¬(q=2 ∨ q=3 ∨ q=5 ∨ q=7 ∨ q=19 ∨ q=31)) : ¬q∣n :=
    fun h => hc (hsmall q hq h hql)
  have h257 := no257 h S hS hA hB (no 43 (by norm_num) (by decide) (by decide))
  have h2 : 2∣n := by
    by_contra hh
    have he : padicValNat 2 n=0 := padicValNat.eq_zero_of_not_dvd hh
    omega
  have hp : Nat.Prime 65537 := by norm_num
  have hd : 65537∣n := by
    apply plus_dvd h Nat.prime_two h2 hp (by decide)
    rw [Nat.factorization_def n Nat.prime_two]
    exact mod_power (k:=32) (r:=16) ha (by decide) (by decide)
  have he := hp.factorization_pos_of_dvd h.2.ne' hd
  refine ⟨hd,he,?_⟩
  let e := n.factorization 65537
  have ban (q k r : ℕ) [NeZero q] (hq : q.Prime) (hq2 : q≠2) (hnq : ¬q∣n)
      (hk : (65537:ZMod q)^k=1) (hr : 1+(65537:ZMod q)^r=0) : e%k≠r :=
    fun heq => hnq (plus_dvd h hp hd hq hq2 (mod_power heq hk hr))
  have hodd := ban 11 2 1 (by norm_num) (by decide)
    (no 11 (by norm_num) (by decide) (by decide)) (by decide) (by decide)
  have hfour := ban 17 8 4 (by norm_num) (by decide)
    (no 17 (by norm_num) (by decide) (by decide)) (by decide) (by decide)
  have height := ban 257 16 8 (by norm_num) (by decide) h257 (by decide) (by decide)
  have two : e%4≠2 := by
    intro ht
    have h5 : 5 ∣ 1+65537^e := mod_power (k:=4) ht (by decide) (by decide)
    have p19 : Nat.Prime 19 := by norm_num
    have f19 : n.factorization 19=1 := by
      have hpos := p19.factorization_pos_of_dvd h.2.ne' h19
      by_contra! hh
      have hm := (hS 19).mpr ⟨p19,by decide,(p19.pow_dvd_iff_le_factorization h.2.ne').mpr (by omega)⟩
      have := (hA _ hm).1
      omega
    have sub : ({19,65537} : Finset ℕ)⊆n.primeFactors := by
      intro x hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Nat.mem_primeFactors.mpr ⟨p19,h19,h.2.ne'⟩
      · exact Nat.mem_primeFactors.mpr ⟨hp,hd,h.2.ne'⟩
    have H := Finset.prod_dvd_prod_of_subset _ _ (fun r => 1+r^n.factorization r) sub
    rw [prod_eq_two_mul h,Finset.prod_insert (by decide),Finset.prod_singleton,f19] at H
    have H25 : 25 ∣ 2*n := (Nat.mul_dvd_mul (by decide : 5∣1+19^1) h5).trans H
    have hn25 : 25∣n := (by decide : Nat.Coprime 25 2).dvd_of_dvd_mul_left H25
    have hs5 := (hS 5).mpr ⟨by norm_num,by decide,hn25⟩
    have := (hA 5 hs5).1
    omega
  change 16∣e
  omega


set_option maxRecDepth 6000 in
theorem forced_fermat_chain {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (S : Finset ℕ) (hS : ∀ p, p∈S ↔ p.Prime ∧ p≠2 ∧ p^2∣n)
    (hA : ∀ z∈S, 128≤z ∧ S.card+3≤z)
    (hB : ∏ z∈S, (((z:ℚ)+1)/((z:ℚ)-2-(S.card:ℚ))) ≤ 2101/2097)
    (h19 : 19∣n) (hsmall : ∀ q:ℕ, q.Prime → q∣n → q<152 →
      q=2 ∨ q=3 ∨ q=5 ∨ q=7 ∨ q=19 ∨ q=31)
    (ha : padicValNat 2 n % 32=16) :
    65537∣n ∧ 0<n.factorization 65537 ∧
      (128∣n.factorization 65537 ∨
        (n.factorization 65537%32=16 ∧ 4365089∈S ∧ Even (n.factorization 4365089))) := by
  obtain ⟨hd,hpos,hm⟩ := forced_fermat_exponent h S hS hA hB h19 hsmall ha
  refine ⟨hd,hpos,?_⟩
  have hp : Nat.Prime 65537 := by norm_num
  have no (q : ℕ) (hq : q.Prime) (hql : q<152)
      (hc : ¬(q=2 ∨ q=3 ∨ q=5 ∨ q=7 ∨ q=19 ∨ q=31)) : ¬q∣n :=
    fun h => hc (hsmall q hq h hql)
  have dead (p q : ℕ) (hpp : p.Prime) (hp2 : p≠2) (hlt : p<2100)
      (hqp : q.Prime) (hq2 : q≠2) (hq : ¬q∣n) (hs : q∣1+p) : ¬p∣n := by
    intro hd'
    have he := simple_below h S hS hA hB hpp hp2 hd' hlt
    exact hq (plus_dvd h hpp hd' hqp hq2 (by simpa [he] using hs))
  have h1409 := dead 1409 47 (by norm_num) (by decide) (by decide) (by norm_num)
    (by decide) (no 47 (by norm_num) (by decide) (by decide)) (by decide)
  have h641 := dead 641 107 (by norm_num) (by decide) (by decide) (by norm_num)
    (by decide) (no 107 (by norm_num) (by decide) (by decide)) (by decide)
  let e := n.factorization 65537
  have h₅ : e%64≠32 := fun he => h1409 (plus_dvd h hp hd (by norm_num) (by decide)
    (mod_power he (by decide) (by decide)))
  have h₆ : e%128≠64 := fun he => h641 (plus_dvd h hp hd (by norm_num) (by decide)
    (mod_power he (by decide) (by decide)))
  change 16∣e at hm
  change 128∣e ∨ (e%32=16 ∧ _)
  by_cases he : e%32=16
  · right
    have hq : Nat.Prime 4365089 := by norm_num
    have hd' : 4365089∣n := plus_dvd h hp hd hq (by decide) (mod_power he (by decide) (by decide))
    have he' : n.factorization 4365089%2≠1 :=
      fun hp' => no 17 (by norm_num) (by decide) (by decide)
        (plus_dvd h hq hd' (by norm_num) (by decide) (mod_power hp' (by decide) (by decide)))
    have hpos' := hq.factorization_pos_of_dvd h.2.ne' hd'
    exact ⟨he,(hS _).mpr ⟨hq,by decide,(hq.pow_dvd_iff_le_factorization h.2.ne').mpr (by omega)⟩,
      ⟨n.factorization 4365089/2,by omega⟩⟩
  · left
    omega


private theorem cert_332873 : Nat.Prime 332873 := by
  refine lucas_primality 332873 (3 : ZMod 332873) ?_ (fun q hq hd => ?_)
  · rw [show 332873 - 1 = 332872 from by decide]
    reduce_mod_char
  · have hfac : 332873 - 1 = [2 ^ 3, 41609 ^ 1].prod := by decide
    rw [hfac] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (332873 - 1) / 2 = 166436 from by decide]
      have hm : (3 : ZMod 332873) ^ 166436 = ((332872 : ℕ) : ZMod 332873) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (332873 - 1) / 41609 = 8 from by decide]
      have hm : (3 : ZMod 332873) ^ 8 = ((6561 : ℕ) : ZMod 332873) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide

private theorem cert_6657461 : Nat.Prime 6657461 := by
  refine lucas_primality 6657461 (2 : ZMod 6657461) ?_ (fun q hq hd => ?_)
  · rw [show 6657461 - 1 = 6657460 from by decide]
    reduce_mod_char
  · have hfac : 6657461 - 1 = [2 ^ 2, 5 ^ 1, 332873 ^ 1].prod := by decide
    rw [hfac] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (6657461 - 1) / 2 = 3328730 from by decide]
      have hm : (2 : ZMod 6657461) ^ 3328730 = ((6657460 : ℕ) : ZMod 6657461) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (6657461 - 1) / 5 = 1331492 from by decide]
      have hm : (2 : ZMod 6657461) ^ 1331492 = ((5465752 : ℕ) : ZMod 6657461) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq cert_332873).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (6657461 - 1) / 332873 = 20 from by decide]
      have hm : (2 : ZMod 6657461) ^ 20 = ((1048576 : ℕ) : ZMod 6657461) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide

private theorem cert_33766642193 : Nat.Prime 33766642193 := by
  refine lucas_primality 33766642193 (3 : ZMod 33766642193) ?_ (fun q hq hd => ?_)
  · rw [show 33766642193 - 1 = 33766642192 from by decide]
    reduce_mod_char
  · have hfac : 33766642193 - 1 = [2 ^ 4, 317 ^ 1, 6657461 ^ 1].prod := by decide
    rw [hfac] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (33766642193 - 1) / 2 = 16883321096 from by decide]
      have hm : (3 : ZMod 33766642193) ^ 16883321096 = ((33766642192 : ℕ) : ZMod 33766642193) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (33766642193 - 1) / 317 = 106519376 from by decide]
      have hm : (3 : ZMod 33766642193) ^ 106519376 = ((11945255704 : ℕ) : ZMod 33766642193) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq cert_6657461).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (33766642193 - 1) / 6657461 = 5072 from by decide]
      have hm : (3 : ZMod 33766642193) ^ 5072 = ((2318798926 : ℕ) : ZMod 33766642193) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide

private theorem cert_38899171806337 : Nat.Prime 38899171806337 := by
  refine lucas_primality 38899171806337 (5 : ZMod 38899171806337) ?_ (fun q hq hd => ?_)
  · rw [show 38899171806337 - 1 = 38899171806336 from by decide]
    reduce_mod_char
  · have hfac : 38899171806337 - 1 = [2 ^ 7, 3 ^ 2, 33766642193 ^ 1].prod := by decide
    rw [hfac] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (38899171806337 - 1) / 2 = 19449585903168 from by decide]
      have hm : (5 : ZMod 38899171806337) ^ 19449585903168 = ((38899171806336 : ℕ) : ZMod 38899171806337) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (38899171806337 - 1) / 3 = 12966390602112 from by decide]
      have hm : (5 : ZMod 38899171806337) ^ 12966390602112 = ((38299027378165 : ℕ) : ZMod 38899171806337) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq cert_33766642193).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (38899171806337 - 1) / 33766642193 = 1152 from by decide]
      have hm : (5 : ZMod 38899171806337) ^ 1152 = ((2226109530862 : ℕ) : ZMod 38899171806337) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide

private theorem cert_29416339 : Nat.Prime 29416339 := by
  refine lucas_primality 29416339 (3 : ZMod 29416339) ?_ (fun q hq hd => ?_)
  · rw [show 29416339 - 1 = 29416338 from by decide]
    reduce_mod_char
  · have hfac : 29416339 - 1 = [2 ^ 1, 3 ^ 3, 7 ^ 1, 59 ^ 1, 1319 ^ 1].prod := by decide
    rw [hfac] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (29416339 - 1) / 2 = 14708169 from by decide]
      have hm : (3 : ZMod 29416339) ^ 14708169 = ((29416338 : ℕ) : ZMod 29416339) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (29416339 - 1) / 3 = 9805446 from by decide]
      have hm : (3 : ZMod 29416339) ^ 9805446 = ((5047549 : ℕ) : ZMod 29416339) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (29416339 - 1) / 7 = 4202334 from by decide]
      have hm : (3 : ZMod 29416339) ^ 4202334 = ((25346929 : ℕ) : ZMod 29416339) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (29416339 - 1) / 59 = 498582 from by decide]
      have hm : (3 : ZMod 29416339) ^ 498582 = ((20660007 : ℕ) : ZMod 29416339) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (29416339 - 1) / 1319 = 22302 from by decide]
      have hm : (3 : ZMod 29416339) ^ 22302 = ((6582334 : ℕ) : ZMod 29416339) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide

private theorem cert_731762088686190817 : Nat.Prime 731762088686190817 := by
  refine lucas_primality 731762088686190817 (5 : ZMod 731762088686190817) ?_ (fun q hq hd => ?_)
  · rw [show 731762088686190817 - 1 = 731762088686190816 from by decide]
    reduce_mod_char
  · have hfac : 731762088686190817 - 1 = [2 ^ 5, 3 ^ 1, 19 ^ 2, 43 ^ 1, 16693 ^ 1, 29416339 ^ 1].prod := by decide
    rw [hfac] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (731762088686190817 - 1) / 2 = 365881044343095408 from by decide]
      have hm : (5 : ZMod 731762088686190817) ^ 365881044343095408 = ((731762088686190816 : ℕ) : ZMod 731762088686190817) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (731762088686190817 - 1) / 3 = 243920696228730272 from by decide]
      have hm : (5 : ZMod 731762088686190817) ^ 243920696228730272 = ((394381745381099409 : ℕ) : ZMod 731762088686190817) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (731762088686190817 - 1) / 19 = 38513794141378464 from by decide]
      have hm : (5 : ZMod 731762088686190817) ^ 38513794141378464 = ((447748476139752048 : ℕ) : ZMod 731762088686190817) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (731762088686190817 - 1) / 43 = 17017722992702112 from by decide]
      have hm : (5 : ZMod 731762088686190817) ^ 17017722992702112 = ((241165761140313619 : ℕ) : ZMod 731762088686190817) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (731762088686190817 - 1) / 16693 = 43836463708512 from by decide]
      have hm : (5 : ZMod 731762088686190817) ^ 43836463708512 = ((266737596360658362 : ℕ) : ZMod 731762088686190817) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq cert_29416339).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (731762088686190817 - 1) / 29416339 = 24876042144 from by decide]
      have hm : (5 : ZMod 731762088686190817) ^ 24876042144 = ((687603439277763110 : ℕ) : ZMod 731762088686190817) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide

private theorem cert_319489 : Nat.Prime 319489 := by
  refine lucas_primality 319489 (23 : ZMod 319489) ?_ (fun q hq hd => ?_)
  · rw [show 319489 - 1 = 319488 from by decide]
    reduce_mod_char
  · have hfac : 319489 - 1 = [2 ^ 13, 3 ^ 1, 13 ^ 1].prod := by decide
    rw [hfac] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (319489 - 1) / 2 = 159744 from by decide]
      have hm : (23 : ZMod 319489) ^ 159744 = ((319488 : ℕ) : ZMod 319489) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (319489 - 1) / 3 = 106496 from by decide]
      have hm : (23 : ZMod 319489) ^ 106496 = ((288206 : ℕ) : ZMod 319489) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (319489 - 1) / 13 = 24576 from by decide]
      have hm : (23 : ZMod 319489) ^ 24576 = ((26620 : ℕ) : ZMod 319489) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide

private theorem cert_974849 : Nat.Prime 974849 := by
  refine lucas_primality 974849 (3 : ZMod 974849) ?_ (fun q hq hd => ?_)
  · rw [show 974849 - 1 = 974848 from by decide]
    reduce_mod_char
  · have hfac : 974849 - 1 = [2 ^ 13, 7 ^ 1, 17 ^ 1].prod := by decide
    rw [hfac] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (974849 - 1) / 2 = 487424 from by decide]
      have hm : (3 : ZMod 974849) ^ 487424 = ((974848 : ℕ) : ZMod 974849) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (974849 - 1) / 7 = 139264 from by decide]
      have hm : (3 : ZMod 974849) ^ 139264 = ((487579 : ℕ) : ZMod 974849) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (974849 - 1) / 17 = 57344 from by decide]
      have hm : (3 : ZMod 974849) ^ 57344 = ((190050 : ℕ) : ZMod 974849) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide

private theorem cert_136752547 : Nat.Prime 136752547 := by
  refine lucas_primality 136752547 (3 : ZMod 136752547) ?_ (fun q hq hd => ?_)
  · rw [show 136752547 - 1 = 136752546 from by decide]
    reduce_mod_char
  · have hfac : 136752547 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 151 ^ 1, 21563 ^ 1].prod := by decide
    rw [hfac] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (136752547 - 1) / 2 = 68376273 from by decide]
      have hm : (3 : ZMod 136752547) ^ 68376273 = ((136752546 : ℕ) : ZMod 136752547) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (136752547 - 1) / 3 = 45584182 from by decide]
      have hm : (3 : ZMod 136752547) ^ 45584182 = ((27141881 : ℕ) : ZMod 136752547) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (136752547 - 1) / 7 = 19536078 from by decide]
      have hm : (3 : ZMod 136752547) ^ 19536078 = ((16340858 : ℕ) : ZMod 136752547) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (136752547 - 1) / 151 = 905646 from by decide]
      have hm : (3 : ZMod 136752547) ^ 905646 = ((22818994 : ℕ) : ZMod 136752547) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (136752547 - 1) / 21563 = 6342 from by decide]
      have hm : (3 : ZMod 136752547) ^ 6342 = ((136533696 : ℕ) : ZMod 136752547) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide

private theorem cert_167988556341760475137 : Nat.Prime 167988556341760475137 := by
  refine lucas_primality 167988556341760475137 (5 : ZMod 167988556341760475137) ?_ (fun q hq hd => ?_)
  · rw [show 167988556341760475137 - 1 = 167988556341760475136 from by decide]
    reduce_mod_char
  · have hfac : 167988556341760475137 - 1 = [2 ^ 14, 3 ^ 1, 373 ^ 1, 67003 ^ 1, 136752547 ^ 1].prod := by decide
    rw [hfac] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (167988556341760475137 - 1) / 2 = 83994278170880237568 from by decide]
      have hm : (5 : ZMod 167988556341760475137) ^ 83994278170880237568 = ((167988556341760475136 : ℕ) : ZMod 167988556341760475137) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (167988556341760475137 - 1) / 3 = 55996185447253491712 from by decide]
      have hm : (5 : ZMod 167988556341760475137) ^ 55996185447253491712 = ((83677090702833273328 : ℕ) : ZMod 167988556341760475137) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (167988556341760475137 - 1) / 373 = 450371464723218432 from by decide]
      have hm : (5 : ZMod 167988556341760475137) ^ 450371464723218432 = ((125490435045567633184 : ℕ) : ZMod 167988556341760475137) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (167988556341760475137 - 1) / 67003 = 2507179623923712 from by decide]
      have hm : (5 : ZMod 167988556341760475137) ^ 2507179623923712 = ((80297890431604984557 : ℕ) : ZMod 167988556341760475137) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq cert_136752547).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (167988556341760475137 - 1) / 136752547 = 1228412633088 from by decide]
      have hm : (5 : ZMod 167988556341760475137) ^ 1228412633088 = ((53432824125450223362 : ℕ) : ZMod 167988556341760475137) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide

private theorem cert_2021081 : Nat.Prime 2021081 := by
  refine lucas_primality 2021081 (3 : ZMod 2021081) ?_ (fun q hq hd => ?_)
  · rw [show 2021081 - 1 = 2021080 from by decide]
    reduce_mod_char
  · have hfac : 2021081 - 1 = [2 ^ 3, 5 ^ 1, 50527 ^ 1].prod := by decide
    rw [hfac] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (2021081 - 1) / 2 = 1010540 from by decide]
      have hm : (3 : ZMod 2021081) ^ 1010540 = ((2021080 : ℕ) : ZMod 2021081) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (2021081 - 1) / 5 = 404216 from by decide]
      have hm : (3 : ZMod 2021081) ^ 404216 = ((719998 : ℕ) : ZMod 2021081) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (2021081 - 1) / 50527 = 40 from by decide]
      have hm : (3 : ZMod 2021081) ^ 40 = ((841231 : ℕ) : ZMod 2021081) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide

private theorem cert_3781909 : Nat.Prime 3781909 := by
  refine lucas_primality 3781909 (6 : ZMod 3781909) ?_ (fun q hq hd => ?_)
  · rw [show 3781909 - 1 = 3781908 from by decide]
    reduce_mod_char
  · have hfac : 3781909 - 1 = [2 ^ 2, 3 ^ 2, 13 ^ 1, 8081 ^ 1].prod := by decide
    rw [hfac] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (3781909 - 1) / 2 = 1890954 from by decide]
      have hm : (6 : ZMod 3781909) ^ 1890954 = ((3781908 : ℕ) : ZMod 3781909) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (3781909 - 1) / 3 = 1260636 from by decide]
      have hm : (6 : ZMod 3781909) ^ 1260636 = ((1649099 : ℕ) : ZMod 3781909) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (3781909 - 1) / 13 = 290916 from by decide]
      have hm : (6 : ZMod 3781909) ^ 290916 = ((1729742 : ℕ) : ZMod 3781909) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (3781909 - 1) / 8081 = 468 from by decide]
      have hm : (6 : ZMod 3781909) ^ 468 = ((1268425 : ℕ) : ZMod 3781909) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide

private theorem cert_91722533083549 : Nat.Prime 91722533083549 := by
  refine lucas_primality 91722533083549 (10 : ZMod 91722533083549) ?_ (fun q hq hd => ?_)
  · rw [show 91722533083549 - 1 = 91722533083548 from by decide]
    reduce_mod_char
  · have hfac : 91722533083549 - 1 = [2 ^ 2, 3 ^ 1, 2021081 ^ 1, 3781909 ^ 1].prod := by decide
    rw [hfac] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (91722533083549 - 1) / 2 = 45861266541774 from by decide]
      have hm : (10 : ZMod 91722533083549) ^ 45861266541774 = ((91722533083548 : ℕ) : ZMod 91722533083549) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (91722533083549 - 1) / 3 = 30574177694516 from by decide]
      have hm : (10 : ZMod 91722533083549) ^ 30574177694516 = ((3734035927748 : ℕ) : ZMod 91722533083549) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq cert_2021081).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (91722533083549 - 1) / 2021081 = 45382908 from by decide]
      have hm : (10 : ZMod 91722533083549) ^ 45382908 = ((67613535417156 : ℕ) : ZMod 91722533083549) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq cert_3781909).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (91722533083549 - 1) / 3781909 = 24252972 from by decide]
      have hm : (10 : ZMod 91722533083549) ^ 24252972 = ((51972370100311 : ℕ) : ZMod 91722533083549) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide

private theorem cert_3560841906445833920513 : Nat.Prime 3560841906445833920513 := by
  refine lucas_primality 3560841906445833920513 (3 : ZMod 3560841906445833920513) ?_ (fun q hq hd => ?_)
  · rw [show 3560841906445833920513 - 1 = 3560841906445833920512 from by decide]
    reduce_mod_char
  · have hfac : 3560841906445833920513 - 1 = [2 ^ 13, 7 ^ 1, 677 ^ 1, 91722533083549 ^ 1].prod := by decide
    rw [hfac] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (3560841906445833920513 - 1) / 2 = 1780420953222916960256 from by decide]
      have hm : (3 : ZMod 3560841906445833920513) ^ 1780420953222916960256 = ((3560841906445833920512 : ℕ) : ZMod 3560841906445833920513) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (3560841906445833920513 - 1) / 7 = 508691700920833417216 from by decide]
      have hm : (3 : ZMod 3560841906445833920513) ^ 508691700920833417216 = ((3020034282294119301184 : ℕ) : ZMod 3560841906445833920513) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (3560841906445833920513 - 1) / 677 = 5259736937143033856 from by decide]
      have hm : (3 : ZMod 3560841906445833920513) ^ 5259736937143033856 = ((94449858441103718122 : ℕ) : ZMod 3560841906445833920513) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq cert_91722533083549).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (3560841906445833920513 - 1) / 91722533083549 = 38821888 from by decide]
      have hm : (3 : ZMod 3560841906445833920513) ^ 38821888 = ((2621264577600180401753 : ℕ) : ZMod 3560841906445833920513) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide

private theorem cert_114689 : Nat.Prime 114689 := by
  refine lucas_primality 114689 (3 : ZMod 114689) ?_ (fun q hq hd => ?_)
  · rw [show 114689 - 1 = 114688 from by decide]
    reduce_mod_char
  · have hfac : 114689 - 1 = [2 ^ 14, 7 ^ 1].prod := by decide
    rw [hfac] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (114689 - 1) / 2 = 57344 from by decide]
      have hm : (3 : ZMod 114689) ^ 57344 = ((114688 : ℕ) : ZMod 114689) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (114689 - 1) / 7 = 16384 from by decide]
      have hm : (3 : ZMod 114689) ^ 16384 = ((72185 : ℕ) : ZMod 114689) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide

private theorem cert_26017793 : Nat.Prime 26017793 := by
  refine lucas_primality 26017793 (3 : ZMod 26017793) ?_ (fun q hq hd => ?_)
  · rw [show 26017793 - 1 = 26017792 from by decide]
    reduce_mod_char
  · have hfac : 26017793 - 1 = [2 ^ 16, 397 ^ 1].prod := by decide
    rw [hfac] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (26017793 - 1) / 2 = 13008896 from by decide]
      have hm : (3 : ZMod 26017793) ^ 13008896 = ((26017792 : ℕ) : ZMod 26017793) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (26017793 - 1) / 397 = 65536 from by decide]
      have hm : (3 : ZMod 26017793) ^ 65536 = ((6782830 : ℕ) : ZMod 26017793) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide

private theorem cert_63766529 : Nat.Prime 63766529 := by
  refine lucas_primality 63766529 (13 : ZMod 63766529) ?_ (fun q hq hd => ?_)
  · rw [show 63766529 - 1 = 63766528 from by decide]
    reduce_mod_char
  · have hfac : 63766529 - 1 = [2 ^ 16, 7 ^ 1, 139 ^ 1].prod := by decide
    rw [hfac] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (63766529 - 1) / 2 = 31883264 from by decide]
      have hm : (13 : ZMod 63766529) ^ 31883264 = ((63766528 : ℕ) : ZMod 63766529) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (63766529 - 1) / 7 = 9109504 from by decide]
      have hm : (13 : ZMod 63766529) ^ 9109504 = ((59264981 : ℕ) : ZMod 63766529) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (63766529 - 1) / 139 = 458752 from by decide]
      have hm : (13 : ZMod 63766529) ^ 458752 = ((36823255 : ℕ) : ZMod 63766529) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide

private theorem cert_211153 : Nat.Prime 211153 := by
  refine lucas_primality 211153 (5 : ZMod 211153) ?_ (fun q hq hd => ?_)
  · rw [show 211153 - 1 = 211152 from by decide]
    reduce_mod_char
  · have hfac : 211153 - 1 = [2 ^ 4, 3 ^ 1, 53 ^ 1, 83 ^ 1].prod := by decide
    rw [hfac] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (211153 - 1) / 2 = 105576 from by decide]
      have hm : (5 : ZMod 211153) ^ 105576 = ((211152 : ℕ) : ZMod 211153) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (211153 - 1) / 3 = 70384 from by decide]
      have hm : (5 : ZMod 211153) ^ 70384 = ((21801 : ℕ) : ZMod 211153) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (211153 - 1) / 53 = 3984 from by decide]
      have hm : (5 : ZMod 211153) ^ 3984 = ((167610 : ℕ) : ZMod 211153) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (211153 - 1) / 83 = 2544 from by decide]
      have hm : (5 : ZMod 211153) ^ 2544 = ((26513 : ℕ) : ZMod 211153) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide

private theorem cert_190274191361 : Nat.Prime 190274191361 := by
  refine lucas_primality 190274191361 (3 : ZMod 190274191361) ?_ (fun q hq hd => ?_)
  · rw [show 190274191361 - 1 = 190274191360 from by decide]
    reduce_mod_char
  · have hfac : 190274191361 - 1 = [2 ^ 14, 5 ^ 1, 11 ^ 1, 211153 ^ 1].prod := by decide
    rw [hfac] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (190274191361 - 1) / 2 = 95137095680 from by decide]
      have hm : (3 : ZMod 190274191361) ^ 95137095680 = ((190274191360 : ℕ) : ZMod 190274191361) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (190274191361 - 1) / 5 = 38054838272 from by decide]
      have hm : (3 : ZMod 190274191361) ^ 38054838272 = ((143396534158 : ℕ) : ZMod 190274191361) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (190274191361 - 1) / 11 = 17297653760 from by decide]
      have hm : (3 : ZMod 190274191361) ^ 17297653760 = ((75995081630 : ℕ) : ZMod 190274191361) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide
    · have he := (Nat.prime_dvd_prime_iff_eq hq cert_211153).mp (hq.dvd_of_dvd_pow hqx)
      subst he
      rw [show (190274191361 - 1) / 211153 = 901120 from by decide]
      have hm : (3 : ZMod 190274191361) ^ 901120 = ((21662065745 : ℕ) : ZMod 190274191361) := by
        push_cast
        reduce_mod_char
      rw [hm]
      decide

private theorem residue_case {a : ℕ} (h : 16∣a) (hh : a%64≠32) : 64∣a ∨ a%32=16 := by omega

private theorem extra_squareful {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (S : Finset ℕ) (hS : ∀ p, p∈S ↔ p.Prime ∧ p≠2 ∧ p^2∣n)
    (hsmall : ∀ q:ℕ, q.Prime → q∣n → q<152 →
      q=2 ∨ q=3 ∨ q=5 ∨ q=7 ∨ q=19 ∨ q=31)
    (hp : 65537∣n) (he : n.factorization 65537%32=16) :
    38899171806337∈S ∧ 731762088686190817∈S := by
  have dead (p q : ℕ) [NeZero p] (hpr : p.Prime) (hp2 : p≠2) (hqr : q.Prime)
      (hq2 : q≠2) (hlt : q<152) (hno : ¬(q=2 ∨ q=3 ∨ q=5 ∨ q=7 ∨ q=19 ∨ q=31))
      (h0 : (65537:ZMod p)^32=1) (h1 : 1+(65537:ZMod p)^16=0) (hdiv : q∣1+p) : p∈S := by
    have hd := plus_dvd h (by norm_num : Nat.Prime 65537) hp hpr hp2 (mod_power he h0 h1)
    have hpos := hpr.factorization_pos_of_dvd h.2.ne' hd
    apply (hS p).mpr
    refine ⟨hpr,hp2,(hpr.pow_dvd_iff_le_factorization h.2.ne').mpr ?_⟩
    by_contra! hh
    have hx : n.factorization p=1 := by omega
    exact hno (hsmall q hqr (plus_dvd h hpr hd hqr hq2 (by simpa [hx] using hdiv)) hlt)
  exact ⟨dead 38899171806337 23 cert_38899171806337 (by decide) (by norm_num)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    dead 731762088686190817 131 cert_731762088686190817 (by decide) (by norm_num)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩

private theorem no_five (S : Finset ℕ) (hs : S.card ≤ 4) (h₁ : 3967∈S) (h₂ : 65537∈S)
    (h₃ : 4365089∈S) (h₄ : 38899171806337∈S) (h₅ : 731762088686190817∈S) : False := by
  have hsub : ({3967,65537,4365089,38899171806337,731762088686190817} : Finset ℕ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hh := Finset.card_le_card hsub
  have hcard : ({3967,65537,4365089,38899171806337,731762088686190817} : Finset ℕ).card=5 := by decide
  omega

private theorem forced_squareful_of_bad_succ {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (S : Finset ℕ) (hS : ∀ p, p∈S ↔ p.Prime ∧ p≠2 ∧ p^2∣n)
    (h3 : n.factorization 3=1) (h5 : 5∣n) (h5e : n.factorization 5=1)
    (hsmall : ∀ q:ℕ, q.Prime → q∣n → q<152 →
      q=2 ∨ q=3 ∨ q=5 ∨ q=7 ∨ q=19 ∨ q=31)
    {p : ℕ} (hp : p.Prime) (hd : p∣n) (hp2 : p≠2) (hp5 : p≠5)
    (hbad : 3∣1+p ∨ ∃ q:ℕ, q.Prime ∧ q≠2 ∧ q<152 ∧
      ¬(q=2 ∨ q=3 ∨ q=5 ∨ q=7 ∨ q=19 ∨ q=31) ∧ q∣1+p) : p∈S := by
  have hpos := hp.factorization_pos_of_dvd h.2.ne' hd
  apply (hS p).mpr
  refine ⟨hp,hp2,(hp.pow_dvd_iff_le_factorization h.2.ne').mpr ?_⟩
  by_contra! hh
  have he : n.factorization p=1 := by omega
  rcases hbad with hb | ⟨q,hq,hq2,hql,hnq,hqb⟩
  · have hsub : ({p,5}:Finset ℕ)⊆n.primeFactors := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Nat.mem_primeFactors.mpr ⟨hp,hd,h.2.ne'⟩
      · exact Nat.mem_primeFactors.mpr ⟨by norm_num,h5,h.2.ne'⟩
    have hh' := Finset.prod_dvd_prod_of_subset _ _ (fun r => 1+r^n.factorization r) hsub
    rw [prod_eq_two_mul h,Finset.prod_insert (by simpa using hp5),Finset.prod_singleton,he,h5e,
      pow_one,pow_one] at hh'
    have h9 : 9∣2*n := (Nat.mul_dvd_mul hb (by decide : 3∣1+5)).trans hh'
    have := ((by norm_num : Nat.Prime 3).pow_dvd_iff_le_factorization h.2.ne').mp
      (show 3^2∣n from (by decide : Nat.Coprime 9 2).dvd_of_dvd_mul_left h9)
    omega
  · exact hnq (hsmall q hq (plus_dvd h hp hd hq hq2 (by simpa [he] using hqb)) hql)

private theorem seed_factor {n k r p : ℕ} [NeZero p] (h : Erdos1052.IsUnitaryPerfect n)
    (hp : p.Prime) (hp2 : p≠2) (ha : padicValNat 2 n%k=r) (hr : r≠0)
    (hd : (2:ZMod p)^k=1) (he : 1+(2:ZMod p)^r=0) : p∣n := by
  have h2 : 2∣n := by
    by_contra hh
    rw [padicValNat.eq_zero_of_not_dvd hh,Nat.zero_mod] at ha
    exact hr ha.symm
  apply plus_dvd h Nat.prime_two h2 hp hp2
  rw [Nat.factorization_def n Nat.prime_two]
  exact mod_power ha hd he


private theorem cardinal_exclusions {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (S : Finset ℕ) (hS : ∀ p, p∈S ↔ p.Prime ∧ p≠2 ∧ p^2∣n)
    (hA : ∀ z∈S, 128≤z ∧ S.card+3≤z)
    (hB : ∏ z∈S, (((z:ℚ)+1)/((z:ℚ)-2-(S.card:ℚ))) ≤ 2101/2097)
    (h3 : 3∣n) (h5 : 5∣n)
    (hsmall : ∀ q:ℕ, q.Prime → q∣n → q<152 →
      q=2 ∨ q=3 ∨ q=5 ∨ q=7 ∨ q=19 ∨ q=31)
    (hs : 3967∈S) (hc : S.card≤4) :
    padicValNat 2 n%4096≠2048 ∧ padicValNat 2 n%8192≠4096 := by
  have h3e := simple_below h S hS hA hB (by norm_num : Nat.Prime 3) (by decide) h3 (by decide)
  have h5e := simple_below h S hS hA hB (by norm_num : Nat.Prime 5) (by decide) h5 (by decide)
  constructor
  · intro ha
    have hm0 : 319489∈S := forced_squareful_of_bad_succ h S hS h3e h5 h5e hsmall
      cert_319489 (seed_factor h cert_319489 (by decide) ha (by decide)
        (by reduce_mod_char) (by reduce_mod_char)) (by decide) (by decide) (Or.inr ⟨43,by norm_num,by decide,by decide,by decide,by decide⟩)
    have hm1 : 974849∈S := forced_squareful_of_bad_succ h S hS h3e h5 h5e hsmall
      cert_974849 (seed_factor h cert_974849 (by decide) ha (by decide)
        (by reduce_mod_char) (by reduce_mod_char)) (by decide) (by decide) (Or.inl (by decide))
    have hm2 : 167988556341760475137∈S := forced_squareful_of_bad_succ h S hS h3e h5 h5e hsmall
      cert_167988556341760475137 (seed_factor h cert_167988556341760475137 (by decide) ha (by decide)
        (by reduce_mod_char) (by reduce_mod_char)) (by decide) (by decide) (Or.inr ⟨17,by norm_num,by decide,by decide,by decide,by decide⟩)
    have hm3 : 3560841906445833920513∈S := forced_squareful_of_bad_succ h S hS h3e h5 h5e hsmall
      cert_3560841906445833920513 (seed_factor h cert_3560841906445833920513 (by decide) ha (by decide)
        (by reduce_mod_char) (by reduce_mod_char)) (by decide) (by decide) (Or.inl (by decide))
    have hsub : ({3967,319489,974849,167988556341760475137,3560841906445833920513} : Finset ℕ)⊆S := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
    have hu := Finset.card_le_card hsub
    have hcard : ({3967,319489,974849,167988556341760475137,3560841906445833920513} : Finset ℕ).card=5 := by decide
    omega
  · intro ha
    have hm0 : 114689∈S := forced_squareful_of_bad_succ h S hS h3e h5 h5e hsmall
      cert_114689 (seed_factor h cert_114689 (by decide) ha (by decide)
        (by reduce_mod_char) (by reduce_mod_char)) (by decide) (by decide) (Or.inl (by decide))
    have hm1 : 26017793∈S := forced_squareful_of_bad_succ h S hS h3e h5 h5e hsmall
      cert_26017793 (seed_factor h cert_26017793 (by decide) ha (by decide)
        (by reduce_mod_char) (by reduce_mod_char)) (by decide) (by decide) (Or.inl (by decide))
    have hm2 : 63766529∈S := forced_squareful_of_bad_succ h S hS h3e h5 h5e hsmall
      cert_63766529 (seed_factor h cert_63766529 (by decide) ha (by decide)
        (by reduce_mod_char) (by reduce_mod_char)) (by decide) (by decide) (Or.inl (by decide))
    have hm3 : 190274191361∈S := forced_squareful_of_bad_succ h S hS h3e h5 h5e hsmall
      cert_190274191361 (seed_factor h cert_190274191361 (by decide) ha (by decide)
        (by reduce_mod_char) (by reduce_mod_char)) (by decide) (by decide) (Or.inl (by decide))
    have hsub : ({3967,114689,26017793,63766529,190274191361} : Finset ℕ)⊆S := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
    have hu := Finset.card_le_card hsub
    have hcard : ({3967,114689,26017793,63766529,190274191361} : Finset ℕ).card=5 := by decide
    omega


private lemma abundancy {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (E : Finset ℕ)
    (hs : E ⊆ n.primeFactors) (he : ∀ z∈E, n.factorization z=1) :
    (∏ z∈E, ((z:ℚ)+1)/z) ≤ 2 := by
  let f (r : ℕ) : ℚ := (1+((r^n.factorization r : ℕ):ℚ))/(r^n.factorization r : ℕ)
  have hf (r : ℕ) (hr : r∈n.primeFactors) : 1≤f r := by
    have hr' : 0<r := (Nat.prime_of_mem_primeFactors hr).pos
    dsimp [f]
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hall : (∏ r∈n.primeFactors, f r) = 2 := by
    dsimp only [f]
    rw [prod_div_distrib]
    have h₁ : (∏ r∈n.primeFactors, (1+((r^n.factorization r : ℕ):ℚ)))=2*(n:ℚ) := by
      exact_mod_cast prod_eq_two_mul h
    have h₂ : (∏ r∈n.primeFactors, ((r^n.factorization r : ℕ):ℚ))=n := by
      exact_mod_cast prod_primeFactors_pow_self h.2.ne'
    rw [h₁,h₂]
    have hn : (n:ℚ)≠0 := by exact_mod_cast h.2.ne'
    field_simp
  rw [←hall]
  calc
    _ = ∏ r∈E,f r := Finset.prod_congr rfl fun r hr => by simp [f, he r hr,add_comm]
    _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le hs
      (fun r hr => zero_le_one.trans (hf r (hs hr))) (fun r hr _ => hf r hr)

theorem additional_simple_cutoff {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hc : ∀ z∈({3,5,7,19,31,223,607,3967} : Finset ℕ), n.factorization z=1)
    {q : ℕ} (hq : q.Prime) (he : n.factorization q=1)
    (hnew : q∉({3,5,7,19,31,223,607,3967} : Finset ℕ)) : 5057 ≤ q := by
  let E : Finset ℕ := {3,5,7,19,31,223,607,3967}
  have exp1 (z : ℕ) (hz : z∈insert q E) : n.factorization z=1 := by
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact he
    · exact hc z hz
  have hs : insert q E ⊆ n.primeFactors := by
    intro z hz
    rw [←Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by rw [exp1 z hz]; decide)
  have H := abundancy h (insert q E) hs exp1
  rw [Finset.prod_insert (show q∉E from hnew)] at H
  have hh : (∏ z∈E, ((z:ℚ)+1)/z)=1073741824/536977087 := by
    norm_num [E, Finset.prod_insert]
  rw [hh] at H
  have hqp : 0<(q:ℚ) := by exact_mod_cast hq.pos
  have H' := (div_le_iff₀ hqp).mp (show ((q:ℚ)+1)/q ≤ 2/(1073741824/536977087) by
    apply (le_div_iff₀ (by norm_num)).mpr
    exact H)
  by_contra! hy
  have hy' : (q:ℚ) ≤ 5056 := by exact_mod_cast (show q≤5056 by omega)
  linarith


private theorem small_squareful_count {c : ℕ} (h : 2101*c+6299≤4*3967) : c≤4 := by omega

private theorem two_le_of_residue {e : ℕ} (h : e%32=16) : 2≤e := by omega

private theorem two_le_of_not_one {e : ℕ} (h : 0<e) (hh : e≠1) : 2≤e := by omega

set_option maxHeartbeats 1000000 in
theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H3_R1.H1 := by
  rintro ⟨A,h₁⟩ ⟨B,h₂⟩
  refine ⟨max A B, ?_⟩
  intro n h hsq S hS hA hB h4 h3 h5 h7 h19 hres h16 h64 h31 hsmall h607 h223 h433 h991 h1213 h1783 h3967
  have hc : 64 ∣ padicValNat 2 n ∨
      (padicValNat 2 n % 32 = 16 ∧ 65537 ∣ n ∧ 0 < n.factorization 65537 ∧
       (128 ∣ n.factorization 65537 ∨ (n.factorization 65537 % 32 = 16 ∧
          4365089 ∈ S ∧ Even (n.factorization 4365089) ∧
          38899171806337 ∈ S ∧ 731762088686190817 ∈ S))) := by
    rcases residue_case h16 h64 with hh | ha
    · exact Or.inl hh
    · obtain ⟨hd,he,hg⟩ := forced_fermat_chain h S hS hA hB h19 hsmall ha
      refine Or.inr ⟨ha,hd,he,?_⟩
      rcases hg with ht | ⟨ht,hs,hev⟩
      · exact Or.inl ht
      · exact Or.inr ⟨ht,hs,hev,extra_squareful h S hS hsmall hd ht⟩
  by_cases hs : 3967∈S
  · have hbu := squareful_budget S hA hB hs
    have hcard : S.card≤4 := small_squareful_count hbu
    have hc' : 64∣padicValNat 2 n ∨
        (padicValNat 2 n%32=16 ∧ 65537∣n ∧ 0<n.factorization 65537 ∧ 128∣n.factorization 65537) := by
      rcases hc with hh | ⟨ha,hd,he,ht | ⟨heq,h₃,_,h₄,h₅⟩⟩
      · exact Or.inl hh
      · exact Or.inr ⟨ha,hd,he,ht⟩
      · have h₂' := (hS 65537).mpr ⟨by norm_num,by decide,
          (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num : Nat.Prime 65537) h.2.ne').mpr
            (two_le_of_residue heq)⟩
        exact (no_five S hcard hs h₂' h₃ h₄ h₅).elim
    obtain ⟨hf11,hf12⟩ := cardinal_exclusions h S hS hA hB h3 h5 hsmall hs hcard
    exact (h₂ n h hsq S hS hA hB h4 h3 h5 h7 h19 hres h16 h64 h31 hsmall h607 h223
      h433 h991 h1213 h1783 h3967 hc' hs hcard hf11 hf12).trans (le_max_right _ _)
  · have hp : Nat.Prime 3967 := by norm_num
    have he : n.factorization 3967=1 := by
      have hpos := hp.factorization_pos_of_dvd h.2.ne' h3967
      by_contra! hm
      exact hs ((hS _).mpr ⟨hp,by decide,(hp.pow_dvd_iff_le_factorization h.2.ne').mpr (two_le_of_not_one hpos hm)⟩)
    have hcore (z : ℕ) (hz : z∈({3,5,7,19,31,223,607,3967} : Finset ℕ)) :
        n.factorization z=1 := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact simple_below h S hS hA hB (by norm_num : Nat.Prime 3) (by decide) h3 (by decide)
      · exact simple_below h S hS hA hB (by norm_num : Nat.Prime 5) (by decide) h5 (by decide)
      · exact simple_below h S hS hA hB (by norm_num : Nat.Prime 7) (by decide) h7 (by decide)
      · exact simple_below h S hS hA hB (by norm_num : Nat.Prime 19) (by decide) h19 (by decide)
      · exact simple_below h S hS hA hB (by norm_num : Nat.Prime 31) (by decide) h31 (by decide)
      · exact simple_below h S hS hA hB (by norm_num : Nat.Prime 223) (by decide) h223 (by decide)
      · exact simple_below h S hS hA hB (by norm_num : Nat.Prime 607) (by decide) h607 (by decide)
      · exact he
    exact (h₁ n h hsq S hS hA hB h4 h3 h5 h7 h19 hres h16 h64 h31 hsmall h607 h223
      h433 h991 h1213 h1783 h3967 hc he
      (fun _ hq hx hn => additional_simple_cutoff h hcore hq hx hn)).trans (le_max_left _ _)


end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H3_R1_H1_R1
