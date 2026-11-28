import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H3_R1

/-!
Reduction of Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H1.R1.H3.R1.H1. Credit: @saientropy.
The unique factor 31 distinguishes the two cases. Exact prime forcing also eliminates
seven divisors in the odd case and two power-of-two residue classes in the even case.
The unitary divisor product identity comes from the first reduction by Adam Carter (@adammcarter).
-/

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H3_R1_H1_R2

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
    Odd (n.factorization 3967) →
    ¬ 31 ∣ n.factorization 3967 →
    (∀ d ∈ ({5,11,13,23,29,41,53} : Finset ℕ), ¬ d ∣ n.factorization 3967) →
    (∀ q ∈ n.primeFactors, q ≠ 3967 → ¬ 31 ∣ 1 + q ^ n.factorization q) →
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
    Even (n.factorization 3967) →
    n.factorization 3967 % 128 ≠ 64 → n.factorization 3967 % 512 ≠ 256 →
    (∃ q ∈ n.primeFactors, q ≠ 3967 ∧ 31 ∣ 1 + q ^ n.factorization q) →
    (n.factorization 3967 % 2048 = 1024 → 61441 ∈ S) →
    padicValNat 2 n ≤ A

open Finset

private theorem two_weight_bound (S : Finset ℕ) {x y m : ℕ}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) (hm : m ≤ S.card)
    (hsize : ∀ z ∈ S, S.card + 3 ≤ z)
    (hcap : ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) :
    (((x : ℚ) + 1) / ((x : ℚ) - 2 - (m : ℚ))) * (((y : ℚ) + 1) / ((y : ℚ) - 2 - (m : ℚ))) ≤ 2101 / 2097 := by
  have pos (z : ℕ) (hz : z ∈ S) : 0 < (z : ℚ) - 2 - S.card := by
    have h : (S.card : ℚ) + 3 ≤ z := by exact_mod_cast hsize z hz
    linarith
  have lower (z : ℕ) (hz : z ∈ S) : 1 ≤ (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) := by
    rw [le_div_iff₀ (pos z hz)]
    have hc : 0 ≤ (S.card : ℚ) := by positivity
    linarith
  have grow (z : ℕ) (hz : z ∈ S) : (((z : ℚ) + 1) / ((z : ℚ) - 2 - (m : ℚ))) ≤ (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) := by
    apply div_le_div_of_nonneg_left (by positivity) (pos z hz)
    have hh : (m : ℚ) ≤ S.card := by exact_mod_cast hm
    linarith
  have nonneg (z : ℕ) (hz : z ∈ S) : 0 ≤ (((z : ℚ) + 1) / ((z : ℚ) - 2 - (m : ℚ))) := by
    have hh : (m : ℚ) ≤ S.card := by exact_mod_cast hm
    exact div_nonneg (by positivity) (by linarith [pos z hz])
  have hsub : ({x,y} : Finset ℕ) ⊆ S := by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hx hy
  have hb := Finset.prod_le_prod_of_subset_of_one_le hsub
    (fun z hz => zero_le_one.trans (lower z (hsub hz))) (fun z hz _ => lower z hz)
  rw [Finset.prod_insert (by simpa using hxy), Finset.prod_singleton] at hb
  exact (mul_le_mul (grow x hx) (grow y hy) (nonneg y hy)
    (zero_le_one.trans (lower x hx))).trans (hb.trans hcap)

private theorem forced_factor {n p r : ℕ} (hn : n ≠ 0)
    (hprod : ∏ z ∈ n.primeFactors, (1 + z ^ n.factorization z) = 2 * n)
    (hp : p.Prime) (hpn : p ∣ n) (hr : r.Prime) (hr2 : r ≠ 2)
    (hdiv : r ∣ 1 + p ^ n.factorization p) : r ∣ n := by
  have hmem := Nat.mem_primeFactors.mpr ⟨hp,hpn,hn⟩
  have h := Finset.dvd_prod_of_mem (fun z => 1 + z ^ n.factorization z) hmem
  rw [hprod] at h
  exact (hr.dvd_mul.mp (hdiv.trans h)).resolve_left
    (fun hd => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hd))

private theorem force_squareful {n p u v : ℕ} (hn : n ≠ 0)
    (hprod : ∏ z ∈ n.primeFactors, (1 + z ^ n.factorization z) = 2 * n)
    (hp : p.Prime) (hpn : p ∣ n) (hu : u.Prime) (hun : u ∣ n)
    (hpu : p ≠ u) (hue : n.factorization u = 1)
    (hv : v.Prime) (hve : n.factorization v = 1)
    (hodd : (v ^ 2).Coprime 2) (hvp : v ∣ 1 + p) (hvu : v ∣ 1 + u) :
    p ^ 2 ∣ n := by
  apply (hp.pow_dvd_iff_le_factorization hn).mpr
  by_contra! hsmall
  have hpos := hp.factorization_pos_of_dvd hn hpn
  have hpe : n.factorization p = 1 := by omega
  have hsub : ({p,u} : Finset ℕ) ⊆ n.primeFactors := by
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro (Nat.mem_primeFactors.mpr ⟨hp,hpn,hn⟩)
      (Nat.mem_primeFactors.mpr ⟨hu,hun,hn⟩)
  have h := Finset.prod_dvd_prod_of_subset _ _ (fun z => 1 + z ^ n.factorization z) hsub
  rw [hprod, Finset.prod_insert (by simpa using hpu), Finset.prod_singleton,
    hpe, hue, pow_one, pow_one] at h
  have hsq : v ^ 2 ∣ 2 * n := by simpa [pow_two] using (Nat.mul_dvd_mul hvp hvu).trans h
  have hle := (hv.pow_dvd_iff_le_factorization hn).mp (hodd.dvd_of_dvd_mul_left hsq)
  omega

private theorem power_residue {p e k r : ℕ} [NeZero p] (he : e % k = r)
    (hk : (3967 : ZMod p) ^ k = 1) (hr : 1 + (3967 : ZMod p) ^ r = 0) :
    p ∣ 1 + 3967 ^ e := by
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  push_cast
  have h : e = r + k * (e / k) := by rw [←he, Nat.mod_add_div]
  rw [h, pow_add, pow_mul, hk, one_pow, mul_one]
  exact hr

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem exponent_exclusions_of_product {n : ℕ} (hn : n ≠ 0)
    (hprod : ∏ z ∈ n.primeFactors, (1 + z ^ n.factorization z) = 2 * n)
    (S : Finset ℕ) (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hadm : ∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z)
    (hcap : ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097)
    (h3 : 3 ∣ n) (h5 : 5 ∣ n) (h19 : 19 ∣ n) (h3967 : 3967 ∣ n) :
    n.factorization 3967 % 128 ≠ 64 ∧ n.factorization 3967 % 512 ≠ 256 := by
  have simple {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hnp : p ∣ n) (hlt : p < 128) :
      n.factorization p = 1 := by
    have hpos := hp.factorization_pos_of_dvd hn hnp
    by_contra! hh
    have hx := (hS p).mpr ⟨hp,hp2,(hp.pow_dvd_iff_le_factorization hn).mpr (by omega)⟩
    exact (not_le_of_gt hlt) (hadm _ hx).1
  have h3e := simple (by norm_num : Nat.Prime 3) (by decide) h3 (by decide)
  have h5e := simple (by norm_num : Nat.Prime 5) (by decide) h5 (by decide)
  have h19e := simple (by norm_num : Nat.Prime 19) (by decide) h19 (by decide)
  have hp : Nat.Prime 3967 := by norm_num
  have sq {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr5 : r ≠ 5)
      (hd : r ∣ n) (hsucc : 3 ∣ 1+r) : r ∈ S :=
    (hS _).mpr ⟨hr,hr2,force_squareful hn hprod hr hd (by norm_num) h5 hr5
      h5e (by norm_num) h3e (by decide) hsucc (by decide)⟩
  have hsize (z : ℕ) (hz : z ∈ S) := (hadm z hz).2
  constructor
  · intro he
    have hs := (hS _).mpr ⟨hp,by decide,(hp.pow_dvd_iff_le_factorization hn).mpr (by omega)⟩
    have hr : Nat.Prime 2689 := by norm_num
    have hd := forced_factor hn hprod hp h3967 hr (by decide)
      (power_residue he (by decide) (by decide))
    have hq := (hS _).mpr ⟨hr,by decide,force_squareful hn hprod hr hd
      (by norm_num) h19 (by decide) h19e (by norm_num) h5e (by decide) (by decide) (by decide)⟩
    have hsub : ({3967,2689} : Finset ℕ) ⊆ S := by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hs hq
    have hm : 2 ≤ S.card := by simpa using Finset.card_le_card hsub
    have hb := two_weight_bound S hs hq (by decide) hm hsize hcap
    norm_num at hb
  · intro he
    have hs := (hS _).mpr ⟨hp,by decide,(hp.pow_dvd_iff_le_factorization hn).mpr (by omega)⟩
    have hr : Nat.Prime 13313 := by norm_num
    have hu : Nat.Prime 1372673 := by norm_num
    have hd := forced_factor hn hprod hp h3967 hr (by decide)
      (power_residue he (by decide) (by decide))
    have hd' := forced_factor hn hprod hp h3967 hu (by decide)
      (power_residue he (by decide) (by decide))
    have hq := sq hr (by decide) (by decide) hd (by decide)
    have hv := sq hu (by decide) (by decide) hd' (by decide)
    have hsub : ({3967,13313,1372673} : Finset ℕ) ⊆ S := by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hs (And.intro hq hv)
    have hm : 3 ≤ S.card := by simpa using Finset.card_le_card hsub
    have hb := two_weight_bound S hs hq (by decide) hm hsize hcap
    norm_num at hb


private theorem single31 {n : ℕ} (S : Finset ℕ)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (ha : ∀ p ∈ S, 128 ≤ p ∧ S.card + 3 ≤ p) : ¬ (31^2) ∣ 2*n := by
  intro hd
  have hsq := (by decide : Nat.Coprime (31^2) 2).dvd_of_dvd_mul_left hd
  have hmem := (hS 31).mpr ⟨by norm_num,by decide,hsq⟩
  have := (ha 31 hmem).1
  omega

set_option maxRecDepth 20000 in
private theorem odd_constraints {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hd : 3967 ∣ n) (hsq : ¬31^2 ∣ 2*n)
    (hsmall : ∀ q : ℕ, q.Prime → q ∣ n → q < 152 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (ho : Odd (n.factorization 3967)) :
    (¬31 ∣ n.factorization 3967) ∧
    (∀ d ∈ ({5,11,13,23,29,41,53} : Finset ℕ), ¬ d ∣ n.factorization 3967) ∧
    ∀ q ∈ n.primeFactors, q ≠ 3967 → ¬31 ∣ 1+q^n.factorization q := by
  have hp : Nat.Prime 3967 := by norm_num
  have hprod := OMA.R_Erdos1052_erdos_1052_R1.prod_eq_two_mul h
  have hmem := Nat.mem_primeFactors.mpr ⟨hp,hd,h.2.ne'⟩
  have ho' := Nat.odd_iff.mp ho
  have h31 : 31 ∣ 1+3967^n.factorization 3967 :=
    power_residue (k:=2) (r:=1) ho' (by decide) (by decide)
  refine ⟨?_,?_,?_⟩
  · intro h
    have hr : n.factorization 3967 % 62 = 31 := by omega
    have hsq' : 961 ∣ 1+3967^n.factorization 3967 :=
      power_residue hr (by decide) (by decide)
    have hb := Finset.dvd_prod_of_mem (fun z => 1+z^n.factorization z) hmem
    rw [hprod] at hb
    exact hsq (hsq'.trans hb)
  · intro d hD hdiv
    have forbid {d r : ℕ} [NeZero r] (hr : r.Prime) (hne : r ≠ 2) (hlt : r < 152)
        (hno : ¬ (r=2 ∨ r=3 ∨ r=5 ∨ r=7 ∨ r=19 ∨ r=31))
        (hrem : n.factorization 3967 % (2*d) = d)
        (hk : (3967:ZMod r)^(2*d)=1) (hx : 1+(3967:ZMod r)^d=0) : False := by
      exact hno (hsmall r hr (forced_factor h.2.ne' hprod hp hd hr hne
        (power_residue hrem hk hx)) hlt)
    simp only [Finset.mem_insert,Finset.mem_singleton] at hD
    rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact forbid (d:=5) (r:=11) (by norm_num) (by decide) (by decide) (by decide) (by omega) (by decide) (by decide)
    · exact forbid (d:=11) (r:=23) (by norm_num) (by decide) (by decide) (by decide) (by omega) (by decide) (by decide)
    · exact forbid (d:=13) (r:=79) (by norm_num) (by decide) (by decide) (by decide) (by omega) (by decide) (by decide)
    · exact forbid (d:=23) (r:=47) (by norm_num) (by decide) (by decide) (by decide) (by omega) (by decide) (by decide)
    · exact forbid (d:=29) (r:=59) (by norm_num) (by decide) (by decide) (by decide) (by omega) (by decide) (by decide)
    · exact forbid (d:=41) (r:=83) (by norm_num) (by decide) (by decide) (by decide) (by omega) (by decide) (by decide)
    · exact forbid (d:=53) (r:=107) (by norm_num) (by decide) (by decide) (by decide) (by omega) (by decide) (by decide)
  · intro q hq hne hqdiv
    have ss : ({q,3967}:Finset ℕ) ⊆ n.primeFactors := by
      simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro hq hmem
    have hb := Finset.prod_dvd_prod_of_subset _ _ (fun z => 1+z^n.factorization z) ss
    rw [hprod,Finset.prod_insert (by simpa using hne),Finset.prod_singleton] at hb
    exact hsq (by simpa [pow_two] using (Nat.mul_dvd_mul hqdiv h31).trans hb)

set_option maxRecDepth 20000 in
private theorem even_constraints {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (S : Finset ℕ)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (h31 : 31 ∣ n) (hd : 3967 ∣ n) (h991 : ¬991 ∣ n) (he : Even (n.factorization 3967)) :
    (∃ q ∈ n.primeFactors, q ≠ 3967 ∧ 31 ∣ 1+q^n.factorization q) ∧
    (n.factorization 3967 % 2048 = 1024 → 61441 ∈ S) := by
  have hprod := OMA.R_Erdos1052_erdos_1052_R1.prod_eq_two_mul h
  constructor
  · have hdiv : 31 ∣ ∏ z ∈ n.primeFactors, (1+z^n.factorization z) := by
      rw [hprod]
      exact dvd_mul_of_dvd_right h31 _
    obtain ⟨q,hq,hqd⟩ := ((by norm_num : Nat.Prime 31).prime.dvd_finsetProd_iff _).mp hdiv
    refine ⟨q,hq,?_,hqd⟩
    rintro rfl
    have hh := (ZMod.natCast_eq_zero_iff _ _).mpr hqd
    push_cast at hh
    obtain ⟨k,hk⟩ := he
    rw [hk,pow_add,←pow_two,←pow_mul, mul_comm] at hh
    rw [pow_mul, show (3967:ZMod 31)^2 = 1 by decide, one_pow] at hh
    exact (by decide : (1:ZMod 31)+1 ≠ 0) hh
  · intro hrem
    have hr : Nat.Prime 61441 := by norm_num
    have hrd := forced_factor h.2.ne' hprod (by norm_num : Nat.Prime 3967) hd hr (by decide)
      (power_residue hrem (by decide) (by decide))
    apply (hS _).mpr
    refine ⟨hr,by decide,(hr.pow_dvd_iff_le_factorization h.2.ne').mpr ?_⟩
    by_contra! hh
    have hpos := hr.factorization_pos_of_dvd h.2.ne' hrd
    have hone : n.factorization 61441 = 1 := by omega
    apply h991 (forced_factor h.2.ne' hprod hr hrd (by norm_num : Nat.Prime 991) (by decide) ?_)
    rw [hone,pow_one]
    decide

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H3_R1.H1 := by
  rintro ⟨A,hA⟩ ⟨B,hB⟩
  refine ⟨max A B,?_⟩
  intro n hn hns S hS hadm hcap h4 h3 h5 h7 h19 hN h16 h64 h31 hsmall h607 h223 h433 h991 h1213 h1783 h3967
  rcases Nat.even_or_odd (n.factorization 3967) with he | ho
  · obtain ⟨hc,hd⟩ := exponent_exclusions_of_product hn.2.ne'
      (OMA.R_Erdos1052_erdos_1052_R1.prod_eq_two_mul hn) S hS hadm hcap h3 h5 h19 h3967
    obtain ⟨hw,hf⟩ := even_constraints hn S hS h31 h3967 h991 he
    exact (hB n hn hns S hS hadm hcap h4 h3 h5 h7 h19 hN h16 h64 h31 hsmall
      h607 h223 h433 h991 h1213 h1783 h3967 he hc hd hw hf).trans (le_max_right _ _)
  · obtain ⟨hx,hy,hz⟩ := odd_constraints hn h3967 (single31 S hS hadm) hsmall ho
    exact (hA n hn hns S hS hadm hcap h4 h3 h5 h7 h19 hN h16 h64 h31 hsmall
      h607 h223 h433 h991 h1213 h1783 h3967 ho hx hy hz).trans (le_max_left _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H3_R1_H1_R2
