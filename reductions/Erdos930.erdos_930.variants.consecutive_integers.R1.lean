import FormalConjectures.ErdosProblems.«930»
import Mathlib

/-! Erdős–Selfridge (1975), Sections 1 and 2. Reduce large odd exponents to a
multiplicative Sidon bound on the power-free coefficients. The separation of
two scaled powers and the comparison modulo the left endpoint are proved below.
The two-term argument is adapted from @Halldon (#2301). -/

namespace OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1

open Finset Erdos930

-- Sylvester–Schur supplies a prime exceeding the interval length.
def H1 : Prop := ∀ n k : ℕ, 3 ≤ k → k < n →
  ∃ p, p.Prime ∧ k < p ∧ p ∣ ∏ i : Fin k, (n + 1 + (i : ℕ))

-- The square case and bounded lengths in the odd-prime case (Sections 2.2–3).
def H2 : Prop := ∀ n k l : ℕ, 3 ≤ k → k < n → l.Prime → l = 2 ∨ k < 30000 →
  ∀ z : ℕ, (∏ i : Fin k, (n + 1 + (i : ℕ))) ≠ z ^ l

-- Remove at most one position for each small prime (Erdős–Selfridge, Lemma 2).
def H3 : Prop := ∀ (n k : ℕ) (a : Fin k → ℕ), 0 < k →
  (∀ i, a i ∣ n + 1 + (i : ℕ)) → (∀ i p, p.Prime → p ∣ a i → p < k) →
  ∃ T : Finset (Fin k), k - (k.primesBelow.card) ≤ T.card ∧ (∏ i ∈ T, a i) ∣ (k-1).factorial

-- Erdős–Selfridge, Section 2.1. Multiplicative Sidon sets cannot have a
-- sufficiently large subcollection with product below the factorial bound.
def H4 : Prop := ∀ (k : ℕ) (a : Fin k → ℕ), 30000 ≤ k → (∀ i, 0 < a i) →
  (∀ i j u v, i ≤ j → u ≤ v → a i * a j = a u * a v → i = u ∧ j = v) →
  ∀ T : Finset (Fin k), k - k.primesBelow.card ≤ T.card → (k-1).factorial < ∏ i ∈ T, a i

lemma scaledPowers {n k A x y l : ℕ} (hk : 0 < k) (hn : k^3 < n) (hl : 3 ≤ l)
    (hx : n^2 ≤ A*x^l) (hy : A*y^l ≤ (n+k)^2) (hxy : x < y) : False := by
  have hn0 : 0 < n := by omega
  have hnk : k ≤ n := (Nat.le_self_pow (by decide : 3 ≠ 0) k).trans hn.le
  have hx0 : 0 < x := by
    by_contra! h
    simp [show x = 0 by omega, zero_pow (by omega : l ≠ 0)] at hx
    omega
  have ha : 0 < A := by by_contra! h; simp [show A=0 by omega] at hx; omega
  have heg : 2*l ≤ 3*(l-1) := by omega
  have hpow : (A*x^l)^2 ≤ (A*x^(l-1))^3 := by
    rw [mul_pow,mul_pow,← pow_mul,← pow_mul]
    exact Nat.mul_le_mul (Nat.pow_le_pow_right ha (by decide)) (Nat.pow_le_pow_right hx0 (by omega))
  have hkn : k*n < A*x^(l-1) := by
    apply (Nat.pow_lt_pow_iff_left (by decide : 3 ≠ 0)).mp
    calc (k*n)^3 = k^3 * n^3 := mul_pow .. 
      _ < n * n^3 := Nat.mul_lt_mul_of_pos_right hn (pow_pos hn0 _)
      _ = (n^2)^2 := by ring
      _ ≤ (A*x^l)^2 := Nat.pow_le_pow_left hx _
      _ ≤ _ := hpow
  have hgap : x^l + l*x^(l-1) ≤ y^l := by
    calc _ ≤ (x+1)^l := by simpa only [Nat.cast_id,mul_one] using
           (pow_add_mul_le_add_pow (b := (1 : ℕ)) (Nat.zero_le x) (Nat.zero_le _) l)
         _ ≤ _ := Nat.pow_le_pow_left hxy l
  have hgap' := Nat.mul_le_mul_left A hgap
  have hscale := Nat.mul_le_mul_right (A*x^(l-1)) hl
  nlinarith [Nat.mul_le_mul_right k hnk]

lemma sameProducts {n k a b c d : ℕ} (hn : k^3 < n) (ha : a ≤ b) (hb : b ≤ k)
    (hc : c ≤ d) (hd : d ≤ k) (he : (n+a)*(n+b)=(n+c)*(n+d)) : a = c ∧ b = d := by
  by_cases hk : k = 0
  · omega
  have hkk : k*k < n := by
    have := Nat.pow_le_pow_right (n := k) (by omega : 0 < k) (by decide : 2 ≤ 3)
    simpa [sq] using this.trans_lt hn
  have hab : a*b < n := (Nat.mul_le_mul (ha.trans hb) hb).trans_lt hkk
  have hcd : c*d < n := (Nat.mul_le_mul (hc.trans hd) hd).trans_lt hkk
  have eq : a*b + n*(n+a+b) = c*d + n*(n+c+d) := by nlinarith
  have prod := congrArg (· % n) eq
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hab, Nat.mod_eq_of_lt hcd] at prod
  have hsum : a+b = c+d := by
    have hcancel : n*(n+a+b) = n*(n+c+d) := by omega
    have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < n) hcancel
    omega
  zify at ha hb hc hd hsum prod ⊢
  have hz : ((a:ℤ)-c)*((a:ℤ)-d)=0 := by linear_combination (a:ℤ)*hsum - prod
  rcases mul_eq_zero.mp hz with heq|heq <;> omega

lemma sidon {n k l : ℕ} (hk : 0 < k) (hn : k^3 < n) (hl : 3 ≤ l)
    (a x : Fin k → ℕ) (h : ∀ i : Fin k, n+1+(i:ℕ) = a i * x i ^ l) :
    ∀ i j u v, i ≤ j → u ≤ v → a i * a j = a u * a v → i = u ∧ j = v := by
  intro i j u v hij huv he
  let m (i : Fin k) := n + 1 + (i : ℕ)
  have eq (s t : Fin k) : m s * m t = (a s*a t)*(x s*x t)^l := by
    dsimp [m]; rw [h s,h t,mul_pow]; ring
  have bounds (s t : Fin k) : n^2 ≤ m s*m t ∧ m s*m t ≤ (n+k)^2 := by
    dsimp [m]; rw [sq,sq]
    exact ⟨Nat.mul_le_mul (by omega) (by omega),
      Nat.mul_le_mul (by have := s.isLt; omega) (by have := t.isLt; omega)⟩
  have hprod : m i*m j = m u*m v := by
    have h₁ := bounds i j
    have h₂ := bounds u v
    rw [eq i j,he] at h₁ ⊢
    rw [eq u v] at h₂ ⊢
    rcases lt_trichotomy (x i*x j) (x u*x v) with hlt|heq|hgt
    · exact (scaledPowers hk hn hl h₁.1 h₂.2 hlt).elim
    · rw [heq]
    · exact (scaledPowers hk hn hl h₂.1 h₁.2 hgt).elim
  have ids := sameProducts (a := 1+i.val) (b := 1+j.val) (c := 1+u.val) (d := 1+v.val)
    hn (by omega) (by have := j.isLt; omega) (by omega) (by have := v.isLt; omega)
    (by simpa [m,Nat.add_assoc] using hprod)
  exact ⟨Fin.ext (by omega),Fin.ext (by omega)⟩

private lemma pairCase (n z l : ℕ) (hl : 2 ≤ l)
    (hp : (n+1)*(n+2) = z^l) : False := by
  have hc : Nat.Coprime (n+1) (n+2) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  have unit {a b : ℕ} (hab : a.Coprime b) : IsUnit (gcd a b) := by
    rw [gcd_eq_nat_gcd,hab.gcd_eq_one]; exact isUnit_one
  obtain ⟨a,ha⟩ := exists_eq_pow_of_mul_eq_pow (unit hc) hp
  obtain ⟨b,hb⟩ := exists_eq_pow_of_mul_eq_pow (unit hc.symm) ((mul_comm _ _).trans hp)
  have ha0 : 0 < a := by
    by_contra! h
    rw [show a = 0 by omega,zero_pow (by omega : l ≠ 0)] at ha
    omega
  have hab : a < b := by by_contra! h; have := Nat.pow_le_pow_left h l; omega
  have hg := pow_add_mul_le_add_pow (b := (1 : ℕ)) (Nat.zero_le a) (Nat.zero_le _) l
  simp only [Nat.cast_id,mul_one] at hg
  have hle : (a+1)^l ≤ b^l := Nat.pow_le_pow_left (show a+1 ≤ b by omega) l
  have := Nat.mul_le_mul_left l (Nat.one_le_pow (l-1) a ha0)
  omega

private lemma toFinProduct (n k : ℕ) :
    (∏ m ∈ Icc (n+1) (n+k), m) = ∏ i : Fin k, (n+1+(i:ℕ)) := by
  rw [← Ico_add_one_right_eq_Icc,prod_Ico_eq_prod_range,Fin.prod_univ_eq_prod_range]
  simp

private lemma smallStart {n k z l : ℕ} (hk : 2 ≤ k) (hn : n ≤ k) (hl : 2 ≤ l)
    (h : (∏ m ∈ Icc (n+1) (n+k), m) = z^l) : False := by
  obtain ⟨p,hp,hlo,hhi⟩ := Nat.bertrand ((n+k)/2) (by omega)
  have him : p ∈ Icc (n+1) (n+k) := mem_Icc.mpr ⟨by omega,by omega⟩
  have hf : (∏ m ∈ Icc (n+1) (n+k), m).factorization p = 1 := by
    rw [Nat.factorization_prod_apply (fun m hm => by have := (mem_Icc.mp hm).1; omega)]
    rw [Finset.sum_eq_single_of_mem p him, hp.factorization_self]
    intro m hm hne
    apply Nat.factorization_eq_zero_of_not_dvd
    rintro ⟨t,ht⟩
    have hbounds := mem_Icc.mp hm
    have ht2 : 2 ≤ t := by
      by_contra! hsmall
      interval_cases t <;> simp_all
    have := Nat.mul_le_mul_left p ht2
    omega
  rw [h,Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul] at hf
  have : l ∣ 1 := ⟨_,hf.symm⟩
  have := Nat.le_of_dvd (by decide : 0 < 1) this
  omega

private lemma uniqueVal {n k l z p : ℕ} {i : Fin k} (hk : k ≤ p)
    (hpi : p ∣ n+1+i.val) (hpow : (∏ j : Fin k, (n+1+j.val)) = z^l) :
    l ∣ (n+1+i.val).factorization p := by
  have eq : (∏ j : Fin k, (n+1+j.val)).factorization p = (n+1+i.val).factorization p := by
    rw [Nat.factorization_prod_apply (fun j _ => by omega)]
    apply sum_eq_single_of_mem i (mem_univ _)
    intro j _ hne
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hpj
    have hne' : j.val ≠ i.val := fun H => hne (Fin.ext H)
    rcases lt_or_gt_of_ne hne' with h|h
    · have := Nat.le_of_dvd (show 0 < (n+1+i.val)-(n+1+j.val) by omega) (Nat.dvd_sub hpi hpj)
      have := i.isLt; omega
    · have := Nat.le_of_dvd (show 0 < (n+1+j.val)-(n+1+i.val) by omega) (Nat.dvd_sub hpj hpi)
      have := j.isLt; omega
  rw [← eq,hpow,Nat.factorization_pow]
  exact ⟨z.factorization p,rfl⟩

theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos930.erdos_930.variants.consecutive_integers := by
  classical
  rintro sylvester cases trim sparse n k _ hk ⟨z₀,l₀,hl₀,h₀⟩
  obtain ⟨l,hl,t,ht⟩ := Nat.exists_prime_and_dvd (n := l₀) (by omega)
  let z := z₀ ^ t
  have hpow : (∏ m ∈ Icc (n+1) (n+k), m) = z^l := by
    rw [← h₀,ht]; dsimp [z]; rw [← pow_mul,Nat.mul_comm t l]
  by_cases hnk : n ≤ k
  · exact smallStart hk hnk hl.two_le hpow
  rw [toFinProduct] at hpow
  by_cases hk2 : k = 2
  · subst k
    apply pairCase n z l hl.two_le
    simpa [Fin.prod_univ_two] using hpow
  have hk3 : 3 ≤ k := by omega
  by_cases hcase : l = 2 ∨ k < 30000
  · exact cases n k l hk3 (by omega) hl hcase z hpow
  obtain ⟨p,hp,hpk,hdiv⟩ := sylvester n k hk3 (by omega)
  obtain ⟨i,_,hi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hdiv
  have hemi := uniqueVal hpk.le hi hpow
  have hval : 0 < (n+1+i.val).factorization p := by
    exact hp.factorization_pos_of_dvd (by omega) hi
  have hlarge := Nat.le_of_dvd (show 0 < n+1+i.val by omega)
    ((hp.pow_dvd_iff_le_factorization (show n+1+i.val ≠ 0 by omega)).2 (Nat.le_of_dvd hval hemi))
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  have hnk3 : k^3 < n := by
    have h₁ := Nat.pow_le_pow_left (show k+1 ≤ p by omega) 3
    have h₂ := Nat.pow_le_pow_right hp.pos hl3
    have := i.isLt
    nlinarith
  let m (j : Fin k) := n + 1 + j.val
  let a (j : Fin k) := ∏ q ∈ (m j).primeFactors, q^((m j).factorization q % l)
  let x (j : Fin k) := ∏ q ∈ (m j).primeFactors, q^((m j).factorization q / l)
  have repr (j : Fin k) : n+1+j.val = a j * x j ^ l := by
    change m j = _
    have hne : m j ≠ 0 := by dsimp [m]; omega
    calc m j = ∏ q ∈ (m j).primeFactors, q^((m j).factorization q) :=
          (Nat.prod_factorization_pow_eq_self hne).symm
      _ = _ := by
        dsimp only [a,x]; rw [← Finset.prod_pow,← prod_mul_distrib]
        apply prod_congr rfl
        intro q _
        rw [← pow_mul,← pow_add]
        congr 1
        exact (Nat.mod_add_div' _ _).symm
  have smooth (j : Fin k) (q : ℕ) (hq : q.Prime) (hqj : q ∣ a j) : q < k := by
    by_contra! hqk
    obtain ⟨r,hr,hd⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp hqj
    have hrq := (Nat.prime_dvd_prime_iff_eq hq (Nat.prime_of_mem_primeFactors hr)).mp
      (hq.dvd_of_dvd_pow hd)
    subst r
    have hfull := uniqueVal hqk (Nat.dvd_of_mem_primeFactors hr) hpow
    change l ∣ (m j).factorization q at hfull
    rw [Nat.mod_eq_zero_of_dvd hfull,pow_zero,Nat.dvd_one] at hd
    exact hq.ne_one hd
  obtain ⟨T,hT,hdvd⟩ := trim n k a (by omega) (fun j => ⟨_,repr j⟩) smooth
  have apos (j : Fin k) : 0 < a j := by
    by_contra! h
    have hh := repr j
    rw [show a j = 0 by omega,zero_mul] at hh
    omega
  have hbad := sparse k a (by omega) apos (sidon (by omega) hnk3 hl3 a x repr) T hT
  exact hbad.not_ge (Nat.le_of_dvd (Nat.factorial_pos _) hdvd)

end OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1
