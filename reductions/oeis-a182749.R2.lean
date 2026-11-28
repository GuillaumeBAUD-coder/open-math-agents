import OMAStatements.S_oeis_a182749
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

-- Credit: @FransDevelopment
namespace OMA.R_oeis_a182749_R2
open OMA.S_oeis_a182749
noncomputable section

/-- Lower Chebyshev estimate, only on the explicit tail used here. -/
def H1 : Prop := ∀ x : ℝ, 100000000 < x → x - x/(2*Real.log x) ≤ Chebyshev.theta x

/-- Upper Chebyshev estimate on the same tail. -/
def H2 : Prop := ∀ x : ℝ, 100000000 < x → Chebyshev.theta x ≤ x + x/(2*Real.log x)

/- The arithmetic allocation lemmas below reuse the independently checked R1 construction;
the project requires root reductions to import only their statement and Mathlib. -/

theorem scaled (k t c s : ℕ) (ht : 2 ≤ t) (hc : 0 < c) (hs : s ≤ c) :
    k+s ≤ c*t^k := by
  induction k with
  | zero => simpa using hs
  | succ k ih =>
    rw [pow_succ, ← Nat.mul_assoc]
    have hp : 0 < c*t^k := Nat.mul_pos hc (pow_pos (by omega) _)
    have hh := Nat.mul_le_mul_left (c*t^k) ht
    omega

theorem unchanged (t e : ℕ) (ht : 2 ≤ t) : e+1 ≤ t^e := by
  simpa using scaled e t 1 1 ht (by decide) (by decide)

theorem single_odd (p a : ℕ) (hp : 3 ≤ p) :
    a+3 ≤ p^(a+1) ∧ p*p^(a+1) = p^(a+2) := by
  constructor
  · simpa [pow_succ, Nat.mul_comm] using scaled a p p 3 (by omega) (by omega) hp
  · ring

theorem single_binary (a : ℕ) :
    a+4 ≤ 2^(a+2) ∧ 2*2^(a+2) = (2:ℕ)^(a+3) := by
  constructor
  · simpa [pow_add, Nat.mul_comm] using scaled a 2 4 4 (by decide) (by decide) (by decide)
  · ring

/-- A repeated smallest base p: n contains p^(a+2), P^(c+1). -/
theorem repeated_min (p P a c : ℕ) (hp : 2 ≤ p) (hP : 3 ≤ P) :
    let dp := P*p^a
    let dP := p*P^c
    a+3 ≤ dp ∧ c+2 ≤ dP ∧ P ∣ dp ∧ p*dp*dP = p^(a+2)*P^(c+1) := by
  dsimp only
  refine ⟨scaled a p P 3 hp (by omega) hP, scaled c P p 2 (by omega) (by omega) hp, ?_, ?_⟩
  · exact dvd_mul_right P _
  · ring

/-- A repeated largest base P: n contains p^(a+1), P^(c+2). -/
theorem repeated_max (p P a c : ℕ) (hp : 2 ≤ p) (hP : 3 ≤ P) :
    let dp := P*p^a
    let dP := P^(c+1)
    a+2 ≤ dp ∧ c+3 ≤ dP ∧ P ∣ dp ∧ p*dp*dP = p^(a+1)*P^(c+2) := by
  dsimp only
  refine ⟨scaled a p P 2 hp (by omega) (by omega), (single_odd P c hP).1, ?_, ?_⟩
  · exact dvd_mul_right P _
  · ring

/-- An interior repeated base r: n contains p^(a+1), r^(b+2), P^(c+1). -/
theorem repeated_interior (p r P a b c : ℕ) (hp : 2 ≤ p) (hr : 3 ≤ r) (hP : 3 ≤ P) :
    let dp := P*p^a
    let dr := r^(b+1)
    let dP := r*P^c
    a+2 ≤ dp ∧ b+3 ≤ dr ∧ c+2 ≤ dP ∧ P ∣ dp ∧
      p*dp*dr*dP = p^(a+1)*r^(b+2)*P^(c+1) := by
  dsimp only
  refine ⟨scaled a p P 2 hp (by omega) (by omega), (single_odd r b hr).1,
    scaled c P r 2 (by omega) (by omega) (by omega), ?_, ?_⟩
  · exact dvd_mul_right P _
  · ring

theorem fresh_coprime (n q : ℕ) (d : ℕ → ℕ) (hq : q.Prime)
    (hbig : ∀ t ∈ n.primeFactors, t < q) : (∏ t ∈ n.primeFactors, t^(d t-1)).Coprime q := by
  apply Nat.Coprime.prod_left
  intro t ht
  exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors ht) hq).2 (hbig t ht).ne).pow_left _

private theorem extend_budgets (s k : Finset ℕ) (e f : ℕ → ℕ) (p P : ℕ)
    (hk : k ⊆ s) (hp : p ∈ k) (ht : ∀ t ∈ s, 2 ≤ t)
    (hl : ∀ t ∈ k, e t + 1 ≤ f t) (ha : P ∣ f p)
    (hm : p * (∏ t ∈ k, f t) = ∏ t ∈ k, t ^ e t) :
    ∃ d : ℕ → ℕ, P ∣ d p ∧ (∀ t ∈ s, e t + 1 ≤ d t) ∧
      p * (∏ t ∈ s, d t) = ∏ t ∈ s, t ^ e t := by
  classical
  let d (t : ℕ) := if t ∈ k then f t else t ^ e t
  refine ⟨d, by simpa [d, hp] using ha, ?_, ?_⟩
  · intro t h
    by_cases hh : t ∈ k
    · simpa [d, hh] using hl t hh
    · simpa [d, hh] using unchanged t (e t) (ht t h)
  · have htail : (∏ t ∈ s \ k, d t) = ∏ t ∈ s \ k, t ^ e t :=
      Finset.prod_congr rfl fun t h => by simp [d, (Finset.mem_sdiff.mp h).2]
    have hhead : (∏ t ∈ k, d t) = ∏ t ∈ k, f t :=
      Finset.prod_congr rfl fun t h => by simp [d, h]
    rw [← Finset.prod_sdiff (f := d) hk, ← Finset.prod_sdiff (f := fun t => t ^ e t) hk,
      htail, hhead, mul_left_comm, hm]

/-- An explicit allocation for every positive nonsquarefree index other than four. -/
theorem factorization_allocation (n : ℕ) (hn : n ≠ 0) (hs : ¬ Squarefree n) (h4 : n ≠ 4) :
    ∃ (p P : ℕ) (d : ℕ → ℕ), p ∈ n.primeFactors ∧ P ∈ n.primeFactors ∧
      (∀ t ∈ n.primeFactors, p ≤ t ∧ t ≤ P) ∧ P ∣ d p ∧
      (∀ t ∈ n.primeFactors, n.factorization t + 1 ≤ d t) ∧
      p * (∏ t ∈ n.primeFactors, d t) = n := by
  classical
  rw [Nat.squarefree_iff_factorization_le_one hn] at hs
  push Not at hs
  obtain ⟨r, hr⟩ := hs
  have hrmem : r ∈ n.primeFactors := by
    change r ∈ n.factorization.support
    exact Finsupp.mem_support_iff.mpr (by omega)
  let s := n.primeFactors
  have hne : s.Nonempty := ⟨r, hrmem⟩
  let p := s.min' hne
  let P := s.max' hne
  have hp : p ∈ s := Finset.min'_mem _ _
  have hP : P ∈ s := Finset.max'_mem _ _
  have hb (t : ℕ) (h : t ∈ s) : p ≤ t ∧ t ≤ P :=
    ⟨Finset.min'_le _ _ h, Finset.le_max' _ _ h⟩
  have ht (t : ℕ) (h : t ∈ s) : 2 ≤ t := (Nat.prime_of_mem_primeFactors h).two_le
  have he (t : ℕ) (h : t ∈ s) : 0 < n.factorization t := by
    change t ∈ n.factorization.support at h
    exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp h)
  have hnprod := Nat.prod_primeFactors_pow_factorization hn
  suffices hall : ∃ d : ℕ → ℕ, P ∣ d p ∧ (∀ t ∈ s, n.factorization t + 1 ≤ d t) ∧
      p * (∏ t ∈ s, d t) = ∏ t ∈ s, t ^ n.factorization t by
    obtain ⟨d, h1, h2, h3⟩ := hall
    exact ⟨p, P, d, hp, hP, hb, h1, h2, h3.trans hnprod.symm⟩
  have hp2 := ht p hp
  have hmin := hb r hrmem
  have heP := he P hP
  have hep := he p hp
  by_cases hsing : p = P
  · have hpr : r = p := by omega
    have hset : s = {p} := by
      ext t
      simp only [Finset.mem_singleton]
      exact ⟨fun h => by have := hb t h; omega, fun h => by simpa [h] using hp⟩
    have hn_eq : n = p ^ n.factorization p := by
      change n = ∏ t ∈ s, t ^ n.factorization t at hnprod
      simpa [hset] using hnprod
    have hrep : 2 ≤ n.factorization p := by rw [hpr] at hr; omega
    obtain ⟨a, ha⟩ : ∃ a, n.factorization p = a+2 := ⟨n.factorization p - 2, by omega⟩
    have hlow : a+3 ≤ p^(a+1) := by
      by_cases hpbin : p = 2
      · have hpos : a ≠ 0 := by
          intro h
          rw [ha, h, hpbin] at hn_eq
          norm_num at hn_eq
          omega
        obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos
        simpa [hpbin, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (single_binary b).1
      · exact (single_odd p a (by omega)).1
    refine ⟨fun _ => p^(a+1), ?_, ?_, ?_⟩
    · rw [← hsing, pow_succ]
      exact dvd_mul_left _ _
    · intro t h
      have hv : t = p := by simpa [hset] using h
      simpa [hv, ha, Nat.add_assoc] using hlow
    · simp [hset, ha, pow_succ, Nat.mul_comm]
  · have hpP : p ≠ P := hsing
    have hPp : P ≠ p := Ne.symm hpP
    have h3P : 3 ≤ P := by have := hb P hP; omega
    have hp_cases (f : ℕ → ℕ)
        (hlp : n.factorization p + 1 ≤ f p)
        (hlP : n.factorization P + 1 ≤ f P) (hanchor : P ∣ f p)
        (hm : p * f p * f P = p^(n.factorization p)*P^(n.factorization P)) :
        ∃ d : ℕ → ℕ, P ∣ d p ∧ (∀ t ∈ s, n.factorization t + 1 ≤ d t) ∧
          p * (∏ t ∈ s, d t) = ∏ t ∈ s, t ^ n.factorization t := by
      apply extend_budgets s {p,P} _ f _ _ (by
        intro t h
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl
        · exact hp
        · exact hP) (by simp) ht
      · intro t h
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl
        · exact hlp
        · exact hlP
      · exact hanchor
      · simpa [hpP, Nat.mul_assoc] using hm
    by_cases hrp : r = p
    · obtain ⟨a, ha⟩ : ∃ a, n.factorization p = a+2 :=
        ⟨n.factorization p - 2, by simpa [hrp] using (show n.factorization r = n.factorization r - 2 + 2 by omega)⟩
      obtain ⟨c, hc⟩ : ∃ c, n.factorization P = c+1 := ⟨n.factorization P-1, by omega⟩
      obtain ⟨h1,h2,h3,h4'⟩ := repeated_min p P a c hp2 h3P
      apply hp_cases (fun t => if t=p then P*p^a else p*P^c)
      · simpa [ha, hc, hPp, Nat.add_assoc] using h1
      · simpa [ha, hc, hPp, Nat.add_assoc] using h2
      · simp
      · simpa [ha, hc, hPp, Nat.add_assoc] using h4'
    · by_cases hrP : r = P
      · obtain ⟨a, ha⟩ : ∃ a, n.factorization p = a+1 := ⟨n.factorization p-1, by omega⟩
        obtain ⟨c, hc⟩ : ∃ c, n.factorization P = c+2 :=
          ⟨n.factorization P-2, by simpa [hrP] using (show n.factorization r = n.factorization r - 2 + 2 by omega)⟩
        obtain ⟨h1,h2,h3,h4'⟩ := repeated_max p P a c hp2 h3P
        apply hp_cases (fun t => if t=p then P*p^a else P^(c+1))
        · simpa [ha, hc, hPp, Nat.add_assoc] using h1
        · simpa [ha, hc, hPp, Nat.add_assoc] using h2
        · simp
        · simpa [ha, hc, hPp, Nat.add_assoc] using h4'
      · have h3r : 3 ≤ r := by omega
        obtain ⟨a, ha⟩ : ∃ a, n.factorization p = a+1 := ⟨n.factorization p-1, by omega⟩
        obtain ⟨b, hb'⟩ : ∃ b, n.factorization r = b+2 := ⟨n.factorization r-2, by omega⟩
        obtain ⟨c, hc⟩ : ∃ c, n.factorization P = c+1 := ⟨n.factorization P-1, by omega⟩
        obtain ⟨h1,h2,h3,h4',h5⟩ := repeated_interior p r P a b c hp2 h3r h3P
        let f (t : ℕ) := if t=p then P*p^a else if t=r then r^(b+1) else r*P^c
        apply extend_budgets s {p,r,P} _ f _ _
          (by
            intro t h
            simp only [Finset.mem_insert, Finset.mem_singleton] at h
            rcases h with rfl | rfl | rfl
            · exact hp
            · exact hrmem
            · exact hP) (by simp) ht
        · intro t h
          simp only [Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with rfl | rfl | rfl
          · simpa [f, ha, Nat.add_assoc] using h1
          · simpa [f, hrp, hb', Nat.add_assoc] using h2
          · simpa [f, hPp, Ne.symm hrP, hc, Nat.add_assoc] using h3
        · simp [f]
        · simpa [f, hpP, Ne.symm hrp, hrp, hrP, hPp, Ne.symm hrP, ha, hb', hc, Nat.mul_assoc] using h5


/-- Exact denominator and divisor count of the base constructed on the
prime support of n. Each d(r) is the divisor factor assigned to prime r. -/
theorem assigned_base_specs (n : ℕ) (hn : n ≠ 0) (d : ℕ → ℕ)
    (hd : ∀ r ∈ n.primeFactors, n.factorization r+1 ≤ d r) :
    n ∣ (∏ r ∈ n.primeFactors, r^(d r-1)) ∧
      (∏ r ∈ n.primeFactors, r^(d r-1)).divisors.card = ∏ r ∈ n.primeFactors, d r := by
  constructor
  · calc
      n = ∏ r ∈ n.primeFactors, r^n.factorization r := Nat.prod_primeFactors_pow_factorization hn
      _ ∣ _ := by
        apply Finset.prod_dvd_prod_of_dvd
        intro r hr
        have := hd r hr
        exact pow_dvd_pow r (by omega)
  · rw [← ArithmeticFunction.sigma_zero_apply]
    calc
      _ = ∏ r ∈ n.primeFactors, ArithmeticFunction.sigma 0 (r^(d r-1)) := by
        apply ArithmeticFunction.IsMultiplicative.map_prod _ ArithmeticFunction.isMultiplicative_sigma
        intro x hx y hy hxy
        exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors hx)
          (Nat.prime_of_mem_primeFactors hy) hxy
      _ = _ := by
        apply Finset.prod_congr rfl
        intro r hr
        rw [ArithmeticFunction.sigma_zero_apply_prime_pow (Nat.prime_of_mem_primeFactors hr)]
        have := hd r hr
        omega


/-- A uniform bound for the cost of increasing the least prime factor. -/
theorem sixteen_mul_pow_three_le (p : ℕ) (hp : 2 ≤ p) :
    16 * p * 3 ^ (p - 1) ≤ 10 ^ p := by
  have aux (k : ℕ) : 16 * (k + 2) * 3 ^ (k + 1) ≤ 10 ^ (k + 2) := by
    induction k with
    | zero => decide
    | succ k ih =>
      calc
        16 * (k + 1 + 2) * 3 ^ (k + 1 + 1)
            = (16 * (k + 1 + 2) * 3) * 3 ^ (k + 1) := by rw [pow_succ 3 (k+1)]; ring
        _ ≤ (10 * (16 * (k + 2))) * 3 ^ (k + 1) := Nat.mul_le_mul_right _ (by omega)
        _ = 10 * (16 * (k + 2) * 3 ^ (k + 1)) := by ring
        _ ≤ 10 * 10 ^ (k + 2) := Nat.mul_le_mul_left _ ih
        _ = 10 ^ (k + 1 + 2) := by rw [show k+1+2 = (k+2)+1 by omega, pow_succ 10 (k+2)]; ring
  simpa only [show p-2+2 = p by omega, show p-2+1 = p-1 by omega] using aux (p-2)

/-- If the initial multiple is small enough, the lower decimal threshold
allows a fresh prime of size larger than three to the m-th power. -/
theorem decimal_budget (p m B : ℕ) (hp : 2 ≤ p) (hm : 3 ≤ m) (hB : B ≤ (4*p)^m) :
    B * 3 ^ ((p-1)*m) < 10 ^ (p*m-1) := by
  have hscaled : 4^m * (B * 3^((p-1)*m)) ≤ 10^(p*m) := calc
    4^m * (B * 3^((p-1)*m)) ≤ 4^m * ((4*p)^m * (3^(p-1))^m) := by rw [pow_mul]; gcongr
    _ = (16*p*3^(p-1))^m := by
      simp only [show 16*p*3^(p-1) = 4*((4*p)*3^(p-1)) by ring, mul_pow]
    _ ≤ (10^p)^m := Nat.pow_le_pow_left (sixteen_mul_pow_three_le p hp) _
    _ = 10^(p*m) := (pow_mul _ _ _).symm
  have h4 : 10 < 4^m := lt_of_lt_of_le (by decide : 10 < 4^3)
    (Nat.pow_le_pow_right (by decide) hm)
  have hpm : 0 < p*m := Nat.mul_pos (by omega) (by omega)
  have hten : 10^(p*m) = 10 * 10^(p*m-1) := by
    conv_lhs => rw [show p*m = (p*m-1)+1 by omega, pow_succ]
    exact Nat.mul_comm _ _
  by_contra! h
  have hle := Nat.mul_le_mul_left (4^m) h
  have hlt := Nat.mul_lt_mul_of_pos_right h4 (show 0 < 10^(p*m-1) by positivity)
  omega


/-- The linear terms and constant term of a product fit inside the product. -/
theorem one_add_sum_le_product (w : List ℕ) :
    1 + w.sum ≤ (w.map (fun a => a+1)).prod := by
  induction w with
  | nil => decide
  | cons a t ih =>
    simp only [List.sum_cons, List.map_cons, List.prod_cons]
    calc
      1 + (a + t.sum) ≤ (a+1) * (1+t.sum) := by nlinarith [Nat.zero_le (a*t.sum)]
      _ ≤ _ := Nat.mul_le_mul_left _ ih

/-- A tail entry (r,e) represents r^e in B and contributes e+1 to the
divisor count. The anchor's assigned factor bounds every tail base. -/
theorem tail_powers_le (a : ℕ) (t : List (ℕ × ℕ)) (hb : ∀ z ∈ t, z.1 ≤ a) :
    (t.map (fun z => z.1^z.2)).prod ≤ 2^(a*(t.map Prod.snd).sum) := by
  induction t with
  | nil => simp
  | cons z t ih =>
    have hz : z.1 ≤ 2^a := (hb z (by simp)).trans (Nat.lt_two_pow_self (n := a)).le
    have ht := ih (fun w hw => hb w (List.mem_cons_of_mem _ hw))
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    calc
      z.1^z.2 * (t.map (fun w => w.1^w.2)).prod
          ≤ (2^a)^z.2 * 2^(a*(t.map Prod.snd).sum) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hz _) ht
      _ = 2^(a*(z.2+(t.map Prod.snd).sum)) := by
        rw [← pow_mul, ← pow_add, Nat.mul_add]

/-- With the largest prime assigned to the anchor, every tail base is at
most a. For m = a times the product of the remaining divisor-count factors,
this bounds the whole base by (2p)^m. -/
theorem assigned_base_bound (p a : ℕ) (t : List (ℕ × ℕ)) (hp : 0 < p)
    (hb : ∀ z ∈ t, z.1 ≤ a) :
    p^(a-1) * (t.map (fun z => z.1^z.2)).prod ≤
      (2*p)^(a*(t.map (fun z => z.2+1)).prod) := by
  let T := (t.map (fun z => z.2+1)).prod
  let S := (t.map Prod.snd).sum
  have hs : 1 + S ≤ T := by
    simpa only [S,T,List.map_map,Function.comp_def] using one_add_sum_le_product (t.map Prod.snd)
  have hstem : a ≤ a*T := calc
    a = a*1 := by simp
    _ ≤ a*T := Nat.mul_le_mul_left a (by omega)
  change p^(a-1) * _ ≤ (2*p)^(a*T)
  calc
    _ ≤ p^(a*T) * 2^(a*S) :=
      Nat.mul_le_mul (Nat.pow_le_pow_right hp (by omega)) (tail_powers_le a t hb)
    _ ≤ p^(a*T) * 2^(a*T) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_left a (by omega)))
    _ = _ := by rw [mul_pow]; exact Nat.mul_comm _ _


/-- Finite-prime-support version of the base bound. This consumes exactly
the assigned divisor factors d(r) on the support of n. -/
theorem assigned_base_bound_finset (s : Finset ℕ) (p : ℕ) (d : ℕ → ℕ)
    (hp0 : 0 < p) (hp : p ∈ s) (hd : ∀ r ∈ s, 0 < d r) (hr : ∀ r ∈ s, r ≤ d p) :
    (∏ r ∈ s, r^(d r-1)) ≤ (2*p)^(∏ r ∈ s, d r) := by
  let t := (s.erase p).toList.map (fun r => (r,d r-1))
  have ht : ∀ z ∈ t, z.1 ≤ d p := by
    intro z hz
    obtain ⟨r, hmem, rfl⟩ := List.mem_map.mp hz
    exact hr r (Finset.mem_of_mem_erase (Finset.mem_toList.mp hmem))
  have hb := assigned_base_bound p (d p) t hp0 ht
  simp only [t, List.map_map, Function.comp_def, Finset.prod_map_toList] at hb
  have he : (∏ r ∈ s.erase p, (d r-1+1)) = ∏ r ∈ s.erase p, d r := by
    apply Finset.prod_congr rfl
    intro r h
    have := hd r (Finset.mem_of_mem_erase h)
    omega
  rw [he] at hb
  simpa only [Finset.mul_prod_erase s (fun r => r^(d r-1)) hp, Finset.mul_prod_erase s d hp] using hb


/-- Multiplying a baseline by one new prime power multiplies its divisor count
by the chosen factor and preserves divisibility by the index. -/
theorem candidate_of_prime_power_window {n b p m q : ℕ} (hp : 0 < p)
    (hn : n = p * m) (hd : n ∣ b) (hc : b.divisors.card = m)
    (hq : q.Prime) (hcop : Nat.Coprime b q)
    (hl : 10 ^ (n - 1) ≤ b * q ^ (p - 1)) (hu : b * q ^ (p - 1) < 10 ^ n) :
    Candidate n (b * q ^ (p - 1)) := by
  refine ⟨dvd_mul_of_dvd_left hd _, hl, hu, ?_⟩
  have hmul : Nat.Coprime b (q ^ (p - 1)) := hcop.pow_right _
  rw [hmul.card_divisors_mul, hc, ← ArithmeticFunction.sigma_zero_apply,
    ArithmeticFunction.sigma_zero_apply_prime_pow hq, hn]
  rw [show p - 1 + 1 = p by omega, Nat.mul_comm]


theorem log_large_of_three_power (m p : ℕ) (x : ℝ) (hp : p ≤ m) (hm : 0 < m)
    (hx : (3:ℝ)^m < x) : (p:ℝ) < Real.log x := by
  have h3 : (1:ℝ) < Real.log 3 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
  have hl := Real.log_lt_log (by positivity : 0 < (3:ℝ)^m) hx
  rw [Real.log_pow] at hl
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hp' : (p:ℝ) ≤ m := by exact_mod_cast hp
  nlinarith [mul_pos hm' (sub_pos.mpr h3)]


theorem no_candidate_four : ¬ ∃ m : ℕ, Candidate 4 m := by
  rintro ⟨m, hdiv, hlo, _, hcard⟩
  rcases hdiv with ⟨k, rfl⟩
  norm_num at hlo
  have hk : 250 ≤ k := by omega
  let s : Finset ℕ := {1, 2, 4, 2*k, 4*k}
  have hsub : s ⊆ (4*k).divisors := by
    intro d hd
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hd
    apply Nat.mem_divisors.mpr
    refine ⟨?_, by omega⟩
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact one_dvd _
    · exact ⟨2*k, by omega⟩
    · exact ⟨k, rfl⟩
    · exact ⟨2, by omega⟩
    · exact dvd_refl _
  have hsize : s.card = 5 := by
    simp [s, Finset.card_insert_of_notMem, show 1 ≠ 2*k by omega,
      show 1 ≠ 4*k by omega, show 2 ≠ 2*k by omega, show 2 ≠ 4*k by omega,
      show 4 ≠ 2*k by omega, show 4 ≠ 4*k by omega, show 2*k ≠ 4*k by omega]
  have hle := Finset.card_le_card hsub
  omega


private theorem baseline_checked : ∀ n : ℕ, 0 < n → ¬ Squarefree n → n ≠ 4 →
  ∃ p m B : ℕ, p.Prime ∧ n=p*m ∧ 3 ≤ m ∧ p ≤ m ∧ 0 < B ∧
    n ∣ B ∧ B.divisors.card=m ∧ B≤(2*p)^m ∧ (∀ t ∈ n.primeFactors, p ≤ t) ∧
    ∀ q : ℕ, q.Prime → m < q → B.Coprime q := by
  intro n hn hs h4
  obtain ⟨p,P,d,hp,hP,hext,hanchor,hd,hprod⟩ :=
    factorization_allocation n hn.ne' hs h4
  let m := ∏ t ∈ n.primeFactors, d t
  let B := ∏ t ∈ n.primeFactors, t^(d t-1)
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hp2 := hprime.two_le
  have hdpos (t : ℕ) (ht : t ∈ n.primeFactors) : 0 < d t := by have := hd t ht; omega
  have hPdp : P ≤ d p := Nat.le_of_dvd (hdpos p hp) hanchor
  have hm : 0 < m := Finset.prod_pos (fun i hi => hdpos i hi)
  have hpP := (hext p hp).2
  have hPm : P ≤ m := Nat.le_of_dvd hm (hanchor.trans (Finset.dvd_prod_of_mem d hp))
  have hpm : p ≤ m := hpP.trans hPm
  have hnpm : p*m=n := hprod
  have hm3 : 3 ≤ m := by
    by_contra! h
    have he : p=2 := by omega
    have he' : m=2 := by omega
    rw [he,he'] at hnpm
    omega
  obtain ⟨hdiv,hcard⟩ := assigned_base_specs n hn.ne' d hd
  have hB : 0 < B := Finset.prod_pos (fun t ht => pow_pos (Nat.prime_of_mem_primeFactors ht).pos _)
  have hsmall : B ≤ (2*p)^m := assigned_base_bound_finset _ p d hprime.pos hp hdpos
    (fun t ht => (hext t ht).2.trans hPdp)
  refine ⟨p,m,B,hprime,hnpm.symm,hm3,hpm,hB,hdiv,hcard,hsmall,(fun t ht => (hext t ht).1),?_⟩
  intro q hq hbig
  exact fresh_coprime n q d hq (fun t ht => lt_of_le_of_lt ((hext t ht).2.trans hPm) hbig)

/-- A strict rise of the Chebyshev theta function detects a prime in (x,y]. -/
theorem prime_of_theta_rise {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hrise : Chebyshev.theta x < Chebyshev.theta y) :
    ∃ q : ℕ, q.Prime ∧ x < q ∧ (q : ℝ) ≤ y := by
  classical
  by_contra hnone
  have heq : Nat.primesLE ⌊x⌋₊ = Nat.primesLE ⌊y⌋₊ := by
    ext p
    constructor
    · exact fun hp => Nat.primesLE_mono (Nat.floor_le_floor hxy) hp
    · intro hp
      obtain ⟨hp_le, hp_prime⟩ := Nat.mem_primesLE.mp hp
      have hpy := (Nat.le_floor_iff (hx.trans hxy)).mp hp_le
      have hpx : (p : ℝ) ≤ x := le_of_not_gt fun h => hnone ⟨p, hp_prime, h, hpy⟩
      exact Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hx).mpr hpx, hp_prime⟩
  rw [Chebyshev.theta_eq_sum_primesLE x, Chebyshev.theta_eq_sum_primesLE y, heq] at hrise
  exact (lt_irrefl _ hrise)

private theorem tail_window (lo : H1) (hi : H2) (x : ℝ) (hx : 100000000 < x) :
    ∃ q : ℕ, q.Prime ∧ x < q ∧ (q:ℝ) ≤ x*(1+2/Real.log x) := by
  have h9 : (9:ℝ) < x := (by norm_num : (9:ℝ) ≤ 100000000).trans_lt hx
  have hpos : 0 < x := by linarith
  have h2 : 2 < Real.log x := by
    apply (Real.lt_log_iff_exp_lt hpos).2
    rw [show (2:ℝ)=1+1 by norm_num, Real.exp_add]
    nlinarith [mul_pos (sub_pos.mpr Real.exp_one_lt_three) (show 0 < 3+Real.exp 1 by positivity)]
  let d := 2/Real.log x
  let y := x*(1+d)
  have hlpos : 0 < Real.log x := by linarith
  have hd : 0 < d := div_pos (by norm_num) hlpos
  have hd1 : d ≤ 1 := (div_le_iff₀ hlpos).2 (by linarith)
  have hxy : x ≤ y := by dsimp [y]; nlinarith [mul_pos hpos hd]
  have hyx : y ≤ 2*x := by dsimp [y]; nlinarith [mul_le_mul_of_nonneg_left hd1 hpos.le]
  have hlog := Real.log_le_log hpos hxy
  have cv (z : ℝ) : z/(2*Real.log x) = z*d/4 := by dsimp [d]; field_simp [hlpos.ne'] <;> ring
  have upper : Chebyshev.theta x - x ≤ x/(2*Real.log x) := by linarith [hi x hx]
  rw [cv] at upper
  have lower : -(y/(2*Real.log y)) ≤ Chebyshev.theta y - y := by linarith [lo y (hx.trans_le hxy)]
  have e : y/(2*Real.log y) ≤ y*d/4 := by
    rw [← cv]
    apply div_le_div_of_nonneg_left (hpos.le.trans hxy) (by positivity)
    linarith
  apply prime_of_theta_rise hpos.le hxy
  have hy : y=x+x*d := by dsimp [y]; ring
  nlinarith [mul_le_mul_of_nonneg_right hyx hd.le,mul_pos hpos hd]



private theorem two_prime_fourth_powers (a b : ℕ) (ha : a.Prime) (hb : b.Prime)
    (hne : a ≠ b) : (a^4*b^4).divisors.card = 25 := by
  have hcop : (a^4).Coprime (b^4) := Nat.coprime_pow_primes _ _ ha hb hne
  rw [hcop.card_divisors_mul, ← ArithmeticFunction.sigma_zero_apply,
    ArithmeticFunction.sigma_zero_apply_prime_pow ha,
    ← ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply_prime_pow hb]

private theorem prime200003 : Nat.Prime 200003 := by norm_num

theorem twentyfive :
    let W : ℕ := 625*200003^4
    25 ∣ W ∧ 10^24 ≤ W ∧ W < 10^25 ∧ W.divisors.card = 25 := by
  refine ⟨dvd_mul_of_dvd_left (by decide : 25 ∣ 625) _, by decide, by decide, ?_⟩
  exact two_prime_fourth_powers 5 200003 (by decide) prime200003 (by decide)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
private theorem fortynine : ∃ W, Candidate 49 W := by
  have hq : Nat.Prime 16384001 := by
    rw [Nat.prime_def_le_sqrt]
    refine ⟨by decide, ?_⟩
    intro k hk hbound hd
    have hb : k < 4096 := hbound.trans_lt (Nat.sqrt_lt.mpr (by decide : 16384001 < 4096*4096))
    have tab : ∀ a b : Fin 64, 2 ≤ 64*a.val+b.val → ¬ (64*a.val+b.val) ∣ 16384001 := by decide
    have hdecomp : 64*(k/64)+k%64 = k := by omega
    have h := tab ⟨k/64, by omega⟩ ⟨k%64, by omega⟩
    change 2 ≤ 64*(k/64)+k%64 → ¬ (64*(k/64)+k%64) ∣ 16384001 at h
    rw [hdecomp] at h
    exact h (by omega) hd
  refine ⟨_, candidate_of_prime_power_window (n:=49) (b:=7^6) (p:=7) (m:=7)
    (q:=16384001) (by decide) (by decide) (by decide) ?_ hq (by decide)
    (by decide) (by decide)⟩
  rw [← ArithmeticFunction.sigma_zero_apply,
    ArithmeticFunction.sigma_zero_apply_prime_pow (by decide : Nat.Prime 7)]


/-- Bertrand supplies the new prime when its exponent is one or two. R bounds
the old prime factors. The size assumption guarantees a fresh prime above R. -/
theorem bertrand_prime_window {n b p R : ℕ} (hn : 0 < n) (hb : 0 < b) (hR : 0 < R)
    (hp : p = 2 ∨ p = 3) (hsize : b * R ^ (p - 1) ≤ 10 ^ (n - 1)) :
    ∃ q : ℕ, q.Prime ∧ R < q ∧ 10 ^ (n - 1) ≤ b * q ^ (p - 1) ∧
      b * q ^ (p - 1) < 10 ^ n := by
  let L : ℕ := 10 ^ (n - 1)
  have hRpow : R ^ (p - 1) ≤ L / b := (Nat.le_div_iff_mul_le hb).mpr (by simpa [Nat.mul_comm] using hsize)
  have hcut : ∃ s : ℕ, R ≤ s ∧ s ^ (p - 1) ≤ L / b ∧
      ∀ q : ℕ, s < q → L / b < q ^ (p - 1) := by
    rcases hp with rfl | rfl
    · exact ⟨L / b, by simpa using hRpow, by simp, by simp⟩
    · refine ⟨(L / b).sqrt, Nat.le_sqrt'.mpr hRpow, Nat.sqrt_le' _, ?_⟩
      intro q hq
      exact Nat.sqrt_lt'.mp hq
  obtain ⟨s, hrs, hs, hs'⟩ := hcut
  obtain ⟨q, hq, hsql, hsqu⟩ := Nat.exists_prime_lt_and_le_two_mul s (by omega)
  refine ⟨q, hq, lt_of_le_of_lt hrs hsql, ?_, ?_⟩
  · simpa [Nat.mul_comm] using ((Nat.div_lt_iff_lt_mul hb).mp (hs' q hsql)).le
  · have h4 : 2 ^ (p - 1) ≤ 4 := by rcases hp with rfl | rfl <;> decide
    have hbase : s ^ (p - 1) * b ≤ L := (Nat.le_div_iff_mul_le hb).mp hs
    have hL : 0 < L := by dsimp [L]; positivity
    calc
      b * q ^ (p - 1) ≤ b * ((2 * s) ^ (p - 1)) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsqu _)
      _ = 2 ^ (p - 1) * (s ^ (p - 1) * b) := by rw [mul_pow]; ring
      _ ≤ 4 * L := Nat.mul_le_mul h4 hbase
      _ < 10 * L := by omega
      _ = 10 ^ n := by
        change 10 * 10 ^ (n - 1) = 10 ^ n
        conv_rhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
        exact Nat.mul_comm _ _


private theorem prime_interval_threshold (p m B : ℕ) (hp : 5 ≤ p) (hm : p ≤ m)
    (ho : ¬ 2 ∣ p*m) (hne : p*m ∉ [25,35,49]) (hB : B ≤ (2*p)^m)
    (hbudget : B*3^((p-1)*m) < 10^(p*m-1)) :
    B*100000001^(p-1) ≤ 10^(p*m-1) := by
  by_cases hlarge : 17 ≤ m
  · have hpow : 100000001 ≤ 3^m :=
      (by decide : 100000001 ≤ 3^17).trans (Nat.pow_le_pow_right (by decide) hlarge)
    calc
      _ ≤ B*(3^m)^(p-1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpow _)
      _ = B*3^((p-1)*m) := by rw [← pow_mul, Nat.mul_comm m]
      _ ≤ _ := hbudget.le
  · have table : ∀ u v : Fin 17, 5 ≤ u.val → u.val ≤ v.val →
        ¬ 2 ∣ u.val*v.val → u.val*v.val ∉ [25,35,49] →
        (2*u.val)^v.val*100000001^(u.val-1) ≤ 10^(u.val*v.val-1) := by decide
    exact (Nat.mul_le_mul_right _ hB).trans
      (table ⟨p, by omega⟩ ⟨m, by omega⟩ hp hm ho hne)



private theorem decimal_prime_on_tail (p m B : ℕ) (hp : 2 ≤ p)
    (hpm : p ≤ m) (hB : 0 < B) (hb : B*3^((p-1)*m) < 10^(p*m-1))
    (ht : B*100000001^(p-1) ≤ 10^(p*m-1))
    (gap : ∀ y : ℝ, 100000000 < y → ∃ q : ℕ, q.Prime ∧ y < q ∧
      (q:ℝ) ≤ y*(1+2/Real.log y)) :
    ∃ q : ℕ, q.Prime ∧ 3^m < q ∧ 10^(p*m-1) ≤ B*q^(p-1) ∧ B*q^(p-1) < 10^(p*m) := by
  let k := p-1
  let L : ℝ := 10^(p*m-1)
  let x : ℝ := (L/(B:ℝ)) ^ (1/(k:ℝ))
  have hk : 0 < k := by dsimp [k]; omega
  have hkr : (0:ℝ) < k := by exact_mod_cast hk
  have hbr : (0:ℝ) < B := by exact_mod_cast hB
  have hL : 0 < L := by dsimp [L]; positivity
  have ha : 0 < L/(B:ℝ) := div_pos hL hbr
  have hx : 0 < x := Real.rpow_pos_of_pos ha _
  have hroot : x^k = L/(B:ℝ) := by
    rw [← Real.rpow_natCast]
    dsimp only [x]
    rw [← Real.rpow_mul ha.le, one_div_mul_cancel hkr.ne', Real.rpow_one]
  have hBx : (B:ℝ)*x^k = L := by rw [hroot]; field_simp
  have hsmall : (3:ℝ)^m < x := by
    by_contra! h
    have H := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.le h k) hbr.le
    rw [hBx, ← pow_mul, Nat.mul_comm m k] at H
    have H' : (B:ℝ)*3^(k*m) < L := by dsimp only [k,L]; exact_mod_cast hb
    linarith
  have hlarge : 100000000 < x := by
    by_contra! h
    have hh : x < 100000001 := by linarith
    have H : x^k < (100000001:ℝ)^k := by gcongr
    have H' := mul_lt_mul_of_pos_left H hbr
    rw [hBx] at H'
    have H'' : (B:ℝ)*100000001^k ≤ L := by dsimp only [k,L]; exact_mod_cast ht
    linarith
  obtain ⟨q,hq,hlo,hhi⟩ := gap x hlarge
  have hqm : 3^m < q := by exact_mod_cast hsmall.trans hlo
  have hm : 0 < m := by omega
  have hlog := log_large_of_three_power m p x hpm hm hsmall
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hlpos : 0 < Real.log x := by linarith
  let u := 2/Real.log x
  have hratio : (q:ℝ)/x ≤ 1+u := (div_le_iff₀ hx).mpr (by simpa only [mul_comm x] using hhi)
  have hfrac : ((p-1:ℕ):ℝ)*u < 2 := by
    have hcast : ((p-1:ℕ):ℝ) = (p:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ p)]; norm_num
    dsimp [u]
    rw [hcast, ← mul_div_assoc, div_lt_iff₀ hlpos]
    linarith
  have hhi' : ((q:ℝ)/x)^(p-1) < 10 := calc
    ((q:ℝ)/x)^(p-1) ≤ (Real.exp u)^(p-1) :=
      pow_le_pow_left₀ (by positivity) (hratio.trans (by simpa only [add_comm] using Real.add_one_le_exp u)) _
    _ = Real.exp (((p-1:ℕ):ℝ)*u) := (Real.exp_nat_mul u _).symm
    _ < Real.exp 2 := Real.exp_lt_exp.mpr hfrac
    _ < 10 := by
      rw [show (2:ℝ) = 1+1 by norm_num, Real.exp_add]
      nlinarith [Real.exp_one_lt_three, Real.exp_pos 1,
        mul_pos (sub_pos.mpr Real.exp_one_lt_three) (show 0 < 3+Real.exp 1 by positivity)]
  refine ⟨q,hq,hqm,?_,?_⟩
  · have H := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.le hlo.le k) hbr.le
    rw [hBx] at H
    dsimp only [k,L] at H
    exact_mod_cast H
  · change ((q:ℝ)/x)^k < 10 at hhi'
    rw [div_pow, div_lt_iff₀ (pow_pos hx _)] at hhi'
    have H : (B:ℝ)*(q:ℝ)^k < 10^(p*m) := calc
      _ < (B:ℝ)*(10*x^k) := mul_lt_mul_of_pos_left hhi' hbr
      _ = 10*((B:ℝ)*x^k) := by ring
      _ = 10*L := by rw [hBx]
      _ = _ := by
        have hn : 0 < p*m := Nat.mul_pos (by omega) hm
        dsimp only [L]
        conv_rhs => rw [show p*m = (p*m-1)+1 by omega, pow_succ]
        ring
    exact_mod_cast H

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a182749.main := by
  intro lo hi n hn hs
  constructor
  · rintro hw rfl
    exact no_candidate_four hw
  · intro h4
    obtain ⟨p,m,B,hprime,hnpm,hm3,hpm,hB,hdiv,hcard,hsmall,hmin,hfresh⟩ := baseline_checked n hn hs h4
    have hp2 := hprime.two_le
    have h4p : 2*p ≤ 4*p := by omega
    have hbudget := decimal_budget p m B hp2 hm3 (hsmall.trans (Nat.pow_le_pow_left h4p _))
    have hh : m ≤ 3^m := by
      have := unchanged 3 m (by decide)
      omega
    by_cases h25 : n = 25
    · rw [h25]
      exact ⟨_,twentyfive⟩
    by_cases h49 : n = 49
    · rw [h49]
      exact fortynine
    have hw : ∃ q : ℕ, q.Prime ∧ 3^m < q ∧
        10^(p*m-1) ≤ B*q^(p-1) ∧ B*q^(p-1)<10^(p*m) := by
      by_cases hPS : p=2 ∨ p=3
      · apply bertrand_prime_window (by omega) hB (by positivity) hPS
        rw [← pow_mul, Nat.mul_comm m]
        exact hbudget.le
      · have hNE : p ≠ 4 := by intro e; rw [e] at hprime; norm_num at hprime
        have hp5 : 5 ≤ p := by omega
        have ho : ¬ 2 ∣ n := by
          intro he
          have h := hmin 2 (Nat.mem_primeFactors.mpr ⟨by decide, he, hn.ne'⟩)
          omega
        have h35 : n ≠ 35 := by
          rintro rfl
          exact hs ((Nat.squarefree_mul (by decide : Nat.Coprime 5 7)).2
            ⟨(by decide : Nat.Prime 5).squarefree, (by decide : Nat.Prime 7).squarefree⟩)
        have hne : n ∉ [25,35,49] := by simp [h25,h35,h49]
        have ht := prime_interval_threshold p m B hp5 hpm
          (hnpm ▸ ho) (hnpm ▸ hne) hsmall hbudget
        exact decimal_prime_on_tail p m B hp2 hpm hB hbudget ht (tail_window lo hi)
    obtain ⟨q,hq,hbig,hl,hu⟩ := hw
    exact ⟨_, candidate_of_prime_power_window hprime.pos hnpm hdiv hcard hq
      (hfresh q hq (lt_of_le_of_lt hh hbig)) (hnpm.symm ▸ hl) (hnpm.symm ▸ hu)⟩

end
end OMA.R_oeis_a182749_R2
