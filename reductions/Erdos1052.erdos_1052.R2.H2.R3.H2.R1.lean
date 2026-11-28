import OMAReductions.R_Erdos1052_erdos_1052_R2_H2_R3

/-!
# Mod-3 and mod-5 elimination of high-jump transitions

Reduction of `Erdos1052.erdos_1052.R2.H2.R3.H2` (uniform bound on high-jump simple primes
`q in S` with `r = ordCompl[2] (1 + q) in S` and `32 | 1 + q`).

For every high-jump prime `q in S` with `1 + q = 2^v * r` (`v >= 5`, `r in S`), we prove:
1. Mod-3 parity lock: since `q >= 31` is prime, `q % 3 != 0`. Consequently:
   - If `r % 3 = 1`, then `v` must be odd (otherwise `3 | q`) and `q % 3 = 1`.
   - If `Even v`, then either `r = 3` (at most `1` such `q`, by `demand_inj`) or `3 | 1 + r`
     (at most `c.factorization 3 + 1` such `q`, by `demand_budget` at `p = 3`).
   Hence ALL even-exponent high jumps (`Even ((1 + q).factorization 2)`) are unconditionally
   bounded in count by `c.factorization 3 + 2`.
2. Mod-5 filter on the remaining odd-exponent jumps: since `q >= 31` is prime, `q % 5 != 0`,
   so `(2^v * r) % 5 != 1`. By `demand_inj` and `demand_budget` at `p = 5`, at most
   `c.factorization 5 + 2` jumps have `r = 5` or `r % 5 = 4`. Every surviving odd-exponent
   high jump has `q % 3 = 1`, `r % 3 = 1`, and splits cleanly by `v % 4`:
   - `H1`: `v % 4 = 1` (`v in {5, 9, 13, ...}`), which additionally forces `r % 5 in {1, 2}`
     (since `r % 5 = 3` gives `2^v * r = 1 (mod 5)`).
   - `H2`: `v % 4 = 3` (`v in {7, 11, 15, ...}`), which additionally forces `r % 5 in {1, 3}`
     (since `r % 5 = 2` gives `2^v * r = 1 (mod 5)`).
-/

namespace OMA.R_Erdos1052_erdos_1052_R2_H2_R3_H2_R1

open scoped BigOperators
open OMA.R_Erdos1052_erdos_1052_R2_H2_R3

/-- High-jump simple primes with `v_2(1 + q) = 1 (mod 4)`, `r = ordCompl[2] (1 + q) in S`,
`r % 3 = 1`, `q % 3 = 1`, and `r % 5 = 1 or 2`. -/
def H1 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ K : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2 ^ a * c
      let u := ∏ p ∈ b.primeFactors, (1 + p ^ b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) →
      u * (∏ p ∈ S, (1 + p)) = (2 * b) * (∏ p ∈ S, p) →
      (S.filter (fun q =>
        let r := ordCompl[2] (1 + q)
        r ∈ S ∧ 32 ∣ 1 + q ∧ (1 + q).factorization 2 % 4 = 1 ∧
        r % 3 = 1 ∧ q % 3 = 1 ∧ (r % 5 = 1 ∨ r % 5 = 2))).card ≤ K

/-- High-jump simple primes with `v_2(1 + q) = 3 (mod 4)`, `r = ordCompl[2] (1 + q) in S`,
`r % 3 = 1`, `q % 3 = 1`, and `r % 5 = 1 or 3`. -/
def H2 : Prop :=
  ∀ c : ℕ, Odd c → (∀ p ∈ c.primeFactors, 2 ≤ c.factorization p) →
    ∃ K : ℕ, ∀ a : ℕ, ∀ S : Finset ℕ,
      let b := 2 ^ a * c
      let u := ∏ p ∈ b.primeFactors, (1 + p ^ b.factorization p)
      5 ≤ a → 4 ≤ S.card → S ⊆ Finset.Icc 3 u →
      (∀ p ∈ S, p.Prime ∧ ¬ p ∣ b) →
      u * (∏ p ∈ S, (1 + p)) = (2 * b) * (∏ p ∈ S, p) →
      (S.filter (fun q =>
        let r := ordCompl[2] (1 + q)
        r ∈ S ∧ 32 ∣ 1 + q ∧ (1 + q).factorization 2 % 4 = 3 ∧
        r % 3 = 1 ∧ q % 3 = 1 ∧ (r % 5 = 1 ∨ r % 5 = 3))).card ≤ K

/-- Odd parts of shifted simple primes divide `c * prod_{q in S} q`. -/
theorem odd_demands_divide {a c : ℕ} {S : Finset ℕ}
    (hbal : (∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p)) *
      (∏ q ∈ S, (1 + q)) = 2 * (2 ^ a * c) * (∏ q ∈ S, q)) :
    (∏ q ∈ S, ordCompl[2] (1 + q)) ∣ c * ∏ q ∈ S, q := by
  have hd := Finset.prod_dvd_prod_of_dvd (s := S) (fun q : ℕ => ordCompl[2] (1 + q))
    (fun q => 1 + q) (fun q _ => Nat.ordCompl_dvd (1 + q) 2)
  have hm := hd.trans (dvd_mul_left (∏ q ∈ S, (1 + q))
    (∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p)))
  rw [hbal, show 2 * (2 ^ a * c) * (∏ q ∈ S, q) = 2 ^ (a + 1) * (c * ∏ q ∈ S, q) by
    rw [pow_succ]; ac_rfl] at hm
  have hcop : (∏ q ∈ S, ordCompl[2] (1 + q)).Coprime 2 :=
    Nat.coprime_prod_left_iff.mpr fun q _ =>
      (Nat.prime_two.coprime_iff_not_dvd.mpr
        (Nat.not_dvd_ordCompl Nat.prime_two (by omega : 1 + q ≠ 0))).symm
  exact (hcop.pow_right (a + 1)).dvd_of_dvd_mul_left hm

/-- Residue of `2^v` modulo `3`. -/
theorem two_pow_mod_three (v : ℕ) : 2 ^ v % 3 = if v % 2 = 0 then 1 else 2 := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    split_ifs <;> omega

/-- Residue of `2^v` modulo `5`. -/
theorem two_pow_mod_five (v : ℕ) :
    (v % 4 = 1 → 2 ^ v % 5 = 2) ∧ (v % 4 = 3 → 2 ^ v % 5 = 3) := by
  have hall : ∀ n : ℕ, 2 ^ n % 5 = match n % 4 with
      | 0 => 1
      | 1 => 2
      | 2 => 4
      | _ => 3 := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
      rw [pow_succ, Nat.mul_mod, ih]
      have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
      rcases h4 with h | h | h | h
      · have h' : (n + 1) % 4 = 1 := by omega
        simp [h, h']
      · have h' : (n + 1) % 4 = 2 := by omega
        simp [h, h']
      · have h' : (n + 1) % 4 = 3 := by omega
        simp [h, h']
      · have h' : (n + 1) % 4 = 0 := by omega
        simp [h, h']
  exact ⟨fun h => by rw [hall, h]; rfl, fun h => by rw [hall, h]; rfl⟩

/-- A prime `q` with `32 | 1 + q` satisfies `31 <= q`, `q % 3 != 0`, and `q % 5 != 0`. -/
theorem high_jump_mod_three_five {q : ℕ} (hq : q.Prime) (h32 : 32 ∣ 1 + q) :
    31 ≤ q ∧ q % 3 ≠ 0 ∧ q % 5 ≠ 0 := by
  have hle := Nat.le_of_dvd (by omega : 0 < 1 + q) h32
  have h3 : q % 3 ≠ 0 := fun h => by
    have hd := Nat.dvd_iff_mod_eq_zero.mpr h
    have eq := (hq.dvd_iff_eq (by decide : 3 ≠ 1)).mp hd
    omega
  have h5 : q % 5 ≠ 0 := fun h => by
    have hd := Nat.dvd_iff_mod_eq_zero.mpr h
    have eq := (hq.dvd_iff_eq (by decide : 5 ≠ 1)).mp hd
    omega
  exact ⟨by omega, h3, h5⟩

/-- Unconditional mod-3 bound: for any fixed odd `c`, the number of high-jump simple primes
with even 2-adic valuation `v_2(1 + q)` is at most `c.factorization 3 + 2`. -/
theorem even_high_jumps_le {a c : ℕ} {S : Finset ℕ} (hc : Odd c)
    (hp : ∀ p ∈ S, p.Prime ∧ ¬ p ∣ 2 ^ a * c)
    (hbal : (∏ p ∈ (2 ^ a * c).primeFactors, (1 + p ^ (2 ^ a * c).factorization p)) *
      (∏ p ∈ S, (1 + p)) = (2 * (2 ^ a * c)) * (∏ p ∈ S, p)) :
    (S.filter (fun q => ordCompl[2] (1 + q) ∈ S ∧ 32 ∣ 1 + q ∧
      (1 + q).factorization 2 % 2 = 0)).card ≤ c.factorization 3 + 2 := by
  classical
  let d (q : ℕ) := ordCompl[2] (1 + q)
  have hd_ne : ∀ q ∈ S, d q ≠ 0 := fun q _ => (Nat.ordCompl_pos 2 (by omega : 1 + q ≠ 0)).ne'
  have hdiv := odd_demands_divide hbal
  have hp1 : ∀ q ∈ S, q.Prime := fun q hq => (hp q hq).1
  have hout : ∀ q ∈ S, ¬ q ∣ c := fun q hq h => (hp q hq).2 (dvd_mul_of_dvd_right h _)
  let E := S.filter (fun q => d q ∈ S ∧ 32 ∣ 1 + q ∧ (1 + q).factorization 2 % 2 = 0)
  let B3 := insert 3 (S.filter (fun r => 3 ∣ d r))
  have hmaps : Set.MapsTo d (E : Set ℕ) (B3 : Set ℕ) := by
    intro q hq
    obtain ⟨hqS, hrS, h32, heven⟩ := Finset.mem_filter.mp hq
    have hq3 := (high_jump_mod_three_five (hp1 q hqS) h32).2.1
    have hsplit : 2 ^ ((1 + q).factorization 2) * d q = 1 + q :=
      Nat.ordProj_mul_ordCompl_eq_self (1 + q) 2
    have hmod : (1 + q) % 3 = d q % 3 := by
      rw [← hsplit, Nat.mul_mod, two_pow_mod_three, if_pos heven, one_mul, Nat.mod_mod]
    have hr_not1 : d q % 3 ≠ 1 := by omega
    by_cases hr3 : d q = 3
    · exact Finset.mem_coe.mpr (hr3 ▸ Finset.mem_insert_self 3 _)
    · have hr0 : d q % 3 ≠ 0 := fun h => by
        have eq := ((hp1 _ hrS).dvd_iff_eq (by decide : 3 ≠ 1)).mp (Nat.dvd_iff_mod_eq_zero.mpr h)
        exact hr3 eq
      have hr2 : d q % 3 = 2 := by omega
      have h3dvd : 3 ∣ 1 + d q := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
      have h3ord : 3 ∣ d (d q) := Nat.dvd_ordCompl_of_dvd_not_dvd h3dvd (by decide : ¬ 2 ∣ 3)
      exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hrS, h3ord⟩))
  have hinj : Set.InjOn d (E : Set ℕ) := by
    intro q₁ hq₁ q₂ hq₂ he
    obtain ⟨hq₁S, hr₁S, _, _⟩ := Finset.mem_filter.mp hq₁
    obtain ⟨hq₂S, _, _, _⟩ := Finset.mem_filter.mp hq₂
    exact demand_inj hc.pos.ne' hp1 hout hd_ne hdiv hq₁S hq₂S hr₁S he
  have hcard_E : E.card ≤ B3.card := Finset.card_le_card_of_injOn d hmaps hinj
  have hbud := demand_budget hc.pos.ne' hp1 hd_ne hdiv Nat.prime_three
  have hB3_le : B3.card ≤ (S.filter (fun r => 3 ∣ d r)).card + 1 := Finset.card_insert_le _ _
  have hbud' : (S.filter (fun r => 3 ∣ d r)).card ≤ c.factorization 3 + 1 := by
    change (S.filter (fun r => 3 ∣ d r)).card ≤ _ at hbud
    split_ifs at hbud <;> omega
  change E.card ≤ _
  omega

/-- Every high-jump simple prime outside the bounded mod-3 and mod-5 exceptional sets falls
into either the `v % 4 = 1` branch or the `v % 4 = 3` branch with locked residues. -/
theorem classify_nonexceptional_jump {q r v : ℕ} (hq : q.Prime) (hr : r.Prime)
    (h32 : 32 ∣ 1 + q) (hsplit : 2 ^ v * r = 1 + q)
    (hr_ne3 : r ≠ 3) (hr_not3 : ¬ 3 ∣ 1 + r)
    (hr_ne5 : r ≠ 5) (hr_not5 : ¬ 5 ∣ 1 + r) :
    r % 3 = 1 ∧ q % 3 = 1 ∧
      ((v % 4 = 1 ∧ (r % 5 = 1 ∨ r % 5 = 2)) ∨
       (v % 4 = 3 ∧ (r % 5 = 1 ∨ r % 5 = 3))) := by
  have hq35 := high_jump_mod_three_five hq h32
  have hr3_ne0 : r % 3 ≠ 0 := fun h =>
    hr_ne3 ((hr.dvd_iff_eq (by decide : 3 ≠ 1)).mp (Nat.dvd_iff_mod_eq_zero.mpr h))
  have hr3_ne2 : r % 3 ≠ 2 := fun h => hr_not3 (Nat.dvd_iff_mod_eq_zero.mpr (by omega))
  have hr3 : r % 3 = 1 := by omega
  have hv_odd : v % 2 = 1 := by
    by_contra he
    have hv0 : v % 2 = 0 := by omega
    have hmod : (1 + q) % 3 = 1 := by
      rw [← hsplit, Nat.mul_mod, two_pow_mod_three, if_pos hv0, hr3]
    omega
  have hq3 : q % 3 = 1 := by
    have hmod : (1 + q) % 3 = 2 := by
      rw [← hsplit, Nat.mul_mod, two_pow_mod_three, if_neg (by omega), hr3]
    omega
  have hr5_ne0 : r % 5 ≠ 0 := fun h =>
    hr_ne5 ((hr.dvd_iff_eq (by decide : 5 ≠ 1)).mp (Nat.dvd_iff_mod_eq_zero.mpr h))
  have hr5_ne4 : r % 5 ≠ 4 := fun h => hr_not5 (Nat.dvd_iff_mod_eq_zero.mpr (by omega))
  have hr5_cases : r % 5 = 1 ∨ r % 5 = 2 ∨ r % 5 = 3 := by omega
  have hv4_cases : v % 4 = 1 ∨ v % 4 = 3 := by omega
  refine ⟨hr3, hq3, ?_⟩
  rcases hv4_cases with hv1 | hv3
  · left
    refine ⟨hv1, ?_⟩
    have h2v : 2 ^ v % 5 = 2 := (two_pow_mod_five v).1 hv1
    rcases hr5_cases with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr h2
    · exfalso
      have hmod : (1 + q) % 5 = 1 := by
        rw [← hsplit, Nat.mul_mod, h2v, h3]
      omega
  · right
    refine ⟨hv3, ?_⟩
    have h2v : 2 ^ v % 5 = 3 := (two_pow_mod_five v).2 hv3
    rcases hr5_cases with h1 | h2 | h3
    · exact Or.inl h1
    · exfalso
      have hmod : (1 + q) % 5 = 1 := by
        rw [← hsplit, Nat.mul_mod, h2v, h2]
      omega
    · exact Or.inr h3

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R2_H2_R3.H2 := by
  classical
  intro h1 h2 c hc hpow
  obtain ⟨K1, hK1⟩ := h1 c hc hpow
  obtain ⟨K2, hK2⟩ := h2 c hc hpow
  refine ⟨c.factorization 3 + c.factorization 5 + 4 + K1 + K2, ?_⟩
  intro a S b u ha hS hsub hp hbal
  let d (q : ℕ) := ordCompl[2] (1 + q)
  have hd_ne : ∀ q ∈ S, d q ≠ 0 := fun q _ => (Nat.ordCompl_pos 2 (by omega : 1 + q ≠ 0)).ne'
  have hdiv := odd_demands_divide hbal
  have hp1 : ∀ q ∈ S, q.Prime := fun q hq => (hp q hq).1
  have hout : ∀ q ∈ S, ¬ q ∣ c := fun q hq h => (hp q hq).2 (dvd_mul_of_dvd_right h _)
  let J := S.filter (fun q => d q ∈ S ∧ 32 ∣ 1 + q)
  let Exc := J.filter (fun q => d q = 3 ∨ 3 ∣ 1 + d q ∨ d q = 5 ∨ 5 ∣ 1 + d q)
  let B1 := S.filter (fun q => d q ∈ S ∧ 32 ∣ 1 + q ∧ (1 + q).factorization 2 % 4 = 1 ∧
    d q % 3 = 1 ∧ q % 3 = 1 ∧ (d q % 5 = 1 ∨ d q % 5 = 2))
  let B3 := S.filter (fun q => d q ∈ S ∧ 32 ∣ 1 + q ∧ (1 + q).factorization 2 % 4 = 3 ∧
    d q % 3 = 1 ∧ q % 3 = 1 ∧ (d q % 5 = 1 ∨ d q % 5 = 3))
  have hcover : J ⊆ Exc ∪ B1 ∪ B3 := by
    intro q hq
    obtain ⟨hqS, hrS, h32⟩ := Finset.mem_filter.mp hq
    by_cases hex : d q = 3 ∨ 3 ∣ 1 + d q ∨ d q = 5 ∨ 5 ∣ 1 + d q
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hq, hex⟩))
    · push Not at hex
      obtain ⟨hr_ne3, hr_not3, hr_ne5, hr_not5⟩ := hex
      have hsplit : 2 ^ ((1 + q).factorization 2) * d q = 1 + q :=
        Nat.ordProj_mul_ordCompl_eq_self (1 + q) 2
      obtain ⟨hr3, hq3, hbranch⟩ := classify_nonexceptional_jump (hp1 q hqS) (hp1 _ hrS)
        h32 hsplit hr_ne3 hr_not3 hr_ne5 hr_not5
      rcases hbranch with ⟨hv1, hr5⟩ | ⟨hv3, hr5⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hqS, hrS, h32, hv1, hr3, hq3, hr5⟩))
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hqS, hrS, h32, hv3, hr3, hq3, hr5⟩)
  let TargetExc := ({3, 5} : Finset ℕ) ∪ S.filter (fun r => 3 ∣ d r) ∪ S.filter (fun r => 5 ∣ d r)
  have hmaps : Set.MapsTo d (Exc : Set ℕ) (TargetExc : Set ℕ) := by
    intro q hq
    obtain ⟨hqJ, hex⟩ := Finset.mem_filter.mp hq
    obtain ⟨_, hrS, _⟩ := Finset.mem_filter.mp hqJ
    apply Finset.mem_coe.mpr
    rcases hex with h3 | h3d | h5 | h5d
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simp [h3]))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hrS, Nat.dvd_ordCompl_of_dvd_not_dvd h3d (by decide : ¬ 2 ∣ 3)⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simp [h5]))
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hrS, Nat.dvd_ordCompl_of_dvd_not_dvd h5d (by decide : ¬ 2 ∣ 5)⟩)
  have hinj : Set.InjOn d (Exc : Set ℕ) := by
    intro q₁ hq₁ q₂ hq₂ he
    obtain ⟨hq₁S, hr₁S, _⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hq₁).1
    obtain ⟨hq₂S, _, _⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hq₂).1
    exact demand_inj hc.pos.ne' hp1 hout hd_ne hdiv hq₁S hq₂S hr₁S he
  have hExc_le : Exc.card ≤ TargetExc.card := Finset.card_le_card_of_injOn d hmaps hinj
  have hbud3 := demand_budget hc.pos.ne' hp1 hd_ne hdiv Nat.prime_three
  have hbud5 := demand_budget hc.pos.ne' hp1 hd_ne hdiv (by decide : Nat.Prime 5)
  have h3_le : (S.filter (fun r => 3 ∣ d r)).card ≤ c.factorization 3 + 1 := by
    change (S.filter (fun r => 3 ∣ d r)).card ≤ _ at hbud3
    split_ifs at hbud3 <;> omega
  have h5_le : (S.filter (fun r => 5 ∣ d r)).card ≤ c.factorization 5 + 1 := by
    change (S.filter (fun r => 5 ∣ d r)).card ≤ _ at hbud5
    split_ifs at hbud5 <;> omega
  have hTExc : TargetExc.card ≤ c.factorization 3 + c.factorization 5 + 4 := by
    have hu1 := Finset.card_union_le (({3, 5} : Finset ℕ) ∪ S.filter (fun r => 3 ∣ d r))
      (S.filter (fun r => 5 ∣ d r))
    have hu2 := Finset.card_union_le ({3, 5} : Finset ℕ) (S.filter (fun r => 3 ∣ d r))
    have hpair : ({3, 5} : Finset ℕ).card = 2 := by decide
    change TargetExc.card ≤ _ at hu1
    omega
  have hB1 : B1.card ≤ K1 := hK1 a S ha hS hsub hp hbal
  have hB3 : B3.card ≤ K2 := hK2 a S ha hS hsub hp hbal
  have hJ_le : J.card ≤ Exc.card + B1.card + B3.card :=
    (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  change J.card ≤ _
  omega

end OMA.R_Erdos1052_erdos_1052_R2_H2_R3_H2_R1
