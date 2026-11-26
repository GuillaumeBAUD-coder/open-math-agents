import FormalConjectures.ErdosProblems.«420»

-- Reduction of part I, prepared for @jpollard-cs. The open arithmetic input is H1.
-- Each block contains a prime multiple whose cofactor is at most a power of log.
-- H2 transfers that hit to factorial divisors. prime_gain_proof discharges it.
-- polylog_packing fits disjoint blocks into a longer window.
namespace OMA.R_Erdos420_erdos_420_parts_i_R1

open Filter
open scoped ArithmeticFunction.sigma

def H1 : Prop :=
  ∃ A : ℕ, ∀ᶠ x : ℕ in atTop, ∃ p s : ℕ,
    p.Prime ∧ 0 < s ∧ s < p ∧ s ≤ ⌊Real.log x ^ A⌋₊ ∧
    x < s * p ∧ s * p ≤ x + ⌊Real.log x ^ A⌋₊

def H2 : Prop :=
  ∀ a b p s : ℕ, p.Prime → 0 < s → s < p → a < s * p → s * p ≤ b →
    (s + 1) * (σ 0 a.factorial) ≤ s * (σ 0 b.factorial)

lemma polylog_packing (A : ℕ) :
    ∀ᶠ C : ℝ in atTop, ∀ K : ℕ, ∀ᶠ n : ℕ in atTop,
    ∃ b : ℕ, 0 < b ∧ K * b * b ≤ ⌊(Real.log n)^C⌋₊ ∧
      ∀ x : ℕ, n ≤ x → x ≤ n + K*b*b → ⌊Real.log x ^ A⌋₊ ≤ b := by
  let E : ℕ := 2*A + 1
  filter_upwards [eventually_ge_atTop (E : ℝ)] with C hC
  intro K
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbound := (isLittleO_log_rpow_rpow_atTop (E : ℝ) (by norm_num : (0 : ℝ) < 1)).bound
    (by norm_num : (0 : ℝ) < 1)
  have hnBound := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hbound
  filter_upwards [hlog.eventually_ge_atTop 1,
    hlog.eventually_ge_atTop ((K : ℝ) * (2:ℝ)^(2*A)),
    eventually_ge_atTop (2 : ℕ), hnBound] with n hl hk hn hE
  let L := Real.log (n : ℝ)
  change 1 ≤ L at hl
  change (K : ℝ)*2^(2*A) ≤ L at hk
  have hL : 0 ≤ L := by linarith
  have hpow : L^E ≤ (n : ℝ) := by
    simpa only [Function.comp_apply, one_mul, Real.rpow_one, Real.rpow_natCast,
      Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hL E), abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ ↑n), L]
      using hE
  let b : ℕ := ⌊(2*L)^A⌋₊
  have hfloor : (b : ℝ) ≤ (2*L)^A := Nat.floor_le (by positivity)
  have hb : 0 < b := (Nat.one_le_floor_iff _).2 (one_le_pow₀ (by linarith : 1 ≤ 2*L))
  have hblocks : ((K*b*b : ℕ) : ℝ) ≤ L^E := by
    push_cast
    calc
      (K : ℝ)*b*b ≤ (K : ℝ)*(2*L)^A*(2*L)^A := by gcongr
      _ = ((K : ℝ)*2^(2*A))*L^(2*A) := by
        rw [mul_pow, two_mul A, pow_add, pow_add]; ring
      _ ≤ L*L^(2*A) := mul_le_mul_of_nonneg_right hk (pow_nonneg hL _)
      _ = L^E := by dsimp [E]; rw [pow_succ, mul_comm]
  have hfit : K*b*b ≤ ⌊(Real.log n)^C⌋₊ := by
    apply Nat.le_floor
    rw [← Real.rpow_natCast L E] at hblocks
    exact hblocks.trans (Real.rpow_le_rpow_of_exponent_le hl hC)
  refine ⟨b, hb, hfit, ?_⟩
  intro x hx hx'
  have hkbn : K*b*b ≤ n := by exact_mod_cast hblocks.trans hpow
  have hxn : (x : ℝ) ≤ 2*(n : ℝ) := by exact_mod_cast (show x ≤ 2*n by omega)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlog2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hxl : Real.log (x : ℝ) ≤ 2*L := by
    have h := Real.log_le_log hxpos hxn
    rw [Real.log_mul (by norm_num) hnpos.ne'] at h
    change Real.log (x : ℝ) ≤ Real.log 2 + L at h
    linarith
  apply Nat.floor_le_floor
  exact pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))) hxl A

lemma prime_gain_proof : H2 := by
  intro a b p s hp hs hsp ha hb
  let d := a.factorial
  let e := d.factorization p
  let v := ordCompl[p] d
  have hd : d ≠ 0 := Nat.factorial_ne_zero _
  have hdet : p^e * v = d := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hcop : p.Coprime v := Nat.coprime_ordCompl hp hd
  have hpmul : p*d ∣ (s*p).factorial := by
    obtain ⟨m, hm⟩ : ∃ m : ℕ, s*p = m+1 := ⟨s*p-1, by omega⟩
    rw [hm, Nat.factorial_succ]
    apply Nat.mul_dvd_mul
    · rw [← hm]; exact dvd_mul_left p s
    · exact Nat.factorial_dvd_factorial (by omega)
  have hfactor := (Nat.factorization_le_iff_dvd (Nat.mul_ne_zero hp.ne_zero hd)
    (Nat.factorial_ne_zero _)).2 hpmul p
  have hbefore : (s*p).factorial.factorization p = s := by
    rw [Nat.mul_comm s p, Nat.factorization_factorial_mul hp,
      Nat.factorization_factorial_eq_zero_of_lt hsp, Nat.zero_add]
  rw [Nat.factorization_mul hp.ne_zero hd, Finsupp.add_apply, hp.factorization_self,
    hbefore] at hfactor
  have he : e+1 ≤ s := by simpa [e, Nat.add_comm] using hfactor
  have hdiv := hpmul.trans (Nat.factorial_dvd_factorial hb)
  have hcount : σ 0 (p*d) ≤ σ 0 b.factorial := by
    simp only [ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card (Nat.divisors_subset_of_dvd (Nat.factorial_ne_zero _) hdiv)
  have count_for (j : ℕ) : σ 0 (p^j*v) = (j+1)*(σ 0 v) := by
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcop.pow_left j),
      ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  have hdcount : σ 0 d = (e+1)*(σ 0 v) := hdet ▸ count_for e
  have hpd : p^(e+1) * v = p*d := by rw [pow_succ, ← hdet]; ac_rfl
  have hpdcount : σ 0 (p*d) = (e+1+1)*(σ 0 v) := hpd ▸ count_for (e+1)
  change (s+1)*(σ 0 d) ≤ _
  calc
    (s+1)*(σ 0 d) = ((s+1)*(e+1))*(σ 0 v) := by rw [hdcount, Nat.mul_assoc]
    _ ≤ (s*(e+1+1))*(σ 0 v) := by
      apply Nat.mul_le_mul_right
      rw [Nat.add_one_mul, Nat.mul_add_one s (e+1)]
      omega
    _ = s*(σ 0 (p*d)) := by rw [hpdcount, Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_left s hcount

lemma block_amplification (D : ℕ → ℕ) (monoD : Monotone D) (n b r t : ℕ)
    (step : ∀ i < t, (r + 1) * D (n + i * b) ≤ r * D (n + (i + 1) * b)) :
    (r + t) * D n ≤ r * D (n + t * b) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h := ih (fun i hi => step i (by omega))
    have h' := step t (by omega)
    have hmono : D n ≤ D (n + t * b) := monoD (Nat.le_add_right _ _)
    rw [Nat.add_mul, Nat.one_mul] at h'
    calc
      (r + (t + 1)) * D n = (r + t) * D n + D n := by
        rw [← Nat.add_assoc, Nat.add_one_mul]
      _ ≤ r * D (n + t * b) + D (n + t * b) := Nat.add_le_add h hmono
      _ ≤ _ := h'

theorem main : H1 → H2 → type_of% @Erdos420.erdos_420.parts.i := by
  rintro ⟨A, hA⟩ hgain
  filter_upwards [polylog_packing A] with C hC
  apply tendsto_atTop.2
  intro y
  obtain ⟨K, hK⟩ := exists_nat_ge y
  obtain ⟨N, hN⟩ := eventually_atTop.1 hA
  filter_upwards [hC K, eventually_ge_atTop N] with n hn hnN
  obtain ⟨b, hb, hfit, hsmall⟩ := hn
  let D : ℕ → ℕ := fun x => σ 0 x.factorial
  have hmono : Monotone D := by
    intro x z hxz
    dsimp [D]
    simp only [ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card (Nat.divisors_subset_of_dvd (Nat.factorial_ne_zero _)
      (Nat.factorial_dvd_factorial hxz))
  have hstep (i : ℕ) (hi : i < K * b) :
      (b + 1) * D (n + i*b) ≤ b * D (n + (i+1)*b) := by
    let x := n + i*b
    have hnx : n ≤ x := Nat.le_add_right _ _
    have hxb : x ≤ n + K*b*b := Nat.add_le_add_left (Nat.mul_le_mul_right b hi.le) n
    have hlen := hsmall x hnx hxb
    obtain ⟨p, s, hp, hs, hsp, hsr, hlow, hhigh⟩ := hN x (hnN.trans hnx)
    have hend : x + b = n + (i+1)*b := by dsimp [x]; rw [Nat.add_one_mul, Nat.add_assoc]
    have h := hgain x (n+(i+1)*b) p s hp hs hsp hlow
      (hend ▸ hhigh.trans (Nat.add_le_add_left hlen x))
    change (s+1) * D x ≤ s * D (n+(i+1)*b) at h
    have hxy : D x ≤ D (n+(i+1)*b) := hmono (hend ▸ Nat.le_add_right x b)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (hsr.trans hlen)
    calc
      (b+1) * D x = (s+1) * D x + d * D x := by rw [← Nat.add_mul]; congr 1; omega
      _ ≤ s * D (n+(i+1)*b) + d * D (n+(i+1)*b) :=
        Nat.add_le_add h (Nat.mul_le_mul_left d hxy)
      _ = b * D (n+(i+1)*b) := by rw [← Nat.add_mul, ← hd]
  have ham := block_amplification D hmono n b b (K*b) hstep
  have hm : b * (K * D n) ≤ b * D (n + K*b*b) := by
    calc
      b * (K * D n) = (K*b) * D n := by ac_rfl
      _ ≤ (b + K*b) * D n := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
      _ ≤ _ := ham
  have hnat : K * D n ≤ D (n + ⌊(Real.log n)^C⌋₊) :=
    (Nat.le_of_mul_le_mul_left hm hb).trans (hmono (Nat.add_le_add_left hfit n))
  have hpos : (0 : ℝ) < (D n : ℝ) := by
    exact_mod_cast ArithmeticFunction.sigma_pos 0 _ (Nat.factorial_ne_zero n)
  apply hK.trans
  change (K : ℝ) ≤ (D (n + ⌊(Real.log n)^C⌋₊) : ℝ) / (D n : ℝ)
  apply (le_div_iff₀ hpos).2
  exact_mod_cast hnat

-- Only the uniform prime-multiple assertion remains.
lemma of_prime_multiples (h : H1) : type_of% @Erdos420.erdos_420.parts.i :=
  main h prime_gain_proof

end OMA.R_Erdos420_erdos_420_parts_i_R1
