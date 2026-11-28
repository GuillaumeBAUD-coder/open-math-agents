import FormalConjectures.ErdosProblems.«542»

-- Problem: Erdős Problem 542 — chen
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/542.lean:118 (declaration Erdos542.erdos_542.variants.chen)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Weighted packing. The multiples `≤ n` of distinct elements of `A` are disjoint (their lcm
exceeds `n`). Give `m ≤ n` the weight `G(⌊4n/m⌋)/m`, where `G = Σ e_d · 1[d ≤ ·] ≥ 0` is a step
function (boundaries `d` with integer jumps `e_d`, positive ones in `Bp`, negative ones in `Bn`),
found by a linear program. The multiples of `a` carry total weight `c(⌊4n/a⌋)/a` and all `m ≤ n`
carry `c(4n)`, where `c(M) = Σ e_d · H(⌊M/d⌋)`. We show `c(M) ≥ 10^6` for all `M ≥ 4` (an
incremental exact check for `M ≤ 3400`, Euler–Mascheroni bounds beyond) and
`c(4n) < 10^6 · (1/3+1/4+1/5+1/7+1/11)` for `n > 172509`; the main term `-Σ e_d log d` is
bounded through `log(1+1/t) = 2 artanh (1/(2t+1))`.
-/

open Finset Real

namespace OMA542

def Gs (j : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | p :: L => (if p.1 ≤ j then p.2 else 0) + Gs j L

noncomputable def cs (M : ℕ) : List (ℕ × ℕ) → ℝ
  | [] => 0
  | p :: L => (p.2 : ℝ) * (harmonic (M / p.1) : ℝ) + cs M L

/-- Multiples of `a` in `[1, n]`. -/
def mult (n a : ℕ) : Finset ℕ := (Icc 1 n).filter (a ∣ ·)

lemma mult_eq (n a : ℕ) (ha : 0 < a) : mult n a = (Icc 1 (n / a)).image (a * ·) := by
  ext m
  simp only [mult, mem_filter, mem_Icc, mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, k, rfl⟩
    refine ⟨k, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos k with h | h
      · subst h; simp at h1
      · exact h
    · rw [Nat.le_div_iff_mul_le ha]; linarith [mul_comm a k]
  · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
    rw [Nat.le_div_iff_mul_le ha] at h2
    refine ⟨⟨?_, by linarith [mul_comm a k]⟩, dvd_mul_right a k⟩
    exact Nat.mul_pos ha h1

lemma single_sum (n a d : ℕ) (ha : 0 < a) (hd : 4 ≤ d) :
    ∑ m ∈ mult n a, (if d ≤ 4 * n / m then (1 : ℝ) else 0) / m =
      (harmonic (4 * n / a / d) : ℝ) / a := by
  rw [mult_eq n a ha, sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left ha h)]
  have hd0 : 0 < d := by omega
  have key : ∀ k ∈ Icc 1 (n / a),
      (if d ≤ 4 * n / (a * k) then (1 : ℝ) else 0) / ((a * k : ℕ) : ℝ) =
        if k ∈ Icc 1 (4 * n / a / d) then (1 / (a : ℝ)) * (k : ℝ)⁻¹ else 0 := by
    intro k hk
    rw [mem_Icc] at hk
    have hk0 : 0 < k := hk.1
    have iff : d ≤ 4 * n / (a * k) ↔ k ≤ 4 * n / a / d := by
      rw [Nat.le_div_iff_mul_le (Nat.mul_pos ha hk0), Nat.le_div_iff_mul_le hd0,
        Nat.le_div_iff_mul_le ha]
      constructor <;> intro h <;> nlinarith [mul_comm a k, mul_assoc d a k, mul_comm (k * d) a]
    by_cases h : d ≤ 4 * n / (a * k)
    · have h' := iff.mp h
      rw [if_pos h, if_pos (mem_Icc.mpr ⟨hk0, h'⟩)]
      push_cast
      field_simp
    · have h' : ¬ k ≤ 4 * n / a / d := fun h' => h (iff.mpr h')
      rw [if_neg h, if_neg (fun hm => h' (mem_Icc.mp hm).2)]
      simp
  rw [sum_congr rfl key, ← sum_filter]
  have hsub : (Icc 1 (n / a)).filter (fun k => k ∈ Icc 1 (4 * n / a / d)) =
      Icc 1 (4 * n / a / d) := by
    rw [filter_mem_eq_inter, inter_eq_right]
    apply Icc_subset_Icc le_rfl
    calc 4 * n / a / d ≤ 4 * n / a / 4 := Nat.div_le_div_left hd (by norm_num)
      _ = n / a := by rw [Nat.div_div_eq_div_mul, mul_comm a 4,
            Nat.mul_div_mul_left _ _ (by norm_num : 0 < 4)]
  rw [hsub, ← mul_sum, harmonic_eq_sum_Icc]
  push_cast
  ring

lemma list_sum (n a : ℕ) (ha : 0 < a) : ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 4 ≤ p.1) →
    ∑ m ∈ mult n a, (Gs (4 * n / m) L : ℝ) / m = cs (4 * n / a) L / a
  | [], _ => by simp [Gs, cs]
  | p :: L, hL => by
    have h1 := single_sum n a p.1 ha (hL p (by simp))
    have h2 := list_sum n a ha L (fun q hq => hL q (by simp [hq]))
    have e : ∀ m, (Gs (4 * n / m) (p :: L) : ℝ) / m =
        (p.2 : ℝ) * ((if p.1 ≤ 4 * n / m then (1 : ℝ) else 0) / m) + (Gs (4 * n / m) L : ℝ) / m := by
      intro m
      simp only [Gs]
      split_ifs <;> push_cast <;> ring
    simp only [e, sum_add_distrib, ← mul_sum, h1, h2, cs]
    ring

/-- Packing: the multiple sets of distinct elements are disjoint. -/
lemma packing (n : ℕ) (A : Finset ℕ) (hA : Erdos542.IsLcmFree n A) (w : ℕ → ℝ)
    (hw : ∀ m, 0 ≤ w m) : ∑ a ∈ A, ∑ m ∈ mult n a, w m ≤ ∑ m ∈ Icc 1 n, w m := by
  rw [← sum_biUnion]
  · apply sum_le_sum_of_subset_of_nonneg
    · intro m hm
      simp only [mem_biUnion, mult, mem_filter] at hm
      obtain ⟨_, _, h, _⟩ := hm
      exact h
    · intro m _ _; exact hw m
  · intro a ha b hb hab
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro m hma hmb
    simp only [mult, mem_filter, mem_Icc] at hma hmb
    have hl : Nat.lcm a b ∣ m := Nat.lcm_dvd hma.2 hmb.2
    have := Nat.le_of_dvd (by omega) hl
    have := hA.2 ha hb hab
    omega

def Bp : List (ℕ × ℕ) := [(4, 1000000), (5, 57143), (18, 67211), (24, 101225), (27, 32109), (40, 46381), (42, 8164), (48, 15622), (50, 5714), (60, 30673), (63, 13761), (66, 5195), (84, 3362), (88, 18515), (90, 3175), (112, 11738), (114, 3008), (140, 6193), (144, 3319), (232, 2237), (280, 1438), (282, 1216)]
def Bn : List (ℕ × ℕ) := [(6, 57143), (8, 403672), (9, 96328), (10, 28571), (12, 304762), (15, 19047), (16, 48164), (20, 166667), (25, 11429), (28, 121905), (44, 54545), (52, 21336), (65, 4396), (68, 45233), (85, 3362), (92, 21690), (115, 2485), (116, 12261), (145, 1971), (148, 7541), (235, 1216), (236, 1021), (284, 2654)]

/-- Floor increment: sum over `(d, a)` with `d ∣ m` of `⌊a d K / m⌋`. -/
def incF (K m : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | p :: L => (if m % p.1 = 0 then p.2 * p.1 * K / m else 0) + incF K m L

/-- Ceiling increment. -/
def incC (K m : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | p :: L => (if m % p.1 = 0 then (p.2 * p.1 * K + m - 1) / m else 0) + incC K m L

def loop (K T : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => true
  | f + 1, m, P, Q =>
    (Nat.blt (m + 1) 4 || Nat.ble (Q + incC K (m + 1) Bn + T) (P + incF K (m + 1) Bp)) &&
      loop K T f (m + 1) (P + incF K (m + 1) Bp) (Q + incC K (m + 1) Bn)


noncomputable def incR (m : ℕ) : List (ℕ × ℕ) → ℝ
  | [] => 0
  | p :: L => (if m % p.1 = 0 then (p.2 : ℝ) * p.1 / m else 0) + incR m L

lemma harm_step (M d : ℕ) (hd : 0 < d) :
    (harmonic ((M + 1) / d) : ℝ) =
      harmonic (M / d) + if (M + 1) % d = 0 then (d : ℝ) / ((M + 1 : ℕ) : ℝ) else 0 := by
  by_cases h : d ∣ M + 1
  · have h0 : (M + 1) % d = 0 := Nat.mod_eq_zero_of_dvd h
    have e : (M + 1) / d = M / d + 1 := by rw [Nat.succ_div, if_pos h]
    rw [if_pos h0, e, harmonic_succ]
    push_cast
    congr 1
    have e2 : ((M / d : ℕ) : ℝ) + 1 = ((M + 1 : ℕ) : ℝ) / d := by
      rw [← Nat.cast_div h (by positivity), e]; push_cast; ring
    rw [e2]
    have : (0 : ℝ) < d := by exact_mod_cast hd
    field_simp
    push_cast
    ring
  · have e : (M + 1) / d = M / d := by rw [Nat.succ_div, if_neg h]; rfl
    rw [if_neg (fun h0 => h (Nat.dvd_of_mod_eq_zero h0)), e]
    simp

lemma cs_step (M : ℕ) : ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1) →
    cs (M + 1) L = cs M L + incR (M + 1) L
  | [], _ => by simp [cs, incR]
  | p :: L, hL => by
    have h1 := harm_step M p.1 (hL p (by simp))
    have h2 := cs_step M L (fun q hq => hL q (by simp [hq]))
    simp only [cs, incR, h1, h2]
    split_ifs <;> ring

lemma cs_zero : ∀ L : List (ℕ × ℕ), cs 0 L = 0
  | [] => rfl
  | p :: L => by simp [cs, cs_zero L]

lemma incF_le (K m : ℕ) : ∀ L : List (ℕ × ℕ), (incF K m L : ℝ) ≤ K * incR m L
  | [] => by simp [incF, incR]
  | p :: L => by
    have h := incF_le K m L
    simp only [incF, incR]
    push_cast
    rw [mul_add]
    apply add_le_add _ h
    split_ifs
    · calc ((p.2 * p.1 * K / m : ℕ) : ℝ) ≤ ((p.2 * p.1 * K : ℕ) : ℝ) / m := Nat.cast_div_le
        _ = K * ((p.2 : ℝ) * p.1 / m) := by push_cast; ring
    · simp

lemma ceil_ge (x m : ℕ) (hm : 0 < m) : (x : ℝ) / m ≤ (((x + m - 1) / m : ℕ) : ℝ) := by
  have h1 := Nat.div_add_mod (x + m - 1) m
  have h2 := Nat.mod_lt (x + m - 1) hm
  have h3 : x ≤ (x + m - 1) / m * m := by
    generalize (x + m - 1) / m = q at h1 h2 ⊢
    generalize (x + m - 1) % m = r at h1 h2
    rw [mul_comm] at h1
    omega
  rw [div_le_iff₀ (by exact_mod_cast hm)]
  exact_mod_cast h3

lemma incC_ge (K m : ℕ) (hm : 0 < m) : ∀ L : List (ℕ × ℕ), K * incR m L ≤ (incC K m L : ℝ)
  | [] => by simp [incC, incR]
  | p :: L => by
    have h := incC_ge K m hm L
    simp only [incC, incR]
    push_cast
    rw [mul_add]
    apply add_le_add _ h
    split_ifs
    · calc (K : ℝ) * ((p.2 : ℝ) * p.1 / m) = ((p.2 * p.1 * K : ℕ) : ℝ) / m := by push_cast; ring
        _ ≤ _ := ceil_ge _ m hm
    · simp

def Pf (K : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => Pf K m + incF K (m + 1) Bp

def Qf (K : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => Qf K m + incC K (m + 1) Bn

lemma Bp_pos : ∀ p ∈ Bp, 4 ≤ p.1 := by decide
lemma Bn_pos : ∀ p ∈ Bn, 4 ≤ p.1 := by decide

lemma Pf_le (K : ℕ) : ∀ M, (Pf K M : ℝ) ≤ K * cs M Bp
  | 0 => by simp [Pf, cs_zero]
  | M + 1 => by
    have h := Pf_le K M
    rw [cs_step M Bp (fun p hp => by have := Bp_pos p hp; omega)]
    simp only [Pf]
    push_cast
    have := incF_le K (M + 1) Bp
    linarith

lemma Qf_ge (K : ℕ) : ∀ M, K * cs M Bn ≤ (Qf K M : ℝ)
  | 0 => by simp [Qf, cs_zero]
  | M + 1 => by
    have h := Qf_ge K M
    rw [cs_step M Bn (fun p hp => by have := Bn_pos p hp; omega)]
    simp only [Qf]
    push_cast
    have := incC_ge K (M + 1) (by omega) Bn
    linarith

lemma loop_spec (K T : ℕ) : ∀ f m, loop K T f m (Pf K m) (Qf K m) = true →
    ∀ j, m < j → j ≤ m + f → 4 ≤ j → Qf K j + T ≤ Pf K j
  | 0, m, _, j, h1, h2, _ => by omega
  | f + 1, m, h, j, h1, h2, h4 => by
    simp only [loop, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq] at h
    obtain ⟨hc, hr⟩ := h
    have e1 : Pf K m + incF K (m + 1) Bp = Pf K (m + 1) := rfl
    have e2 : Qf K m + incC K (m + 1) Bn = Qf K (m + 1) := rfl
    rw [e1, e2] at hr hc
    rcases Nat.lt_or_ge (m + 1) j with hj | hj
    · exact loop_spec K T f (m + 1) hr j hj (by omega) h4
    · have : j = m + 1 := by omega
      subst this
      rcases hc with hc | hc
      · omega
      · exact hc

set_option maxRecDepth 100000 in
theorem loop_ok : loop (10 ^ 9) (10 ^ 15) 3400 0 0 0 = true := by decide +kernel

lemma c_fin (M : ℕ) (h4 : 4 ≤ M) (hM : M ≤ 3400) : (10 ^ 6 : ℝ) ≤ cs M Bp - cs M Bn := by
  have h := loop_spec (10 ^ 9) (10 ^ 15) 3400 0 loop_ok M (by omega) (by omega) h4
  have h1 := Pf_le (10 ^ 9) M
  have h2 := Qf_ge (10 ^ 9) M
  have h3 : ((Qf (10 ^ 9) M : ℕ) : ℝ) + 10 ^ 15 ≤ (Pf (10 ^ 9) M : ℝ) := by exact_mod_cast h
  norm_num at h1 h2 h3
  linarith

lemma harm_bounds (x : ℕ) (hx : 1 ≤ x) :
    eulerMascheroniConstant + log x ≤ harmonic x ∧
      (harmonic x : ℝ) ≤ eulerMascheroniConstant + log (x + 1) := by
  have h1 := eulerMascheroniConstant_lt_eulerMascheroniSeq' x
  have h2 := eulerMascheroniSeq_lt_eulerMascheroniConstant x
  rw [eulerMascheroniSeq', if_neg (by omega)] at h1
  rw [eulerMascheroniSeq] at h2
  constructor <;> linarith

lemma hd_bounds (M d : ℕ) (hd : 0 < d) (hM : d < M) :
    |(harmonic (M / d) : ℝ) - (eulerMascheroniConstant + log M - log d)| ≤ (d : ℝ) / (M - d) := by
  have hx : 1 ≤ M / d := Nat.div_pos hM.le hd
  obtain ⟨hl, hu⟩ := harm_bounds (M / d) hx
  have e1 := Nat.div_add_mod M d
  have e2 := Nat.mod_lt M hd
  set x := M / d
  set r := M % d
  have hxr : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hMd : (d : ℝ) < M := by exact_mod_cast hM
  have hMeq : (M : ℝ) = d * x + r := by exact_mod_cast e1.symm
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hrd : (r : ℝ) < d := by exact_mod_cast e2
  have hMd' : (0 : ℝ) < M - d := by linarith
  have hM0 : (0 : ℝ) < M := by linarith
  rw [abs_le]
  constructor
  · -- lower: log x ≥ log ((M - d) / d)
    have h1 : log (((M : ℝ) - d) / d) ≤ log x := by
      apply log_le_log (div_pos hMd' hdr)
      rw [div_le_iff₀ hdr]; nlinarith
    rw [log_div (ne_of_gt hMd') (ne_of_gt hdr)] at h1
    have h2 : log (M : ℝ) - log ((M : ℝ) - d) ≤ d / (M - d) := by
      rw [← log_div (ne_of_gt hM0) (ne_of_gt hMd')]
      have := log_le_sub_one_of_pos (div_pos hM0 hMd')
      have e : (M : ℝ) / (M - d) - 1 = d / (M - d) := by field_simp; ring
      linarith
    linarith
  · have h1 : log ((x : ℝ) + 1) ≤ log (((M : ℝ) + d) / d) := by
      apply log_le_log (by positivity)
      rw [le_div_iff₀ hdr]; nlinarith
    rw [log_div (by positivity) (ne_of_gt hdr)] at h1
    have h2 : log ((M : ℝ) + d) - log M ≤ d / (M - d) := by
      rw [← log_div (by positivity) (ne_of_gt hM0)]
      have := log_le_sub_one_of_pos (show (0 : ℝ) < (M + d) / M by positivity)
      have e : ((M : ℝ) + d) / M - 1 = d / M := by field_simp; ring
      have e3 : (d : ℝ) / M ≤ d / (M - d) := div_le_div_of_nonneg_left hdr.le hMd' (by linarith)
      linarith
    linarith

lemma log_series (t : ℕ) (ht : 1 ≤ t) :
    2 / (2 * (t : ℝ) + 1) + 2 / (3 * (2 * (t : ℝ) + 1) ^ 3) ≤ log ((t : ℝ) + 1) - log t ∧
      log ((t : ℝ) + 1) - log t ≤
        2 / (2 * (t : ℝ) + 1) + 1 / (6 * (t : ℝ) * ((t : ℝ) + 1) * (2 * (t : ℝ) + 1)) := by
  have htr : (1 : ℝ) ≤ t := by exact_mod_cast ht
  set z : ℝ := 1 / (2 * (t : ℝ) + 1) with hz
  have hz0 : 0 < z := by positivity
  have hz1 : z < 1 := by rw [hz, div_lt_one (by linarith)]; linarith
  have habs : |z| < 1 := by rw [abs_of_pos hz0]; exact hz1
  have hf := hasSum_log_sub_log_of_abs_lt_one habs
  have elog : log (1 + z) - log (1 - z) = log ((t : ℝ) + 1) - log t := by
    have e1 : 1 + z = 2 * ((t : ℝ) + 1) / (2 * t + 1) := by rw [hz]; field_simp; ring
    have e2 : 1 - z = 2 * (t : ℝ) / (2 * t + 1) := by rw [hz]; field_simp; ring
    rw [e1, e2, log_div (by positivity) (by positivity), log_div (by positivity) (by positivity),
      log_mul (by norm_num) (by positivity), log_mul (by norm_num) (by positivity)]
    ring
  rw [elog] at hf
  constructor
  · have := sum_le_hasSum (range 2) (fun i _ => by positivity) hf
    simp only [sum_range_succ, sum_range_zero] at this
    have e : 2 / (2 * (t : ℝ) + 1) + 2 / (3 * (2 * (t : ℝ) + 1) ^ 3) =
        0 + 2 * (1 / (2 * ((0 : ℕ) : ℝ) + 1)) * z ^ (2 * 0 + 1) +
          2 * (1 / (2 * ((1 : ℕ) : ℝ) + 1)) * z ^ (2 * 1 + 1) := by
      rw [hz]; push_cast; field_simp; ring
    rw [e]; exact this
  · have hg : HasSum (fun k : ℕ => (2 * z / 3) * (z ^ 2) ^ k + if k = 0 then 4 * z / 3 else 0)
        ((2 * z / 3) * (1 - z ^ 2)⁻¹ + 4 * z / 3) := by
      apply HasSum.add
      · exact (hasSum_geometric_of_lt_one (by positivity) (by nlinarith)).mul_left _
      · exact hasSum_ite_eq 0 _
    have hle := hasSum_le (fun k => ?_) hf hg
    · have e : (2 * z / 3) * (1 - z ^ 2)⁻¹ + 4 * z / 3 =
          2 / (2 * (t : ℝ) + 1) + 1 / (6 * (t : ℝ) * ((t : ℝ) + 1) * (2 * (t : ℝ) + 1)) := by
        have : (1 : ℝ) - z ^ 2 = 4 * t * (t + 1) / (2 * t + 1) ^ 2 := by rw [hz]; field_simp; ring
        rw [this, hz]; field_simp; ring
      rw [← e]; exact hle
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp; linarith
      · rw [if_neg (by omega), add_zero, pow_succ, ← pow_mul]
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
        have hp : 0 < z ^ (2 * k) := by positivity
        have : 2 * (1 / (2 * (k : ℝ) + 1)) ≤ 2 / 3 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        calc 2 * (1 / (2 * (k : ℝ) + 1)) * (z ^ (2 * k) * z) ≤ 2 / 3 * (z ^ (2 * k) * z) := by
              apply mul_le_mul_of_nonneg_right this; positivity
          _ = 2 * z / 3 * z ^ (2 * k) := by ring

noncomputable def Ls : List (ℕ × ℕ) → ℝ
  | [] => 0
  | p :: L => (p.2 : ℝ) * log p.1 + Ls L

def tot : List (ℕ × ℕ) → ℕ
  | [] => 0
  | p :: L => p.2 + tot L

def Es : List (ℕ × ℕ) → ℕ
  | [] => 0
  | p :: L => p.2 * p.1 + Es L

lemma cs_bounds (M dm : ℕ) (hM : dm < M) : ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1 ∧ p.1 ≤ dm) →
    |cs M L - ((tot L : ℝ) * (eulerMascheroniConstant + log M) - Ls L)| ≤
      (Es L : ℝ) / (M - dm)
  | [], _ => by simp [cs, tot, Ls, Es]
  | p :: L, hL => by
    have ih := cs_bounds M dm hM L (fun q hq => hL q (by simp [hq]))
    obtain ⟨h0, h1⟩ := hL p (by simp)
    have hb := hd_bounds M p.1 h0 (by omega)
    have hdr : (0 : ℝ) < p.1 := by exact_mod_cast h0
    have hmd : (0 : ℝ) < (M : ℝ) - dm := by
      have : (dm : ℝ) < M := by exact_mod_cast hM
      linarith
    have hle : (p.1 : ℝ) / (M - p.1) ≤ p.1 / (M - dm) := by
      apply div_le_div_of_nonneg_left hdr.le hmd
      have : (p.1 : ℝ) ≤ dm := by exact_mod_cast h1
      linarith
    have ha : (0 : ℝ) ≤ p.2 := by positivity
    have key : |(p.2 : ℝ) * harmonic (M / p.1) -
        p.2 * (eulerMascheroniConstant + log M - log p.1)| ≤ p.2 * (p.1 / (M - dm)) := by
      rw [← mul_sub, abs_mul, abs_of_nonneg ha]
      exact mul_le_mul_of_nonneg_left (hb.trans hle) ha
    simp only [cs, tot, Ls, Es]
    push_cast
    calc _ = |((p.2 : ℝ) * harmonic (M / p.1) - p.2 * (eulerMascheroniConstant + log M - log p.1)) +
          (cs M L - ((tot L : ℝ) * (eulerMascheroniConstant + log M) - Ls L))| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ p.2 * (p.1 / (M - dm)) + (Es L : ℝ) / (M - dm) := add_le_add key ih
      _ = _ := by field_simp

lemma tele (d : ℕ) : ∀ T, d ≤ T →
    ∑ t ∈ range T, (if d ≤ t then (1 : ℝ) else 0) * (log ((t : ℝ) + 1) - log t) = log T - log d
  | 0, h => by
    have : d = 0 := by omega
    subst this; simp
  | T + 1, h => by
    rw [sum_range_succ]
    rcases Nat.lt_or_ge T d with hT | hT
    · have : d = T + 1 := by omega
      subst this
      rw [sum_eq_zero (fun t ht => by rw [mem_range] at ht; rw [if_neg (by omega)]; ring)]
      rw [if_neg (by omega)]; simp
    · rw [tele d T hT, if_pos hT]; push_cast; ring

lemma abel (T : ℕ) : ∀ L : List (ℕ × ℕ), (∀ p ∈ L, p.1 ≤ T) →
    ∑ t ∈ range T, (Gs t L : ℝ) * (log ((t : ℝ) + 1) - log t) = tot L * log T - Ls L
  | [], _ => by simp [Gs, tot, Ls]
  | p :: L, hL => by
    have ih := abel T L (fun q hq => hL q (by simp [hq]))
    have ht := tele p.1 T (hL p (by simp))
    have e : ∀ t, (Gs t (p :: L) : ℝ) * (log ((t : ℝ) + 1) - log t) =
        p.2 * ((if p.1 ≤ t then (1 : ℝ) else 0) * (log ((t : ℝ) + 1) - log t)) +
          (Gs t L : ℝ) * (log ((t : ℝ) + 1) - log t) := by
      intro t; simp only [Gs]; split_ifs <;> push_cast <;> ring
    simp only [e, sum_add_distrib, ← mul_sum, ht, ih, tot, Ls]
    push_cast; ring

/-- Lower and upper scaled values for `log (1 + 1/t)`. -/
def lo (t : ℕ) : ℕ := 2 * 10 ^ 9 / (2 * t + 1) + 2 * 10 ^ 9 / (3 * (2 * t + 1) ^ 3)

/-- Upper scaled value for `log (1 + 1/t)`. -/
def up (t : ℕ) : ℕ := (2 * 10 ^ 9 + (2 * t + 1) - 1) / (2 * t + 1) +
  (10 ^ 9 + 6 * t * (t + 1) * (2 * t + 1) - 1) / (6 * t * (t + 1) * (2 * t + 1))

lemma lo_le (t : ℕ) (ht : 1 ≤ t) : (lo t : ℝ) ≤ 10 ^ 9 * (log ((t : ℝ) + 1) - log t) := by
  have h := (log_series t ht).1
  have a1 : ((2 * 10 ^ 9 / (2 * t + 1) : ℕ) : ℝ) ≤ ((2 * 10 ^ 9 : ℕ) : ℝ) / ((2 * t + 1 : ℕ) : ℝ) :=
    Nat.cast_div_le
  have a2 : ((2 * 10 ^ 9 / (3 * (2 * t + 1) ^ 3) : ℕ) : ℝ) ≤
      ((2 * 10 ^ 9 : ℕ) : ℝ) / ((3 * (2 * t + 1) ^ 3 : ℕ) : ℝ) := Nat.cast_div_le
  simp only [lo]; push_cast at a1 a2 ⊢
  have e : (2 * 10 ^ 9 : ℝ) / (2 * t + 1) + 2 * 10 ^ 9 / (3 * (2 * t + 1) ^ 3) =
      10 ^ 9 * (2 / (2 * (t : ℝ) + 1) + 2 / (3 * (2 * (t : ℝ) + 1) ^ 3)) := by ring
  nlinarith

lemma up_ge (t : ℕ) (ht : 1 ≤ t) : 10 ^ 9 * (log ((t : ℝ) + 1) - log t) ≤ (up t : ℝ) := by
  have h := (log_series t ht).2
  have a1 := ceil_ge (2 * 10 ^ 9) (2 * t + 1) (by omega)
  have a2 := ceil_ge (10 ^ 9) (6 * t * (t + 1) * (2 * t + 1)) (by positivity)
  simp only [up]
  rw [Nat.cast_add]
  have e : (10 ^ 9 : ℝ) * (2 / (2 * (t : ℝ) + 1) +
      1 / (6 * (t : ℝ) * ((t : ℝ) + 1) * (2 * (t : ℝ) + 1))) =
      ((2 * 10 ^ 9 : ℕ) : ℝ) / ((2 * t + 1 : ℕ) : ℝ) +
        ((10 ^ 9 : ℕ) : ℝ) / ((6 * t * (t + 1) * (2 * t + 1) : ℕ) : ℝ) := by
    push_cast; ring
  nlinarith

def sumTo (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | T + 1 => sumTo f T + f T

lemma sumTo_eq (f : ℕ → ℕ) : ∀ T, (sumTo f T : ℝ) = ∑ t ∈ range T, (f t : ℝ)
  | 0 => by simp [sumTo]
  | T + 1 => by rw [sum_range_succ, ← sumTo_eq f T]; simp [sumTo]

def Gd (t : ℕ) : ℕ := Gs t Bp - Gs t Bn

lemma tot_eq : tot Bp = tot Bn := by decide

lemma Gs_full (t : ℕ) : ∀ L : List (ℕ × ℕ), (∀ p ∈ L, p.1 ≤ t) → Gs t L = tot L
  | [], _ => rfl
  | p :: L, hL => by
    simp only [Gs, tot, if_pos (hL p (by simp)), Gs_full t L (fun q hq => hL q (by simp [hq]))]

lemma Bp_le : ∀ p ∈ Bp, p.1 ≤ 284 := by decide
lemma Bn_le : ∀ p ∈ Bn, p.1 ≤ 284 := by decide

lemma hG (t : ℕ) : Gs t Bn ≤ Gs t Bp := by
  rcases Nat.lt_or_ge t 285 with h | h
  · have : ∀ t < 285, Gs t Bn ≤ Gs t Bp := by
      set_option maxRecDepth 100000 in decide +kernel
    exact this t h
  · rw [Gs_full t Bp (fun p hp => by have := Bp_le p hp; omega),
      Gs_full t Bn (fun p hp => by have := Bn_le p hp; omega), tot_eq]

set_option maxRecDepth 100000 in
lemma sum_lo : sumTo (fun t => Gd t * lo t) 285 = 1016845802616882 := by decide +kernel
set_option maxRecDepth 100000 in
lemma sum_up : sumTo (fun t => Gd t * up t) 285 = 1016864927398347 := by decide +kernel
lemma Es_val : Es Bp + Es Bn = 51553697 := by decide

lemma Lam_eq : Ls Bn - Ls Bp =
    ∑ t ∈ range 285, (Gd t : ℝ) * (log ((t : ℝ) + 1) - log t) := by
  have h1 := abel 285 Bp (fun p hp => by have := Bp_le p hp; omega)
  have h2 := abel 285 Bn (fun p hp => by have := Bn_le p hp; omega)
  have e : ∀ t, (Gd t : ℝ) = (Gs t Bp : ℝ) - Gs t Bn := fun t => by
    rw [Gd, Nat.cast_sub (hG t)]
  simp only [e, sub_mul, sum_sub_distrib, h1, h2, tot_eq]
  ring

lemma Gd_zero : Gd 0 = 0 := by decide

lemma Lam_lo : (1016845802616882 : ℝ) / 10 ^ 9 ≤ Ls Bn - Ls Bp := by
  have e : (1016845802616882 : ℝ) = (sumTo (fun t => Gd t * lo t) 285 : ℕ) := by
    rw [sum_lo]; norm_num
  rw [Lam_eq, e, sumTo_eq, div_le_iff₀ (by norm_num), sum_mul]
  apply sum_le_sum
  intro t _
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [Gd_zero]
  · rw [Nat.cast_mul]
    have := lo_le t ht
    have h0 : (0 : ℝ) ≤ (Gd t : ℝ) := Nat.cast_nonneg _
    nlinarith

lemma Lam_up : Ls Bn - Ls Bp ≤ (1016864927398347 : ℝ) / 10 ^ 9 := by
  have e : (1016864927398347 : ℝ) = (sumTo (fun t => Gd t * up t) 285 : ℕ) := by
    rw [sum_up]; norm_num
  rw [Lam_eq, e, sumTo_eq, le_div_iff₀ (by norm_num), sum_mul]
  apply sum_le_sum
  intro t _
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [Gd_zero]
  · rw [Nat.cast_mul]
    have := up_ge t ht
    have h0 : (0 : ℝ) ≤ (Gd t : ℝ) := Nat.cast_nonneg _
    nlinarith

lemma c_near (M : ℕ) (hM : 284 < M) :
    |(cs M Bp - cs M Bn) - (Ls Bn - Ls Bp)| ≤ (51553697 : ℝ) / (M - 284) := by
  have h1 := cs_bounds M 284 hM Bp
    (fun p hp => by have := Bp_le p hp; have := Bp_pos p hp; omega)
  have h2 := cs_bounds M 284 hM Bn
    (fun p hp => by have := Bn_le p hp; have := Bn_pos p hp; omega)
  rw [tot_eq] at h1
  have e : (51553697 : ℝ) = Es Bp + Es Bn := by exact_mod_cast Es_val.symm
  rw [e, add_div]
  calc _ = |(cs M Bp - ((tot Bn : ℝ) * (eulerMascheroniConstant + log M) - Ls Bp)) -
        (cs M Bn - ((tot Bn : ℝ) * (eulerMascheroniConstant + log M) - Ls Bn))| := by ring_nf
    _ ≤ _ := abs_sub _ _
    _ ≤ _ := add_le_add h1 h2

lemma c_ge (M : ℕ) (h4 : 4 ≤ M) : (10 ^ 6 : ℝ) ≤ cs M Bp - cs M Bn := by
  rcases Nat.lt_or_ge M 3401 with h | h
  · exact c_fin M h4 (by omega)
  · have h1 := (abs_le.mp (c_near M (by omega))).1
    have h2 := Lam_lo
    have hMr : (3401 : ℝ) ≤ M := by exact_mod_cast h
    have h3 : (51553697 : ℝ) / (M - 284) ≤ 51553697 / (3401 - 284) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    norm_num at h2 h3 ⊢
    linarith

lemma c_top (N : ℕ) (hN : 690040 ≤ N) :
    cs N Bp - cs N Bn < 10 ^ 6 * (1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  have h1 := (abs_le.mp (c_near N (by omega))).2
  have h2 := Lam_up
  have hNr : (690040 : ℝ) ≤ N := by exact_mod_cast hN
  have h3 : (51553697 : ℝ) / (N - 284) ≤ 51553697 / (690040 - 284) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  norm_num at h2 h3 ⊢
  linarith

theorem main (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hA : Erdos542.IsLcmFree n A) :
    ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11 := by
  set w : ℕ → ℝ := fun m => ((Gs (4 * n / m) Bp : ℝ) - Gs (4 * n / m) Bn) / m with hw
  have hw0 : ∀ m, 0 ≤ w m := fun m => by
    simp only [hw]
    apply div_nonneg _ (Nat.cast_nonneg _)
    have := hG (4 * n / m)
    have : (Gs (4 * n / m) Bn : ℝ) ≤ Gs (4 * n / m) Bp := by exact_mod_cast this
    linarith
  have hmult : ∀ a, 0 < a →
      ∑ m ∈ mult n a, w m = (cs (4 * n / a) Bp - cs (4 * n / a) Bn) / a := by
    intro a ha
    simp only [hw, sub_div, sum_sub_distrib,
      list_sum n a ha Bp Bp_pos, list_sum n a ha Bn Bn_pos]
  have hpack := packing n A hA w hw0
  have htot : ∑ m ∈ Icc 1 n, w m = cs (4 * n) Bp - cs (4 * n) Bn := by
    have : mult n 1 = Icc 1 n := by
      simp only [mult]; exact filter_true_of_mem (fun _ _ => one_dvd _)
    rw [← this, hmult 1 one_pos]; simp
  have hlow : ∑ a ∈ A, (10 ^ 6 : ℝ) * (1 / a) ≤ ∑ a ∈ A, ∑ m ∈ mult n a, w m := by
    apply sum_le_sum
    intro a ha
    have ha' := mem_Icc.mp (hA.1 ha)
    rw [hmult a (by omega)]
    have h4 : 4 ≤ 4 * n / a := by
      rw [Nat.le_div_iff_mul_le (by omega)]; omega
    have := c_ge (4 * n / a) h4
    have hapos : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right this hapos.le
  have htop := c_top (4 * n) (by omega)
  rw [← mul_sum] at hlow
  linarith

end OMA542

theorem OMA.solution : type_of% @Erdos542.erdos_542.variants.chen := OMA542.main
