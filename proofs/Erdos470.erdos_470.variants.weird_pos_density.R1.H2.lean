import OMAReductions.R_Erdos470_erdos_470_variants_weird_pos_density_R1
import Mathlib.NumberTheory.Chebyshev


/-!
The pseudoperfect numbers have a natural density (Davenport 1933 / Erdos 1934 / Benkoski-Erdos 1974).

A block with no prime divisors separates a smooth part of the integer from its
remaining factors. When the smooth part is small enough and the reciprocal
sum of the remaining divisors is small, weirdness is decided by the smooth
part. The reciprocal divisor criterion follows Benkoski and Erdős, *On Weird
and Pseudoperfect Numbers* (1974). The Chinese remainder theorem gives a
uniform chance of finding such
a block. Iterating this estimate yields arbitrarily accurate periodic
approximations and hence a natural density.

For positivity, restrict to multiples of 70 whose multiplier has no
small prime factor. The reciprocal tail exceeds the stability threshold
for too few multipliers to account for the whole restriction.
-/

open Finset Filter
open scoped Topology

namespace PseudoperfectDensity

private theorem scale_proper {c m : ℕ} (hc : 0 < c) :
    ((c*m).properDivisors.filter (fun d => c ∣ d)) =
      m.properDivisors.image (fun d => c*d) := by
  ext d
  constructor
  · intro hd
    obtain ⟨hd, e, rfl⟩ := mem_filter.mp hd
    obtain ⟨hdiv, hlt⟩ := Nat.mem_properDivisors.mp hd
    obtain ⟨a, ha⟩ := hdiv
    refine mem_image.mpr ⟨e, Nat.mem_properDivisors.mpr ⟨⟨a, ?_⟩,
      Nat.lt_of_mul_lt_mul_left hlt⟩, rfl⟩
    apply Nat.eq_of_mul_eq_mul_left hc
    simpa only [mul_assoc] using ha
  · intro hd
    obtain ⟨e, he, rfl⟩ := mem_image.mp hd
    obtain ⟨hdiv, hlt⟩ := Nat.mem_properDivisors.mp he
    obtain ⟨a, rfl⟩ := hdiv
    exact mem_filter.mpr ⟨Nat.mem_properDivisors.mpr ⟨⟨a, by ring⟩,
      Nat.mul_lt_mul_of_pos_left hlt hc⟩, dvd_mul_right _ _⟩

private theorem split_proper_sum {c m : ℕ} (hc : 0 < c) {S : Finset ℕ}
    (hS : S ⊆ (c*m).properDivisors) :
    (∑ d ∈ S, d) =
      c * (∑ d ∈ m.properDivisors.filter (fun d => c*d ∈ S), d) +
        ∑ d ∈ S.filter (fun d => ¬ c ∣ d), d := by
  classical
  let R := m.properDivisors.filter (fun d => c*d ∈ S)
  have h : S.filter (fun d => c ∣ d) = R.image (fun d => c*d) := by
    ext d
    constructor
    · intro hd
      obtain ⟨hs, hcd⟩ := mem_filter.mp hd
      have hd := mem_filter.mpr ⟨hS hs, hcd⟩
      rw [scale_proper hc] at hd
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hd
      exact mem_image.mpr ⟨a, mem_filter.mpr ⟨ha, hs⟩, rfl⟩
    · intro hd
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hd
      exact mem_filter.mpr ⟨(mem_filter.mp ha).2, dvd_mul_right _ _⟩
  have hi : (R : Set ℕ).InjOn (fun d => c*d) := fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hc h
  rw [← sum_filter_add_sum_filter_not S (fun d => c ∣ d), h, sum_image hi, ← mul_sum]


private theorem pseudoperfect_stable {c m : ℕ} (hc : 0 < c) (hm : 0 < m)
    (hsmall : (∑ d ∈ (c*m).properDivisors.filter (fun d => ¬ c ∣ d), d) < c) :
    (c*m).Pseudoperfect ↔ m.Pseudoperfect := by
  classical
  have hi : Function.Injective (fun d => c*d) := fun _ _ h => Nat.eq_of_mul_eq_mul_left hc h
  have hp : (c*m).Pseudoperfect ↔ m.Pseudoperfect := by
    constructor
    · rintro ⟨_, S, hS, hsum⟩
      let T := m.properDivisors.filter (fun d => c*d ∈ S)
      let r := ∑ d ∈ S.filter (fun d => ¬c ∣ d), d
      have he : c * (∑ d ∈ T, d) + r = c*m := (split_proper_sum hc hS).symm.trans hsum
      have hd : c ∣ (c * (∑ d ∈ T, d) + r) := by rw [he]; exact dvd_mul_right _ _
      have hrd : c ∣ r := by
        simpa only [Nat.add_sub_cancel_left] using Nat.dvd_sub hd (dvd_mul_right c (∑ d ∈ T, d))
      have hrc : r < c := by
        apply lt_of_le_of_lt _ hsmall
        exact sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ hS) (fun _ _ _ => Nat.zero_le _)
      have hr0 : r = 0 := by
        by_contra h
        exact (Nat.le_of_dvd (Nat.pos_of_ne_zero h) hrd).not_gt hrc
      rw [hr0, add_zero] at he
      exact ⟨hm, T, filter_subset _ _, Nat.eq_of_mul_eq_mul_left hc he⟩
    · rintro ⟨_, T, hT, ht⟩
      refine ⟨mul_pos hc hm, T.image (fun d => c*d), ?_, ?_⟩
      · intro d hd
        have hd' : d ∈ m.properDivisors.image (fun d => c*d) := image_subset_image hT hd
        rw [← scale_proper hc] at hd'
        exact (mem_filter.mp hd').1
      · rw [sum_image hi.injOn, ← mul_sum, ht]
  exact hp

private noncomputable def reciprocalTail (n Y : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => Y < d), 1/(d : ℝ)

private theorem pseudoperfect_of_small_tail {c m Y : ℕ} (hc : 0 < c) (hm : 0 < m)
    (hcut : ∀ d, d ∣ c*m → d ≤ Y → d ∣ m)
    (ht : reciprocalTail (c*m) Y < 1/(m : ℝ)) :
    (c*m).Pseudoperfect ↔ m.Pseudoperfect := by
  let n := c*m
  let A := n.properDivisors.filter (fun d => ¬ c ∣ d)
  have hn : 0 < n := mul_pos hc hm
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hd (d : ℕ) (hd : d ∈ A) : d ∣ n ∧ 0 < d ∧ ¬ c ∣ d := by
    obtain ⟨hd₁, hd₂⟩ := mem_filter.mp hd
    have hdd := (Nat.mem_properDivisors.mp hd₁).1
    exact ⟨hdd, Nat.pos_of_dvd_of_pos hdd hn, hd₂⟩
  let f (d : ℕ) := n/d
  have hf (d : ℕ) (h : d ∈ A) : n = d * f d := by
    exact (Nat.mul_div_cancel' (hd d h).1).symm
  have hfd (d : ℕ) (h : d ∈ A) : f d ∣ n := ⟨d, by rw [hf d h, mul_comm]⟩
  have hpos (d : ℕ) (h : d ∈ A) : 0 < f d := Nat.pos_of_dvd_of_pos (hfd d h) hn
  have hinj : (A : Set ℕ).InjOn f := by
    intro a ha b hb he
    apply Nat.eq_of_mul_eq_mul_right (hpos b hb)
    rw [← he, ← hf a ha, he, ← hf b hb]
  have hsub : A.image f ⊆ n.divisors.filter (fun d => Y < d) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
    refine mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hfd b hb, hn.ne'⟩, ?_⟩
    by_contra! hY
    obtain ⟨e, he⟩ := hcut (f b) (hfd b hb) hY
    apply (hd b hb).2.2
    refine ⟨e, Nat.eq_of_mul_eq_mul_right (hpos b hb) ?_⟩
    calc
      b * f b = n := (hf b hb).symm
      _ = c * (f b * e) := congrArg (c * ·) he
      _ = (c * e) * f b := by ring
  have hsum : ((∑ d ∈ A, d : ℕ) : ℝ) / n ≤ reciprocalTail n Y := by
    rw [Nat.cast_sum, sum_div]
    calc
      _ = ∑ d ∈ A, (1 : ℝ)/(f d : ℝ) := by
        apply sum_congr rfl
        intro d hda
        have hf' : (n : ℝ) = d * (f d : ℝ) := by exact_mod_cast hf d hda
        rw [hf']
        have hdp : (d : ℝ) ≠ 0 := by exact_mod_cast (hd d hda).2.1.ne'
        field_simp
      _ = ∑ e ∈ A.image f, (1 : ℝ)/(e : ℝ) := (sum_image (f := fun e : ℕ => (1 : ℝ)/(e : ℝ)) hinj).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  apply pseudoperfect_stable hc hm
  have hh := hsum.trans_lt ht
  have he : (1 : ℝ)/(m : ℝ) * n = (c : ℝ) := by
    dsimp [n]
    push_cast
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  rw [div_lt_iff₀ hnr, he] at hh
  exact_mod_cast hh

private def Modular (m : ℕ) (f : ℕ → ℝ) := ∀ a b, a ≡ b [MOD m] → f a = f b

private noncomputable def mean (M : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ n ∈ range M, f n) / M

private noncomputable def flag (P : ℕ → Prop) (n : ℕ) : ℝ := by
  classical
  exact if P n then 1 else 0

private theorem flag_nonneg (P : ℕ → Prop) (n : ℕ) : 0 ≤ flag P n := by
  unfold flag
  split <;> norm_num

private theorem flag_le_one (P : ℕ → Prop) (n : ℕ) : flag P n ≤ 1 := by
  unfold flag
  split <;> norm_num

private theorem modular_flag {M : ℕ} {P : ℕ → Prop}
    (h : ∀ a b, a ≡ b [MOD M] → (P a ↔ P b)) : Modular M (flag P) := by
  classical
  intro a b hab
  unfold flag
  simp only [h a b hab]

private theorem mean_mono {f g : ℕ → ℝ} (M : ℕ) (h : ∀ n < M, f n ≤ g n) :
    mean M f ≤ mean M g :=
  div_le_div_of_nonneg_right (sum_le_sum fun n hn => h n (mem_range.mp hn)) (by positivity)

private theorem mean_add (M : ℕ) (f g : ℕ → ℝ) :
    mean M (fun n => f n + g n) = mean M f + mean M g := by
  simp [mean, sum_add_distrib, add_div]

private theorem mean_sub (M : ℕ) (f g : ℕ → ℝ) :
    mean M (fun n => f n - g n) = mean M f - mean M g := by
  simp [mean, sum_sub_distrib, sub_div]

private theorem mean_mul_const (M : ℕ) (f : ℕ → ℝ) (c : ℝ) :
    mean M (fun n => c * f n) = c * mean M f := by
  simp [mean, ← mul_sum, mul_div_assoc]

private theorem mean_one {M : ℕ} (hM : 0 < M) : mean M (fun _ => 1) = 1 := by
  simp [mean, show (M : ℝ) ≠ 0 by exact_mod_cast hM.ne']

private theorem mean_flag (M : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    mean M (flag P) = ((Nat.count P M : ℕ) : ℝ) / M := by
  classical
  rw [Nat.count_eq_card_filter_range]
  unfold mean
  congr 1
  calc
    (∑ n ∈ range M, flag P n) = ∑ _n ∈ (range M).filter P, (1 : ℝ) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro n _
      by_cases hn : P n <;> simp [flag, hn]
    _ = _ := by simp

private theorem modular_mul {D M : ℕ} (hD : D ∣ M) {f : ℕ → ℝ} (hf : Modular D f) :
    Modular M f := fun a b hab => hf a b (hab.of_dvd hD)

private theorem sum_blocks {M : ℕ} {f : ℕ → ℝ} (hf : Modular M f) (q : ℕ) :
    (∑ n ∈ range (M*q), f n) = (q : ℝ) * ∑ n ∈ range M, f n := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, sum_range_add, ih, Nat.cast_succ, add_mul, one_mul]
    congr 1
    apply sum_congr rfl
    intro n _
    exact hf _ _ (by simp [Nat.ModEq, Nat.add_mod])

private theorem mean_mul_range {M q : ℕ} (hM : 0 < M) (hq : 0 < q) {f : ℕ → ℝ}
    (hf : Modular M f) : mean (M*q) f = mean M f := by
  rw [mean, sum_blocks hf]
  unfold mean
  push_cast
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  field_simp

private theorem mean_tendsto {M : ℕ} (hM : 0 < M) {f : ℕ → ℝ} (hf : Modular M f)
    (hlo : ∀ n, 0 ≤ f n) (hhi : ∀ n, f n ≤ 1) :
    Tendsto (fun N => mean N f) atTop (𝓝 (mean M f)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hM' : 0 < (M : ℝ) := by exact_mod_cast hM
  have hLarge : ∀ᶠ N : ℕ in atTop, (M : ℝ)/ε < (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop _
  filter_upwards [eventually_ge_atTop (1 : ℕ), hLarge] with N hN hNlarge
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hdecomp : (N : ℝ) = (M : ℝ) * ((N/M : ℕ) : ℝ) + ((N%M : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod N M).symm
  let R := ∑ n ∈ range (N%M), f n
  have hR₀ : 0 ≤ R := sum_nonneg fun n _ => hlo n
  have hR₁ : R ≤ ((N%M : ℕ) : ℝ) := by
    have h := sum_le_sum (s := range (N%M)) (fun n _ => hhi n)
    simpa using h
  have hμ₀ : 0 ≤ mean M f := div_nonneg (sum_nonneg fun n _ => hlo n) (by positivity)
  have hμ₁ : mean M f ≤ 1 := by
    rw [mean, div_le_one₀ hM']
    have h := sum_le_sum (s := range M) (fun n _ => hhi n)
    simpa using h
  have hNsum : (∑ n ∈ range N, f n) =
      ((N/M : ℕ) : ℝ) * (∑ n ∈ range M, f n) + R := by
    conv_lhs => rw [← Nat.div_add_mod N M, sum_range_add, sum_blocks hf]
    congr 1
    apply sum_congr rfl
    intro n _
    exact hf _ _ (by simp [Nat.ModEq, Nat.add_mod])
  have herr : mean N f - mean M f = (R - ((N%M : ℕ) : ℝ)*mean M f)/N := by
    rw [mean, hNsum]
    have he : (N : ℝ) * mean M f =
        ((N/M : ℕ) : ℝ) * (∑ n ∈ range M, f n) + ((N%M : ℕ) : ℝ) * mean M f := by
      conv_lhs => rw [hdecomp, add_mul]
      rw [mean]
      field_simp
    field_simp
    linarith
  rw [Real.dist_eq, herr, abs_div, abs_of_pos hN']
  have hMr : ((N%M : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Nat.mod_lt N hM).le
  have hμR₀ : 0 ≤ ((N%M : ℕ) : ℝ) * mean M f := by positivity
  have hμR₁ : ((N%M : ℕ) : ℝ) * mean M f ≤ ((N%M : ℕ) : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hμ₁ (by positivity : 0 ≤ ((N%M : ℕ) : ℝ))
  apply (div_lt_iff₀ hN').mpr
  have hbound := (div_lt_iff₀ hε).mp hNlarge
  rw [abs_lt]
  constructor <;> linarith

private theorem range_to_mod {m : ℕ} [NeZero m] (f : ℕ → ℝ) :
    (∑ a ∈ range m, f a) = ∑ z : ZMod m, f z.val := by
  classical
  apply sum_bij (fun a : ℕ => fun _ => (a : ZMod m))
  · intro a ha
    exact mem_univ _
  · intro a ha b hb h
    have h' := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha),
      ZMod.val_natCast_of_lt (mem_range.mp hb)] using h'
  · intro z _
    exact ⟨z.val, mem_range.mpr (ZMod.val_lt _), ZMod.natCast_zmod_val z⟩
  · intro a ha
    rw [ZMod.val_natCast_of_lt (mem_range.mp ha)]

private theorem mean_crt {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : m.Coprime n)
    {f g : ℕ → ℝ} (hf : Modular m f) (hg : Modular n g) :
    mean (m*n) (fun a => f a*g a) = mean m f * mean n g := by
  let : NeZero m := ⟨hm.ne'⟩
  let : NeZero n := ⟨hn.ne'⟩
  let : NeZero (m*n) := ⟨(mul_pos hm hn).ne'⟩
  let e := ZMod.chineseRemainder h
  have he (z : ZMod (m*n)) : e z = ((z.val : ZMod m),(z.val : ZMod n)) := by
    calc
      _ = e (z.val : ZMod (m*n)) := congrArg e (ZMod.natCast_zmod_val z).symm
      _ = _ := by rw [map_natCast]; rfl
  have hsum : (∑ a ∈ range (m*n), f a*g a) =
      (∑ a ∈ range m, f a) * (∑ a ∈ range n, g a) := by
    calc
      _ = ∑ z : ZMod (m*n), f z.val*g z.val := range_to_mod _
      _ = ∑ z : ZMod (m*n), f (e z).1.val * g (e z).2.val := by
        apply sum_congr rfl
        intro z _
        congr 1
        · apply hf
          apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
          rw [ZMod.natCast_zmod_val, he]
        · apply hg
          apply (ZMod.natCast_eq_natCast_iff' _ _ _).mp
          rw [ZMod.natCast_zmod_val, he]
      _ = ∑ z : ZMod m × ZMod n, f z.1.val*g z.2.val :=
        e.toEquiv.sum_comp (fun z => f z.1.val*g z.2.val)
      _ = _ := by rw [Fintype.sum_prod_type, range_to_mod f, range_to_mod g, sum_mul]; simp_rw [mul_sum]
  simp only [mean, hsum, Nat.cast_mul, div_mul_div_comm]

private theorem flag_and (P Q : ℕ → Prop) (a : ℕ) :
    flag (fun n => P n ∧ Q n) a = flag P a * flag Q a := by
  classical
  by_cases hP : P a <;> by_cases hQ : Q a <;> simp [flag, hP, hQ]

private theorem flag_compl (P : ℕ → Prop) (a : ℕ) :
    flag (fun n => ¬P n) a = 1-flag P a := by
  classical
  by_cases hp : P a <;> simp [flag, hp]

private theorem modular_div {d M : ℕ} (hd : d ∣ M) : Modular M (flag (d ∣ ·)) := by
  apply modular_flag
  intro a b h
  have he : a%d = b%d := h.of_dvd hd
  simp only [Nat.dvd_iff_mod_eq_zero, he]

private theorem mean_dvd {d M : ℕ} (hM : 0 < M) (hd : d ∣ M) :
    mean M (flag (d ∣ ·)) = 1/(d : ℝ) := by
  have hd₀ : 0 < d := Nat.pos_of_dvd_of_pos hd hM
  obtain ⟨q, rfl⟩ := hd
  have hq : 0 < q := Nat.pos_of_dvd_of_pos (dvd_mul_left _ _) hM
  rw [mean_mul_range hd₀ hq (modular_div dvd_rfl)]
  unfold mean
  congr 1
  rw [sum_eq_single_of_mem 0 (by simpa using hd₀)]
  · simp [flag]
  · intro a ha ha₀
    have had : ¬ d ∣ a := fun h => (mem_range.mp ha).not_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero ha₀) h)
    simp [flag, had]

private def primeMod (P : Finset ℕ) (E : ℕ) : ℕ := ∏ p ∈ P, p^E

private theorem primeMod_pos {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (E : ℕ) :
    0 < primeMod P E := prod_pos fun p hp => pow_pos (hP p hp).pos E

private theorem primeMod_dvd {p E : ℕ} {P : Finset ℕ} (hp : p ∈ P) (hE : 0 < E) :
    p ∣ primeMod P E := dvd_trans (dvd_pow_self p hE.ne') (dvd_prod_of_mem _ hp)

private def gap (P : Finset ℕ) (n : ℕ) : Prop := ∀ p ∈ P, ¬ p ∣ n

private theorem modular_gap {P : Finset ℕ} {E : ℕ} (hE : 0 < E) :
    Modular (primeMod P E) (flag (gap P)) := by
  apply modular_flag
  intro a b h
  have he (p : ℕ) (hp : p ∈ P) : a%p = b%p := h.of_dvd (primeMod_dvd hp hE)
  unfold gap
  constructor <;> intro hgap p hp <;> specialize hgap p hp
  · simpa only [Nat.dvd_iff_mod_eq_zero, ←he p hp] using hgap
  · simpa only [Nat.dvd_iff_mod_eq_zero, he p hp] using hgap

private theorem coprime_primeMod {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ q ∈ Q, q.Prime) (h : Disjoint P Q) (E : ℕ) :
    (primeMod P E).Coprime (primeMod Q E) := by
  apply Nat.coprime_prod_left_iff.mpr
  intro p hp
  apply Nat.coprime_prod_right_iff.mpr
  intro q hq
  have hne : p ≠ q := fun h' => disjoint_left.mp h hp (h' ▸ hq)
  exact (((Nat.coprime_primes (hP p hp) (hQ q hq)).mpr hne).pow_left _).pow_right _

private theorem mean_gap (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {E : ℕ} (hE : 0 < E) :
    mean (primeMod P E) (flag (gap P)) = ∏ p ∈ P, (1-1/(p : ℝ)) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [primeMod, mean, flag, gap]
  | @insert p P hp ih =>
    have hP' (q : ℕ) (hq : q ∈ P) : q.Prime := hP q (mem_insert_of_mem hq)
    have hp' := hP p (mem_insert_self _ _)
    have hpow : 0 < p^E := pow_pos hp'.pos _
    have hco : (p^E).Coprime (primeMod P E) := by
      simpa [primeMod] using coprime_primeMod (P := {p}) (Q := P)
        (fun q hq => by simpa using (mem_singleton.mp hq ▸ hp')) hP'
        (by simpa using hp) E
    have hfg : flag (gap (insert p P)) =
        (fun a => flag (fun n => ¬p ∣ n) a * flag (gap P) a) := by
      funext a
      rw [← flag_and]
      have he : gap (insert p P) a ↔ ¬ p ∣ a ∧ gap P a := by simp [gap]
      by_cases hp : gap (insert p P) a
      · simp [flag, hp, he.mp hp]
      · have hh : ¬ (¬ p ∣ a ∧ gap P a) := fun h => hp (he.mpr h)
        simp only [flag, if_neg hp, if_neg hh]
    have hM : primeMod (insert p P) E = p^E * primeMod P E := prod_insert hp
    rw [hM, hfg, mean_crt hpow (primeMod_pos hP' E) hco _ (modular_gap hE), prod_insert hp, ih hP']
    have hd : p ∣ p^E := dvd_pow_self _ hE.ne'
    · rw [show flag (fun n => ¬ p ∣ n) = (fun n => 1-flag (p ∣ ·) n) from funext (flag_compl _) ,
        mean_sub, mean_one hpow, mean_dvd hpow hd]
    · apply modular_flag
      intro a b hab
      have he : a%p = b%p := hab.of_dvd (dvd_pow_self p hE.ne')
      simp only [Nat.dvd_iff_mod_eq_zero, he]

private theorem le_cast_div_succ (N p : ℕ) (hp : 0 < p) :
    (N : ℝ)/p ≤ ((N/p : ℕ) : ℝ) + 1 := by
  apply (div_le_iff₀ (by exact_mod_cast hp : 0 < (p : ℝ))).mpr
  rw [mul_comm]
  exact_mod_cast (Nat.lt_mul_div_succ N hp).le

private theorem log_factors {n : ℕ} (hn : 0 < n) :
    Real.log n = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ)*Real.log p := by
  have hprod : (∏ p ∈ n.primeFactors, p^(n.factorization p)) = n :=
    Nat.prod_factorization_pow_eq_self hn.ne'
  calc
    Real.log n = Real.log ((∏ p ∈ n.primeFactors, p^(n.factorization p) : ℕ) : ℝ) := by rw [hprod]
    _ = _ := by
      push_cast
      rw [Real.log_prod]
      · simp only [Real.log_pow]
      · intro p hp
        exact pow_ne_zero _ (by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.ne_zero)

private theorem prime_log_sum (Y : ℕ) :
    (∑ p ∈ Nat.primesLE Y, Real.log p) ≤ Real.log 4 * Y := by
  rw [← Chebyshev.theta_eq_sum_primesLE_log]
  exact Chebyshev.theta_le_log4_mul_x (by positivity)

private theorem prime_log_harmonic {Y : ℕ} (hY : 0 < Y) :
    (∑ p ∈ Nat.primesLE Y, Real.log p / (p : ℝ)) ≤ Real.log Y + Real.log 4 := by
  let P := Nat.primesLE Y
  have hY' : 0 < (Y : ℝ) := by exact_mod_cast hY
  have hp (p : ℕ) (hp : p ∈ P) : p.Prime ∧ p ≤ Y := ⟨(Nat.mem_primesLE.mp hp).2, (Nat.mem_primesLE.mp hp).1⟩
  have hfac (p : ℕ) (hp : p.Prime) : Y/p ≤ Y.factorial.factorization p := by
    rw [Nat.factorization_factorial hp (show Nat.log p Y < Nat.log p Y + 2 by omega)]
    simpa only [pow_one] using
      (single_le_sum (f := fun i : ℕ => Y/p^i) (fun _ _ => Nat.zero_le _)
        (mem_Ico.mpr (show 1 ≤ (1 : ℕ) ∧ 1 < Nat.log p Y + 2 by omega)))
  have hmul : (Y : ℝ) * (∑ p ∈ P, Real.log p / (p : ℝ)) ≤
      Real.log Y.factorial + ∑ p ∈ P, Real.log p := by
    rw [mul_sum, log_factors (Nat.factorial_pos Y)]
    calc
      _ ≤ ∑ p ∈ P, ((Y.factorial.factorization p : ℝ)+1) * Real.log p := by
        apply sum_le_sum
        intro p hP
        have hq := (hp p hP).1
        have hbound := (le_cast_div_succ Y p hq.pos).trans
          (add_le_add_left (show ((Y/p : ℕ) : ℝ) ≤ (Y.factorial.factorization p : ℝ) by
            exact_mod_cast hfac p hq) 1)
        rw [show (Y : ℝ) * (Real.log p / (p : ℝ)) = ((Y : ℝ)/p)*Real.log p by ring]
        apply mul_le_mul_of_nonneg_right hbound
        exact Real.log_natCast_nonneg p
      _ = (∑ p ∈ P, (Y.factorial.factorization p : ℝ)*Real.log p) + ∑ p ∈ P, Real.log p := by
        simp only [add_mul, one_mul, sum_add_distrib]
      _ ≤ _ := by
        apply add_le_add_left
        refine sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ =>
          mul_nonneg (by positivity) (Real.log_natCast_nonneg p))
        intro p hP
        obtain ⟨hp, hpY⟩ := hp p hP
        exact Nat.mem_primeFactors.mpr
          ⟨hp, hp.dvd_factorial.mpr hpY, Nat.factorial_ne_zero _⟩
  have hlog : Real.log Y.factorial ≤ (Y : ℝ)*Real.log Y := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos Y)
    exact_mod_cast Nat.factorial_le_pow Y
  have hθ := prime_log_sum Y
  apply (mul_le_mul_iff_of_pos_left hY').mp
  linarith

private theorem mean_sum {α : Type*} (M : ℕ) (S : Finset α) (f : α → ℕ → ℝ) :
    mean M (fun n => ∑ a ∈ S, f a n) = ∑ a ∈ S, mean M (f a) := by
  simp only [mean, sum_div]
  rw [sum_comm]

private theorem primeMod_factorization {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (E p : ℕ) :
    (primeMod P E).factorization p = if p ∈ P then E else 0 := by
  classical
  rw [primeMod, Nat.factorization_prod_apply (fun q hq => pow_ne_zero _ (hP q hq).ne_zero)]
  rw [show (∑ q ∈ P, (q^E).factorization p) = ∑ q ∈ P, if q=p then E else 0 from by
    apply sum_congr rfl
    intro q hq
    rw [(hP q hq).factorization_pow, Finsupp.single_apply]]
  simp

private theorem gcd_modular (M : ℕ) (a b : ℕ) (h : a ≡ b [MOD M]) :
    a.gcd M = b.gcd M := by
  have H (x : ℕ) : x.gcd M = (x%M).gcd M := by
    rw [Nat.gcd_comm x M, Nat.gcd_rec]
  rw [H a, H b, show a%M = b%M from h]

private theorem geometric_tail {p : ℕ} (hp : p.Prime) (E : ℕ) :
    (∑ j ∈ Icc 1 E, (1 : ℝ)/(p : ℝ)^j) ≤ 2/(p : ℝ) := by
  let z := (p : ℝ)⁻¹
  have hz₀ : 0 ≤ z := by dsimp [z]; positivity
  have hz₁ : z ≤ 1/2 := by
    dsimp [z]
    rw [inv_le_iff_one_le_mul₀ (by exact_mod_cast hp.pos)]
    have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have hz : z < 1 := by linarith
  have hr : insert 0 (Icc 1 E) = range (E+1) := by
    ext j
    simp only [mem_insert, mem_Icc, mem_range]
    omega
  have hgeom := (summable_geometric_of_lt_one hz₀ hz).sum_le_tsum (range (E+1)) (fun j _ =>
    pow_nonneg hz₀ _)
  rw [tsum_geometric_of_lt_one hz₀ hz, ← hr, sum_insert (by simp : (0 : ℕ) ∉ Icc 1 E), pow_zero] at hgeom
  have hbound : (1-z)⁻¹ ≤ 1+2*z := by
    apply (inv_le_iff_one_le_mul₀ (by linarith : 0 < 1-z)).mpr
    nlinarith [mul_nonneg hz₀ (show 0 ≤ 1-2*z by linarith)]
  simp only [one_div, ← inv_pow]
  change (∑ j ∈ Icc 1 E, z^j) ≤ 2*z
  linarith

private theorem log_gcd_eq {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (E n : ℕ) :
    Real.log (n.gcd (primeMod P E)) =
      ∑ p ∈ P, ∑ j ∈ Icc 1 E, Real.log p * flag (p^j ∣ ·) n := by
  classical
  let M := primeMod P E
  let a := n.gcd M
  have hM : 0 < M := primeMod_pos hP E
  have ha : 0 < a := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_right n M) hM
  have hfac : a.factorization ≤ M.factorization :=
    (Nat.factorization_le_iff_dvd ha.ne' hM.ne').mpr (Nat.gcd_dvd_right _ _)
  have hsubset : a.primeFactors ⊆ P := by
    intro p hp
    have hv := (Nat.mem_primeFactors.mp hp).1.factorization_pos_of_dvd ha.ne'
      (Nat.mem_primeFactors.mp hp).2.1
    have := hfac p
    change a.factorization p ≤ (primeMod P E).factorization p at this
    rw [primeMod_factorization hP] at this
    by_contra! hn
    simp [hn] at this
    omega
  have hsum (p : ℕ) (hp : p ∈ P) :
      (∑ j ∈ Icc 1 E, flag (p^j ∣ ·) n) = (a.factorization p : ℝ) := by
    let v := a.factorization p
    have hvE : v ≤ E := by
      have := hfac p
      simpa only [M, primeMod_factorization hP, if_pos hp] using this
    have hJ : ((Icc 1 E).filter (fun j => p^j ∣ n)) = Icc 1 v := by
      ext j
      simp only [mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨h₁, h₂⟩, hd⟩
        have hpow : p^j ∣ M := (pow_dvd_pow p h₂).trans (dvd_prod_of_mem _ hp)
        exact ⟨h₁, ((hP p hp).pow_dvd_iff_le_factorization ha.ne').mp (Nat.dvd_gcd hd hpow)⟩
      · rintro ⟨h₁,h₂⟩
        exact ⟨⟨h₁, h₂.trans hvE⟩,
          (((hP p hp).pow_dvd_iff_le_factorization ha.ne').mpr h₂).trans (Nat.gcd_dvd_left n M)⟩
    calc
      _ = ∑ _j ∈ (Icc 1 E).filter (fun j => p^j ∣ n), (1 : ℝ) := by
        rw [sum_filter]
        apply sum_congr rfl
        intro j _
        by_cases h : p^j ∣ n <;> simp [flag, h]
      _ = _ := by simp [hJ, Nat.card_Icc, v]
  have hlog : (∑ p ∈ a.primeFactors, (a.factorization p : ℝ)*Real.log p) =
      ∑ p ∈ P, (a.factorization p : ℝ)*Real.log p := by
    apply sum_subset hsubset
    intro p _ hp
    have hnz : a.factorization p = 0 := by
      apply Finsupp.notMem_support_iff.mp
      simpa only [Nat.support_factorization] using hp
    simp [hnz]
  rw [log_factors ha, hlog]
  apply sum_congr rfl
  intro p hp
  rw [← mul_sum, hsum p hp, mul_comm]

private theorem log_gcd_mean (Y : ℕ) (hY : 0 < Y) (E : ℕ) :
    mean (primeMod (Nat.primesLE Y) E) (fun n => Real.log (n.gcd (primeMod (Nat.primesLE Y) E))) ≤
      2 * (Real.log Y + Real.log 4) := by
  let P := Nat.primesLE Y
  let M := primeMod P E
  have hp (p : ℕ) (h : p ∈ P) : p.Prime := (Nat.mem_primesLE.mp h).2
  have hM : 0 < M := primeMod_pos hp E
  calc
    _ = ∑ p ∈ P, Real.log p * ∑ j ∈ Icc 1 E, 1 / (p : ℝ)^j := by
      have he : (fun n => Real.log (n.gcd M)) =
          (fun n => ∑ p ∈ P, ∑ j ∈ Icc 1 E, Real.log p * flag (p^j ∣ ·) n) :=
        funext (log_gcd_eq hp E)
      change mean M (fun n => Real.log (n.gcd M)) = _
      rw [he]
      simp_rw [mean_sum, mean_mul_const]
      apply sum_congr rfl
      intro p hp
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      congr 1
      have hd : p^j ∣ M := (pow_dvd_pow p (mem_Icc.mp hj).2).trans (dvd_prod_of_mem _ hp)
      rw [mean_dvd hM hd, Nat.cast_pow]
    _ ≤ ∑ p ∈ P, 2 * (Real.log p/(p : ℝ)) := by
      refine sum_le_sum fun p h => ?_
      calc
        _ ≤ Real.log p * (2/(p : ℝ)) :=
          mul_le_mul_of_nonneg_left (geometric_tail (hp p h) E) (Real.log_natCast_nonneg p)
        _ = _ := by ring
    _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (prime_log_harmonic hY) (by norm_num)

private theorem mean_large_gcd (Y : ℕ) (hY : 4 ≤ Y) (E r : ℕ) (hr : 0 < r) :
    mean (primeMod (Nat.primesLE Y) E) (flag (fun n => Y^r < n.gcd (primeMod (Nat.primesLE Y) E))) ≤
      4/(r : ℝ) := by
  let M := primeMod (Nat.primesLE Y) E
  have hM : 0 < M := primeMod_pos (fun p hp => (Nat.mem_primesLE.mp hp).2) E
  have hY' : (1 : ℝ) < Y := by exact_mod_cast (show 1 < Y by omega)
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  have hlog : 0 < Real.log Y := Real.log_pos hY'
  have hμ : ((r : ℝ)*Real.log Y) * mean M (flag (fun n => Y^r < n.gcd M)) ≤
      2 * (Real.log Y + Real.log 4) := by
    rw [← mean_mul_const]
    refine (mean_mono M (fun n _ => ?_)).trans (log_gcd_mean Y (by omega) E)
    have ha : 0 < n.gcd M := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_right _ _) hM
    classical
    by_cases h : Y^r < n.gcd M
    · rw [flag, if_pos h, mul_one, ← Real.log_pow]
      exact Real.log_le_log (by positivity) (by exact_mod_cast h.le)
    · simp only [flag, if_neg h, mul_zero]
      exact Real.log_natCast_nonneg _
  have h₄ : Real.log 4 ≤ Real.log Y :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hY)
  have hμ' : ((r : ℝ)*Real.log Y) * mean M (flag (fun n => Y^r < n.gcd M)) ≤ 4*Real.log Y :=
    hμ.trans (by linarith)
  apply (mul_le_mul_iff_of_pos_right (mul_pos hr' hlog)).mp
  calc
    _ = ((r : ℝ)*Real.log Y) * mean M (flag (fun n => Y^r < n.gcd M)) := by ring
    _ ≤ 4*Real.log Y := hμ'
    _ = _ := by field_simp [ne_of_gt hr']

private def block (Y Z : ℕ) : Finset ℕ := Nat.primesLE Z \ Nat.primesLE Y

private theorem block_prime {Y Z p : ℕ} (h : p ∈ block Y Z) : p.Prime :=
  (Nat.mem_primesLE.mp (mem_sdiff.mp h).1).2

private theorem block_pos_probability {Y r E : ℕ} (hY : 4 ≤ Y) (_hr : 0 < r) (hE : 0 < E) :
    Real.exp (-2*(4*(r : ℝ)+1)) ≤ mean (primeMod (block Y ((Y^r)^4)) E)
      (flag (gap (block Y ((Y^r)^4)))) := by
  let Z := (Y^r)^4
  let B := block Y Z
  have hY₀ : 0 < Y := by omega
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hYlog : 0 < Real.log Y := Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hweights : (∑ p ∈ B, (1 : ℝ)/(p : ℝ)) ≤ 4*(r : ℝ)+1 := by
    apply (mul_le_mul_iff_of_pos_left hYlog).mp
    rw [mul_sum]
    calc
      _ ≤ ∑ p ∈ B, Real.log p/(p : ℝ) := by
        apply sum_le_sum
        intro p hp
        have hp' := block_prime hp
        have hlt : Y < p := by
          by_contra! h
          exact (mem_sdiff.mp hp).2 (Nat.mem_primesLE.mpr ⟨h, hp'⟩)
        rw [mul_one_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact Real.log_le_log (by exact_mod_cast hY₀) (by exact_mod_cast hlt.le)
      _ ≤ ∑ p ∈ Nat.primesLE Z, Real.log p/(p : ℝ) :=
        sum_le_sum_of_subset_of_nonneg sdiff_subset (fun p _ _ =>
          div_nonneg (Real.log_natCast_nonneg p) (by positivity))
      _ ≤ Real.log Z + Real.log 4 := prime_log_harmonic hZ
      _ ≤ _ := by
        have h₄ : Real.log 4 ≤ Real.log Y := Real.log_le_log (by norm_num) (by exact_mod_cast hY)
        dsimp [Z]
        push_cast
        rw [Real.log_pow, Real.log_pow]
        push_cast
        linarith
  have hexp (p : ℕ) (hp : p ∈ B) : Real.exp (-(2*(1/(p : ℝ)))) ≤ 1-1/(p : ℝ) := by
    let x := 1/(p : ℝ)
    have hx₀ : 0 ≤ x := by dsimp [x]; positivity
    have hx₁ : x ≤ 1/2 := by
      dsimp [x]
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      exact_mod_cast (block_prime hp).two_le
    change Real.exp (-(2*x)) ≤ 1-x
    rw [Real.exp_neg]
    apply (inv_le_iff_one_le_mul₀ (Real.exp_pos _)).mpr
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (2*x)) (show 0 ≤ 1-x by linarith)
    nlinarith [mul_nonneg hx₀ (show 0 ≤ 1-2*x by linarith)]
  have hprod : Real.exp (-(2*(∑ p ∈ B, (1 : ℝ)/(p : ℝ)))) ≤
      ∏ p ∈ B, (1-1/(p : ℝ)) := by
    rw [mul_sum, ← sum_neg_distrib, Real.exp_sum]
    exact prod_le_prod (fun _ _ => Real.exp_nonneg _) hexp
  exact (Real.exp_le_exp.mpr (by linarith)).trans
    (hprod.trans_eq (mean_gap B (fun _ hp => block_prime hp) hE).symm)

private theorem prefix_split {Y Z : ℕ} (hYZ : Y ≤ Z) (E : ℕ) :
    primeMod (Nat.primesLE Z) E = primeMod (Nat.primesLE Y) E * primeMod (block Y Z) E := by
  have hsub : Nat.primesLE Y ⊆ Nat.primesLE Z := fun p hp =>
    Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans hYZ, (Nat.mem_primesLE.mp hp).2⟩
  unfold primeMod block
  rw [← prod_union (disjoint_sdiff : Disjoint (Nat.primesLE Y) (Nat.primesLE Z \ Nat.primesLE Y))]
  rw [union_sdiff_of_subset hsub]

private theorem level_primeMod_dvd {Y Z : ℕ} (hYZ : Y ≤ Z) (E : ℕ) :
    primeMod (Nat.primesLE Y) E ∣ primeMod (Nat.primesLE Z) E :=
  ⟨_, prefix_split hYZ E⟩

private theorem block_independent {Y Z E : ℕ} (hYZ : Y ≤ Z) {f g : ℕ → ℝ}
    (hf : Modular (primeMod (Nat.primesLE Y) E) f) (hg : Modular (primeMod (block Y Z) E) g) :
    mean (primeMod (Nat.primesLE Z) E) (fun a => f a * g a) =
      mean (primeMod (Nat.primesLE Y) E) f * mean (primeMod (block Y Z) E) g := by
  have hP (p : ℕ) (h : p ∈ Nat.primesLE Y) : p.Prime := (Nat.mem_primesLE.mp h).2
  have hQ (p : ℕ) (h : p ∈ block Y Z) : p.Prime := block_prime h
  have hd : Disjoint (Nat.primesLE Y) (block Y Z) := by unfold block; exact disjoint_sdiff
  rw [prefix_split hYZ]
  exact mean_crt (primeMod_pos hP E) (primeMod_pos hQ E) (coprime_primeMod hP hQ hd E) hf hg

private theorem failure_step {Y Z E : ℕ} (hYZ : Y ≤ Z) (hE : 0 < E) (r : ℕ)
    (A : ℕ → Prop) (hA : Modular (primeMod (Nat.primesLE Y) E) (flag A)) :
    let B := gap (block Y Z)
    let C := fun n : ℕ => Y^r < n.gcd (primeMod (Nat.primesLE Y) E)
    mean (primeMod (Nat.primesLE Z) E) (flag (fun n => A n ∧ ¬(B n ∧ ¬C n))) ≤
      (1-mean (primeMod (block Y Z) E) (flag B)) * mean (primeMod (Nat.primesLE Y) E) (flag A) +
      mean (primeMod (block Y Z) E) (flag B) * mean (primeMod (Nat.primesLE Y) E) (flag C) := by
  dsimp
  let B := gap (block Y Z)
  let C := fun n : ℕ => Y^r < n.gcd (primeMod (Nat.primesLE Y) E)
  let I := primeMod (Nat.primesLE Y) E
  let J := primeMod (block Y Z) E
  let K := primeMod (Nat.primesLE Z) E
  have hB₀ : Modular J (flag B) := modular_gap hE
  have hB₁ : Modular J (flag (fun n => ¬ B n)) := by
    intro a b hab
    rw [flag_compl, flag_compl, hB₀ _ _ hab]
  have hC : Modular I (flag C) := modular_flag fun a b hab => by dsimp [C]; rw [gcd_modular _ _ _ hab]
  have hJ : 0 < J := primeMod_pos (fun _ hp => block_prime hp) E
  have hBμ : mean J (flag (fun n => ¬B n)) = 1-mean J (flag B) := by
    rw [show flag (fun n => ¬B n) = (fun n => 1-flag B n) from funext (flag_compl _), mean_sub, mean_one hJ]
  calc
    _ ≤ mean K (fun n => flag A n * flag (fun n => ¬B n) n + flag C n * flag B n) := by
      apply mean_mono
      intro n _
      change flag (fun n => A n ∧ ¬(B n ∧ ¬C n)) n ≤ _
      classical
      by_cases ha : A n <;> by_cases hb : B n <;> by_cases hc : C n <;> norm_num [flag, ha,hb,hc]
    _ = mean I (flag A) * mean J (flag (fun n => ¬ B n)) +
        mean I (flag C) * mean J (flag B) := by
      rw [mean_add, block_independent hYZ hA hB₁, block_independent hYZ hC hB₀]
    _ = _ := by rw [hBμ]; ring

private theorem inverse_square_tail (Y N : ℕ) (hY : 0 < Y) :
    (∑ d ∈ Ioc Y N, 1/(d : ℝ)^2) ≤ 1/(Y : ℝ) := by
  by_cases hYN : Y ≤ N
  · have ht (d : ℕ) (hd : d ∈ Ioc Y N) :
        1/(d : ℝ)^2 ≤ 1/((d-1 : ℕ) : ℝ) - 1/(d : ℝ) := by
      have hd₁ : 1 < d := (show 1 ≤ Y from hY).trans_lt (mem_Ioc.mp hd).1
      have hdR : (1 : ℝ) < d := by exact_mod_cast hd₁
      rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
      have h₁ : (d : ℝ) ≠ 0 := by positivity
      have h₂ : (d : ℝ) - 1 ≠ 0 := by linarith
      rw [show (1 : ℝ)/((d : ℝ)-1)-1/(d : ℝ) = 1/(((d : ℝ)-1)*(d : ℝ)) by
        field_simp [h₁, h₂]; ring]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith
    have htelescope : (∑ d ∈ Ioc Y N, ((1 : ℝ)/((d-1 : ℕ) : ℝ) - 1/(d : ℝ))) =
        1/(Y : ℝ) - 1/(N : ℝ) := by
      let f (i : ℕ) := (1 : ℝ)/((Y+i : ℕ) : ℝ)
      calc
        _ = ∑ j ∈ range (N-Y), (f j - f (j+1)) := by
          symm
          apply sum_bij (fun j : ℕ => fun _ => Y+j+1)
          · intro j hj
            have := mem_range.mp hj
            exact mem_Ioc.mpr (by omega)
          · intro j hj k hk he
            omega
          · intro d hd
            have := mem_Ioc.mp hd
            exact ⟨d-Y-1, mem_range.mpr (by omega), by omega⟩
          · intro j _
            simp only [f, Nat.add_succ_sub_one, Nat.add_assoc]
        _ = -(∑ j ∈ range (N-Y), (f (j+1)-f j)) := by
          rw [← sum_neg_distrib]
          apply sum_congr rfl
          intro j _
          ring
        _ = _ := by rw [sum_range_sub]; simp only [f, Nat.add_zero, Nat.add_sub_of_le hYN]; ring
    exact (sum_le_sum ht).trans (htelescope.le.trans (sub_le_self _ (by positivity)))
  · have he : Ioc Y N = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro d hd
      have := mem_Ioc.mp hd
      omega
    rw [he, sum_empty]
    positivity

private theorem reciprocal_tail_mean (Y N : ℕ) (hY : 0 < Y) (hN : 0 < N) :
    mean N (fun n => reciprocalTail n Y) ≤ 1/(Y : ℝ) := by
  classical
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hterm (n : ℕ) (hn : n < N) :
      reciprocalTail n Y = ∑ d ∈ Ioc Y N, (1/(d : ℝ))*flag (fun a => a ≠ 0 ∧ d ∣ a) n := by
    have he : n.divisors.filter (fun d => Y < d) = (Ioc Y N).filter (fun d => n ≠ 0 ∧ d ∣ n) := by
      ext d
      simp only [mem_filter, Nat.mem_divisors, mem_Ioc]
      constructor
      · rintro ⟨⟨hd, hn₀⟩, hYd⟩
        exact ⟨⟨hYd, (Nat.le_of_dvd (Nat.pos_of_ne_zero hn₀) hd).trans hn.le⟩, hn₀, hd⟩
      · rintro ⟨⟨hYd,_⟩, hn₀, hd⟩
        exact ⟨⟨hd, hn₀⟩, hYd⟩
    rw [reciprocalTail, he, sum_filter]
    apply sum_congr rfl
    intro d _
    by_cases h : n ≠ 0 ∧ d ∣ n <;> simp [flag, h]
  have hmean : mean N (fun n => reciprocalTail n Y) =
      ∑ d ∈ Ioc Y N, (1/(d : ℝ))*mean N (flag (fun a => a ≠ 0 ∧ d ∣ a)) := by
    calc
      _ = mean N (fun n => ∑ d ∈ Ioc Y N, (1/(d : ℝ))*flag (fun a => a ≠ 0 ∧ d ∣ a) n) := by
        unfold mean
        rw [sum_congr rfl (fun n hn => hterm n (mem_range.mp hn))]
      _ = _ := by simp_rw [mean_sum, mean_mul_const]
  rw [hmean]
  refine (sum_le_sum (g := fun d : ℕ => 1/(d : ℝ)^2) (fun d hd => ?_)).trans (inverse_square_tail Y N hY)
  have hd₀ : 0 < d := hY.trans (mem_Ioc.mp hd).1
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd₀
  have hs : mean N (flag (fun a => a ≠ 0 ∧ d ∣ a)) ≤ 1/(d : ℝ) := by
    rw [mean_flag, Nat.count_eq_card_filter_range]
    have hc : ((range N).filter (fun a => a ≠ 0 ∧ d ∣ a)).card = (N-1)/d := by
      conv_lhs => rw [show N = (N-1).succ by omega]
      exact Nat.card_multiples' (N-1) d
    rw [hc]
    apply (div_le_iff₀ (by positivity)).mpr
    rw [show (1 : ℝ)/(d : ℝ)*N = (N : ℝ)/d by ring]
    apply (le_div_iff₀ hdR).mpr
    have hh := Nat.div_mul_le_self (N-1) d
    exact_mod_cast hh.trans (Nat.sub_le _ _)
  have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ (1 : ℝ)/(d : ℝ) by positivity)
  convert hh using 1
  ring

private def levels (A r : ℕ) : ℕ → ℕ
  | 0 => A
  | j+1 => ((levels A r j)^r)^4

private theorem levels_step (A r j : ℕ) (hr : 0 < r) :
    levels A r j ≤ levels A r (j+1) :=
  (Nat.le_self_pow hr.ne' _).trans (Nat.le_self_pow (by decide : 4 ≠ (0 : ℕ)) _)

private theorem levels_mono (A r : ℕ) (hr : 0 < r) : Monotone (levels A r) :=
  monotone_nat_of_le_succ (fun j => levels_step A r j hr)

private def smooth (A r E j n : ℕ) : ℕ := n.gcd (primeMod (Nat.primesLE (levels A r j)) E)

private def good (A r E j n : ℕ) : Prop :=
  gap (block (levels A r j) (levels A r (j+1))) n ∧ smooth A r E j n ≤ (levels A r j)^r

private def failure (A r E L n : ℕ) : Prop := ∀ j < L, ¬ good A r E j n

private theorem modular_failure {A r E : ℕ} (hr : 0 < r) (hE : 0 < E) (k : ℕ) :
    Modular (primeMod (Nat.primesLE (levels A r k)) E) (flag (failure A r E k)) := by
  apply modular_flag
  intro a b hab
  have he (j : ℕ) (hj : j < k) : good A r E j a ↔ good A r E j b := by
    let y := levels A r j
    let z := levels A r (j+1)
    have hyz := levels_step A r j hr
    have hz := level_primeMod_dvd (levels_mono A r hr (show j+1 ≤ k from hj)) E
    have ha := hab.of_dvd ((level_primeMod_dvd hyz E).trans hz)
    have hb := hab.of_dvd ((show primeMod (block y z) E ∣ primeMod (Nat.primesLE z) E from
      ⟨_, (prefix_split hyz E).trans (mul_comm _ _)⟩).trans hz)
    change (gap (block y z) a ∧ a.gcd (primeMod (Nat.primesLE y) E) ≤ y^r) ↔
      (gap (block y z) b ∧ b.gcd (primeMod (Nat.primesLE y) E) ≤ y^r)
    rw [gcd_modular _ _ _ ha]
    apply and_congr_left
    intro _
    unfold gap
    constructor <;> intro hg p hp
    · specialize hg p hp
      simpa only [Nat.dvd_iff_mod_eq_zero, ←show a%p = b%p from hb.of_dvd (primeMod_dvd hp hE)] using hg
    · specialize hg p hp
      simpa only [Nat.dvd_iff_mod_eq_zero, show a%p = b%p from hb.of_dvd (primeMod_dvd hp hE)] using hg
  constructor <;> intro ht j hj
  · exact fun h => ht j hj ((he j hj).mpr h)
  · exact fun h => ht j hj ((he j hj).mp h)

private theorem probability_failure {A r E : ℕ} (hA : 4 ≤ A) (hr : 0 < r) (hE : 0 < E) (k : ℕ) :
    mean (primeMod (Nat.primesLE (levels A r k)) E) (flag (failure A r E k)) ≤
      4/(r : ℝ) + (1-Real.exp (-2*(4*(r : ℝ)+1)))^k := by
  let ρ := Real.exp (-2*(4*(r : ℝ)+1))
  have hρ : 0 < ρ := Real.exp_pos _
  have hρ₁ : ρ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [Nat.cast_nonneg (α := ℝ) r])
  induction k with
  | zero =>
    have hM : 0 < primeMod (Nat.primesLE A) E :=
      primeMod_pos (fun _ hp => (Nat.mem_primesLE.mp hp).2) E
    rw [show levels A r 0 = A from rfl,
      show flag (failure A r E 0) = (fun _ => 1) from by
        funext n; simp [flag, failure], mean_one hM, pow_zero]
    linarith [show 0 ≤ (4 : ℝ)/(r : ℝ) by positivity]
  | succ k ih =>
    let y := levels A r k
    let z := levels A r (k+1)
    let I := primeMod (Nat.primesLE y) E
    let J := primeMod (block y z) E
    let g := mean J (flag (gap (block y z)))
    have hy : 4 ≤ y := hA.trans (levels_mono A r hr (Nat.zero_le k))
    have hyz : y ≤ z := levels_step A r k hr
    have hgρ : ρ ≤ g := block_pos_probability hy hr hE
    have hg₀ : 0 ≤ g := hρ.le.trans hgρ
    have hg₁ : g ≤ 1 := (mean_mono J (fun n _ => flag_le_one _ _)).trans_eq
      (mean_one (primeMod_pos (fun _ hp => block_prime hp) E))
    have hEq : flag (failure A r E (k+1)) =
        flag (fun n => failure A r E k n ∧ ¬ (gap (block y z) n ∧ ¬ y^r < n.gcd I)) := by
      funext n
      have he : failure A r E (k+1) n ↔
          failure A r E k n ∧ ¬ (gap (block y z) n ∧ ¬ y^r < n.gcd I) := by
        rw [not_lt]
        constructor
        · intro h
          exact ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), fun h' => h k (Nat.lt_succ_self _) h'⟩
        · rintro ⟨h₁,h₂⟩ j hj
          rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | rfl
          · exact h₁ j h
          · exact h₂
      classical
      by_cases h : failure A r E (k+1) n
      · simp only [flag, if_pos h, if_pos (he.mp h)]
      · have hn : ¬ (failure A r E k n ∧ ¬(gap (block y z) n ∧ ¬y^r<n.gcd I)) := fun hh => h (he.mpr hh)
        simp only [flag, if_neg h, if_neg hn]
    rw [hEq]
    have hs := failure_step hyz hE r (failure A r E k) (modular_failure hr hE k)
    have hbig := mean_large_gcd y hy E r hr
    calc
      _ ≤ (1-g)*mean I (flag (failure A r E k)) +
           g*mean I (flag (fun n => y^r < n.gcd I)) := hs
      _ ≤ (1-g)*(4/(r : ℝ)+(1-ρ)^k) + g*(4/(r : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hg₁)) (mul_le_mul_of_nonneg_left hbig hg₀)
      _ = 4/(r : ℝ) + (1-g)*(1-ρ)^k := by ring
      _ ≤ _ := by
        change _ ≤ 4/(r : ℝ)+(1-ρ)^(k+1)
        rw [pow_succ, mul_comm ((1-ρ)^k)]
        exact add_le_add_right (mul_le_mul_of_nonneg_right (sub_le_sub_left hgρ 1)
          (pow_nonneg (sub_nonneg.mpr hρ₁) k)) _

private theorem stable_at_good {A r E j n : ℕ} (hn : 0 < n)
    (hE : levels A r (j+1) ≤ E) (hg : good A r E j n)
    (ht : reciprocalTail n (levels A r (j+1)) < 1/((levels A r j : ℝ)^r)) :
    n.Pseudoperfect ↔ (smooth A r E j n).Pseudoperfect := by
  let y := levels A r j
  let z := levels A r (j+1)
  let M := primeMod (Nat.primesLE y) E
  let b := n.gcd M
  have hP (p : ℕ) (hp : p ∈ Nat.primesLE y) : p.Prime := (Nat.mem_primesLE.mp hp).2
  have hM : 0 < M := primeMod_pos hP E
  have hbn : b ∣ n := Nat.gcd_dvd_left n M
  have hb : 0 < b := Nat.pos_of_dvd_of_pos hbn hn
  have hcut (a : ℕ) (ha : a ∣ n) (haz : a ≤ z) : a ∣ b := by
    have ha₀ : 0 < a := Nat.pos_of_dvd_of_pos ha hn
    apply Nat.dvd_gcd ha
    apply (Nat.factorization_le_iff_dvd ha₀.ne' hM.ne').mp
    intro p
    change a.factorization p ≤ (primeMod (Nat.primesLE y) E).factorization p
    rw [primeMod_factorization hP]
    by_cases hp : p ∈ a.primeFactors
    · obtain ⟨hprime, hdiv, _⟩ := Nat.mem_primeFactors.mp hp
      have hpz := (Nat.le_of_dvd ha₀ hdiv).trans haz
      have hpy : p ≤ y := by
        by_contra h
        have hpB : p ∈ block y z :=
          mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨hpz, hprime⟩, fun h2 => h (Nat.mem_primesLE.mp h2).1⟩
        exact hg.1 p hpB (hdiv.trans ha)
      rw [if_pos (Nat.mem_primesLE.mpr ⟨hpy,hprime⟩)]
      by_contra! hv
      have hdvd := (hprime.pow_dvd_iff_le_factorization ha₀.ne').mpr (show E ≤ a.factorization p by omega)
      have hpow := Nat.le_of_dvd ha₀ hdvd
      have hp₂ : 2^E ≤ p^E := Nat.pow_le_pow_left hprime.two_le _
      have hh := E.lt_two_pow_self
      omega
    · have hf : a.factorization p = 0 := by
        apply Finsupp.notMem_support_iff.mp
        simpa only [Nat.support_factorization] using hp
      simp [hf]
  have hbdy : (b : ℝ) ≤ (y : ℝ)^r := by exact_mod_cast hg.2
  have ht' : reciprocalTail n z < 1/(b : ℝ) :=
    ht.trans_le (div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hb) hbdy)
  obtain ⟨c,hc⟩ := hbn
  have hc' : 0 < c := by
    by_contra! hh
    have hc₀ : c = 0 := by omega
    simp [hc₀] at hc
    omega
  have he : n = c*b := hc.trans (mul_comm _ _)
  have h := pseudoperfect_of_small_tail (Y := z) hc' hb (fun a ha haz => hcut a (he ▸ ha) haz)
    (he ▸ ht')
  change n.Pseudoperfect ↔ b.Pseudoperfect
  exact he.symm ▸ h

private theorem approximation_density {P : ℕ → Prop}
    (hP : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 0 < M ∧ ∃ f : ℕ → ℝ, Modular M f ∧
      (∀ n, 0 ≤ f n) ∧ (∀ n, f n ≤ 1) ∧
      ∀ᶠ N : ℕ in atTop, dist (mean N (flag P)) (mean N f) ≤ ε) :
    ∃ d : ℝ, Tendsto (fun N => mean N (flag P)) atTop (𝓝 d) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨M,hM,f,hmod,hlo,hhi,happ⟩ := hP (ε/6) (by positivity)
  have hf := mean_tendsto hM hmod hlo hhi
  have hnear := (Metric.tendsto_nhds.mp hf) (ε/6) (by positivity)
  have hall : ∀ᶠ N : ℕ in atTop, dist (mean N (flag P)) (mean M f) ≤ ε/3 := by
    filter_upwards [happ, hnear] with N hN hs
    have htri := dist_triangle (mean N (flag P)) (mean N f) (mean M f)
    linarith
  obtain ⟨K,hK⟩ := eventually_atTop.mp hall
  refine ⟨K, fun m hm n hn => ?_⟩
  have hm' := hK m hm
  have hn' := hK n hn
  have htri := dist_triangle_right (mean m (flag P)) (mean n (flag P)) (mean M f)
  linarith

private def approximant (A r E L n : ℕ) : Prop :=
  ∃ j < L, good A r E j n ∧ (smooth A r E j n).Pseudoperfect

private theorem modular_approx {A r E : ℕ} (hr : 0 < r) (hE : 0 < E) (L : ℕ) :
    Modular (primeMod (Nat.primesLE (levels A r L)) E) (flag (approximant A r E L)) := by
  apply modular_flag
  intro a b hab
  have he (j : ℕ) (hj : j < L) : (good A r E j a ∧ (smooth A r E j a).Pseudoperfect) ↔
      (good A r E j b ∧ (smooth A r E j b).Pseudoperfect) := by
    have hset := levels_step A r j hr
    have hL := level_primeMod_dvd (levels_mono A r hr (Nat.succ_le_of_lt hj)) E
    have hprefix := level_primeMod_dvd hset E
    have ha' := hab.of_dvd (hprefix.trans hL)
    have hb' := hab.of_dvd ((show primeMod (block (levels A r j) (levels A r (j+1))) E ∣
      primeMod (Nat.primesLE (levels A r (j+1))) E from ⟨_, (prefix_split hset E).trans (mul_comm _ _)⟩).trans hL)
    have hm : smooth A r E j a = smooth A r E j b := gcd_modular _ _ _ ha'
    have ht : gap (block (levels A r j) (levels A r (j+1))) a ↔
        gap (block (levels A r j) (levels A r (j+1))) b := by
      constructor <;> intro h p hp
      · exact fun hd => h p hp (by
          rw [Nat.dvd_iff_mod_eq_zero, (show a%p = b%p from hb'.of_dvd (primeMod_dvd hp hE))]
          exact Nat.mod_eq_zero_of_dvd hd)
      · exact fun hd => h p hp (by
          rw [Nat.dvd_iff_mod_eq_zero, ← (show a%p = b%p from hb'.of_dvd (primeMod_dvd hp hE))]
          exact Nat.mod_eq_zero_of_dvd hd)
    unfold good
    rw [hm, ht]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (he j hj).mp h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (he j hj).mpr h⟩

private theorem tail_failure_mean {A r j N : ℕ} (hA : 1 ≤ A) (hr : 0 < r) (hN : 0 < N) :
    mean N (flag (fun n => 1/((levels A r j : ℝ)^r) ≤ reciprocalTail n (levels A r (j+1)))) ≤ 1/(A : ℝ) := by
  let y := levels A r j
  let w : ℝ := (y : ℝ)^r
  let z := levels A r (j+1)
  let T := fun n => 1/w ≤ reciprocalTail n z
  have hyA : A ≤ y := levels_mono A r hr (Nat.zero_le _)
  have hypos : 0 < y := hA.trans hyA
  have hwy : (y : ℝ) ≤ w := by dsimp [w]; exact_mod_cast Nat.le_self_pow hr.ne' y
  have hw : 0 < w := (show 0 < (y : ℝ) by exact_mod_cast hypos).trans_le hwy
  have hz : 0 < z := by change 0 < (y^r)^4; positivity
  have hmarkov : (1/w)*mean N (flag T) ≤ 1/(z : ℝ) := by
    rw [← mean_mul_const]
    refine (mean_mono N (fun n _ => ?_)).trans (reciprocal_tail_mean z N hz hN)
    classical
    by_cases h : T n
    · rwa [flag, if_pos h, mul_one]
    · simp only [flag, if_neg h, mul_zero]
      exact sum_nonneg fun a _ => by positivity
  have hnew : mean N (flag T) ≤ w/(z : ℝ) := by
    have hh : mean N (flag T) / w ≤ 1/(z : ℝ) := by
      simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hmarkov
    exact ((div_le_iff₀ hw).mp hh).trans_eq (by ring)
  have hz' : (z : ℝ) = w^4 := by
    change (((y^r)^4 : ℕ) : ℝ) = w^4
    push_cast
    rfl
  have hA' : (A : ℝ) ≤ w := (by exact_mod_cast hyA : (A : ℝ) ≤ y).trans hwy
  have hw1 : 1 ≤ w := (by exact_mod_cast hA : (1 : ℝ) ≤ A).trans hA'
  refine hnew.trans ?_
  rw [hz']
  have hposA : 0 < (A : ℝ) := by exact_mod_cast hA
  apply (le_div_iff₀ hposA).mpr
  rw [div_mul_eq_mul_div, div_le_one₀ (by positivity)]
  have h₁ := mul_le_mul_of_nonneg_left hA' hw.le
  have h₂ : w^2 ≤ w^4 := pow_le_pow_right₀ hw1 (by decide)
  nlinarith

private theorem approx_error {A r E L N : ℕ} (hA : 1 ≤ A) (hr : 0 < r)
    (hE : levels A r L ≤ E) (hN : 0 < N) :
    dist (mean N (flag Nat.Pseudoperfect)) (mean N (flag (approximant A r E L))) ≤
      mean N (flag (failure A r E L)) + 1/(N : ℝ) + (L : ℝ)/(A : ℝ) := by
  let T (j n : ℕ) : Prop :=
    1/((levels A r j : ℝ)^r) ≤ reciprocalTail n (levels A r (j+1))
  have hpoint (n : ℕ) :
      |flag Nat.Pseudoperfect n - flag (approximant A r E L) n| ≤
        flag (failure A r E L) n + flag (· = 0) n + ∑ j ∈ range L, flag (T j) n := by
    classical
    have hbasic : |flag Nat.Pseudoperfect n - flag (approximant A r E L) n| ≤ 1 :=
      abs_le.mpr ⟨by linarith [flag_nonneg Nat.Pseudoperfect n, flag_le_one (approximant A r E L) n],
        by linarith [flag_le_one Nat.Pseudoperfect n, flag_nonneg (approximant A r E L) n]⟩
    have hsum₀ : 0 ≤ ∑ j ∈ range L, flag (T j) n := sum_nonneg fun j _ => flag_nonneg _ _
    by_cases hfail : failure A r E L n
    · have hf : flag (failure A r E L) n = 1 := by simp only [flag, if_pos hfail]
      linarith [flag_nonneg (·=0) n]
    by_cases hn : n = 0
    · have hf : flag (·=0) n = 1 := by simp only [flag, if_pos hn]
      linarith [flag_nonneg (failure A r E L) n]
    by_cases htail : ∃ j < L, T j n
    · obtain ⟨j,hj,hj'⟩ := htail
      have h₁ := single_le_sum (f := fun j => flag (T j) n) (fun j _ => flag_nonneg _ _)
        (mem_range.mpr hj)
      have hf : flag (T j) n = 1 := by simp only [flag, if_pos hj']
      rw [hf] at h₁
      linarith [flag_nonneg (failure A r E L) n, flag_nonneg (·=0) n]
    have hstable (j : ℕ) (hj : j < L) (hg : good A r E j n) :
        n.Pseudoperfect ↔ (smooth A r E j n).Pseudoperfect :=
      stable_at_good (Nat.pos_of_ne_zero hn)
        ((levels_mono A r hr (Nat.succ_le_of_lt hj)).trans hE) hg
        (lt_of_not_ge (fun h => htail ⟨j,hj,h⟩))
    have he : n.Pseudoperfect ↔ approximant A r E L n := by
      constructor
      · intro hw
        have : ∃ j < L, good A r E j n := by
          by_contra! h
          exact hfail h
        obtain ⟨j,hj,hg⟩ := this
        exact ⟨j,hj,hg,(hstable j hj hg).mp hw⟩
      · rintro ⟨j,hj,hg,hw⟩
        exact (hstable j hj hg).mpr hw
    have hf : flag Nat.Pseudoperfect n = flag (approximant A r E L) n := by
      by_cases h : n.Pseudoperfect
      · simp only [flag, if_pos h, if_pos (he.mp h)]
      · simp only [flag, if_neg h, if_neg (fun ha => h (he.mpr ha))]
    rw [hf, sub_self, abs_zero]
    exact add_nonneg (add_nonneg (flag_nonneg _ _) (flag_nonneg _ _)) hsum₀
  have hsum : (∑ j ∈ range L, mean N (flag (T j))) ≤ (L : ℝ)/(A : ℝ) := by
    calc
      _ ≤ ∑ _j ∈ range L, (1 : ℝ)/(A : ℝ) := sum_le_sum fun j _ => tail_failure_mean hA hr hN
      _ = _ := by simp [div_eq_mul_inv]
  have hzero : mean N (flag (·=0)) = 1/(N : ℝ) := by
    rw [mean]
    congr 1
    rw [sum_eq_single_of_mem 0 (mem_range.mpr hN)]
    · simp [flag]
    · intro n _ hn
      simp [flag, hn]
  have hd : dist (mean N (flag Nat.Pseudoperfect)) (mean N (flag (approximant A r E L))) ≤
      mean N (fun n => |flag Nat.Pseudoperfect n - flag (approximant A r E L) n|) := by
    rw [Real.dist_eq, ← mean_sub, mean, mean, abs_div, abs_of_nonneg (by exact_mod_cast hN.le : (0 : ℝ) ≤ (N : ℝ))]
    exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (by exact_mod_cast hN.le : (0 : ℝ) ≤ (N : ℝ))
  exact hd.trans ((mean_mono N (fun n _ => hpoint n)).trans (by
    rw [mean_add, mean_add, mean_sum, hzero]
    exact add_le_add_right hsum _))


private theorem pseudoperfect_limit : ∃ d : ℝ, Tendsto (fun N => mean N (flag Nat.Pseudoperfect)) atTop (𝓝 d) := by
  apply approximation_density
  intro ε hε
  obtain ⟨r,hr⟩ := exists_nat_gt (32/ε)
  have hr₀ : 0 < r := by
    by_contra! h
    have hrz : r=0 := by omega
    simp only [hrz, Nat.cast_zero] at hr
    exact (not_lt_of_ge (by positivity : 0 ≤ (32 : ℝ)/ε)) hr
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr₀
  have hr' : (4 : ℝ)/r ≤ ε/8 := by
    apply (div_le_iff₀ hrR).mpr
    have hh := (div_lt_iff₀ hε).mp hr
    linarith
  let ρ := Real.exp (-2*(4*(r : ℝ)+1))
  have hρ₀ : 0 < ρ := Real.exp_pos _
  have hρ₁ : ρ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hg : Tendsto (fun k : ℕ => (1-ρ)^k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hρ₁) (by linarith)
  obtain ⟨L,hL⟩ := ((tendsto_order.mp hg).2 _ (show (0 : ℝ) < ε/8 by positivity)).exists
  obtain ⟨a,ha⟩ := exists_nat_gt (4*(L : ℝ)/ε)
  let A := a+4
  have hA : 4 ≤ A := by dsimp [A]; omega
  have hA₀ : 0 < A := by omega
  have hA' : (L : ℝ)/(A : ℝ) ≤ ε/4 := by
    apply (div_le_iff₀ (by exact_mod_cast hA₀ : 0 < (A : ℝ))).mpr
    have ha' := (div_lt_iff₀ hε).mp ha
    dsimp [A]
    push_cast
    nlinarith
  let E := levels A r L + 1
  have hE : 0 < E := by dsimp [E]; omega
  let M := primeMod (Nat.primesLE (levels A r L)) E
  have hM : 0 < M := primeMod_pos (fun _ hp => (Nat.mem_primesLE.mp hp).2) E
  let P := approximant A r E L
  refine ⟨M, hM, flag P, modular_approx hr₀ hE L, flag_nonneg P, flag_le_one P, ?_⟩
  let F := flag (failure A r E L)
  have hlim := mean_tendsto hM (modular_failure hr₀ hE L) (flag_nonneg _) (flag_le_one _)
  have hμ : mean M F < ε/2 := by
    have hprob := probability_failure hA hr₀ hE L
    change mean M F ≤ 4/(r : ℝ)+(1-ρ)^L at hprob
    linarith
  have hfail : ∀ᶠ N : ℕ in atTop, mean N F < ε/2 :=
    (tendsto_order.mp hlim).2 _ hμ
  have hnear : ∀ᶠ N : ℕ in atTop, (4 : ℝ)/ε ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop (1 : ℕ), hnear, hfail] with N hN hNbig hFN
  have hsmall : 1/(N : ℝ) ≤ ε/4 := by
    apply (div_le_iff₀ (by exact_mod_cast hN : 0 < (N : ℝ))).mpr
    have hh := (div_le_iff₀ hε).mp hNbig
    linarith
  have herror := approx_error (show 1 ≤ A by omega) hr₀ (show levels A r L ≤ E from Nat.le_succ _) hN
  change dist (mean N (flag Nat.Pseudoperfect)) (mean N (flag P)) ≤ _
  change dist (mean N (flag Nat.Pseudoperfect)) (mean N (flag P)) ≤ mean N F + 1/(N : ℝ) + (L : ℝ)/(A : ℝ) at herror
  linarith

end PseudoperfectDensity

theorem OMA.solution : OMA.R_Erdos470_erdos_470_variants_weird_pos_density_R1.H2 := by
  classical
  obtain ⟨d, hd⟩ := PseudoperfectDensity.pseudoperfect_limit
  refine ⟨d, ?_⟩
  rw [Set.HasDensity]
  convert hd using 1
  funext N
  rw [PseudoperfectDensity.mean_flag, Nat.count_eq_card_filter_range]
  let A := (range N).filter Nat.Pseudoperfect
  have hset : (A : Set ℕ) = {n : ℕ | n.Pseudoperfect} ∩ Set.Iio N := by
    ext n
    simp [A, and_comm]
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio, ← hset,
    Set.ncard_coe_finset]
  congr 3
