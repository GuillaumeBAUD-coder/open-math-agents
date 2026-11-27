import FormalConjectures.GreensOpenProblems.«25»
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# An orbit partition with few restricted sums

For `N = 64^m - 1` with `m` a power of two, partition the positive representatives
modulo `N` into orbits under multiplication by `64`. Short orbits are sparse, so the
number of parts has order `N / log N`. Two different elements of a single orbit have
sum divisible by one of the numbers `64^u + 1`, whose reciprocals have small sum.
-/

/- Rotation of base-64 digits gives an orbit partition modulo `64^m-1`. -/
namespace OMA.Green25Orbit
open Finset Function
open scoped Classical

private def rotationRel {α : Type*} (f : α → α) {m : ℕ} (hm : 0 < m)
    (hper : ∀ x, IsPeriodicPt f m x) : Setoid α where
  r x y := ∃ j, f^[j] x = y
  iseqv := {
    refl := fun _ => ⟨0,rfl⟩
    symm := by
      rintro x y ⟨j,rfl⟩
      refine ⟨m-j%m,?_⟩
      rw [← (hper x).iterate_mod_apply j,←iterate_add_apply,
        Nat.sub_add_cancel (Nat.mod_lt _ hm).le]
      exact hper x
    trans := by
      rintro x y z ⟨i,rfl⟩ ⟨j,rfl⟩
      exact ⟨j+i,iterate_add_apply _ _ _ _⟩ }

private lemma cast_injective {N : ℕ} : Set.InjOn (fun a : ℕ => (a : ZMod N)) (Icc 1 N) := by
  intro a ha b hb he
  obtain ⟨ha,haN⟩ := mem_Icc.mp ha
  obtain ⟨hb,hbN⟩ := mem_Icc.mp hb
  have h := (ZMod.natCast_eq_natCast_iff' a b N).mp he
  rcases haN.lt_or_eq with haN | rfl <;> rcases hbN.lt_or_eq with hbN | rfl
  · rwa [Nat.mod_eq_of_lt haN,Nat.mod_eq_of_lt hbN] at h
  · rw [Nat.mod_eq_of_lt haN,Nat.mod_self] at h
    omega
  · rw [Nat.mod_self,Nat.mod_eq_of_lt hbN] at h
    omega
  · rfl

private lemma rotation_partition {N m : ℕ} [NeZero N] (hm : 0 < m)
    (f : ZMod N → ZMod N) (hper : ∀ x, IsPeriodicPt f m x) :
    ∃ P : Finpartition (Icc 1 N), ∀ C ∈ P.parts, ∀ x ∈ C,
      C.card = minimalPeriod f (x : ZMod N) ∧
      ∀ y ∈ C, x ≠ y → ∃ j, 0 < j ∧ j < m ∧ f^[j] (x:ZMod N) = (y:ZMod N) := by
  let I := Icc 1 N
  let cast (n : ℕ) := (n : ZMod N)
  have surj : Function.Surjective (fun a : I => cast a.val) := by
    apply (Fintype.bijective_iff_injective_and_card _).mpr _ |>.surjective
    exact ⟨fun a b h => Subtype.ext (cast_injective a.property b.property h),
      by simp [I,Nat.card_Icc]⟩
  let R := (rotationRel f hm hper).comap cast
  let P := Finpartition.ofSetSetoid R I
  refine ⟨P,?_⟩
  intro C hC x hx
  have hsub := P.le hC
  have memC (y : ℕ) : y ∈ C ↔ y ∈ I ∧ ∃ j, f^[j] (cast x)=cast y := by
    rw [←P.part_eq_of_mem hC hx,Finpartition.mem_part_ofSetSetoid_iff_rel]
    exact and_iff_right (hsub hx)
  constructor
  · let k := minimalPeriod f (cast x)
    have hk : 0 < k := (hper _).minimalPeriod_pos hm
    have himage : C.image cast = (range k).image (fun j => f^[j] (cast x)) := by
      ext z
      constructor
      · intro hz
        obtain ⟨y,hy,rfl⟩ := mem_image.mp hz
        obtain ⟨j,hj⟩ := ((memC y).mp hy).2
        exact mem_image.mpr ⟨j%k,mem_range.mpr (Nat.mod_lt _ hk),iterate_mod_minimalPeriod_eq.trans hj⟩
      · intro hz
        obtain ⟨j,_,rfl⟩ := mem_image.mp hz
        obtain ⟨y,hy⟩ := surj (f^[j] (cast x))
        exact mem_image.mpr ⟨y.val,(memC _).mpr ⟨y.property,j,hy.symm⟩,hy⟩
    have hinj : Set.InjOn cast (C : Set ℕ) := cast_injective.mono hsub
    have hinj' : Set.InjOn (fun j => f^[j] (cast x)) (range k) := by
      intro i hi j hj he
      exact (iterate_eq_iterate_iff_of_lt_minimalPeriod (mem_range.mp hi) (mem_range.mp hj)).mp he
    rw [←card_image_of_injOn hinj,himage,card_image_of_injOn hinj',card_range]
  · intro y hy hne
    obtain ⟨j,hj⟩ := ((memC y).mp hy).2
    have he := ((hper _).iterate_mod_apply j).trans hj
    refine ⟨j%m,?_,Nat.mod_lt _ hm,he⟩
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h] at he
    exact hne (cast_injective (hsub hx) (hsub hy) he)

private lemma partition_count {N m u : ℕ} (P : Finpartition (Icc 1 N))
    (hu : m ≤ u) (hsize : ∀ C ∈ P.parts, C.card ≤ m)
    (hexc : ∀ C ∈ P.parts, C.card < m → ∀ x ∈ C, u ∣ x) :
    N ≤ m * P.parts.card ∧ m * P.parts.card ≤ 2*N := by
  have hsum : ∑ C ∈ P.parts, C.card = N := by simpa [Nat.card_Icc] using P.sum_card_parts
  constructor
  · calc N = ∑ C ∈ P.parts, C.card := hsum.symm
         _ ≤ ∑ _C ∈ P.parts, m := sum_le_sum hsize
         _ = _ := by simp [Nat.mul_comm]
  · let short := P.parts.filter (fun C => C.card < m)
    let rep (C : Finset ℕ) := if h : C.Nonempty then C.min' h else 0
    have hrep (C : Finset ℕ) (hC : C ∈ P.parts) : rep C ∈ C := by
      simpa [rep,P.nonempty_of_mem_parts hC] using C.min'_mem (P.nonempty_of_mem_parts hC)
    have few : short.card ≤ N/u := by
      rw [←Nat.Ioc_filter_dvd_card_eq_div]
      apply card_le_card_of_injOn rep
      · intro C hC
        obtain ⟨hc,hc'⟩ := mem_filter.mp hC
        have hx := hrep C hc
        have hm := mem_Icc.mp (P.le hc hx)
        exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hm.1,hm.2⟩,hexc C hc hc' _ hx⟩
      · intro C hC D hD he
        have hc := (mem_filter.mp hC).1
        have hd := (mem_filter.mp hD).1
        rw [←P.part_eq_of_mem hc (hrep C hc),he,P.part_eq_of_mem hd (hrep D hd)]
    have budget : m*short.card ≤ N := by
      calc m*short.card ≤ u*(N/u) := Nat.mul_le_mul hu few
           _ ≤ N := by simpa [Nat.mul_comm] using Nat.div_mul_le_self N u
    calc m*P.parts.card = ∑ _C ∈ P.parts, m := by simp [Nat.mul_comm]
         _ ≤ ∑ C ∈ P.parts, (C.card + if C.card < m then m else 0) := by
           apply sum_le_sum
           intro C hC
           split_ifs <;> omega
         _ = N+short.card*m := by simp [sum_add_distrib,hsum,←sum_filter,short]
         _ ≤ _ := by nlinarith

theorem partition (s : ℕ) :
    let m := 2^(s+1)
    let N := 64^m-1
    ∃ P : Finpartition (Icc 1 N), N ≤ m*P.parts.card ∧ m*P.parts.card ≤ 2*N ∧
      ∀ C ∈ P.parts, ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
        ∃ j, 0 < j ∧ j < m ∧ y ≡ 64^j*x [MOD N] := by
  let m := 2^(s+1)
  let l := 2^s
  let K := 64^l
  let N := 64^m-1
  have hm : 0 < m := by dsimp [m]; positivity
  have hl : 0 < l := by dsimp [l]; positivity
  have hml : m = l+l := by dsimp [m,l]; rw [pow_succ]; omega
  have hgrowth (n : ℕ) : 2*n+1 ≤ 64^n := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ]; omega
  have hK : 1 < K := by have := hgrowth l; change 1 < 64^l; omega
  have hKN : 64^m = K*K := by rw [hml,pow_add]
  have hN : 0 < N := by dsimp [N]; rw [hKN]; nlinarith [Nat.sub_add_cancel (by nlinarith : 1≤K*K)]
  have : NeZero N := ⟨hN.ne'⟩
  have hfac : N = (K-1)*(K+1) := by
    change 64^m-1 = _
    rw [hKN]
    nlinarith [Nat.sub_add_cancel (by omega : 1≤K),Nat.sub_add_cancel (by nlinarith : 1≤K*K)]
  have hlarge : m ≤ K+1 := by have := hgrowth l; change m ≤ 64^l+1; omega
  let f : ZMod N → ZMod N := (64 * ·)
  have hper (z : ZMod N) : IsPeriodicPt f m z := by
    have h := Nat.sub_add_cancel (Nat.one_le_pow m 64 (by decide))
    change N+1=64^m at h
    have hpow : (64:ZMod N)^m=1 := by
      calc (64:ZMod N)^m = ((64^m:ℕ):ZMod N) := by norm_cast
           _ = ((N+1:ℕ):ZMod N) := by rw [h]
           _ = 1 := by simp
    change (64 * ·)^[m] z=z
    rw [mul_left_iterate_apply,hpow,one_mul]
  obtain ⟨P,hP⟩ := rotation_partition hm f hper
  have hsize (C) (hC : C ∈ P.parts) : C.card ≤ m := by
    obtain ⟨x,hx⟩ := P.nonempty_of_mem_parts hC
    exact ((hP C hC x hx).1).trans_le ((hper _).minimalPeriod_le hm)
  have hex (C) (hC : C ∈ P.parts) (hshort : C.card < m) (x) (hx : x ∈ C) : K+1 ∣ x := by
    have hlen := (hP C hC x hx).1
    have hd := (hper (x:ZMod N)).minimalPeriod_dvd
    obtain ⟨i,his,hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    have his' : i ≤ s := by
      by_contra! h
      have : i=s+1 := by omega
      rw [this] at hi
      change minimalPeriod f (x:ZMod N) = m at hi
      omega
    have hfix : IsPeriodicPt f l (x:ZMod N) := isPeriodicPt_iff_minimalPeriod_dvd.mpr
      (hi ▸ pow_dvd_pow 2 his')
    change (64 * ·)^[l] (x:ZMod N) = x at hfix
    rw [mul_left_iterate_apply] at hfix
    have he : (x:ZMod N) = ((K*x:ℕ):ZMod N) := by
      simpa [K] using hfix.symm
    have hdvd := (Nat.modEq_iff_dvd' (by nlinarith : x ≤ K*x)).mp
      ((ZMod.natCast_eq_natCast_iff _ _ _).mp he)
    have hf : K*x-x=(K-1)*x := by rw [Nat.sub_mul,one_mul]
    rw [hf,hfac] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by omega) hdvd
  obtain ⟨h₁,h₂⟩ := partition_count P hlarge hsize hex
  refine ⟨P,h₁,h₂,?_⟩
  intro C hC x hx y hy hne
  obtain ⟨j,hj,hjm,he⟩ := (hP C hC x hx).2 y hy hne
  refine ⟨j,hj,hjm,(ZMod.natCast_eq_natCast_iff _ _ _).mp ?_⟩
  change (64 * ·)^[j] (x:ZMod N) = y at he
  simpa [mul_left_iterate_apply] using he.symm

end OMA.Green25Orbit

/- Divisibility and density of sums of two different points in a cyclic base-64 orbit. -/

namespace OMA.Green25

open Finset

/-- A nonidentity shift in an orbit forces the sum to have a divisor of the form
    `64^u+1`. Both congruences use the same power of two dividing the shift. -/
theorem orbit_collision {s j x y : ℕ} (hj : 0 < j) (hjm : j < 2 ^ s)
    (h : y ≡ 64 ^ j * x [MOD 64 ^ (2 ^ s) - 1]) :
    ∃ u ∈ Icc 1 (2 ^ s), 64 ^ u + 1 ∣ x + y := by
  obtain ⟨v, q, hq, hjq⟩ := Nat.exists_eq_two_pow_mul_odd hj.ne'
  have huv : 2 ^ v ≤ j := Nat.le_of_dvd hj ⟨q, hjq⟩
  have hvs : v < s := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (huv.trans_lt hjm)
  refine ⟨2 ^ v, mem_Icc.mpr ⟨Nat.one_le_pow _ _ (by decide), (huv.trans hjm.le)⟩, ?_⟩
  have hplus : 64 ^ (2 ^ v) + 1 ∣ (64 : ℕ) ^ j + 1 := by
    rw [hjq, pow_mul]
    simpa using hq.nat_add_dvd_pow_add_pow (64 ^ (2 ^ v)) 1
  have hdiv : 2 ^ (v+1) ∣ (2 : ℕ) ^ s := pow_dvd_pow 2 hvs
  have hN : 64 ^ (2 ^ v) + 1 ∣ (64 : ℕ) ^ (2 ^ s) - 1 := by
    apply dvd_trans _ (Nat.pow_sub_one_dvd_pow_sub_one (x := 64) hdiv)
    rw [pow_succ, pow_mul]
    let w : ℕ := 64 ^ (2 ^ v)
    change w+1 ∣ w^2-1
    have hw : 1 ≤ w := Nat.one_le_pow _ _ (by decide)
    refine ⟨w-1, ?_⟩
    obtain ⟨z,hz⟩ := Nat.exists_eq_add_of_le hw
    rw [hz]
    simp only [Nat.add_sub_cancel_left]
    have : (1+z)^2 = (1+z+1)*z+1 := by ring
    omega
  apply Nat.modEq_zero_iff_dvd.mp
  refine ((h.of_dvd hN).add_left x).trans ?_
  apply Nat.modEq_zero_iff_dvd.mpr
  rw [show x + 64 ^ j * x = (64 ^ j + 1) * x by ring]
  exact dvd_mul_of_dvd_left hplus x

/-- Exceptional positive sums among the integers up to `2*N`. -/
def badSums (m N : ℕ) : Finset ℕ :=
  (Icc 1 (2*N)).filter fun z => ∃ u ∈ Icc 1 m, 64 ^ u + 1 ∣ z

private theorem geometric_count (m n : ℕ) :
    63 * (∑ i ∈ range m, n / 64 ^ (i+1)) ≤ n := by
  induction m generalizing n with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ']
    simp only [zero_add, pow_one]
    have hshift (i : ℕ) : n / 64 ^ (i+1+1) = (n/64) / 64^(i+1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm 64]
    simp_rw [hshift]
    have := ih (n / 64)
    have hd := Nat.div_mul_le_self n 64
    omega

theorem bad_card (m N : ℕ) : 63 * (badSums m N).card ≤ 2*N := by
  let M (i : ℕ) := (range (2*N+1)).filter (fun z => z ≠ 0 ∧ 64^(i+1)+1 ∣ z)
  have hsub : badSums m N ⊆ (range m).biUnion M := by
    intro z hz
    obtain ⟨hz, u, hu, hd⟩ := mem_filter.mp hz
    obtain ⟨hu1,hum⟩ := mem_Icc.mp hu
    obtain ⟨hz1,hzN⟩ := mem_Icc.mp hz
    cases u with
    | zero => omega
    | succ i =>
      exact mem_biUnion.mpr ⟨i, mem_range.mpr (by omega),
        mem_filter.mpr ⟨mem_range.mpr (by omega), by omega, hd⟩⟩
  have hsum : (badSums m N).card ≤ ∑ i ∈ range m, (2*N) / 64^(i+1) := by
    apply (card_le_card hsub).trans
    apply (card_biUnion_le ..).trans
    apply sum_le_sum
    intro i _
    rw [show (M i).card = (2*N)/(64^(i+1)+1) from Nat.card_multiples' ..]
    exact Nat.div_le_div_left (by omega) (by positivity)
  exact (Nat.mul_le_mul_left 63 hsum).trans (geometric_count m (2*N))

end OMA.Green25

/- Extending the cyclic-orbit examples to the precise asymptotic partition statement. -/
namespace OMA.Green25Upper

open _root_.Green25 Real Filter Asymptotics

private theorem scale (m : ℕ) (hm : 0 < m) (N k : ℕ) (hN : N = 64^m-1)
    (lo : N ≤ m*k) (hi : m*k ≤ 2*N) :
    bestUpper N ≤ k ∧ (k:ℝ) ≤ 12*bestUpper N := by
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  have lowerNat : 3^m ≤ N := by
    have : (3:ℕ)^m < 64^m := Nat.pow_lt_pow_left (by norm_num) hm.ne'
    omega
  have upperNat : N ≤ 64^m := hN ▸ Nat.sub_le _ _
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N from (pow_pos (by decide) m).trans_le lowerNat)
  have smallog : (m:ℝ) ≤ log N := calc
    (m:ℝ) ≤ (m:ℝ)*log 3 := by nlinarith [log_three_gt_d9]
    _ = log ((3:ℝ)^m) := (log_pow _ _).symm
    _ ≤ _ := log_le_log (by positivity) (by exact_mod_cast lowerNat)
  have largeLog : log N ≤ 6*m := calc
    _ ≤ log ((64:ℝ)^m) := log_le_log hn (by exact_mod_cast upperNat)
    _ = (m:ℝ)* (6*log 2) := by rw [log_pow,show (64:ℝ) = 2^6 by norm_num,log_pow]; norm_num
    _ ≤ _ := by nlinarith [log_two_lt_d9]
  have lpos := hm'.trans_le smallog
  have h₁ : (N : ℝ) ≤ m*k := by exact_mod_cast lo
  have h₂ : (m : ℝ)*k ≤ 2*N := by exact_mod_cast hi
  change (N:ℝ)/log N ≤ k ∧ (k:ℝ) ≤ 12*((N:ℝ)/log N)
  constructor
  · apply (div_le_iff₀ lpos).mpr
    nlinarith only [h₁,mul_le_mul_of_nonneg_right smallog (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ lpos).mpr
    nlinarith only [h₂,mul_le_mul_of_nonneg_right largeLog (Nat.cast_nonneg k : (0:ℝ) ≤ k)]

/-- Infinitely many counterexamples with the right color count suffice; at other
interval lengths use the ordinary ceiling of n / log n. -/
theorem upper_of_examples (examples : ∀ s : ℕ, 1 ≤ s →
    ∃ k : ℕ, let m := 2^s; let N := 64^m-1
      1 ≤ k ∧ k ≤ N ∧ N ≤ m*k ∧ m*k ≤ 2*N ∧ ¬ Property25 k N) :
    type_of% @Green25.green_25.variants.upper_ess89 := by
  classical
  let Good (N k : ℕ) := 1 ≤ k ∧ k ≤ N ∧ bestUpper N ≤ k ∧
    (k:ℝ) ≤ 12*bestUpper N ∧ ¬ Property25 k N
  let k (n : ℕ) := if h : ∃ j, Good n j then Classical.choose h else ⌈bestUpper n⌉₊
  have has {n} (h : ∃ j, Good n j) : Good n (k n) := by
    simpa only [k,dif_pos h] using Classical.choose_spec h
  have bounds (n : ℕ) (hn : 3 ≤ n) : 1 ≤ k n ∧ k n ≤ n ∧
      bestUpper n ≤ k n ∧ (k n : ℝ) ≤ 12*bestUpper n := by
    by_cases h : ∃ j, Good n j
    · obtain ⟨a,b,c,d,_⟩ := has h
      exact ⟨a,b,c,d⟩
    have logn : 1 ≤ log n := (by linarith [log_three_gt_d9] : 1 ≤ log 3).trans
      (log_le_log (by norm_num) (by exact_mod_cast hn))
    have pos : 0 < log n := by linarith
    have one : 1 ≤ bestUpper n := (le_div_iff₀ pos).mpr (by simpa using Real.log_le_self (Nat.cast_nonneg n))
    have upper : bestUpper n ≤ (n:ℝ) := div_le_self (Nat.cast_nonneg _) logn
    simp only [k,dif_neg h]
    refine ⟨?_,Nat.ceil_le.mpr upper,Nat.le_ceil _,?_⟩
    · have H := Nat.le_ceil (bestUpper n)
      exact_mod_cast one.trans H
    · have H := Nat.ceil_lt_add_one (show 0 ≤ bestUpper n by linarith)
      linarith
  refine ⟨k,?_,?_,?_⟩
  · filter_upwards [eventually_ge_atTop 3] with n hn
    exact ⟨(bounds n hn).1,(bounds n hn).2.1⟩
  · constructor
    · apply Asymptotics.IsBigO.of_bound 12
      filter_upwards [eventually_ge_atTop 3] with n hn
      have h := bounds n hn
      simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _),
        Real.norm_of_nonneg (show 0 ≤ bestUpper n by unfold bestUpper; positivity)] using h.2.2.2
    · apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [eventually_ge_atTop 3] with n hn
      simpa only [Real.norm_of_nonneg (Nat.cast_nonneg _), one_mul,
        Real.norm_of_nonneg (show 0 ≤ bestUpper n by unfold bestUpper; positivity)] using (bounds n hn).2.2.1
  · intro all
    obtain ⟨b,hb⟩ := eventually_atTop.1 all
    let s := b+1
    let m := 2^s
    let N := 64^m-1
    have hm : 0 < m := by dsimp [m]; positivity
    obtain ⟨j,hj⟩ := examples s (by dsimp [s]; omega)
    change 1 ≤ j ∧ j ≤ N ∧ N ≤ m*j ∧ m*j ≤ 2*N ∧ ¬ Property25 j N at hj
    obtain ⟨hjp,hjn,hlo,hhi,hbad⟩ := hj
    have hs := scale m hm N j rfl hlo hhi
    have hg := has (n := N) ⟨j,hjp,hjn,hs.1,hs.2,hbad⟩
    have hsm : s < m := Nat.lt_two_pow_self
    have hmN : m < 64^m := (Nat.lt_two_pow_self (n := m)).trans_le
      (Nat.pow_le_pow_left (by decide) m)
    exact hg.2.2.2.2 (hb N (by dsimp [N,s] at *; omega))

end OMA.Green25Upper

open Finset in
theorem OMA.solution : type_of% @Green25.green_25.variants.upper_ess89 := by
  classical
  apply OMA.Green25Upper.upper_of_examples
  intro s hs
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  let m := 2^(s+1)
  let N := 64^m-1
  obtain ⟨P, lo, hi, pairs⟩ := OMA.Green25Orbit.partition s
  change ∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧ N ≤ m*k ∧ m*k ≤ 2*N ∧ ¬Green25.Property25 k N
  have hm : 0 < m := by dsimp [m]; positivity
  have hpow : 1 < 64^m := one_lt_pow₀ (by decide) hm.ne'
  have np : 0 < N := by dsimp [N]; omega
  change N ≤ m * P.parts.card at lo
  have kpos : 1 ≤ P.parts.card := by
    by_contra! h
    rw [show P.parts.card = 0 by omega, mul_zero] at lo
    omega
  refine ⟨P.parts.card, kpos, by simpa [Nat.card_Icc] using P.card_parts_le_card, lo, hi, ?_⟩
  intro good
  have hgood := good.2.2 P rfl
  have hsub : P.parts.biUnion Finset.restrictedSumset ⊆ OMA.Green25.badSums m N := by
    intro z hz
    obtain ⟨C, hC, hz⟩ := mem_biUnion.mp hz
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := mem_image.mp hz
    obtain ⟨hx, hy, hne⟩ := mem_offDiag.mp hxy
    obtain ⟨j, hj, hjm, hjxy⟩ := pairs C hC x hx y hy hne
    have hX := mem_Icc.mp (P.le hC hx)
    have hY := mem_Icc.mp (P.le hC hy)
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨?_, ?_⟩, OMA.Green25.orbit_collision hj hjm hjxy⟩
    · change 1 ≤ x + y
      omega
    · change x + y ≤ 2*N
      change 1 ≤ x ∧ x ≤ N at hX
      change 1 ≤ y ∧ y ≤ N at hY
      omega
  have bound := Finset.card_le_card hsub
  have bad := OMA.Green25.bad_card m N
  omega
