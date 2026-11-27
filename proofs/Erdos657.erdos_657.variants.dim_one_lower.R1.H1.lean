import OMAReductions.R_Erdos657_erdos_657_variants_dim_one_lower_R1
import Mathlib


/-! A simultaneous phase-avoidance lemma for finite sets of real numbers.
Inside a sufficiently long interval, the total lengths of the forbidden
subintervals are less than half the interval's length. -/

open Finset Set MeasureTheory

namespace OMA.Avoid657

theorem avoid (D : Finset ℝ) : ∃ t : ℝ, ∀ d ∈ D, d ≠ 0 → ∀ z : ℤ,
    2 ≤ |((16*(D.card+1):ℕ):ℝ)*(t*d-z)| := by
  classical
  let N : ℝ := ((16*(D.card+1):ℕ):ℝ)
  let ε : ℝ := 2/N
  let T : ℝ := 1 + ∑ d ∈ D, 2/|d|
  have hN : 0<N := by dsimp [N]; positivity
  have eps : 0<ε := div_pos (by norm_num) hN
  have eps1 : ε≤1 := by
    apply (div_le_one hN).2
    dsimp [N]; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) D.card]
  have hT : 0<T := by dsimp [T]; positivity
  have large {d} (hd : d∈D) (ne:d≠0) : 2≤T*|d| := by
    have hs := single_le_sum (f:=fun x:ℝ ↦ 2/|x|) (fun _ _ ↦ by positivity) hd
    apply (div_le_iff₀ (abs_pos.mpr ne)).1
    exact hs.trans (by dsimp [T]; linarith)
  let J (d:ℝ) := ⌊T*|d|⌋₊+2
  let I (d:ℝ) (j:ℕ) := Icc (((j:ℝ)-ε)/|d|) (((j:ℝ)+ε)/|d|)
  let Bad (d:ℝ) := ⋃ j ∈ range (J d), I d j
  let U := ⋃ d ∈ D.erase 0, Bad d
  have size {d} (hd:d∈D.erase 0) : volume.real (Bad d) ≤ 4*ε*T := by
    obtain ⟨ne, mem⟩ := mem_erase.mp hd
    have dp := abs_pos.mpr ne
    have hj : (J d:ℝ) ≤ 2*(T*|d|) := by
      dsimp [J]; push_cast
      linarith [Nat.floor_le (mul_nonneg hT.le dp.le),large mem ne]
    have vol (j:ℕ) : volume.real (I d j)=2*ε/|d| := by
      dsimp [I]
      rw [Real.volume_real_Icc_of_le (div_le_div_of_nonneg_right (by linarith) dp.le)]
      ring
    calc _ ≤ ∑ j ∈ range (J d), volume.real (I d j) := measureReal_biUnion_finset_le ..
         _ = (J d:ℝ)*(2*ε/|d|) := by simp [vol]
         _ ≤ (2*(T*|d|))*(2*ε/|d|) := mul_le_mul_of_nonneg_right hj (by positivity)
         _ = _ := by field_simp; ring
  have total : volume.real U < T := by
    calc _ ≤ ∑ d ∈ D.erase 0, volume.real (Bad d) := measureReal_biUnion_finset_le ..
         _ ≤ ∑ _d ∈ D.erase 0, 4*ε*T := sum_le_sum fun _ h ↦ size h
         _ ≤ (D.card:ℝ)*(4*ε*T) := by
           simp only [sum_const,nsmul_eq_mul]
           gcongr
           exact erase_subset _ _
         _ < T := by
           dsimp [ε,N]
           push_cast
           have hd : 0≤(D.card:ℝ) := Nat.cast_nonneg _
           field_simp
           nlinarith only [hT, mul_nonneg hd hT.le]
  have comp : IsCompact U := (D.erase 0).isCompact_biUnion fun d _ ↦
    (range (J d)).isCompact_biUnion fun _ _ ↦ isCompact_Icc
  obtain ⟨t, ta, tout⟩ : ∃ t ∈ Icc 0 T, t ∉ U := by
    by_contra! h
    have vv := measureReal_mono (μ:=volume) (s₁:=Icc 0 T) (s₂:=U)
      (fun t ht ↦ h t ht) comp.measure_lt_top.ne
    rw [Real.volume_real_Icc_of_le hT.le, sub_zero] at vv
    exact (not_lt_of_ge vv) total
  refine ⟨t, ?_⟩
  intro d hd ne z
  by_contra! h
  change |N*(t*d-z)|<2 at h
  rw [abs_mul, abs_of_pos hN, mul_comm] at h
  have near := (lt_div_iff₀ hN).2 h
  change |t*d-z|<ε at near
  have near' := (abs_abs_sub_abs_le_abs_sub (t*d) (z:ℝ)).trans_lt near
  have zn : (z.natAbs:ℝ)=|(z:ℝ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  rw [abs_mul,abs_of_nonneg ta.1,←zn] at near'
  obtain ⟨lo,hi⟩ := abs_lt.mp near'
  have dp := abs_pos.mpr ne
  have index : z.natAbs < J d := by
    have htd := mul_le_mul_of_nonneg_right ta.2 dp.le
    apply Nat.cast_lt (α:=ℝ) |>.mp
    dsimp [J]; push_cast
    linarith [Nat.lt_floor_add_one (T*|d|)]
  apply tout
  simp only [U,Bad,Set.mem_iUnion,exists_prop]
  exact ⟨d, mem_erase.mpr ⟨ne,hd⟩,z.natAbs,mem_range.mpr index,
    (div_le_iff₀ dp).2 (by linarith), (le_div_iff₀ dp).2 (by linarith)⟩

end OMA.Avoid657

/- Discretizing a finite set on the line by a phase avoiding its nonzero
four-term differences. The resulting integer bins reflect all two-sum equations. -/
open Finset
open scoped Pointwise

namespace OMA.Model657

theorem build
    (avoid : ∀ D : Finset ℝ, ∃ t : ℝ, ∀ d ∈ D, d ≠ 0 → ∀ z : ℤ,
      2 ≤ |((16*(D.card+1):ℕ):ℝ)*(t*d-z)|) :
    ∃ C : ℝ, 0<C ∧ ∀ (A : Finset ℝ) (K : ℝ), 1≤K → 0<A.card →
      ((A-A).card:ℝ) ≤ K*A.card →
      ∃ (N : ℕ) (B : Finset ℕ) (g : ℕ → ℝ), B⊆range N ∧ A.card≤4*B.card ∧
        (N:ℝ)≤C*K^8*A.card ∧ Set.MapsTo g (B:Set ℕ) (A:Set ℝ) ∧
        Set.InjOn g (B:Set ℕ) ∧
        (∀ a∈B, ∀ b∈B, ∀ c∈B, a+c=b+b → g a+g c=g b+g b) := by
  classical
  refine ⟨32, by norm_num, ?_⟩
  intro A K hK hA hd
  let D := (A+A)-(A+A)
  let N := 16*(D.card+1)
  have npos : 0<N := by dsimp [N]; omega
  obtain ⟨t, ht⟩ := avoid D
  let f (x : ℝ) : ℕ := ⌊(N:ℝ)*Int.fract (t*x)⌋₊
  have err (x : ℝ) :
      (f x:ℝ) ≤ (N:ℝ)*(t*x-(⌊t*x⌋:ℤ)) ∧ (N:ℝ)*(t*x-(⌊t*x⌋:ℤ)) < (f x:ℝ)+1 :=
    ⟨Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (Int.fract_nonneg _)), Nat.lt_floor_add_one _⟩
  have reflect {a b c d : ℝ} (ha:a∈A) (hb:b∈A) (hc:c∈A) (hd':d∈A)
      (eq : f a+f b=f c+f d) : a+b=c+d := by
    by_contra ne
    have hm : (a+b)-(c+d) ∈ D := sub_mem_sub (add_mem_add ha hb) (add_mem_add hc hd')
    have h := ht _ hm (sub_ne_zero.mpr ne) (⌊t*a⌋+⌊t*b⌋-(⌊t*c⌋+⌊t*d⌋))
    change 2 ≤ |(N:ℝ)*_| at h
    push_cast at h
    have heq : (f a:ℝ)+f b=(f c:ℝ)+f d := by exact_mod_cast eq
    apply (not_lt_of_ge h)
    apply abs_lt.mpr
    constructor <;> nlinarith only [heq, (err a).1, (err a).2, (err b).1, (err b).2,
      (err c).1, (err c).2, (err d).1, (err d).2]
  have inj : Set.InjOn f (A : Set ℝ) := by
    intro a ha b hb eq
    exact add_right_cancel (reflect ha ha hb ha (congrArg (·+f a) eq))
  let B := A.image f
  let g := Function.invFunOn f (A:Set ℝ)
  have left {a} (ha:a∈A) : g (f a)=a := inj.leftInvOn_invFunOn ha
  have right {b} (hb:b∈B) : g b ∈ A ∧ f (g b)=b := by
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
    rw [left ha]
    exact ⟨ha,rfl⟩
  have size : (D.card:ℝ) ≤ K^4*A.card := by
    have h := pluennecke_ruzsa_inequality_nsmul_sub_nsmul_sub (card_pos.mp hA) A 2 2
    have h' : (D.card:ℝ) ≤ (((A-A).card:ℝ)/A.card)^4*A.card := by
      dsimp [D]
      simpa only [two_nsmul, NNRat.cast_natCast, NNRat.cast_mul, NNRat.cast_pow,
        NNRat.cast_div] using (NNRat.cast_le (K:=ℝ)).mpr h
    apply h'.trans
    gcongr
    exact (div_le_iff₀ (by exact_mod_cast hA)).mpr hd
  refine ⟨N,B,g,?_,?_,?_,fun _ hb ↦ (right hb).1,?_,?_⟩
  · intro b hb
    obtain ⟨a, _, rfl⟩ := mem_image.mp hb
    apply Finset.mem_range.mpr
    apply (Nat.floor_lt' npos.ne').2
    simpa using mul_lt_mul_of_pos_left (Int.fract_lt_one (t*a)) (by exact_mod_cast npos : 0<(N:ℝ))
  · rw [show B.card=A.card from card_image_of_injOn inj]; omega
  · have h4 : 1≤K^4 := one_le_pow₀ hK
    have h8 : K^4≤K^8 := pow_le_pow_right₀ hK (by norm_num)
    have ha : 1≤(A.card:ℝ) := by exact_mod_cast hA
    have s1 := one_le_mul_of_one_le_of_one_le h4 ha
    have s2 := mul_le_mul_of_nonneg_right h8 (Nat.cast_nonneg A.card)
    dsimp [N]
    push_cast
    nlinarith only [size,s1,s2]
  · intro b hb c hc eq
    rw [←(right hb).2,←(right hc).2,eq]
  · intro a ha b hb c hc eq
    apply reflect (right ha).1 (right hc).1 (right hb).1 (right hb).1
    simpa only [(right ha).2,(right hb).2,(right hc).2] using eq

end OMA.Model657

theorem OMA.solution : OMA.R_Erdos657_erdos_657_variants_dim_one_lower_R1.H1 :=
  OMA.Model657.build OMA.Avoid657.avoid
