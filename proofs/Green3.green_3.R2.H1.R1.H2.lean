import OMAReductions.R_Green3_green_3_R2_H1_R1
import Mathlib

/-! The three translated prefix measures from Franchi–Gowers–Yip, Lemma 4.4.
Between the last nonpositive point and a violation, their total exceeds the
interval length. Sum-freeness makes neighboring windows disjoint, so the two
outer open windows must overlap. -/

open Set MeasureTheory Filter
namespace OMA.SumFreeWindows

lemma openPart {A : Set ℝ} (fin : ∃ s : Finset (ℝ × ℝ), A=⋃ p∈s,Icc p.1 p.2) :
    ∃ U : Set ℝ, IsOpen U ∧ U⊆A ∧ U=ᵐ[volume] A := by
  classical
  obtain ⟨s,rfl⟩ := fin
  exact ⟨⋃ p∈s,Ioo p.1 p.2,isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_Ioo,
    iUnion₂_mono fun _ _ => Ioo_subset_Icc_self,
    ae_eq_set_biUnion s.finite_toSet.countable fun _ _ => Ioo_ae_eq_Icc⟩

lemma prefixMeasure {U : Set ℝ} (ho : IsOpen U) (low : ∀ x∈U, 1≤x) :
    let F (t : ℝ) := volume.real (U ∩ Iic t)
    Continuous F ∧ (∀ a b : ℝ, a≤b → F b-F a=volume.real (U∩Ioo a b)) ∧
      F 0=0 ∧ F 1=0 ∧ F 2≤1 := by
  classical
  let F (t : ℝ) := volume.real (U ∩ Iic t)
  have sub (t : ℝ) : U ∩ Iic t ⊆ Icc 1 t := fun x h => ⟨low x h.1,h.2⟩
  have finite (t : ℝ) : volume (U ∩ Iic t) ≠ ⊤ :=
    ne_of_lt ((measure_mono (sub t)).trans_lt (by simp only [Real.volume_Icc,ENNReal.ofReal_lt_top]))
  have diff (a b : ℝ) (hab : a≤b) : F b-F a=volume.real (U∩Ioo a b) := by
    have split : U∩Iic b=(U∩Iic a)∪(U∩Ioc a b) := by
      ext x; simp only [mem_inter_iff,mem_union,mem_Iic,mem_Ioc]; grind
    have dis : Disjoint (U∩Iic a) (U∩Ioc a b) := Set.disjoint_left.mpr fun _ h k => k.2.1.not_ge h.2
    have same : volume.real (U∩Ioo a b)=volume.real (U∩Ioc a b) :=
      measureReal_congr (ae_eq_set_inter .rfl Ioo_ae_eq_Ioc)
    dsimp only [F]; rw [split,measureReal_union dis (ho.measurableSet.inter measurableSet_Ioc)
      (finite a) (ne_of_lt ((measure_mono inter_subset_right).trans_lt (by simp only [Real.volume_Ioc,ENNReal.ofReal_lt_top]))),same]
    ring
  have bounds (a b : ℝ) (hab : a≤b) : 0≤F b-F a ∧ F b-F a≤b-a := by
    rw [diff a b hab]
    refine ⟨measureReal_nonneg,(measureReal_mono inter_subset_right (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).trans ?_⟩
    simpa using (Real.volume_real_Ioo_of_le hab).le
  have lip : LipschitzWith 1 F := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simp only [Real.dist_eq,NNReal.coe_one,one_mul]
    rcases le_total a b with ab | ba
    · rw [abs_of_nonpos (by linarith [(bounds a b ab).1]),abs_of_nonpos (by linarith)]
      linarith [(bounds a b ab).2]
    · rw [abs_of_nonneg (bounds b a ba).1,abs_of_nonneg (by linarith)]
      exact (bounds b a ba).2
  refine ⟨lip.continuous,diff,?_,?_,?_⟩
  · apply le_antisymm _ measureReal_nonneg
    exact (measureReal_mono (sub 0) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).trans (by norm_num)
  · apply le_antisymm _ measureReal_nonneg
    exact (measureReal_mono (sub 1) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).trans (by rw [Real.volume_real_Icc]; norm_num)
  · exact (measureReal_mono (sub 2) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).trans (by norm_num)

lemma crossing {G : ℝ → ℝ} (hg : Continuous G) {z : ℝ} (zge : 1 ≤ z)
    (left : G 1 ≤ 0) (right : 0 < G z) :
    ∃ u : ℝ, 1 ≤ u ∧ u<z ∧ G u≤0 ∧ ∀ x∈Ioo u z, 0 < G x := by
  let S := Icc 1 z ∩ {x | G x≤0}
  have compact : IsCompact S := isCompact_Icc.inter_right (isClosed_le hg continuous_const)
  obtain ⟨u,hu,top⟩ := compact.exists_isGreatest (show S.Nonempty from ⟨1,⟨le_rfl,zge⟩,left⟩)
  have uz : u<z := lt_of_le_of_ne hu.1.2 fun eq => right.not_ge (eq ▸ hu.2)
  refine ⟨u,hu.1.1,uz,hu.2,?_⟩
  intro x hx
  by_contra! h
  exact hx.1.not_ge (top (show x∈S from ⟨⟨hu.1.1.trans hx.1.le,hx.2.le⟩,h⟩))

lemma window {A : Set ℝ} (fin : ∃ s : Finset (ℝ×ℝ), A=⋃p∈s,Icc p.1 p.2)
    (least : IsLeast A 1) (sf : ∀ a∈A,∀ b∈A,a+b∉A) (z : ℝ) (zge : 1≤z)
    (bad : z<volume.real (A∩Icc 0 (z-1))+volume.real (A∩Icc 0 z)+volume.real (A∩Icc 0 (z+1))) :
    ∃ x ε : ℝ, 1≤x ∧ 0<ε ∧
      (∀ y∈Icc (x-ε) (x+ε),y<volume.real (A∩Icc 0 (y-1))+volume.real (A∩Icc 0 y)+volume.real (A∩Icc 0 (y+1))) ∧
      Icc (x-1-ε) (x-1+ε) ⊆ A ∧ Icc (x+1-ε) (x+1+ε) ⊆ A := by
  classical
  obtain ⟨U,uo,ua,ae⟩ := openPart fin
  let F (t : ℝ) := volume.real (U ∩ Iic t)
  obtain ⟨cf,diff,zero,one,two⟩ := prefixMeasure uo (fun _ h => least.2 (ua h))
  have value (t : ℝ) : F t=volume.real (A∩Icc 0 t) := by
    have same : A∩Iic t=A∩Icc 0 t := by
      ext x; constructor
      · intro h; exact ⟨h.1,by linarith [least.2 h.1],h.2⟩
      · intro h; exact ⟨h.1,h.2.2⟩
    exact (measureReal_congr (ae_eq_set_inter ae (.rfl : Iic t =ᵐ[volume] Iic t))).trans (congrArg volume.real same)
  let G (t : ℝ) := F (t-1)+F t+F (t+1)-t
  have cg : Continuous G := ((cf.comp (continuous_id.sub continuous_const)).add cf |>.add
    (cf.comp (continuous_id.add continuous_const))).sub continuous_id
  have left : G 1≤0 := by
    change F (1-1)+F 1+F (1+1)-1≤0
    change F 0=0 at zero; change F 1=0 at one; change F 2≤1 at two
    norm_num [zero,one] <;> linarith
  have right : 0<G z := by dsimp only [G]; simp only [value]; linarith
  obtain ⟨u,u1,uz,ule,good⟩ := crossing cg zge left right
  let B (d : ℝ) := Ioo u z ∩ ((fun x : ℝ => x+d) ⁻¹' U)
  have measureB (d : ℝ) : volume.real (B d)=F (z+d)-F (u+d) := by
    rw [diff _ _ (by linarith)]
    have eq : B d=(fun x : ℝ => x+d) ⁻¹' (U∩Ioo (u+d) (z+d)) := by
      ext x; simp [B,mem_Ioo,and_comm]
    rw [eq,measureReal_def,measure_preimage_add_right]; rfl
  have bo (d : ℝ) : IsOpen (B d) := isOpen_Ioo.inter (uo.preimage (continuous_id.add continuous_const))
  have neig (d : ℝ) : Disjoint (B d) (B (d+1)) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact sf _ (ua hx.2) 1 least.1 (by simpa [add_assoc] using ua hy.2)
  have meeting : (B (-1) ∩ B 1).Nonempty := by
    by_contra neg
    have no : Disjoint (B (-1)) (B 1) := Set.disjoint_left.mpr fun x hx hy => neg ⟨x,hx,hy⟩
    have d1 : Disjoint (B (-1)) (B 0) := by simpa using neig (-1)
    have d2 : Disjoint (B 0) (B 1) := by simpa using neig 0
    have bounded (d : ℝ) : volume (B d)≠⊤ :=
      ne_of_lt ((measure_mono (show B d⊆Ioo u z from inter_subset_left)).trans_lt (by simp only [Real.volume_Ioo,ENNReal.ofReal_lt_top]))
    have bnd : volume.real ((B (-1)∪B 0)∪B 1) ≤ volume.real (Ioo u z) := by
      exact measureReal_mono (union_subset (union_subset inter_subset_left inter_subset_left) inter_subset_left) (by simp)
    rw [measureReal_union (disjoint_union_left.mpr ⟨no,d2⟩) (bo 1).measurableSet
      (measure_union_ne_top (bounded _) (bounded _)) (bounded _),
      measureReal_union d1 (bo 0).measurableSet (bounded _) (bounded _),
      measureB,measureB,measureB,Real.volume_real_Ioo_of_le uz.le] at bnd
    change F (u-1)+F u+F (u+1)-u≤0 at ule
    change 0<F (z-1)+F z+F (z+1)-z at right
    simp only [add_zero,←sub_eq_add_neg] at bnd
    linarith
  obtain ⟨x,hL,hR⟩ := meeting
  let O := (B (-1)∩B 1) ∩ {t | 0<G t}
  have ho : IsOpen O := ((bo _).inter (bo _)).inter (isOpen_lt continuous_const cg)
  obtain ⟨e,ep,ball⟩ := Metric.isOpen_iff.mp ho x (show x∈O from ⟨⟨hL,hR⟩,good x hL.1⟩)
  have close (t : ℝ) (lo : x-e/2≤t) (hi : t≤x+e/2) : t∈O := by
    apply ball; rw [Metric.mem_ball,Real.dist_eq,abs_lt]; constructor <;> linarith
  refine ⟨x,e/2,u1.trans hL.1.1.le,by positivity,?_,?_,?_⟩
  · intro y hy; have v := (close y hy.1 hy.2).2
    change 0<F (y-1)+F y+F (y+1)-y at v
    simp only [value] at v; linarith
  · intro y hy
    have h := (close (y+1) (by linarith [hy.1]) (by linarith [hy.2])).1.1.2
    apply ua; simpa using h
  · intro y hy
    have h := (close (y-1) (by linarith [hy.1]) (by linarith [hy.2])).1.2.2
    apply ua; simpa using h

end OMA.SumFreeWindows
theorem OMA.solution : OMA.R_Green3_green_3_R2_H1_R1.H2 := fun _ => OMA.SumFreeWindows.window
