import OMAStatements.S_mo_234762

open AffineSubspace Module Matrix

namespace OMA.S_mo_234762

private abbrev Space := EuclideanSpace ℝ (Fin 3)
private abbrev Plane := AffineSubspace ℝ Space

private theorem noncollinear_triple {p q r x : Space} {U V W : Plane}
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hU : p ∈ U ∧ q ∈ U) (hV : q ∈ V ∧ r ∈ V) (hW : p ∈ W ∧ r ∈ W)
    (hint : (U : Set Space) ∩ V ∩ W = {x}) :
    AffineIndependent ℝ ![p,q,r] := by
  rw [affineIndependent_iff_not_collinear_set]
  intro hc
  have hp' : p ∈ affineSpan ℝ ({q,r} : Set Space) :=
    hc.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hqr
  have hq' : q ∈ affineSpan ℝ ({p,r} : Set Space) :=
    hc.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hpr
  have hpv := affineSpan_pair_le_of_mem_of_mem hV.1 hV.2 hp'
  have hqw := affineSpan_pair_le_of_mem_of_mem hW.1 hW.2 hq'
  have hp : p ∈ (U : Set Space) ∩ V ∩ W := by exact ⟨⟨hU.1,hpv⟩,hW.1⟩
  have hq : q ∈ (U : Set Space) ∩ V ∩ W := by exact ⟨⟨hU.2,hV.1⟩,hqw⟩
  rw [hint, Set.mem_singleton_iff] at hp hq
  exact hpq (hp.trans hq.symm)

private theorem common_plane_line {T U : Plane} (hT : finrank ℝ T.direction=2)
    (hU : finrank ℝ U.direction=2) (hne : T ≠ U) {p q x : Space}
    (hpq : p ≠ q) (hpT : p∈T) (hqT : q∈T) (hxT : x∈T)
    (hpU : p∈U) (hqU : q∈U) (hxU : x∈U) :
    x ∈ affineSpan ℝ ({p,q} : Set Space) := by
  by_contra hn
  have ai := affineIndependent_of_ne_of_mem_of_mem_of_notMem hpq
    (left_mem_affineSpan_pair ℝ p q) (right_mem_affineSpan_pair ℝ p q) hn
  have eqT : affineSpan ℝ (Set.range ![p,q,x]) = T :=
    ai.affineSpan_eq_of_le_of_card_eq_finrank_add_one (affineSpan_le.mpr (by
      rintro y ⟨i,rfl⟩
      fin_cases i
      · exact hpT
      · exact hqT
      · exact hxT)) (by simp [hT])
  have eqU : affineSpan ℝ (Set.range ![p,q,x]) = U :=
    ai.affineSpan_eq_of_le_of_card_eq_finrank_add_one (affineSpan_le.mpr (by
      rintro y ⟨i,rfl⟩
      fin_cases i
      · exact hpU
      · exact hqU
      · exact hxU)) (by simp [hU])
  exact hne (eqT.symm.trans eqU)

private theorem not_on_three_lines {p q r x : Space} (hi : AffineIndependent ℝ ![p,q,r])
    (hx01 : x ∈ affineSpan ℝ ({p,q} : Set Space))
    (hx02 : x ∈ affineSpan ℝ ({p,r} : Set Space))
    (hx12 : x ∈ affineSpan ℝ ({q,r} : Set Space)) : False := by
  let v : Fin 3 → Space := ![p,q,r]
  have hh01 : x ∈ affineSpan ℝ (v '' ({0,1} : Set (Fin 3))) := by
    simpa [v, Set.image_pair] using hx01
  have hh02 : x ∈ affineSpan ℝ (v '' ({0,2} : Set (Fin 3))) := by
    simpa [v, Set.image_pair] using hx02
  have hh : x ∈ affineSpan ℝ (v '' (({0,1} : Set (Fin 3)) ∩ {0,2})) := by
    rw [← hi.inf_affineSpan_eq_affineSpan_inter]
    exact ⟨hh01,hh02⟩
  have he : (({0,1} : Set (Fin 3)) ∩ {0,2}) = {0} := by
    ext i
    fin_cases i <;> decide
  have hxp : x=p := by
    rw [he, Set.image_singleton, mem_affineSpan_singleton] at hh
    simpa [v] using hh
  have hp' : v 0 ∈ affineSpan ℝ (v '' ({1,2} : Set (Fin 3))) := by
    simpa [v, Set.image_pair, hxp] using hx12
  have hwrong := (hi.mem_affineSpan_iff 0 ({1,2} : Set (Fin 3))).mp hp'
  exact (by decide : (0 : Fin 3) ∉ ({1,2} : Set (Fin 3))) hwrong

/-- Translate three points of a plane by a point outside it to get an independent family. -/
private theorem translate_independent {T : Plane} {p q r x : Space}
    (hi : AffineIndependent ℝ ![p,q,r]) (hp : p∈T) (hq : q∈T) (hr : r∈T)
    (hx : x∉T) : LinearIndependent ℝ ![p-x,q-x,r-x] := by
  let v : Fin 4 → Space := ![x,p,q,r]
  let e := finSuccAboveEquiv (0 : Fin 4)
  have hc : (fun i : Fin 3 => v (e i)) = ![p,q,r] := by
    funext i
    fin_cases i <;> rfl
  have hi' : AffineIndependent ℝ (fun i : {i : Fin 4 // i ≠ 0} => v i) := by
    rw [← affineIndependent_equiv e]
    change AffineIndependent ℝ (fun i : Fin 3 => v (e i))
    rwa [hc]
  have hno : v 0 ∉ affineSpan ℝ (v '' {i | i ≠ 0}) := by
    intro hg
    apply hx
    refine affineSpan_le.mpr ?_ hg
    rintro y ⟨i,i_ne,rfl⟩
    fin_cases i
    · exfalso
      exact i_ne rfl
    · exact hp
    · exact hq
    · exact hr
  have ha := hi'.affineIndependent_of_notMem_span hno
  have hl := (affineIndependent_iff_linearIndependent_vsub ℝ v (0 : Fin 4)).mp ha
  rw [← linearIndependent_equiv e] at hl
  change LinearIndependent ℝ (fun i : Fin 3 => v (e i) - x) at hl
  convert hl using 1
  funext i
  fin_cases i <;> rfl

private noncomputable def detAt (b : Basis (Fin 3) ℝ Space) (p x y z : Space) : ℝ :=
  b.det ![x-p,y-p,z-p]

private theorem detAt_plane (b : Basis (Fin 3) ℝ Space) (U : Plane)
    (hd : finrank ℝ U.direction=2) {p x y z : Space}
    (hp : p∈U) (hx : x∈U) (hy : y∈U) (hz : z∈U) :
    detAt b p x y z=0 := by
  unfold detAt
  apply b.det.map_linearDependent
  intro hli
  have hmem : ∀ i : Fin 3, ![x-p,y-p,z-p] i ∈ U.direction := by
    intro i
    fin_cases i
    · exact U.vsub_mem_direction hx hp
    · exact U.vsub_mem_direction hy hp
    · exact U.vsub_mem_direction hz hp
  have hli' : LinearIndependent ℝ (fun i => (⟨![x-p,y-p,z-p] i,hmem i⟩ : U.direction)) :=
    LinearIndependent.of_comp U.direction.subtype hli
  have hc := hli'.fintype_card_le_finrank
  simp [hd] at hc

private theorem detAt_independent (b : Basis (Fin 3) ℝ Space) {p x y z : Space}
    (hl : LinearIndependent ℝ ![x-p,y-p,z-p]) : detAt b p x y z ≠ 0 := by
  let b' := basisOfLinearIndependentOfCardEqFinrank hl (by simp)
  have hu : IsUnit (b.det b') := b.isUnit_det b'
  rw [show ⇑b' = ![x-p,y-p,z-p] from coe_basisOfLinearIndependentOfCardEqFinrank _ _] at hu
  exact hu.ne_zero

private theorem detAt_coordinates (b : Basis (Fin 3) ℝ Space) (p x y z : Space) :
    let a := b.equivFun (x-p)
    let c := b.equivFun (y-p)
    let d := b.equivFun (z-p)
    detAt b p x y z =
      a 0*(c 1*d 2-c 2*d 1)-a 1*(c 0*d 2-c 2*d 0)+a 2*(c 0*d 1-c 1*d 0) := by
  dsimp only
  unfold detAt
  rw [Basis.det_apply, ← Matrix.det_transpose, Matrix.det_fin_three]
  simp [Basis.toMatrix_apply, Basis.equivFun_apply]
  ring

private theorem coplanar_of_detAt_zero (b : Basis (Fin 3) ℝ Space) {p x y z : Space}
    (hd : detAt b p x y z=0) : Coplanar ℝ ({p,x,y,z} : Set Space) := by
  let v : Fin 4 → Space := ![p,x,y,z]
  have hr : Set.range v = ({p,x,y,z} : Set Space) := by
    ext t
    simp [v, Matrix.range_cons, or_left_comm, or_comm, or_assoc]
  rw [coplanar_iff_finrank_le_two, ← hr,
    finrank_vectorSpan_le_iff_not_affineIndependent ℝ v (by decide : Fintype.card (Fin 4)=2+2)]
  intro hi
  have hl := (affineIndependent_iff_linearIndependent_vsub ℝ v (0 : Fin 4)).mp hi
  rw [← linearIndependent_equiv (finSuccAboveEquiv (0 : Fin 4))] at hl
  change LinearIndependent ℝ (fun i : Fin 3 => v ((finSuccAboveEquiv (0 : Fin 4)) i)-p) at hl
  have hv : (fun i : Fin 3 => v ((finSuccAboveEquiv (0 : Fin 4)) i)-p) =
      ![x-p,y-p,z-p] := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at hl
  exact detAt_independent b hl hd

private def det3 (x y z : Fin 3 → ℝ) : ℝ :=
  x 0*(y 1*z 2-y 2*z 1)-x 1*(y 0*z 2-y 2*z 0)+x 2*(y 0*z 1-y 1*z 0)

private theorem coordinates_det (b : Basis (Fin 3) ℝ Space) (q p x y z : Space) :
    let C (v : Space) := b.equivFun (v-q)
    detAt b p x y z = det3 (C x-C p) (C y-C p) (C z-C p) := by
  dsimp only
  rw [detAt_coordinates]
  simp only [det3, ← map_sub, sub_sub_sub_cancel_right]

/-- The determinant identity for the three shared planes after taking coordinates at Q012. -/
private theorem determinant_identity (a b c d e f u v w : ℝ)
    (hsum : u+v+w=1) (hu : u≠0) (hv : v≠0) (hw : w≠0)
    (hx : 1-a-b≠0) (hy : 1-c-d≠0) (hz : 1-e-f≠0)
    (h03 : det3 ![a-1,b,0] ![c-1,0,d] ![u-1,v,w]=0)
    (h13 : det3 ![a,b-1,0] ![0,e-1,f] ![u,v-1,w]=0)
    (h23 : det3 ![c,0,d-1] ![0,e,f-1] ![u,v,w-1]=0) :
    det3 ![a,b,0] ![c,0,d] ![0,e,f]=0 := by
  simp [det3] at h03 h13 h23 ⊢
  let A := 1-a-b
  let B := 1-c-d
  let C := 1-e-f
  have hA : A≠0 := hx
  have hB : B≠0 := hy
  have hC : C≠0 := hz
  have g1 : A*d*v+B*b*w=0 := by
    dsimp [A,B]
    linear_combination h03 - b*d*hsum
  have g2 : C*a*w+A*f*u=0 := by
    dsimp [C,A]
    linear_combination -h13 - a*f*hsum
  have g3 : C*c*v+B*e*u=0 := by
    dsimp [C,B]
    linear_combination h23 - c*e*hsum
  have hprod : A*B*C*u*v*w * (a*d*e+b*c*f)=0 := by
    linear_combination (A*d*v)*(B*e*u)*g2 - (A*f*u)*(B*e*u)*g1 +
      (A*f*u)*(B*b*w)*g3
  have hn : A*B*C*u*v*w ≠ 0 := by positivity
  have h := (mul_eq_zero.mp hprod).resolve_left hn
  linear_combination -h

end OMA.S_mo_234762

open OMA.S_mo_234762

set_option maxHeartbeats 1200000 in
theorem OMA.solution : type_of% @OMA.S_mo_234762.main := by
  intro P σ S Q hσ hP hPinj _ hS hQ
  have triple (i j k : Fin 4) (hij : i<j) (hjk : j<k) :
      AffineIndependent ℝ ![P i,P j,P k] := by
    have hik := lt_trans hij hjk
    exact noncollinear_triple (hPinj.ne hij.ne) (hPinj.ne hik.ne) (hPinj.ne hjk.ne)
      ⟨(hS i j hij.ne).2.1,(hS i j hij.ne).2.2.1⟩
      ⟨(hS j k hjk.ne).2.1,(hS j k hjk.ne).2.2.1⟩
      ⟨(hS i k hik.ne).2.1,(hS i k hik.ne).2.2.1⟩ (hQ i j k hij hjk)
  have qMem (i j k : Fin 4) (hij : i<j) (hjk : j<k) :
      Q i j k∈S i j ∧ Q i j k∈S j k ∧ Q i j k∈S i k := by
    have h : Q i j k ∈ (S i j : Set Space) ∩ S j k ∩ S i k := by
      rw [hQ i j k hij hjk]
      exact Set.mem_singleton _
    exact ⟨h.1.1,h.1.2,h.2⟩
  have qOutside (i j k : Fin 4) (hij : i<j) (hjk : j<k) : Q i j k∉σ := by
    intro h
    have hik := lt_trans hij hjk
    have hmem := qMem i j k hij hjk
    have toLine (s t : Fin 4) (hst : s<t) (hmem' : Q i j k∈S s t) :
        Q i j k∈affineSpan ℝ ({P s,P t} : Set Space) :=
      common_plane_line hσ (hS s t hst.ne).1 (hS s t hst.ne).2.2.2.symm
        (hPinj.ne hst.ne) (hP s) (hP t) h (hS s t hst.ne).2.1 (hS s t hst.ne).2.2.1 hmem'
    exact not_on_three_lines (triple i j k hij hjk) (toLine i j hij hmem.1)
      (toLine i k hik hmem.2.2) (toLine j k hjk hmem.2.1)
  let q := Q 0 1 2
  let X := Q 0 1 3
  let Y := Q 0 2 3
  let Z := Q 1 2 3
  have qm : q∈S 0 1 ∧ q∈S 1 2 ∧ q∈S 0 2 := qMem 0 1 2 (by decide) (by decide)
  have Xm : X∈S 0 1 ∧ X∈S 1 3 ∧ X∈S 0 3 := qMem 0 1 3 (by decide) (by decide)
  have Ym : Y∈S 0 2 ∧ Y∈S 2 3 ∧ Y∈S 0 3 := qMem 0 2 3 (by decide) (by decide)
  have Zm : Z∈S 1 2 ∧ Z∈S 2 3 ∧ Z∈S 1 3 := qMem 1 2 3 (by decide) (by decide)
  have hq : q∉σ := qOutside 0 1 2 (by decide) (by decide)
  have hi := triple 0 1 2 (by decide) (by decide)
  have hli := translate_independent hi (hP 0) (hP 1) (hP 2) hq
  let B : Basis (Fin 3) ℝ Space := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have basePoint : ⇑B = ![P 0-q,P 1-q,P 2-q] :=
    coe_basisOfLinearIndependentOfCardEqFinrank _ _
  let C (x : Space) := B.equivFun (x-q)
  have Cq : C q = 0 := by simp [C]
  have CP (i : Fin 3) : C (P i.castSucc) = fun j => if i=j then 1 else 0 := by
    have h : P i.castSucc-q = B i := by
      rw [congrFun basePoint i]
      fin_cases i <;> rfl
    unfold C
    rw [h]
    exact funext (B.equivFun_self i)
  have C0 : C (P 0) = ![1,0,0] := by
    funext i
    have h := congrFun (CP 0) i
    fin_cases i <;> exact h
  have C1 : C (P 1) = ![0,1,0] := by
    funext i
    have h := congrFun (CP 1) i
    fin_cases i <;> exact h
  have C2 : C (P 2) = ![0,0,1] := by
    funext i
    have h := congrFun (CP 2) i
    fin_cases i <;> exact h
  have detC (p x y z : Space) :
      detAt B p x y z = det3 (C x-C p) (C y-C p) (C z-C p) :=
    coordinates_det B q p x y z
  have height_ne (x : Space) (hout : x∉σ) : 1-C x 0-C x 1-C x 2≠0 := by
    intro hh
    have hn := detAt_independent B (translate_independent hi (hP 0) (hP 1) (hP 2) hout)
    apply hn
    rw [detC, C0,C1,C2]
    simp [det3, Pi.sub_apply]
    linear_combination hh
  have hsum : C (P 3) 0+C (P 3) 1+C (P 3) 2=1 := by
    have h := detAt_plane B σ hσ (hP 0) (hP 1) (hP 2) (hP 3)
    rw [detC,C0,C1,C2] at h
    simp [det3, Pi.sub_apply] at h
    linear_combination h
  have hu : C (P 3) 0≠0 := by
    have h := detAt_independent B
      (translate_independent (triple 1 2 3 (by decide) (by decide)) (hP 1) (hP 2) (hP 3) hq)
    rw [detC,Cq,C1,C2] at h
    simpa [det3] using h
  have hv : C (P 3) 1≠0 := by
    have h := detAt_independent B
      (translate_independent (triple 0 2 3 (by decide) (by decide)) (hP 0) (hP 2) (hP 3) hq)
    rw [detC,Cq,C0,C2] at h
    simpa [det3] using h
  have hw : C (P 3) 2≠0 := by
    have h := detAt_independent B
      (translate_independent (triple 0 1 3 (by decide) (by decide)) (hP 0) (hP 1) (hP 3) hq)
    rw [detC,Cq,C0,C1] at h
    simpa [det3] using h
  have h01 := hS 0 1 (by decide)
  have h02 := hS 0 2 (by decide)
  have h12 := hS 1 2 (by decide)
  have CX0 : C X 2=0 := by
    have h := detAt_plane B (S 0 1) h01.1 qm.1 h01.2.1 h01.2.2.1 Xm.1
    rw [detC,Cq,C0,C1] at h
    simpa [det3] using h
  have CY0 : C Y 1=0 := by
    have h := detAt_plane B (S 0 2) h02.1 qm.2.2 h02.2.1 h02.2.2.1 Ym.1
    rw [detC,Cq,C0,C2] at h
    simpa [det3] using h
  have CZ0 : C Z 0=0 := by
    have h := detAt_plane B (S 1 2) h12.1 qm.2.1 h12.2.1 h12.2.2.1 Zm.1
    rw [detC,Cq,C1,C2] at h
    simpa [det3] using h
  have CX : C X = ![C X 0,C X 1,0] := by
    funext i
    fin_cases i <;> simp [CX0]
  have CY : C Y = ![C Y 0,0,C Y 2] := by
    funext i
    fin_cases i <;> simp [CY0]
  have CZ : C Z = ![0,C Z 1,C Z 2] := by
    funext i
    fin_cases i <;> simp [CZ0]
  have hx : 1-C X 0-C X 1≠0 := by
    simpa [CX0] using height_ne X (qOutside 0 1 3 (by decide) (by decide))
  have hy : 1-C Y 0-C Y 2≠0 := by
    simpa [CY0] using height_ne Y (qOutside 0 2 3 (by decide) (by decide))
  have hz : 1-C Z 1-C Z 2≠0 := by
    simpa [CZ0] using height_ne Z (qOutside 1 2 3 (by decide) (by decide))
  have hs03 := hS 0 3 (by decide)
  have hs13 := hS 1 3 (by decide)
  have hs23 := hS 2 3 (by decide)
  have h03 := detAt_plane B (S 0 3) hs03.1 hs03.2.1 Xm.2.2 Ym.2.2 hs03.2.2.1
  have h13 := detAt_plane B (S 1 3) hs13.1 hs13.2.1 Xm.2.1 Zm.2.2 hs13.2.2.1
  have h23 := detAt_plane B (S 2 3) hs23.1 hs23.2.1 Ym.2.1 Zm.2.1 hs23.2.2.1
  rw [detC,C0] at h03
  rw [detC,C1] at h13
  rw [detC,C2] at h23
  apply coplanar_of_detAt_zero B
  rw [detC,Cq,sub_zero,sub_zero,sub_zero,CX,CY,CZ]
  apply determinant_identity _ _ _ _ _ _ _ _ _ hsum hu hv hw hx hy hz
  · simpa [det3, Pi.sub_apply, CX0,CY0,CZ0] using h03
  · simpa [det3, Pi.sub_apply, CX0,CY0,CZ0] using h13
  · simpa [det3, Pi.sub_apply, CX0,CY0,CZ0] using h23
