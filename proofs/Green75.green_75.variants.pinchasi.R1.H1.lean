import OMAReductions.R_Green75_green_75_variants_pinchasi_R1
import Mathlib

open Green75 Finset

theorem OMA.solution : OMA.R_Green75_green_75_variants_pinchasi_R1.H1 := by
  classical
  intro X
  let bad := (X ×ˢ X).image (fun z ↦ (z.2.1 - z.1.1) / (z.1.2 - z.2.2))
  obtain ⟨t,ht⟩ := bad.exists_notMem
  let e : (ℝ × ℝ) ↪ (ℝ × ℝ) :=
    ⟨fun p ↦ (p.1+t*p.2,p.2), by
      intro a b hab
      have hy := congrArg Prod.snd hab
      change a.2 = b.2 at hy
      have hx := congrArg Prod.fst hab
      change a.1+t*a.2 = b.1+t*b.2 at hx
      exact Prod.ext (by rw [hy] at hx; linarith) hy⟩
  refine ⟨e,?_,?_⟩
  · intro a ha b hb hab
    obtain ⟨p,hp,rfl⟩ := mem_map.mp ha
    obtain ⟨q,hq,rfl⟩ := mem_map.mp hb
    change p.1+t*p.2 = q.1+t*q.2 at hab
    by_cases hy : p.2 = q.2
    · exact congrArg e (Prod.ext (by rw [hy] at hab; linarith) hy)
    · exfalso
      apply ht
      apply mem_image.mpr
      refine ⟨(p,q),mem_product.mpr ⟨hp,hq⟩,?_⟩
      exact (div_eq_iff (sub_ne_zero.mpr hy)).2 (by nlinarith)
  · intro p q
    have hc (x : ℝ × ℝ) : cross (e p) (e q) (e x) = cross p q x := by
      change ((q.1+t*q.2)-(p.1+t*p.2))*(x.2-p.2) - (q.2-p.2)*((x.1+t*x.2)-(p.1+t*p.2)) =
        (q.1-p.1)*(x.2-p.2)-(q.2-p.2)*(x.1-p.1)
      ring
    simp [imbalance,leftCount,rightCount,filter_map,Function.comp_def,hc]

