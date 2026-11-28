import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H2_R2

-- Credit: @mattdorman
/-! # Eight finite three-slice seed ranks

The odd sharp-boundary theorem gives generic complex rank 23 in format
3 × 14 × 18. For the other seven formats, the normal equations reduce
to finite matrices over the field of order 251. Kernel-checked minors
give spanning tangent configurations, and the dimension count fixes
the exact generic rank. The four largest certificates are checked one
hub at a time where needed.
-/

namespace CriticalThreeQuotient

/-- A matrix with `r-b` rows has room in its kernel for a split injection
from `K^b`. The matrix `L` recovers the coordinates of that injection. -/
lemma kernel_frame {K : Type*} [Field K] {r b : ℕ} (hb : b ≤ r)
    (P : Matrix (Fin (r-b)) (Fin r) K) :
    ∃ Y : Matrix (Fin r) (Fin b) K, ∃ L : Matrix (Fin b) (Fin r) K,
      P * Y = 0 ∧ L * Y = 1 := by
  classical
  let F := P.mulVecLin
  have dims : Module.finrank K F.range + Module.finrank K F.ker = r := by
    simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using
      F.finrank_range_add_finrank_ker
  have room : Module.finrank K (Fin b → K) ≤ Module.finrank K F.ker := by
    rw [Module.finrank_fintype_fun_eq_card,Fintype.card_fin]
    have height : Module.finrank K F.range ≤ r-b := by
      simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using F.range.finrank_le
    omega
  obtain ⟨g,hg⟩ := finrank_le_iff_exists_linearMap.mp room
  let f := F.ker.subtype.comp g
  have injective : Function.Injective f := Subtype.val_injective.comp hg
  obtain ⟨L,hL⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr injective)
  refine ⟨LinearMap.toMatrix' f,LinearMap.toMatrix' L,?_,?_⟩
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul,Matrix.toLin'_toMatrix',map_zero]
    change F.comp f = 0
    apply LinearMap.ext
    intro v
    exact (g v).property
  · rw [← LinearMap.toMatrix'_comp,hL,LinearMap.toMatrix'_id]

/-- Kernel frames for the two relation matrices faithfully represent every
rectangular matrix by left and right multiplication. -/
lemma kernel_frames {K : Type*} [Field K] {r b n : ℕ} (hb : b ≤ r) (hn : n ≤ r)
    (P : Matrix (Fin (r-b)) (Fin r) K) (Q : Matrix (Fin (r-n)) (Fin r) K) :
    ∃ Y : Matrix (Fin r) (Fin b) K, ∃ Z : Matrix (Fin r) (Fin n) K,
      P * Y = 0 ∧ Q * Z = 0 ∧
      Function.Injective (fun M : Matrix (Fin b) (Fin n) K => Y * M * Z.transpose) := by
  obtain ⟨Y,L,pY,left⟩ := kernel_frame hb P
  obtain ⟨Z,R,qZ,right⟩ := kernel_frame hn Q
  have recover (M : Matrix (Fin b) (Fin n) K) :
      L * (Y * M * Z.transpose) * R.transpose = M := by
    calc
      _ = (L * Y) * M * (R * Z).transpose := by simp only [Matrix.transpose_mul,Matrix.mul_assoc]
      _ = M := by rw [left,right,Matrix.transpose_one,Matrix.one_mul,Matrix.mul_one]
  refine ⟨Y,Z,pY,qZ,fun A B he => ?_⟩
  exact (recover A).symm.trans ((congrArg (fun C => L * C * R.transpose) he).trans (recover B))

end CriticalThreeQuotient

namespace CriticalThreeQuotient

/-- A commutator certificate specified only by its relation matrices yields
two kernel frames and a spanning tangent at the prescribed first-mode factors. -/
lemma tangent_of_kernel_commutators {K : Type*} [Field K] {b n r : ℕ}
    (hb : b ≤ r) (hn : n ≤ r) (l m : Fin r → K) (distinct : Function.Injective l)
    (P : Matrix (Fin (r-b)) (Fin r) K) (Q : Matrix (Fin (r-n)) (Fin r) K)
    (exactPair : ∀ E : Fin r → Fin r → K,
      (∀ u t, ∑ s, P u s*((l s-l t)*E s t) = 0) →
      (∀ u t, ∑ s, P u s*((m s-m t)*E s t) = 0) →
      (∀ v s, ∑ t, ((l s-l t)*E s t)*Q v t = 0) →
      (∀ v s, ∑ t, ((m s-m t)*E s t)*Q v t = 0) →
      ∀ s t, s≠t → E s t=0) :
    ∃ Y : Fin r → Fin b → K, ∃ Z : Fin r → Fin n → K,
      let x (s : Fin r) : Fin 3 → K := ![1,l s,m s]
      ∀ T : Fin 3 → Fin b → Fin n → K, ∃ u : Fin r → Fin 3 → K,
        ∃ v : Fin r → Fin b → K, ∃ w : Fin r → Fin n → K, ∀ i j k,
          T i j k=∑ t, (u t i*(Y t j*Z t k) + x t i*(v t j*Z t k) + x t i*(Y t j*w t k)) := by
  obtain ⟨Y,Z,pY,qZ,embed⟩ := kernel_frames hb hn P Q
  exact ⟨Y,Z,tangent_of_commutators l m distinct Y Z P Q pY qZ embed exactPair⟩

end CriticalThreeQuotient

namespace CriticalThreeCubic

/-- In a right-hand relation vanishing on the hub rows and their cubic
commutators, the four equations on a pair are equivalent to evaluation of
one scalar pole row. The coefficients do not depend on the sample column. -/
theorem right_pair_iff {I J K : Type*} [Fintype I] [Field K]
    (a p : I → K) (u v : K) (distinct : u≠v) (t : J → K) (S : I → J → K)
    (U V : J → K) (poles : ∀ j,t j+u+v≠0)
    (linear : ∀ j,U j+V j+∑ i,p i*S i j=0)
    (cubic : ∀ j,(u^2+u*t j+(t j)^2)*U j+(v^2+v*t j+(t j)^2)*V j+
      ∑ i,p i*(a i^2+a i*t j+(t j)^2)*S i j=0) :
    let C (s : K) (f : J → K) := fun j => (s^2+s*t j+(t j)^2)*f j
    let R := fun j => (∑ i,p i*(a i-u)*(a i-v)*S i j)/(t j+u+v)
    ∀ L : (J → K) →ₗ[K] K, (∀ i,L (S i)=0) → (∀ i,L (C (a i) (S i))=0) →
      ((L U=0 ∧ L V=0 ∧ L (C u U)=0 ∧ L (C v V)=0) ↔ L R=0) := by
  intro C R L hS hC
  have entries (j : J) := cubic_pair a p (fun i => S i j) u v (t j) (U j) (V j)
    (poles j) (linear j) (cubic j)
  have sumU : U+V+∑ i,p i • S i=0 := by
    funext j
    simpa only [Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using linear j
  have sumC : C u U+C v V+∑ i,p i • C (a i) (S i)=0 := by
    funext j
    simpa only [C,Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,mul_assoc] using cubic j
  have reduced : (u-v) • U=-(∑ i,(p i*(a i-v)) • S i)-R := by
    funext j
    simpa only [Pi.smul_apply,smul_eq_mul,Pi.sub_apply,Pi.neg_apply,Finset.sum_apply,R] using (entries j).1
  have reducedC : (u-v) • C u U=-(∑ i,(p i*(a i-v)) • C (a i) (S i))+
      (∑ i,(p i*(a i-u)*(a i-v)*(a i+(u+v))) • S i)+(u*v-(u+v)^2) • R := by
    funext j
    simpa only [Pi.smul_apply,smul_eq_mul,Pi.add_apply,Pi.neg_apply,Finset.sum_apply,C,R] using (entries j).2
  have sumU' := congrArg L sumU
  have sumC' := congrArg L sumC
  have reduced' := congrArg L reduced
  have reducedC' := congrArg L reducedC
  simp only [map_add,map_sum,map_smul,smul_eq_mul,map_zero,hS,hC,mul_zero,Finset.sum_const_zero,
    add_zero] at sumU' sumC'
  simp only [map_add,map_sum,map_smul,map_neg,map_sub,smul_eq_mul,hS,hC,mul_zero,
    Finset.sum_const_zero,neg_zero,zero_sub,zero_add] at reduced' reducedC'
  constructor
  · rintro ⟨hu,_,_,_⟩
    rw [hu,mul_zero] at reduced'
    exact neg_eq_zero.mp reduced'.symm
  · intro h
    rw [h,neg_zero] at reduced'
    rw [h,mul_zero] at reducedC'
    have hu := (mul_eq_zero.mp reduced').resolve_left (sub_ne_zero.mpr distinct)
    have hcu := (mul_eq_zero.mp reducedC').resolve_left (sub_ne_zero.mpr distinct)
    exact ⟨hu,by simpa only [hu,zero_add] using sumU',hcu,by simpa only [hcu,zero_add] using sumC'⟩

end CriticalThreeCubic

namespace CriticalThreeCubic

/-- The two points of a pair and its hub coefficients form a matrix row
on the physical sample labels. -/
theorem pair_relation_matrix {K I J A : Type*} [Field K] [Fintype A] [Fintype I]
    (hub : I→A) (left right : J→A) (p : J→I→K) :
    ∃ P : Matrix J A K, ∀ j, ∀ f : A→K,
      (∑ s, P j s*f s)=f (left j)+f (right j)+∑ i,p j i*f (hub i) := by
  classical
  let P : Matrix J A K := fun j s =>
    (if s=left j then 1 else 0)+(if s=right j then 1 else 0)+
    ∑ i, if s=hub i then p j i else 0
  refine ⟨P,?_⟩
  intro j f
  simp only [P,add_mul,Finset.sum_add_distrib,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,
    if_true,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

/-- If the diagonal entry in one row of a pair vanishes, eliminating the
other row gives its single weighted equation on the hub values. -/
theorem diagonal_row {K I : Type*} [Field K] [Fintype I] (a p S : I→K)
    (v t y : K) (lin : y+∑ i,p i*S i=0)
    (cub : (v^2+v*t+t^2)*y+∑ i,p i*(a i^2+a i*t+t^2)*S i=0) :
    (∑ i, p i*(a i-v)*(a i+v+t)*S i)=0 := by
  calc
    _=(∑ i, p i*(a i^2+a i*t+t^2)*S i)-(v^2+v*t+t^2)*(∑ i,p i*S i) := by
      rw [Finset.mul_sum,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _=0 := by linear_combination cub-(v^2+v*t+t^2)*lin

/-- Testing the two hub channels, one pole channel per pair, and the
physical diagonal equations suffices for injectivity of the two compressed
commutators, over any field. -/
theorem cubic_hub_kernel {K I J A V : Type*} [Field K] [Fintype I] [Fintype A]
    (t : A→K) (distinct : Function.Injective t) (hub : I→A) (left right : J→A)
    (cover : ∀ k, (∃ i,hub i=k) ∨ (∃ j,left j=k) ∨ ∃ j,right j=k)
    (separated : ∀ j,left j≠right j) (p : J→I→K) (Q : Matrix V A K)
    (poles : ∀ j k, t k+t (left j)+t (right j)≠0) (P : Matrix J A K)
    (row : ∀ j, ∀ f : A→K, (∑ s,P j s*f s)=f (left j)+f (right j)+∑ i,p j i*f (hub i)) :
    let a (i : I) := t (hub i)
    let u (j : J) := t (left j)
    let v (j : J) := t (right j)
    let R (j : J) (S : I→A→K) (k : A) := (∑ i,p j i*(a i-u j)*(a i-v j)*S i k)/(t k+u j+v j)
    (∀ S : I→A→K,
      (∀ i,S i (hub i)=0) →
      (∀ j,(∑ i,p j i*(a i-v j)*(a i+u j+v j)*S i (left j))=0) →
      (∀ j,(∑ i,p j i*(a i-u j)*(a i+u j+v j)*S i (right j))=0) →
      (∀ q i,(∑ k,S i k*Q q k)=0) →
      (∀ q i,(∑ k,(((t k)^2+a i*t k)*S i k)*Q q k)=0) →
      (∀ q j,(∑ k,R j S k*Q q k)=0) → S=0) →
    ∀ E : A→A→K,
      (∀ j k, (∑ s,P j s*((t s-t k)*E s k))=0) →
      (∀ j k, (∑ s,P j s*(((t s)^3-(t k)^3)*E s k))=0) →
      (∀ q s, (∑ k,((t s-t k)*E s k)*Q q k)=0) →
      (∀ q s, (∑ k,(((t s)^3-(t k)^3)*E s k)*Q q k)=0) →
      ∀ s k, s≠k → E s k=0 := by
  intro a u v R reduced E lB lC rB rC
  let B (s k : A) := (t s-t k)*E s k
  let C (s k : A) := ((t s)^2+t s*t k+(t k)^2)*B s k
  let S (i : I) := B (hub i)
  have diag (s : A) : B s s=0 := by simp [B]
  have factor (s k : A) : C s k=((t s)^3-(t k)^3)*E s k := by dsimp [C,B]; ring
  have lin (j : J) (k : A) : B (left j) k+B (right j) k+∑ i,p j i*S i k=0 :=
    (row j (fun s => B s k)).symm.trans (lB j k)
  have cub (j : J) (k : A) :
      ((u j)^2+u j*t k+(t k)^2)*B (left j) k+
      ((v j)^2+v j*t k+(t k)^2)*B (right j) k+
      ∑ i,p j i*((a i)^2+a i*t k+(t k)^2)*S i k=0 := by
    have z : (∑ s,P j s*C s k)=0 := by simp only [factor,lC j k]
    rw [row j] at z
    simpa only [C,S,u,v,a,mul_assoc] using z
  let L (q : V) : (A→K) →ₗ[K] K := ∑ k,(Q q k) • (LinearMap.proj k : (A→K) →ₗ[K] K)
  have readL (q : V) (f : A→K) : L q f=∑ k,f k*Q q k := by
    simp [L,LinearMap.sum_apply,mul_comm]
  have hB (q : V) (s : A) : L q (B s)=0 := (readL q _).trans (rB q s)
  have hC (q : V) (s : A) : L q (C s)=0 := by
    rw [readL]
    simp only [factor,rC q s]
  have allS : S=0 := by
    apply reduced
    · exact fun i => diag (hub i)
    · intro j
      have h := diagonal_row a (p j) (fun i => S i (left j)) (v j) (u j) (B (right j) (left j))
        (by simpa only [diag,zero_add] using lin j (left j))
        (by simpa only [diag,mul_zero,zero_add] using cub j (left j))
      simpa only [add_assoc,add_comm (v j) (u j)] using h
    · intro j
      exact diagonal_row a (p j) (fun i => S i (right j)) (u j) (v j) (B (left j) (right j))
        (by simpa only [diag,add_zero] using lin j (right j))
        (by simpa only [diag,mul_zero,add_zero] using cub j (right j))
    · exact fun q i => (readL q _).symm.trans (hB q (hub i))
    · intro q i
      have split : (fun k => ((t k)^2+a i*t k)*S i k)=C (hub i)-(a i)^2 • S i := by
        funext k
        change _=(((a i)^2+a i*t k+(t k)^2)*S i k)-(a i)^2*S i k
        ring
      rw [← readL,split,map_sub,map_smul,hC,hB q (hub i)]
      simp
    · intro q j
      have test := right_pair_iff a (p j) (u j) (v j) (distinct.ne (separated j)) t S
        (B (left j)) (B (right j)) (poles j) (lin j) (cub j) (L q)
        (fun i => hB q (hub i)) (fun i => hC q (hub i))
      apply (readL q _).symm.trans
      exact test.mp ⟨hB q _,hB q _,hC q _,hC q _⟩
  have s0 (i : I) (k : A) : S i k=0 := congrFun (congrFun allS i) k
  have pairZero (j : J) (k : A) : B (left j) k=0 ∧ B (right j) k=0 := by
    have h := (cubic_pair a (p j) (fun i => S i k) (u j) (v j) (t k)
      (B (left j) k) (B (right j) k) (poles j k) (lin j k) (cub j k)).1
    have hleft : B (left j) k=0 := by
      apply (mul_eq_zero.mp (show (u j-v j)*B (left j) k=0 by simpa only [s0,mul_zero,
        Finset.sum_const_zero,zero_div,neg_zero,sub_zero] using h)).resolve_left
      exact sub_ne_zero.mpr (distinct.ne (separated j))
    refine ⟨hleft,?_⟩
    simpa only [hleft,zero_add,s0,mul_zero,Finset.sum_const_zero,add_zero] using lin j k
  intro s k ne
  have zero : B s k=0 := by
    rcases cover s with ⟨i,rfl⟩ | ⟨j,rfl⟩ | ⟨j,rfl⟩
    · exact s0 i k
    · exact (pairZero j k).1
    · exact (pairZero j k).2
  exact (mul_eq_zero.mp zero).resolve_left (sub_ne_zero.mpr (distinct.ne ne))

end CriticalThreeCubic

namespace CriticalThreeCubic

/-- A reduced hub test constructs actual second and third frames whose
three-slice tangent spans at the literal first factors (1,t,t³). The two
right-hand hub channels and one scalar pole per pair suffice. -/
theorem tangent_of_hub_injectivity {K I : Type*} [Field K] [Fintype I] {b n r : ℕ}
    (hb : b≤r) (hn : n≤r) (t : Fin r→K) (distinct : Function.Injective t)
    (hub : I→Fin r) (left right : Fin (r-b)→Fin r)
    (cover : ∀ k, (∃ i,hub i=k) ∨ (∃ j,left j=k) ∨ ∃ j,right j=k)
    (separated : ∀ j,left j≠right j) (p : Fin (r-b)→I→K) (Q : Matrix (Fin (r-n)) (Fin r) K)
    (poles : ∀ j k, t k+t (left j)+t (right j)≠0) :
    let a (i : I) := t (hub i)
    let u (j : Fin (r-b)) := t (left j)
    let v (j : Fin (r-b)) := t (right j)
    let R (j : Fin (r-b)) (S : I→Fin r→K) (k : Fin r) :=
      (∑ i,p j i*(a i-u j)*(a i-v j)*S i k)/(t k+u j+v j)
    (∀ S : I→Fin r→K,
      (∀ i,S i (hub i)=0) →
      (∀ j,(∑ i,p j i*(a i-v j)*(a i+u j+v j)*S i (left j))=0) →
      (∀ j,(∑ i,p j i*(a i-u j)*(a i+u j+v j)*S i (right j))=0) →
      (∀ q i,(∑ k,S i k*Q q k)=0) →
      (∀ q i,(∑ k,(((t k)^2+a i*t k)*S i k)*Q q k)=0) →
      (∀ q j,(∑ k,R j S k*Q q k)=0) → S=0) →
    ∃ Y : Fin r→Fin b→K, ∃ Z : Fin r→Fin n→K,
      let x (s : Fin r) : Fin 3→K := ![1,t s,(t s)^3]
      ∀ T : Fin 3→Fin b→Fin n→K, ∃ a' : Fin r→Fin 3→K,
        ∃ w' : Fin r→Fin b→K, ∃ z' : Fin r→Fin n→K, ∀ i j k,
          T i j k=∑ s,(a' s i*(Y s j*Z s k)+x s i*(w' s j*Z s k)+x s i*(Y s j*z' s k)) := by
  intro a u v R reduced
  obtain ⟨P,prow⟩ := pair_relation_matrix hub left right p
  exact CriticalThreeQuotient.tangent_of_kernel_commutators hb hn t (fun s => (t s)^3) distinct P Q
    (cubic_hub_kernel t distinct hub left right cover separated p Q poles P prow reduced)

end CriticalThreeCubic

namespace CriticalThreeCubic

/-- The pole coefficients can be prescribed directly when the physical
hubs are disjoint from the paired samples. The two diagonal tests then
use exactly the residues Gᵢ(aᵢ+u+v)/(aᵢ−u) and Gᵢ(aᵢ+u+v)/(aᵢ−v). -/
theorem tangent_of_hub_residues {K I : Type*} [Field K] [Fintype I] {b n r : ℕ}
    (hb : b≤r) (hn : n≤r) (t : Fin r→K) (distinct : Function.Injective t)
    (hub : I→Fin r) (left right : Fin (r-b)→Fin r)
    (cover : ∀ k, (∃ i,hub i=k) ∨ (∃ j,left j=k) ∨ ∃ j,right j=k)
    (separated : ∀ j,left j≠right j) (awayLeft : ∀ i j,hub i≠left j) (awayRight : ∀ i j,hub i≠right j)
    (G : Fin (r-b)→I→K) (Q : Matrix (Fin (r-n)) (Fin r) K)
    (poles : ∀ j k, t k+t (left j)+t (right j)≠0) :
    let a (i : I) := t (hub i)
    let u (j : Fin (r-b)) := t (left j)
    let v (j : Fin (r-b)) := t (right j)
    (∀ S : I→Fin r→K,
      (∀ i,S i (hub i)=0) →
      (∀ j,(∑ i,(G j i*(a i+u j+v j)/(a i-u j))*S i (left j))=0) →
      (∀ j,(∑ i,(G j i*(a i+u j+v j)/(a i-v j))*S i (right j))=0) →
      (∀ q i,(∑ k,S i k*Q q k)=0) →
      (∀ q i,(∑ k,(((t k)^2+a i*t k)*S i k)*Q q k)=0) →
      (∀ q j,(∑ k,((∑ i,G j i*S i k)/(t k+u j+v j))*Q q k)=0) → S=0) →
    ∃ Y : Fin r→Fin b→K, ∃ Z : Fin r→Fin n→K,
      let x (s : Fin r) : Fin 3→K := ![1,t s,(t s)^3]
      ∀ T : Fin 3→Fin b→Fin n→K, ∃ a' : Fin r→Fin 3→K,
        ∃ w' : Fin r→Fin b→K, ∃ z' : Fin r→Fin n→K, ∀ i j k,
          T i j k=∑ s,(a' s i*(Y s j*Z s k)+x s i*(w' s j*Z s k)+x s i*(Y s j*z' s k)) := by
  intro a u v reduced
  let p (j : Fin (r-b)) (i : I) := G j i/((a i-u j)*(a i-v j))
  have l (i : I) (j : Fin (r-b)) : a i-u j≠0 := sub_ne_zero.mpr (distinct.ne (awayLeft i j))
  have h (i : I) (j : Fin (r-b)) : a i-v j≠0 := sub_ne_zero.mpr (distinct.ne (awayRight i j))
  have gain (j : Fin (r-b)) (i : I) : p j i*(a i-u j)*(a i-v j)=G j i := by
    dsimp [p]
    field_simp [l i j,h i j]
  have lw (j : Fin (r-b)) (i : I) : p j i*(a i-v j)*(a i+u j+v j)=G j i*(a i+u j+v j)/(a i-u j) := by
    rw [← gain j i]
    field_simp [l i j]
  have rw' (j : Fin (r-b)) (i : I) : p j i*(a i-u j)*(a i+u j+v j)=G j i*(a i+u j+v j)/(a i-v j) := by
    rw [← gain j i]
    field_simp [h i j]
  apply tangent_of_hub_injectivity hb hn t distinct hub left right cover separated p Q poles
  intro S dH dU dV rH rC rR
  refine reduced S dH (fun j => ?_) (fun j => ?_) rH rC (fun q j => ?_)
  · simpa only [← lw] using dU j
  · simpa only [← rw'] using dV j
  · have z := rR q j
    change (∑ k,((∑ i,p j i*(a i-u j)*(a i-v j)*S i k)/(t k+u j+v j))*Q q k)=0 at z
    simpa only [gain] using z

end CriticalThreeCubic

namespace CriticalThreeCubic

open Polynomial

/-- If deg T≤q, then multiplication by T+w carries degree-<n polynomials
to degree below n+q. Its values on n+q distinct nodes therefore determine
the product itself. A pole row belongs to the evaluation code exactly when
its numerator has a bounded-degree polynomial quotient. -/
theorem pole_iff_divides {K : Type*} [Field K] {q n r : ℕ} (size : n+q≤r)
    (T f : K[X]) (w : K) (degreeT : T.natDegree≤q) (degreeF : f.natDegree<n)
    (z : Fin r → K) (distinct : Function.Injective z) (regular : ∀ i,T.eval (z i)+w≠0) :
    (∃ g : K[X], g.natDegree<n ∧ ∀ i,g.eval (z i)=f.eval (z i)/(T.eval (z i)+w)) ↔
      ∃ g : K[X], g.natDegree<n ∧ f=(T+C w)*g := by
  constructor
  · rintro ⟨g,dg,node⟩
    refine ⟨g,dg,eq_of_natDegree_lt_card_of_eval_eq _ _ distinct ?_ ?_⟩
    · intro i
      rw [eval_mul,eval_add,eval_C,node]
      field_simp [regular i]
    · have plus : (T+C w).natDegree≤q :=
        (natDegree_add_le ..).trans (max_le degreeT (by simp))
      have bound : ((T+C w)*g).natDegree≤(T+C w).natDegree+g.natDegree := natDegree_mul_le
      rw [Fintype.card_fin]
      omega
  · rintro ⟨g,dg,eq⟩
    refine ⟨g,dg,fun i => ?_⟩
    rw [eq,eval_mul,eval_add,eval_C]
    field_simp [regular i]

end CriticalThreeCubic

namespace CriticalThreeCubic

open Polynomial

/-- The top coefficient on a distinct finite evaluation grid is a
barycentric sum of the values. -/
theorem top_moment {K : Type*} [Field K] {r : ℕ} (z : Fin r → K) (distinct : Function.Injective z)
    (f : K[X]) (degree : f.natDegree<r) :
    (∑ i : Fin r, f.eval (z i)/(∏ j ∈ (Finset.univ : Finset (Fin r)).erase i, (z i - z j)))=f.coeff (r-1) := by
  classical
  by_cases zero : f=0
  · simp [zero]
  have deg : f.degree < ((Finset.univ : Finset (Fin r)).card : WithBot ℕ) := by
    rw [degree_eq_natDegree zero,Finset.card_univ,Fintype.card_fin]
    exact_mod_cast degree
  simpa only [Finset.card_univ,Fintype.card_fin] using (Lagrange.coeff_eq_sum distinct.injOn deg).symm

/-- The r−n barycentric moments are an exact parity check for evaluation
of degree-<n polynomials at r distinct points over any field. -/
theorem evaluation_iff_moments {K : Type*} [Field K] {r n : ℕ} (hn : 0<n) (enough : n≤r)
    (z : Fin r → K) (distinct : Function.Injective z) (v : Fin r → K) :
    (∃ f : K[X], f.natDegree<n ∧ ∀ i,f.eval (z i)=v i) ↔
      ∀ j : Fin (r-n), ∑ i : Fin r, (z i^j.val*v i)/(∏ k ∈ (Finset.univ : Finset (Fin r)).erase i, (z i - z k))=0 := by
  classical
  constructor
  · rintro ⟨f,df,valid⟩ j
    have bound : (X^j.val*f).natDegree≤j.val+f.natDegree := by
      simpa only [natDegree_X_pow] using
        (natDegree_mul_le : ((X^j.val : K[X])*f).natDegree≤(X^j.val : K[X]).natDegree+f.natDegree)
    have id := top_moment z distinct (X^j.val*f) (by omega)
    rw [coeff_eq_zero_of_natDegree_lt (by omega : (X^j.val*f).natDegree < r-1)] at id
    simpa only [eval_mul,eval_pow,eval_X,valid] using id
  · intro vanishes
    let f := Lagrange.interpolate Finset.univ z v
    have valid (i : Fin r) : f.eval (z i)=v i :=
      Lagrange.eval_interpolate_at_node _ distinct.injOn (Finset.mem_univ i)
    refine ⟨f,?_,valid⟩
    by_cases zero : f=0
    · simpa only [zero,natDegree_zero] using hn
    have less : f.natDegree<r := by
      have h := Lagrange.degree_interpolate_lt v (s:=Finset.univ) distinct.injOn
      change f.degree < _ at h
      rw [degree_eq_natDegree zero,Finset.card_univ,Fintype.card_fin] at h
      exact_mod_cast h
    by_contra! large
    let j : Fin (r-n) := ⟨r-1-f.natDegree,by omega⟩
    have top : (X^j.val*f).natDegree=r-1 := by rw [natDegree_X_pow_mul _ zero]; dsimp [j]; omega
    have moment := top_moment z distinct (X^j.val*f) (by omega)
    have empty := vanishes j
    simp only [eval_mul,eval_pow,eval_X,valid] at moment
    rw [empty] at moment
    rw [←top,coeff_natDegree] at moment
    exact (leadingCoeff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ X_ne_zero) zero)) moment.symm

end CriticalThreeCubic

namespace CriticalThreeCubic

open Polynomial

/-- Distinct scalar translates of one polynomial are comaximal, regardless
of how either translate factors over the field. -/
theorem coprime_private_poles {K : Type*} [Field K] (T : K[X]) {a b : K} (distinct : a≠b) :
    IsCoprime (T+C a) (T+C b) := by
  let v := C ((a-b)⁻¹)
  refine ⟨v,-v,?_⟩
  calc
    v*(T+C a)+(-v)*(T+C b) = v*C (a-b) := by rw [map_sub]; ring
    _ = 1 := by dsimp only [v]; rw [← map_mul,inv_mul_cancel₀ (sub_ne_zero.mpr distinct),map_one]

/-- The node factors and all assigned pole polynomials divide jointly. -/
theorem private_factor_dvd {K I J : Type*} [Field K] [Fintype I] [Fintype J]
    (T : K[X]) (nodes : I → K) (poles : J → K)
    (node_inj : Function.Injective nodes) (pole_inj : Function.Injective poles)
    (disjoint : ∀ i j, T.eval (nodes i)+poles j≠0) (f : K[X])
    (roots : ∀ i, f.eval (nodes i)=0) (divs : ∀ j, T+C (poles j) ∣ f) :
    (∏ i, (X-C (nodes i)))*(∏ j, (T+C (poles j))) ∣ f := by
  have linear : (∏ i, (X-C (nodes i))) ∣ f := Fintype.prod_dvd_of_coprime
    (pairwise_coprime_X_sub_C node_inj) (fun i => dvd_iff_isRoot.mpr (roots i))
  have shifted : (∏ j, (T+C (poles j))) ∣ f := Fintype.prod_dvd_of_coprime
    (fun i j h => coprime_private_poles T (pole_inj.ne h)) divs
  have separate (i : I) (j : J) : IsCoprime (X-C (nodes i)) (T+C (poles j)) := by
    apply (prime_X_sub_C (nodes i)).coprime_iff_not_dvd.mpr
    intro h
    have bad := dvd_iff_isRoot.mp h
    change (T+C (poles j)).eval (nodes i)=0 at bad
    exact disjoint i j (by simpa only [eval_add,eval_C] using bad)
  exact (IsCoprime.prod_left (fun i _ => IsCoprime.prod_right (fun j _ => separate i j))).mul_dvd linear shifted

/-- With `T=X^q` of positive degree, the private product is monic of degree
`number of nodes + q * number of private poles`. -/
theorem private_factor_degree {K I J : Type*} [Field K] [Fintype I] [Fintype J]
    {q : ℕ} (hq : 0<q) (nodes : I → K) (poles : J → K) :
    let H : K[X] := (∏ i, (X-C (nodes i)))*(∏ j, (X^q+C (poles j)))
    H.Monic ∧ H.natDegree=Fintype.card I+q*Fintype.card J := by
  intro H
  have a := monic_prod_X_sub_C nodes Finset.univ
  have b := monic_prod_of_monic Finset.univ (fun j => X^q+C (poles j)) (fun j _ => monic_X_pow_add_C (poles j) hq.ne')
  refine ⟨a.mul b,?_⟩
  dsimp only [H]
  rw [natDegree_mul a.ne_zero b.ne_zero,natDegree_finsetProd_X_sub_C_eq_card,
    natDegree_prod_of_monic _ _ (fun j _ => monic_X_pow_add_C (poles j) hq.ne')]
  simp [Nat.mul_comm]

/-- This quotient degree formula includes the zero polynomial, whose
quotient is zero and whose natural degree is zero. -/
theorem private_quotient_polynomial {K I J : Type*} [Field K] [Fintype I] [Fintype J]
    {q : ℕ} (hq : 0<q) (nodes : I → K) (poles : J → K)
    (node_inj : Function.Injective nodes) (pole_inj : Function.Injective poles)
    (disjoint : ∀ i j, (nodes i)^q+poles j≠0) (f : K[X])
    (roots : ∀ i, f.eval (nodes i)=0) (divs : ∀ j, X^q+C (poles j) ∣ f) :
    let H : K[X] := (∏ i, (X-C (nodes i)))*(∏ j, (X^q+C (poles j)))
    ∃ Q : K[X], f=H*Q ∧ (Q=0 ↔ f=0) ∧ Q.natDegree=f.natDegree-(Fintype.card I+q*Fintype.card J) := by
  intro H
  obtain ⟨Q,repr⟩ := private_factor_dvd (X^q) nodes poles node_inj pole_inj
    (fun i j => by simpa only [eval_pow,eval_X] using disjoint i j) f roots divs
  change f=H*Q at repr
  obtain ⟨monic,degree⟩ := private_factor_degree hq nodes poles
  change H.Monic at monic
  change H.natDegree=Fintype.card I+q*Fintype.card J at degree
  have nonzero : H≠0 := monic.ne_zero
  have factors : Q=0 ↔ f=0 := by rw [repr]; simp [nonzero]
  refine ⟨Q,repr,factors,?_⟩
  by_cases zero : Q=0
  · simp only [zero,factors.mp zero,natDegree_zero,Nat.zero_sub]
  · have add := congrArg Polynomial.natDegree repr
    rw [natDegree_mul monic.ne_zero zero,degree] at add
    omega

/-- Evaluation uses exactly `d` quotient coefficients when the allowed
degree is less than the private-factor degree plus `d`. -/
theorem private_quotient {K : Type*} [Field K] {m g n d q : ℕ} (hq : 0<q) (hd : 0<d)
    (size : m+q*g+d=n) (nodes : Fin m → K) (poles : Fin g → K)
    (node_inj : Function.Injective nodes) (pole_inj : Function.Injective poles)
    (disjoint : ∀ i j, (nodes i)^q+poles j≠0) (f : K[X]) (deg : f.natDegree<n)
    (roots : ∀ i, f.eval (nodes i)=0) (divs : ∀ j, X^q+C (poles j) ∣ f) :
    ∃ a : Fin d → K, ∀ z : K, f.eval z = (∏ j, (z-nodes j))*(∏ j, (z^q+poles j)) *
      (∑ k, a k*z^k.val) := by
  obtain ⟨Q,repr,_,degree⟩ := private_quotient_polynomial hq nodes poles node_inj pole_inj disjoint f roots divs
  rw [Fintype.card_fin,Fintype.card_fin] at degree
  have short : Q.natDegree<d := by omega
  refine ⟨fun k => Q.coeff k.val,?_⟩
  intro z
  rw [repr,eval_mul,eval_mul,eval_prod,eval_prod]
  simp only [eval_sub,eval_add,eval_C,eval_X,eval_pow]
  rw [Q.eval_eq_sum_range' short z,← Fin.sum_univ_eq_sum_range]

end CriticalThreeCubic

namespace CriticalHigher.PrimeTangent

/-- An integral matrix surjective modulo a prime remains surjective over any
characteristic-zero field. Lift a right inverse entrywise: its product with the
original matrix has determinant congruent to one. -/
theorem integer_matrix_lift (K : Type*) [Field K] [CharZero K] {p : ℕ} [Fact p.Prime]
    {I J : Type*} [Fintype I] [Fintype J] (A : Matrix I J ℤ)
    (onto : Function.Surjective (A.map (Int.castRingHom (ZMod p))).mulVec) :
    Function.Surjective (A.map (Int.castRingHom K)).mulVec := by
  classical
  obtain ⟨b,right⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp onto
  let B : Matrix J I ℤ := fun j i => (b j i).val
  have reduction : B.map (Int.castRingHom (ZMod p))=b := by
    ext j i
    change (((b j i).val : ℤ) : ZMod p)=b j i
    simp
  let D := A*B
  have mod_det : (Int.castRingHom (ZMod p)) D.det=1 := by
    rw [RingHom.map_det,RingHom.mapMatrix_apply,show D=A*B from rfl,Matrix.map_mul,reduction,right,Matrix.det_one]
  have nonzero : D.det≠0 := by
    intro zero
    rw [zero,map_zero] at mod_det
    exact zero_ne_one mod_det
  have unit : IsUnit (D.map (Int.castRingHom K)).det := by
    apply isUnit_iff_ne_zero.mpr
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    change (D.det : K)≠0
    exact_mod_cast nonzero
  have product_onto := Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr unit)
  intro target
  obtain ⟨u,hu⟩ := product_onto target
  refine ⟨(B.map (Int.castRingHom K)).mulVec u,?_⟩
  rw [Matrix.mulVec_mulVec,← Matrix.map_mul]
  exact hu

/-- Fixed factors and unrestricted variations in a three-factor tangent space,
encoded as a single finite matrix over the same field. -/
theorem tangent_iff_matrix {K A B C P : Type*} [Field K] [Fintype A] [Fintype B] [Fintype C]
    [Fintype P] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (x : P → A → K) (y : P → B → K) (z : P → C → K)
    (M : Matrix ((A × B) × C) (P × (A ⊕ (B ⊕ C))) K)
    (entry : ∀ i j k t s, M ((i,j),k) (t,s) =
      s.elim (fun i' => if i'=i then y t j*z t k else 0)
        (Sum.elim (fun j' => if j'=j then x t i*z t k else 0)
          (fun k' => if k'=k then x t i*y t j else 0))) :
    (∀ T : A → B → C → K, ∃ u : P → A → K, ∃ v : P → B → K, ∃ w : P → C → K,
      ∀ i j k, T i j k = ∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) ↔
    Function.Surjective M.mulVec := by
  have action (q : P × (A ⊕ (B ⊕ C)) → K) (i : A) (j : B) (k : C) :
      M.mulVec q ((i,j),k) = ∑ t, (q (t,.inl i)*(y t j*z t k) +
        x t i*(q (t,.inr (.inl j))*z t k) + x t i*(y t j*q (t,.inr (.inr k)))) := by
    change (∑ s, M ((i,j),k) s*q s)=_
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro t _
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
    simp [entry,ite_mul,Finset.sum_ite_eq']
    ring
  constructor
  · intro spanning T
    obtain ⟨u,v,w,hit⟩ := spanning (fun i j k => T ((i,j),k))
    let q : P × (A ⊕ (B ⊕ C)) → K := fun (t,s) => s.elim (u t) (Sum.elim (v t) (w t))
    refine ⟨q,?_⟩
    funext ⟨⟨i,j⟩,k⟩
    exact (action q i j k).trans (hit i j k).symm
  · intro onto T
    obtain ⟨q,hit⟩ := onto (fun row => T row.1.1 row.1.2 row.2)
    refine ⟨fun t i => q (t,.inl i),fun t j => q (t,.inr (.inl j)),fun t k => q (t,.inr (.inr k)),?_⟩
    intro i j k
    exact (congrFun hit ((i,j),k)).symm.trans (action q i j k)

end CriticalHigher.PrimeTangent

namespace CriticalHigher.PrimeTangent

private theorem integer_tangent_iff (K : Type*) [Field K] {A B C P : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype P] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (x : P → A → ℤ) (y : P → B → ℤ) (z : P → C → ℤ) :
    let M : Matrix ((A × B) × C) (P × (A ⊕ (B ⊕ C))) ℤ := fun row col =>
      col.2.elim (fun i => if i=row.1.1 then y col.1 row.1.2*z col.1 row.2 else 0)
        (Sum.elim (fun j => if j=row.1.2 then x col.1 row.1.1*z col.1 row.2 else 0)
          (fun k => if k=row.2 then x col.1 row.1.1*y col.1 row.1.2 else 0))
    (∀ T : A → B → C → K, ∃ u : P → A → K, ∃ v : P → B → K, ∃ w : P → C → K,
      ∀ i j k, T i j k = ∑ t, (u t i*((y t j : K)*(z t k : K)) +
        (x t i : K)*(v t j*(z t k : K)) + (x t i : K)*((y t j : K)*w t k))) ↔
      Function.Surjective (M.map (Int.castRingHom K)).mulVec := by
  intro M
  apply tangent_iff_matrix
  intro i j k t s
  change (Int.castRingHom K) (M ((i,j),k) (t,s)) = _
  rcases s with i' | j' | k'
  · by_cases h : i'=i <;> simp [M,h]
  · by_cases h : j'=j <;> simp [M,h]
  · by_cases h : k'=k <;> simp [M,h]

/-- Lift these fixed factor entries, using their canonical natural-number
representatives, into any field of characteristic zero. -/
theorem lift_over (K : Type*) [Field K] [CharZero K] {p : ℕ} [Fact p.Prime]
    {A B C P : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype P]
    (x : P → A → ZMod p) (y : P → B → ZMod p) (z : P → C → ZMod p)
    (span : ∀ T : A → B → C → ZMod p, ∃ u : P → A → ZMod p, ∃ v : P → B → ZMod p,
      ∃ w : P → C → ZMod p, ∀ i j k, T i j k =
        ∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) :
    ∀ T : A → B → C → K, ∃ u : P → A → K, ∃ v : P → B → K, ∃ w : P → C → K,
      ∀ i j k, T i j k = ∑ t, (u t i*(((y t j).val : K)*((z t k).val : K)) +
        ((x t i).val : K)*(v t j*((z t k).val : K)) + ((x t i).val : K)*(((y t j).val : K)*w t k)) := by
  classical
  let X (t : P) (i : A) : ℤ := (x t i).val
  let Y (t : P) (j : B) : ℤ := (y t j).val
  let Z (t : P) (k : C) : ℤ := (z t k).val
  have reduced := (integer_tangent_iff (ZMod p) X Y Z).mp (by
    simpa only [X,Y,Z,Int.cast_natCast,ZMod.natCast_zmod_val] using span)
  have full := (integer_tangent_iff K X Y Z).mpr (integer_matrix_lift K _ reduced)
  simpa only [X,Y,Z,Int.cast_natCast] using full

/-- The ordinary three-factor complex tangent at the integer representatives. -/
theorem lift {p a b n r : ℕ} [Fact p.Prime] (x : Fin r → Fin a → ZMod p)
    (y : Fin r → Fin b → ZMod p) (z : Fin r → Fin n → ZMod p)
    (span : ∀ T : Fin a → Fin b → Fin n → ZMod p, ∃ u : Fin r → Fin a → ZMod p,
      ∃ v : Fin r → Fin b → ZMod p, ∃ w : Fin r → Fin n → ZMod p, ∀ i j k,
        T i j k = ∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) :
    ∀ T : Fin a → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
      ∃ w : Fin r → Fin n → ℂ, ∀ i j k, T i j k =
        ∑ t, (u t i*(((y t j).val : ℂ)*((z t k).val : ℂ)) + ((x t i).val : ℂ)*(v t j*((z t k).val : ℂ)) +
          ((x t i).val : ℂ)*(((y t j).val : ℂ)*w t k)) :=
  lift_over ℂ x y z span

/-- Existence of an unrestricted modular witness suffices for `Spans`
at exactly the same dimensions and point count. -/
theorem exists_lift {p a b n r : ℕ} [Fact p.Prime]
    (witness : ∃ x : Fin r → Fin a → ZMod p, ∃ y : Fin r → Fin b → ZMod p, ∃ z : Fin r → Fin n → ZMod p,
      ∀ T : Fin a → Fin b → Fin n → ZMod p, ∃ u : Fin r → Fin a → ZMod p, ∃ v : Fin r → Fin b → ZMod p,
        ∃ w : Fin r → Fin n → ZMod p, ∀ i j k, T i j k =
          ∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k))) :
    ∃ x : Fin r → Fin a → ℂ, ∃ y : Fin r → Fin b → ℂ, ∃ z : Fin r → Fin n → ℂ,
      ∀ T : Fin a → Fin b → Fin n → ℂ, ∃ u : Fin r → Fin a → ℂ, ∃ v : Fin r → Fin b → ℂ,
        ∃ w : Fin r → Fin n → ℂ, ∀ i j k, T i j k =
          ∑ t, (u t i*(y t j*z t k)+x t i*(v t j*z t k)+x t i*(y t j*w t k)) := by
  obtain ⟨x,y,z,span⟩ := witness
  exact ⟨fun t i => (x t i).val,fun t j => (y t j).val,fun t k => (z t k).val,lift x y z span⟩

end CriticalHigher.PrimeTangent

namespace CriticalHigher.FourHub

def checkRange (test : ℕ → Bool) (start : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => checkRange test start n && test (start+n)

lemma checkRange_sound (test : ℕ → Bool) (start n : ℕ)
    (ok : checkRange test start n = true) (i : ℕ) (hi : start ≤ i) (lt : i < start+n) :
    test i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨front,back⟩ := Bool.and_eq_true_iff.mp ok
    by_cases h : i < start+n
    · exact ih front h
    · simpa only [show i=start+n by omega] using back

structure Prefix (test : ℕ → Bool) (n : ℕ) : Type where
  checked : ∀ i < n, test i = true

def Prefix.start (test : ℕ → Bool) : Prefix test 0 := ⟨fun _ h => by omega⟩

def Prefix.step {test : ℕ → Bool} {start len : ℕ} (p : Prefix test start)
    (ok : checkRange test start len = true) : Prefix test (start+len) := by
  refine ⟨fun i hi => ?_⟩
  by_cases h : i < start
  · exact p.checked i h
  · exact checkRange_sound test start len ok i (by omega) hi

def testFin {n : ℕ} (P : Fin n → Prop) [DecidablePred P] (i : ℕ) : Bool :=
  if h : i < n then decide (P ⟨i,h⟩) else true

lemma Prefix.all {n : ℕ} {P : Fin n → Prop} [DecidablePred P]
    (p : Prefix (testFin P) n) (i : Fin n) : P i := by
  simpa [testFin,i.isLt] using p.checked i.val i.isLt

end CriticalHigher.FourHub

namespace CriticalHigher.Hub251

/-- Consecutive 8-bit entries in a compact matrix row. -/
def digit (w j : ℕ) : ℕ := (w >>> (8*j)) % 256

def fromRows (n : ℕ) (A : ℕ → ℕ) : Matrix (Fin n) (Fin n) (ZMod 251) :=
  fun i j => digit (A i.val) j.val

private def radix : ℕ := 16777216

private def encode : ℕ → (ℕ → ℕ) → ℕ
  | 0,_ => 0
  | n+1,f => f 0 + radix * encode n (fun j => f (j+1))

/-- Spread the 8-bit entries into 24-bit lanes before forming dot products. -/
def widen : ℕ → ℕ → ℕ
  | 0,_ => 0
  | n+1,w => w % 256 + radix * widen n (w >>> 8)

private lemma widen_spec (n w : ℕ) : widen n w = encode n (digit w) := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    rw [widen,encode,ih]
    congr 2
    apply congrArg (encode n)
    funext j
    simp only [digit,show 8*(j+1)=8+8*j by omega,Nat.shiftRight_add]

private def sumUp : ℕ → (ℕ → ℕ) → ℕ
  | 0,_ => 0
  | n+1,f => sumUp n f + f n

private lemma sumUp_spec (n : ℕ) (f : ℕ → ℕ) : sumUp n f = ∑ j : Fin n, f j.val := by
  induction n with
  | zero => simp [sumUp]
  | succ n ih => rw [sumUp,ih,Fin.sum_univ_castSucc]; rfl

private lemma encode_weighted {n : ℕ} (k : ℕ) (a : Fin n → ℕ) (f : Fin n → ℕ → ℕ) :
    (∑ j, a j * encode k (f j)) = encode k (fun i => ∑ j, a j * f j i) := by
  induction k generalizing f with
  | zero => simp [encode]
  | succ k ih =>
    simp only [encode,Nat.mul_add,Finset.sum_add_distrib]
    congr 1
    have term (j : Fin n) : a j * (radix * encode k (fun i => f j (i+1))) =
        radix * (a j * encode k (fun i => f j (i+1))) := by ring
    simp_rw [term]
    rw [←Finset.mul_sum,ih]

/-- Check every output lane against the requested row of the identity. -/
def checkDigits (row : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0,_,_ => true
  | n+1,offset,w =>
      (w % radix % 251 == (if row=offset then 1 else 0)) &&
        checkDigits row n (offset+1) (w / radix)

private lemma checkDigits_sound (row n offset : ℕ) (f : ℕ → ℕ)
    (small : ∀ j < n, f j < radix) (checked : checkDigits row n offset (encode n f) = true) :
    ∀ j < n, f j % 251 = if row=offset+j then 1 else 0 := by
  induction n generalizing offset f with
  | zero => omega
  | succ n ih =>
    have small0 := small 0 (Nat.succ_pos n)
    rw [checkDigits,encode,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt small0,
      Nat.add_mul_div_left _ _ (by decide : 0 < radix),Nat.div_eq_of_lt small0,zero_add] at checked
    obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp checked
    intro j hj
    cases j with
    | zero => simpa using beq_iff_eq.mp head
    | succ j =>
      have h := ih (offset+1) (fun i => f (i+1)) (fun i hi => small _ (by omega)) tail j (by omega)
      simpa only [show offset+1+j=offset+(j+1) by omega] using h

/-- Verify a row of A times the candidate inverse, checking all integer dot
products simultaneously by carrying sufficiently wide lanes. -/
def rowOK (n : ℕ) (A B : ℕ → ℕ) (i : ℕ) : Bool :=
  let w := sumUp n (fun j => digit (A i) j * widen n (B j))
  checkDigits i n 0 w

private lemma row_sound {n : ℕ} (bound : n ≤ 256) (A B : ℕ → ℕ) (i : Fin n)
    (h : rowOK n A B i.val = true) (k : Fin n) :
    ((fromRows n A) * (fromRows n B)) i k = (1 : Matrix (Fin n) (Fin n) (ZMod 251)) i k := by
  let f (s : ℕ) := ∑ j : Fin n, digit (A i.val) j.val * digit (B j.val) s
  have w : sumUp n (fun j => digit (A i.val) j * widen n (B j)) = encode n f := by
    rw [sumUp_spec]
    simp_rw [widen_spec]
    exact encode_weighted n _ _
  have small (s : ℕ) (_hs : s < n) : f s < radix := by
    have le (j : Fin n) : digit (A i.val) j.val * digit (B j.val) s ≤ 65025 :=
      Nat.mul_le_mul (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide : 0<256)))
        (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide : 0<256)))
    have total := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => le j)
    change (∑ j : Fin n, digit (A i.val) j.val * digit (B j.val) s) < radix
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at total
    apply lt_of_le_of_lt total
    change n*65025 < 16777216
    omega
  unfold rowOK at h
  rw [w] at h
  have hn := checkDigits_sound i.val n 0 f small h k.val k.isLt
  simp only [zero_add] at hn
  have hz := congrArg (fun t : ℕ => (t : ZMod 251)) hn
  simp only [ZMod.natCast_mod,Nat.cast_ite,Nat.cast_one,Nat.cast_zero] at hz
  simpa only [f,Nat.cast_sum,Nat.cast_mul,fromRows,Matrix.mul_apply,Matrix.one_apply,Fin.ext_iff] using hz

/-- One true row check per selected row supplies a right inverse over F₂₅₁. -/
theorem injective_of_rows {n : ℕ} (bound : n ≤ 256) (A B : ℕ → ℕ)
    (checks : ∀ i : Fin n, rowOK n A B i.val = true) :
    Function.Injective (fromRows n A).mulVec := by
  let _ : Fact (Nat.Prime 251) := ⟨by norm_num⟩
  have prod : fromRows n A * fromRows n B = 1 :=
    Matrix.ext fun i k => row_sound bound A B i (checks i) k
  have det := congrArg Matrix.det prod
  rw [Matrix.det_mul,Matrix.det_one] at det
  have regular : (fromRows n A).det ≠ 0 := by
    intro h
    rw [h,zero_mul] at det
    exact (zero_ne_one : (0 : ZMod 251) ≠ 1) det
  exact Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr regular))

def batch (n : ℕ) (A B : ℕ → ℕ) (offset : ℕ) : ℕ → Bool
  | 0 => true
  | count+1 => batch n A B offset count && rowOK n A B (offset+count)

theorem batch_sound {n : ℕ} (A B : ℕ → ℕ) (offset count : ℕ) (check : batch n A B offset count=true) :
    ∀ j, offset ≤ j → j < offset+count → rowOK n A B j=true := by
  induction count with
  | zero => omega
  | succ count ih =>
    obtain ⟨prior,last⟩ := Bool.and_eq_true_iff.mp check
    intro j low high
    by_cases h : j < offset+count
    · exact ih prior j low h
    · have : j=offset+count := by omega
      exact this ▸ last

end CriticalHigher.Hub251

namespace CriticalHigher.Hub251

/-- The packed product can use a fast precomputed expansion whose equality
with the simple mathematical encoding is checked separately for each row. -/
def wideRowOK (n : ℕ) (A W : ℕ → ℕ) (i : ℕ) : Bool :=
  checkDigits i n 0 (sumUp n (fun j => digit (A i) j*W j))

theorem injective_of_wide {n : ℕ} (bound : n ≤ 256) (A B W : ℕ → ℕ)
    (prep : ∀ j : Fin n, W j.val = widen n (B j.val))
    (checks : ∀ i : Fin n, wideRowOK n A W i.val = true) :
    Function.Injective (fromRows n A).mulVec := by
  apply injective_of_rows bound A B
  intro i
  have eq : sumUp n (fun j => digit (A i.val) j*widen n (B j)) =
      sumUp n (fun j => digit (A i.val) j*W j) := by
    rw [sumUp_spec,sumUp_spec]
    exact Finset.sum_congr rfl fun j _ => congrArg (digit (A i.val) j.val * ·) (prep j).symm
  simpa only [rowOK,wideRowOK,eq] using checks i

end CriticalHigher.Hub251

namespace CriticalHigher.Hub251

def verifyRange (f : ℕ → Bool) (offset : ℕ) : ℕ → Bool
  | 0 => true
  | count+1 => verifyRange f offset count && f (offset+count)

theorem range_sound {f : ℕ → Bool} {off len : ℕ} (h : verifyRange f off len) :
    ∀ j, off ≤ j → j < off+len → f j=true := by
  induction len with
  | zero => omega
  | succ len ih =>
    obtain ⟨old,last⟩ := Bool.and_eq_true_iff.mp h
    intro j low high
    by_cases hj : j < off+len
    · exact ih old j low hj
    · have eq : j=off+len := by omega
      exact eq ▸ last

structure Prefix (f : ℕ → Bool) (last : ℕ) : Type where
  verified : ∀ j, j < last → f j=true

def startPrefix (f : ℕ → Bool) : Prefix f 0 := ⟨by intro j hj; omega⟩

def extendPrefix {f : ℕ → Bool} {off : ℕ} (p : Prefix f off) (len : ℕ)
    (h : verifyRange f off len = true) : Prefix f (off+len) := by
  refine ⟨fun j hj => ?_⟩
  by_cases earlier : j < off
  · exact p.verified j earlier
  · exact range_sound h j (by omega) hj

/-- Each lower half consists of g consecutive eight-bit entries. The next
upper half moves 16g positions to leave room for the twenty-four-bit lanes. -/
private def spreadAt (g w : ℕ) : ℕ :=
  let mask := ((1 <<< (8*g))-1) * (((1 <<< 6144)-1)/((1 <<< (48*g))-1))
  let keep := w &&& mask
  keep + ((w-keep) <<< (16*g))

def spread (w : ℕ) : ℕ :=
  spreadAt 1 (spreadAt 2 (spreadAt 4 (spreadAt 8 (spreadAt 16 (spreadAt 32 (spreadAt 64 (spreadAt 128 w)))))))

end CriticalHigher.Hub251

namespace CriticalHigher.PrivateBlocks

structure Data (K : Type*) (h b n r g m free : ℕ) where
  z : Fin r → K
  t : Fin r → K
  hub : Fin h → Fin r
  left : Fin (r-b) → Fin r
  right : Fin (r-b) → Fin r
  G : Fin (r-b) → Fin h → K
  owned : Fin h → Fin g → Fin (r-b)
  node : Fin h → Fin m → Fin r
  shared : Fin free → Fin (r-b)
  bary : Fin r → K
  weight : Fin h → Fin r → K

variable {K : Type*} [Field K] {h b n r g m free : ℕ} (D : Data K h b n r g m free)

def Data.a (i : Fin h) := D.t (D.hub i)
def Data.w (j : Fin (r-b)) := D.t (D.left j) + D.t (D.right j)
def Data.Q (v : Fin (r-n)) (s : Fin r) := D.z s^v.val * D.bary s
def Data.endAt (j : Fin (r-b)) (side : Fin 2) : Fin r := if side=0 then D.left j else D.right j
def Data.residue (j : Fin (r-b)) (i : Fin h) (s : Fin r) :=
  D.G j i * (D.a i+D.w j) / (D.a i-D.t s)

abbrev Channel (h q free : ℕ) := (Fin h × Fin q) ⊕ (Fin free × (Fin 2 ⊕ Fin q))

def Data.raw (ch : Channel h (r-n) free) (i : Fin h) (s : Fin r) : K :=
  match ch with
  | .inl (h,v) => if i=h then ((D.t s)^2+D.a h*D.t s)*D.Q v s else 0
  | .inr (j,.inl side) => if s=D.endAt (D.shared j) side then D.residue (D.shared j) i s else 0
  | .inr (j,.inr v) => (D.G (D.shared j) i / (D.t s+D.w (D.shared j))) * D.Q v s

def Data.coefficient (ch : Channel h (r-n) free) (i : Fin h) (k : ℕ) :=
  ∑ s, D.raw ch i s * (D.weight i s * D.z s ^ k)

lemma Data.zero_channel (S : Fin h → Fin r → K)
    (lef : ∀ j, ∑ i, D.residue j i (D.left j)*S i (D.left j) = 0)
    (rig : ∀ j, ∑ i, D.residue j i (D.right j)*S i (D.right j) = 0)
    (quad : ∀ v i, ∑ t, (((D.t t)^2+D.a i*D.t t)*S i t)*D.Q v t=0)
    (pole : ∀ v j, ∑ t, ((∑ i,D.G j i*S i t)/(D.t t+D.w j))*D.Q v t=0)
    (ch : Channel h (r-n) free) : ∑ i, ∑ t, D.raw ch i t * S i t = 0 := by
  classical
  rcases ch with ⟨i,v⟩ | ⟨j,side|v⟩
  · simp only [Data.raw,ite_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    simpa only [mul_right_comm] using quad v i
  · simp only [Data.raw,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    by_cases e : side=0
    · simpa [Data.endAt,e] using lef (D.shared j)
    · simpa [Data.endAt,e] using rig (D.shared j)
  · rw [Finset.sum_comm,← pole v (D.shared j)]
    apply Finset.sum_congr rfl
    intro t _
    simp only [Data.raw,Finset.sum_div,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring

lemma zero_of_minor {d : ℕ} (sel : Fin (h*d) → Channel h (r-n) free)
    (A : Matrix (Fin (h*d)) (Fin (h*d)) K)
    (entries : ∀ j i k, A j (finProdFinEquiv (i,k)) = D.coefficient (sel j) i k.val)
    (inj : Function.Injective A.mulVec)
    (S : Fin h → Fin r → K) (c : Fin h → Fin d → K)
    (expansion : ∀ i s, S i s = D.weight i s * ∑ k,c i k * D.z s^k.val)
    (rows : ∀ j, ∑ i, ∑ s, D.raw (sel j) i s*S i s = 0) : S=0 := by
  classical
  let x : Fin (h*d) → K := fun u => c (finProdFinEquiv.symm u).1 (finProdFinEquiv.symm u).2
  have ker : A.mulVec x = 0 := by
    funext j
    change (∑ u, A j u*x u)=0
    rw [← Equiv.sum_comp finProdFinEquiv (fun u => A j u*x u),Fintype.sum_prod_type]
    simp only [entries,x,Equiv.symm_apply_apply,Data.coefficient,Finset.sum_mul]
    rw [← rows j]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [expansion]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have x0 := inj (ker.trans (Matrix.mulVec_zero A).symm)
  have cz (i : Fin h) (k : Fin d) : c i k = 0 := by
    simpa only [x,Equiv.symm_apply_apply,Pi.zero_apply] using congrFun x0 (finProdFinEquiv (i,k))
  funext i s
  simp [expansion,cz]

end CriticalHigher.PrivateBlocks

namespace CriticalHigher.PrivateBlocks

variable {K : Type*} [Field K] {h b n r g m free : ℕ} (D : Data K h b n r g m free)

structure Moments (d : ℕ) where
  quad : Fin h → Fin (r-n+d) → K
  pole : Fin free → Fin h → Fin (r-n+d) → K

variable {d : ℕ} (M : Moments (h:=h) (K:=K) (n:=n) (r:=r) (free:=free) d)

structure Correct : Prop where
  quad : ∀ i e,M.quad i e = ∑ t,D.bary t * D.weight i t * ((D.t t)^2+D.a i*D.t t) * D.z t ^ e.val
  pole : ∀ j i e,M.pole j i e = ∑ t,D.bary t * D.weight i t / (D.t t + D.w (D.shared j)) * D.z t ^ e.val

def degreeIndex {q d : ℕ} (v : Fin q) (k : Fin d) : Fin (q+d) := ⟨v.val+k.val,by omega⟩

def short (ch : Channel h (r-n) free) (i : Fin h) (k : Fin d) : K :=
  match ch with
  | .inl (h,v) => if i=h then M.quad h (degreeIndex v k) else 0
  | .inr (j,.inl side) =>
    let s := D.endAt (D.shared j) side
    D.residue (D.shared j) i s * (D.weight i s * (D.z s)^k.val)
  | .inr (j,.inr v) => D.G (D.shared j) i * M.pole j i (degreeIndex v k)

lemma value_of_moments (valid : Correct D M) (ch : Channel h (r-n) free) (i : Fin h) (k : Fin d) :
    short D M ch i k = D.coefficient ch i k.val := by
  classical
  rcases ch with ⟨h,v⟩ | ⟨j,side|v⟩
  · by_cases e : i=h
    · subst h
      simp only [short,Data.coefficient,Data.raw,ite_true,valid.quad,degreeIndex,pow_add,Data.Q]
      apply Finset.sum_congr rfl
      intro t _
      ring
    · simp [short,Data.coefficient,Data.raw,e]
  · simp [short,Data.coefficient,Data.raw,ite_mul,Finset.sum_ite_eq']
  · simp only [short,Data.coefficient,Data.raw,valid.pole,degreeIndex,pow_add,Data.Q,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring

end CriticalHigher.PrivateBlocks

namespace CriticalHigher.PrivateBlocks

open Polynomial

variable {K : Type*} [Field K] {h b n r g m free : ℕ} (D : Data K h b n r g m free)

structure Good : Prop where
  distinctZ : Function.Injective D.z
  power : ∀ k,D.z k^(r-n) = D.t k
  distinctT : Function.Injective D.t
  cover : ∀ k,(∃ i,D.hub i=k) ∨ (∃ j,D.left j=k) ∨ ∃ j,D.right j=k
  separated : ∀ j,D.left j ≠ D.right j
  awayL : ∀ i j,D.hub i ≠ D.left j
  awayR : ∀ i j,D.hub i ≠ D.right j
  regular : ∀ j k,D.t k + D.w j ≠ 0
  individual : ∀ i j h,D.G (D.owned i j) h = if h=i then 1 else 0
  node_inj : ∀ i,Function.Injective (D.node i)
  pole_inj : ∀ i,Function.Injective (fun j => D.w (D.owned i j))
  position : ∀ i k,D.node i k = D.hub i ∨ ∃ j,
    D.node i k = D.left (D.owned i j) ∨ D.node i k = D.right (D.owned i j)
  bary : ∀ s,D.bary s = (∏ t ∈ (Finset.univ : Finset (Fin r)).erase s,(D.z s-D.z t))⁻¹
  weight : ∀ i s,D.weight i s =
    (∏ j : Fin m,(D.z s-D.z (D.node i j)))*(∏ j : Fin g,(D.t s+D.w (D.owned i j)))

lemma as_polynomial (ok : Good D) (positive : 0<n) (enough : n≤r) (S : Fin r → K)
    (rows : ∀ v, ∑ k,S k*D.Q v k = 0) :
    ∃ f : K[X], f.natDegree<n ∧ ∀ k,f.eval (D.z k)=S k := by
  apply (CriticalThreeCubic.evaluation_iff_moments positive enough D.z ok.distinctZ S).mpr
  intro v
  refine Eq.trans ?_ (rows v)
  apply Finset.sum_congr rfl
  intro k _
  rw [Data.Q,ok.bary]
  ring

lemma own_zero (ok : Good D) (i : Fin h) (j : Fin g) (s : Fin r)
    (different : D.hub i ≠ s) (S : Fin h → Fin r → K)
    (eqn : ∑ h,D.residue (D.owned i j) h s * S h s = 0) : S i s = 0 := by
  classical
  rw [Finset.sum_eq_single i] at eqn
  · have coeff : D.residue (D.owned i j) i s ≠ 0 := by
      simp only [Data.residue,ok.individual,ite_true,one_mul]
      exact div_ne_zero (ok.regular _ _) (sub_ne_zero.mpr (ok.distinctT.ne different))
    exact (mul_eq_zero.mp eqn).resolve_left coeff
  · intro h _ other
    simp [Data.residue,ok.individual,other]
  · simp

/-- Private pairs supply two physical roots and a complete degree-q pole
factor in each hub polynomial, compressing its evaluation vector to d scalars. -/
lemma expand_private {d : ℕ} (ok : Good D) (small : 0<r-n) (positive : 0<n)
    (enough : n≤r) (width : 0<d) (dimension : m+(r-n)*g+d=n)
    (S : Fin h → Fin r → K) (diag : ∀ i,S i (D.hub i)=0)
    (lef : ∀ j, ∑ h,D.residue j h (D.left j)*S h (D.left j)=0)
    (rig : ∀ j, ∑ h,D.residue j h (D.right j)*S h (D.right j)=0)
    (hubRows : ∀ v i,∑ k,S i k*D.Q v k=0)
    (poleRows : ∀ v j,∑ k,((∑ i,D.G j i*S i k)/(D.t k+D.w j))*D.Q v k=0)
    (i : Fin h) : ∃ c : Fin d → K, ∀ s,
      S i s = D.weight i s * (∑ k,c k * D.z s ^ k.val) := by
  classical
  obtain ⟨f,degree,values⟩ := as_polynomial D ok positive enough (S i) fun v => hubRows v i
  have roots (k : Fin m) : f.eval (D.z (D.node i k))=0 := by
    rw [values]
    rcases ok.position i k with loc | ⟨j,loc|loc⟩
    · simpa only [loc] using diag i
    · rw [loc]
      exact own_zero D ok i j _ (ok.awayL _ _) S (lef _)
    · rw [loc]
      exact own_zero D ok i j _ (ok.awayR _ _) S (rig _)
  have divs (j : Fin g) : X^(r-n)+C (D.w (D.owned i j)) ∣ f := by
    let F (s : Fin r) := S i s/(D.t s+D.w (D.owned i j))
    have one (s : Fin r) : (∑ h,D.G (D.owned i j) h*S h s)=S i s := by
      simp [ok.individual,ite_mul,Finset.sum_ite_eq']
    obtain ⟨q,dq,eval⟩ := as_polynomial D ok positive enough F
      (fun v => by simpa only [F,one] using poleRows v (D.owned i j))
    have hx (s : Fin r) : ((X^(r-n):K[X]).eval (D.z s)) = D.t s := by simp [ok.power]
    obtain ⟨Q,_,eq⟩ := (CriticalThreeCubic.pole_iff_divides (q:=r-n)
      (by omega : n+(r-n)≤r) (X^(r-n)) f (D.w (D.owned i j)) (by simp) degree D.z ok.distinctZ
      (fun s => by rw [hx]; exact ok.regular _ _)).mp
      ⟨q,dq,fun s => by rw [hx,values]; exact eval s⟩
    exact ⟨Q,eq⟩
  obtain ⟨c,e⟩ := CriticalThreeCubic.private_quotient small width dimension
    (fun k => D.z (D.node i k)) (fun j => D.w (D.owned i j))
    (ok.distinctZ.comp (ok.node_inj i)) (ok.pole_inj i)
    (fun s j => by rw [ok.power];exact ok.regular _ _) f degree roots divs
  exact ⟨c,fun s => by simpa only [values,ok.weight,ok.power] using e (D.z s)⟩

theorem tangent_of_private_minor {d : ℕ} (hb : b≤r) (hn : n≤r) (positive : 0<n)
    (small : 0<r-n) (width : 0<d) (dimension : m+(r-n)*g+d=n)
    (ok : Good D) (sel : Fin (h*d) → Channel h (r-n) free)
    (A : Matrix (Fin (h*d)) (Fin (h*d)) K)
    (entries : ∀ j i k,A j (finProdFinEquiv (i,k)) = D.coefficient (sel j) i k.val)
    (inj : Function.Injective A.mulVec) :
    ∃ Y : Fin r → Fin b → K, ∃ Z : Fin r → Fin n → K,
      let x (k : Fin r) : Fin 3 → K := ![1,D.t k,(D.t k)^3]
      ∀ F : Fin 3 → Fin b → Fin n → K, ∃ u : Fin r → Fin 3 → K,
        ∃ v : Fin r → Fin b → K, ∃ w : Fin r → Fin n → K, ∀ i j k,
          F i j k = ∑ s,(u s i*(Y s j*Z s k)+x s i*(v s j*Z s k)+x s i*(Y s j*w s k)) := by
  apply CriticalThreeCubic.tangent_of_hub_residues hb hn D.t ok.distinctT D.hub D.left D.right
    ok.cover ok.separated ok.awayL ok.awayR D.G D.Q (fun j k => by simpa [Data.w,add_assoc] using ok.regular j k)
  intro S dia eqL eqR hubRows quad pole
  have l : ∀ j,∑ h,D.residue j h (D.left j)*S h (D.left j)=0 := by simpa [Data.residue,Data.w,Data.a,add_assoc] using eqL
  have r' : ∀ j,∑ h,D.residue j h (D.right j)*S h (D.right j)=0 := by simpa [Data.residue,Data.w,Data.a,add_assoc] using eqR
  have poles : ∀ v j,∑ k,((∑ i,D.G j i*S i k)/(D.t k+D.w j))*D.Q v k=0 := by simpa [Data.w,add_assoc] using pole
  choose c repr using expand_private D ok small positive hn width dimension S dia l r' hubRows poles
  exact zero_of_minor D sel A entries inj S c repr (fun j => D.zero_channel S l r' quad poles (sel j))

end CriticalHigher.PrivateBlocks
namespace CriticalHigher.PrivateBlocks

/-- The residual dimension is bounded in terms of the number of distinguished
coordinates, uniformly in the potentially much larger middle and third axes. -/
theorem coefficient_bound {h D s b k q n d : ℕ} (hh : 2≤h) (hD : 0<D) (hs : s<h)
    (width : b=h*D+s) (endpoint : k=3*h*(h-1)/(b+h))
    (slack : q+k=2*h-2) (samples : n+q=2*b-h)
    (frame : 1+2*(D-1)+q*(D-1)+d=n) :
    d+h = k*D+2*s+1 ∧ h*d ≤ h*(4*h-4) := by
  have hb : h≤b := by
    have := Nat.mul_le_mul_left h hD
    rw [width]
    simpa only [Nat.mul_one] using this.trans (Nat.le_add_right _ s)
  have eD := Nat.sub_add_cancel (show 1≤D by omega)
  have eh := Nat.sub_add_cancel (show 2≤2*h by omega)
  have sample := Nat.sub_add_cancel (show h≤2*b by omega)
  have numeric : d+h = k*D+2*s+1 := by
    nlinarith only [width,slack,samples,frame,eD,eh,sample,congrArg (· * D) slack,
      congrArg (· * D) eh,congrArg (q * ·) eD]
  have pos : 0<b+h := by omega
  have budget : k*(b+h) ≤ 3*h*(h-1) := (Nat.le_div_iff_mul_le pos).mp endpoint.le
  have grow := Nat.mul_le_mul_left k (show h*D≤b+h by omega)
  have scaled : h*(k*D) ≤ h*(3*(h-1)) := by
    calc
      h*(k*D) = k*(h*D) := by ring
      _ ≤ 3*h*(h-1) := grow.trans budget
      _ = h*(3*(h-1)) := by ring
  have extra := Nat.le_of_mul_le_mul_left scaled (show 0<h by omega)
  exact ⟨numeric,Nat.mul_le_mul_left h (by omega)⟩

end CriticalHigher.PrivateBlocks

namespace CriticalHigher.PrivateBlocks

/-- Eliminate constraints supported on just one hub, using explicit
recovery identities followed by a single minor on the remaining columns. -/
theorem kill_of_recovery {K : Type*} [Field K] {h q d e : ℕ}
    (base : Fin h → Fin q → Fin d → K)
    (rest : Fin h → Fin e → Fin d)
    (R : Fin h → Fin d → Fin q → K) (P : Fin h → Fin d → Fin e → K)
    (identity : ∀ i k j, (if j=k then (1:K) else 0) =
      (∑ v,R i k v*base i v j) +
        ∑ l,P i k l*(if j=rest i l then 1 else 0))
    (measure : Fin (h*e) → Fin h → Fin d → K)
    (A : Matrix (Fin (h*e)) (Fin (h*e)) K)
    (entries : ∀ u i l,A u (finProdFinEquiv (i,l))=∑ k,measure u i k*P i k l)
    (inj : Function.Injective A.mulVec)
    (c : Fin h → Fin d → K)
    (local_zero : ∀ i v,∑ k,base i v k*c i k=0)
    (shared_zero : ∀ u,∑ i,∑ k,measure u i k*c i k=0) : c=0 := by
  classical
  have recover (i : Fin h) (k : Fin d) : c i k=∑ l,P i k l*c i (rest i l) := by
    have same : c i k = ∑ j,(if j=k then (1:K) else 0)*c i j := by
      simp [ite_mul,Finset.sum_ite_eq']
    calc
      _ = ∑ j, ((∑ v,R i k v*base i v j) +
          ∑ l,P i k l*(if j=rest i l then 1 else 0))*c i j := by
        rw [same]
        apply Finset.sum_congr rfl
        intro j _
        rw [identity i k j]
      _ = (∑ v,R i k v*(∑ j,base i v j*c i j)) +
          ∑ l,P i k l*c i (rest i l) := by
        simp only [add_mul,Finset.sum_add_distrib,Finset.sum_mul]
        congr 1
        · rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro v _
          simp [Finset.mul_sum,mul_assoc]
        · rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro l _
          simp [mul_ite,ite_mul,Finset.sum_ite_eq']
      _ = _ := by simp [local_zero]
  let x (u : Fin (h*e)) := c (finProdFinEquiv.symm u).1
    (rest (finProdFinEquiv.symm u).1 (finProdFinEquiv.symm u).2)
  have ker : A.mulVec x=0 := by
    funext u
    change (∑ v,A u v*x v)=0
    rw [← Equiv.sum_comp finProdFinEquiv (fun v => A u v*x v),Fintype.sum_prod_type]
    simp only [entries,x,Equiv.symm_apply_apply,Finset.sum_mul]
    rw [← shared_zero u]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [recover i k,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  have zero := inj (ker.trans (Matrix.mulVec_zero A).symm)
  have rest0 (i : Fin h) (l : Fin e) : c i (rest i l)=0 := by
    simpa only [x,Equiv.symm_apply_apply,Pi.zero_apply] using congrFun zero (finProdFinEquiv (i,l))
  funext i k
  simpa only [rest0,mul_zero,Finset.sum_const_zero,Pi.zero_apply] using recover i k

end CriticalHigher.PrivateBlocks

namespace CriticalHigher.PrivateBlocks

variable {K : Type*} [Field K] {h b n r g m free d e : ℕ}
    (D : Data K h b n r g m free) (M : Moments (h:=h) (K:=K) (r:=r) (n:=n) (free:=free) d)

structure Recovery (h q d e : ℕ) (K : Type*) where
  rest : Fin h → Fin e → Fin d
  R : Fin h → Fin d → Fin q → K
  P : Fin h → Fin d → Fin e → K

variable (L : Recovery h (r-n) d e K)

def localIdentity : Prop := ∀ i k j, (if j=k then (1:K) else 0) =
  (∑ v,L.R i k v*M.quad i (degreeIndex v j)) + ∑ l,L.P i k l*(if j=L.rest i l then 1 else 0)

def smallEntry (ch : Channel h (r-n) free) (i : Fin h) (l : Fin e) : K :=
  ∑ k,short D M ch i k * L.P i k l

theorem tangent_of_small_minor (hb : b≤r) (hn : n≤r) (positive : 0<n)
    (small : 0<r-n) (width : 0<d) (dimension : m+(r-n)*g+d=n)
    (ok : Good D) (valid : Correct D M) (id : localIdentity M L)
    (sel : Fin (h*e) → Channel h (r-n) free) (A : Matrix (Fin (h*e)) (Fin (h*e)) K)
    (entries : ∀ u i l,A u (finProdFinEquiv (i,l))=smallEntry D M L (sel u) i l)
    (inj : Function.Injective A.mulVec) :
    ∃ Y : Fin r → Fin b → K, ∃ Z : Fin r → Fin n → K,
      let x (k : Fin r) : Fin 3 → K := ![1,D.t k,(D.t k)^3]
      ∀ F : Fin 3 → Fin b → Fin n → K, ∃ u : Fin r → Fin 3 → K,
        ∃ v : Fin r → Fin b → K, ∃ w : Fin r → Fin n → K, ∀ i j k,
          F i j k = ∑ s,(u s i*(Y s j*Z s k)+x s i*(v s j*Z s k)+x s i*(Y s j*w s k)) := by
  classical
  apply CriticalThreeCubic.tangent_of_hub_residues hb hn D.t ok.distinctT D.hub D.left D.right
    ok.cover ok.separated ok.awayL ok.awayR D.G D.Q (fun j k => by simpa [Data.w,add_assoc] using ok.regular j k)
  intro S dia eqL eqR hubRows quad pole
  have left : ∀ j,∑ h,D.residue j h (D.left j)*S h (D.left j)=0 := by simpa [Data.residue,Data.w,Data.a,add_assoc] using eqL
  have right : ∀ j,∑ h,D.residue j h (D.right j)*S h (D.right j)=0 := by simpa [Data.residue,Data.w,Data.a,add_assoc] using eqR
  have poles : ∀ v j,∑ k,((∑ i,D.G j i*S i k)/(D.t k+D.w j))*D.Q v k=0 := by simpa [Data.w,add_assoc] using pole
  choose c repr using expand_private D ok small positive hn width dimension S dia left right hubRows poles
  have row (ch : Channel h (r-n) free) : ∑ i,∑ k,short D M ch i k*c i k = 0 := by
    simp only [value_of_moments D M valid,Data.coefficient,Finset.sum_mul]
    rw [← D.zero_channel S left right quad poles ch]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [repr]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have qr (i : Fin h) (v : Fin (r-n)) : ∑ k, M.quad i (degreeIndex v k)*c i k=0 := by
    simpa only [short,ite_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true] using row (.inl (i,v))
  have zero := CriticalHigher.PrivateBlocks.kill_of_recovery (fun i v k => M.quad i (degreeIndex v k))
    L.rest L.R L.P id (fun u => short D M (sel u)) A entries inj c qr (fun u => row (sel u))
  funext i s
  simp [repr,zero]

end CriticalHigher.PrivateBlocks

namespace CriticalHigher.FrontierSeed.B47
open CriticalHigher.PrivateBlocks
open CriticalHigher.FourHub (Prefix testFin)
local instance : Fact (Nat.Prime 251) := ⟨by norm_num⟩
private def byte (w i : ℕ) : ZMod 251 := ((w >>> (8*i)) % 256 : ℕ)
private def sharedRows : Array ℕ := #[0xc230a2b3f7032a9,0xff1524f151b4584,0x8d70e5e929a8226d,0xb8c1f39b4fc39c74,0xfac9c1ec731ab690,0xf6c4eeb345232d6c,0x5199a97168ad83c7]
private def weights : Array ℕ := #[0x80361c9df6e3d3220b2f062cb68d69999d0b881885108eca16d6ebf00000d1e5df1158184f6c045ce762200800009c81a27201889288759e12a1ee22000067164e9588b52d35caf1ea2a47a80000d8182124f121b700,0x9edadf5df1c38165340ed7ba98a32ed2c7c045b52a17018ca4740000391665e2463aee1aab9bb93c586000008bdab5e0492df1619bb4574361ad0000b5e395190ca258f49e15f427df6f00003b182b3d36dc59af00dc,0x1eb513b29ccb13c5aa4b91321e7f85a9f38b581a0bedd2c600004d92275bf7661db30a5dec0e694e0000bb6cbb76d8add258b0ba46031eca0000e188bf110220d8ddf334282413ab0000a6d9ab7ba27c526d82002a67,0x3fcd148ac1f9a097f52f22cb56c9d2ccb3d65024b27c000061d87a2ce7cd3042cdc52431f17800001cb4e9314f6ead7aae1d8ceef1f60000c44b59bfc56a66d3d0ae01e6dad1000031ad9555d3686d5753940040d25a,0xf40137aa8b397ba5275f658aa07a7e13625625aa00000ce70f2ff08238409d86f458a6b40000d697a80d0ea1c37676b2e16a42990000821a8d8f2071d60e1f11c60d710f0000187272a319a122bd0fba3a0011c96841,0x1401b312ec1c6d5fa098686040b796932fcf0000292776dfc413d8abfa671d5e8b8f0000b84cf3cb8cf97c0cc2c8a2e949a10000462ac244d45ff266aa3842ad635500002a754beb0af99b7e721618e4009f11ab7fb4,0x73f9dd073dcc5cd9b4df25c2cf33b9680000bdcf4abfa61d0e02d40ce0159d7c0000a40e9c4256e8d6de6af1a52921ad000088c5a099d66521ee2c570258f551000074edbc8d35a2c654c58c77089700de2eaf8dc12b,0x73a1cfe2527c61450c07e36f1f2300000398409543dce291522b9d2e76980000d5df7ea0100536306c425dcdf3500000d4d8ab13e9eeb5a7fa88e364c6800000d76d980fc78dec22d0f21ee497df00ef76f39c26e91b]
private def quadMoments : Array ℕ := #[0x1ce80b312d3b7f394e295209a169db6ead624caec59a0100000000000000000000,0x580f17e79f88b9a0e035f51388e6c5e82538e3e1e3c30100000000000000000000,0x6f7e40bd7b806c51ef0f1a9997d001aebfd47354b9d80100000000000000000000,0xa66c6f364f40072cb9b2f3d6fa6f2fade976bf0cc4510100000000000000000000,0xc6926d6b257f02690accaf88921c97c6b946c8dc5dc20100000000000000000000,0x582ff612f7e126a408d522f3b18aa39988dc03c850db0100000000000000000000,0xf532968c268d42176e65aa0bf47c7ec3a5bb2b94f9940100000000000000000000,0x6749b94e4ae4563b88d5bdd2ddf387bf4ae3cd0c10500100000000000000000000]
private def poleMoments : Array ℕ := #[0x17408ceb2d9e0547d2d92545c0a9cb87df0fd580956fcf4a056b9aa72d8985c452,0x86566e58f3a5009c3a3adc97074f0de3f400d9aeae9eca15ed27b3e600951414df,0x99925129d3eace77424241bd06f36dcba0ebf616c6c517a52a29e382a47284949,0x6144dad718bd9bb958efb928cc988f4841d6350dd735786ecdb2d8c38c9f278f9f,0x3d4cf45be5407a2a1a10eeb7e4e616b9c0737e4e30d42fb6bc42354a5e7fea9086,0x18a23339cfb54426c1d51448eb99ab7729cc724d893cd8cbd00b6a7b6e5be7a0b4,0x51df16dfb5db1487817543f3a742a7299b3c9a8864c9e3fac6fa7bd6b4d39d3165,0x4389dbbe3da0ac10b2ef1cc9a09b44b7e50e3020d75465e5d6cc2fb92a90608f01,0x48d09b1c67f3cb96dd2d7ea75c7033595d384c234968623ccc42bd1166f6017c2e,0x20975af03fa649f01230ab822192de348d7cdee6c3b1b757f8f317d4bef39695aa,0x82e26e3e2b81d37f9d9b99b747275f9fe2d63d1a70c6a3d250b6bf47558a89cc14,0xf9af4dcae1a0e6b00b7f875605cb63729496d51d3ddb4324380a76a24c80088a79,0x81aa8fbd7747a21023597de2dc7e9c9ad23e4101bd93474e68459b065fd9d09ccd,0x86555a51b3ceb01ccb637f0b6e921f54b2d533380a3d1d27f8ad997f804266488a,0xa68e4ba26a0ec2b8c7d3cb8da9263ed397c078e4d638d40c7b5fd6211b6fec5566,0x7bbb064ba1098c0c61c3a7e9f2f426697304ed6095621588327b034b4f648b7735,0x30386edf653d428f1e388417ec698555183f0beaec7e4f8642b8a1898c8812861d,0x463051afab9079f9aa0f802c17b46e8145f1874775912a4f9569cbedad3166097f,0x8192e4f98438719fc58611cbb9ac877eec1cba83f2e9e4bcbb311d8676f644e7d3,0x8e786deb5fddb6780441c3ccb72f4cef110eb7e8050f2348d88d39e93b48992775,0xf8c1799630d3a7ca64e8e75584f59dc0165a45a06cc0954408ed23a55e1c86123,0xd3c5251164570fa33af7c7be838ae91b1a75a76513f7e344dfd33c020994556213,0x7ed492e2cf70906147f0b21df8b938d1dd4568667321b04dbcec4a11ed088f909d,0x568ebc4228c050163df4bfdbcc6f3f3d5c7a151860229823a38c184130d6892ed7,0x457d99770d0df2451556df7f1e6b8be0e0267ff66faea1d06ac27272e6a1317566,0x3d32e08b17a36ba86b89a478d0116add21787f3042f074abfbaa2c97eb7e50bc0,0x2bb3eed353f8e78b3fb491b5351b8d28b4c4c2ecf455b853894a6ef4259d93a9ab,0x1c4d37b7de337cb40c6b024d95d640eacb5af4216a839560d4b010777aa91ca6ac,0x31ba062deae4ac764be5b848878e3d107ddec7124104c6b70e692c1eea6caf740b,0x775187714d41e9a57398c88ba0b7f895744c8c80a730c2bd40b46044d186651484,0x5c9185b71835ab55ad271c0255344042531faba2aa4d83ab8fb03828941f455b95,0x7a835901e0781614ad25b3d2acb6bf724fba37a22735c9de7c56bc1d87d645aa53,0x739d140c484a58708ae5e8bcbd7848b5c11aaa4b77897c82dab5529a9c10c7d445,0x34ea3e38507e9fb3eb75943d957955e503c9469bc887738de0087712caa9b1c439,0xc56e4357f05659891520c0b29e9714b90e20457ec09440c399786a54c0a3039487,0x84ce08347201b603818f7d27e8303db60658121569f8ea89257358241a6c7e80e9,0xc4b81df8c28d722420d052ac64aee9a05db6d8c0f4f11c62288fcf38582994d1bf,0xa3881e4e3b21d4ab1f2d02e13fb4d967c61116ba130c5f7f4c2f74b86684707248,0xcbdae161792a27b6e32de0d6355f50e001ea586b13591d4344e55906951a8c7220,0xa8e0089e20764a6257dace045930c3c0cec1561435e8182025a694e89a0e784389,0x4f4f5d85280b986abeb70e0606ef505cc9c72bbac3e940407bb83d881f7ce3483b,0x3e130da02913c8ec9b48dcf37737751377d15be70f04526201f477623686cda0d2,0xf8a85e861745c9bcab5564db23a6074eea88514346e64dceb5f24fed706f81a11b,0x2e82bda4b55d79f59b4d6e9c30084c5aefcbbbe798029e0aa9e1cf7bf19acdc769,0xe976a8da70ec534e9327563bab23966b5bd84f3ea5f8d343ce5edd862d06f303db,0x9f4423b417701a379e0ab0be38cea34e6b6e010c17ccbab316954fdd02b2804ea8,0x47d096a60d0ae2cd4f9f92587f5eb53717445f06be876610a65a014e385d40bab9,0xece82f377f1c4646b3524e5b84530110d7a1a1ec264f8699d8b257762c2c5bee06,0x5385a0aa8e5765bfc5e90f199e1897c57e67f211ad41c06368ec112c1cd4f1a4c6,0xb6e46883e755834cb04ce2cbeb74e9f8c9e9a2b1a23b2b62a8adee76adc80ec8ac,0xa800ac6e62594848550ec2e2004c8e5a333d3dc9e4043b00a2c58bdd616176eb65,0xd1edb254335cf8e0659e78c82c4f47b9290c51a33f81591b4891f2f7a111dddee,0xbaab416a8ae369dae6792c35efc6296093cc6ca06a6b92c7695ea58783d9182981,0xaec6610bb8935dbdc22822016902d7808798420406e758ccb05fdc534923651af8,0x5773542fa69cdb74ef5d817e50717832aec4a8c798392c0c9b128501b4e2c149f7,0x51204ce40608eeccc227796437a2eb1aca6f8304a96a0f47c8621dcee6e9653f29]
private def selected : Array ℕ := #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,53,52,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87]
private def restRows : Array ℕ := #[0x1514131211100f0e0d0c0b,0x1514131211100f0e0d0c0b,0x1514131211100f0e0d0c0b,0x1514131211100f0e0d0c0b,0x1514131211100f0e0d0c0b,0x1514131211100f0e0d0c0b,0x1514131211100f0e0d0c0b,0x1514131211100f0e0d0c0b]
private def recoverRows : Array ℕ := #[0x1000000000000000000016100000000000000000161b0000000000000000161b0300000000000000161b030da00000000000161b030daca000000000161b030dacad20000000161b030dacad2ed00000161b030dacad2ed4b000161b030dacad2ed4bd50161b030dacad2ed4bd59e,0x100000000000000000001380000000000000000013894000000000000000138947800000000000001389478ce000000000001389478cee10000000001389478cee1d200000001389478cee1d2f6000001389478cee1d2f6d10001389478cee1d2f6d11a01389478cee1d2f6d11ad5,0x10000000000000000000123000000000000000001232400000000000000012324df000000000000012324df620000000000012324df625e00000000012324df625e6c000000012324df625e6c130000012324df625e6c13aa00012324df625e6c13aa19012324df625e6c13aa190a,0x100000000000000000001aa000000000000000001aa5a0000000000000001aa5a2800000000000001aa5a28e8000000000001aa5a28e8bf0000000001aa5a28e8bfef00000001aa5a28e8bfef61000001aa5a28e8bfef61ac0001aa5a28e8bfef61ac7701aa5a28e8bfef61ac7707,0x10000000000000000000139000000000000000001399000000000000000013990b1000000000000013990b1150000000000013990b1154500000000013990b115455e000000013990b115455e5f0000013990b115455e5f7600013990b115455e5f76e6013990b115455e5f76e66b,0x1000000000000000000012000000000000000000120bf000000000000000120bf590000000000000120bf59f100000000000120bf59f1e4000000000120bf59f1e4750000000120bf59f1e475c700000120bf59f1e475c7db000120bf59f1e475c7db520120bf59f1e475c7db52ab,0x100000000000000000001670000000000000000016745000000000000000167458900000000000001674589d9000000000001674589d9100000000001674589d9104b00000001674589d9104b94000001674589d9104b94c20001674589d9104b94c24901674589d9104b94c249df,0x100000000000000000001ab000000000000000001ab6d0000000000000001ab6d4e00000000000001ab6d4e32000000000001ab6d4e324f0000000001ab6d4e324feb00000001ab6d4e324feb36000001ab6d4e324feb36d70001ab6d4e324feb36d72c01ab6d4e324feb36d72c28]
private def basisRows : Array ℕ := #[0x1000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001f25a92208d4e99af4d366131bbc4ee9bb16e3c722cb0d24c1e37cd4ef8253a50309d0c383c2eb88f72db8cda60c7d604b0e99b8d53c2ca76cc49987b770f7285c6d2a8c1f21090bc7977dcb2ed38a39d2d323836b52dd94b0f1d452f4e7fec7fb74fd5e16d036cd37e5670d58b9e8f8a55272feccc7ee6d39a,0x1000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001e873153613d6c3181a1838c592242172ce5a21e17394e895f2f754a0c980740c78b9e39fc411a2d945ecebce671e23ef5eb0ac8d9aa0e10a7ded89f7347e32da20d2b840111f6f075992efeef67c6fd2f9bb2d24dc1077d1903fe9c9cceb8a20840c1a037a6b83c1f62209ce03d518974d3fa25d737e192f86,0x100000000000000000000000100000000000000000000000100000000000000000000000100000000000000000000000100000000000000000000000100000000000000000000000100000000000000000000000100000000000000000000000100000000000000000000000100000000000000000000000162642bfa4d3c2788a742238d546308b8a9aa1ed0da245de37e3f1355432e124adf4a361b9aa660f8188bb2625b5501b4aa1699164b515e37cc6f9e8b25ae889e046c0c3e4f03bf5de9356407137f9b7e3cd34c5138d663aa983bbacf6278b46d538b19b18e82a17c5c5b4211e30af5ad4678b2dee7c4e6af4b,0x100000000000000000000000100000000000000000000000100000000000000000000000100000000000000000000000100000000000000000000000100000000000000000000000100000000000000000000000100000000000000000000000100000000000000000000000100000000000000000000000125018ccc4e12853cef37aa17cfcfb6a17e262a1c335af57106f4ae1830a7d9d1287622bf86658d49bdbd9ee82c6387509e0a7cbca694bf05ebe9c2a9523e269b81ef87f43d2c0bccf35fb6f86148e8131450003527baf6acb6f4d8da85a42352ea6c7793325791d510b293a00207689a1a09bd58c2603f2bbc,0x10000000000000000000000010000000000000000000000010000000000000000000000010000000000000000000000010000000000000000000000010000000000000000000000010000000000000000000000010000000000000000000000010000000000000000000000010000000000000000000000017369df643542b5331f9e39694c0f966d325c4c3d01906aa53c6c014b0a9d16dfb15375e5beca89eb017a7f157b1d1f463052ad3396b1458459699ad55415b2b6085ea1d5dada748e1e2e50e15fe0603fb4e96f126ae61e76c84037429ff0860cfa31e6970396d6d01ccc4372c36ba75b133970f2448b79cb13,0x1000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001084a715862731ff833ab20de75b0a8d40d67ba7b01bfe33172a73d59a1208a9a59c32442a568055791352ef1dad0a1bebdd1c5758964e4ee167791c336f90fc7dc75f06fbf7c4160a795d17ec7959d0885306df1480766dbbd2837cc09857956c53952dce913f3d098a57e01a3ab5249e507b82cb69a3e7e71,0x1000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001f0077f7d385640d0670267cbd024c978819899183a45ccb8ba7f311e1bc5e8a2895f9f0df312220da00104d9b16c6c1e606a75dcacb81041268464add97eb66fcc4b8a5819dc2161f8a47e0a9476aa3bcae1d31f9f61abc23eddd2d5165c4ddf3dea490147cd302219f6c9d4cfdfe2381ddbed88f1c34e9c54,0x1000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001291e08743cb1182eefebab2d978f0f55cf0e6d020d6d313413ed1d333e08380f4e0382ae1f941ea6884c3f320cf81cc913d5e2cf261d4f757b7f9cacc5655f0c1deb168bf61cc86540762411366c8845eb05dc8e26dfb0d7042063a0539f6df3db2e2c904585b7275ad37dd91128c2598a04495b2e2b934f50]

def D : Data (ZMod 251) 8 47 75 86 4 9 7 where
  z t := byte 0x4e258d1a11ab09bacd908a3d755b726d13958f02a9d7560662c9bfe959c0674bc384dd97ace5b74dd8689250c164d50b37d152f53615217c93a4f39163cade6ea7eb70f62bbdcb799e7b2ac4b0b6a38e1ea52318e740 t.val
  t s := byte 0x81c70bb95180daeea44a8a4e4364c2ce5f95d428295a6796a350b041721f7776ed1a9bbc687fa7a236474d7bf43fd8e506a9d26546732bc4b47505dfe0cbe8f0eac83aa0acddf8e96b0452f585eb8d2d6094c52ce719 s.val
  hub i := Fin.ofNat _ i.val
  left j := Fin.ofNat _ (8+2*j.val)
  right j := Fin.ofNat _ (9+2*j.val)
  G j i := if j.val<32 then (if j.val%8=i.val then 1 else 0) else byte sharedRows[j.val-32]! i.val
  owned i j := Fin.ofNat _ (8*j.val+i.val)
  node i j := if j.val=0 then Fin.ofNat _ i.val else
    Fin.ofNat _ (8+2*(8*((j.val-1)/2)+i.val)+(j.val-1)%2)
  shared j := Fin.ofNat _ (32+j.val)
  bary t := byte 0x4a49efab0e8960abce2d2c3406a7b02f36fa94b8a554b3a22ae596cb28f6e771de5461ae38e42f6394b52794bc0457951ba1de6d6f4459e22c574e4fa112bc5414949f25a393a045414d7428ebe0de66f19f07a20553 t.val
  weight i t := byte weights[i.val]! t.val

def M : Moments (K:=ZMod 251) (h:=8) (r:=86) (n:=75) (free:=7) 22 where
  quad i e := byte quadMoments[i.val]! e.val
  pole j i e := byte poleMoments[8*j.val+i.val]! e.val

def L : Recovery 8 11 22 11 (ZMod 251) where
  rest i l := Fin.ofNat _ ((restRows[i.val]! >>> (8*l.val))%256)
  R i k v := byte recoverRows[i.val]! (11*k.val+v.val)
  P i k l := byte basisRows[i.val]! (11*k.val+l.val)

def sel (u : Fin 88) : Channel 8 11 7 :=
  let z := selected[u.val]!
  let a := z%13
  .inr (Fin.ofNat _ (z/13),if a<2 then .inl (Fin.ofNat _ a) else .inr (Fin.ofNat _ (a-2)))

private abbrev baryP (s : Fin 86) : Prop := D.bary s = (∏ t ∈ (Finset.univ : Finset (Fin 86)).erase s,(D.z s-D.z t))⁻¹
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def baryOK : Prefix (testFin baryP) 86 := by
  let p : Prefix (testFin baryP) 0 := Prefix.start _
  iterate 21 let p := p.step (len:=4) (by decide +kernel)
  exact p.step (len:=2) (by decide +kernel)
private abbrev weightP (s : Fin 86) : Prop := ∀ i,D.weight i s = (∏ j : Fin 9,(D.z s-D.z (D.node i j)))*(∏ j : Fin 4,(D.t s+D.w (D.owned i j)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def weightOK : Prefix (testFin weightP) 86 := by
  let p : Prefix (testFin weightP) 0 := Prefix.start _
  iterate 21 let p := p.step (len:=4) (by decide +kernel)
  exact p.step (len:=2) (by decide +kernel)
theorem geometry : Good D where
  distinctZ := by decide +kernel
  power := by decide +kernel
  distinctT := by decide +kernel
  cover := by decide +kernel
  separated := by decide +kernel
  awayL := by decide +kernel
  awayR := by decide +kernel
  regular := by decide +kernel
  individual := by decide +kernel
  node_inj := by decide +kernel
  pole_inj := by decide +kernel
  position := by decide +kernel
  bary := baryOK.all
  weight := fun i s => weightOK.all s i
private abbrev quadP (s : Fin 33) : Prop := ∀ i,M.quad i s = ∑ t,D.bary t*D.weight i t*((D.t t)^2+D.a i*D.t t)*D.z t^s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def quadOK : Prefix (testFin quadP) 33 := by
  let p : Prefix (testFin quadP) 0 := Prefix.start _
  iterate 33 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev poleJ0P (s : Fin 33) : Prop := ∀ i,M.pole (0:Fin 7) i s = ∑ t,D.bary t*D.weight i t/(D.t t+D.w (D.shared (0:Fin 7)))*D.z t^s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def poleJ0OK : Prefix (testFin poleJ0P) 33 := by
  let p : Prefix (testFin poleJ0P) 0 := Prefix.start _
  iterate 33 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev poleJ1P (s : Fin 33) : Prop := ∀ i,M.pole (1:Fin 7) i s = ∑ t,D.bary t*D.weight i t/(D.t t+D.w (D.shared (1:Fin 7)))*D.z t^s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def poleJ1OK : Prefix (testFin poleJ1P) 33 := by
  let p : Prefix (testFin poleJ1P) 0 := Prefix.start _
  iterate 33 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev poleJ2P (s : Fin 33) : Prop := ∀ i,M.pole (2:Fin 7) i s = ∑ t,D.bary t*D.weight i t/(D.t t+D.w (D.shared (2:Fin 7)))*D.z t^s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def poleJ2OK : Prefix (testFin poleJ2P) 33 := by
  let p : Prefix (testFin poleJ2P) 0 := Prefix.start _
  iterate 33 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev poleJ3P (s : Fin 33) : Prop := ∀ i,M.pole (3:Fin 7) i s = ∑ t,D.bary t*D.weight i t/(D.t t+D.w (D.shared (3:Fin 7)))*D.z t^s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def poleJ3OK : Prefix (testFin poleJ3P) 33 := by
  let p : Prefix (testFin poleJ3P) 0 := Prefix.start _
  iterate 33 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev poleJ4P (s : Fin 33) : Prop := ∀ i,M.pole (4:Fin 7) i s = ∑ t,D.bary t*D.weight i t/(D.t t+D.w (D.shared (4:Fin 7)))*D.z t^s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def poleJ4OK : Prefix (testFin poleJ4P) 33 := by
  let p : Prefix (testFin poleJ4P) 0 := Prefix.start _
  iterate 33 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev poleJ5P (s : Fin 33) : Prop := ∀ i,M.pole (5:Fin 7) i s = ∑ t,D.bary t*D.weight i t/(D.t t+D.w (D.shared (5:Fin 7)))*D.z t^s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def poleJ5OK : Prefix (testFin poleJ5P) 33 := by
  let p : Prefix (testFin poleJ5P) 0 := Prefix.start _
  iterate 33 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev poleJ6P (s : Fin 33) : Prop := ∀ i,M.pole (6:Fin 7) i s = ∑ t,D.bary t*D.weight i t/(D.t t+D.w (D.shared (6:Fin 7)))*D.z t^s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def poleJ6OK : Prefix (testFin poleJ6P) 33 := by
  let p : Prefix (testFin poleJ6P) 0 := Prefix.start _
  iterate 33 let p := p.step (len:=1) (by decide +kernel)
  exact p
theorem moments : Correct D M where
  quad := fun i e => quadOK.all e i
  pole := by
    intro j
    fin_cases j
    · exact fun i e => poleJ0OK.all e i
    · exact fun i e => poleJ1OK.all e i
    · exact fun i e => poleJ2OK.all e i
    · exact fun i e => poleJ3OK.all e i
    · exact fun i e => poleJ4OK.all e i
    · exact fun i e => poleJ5OK.all e i
    · exact fun i e => poleJ6OK.all e i
private abbrev recoverI0P (s : Fin 22) : Prop := ∀ j,(if j=s then (1:ZMod 251) else 0) = (∑ v,L.R (0:Fin 8) s v*M.quad (0:Fin 8) (degreeIndex v j)) + ∑ l,L.P (0:Fin 8) s l*(if j=L.rest (0:Fin 8) l then 1 else 0)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def recoverI0OK : Prefix (testFin recoverI0P) 22 := by
  let p : Prefix (testFin recoverI0P) 0 := Prefix.start _
  iterate 22 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev recoverI1P (s : Fin 22) : Prop := ∀ j,(if j=s then (1:ZMod 251) else 0) = (∑ v,L.R (1:Fin 8) s v*M.quad (1:Fin 8) (degreeIndex v j)) + ∑ l,L.P (1:Fin 8) s l*(if j=L.rest (1:Fin 8) l then 1 else 0)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def recoverI1OK : Prefix (testFin recoverI1P) 22 := by
  let p : Prefix (testFin recoverI1P) 0 := Prefix.start _
  iterate 22 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev recoverI2P (s : Fin 22) : Prop := ∀ j,(if j=s then (1:ZMod 251) else 0) = (∑ v,L.R (2:Fin 8) s v*M.quad (2:Fin 8) (degreeIndex v j)) + ∑ l,L.P (2:Fin 8) s l*(if j=L.rest (2:Fin 8) l then 1 else 0)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def recoverI2OK : Prefix (testFin recoverI2P) 22 := by
  let p : Prefix (testFin recoverI2P) 0 := Prefix.start _
  iterate 22 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev recoverI3P (s : Fin 22) : Prop := ∀ j,(if j=s then (1:ZMod 251) else 0) = (∑ v,L.R (3:Fin 8) s v*M.quad (3:Fin 8) (degreeIndex v j)) + ∑ l,L.P (3:Fin 8) s l*(if j=L.rest (3:Fin 8) l then 1 else 0)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def recoverI3OK : Prefix (testFin recoverI3P) 22 := by
  let p : Prefix (testFin recoverI3P) 0 := Prefix.start _
  iterate 22 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev recoverI4P (s : Fin 22) : Prop := ∀ j,(if j=s then (1:ZMod 251) else 0) = (∑ v,L.R (4:Fin 8) s v*M.quad (4:Fin 8) (degreeIndex v j)) + ∑ l,L.P (4:Fin 8) s l*(if j=L.rest (4:Fin 8) l then 1 else 0)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def recoverI4OK : Prefix (testFin recoverI4P) 22 := by
  let p : Prefix (testFin recoverI4P) 0 := Prefix.start _
  iterate 22 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev recoverI5P (s : Fin 22) : Prop := ∀ j,(if j=s then (1:ZMod 251) else 0) = (∑ v,L.R (5:Fin 8) s v*M.quad (5:Fin 8) (degreeIndex v j)) + ∑ l,L.P (5:Fin 8) s l*(if j=L.rest (5:Fin 8) l then 1 else 0)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def recoverI5OK : Prefix (testFin recoverI5P) 22 := by
  let p : Prefix (testFin recoverI5P) 0 := Prefix.start _
  iterate 22 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev recoverI6P (s : Fin 22) : Prop := ∀ j,(if j=s then (1:ZMod 251) else 0) = (∑ v,L.R (6:Fin 8) s v*M.quad (6:Fin 8) (degreeIndex v j)) + ∑ l,L.P (6:Fin 8) s l*(if j=L.rest (6:Fin 8) l then 1 else 0)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def recoverI6OK : Prefix (testFin recoverI6P) 22 := by
  let p : Prefix (testFin recoverI6P) 0 := Prefix.start _
  iterate 22 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev recoverI7P (s : Fin 22) : Prop := ∀ j,(if j=s then (1:ZMod 251) else 0) = (∑ v,L.R (7:Fin 8) s v*M.quad (7:Fin 8) (degreeIndex v j)) + ∑ l,L.P (7:Fin 8) s l*(if j=L.rest (7:Fin 8) l then 1 else 0)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def recoverI7OK : Prefix (testFin recoverI7P) 22 := by
  let p : Prefix (testFin recoverI7P) 0 := Prefix.start _
  iterate 22 let p := p.step (len:=1) (by decide +kernel)
  exact p
private theorem recovery_identity : localIdentity M L := by
  intro i
  fin_cases i
  · exact fun k j => recoverI0OK.all k j
  · exact fun k j => recoverI1OK.all k j
  · exact fun k j => recoverI2OK.all k j
  · exact fun k j => recoverI3OK.all k j
  · exact fun k j => recoverI4OK.all k j
  · exact fun k j => recoverI5OK.all k j
  · exact fun k j => recoverI6OK.all k j
  · exact fun k j => recoverI7OK.all k j

open CriticalHigher.Hub251 (fromRows batch batch_sound injective_of_rows)
def matrixRows : Array ℕ := #[
  0x3faef163447636b7a1135154e60ceb5e3addf4d43042e64e7dbfdccdb74f5d6eb0df89cf96b42a7ebb9bcf62b0363680cb73353b7151de382dde1681d7716c365f4b826d030bd6776913119070d7494fa460672368c4bf8b,
  0x23a96157ee22af736898ecd9505319c73c627947bf8e93b5c9f1a505ccd4a943780af902261f8e17bccb086a6af4a36524892deecbc0eee7a8bd3a5363cd38e6bccd5498bfcd1b32b6b3ead6a1ac54e0645e781abcf0e018,
  0x6cf874d1401263d966d19092b7f7a7f5e1c34a8a27f0800738429cc18e6c9e090745268ebadd2bc41d67327650c89a086a46ee027648327bd942380e950a88a9b55b07e3725c774bb80f6bb04ec4d5950fa39e1dfaf60c16,
  0x909db6bc9255afa3ce63224f2beb9552f6e9af95ddb488f927e0a512f65f2e74daf361a6aa48c29233958b59ca4594f11b680a4cadadaf686401c125044707f7cb0936ce46dc745fa177962c3bb5d8dfdc2729f2ba412dbe,
  0x555ac6d29576148c3b920bd288b06583723305eb30957a82c4c326f5a02bbbf6da671f9ead4e632c91e951042ee5ac21b30147209315c199a47bd2877ff2d3e58cad14340281e7541c5c1ddfa9242864dfea8a79e2f8826f,
  0xce1fd89ed0f7bd17b896320b8b807f35265d0fd193cb120b532f5e3931ea347870cb935306459fa11842b4811c99ad4362039236ca84669915b70b5f1dcfe1d19d936d7696e4de91845965e8e9221521646b5f0d92234479,
  0xd87eed1a9d871c67bda15794ed6618bfe322332d8d2ca661ce66c23f690f9b3a2453320518d42b3ddbef6f897745664b7e1c525c6769278bb04a8a0681f71833798bf062f78d19ea837816a8976765ad41c5598c3b404065,
  0x2294751b9c8ed15c8c3b46f3ba149a90b21e591507527dafe5904eae13094bf19bc5ad96cecb5da7a660ae5671e56d946012e0adaf554263997770c5ac128bd82ff2ee230676f9d33df11e845ae87494a518def23a5664ae,
  0xca8b172b467ab697870dc307f53bd471a906d8deec56e53a8d7ec3f51f93dba96c7573c423563d46c636553940005bab816696a40e6611d35fab712489e2da99666473b60e9b6bc38f4edcae72aebd83da8a4cb8ebe57647,
  0xf15bafd623116218c6f4422330eb08b45b1da1c052bcbed1b1bd68e8efd8658090e80a3c92637a0a3ace3fcc607edd8c380a222688acccafbdbac7deb74fca8d93c2a1d1283a2a5d1dc1033c5100abfa64a308f585d0e68e,
  0x9d96878c45651ed66cb490ccdfaebc7180e3d56d8eab90a4aee3bfb83e090316eed2058fcd3ff75b5c182e11166bad9a10e08ba7576181884f42654e5b2544d0aa71802cbc6f3cf8c89056a929183cdc66d54aa3f2e1d6e0,
  0xc56bb8cde0e77883d90f71aa6476c30719346f39d4b4708c0af7365ea66e168207c20b7ac4f5b6a2f6a2c99c6df653df7682dd1786bb85a6c612bf21f650cf9d326e49518562a1e1b35a8ae4617ed3ca00076b10f223adc8,
  0xc0a1c5baa1bbdd2a9df6a6ac33d64b6714974eeff2e64a641dd2774957553cc26b686ab195f218466bb7eda8ccf49da71e0bda8d616605d24276cf0a4de48e126c70b8300d2a94497084ccd7b015e8c5139d1b198f194492,
  0x8c774100c2a9bf25ca44e181b26a2aa81e4ec6134a159fd69a0d37e839c47c66d5e7aaf5d39bb591792eedac14a9d86db7b36ec376d26c3514a18b0b6bf8f1d959c925a584b7acc5f00310535d5e10b50c3e5a946ca94554,
  0x5e02d1c5e0484c5be82363e8357b8c31177dd194ad3d99b3acecba035ce25bad3b2330a2e7c42f776abd60f0f3d90c2f6cbf0d27261dbb04c3e651d5f5acc490d483817f00a627720f84f6920f4a5e07b9056c7f653485d5,
  0x2b75e6c366133c261fd58a6d1633276d6324e775ca17f1473561875de8d11165a315359e509ea7c6ca6e2441038794a92dd74bfae0114e2d36e7575ef4bb8094218b67e1bd318d82cc3560a1afe97ec55899155b5a6f3843,
  0x2c99ddc2e41ac10efae58d67f252d01ae69c504e53b2a3893b3aea95ba1ce3421bdce21ff5b7c65fc2dd6ab6e9415712b27a2cd20a26544a02941f825f21d91ae699b36af978da8c3caff23d49a71659a70d52e546268d18,
  0xfaa5c46c90953ff199641adaee5bee0e6b6e6251c842e0924c487405b15a6f07b28ca9837d6c856412ba62a7c1de284266855b8bc54f44093dbcb0d904abd332416b390fa50dee0803e915115cf07449e0de2fddea27c40b,
  0xc654d599e49928f607843828409100a1e33aa96ad222ac687ac6d408593d0ef924829f9988c7971cee581fd98f9629286ac7e6cb0ab5096e32120298812376fa666dc075ca73bbb886cfe00da5e1c2085e3e82995af23539,
  0x137b89d8d19e097b605e9116da50059c2658c8cb927eecd794630ffaec1ea7007ecc4632a56dac2e5637c4234c85393465393b202b93743244d5d865836bef8d82a773d9e413a80b9dd70a480c51f412e082deaa4d8cc442,
  0xb3d16917477053b8ce29536a376415c68f8394316d078e9518235d1098a61c22d584c7714606ae8c922c4dcd6c108d76058e8dc4156cf49ee182e2955e1bd1878435b286b79f1b23da0fe6441c80f7d2f5d5f4422f980f32,
  0xef230c9d0f7aeb56cfb4def7cd0bc71d763453f5aa89da7563962bb632fa5ec98dee74b731414e26e01c9750c7af41b499d448bf4984e570aee77c62448b9217790e543bf7442480b1922fb7a6a244f6c70b0ba1dbb014b0,
  0x336b822869dc2c9a21c934e1ded56d57c124ec276ef9a90196ee3cc8a703ec5a67f389a672fa2ce97f63586e6cea9630888b2ad56dbcaddfa966953266bfb68d6f2541af49b6df61129fc828f800a5062dc764d9341bd1f9,
  0x17f37d9c5008c85f9d0b5926b4b4a3d77f67b5c436a836a423cf00a46bbc5a1265cb89854ea450b99a05091905cdd91eb993e6bfbca07e766b0625759a2aea8cd8127d61156937efbf537020a9a0dac9b89d5d80d5f62aed,
  0x3ab882314f3191a1296720aebf95aac74955617a9bd94ec54de283bb76576503669b5e0ab898d7e89d0761f88d6b8a657656d15ee1999f346fbef6c6dca5235964bd955cc079d70a61000274266f99a9fa9e2921b9a59092,
  0x7457cc98604fdb68058f1337e48f70b427d38513cfa6cb1351804d24df955be50f52ae2bc31cc6dc2b001ca6d8b1ad136e2aadb09464c79ab837ef069da1810fb2bee94a9ac5a1fa82b2f3c9af3c24cc2985e42f71f36ab2,
  0x8a83ed9c6da373ed48192cc6d5634e940cd7ce474a042de9a4923f092709a9d78f37e098e6f50aa61f394c95a314e75b43948fa8c23e0836c31fbda5e8cda2da0453f6f578cc1ef4661ee150ea64cc46443e5f89449569cc,
  0xc9c9fa599c1042d19c9f1dc23fcbf150511465d0dbbca750ab815e4e3071f4a8977bef7723160f55f317905b3506d27b0ab2025c408e1794046290164357758e1bcb233909b1eaeabcca3a4c7488a43e0f0604cd119e1377,
  0x414aeb6a3fd72952f374dbf6b41fc82fab65eed52887137075355e0ca76c41ad47f3ddc3b8d77b21829999eed7cf0334f1544495d6de8520ae9aba0b4242c786605b36038852503f3c8f80dbf21c141c1cb38a0d98ebb8c9,
  0xa62ce75e922c75964339646456db145249a64bdf3345e320add58a65c25aa7376e2a106e35930b465029087595ccb8e1b2e6b018307ee4078c9d61ef74bbc37f2036de19cbaf8521148d211e9675a200e0dfa2f4de410e91,
  0xd008703d74d3691ab5406dec1d58a348d6d5fcab3a46d43cfaa9ad170de9bcaab965b55ef487a1898d9ee3d944ee04c2332aedd81a43c399ef67819ae061bc687b785a5ee9e5a549483104af78795dacf67d40544982812,
  0xd91d3b85d32300bfbe2894461f8b09943375ac8627676853b2a41922cbb573393fc7dd7325625aaec8904a6ace27b673d9e5e974c98b4a5da096cee69abb39f6aa032b3cb250760009a8b0a33feb46e9dd8805330010aa6b,
  0xa479fa715f20a281f313ded2648a40463029589e3350eb7d8a16376afa6d7fbfe288fa509fa54b69b07e548eece6dce0ed45356694c6c7ac16edd60717dbe17c399a4e9e7694f66316b300bc50a17698f802220d0ea35cb2,
  0xd732af49c24574ea0530a89122d12d24a21ec47c08b3728f93b081ee5c70ee396c4aa8f8605999a76bd57e890d960e8a6b98ceaac5c93fcb51283a8407b21ac02c78b28ab8e6a4e5da344e337816af80dce58c167ea5603c,
  0xbcc0df037445c84a2f9948cad41d94e8de24b1e8d504af825fc05941128b9faef214251b61db1104bf5bc38b23d69dbd4069752ebce1ec096cd120f0ea9d3b150a0774ee7307bbbfcc4bae10c953c5c69b141f583184a097,
  0x43d89e0358e4b3c7e5c5d286b03d5c68a81a991c0e0880b915a7d11eae830483941a6c482a510e473a6d7c31c2557f3359d4f04022a592b4963ad735f49cf3b54303b04b2bc1ec8da42a4eda71e40a4a7268e83b7829046e,
  0xbe260b219c320d5d97c588390be636e451c3d9dbb247faab9caab760b05bb87d07b1cf247d808afa48b09c4c0a0cf6f2e4ed74261e8c84a09688338e6edaaeb20599f3083ce13b4dc9487206632e4715a336a379521af509,
  0xac7b10c5d3627f0aa3e574690344cf3b874e8ee6dd67e6eb35a8984041e86028d22e4c4fede8edcfe1eaf92839f3035472ac2660d25b501c77bebc350128e28ccaf7a6c5e94d3e9467caeeef428e7459d841b93754681a95,
  0x69fa0f095c927d8cf08f5b9369da39934361629785e2ab68d4872fbfdc01d723d54a964b1fcf18c4ba3cc0cd7357090eac4a29103823a7e77c5febeb07f469d646c26ca44248de716a0a52acefe12003ad9d738a4d472ca7,
  0x70c86c1a41665a1b7e7316bfef2a273f937016abdc03b3ce04c8c5f43715d2d57676929aa69007d98c9a609ebccbbf12bb8f016e4ac4444f0931f876f33832d568ebca4fe326aa4be490d699206d04e5e1f29c6247692eee,
  0x92067ec82fb1378d0b73b39fe9ee911643837228a33fa124d7e77c80607cda948548b89df7862fa7f0193cf8eaa454418ca7697c408d605914318338c551258391236c9a3c6f017d57441a072bd4bea2120ae56f33418809,
  0x66301ccb645b6f4a8cd33ad93e7dcc5fdc22f6c33cd86f936ef588f851dccd0655d2e1e2c9dd594bd8d5b11e420e3c7c9d308f833656562097196a4a166d3499154398642d15c92e1b576ab779a854a1c7101dd4e36694f1,
  0x86624e441cc95e030acd343d22d57743afa3a64a57c238d757c7d0c851c4f6ba1855492f688ec0933a61b7ec8f0de383a1c9d4dd00df83eb5d82137086ebeaa97153b85d10f37fe0d2302243c44e770e56df6a9073bf924f,
  0xa588f2e8eec2e42472e2d174595d190dccde6500b096b8e9c888bcc4c8f0714c234e8051943c4d289f369eacf6f2b68acf7430ed290a7b339bc6a68f1d9e9fba5284259d17c5f53397ac2c476bc56e219ebba3ee5947e1b7,
  0x85c32959845e03e1892a0b943d19c8f54a9b357d77f43453a8354f9a54f59c01b633d130dcd4ee07db8ff394d325d6034dae231c9716ecd91bc9465c9a31b1b3eccb03f8ea018806729b66954a51993af6a28186d5c9e42c,
  0x3e37296b4d24c8351de5f6df5a6c7b624ddc2c759d5a67795e804a1b089df352f5115a09d686cce33879c516a2ec066f5aee4551e1e1d1deb9a3d6f059e717878b54c041cec7a086ca6784af9db1a032acd1d56d825962bb,
  0xfa6328a7a20c2798fcbd7178a26a63e7942ed732f23981ee13aa0873044a13c581ff247785f96d4cb7b993718241ad590d3dde7df123f7c2b8a0ab7d1d021926a351b770008e5de84acd35e32e760f51a7db0ae3fbd0c69,
  0xde01b7a0dd42e445a94431efe07b6ae176f5055e83238d7b9601c434e9da3e4b996824bc0087756da7bcb9c8afb63ba6314ad7a1edcf8147d16825c0823ae254a0e31b5219534e7db97221f01e54df8528a394e55f501ea0,
  0x24222a60c0db7dbadce438da47b6af0703f96daaef806849ce2fef7613b48dee6cb5af60aaef1c1469a39ed4cbba67f59d53eb45e831aa2e36dac9dfb5eb1593b46a4e8e0b40bf624102c31341b20607b697d152ed5082f2,
  0xfa27f44d3b7d18763ff1135743d9c153b0f0c37358dbf8e721b39d0a2111c8dfc089eec1a6016197689bc6b3c74f9d6e70898ef41900a0620e37e186ce09c0cc0d61391846909b6a4b8ef839ed8f51bd79df903dcc407c86,
  0xab9f5dc954429aae393051da200d5a5f561ab15bf7399502f9bb26a41192cde57118089984b86caba9a5a46cf5b044c7c223200587ee0130a80c01a93c43c80bd2a1659340274dd027b9093f350cf7a3bdbda6ae37273956,
  0xc1d00b73949c55a58a57476cb7fbe3870b9d1f13e3186bed8c6bcf164f2f72fc1110c7d57d63ef65b35beeac928a5745b2662d7a9a682eaad2bcd92072c03793e7a7ea7a2e9f046efc0f9e93d73a1e97fc21313c6bf201d,
  0x6f149b8f7fd868217940639396255d650929a442485a62cb8e88d184e07b88e1347725521f476edfea71dd79b958f836ed8d72bb29d4e18e68321fa944151e266cb15fa9af138d2b9a777e8f32e8271834038872fa38d23b,
  0x53b73dab543935aa3183282194d1592308ca81c18dcd6547269162cb44c488bf23f1269d3e675aa509a537bcb03398a16c3ccbc14cef4f2695d2f84cd06491956d0b5c29b3c2a542883eacdb9fd6446320002ccf8a76c85e,
  0x23c91a4164dcded467f7f33308711e69eeaba50c1a2dcd7c0544e921cf847591edabbaa5588d2bb1052499d83beb3c16277084990402e791f51658d6d53f35d7ade67b7d282884edd8cccbf487936a28214863f9218bb29c,
  0xe60870e4715cbc21b3806bd04cf1f9d1faaa8456862eb95052e062766ee577e221a4d5e7d2ce582043551a7f59472ccb464adbf1054b9323a08517d660b91af2de603ea854f1a18b77470df925c58d6a25f15103cd7616db,
  0x9f2009d9d02664ee3c7320a25da2a375a69f345d29b53e9e38757206d63ff0d039c13e90e30e99c11ab0aa22077876c543ba587909ed87b5496fc932e0a5736c4b5e9b7d603ae96813dea137b94174eab5b32236e908140d,
  0x6c9ba9723e04a29b038443fadfa33bd62de9a98e5ddb18cb624e4b621eeb9cd7d49010f5eebfbc2d8a2fd7927ba90469e0ea1b1dd5f181ce5a6f9cb6ee8915d86b48263b14864fe45c7527da4b0cc6a8bf14e5e8929dce35,
  0xa01f68ed6a5c94bc438998b20a5260b182390ca5685b0369d179a52e23c24b2a55d6f63c13c61f36b05210f3c73c41e511b024a4381f94d7574991ca6ab8b8bb46f440daf5c78fdfafae373e38ca8bddab9591a29e4fdc57,
  0x58563d09bd34ba82d86cdcb6ca13c697dce40f9ef56b39c80b66bcf079aa153fe2bb61a801e86c97223c09456ef53759f7d66a35407666f00d34bf0af6638c26bda4a816a30a7b0271155be6da8763387361260463300e2c,
  0x7a482b00f57c04036897c79d9b77cfb6c7347c127f5e6e3dc329cb12f1752d17266ff8d14e5d88120ff92571d69414763c26d65e6b454d1a877a0f840dc916c115456d2dbfc668bd34c2ae57756de1c1489d33718e5371d7,
  0x80c9786034a9497bc8a70d2eb5dbcb139d765b442cd524355722c36b512713bb6bccc2f7dc6535e341bd3f4a1e17999ebbf07e34239743e6dc0c1ca53474f56519793bbe712d3ee581df59306be7d58b7abbf05054520fa0,
  0x539b561fa06de2dd66a4196bc7dee76c70bf480eddc5733ca74fbd170aebcdde95b6cfccdf3f70b6efbde7f5eb206f4a2fdef424c19d22009a82b4b9b9e7c5e35e30aebf573d0018bb4918333e3dd404d2f637fa3337a613,
  0x26b0dc34415a43b880c8e32b36cbe1e9433710f3e14534d0589b455b08101ae4f106564ea90c035162714fa60008c4dd5a7082a53f90aa1ba9458fe56d9f1f99bcf4b427c852204202f02b4f2a25a2b7e53223f7205c7cf5,
  0x26f9dc7aeae270e1f49592a73c35a7a8a463f2dac52e7f1087ed87b38eb8ed63a6085f13351ec3c05078068e2626582b472eaa826660d0eb7b924b1e5c72ef65e101eb8ce3b1d36270c15a70a7c2cf880965ebce0b811866,
  0x554702c7b713792da77542caf202d1eb8357d6011adacd53ee6fbdc1474eddfabec4b1d033a56778347d17cf15a0666b5b6709c68edbe1d834e9591528dd3a66804b147cb5f3417a178c6361762bf9d72f6acad6e8a6a7f0,
  0x5ae4537d80233300d2e2013b13193157e60b04894c7530f0f6b258b411418519894a794a0b58b6717f0c65f55f053c6d5fdeb3e36b525b5d165f3a10d9401c129d0cb08dce69c4cbcfe3d032e25b5ae71500b058ed497e8a,
  0x359fc140e22b95165961cb5e6cf30389427ad13921f586717d92ca614a3e6f4acca997ef06f921aaf3bc2c33f6c02eea91802b1c1f7976d70b0e9540e7a1d7834f8673950d16ba6ae6c530a25f8b83a1674c2a02ee943218,
  0x8c813b3df234ec22c4fa2f5f0447f87e5f596bb47b0a338f0a462c51b5c1a8172c2364f539097ef31fbcef325501b0b02d08ef9ddd267689c4b8575fe17727345c2ad11b1067f844eed3478d33aba11d665980f1f20b1d14,
  0xae6a39086844e8a45a30e9a8d1d46ac7af5adf740301c39403c0ea6312ec70f0c5aa924f4d69b14484c5bbf768e1e33b450932ea2bbe37497a32cd4d61a2331d37a78ae592b96cf45739553b8a14c8e584f3c6c0cecf939b,
  0xa7cc565f2c91f8e938a688d027ad08527ab398c458f4553316c9f4227ddf9a2a958c970bf1c2a193b76588af42185f768a4b04dc328053b663b2777f23eeca5aecf47f28d5a8a06991553b1935bd56676127b7e6d874178d,
  0xd891c048e3735b7ab7afa10b57d47becce60932d12e288943761511c14fb4d11f70cd11932dd142ec4f98a05cdb8e33c3bef0efc3e38c1c25a4200055803863065012d5b46e4f76bc0586d06a3e1a03da5f1256e5cb8806,
  0x718c78767200bdd408aa7ac9db4cde43cfd1c3b235ec06f5bce5666f4f2285d465ba435ff3db14e4bcf9d819189f179dd402ee7c67561928367a6a53506565d69d1874d3b95a0415bc8c96a52b5257be25ac82a2ee6b09b5,
  0x257908c6e388b46e8107a776f4f1a1a3ca157f4c2129bfa1ba7fd758a10de53773b3ad355488174a71dd5e1f6bdbd8b7e9acbe6fd2d8da416fdb9eef6995b331811b3e16369b350fae1e503d488aaa0e73533b30049c26df,
  0x53ac353d5c6ab2b83a4c141ef6968586911163e686faf7692b3ec82e91dd9a90c27c6a497389774f99692ca14336d4a376336df77a4f8ce194e6d4f3d774f9efbba5c412d352eb9f2bce718e4630977a3678e5c34d3b9f57,
  0xce8f38f02014f4164289cec014b4b65a6d1c5aae4cb22da0288e84becba88e5eccca51459d4ce293d462c59d9ddad4ed1b343448dea9b2a87246f78f34e68d5e22af1936ed8fdab85a338a8687cf75b6c3789efa8bf1e102,
  0xedcda17c8f8ace69212f1ae904c7c1c7f132b9c3cf178c231395eb08b78329f2c7c9564a845be6980ed6246a78a9ef38fd330bb69907ef9fa29c37f2720441e2436c4e2ebe00acb4613f565df81850d7188ea49db514b66,
  0xcfdc67805e342cf88b0d0fda4697bb2ec2e1246e03c2df11ada46cec137c6cdf03b88326c59601d0dbaa53145573afbff868963c8f23876d995a90dd64a5db344c63e3dc54885d8a41d879d130cf95a3cee95161a793ccd5,
  0x6db048c23ff1e5c649dea137969ecd5045951ae48130b3cce1f43a687d842a996ed95c02a50a0f0a0acabd759fd8392b6a023eafd6f1de9390c71193503068e56a3f8231593c3134d139b3813a19087d29498a0df787b57f,
  0xd4cac83e956028ca289b55f00eb4e965eebc90f63bcc3a6ee1c3ad281593be1bb81eb6885ecf1c874ef0496a4420404c5bd1424f1eb65e52b20b7f0b563a34b9eebe081d78ec660eeb14ce6d52e713c00576769e5f3806c2,
  0xd358131951900f8aaa5f9a726bc84fed5eb150a0298db44275700509a6019a457d57850b1e5211206f613de7e902484a812cbf73d1b79693b8f0458aa1a4e96af68d2d6071ba74475da7a37e63dfb83737f13a6805c48f27,
  0x2bd2caf5cf05984a15a8e85a1e85504204ed37588f1ae4c359ecf8ce210a44e9bd005124cc59a7018ed963590c5da68758128ec789f7043ad50f74aa16b527cf53b358f1ca981c9eae8a1a086f76cd0e0d724b1183b26768,
  0xad1f2ab1d8e135056defebbab1a0ef6b869d45030cc5902a1e510351754e92aca6daa9705f1de253f303086516b1ca274206bc88329ae4ed884634c3e9a79a05595fef2938ab2413584b5321c08c0789797980cd78f0c877,
  0x5ee5d8021a7f936c23085a17d9e6228073379219cb0b2adbb9c6f88dae1b756fec1a2e4f4e6956544a8d41057556f6802ca9f264105e07f4af2c8b02910cd44517b14b2fa219d41fb8d5b96e84c807ef3759a9697a90af65,
  0x9115d65d0b587877b1224bff6eb4865c5db82e6f9ce23a6e83b00430aae956d88096e5501c2c52d773dbfe3b9af08c0a217b8c7b6ad95635260bd58436f0822c05c2ab8340a39b32857cac2d7943b3961a3d9f72b8f57a0,
  0x1968fc432b67cd266f5d83f82f3e231ba83745629ec95d8ab76b815112e8475408daa90a35d1d7617e5c60dc5c65fdcd3e06feb3cc85331de714b7749e85dc1452ff2e26290836122ecafbf9fe382e905002dbe5e019771,
  0xea6f0c0abe1edb6e64e1fd3a3f86aab1d03e88144f82110677ab8b7c929cfd0f3e95ad2e1c48bbc771ed8a51caaa7ad25cea76908524590875ddc57130735737c3d64c3b7ac9ee137812fc5eb854bed84c7619ed7a2b08b,
  0x31a1404e9d13c5990c31e89860146bb29711443ed5623c3e3ba3a2dc86e52df6bae562afbcc0c14bece8938d82bea4d8004223f47e8ba0a0d556266629e4672db89a21988af42cc8d90f3362af3eb2d603c1b7938a18ccda]


def inverseRows : Array ℕ := #[
  0x957874e997a4413af57c6cdf81828ae98b8e89ddbcaad3661226c98d31e812afd01e4b2aa2e6d0ed182b093554827f66dc09a436f71628dce88634b22077ed9acbbad6e7f545c2e37cab3ea313f6eaa2d601eed24803b283,
  0xf1322d2f78496b316d687bcf2e63e3b272996a206d20bbd513b804ce0e6f9705699e367f0f38ef29a1a2425e2c90c15eb675193773580d7d8f4056326e4c4f48f5c06fc4cb47dadf09579623cc0d9acd3e8a81410f3c5b3f,
  0x3cf3a936eb9653156f1ebc98b2164ff3bd9011580fb3f56f4a14eb1edbc278d0b0af43962280db5b7f211d1df614533de1233924e7c59ef7f6156f723fa4424aa45971b0889d32b7c56602938cf1bd773d68968a8fa10f24,
  0x4c435348c30cc0d759598c471fdd29128f9c0a004639c519f7dc8ab16df91eb584b7586584b1a30ec2ea17da7b079d9c8ae32aef9c9b39f55fed88e252afc256d03626f23f1cb07195126816153b96c397c6a6a2e92ad041,
  0x5770aad279026a33392e48069c086df0b71c9c418008161766301f60d638773165242929335f549dafcc48d3f99a53c13774baa83c278e55af9c3242b4caf8948330474732cd59501474d562d797b7b7d899ef29b63e9755,
  0xc330e1a0789e6353f1458695ca190dbda736375ada0f9946adbf3224bc800b238a4063ba098b79aa9f3409dce8bd947309d87568539b01f188155cf7a776358b7f615711296a088152a7700c2d4703dd6a5ba9af158d23c6,
  0x254d06cd46508d58814ce9ed8ab30e346b87798a4b703285c5eeb72d5e0c162937be3cc1b82508d52f8e103fe19131c921a5edcd60d2e384b9d5532352ee78a90501d2f913321fd7544ac482918a204a1328d63e47872145,
  0xefe19c5f278311bcbf9ba06ccce59387bfa83311e1e5090a9269084b67775071edf22df4d76ab00b4f0d782936f243de58caa77bac21f3c4775f9886ae5e5413844b682c7cbddc0267516938d298981596110733839b46f6,
  0x7d9d8cfbac0a5cc001c95b0a8215820879949085623e806c64d301d7ba82494dcd6d265b4147f4321026865d848d1aff91fa4d2d4888c3da4e6757bc1d341eb9a47e0ce12cc0f138f16c6d7459dadf212985789b1381b4d,
  0xebeaac38bdb89ef19a2900cb6794f83b655ba3515782a40bb9418ee961bae958a0aa13d6be58f8c0a02a3fb2185920715a87814e67b5ca5ee875189ad453acd26ad5732b152ef403182fc634f2319028188568da135525e0,
  0x900c82570b71382d107c3fde10d205d2423d2ddc3e15973749eaeda5698109621faa6f38a5df161c4f71ccf60db7d51e392daad668779621dd420d3af9e581827d031413a00d03caa5e4321ee6b734a089779c51b8e0de16,
  0xbcad2b08e1a85ac2165a8cd8c4b351301fd6c36c048a27228743e170b727642758b9a173368651c5874d95a855517976dae38d4ca54ca0499a731c21eb2510101014131fc34f375e90e79cc4873372d5130b458bb0e44b4c,
  0x49aca17fdd042736a6a7cdc07880af7c4ad2b732439f6fea66273b64a007cdcfaa1dae127ff17e905ef8eb13f5ce47aeea7cd7329561f5548165af4b3c30f1df4711c7209982a897aa0b73d4818bed4e78c7d82fb0ec68e8,
  0x2bd0bcd507b7f3b7c9cd966490645476872340e0e144430d9ce15da7abd85a3cc9a71b84da03ded332773f8e5b9b474db55f1bddc6a7eadd23e7a326460da5de336b97b0806eeccdac4841c9d87ec05994f453bba19f060f,
  0x982f5b2799d408e5604f9bcf5c78b416811f00c8be1d49e835a9457e47a6a9003321dd8fc1bbad4662374f53ec29c94f2fbff92beb6810bbe0ca6ee29a0ec4821d0a450ce5b2742b70fa9ec3926071e007632f59ec8dc9be,
  0x7ec4e77b42f4ec15dd44a77d1220ef6479e5cb01544c064f2ec7e2769c6bea1e7544db6bf97e3be603376de88d34a7a2897cf770126f36d4f14011cb9b0daf0ad2da0700333a473a3a415be8b8c3e6973124ebd149ee1436,
  0x5d2406bc02c319001aebd5ebcf2b981383adb53597ddbfeb51341faf93bef329237843afbe38711aee134dbe269b56ad998c69b96c4c2e9d99853e5ab21a17ee215fa397b66b1cb41412675ad2d96eb3df4a5045b121af75,
  0x842af4ba24bbef6fb6e9cdb9a93fa1b54fef63f6305d9bd773db77ea125e2aa08028799025eac1b210a744e81a9cde101e1630125292df82458f1e976b36c30a56b7ddcf46eac35167d1c9b4b588d4560b920199d5519af1,
  0x26faf0d83a6dbb984132ac81efc2e558a8adcdafcdf369f5129ef58ba414202a596023ccd613a1bd7f1c488ab94d15a937a9c278812f9c86dcd9eac1a7a9776c0b45f97c08b91d85977ad8041b303d45db6404b318f0d5f2,
  0x9bfa444d0cd00206994cef834faea0612f01b366a8105e32d3190e2b1e20edd41deb6ff00300a731900b05c2de58a8a0e7c8106caeb09142eb0e3132f22cdab2da58cb58545b214cc227a42ece12be5c3871e929bd7f5f26,
  0xd8d872ca3fee0b2983aff6aeea290d757d4c964df0b1d9e56cd8180997dab947f97bdcdfa7aa54d99bc4341940ec906c7524e5b6ec1c0b9b21336b1e53af97a3838e086c14c35cc5e8464a0a22aadd6b4d79ed3d161ac2d2,
  0xc737c2573de92fd3806fdd472a4b1ebf7f1ed10c15d44a8bcd863ea723b3633fae43e73c703b0e42ccdbd98bd7b060c991e53e718982bf254f7c39739b7f04dc0225a3f74754aedd0dbf3ede83c329223663308ce872295c,
  0x38e8c7314e53f2e0400a11d03688dfbf2abe8808da6f47cd3bdc42e5e3b9419f85b3b7b104555ad05b1e56ba24184122b8c38851ac88a08e0a7266161b7f57c56e1417a4b145620a5c7d481df36fe0b0f7106c8aeb6ced66,
  0x74380db706bbf6173560dd09bc66a85d350ec0b40dd7c0367584cd8e39523461f3805ec5f13e9af12015aae0c2cddec73d6b5eeea21a5485d1dfc37e5d230c86d1f399ad9e629e3651648358f6177b8669b952b24f05a641,
  0xfaec7e7194270c5ca4d9a9840fe7eca77b5071b411ac80815c23034d7e0db48511b1b75adc1e0165f586c32ff33f0769516c3e25e8b6f0523ddbe0a151ddbc7e1a8396673c5048cbc6a2cb72c9293816bf9befa9195a6f7e,
  0xebe4ec6a83c6f94e84f2b5eacc26415311b2b300f14205ab19b57815cf3f99124e847ed9c9cf4b5a8d9f4c1259482f398550fa90084992672a3e72965478017ea386516599e0a6ef68b6ad4f560fcd9e5456144fe484ad1d,
  0xd56986638c867e2749e10dbd05a3886913721daeebc42f3f241e1815d4595b2b54a17b750fcbb6acb57df32363886b48e1f333d319a8a025527ce0a45632007a1ce52779b1bc03b0faa5d16c4a317c7318cac69001273db1,
  0x9a04a6b4a736ccb45c55f05949f282d7b2b673b498e7bd91045b238f418fa69f7856a12dc36b5f0e5015a86fcb455b188c7103a334e54a3c020e6b11b1ad965101bf483b4f9e585cb4bccede49dfce9644e84763b7f032dd,
  0x337a898661c4b219ebd4cb744f3d45b6076bcaf4e666081a032ab3e0d22f4ca7ad6a0c62940e816fbf80e9374e676cf7c2c996aa9711f62f29b6734d94217ef1f806f9a246d04f7b0ebddf2d0fc5889638b16ce8c60fec34,
  0x638291def39f5342b99f45c809956e33577229a9373fd73886545444d6eb2e7f84f8051522544af688b65f98387f8de6bda0cef52fe9245d7cd299ab8a7a9872afdeba78799de6de580bf91c7ef21751bbe6240e192bae67,
  0x6ea1a5f060b13655f6d24a33c0644ff623b9785163c61a4e4d3da70bec2b7cb17ab9f9edf0caa949a6edc72176942c0e640c9d33f1e148af3924c42a795d770b6782af9e815a56f41924c1810eda6bf1b7a306ca2ccc4cea,
  0xa52e576163d952ecf48d615fcc591f87ea269791b6119c1bf930b963bdfa18a6d5086df15cb6c102e4c03bc7b10f96df85059341ba00bca91ed505ee420df0a444c5c72e810f7ed3cb00bd3311da1ee89dc41b055a216c10,
  0xba7027d4b4be85d883ed76f69b4549f499f2c1da29079731473d0d49f761bb39a3cfd8be9fb4a224dda1ec825e2cea7704f506240d5fda64455fad85197478e23a2d16d603cebea2429ed863a60ce53cbf940920bf45024c,
  0xad884aa90da1c1ec1d78a0f2fa24772c86ca6a1f86530e572216008c65d31e43d24ada967c81ee859bd464f7205c0363290e4cbb4b1e8462a20ba3ae666683d1e43aaf58258726d3f5039e3c50402c8fb4188ab3a494e483,
  0xe58770d0a16ea4dbf9a0c94dc172147070d066c8c6c072151b4a6714500a551b5da201a851784a2c572e4a65c91793ec075fd8e00e657de121ed5e6008e300c409b7f8d72f13d2ad52b7a54d74f04a1878ee4b5b6d02c8ab,
  0xb80e20e7da90627502561cf2dce51d1ebf18106bd16c566a253c22cc1ac36b586de07ddb22d558423528253d1ad39d3addb8186f22d1f57f84b22dfa0c5a335ca699ce202acbf9317c99850931c9277a46ed0cc9c7136db9,
  0x85428292b3f5a532024d03addc81a3eb50a516cbdce1208de8e8200851d2b3a909e600f115514db95939bf88a18e437eeb0d2f81deb70a24740751337f7a463e94ca027710768d552c793db9ac74bc1ba22e2ce6932434ab,
  0x449a8f5dc12e46d00eb3a8ebbe1ac94b54007ad48f03df26e5f95e006b024f1d309f089ed2cdd11393d0130ddd5b6b7a10c4dd45ea290103f56f8492c3d8741c0de825bd6aea0b5f324f01f2e23d9254296e64313448d708,
  0x1aef3a1e20da13a3355483f5c9e69e6e6a1408ac3e8633c4566b453192b0a0835c3b89b96451d28204ae9ad86ace2b4478e90ce8649aa0382cf566fadcf552b2aed32d36ccc8bc42dea3f7eb517655a444d27c23881e11d9,
  0x596e69e05e3fcc9764bfed892311f32e73a7d59b2f8d16b5a9ad3061f0d4790be031c8f90724b4e93a16ddd85ef90227ca47f837cb417394e2c4c59298be79e3e8a61f226e4fe5ecb4ee23f5b702efe491799a9ab5997da5,
  0x614fd943be0f358369e8414e098cec6f45ef1f267ad3efb56e197a03e8ce7476c6faeec53ac68051ab5d199055c5c51526a4bb4ed99cb94688aecf5f5b64f3e3ac29c09e1f0df57b10568d1acb8934d96b2ac77428f30652,
  0x3c1ba0132905215bab9bb1ab59f1162e505cce6342784bf1144ee3a317a70072a1cf7227d8d01da8945954c5753920e8ca9087a95326c48e235f1be3d08fd8f8824b70e8741f9a2b7feb46191444c17d6898cd2a3cb6df8f,
  0x52c86d30dd7c85cbdad20ea51446736b1a9928f651ef752c3a19f8beb821f710a164260b36483f5ad936d84ce90dbb6add038feab97a2b8d39023faeeee9464018bb136dd7350b69a17be5aa102d803119b12b3958662e77,
  0xe751b6440a24f08d1f9d54dde4ca4510c21f83d1a4467dafa3439f8d43824ff876ba6ab31d3b70c8c8a467178c8dc715a67f597cd32243c38c1a225c3ee21074755e0796b8dcf1a33c34972617aa0dc18f141cb7155ba7c4,
  0xe19d5ca6b068dd2d92c63907570d054f4cd6cbd30df4a1209b314fa79475a6dfc5a88d83b33a7488888c3fea254370af08c9602802ef0dbc1fa12fd5b9eb675bba1691c8b4e25c097b4c2deccff3608328a8f594316ba07d,
  0x94959f1bd8859cd0ad0805bf1d7fbff993a794045b39c17f5f419aa56a485e58114ba27de6ba72d9639f3eb93d501ce64099e55567109aeca016f017640854f188dc143d4f96599b57e89bc909a6eac195b19ca2850204bf,
  0xcfb8457e23008544bf5bd01b8140b3277c730232e04078237892103030b55f01bb8a295894c76093f087812b43b1197fa746cc3349664d83c3316321e7ed597642356eb9265f5775c0f241473ae989474a318451cf8c4c48,
  0xa0e50381939d431c0d889a5211037ef77d40f31e2ed95f5738053fa414ccf395dfb9689fac6532510adc9351ca1b836475dda33ae20c541a0541a5906d410db3317491cc0a983a1e46167ec51e460c6a2dcd0d4074bba319,
  0xb679622ff1a672e01deec3426faa759a52131ed706d4e08469a7410b4b928971b7667772c59b2a02a58ea0d753993512af779f8877a2d9bb74d5f8ef2ce3682b251f127af8554eeb36f319999d20470c1f15042bf7956cc6,
  0xd658e92605bdbbaa20984a587a61263fce2991a462733f33905b04d51656f5c962bcfa74c53bf4523abbdcdf9b6bea82a6ae4cdccc38ca846800ba10bca45964c3b0a5d7a8b64389dade9b7f45302c2b7ceb0bec2ce1c05f,
  0xd74fabd09da435a5a6a826f350f01b7e1a24c0215801f1ddf5ac91f79e83dfbdaf4e3302106676935144301446693ca107f98d5bbba1d039cc7a397ed674e934ca5933d9b14e6573b675eb278b6d6639d757c77568c497d9,
  0x149485a1da8b4fb39d39c2c1931920c086a2bda585564999f1d7cab4f859c996c9e35df7eea9ee3cd48bb22d1c146691186378d86f71d649a59a71858f0eedddc86c9bcae6404c070f1deec7d80f5681a2f42a1733dc18af,
  0x8922755eb87d27b3ae7ad671039bd7a2cd74f5132840e08881551d0ecb275101c0f9f9262cdee1c649e23985d76976cbad3c398547c76718def5324edb87787febd3f304131436e038be7cf46443f3013ccfa52a23889cec,
  0x811fe3b96c630919310aaf0e895e0fabafbe55de0c3d4e1826cf389dd269b104687fc3608fb37e0408e94bf8b4a54ff3fa77813be1d7916f67e081d477d7afc33b24d3779055fa357dbf1c769783195749d9958af792a24b,
  0x2cc72049f262260b2aa32c4e9622b3c9c15f6b925c2baba66dc7dceeec10038cc7dc1cd9577ec250474351a04d1e28f75b77f7794a258639b6a3a59c09b8bedd788f038f035daaef108463b446dd7829c84c5be8ad6f4c33,
  0x607e61ef283b1c422489b4009d8cc2d72047adeacf0ddfbee56a54ebf0ede6137f60e48579ac227f335c3ad99abd38af70e9c16f07ae4ab1f06178ab7de69662ceb82f1f08371f9259a0e72490e51498baf8c5ab68eb7c10,
  0x7ebcf23366d6b266a1e67bbf5db3dd6cd1fa5dc96fb884eb2851ad1f3583e6da4ac1263d8ce6b708093cbe82a655912d6351e0c9046ce524c36bdab601aa0a5105db35b658e8c35e68e7104f5c06cc45a293186c953dc4df,
  0x51a448b610225c2cf318bb5d1a38659fc99062f7f3bb8f2a18cbdc63cc8fa7f3a236981eef6e3b35c93b7076722162c78661afeb110431b601c616e70acfee4d1feef7d18111dd263964b56331f09c36c8563415c887111d,
  0x262fc420de9f3be62f21dcd016f8c62ca7312b4572239c4f5d09f917f79eb86543ce337cd8382d4f0d97f30c67ab5fcbb934a6799b08ea358fb641500b724306e193f551d628a187808626ba6f1a859c4981be44e1916ea0,
  0xace6bb05e48dfaf93e78a60dc0d7c678c255b03fd355b45974664ac6cf92455d86939c53978310276000014c06850311cfdf764abea2ec565a83f81f101b65c287c3b469f07286676cd6a709775bd5a3f0d00120c98cacb8,
  0xc7a853ec69f3795dbb60e83d00f35aad4281bb7d4a3d2b4726b33bd6098e4c4ceccd1fbab5234190a35c93f42f0b1a034e3f37162a745090656369f0734b80276337d5255eb227d4d696cc89a2c3f8254eeaa4b280e2d307,
  0x1d843909f53e9936f999f7a7cb8b4c59b1a4efc74aaf749159a136aabcf9a526cfee910f4973b1c3e3c10950083c04819f98e9583bcbdf628c02042e58bd5810d2ccc323c7342a04f74f736f8d7734e70e4e3001948406a7,
  0x3cc6ed05b7b35de1dd1e8fafe44da2c851e1559b5b3310a0026c9015431b70b0b1794cb42f610cb02114db115e8e9cb2d5253bbd3ea9aa8c028ef37099e3a4a2222cb5f092e0890923558ab08383f656d3797a7deac96261,
  0x1d39978ccc23c6989ab8090e54b163d6f16e6e3540790505e97f7a9b3d0bd684e04712e3a270a79942aeb56f850bc1d92f4eddf6b6c0699586b27c28999355be57772cb0eb763670052ced197d0ea963110b2346f56aadc0,
  0x2b99cc1c0642ad04bad42ff17265ee0b0f5aa6ea29e6a81c338191cd9312b58e2351267b547e0bbdb6e652b9002de6819f06ce864b1637a7b8813556b51eec1434c1ac98f56340dce926c622eac8c9d3dea112980d0116f3,
  0xf75069a88251d2b13833b6dd0c7d7a8b97faa6f7f62831110f1ecb9dbea4b3be9476374f7c8c8772f47c195250dc941069360ac869adf788b84da37fc3184f3a65d347bbe9757204bbcb8880f85ce09bfa21448117c4ab55,
  0x27406867452fb03a58ecb4a0d4e63da013f34f5252238d20e900593c35e3c7ea118409e32a708558007f32f6243156b7b4043082c204194451d013c011d5bf39c1eb2932e8be734dac63e226c27335c15e309fdc38f3c25b,
  0x9254a8af8638f289a5de9c71a21290b640e82dcf13d4dfee95749dfac03b67fa655a6d4f6da34139698f94c49facbfb7ef64b8dbbe80a9c37e3a0a1f3eaeafc3f0911b324317d9e7de86250ceadb72a8734355250c672197,
  0x45179fca7f7bb0aa435249e1c745024a0e510b6d57631b414217c79777663eaa095bb8d8941d7f26b65d4f4498f5c76816aea2db412f71f86a3e5c1bfaca86c992a9df5e65292e52c30eb142ee21c871e07c5ca0d63582dd,
  0x1f647775d01ad7e48c4e5d7df421d85e78b501642f9ce76f8e7c43d56f5a7a3f4d1d7fa6e63d696fb4438e1636926db11b1c0b5b5b10b31c4777f93dde7828d42fd3d9b8938806589ca23674677c3e76389294f719073e24,
  0x11c3e3c43bea0badb3a1c37084debefac609ae1c53e8d9324dac1e7159c2e7b1423e959fc7f66c25a08044104467b2c2e2379aa188747c8e5024e9f0d66937dce7f0f6f6a9cd8f5903688852a41c6754a1e994ce33111521,
  0x60cb1fded019581b2e43569765cef98b95ca2579b1c0a27a7f70cb2c14f21b702b15df8ada1f7329c7615a71d429093c5a63952e0894181bc30ccc9be8e22e43196efa20b3420b0201a5038c4040b0f73fd75b94d0ee71ef,
  0xa2efa3ef4f41faec68dae520f267f527f02199e14911a7951a76313d48a2348bd45589d745dceab89cbcdf47dbd505b414149f435d6c86756e7a4f029e92089ebe000a56d835e10dc86ba3dcc98daa89dbb92267b9ea5281,
  0xbf5f14f01fc3e0afc3b104d0a844cca41904b44f59c5c4bb58f96655c121cd6befa4c0166d52e2248bd697052e37bde67c644de77ca76d837f64a787f3e68c35bf83926a8fd8c33ece3672693b439ef4b738aeec45341275,
  0x59503d9794f8fa6d1231e928f7b4f34f1caf46645b98c86d260e880c4a0ed7fa33ecd86129f62250e220b4287b7eb458adb33db581a2ed084356f96b78630420359bcb27287e235343db0adb7498418eea1c1e6114bae425,
  0x67586b2e8fdb8e33d5f50da990e09d4df88ea2af3929ed811a9c7d99fa91f5eae5537119c447edf7e75112397ddc5bf98c206c09ad76680df382663689b3cbe8742adeb8aa68b55c73ca627b915f2f7b2a8b08b6b1020681,
  0x516b39445572f58c085bc68a4ee4096ff887a3cc1e4917ad10e11cb46152056c8d9d9e67383642addab46c87ab85a82decbd770dad161c0036eec532c13635053907cc9708544e750f1ac92cbaec2702bf4b6e3b42289f03,
  0x12d2dd0d1b595a99eb9e00b7b482311883faa9deb5a49bb1f3c20feb1efa7673535e0a703fe55d25062b60ac73c2d0f13511cad64a69f3aa7ee6a087124f43e5185acad97b04cc9f522d7f18b955a1b73520b38894352114,
  0xd3368c6ebf35943e6473e04815527152c1933652cb09d94bf672246c9c4e208262ea22ad225e3d99ab1b852f14a95557118f4b0b73d1ad602645ad2de24a7564ec926c24ee94e2607c25d85938afbf8261eb7bf970b795a8,
  0xba175db91d60e2d4790141126687c94b22ae392b95b33006e93201312bf37bd738a18c7752755074ce2d9dbaea483ac1824000f6549eac701229dcd63d9758b799eefa0b92a3aa4426e8dd085b43c4dce41976daf2117f31,
  0x7672b99a273a4aa95f1a3a3290635295a0ec86bb6bd8bd60312e3f5d307e0c72cee9d6ee049fafa76b0d03178a1d4ed9b8c35a370597d82ac294c4538ebe4232b00f4da5a2a4a634d9a6d57ed69f8f4769a506adc4992e24,
  0x52507fd031a4b8ccea291aa33755a35b1c1193e8a706b3e10b059e458f4813939fb322d0ee45e2ec82857a546b8b008e9751ab9c47af98b87a1eaf1eae28f49a20945d91b2ed6da37bd9926e470e7577fa5cf97c547306cf,
  0xb95dbc200dcb1c33e7cc2aab0674e40bc4e670ca321275570799e7a6bbd89f3f82ae450f68532a53c5f42b224ed2b7ada05481c4148e3badaa891972a562ae63960b90548b8d1e720dbc22273075edbac91779b1c8327b7b,
  0xa1f34622b3e902423283a7842642e0a2115e7b091097e4537567247df85a5917025db8a3dbedc76a13057f9ada275e74873932a65013f1b2c884a7e0deaff2c83e1c5d03e532a76a241012c6ba89b78507724d17d2779ceb,
  0xcb1c47cdf80b18d3f0542101a0bd9712fa45057f287e198bdc5c6ab018ed9ec4d39f3eedabb99f5b7b242cde48f3bbfa15fa64eeb5bc3b8e5bf87516a7b20d1f39b901ae13f483f07c9f851fe85d1e430ec9cb66e77b5d64,
  0x2a45dac74d313c6f4aa981abf048053324b5d0ef13854305424e1e82780d1a6eb2ebe0e45ab32b9ee0be4163d67bef7d3ac928de5a213b4a31241778227e77dba7b13957d44bdaba3586bf9da4cda0f81075509cdc69ac3,
  0x726ef41e27bac6bc99f3ae8a4ed599df4c8d3283d0d4ba86d3b3f558c407465847447b181f6df66fee87abb915c9c2afe2b56e7bc16f87472c538fc5c956deeef506f4638e42a317118a4366c956aca68fa0006cc60128db,
  0x8f9fba8c86cba54e726b6ba80f89226016c781f9d1556c5042d4659ed6bcd83557a92fc050f7107570d24a05728ef61769fac404c6dd81cb42aaccef506db650342c5e21500677569142d71ed1a1c9fa78ba6a4299738eb1]


private def packed (u : ℕ) := matrixRows[u]?.getD 0
private def inversePacked (u : ℕ) := inverseRows[u]?.getD 0
private def A : Matrix (Fin 88) (Fin 88) (ZMod 251) := fromRows 88 packed
private def wide (j : ℕ) := CriticalHigher.Hub251.spread (inversePacked j)
private def rowGood (i : ℕ) := (wide i == CriticalHigher.Hub251.widen 88 (inversePacked i)) &&
  CriticalHigher.Hub251.wideRowOK 88 packed wide i
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private def checked : CriticalHigher.Hub251.Prefix rowGood 88 := by
  let p : CriticalHigher.Hub251.Prefix rowGood 0 := CriticalHigher.Hub251.startPrefix rowGood
  iterate 22 let p := CriticalHigher.Hub251.extendPrefix p 4 (by decide +kernel)
  exact p
private theorem injective : Function.Injective A.mulVec := by
  apply CriticalHigher.Hub251.injective_of_wide (by decide : 88≤256) packed inversePacked wide
  · intro i
    exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp (checked.verified i.val i.isLt)).1
  · intro i
    exact (Bool.and_eq_true_iff.mp (checked.verified i.val i.isLt)).2
private abbrev entryI0P (s : Fin 88) : Prop := ∀ l,A s (finProdFinEquiv ((0:Fin 8),l))=smallEntry D M L (sel s) (0:Fin 8) l
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def entryI0OK : Prefix (testFin entryI0P) 88 := by
  let p : Prefix (testFin entryI0P) 0 := Prefix.start _
  iterate 44 let p := p.step (len:=2) (by decide +kernel)
  exact p
private abbrev entryI1P (s : Fin 88) : Prop := ∀ l,A s (finProdFinEquiv ((1:Fin 8),l))=smallEntry D M L (sel s) (1:Fin 8) l
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def entryI1OK : Prefix (testFin entryI1P) 88 := by
  let p : Prefix (testFin entryI1P) 0 := Prefix.start _
  iterate 44 let p := p.step (len:=2) (by decide +kernel)
  exact p
private abbrev entryI2P (s : Fin 88) : Prop := ∀ l,A s (finProdFinEquiv ((2:Fin 8),l))=smallEntry D M L (sel s) (2:Fin 8) l
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def entryI2OK : Prefix (testFin entryI2P) 88 := by
  let p : Prefix (testFin entryI2P) 0 := Prefix.start _
  iterate 44 let p := p.step (len:=2) (by decide +kernel)
  exact p
private abbrev entryI3P (s : Fin 88) : Prop := ∀ l,A s (finProdFinEquiv ((3:Fin 8),l))=smallEntry D M L (sel s) (3:Fin 8) l
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def entryI3OK : Prefix (testFin entryI3P) 88 := by
  let p : Prefix (testFin entryI3P) 0 := Prefix.start _
  iterate 44 let p := p.step (len:=2) (by decide +kernel)
  exact p
private abbrev entryI4P (s : Fin 88) : Prop := ∀ l,A s (finProdFinEquiv ((4:Fin 8),l))=smallEntry D M L (sel s) (4:Fin 8) l
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def entryI4OK : Prefix (testFin entryI4P) 88 := by
  let p : Prefix (testFin entryI4P) 0 := Prefix.start _
  iterate 44 let p := p.step (len:=2) (by decide +kernel)
  exact p
private abbrev entryI5P (s : Fin 88) : Prop := ∀ l,A s (finProdFinEquiv ((5:Fin 8),l))=smallEntry D M L (sel s) (5:Fin 8) l
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def entryI5OK : Prefix (testFin entryI5P) 88 := by
  let p : Prefix (testFin entryI5P) 0 := Prefix.start _
  iterate 44 let p := p.step (len:=2) (by decide +kernel)
  exact p
private abbrev entryI6P (s : Fin 88) : Prop := ∀ l,A s (finProdFinEquiv ((6:Fin 8),l))=smallEntry D M L (sel s) (6:Fin 8) l
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def entryI6OK : Prefix (testFin entryI6P) 88 := by
  let p : Prefix (testFin entryI6P) 0 := Prefix.start _
  iterate 44 let p := p.step (len:=2) (by decide +kernel)
  exact p
private abbrev entryI7P (s : Fin 88) : Prop := ∀ l,A s (finProdFinEquiv ((7:Fin 8),l))=smallEntry D M L (sel s) (7:Fin 8) l
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def entryI7OK : Prefix (testFin entryI7P) 88 := by
  let p : Prefix (testFin entryI7P) 0 := Prefix.start _
  iterate 44 let p := p.step (len:=2) (by decide +kernel)
  exact p
private theorem read_entry (u : Fin 88) (i : Fin 8) (l : Fin 11) :
    A u (finProdFinEquiv (i,l))=smallEntry D M L (sel u) i l := by
  fin_cases i
  · exact entryI0OK.all u l
  · exact entryI1OK.all u l
  · exact entryI2OK.all u l
  · exact entryI3OK.all u l
  · exact entryI4OK.all u l
  · exact entryI5OK.all u l
  · exact entryI6OK.all u l
  · exact entryI7OK.all u l

theorem spans :
    ∃ x : Fin 86 → Fin 3 → ℂ, ∃ y : Fin 86 → Fin 47 → ℂ, ∃ z : Fin 86 → Fin 75 → ℂ,
      ∀ T : Fin 3 → Fin 47 → Fin 75 → ℂ, ∃ u : Fin 86 → Fin 3 → ℂ,
        ∃ v : Fin 86 → Fin 47 → ℂ, ∃ w : Fin 86 → Fin 75 → ℂ, ∀ i j k,
          T i j k = ∑ a,(u a i*(y a j*z a k)+x a i*(v a j*z a k)+x a i*(y a j*w a k)) := by
  apply CriticalHigher.PrimeTangent.exists_lift (p:=251)
  obtain ⟨Y,Z,f⟩ := tangent_of_small_minor D M L (by decide) (by decide) (by decide) (by decide)
    (by decide : 0<22) (by decide) geometry moments recovery_identity
    sel A read_entry injective
  exact ⟨fun i => ![1,D.t i,(D.t i)^3],Y,Z,f⟩

theorem generic_rank : Arxiv.«0805.3777».IsGenericRank [3,47,75] 86 :=
  CriticalLastSlice.TwoPlanes.generic_rank_of_witness (by decide) (by decide) (by decide) (by decide) spans

end CriticalHigher.FrontierSeed.B47

namespace CriticalHigher.FrontierSeed.B23
open CriticalHigher.PrivateBlocks
open CriticalHigher.FourHub (Prefix testFin)
local instance : Fact (Nat.Prime 251) := ⟨by norm_num⟩
private def byte (w i : ℕ) : ZMod 251 := ((w >>> (8*i)) % 256 : ℕ)
private def sharedRows : Array ℕ := #[0x29fd98275f3db0d,0x58bd35c34850730d,0xf2e61546c6563b0a,0x18a13a12db14a1ec,0x7f39eb77fc869a4,0xc10b6a1d3fbc57e9,0xa89e35a966f3eb4d]
private def weights : Array ℕ := #[0xb27706904055f135f09078ad3a9487d52e574291660543a66b8c56e60000cdb257a917d86f00,0xb0cf6bdaa5ac18306b10f14e3ab5084ef9976c749c4004f3251d000045acf910a7ef4c300027,0xcf3bd567cda61ec7cb0c025636176929245425f7ebddbc84000062fada5ab3c24335450033e9,0xf26f12ca2345586281088d0f9746b584955dd3cfea1e0000f3317ac5bb9be2ce7de50078d62c,0x6b244de82e5c356911166b76752811141a3d1f1300002e4d702023c44f6401e7e90092268a5f,0x9518c85fafdddc8b87e5e5954c48ae36d61d0000c264c3622221a67d23e9abbd00f78d36a55f,0xa39676b4eeddcc98f75f8721a63bdb5a00002c26640b1d40cbefc231f619b60013d26af1c8e3,0xd9286cc118a5c4eb8e81aa8c4b6f0000128e893e0424b05d232068b6584c005c4eef47357cad]
private def quadMoments : Array ℕ := #[0xb5ca87730ba36c714da899539491437439d0100000000000000,0x1fc24eddf84b134d723d1d3a5e9ad727dfc00100000000000000,0x8bc4f9a355cd4cc2e8e9dccc974ab53312ef0100000000000000,0xad9859eb4c0ca055d9db203642cb6c262e220100000000000000,0x16b7888664ced239b99266a84a62f684c0350100000000000000,0x7632f223d63e7e1d040d35e7494f49c6752f0100000000000000,0xe2a1c066a2897329b2a1162518a3e97844de0100000000000000,0x327b09937acb06beb62dbff2852559c98b9e0100000000000000]
private def poleMoments : Array ℕ := #[0x6ae6058a88773c6274162bb54c685ba48685c297e3bf32e8d684,0x52d2fce1ade42dfe2b57b5f808a9b508d63e323b0d84c598722,0x1e3b2e3a5a3d7c706a52b26dc0f69615bd166b12e749469fd073,0xdf19817b54ab1df6828d98ca234f746046bc2283b80c9585a218,0x305f8aee4782972a6d51b04cb60abc91a5e7792ebfd56f81e5c8,0xe696cb4df0033f57bc2b9faab19ad17a258197218220675631eb,0xd2e876e6170563d7f9480f692bb4b578021cf7292497f1e34ddf,0xab2cc3f642e9bb3f66f129c7a6a6d590446cbfa4b3116e709c3,0x2b6b1a8ce647d30b65e3160384b59922cc02ab9d0abdb908c5b2,0xbd891b0044dc7f781e807a5a008f400595645c4831008e2eb8a2,0x2363314996d5b62b62214ff74cf9d015e3f36e609a564d1846ab,0x53a91922ed10b82997c191a7c52589c33555e141de47cf7a945d,0x1e51f4a8e496aa1fa36413903a07f9e8bb7da693e51a6b4d68cd,0xeb1a00403183db05407203002ef766e4b82e810a00ed9a5907c3,0xc1796bf842b4722b2ce1ec16f1dc6281e33ff8c99d8640f3b3ab,0xc7d6cc7b346d35a57df52cb29f06c45d3052e73faf1c14eb3ba0,0x58253903cbe8b04b129e9833948eea41ba87b588066a3df96f8c,0xa990900c09b5298c848a4c4c5ac1e4b62eed1f4444ad43cc6e5e,0xd7ae261a65997b04d2e83222c382122c1e45ea7c0452de874fe1,0xba83051402e08ddd5d8c68a3960faeb31a462e1b5d79ee32d5c3,0x31c06471743b082eb2f2b9f8dc75423c5e503a076790faf4c7cb,0x20e329319916c3a230f047b6f212a552d36d2b9c6e3a876c71ca,0x56cf49c77b93ed593c8facab702ce09228c7c22399574fae5b31,0xc0daa477026f24ccefb981e20e0fcd1318a10759bd69ee9d11b4,0x3384b6712325f8d1d3fa56952f138ec0b2324012020427c70b9a,0x891f21a4836ae0dbea1118932e96f4de2854a7dd8244bdc563c9,0x4c02de20b68c08749d9c7b63d3954cf16af338a0be32029c8af4,0x5dd2a00a4c2851cc3d487233719cc957f770a1eafa2f38bccd05,0x92397a4e2ee97d1414c275e01c449420e2e2862aded8a642d35e,0xe6d6f79c802e571fcc596d05385b44cd18f74d34b6b5c8a6b7dd,0x74fa600153ba51b22e6a4083bbd290579a44f4ab96507247cdb8,0xafc93a01f806af3a885fbc35bbc0765f3551c3107a500be5c37a,0xcd6157483c55e2c59ce74010c3259d832a2e9b067fb71b65b133,0x6d33093dda11b01493de2cf45cc1b68e6035a2a1752849dd1d09,0xab0af1d011cec2732c7630cb91b6238032a1d78279c2dda80cf0,0x995b885287a3543f0884ecc9f392b466cabde8b30b3ef96f5842,0xc93f2c4da7bc45da740bcaa1db95311ec169674246f8a3b99049,0x969beeb9e526717c34daf226872d52bf2b63c1075292d8f3d66a,0x792f89d0549a2523a6814b059166bb1ba85e436d18c258f5e6cc,0x4524dbdab67c8b38bd1edff8c1dd2b73446890d956496b6a32e2,0xf66f53b98b864499f3c9de3ec6aea952986f07e9bbfadb75ea4,0x35661ead6f91ab767bd49d78bec14eb6ddf15f7ee507133de283,0x6ef6be5a9498cfc8cabde7076d5a6a4b2f3703ab1cb96dad31bc,0x819aa25b25e8da52ca0e72927194af774d3738cd52c95ac6e139,0x9392a955b873abc1d05652ae59ead1b6134f5d4dc269b753e24c,0xf48e528372a6795d31df424d16cda2e979c48b0d39584392b3e9,0xaec4c0940c9bafd45ac21f0f5a3076c65f6d177c3c6dc0dd2781,0xd6790925f8e7d8969d67e92494efab6f627ea1b3905acbb6c18d,0xb8c69f84186cee87e00855f7e0845c3673e42c5be5e4e0042e05,0xe4602e27e2d65ebff8fa1a0259efad0fac6d788f0b71b949d0c1,0x853e440635c61e0bba685a7b21a655a5ba1346f43138a05b1d13,0xd6989631574847710ead53489066910ef54d495091273baa4dda,0x3ba0ea7409bed67f16c77f2088af29ad4779d847b0f65464490e,0x39d601adc92bcc43a1bcad8349e36f76f3071e495d1977ea93cf,0x461b2472c1023c5db28617c67db70b4f87e2eb01553c80ba3a73,0xe4acbb252053038a2efac1964eb0508e060278b748b2d7bd1c21]
private def selected : Array ℕ := #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]
private def restRows : Array ℕ := #[0x100f0e0d0c0b0a09,0x100f0e0d0c0b0a09,0x100f0e0d0c0b0a09,0x100f0e0d0c0b0a09,0x100f0e0d0c0b0a09,0x100f0e0d0c0b0a09,0x100f0e0d0c0b0a09,0x100f0e0d0c0b0a09]
private def recoverRows : Array ℕ := #[0xe622555a3c37f307b622b8d1b17696019c2955d192422c7c808cc25ab142bcd1576b40d03c762cd1df3b51d79d37967c573bbdf4498ef301806b51f4a0cbf6079c8c40d749cb0777b629c2d09d8ef6770c,0x757ea85c8f0f2782177e9b7b9d9a842a8c67a87ba42a26b03868c35c9d2a17e0c0c7d9bd8f9a26e07767177e770f84b0c0670300f769272a38c717004cb8bc828c68d97ef7b812f91767c3bd7769bcf9cb,0x3f039d7b9283c98c0203247fddf64299ae199d7fccbb49bfe2470d7bddbb192ec4fa766a92f6492eafc9b33c9a8342bfc4c9851e3a7ec999e2fab31ec9c27c8cae47763c3ac26ea702190d6a9a7e7ca74a,0xbaca8a20bf06ab4ea7caa04da7202fd26d608a4d4681a68636ed6220a78113b8524f1cd5bf20a6b89da108b2c8062f8652a1c998e0a7abd2364f0898ed27be4e6ded1cb2e0278a4ba76062d5c8a7be4bb0,0xcdb3629091375cda52b3334d95606190f3ad624dc361cc7037ebbb909561cc3b39d7d60e9160cc3be15f9f97a4376170395fe1f88cbc5c9037d79ff8ade87cdaf3ebd6978ce8752352adbb0ea4bc7c236f,0x337111e5386f1f843271d3cd1e81363147a111cdada0ba255e2d89e51ea067d9551b58d73881bad99bf17325546f362555f16ab55a691f315e1b73b56ba58384472d58255aa513c232a189d7546983c21b,0xc4a29b4fba50406acda2b4e4207b3d633ead9be4584ace5e1971714f204a1c8b1677922dba7bce8bc5a43b3691503d5e16a4762944cd406319773b293d210b6a3e71923644211b7ccdad712d91cd0b7c3c,0x7a33542e6bd2c12f2033e11f0ba2cb8068d8541ff397c1e789804e2e0b97051c015231a56ba2c11ccf6b91519cd2cbe7016b2bc18fa5c180895291c1d143282f688031518f431a3520d84ea59ca52835c4]
private def basisRows : Array ℕ := #[0x1000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001d5ae3c80c47ec238e29bdcb21c1b6db1b0b8d0e2ec2ff01e1e5227855c8cf7a089f404672854da5e0900b90f9870694ce5e344568ac0922183cd48acdbc19a0442a2d3ad82cb4eae,0x100000000000000000100000000000000000100000000000000000100000000000000000100000000000000000100000000000000000100000000000000000121d0d10edec2e3c281c3e1e68fbb33b38ac8166301f7728d63f98ba07465971c4611adabded176b203f47a9807aeaa526c6723783250954a8cb38759e35c8f672c70d4e45e16ec3f,0x1000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001aff4bde0133be0696ec6381b9a197feec50a3e6864a848a232c39ba210a3849c68a35d56b64d35769dbed7e9a48c0159c492e08fa81c6c20c6e3398f67a78383784966c94f1361ee,0x1000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001d2a1be5b2a401365ab100c677ee245227a726b27f4d5bab80161a8eb47c3771f9cea32646292e4a7bc8612b0b41bdc4278e39ce31bea6e507c2e18e21f0584d2ced9caf8bdae4384,0x10000000000000000010000000000000000010000000000000000010000000000000000010000000000000000010000000000000000010000000000000000019063dd610b7e06cd03ada738486834ee7828464d164371666769a87acfbacd9be5face3c679cbdc3c0ccf905e104dc067ab3aeb82f02eb0e557b7cd98149b860a572a5ecb7a21ef4,0x1000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001712fa5651120a650c6f82ec87eb4208b3b97428a301055e06508f80cee8ee3d907af7f3a80b80fb5a8f220b32d19d65a67e5036693da9381362df129c739f73b504a04278f965cda,0x1000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001167050196ec7b47de2d618c70f10502b6fba0312d2488a9de641f02074bc8ec990aa76d123ad93709f42c53237743b3cd498905b7fbebcb7b6a679792bf3322ce7dbe4d20e9a7b5e,0x10000000000000000010000000000000000010000000000000000010000000000000000010000000000000000010000000000000000010000000000000000015b793c407adf6baa8712432e0e44d46de279d2a0188bec6f573d78c878b93445ab8281c6ec1454601b3ecd02a1e36c3ae1a343bce73a759773ca53618be65db0b8b20ae133492179]

def D : Data (ZMod 251) 8 23 29 38 1 3 7 where
  z t := byte 0x8702384d8da1f91246c76a7307bf612989b81604cc58e07ae4de30ec5157d9ddbda8854b25bc t.val
  t s := byte 0xda0a9e1e2227f13d1263e16556b7ca7678dc1564455cee8e37d043aa6ef87cc27218ea544680 s.val
  hub i := Fin.ofNat _ i.val
  left j := Fin.ofNat _ (8+2*j.val)
  right j := Fin.ofNat _ (9+2*j.val)
  G j i := if j.val<8 then (if j.val%8=i.val then 1 else 0) else byte sharedRows[j.val-8]! i.val
  owned i j := Fin.ofNat _ (8*j.val+i.val)
  node i j := if j.val=0 then Fin.ofNat _ i.val else
    Fin.ofNat _ (8+2*(8*((j.val-1)/2)+i.val)+(j.val-1)%2)
  shared j := Fin.ofNat _ (8+j.val)
  bary t := byte 0xadf522606f1a355bc4b00c43cf87268b31ed7bc8155a12e46ecbb2f0a91826dc03c045eb192f t.val
  weight i t := byte weights[i.val]! t.val

def M : Moments (K:=ZMod 251) (h:=8) (r:=38) (n:=29) (free:=7) 17 where
  quad i e := byte quadMoments[i.val]! e.val
  pole j i e := byte poleMoments[8*j.val+i.val]! e.val

def L : Recovery 8 9 17 8 (ZMod 251) where
  rest i l := Fin.ofNat _ ((restRows[i.val]! >>> (8*l.val))%256)
  R i k v := byte recoverRows[i.val]! (9*k.val+v.val)
  P i k l := byte basisRows[i.val]! (8*k.val+l.val)

def sel (u : Fin 64) : Channel 8 9 7 :=
  let z := selected[u.val]!
  let a := z%11
  .inr (Fin.ofNat _ (z/11),if a<2 then .inl (Fin.ofNat _ a) else .inr (Fin.ofNat _ (a-2)))

private abbrev baryP (s : Fin 38) : Prop := D.bary s = (∏ t ∈ (Finset.univ : Finset (Fin 38)).erase s,(D.z s-D.z t))⁻¹
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def baryOK : Prefix (testFin baryP) 38 := by
  let p : Prefix (testFin baryP) 0 := Prefix.start _
  iterate 9 let p := p.step (len:=4) (by decide +kernel)
  exact p.step (len:=2) (by decide +kernel)
private abbrev weightP (s : Fin 38) : Prop := ∀ i,D.weight i s = (∏ j : Fin 3,(D.z s-D.z (D.node i j)))*(∏ j : Fin 1,(D.t s+D.w (D.owned i j)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def weightOK : Prefix (testFin weightP) 38 := by
  let p : Prefix (testFin weightP) 0 := Prefix.start _
  iterate 9 let p := p.step (len:=4) (by decide +kernel)
  exact p.step (len:=2) (by decide +kernel)
theorem geometry : Good D where
  distinctZ := by decide +kernel
  power := by decide +kernel
  distinctT := by decide +kernel
  cover := by decide +kernel
  separated := by decide +kernel
  awayL := by decide +kernel
  awayR := by decide +kernel
  regular := by decide +kernel
  individual := by decide +kernel
  node_inj := by decide +kernel
  pole_inj := by decide +kernel
  position := by decide +kernel
  bary := baryOK.all
  weight := fun i s => weightOK.all s i
private abbrev quadP (s : Fin 26) : Prop := ∀ i,M.quad i s = ∑ t,D.bary t*D.weight i t*((D.t t)^2+D.a i*D.t t)*D.z t^s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def quadOK : Prefix (testFin quadP) 26 := by
  let p : Prefix (testFin quadP) 0 := Prefix.start _
  iterate 26 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev poleJ0P (s : Fin 26) : Prop := ∀ i,M.pole (0:Fin 7) i s = ∑ t,D.bary t*D.weight i t/(D.t t+D.w (D.shared (0:Fin 7)))*D.z t^s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def poleJ0OK : Prefix (testFin poleJ0P) 26 := by
  let p : Prefix (testFin poleJ0P) 0 := Prefix.start _
  iterate 26 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev poleJ1P (s : Fin 26) : Prop := ∀ i,M.pole (1:Fin 7) i s = ∑ t,D.bary t*D.weight i t/(D.t t+D.w (D.shared (1:Fin 7)))*D.z t^s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def poleJ1OK : Prefix (testFin poleJ1P) 26 := by
  let p : Prefix (testFin poleJ1P) 0 := Prefix.start _
  iterate 26 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev poleJ2P (s : Fin 26) : Prop := ∀ i,M.pole (2:Fin 7) i s = ∑ t,D.bary t*D.weight i t/(D.t t+D.w (D.shared (2:Fin 7)))*D.z t^s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def poleJ2OK : Prefix (testFin poleJ2P) 26 := by
  let p : Prefix (testFin poleJ2P) 0 := Prefix.start _
  iterate 26 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev poleJ3P (s : Fin 26) : Prop := ∀ i,M.pole (3:Fin 7) i s = ∑ t,D.bary t*D.weight i t/(D.t t+D.w (D.shared (3:Fin 7)))*D.z t^s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def poleJ3OK : Prefix (testFin poleJ3P) 26 := by
  let p : Prefix (testFin poleJ3P) 0 := Prefix.start _
  iterate 26 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev poleJ4P (s : Fin 26) : Prop := ∀ i,M.pole (4:Fin 7) i s = ∑ t,D.bary t*D.weight i t/(D.t t+D.w (D.shared (4:Fin 7)))*D.z t^s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def poleJ4OK : Prefix (testFin poleJ4P) 26 := by
  let p : Prefix (testFin poleJ4P) 0 := Prefix.start _
  iterate 26 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev poleJ5P (s : Fin 26) : Prop := ∀ i,M.pole (5:Fin 7) i s = ∑ t,D.bary t*D.weight i t/(D.t t+D.w (D.shared (5:Fin 7)))*D.z t^s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def poleJ5OK : Prefix (testFin poleJ5P) 26 := by
  let p : Prefix (testFin poleJ5P) 0 := Prefix.start _
  iterate 26 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev poleJ6P (s : Fin 26) : Prop := ∀ i,M.pole (6:Fin 7) i s = ∑ t,D.bary t*D.weight i t/(D.t t+D.w (D.shared (6:Fin 7)))*D.z t^s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def poleJ6OK : Prefix (testFin poleJ6P) 26 := by
  let p : Prefix (testFin poleJ6P) 0 := Prefix.start _
  iterate 26 let p := p.step (len:=1) (by decide +kernel)
  exact p
theorem moments : Correct D M where
  quad := fun i e => quadOK.all e i
  pole := by
    intro j
    fin_cases j
    · exact fun i e => poleJ0OK.all e i
    · exact fun i e => poleJ1OK.all e i
    · exact fun i e => poleJ2OK.all e i
    · exact fun i e => poleJ3OK.all e i
    · exact fun i e => poleJ4OK.all e i
    · exact fun i e => poleJ5OK.all e i
    · exact fun i e => poleJ6OK.all e i
private abbrev recoverI0P (s : Fin 17) : Prop := ∀ j,(if j=s then (1:ZMod 251) else 0) = (∑ v,L.R (0:Fin 8) s v*M.quad (0:Fin 8) (degreeIndex v j)) + ∑ l,L.P (0:Fin 8) s l*(if j=L.rest (0:Fin 8) l then 1 else 0)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def recoverI0OK : Prefix (testFin recoverI0P) 17 := by
  let p : Prefix (testFin recoverI0P) 0 := Prefix.start _
  iterate 17 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev recoverI1P (s : Fin 17) : Prop := ∀ j,(if j=s then (1:ZMod 251) else 0) = (∑ v,L.R (1:Fin 8) s v*M.quad (1:Fin 8) (degreeIndex v j)) + ∑ l,L.P (1:Fin 8) s l*(if j=L.rest (1:Fin 8) l then 1 else 0)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def recoverI1OK : Prefix (testFin recoverI1P) 17 := by
  let p : Prefix (testFin recoverI1P) 0 := Prefix.start _
  iterate 17 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev recoverI2P (s : Fin 17) : Prop := ∀ j,(if j=s then (1:ZMod 251) else 0) = (∑ v,L.R (2:Fin 8) s v*M.quad (2:Fin 8) (degreeIndex v j)) + ∑ l,L.P (2:Fin 8) s l*(if j=L.rest (2:Fin 8) l then 1 else 0)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def recoverI2OK : Prefix (testFin recoverI2P) 17 := by
  let p : Prefix (testFin recoverI2P) 0 := Prefix.start _
  iterate 17 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev recoverI3P (s : Fin 17) : Prop := ∀ j,(if j=s then (1:ZMod 251) else 0) = (∑ v,L.R (3:Fin 8) s v*M.quad (3:Fin 8) (degreeIndex v j)) + ∑ l,L.P (3:Fin 8) s l*(if j=L.rest (3:Fin 8) l then 1 else 0)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def recoverI3OK : Prefix (testFin recoverI3P) 17 := by
  let p : Prefix (testFin recoverI3P) 0 := Prefix.start _
  iterate 17 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev recoverI4P (s : Fin 17) : Prop := ∀ j,(if j=s then (1:ZMod 251) else 0) = (∑ v,L.R (4:Fin 8) s v*M.quad (4:Fin 8) (degreeIndex v j)) + ∑ l,L.P (4:Fin 8) s l*(if j=L.rest (4:Fin 8) l then 1 else 0)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def recoverI4OK : Prefix (testFin recoverI4P) 17 := by
  let p : Prefix (testFin recoverI4P) 0 := Prefix.start _
  iterate 17 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev recoverI5P (s : Fin 17) : Prop := ∀ j,(if j=s then (1:ZMod 251) else 0) = (∑ v,L.R (5:Fin 8) s v*M.quad (5:Fin 8) (degreeIndex v j)) + ∑ l,L.P (5:Fin 8) s l*(if j=L.rest (5:Fin 8) l then 1 else 0)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def recoverI5OK : Prefix (testFin recoverI5P) 17 := by
  let p : Prefix (testFin recoverI5P) 0 := Prefix.start _
  iterate 17 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev recoverI6P (s : Fin 17) : Prop := ∀ j,(if j=s then (1:ZMod 251) else 0) = (∑ v,L.R (6:Fin 8) s v*M.quad (6:Fin 8) (degreeIndex v j)) + ∑ l,L.P (6:Fin 8) s l*(if j=L.rest (6:Fin 8) l then 1 else 0)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def recoverI6OK : Prefix (testFin recoverI6P) 17 := by
  let p : Prefix (testFin recoverI6P) 0 := Prefix.start _
  iterate 17 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev recoverI7P (s : Fin 17) : Prop := ∀ j,(if j=s then (1:ZMod 251) else 0) = (∑ v,L.R (7:Fin 8) s v*M.quad (7:Fin 8) (degreeIndex v j)) + ∑ l,L.P (7:Fin 8) s l*(if j=L.rest (7:Fin 8) l then 1 else 0)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def recoverI7OK : Prefix (testFin recoverI7P) 17 := by
  let p : Prefix (testFin recoverI7P) 0 := Prefix.start _
  iterate 17 let p := p.step (len:=1) (by decide +kernel)
  exact p
private theorem recovery_identity : localIdentity M L := by
  intro i
  fin_cases i
  · exact fun k j => recoverI0OK.all k j
  · exact fun k j => recoverI1OK.all k j
  · exact fun k j => recoverI2OK.all k j
  · exact fun k j => recoverI3OK.all k j
  · exact fun k j => recoverI4OK.all k j
  · exact fun k j => recoverI5OK.all k j
  · exact fun k j => recoverI6OK.all k j
  · exact fun k j => recoverI7OK.all k j

open CriticalHigher.Hub251 (fromRows batch batch_sound injective_of_rows)
def matrixRows : Array ℕ := #[
  0xa7c458ce1f17796e316b09ed261fd39b9a0acb495d2846f827e02aa17055c7f6e2db4330d1e278751e6c1ee90f87d442b87628538aa75ca98a357e5040245c7e,
  0x350d9dae4b083f12f1ae1aa8741ab9cd0ad5728150ba34c8f682d33e322e57d653a2c5516bb62d029f88f12c7c56182d2b8e6a68935961cb9f82f8344b7848c4,
  0xf7ee3c91cff485b71c92963b54f3afa122a7c367237d972bd1dbb7f5795c752439671886a211e575600b45f255ed1f1783d49f6bb78f70f5b95db695c98aec08,
  0x120f82e06c904409cd9748540df05dd2659314beefa56c4c4374a85f87b9d792230c44c7a06deee589806211235d1b05bc346dd6810dbd8b78e6131b8bc9ed35,
  0x7e3365e574decfd481a8e0e4276fa2700a4c9f3283926c5257393069ee5af12ef383a717be77f6b6820ce3298625a3d1b799857fc81e0a1580631ec5d51f7b5b,
  0xb96c6ea76f8ec9cad3ad8ba301e705096f39acbbd5baac253c6c3d2bf99d6b8fe1ea803b712bb00cc38977573763f9b8611c58bb11814592e28ddad7ad59c423,
  0x57868dc920d5d3b629e0215f0e90b5e0d6b3d7f0e5d7fa548faeae859ca8ca82cb7b5f556c91661b35c7ab486398f8b98d8e9fa9307093ebf1b69581c9d59598,
  0xc0aec57ea8dd367624d724f16c495eaaac121a6214187d7c3ca842e98564cd6c3203d13c54455d1b5661a14913d2992f22f0141a8179696b5dd517f779efd21f,
  0x77483bc8ee8ce4f442177fe016dc6a7854f04af853380ca3ecbe704412844467da1ae2867f7b9d897c0f3c4a5333c240b57c9e215996322aeedfbd7aefaf40cf,
  0x440a349a59ddae2692b820999b32867601c13622a31531c4c5db0202405d69d78a592c4a9de85189e6c9e5884a58b558b41552bb9a3402f1a2f81caec1d43389,
  0x7ee199309c1275a2092c610037c43d4fc7793fe387a5db1b7e705e8f648ac16f0a3db09a03e41a1638baac8706c3ca5e9220d13b50db70653c821ddecc7c5c39,
  0xe5a272cb3d58e32282ced3aa9e682e1c62d24501c24794141f5ea91d76a2426ec25231e56e6e4ecf6087e978cedf1a4fca0734b28c71ba4f1214019024012cfa,
  0x9b0d94e4cea557f8e93e09b4ca8802403648c2686df09c637047ce6597cdbf730895c74d1b874623836d66689a758a389ec8dc769fe7bdbe4c0dcf2912373448,
  0x53134c31f1fac94777cdfa8b6a9bc6a86253757e6a8ee55be9cb24e3445448df72eece5dd0776ec593f837208573075099906b1697cd697859462a9e76729dc0,
  0xa0138fa5b46339aeb073abaddd689c1d32417de0545fd7f8cad1c94b7c51e31ecb638adeed41a184f225140fbb2bc15280017fcf63b454b3c7e56db0e6db5559,
  0x9854385d6fe3ebf1b71293b2ed155dbcf7d0960426a31c5f853eca83e8f6c0002e859f2a5f1116f33091f003654d8368e7277766855ba4a04c231e737ba73502,
  0x43436a6a7d33aa5aad1461612a79b123f2788a1fe3e1dba494976cbfd69c69b4d2078ce7671f4d612465b998cc2a16f2d8492fddc688d8b952724e33bcb07555,
  0xedc15cf8914b5596d6e92d9e65c3948f6dd5120af8da0492e7ddef943a83eee2e7452f2c7a1d62e8011443d4e515c8a26fa5740700056d0128d648492239ea42,
  0x53f6f0c0b3bac741a2af1458bf35a931559cd029b7025a2b46cee81ab606c8ad5fb2f57a916b8342af68944cb65acee0e671311f05647267421cdb208a5bf4ba,
  0xad7662c88d7bd37d9c2be1a0e31067d1b8b5c9957344eb62429827a8291245af51c6e378591668c2c68ba54478f1ca9936ee89719e1afa7d06682b284592d84b,
  0xea7f24124187a6f7bfcdc0d32f0ea691a612bc4fefb5c6a1b913b14cf5ab13aa5c1e616c360c1ab25a0614f285dc5a83d45863e487073dd1c5333a58427246ea,
  0x409f6cebdd0b90a4504c7984c3c2d1925a800c843eb0d0d79d04016c9fad75c13016717843818f8f370506d5e0eb1fd2152f1720a3463bab8fba1f1f6eca8daa,
  0x9d3cc04c73a509815f961677b5de13cf6fd60c97d2979520723a55193a839286b16082865e136736768ff732e418f7ebd95a4993eb23623cd43068d7b1f73632,
  0xfa8e337b12c09068af0b2b899952c01c2987aedc179c563081201c9c6ac11c24bb7a80f4e7795f5eed1b7d481fe769386b7c8687a36dd45c0af2852e799adf42,
  0xcdabdf510e8ea0d94c9ef164ac92d3973c0a200b7be083870f9a46e8250cfaba87c0991f97647a39a0712e6f2ae859add653c2d6edb8ec9812b6e36a613fbd07,
  0x3d3027e94d4e889a4dc238cd321116794bb1f2da38f82082830fe2f9c7442acd9189587076269a16cac1b1bba04676091bc32785a8b0ae9219960a9a891a379b,
  0xf9129aaad3e2c4da5780b4d6aa9136beabb70e060dcfc7c446e55ce452a851e47ff4b2ed919d27011ae446e1f70dc42c3b478a4890bb98cdeae025468f3caccf,
  0x50fced99c60dd0633c373565f49c3c8b13df42f5faaaa68b7c641e2cadde1cd8280f164f0188c09806d47b7dae728daba1df6f79705240da24c41084bc48340,
  0xd4167aca3aa194e869f7204ce873e63bdc7ab86f0e3b5a175b03ced13c2245b2cbf46e615260b169d386289971ae036e4340404552f3e23adb0461f665ee9260,
  0xaefa41f9c329e701c0364e101b7ff64d8bcfc25f9f0e97c775063aa76356d1584514b8c88d60cc04f0becc3482d10251ce42cd3cb80291939f601d7f005ec92e,
  0xc73e5182841570cd8a5b927e38b4094251616fb4cdac0def969898f57fbd13699d277fde77683aeb784772f9743aef8ce08a2fcb65ad445b4ad32a43f6d4b096,
  0xeaba4951e43539622e7f7c24d2c6984c164512ef37cafab6a1aa86b5b04ade0e836a54b9bdea177da421ed913af2033235f6a4c2b0356d0ad64b9c145ddf7213,
  0x1becc1f8756e73985207a23275604c98b93c47d0efcbec2e2f3d50a9e8ee55eacccd23922ca7a28b0ee1c25718eead224897c42e144c98251b447e7d5d4351be,
  0x581730210032c9a664823362d0313829b37a810bebc0e39c5b5e82621f6f0945ed1c76c5ab47422523103225a627ca7a16f02714d5d43274b1919f907fc61e27,
  0xb109d4c2485158a59ef896b7a1b6229fa694b71c314e920ebdf899b49d8ca9155be9ea8e8273d0dda90c7223b5b8ca544182c78ab1943dea24803ff9799057e2,
  0x6dfac99b28ca4797a00c142555a4ea856ca01955f4ce840e88555ba6c843844c99715c51dd6ea949365361961c6c97644b80d6a3668c0b4cafc8ef5de1dd0d9e,
  0x81435bd8b1dd183a653fb2c76c74469e97caadb3d74fa45d70f8035444ba119b540f0519f71f85d0e81e89d0d9babf9980df62586d77e013585e989c568360cf,
  0x68dc11c5a4bcc93770726657c6ad159b5e0cf98e6afaec5e34038da31c42135eb15e548dc49ae4bf4306f4d208b8e0f7e3bbd2f4a35b3cb8698fe64ea4b516d5,
  0x78841673e60100356abc168e2e4084e39b009ea57bdabdf16e283ce440b24e968e4f9cd13156aeaeb941df7fe109c16cc5e313266b85ade57c34614ba4c963ca,
  0x3daf57f4a7e44145a2ccae7d8b23a9dd52df28a352f8c7e87ec28ccf8a451e0ad67ce588846c9376155c3592c11d3b92f0aacac32acbce5af344420bc7a4803b,
  0xb68d5db5ddf135ec81eb165830d87f375c9da7760421de5f832e3ce6b4579074a902ac88edcbe0f3c9afeda29c77129fd37add5525c707625e212cdb25d75610,
  0x4098541b2b8756eebe7508bb4b35ebe79c181a4980f47a8183d879dc86cb08e82bb9c16a1ea6f4c3b9391c4a449667a73a3ac7ef1f82eff56b1c1adf42b76e24,
  0x35362444948a5306a7685e7bbc3fce421d121642d24deef33527e6000093b6a565cd9ab03366cfaf01d9143206152b3c4af52d43359627e96de78a201ee308,
  0x29394f629e43886ab12c05762f0e5fe5478dbf48a21cf8fa6129b74ab7ba4c493bf53248b85a634a61d4d3552eda6f2839bd7683623eab18a9c16b30f7c011b8,
  0xbf4b7caea5be1e2caf7e6a6185cf08783cd953afec4e62197b4651c4e0c5748aed317d20a889985d64b7015455601b7b4e4bf424235642ba27513afa93f4f977,
  0xb85f0c9abd68ccb7afe962083b7616be2b7131c13f0e0319bb3bb2bd7a810d4d1775952e2b0d70e34073f43253727f0a067a0a8f6e777284976d71343b7dd99c,
  0x331fdde85259b1e1d521caec38543891330f8c1dd231dfcfcf6d66592f4df6e0bdb608e3979d2fee52176dd15944c0b72f7af0bf5dd86388ad702df38480e26d,
  0x8a5ddc1116f7da043ddda0938467d5cc3831bfa2d807746f64f55ea3af93df63f67a9fbef7ea1b65be8d12c6cf31338bda222a64fa413ad7cfdf142630bc4c48,
  0x17a450587453558c0fb73a0a1d94c9a407034ab8946a33582af340417114af105adc8a0b99ba4ca797b8a181305bd7919c8908a010e91e3f0aa5651f7ae1b1b8,
  0xd66892a948da574f723beb90f4f67c887004adf441548684f2d5a85f7e3f0f824c23f5928d24ab7fa84405e0f1ba69ce1ada7c7360c591309124efc43bdc4a07,
  0x7b50191452b1c45976ab3f640c766803ae343b2d97970c3684a4251988e2709de69950b99a893e26afc46ec5b51de43ecf437bb5edd66bd5ec8a5b081466524d,
  0x6abd08cc917be927486852559ea3cb9a32489a156923dbf24bb0852aa04a2f7f860551de59d9a6ba505132e90995e6c52f6fd586f5bc0191af8dd1b8378f54f8,
  0xe975e95f96789e7714f3e8b95c49ba1ceeaabf8fef188ae51003c3e1ea19747deeecf3243faa17abf9b471b043e025cdea4dad06be0535afa6ba2ce19be09daf,
  0x3ae3a5ca9d5ff89479afda75277f3a93352134387854ab4ac9bbcdc82cf4f0f3d9326532a5ed4bf5827b7e035c5958e82f71a3591ad933b0adb48cf6e58864d8,
  0xc231790a7ade3bb64eb3bc3b5232bd97c173a60c03203c3d2e7e54ccc5c0e382387b7d57f963124669d26474c4da97cbbac28ed47426f9b993176aab827e5fb7,
  0x43214afaac0b8244705c60a4f32fb241d703d3ce16d111dfa400dc04dc461f5c6637f50902e655242d58a8bd1b847cb3f1729abd010eb372ba8051ba5a61ed6f,
  0xcd9482273ca821c686d38570feaed7e024b89650c496c351ce9e4baa689a585d2f5af00e8a74de42297d25249ce340361b316dd1b219c2e229aa607725af579,
  0x509fd6273a5db5306627225f891fc237cd533c408eb4847facbf208761b7ad4bc446c30ad6bce20a54d6602851020aa8a6b772f65885e6579886705b028eb81e,
  0xa3783d5dd128c78f6b16e65462b73ec7256fad5f3abddc1d678e3918091babbb6ea148908369669424b43050e3910f8ea7dfdf9b3493b8e41304909e856f4901,
  0xe1aadef84492eb333316570291bb74a43fda1abd74dec25749e690259ff30b910cbd54ee08b01ba9be7a162f04497ed86ee0a75e3e3ad1abaece732b87cd8e13,
  0x90f4c9bc1aec56cb13b0730b1958c1b4c2a7229cd845224eb9b6182ee2d3afa12d3582780bf4ec49d86b0c0d3be524090475eeae35ec6d8e002d5cbe2a4decbe,
  0x9a54ce2aac0baa23c1c000a25d9e041c2941fa501d7ce5afd8ad67f75db2fa8cea477c75902a4e98cbfa097820961e419ef0dfab3e3f9038976a4c265370b7da,
  0xc445a7c6b16061c7acc94ab3d515e4cd40357edf0326c3614bf75f3c0361ca655ba11ac4183a898e5410c30d6b2bb78c50c963b776a7061f4a6e0671f72fd47a,
  0xf4d97784ee0ee5ba350d69e92a130ed053319a5993647522b7cb83b50c4fae2d3d4733082ed1698ce8ba330c4d14b98935f25e05b519d81134e53b280ef32974]


def inverseRows : Array ℕ := #[
  0xe1dcc4ed286f65b7302207139f32c25e1884ca35ccc532271c7ae5a48e56bea3ea85030c85a20a06b88ecf0c192c48b09724dd65a98b895836b1290c9436b453,
  0x3d87137be00b9ce8b2c7f1d5820c2b6ca144804afa709bb770a9aa16249e04c081d31a19db8e0da0c5c78edf77254565cc89aed624795c1ddcc5db8507ed17ae,
  0x915e9acf08cd7e405ad91f29558234de98b887645e4792487e3acfe534311993f13e004cf956c989d54fe1d71601e6afa19c9098b877a3dbe4bc44cc7ae5a0,
  0x9e5a76c1590acf32abc23faeca129b4e643a13e1198534f30f038cd06f1615df95666c4bac91f03d7ae23cdefa316e97518b4202054d5f37dec1a96d548f2266,
  0x525b18992d9bb4151b5fb74262e821e595c48878292e12c72aa0542611e442f84696e705e09ead08f8760103f877700abfc6f30b7ff729812698a2166214a4e9,
  0xf73c085b8d7322517a334865a7e88ffab14f73503b7acaa99275c2465994a6777dc053efdb949bef972735103619436ac42f4704b3e54e4388a55e145f3015bb,
  0x725e54c5e4a468047c61b0b5ea7e00f487c465ac696b32d75b98c44f4ccd750505eb1f2df2f0d07903dfe724d828e4257a55906ce153dadd5a4418499c3d383c,
  0x2fc3a495a6941c3c231e8ccc15533d1b22ea1226c71253a99e15e4ed5c58a7a784eead9c362e65f63a47b2a4f359cd3dc9787da6a4bb3d172d4ab3ec3391a3b6,
  0x597a9b8773d9a875cde5b4e9ad1120b028c798a85494de1643425496d1a1042417c3658804c79b4c5da42b22e0aada849737736daee6749ab38c62da4596c200,
  0xe6c181654655f61856c2e95c421a470c9e1f32ba8d3016ced7b87e2797127376df4285728661992b8e84db19702eeb3287f59569be7a578176ac4a38a76709ab,
  0x249e26bdc2c76218531b8a7945d42d372dca6c9a3bea44a3ba66c900cb156ef75337b6469259f9f90a2bb416c16ab5bfca673213e911001a712e891c5e253d0e,
  0xccc352e8a0d1ce72675eb01ec913dbf31a330062dd982f094525dee0853856ebc90c6957bba2dbacdef67a80266b4b2d61eda22e422376681c187a2f7d9cd2b4,
  0x158b7baadfd252b5a4009b2abb321e4d7f2d3dcbec55b7c641545e20954905ba2bc7cf1e42a0b4d758d86d5550bc91252b333cf215c8d5b0bf9e9a7f36e95991,
  0x8fd90a1a21090e52735975cdd7789f8b6edee1b49891b12c6877618bf4935f04b1d58fb3b37a4fe91d6aa625227491325c074f685b454d986cc6d7427910b4de,
  0x65dae1d459605c7a0db51ce0e273993f966216e108c3d9efa804309fb38f8f30259f0e95470306c3809b1e578ba505988a6b6b95cada64485d034a8e007745bf,
  0x2919b9d9c76df09fed6c9f23e10705c83c28793a938b0ce31711eb9e26c053bba13124f89be555edb09a353eb3becfd3a00f7618dcb7aa93dceb796b2c7fa994,
  0xd458a07600227f014c8831a17adc2df59f5b3c1da25245db3460bd21e8f82f4273315defa3fa1c1909bce276f1ea2b05f749d66c2f1a4334d5d519f5d1913711,
  0x6f031cce4e39f2e474e99f15ac173c65b382d3d34007842daa3253f3e50d6352c2a5709d4dd157cc26c2bf76a506bdb2c62c43d89ca813fa787e1d8d6aa4ca92,
  0x4dba9b0e7134dee71d95e620dff11c68c0c667904704dbc7ad8238d7ef5f1d8890c54b3c137ef22811bb402a67e8d77bed909008cef2766b440bf78e102ef27e,
  0xaecf57edcb37284043a449f0d13b553354f9995e4e501f14363a92d50ae84a1751672ec0b380628b471c5271c58b6374dc2a3baae128f13024625a8978dc6026,
  0x52839a39cd9ee6b651c57f6489b3c053ce9377b203904b9a975da6aa98ce41a40b1b08c70ac49fe2bc55e251a25bc763d142bfdf9f2c8dc9f981436f8f18ab71,
  0x70283250141a278af8963f93f1a9a2a9d0f424e59135bd7ff71af7a16c4e852ea3ed05ccf4173d86f2be68ca39017ef1543636c6f452acd464a2cce3e22a0b59,
  0x5b4c5839c858bf834587daa853d4ae689faa0cc922ca89f6e2942ed06717070fa88f3ea4667719cd809aed6963927a371a6f9b268d91ae9b20af82f1b4f9639b,
  0x8f8befbb6e03b2aa45435e80df8e8d87ea83aac62875ac392094aa8f09934d1dc87f5e6cd8b4a8b46ab4763a9389de92138cb4d9839fe60d1dbc3166d8901653,
  0xbcca44ec5b03cbf5a6194b92e70761c4941ebbb7d023598d3f2838e945574ec0865f11d8bb1d799e3797547b2f6ecb9f1e3de16bd0087510ef6b19546844e5a0,
  0x58636edd34014a8b6ac624e275a4ddd4142c471a7ee49c7dab0b74789075eba0e534087f06c2bcae5bbf32c6209235c45f01c7307180837e377865981a468a90,
  0x60f1596218331ee0510bc79bda1b2a2cf5c15903d246ebea6499eac9b4cb738eea15c5b38fa0e211d269a50353b931a1bb7262a9bab48c2110a88382b7e1da9,
  0xbafaf3c0bf9d34c0285496f0af7e8c9a9a7fec22f451ca3bf9e5ef5bf66100a2791ea38348ba66b7a04ac9c27c808d4c9a3c980a30767b242e0deff81965c35f,
  0x5a0502100f85caec9b24c084843d1dac6d16e5659d05f4e6de79b76dbeba1d3e6beac2075ff9c20df8c7418ad0d142540c427d2bc1f6ae430be18e1a2493b8d0,
  0x6468c326572e36a65c72ba8c42e8748cf6ae4834d48e7f8aaf1db954d62f055d42d9cb494ac5bb6e9a8eb1c66b40d487c1ca1df7bd37d9ede7024a823ef8e52a,
  0xa0d4b273abc2f14a43121ced9bd6b6556c780440062725352697299e1f7baab2437ab20b5a874b2291533494f77d4d3b7d77ba293a1a81a413a37f05479a6af7,
  0xd77530768ab2a798d7ea29d3868cdab9469e02cf7fb9534c775145780aafbe5e59ec491f0018394a700ab615e0e04c8832de8b3a0f3348c3206fe617e1c379be,
  0xbb28cbe5cffaf4c0770431f85b5477dddb18bbb28e767521c37054821630e8740a812de232f94198b56af8efcc49086197a73f9aab5c429cd536678cf6a56db1,
  0xa88471e16ddb445be02847bc4fb6b547397c4d843bb8c8b6adbb2bfa6e552bcc14c2dcd0400f32664ba6287664031098b2def523bc6389ab64947b685c3a9503,
  0x15ab317fc013016b01279df46bde60348d78068aa6112e3c4fd5f4c8630d7ad4563971f90147861fec762e6f36b145cc846f6689a9c65d86b593de2b92f3fae9,
  0xa625519e3a472fe982de0b59e46bd8b68b56477e3251ea6c978c3a5c5ea8ae239c9b0ef7b662614050483de61ed762c4c06ba6b4693289e757901b2cdf125f2f,
  0xafb077f97d8c21837b7caa26a7957ea12845e25e030d701c166a35904ea4a41d9d81c53ca0016202821635a0322e9d1505dbceb4b79be66e1c66d14454220774,
  0x1c659f79a2a20687611746f5f9af3480f0afd5467917c414016a1b2d917af0cc9f4901ce60f07cf1378fd5afeb5fb1cfb377b844930ef3a9de160575aaf062b9,
  0xa9e10e6a6c75e848c5c2e1e045c301585981da3ab145063733b7a8685e457f4ad7c0d0908bb39993e535ba115991f0536180c66225e249a37b8ac90cbe109a7b,
  0x88b45730e0653b24821b5a3c073a703e6485ebe32bc13722c72de66e1d7ce8d4442a92c10276918b85540ef0a987ba3c7f32a9ca2d3889bff2ce494e99769ba8,
  0xdb8bdd883b34d6e5400e47674938588b9f22769dc3ad9b02f3b9f8bfada00a4fce40bd361702a7a3702f562994c81845088e4f9bb34a4fd806bb48070212ce21,
  0x85a1dbc48ddf01093dae7f3025057bcfa56a4f42166a1cada0a5b7f379a29dd1c32c0cdeb0cdf1fa9724158905934f537c6729d0d96980e5f9c72bb6cd71a1c,
  0xc997daa336bc41af77c10fbce32a6c168eee26eb1e146de98031a53240538f895d845787a95abed4502ff4654a35d1320cb39a4e1a89bb205162941868450cb1,
  0xa99c79cfe26903f6f0f28574e89d57063d4b4d1fe5623069308f55ae898184c60e6d0038e2426539045d08191e9b04e0f74371cd8356cd6f13a522c7eb754e72,
  0x19c2a2d54577dd86253a64f9bdfe7978fc9f96f4fbec009a4c2ab21f12cec63e5c4f97125c11ad90104216e49215ef7ee43296b9275f462db5ca2bc783c240e,
  0x23df892da063f1b0d97120b4f7a52a8c5976970ec5488350e48ad900ca7e09297a53aeb7ce818061f3dcc15120b7455caab85a325515c45eda904e5bf68ae98,
  0x8bc5a315bdbf1d1220a26690dfc5092d1cf51ddd2fd8ad72e1ad5ead4d1e5787073b06685e30edb04cbeb513675687d592518a4feac0e58796eb45025e33b364,
  0x535d7e7a7a007e1d1e2e327a4dbee6949f2b7bde1f1b34835337d7e8a59eed6c8b5351cc9845739d4974b4eec49a7688541679c59667467f7f4bb1dd99c1b4ea,
  0x64d40774d0f070197da37b97d0214548f9b3b8cecbda2ddec5dddd4d6d1b545c9c0f8692ed32a22933a38ab6771b4c8e2c562e81f45a7025f467cad96dc675c1,
  0x3b2442acf9888eec04d0f41930a0f4e9edda3ce45f43adaed35576c6f9cab688b589efe881f8c467f2d7d219ed54e88640286084ccccec765cf04ca42a7cb1a6,
  0x7a98d0b06503ed693c3aed89a9de0011ec5d525781409d565cefc564cdb3c64e5bdf77ef0544a6970e2dea34f5ce42b17d4ff1d6944a79f162cc40b4d52d4d17,
  0x5737844001e5f9b6bf6a8357cd95a2878e70f99735035ee0a0de1d24565196086cf27b4b2a3630fa843a70626ec8a443b7a384762978c3dc49f64e537f2d0fed,
  0xe0973402d3c00200dd148cf1f44bba9a471f6111154cb7a46012e70a2cbe77476f451cb00c4bafc999715de57da84b492c240ca55cb515d4a2864d4664080d8d,
  0x2f35f06f50139e24e44ab4b56097d7ec150ea21776e6ab8b3eaa1c14684f8038c236d959d42615bc893533bf941a700cd83fa59be13cc60a3b65bdb7819d1d9b,
  0x14c7c3137b5377ab2ea369d246006c88858a7eb6ed35890427a41f290759b41ec629567444b16166424237a60c42d108e71e3e9cf9e575bea3197a41c0e0db1d,
  0xea83021ae7ebbd099fb38e8ea45e84ce4c086ca32c0324f68f534b411e4fc3221e7e8dc45b99824dbc6c62ab2aca3d76433cf92d487002e184627ba3b8958045,
  0xc0d7f2d0afbbd45f49b675367f0520833beab49adce1f0bda20852ebdb707a9151b3c24a9e9a2b973da4621576784cba7d938ff5b80f47a961f5c5c307d60473,
  0xc7191c8e679ce314dd0e43f6c4aef5a4c77c6287f75ba90274da66f2f4f278e62d8aab28256d93be05d4cf95ca85e1edae6ff6cc571728753ad6f60b8bf6c776,
  0xe4ee5553d3473481303e47d6b18aaeb548c6acd49a86d860268aef0f317d84c324536320a966f8389966bbdf83d719c5d27f5b1ed3af172515529082cf1b2441,
  0x28f7c3f054f2814926333dd60767f230bee6e3baa8a034386fcd1059c208841c58eb69cd0e3d2040f49d60362c44c3ca20cc5d25185665b729eb3cee0bdf5c12,
  0x3b0878b00580f487cf393f994ace4f793bc5bae36759aa37300d9760865660df3e484ea2c84804f791298848d7bd4b497112cb85cd7a1fb507a6436b984624a5,
  0x87e44ce289af7d22ca0c4da75040ac1448c805dbf18586e70e81c02724f8d7187db07187b4b590d6a9342beb68a5365e20ee8f2dbcd3c7bb0401d26aa2258d5f,
  0xa3159e60980caea2565463f148e2a54fc3af4fb4e23895d12c46d2211b30115901262abfc93954ed5038d45b173b76e6aeee14b2aa201174cb0b2a392c044e46,
  0x766e5ce6dc4d70ae154aa15c4cad0cd185333e33ac6bae4a577450c632b6e4cef2e78b1d6993c32fb8fa37c96e05bf2d78160393a334001e2b78066363a205d5]


private def packed (u : ℕ) := matrixRows[u]?.getD 0
private def inversePacked (u : ℕ) := inverseRows[u]?.getD 0
private def A : Matrix (Fin 64) (Fin 64) (ZMod 251) := fromRows 64 packed
private def wide (j : ℕ) := CriticalHigher.Hub251.spread (inversePacked j)
private def rowGood (i : ℕ) := (wide i == CriticalHigher.Hub251.widen 64 (inversePacked i)) &&
  CriticalHigher.Hub251.wideRowOK 64 packed wide i
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private def checked : CriticalHigher.Hub251.Prefix rowGood 64 := by
  let p : CriticalHigher.Hub251.Prefix rowGood 0 := CriticalHigher.Hub251.startPrefix rowGood
  iterate 16 let p := CriticalHigher.Hub251.extendPrefix p 4 (by decide +kernel)
  exact p
private theorem injective : Function.Injective A.mulVec := by
  apply CriticalHigher.Hub251.injective_of_wide (by decide : 64≤256) packed inversePacked wide
  · intro i
    exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp (checked.verified i.val i.isLt)).1
  · intro i
    exact (Bool.and_eq_true_iff.mp (checked.verified i.val i.isLt)).2
private abbrev entryI0P (s : Fin 64) : Prop := ∀ l,A s (finProdFinEquiv ((0:Fin 8),l))=smallEntry D M L (sel s) (0:Fin 8) l
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def entryI0OK : Prefix (testFin entryI0P) 64 := by
  let p : Prefix (testFin entryI0P) 0 := Prefix.start _
  iterate 32 let p := p.step (len:=2) (by decide +kernel)
  exact p
private abbrev entryI1P (s : Fin 64) : Prop := ∀ l,A s (finProdFinEquiv ((1:Fin 8),l))=smallEntry D M L (sel s) (1:Fin 8) l
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def entryI1OK : Prefix (testFin entryI1P) 64 := by
  let p : Prefix (testFin entryI1P) 0 := Prefix.start _
  iterate 32 let p := p.step (len:=2) (by decide +kernel)
  exact p
private abbrev entryI2P (s : Fin 64) : Prop := ∀ l,A s (finProdFinEquiv ((2:Fin 8),l))=smallEntry D M L (sel s) (2:Fin 8) l
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def entryI2OK : Prefix (testFin entryI2P) 64 := by
  let p : Prefix (testFin entryI2P) 0 := Prefix.start _
  iterate 32 let p := p.step (len:=2) (by decide +kernel)
  exact p
private abbrev entryI3P (s : Fin 64) : Prop := ∀ l,A s (finProdFinEquiv ((3:Fin 8),l))=smallEntry D M L (sel s) (3:Fin 8) l
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def entryI3OK : Prefix (testFin entryI3P) 64 := by
  let p : Prefix (testFin entryI3P) 0 := Prefix.start _
  iterate 32 let p := p.step (len:=2) (by decide +kernel)
  exact p
private abbrev entryI4P (s : Fin 64) : Prop := ∀ l,A s (finProdFinEquiv ((4:Fin 8),l))=smallEntry D M L (sel s) (4:Fin 8) l
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def entryI4OK : Prefix (testFin entryI4P) 64 := by
  let p : Prefix (testFin entryI4P) 0 := Prefix.start _
  iterate 32 let p := p.step (len:=2) (by decide +kernel)
  exact p
private abbrev entryI5P (s : Fin 64) : Prop := ∀ l,A s (finProdFinEquiv ((5:Fin 8),l))=smallEntry D M L (sel s) (5:Fin 8) l
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def entryI5OK : Prefix (testFin entryI5P) 64 := by
  let p : Prefix (testFin entryI5P) 0 := Prefix.start _
  iterate 32 let p := p.step (len:=2) (by decide +kernel)
  exact p
private abbrev entryI6P (s : Fin 64) : Prop := ∀ l,A s (finProdFinEquiv ((6:Fin 8),l))=smallEntry D M L (sel s) (6:Fin 8) l
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def entryI6OK : Prefix (testFin entryI6P) 64 := by
  let p : Prefix (testFin entryI6P) 0 := Prefix.start _
  iterate 32 let p := p.step (len:=2) (by decide +kernel)
  exact p
private abbrev entryI7P (s : Fin 64) : Prop := ∀ l,A s (finProdFinEquiv ((7:Fin 8),l))=smallEntry D M L (sel s) (7:Fin 8) l
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def entryI7OK : Prefix (testFin entryI7P) 64 := by
  let p : Prefix (testFin entryI7P) 0 := Prefix.start _
  iterate 32 let p := p.step (len:=2) (by decide +kernel)
  exact p
private theorem read_entry (u : Fin 64) (i : Fin 8) (l : Fin 8) :
    A u (finProdFinEquiv (i,l))=smallEntry D M L (sel u) i l := by
  fin_cases i
  · exact entryI0OK.all u l
  · exact entryI1OK.all u l
  · exact entryI2OK.all u l
  · exact entryI3OK.all u l
  · exact entryI4OK.all u l
  · exact entryI5OK.all u l
  · exact entryI6OK.all u l
  · exact entryI7OK.all u l

theorem spans :
    ∃ x : Fin 38 → Fin 3 → ℂ, ∃ y : Fin 38 → Fin 23 → ℂ, ∃ z : Fin 38 → Fin 29 → ℂ,
      ∀ T : Fin 3 → Fin 23 → Fin 29 → ℂ, ∃ u : Fin 38 → Fin 3 → ℂ,
        ∃ v : Fin 38 → Fin 23 → ℂ, ∃ w : Fin 38 → Fin 29 → ℂ, ∀ i j k,
          T i j k = ∑ a,(u a i*(y a j*z a k)+x a i*(v a j*z a k)+x a i*(y a j*w a k)) := by
  apply CriticalHigher.PrimeTangent.exists_lift (p:=251)
  obtain ⟨Y,Z,f⟩ := tangent_of_small_minor D M L (by decide) (by decide) (by decide) (by decide)
    (by decide : 0<17) (by decide) geometry moments recovery_identity
    sel A read_entry injective
  exact ⟨fun i => ![1,D.t i,(D.t i)^3],Y,Z,f⟩

theorem generic_rank : Arxiv.«0805.3777».IsGenericRank [3,23,29] 38 :=
  CriticalLastSlice.TwoPlanes.generic_rank_of_witness (by decide) (by decide) (by decide) (by decide) spans

end CriticalHigher.FrontierSeed.B23

namespace CriticalHigher.FrontierSeed.B18
open CriticalHigher.PrivateBlocks
open CriticalHigher.FourHub (Prefix testFin)
local instance : Fact (Nat.Prime 251) := ⟨by norm_num⟩
private def byte (w i : ℕ) : ZMod 251 := ((w >>> (8*i)) % 256 : ℕ)
private def sharedRows : Array ℕ := #[0xb10a17537605b6,0x580cf6bb7a3414,0x1cda952f2f60dd,0x1481f5330de4c]
private def weights : Array ℕ := #[0xcdc8c7d2267d9aa4d9ccae77b71348c996c510c400007268afb68cec00,0x4072ea351badabad87a13225dc864a02123d00001bb7b42e5647600036,0x81446369c03bad36b2a1a4c1d13e9fbf00009612d193c403b5a5003ecb,0x9038ebd8f12d9d9c5a3d2466b36200000ef28eddf6786bdc3b001dcba3,0xba2ce9c76a66f7ca4e99aea80000a084db51600c27715e8400296782b2,0xc427685d5a031c073c1a000072a8ebad8b0f06bfeecca9000455186082,0xf6c0a14f245ed25b0000b7897bc219dc954642b6803e0086092bca138d]
private def quadMoments : Array ℕ := #[0x87378aba449bdbbf2aada2a545920100000000,0x1a224eb9f9417b4c096bd4d6f42b0100000000,0x4b787bd9647500935045a407acce0100000000,0x10a25482fe257c1ca8da07504330100000000,0x9ccf79d5c646f9926f6d0cca391d0100000000,0x51d50678faa3b366f41b9621f9d00100000000,0x2558cdc45716007e4616d9ee73320100000000]
private def poleMoments : Array ℕ := #[0x3abd063e7ef0f4c49ae4611354eca94f82acdc,0xe280f697167981e0e44e11b9503881e4a1016,0x7e8db96aa6a34e1357020c21aacbdc2b4ccdfa,0x6d6934d5843c847ee1db3ef715f71310276163,0x136f21b09425e7dccafaa26697f44d92d5846f,0xcc3196099e8c4bde69b25be7315999e1eec3f4,0xa8ac37a00d07ed6d0a5238f30fdd7e816878c6,0x12e3a3a2ec72cdb707c18de09b76e571f73566,0x7a1c299e038b3945c97cb89cc8cb4aa1ad1e50,0x741e53f75e2df70836312b77512ba52f26e4a4,0x265a257b01b1e9dba2a77934a8445d8d9611c2,0xd3d54243378ecab320a9dd6369d5159e03c580,0xde16e44126dd51f98c3b75dbc5c49301383c5d,0x7aa3252a73d01045c1a7b0cf174f4af79674de,0x3a352596f87d1468794bf3d34db730bff7e488,0x8008a9d123b95275174ec1847cad36df249303,0xe1aa1442c73d1eefafb77fe390955b9eb514b6,0xb8a93f24eded591b4e57e59494636d249c7d31,0x1d1f837acafad61c1d340769ed77a9388b897,0x2edf5f11f256bec32db38f833b6b5a622c429d,0xf14c0c4e9e6496225da0240fa2f323ecd1e5c8,0xdbf78b439e1073c5383e422f1b9303dc88505f,0x6a21298839e5591628b368ce3909c2c1043280,0x2dd553e570eb217b1e5d39bde0282352ccce73,0x55199b89b59ce74198595ae34b1d5e8309f655,0xa47e185053baf6d6f4a6875d9d461062ba76cc,0x25798fa4544972eb3f06d64fe9a1e07aa71095,0x489b4038e5e52af7596cdc3939a53809f5b7ce]
private def selected : Array ℕ := #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
private def restRows : Array ℕ := #[0xb0a090807,0xb0a090807,0xb0a090807,0xb0a090807,0xb0a090807,0xb0a090807,0xb0a090807]
private def recoverRows : Array ℕ := #[0xbbcb813aa6c697cb7ee3dcc40d9a81e37d165a02e63adc1696a21b9ba6c45aa20c66e7c60d021b66125a979ae69be75a64,0x5a6c02ebb01cc86ce5c4b7a46f7c02c47833ccc055ebb733028f545fb0a4cc8fb4aa711c6fc054aad1d0c87c555f71d0af,0xb87fab7d75f8817f2e37c8e32442ab37ab3283806e7dc8326ba85ce175e383a891b9d1f824805cb9d79f81426ee1d19fdd,0x8435201f562d9f35cd7e6be4c553207edfc04c40981f6bc0d1d2deaa56e44cd2065af92dc540de5a7a9b9f5398aaf99bcd,0xa6e87d46ddc758e879541b5407397d54e4f71b006d461bf7faee42a1dd541bee34398ec707004239a95d58396da18e5d8c,0x8656c97ec93323569ebd538c1ff3c9bdf63893b4e57e5338addb608ec98c93db2a5248331fb46052225e23f3e58e485ef9,0xec89925da28bd7899658d3f562b59258915af4c76f5dd35a3686a618a2f5f48626a6d88b62c7a6a64564d7b56f18d8648f]
private def basisRows : Array ℕ := #[0x1000000000001000000000001000000000001000000000001eb37a09310d8f9d2906efadc2c2ef1d5a753546818528ac6e97b874b78428810572362,0x1000000000001000000000001000000000001000000000001c6ae4a6f88c765492a822081210ea8c01040b20cd349e54b7d7036b615db4ce2b9863d,0x1000000000001000000000001000000000001000000000001124794866f0bb9aa73140d31c5237c49705f73c3a2ef028b9e1fdb0191566274125739,0x1000000000001000000000001000000000001000000000001a410f9c61c18246279ddba9d8c9c2e084b1e826fc4ea7daa48b83c2b88bc6fbdb0ef23,0x1000000000001000000000001000000000001000000000001b7100c44923a13bd4ac328b701f180ec15d93060edf36f787cc9bbd69fae2670b50785,0x1000000000001000000000001000000000001000000000001818eda56c46f96699071a0d79bbec69cefbe4772a75b4a5f0399a6e225ca9515d16737,0x1000000000001000000000001000000000001000000000001fac37d43d6444d210c25670a110c9f4552ad7c955b7adf374889e1b21a971466c7eabf]

def D : Data (ZMod 251) 7 18 22 29 1 3 4 where
  z t := byte 0x8a9a576193b6813dad7a98a40dd6782289d86da16bbec5122356eae563 t.val
  t s := byte 0x20edc10eaebc37e57cc46e3a17112513d5ec61733916999f0fd18f2b8d s.val
  hub i := Fin.ofNat _ i.val
  left j := Fin.ofNat _ (7+2*j.val)
  right j := Fin.ofNat _ (8+2*j.val)
  G j i := if j.val<7 then (if j.val%7=i.val then 1 else 0) else byte sharedRows[j.val-7]! i.val
  owned i j := Fin.ofNat _ (7*j.val+i.val)
  node i j := if j.val=0 then Fin.ofNat _ i.val else
    Fin.ofNat _ (7+2*(7*((j.val-1)/2)+i.val)+(j.val-1)%2)
  shared j := Fin.ofNat _ (7+j.val)
  bary t := byte 0xaa81f59bea15c83871883325be011fee6163e4ce02a773910649464be0 t.val
  weight i t := byte weights[i.val]! t.val

def M : Moments (K:=ZMod 251) (h:=7) (r:=29) (n:=22) (free:=4) 12 where
  quad i e := byte quadMoments[i.val]! e.val
  pole j i e := byte poleMoments[7*j.val+i.val]! e.val

def L : Recovery 7 7 12 5 (ZMod 251) where
  rest i l := Fin.ofNat _ ((restRows[i.val]! >>> (8*l.val))%256)
  R i k v := byte recoverRows[i.val]! (7*k.val+v.val)
  P i k l := byte basisRows[i.val]! (5*k.val+l.val)

def sel (u : Fin 35) : Channel 7 7 4 :=
  let z := selected[u.val]!
  let a := z%9
  .inr (Fin.ofNat _ (z/9),if a<2 then .inl (Fin.ofNat _ a) else .inr (Fin.ofNat _ (a-2)))

private abbrev baryP (s : Fin 29) : Prop := D.bary s = (∏ t ∈ (Finset.univ : Finset (Fin 29)).erase s,(D.z s-D.z t))⁻¹
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def baryOK : Prefix (testFin baryP) 29 := by
  let p : Prefix (testFin baryP) 0 := Prefix.start _
  iterate 7 let p := p.step (len:=4) (by decide +kernel)
  exact p.step (len:=1) (by decide +kernel)
private abbrev weightP (s : Fin 29) : Prop := ∀ i,D.weight i s = (∏ j : Fin 3,(D.z s-D.z (D.node i j)))*(∏ j : Fin 1,(D.t s+D.w (D.owned i j)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def weightOK : Prefix (testFin weightP) 29 := by
  let p : Prefix (testFin weightP) 0 := Prefix.start _
  iterate 7 let p := p.step (len:=4) (by decide +kernel)
  exact p.step (len:=1) (by decide +kernel)
theorem geometry : Good D where
  distinctZ := by decide +kernel
  power := by decide +kernel
  distinctT := by decide +kernel
  cover := by decide +kernel
  separated := by decide +kernel
  awayL := by decide +kernel
  awayR := by decide +kernel
  regular := by decide +kernel
  individual := by decide +kernel
  node_inj := by decide +kernel
  pole_inj := by decide +kernel
  position := by decide +kernel
  bary := baryOK.all
  weight := fun i s => weightOK.all s i
private abbrev quadP (s : Fin 19) : Prop := ∀ i,M.quad i s = ∑ t,D.bary t*D.weight i t*((D.t t)^2+D.a i*D.t t)*D.z t^s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def quadOK : Prefix (testFin quadP) 19 := by
  let p : Prefix (testFin quadP) 0 := Prefix.start _
  iterate 19 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev poleP (s : Fin 19) : Prop := ∀ j i,M.pole j i s = ∑ t,D.bary t*D.weight i t/(D.t t+D.w (D.shared j))*D.z t^s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def poleOK : Prefix (testFin poleP) 19 := by
  let p : Prefix (testFin poleP) 0 := Prefix.start _
  iterate 19 let p := p.step (len:=1) (by decide +kernel)
  exact p
theorem moments : Correct D M where
  quad := fun i e => quadOK.all e i
  pole := fun j i e => poleOK.all e j i
private abbrev recoverP (s : Fin 12) : Prop := ∀ i j,(if j=s then (1:ZMod 251) else 0) = (∑ v,L.R i s v*M.quad i (degreeIndex v j)) + ∑ l,L.P i s l*(if j=L.rest i l then 1 else 0)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def recoverOK : Prefix (testFin recoverP) 12 := by
  let p : Prefix (testFin recoverP) 0 := Prefix.start _
  iterate 12 let p := p.step (len:=1) (by decide +kernel)
  exact p
open CriticalHigher.Hub251 (fromRows batch batch_sound injective_of_rows)
def matrixRows : Array ℕ := #[
  0xbed03ff4d57b8640ab70e07b39873ad2471c7915c4b160a27f02705a05167ca9381ca2,
  0x832227329d3e1d125230699756be775414de217b5041633b7ad0e6bb714b9cca33e588,
  0xcc9880bfbc8ee42640c518c6d96d8726b5412fa62b4bbf4ec2a4aaa6b814768963b5a1,
  0xc952a21f7878a039ca9211e868e79bf4301ca3cbf23b5c121ca846364402a3d7462f56,
  0x97b4b928e69e538c4ff21f3d60ebf7e82a2df62fa996f7f89f93422dd2a16d11e15192,
  0x7a1130193809748cb193a8e8d4a806e52e2abf248668b366cfeb0778815f4482b12997,
  0x668bce13c4b55d80b47e326cee0eac56ca8e86da8f68d9f77c6c8baa406bd37f357c9a,
  0xd9b299848f73fa052da75d2c758b78730ad435270d43036eea7abbcb8acb47634380a9,
  0x74bbe56a1633e7763bb070e03d8cae33a3460385f3016f538fc43010a2bb4412796f23,
  0x11bf7c28378cf53ccc07974bb26ba58ddd80dc8527860dd5b4496caf3189956813badb,
  0x7cf74546d3c7888f6d56be5ba38628f0b3694ebb9d81e907f5f69c24f84e5804357e61,
  0x9ae4a72bc6345f90e5034ac3e7f32cfbe308ef1324dc995df1ccb4bd69e9c1104889c,
  0xde371a064898bef1e9453e5be46ee81e5adae78a5690de75c3e900e906caea323837c9,
  0x7ce33e748aeedc55675916473f41c71a2d9f3b3b649b492501daf61531440d94dd7667,
  0xf3d9d8040d528c2e25c4af0c7b579dba7542856a15e7026cec34e86538aeea141802e1,
  0xda71aef3b9a580b52947c31f004cc341b9ad1130046fbaa589e8cbae68b1be2da0457d,
  0x31058a1eba27d5858bea816471f0b5091365f6124d32d95d77a2f200ded910a6913df0,
  0xde6b43ab8547c43ed57525efab0583cc3b42e8e6b82e42f6561d519495f229525d756,
  0x68e0565fbb0f5f46ec338b937f2ff004356e3059f368d8f00b8ff8d17f197ee4417261,
  0x31e9ca84cb19b6270b87989896811c6c7e4c764c9a3f60598d9578970ddf4ac4674e54,
  0x5b5f6eaee4b5b004a49ab8048f6a0bc74df59068bf0978454aa04db72f6f80ca0e8a92,
  0x2e30ac20e5c38fdc74268fdf6bd60d423be4d6057d7431a763ab950b30a3df73e3060b,
  0x152a4a98299cd09cc55d43abbb76ed0f1f79674d5e0e88f7b6d36840c1f9308ee541ee,
  0x60662aad0325e719a56e61962e6df7b9b3e37b1b1c7684c7d2c3ddf266b9f1a9d72c32,
  0x798ed20e5483dc0329ae22466cd90fc9f2cf47c23a670ce4f5351682c2312562e9ac99,
  0xc02e94fa670e3d5b713ba0a431da304f71364b6852215e5a21f7889139cf598804e700,
  0xe5695723daec4ecec82a34d3b04a4704ed9c40e261bb0501456dae610bd16dd6b6a93e,
  0x7cf2838c8d520502377f617c09cb6212f1cc487695bd2ae47fe95681880a62f2da3f6d,
  0x860928773f69c18e6023c28c825333182876bd34e12982b313d30032c2c976006f6146,
  0x94345c71782f52deff2e9cda06d8d1edcb9eb3ad6d88f7429743f1c9f258aecd08b50,
  0xef7d2ddda894e46cd03e17094d761eed57b92828624736867ead6444c5114f6198af8,
  0xf29501a45d60fa93bb7167d1485ddbf3f8f5143797c1f108c39c0c2d66be1b639f89ea,
  0x3e40758daa5e5f4e8f3dd5e525a211482a7098a1d5068585d6bee369f6248abfb9c362,
  0x42eda98b351880769b69c444bda278875fd6d17577b6401c33d90c0511dba1b5160dab,
  0x1a70712a16566299a823babdef788cfab1ddeb5c1e56e96581d5021a38c8843d9ed562]


def inverseRows : Array ℕ := #[
  0xbb7bd960a66b9499a9cb9b17f48b5f8c0718194a6810a240b31cd7f5da45583e0cad98,
  0xdac5a3f9e2eaf9a635824d6e7f4856ca27cc12331814ee76650bdf5491c4ae3dd97ee9,
  0xbf68ebeb78a2f68a48c746c67bf6b8268673065c57b9943990541e8503b6b363b12aea,
  0x6e325410b71a1d54f4da6e91dfcd7941cb64541a6e8e8b22d0bf0f909fbc729ff7e268,
  0xdb88d876c68dbbabf1ee4857757d38bcf80629a700666a3c6306356674de0996b0809a,
  0x234ea4840b149fed7f1213da87598a172a5374b1bd643634bfb0909cdee3ed35f457cc,
  0x4c8c3c625321953cf8dd147a3eacec7569bdd9a1bc2e34d5a9f7aad89b19003756bb20,
  0x701cc43ef28fc056ed7fd7827490e3450545b25c44f92b463cae0f66dd0e885d65a868,
  0xe1476b1cb9023fabbbb5c3648a350bbb198bb9d7c27fa04c42d4d4a44f179a069172da,
  0xaa21311321f0d986f469a8b493edc915ec51380c48e67b63d7b81894805b1b3aea78c2,
  0x902213d76531b704b655c07e86d8748d6876a705c2ef97991bddbf04d7e78cd2019ae0,
  0xbb4096707f5c8fe8cae51c7590dfe09fab13dc2605e079c82d647eb7c2b3006055adb7,
  0x57cab6c202117db6f76e88c3f3b234c1b8dd802d0987ab894d35957574f5ac6e1367ab,
  0x224015bf8dcd8991663a44f0e0273338f70946175bb0cf01106613a7a90b6bddc54c93,
  0xe251523b01cede8e59317ad9a8073069285d6fe18f9f084da83dc6862056f7652780b2,
  0x38630106d611cdbb48d53a3451adcbc9b32646127ab240d330d10472e6c1f168addf02,
  0xd50d179eb67a6cf3aa7fc321d5f2d59b45f135ce2343e0357965745c25f56931b97322,
  0x47bf569c4d988d1d4791827ea9af9165f8abecf84308e59d62b4c7495c15f7e61fb6bd,
  0xd5120d61790d59025007425591ba16e6d44bced3a71a7595b4b8e29560089d0c4c3951,
  0xbdb706c1b0b673e4ba4c3abe305620d172000c5552b4b3d843642e05cc01e9763a31f8,
  0xf92596bb87680e13294d45127ab78a4760e6f0196b23c0c64c1454ed0ac69ade29119b,
  0xdeed6a66cf352aed999a4ed63c4d51cf053e5060af1cb2524e9d6ec391832b00c690a7,
  0x9f87798c6ed2bbd35e95f3c62507c1a32db096a43a58b1fa74955ae83337bb8eb9d32c,
  0x782dc34bf7612a8c96e50bb794774c948f58cc30b482004c7c2d8d9045807a09916d7,
  0x1301940a044b141f40ed6e239e2ed9a8eabea91fa1f3f10e2f3de54a98912571e99142,
  0xca606118373391cc3c376a398f646db5660147a0290d08eda2d76c0a10408321ce03f7,
  0x714b374dbc192cd8cf609d2b51fa8dd28e2dd1be867efa4ea7bddf9d0c9763e3558d70,
  0xc08a67402e3104577dacb672cbab895f3e371c7e0ea8a2f5f604c31832ed86af1a36ab,
  0x972213cebcf31d134f42aee729f612881cb51c99ba7fe1f8eb366eeb3dc6aa2a2877e1,
  0xa410ca0629d7d4d78b989c5579e2ae21a27d015a02593995560441c3338dd54f25d00a,
  0x3708d77c9f112bc6e6d1bed8936cbcf2b4727105e1807f6d29c6f11163c1b5d53a91a2,
  0x6aebbe19ce563bab717732fac5b63718879e76af9e6f741516160fa2aa20a4c21018d8,
  0x56964b56f5bb8055109400952c3e378215d4cb230a43052c2cdf8ba645b68200e53f50,
  0x614881149b77af9f701119ed783f38085d617e252ba4119d92c307d95e5e93080bf063,
  0x4853854693a19780357b79295d9e493069f6937ea29dbc40060688498d49fa89525b99]


private def packed (u : ℕ) := matrixRows[u]?.getD 0
private def inversePacked (u : ℕ) := inverseRows[u]?.getD 0
private def A : Matrix (Fin 35) (Fin 35) (ZMod 251) := fromRows 35 packed
private def wide (j : ℕ) := CriticalHigher.Hub251.spread (inversePacked j)
private def rowGood (i : ℕ) := (wide i == CriticalHigher.Hub251.widen 35 (inversePacked i)) &&
  CriticalHigher.Hub251.wideRowOK 35 packed wide i
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private def checked : CriticalHigher.Hub251.Prefix rowGood 35 := by
  let p : CriticalHigher.Hub251.Prefix rowGood 0 := CriticalHigher.Hub251.startPrefix rowGood
  iterate 8 let p := CriticalHigher.Hub251.extendPrefix p 4 (by decide +kernel)
  exact CriticalHigher.Hub251.extendPrefix p 3 (by decide +kernel)
private theorem injective : Function.Injective A.mulVec := by
  apply CriticalHigher.Hub251.injective_of_wide (by decide : 35≤256) packed inversePacked wide
  · intro i
    exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp (checked.verified i.val i.isLt)).1
  · intro i
    exact (Bool.and_eq_true_iff.mp (checked.verified i.val i.isLt)).2
private abbrev entriesP (s : Fin 35) : Prop := ∀ i l,A s (finProdFinEquiv (i,l))=smallEntry D M L (sel s) i l
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def entriesOK : Prefix (testFin entriesP) 35 := by
  let p : Prefix (testFin entriesP) 0 := Prefix.start _
  iterate 17 let p := p.step (len:=2) (by decide +kernel)
  exact p.step (len:=1) (by decide +kernel)

theorem spans :
    ∃ x : Fin 29 → Fin 3 → ℂ, ∃ y : Fin 29 → Fin 18 → ℂ, ∃ z : Fin 29 → Fin 22 → ℂ,
      ∀ T : Fin 3 → Fin 18 → Fin 22 → ℂ, ∃ u : Fin 29 → Fin 3 → ℂ,
        ∃ v : Fin 29 → Fin 18 → ℂ, ∃ w : Fin 29 → Fin 22 → ℂ, ∀ i j k,
          T i j k = ∑ a,(u a i*(y a j*z a k)+x a i*(v a j*z a k)+x a i*(y a j*w a k)) := by
  apply CriticalHigher.PrimeTangent.exists_lift (p:=251)
  obtain ⟨Y,Z,f⟩ := tangent_of_small_minor D M L (by decide) (by decide) (by decide) (by decide)
    (by decide : 0<12) (by decide) geometry moments (fun i k j => recoverOK.all k i j)
    sel A (fun u i l => entriesOK.all u i l) injective
  exact ⟨fun i => ![1,D.t i,(D.t i)^3],Y,Z,f⟩

theorem generic_rank : Arxiv.«0805.3777».IsGenericRank [3,18,22] 29 :=
  CriticalLastSlice.TwoPlanes.generic_rank_of_witness (by decide) (by decide) (by decide) (by decide) spans

end CriticalHigher.FrontierSeed.B18

namespace CriticalHigher.FrontierSeed.B24
open CriticalHigher.PrivateBlocks
open CriticalHigher.FourHub (Prefix testFin)
local instance : Fact (Nat.Prime 251) := ⟨by norm_num⟩
private def byte (w i : ℕ) : ZMod 251 := ((w >>> (8*i)) % 256 : ℕ)
private def sharedRows : Array ℕ := #[0x55f297dfcac579,0xf3367ac96e1358,0xd1a59fd55ac17c]
private def weights : Array ℕ := #[0x568b6098d5e1b810a9a843834c7792b28270000786c80cd0a0ec23ad8c02249000097d72b7dc31200,0x218dc357c0504583c15329ecf810e603000073a97e0d22bf9edbc26f9bb6000081bb855b7269620009,0xb430526134c210127087ce7e326600008716d8b92f8daa7663fa34b00000a7e5d96db261ab3500aa2c,0x7a378dd194ac4664539c4ed500005607c0cc3cd488f20d12954b000045e4eb47121f5c5992008445eb,0x42eb72d5763a3696e2ce0000b8bf3eec3e62c45690e2d6490000241d1b7bdcab5136365600ce46be9e,0xd17e849d8f776cf30000d6ef1f15c10937ca6630e37300000997187cd39a60eed1019600b7cea862a4,0xc42e3d44dbb500004268d1d9d3caf22b41bcb2b90000dc713374479685265be69089008f91631f0595]
private def quadMoments : Array ℕ := #[0x40f78babf9215cc38958f33364a3c71e01000000,0xbe73b47b820bc8197bd997e73df412c701000000,0x76e12bbfb4125229f59313c27ff028ce01000000,0xc1fae67a302c080c4be199af80706e2501000000,0xbcae4fec33ea24c0c31086178f27150201000000,0x7cd1d1d2b30de35b465c19e1828ca07f01000000,0x27a5a8f94851014236dd109cc0e0352c01000000]
private def poleMoments : Array ℕ := #[0xe357ae62c9ecf92273f2e98987a69c6d42c8956b,0x5db2606aa189b55819ac2a0ff36bbda43a8aee55,0xe2db99d1451f9d02c1ed720d8c5c355f065890f1,0x7ddfa4246c69c4cc27b009cc6e5d1798dd4d3398,0x2901f2832894cb6341adc8498f02e63bc93cd54f,0x7b605a1321789bc3c32a0818bbb2d16565ee8188,0x92befa8ca77a2dbc9ef04e7c1a160491e269bf75,0x7cdbb53112b66aece288ace73169b101a9af1655,0x431961a3dfa5ca0b1d521b7b77f01410411cc72a,0x3fccc659f968a7062e89253d863c6a64b56c1fb4,0xf790ba7ad816f309118d586d56202296745b80e3,0xb2ee84bf1acfd3087a76c0040fbbaad96d7ebcea,0x64247da989b5480b4d629fdf6cacc41070d38c77,0xf51d1f6c0b2237119741b62b10e85074aea36983,0xd224b598dc72c2da4fc88dcb17d712eba0877244,0x3ce519c9ec859ab8a6496f1d54d1f24ae12b1fbd,0xd8aaed9ad924709ac434e5f25ac8b0f2390a49c9,0x8e9bacae0966d399c9771ae65a4f3e91e3a4682,0x3a52cd642bd6da947f5d6bc1d39deb7d5cb6cc7c,0xf835ab5f60e02bda439bc5dd7365d3ebb188caa8,0x4968de1d760f2cc22b143ebd2aa76912d38bcd2e]
private def selected : Array ℕ := #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27]
private def restRows : Array ℕ := #[0xb0a0908,0xb0a0908,0xb0a0908,0xb0a0908,0xb0a0908,0xb0a0908,0xb0a0908]
private def recoverRows : Array ℕ := #[0x6959603247b9248159a0bfa57ab93d2860bfe279136ca67d32a5795878682464477a137814192191b9b96c6819201910243da6242119165d81287d6491105dd4,0xb968ea144c4cf5b168a07c1c18cff950ea7c9d3e2c8c8547141c3e7c291ed99b4c182c298778ce3c4ccf8c1e785bd2f0f5f985d9ced2e55fb150479b3cf05ff6,0xac69c32d8ec0e80d6995a5aa93ee187dc3a53b6db1bbef5a2daa6d9ae7d658668e93b1e7c9d559d5c0eebbd6d573ef92e818ef5859ef798e0d7d5a66d5928e46,0x4ec5887807d5b93cc573bd42a720005488bdbe047273b9d1784204e94057f08407a7724082dc33dbd5207357dc4cc2ecb900b9f033c2d59a3c54d184dbec9a21,0xd36c836739b29f306cadaa280cac0c0a83aad21c28d66fae67281cda0622bc0a390c280643adc075b2acd622ad3817199f0c6fbcc01750c5300aae0a7519c51e,0xa4cc5a9405418c2dcc02f53ab1e5ee3d5af5810478350f95943a04223d83102705b1783d528715f141e5358387bd0c288cee0f10150c8c0c2d3d9527f1280ca9,0x5e3f3aa82c6ef7da3f6f8c0f8c4854193a8c41925e89670ea80f920ecebc553b2c8c5ece6fb470a06e4889bcb40bb861f754675570b87d68da190e3ba0616820]
private def basisRows : Array ℕ := #[0x1000000000100000000010000000001d8c5926beac32ed4784d21763dcaa6d70255f83d916af5719ff2e479a37c1d64,0x100000000010000000001000000000197152ded57a031614ad12324dd62876eb4cb48634a270654e178abe493597e5c,0x1000000000100000000010000000001aabba866a491090a3188374dbaa6d375b83c5fbff061d0001ce2e7aecabfe860,0x1000000000100000000010000000001ef415ad584b544d24ab444f5941c43c3a92d77d835d76c2b966dc5e24c38c3f0,0x10000000001000000000100000000010d791defe4422b2e7663a96e557a53e1d37b749705f2a43ce103996147eeaee4,0x100000000010000000001000000000160490fe88ce3662022550e0f8e3473e862b4202501140d603ef96a801f75194a,0x1000000000100000000010000000001cf8aabbb2b248e32d0a3f46964c5a3c19b784eb2465f5ecab6148f8fe1874279]

def D : Data (ZMod 251) 7 24 33 41 2 5 3 where
  z t := byte 0x90f244ee8aca1a06197b47721c6d4fd04bf48cd4cd0ebad99679513da74a4894392a118869f7504c52 t.val
  t s := byte 0x4bddda30951cf0aff340cf415c1f0c83de5449ae77a931906af593a4d0760f580d8e4f563419cc512d s.val
  hub i := Fin.ofNat _ i.val
  left j := Fin.ofNat _ (7+2*j.val)
  right j := Fin.ofNat _ (8+2*j.val)
  G j i := if j.val<14 then (if j.val%7=i.val then 1 else 0) else byte sharedRows[j.val-14]! i.val
  owned i j := Fin.ofNat _ (7*j.val+i.val)
  node i j := if j.val=0 then Fin.ofNat _ i.val else
    Fin.ofNat _ (7+2*(7*((j.val-1)/2)+i.val)+(j.val-1)%2)
  shared j := Fin.ofNat _ (14+j.val)
  bary t := byte 0x936ba7e9f0c2c3a34905ed6ea9c614f142a8c72dcd99a43e650ac2cfe739a9d20a15446c954a54ca42 t.val
  weight i t := byte weights[i.val]! t.val

def M : Moments (K:=ZMod 251) (h:=7) (r:=41) (n:=33) (free:=3) 12 where
  quad i e := byte quadMoments[i.val]! e.val
  pole j i e := byte poleMoments[7*j.val+i.val]! e.val

def L : Recovery 7 8 12 4 (ZMod 251) where
  rest i l := Fin.ofNat _ ((restRows[i.val]! >>> (8*l.val))%256)
  R i k v := byte recoverRows[i.val]! (8*k.val+v.val)
  P i k l := byte basisRows[i.val]! (4*k.val+l.val)

def sel (u : Fin 28) : Channel 7 8 3 :=
  let z := selected[u.val]!
  let a := z%10
  .inr (Fin.ofNat _ (z/10),if a<2 then .inl (Fin.ofNat _ a) else .inr (Fin.ofNat _ (a-2)))

private abbrev baryP (s : Fin 41) : Prop := D.bary s = (∏ t ∈ (Finset.univ : Finset (Fin 41)).erase s,(D.z s-D.z t))⁻¹
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def baryOK : Prefix (testFin baryP) 41 := by
  let p : Prefix (testFin baryP) 0 := Prefix.start _
  iterate 10 let p := p.step (len:=4) (by decide +kernel)
  exact p.step (len:=1) (by decide +kernel)
private abbrev weightP (s : Fin 41) : Prop := ∀ i,D.weight i s = (∏ j : Fin 5,(D.z s-D.z (D.node i j)))*(∏ j : Fin 2,(D.t s+D.w (D.owned i j)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def weightOK : Prefix (testFin weightP) 41 := by
  let p : Prefix (testFin weightP) 0 := Prefix.start _
  iterate 10 let p := p.step (len:=4) (by decide +kernel)
  exact p.step (len:=1) (by decide +kernel)
theorem geometry : Good D where
  distinctZ := by decide +kernel
  power := by decide +kernel
  distinctT := by decide +kernel
  cover := by decide +kernel
  separated := by decide +kernel
  awayL := by decide +kernel
  awayR := by decide +kernel
  regular := by decide +kernel
  individual := by decide +kernel
  node_inj := by decide +kernel
  pole_inj := by decide +kernel
  position := by decide +kernel
  bary := baryOK.all
  weight := fun i s => weightOK.all s i
private abbrev quadP (s : Fin 20) : Prop := ∀ i,M.quad i s = ∑ t,D.bary t*D.weight i t*((D.t t)^2+D.a i*D.t t)*D.z t^s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def quadOK : Prefix (testFin quadP) 20 := by
  let p : Prefix (testFin quadP) 0 := Prefix.start _
  iterate 20 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev poleP (s : Fin 20) : Prop := ∀ j i,M.pole j i s = ∑ t,D.bary t*D.weight i t/(D.t t+D.w (D.shared j))*D.z t^s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def poleOK : Prefix (testFin poleP) 20 := by
  let p : Prefix (testFin poleP) 0 := Prefix.start _
  iterate 20 let p := p.step (len:=1) (by decide +kernel)
  exact p
theorem moments : Correct D M where
  quad := fun i e => quadOK.all e i
  pole := fun j i e => poleOK.all e j i
private abbrev recoverP (s : Fin 12) : Prop := ∀ i j,(if j=s then (1:ZMod 251) else 0) = (∑ v,L.R i s v*M.quad i (degreeIndex v j)) + ∑ l,L.P i s l*(if j=L.rest i l then 1 else 0)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def recoverOK : Prefix (testFin recoverP) 12 := by
  let p : Prefix (testFin recoverP) 0 := Prefix.start _
  iterate 12 let p := p.step (len:=1) (by decide +kernel)
  exact p
open CriticalHigher.Hub251 (fromRows batch batch_sound injective_of_rows)
def matrixRows : Array ℕ := #[
  0xa803b16262d220521d80d3c20e4088096127f99a78f1296781ea94a4,
  0xea96edd4213e8f1a1b81af3bb65b7c4742aa00ab714a938079466398,
  0x3052dc885009ad84685517875a82ed18cae6e0d85f29a5dc34ea3c0b,
  0xeedfcf567c7c4ad93699ba4e12c5867b527aa9eba0636d9c3c7b3400,
  0xefc7849c0550f0176a4d4e3eab7004a537dd3c51f7ba8294f29e8159,
  0x6c2f3c48c75eebcb62a30959e019e076251df59fe61d8356aaa44d0e,
  0x956a3a6b66f685aa9a30e29d0d02e9f9d211d06bf242f89a9ae923b5,
  0x51625a37313df159e912a28bd95688b70422ad4a0fa44804b9860f08,
  0xe6cd882a3695807b8b7249c38f7ebf3ba4211a026e696f267a1af3ef,
  0xa75abbb48a24188fbf1fc240bd4791a749e62137b994bf13d52b25,
  0xc1a88787bea3e02f6e23ef7788cf09faa47ddb6d79b2ade72198ce77,
  0xeab262410005b9cd12cde37aad3e601fdaf9731f0e328ffae14d1a31,
  0xc7bb21df009a3bf29f838ebef10036b639c4968bd6578e550f65d42e,
  0x5ddcda976e930ebc331146dd1dce657d53f7d5ac61b0458bf543ae1,
  0xbc4c8c99932b15e32cd97cab8a934653ab0ceb48492df3dc81a4f249,
  0x3f77c464792e05a9a37f9429f9e6815fefa66b7049a17228adaaedd8,
  0x1edacad944630714d0c4462d5b4bf91b1f5d474ec8f1c46653394b11,
  0xd2264b4e557f0983f1583b5dde68f2eb07c24824c8677ab4bf566f39,
  0x1c7b0c956921602f844037f124953146ec43a7534a109a5c036b1ac,
  0xef921619c18585a9560adaf870a0d1fc06f15cb911774738a83d8b3,
  0xdfac0fdbc949890f22d5b2a44d21f13b8c1658adfae9890b768e0734,
  0x58a1236745456b071b87293c1f7199780b85b9779f6e8c937418c301,
  0x13003a3db29e281d9d14437c0df9e69fe5109d5654ccf34fa328657b,
  0xe3b1ae6449990f979acf60f44ac2b66532a76281aca41ad076205902,
  0xbd2eb227dc803847a8f14f4bdf698558a7b26f13f2e66c343211b5d8,
  0x4ec6bf37c5c146366b5a7985bc1332bd62b5a7349f83d8f0ae582737,
  0xafbc800b8aa41a2c9a9c353dedc9043d6e7a45c95739175accbd1c80,
  0x97a816d5e346aa0c54aa2dc44709a6ca81dfb916286a0066b1c1f463]


def inverseRows : Array ℕ := #[
  0xf4c8bde67b2f8f6eb94e4ec94ca98be20e9c9c93230674b0c0b87aed,
  0xd5f88511eb3b017bea7d2af599d0e174d0daf289c2865aa784f5ef2b,
  0xad9dedbeaa6a0f59654d4c59086844de7a50c6d7e7e232c16d3e72b1,
  0x9dc264e812af316841dc32e4934d4838ae95789ab12d0d35edf832cb,
  0x5fcb3a270fa7696fbc9c94ba4c4d0d4f3feaab19133ea08006eada5c,
  0x7a8c7b8805a2c7151a85c265bf0b4332cfe4603e8b68c06e9fcf3038,
  0x9a97e0a553ad16e188c68f44bec90e5855f789f13be60d008f1abe4,
  0x3ed00c7652573db6dfda68f49ee491e7c31c066536103846d0352292,
  0x2c7c966f898e51928ea240038a3e76c30500e3dfd2a6eaa9e0653f60,
  0xa179af6331dcde2b79a51019bacd6639d208b8b76990703496101c8,
  0x75b8e941ba5736f431f33d8db0b88a83e14e334a4f6dc13f6344f203,
  0xc7bcb3d645e4d17982b1f693d3623db77bf12b76ea84f2329fe846d1,
  0x54da847304dbedbbb86458e848d5f2e0995c8970064509a422b015f5,
  0x65014d84551f35656eb6dcf0319af0697c3061200a746fb2e64d9e2d,
  0x73e96b2a96cb34eaacef548a1f029d2fb87436cf02f09c604f7e9f91,
  0xd52eb436608eb53a33a76e38bb8d2c5a059715e41654bc09cd39749a,
  0x6f6381a1a1b14b731ef5a0229d5c983af1082badc45389be2ec64ed5,
  0x1a91f9fc38d4f133240229b96100f16d730ebdbe2904201a86924b7,
  0x2870a25b25a351960e522d4dd4ce858d2863722d4ae4831016e8e8ea,
  0x4a924ca11e04588af65d5ed92c15d38bd147378dc2515e9588b44401,
  0x5a305e4bca1ba53ee54dd863db466b55d20828c7f6d31f6056a7c69e,
  0x75bf063ce942dfe2257592bd83b8ec0698222351bcab5400128c75f2,
  0x7ca373ecec78909a334f54c3bebe1f2adb2c4d48e67a7bafcfd2c553,
  0xdebd13a0b69c4629856b5fa5d50a13b2c06446673304e3a3ea0ab16e,
  0x897da9b7cdd951b1ebc1cea0ddc6335f3da974c63b02add8613957e4,
  0xd08eecd2c2adf68707f99a9be126698758632808c06137640f2c02a2,
  0xb3311863c11cf58b07084ea352744e3da0d15c5252cbacc45d12bfd9,
  0xd90e5152b12456e4a2659a262ca39e6d22cb58b3bb367be09fb31867]


private def packed (u : ℕ) := matrixRows[u]?.getD 0
private def inversePacked (u : ℕ) := inverseRows[u]?.getD 0
private def A : Matrix (Fin 28) (Fin 28) (ZMod 251) := fromRows 28 packed
private def wide (j : ℕ) := CriticalHigher.Hub251.spread (inversePacked j)
private def rowGood (i : ℕ) := (wide i == CriticalHigher.Hub251.widen 28 (inversePacked i)) &&
  CriticalHigher.Hub251.wideRowOK 28 packed wide i
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private def checked : CriticalHigher.Hub251.Prefix rowGood 28 := by
  let p : CriticalHigher.Hub251.Prefix rowGood 0 := CriticalHigher.Hub251.startPrefix rowGood
  iterate 7 let p := CriticalHigher.Hub251.extendPrefix p 4 (by decide +kernel)
  exact p
private theorem injective : Function.Injective A.mulVec := by
  apply CriticalHigher.Hub251.injective_of_wide (by decide : 28≤256) packed inversePacked wide
  · intro i
    exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp (checked.verified i.val i.isLt)).1
  · intro i
    exact (Bool.and_eq_true_iff.mp (checked.verified i.val i.isLt)).2
private abbrev entriesP (s : Fin 28) : Prop := ∀ i l,A s (finProdFinEquiv (i,l))=smallEntry D M L (sel s) i l
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def entriesOK : Prefix (testFin entriesP) 28 := by
  let p : Prefix (testFin entriesP) 0 := Prefix.start _
  iterate 14 let p := p.step (len:=2) (by decide +kernel)
  exact p

theorem spans :
    ∃ x : Fin 41 → Fin 3 → ℂ, ∃ y : Fin 41 → Fin 24 → ℂ, ∃ z : Fin 41 → Fin 33 → ℂ,
      ∀ T : Fin 3 → Fin 24 → Fin 33 → ℂ, ∃ u : Fin 41 → Fin 3 → ℂ,
        ∃ v : Fin 41 → Fin 24 → ℂ, ∃ w : Fin 41 → Fin 33 → ℂ, ∀ i j k,
          T i j k = ∑ a,(u a i*(y a j*z a k)+x a i*(v a j*z a k)+x a i*(y a j*w a k)) := by
  apply CriticalHigher.PrimeTangent.exists_lift (p:=251)
  obtain ⟨Y,Z,f⟩ := tangent_of_small_minor D M L (by decide) (by decide) (by decide) (by decide)
    (by decide : 0<12) (by decide) geometry moments (fun i k j => recoverOK.all k i j)
    sel A (fun u i l => entriesOK.all u i l) injective
  exact ⟨fun i => ![1,D.t i,(D.t i)^3],Y,Z,f⟩

theorem generic_rank : Arxiv.«0805.3777».IsGenericRank [3,24,33] 41 :=
  CriticalLastSlice.TwoPlanes.generic_rank_of_witness (by decide) (by decide) (by decide) (by decide) spans

end CriticalHigher.FrontierSeed.B24

namespace CriticalHigher.ComponentSeed.B24
open CriticalHigher.PrivateBlocks
open CriticalHigher.FourHub (Prefix testFin)
local instance : Fact (Nat.Prime 251) := ⟨by norm_num⟩
private def byte (a i : ℕ) : ZMod 251 := ((a >>> (8*i)) % 256 : ℕ)
private def sharedRows : Array ℕ := #[0x8d4797cb28,0xebda73db46,0xacc6048adf,0x29ae6769ed]
private def weights : Array ℕ := #[0x2f6080010c1786bee783ce4682471a6900007a5c2446793e9951000031329408a4b5408c00005c93b0d600,0x757c785e5666bd0d0eb7c4416e92000003828b534843b0930000a516593ad2707615000035aa0e4eb100d7,0xa2483de5292474f590dd23db0000b3547d24b7bf031f000075d518a812817e8c000011cfeab0b0ae00c71f,0xc2a2b4a1363882f8ba390000d997e1ad35878a850000f90519b9614b0359000020484d7630e31c005d4de6,0x83f9f7360112c848000070a8a31cd03f8b820000aaa768c0c1f152f40000ca7ad1aaad897fc200bd2c9805]
private def quadMoments : Array ℕ := #[0x4609e525c5d8523e874ab06a010000000000,0x42126579b1810a748051cd5b010000000000,0xa394b1e1ddf23ec20ebfca30010000000000,0xbdf1884d2149648197c50420010000000000,0xbcf5cd4d9eae2f3920325fce010000000000]
private def poleMoments : Array ℕ := #[0xa613f7203edc24f06c8c5354202e60ec12f2,0x840a19879c02c9e84e7837c55f0b991715cb,0x5b6f7a067c1b350fdc59a6184b61546b2469,0xcb19444cafd0294eaccf2c9d94997db8431c,0x86849f2b7a0393c9e15edcaa2f5fc8df54b3,0x694e5a34d2548c6878991d706737a0cccee9,0xf07390c9bc2345edc011a7d65c4105be8b76,0x8fc9801fcd7c6b11577d6af93bbe7453e151,0x2b41de1117048d032dbec659bc043c560d23,0x9b439851f7237bad776ca2d6a4934b90d876,0x7b34ad0617506f97965521d5c0ad75f25b83,0x2a5e396ca4405df4b4189446bc6e2859059b,0xa3b3c77230d05ceb646db266846c4e50b3be,0x759333abdc091ac85f261502c99c3178ac70,0xaa2bf1f6744ae995c1dedd80f73d0f854d8c,0xcaf34781c636763279878f278d40b9dfad46,0x305daddc7166ca6d6f83ebf176097af864bc,0x35ba863bc0266cda29c4378b4e12b71eddc6,0x117b682e3e2b522f6759f02d7314ac86069e,0xc045865b8c35370829f7816cddc9b719874e]

def D : Data (ZMod 251) 5 24 37 43 3 7 4 where
  z s := byte 0xbb00e40a2ff935e54d3a268cbfe05a05f0e39d112814c0afee874a9b973ecf6b738a8223255592272a96c9 s.val
  t s := byte 0xd3006910f94098c029c57a6a16e8b43f036e7b9a1914cf1b4f3a340f054bf0d65971096c8ea4a9705c9b04 s.val
  hub i := Fin.ofNat _ i.val
  left j := Fin.ofNat _ (5+2*j.val)
  right j := Fin.ofNat _ (6+2*j.val)
  G j i := if j.val<15 then (if j.val%5=i.val then 1 else 0) else byte sharedRows[j.val-15]! i.val
  owned i j := Fin.ofNat _ (5*j.val+i.val)
  node i j := if j.val=0 then Fin.ofNat _ i.val else
    Fin.ofNat _ (5+2*(5*((j.val-1)/2)+i.val)+(j.val-1)%2)
  shared j := Fin.ofNat _ (15+j.val)
  bary s := byte 0x3851458b32ac6686502d63cc0a61d6934502db7c4626d766a61b02b2f5e00fd30e8c01db3497ad035b5ce3 s.val
  weight i s := byte weights[i.val]! s.val

def M : Moments (h:=5) (K:=ZMod 251) (r:=43) (n:=37) (free:=4) 12 where
  quad i e := byte quadMoments[i.val]! e.val
  pole j i e := byte poleMoments[5*j.val+i.val]! e.val

private abbrev baryP (s : Fin 43) : Prop := D.bary s = (∏ t ∈ (Finset.univ : Finset (Fin 43)).erase s,(D.z s-D.z t))⁻¹
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def baryOK : Prefix (testFin baryP) 43 := by
  let p : Prefix (testFin baryP) 0 := Prefix.start _
  iterate 10 let p := p.step (len:=4) (by decide +kernel)
  exact p.step (len:=3) (by decide +kernel)
private abbrev weightP (s : Fin 43) : Prop := ∀ i,D.weight i s = (∏ j : Fin 7,(D.z s-D.z (D.node i j)))*(∏ j : Fin 3,(D.t s+D.w (D.owned i j)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def weightOK : Prefix (testFin weightP) 43 := by
  let p : Prefix (testFin weightP) 0 := Prefix.start _
  iterate 10 let p := p.step (len:=4) (by decide +kernel)
  exact p.step (len:=3) (by decide +kernel)
theorem good : Good D where
  distinctZ := by decide +kernel
  power := by decide +kernel
  distinctT := by decide +kernel
  cover := by decide +kernel
  separated := by decide +kernel
  awayL := by decide +kernel
  awayR := by decide +kernel
  regular := by decide +kernel
  individual := by decide +kernel
  node_inj := by decide +kernel
  pole_inj := by decide +kernel
  position := by decide +kernel
  bary := baryOK.all
  weight := fun i s => weightOK.all s i

private abbrev quadP (s : Fin 18) : Prop := ∀ i,M.quad i s = ∑ t,D.bary t * D.weight i t * ((D.t t)^2+D.a i*D.t t) * D.z t ^ s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def quadOK : Prefix (testFin quadP) 18 := by
  let p : Prefix (testFin quadP) 0 := Prefix.start _
  iterate 18 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev poleP (s : Fin 18) : Prop := ∀ j i,M.pole j i s = ∑ t,D.bary t * D.weight i t / (D.t t+D.w (D.shared j)) * D.z t ^ s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def poleOK : Prefix (testFin poleP) 18 := by
  let p : Prefix (testFin poleP) 0 := Prefix.start _
  iterate 18 let p := p.step (len:=1) (by decide +kernel)
  exact p
theorem correct : Correct D M where
  quad := fun i e => quadOK.all e i
  pole := fun j i e => poleOK.all e j i
end CriticalHigher.ComponentSeed.B24

namespace CriticalHigher.Hub251.Tiny24

def rowData : Array ℕ := #[
  0x6328e4ee281b7ad067f71ed90552ebfa529ff325ba827204d32727e1035e,
  0xd5bc321b3af23ba2a650534fb56221b7c7ef54f80c8de0d4ca67b3e02c33,
  0x40cb788c7abfc676c38b3db1a7dd0f67f638497c892104b1a39caadf6a46,
  0x2400f92895c4697b13f2c3d22a3d2c5d0431d3004c582cbf2a5228b2349b,
  0xbf7c0e96e97f3517021e0b195d3ea4ee80b15c5730bf946545ed931f373b,
  0x2a9f9c3489c259bf32834abf1abec9b6346ac11cabf825cfd74fd74dbe3a,
  0x6e70319b1812052d744dc4391b102d46be136478706d7c8bd133c69b0383,
  0xb999a1ad2d97166092d5bbf03ef1624b86b06bb2ef35ebab99848e1479b2,
  0xa5699ced7d884df61d51cea996b7c81669145c4d8db56a7fae1b2fd7c955,
  0x70f460e5e1ab86afbe126389bb2c356c83d595da65d71f7e3d43f593f6da,
  0x15ea1389901e6138ba3c4f67942a604c729d398a17b4e28469230c3dc8d0,
  0x7b00f23ef7f3d21ace5b5f6143cdad3111b398999bbeca96cae96a114c98,
  0x86b258e5a149cfbab7574d6c1e800d7a04d4e52f39879f9d82f61075be3b,
  0x9c8cf05fd838831866e9ed266566408a264af53a6de2975818887a1ec925,
  0x279ad65240ba2e40e53aa6dcad3f25237631186019d86ca6c0d295166d81,
  0xd06b1c1cc6adf4b847bd68a730ec25f03831b05b683f81c44dc8ccb930e6,
  0xf5e4b71a74beae50c9e05d79ab85a38fee86f0c20819d27118e8f244fa13,
  0xcfa01d04409f7d109df8296bd2c3f891590f3a1b85e61ffad1b8a3c62d5c,
  0xf7df8c164b2e84f3325ff46e9a02c219e16e01696b83b425209538349bf2,
  0x47d33da16e67313e3430d13e17b96fdfd6abb6f4a02bce86f04f059e1805,
  0xc84114bf848551024bf55f8e10dd531fc8f06847b9e2abf051a9668a391e,
  0x84abbfe73188672f720ea3ef31d2ab5bb68d2c8aa7ae9f6d5a544daeea07,
  0x8ccd4155f9e7c5ad166216db8b2d14ab500e13adbf8748d64023908657d9,
  0x42896bc0a6b8b2b75edb9b0c094bb0379d6dc0dabcd1b1782df6beb90070,
  0x8c682d4326ebc38d5e6b7a038a0bb07abd72a66cd24a2d85b584cb1f39aa,
  0x593c74651a516d90c6bbaa9ccab5d22859e6152c7f80c6a1614f5af58472,
  0xa29774093b5b11d5875dd8e6457f602e9993b27068425bba4488c34cb1b1,
  0xd4f191b3db5ec2993259107881ee6de462dee6c50d825339ecacc8bc3a3c,
  0xde7ed8c314f17cbf3dc959709e2fc6e9235bc33a71a6ea24c14714aa7b42,
  0xc9020da49d94cc09c986b6496e09df1dc94e4a8f5d5b0575a903332860e3]

def inverseData : Array ℕ := #[
  0x19a4483467bbff50e8ff221f704ed502559819abd1d79862b9868f69a30,
  0xecf7e46c9cb52d841830dada2d3e27c161a61e7f4ef616e194f6bb490a7f,
  0x9ce1cb56b92474a1ca085ee0e90a1139f7cfdb7dad1e6f839712b161b3e6,
  0xcf1e6d67699dea440f097e9d34d85618b0627728dd97a3c6f6ba9d9f7beb,
  0x7c405ed046199c6fe4762207e13fd97a3fc03ae41cf8110a606c922f4a30,
  0xcbd2d98f514da34939f17023a1c991d746ab024f50cab7b1e07b95dae805,
  0x96c03c57c08853eedaf71eda499641518fdda9d4451fabb4c0bf70195e8e,
  0x365b17849bb6a9e7562d8c0f755636d9679f0b1d41b89fe8023c4e800449,
  0xba2e14efdd1af26c9e08bce2927525240031b2d275fa3e324a3d727c78cd,
  0xa0216f6d5a40d017d82f4b342a91f6088417a731b10f8ccfa05fc84036cd,
  0x53068d88adaefa552fa776237e9bf5ade894aae4e4cc95d72d8eee78b3d6,
  0x656c2b6489a42931c798558a53e1280e25573a8fef0e6b4b53d235c3bb3e,
  0xed2b8c44d5153f7cf05ed9ae87b030b8f578312efa3a896ce5c50f2ff0cf,
  0xf5af0b2144752379c59104f703ef19c29b9424ca21d28fb9f76012ee960b,
  0x3a3930049dae20f45665a1b898bcebd3ec7f70cb5522ef77f709c60a6fd2,
  0x7daa3251497583df25b2a55346c053e5165a12aa98d0edb74a35ab9e6c2f,
  0x24f36d2f4c1872a7b655e28c96d0efad07c98705d429f2455a2d50f83335,
  0xe418ce226524420ec1a345094dc7702309acb12929420fa5426144e6863f,
  0xbcf32a04ddbbbc7739522ec64b30bae8d4d95164236144bff66d243e97ac,
  0xe72994b6ad2f22f6888a3e0e69b755a0bc82152409a816c4568a945ab1ba,
  0xdddebfb4443bd15df9b5d31362189f774ef6da0e3d59b88580eb90c5e35e,
  0xdbe042911aa427d1b948f874e558909580f359a4ee076b2dd7b138c067b5,
  0x1cab4a7a4ee3b692a9ab955d5d85144673293c113c61b147bbe022f955d3,
  0x3b313ec20e4d8eaad6c2b9ad4f7c2b737e419c3ad9e2519e47e8ecc0bbb1,
  0x594a76e920db06d9625a2532c9039b5f99a708887e58acdbc24297a8ad0a,
  0x1ae9610e221c4b75b54c13c3cf51937c897240c2e36cca93f078939868f3,
  0xcc0ec094dc5a8896abb350a58a37512f41d12e4772d8222075c7812cc4b4,
  0x364c8ec3eed5d1ab97d6c6824121808b485950cdf8937c7386d7529947a0,
  0xdbf74fbd81dc2151cd37ed068bf3e5e68f5d479ad53528d4bd6a4d7dabab,
  0x7d2a091dbabf42e22399e8f53f9b279fd0b0732c8acc045991351bc21172]

def row (i : ℕ) := rowData[i]?.getD 0
def inverseRow (i : ℕ) := inverseData[i]?.getD 0
def A : Matrix (Fin 30) (Fin 30) (ZMod 251) := fromRows 30 row

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1500000 in
private theorem product_checked : batch 30 row inverseRow 0 30 = true := by decide +kernel

theorem injective : Function.Injective A.mulVec := by
  apply injective_of_rows (by decide : 30 ≤ 256) row inverseRow
  intro i
  exact batch_sound row inverseRow 0 30 product_checked i.val (Nat.zero_le _) i.isLt

end CriticalHigher.Hub251.Tiny24

namespace CriticalHigher.ComponentSeed.B24
open CriticalHigher.PrivateBlocks
open CriticalHigher.FourHub (Prefix testFin)
local instance : Fact (Nat.Prime 251) := ⟨by norm_num⟩
private def byteNat (v i : ℕ) := (v >>> (8*i))%256
private def restRows : Array ℕ := #[0xb0a09080706,0xb0a09080706,0xb0a09080706,0xb0a09080706,0xb0a09080706]
private def recoverRows : Array ℕ := #[0x1000000000191000000019110000001911045000191104559019110455914,0x10000000001a000000001a02c000001a02c0c0001a02c0c8f01a02c0c8f19,0x10000000001cb00000001cb5e000001cb5ee00001cb5ee0f701cb5ee0f7da,0x10000000001db00000001db10000001db10ac0001db10ac5301db10ac53d7,0x100000000012d000000012dad0000012dadc500012dadc5bc012dadc5bcb4]
private def basisRows : Array ℕ := #[0x10000000000000100000000000001000000000000010000000000000100000000000001a9bd74b14b91c1d7c0b3081034cd3f0c7c45b929b1e4a759b0bd4a757e1409bffa646f0e,0x10000000000000100000000000001000000000000010000000000000100000000000001f1877baa2ea01c04edd7002c4ec391bbe70c96c0a5b1ed8f9080d380e5196005bfc217d5,0x10000000000000100000000000001000000000000010000000000000100000000000001bd39ed3c31cbe0d6e376da5e2d3c995ecee0660cbb271af7917d44c65edac315556057ac,0x10000000000000100000000000001000000000000010000000000000100000000000001977a6436f7db730cb981b610c93b6a2d41acb565bf6b6e531410769b1ad70f92b5b630ae,0x10000000000000100000000000001000000000000010000000000000100000000000001ccc2dbc99c2ddd9509e4c1adc49587906cc58a0b784a03bcb2d7130723b428d1e437e267]
private def smallSelected : Array ℕ := #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29]

def L : Recovery 5 6 12 6 (ZMod 251) where
  rest i l := Fin.ofNat _ (byteNat restRows[i.val]! l.val)
  R i k v := byteNat recoverRows[i.val]! (6*k.val+v.val)
  P i k l := byteNat basisRows[i.val]! (6*k.val+l.val)

def smallSel (u : Fin 30) : Channel 5 6 4 :=
  let z := smallSelected[u.val]!
  let a := z%8
  .inr (Fin.ofNat _ (z/8),if a<2 then .inl (Fin.ofNat _ a) else .inr (Fin.ofNat _ (a-2)))

private abbrev recoverP (s : Fin 12) : Prop := ∀ i j,(if j=s then (1:ZMod 251) else 0) = (∑ v,L.R i s v*M.quad i (degreeIndex v j)) + ∑ l,L.P i s l*(if j=L.rest i l then 1 else 0)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def recoverOK : Prefix (testFin recoverP) 12 := by
  let p : Prefix (testFin recoverP) 0 := Prefix.start _
  iterate 12 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev smallReadP (s : Fin 30) : Prop := ∀ i l,Hub251.Tiny24.A s (finProdFinEquiv (i,l))=smallEntry D M L (smallSel s) i l
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def smallReadOK : Prefix (testFin smallReadP) 30 := by
  let p : Prefix (testFin smallReadP) 0 := Prefix.start _
  iterate 15 let p := p.step (len:=2) (by decide +kernel)
  exact p
theorem tinySpans :
    ∃ x : Fin 43 → Fin 3 → ℂ, ∃ y : Fin 43 → Fin 24 → ℂ, ∃ z : Fin 43 → Fin 37 → ℂ,
      ∀ T : Fin 3 → Fin 24 → Fin 37 → ℂ, ∃ u : Fin 43 → Fin 3 → ℂ,
        ∃ v : Fin 43 → Fin 24 → ℂ, ∃ w : Fin 43 → Fin 37 → ℂ, ∀ i j k,
          T i j k = ∑ a,(u a i*(y a j*z a k)+x a i*(v a j*z a k)+x a i*(y a j*w a k)) := by
  apply PrimeTangent.exists_lift (p:=251)
  obtain ⟨Y,Z,f⟩ := tangent_of_small_minor D M L (by decide) (by decide) (by decide) (by decide)
    (by decide : 0<12) (by decide) good correct (fun i k j => recoverOK.all k i j)
    smallSel Hub251.Tiny24.A (fun u i l => smallReadOK.all u i l) Hub251.Tiny24.injective
  exact ⟨fun s => ![1,D.t s,(D.t s)^3],Y,Z,f⟩
end CriticalHigher.ComponentSeed.B24

namespace CriticalHigher.SixEndpoint.B16
open CriticalHigher.PrivateBlocks
open CriticalHigher.FourHub (Prefix testFin)
local instance : Fact (Nat.Prime 251) := ⟨by norm_num⟩
private def byte (w i : ℕ) : ZMod 251 := ((w >>> (8*i)) % 256 : ℕ)
private def sharedRows : Array ℕ := #[0xf34f485c306,0x181ee4cd9b93,0x49aae89ecef9,0xa6af49a12d2a]
private def weights : Array ℕ := #[0xf332c5fa183d567120597b3842ad37b9b4ae00003d801fb20600,0x831bba6c579f7b441ae6da243405313600005ce3e6bc854f0049,0xc5f300f223cdbcb37e5e404342a0000aad0e8cd2dd1a000ed5c,0x3e899f0286d655bb52b23090000931980702b24399e0081e08d,0x5e77b38907c5434a438100009717e38ca19b892af0000ed24dd5,0xac0546f2bda7dae90000a9e88d06035c297ee3d0007a5be9b24d]
private def quadMoments : Array ℕ := #[0x8310d19bd8b6d64fb5d608300100000000,0x69537351c86463aa6e9f71810100000000,0x14ae87d5c80f3830e75dd9430100000000,0x6b09a0762a1e3c7eb7802c990100000000,0x9da20b6cae02756f9f2c61890100000000,0xf605b9a49f1b6641cd63882d0100000000]
private def poleMoments : Array ℕ := #[0x2b33f1593c729643297005878a986c5d69,0x131d5e033e4e946bd93f2f8460ef2744ea,0x3c191f510d9d051795c3162269e8754fd3,0x39a79c505eaec1f40daed98c2568168c27,0x2e30661b8481d50486410bc7ce54356ee7,0x469d490c0fded7221b014090f8d4411559,0x6da018cb963cbd547119109de713a6aa9f,0x93cedee47e2860c468c39a15c9809b47f4,0x45635b0408b0a879a7e4cdf32678e8c38b,0x9e04cbae04d5dde41981e45d2fc3aa4ac3,0x1621918a0ebafa7ce9552d3cc228e54c37,0xb2781e988dbc6a3fcc8205ae124d528322,0x172ce141b7c4f9122326f6671635755437,0x5ce7ccb20a96f3dc0f328d6b585a56cbce,0xc60ccb45c56151771af55cbc71c5d842f3,0xada00fce788069f856f4ba6264213a4dd5,0x46c92a36cfbbea30289fe9cabbe13e08c6,0xb9163cbf510ee0095d9e71612e98e8130c,0xab239b714b95a0b5c01965ccb68c76c931,0x3b491840523a8569cb7b5787ec2960054d,0x98a1d9612677c6b44439af0d6a8e738998,0x2ebfe8ad6af19f78269c2714b80bafbead,0xb34938352dce593d0f0573e2cd056164d,0x98547a9043c0c65307d675766a55ed4a11]
private def selected : Array ℕ := #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29]
private def restRows : Array ℕ := #[0xa09080706,0xa09080706,0xa09080706,0xa09080706,0xa09080706,0xa09080706]
private def recoverRows : Array ℕ := #[0x94afcd09cdefaf86c846c84bcdc83752380a0946526922e9cdc838225cd1ef4b0ae9d1c2,0x69091a125238095ea0bcd7381aa01045940212bc457e324852d79432881438380248148f,0x3db4365ce833b4ef936f1262369313d19dbc5c6fd1298f31e8129d8fe5233362bc3123ae,0xd529a8c542bb290295e6c104a895b643c6c4c5e64360cd7442c1c6cdc68bbb04c4748b31,0x4555ec3de06d55982fb1b980ec2f24cd74033db1cd04e8c6e0b974e836476d8003c647e6,0xd9181e07c7e218af9cbb517a1e9cc3aba5a907bbab420a73c751a50a521ce27aa9731cd4]
private def basisRows : Array ℕ := #[0x100000000000100000000000100000000000100000000000118bdce86128c88de8384b91da7f053d2407e5cd6a5b8089395abdb48f336,0x1000000000001000000000001000000000001000000000001a7d066e0f2c36a233d2c327a685ccae969c5aba0b103a67c386e3fe129a2,0x10000000000010000000000010000000000010000000000018465bd932588d59e624182973bd149041065d0adce817bf3606f95a080a1,0x1000000000001000000000001000000000001000000000001aea15be855af5ac91203b1aa069ebf855e74b5f452724466c4d96cbfcd40,0x10000000000010000000000010000000000010000000000014faff27e6c680a460da7af70d091ebbc50854c9e0dbc70e7ccb3abef2960,0x1000000000001000000000001000000000001000000000001b139cf4777d88312dc1f423859448fac623c56ccf93abc8f432402bac180]

def D : Data (ZMod 251) 6 16 20 26 1 3 4 where
  z t := byte 0x69ba43dac297ea494b715dcfd215bf28e55fad515988bd187814 t.val
  t s := byte 0xa9d0d1b311059a557c7142f017ae1619c0af8ccd44594b6e9914 s.val
  hub i := Fin.ofNat _ i.val
  left j := Fin.ofNat _ (6+2*j.val)
  right j := Fin.ofNat _ (7+2*j.val)
  G j i := if j.val<6 then (if j.val%6=i.val then 1 else 0) else byte sharedRows[j.val-6]! i.val
  owned i j := Fin.ofNat _ (6*j.val+i.val)
  node i j := if j.val=0 then Fin.ofNat _ i.val else
    Fin.ofNat _ (6+2*(6*((j.val-1)/2)+i.val)+(j.val-1)%2)
  shared j := Fin.ofNat _ (6+j.val)
  bary t := byte 0x7ad7df430c10817e6038ae832ee6e1cde031f2bc8dc52c35e14e t.val
  weight i t := byte weights[i.val]! t.val

def M : Moments (K:=ZMod 251) (h:=6) (r:=26) (n:=20) (free:=4) 11 where
  quad i e := byte quadMoments[i.val]! e.val
  pole j i e := byte poleMoments[6*j.val+i.val]! e.val

def L : Recovery 6 6 11 5 (ZMod 251) where
  rest i l := Fin.ofNat _ ((restRows[i.val]! >>> (8*l.val))%256)
  R i k v := byte recoverRows[i.val]! (6*k.val+v.val)
  P i k l := byte basisRows[i.val]! (5*k.val+l.val)

def sel (u : Fin 30) : Channel 6 6 4 :=
  let z := selected[u.val]!
  let a := z%8
  .inr (Fin.ofNat _ (z/8),if a<2 then .inl (Fin.ofNat _ a) else .inr (Fin.ofNat _ (a-2)))

private abbrev baryP (s : Fin 26) : Prop := D.bary s = (∏ t ∈ (Finset.univ : Finset (Fin 26)).erase s,(D.z s-D.z t))⁻¹
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def baryOK : Prefix (testFin baryP) 26 := by
  let p : Prefix (testFin baryP) 0 := Prefix.start _
  iterate 6 let p := p.step (len:=4) (by decide +kernel)
  exact p.step (len:=2) (by decide +kernel)
private abbrev weightP (s : Fin 26) : Prop := ∀ i,D.weight i s = (∏ j : Fin 3,(D.z s-D.z (D.node i j)))*(∏ j : Fin 1,(D.t s+D.w (D.owned i j)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def weightOK : Prefix (testFin weightP) 26 := by
  let p : Prefix (testFin weightP) 0 := Prefix.start _
  iterate 6 let p := p.step (len:=4) (by decide +kernel)
  exact p.step (len:=2) (by decide +kernel)
theorem geometry : Good D where
  distinctZ := by decide +kernel
  power := by decide +kernel
  distinctT := by decide +kernel
  cover := by decide +kernel
  separated := by decide +kernel
  awayL := by decide +kernel
  awayR := by decide +kernel
  regular := by decide +kernel
  individual := by decide +kernel
  node_inj := by decide +kernel
  pole_inj := by decide +kernel
  position := by decide +kernel
  bary := baryOK.all
  weight := fun i s => weightOK.all s i
private abbrev quadP (s : Fin 17) : Prop := ∀ i,M.quad i s = ∑ t,D.bary t*D.weight i t*((D.t t)^2+D.a i*D.t t)*D.z t^s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def quadOK : Prefix (testFin quadP) 17 := by
  let p : Prefix (testFin quadP) 0 := Prefix.start _
  iterate 17 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev poleP (s : Fin 17) : Prop := ∀ j i,M.pole j i s = ∑ t,D.bary t*D.weight i t/(D.t t+D.w (D.shared j))*D.z t^s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def poleOK : Prefix (testFin poleP) 17 := by
  let p : Prefix (testFin poleP) 0 := Prefix.start _
  iterate 17 let p := p.step (len:=1) (by decide +kernel)
  exact p
theorem moments : Correct D M where
  quad := fun i e => quadOK.all e i
  pole := fun j i e => poleOK.all e j i
private abbrev recoverP (s : Fin 11) : Prop := ∀ i j,(if j=s then (1:ZMod 251) else 0) = (∑ v,L.R i s v*M.quad i (degreeIndex v j)) + ∑ l,L.P i s l*(if j=L.rest i l then 1 else 0)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def recoverOK : Prefix (testFin recoverP) 11 := by
  let p : Prefix (testFin recoverP) 0 := Prefix.start _
  iterate 11 let p := p.step (len:=1) (by decide +kernel)
  exact p
open CriticalHigher.Hub251 (fromRows batch batch_sound injective_of_rows)
def matrixRows : Array ℕ := #[
  0x11d84eac7366a92a87031dd7a3498eb5a0d4862ba112f0e4b2e4d84f05c0,
  0x720b3d5aabd1787204ee15250f7788b147358f39d9dd44a267e86f3e79a9,
  0x91a3962a59bf953e0f7984681e396c3a34e1473a9692453f9d397baa817a,
  0xbb8a8b72c27c64e560e6e53598591c6c50e676a89056c19859ce271273de,
  0x3da189de5de5ee13b63aaa8f152ebda1799a9311d379b243292ba1297787,
  0x432ada410782b4bbb41208926a71615a4cb990ad82e617f179e17b8b13e0,
  0xa5d3d37c12e93f800ba54b378d0c56c486578033c46041a5935e9f6e438a,
  0x632acfd0eb45803cab0de048dadce5b315cf6f17c82bb0189a96bfa20109,
  0x1da4533d98e96dd75eca2a56bc75b1a77463cba9f0d560f185c7b869c757,
  0xcaa3720b6e7a30eaf6b77f000d87de49ce16645253236bb2abac02740238,
  0x3981afe961f6989768562faf5616561fb9ca64e25257b6f56d54aa30a5ea,
  0x7b9a3f9ac94f3bb147a23a1cf4950a1fd915460b57a4a10011d27c30548a,
  0x8a345233ac473b7b75f6e1108f9f8556ec1723eae6a615d3c746105d9f8a,
  0xd2794124b0bf97d80c41cf6466ae67a66e6de02dd97c889776c7194a0c61,
  0xb1887aaeb935f11dc867e0286ddc928269edef07a415e2f46ecec2e4e42b,
  0x2394b2995e4d90fe1a1b4f582cd576544f7c9853029dd7425b6f034b0db,
  0x30a6697b3eacbca02fc689230824d976b8629099412dcb3d763d1076d319,
  0x8c39219af6be83c29432cd15afb49adb6f983b66db8156cd272d8694f995,
  0x15c476d60772b6457878b86cad06ec7446898bd0b7b5ae75c37cd7d2bc2c,
  0x4c226fb8d495960b488651e2dc9a993a4e714f0bf1e007f68b19afb7ea1a,
  0x847970732178afa93cb2c7d337a9c4b20babe94fa14e9ae70a1bb9d2c49e,
  0xc07c6714663453dff4bedce289c1a11aed75a3bde78180573a468833a29b,
  0xd010f1c33c7127230a25636fbda4225c5217fa9816a1880994aacc586e42,
  0xab4d5e65c72d0972dfbe887cd676e008b5e1d3c03d2bbe21ed01d36b8375,
  0x1b6f42745c3861a4370554c23c78a02062f2d7a2926972865248f3846c4c,
  0x9f80b32d163a027d16f4336c82bcf84872193e73a5ec659c4fb8fa047bba,
  0xe26a50d95d19e0ebea894e4992c0f6631b0cdf074a5beb099c81de54353f,
  0xc57a473e7f4dd37633edc92ad606f7ace1b2804c07820621844ca0f43267,
  0x891b7a2e81d85fb6122108411b2d61c84dadfa3eb8491ad4d02d9b4fc875,
  0x782461b3f0657ce4504dcba012269cbf27377e6d3b7c17f8f67946a1c32f]


def inverseRows : Array ℕ := #[
  0xb54fad1af4ca0f5649a4d4f6994f4a84e295c3957aadf10b7466d0c112,
  0xc4d7f340c2b7452555a85f1a2a7be84163ec50f061493b35a9399ea3160a,
  0xa28e8da9a3e011ac9bb19fe2bf34dc20ab5d4eb6ac1a929e7335404ccbf0,
  0x2bdd745e714ab31fe9f6f362bb3e72bbaf0ed9ba399bb5a11c06be0e1279,
  0x8fef612fb46626be2130105c0395b1236fbf1a101b6986994eac37767af2,
  0x69cc3431e3340d600ac92cc102962203cbb12289157a66aa7f7723db620d,
  0x10a919861bb2e252be3a4f15e6a7853c680d5e50e8770a9808bd985f3cb7,
  0xd13da9cdbab9d33c1b0aeddc15cf9e06cc92aa9814666b6cc40968551f07,
  0x8fb87985b9b3dc11b45310a5c3319eab8d7c4c7654de688d517c69caa867,
  0x319d10ec6e85be30ae1aa98b476f2b9c44d86f3395194e3207b48ac7797d,
  0xeda21db5d04ec782b8118d507c450033535981f6da2a7a40cee23bd529c3,
  0xd9a648e58704b75882c36f8ae7d83ec957e5bd1723ba597733aeeb4deb11,
  0x15d37c7eacf2268e755bc17941f4c5f2e932af4f5e4de9f68f6fb80766f4,
  0xd7c4e951042437ee6d430df8f98c87bece977fd6d3243dc1555240ad844a,
  0xbddf4c1622e6481a565d362aab48f5e64aaa406d3924d27cbfcaee7f82c1,
  0xa47183fa764d074b695c432d78d731669e134e3ee22fca7c769b8e180ab3,
  0xb54fb677bd03802b6f9a5c636bf17ba6270214c065611e34178f5a0b1ca2,
  0x7572573ec06106f7b9e9ea2e2a94c0b4a81fa1c8485441dde632cc315912,
  0xa471abbc5b06d0942b8d7361143b650e8201857102d98041bbf688f91c77,
  0xcf3b028c0fc85812aedbc181153657870cc41b44b24cf1cf005bd7d6d468,
  0x52aa3fa5af0109a13bddc7dbf873e6da840eefc41d5b3213786ef23d9329,
  0x8480df60e57ec36fac51a487661bdfdf86f332f46d82b5e2641cf3eae89b,
  0x6c3b448349bb9ee6c87f8722acc6baf30434d276cee2b2a56b7e3575ad77,
  0x14bc00e350978fadd18661aa752d0356ec02140c67845841725a70ef9e59,
  0xe083891082e970d9c7bf1a1c16623f12e09c641961d14b95b0258037a5b4,
  0x6242e5394d13e8a1b07ec03fab87569f4b9064aa5db7bbf3803b9f8e167d,
  0x128050b34b4d98b149ea8ff7901882d4194d9741c0a67378ae072aaa580a,
  0x3b5dc149349f44d369f3f34e1d78b6a1210756eb04578905a210defa3c6f,
  0xd9c39079f6e8dc33a7b66af829804e6457519476bba0556ba105a1ee2b8c,
  0x25da79ed6abf83a7933b4aa8d365c51f0f1a3bf62064846b36c83c4a831d]


private def packed (u : ℕ) := matrixRows[u]?.getD 0
private def inversePacked (u : ℕ) := inverseRows[u]?.getD 0
private def A : Matrix (Fin 30) (Fin 30) (ZMod 251) := fromRows 30 packed
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem batch_verified : batch 30 packed inversePacked 0 30=true := by decide +kernel
private theorem injective : Function.Injective A.mulVec := by
  apply injective_of_rows (by decide : 30≤256) packed inversePacked
  intro i
  exact batch_sound packed inversePacked 0 30 batch_verified i.val (Nat.zero_le _) i.isLt
private abbrev entriesP (s : Fin 30) : Prop := ∀ i l,A s (finProdFinEquiv (i,l))=smallEntry D M L (sel s) i l
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def entriesOK : Prefix (testFin entriesP) 30 := by
  let p : Prefix (testFin entriesP) 0 := Prefix.start _
  iterate 15 let p := p.step (len:=2) (by decide +kernel)
  exact p

theorem spans :
    ∃ x : Fin 26 → Fin 3 → ℂ, ∃ y : Fin 26 → Fin 16 → ℂ, ∃ z : Fin 26 → Fin 20 → ℂ,
      ∀ T : Fin 3 → Fin 16 → Fin 20 → ℂ, ∃ u : Fin 26 → Fin 3 → ℂ,
        ∃ v : Fin 26 → Fin 16 → ℂ, ∃ w : Fin 26 → Fin 20 → ℂ, ∀ i j k,
          T i j k = ∑ a,(u a i*(y a j*z a k)+x a i*(v a j*z a k)+x a i*(y a j*w a k)) := by
  apply CriticalHigher.PrimeTangent.exists_lift (p:=251)
  obtain ⟨Y,Z,f⟩ := tangent_of_small_minor D M L (by decide) (by decide) (by decide) (by decide)
    (by decide : 0<11) (by decide) geometry moments (fun i k j => recoverOK.all k i j)
    sel A (fun u i l => entriesOK.all u i l) injective
  exact ⟨fun i => ![1,D.t i,(D.t i)^3],Y,Z,f⟩

theorem generic_rank : Arxiv.«0805.3777».IsGenericRank [3,16,20] 26 :=
  CriticalLastSlice.TwoPlanes.generic_rank_of_witness (by decide) (by decide) (by decide) (by decide) spans

end CriticalHigher.SixEndpoint.B16

namespace CriticalHigher.SixEndpoint.B23
open CriticalHigher.PrivateBlocks
open CriticalHigher.FourHub (Prefix testFin)
local instance : Fact (Nat.Prime 251) := ⟨by norm_num⟩
private def byte (w i : ℕ) : ZMod 251 := ((w >>> (8*i)) % 256 : ℕ)
private def sharedRows : Array ℕ := #[0xc6825847a745,0x98b4ce82ad3e,0x68c231eaa4a9,0x7f80d51005d7,0x30cd57376018]
private def weights : Array ℕ := #[0xde3eeaec158cd7542e51e15dd9635de1293bea5c00004da57a593f849e26573200006a207eb1c800,0x43a8875ca937b109a1db3eac806ec976112f0000a1a302cab765d39bc5fa0000457f611d1323004d,0x38450c3a48def85f87489a440f2e8a6900003dbb8155f7ae81d2b3220000957814512229ca000679,0x774de19bbf30c8b7935333b6d7bd0000706384f6d175b064638200000458e593cfeef81300be931b,0x138906b0880444d1a50d5e790000907f8bc03bd0952ec8ad00008a435f79f5804466af00647251db,0xe7f23126ce3868d4a1750000319f37ecdaf1dfa63df70000830c676a82ed6cc0313900d7a506d493]
private def quadMoments : Array ℕ := #[0xaa6e2bfd022b8f4f94d6f7d001101000000000000,0x20902389ad57224961610b5fca3801000000000000,0x2fc378ac7634801d0ed13de0f96c01000000000000,0xeaeaa06f2ac310466ec297d272e801000000000000,0xe85c46a6ac1a1e8c3f04c4b57c2801000000000000,0x2bd1147bbaedc9127b0c9f78ec4c01000000000000]
private def poleMoments : Array ℕ := #[0xed2d246541c8ea9d57aad42a34655676f5191f86d4,0xd890c389a31e0b10b27e83c63a26d7e35d13b6f628,0xc50fb0e8a2c395f71d6ae70c7e68097b8a2de05d11,0xd295727dd4204f9b68789e19b388d811e81584a2c4,0x4d16c98499a6250f4ceecd5f03691d505ce56438cb,0xb1b778880cba962999e8c4e0d127605fe73df9dce2,0xd88a6a239549b891021b6a405caae0abaf1bc955e4,0x37bac8446370303b5a202938265896a5e27513edf5,0x101adde227aecc71d7c4f7c5447bf9b9c0a0982964,0x4537941c932d8a013b688790d002d3966b7a0dd6ab,0xcf646e0526d7e903107633edb9da837131db3a8241,0xe698166095395157c37cb040e61722e83cefc95754,0x30828e840225afe79b96c42983c75c283f02d532bd,0x6a3ec1d4a4aff1a510424f63c72ef54d62ef93bdbe,0x9e796ba15645e9e3603ca30622850ad3e2cc7bc35b,0x8e0a580dc278d596cd2f8dd4c9e13f3d55044fe6dc,0xed4e3222c23b3bd75d15c3d450500f18366b4f8686,0x92ad22a76e0928e89ec323f73b43eee36b5aa950f4,0xe853912a9f286521363470ad1766589037d72b9115,0x5496caba1f7ec616f25cd0b49d3af2d0fd4716fe4,0x1e97c9162ba8e2504422e21fc5112e0e0711fa6b81,0xb44be29e2226a710eacc11107c786797cb481bac4,0x788d297459d637457dc18e46ec3fb8a6b42c67d3a8,0x5410f3eef6e015e0d292319ab338b33ade2f4c3be9,0x88ab50629b616ec204f7dd375378a632c97f3c9ff5,0x40c2a0db2e608f2fa6f36649c49cd343971422bfc1,0x690b2b115462ecb70ca1572eddbd9a9682d1497fe5,0x81e8856d16aa33e88b1fe918750a8b6a0b1a31527d,0x1d79a4539010e3ed842a9f2bc8ca4c901769a1f10f,0x1cf634acaf5c9e633f948e3692da6ca05d12ad44d7]
private def selected : Array ℕ := #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41]
private def restRows : Array ℕ := #[0xd0c0b0a090807,0xd0c0b0a090807,0xd0c0b0a090807,0xd0c0b0a090807,0xd0c0b0a090807,0xd0c0b0a090807]
private def recoverRows : Array ℕ := #[0x1000000000001ea0000000001ea2600000001ea26e9000001ea26e93d0001ea26e93d2701ea26e93d27ba,0x1000000000001c30000000001c3ad00000001c3ad17000001c3ad17c70001c3ad17c7ab01c3ad17c7aba7,0x10000000000018f00000000018f78000000018f789a0000018f789ad100018f789ad19c018f789ad19ccd,0x100000000000113000000000113f70000000113f73a00000113f73ab2000113f73ab2450113f73ab24522,0x1000000000001d30000000001d3dd00000001d3ddce000001d3ddce0e0001d3ddce0ed601d3ddce0ed63d,0x1000000000001af0000000001af1200000001af1285000001af12857f0001af12857ff701af12857ff7f0]
private def basisRows : Array ℕ := #[0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010702ae8c7e00eac7e03835067e2661183b694806e91d3d9b3160483d139785a1cd60275961a04737cdbaf6d25260a43737,0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001b29a9af09c31c32658401126adade84a7ca994e8179609667af314c718ae21ac2acdab840399a0f28aa73ef877496c8e49,0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001deed2abe1b028ff3e4db68233e780145f8b251189ae6680b8d458ad18941613f0bec9c98d45b770848cdad2b258884a714,0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001b58d3964298913a063dcc87e86f720627a4724503a26b28d95bec9b225242178a8e545f6e4cc9cbc5322d6149e5a2c4de3,0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000016fbcf737467fd330796137100add67b5f1ccd6dece24b16e1942150e6b9e797f0157d65ab3375e2f473d680cba93610d8d,0x1000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001e980ef5c830fafa32b2418b0f6129dd04eba7bc3851171760f276e7f37d15f0556bbf7d02d06e5ea1af0e737b1f92b456d]

def D : Data (ZMod 251) 6 23 33 40 2 5 5 where
  z t := byte 0x1c7ad2edb4056975e29cbe2ab287f7706d5fe782c7daeff9adecc01264331e68275d89ab84db8374 t.val
  t s := byte 0x4bc43ddd5940af07abc016634631b69b613b66a6aa75c77b7c5a569ff9051a4d6572d50ad214d6ca s.val
  hub i := Fin.ofNat _ i.val
  left j := Fin.ofNat _ (6+2*j.val)
  right j := Fin.ofNat _ (7+2*j.val)
  G j i := if j.val<12 then (if j.val%6=i.val then 1 else 0) else byte sharedRows[j.val-12]! i.val
  owned i j := Fin.ofNat _ (6*j.val+i.val)
  node i j := if j.val=0 then Fin.ofNat _ i.val else
    Fin.ofNat _ (6+2*(6*((j.val-1)/2)+i.val)+(j.val-1)%2)
  shared j := Fin.ofNat _ (12+j.val)
  bary t := byte 0xe4073604142a40c5bea40aa4f6e2c3db5a45f00625cb63d0edbc3f06a82a371e2c91cef788e901ed t.val
  weight i t := byte weights[i.val]! t.val

def M : Moments (K:=ZMod 251) (h:=6) (r:=40) (n:=33) (free:=5) 14 where
  quad i e := byte quadMoments[i.val]! e.val
  pole j i e := byte poleMoments[6*j.val+i.val]! e.val

def L : Recovery 6 7 14 7 (ZMod 251) where
  rest i l := Fin.ofNat _ ((restRows[i.val]! >>> (8*l.val))%256)
  R i k v := byte recoverRows[i.val]! (7*k.val+v.val)
  P i k l := byte basisRows[i.val]! (7*k.val+l.val)

def sel (u : Fin 42) : Channel 6 7 5 :=
  let z := selected[u.val]!
  let a := z%9
  .inr (Fin.ofNat _ (z/9),if a<2 then .inl (Fin.ofNat _ a) else .inr (Fin.ofNat _ (a-2)))

private abbrev baryP (s : Fin 40) : Prop := D.bary s = (∏ t ∈ (Finset.univ : Finset (Fin 40)).erase s,(D.z s-D.z t))⁻¹
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def baryOK : Prefix (testFin baryP) 40 := by
  let p : Prefix (testFin baryP) 0 := Prefix.start _
  iterate 10 let p := p.step (len:=4) (by decide +kernel)
  exact p
private abbrev weightP (s : Fin 40) : Prop := ∀ i,D.weight i s = (∏ j : Fin 5,(D.z s-D.z (D.node i j)))*(∏ j : Fin 2,(D.t s+D.w (D.owned i j)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def weightOK : Prefix (testFin weightP) 40 := by
  let p : Prefix (testFin weightP) 0 := Prefix.start _
  iterate 10 let p := p.step (len:=4) (by decide +kernel)
  exact p
theorem geometry : Good D where
  distinctZ := by decide +kernel
  power := by decide +kernel
  distinctT := by decide +kernel
  cover := by decide +kernel
  separated := by decide +kernel
  awayL := by decide +kernel
  awayR := by decide +kernel
  regular := by decide +kernel
  individual := by decide +kernel
  node_inj := by decide +kernel
  pole_inj := by decide +kernel
  position := by decide +kernel
  bary := baryOK.all
  weight := fun i s => weightOK.all s i
private abbrev quadP (s : Fin 21) : Prop := ∀ i,M.quad i s = ∑ t,D.bary t*D.weight i t*((D.t t)^2+D.a i*D.t t)*D.z t^s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def quadOK : Prefix (testFin quadP) 21 := by
  let p : Prefix (testFin quadP) 0 := Prefix.start _
  iterate 21 let p := p.step (len:=1) (by decide +kernel)
  exact p
private abbrev poleP (s : Fin 21) : Prop := ∀ j i,M.pole j i s = ∑ t,D.bary t*D.weight i t/(D.t t+D.w (D.shared j))*D.z t^s.val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def poleOK : Prefix (testFin poleP) 21 := by
  let p : Prefix (testFin poleP) 0 := Prefix.start _
  iterate 21 let p := p.step (len:=1) (by decide +kernel)
  exact p
theorem moments : Correct D M where
  quad := fun i e => quadOK.all e i
  pole := fun j i e => poleOK.all e j i
private abbrev recoverP (s : Fin 14) : Prop := ∀ i j,(if j=s then (1:ZMod 251) else 0) = (∑ v,L.R i s v*M.quad i (degreeIndex v j)) + ∑ l,L.P i s l*(if j=L.rest i l then 1 else 0)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def recoverOK : Prefix (testFin recoverP) 14 := by
  let p : Prefix (testFin recoverP) 0 := Prefix.start _
  iterate 14 let p := p.step (len:=1) (by decide +kernel)
  exact p
open CriticalHigher.Hub251 (fromRows batch batch_sound injective_of_rows)
def matrixRows : Array ℕ := #[
  0xeb8a531ed2c89a1af907f4088e4652f1cd56ce533ebe5e787a830597dfed2ec0ce7c905a2e053ddc29a4,
  0x975bce153f3d3131004d23f392885839d8070c563350a9f4f01647b9d646463a0a984fe73ccb65b7ee74,
  0xb4835e17d029d234098254f9606057185ab2e77af9a00173064913210b5964d20c70cf2786f013bb63b9,
  0x4d62e8530f679a3e45783d4f0cb6c785545d7d3320bd546134d570bb9484b4f9a1884fd55749d97e0247,
  0xe583eb4e1460a7ea8890b517a97471a7e287eecf9b8d25bbd6ed9060e800b0c851e9c5e28e180e2d4972,
  0x9f6fae75236a19600f54234daf6dce93c9e52d3f406700144e1858d014f300bb061c8d520249285293d6,
  0x1a3302221913b62362975275a0e55b0ed2227a387eddce0609cf58e671cd648de2d9bd8b6935c4533be2,
  0x38920ee3cd97c8e0c035dc207c5354a3294675cf1bd9dfa289877bd58583d8a085e65671883de6ead172,
  0x5dca23387c0c1b8f7227e603a4d9aa34139612f1c16bcd74c87fdaee060212e0c8da7d05568162050fc1,
  0xd3456632261e4fd8d27795a79c776875cd29cc5ea0a104b60262b78b4d9378bf01e7aecff22925a221d5,
  0x5079f93505d0e60f267bc742de6d50b64db4ec64bc65c49d1e6f5fb7cc13fa3dd246d03bbc9da6289c06,
  0x6b8fbdb56825d9a9871025a8b855ec55d66500c70774f328b3e4b15dc61f6b305587c8859398a5ae724e,
  0x4ec573f708fa60d8a5d883f264992d02c7cdd74e2de01b7477c047c861b43e02f689647fac84c7716aa3,
  0x2b3ccf91a2e3536618900d68ced84d8923ef7a60c9f6df04ea16e9b08793b1a9f18aae2a38a270991adc,
  0x96e6d0428590b9309e54e8ed12b77df46ed328784457bc1309afc251196daf79ed9109f7b891b12e1baa,
  0xb9d398abcb7db21aee4c25260f572cd3445be8d6ed06bf63d79df0e0b2d5dc0b9604a8640f98b7606896,
  0xf102a69e9cded4e76c860e9ba4d2d4599bcb3bc05404d5bd1d0157ec96d9f773cde4b2e2bc160b792318,
  0x7053ded6185019c0fadccc704eef75076d40af0ae0543d299562668a8047ab26b5906e61f9873b8f46db,
  0x53859cc9cf1d7bc7f5d0513cb380152dd21cf3127cd074aed29afa2b7a2eda723bb1bc88d0e18a513dd7,
  0x1ce2326f5825a90d57885883147f04c529518c711dc8d4a1b066ce872d92e7981e208f7f7471191a96ea,
  0xa2f6a390dbc8b587c579614f201d68b2020ec2c862611fbf8d1101f5cf381cef7210471be55ee3e653e5,
  0x584b208c078c3756d3cbab91b752c44725eabf3e93063d59f6551d09cd18cd1a44c62e5628f0d55d1933,
  0x6caa5ef2acf1dd1e56059ca4cb79189c6566e2df9d3859ab15fa0b58929ebff85772384ddf7eb9c44024,
  0xe318106d06c469366265f4baecc9bc048ac2968fd0d0ea111a1690237880a702d71a9a7216902aa0d06e,
  0xa4817c8df14535628c3e40271f86ddf4db24d649434b7af25cf6d4c04b85e7e743a89457eb749214c764,
  0x4c2d4eb0428e769c5445ab911328964e6377c6245782c07c626445d13dcd1e3b9ab269053706ce9b7725,
  0x5a636b5af1b50b93472f1279336c48f9899ac004007eba89a17816b2f6daa113e4f485ce6b41b741b65c,
  0x31dd106ee26722d7908371d9836cd81cc4aebf17ef85adf1227de9e578c9c9e35a251f4a78d7ca07e009,
  0x77e6f0166a9101f0f31901773b1abb8a2238829e2358ba181313e13731c2106be8614364606d0da87bb6,
  0x9ba35bb822a6f5d645b1272310d6cb926b08613b5d39ad1a8e9a4f73c7bcd233b1a8126839f75892b9a9,
  0xca3726e55e46c7c81985da5133a5a8a815e848ec17c9ace9171d277ab1f122a6708eb6780445412988c2,
  0x46020068589c0c6ac28a6cb5b413996712f035da47dccc662f67e858e1767194b6da2d29ad53460dd334,
  0x63b484734cee1a8c7dc08fcf18e4bfc2405cd308690a25cf99bb13044d3e2228e09441a5253a7e0c7c11,
  0x3179e5357289f5a8b0c3983bf8c32816455920e7d62cc1ecd0796119f92d9ce0836c7609a1658a5b4116,
  0x9ea21dcbdde325a1f33ba438cc28d440caa9539b2f8584edb9dceaeb1ab04ed19e742fc97de18dcd11eb,
  0x63782e7a8277213bab0073d2e00be8df48ee670a5fe3e5d191b83f6c2edbb9643c82395a46849d38f42b,
  0x446f84126b4c91ae27da7f4b9c5ddb73dae0af45a8bd695ac8d0a3ab2f5a090f2f1ecef09a690569aea2,
  0xcb881bed36b299c7cad5717ea5c2ce537eb5c6e14b32462cef74bdceb0f2ddb46077991a0f1f0fc97c48,
  0x6f9cc952f6258bc434ce45c60c021ad413bda66395b7bfba8c310e663a79cc023a271c6a91cdb599cf1a,
  0x1fa4bbac556833b6c2b61998da15396a10de27c47b5038830b542b78270f643ad109b9dbda6ee09daf33,
  0x959d34c46ab0b0657312191bd6ef3c0c9edf834325504a90aebfbe1b283175b49a1722afed0dabe24c0c,
  0x30b50be5258ab59e7158641d9ea08d7ff3a1ac05072b61534b49a63240f746b02f8f39d865e1022d0618]


def inverseRows : Array ℕ := #[
  0x92b8b8ca8ebf8597573dcfb907760139f69671d832e3122068a856f0dc515568f7c1a843129582df3085,
  0x9053c621cdeb8ef4afabef81ef84d662a0b81abf03b2be111f834a524829882043a11db4c6524c938c7c,
  0xe08fca8585f27c78098ac5d968cc43e6050c77cf32e324ba8884f4337f54291959080ade1273a9ba8854,
  0x7c50888a4015672ba0db6038dac0c84660e3b135e20e79fa930930590853e7b79502b8aab39f55735a98,
  0x1e2dc1b659c577a33b0f25ceb962a4f0a3884eabf9ced86cd6a739fa6e6d54013ecf64c77ff650c80ec4,
  0xa022a336f42bb6cb819f14076080c809171a3892347d03a0d7e987e8e3c87c92919754e252b0ec5384e1,
  0xcfbf6a795b6bcb317dcc7185b0a0b768400d380d0545cf551e80f6fad741e84fdfc853668390cc4eaaf4,
  0xc1ea8aa28a8dd0ab2dab426229ac30ea1d71d160146b1350bc5b6bf5ac55402b4052642c51ef9636ae46,
  0x5f618496471adb193be11eb5a365724c5d7658d1ca133ec4382f37a032f0d0e858f4a32d7e92d77d75e1,
  0x49314be44595801f13576aef1ae63bc90ce0881d79fae4ab08a8130fc52f3639cfbae1e699c6031ab508,
  0x2a46f3baa54c3a970e1c4015347f4630cf46b0a84da39b003c581a542656a293adc5410fde269b1427c9,
  0x3aac80ed859e5a27ed7ebaf177ed8f2b54a88ae673b59266ad69a85e78ccc1ebd7ea40a0fcacba1f41b,
  0x2dd2037e5eaf34636590331e19928143445ff2603f3a3d07d5041292c9f6795a8ed75f964c9c57f5f3cf,
  0xe294a5db721bced82577cc462a95419233b5e1c7f649a999bf245d924747ba2ee33d08265b202c51fae2,
  0x9bcfe98873610ccb5b96b0a8b336002aac0063abaa6f141534ae31624603f5c53c02e2328ff616ab5ad7,
  0x7990bac4b3d70a596e549cd995a6d8d864b11def3c9627030441d1326e52e4d928694b0934e82ec19a82,
  0xa70a675c49cf82247d5367cb738b3eb0c0419f272108e6ba93e9444fbf3171df5c333d0fdfe5e38fd2e7,
  0x804d93e18cda0fce550c1c8653ca9fbe998e4c66d654e2c27c9f43d76714c1e46d1bdf593124cc90a9ab,
  0x1cd982f67a52c776e66a0e58a7b899548c7fa4a318190405d2f303808eaf9dacf332aa282b3236835a95,
  0xb0d1b1049e1e93c650a9afe45dc1312c5dc74d7226687bf0107173e0d7f79873e5c30d2b4e5cb4a94d68,
  0xafdd7d71f51a4631f7b6b4b0a8d8f410ec7a197a9f6f58032792eb057ef8e49a896ae1aac1d056a6d81e,
  0x2d35c995f4b4f2a373d4bd4a2e936bdb4bd754119cf9beacd7b172c91e7dc2c95e35abd38f1da9f09e52,
  0x4c0d9fc02a6884ecabbfe0a89ef6ce915f554c01d997c5855aa1bceeef43d2350cce030ac32e9ebb7142,
  0x437fc33679f45a4286781a74490b2c61d67e39d471f57194e5d225734c2ed80acd9773e52f2b9cd8bbc3,
  0x4e38967c7e91ba760481abb5446887c1059c2b93197b3bb29101d7f1fa0cd41171485ce6a256ab0a47b2,
  0x3eba5ec5831ffa3648c9b7c428f4390aa9448e454c73d25d976a1e517032f7446eabe40ab36fa9147e1a,
  0xd7fa44dfe4b971ef4b35bf3cd0ef50d9c44457666a8c5e47b33371ed080aee7bba1170f861495e2cd5,
  0x45f6c8954c05b5843df360f12d04ae39e8e8b421e275541de0aff8b2ca25bf1cbf38ca2cef7e9faf0b00,
  0x456b84048730147352606205dfe0aae92bb2f61ee902016edea018dfb0f0948550ab2ea29f65468b769a,
  0xdd388cea15a75ca38f4db588acf4336ca867a489e6f169b86c922ee5e972f6dd3d8abcd4a3ed4680330e,
  0x886210dab9524a1b0737f5ccf34c474d1f1a759796a237b29eaa5d6ead5919497f9c08f1ce366a173ab0,
  0x571159928705b6b77015dc65c9a684beea3671056bf9787c04cfa267bff2f41289b1f0c7d22e52bde29f,
  0xf81cc9df1e38b1dac0bf3a5fb7e7130409a7115ad249b9d72696911428f63d8c979f8416e72478a2b81a,
  0xdd81068022307f20ee321069417c11374a7976ce54c12a580ce69d44af6a503d36c1736d55a97b495309,
  0x54c62a8c3e47eb6fdc10b96a7a6db54d075b1a84870df4f21dcb9a49385f31c3e8a20524ab9b7254bdf0,
  0x433a160d93221ad63340e2cb9adfdb13ac3571d977f348cb6bc26e794391d8a3f96e253bb0ef1f680c10,
  0x16bf762fdc9e04ec4a9aa2b4c9afc0a5141f56d5465ecd261b321cce3c4703075d2b0b80cfb427e82f87,
  0xc1e11fdb441e88df837dcc292207aaf70febc8e724f95e32e27e29c8409b3df98eb30b8daf4686051c4d,
  0x67a9804f7e3416a58f196f768de6b69eb1b58776186530acb469f7d42de51776ab7a01651217d91e5746,
  0xd940a9e3a77cb0b951eaab2e916f32c5b2179bd621e854df608cc0d19d80d43b09d8a6bd26d0199808a2,
  0xaa32007a6e5dcaecf9d8ca4290022ecef55c6a3c0a9629a088edf45aedea066045d0aa648a348deb0097,
  0x2ab07b7dd36aec59409e7c063f401891eb9f8d58bd16df2713743d5fbca22f1b20f472ea7513eb4a8ce9]


private def packed (u : ℕ) := matrixRows[u]?.getD 0
private def inversePacked (u : ℕ) := inverseRows[u]?.getD 0
private def A : Matrix (Fin 42) (Fin 42) (ZMod 251) := fromRows 42 packed
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem batch_verified : batch 42 packed inversePacked 0 42=true := by decide +kernel
private theorem injective : Function.Injective A.mulVec := by
  apply injective_of_rows (by decide : 42≤256) packed inversePacked
  intro i
  exact batch_sound packed inversePacked 0 42 batch_verified i.val (Nat.zero_le _) i.isLt
private abbrev entriesP (s : Fin 42) : Prop := ∀ i l,A s (finProdFinEquiv (i,l))=smallEntry D M L (sel s) i l
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
private def entriesOK : Prefix (testFin entriesP) 42 := by
  let p : Prefix (testFin entriesP) 0 := Prefix.start _
  iterate 21 let p := p.step (len:=2) (by decide +kernel)
  exact p

theorem spans :
    ∃ x : Fin 40 → Fin 3 → ℂ, ∃ y : Fin 40 → Fin 23 → ℂ, ∃ z : Fin 40 → Fin 33 → ℂ,
      ∀ T : Fin 3 → Fin 23 → Fin 33 → ℂ, ∃ u : Fin 40 → Fin 3 → ℂ,
        ∃ v : Fin 40 → Fin 23 → ℂ, ∃ w : Fin 40 → Fin 33 → ℂ, ∀ i j k,
          T i j k = ∑ a,(u a i*(y a j*z a k)+x a i*(v a j*z a k)+x a i*(y a j*w a k)) := by
  apply CriticalHigher.PrimeTangent.exists_lift (p:=251)
  obtain ⟨Y,Z,f⟩ := tangent_of_small_minor D M L (by decide) (by decide) (by decide) (by decide)
    (by decide : 0<14) (by decide) geometry moments (fun i k j => recoverOK.all k i j)
    sel A (fun u i l => entriesOK.all u i l) injective
  exact ⟨fun i => ![1,D.t i,(D.t i)^3],Y,Z,f⟩

theorem generic_rank : Arxiv.«0805.3777».IsGenericRank [3,23,33] 40 :=
  CriticalLastSlice.TwoPlanes.generic_rank_of_witness (by decide) (by decide) (by decide) (by decide) spans

end CriticalHigher.SixEndpoint.B23

theorem OMA.solution : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H2_R1_H2_R2.H1 :=
  ⟨CriticalConicBoundary.odd_boundary_rank 5 (by decide) (by decide),
   CriticalLastSlice.TwoPlanes.generic_rank_of_witness (by decide) (by decide) (by decide) (by decide)
     CriticalHigher.ComponentSeed.B24.tinySpans,
   CriticalHigher.SixEndpoint.B16.generic_rank, CriticalHigher.SixEndpoint.B23.generic_rank,
   CriticalHigher.FrontierSeed.B18.generic_rank, CriticalHigher.FrontierSeed.B24.generic_rank,
   CriticalHigher.FrontierSeed.B23.generic_rank, CriticalHigher.FrontierSeed.B47.generic_rank⟩
