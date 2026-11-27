import OMAReductions.R_Erdos19_erdos_19_R1_H2_R1_H2_R1

-- Credit: @zarnab222-dev
/-! A five-edge alternating path augments a matching whenever two disjoint chosen ends can reach distinct unused supports through their mates. Fisher’s inequality forces a disjoint pair of chosen ends. If no path augments, either a mate has no unused neighbor or the two mates have exactly the same single unused neighbor, giving a five-cycle. -/

/- Fisher's inequality for pairwise-intersecting linear support families. -/

open Finset

namespace E19FiveFisher

/-- Distinct blocks meet exactly once, so their real incidence vectors are independent. -/
theorem fisher_one {n : ℕ} (K : Finset (Finset (Fin n)))
    (size : ∀ A ∈ K, 2 ≤ A.card)
    (one : ∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card = 1) : K.card ≤ n := by
  classical
  let v (A : K) (i : Fin n) : ℝ := if i ∈ A.val then 1 else 0
  have gram (A B : K) : (∑ i ∈ A.val, v B i) =
      1 + (if B=A then (A.val.card:ℝ)-1 else 0) := by
    by_cases same : B=A
    · subst B
      simp [v]
    · have diff : A.val ≠ B.val := fun he => same (Subtype.ext he.symm)
      simp [v, same, one _ A.property _ B.property diff]
  have independent : LinearIndependent ℝ v := by
    refine Fintype.linearIndependent_iff.mpr ?_
    intro g relation
    let T : ℝ := ∑ B : K, g B
    have column (i : Fin n) : ∑ B : K, g B * v B i = 0 := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        using congrFun relation i
    have row (A : K) : T + g A * ((A.val.card:ℝ)-1) = 0 := by
      have he : ∑ B : K, g B * (∑ i ∈ A.val, v B i) = 0 := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        simp only [column, Finset.sum_const_zero]
      simp only [gram, mul_add, mul_one, mul_ite, mul_zero, Finset.sum_add_distrib] at he
      simpa [T] using he
    have weight (A : K) : 0 < (A.val.card:ℝ)-1 := by
      have h : (2:ℝ) ≤ A.val.card := by exact_mod_cast size _ A.property
      linarith
    have total : T=0 := by
      rcases lt_trichotomy T 0 with ht | ht | ht
      · have hpos (A : K) : 0 ≤ g A := by
          by_contra! hbad
          linarith [row A, mul_neg_of_neg_of_pos hbad (weight A)]
        exact (ht.not_ge (Finset.sum_nonneg fun A _ => hpos A)).elim
      · exact ht
      · have hneg (A : K) : g A ≤ 0 := by
          by_contra! hbad
          linarith [row A, mul_pos hbad (weight A)]
        exact (ht.not_ge (Finset.sum_nonpos fun A _ => hneg A)).elim
    intro A
    have h := row A
    rw [total,zero_add] at h
    exact (mul_eq_zero.mp h).resolve_right (weight A).ne'
  simpa only [Fintype.card_coe, Module.finrank_fin_fun] using independent.fintype_card_le_finrank

/-- At most n mutually intersecting linear supports of size at least two fit on n indices. -/
theorem fisher_bound {n : ℕ} (K : Finset (Finset (Fin n)))
    (size : ∀ A ∈ K, 2 ≤ A.card)
    (linear : ∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1)
    (intersect : ∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).Nonempty) : K.card ≤ n := by
  apply fisher_one K size
  intro A hA B hB hne
  have hpos := Finset.card_pos.mpr (intersect A hA B hB hne)
  have hle := linear A hA B hB hne
  omega

end E19FiveFisher
open Finset
open scoped Classical

namespace E19Five
/-- Flip the five-edge alternating path from x through two matched pairs to y. -/
theorem augment {V : Type*} [DecidableEq V] (K : Finset (Finset V)) {m : ℕ}
    (L R : Fin m → Finset V) (lK : ∀ k, L k ∈ K) (rK : ∀ k, R k ∈ K)
    (il : Function.Injective L) (ir : Function.Injective R)
    (apart : ∀ a b, L a ≠ R b) (matched : ∀ k, Disjoint (L k) (R k))
    (i j : Fin m) (ij : i ≠ j) (x y : Finset V) (xK : x ∈ K) (yK : y ∈ K)
    (xy : x ≠ y) (xl : ∀ k, x ≠ L k) (xr : ∀ k, x ≠ R k)
    (yl : ∀ k, y ≠ L k) (yr : ∀ k, y ≠ R k)
    (first : Disjoint x (R i)) (middle : Disjoint (L i) (L j)) (last : Disjoint y (R j)) :
    ∃ l r : Fin (m+1) → Finset V, (∀ k, l k ∈ K) ∧ (∀ k, r k ∈ K) ∧
      Function.Injective l ∧ Function.Injective r ∧ (∀ a b, l a ≠ r b) ∧
      ∀ k, Disjoint (l k) (r k) := by
  classical
  let g (k : Fin m) := if k = i then x else if k = j then y else L k
  have gi : Function.Injective g := by
    intro a b h
    dsimp [g] at h
    split_ifs at h <;> grind
  have fresh (k : Fin m) : L i ≠ g k ∧ L j ≠ g k := by
    dsimp [g]
    split_ifs <;> grind
  have home (k : Fin m) : g k ∈ K := by dsimp [g]; split_ifs <;> grind
  have sep (a b : Fin m) : g a ≠ R b := by dsimp [g]; split_ifs <;> grind
  have good (k : Fin m) : Disjoint (g k) (R k) := by dsimp [g]; split_ifs <;> grind
  refine ⟨Fin.cons (L i) g, Fin.cons (L j) R, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Fin.cases (lK i) home
  · exact Fin.cases (lK j) rK
  · intro a b
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b <;>
      simp [Fin.cons_zero, Fin.cons_succ, gi.eq_iff, (fresh _).1, Ne.symm (fresh _).1]
  · intro a b
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b <;>
      simp [Fin.cons_zero, Fin.cons_succ, ir.eq_iff, apart, fun k => Ne.symm (apart j k)]
  · intro a b
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b <;>
      simp [Fin.cons_zero, Fin.cons_succ, il.ne ij, apart, fun k => Ne.symm (fresh k).2, sep]
  · exact Fin.cases middle good

theorem critical_pair {n m : ℕ} (K U : Finset (Finset (Fin n)))
    (L : Fin m → Finset (Fin n)) (lK : ∀ k, L k ∈ K) (il : Function.Injective L)
    (sub : U ⊆ K) (lout : ∀ k, L k ∉ U)
    (umeet : ∀ A ∈ U, ∀ B ∈ U, ¬ Disjoint A B) (lmeet : ∀ k, ∀ A ∈ U, ¬ Disjoint (L k) A)
    (size : ∀ A ∈ K, 2 ≤ A.card)
    (linear : ∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1)
    (large : n < U.card+m) : ∃ i j, i ≠ j ∧ Disjoint (L i) (L j) := by
  classical
  let S := U ∪ univ.image L
  have members (A) (ha : A ∈ S) : A ∈ U ∨ ∃ k, L k = A := by simpa [S] using ha
  have incl : S ⊆ K := by
    intro A ha
    rcases members A ha with u | ⟨k,rfl⟩
    · exact sub u
    · exact lK k
  have dj : Disjoint U (univ.image L) := by
    rw [Finset.disjoint_left]
    intro A hu ha
    obtain ⟨k,_,rfl⟩ := mem_image.mp ha
    exact lout k hu
  have crit : ∃ i j, i ≠ j ∧ Disjoint (L i) (L j) := by
    by_contra! no
    have bound := E19FiveFisher.fisher_bound S (fun A ha => size A (incl ha))
      (fun A ha B hb => linear A (incl ha) B (incl hb)) (by
        intro A ha B hb ne
        apply Finset.not_disjoint_iff_nonempty_inter.mp
        rcases members A ha with au | ⟨i,rfl⟩ <;> rcases members B hb with bu | ⟨j,rfl⟩
        · exact umeet _ au _ bu
        · exact fun h => lmeet j _ au h.symm
        · exact lmeet i _ bu
        · exact no i j (fun h => ne (congrArg L h)))
    simp only [S,card_union_of_disjoint dj,card_image_of_injective _ il,card_univ,Fintype.card_fin] at bound
    omega
  exact crit
end E19Five

namespace OMA.R_Erdos19_erdos_19_R1_H2_R1_H2_R1_H1_R1

def H1 : Prop := ∀ (n r : ℕ) (K : Finset (Finset (Fin n))), 3 ≤ r → r*r+r-1 ≤ n →
    n ≤ r*((n-r)/(r-1)) →
    (∃ T ∈ K, T.card = r) → (∀ A ∈ K, r ≤ A.card) →
    (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1) →
    (∀ T ∈ K, n ≤ ((K.erase T).filter fun A => (T ∩ A).Nonempty).card) →
    3 ≤ (K.filter fun A => 3 ≤ A.card).card →
    (¬ ∃ e : Fin n ≃ Fin n, ∀ A ∈ K.image (Finset.map e.toEmbedding),
      3 ≤ A.card → ∃ l r : Fin n, A = Finset.Icc l r) →

    (¬ ∃ L R : Finset (Finset (Fin n)), L ∪ R = K ∧ Disjoint L R ∧
      (∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).Nonempty) ∧
      (∀ A ∈ R, ∀ B ∈ R, A ≠ B → (A ∩ B).Nonempty)) →
    (¬ ∃ T ⊆ K, T.card = 3 ∧ ∀ A ∈ T, ∀ B ∈ T, A ≠ B → Disjoint A B) →
    ∀ (m : ℕ) (L R : Fin m → Finset (Fin n)) (U : Finset (Finset (Fin n))),
    (∀ i, L i ∈ K) → (∀ i, R i ∈ K) → Function.Injective L → Function.Injective R →
    (∀ i j, L i ≠ R j) → (∀ i, Disjoint (L i) (R i)) → U ⊆ K →
    (∀ A ∈ U, ∀ B ∈ U, ¬ Disjoint A B) → (∀ i, ∀ A ∈ U, ¬ Disjoint (L i) A) →
    (∀ i, L i ∉ U) → (∀ i, R i ∉ U) → K.card = U.card+2*m →
    (U.card + m = n + 1) → (2 * (r - 1) < m) →
    (¬ ∃ w : Fin n → ℝ, ∀ A ∈ U ∪ univ.image L, ∑ i ∈ A, w i = 1) →
    (∃ i j, i ≠ j ∧ Disjoint (L i) (L j) ∧ ∀ x ∈ U, ¬ Disjoint x (R i)) →
    ∃ l r' : Fin (m+1) → Finset (Fin n), (∀ i, l i ∈ K) ∧ (∀ i, r' i ∈ K) ∧
      Function.Injective l ∧ Function.Injective r' ∧ (∀ i j, l i ≠ r' j) ∧ ∀ i, Disjoint (l i) (r' i)

def H2 : Prop := ∀ (n r : ℕ) (K : Finset (Finset (Fin n))), 3 ≤ r → r*r+r-1 ≤ n →
    n ≤ r*((n-r)/(r-1)) →
    (∃ T ∈ K, T.card = r) → (∀ A ∈ K, r ≤ A.card) →
    (∀ A ∈ K, ∀ B ∈ K, A ≠ B → (A ∩ B).card ≤ 1) →
    (∀ T ∈ K, n ≤ ((K.erase T).filter fun A => (T ∩ A).Nonempty).card) →
    3 ≤ (K.filter fun A => 3 ≤ A.card).card →
    (¬ ∃ e : Fin n ≃ Fin n, ∀ A ∈ K.image (Finset.map e.toEmbedding),
      3 ≤ A.card → ∃ l r : Fin n, A = Finset.Icc l r) →

    (¬ ∃ L R : Finset (Finset (Fin n)), L ∪ R = K ∧ Disjoint L R ∧
      (∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).Nonempty) ∧
      (∀ A ∈ R, ∀ B ∈ R, A ≠ B → (A ∩ B).Nonempty)) →
    (¬ ∃ T ⊆ K, T.card = 3 ∧ ∀ A ∈ T, ∀ B ∈ T, A ≠ B → Disjoint A B) →
    ∀ (m : ℕ) (L R : Fin m → Finset (Fin n)) (U : Finset (Finset (Fin n))),
    (∀ i, L i ∈ K) → (∀ i, R i ∈ K) → Function.Injective L → Function.Injective R →
    (∀ i j, L i ≠ R j) → (∀ i, Disjoint (L i) (R i)) → U ⊆ K →
    (∀ A ∈ U, ∀ B ∈ U, ¬ Disjoint A B) → (∀ i, ∀ A ∈ U, ¬ Disjoint (L i) A) →
    (∀ i, L i ∉ U) → (∀ i, R i ∉ U) → K.card = U.card+2*m →
    (U.card + m = n + 1) → (2 * (r - 1) < m) →
    (¬ ∃ w : Fin n → ℝ, ∀ A ∈ U ∪ univ.image L, ∑ i ∈ A, w i = 1) →
    (∃ i j, i ≠ j ∧ Disjoint (L i) (L j) ∧ ∃ x ∈ U,
      ∀ y ∈ U, (Disjoint y (R i) ↔ y=x) ∧ (Disjoint y (R j) ↔ y=x)) →
    ∃ l r' : Fin (m+1) → Finset (Fin n), (∀ i, l i ∈ K) ∧ (∀ i, r' i ∈ K) ∧
      Function.Injective l ∧ Function.Injective r' ∧ (∀ i j, l i ≠ r' j) ∧ ∀ i, Disjoint (l i) (r' i)

theorem main : H1 → H2 → OMA.R_Erdos19_erdos_19_R1_H2_R1_H2_R1.H1 := by
  classical
  intro dead cycle n r K hr gap pack min size linear degree many disorder nonsplit tri m L R U lk rk il ir apart matched sub um lm lo ro count total band weight
  obtain ⟨i,j,ij,mid⟩ := E19Five.critical_pair K U L lk il sub lo um lm (fun A ha => by have := size A ha; omega) linear (by omega)
  by_cases hi : ∃ x ∈ U, Disjoint x (R i)
  · by_cases hj : ∃ x ∈ U, Disjoint x (R j)
    · by_cases path : ∃ x ∈ U, ∃ y ∈ U, x ≠ y ∧ Disjoint x (R i) ∧ Disjoint y (R j)
      · obtain ⟨x,hx,y,hy,xy,first,last⟩ := path
        apply E19Five.augment K L R lk rk il ir apart matched i j ij x y (sub hx) (sub hy) xy
        all_goals first | exact first | exact mid | exact last | grind
      · obtain ⟨x,hx,first⟩ := hi
        obtain ⟨z,hz,last⟩ := hj
        have eq : x=z := by by_contra h; exact path ⟨x,hx,z,hz,h,first,last⟩
        subst z
        apply cycle n r K hr gap pack min size linear degree many disorder nonsplit tri m L R U lk rk il ir apart matched sub um lm lo ro count total band weight
        refine ⟨i,j,ij,mid,x,hx,?_⟩
        intro y hy
        constructor
        · constructor
          · intro yi
            by_contra ne
            exact path ⟨y,hy,x,hx,ne,yi,last⟩
          · rintro rfl; exact first
        · constructor
          · intro yj
            by_contra ne
            exact path ⟨x,hx,y,hy,Ne.symm ne,first,yj⟩
          · rintro rfl; exact last
    · apply dead n r K hr gap pack min size linear degree many disorder nonsplit tri m L R U lk rk il ir apart matched sub um lm lo ro count total band weight
      exact ⟨j,i,ij.symm,mid.symm,fun x hx h => hj ⟨x,hx,h⟩⟩
  · apply dead n r K hr gap pack min size linear degree many disorder nonsplit tri m L R U lk rk il ir apart matched sub um lm lo ro count total band weight
    exact ⟨i,j,ij,mid,fun x hx h => hi ⟨x,hx,h⟩⟩

end OMA.R_Erdos19_erdos_19_R1_H2_R1_H2_R1_H1_R1
