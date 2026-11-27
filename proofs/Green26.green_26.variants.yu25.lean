import FormalConjectures.GreensOpenProblems.«26»

/-!
Formalization of Yang Yu (2025), Four cubes cover F_3^n (Green open problem 26, yu25 variant),
via square-free exterior algebra ideals over RatFunc (ZMod 3) and Combinatorial Nullstellensatz.
-/

namespace OMA.Yu25

variable {ι K : Type*}

structure SqFreeAlg (ι K : Type*) where
  coeff : Finset ι → K

namespace SqFreeAlg

lemma ext {f g : SqFreeAlg ι K} (h : ∀ S, f.coeff S = g.coeff S) : f = g := by
  cases f; cases g; congr 1; exact funext h

section RingOps

variable [DecidableEq ι] [CommRing K]

private def mulSq (f g : SqFreeAlg ι K) : SqFreeAlg ι K :=
  ⟨fun S => ∑ T ∈ S.powerset, f.coeff T * g.coeff (S \ T)⟩

private lemma mulSq_comm (f g : SqFreeAlg ι K) : mulSq f g = mulSq g f := by
  apply ext
  intro S
  dsimp [mulSq]
  refine Finset.sum_bij (fun T _ => S \ T) ?_ ?_ ?_ ?_
  · intro T hT
    rw [Finset.mem_powerset] at hT ⊢
    exact Finset.sdiff_subset
  · intro T₁ hT₁ T₂ hT₂ h
    rw [Finset.mem_powerset] at hT₁ hT₂
    have := congrArg (fun X => S \ X) h
    simpa [Finset.sdiff_sdiff_eq_self hT₁, Finset.sdiff_sdiff_eq_self hT₂] using this
  · intro T hT
    rw [Finset.mem_powerset] at hT
    exact ⟨S \ T, Finset.mem_powerset.mpr Finset.sdiff_subset,
      Finset.sdiff_sdiff_eq_self hT⟩
  · intro T hT
    rw [Finset.mem_powerset] at hT
    rw [Finset.sdiff_sdiff_eq_self hT, mul_comm]

private lemma mulSq_assoc (f g h : SqFreeAlg ι K) : mulSq (mulSq f g) h = mulSq f (mulSq g h) := by
  apply ext
  intro S
  dsimp [mulSq]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  have lhs_eq : ∑ U ∈ S.powerset, ∑ T ∈ U.powerset, f.coeff T * g.coeff (U \ T) * h.coeff (S \ U) =
      ∑ p ∈ S.powerset.sigma (fun U => U.powerset),
        f.coeff p.2 * g.coeff (p.1 \ p.2) * h.coeff (S \ p.1) :=
    (Finset.sum_sigma (S.powerset) (fun U => U.powerset)
      (fun p => f.coeff p.2 * g.coeff (p.1 \ p.2) * h.coeff (S \ p.1))).symm
  have rhs_eq : ∑ T ∈ S.powerset, ∑ V ∈ (S \ T).powerset,
      f.coeff T * (g.coeff V * h.coeff ((S \ T) \ V)) =
      ∑ p ∈ S.powerset.sigma (fun T => (S \ T).powerset),
        f.coeff p.1 * (g.coeff p.2 * h.coeff ((S \ p.1) \ p.2)) :=
    (Finset.sum_sigma (S.powerset) (fun T => (S \ T).powerset)
      (fun p => f.coeff p.1 * (g.coeff p.2 * h.coeff ((S \ p.1) \ p.2)))).symm
  rw [lhs_eq, rhs_eq]
  refine Finset.sum_bij (fun p _ => ⟨p.2, p.1 \ p.2⟩) ?_ ?_ ?_ ?_
  · rintro ⟨U, T⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hp ⊢
    exact ⟨hp.2.trans hp.1, Finset.sdiff_subset_sdiff hp.1 le_rfl⟩
  · rintro ⟨U₁, T₁⟩ hp₁ ⟨U₂, T₂⟩ hp₂ hEq
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hp₁ hp₂
    have hT : T₁ = T₂ := congrArg Sigma.fst hEq
    subst hT
    have hD : U₁ \ T₁ = U₂ \ T₁ := by
      simpa using congrArg Sigma.snd hEq
    have hU : U₁ = U₂ := by
      rw [← Finset.union_sdiff_of_subset hp₁.2, ← Finset.union_sdiff_of_subset hp₂.2, hD]
    cases hU; rfl
  · rintro ⟨T, V⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hp
    refine ⟨⟨T ∪ V, T⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_powerset]
      exact ⟨Finset.union_subset hp.1 (hp.2.trans Finset.sdiff_subset), Finset.subset_union_left⟩
    · have hdisj : Disjoint T V := disjoint_sdiff_self_right.mono_right hp.2
      simp [Finset.union_sdiff_cancel_left hdisj]
  · rintro ⟨U, T⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hp
    dsimp only
    have hs : (S \ T) \ (U \ T) = S \ U := by
      ext x
      simp only [Finset.mem_sdiff]
      have hsub := hp.2
      constructor
      · rintro ⟨⟨hxS, hxT⟩, hxUT⟩
        refine ⟨hxS, fun hxU => hxUT ⟨hxU, hxT⟩⟩
      · rintro ⟨hxS, hxU⟩
        refine ⟨⟨hxS, fun hxT => hxU (hsub hxT)⟩, fun ⟨hxU', _⟩ => hxU hxU'⟩
    rw [hs, mul_assoc]

instance : Zero (SqFreeAlg ι K) := ⟨⟨fun _ => 0⟩⟩
instance : Add (SqFreeAlg ι K) := ⟨fun f g => ⟨fun S => f.coeff S + g.coeff S⟩⟩
instance : Neg (SqFreeAlg ι K) := ⟨fun f => ⟨fun S => - f.coeff S⟩⟩
instance : Sub (SqFreeAlg ι K) := ⟨fun f g => ⟨fun S => f.coeff S - g.coeff S⟩⟩

instance : AddCommGroup (SqFreeAlg ι K) where
  add_assoc a b c := by apply ext; intro S; exact add_assoc _ _ _
  zero_add a := by apply ext; intro S; exact zero_add _
  add_zero a := by apply ext; intro S; exact add_zero _
  nsmul := nsmulRec
  neg_add_cancel a := by apply ext; intro S; exact neg_add_cancel _
  sub_eq_add_neg a b := by apply ext; intro S; exact sub_eq_add_neg _ _
  zsmul := zsmulRec
  add_comm a b := by apply ext; intro S; exact add_comm _ _

instance : CommRing (SqFreeAlg ι K) where
  one := ⟨fun S => if S = ∅ then 1 else 0⟩
  natCast n := ⟨fun S => if S = ∅ then (n : K) else 0⟩
  intCast z := ⟨fun S => if S = ∅ then (z : K) else 0⟩
  mul := mulSq
  left_distrib a b c := by
    apply ext; intro S
    change ∑ T ∈ S.powerset, a.coeff T * (b.coeff (S \ T) + c.coeff (S \ T)) =
      (∑ T ∈ S.powerset, a.coeff T * b.coeff (S \ T)) +
      (∑ T ∈ S.powerset, a.coeff T * c.coeff (S \ T))
    simp only [mul_add, Finset.sum_add_distrib]
  right_distrib a b c := by
    apply ext; intro S
    change ∑ T ∈ S.powerset, (a.coeff T + b.coeff T) * c.coeff (S \ T) =
      (∑ T ∈ S.powerset, a.coeff T * c.coeff (S \ T)) +
      (∑ T ∈ S.powerset, b.coeff T * c.coeff (S \ T))
    simp only [add_mul, Finset.sum_add_distrib]
  zero_mul a := by
    apply ext; intro S
    change ∑ T ∈ S.powerset, (0 : K) * a.coeff (S \ T) = 0
    simp
  mul_zero a := by
    apply ext; intro S
    change ∑ T ∈ S.powerset, a.coeff T * (0 : K) = 0
    simp
  mul_assoc := mulSq_assoc
  one_mul a := by
    apply ext; intro S
    change ∑ T ∈ S.powerset, (if T = ∅ then (1 : K) else 0) * a.coeff (S \ T) = a.coeff S
    rw [Finset.sum_eq_single ∅]
    · simp
    · intro T _ hT; simp [hT]
    · intro h; exact (h (Finset.empty_mem_powerset S)).elim
  mul_one a := by
    change mulSq a ⟨fun S => if S = ∅ then 1 else 0⟩ = a
    rw [mulSq_comm]
    apply ext; intro S
    change ∑ T ∈ S.powerset, (if T = ∅ then (1 : K) else 0) * a.coeff (S \ T) = a.coeff S
    rw [Finset.sum_eq_single ∅]
    · simp
    · intro T _ hT; simp [hT]
    · intro h; exact (h (Finset.empty_mem_powerset S)).elim
  natCast_zero := by
    apply ext; intro S
    change (if S = ∅ then ((0 : ℕ) : K) else 0) = 0
    simp
  natCast_succ n := by
    apply ext; intro S
    change (if S = ∅ then ((n + 1 : ℕ) : K) else 0) =
      (if S = ∅ then (n : K) else 0) + (if S = ∅ then (1 : K) else 0)
    by_cases hS : S = ∅ <;> simp [hS]
  intCast_ofNat n := by
    apply ext; intro S
    change (if S = ∅ then ((n : ℤ) : K) else 0) = if S = ∅ then (n : K) else 0
    by_cases hS : S = ∅ <;> simp [hS]
  intCast_negSucc n := by
    apply ext; intro S
    change (if S = ∅ then ((Int.negSucc n : ℤ) : K) else 0) =
      -(if S = ∅ then ((n + 1 : ℕ) : K) else 0)
    by_cases hS : S = ∅ <;> simp [hS, Int.negSucc_eq]
  mul_comm := mulSq_comm

@[simp] lemma zero_coeff (S : Finset ι) : (0 : SqFreeAlg ι K).coeff S = 0 := rfl
@[simp] lemma one_coeff (S : Finset ι) :
    (1 : SqFreeAlg ι K).coeff S = if S = ∅ then 1 else 0 := rfl
@[simp] lemma add_coeff (f g : SqFreeAlg ι K) (S : Finset ι) :
    (f + g).coeff S = f.coeff S + g.coeff S := rfl
@[simp] lemma neg_coeff (f : SqFreeAlg ι K) (S : Finset ι) :
    (-f).coeff S = - f.coeff S := rfl
@[simp] lemma sub_coeff (f g : SqFreeAlg ι K) (S : Finset ι) :
    (f - g).coeff S = f.coeff S - g.coeff S := rfl
@[simp] lemma natCast_coeff (n : ℕ) (S : Finset ι) :
    (n : SqFreeAlg ι K).coeff S = if S = ∅ then (n : K) else 0 := rfl
@[simp] lemma intCast_coeff (z : ℤ) (S : Finset ι) :
    (z : SqFreeAlg ι K).coeff S = if S = ∅ then (z : K) else 0 := rfl
lemma mul_coeff (f g : SqFreeAlg ι K) (S : Finset ι) :
    (f * g).coeff S = ∑ T ∈ S.powerset, f.coeff T * g.coeff (S \ T) := rfl

instance : SMul K (SqFreeAlg ι K) := ⟨fun c f => ⟨fun S => c * f.coeff S⟩⟩

omit [DecidableEq ι] in
@[simp] lemma smul_coeff (c : K) (f : SqFreeAlg ι K) (S : Finset ι) :
    (c • f).coeff S = c * f.coeff S := rfl

instance : Module K (SqFreeAlg ι K) where
  one_smul f := by apply ext; intro S; simp
  mul_smul c₁ c₂ f := by apply ext; intro S; simp [mul_assoc]
  smul_zero c := by apply ext; intro S; simp
  smul_add c f g := by apply ext; intro S; simp [mul_add]
  add_smul c₁ c₂ f := by apply ext; intro S; simp [add_mul]
  zero_smul f := by apply ext; intro S; simp

instance : Algebra K (SqFreeAlg ι K) :=
  Algebra.ofModule
    (fun c f g => by
      apply ext; intro S
      simp only [smul_coeff, mul_coeff, Finset.mul_sum]
      refine Finset.sum_congr rfl fun T _ => by ring)
    (fun c f g => by
      apply ext; intro S
      simp only [smul_coeff, mul_coeff, Finset.mul_sum]
      refine Finset.sum_congr rfl fun T _ => by ring)

@[simp] lemma algebraMap_coeff (c : K) (S : Finset ι) :
    (algebraMap K (SqFreeAlg ι K) c).coeff S = if S = ∅ then c else 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  by_cases hS : S = ∅ <;> simp [hS]

lemma charP_three [CharP K 3] : CharP (SqFreeAlg ι K) 3 := by
  constructor
  intro n
  rw [← CharP.cast_eq_zero_iff K 3 n]
  constructor
  · intro h
    have := congrArg (fun x : SqFreeAlg ι K => x.coeff ∅) h
    simpa using this
  · intro h
    apply ext; intro S
    by_cases hS : S = ∅ <;> simp [hS, h]

def sqFreeAlgEquiv : SqFreeAlg ι K ≃ₗ[K] (Finset ι → K) where
  toFun f := f.coeff
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun c := ⟨c⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype ι] : Module.Finite K (SqFreeAlg ι K) :=
  Module.Finite.equiv sqFreeAlgEquiv.symm

def X (i : ι) : SqFreeAlg ι K := ⟨fun S => if S = {i} then 1 else 0⟩

@[simp] lemma X_coeff (i : ι) (S : Finset ι) :
    (X (K := K) i).coeff S = if S = {i} then 1 else 0 := rfl

lemma X_mul_X (i : ι) : X (K := K) i * X i = 0 := by
  apply ext; intro S
  simp only [mul_coeff, X_coeff, zero_coeff]
  apply Finset.sum_eq_zero
  intro T hT
  by_cases h1 : T = {i}
  · subst h1
    have : S \ {i} ≠ {i} := by
      intro h2
      have hi : i ∈ S \ {i} := by rw [h2]; exact Finset.mem_singleton_self i
      exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_singleton_self i)
    simp [this]
  · simp [h1]

lemma X_sq (i : ι) : (X (K := K) i) ^ 2 = 0 := by
  rw [sq, X_mul_X]

def IsHomog (k : ℕ) (f : SqFreeAlg ι K) : Prop :=
  ∀ S : Finset ι, S.card ≠ k → f.coeff S = 0

lemma isHomog_zero (k : ℕ) : IsHomog k (0 : SqFreeAlg ι K) := fun _ _ => rfl

lemma isHomog_one : IsHomog 0 (1 : SqFreeAlg ι K) := by
  intro S hS
  have : S ≠ ∅ := fun h => hS (by simp [h])
  simp [this]

lemma isHomog_algebraMap (c : K) : IsHomog 0 (algebraMap K (SqFreeAlg ι K) c) := by
  intro S hS
  have : S ≠ ∅ := fun h => hS (by simp [h])
  simp [this]

lemma isHomog_X (i : ι) : IsHomog 1 (X (K := K) i) := by
  intro S hS
  have : S ≠ {i} := fun h => hS (by simp [h])
  simp [this]

lemma isHomog_add {k : ℕ} {f g : SqFreeAlg ι K} (hf : IsHomog k f) (hg : IsHomog k g) :
    IsHomog k (f + g) := fun S hS => by simp [hf S hS, hg S hS]

lemma isHomog_neg {k : ℕ} {f : SqFreeAlg ι K} (hf : IsHomog k f) :
    IsHomog k (-f) := fun S hS => by simp [hf S hS]

lemma isHomog_sub {k : ℕ} {f g : SqFreeAlg ι K} (hf : IsHomog k f) (hg : IsHomog k g) :
    IsHomog k (f - g) := fun S hS => by simp [hf S hS, hg S hS]

omit [DecidableEq ι] in
lemma isHomog_smul {k : ℕ} (c : K) {f : SqFreeAlg ι K} (hf : IsHomog k f) :
    IsHomog k (c • f) := fun S hS => by simp [hf S hS]

lemma isHomog_sum {α : Type*} {s : Finset α} {k : ℕ} {f : α → SqFreeAlg ι K}
    (hf : ∀ a ∈ s, IsHomog k (f a)) : IsHomog k (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isHomog_zero k
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isHomog_add (hf a (Finset.mem_insert_self a s))
      (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))

lemma isHomog_mul {k₁ k₂ : ℕ} {f g : SqFreeAlg ι K} (hf : IsHomog k₁ f) (hg : IsHomog k₂ g) :
    IsHomog (k₁ + k₂) (f * g) := by
  intro S hS
  simp only [mul_coeff]
  apply Finset.sum_eq_zero
  intro T hT
  rw [Finset.mem_powerset] at hT
  by_cases h1 : T.card = k₁
  · have h2 : (S \ T).card ≠ k₂ := by
      have hsum := Finset.card_sdiff_add_card_eq_card hT
      omega
    simp [hg (S \ T) h2]
  · simp [hf T h1]

lemma isHomog_prod_sq {n : ℕ} {b : Fin n → SqFreeAlg ι K} (hb : ∀ j, IsHomog 1 (b j)) :
    IsHomog (2 * n) (∏ j : Fin n, (b j) ^ 2) := by
  induction n with
  | zero => simpa using isHomog_one
  | succ n ih =>
    rw [Fin.prod_univ_castSucc]
    have h1 : IsHomog (2 * n) (∏ j : Fin n, (b (Fin.castSucc j)) ^ 2) :=
      ih (fun j => hb (Fin.castSucc j))
    have h2 : IsHomog 2 ((b (Fin.last n)) ^ 2) := by
      rw [sq]
      exact isHomog_mul (hb (Fin.last n)) (hb (Fin.last n))
    have hmul := isHomog_mul h1 h2
    rwa [show 2 * n + 2 = 2 * (n + 1) by omega] at hmul

lemma isHomog_zero_eq_algebraMap {f : SqFreeAlg ι K} (hf : IsHomog 0 f) :
    f = algebraMap K (SqFreeAlg ι K) (f.coeff ∅) := by
  apply ext; intro S
  by_cases hS : S = ∅
  · simp [hS]
  · have hc : S.card ≠ 0 := by rwa [ne_eq, Finset.card_eq_zero]
    simp [hS, hf S hc]

lemma isHomog_one_eq_sum_X [Fintype ι] {u : SqFreeAlg ι K} (hu : IsHomog 1 u) :
    u = ∑ i : ι, u.coeff {i} • X i := by
  apply ext; intro S
  have hsum : ∀ (s : Finset ι), (∑ i ∈ s, u.coeff {i} • X (K := K) i).coeff S =
      ∑ i ∈ s, (if S = {i} then u.coeff {i} else 0) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, add_coeff, Finset.sum_insert ha, ih]
      simp [smul_coeff, X_coeff]
  rw [hsum]
  by_cases h1 : S.card = 1
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h1
    subst hi
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      have : ({i} : Finset ι) ≠ {j} := by
        intro h
        exact hj (Finset.singleton_injective h).symm
      simp [this]
    · intro hi; exact (hi (Finset.mem_univ i)).elim
  · rw [hu S h1, eq_comm]
    apply Finset.sum_eq_zero
    intro i _
    have : S ≠ {i} := fun h => h1 (by simp [h])
    simp [this]

lemma linear_cube_eq_zero [Fintype ι] [CharP K 3] {u : SqFreeAlg ι K} (hu : IsHomog 1 u) :
    u ^ 3 = 0 := by
  have : CharP (SqFreeAlg ι K) 3 := charP_three
  have hpow : ∀ s : Finset ι, (∑ i ∈ s, u.coeff {i} • X (K := K) i) ^ 3 = 0 := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      set A := u.coeff {a} • X (K := K) a
      set B := ∑ i ∈ s, u.coeff {i} • X (K := K) i
      have hA2 : A ^ 2 = 0 := by
        dsimp [A]
        rw [smul_pow, X_sq, smul_zero]
      have hA3 : A ^ 3 = 0 := by
        calc A ^ 3 = A ^ 2 * A := by ring
        _ = 0 := by rw [hA2, zero_mul]
      have h3 : (3 : SqFreeAlg ι K) = 0 := CharP.cast_eq_zero_iff (SqFreeAlg ι K) 3 3 |>.mpr dvd_rfl
      calc (A + B) ^ 3
          = A ^ 3 + 3 * (A ^ 2 * B + A * B ^ 2) + B ^ 3 := by ring
        _ = 0 + 0 * (A ^ 2 * B + A * B ^ 2) + 0 := by rw [hA3, ih, h3]
        _ = 0 := by ring
  rw [isHomog_one_eq_sum_X hu]
  exact hpow Finset.univ

def homogPart (k : ℕ) (f : SqFreeAlg ι K) : SqFreeAlg ι K :=
  ⟨fun S => if S.card = k then f.coeff S else 0⟩

omit [DecidableEq ι] in
@[simp] lemma homogPart_coeff (k : ℕ) (f : SqFreeAlg ι K) (S : Finset ι) :
    (homogPart k f).coeff S = if S.card = k then f.coeff S else 0 := rfl

omit [DecidableEq ι] in
lemma isHomog_homogPart (k : ℕ) (f : SqFreeAlg ι K) : IsHomog k (homogPart k f) := by
  intro S hS; simp [hS]

omit [DecidableEq ι] in
lemma homogPart_of_isHomog {k : ℕ} {f : SqFreeAlg ι K} (hf : IsHomog k f) :
    homogPart k f = f := by
  apply ext; intro S
  by_cases hS : S.card = k
  · simp [hS]
  · simp [hS, hf S hS]

lemma homogPart_add (k : ℕ) (f g : SqFreeAlg ι K) :
    homogPart k (f + g) = homogPart k f + homogPart k g := by
  apply ext; intro S
  by_cases hS : S.card = k <;> simp [hS]

lemma homogPart_sum {α : Type*} (s : Finset α) (k : ℕ) (f : α → SqFreeAlg ι K) :
    homogPart k (∑ a ∈ s, f a) = ∑ a ∈ s, homogPart k (f a) := by
  classical
  induction s using Finset.induction with
  | empty => apply ext; intro S; simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, homogPart_add, ih, Finset.sum_insert ha]

lemma homogPart_mul_linear_zero (a u : SqFreeAlg ι K) (hu : IsHomog 1 u) :
    homogPart 0 (a * u) = 0 := by
  apply ext; intro S
  by_cases hS : S.card = 0
  · simp only [homogPart_coeff, hS, ↓reduceIte, mul_coeff, zero_coeff]
    apply Finset.sum_eq_zero
    intro T hT
    rw [Finset.mem_powerset] at hT
    have hST : (S \ T).card = 0 := by
      have := Finset.card_le_card (Finset.sdiff_subset (s := S) (t := T))
      omega
    have hne : (S \ T).card ≠ 1 := by omega
    simp [hu (S \ T) hne]
  · simp [hS]

lemma homogPart_mul_linear_succ (k : ℕ) (a u : SqFreeAlg ι K) (hu : IsHomog 1 u) :
    homogPart (k + 1) (a * u) = homogPart k a * u := by
  apply ext; intro S
  by_cases hS : S.card = k + 1
  · simp only [homogPart_coeff, hS, ↓reduceIte, mul_coeff]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [Finset.mem_powerset] at hT
    by_cases hST : (S \ T).card = 1
    · have hTc : T.card = k := by
        have hsum := Finset.card_sdiff_add_card_eq_card hT
        omega
      simp [hTc]
    · simp [hu (S \ T) hST]
  · simp only [homogPart_coeff, hS, ↓reduceIte]
    have hm : IsHomog (k + 1) (homogPart k a * u) :=
      isHomog_mul (isHomog_homogPart k a) hu
    exact (hm S hS).symm

def elim (i : ι) : SqFreeAlg ι K →ₗ[K] SqFreeAlg ι K where
  toFun f := ⟨fun S => if i ∈ S then 0 else f.coeff S⟩
  map_add' f g := by apply ext; intro S; by_cases hi : i ∈ S <;> simp [hi]
  map_smul' c f := by apply ext; intro S; by_cases hi : i ∈ S <;> simp [hi]

def deriv (i : ι) : SqFreeAlg ι K →ₗ[K] SqFreeAlg ι K where
  toFun f := ⟨fun S => if i ∈ S then 0 else f.coeff (insert i S)⟩
  map_add' f g := by apply ext; intro S; by_cases hi : i ∈ S <;> simp [hi]
  map_smul' c f := by apply ext; intro S; by_cases hi : i ∈ S <;> simp [hi]

@[simp] lemma elim_coeff (i : ι) (f : SqFreeAlg ι K) (S : Finset ι) :
    (elim i f).coeff S = if i ∈ S then 0 else f.coeff S := rfl

@[simp] lemma deriv_coeff (i : ι) (f : SqFreeAlg ι K) (S : Finset ι) :
    (deriv i f).coeff S = if i ∈ S then 0 else f.coeff (insert i S) := rfl

lemma elim_one (i : ι) : elim i (1 : SqFreeAlg ι K) = 1 := by
  apply ext; intro S
  by_cases hi : i ∈ S
  · have hne : S ≠ ∅ := fun h => by simp [h] at hi
    simp [hi, hne]
  · simp [hi]

lemma elim_algebraMap (i : ι) (c : K) :
    elim i (algebraMap K (SqFreeAlg ι K) c) = algebraMap K (SqFreeAlg ι K) c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, elim_one]

lemma elim_mul (i : ι) (f g : SqFreeAlg ι K) :
    elim i (f * g) = elim i f * elim i g := by
  apply ext; intro S
  by_cases hi : i ∈ S
  · simp only [elim_coeff, hi, ↓reduceIte, mul_coeff]
    symm
    apply Finset.sum_eq_zero
    intro T hT
    rw [Finset.mem_powerset] at hT
    by_cases hiT : i ∈ T
    · simp [hiT]
    · have hiST : i ∈ S \ T := Finset.mem_sdiff.mpr ⟨hi, hiT⟩
      simp [hiST]
  · simp only [elim_coeff, hi, ↓reduceIte, mul_coeff]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [Finset.mem_powerset] at hT
    have hiT : i ∉ T := fun h => hi (hT h)
    have hiST : i ∉ S \ T := fun h => hi ((Finset.mem_sdiff.mp h).1)
    simp [hiT, hiST]

lemma elim_prod {α : Type*} (i : ι) (s : Finset α) (f : α → SqFreeAlg ι K) :
    elim i (∏ a ∈ s, f a) = ∏ a ∈ s, elim i (f a) := by
  classical
  induction s using Finset.induction with
  | empty => simp [elim_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, elim_mul, ih, Finset.prod_insert ha]

lemma deriv_mul (i : ι) (f g : SqFreeAlg ι K) :
    deriv i (f * g) = deriv i f * elim i g + elim i f * deriv i g := by
  apply ext; intro S
  by_cases hi : i ∈ S
  · simp only [deriv_coeff, hi, ↓reduceIte, add_coeff, mul_coeff, elim_coeff]
    symm
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    · intro T hT
      rw [Finset.mem_powerset] at hT
      by_cases hiT : i ∈ T
      · simp [hiT]
      · simp [Finset.mem_sdiff.mpr ⟨hi, hiT⟩]
    · intro T hT
      rw [Finset.mem_powerset] at hT
      by_cases hiT : i ∈ T
      · simp [hiT]
      · simp [Finset.mem_sdiff.mpr ⟨hi, hiT⟩]
  · simp only [deriv_coeff, hi, ↓reduceIte, add_coeff, mul_coeff, elim_coeff]
    rw [Finset.powerset_insert, Finset.sum_union]
    · have h1 : ∑ T ∈ S.powerset, f.coeff T * g.coeff (insert i S \ T) =
          ∑ T ∈ S.powerset, (if i ∈ T then 0 else f.coeff T) *
            (if i ∈ S \ T then 0 else g.coeff (insert i (S \ T))) := by
        refine Finset.sum_congr rfl fun T hT => ?_
        rw [Finset.mem_powerset] at hT
        have hiT : i ∉ T := fun h => hi (hT h)
        have hiST : i ∉ S \ T := fun h => hi ((Finset.mem_sdiff.mp h).1)
        rw [if_neg hiT, if_neg hiST, Finset.insert_sdiff_of_notMem _ hiT]
      have h2 : ∑ T ∈ S.powerset.image (insert i), f.coeff T * g.coeff (insert i S \ T) =
          ∑ T ∈ S.powerset, (if i ∈ T then 0 else f.coeff (insert i T)) *
            (if i ∈ S \ T then 0 else g.coeff (S \ T)) := by
        rw [Finset.sum_image]
        · refine Finset.sum_congr rfl fun T hT => ?_
          rw [Finset.mem_powerset] at hT
          have hiT : i ∉ T := fun h => hi (hT h)
          have hiST : i ∉ S \ T := fun h => hi ((Finset.mem_sdiff.mp h).1)
          rw [if_neg hiT, if_neg hiST]
          congr 2
          ext x
          by_cases hx : x = i
          · subst hx; simp [hi, hiT]
          · simp [hx]
        · intro T₁ hT₁ T₂ hT₂ heq
          rw [Finset.mem_coe, Finset.mem_powerset] at hT₁ hT₂
          have hi1 : i ∉ T₁ := fun h => hi (hT₁ h)
          have hi2 : i ∉ T₂ := fun h => hi (hT₂ h)
          have := congrArg (fun X => Finset.erase X i) heq
          simpa [Finset.erase_insert hi1, Finset.erase_insert hi2] using this
      rw [h1, h2, add_comm]
    · rw [Finset.disjoint_left]
      intro T hT1 hT2
      rw [Finset.mem_powerset] at hT1
      rw [Finset.mem_image] at hT2
      rcases hT2 with ⟨T', _, rfl⟩
      exact hi (hT1 (Finset.mem_insert_self i T'))

lemma decomp (i : ι) (f : SqFreeAlg ι K) :
    f = elim i f + deriv i f * X i := by
  apply ext; intro S
  simp only [add_coeff, elim_coeff, mul_coeff, deriv_coeff, X_coeff]
  by_cases hi : i ∈ S
  · rw [if_pos hi, zero_add]
    rw [Finset.sum_eq_single (S.erase i)]
    · have hiE : i ∉ S.erase i := Finset.notMem_erase i S
      have hsd : S \ S.erase i = {i} := by
        ext x
        by_cases hx : x = i
        · subst hx; simp [hi]
        · simp [hx]
      rw [if_neg hiE, hsd, if_pos rfl, mul_one, Finset.insert_erase hi]
    · intro T hT hne
      rw [Finset.mem_powerset] at hT
      have hne2 : S \ T ≠ {i} := by
        intro heq
        apply hne
        calc T = S \ (S \ T) := (Finset.sdiff_sdiff_eq_self hT).symm
        _ = S \ {i} := by rw [heq]
        _ = S.erase i := Finset.sdiff_singleton_eq_erase i S
      rw [if_neg hne2, mul_zero]
    · intro h
      exact (h (Finset.mem_powerset.mpr (Finset.erase_subset i S))).elim
  · rw [if_neg hi, eq_comm, add_eq_left]
    apply Finset.sum_eq_zero
    intro T _
    have hne : S \ T ≠ {i} := by
      intro heq
      have : i ∈ S \ T := heq ▸ Finset.mem_singleton_self i
      exact hi (Finset.mem_sdiff.mp this).1
    rw [if_neg hne, mul_zero]

lemma elim_X_self (i : ι) : elim i (X (K := K) i) = 0 := by
  apply ext; intro S
  by_cases hS : S = {i}
  · subst hS; simp
  · simp [hS]

lemma deriv_X_self (i : ι) : deriv i (X (K := K) i) = 1 := by
  apply ext; intro S
  by_cases hi : i ∈ S
  · have hne : S ≠ ∅ := fun h => by simp [h] at hi
    simp [hi, hne]
  · by_cases hS : S = ∅
    · subst hS; simp
    · have hne : insert i S ≠ {i} := by
        intro heq
        obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hS
        have : x ∈ ({i} : Finset ι) := heq ▸ Finset.mem_insert_of_mem hx
        rw [Finset.mem_singleton] at this
        subst this
        exact hi hx
      simp [hi, hS, hne]

lemma deriv_elim_self (i : ι) (f : SqFreeAlg ι K) : deriv i (elim i f) = 0 := by
  apply ext; intro S
  by_cases hi : i ∈ S <;> simp [hi]

lemma deriv_deriv_self (i : ι) (f : SqFreeAlg ι K) : deriv i (deriv i f) = 0 := by
  apply ext; intro S
  by_cases hi : i ∈ S <;> simp [hi]

lemma elim_deriv_self (i : ι) (f : SqFreeAlg ι K) : elim i (deriv i f) = deriv i f := by
  apply ext; intro S
  by_cases hi : i ∈ S <;> simp [hi]

lemma elim_elim (i : ι) (f : SqFreeAlg ι K) : elim i (elim i f) = elim i f := by
  apply ext; intro S
  by_cases hi : i ∈ S <;> simp [hi]

lemma deriv_one (i : ι) : deriv i (1 : SqFreeAlg ι K) = 0 := by
  apply ext; intro S
  by_cases hi : i ∈ S <;> simp [hi]

lemma deriv_algebraMap (i : ι) (c : K) :
    deriv i (algebraMap K (SqFreeAlg ι K) c) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, deriv_one, smul_zero]

lemma isHomog_elim {k : ℕ} (i : ι) {f : SqFreeAlg ι K} (hf : IsHomog k f) :
    IsHomog k (elim i f) := by
  intro S hS
  by_cases hi : i ∈ S <;> simp [hi, hf S hS]

lemma isHomog_deriv {k : ℕ} (i : ι) {f : SqFreeAlg ι K} (hf : IsHomog (k + 1) f) :
    IsHomog k (deriv i f) := by
  intro S hS
  by_cases hi : i ∈ S
  · simp [hi]
  · simp only [deriv_coeff, hi, ↓reduceIte]
    apply hf
    rw [Finset.card_insert_of_notMem hi]
    omega

lemma deriv_isHomog_zero (i : ι) {f : SqFreeAlg ι K} (hf : IsHomog 0 f) :
    deriv i f = 0 := by
  rw [isHomog_zero_eq_algebraMap hf, deriv_algebraMap]

lemma deriv_isHomog_one (i : ι) {u : SqFreeAlg ι K} (hu : IsHomog 1 u) :
    deriv i u = algebraMap K (SqFreeAlg ι K) (u.coeff {i}) := by
  have hd : IsHomog 0 (deriv i u) := isHomog_deriv i hu
  rw [isHomog_zero_eq_algebraMap hd]
  simp

lemma decomp_linear (i : ι) {u : SqFreeAlg ι K} (hu : IsHomog 1 u) :
    u = elim i u + u.coeff {i} • X i := by
  conv_lhs => rw [decomp i u]
  rw [deriv_isHomog_one i hu, ← Algebra.smul_def]

lemma deriv_sq_of_deriv_zero (i : ι) {u : SqFreeAlg ι K} (hdu : deriv i u = 0) :
    deriv i (u ^ 2) = 0 := by
  rw [sq, deriv_mul, hdu, zero_mul, mul_zero, add_zero]

lemma deriv_sq_add_X (i : ι) {u : SqFreeAlg ι K} (hdu : deriv i u = 0) :
    deriv i ((u + X i) ^ 2) = (2 : K) • u := by
  have heu : elim i u = u := by
    have := decomp i u
    rw [hdu, zero_mul, add_zero] at this
    exact this.symm
  have h1 : (u + X i) ^ 2 = u ^ 2 + (2 : K) • (u * X i) := by
    have hx : (X (K := K) i) ^ 2 = 0 := X_sq i
    calc (u + X i) ^ 2 = u ^ 2 + (2 : ℕ) • (u * X i) + (X i) ^ 2 := by ring
    _ = u ^ 2 + (2 : K) • (u * X i) := by
      rw [hx, add_zero, ← Nat.cast_smul_eq_nsmul K 2]
      norm_num
  rw [h1, map_add, map_smul, deriv_sq_of_deriv_zero i hdu, zero_add, deriv_mul,
    hdu, zero_mul, zero_add, deriv_X_self, mul_one, heu]

lemma elim_sq_add_X (i : ι) {u : SqFreeAlg ι K} (hdu : deriv i u = 0) :
    elim i ((u + X i) ^ 2) = u ^ 2 := by
  have heu : elim i u = u := by
    have := decomp i u
    rw [hdu, zero_mul, add_zero] at this
    exact this.symm
  rw [sq, elim_mul, map_add, heu, elim_X_self, add_zero, sq]

lemma sq_eq_add_mul_sub (u v : SqFreeAlg ι K) (hv : v ^ 2 = 0) :
    u ^ 2 = (u + v) * (u - v) := by
  calc u ^ 2 = u ^ 2 - v ^ 2 := by rw [hv, sub_zero]
  _ = (u + v) * (u - v) := by ring

lemma prod_pow_three_eq_zero_of_count_ge_three [Fintype ι] [CharP K 3] {n m : ℕ}
    {b : Fin n → SqFreeAlg ι K} (hb : ∀ j, IsHomog 1 (b j))
    (g : Fin m → Fin n) (j₀ : Fin n)
    (hj : 3 ≤ (Finset.univ.filter (fun k => g k = j₀)).card) :
    ∏ k : Fin m, b (g k) = 0 := by
  classical
  set s := Finset.univ.filter (fun k : Fin m => g k = j₀)
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hj
  have hsplit : ∏ k : Fin m, b (g k) =
      (∏ k ∈ t, b (g k)) * (∏ k ∈ Finset.univ \ t, b (g k)) := by
    rw [← Finset.prod_sdiff (Finset.subset_univ t)]
    ring
  have htprod : ∏ k ∈ t, b (g k) = (b j₀) ^ 3 := by
    calc ∏ k ∈ t, b (g k) = ∏ _k ∈ t, b j₀ := by
          refine Finset.prod_congr rfl fun k hk => ?_
          have := (Finset.mem_filter.mp (hts hk)).2
          rw [this]
    _ = (b j₀) ^ t.card := Finset.prod_const _
    _ = (b j₀) ^ 3 := by rw [htc]
  rw [hsplit, htprod, linear_cube_eq_zero (hb j₀), zero_mul]

lemma prod_2n_mem_span_prodSq [Fintype ι] [CharP K 3] {n : ℕ} {b : Fin n → SqFreeAlg ι K}
    (hb : ∀ j, IsHomog 1 (b j)) (v : Fin (2 * n) → SqFreeAlg ι K)
    (hv : ∀ k, v k ∈ Submodule.span K (Set.range b)) :
    ∃ c : K, ∏ k : Fin (2 * n), v k = c • ∏ j : Fin n, (b j) ^ 2 := by
  classical
  have hrep : ∀ k : Fin (2 * n), ∃ A : Fin n → K, v k = ∑ j : Fin n, A j • b j := by
    intro k
    have hk := hv k
    rw [Submodule.mem_span_range_iff_exists_fun] at hk
    rcases hk with ⟨A, hA⟩
    exact ⟨A, hA.symm⟩
  choose A hA using hrep
  have hexp : ∏ k : Fin (2 * n), v k =
      ∑ g : Fin (2 * n) → Fin n, (∏ k : Fin (2 * n), A k (g k)) • ∏ k : Fin (2 * n), b (g k) := by
    conv_lhs =>
      arg 2; ext k; rw [hA k]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp_rw [Algebra.smul_def]
    rw [Finset.prod_mul_distrib, map_prod]
  have hterm : ∀ g : Fin (2 * n) → Fin n,
      ∃ c : K, ∏ k : Fin (2 * n), b (g k) = c • ∏ j : Fin n, (b j) ^ 2 := by
    intro g
    by_cases hle : ∀ j : Fin n, (Finset.univ.filter (fun k : Fin (2 * n) => g k = j)).card ≤ 2
    · have hsum : ∑ j : Fin n, (Finset.univ.filter (fun k : Fin (2 * n) => g k = j)).card = 2 * n := by
        have := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin (2 * n)))
          (Finset.univ : Finset (Fin n)) g
        simpa using this
      have heq2 : ∀ j : Fin n, (Finset.univ.filter (fun k : Fin (2 * n) => g k = j)).card = 2 := by
        by_contra hnot
        push Not at hnot
        rcases hnot with ⟨j₀, hj₀⟩
        have hlt : (Finset.univ.filter (fun k : Fin (2 * n) => g k = j₀)).card < 2 :=
          lt_of_le_of_ne (hle j₀) hj₀
        have hlt_sum : ∑ j : Fin n, (Finset.univ.filter (fun k : Fin (2 * n) => g k = j)).card <
            ∑ _j : Fin n, 2 :=
          Finset.sum_lt_sum (fun j _ => hle j) ⟨j₀, Finset.mem_univ j₀, hlt⟩
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm n 2] at hlt_sum
        omega
      refine ⟨1, ?_⟩
      rw [one_smul]
      calc ∏ k : Fin (2 * n), b (g k)
          = ∏ j : Fin n, ∏ k ∈ Finset.univ.filter (fun k : Fin (2 * n) => g k = j), b (g k) := by
            symm
            exact Finset.prod_fiberwise Finset.univ g (fun k => b (g k))
        _ = ∏ j : Fin n, (b j) ^ 2 := by
            refine Finset.prod_congr rfl fun j _ => ?_
            calc ∏ k ∈ Finset.univ.filter (fun k => g k = j), b (g k)
                = ∏ _k ∈ Finset.univ.filter (fun k => g k = j), b j :=
                  Finset.prod_congr rfl fun k hk => by rw [(Finset.mem_filter.mp hk).2]
              _ = (b j) ^ (Finset.univ.filter (fun k => g k = j)).card := Finset.prod_const _
              _ = (b j) ^ 2 := by rw [heq2 j]
    · push Not at hle
      rcases hle with ⟨j₀, hj₀⟩
      refine ⟨0, ?_⟩
      rw [zero_smul]
      exact prod_pow_three_eq_zero_of_count_ge_three hb g j₀ hj₀
  choose cg hcg using hterm
  refine ⟨∑ g : Fin (2 * n) → Fin n, (∏ k : Fin (2 * n), A k (g k)) * cg g, ?_⟩
  rw [hexp, Finset.sum_smul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [hcg g, smul_smul]

lemma prodSq_mem_span_prodSq [Fintype ι] [CharP K 3] {n : ℕ} {b b' : Fin n → SqFreeAlg ι K}
    (hb : ∀ j, IsHomog 1 (b j))
    (hb' : ∀ i, b' i ∈ Submodule.span K (Set.range b)) :
    ∃ c : K, ∏ i : Fin n, (b' i) ^ 2 = c • ∏ j : Fin n, (b j) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, by simp⟩
  let v : Fin (2 * n) → SqFreeAlg ι K := fun k => b' ⟨k.1 % n, Nat.mod_lt _ hn⟩
  have hprod : ∏ i : Fin n, (b' i) ^ 2 = ∏ k : Fin (2 * n), v k := by
    have heq : 2 * n = n + n := two_mul n
    let e : Fin (n + n) ≃ Fin (2 * n) := (Fin.castOrderIso heq.symm).toEquiv
    rw [← Fintype.prod_equiv e (fun x => v (e x)) v (fun _ => rfl)]
    rw [Fin.prod_univ_add]
    have h1 : ∏ k : Fin n, v (e (Fin.castAdd n k)) = ∏ i : Fin n, b' i := by
      refine Finset.prod_congr rfl fun k _ => ?_
      dsimp [v, e]
      congr 1; ext; simp [Nat.mod_eq_of_lt k.2]
    have h2 : ∏ k : Fin n, v (e (Fin.natAdd n k)) = ∏ i : Fin n, b' i := by
      refine Finset.prod_congr rfl fun k _ => ?_
      dsimp [v, e]
      congr 1; ext; simp [Nat.mod_eq_of_lt k.2]
    rw [h1, h2, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => sq (b' i)
  rw [hprod]
  exact prod_2n_mem_span_prodSq hb v (fun k => hb' _)

end RingOps

section FieldOps

variable {ι K : Type*} [DecidableEq ι] [Field K]

def rem (u : SqFreeAlg ι K) (i : ι) (f : SqFreeAlg ι K) : SqFreeAlg ι K :=
  elim i f - (u.coeff {i})⁻¹ • (deriv i f * elim i u)

lemma deriv_rem (i : ι) {u : SqFreeAlg ι K}
    (f : SqFreeAlg ι K) : deriv i (rem u i f) = 0 := by
  dsimp [rem]
  rw [map_sub, map_smul, deriv_elim_self, zero_sub, deriv_mul,
    deriv_elim_self, mul_zero, add_zero,
    deriv_deriv_self, zero_mul, smul_zero, neg_zero]

lemma sub_rem (i : ι) {u : SqFreeAlg ι K} (hu : IsHomog 1 u) (huc : u.coeff {i} ≠ 0)
    (f : SqFreeAlg ι K) :
    f - rem u i f = (u.coeff {i})⁻¹ • (deriv i f * u) := by
  dsimp [rem]
  have heq : f - (elim i f - (u.coeff {i})⁻¹ • (deriv i f * elim i u)) =
      (f - elim i f) + (u.coeff {i})⁻¹ • (deriv i f * elim i u) := by ring
  rw [heq]
  have h1 : f - elim i f = deriv i f * X i := by
    conv_lhs => lhs; rw [decomp i f]
    rw [add_sub_cancel_left]
  have h2 : u = elim i u + u.coeff {i} • X i := decomp_linear i hu
  rw [h1]
  conv_rhs =>
    rhs; rw [h2, mul_add]
  rw [smul_add, Algebra.mul_smul_comm, smul_smul, inv_mul_cancel₀ huc, one_smul, add_comm]

lemma isHomog_rem {k : ℕ} (i : ι) {u : SqFreeAlg ι K} (hu : IsHomog 1 u)
    (f : SqFreeAlg ι K) (hf : IsHomog k f) : IsHomog k (rem u i f) := by
  dsimp [rem]
  refine isHomog_sub (isHomog_elim i hf) (isHomog_smul _ ?_)
  cases k with
  | zero =>
    rw [deriv_isHomog_zero i hf, zero_mul]
    exact isHomog_zero 0
  | succ k =>
    simpa [add_comm] using isHomog_mul (isHomog_deriv i hf) (isHomog_elim i hu)

end FieldOps

section OptionLift

variable {ι K : Type*} [DecidableEq ι] [CommRing K]

noncomputable def optPre (S : Finset (Option ι)) : Finset ι :=
  S.preimage some (fun _ _ _ _ h => Option.some.inj h)

@[simp] lemma mem_optPre {S : Finset (Option ι)} {a : ι} :
    a ∈ optPre S ↔ some a ∈ S := Finset.mem_preimage

noncomputable def liftOpt : SqFreeAlg ι K →ₐ[K] SqFreeAlg (Option ι) K where
  toFun f := ⟨fun S => if none ∈ S then 0 else f.coeff (optPre S)⟩
  map_one' := by
    apply ext; intro S
    by_cases hn : none ∈ S
    · have hne : S ≠ ∅ := fun h => by simp [h] at hn
      simp [hn, hne]
    · have hemp : optPre S = ∅ ↔ S = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem, Finset.eq_empty_iff_forall_notMem]
        constructor
        · intro h x hx
          cases x with
          | none => exact hn hx
          | some a => exact h a (mem_optPre.mpr hx)
        · intro h a ha
          exact h (some a) (mem_optPre.mp ha)
      by_cases hS : S = ∅
      · subst hS
        have hemp0 : optPre (∅ : Finset (Option ι)) = ∅ := hemp.mpr rfl
        simp [hn, hemp0]
      · simp [hn, hS, (not_iff_not.mpr hemp).mpr hS]
  map_mul' f g := by
    apply ext; intro S
    by_cases hn : none ∈ S
    · simp only [mul_coeff, hn, ↓reduceIte]
      symm
      apply Finset.sum_eq_zero
      intro T hT
      rw [Finset.mem_powerset] at hT
      by_cases hnT : none ∈ T
      · simp [hnT]
      · have hnST : none ∈ S \ T := Finset.mem_sdiff.mpr ⟨hn, hnT⟩
        simp [hnST]
    · simp only [mul_coeff, hn, ↓reduceIte]
      have hmap : S = (optPre S).map ⟨some, Option.some_injective ι⟩ := by
        ext x
        cases x with
        | none => simp [hn]
        | some a => simp
      symm
      rw [Finset.sum_bij (fun T _ => optPre T)]
      · intro T hT
        rw [Finset.mem_powerset] at hT ⊢
        intro a ha
        exact mem_optPre.mpr (hT (mem_optPre.mp ha))
      · intro T₁ hT₁ T₂ hT₂ heq
        rw [Finset.mem_powerset] at hT₁ hT₂
        ext x
        cases x with
        | none =>
          have h1 : none ∉ T₁ := fun h => hn (hT₁ h)
          have h2 : none ∉ T₂ := fun h => hn (hT₂ h)
          simp [h1, h2]
        | some a =>
          have := Finset.ext_iff.mp heq a
          simpa using this
      · intro T' hT'
        rw [Finset.mem_powerset] at hT'
        refine ⟨T'.map ⟨some, Option.some_injective ι⟩, ?_, ?_⟩
        · rw [Finset.mem_powerset, hmap]
          exact Finset.map_subset_map.mpr hT'
        · ext a; simp
      · intro T hT
        rw [Finset.mem_powerset] at hT
        have hnT : none ∉ T := fun h => hn (hT h)
        have hnST : none ∉ S \ T := fun h => hn ((Finset.mem_sdiff.mp h).1)
        rw [if_neg hnT, if_neg hnST]
        congr 2
        ext a; simp
  map_zero' := by apply ext; intro S; by_cases hn : none ∈ S <;> simp [hn]
  map_add' f g := by apply ext; intro S; by_cases hn : none ∈ S <;> simp [hn]
  commutes' c := by
    apply ext; intro S
    by_cases hn : none ∈ S
    · have hne : S ≠ ∅ := fun h => by simp [h] at hn
      simp [hn, hne]
    · have hemp : optPre S = ∅ ↔ S = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem, Finset.eq_empty_iff_forall_notMem]
        constructor
        · intro h x hx
          cases x with
          | none => exact hn hx
          | some a => exact h a (mem_optPre.mpr hx)
        · intro h a ha
          exact h (some a) (mem_optPre.mp ha)
      by_cases hS : S = ∅
      · subst hS
        have hemp0 : optPre (∅ : Finset (Option ι)) = ∅ := hemp.mpr rfl
        simp [hn, hemp0]
      · simp [hn, hS, (not_iff_not.mpr hemp).mpr hS]

noncomputable def projOpt : SqFreeAlg (Option ι) K →ₐ[K] SqFreeAlg ι K where
  toFun f := ⟨fun S => f.coeff (S.map ⟨some, Option.some_injective ι⟩)⟩
  map_one' := by
    apply ext; intro S
    by_cases hS : S = ∅ <;> simp [hS]
  map_mul' f g := by
    apply ext; intro S
    simp only [mul_coeff]
    symm
    rw [Finset.sum_bij (fun T _ => T.map ⟨some, Option.some_injective ι⟩)]
    · intro T hT
      rw [Finset.mem_powerset] at hT ⊢
      exact Finset.map_subset_map.mpr hT
    · intro T₁ _ T₂ _ heq
      ext a
      have := Finset.ext_iff.mp heq (some a)
      simpa using this
    · intro U hU
      rw [Finset.mem_powerset] at hU
      refine ⟨optPre U, ?_, ?_⟩
      · rw [Finset.mem_powerset]
        intro a ha
        have := hU (mem_optPre.mp ha)
        simpa using this
      · ext x
        cases x with
        | none =>
          simp only [Finset.mem_map, Function.Embedding.coeFn_mk, reduceCtorEq, and_false,
            exists_false, false_iff]
          intro h
          have := hU h
          simp at this
        | some a => simp
    · intro T _
      congr 2
      ext x
      cases x with
      | none => simp
      | some a => simp
  map_zero' := by apply ext; intro S; rfl
  map_add' f g := by apply ext; intro S; rfl
  commutes' c := by
    apply ext; intro S
    by_cases hS : S = ∅ <;> simp [hS]

@[simp] lemma projOpt_liftOpt (f : SqFreeAlg ι K) : projOpt (liftOpt f) = f := by
  apply ext; intro S
  dsimp [projOpt, liftOpt]
  have hnot : none ∉ S.map ⟨some, Option.some_injective ι⟩ := by simp
  rw [if_neg hnot]
  congr 1; ext a; simp

@[simp] lemma projOpt_X_none : projOpt (X (K := K) (none : Option ι)) = 0 := by
  apply ext; intro S
  dsimp [projOpt, X]
  have hne : S.map ⟨some, Option.some_injective ι⟩ ≠ {none} := by
    intro h
    have : (none : Option ι) ∈ S.map ⟨some, Option.some_injective ι⟩ :=
      h ▸ Finset.mem_singleton_self _
    simp at this
  simp [hne]

lemma isHomog_liftOpt {k : ℕ} {f : SqFreeAlg ι K} (hf : IsHomog k f) :
    IsHomog k (liftOpt f) := by
  intro S hS
  dsimp [liftOpt]
  by_cases hn : none ∈ S
  · simp [hn]
  · rw [if_neg hn]
    apply hf
    have hcard : (optPre S).card = S.card := by
      symm
      rw [← Finset.card_map ⟨some, Option.some_injective ι⟩]
      congr 1
      ext x
      cases x with
      | none => simp [hn]
      | some a => simp
    rwa [hcard]

lemma deriv_none_liftOpt (f : SqFreeAlg ι K) : deriv (none : Option ι) (liftOpt f) = 0 := by
  apply ext; intro S
  by_cases hn : none ∈ S
  · simp [hn]
  · simp [hn, liftOpt]

lemma liftOpt_X (i : ι) : liftOpt (X (K := K) i) = X (some i) := by
  apply ext; intro S
  dsimp [liftOpt, X]
  by_cases hn : none ∈ S
  · have hne : S ≠ {some i} := fun h => by simp [h] at hn
    simp [hn, hne]
  · rw [if_neg hn]
    have heq : optPre S = {i} ↔ S = {some i} := by
      constructor
      · intro h
        ext x
        cases x with
        | none => simp [hn]
        | some a =>
          have := Finset.ext_iff.mp h a
          simpa using this
      · intro h; subst h; ext a; simp
    by_cases hS : S = {some i}
    · subst hS
      rw [heq.mpr rfl, if_pos rfl, if_pos rfl]
    · rw [if_neg hS, if_neg ((not_iff_not.mpr heq).mpr hS)]

lemma elim_some_liftOpt (i : ι) (f : SqFreeAlg ι K) :
    elim (some i) (liftOpt f) = liftOpt (elim i f) := by
  apply ext; intro S
  by_cases hn : none ∈ S
  · by_cases hi : some i ∈ S <;> simp [hi, hn, liftOpt]
  · by_cases hi : some i ∈ S <;> simp [hi, hn, liftOpt]

end OptionLift

section LinearSpaces

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

noncomputable def supp (u : SqFreeAlg ι K) : Finset ι :=
  open scoped Classical in
  Finset.univ.filter (fun i => u.coeff {i} ≠ 0)

lemma mem_supp_iff {u : SqFreeAlg ι K} {i : ι} : i ∈ supp u ↔ u.coeff {i} ≠ 0 := by
  classical
  simp [supp]

lemma supp_nonempty_of_ne_zero {u : SqFreeAlg ι K} (hu : IsHomog 1 u) (hne : u ≠ 0) :
    (supp u).Nonempty := by
  by_contra hemp
  rw [Finset.not_nonempty_iff_eq_empty] at hemp
  apply hne
  apply ext; intro S
  by_cases h1 : S.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
    by_contra hc
    have : i ∈ supp u := mem_supp_iff.mpr hc
    rw [hemp] at this
    exact Finset.notMem_empty i this
  · exact hu S h1

def IsLinearSpace (U : Submodule K (SqFreeAlg ι K)) : Prop :=
  ∀ u ∈ U, IsHomog 1 u

noncomputable def spaceSupp (U : Submodule K (SqFreeAlg ι K)) : Finset ι :=
  open scoped Classical in
  Finset.univ.filter (fun i => ∃ u ∈ U, u.coeff {i} ≠ 0)

lemma mem_spaceSupp_iff {U : Submodule K (SqFreeAlg ι K)} {i : ι} :
    i ∈ spaceSupp U ↔ ∃ u ∈ U, u.coeff {i} ≠ 0 := by
  classical
  simp [spaceSupp]

lemma spaceSupp_mono {W U : Submodule K (SqFreeAlg ι K)} (hW : W ≤ U) :
    spaceSupp W ⊆ spaceSupp U := by
  intro i hi
  rw [mem_spaceSupp_iff] at hi ⊢
  rcases hi with ⟨u, hu, hc⟩
  exact ⟨u, hW hu, hc⟩

lemma supp_subset_spaceSupp {U : Submodule K (SqFreeAlg ι K)} {u : SqFreeAlg ι K} (hu : u ∈ U) :
    supp u ⊆ spaceSupp U := by
  intro i hi
  rw [mem_supp_iff] at hi
  rw [mem_spaceSupp_iff]
  exact ⟨u, hu, hi⟩

def Covers (U : Submodule K (SqFreeAlg ι K)) (a : ℕ → ℕ) : Prop :=
  ∀ W : Submodule K (SqFreeAlg ι K), W ≤ U → 1 ≤ Module.finrank K W →
    a (Module.finrank K W) ≤ (spaceSupp W).card

lemma covers_mono {U : Submodule K (SqFreeAlg ι K)} {a b : ℕ → ℕ}
    (hUa : Covers U a) (hba : ∀ i, 1 ≤ i → i ≤ Module.finrank K U → b i ≤ a i) :
    Covers U b := by
  intro W hWU hW1
  have hWle : Module.finrank K W ≤ Module.finrank K U := Submodule.finrank_mono hWU
  exact (hba (Module.finrank K W) hW1 hWle).trans (hUa W hWU hW1)

lemma covers_sub {V U : Submodule K (SqFreeAlg ι K)} {a : ℕ → ℕ}
    (hVU : V ≤ U) (hUa : Covers U a) : Covers V a :=
  fun W hWV hW1 => hUa W (hWV.trans hVU) hW1

lemma not_mem_iUnion_proper_submodules [Infinite K] {M : Type*} [AddCommGroup M] [Module K M]
    {α : Type*} (s : Finset α) (V : α → Submodule K M) (hV : ∀ a ∈ s, V a ≠ ⊤) :
    ∃ x : M, ∀ a ∈ s, x ∉ V a := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, fun a ha => (Finset.notMem_empty a ha).elim⟩
  | @insert b s hb ih =>
    have hs : ∀ a ∈ s, V a ≠ ⊤ := fun a ha => hV a (Finset.mem_insert_of_mem ha)
    obtain ⟨x, hx⟩ := ih hs
    have hbtop : V b ≠ ⊤ := hV b (Finset.mem_insert_self b s)
    have hy_ex : ∃ y : M, y ∉ V b := by
      by_contra h
      push Not at h
      apply hbtop
      rw [eq_top_iff]
      intro m _
      exact h m
    obtain ⟨y, hy⟩ := hy_ex
    have hbad_sub : ∀ a ∈ insert b s, ({c : K | x + c • y ∈ V a} : Set K).Subsingleton := by
      intro a ha c₁ hc₁ c₂ hc₂
      by_contra hne
      have hdiff : (c₁ - c₂) • y ∈ V a := by
        have hsub := (V a).sub_mem hc₁ hc₂
        have heq : x + c₁ • y - (x + c₂ • y) = (c₁ - c₂) • y := by
          rw [sub_smul]; abel
        rwa [heq] at hsub
      have hy_mem : y ∈ V a := by
        have := (V a).smul_mem (c₁ - c₂)⁻¹ hdiff
        rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul] at this
      rcases Finset.mem_insert.mp ha with rfl | has
      · exact hy hy_mem
      · have hx_mem : x ∈ V a := by
          have := (V a).sub_mem hc₁ ((V a).smul_mem c₁ hy_mem)
          simpa using this
        exact hx a has hx_mem
    have hfin : (⋃ a ∈ (insert b s : Finset α), {c : K | x + c • y ∈ V a}).Finite :=
      (insert b s).finite_toSet.biUnion fun a ha => (hbad_sub a ha).finite
    obtain ⟨c, hc⟩ := hfin.infinite_compl.nonempty
    refine ⟨x + c • y, fun a ha hmem => hc ?_⟩
    exact Set.mem_biUnion ha hmem

lemma ideal_homog_decomp {n k : ℕ} {U : Submodule K (SqFreeAlg ι K)}
    (hU : IsLinearSpace U) {b : Fin n → SqFreeAlg ι K}
    (hb : Submodule.span K (Set.range b) = U) {f : SqFreeAlg ι K}
    (hfU : f ∈ Ideal.span (U : Set (SqFreeAlg ι K))) :
    (IsHomog 0 f → f = 0) ∧
    (IsHomog (k + 1) f → ∃ a : Fin n → SqFreeAlg ι K,
      (∀ j, IsHomog k (a j)) ∧ f = ∑ j : Fin n, a j * b j) := by
  have hbU : ∀ j, b j ∈ U := fun j => hb ▸ Submodule.subset_span ⟨j, rfl⟩
  have hspan_eq : Ideal.span (U : Set (SqFreeAlg ι K)) = Ideal.span (Set.range b) := by
    apply le_antisymm
    · rw [Ideal.span_le]
      intro u hu
      have hu' : u ∈ Submodule.span K (Set.range b) := hb ▸ hu
      rw [Submodule.mem_span_range_iff_exists_fun] at hu'
      rcases hu' with ⟨c, rfl⟩
      refine Ideal.sum_mem _ fun j _ => ?_
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact Ideal.subset_span (hbU j)
  rw [hspan_eq, Ideal.mem_span_range_iff_exists_fun] at hfU
  rcases hfU with ⟨a₀, ha₀⟩
  constructor
  · intro hf0
    have hp := congrArg (homogPart 0) ha₀.symm
    rw [homogPart_of_isHomog hf0, homogPart_sum] at hp
    rw [hp]
    apply Finset.sum_eq_zero
    intro j _
    exact homogPart_mul_linear_zero (a₀ j) (b j) (hU (b j) (hbU j))
  · intro hfk
    have hp := congrArg (homogPart (k + 1)) ha₀.symm
    rw [homogPart_of_isHomog hfk, homogPart_sum] at hp
    refine ⟨fun j => homogPart k (a₀ j), fun j => isHomog_homogPart k (a₀ j), ?_⟩
    rw [hp]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact homogPart_mul_linear_succ k (a₀ j) (b j) (hU (b j) (hbU j))

lemma mem_ideal_span_coeff_empty {U : Submodule K (SqFreeAlg ι K)}
    (hU : IsLinearSpace U) {f : SqFreeAlg ι K}
    (hf : f ∈ Ideal.span (U : Set (SqFreeAlg ι K))) : f.coeff ∅ = 0 := by
  rw [Submodule.mem_span_set] at hf
  rcases hf with ⟨c, hc, rfl⟩
  simp only [Finsupp.sum, smul_eq_mul]
  have hsum : ∀ (s : Finset (SqFreeAlg ι K)) (g : SqFreeAlg ι K → SqFreeAlg ι K),
      (∑ u ∈ s, g u).coeff ∅ = ∑ u ∈ s, (g u).coeff ∅ := by
    intro s g
    classical
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, add_coeff, ih, Finset.sum_insert ha]
  rw [hsum]
  apply Finset.sum_eq_zero
  intro u hu
  have huU : u ∈ U := hc hu
  have hlin : IsHomog 1 u := hU u huU
  have hmul0 : (c u * u).coeff ∅ = 0 := by
    have := homogPart_mul_linear_zero (c u) u hlin
    have := congrArg (fun x : SqFreeAlg ι K => x.coeff ∅) this
    simpa using this
  exact hmul0

end LinearSpaces

section Theorem5

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K] [CharP K 3]

private lemma thm5_joint (k : ℕ) :
    (∀ {u : SqFreeAlg ι K}, IsHomog 1 u → 2 * k + 1 ≤ (supp u).card →
      ∀ f : SqFreeAlg ι K, IsHomog k f → f * u = 0 →
        (k < 2 → f = 0) ∧ (2 ≤ k → ∃ g, IsHomog (k - 2) g ∧ f = g * u ^ 2)) ∧
    (∀ {u : SqFreeAlg ι K}, IsHomog 1 u → 2 * k + 2 ≤ (supp u).card →
      ∀ f : SqFreeAlg ι K, IsHomog k f → f * u ^ 2 = 0 →
        f ∈ Ideal.span ({u} : Set (SqFreeAlg ι K))) := by
  induction k with
  | zero =>
    constructor
    · intro u hu hcard f hf0 hfu
      rw [isHomog_zero_eq_algebraMap hf0] at hfu ⊢
      have hne : (supp u).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨x, hx⟩ := hne
      have hxc : u.coeff {x} ≠ 0 := mem_supp_iff.mp hx
      have h0 : f.coeff ∅ * u.coeff {x} = 0 := by
        have := congrArg (fun z : SqFreeAlg ι K => z.coeff {x}) hfu
        simpa [Algebra.algebraMap_eq_smul_one] using this
      have hc : f.coeff ∅ = 0 := (mul_eq_zero.mp h0).resolve_right hxc
      exact ⟨fun _ => by simp [hc], fun h => by omega⟩
    · intro u hu hcard f hf0 hfu2
      have hne : (supp u).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨x, hx⟩ := hne
      have hsub : 2 ≤ (supp u).card := by omega
      obtain ⟨y, hy, hxy⟩ : ∃ y ∈ supp u, y ≠ x := by
        by_contra h
        push Not at h
        have hsub1 : supp u ⊆ {x} := fun z hz => Finset.mem_singleton.mpr (h z hz)
        have := Finset.card_le_card hsub1
        simp at this
        omega
      have hc2 : (u ^ 2).coeff {x, y} ≠ 0 := by
        rw [sq, mul_coeff]
        have hx_ne : ({x} : Finset ι) ≠ {y} := fun h => hxy (Finset.singleton_injective h).symm
        have hxy_sdiff_x : ({x, y} : Finset ι) \ {x} = {y} := by
          ext z
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | rfl, h⟩
            · exact (h rfl).elim
            · rfl
          · rintro rfl; exact ⟨Or.inr rfl, hxy⟩
        have hxy_sdiff_y : ({x, y} : Finset ι) \ {y} = {x} := by
          ext z
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | rfl, h⟩
            · rfl
            · exact (h rfl).elim
          · rintro rfl; exact ⟨Or.inl rfl, hxy.symm⟩
        have hpow : ({x, y} : Finset ι).powerset = {∅, {x}, {y}, {x, y}} := by
          ext T
          simp only [Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · intro hT
            by_cases hxT : x ∈ T <;> by_cases hyT : y ∈ T
            · right; right; right; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]
              refine ⟨fun hz => ?_, by rintro (rfl | rfl) <;> assumption⟩
              rcases Finset.mem_insert.mp (hT hz) with hzx | hzy
              · exact Or.inl hzx
              · exact Or.inr (Finset.mem_singleton.mp hzy)
            · right; left; ext z; simp only [Finset.mem_singleton]
              refine ⟨fun hz => ?_, by rintro rfl; exact hxT⟩
              rcases Finset.mem_insert.mp (hT hz) with rfl | hzy
              · rfl
              · exact (hyT ((Finset.mem_singleton.mp hzy) ▸ hz)).elim
            · right; right; left; ext z; simp only [Finset.mem_singleton]
              refine ⟨fun hz => ?_, by rintro rfl; exact hyT⟩
              rcases Finset.mem_insert.mp (hT hz) with hzx | hzy
              · exact (hxT (hzx ▸ hz)).elim
              · exact Finset.mem_singleton.mp hzy
            · left; ext z; simp only [Finset.notMem_empty, iff_false]
              intro hz
              rcases Finset.mem_insert.mp (hT hz) with hzx | hzy
              · exact hxT (hzx ▸ hz)
              · exact hyT ((Finset.mem_singleton.mp hzy) ▸ hz)
          · rintro (rfl | rfl | rfl | rfl)
            · exact Finset.empty_subset _
            · exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)
            · exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
            · exact Finset.Subset.refl _
        have hsum2 : ∑ T ∈ ({x, y} : Finset ι).powerset, u.coeff T * u.coeff ({x, y} \ T) =
            2 * (u.coeff {x} * u.coeff {y}) := by
          have hnot1 : (∅ : Finset ι) ∉ ({({x} : Finset ι), {y}, {x, y}} : Finset (Finset ι)) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            refine ⟨Finset.empty_ne_singleton _, Finset.empty_ne_singleton _, ?_⟩
            intro h
            have : x ∈ (∅ : Finset ι) := h ▸ Finset.mem_insert_self x {y}
            exact Finset.notMem_empty x this
          have hnot2 : ({x} : Finset ι) ∉ ({({y} : Finset ι), {x, y}} : Finset (Finset ι)) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, hx_ne, false_or]
            intro h
            have : y ∈ ({x} : Finset ι) := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
            exact hxy (Finset.mem_singleton.mp this)
          have hnot3 : ({y} : Finset ι) ∉ ({({x, y} : Finset ι)} : Finset (Finset ι)) := by
            simp only [Finset.mem_singleton]
            intro h
            have : x ∈ ({y} : Finset ι) := h ▸ Finset.mem_insert_self x {y}
            exact hxy.symm (Finset.mem_singleton.mp this)
          rw [hpow, Finset.sum_insert hnot1, Finset.sum_insert hnot2, Finset.sum_insert hnot3,
            Finset.sum_singleton]
          have h0c : u.coeff ∅ = 0 := hu ∅ (by simp)
          have h2c : u.coeff {x, y} = 0 := hu {x, y} (by simp [hxy.symm])
          rw [h0c, h2c, hxy_sdiff_x, hxy_sdiff_y]
          ring
        rw [hsum2]
        have h2ne : (2 : K) ≠ 0 := by
          intro h2
          have h2' : ((2 : ℕ) : K) = 0 := by simpa using h2
          rw [CharP.cast_eq_zero_iff K 3 2] at h2'
          omega
        exact mul_ne_zero h2ne (mul_ne_zero (mem_supp_iff.mp hx) (mem_supp_iff.mp hy))
      rw [isHomog_zero_eq_algebraMap hf0] at hfu2 ⊢
      have h0 : f.coeff ∅ * (u ^ 2).coeff {x, y} = 0 := by
        have := congrArg (fun z : SqFreeAlg ι K => z.coeff {x, y}) hfu2
        simpa [Algebra.algebraMap_eq_smul_one] using this
      have hc : f.coeff ∅ = 0 := (mul_eq_zero.mp h0).resolve_right hc2
      simp [hc]
  | succ k ih =>
    have ih2 : ∀ {u : SqFreeAlg ι K}, IsHomog 1 u → 2 * k + 2 ≤ (supp u).card →
        ∀ f : SqFreeAlg ι K, IsHomog k f → f * u ^ 2 = 0 →
          f ∈ Ideal.span ({u} : Set (SqFreeAlg ι K)) := ih.2
    have step1 : ∀ {u : SqFreeAlg ι K}, IsHomog 1 u → 2 * (k + 1) + 1 ≤ (supp u).card →
        ∀ f : SqFreeAlg ι K, IsHomog (k + 1) f → f * u = 0 →
          (k + 1 < 2 → f = 0) ∧ (2 ≤ k + 1 → ∃ g, IsHomog (k + 1 - 2) g ∧ f = g * u ^ 2) := by
      intro u hu hcard f hf hfu
      have hne : (supp u).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨x, hx⟩ := hne
      have hxc : u.coeff {x} ≠ 0 := mem_supp_iff.mp hx
      set u' := (u.coeff {x})⁻¹ • u
      have hu' : IsHomog 1 u' := isHomog_smul _ hu
      have huc' : u'.coeff {x} = 1 := by simp [u', inv_mul_cancel₀ hxc]
      have hfu' : f * u' = 0 := by
        rw [mul_smul_comm, hfu, smul_zero]
      have hsupp_u' : supp u' = supp u := by
        ext z
        simp only [mem_supp_iff, u', smul_coeff, ne_eq, mul_eq_zero, inv_eq_zero, hxc, false_or]
      set v := elim x u'
      have hv1 : IsHomog 1 v := isHomog_elim x hu'
      have hv_decomp : u' = v + X x := by
        have := decomp_linear x hu'
        rwa [huc', one_smul] at this
      have hsupp_v : (supp v).card = (supp u).card - 1 := by
        rw [← hsupp_u']
        have heq : supp v = (supp u').erase x := by
          ext z
          by_cases hz : z = x
          · subst hz; simp [v, mem_supp_iff]
          · simp [v, mem_supp_iff, hz, Ne.symm hz]
        rw [heq, Finset.card_erase_of_mem (hsupp_u' ▸ hx)]
      have hcard_v : 2 * k + 2 ≤ (supp v).card := by omega
      have hderiv := congrArg (deriv x) hfu'
      rw [deriv_mul, map_zero, deriv_isHomog_one x hu', huc', map_one, mul_one] at hderiv
      have hmul_v : deriv x f * v ^ 2 = 0 := by
        have helim := congrArg (elim x) hfu'
        rw [elim_mul, map_zero] at helim
        have := congrArg (fun z => z * v) hderiv
        rw [add_mul, mul_assoc, ← sq, helim, add_zero, zero_mul] at this
        exact this
      have hdf_ideal : deriv x f ∈ Ideal.span ({v} : Set (SqFreeAlg ι K)) :=
        ih2 hv1 hcard_v (deriv x f) (isHomog_deriv x hf) hmul_v
      rw [Ideal.mem_span_singleton] at hdf_ideal
      rcases hdf_ideal with ⟨g', hg'⟩
      have helim_f : elim x f = - (deriv x f * v) := by
        exact eq_neg_of_add_eq_zero_right hderiv
      have hf_eq : f = (deriv x f) * (X x - v) := by
        calc f = elim x f + deriv x f * X x := decomp x f
        _ = -(deriv x f * v) + deriv x f * X x := by rw [helim_f]
        _ = deriv x f * (X x - v) := by ring
      cases k with
      | zero =>
        have hd0 : deriv x f = 0 := by
          have := congrArg (homogPart 0) hg'
          rw [homogPart_of_isHomog (isHomog_deriv x hf), mul_comm, homogPart_mul_linear_zero g' v hv1] at this
          exact this
        have hf0 : f = 0 := by rw [hf_eq, hd0, zero_mul]
        exact ⟨fun _ => hf0, fun h => by omega⟩
      | succ k' =>
        have hg_hom : ∃ g : SqFreeAlg ι K, IsHomog k' g ∧ deriv x f = g * v := by
          have := congrArg (homogPart (k' + 1)) hg'
          rw [homogPart_of_isHomog (isHomog_deriv x hf), mul_comm,
            homogPart_mul_linear_succ k' g' v hv1] at this
          exact ⟨homogPart k' g', isHomog_homogPart k' g', this⟩
        rcases hg_hom with ⟨g, hg, hdv⟩
        have hchar : CharP (SqFreeAlg ι K) 3 := charP_three
        have h3 : (3 : SqFreeAlg ι K) = 0 := CharP.cast_eq_zero_iff (SqFreeAlg ι K) 3 3 |>.mpr dvd_rfl
        have hneg_sq : v * (X x - v) = - (u' ^ 2) := by
          rw [hv_decomp]
          have hx2 : (X (K := K) x) ^ 2 = 0 := X_sq x
          calc v * (X x - v) = - v ^ 2 + v * X x := by ring
          _ = - v ^ 2 + v * X x - 3 * (v * X x) := by rw [h3, zero_mul, sub_zero]
          _ = - (v ^ 2 + 2 * (v * X x) + (X x) ^ 2) := by rw [hx2]; ring
          _ = - ((v + X x) ^ 2) := by ring
        have hf_u' : f = (- ((u.coeff {x})⁻¹ ^ 2 • g)) * u ^ 2 := by
          calc f = deriv x f * (X x - v) := hf_eq
          _ = (g * v) * (X x - v) := by rw [hdv]
          _ = g * (v * (X x - v)) := by ring
          _ = g * (- (u' ^ 2)) := by rw [hneg_sq]
          _ = (- g) * (((u.coeff {x})⁻¹ • u) ^ 2) := by ring
          _ = (- ((u.coeff {x})⁻¹ ^ 2 • g)) * u ^ 2 := by
            rw [smul_pow, Algebra.mul_smul_comm, ← Algebra.smul_mul_assoc, smul_neg]
        refine ⟨fun h => by omega, fun _ => ⟨- ((u.coeff {x})⁻¹ ^ 2 • g),
          isHomog_neg (isHomog_smul _ hg), hf_u'⟩⟩
    refine ⟨step1, ?_⟩
    intro u hu hcard f hf hfu2
    have hne : (supp u).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hx⟩ := hne
    have hxc : u.coeff {x} ≠ 0 := mem_supp_iff.mp hx
    set u' := (u.coeff {x})⁻¹ • u
    have hu' : IsHomog 1 u' := isHomog_smul _ hu
    have huc' : u'.coeff {x} = 1 := by simp [u', inv_mul_cancel₀ hxc]
    have hfu'2 : f * u' ^ 2 = 0 := by
      rw [smul_pow, Algebra.mul_smul_comm, hfu2, smul_zero]
    have hsupp_u' : supp u' = supp u := by
      ext z
      simp only [mem_supp_iff, u', smul_coeff, ne_eq, mul_eq_zero, inv_eq_zero, hxc, false_or]
    set v := elim x u'
    have hv1 : IsHomog 1 v := isHomog_elim x hu'
    have hv_decomp : u' = v + X x := by
      have := decomp_linear x hu'
      rwa [huc', one_smul] at this
    have hsupp_v : (supp v).card = (supp u).card - 1 := by
      rw [← hsupp_u']
      have heq : supp v = (supp u').erase x := by
        ext z
        by_cases hz : z = x
        · subst hz; simp [v, mem_supp_iff]
        · simp [v, mem_supp_iff, hz, Ne.symm hz]
      rw [heq, Finset.card_erase_of_mem (hsupp_u' ▸ hx)]
    have hcard_v : 2 * (k + 1) + 1 ≤ (supp v).card := by omega
    have hderiv := congrArg (deriv x) hfu'2
    rw [hv_decomp, deriv_mul, map_zero, deriv_sq_add_X x (deriv_elim_self x u'),
      elim_sq_add_X x (deriv_elim_self x u')] at hderiv
    have hsum_v : ((2 : K) • elim x f + deriv x f * v) * v = 0 := by
      calc ((2 : K) • elim x f + deriv x f * v) * v
          = deriv x f * v ^ 2 + elim x f * ((2 : K) • v) := by
            rw [add_mul, mul_assoc, ← sq, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, add_comm]
        _ = 0 := hderiv
    have hhom_sum : IsHomog (k + 1) ((2 : K) • elim x f + deriv x f * v) := by
      refine isHomog_add (isHomog_smul _ (isHomog_elim x hf)) ?_
      simpa [add_comm] using isHomog_mul (isHomog_deriv x hf) hv1
    obtain ⟨h_lt, h_ge⟩ := step1 hv1 hcard_v ((2 : K) • elim x f + deriv x f * v) hhom_sum hsum_v
    have h_eq : ∃ g : SqFreeAlg ι K, (2 : K) • elim x f + deriv x f * v = g * v ^ 2 := by
      by_cases hk : k + 1 < 2
      · exact ⟨0, by rw [h_lt hk, zero_mul]⟩
      · obtain ⟨g, _, hg⟩ := h_ge (by omega)
        exact ⟨g, hg⟩
    rcases h_eq with ⟨g, hg⟩
    have h3 : (3 : K) = 0 := CharP.cast_eq_zero_iff K 3 3 |>.mpr dvd_rfl
    have helim_f : elim x f = deriv x f * v - g * v ^ 2 := by
      have h2eq : (2 : K) • elim x f = - elim x f := by
        calc (2 : K) • elim x f = (2 : K) • elim x f - (3 : K) • elim x f := by rw [h3, zero_smul, sub_zero]
        _ = - elim x f := by rw [← sub_smul]; norm_num
      rw [h2eq] at hg
      calc elim x f = deriv x f * v - (- elim x f + deriv x f * v) := by ring
      _ = deriv x f * v - g * v ^ 2 := by rw [hg]
    have hf_in_u' : f ∈ Ideal.span ({u'} : Set (SqFreeAlg ι K)) := by
      have hv2 : v ^ 2 = u' * (v - X x) := by
        rw [hv_decomp]
        exact sq_eq_add_mul_sub v (X x) (X_sq x)
      have hf_eq : f = (deriv x f - g * (v - X x)) * u' := by
        calc f = elim x f + deriv x f * X x := decomp x f
        _ = (deriv x f * v - g * v ^ 2) + deriv x f * X x := by rw [helim_f]
        _ = deriv x f * (v + X x) - g * (u' * (v - X x)) := by rw [hv2]; ring
        _ = (deriv x f - g * (v - X x)) * u' := by rw [← hv_decomp]; ring
      rw [hf_eq, Ideal.mem_span_singleton]
      exact ⟨deriv x f - g * (v - X x), mul_comm _ _⟩
    have hspan_eq : Ideal.span ({u'} : Set (SqFreeAlg ι K)) = Ideal.span ({u} : Set (SqFreeAlg ι K)) := by
      apply le_antisymm <;> rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
      · exact ⟨algebraMap K _ (u.coeff {x})⁻¹, by simp [u', Algebra.smul_def, mul_comm]⟩
      · refine ⟨algebraMap K _ (u.coeff {x}), ?_⟩
        rw [mul_comm, ← Algebra.smul_def]
        simp [u', smul_smul, mul_inv_cancel₀ hxc]
    rwa [← hspan_eq]

lemma thm5_1 {u : SqFreeAlg ι K} (hu : IsHomog 1 u) {k : ℕ}
    (hcard : 2 * k + 1 ≤ (supp u).card) {f : SqFreeAlg ι K} (hf : IsHomog k f)
    (hfu : f * u = 0) :
    (k < 2 → f = 0) ∧ (2 ≤ k → ∃ g, IsHomog (k - 2) g ∧ f = g * u ^ 2) :=
  (thm5_joint k).1 hu hcard f hf hfu

lemma thm5_2 {u : SqFreeAlg ι K} (hu : IsHomog 1 u) {k : ℕ}
    (hcard : 2 * k + 2 ≤ (supp u).card) {f : SqFreeAlg ι K} (hf : IsHomog k f)
    (hfu2 : f * u ^ 2 = 0) :
    f ∈ Ideal.span ({u} : Set (SqFreeAlg ι K)) :=
  (thm5_joint k).2 hu hcard f hf hfu2

end Theorem5

section Lemma6

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K] [Infinite K]

lemma lemma6_aux {U : Submodule K (SqFreeAlg ι K)} (hU : IsLinearSpace U)
    {n : ℕ} (hn : Module.finrank K U = n) (a : ℕ → ℕ)
    (ha : ∀ i j, 1 ≤ i → i ≤ j → j ≤ n → a i ≤ a j)
    (hcov : Covers U a) :
    ∀ k ≤ n, ∃ Uk : Submodule K (SqFreeAlg ι K), Uk ≤ U ∧ Module.finrank K Uk = k ∧
      Covers Uk (fun i => a (n - k + i)) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨⊥, bot_le, by simp, fun W hW hW1 => ?_⟩
    have : W = ⊥ := le_bot_iff.mp hW
    subst this
    simp at hW1
  | succ k ih =>
    intro hk
    obtain ⟨Uk, hUkU, hUk_dim, hUk_cov⟩ := ih (Nat.le_of_succ_le hk)
    let m := a (n - k)
    let badS := (spaceSupp U).powerset.filter (fun S => S.card = m - 1)
    let VS (S : Finset ι) : Submodule K (SqFreeAlg ι K) :=
      { carrier := {v ∈ U | ∃ u ∈ Uk, supp (v + u) ⊆ S}
        zero_mem' := ⟨U.zero_mem, 0, Uk.zero_mem, by simp [supp]⟩
        add_mem' := by
          rintro v₁ v₂ ⟨hv₁, u₁, hu₁, hS₁⟩ ⟨hv₂, u₂, hu₂, hS₂⟩
          refine ⟨U.add_mem hv₁ hv₂, u₁ + u₂, Uk.add_mem hu₁ hu₂, fun z hz => ?_⟩
          rw [mem_supp_iff, add_coeff, add_coeff, add_coeff] at hz
          have heq : (v₁ + u₁).coeff {z} + (v₂ + u₂).coeff {z} =
              (v₁.coeff {z} + v₂.coeff {z}) + (u₁.coeff {z} + u₂.coeff {z}) := by
            simp only [add_coeff]; ring
          rw [← heq] at hz
          by_cases h1 : (v₁ + u₁).coeff {z} = 0
          · have h2 : (v₂ + u₂).coeff {z} ≠ 0 := fun h2 => hz (by simp [h1, h2])
            exact hS₂ (mem_supp_iff.mpr h2)
          · exact hS₁ (mem_supp_iff.mpr h1)
        smul_mem' := by
          rintro c v ⟨hv, u, hu, hS⟩
          refine ⟨U.smul_mem c hv, c • u, Uk.smul_mem c hu, fun z hz => ?_⟩
          rw [mem_supp_iff, ← smul_add, smul_coeff] at hz
          have hnz : (v + u).coeff {z} ≠ 0 := fun h => hz (by simp [h])
          exact hS (mem_supp_iff.mpr hnz) }
    let VS_sub (S : Finset ι) : Submodule K U := (VS S).comap U.subtype
    have hproper : ∀ S ∈ badS, VS_sub S ≠ ⊤ := by
      intro S hS htop
      have hScard : S.card = m - 1 := (Finset.mem_filter.mp hS).2
      let Uk_sub : Submodule K U := Uk.comap U.subtype
      obtain ⟨W_sub, hW_compl⟩ := Submodule.exists_isCompl Uk_sub
      let W : Submodule K (SqFreeAlg ι K) := W_sub.map U.subtype
      have hWU : W ≤ U := Submodule.map_subtype_le U W_sub
      have hdisj : Disjoint Uk W := by
        rw [disjoint_iff]
        ext x
        simp only [Submodule.mem_inf, Submodule.mem_bot, W, Submodule.mem_map,
          Submodule.subtype_apply]
        constructor
        · rintro ⟨hxUk, y, hyW, rfl⟩
          have hyUk : y ∈ Uk_sub := hxUk
          have : y ∈ Uk_sub ⊓ W_sub := ⟨hyUk, hyW⟩
          rw [hW_compl.inf_eq_bot, Submodule.mem_bot] at this
          simp [this]
        · rintro rfl; exact ⟨Uk.zero_mem, 0, W_sub.zero_mem, rfl⟩
      have hsup : Uk ⊔ W = U := by
        apply le_antisymm (sup_le hUkU hWU)
        intro x hxU
        have hmem : (⟨x, hxU⟩ : U) ∈ Uk_sub ⊔ W_sub := by
          rw [hW_compl.sup_eq_top]; trivial
        rw [Submodule.mem_sup] at hmem
        rcases hmem with ⟨y, hy, z, hz, hyz⟩
        rw [Submodule.mem_sup]
        exact ⟨y.1, hy, z.1, ⟨z, hz, rfl⟩, congrArg Subtype.val hyz⟩
      have hW_dim : Module.finrank K W = n - k := by
        have hadd := Submodule.finrank_sup_add_finrank_inf_eq Uk W
        rw [hsup, hdisj.eq_bot, finrank_bot, add_zero, hn, hUk_dim] at hadd
        omega
      let bW := Module.finBasis K W
      have hbW_ind : LinearIndependent K (fun j : Fin (Module.finrank K W) => (bW j : SqFreeAlg ι K)) :=
        (bW.linearIndependent).map' W.subtype (Submodule.ker_subtype W)
      have hbW_mem : ∀ j, (bW j : SqFreeAlg ι K) ∈ U := fun j => hWU (bW j).2
      have hpair : ∀ j, ∃ u ∈ Uk, supp ((bW j : SqFreeAlg ι K) + u) ⊆ S := by
        intro j
        have hmem : (⟨(bW j : SqFreeAlg ι K), hbW_mem j⟩ : U) ∈ VS_sub S := by
          rw [htop]; trivial
        exact hmem.2
      choose u hu_mem hu_supp using hpair
      let w' : Fin (Module.finrank K W) → SqFreeAlg ι K := fun j => (bW j : SqFreeAlg ι K) + u j
      let W' : Submodule K (SqFreeAlg ι K) := Submodule.span K (Set.range w')
      have hW'U : W' ≤ U := by
        rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact U.add_mem (hbW_mem j) (hUkU (hu_mem j))
      have hw'_ind : LinearIndependent K w' := by
        rw [Fintype.linearIndependent_iff]
        intro c hc
        have hsum_eq : ∑ j, c j • (bW j : SqFreeAlg ι K) = - ∑ j, c j • u j := by
          have : (∑ j, c j • (bW j : SqFreeAlg ι K)) + ∑ j, c j • u j = 0 := by
            calc (∑ j, c j • (bW j : SqFreeAlg ι K)) + ∑ j, c j • u j
                = ∑ j, c j • w' j := by simp only [w', smul_add, Finset.sum_add_distrib]
              _ = 0 := hc
          exact eq_neg_of_add_eq_zero_left this
        have hmemW : ∑ j, c j • (bW j : SqFreeAlg ι K) ∈ W :=
          W.sum_mem fun j _ => W.smul_mem (c j) (bW j).2
        have hmemUk : ∑ j, c j • (bW j : SqFreeAlg ι K) ∈ Uk := by
          rw [hsum_eq]
          exact Uk.neg_mem (Uk.sum_mem fun j _ => Uk.smul_mem (c j) (hu_mem j))
        have hbot : ∑ j, c j • (bW j : SqFreeAlg ι K) = 0 := by
          rw [← Submodule.mem_bot (R := K), ← hdisj.eq_bot]
          exact ⟨hmemUk, hmemW⟩
        exact (Fintype.linearIndependent_iff.mp hbW_ind) c hbot
      have hW'_dim : Module.finrank K W' = n - k := by
        rw [finrank_span_eq_card hw'_ind, Fintype.card_fin, hW_dim]
      have hW'_supp : spaceSupp W' ⊆ S := by
        intro z hz
        rw [mem_spaceSupp_iff] at hz
        rcases hz with ⟨x, hxW', hxz⟩
        rw [Submodule.mem_span_range_iff_exists_fun] at hxW'
        rcases hxW' with ⟨c, rfl⟩
        have hsum_coeff : (∑ j, c j • w' j).coeff {z} = ∑ j, c j * (w' j).coeff {z} := by
          clear hxz
          induction (Finset.univ : Finset (Fin (Module.finrank K W))) using Finset.induction with
          | empty => simp
          | insert a s ha ih =>
            rw [Finset.sum_insert ha, add_coeff, Finset.sum_insert ha, ih, smul_coeff]
        rw [hsum_coeff] at hxz
        obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hxz
        have hjc : (w' j).coeff {z} ≠ 0 := fun h => hj (by simp [h])
        exact hu_supp j (mem_supp_iff.mpr hjc)
      have hcard_le : (spaceSupp W').card ≤ m - 1 :=
        (Finset.card_le_card hW'_supp).trans hScard.le
      by_cases hm0 : m = 0
      · have hpos : 0 < Module.finrank K W' := by omega
        have hne_bot : W' ≠ ⊥ := fun h => by rw [h, finrank_bot] at hpos; omega
        obtain ⟨x, hxW', hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
        obtain ⟨z, hz⟩ := supp_nonempty_of_ne_zero (hU x (hW'U hxW')) hx0
        have hzS : z ∈ spaceSupp W' := supp_subset_spaceSupp hxW' hz
        have : 0 < (spaceSupp W').card := Finset.card_pos.mpr ⟨z, hzS⟩
        omega
      · have hcovW' := hcov W' hW'U (by omega)
        rw [hW'_dim] at hcovW'
        omega
    obtain ⟨⟨v, hvU⟩, hv_not⟩ := not_mem_iUnion_proper_submodules badS VS_sub hproper
    have hbad_ne : badS.Nonempty := by
      have hm_le : m - 1 ≤ (spaceSupp U).card := by
        have hcovU := hcov U le_rfl (by omega)
        rw [hn] at hcovU
        have hnk : a (n - k) ≤ a n := ha (n - k) n (by omega) (Nat.sub_le n k) le_rfl
        have hm_eq : m = a (n - k) := rfl
        omega
      obtain ⟨S, hSU, hSc⟩ := Finset.exists_subset_card_eq hm_le
      exact ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSU, hSc⟩⟩
    have hv_not_Uk : v ∉ Uk := by
      intro hvUk
      obtain ⟨S, hS⟩ := hbad_ne
      apply hv_not S hS
      refine ⟨hvU, -v, Uk.neg_mem hvUk, ?_⟩
      have h0 : supp (v + -v) = ∅ := by
        rw [add_neg_cancel]
        ext z; simp [mem_supp_iff]
      change supp (v + -v) ⊆ S
      rw [h0]
      exact Finset.empty_subset S
    let Uk' := Uk ⊔ Submodule.span K {v}
    have hUk'U : Uk' ≤ U := sup_le hUkU (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvU))
    have hUk'_dim : Module.finrank K Uk' = k + 1 := by
      have hdisj : Disjoint Uk (Submodule.span K {v}) := by
        rw [disjoint_iff]
        ext x
        simp only [Submodule.mem_inf, Submodule.mem_bot, Submodule.mem_span_singleton]
        constructor
        · rintro ⟨hxUk, c, rfl⟩
          by_cases hc : c = 0
          · simp [hc]
          · exfalso; apply hv_not_Uk
            have := Uk.smul_mem c⁻¹ hxUk
            rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
        · rintro rfl; exact ⟨Uk.zero_mem, 0, by simp⟩
      have hv_ne0 : v ≠ 0 := fun h => hv_not_Uk (h ▸ Uk.zero_mem)
      have hspan_dim : Module.finrank K (Submodule.span K {v}) = 1 := finrank_span_singleton hv_ne0
      have hadd := Submodule.finrank_sup_add_finrank_inf_eq Uk (Submodule.span K {v})
      rw [hdisj.eq_bot, finrank_bot, add_zero, hUk_dim, hspan_dim] at hadd
      exact hadd
    refine ⟨Uk', hUk'U, hUk'_dim, ?_⟩
    intro H hHUk' hH1
    by_cases hHUk : H ≤ Uk
    · have hHcov := hUk_cov H hHUk hH1
      have hHle : Module.finrank K H ≤ k := by
        have := Submodule.finrank_mono hHUk
        omega
      have hmono : a (n - (k + 1) + Module.finrank K H) ≤ a (n - k + Module.finrank K H) := by
        apply ha <;> omega
      exact hmono.trans hHcov
    · by_cases hH_eq1 : Module.finrank K H = 1
      · dsimp only
        rw [hH_eq1, show n - (k + 1) + 1 = n - k by omega]
        obtain ⟨w, hwH, hw_not_Uk⟩ : ∃ w ∈ H, w ∉ Uk := by
          by_contra h
          push Not at h
          exact hHUk h
        have hwUk' : w ∈ Uk' := hHUk' hwH
        rw [Submodule.mem_sup] at hwUk'
        rcases hwUk' with ⟨u₀, hu₀, x₀, hx₀, hw_eq⟩
        rw [Submodule.mem_span_singleton] at hx₀
        rcases hx₀ with ⟨c, rfl⟩
        have hc0 : c ≠ 0 := by
          intro hc; subst hc
          apply hw_not_Uk
          rw [← hw_eq, zero_smul, add_zero]
          exact hu₀
        let w' := c⁻¹ • w
        have hw'H : w' ∈ H := H.smul_mem c⁻¹ hwH
        have hw'_eq : w' = v + c⁻¹ • u₀ := by
          dsimp [w']
          rw [← hw_eq, smul_add, smul_smul, inv_mul_cancel₀ hc0, one_smul, add_comm]
        have hm_le_w' : m ≤ (supp w').card := by
          by_contra hlt
          push Not at hlt
          have hle_m1 : (supp w').card ≤ m - 1 := by omega
          have hsub_U : supp w' ⊆ spaceSupp U := supp_subset_spaceSupp (hUk'U (hHUk' hw'H))
          have h_card_U : m - 1 ≤ (spaceSupp U).card := by
            obtain ⟨S, hS⟩ := hbad_ne
            have := (Finset.mem_filter.mp hS).2
            rw [← this]
            exact Finset.card_le_card (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
          obtain ⟨S, hS_sub, hSU, hS_card⟩ : ∃ S, supp w' ⊆ S ∧ S ⊆ spaceSupp U ∧ S.card = m - 1 := by
            have hdiff : m - 1 - (supp w').card ≤ (spaceSupp U \ supp w').card := by
              rw [Finset.card_sdiff_of_subset hsub_U]
              omega
            obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hdiff
            refine ⟨supp w' ∪ T, Finset.subset_union_left, Finset.union_subset hsub_U (hT_sub.trans Finset.sdiff_subset), ?_⟩
            rw [Finset.card_union_of_disjoint (disjoint_sdiff_self_right.mono_right hT_sub)]
            omega
          have hS_bad : S ∈ badS := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSU, hS_card⟩
          apply hv_not S hS_bad
          refine ⟨hvU, c⁻¹ • u₀, Uk.smul_mem c⁻¹ hu₀, ?_⟩
          change supp (v + c⁻¹ • u₀) ⊆ S
          rw [← hw'_eq]
          exact hS_sub
        exact hm_le_w'.trans (Finset.card_le_card (supp_subset_spaceSupp hw'H))
      · have hH_ge2 : 2 ≤ Module.finrank K H := by omega
        have hsup_eq : Uk ⊔ H = Uk' := by
          apply le_antisymm (sup_le le_sup_left hHUk')
          have hlt : Uk < Uk ⊔ H := lt_of_le_of_ne le_sup_left (fun h => hHUk (h ▸ le_sup_right))
          have hdim_lt : k < Module.finrank K ↥(Uk ⊔ H) := by
            rw [← hUk_dim]
            exact Submodule.finrank_lt_finrank_of_lt hlt
          have hdim_le : Module.finrank K ↥(Uk ⊔ H) ≤ k + 1 := by
            rw [← hUk'_dim]
            exact Submodule.finrank_mono (sup_le le_sup_left hHUk')
          have hdim_eq : Module.finrank K ↥Uk' = Module.finrank K ↥(Uk ⊔ H) := by
            rw [hUk'_dim]
            omega
          exact (Submodule.eq_of_le_of_finrank_eq (sup_le le_sup_left hHUk') hdim_eq.symm).ge
        have hinf_dim : Module.finrank K ↥(Uk ⊓ H) = Module.finrank K H - 1 := by
          have hadd := Submodule.finrank_sup_add_finrank_inf_eq Uk H
          rw [hsup_eq, hUk'_dim, hUk_dim] at hadd
          omega
        have hcov_inf := hUk_cov (Uk ⊓ H) inf_le_left (by omega)
        dsimp only at hcov_inf ⊢
        rw [hinf_dim, show n - k + (Module.finrank K H - 1) = n - (k + 1) + Module.finrank K H by omega] at hcov_inf
        exact hcov_inf.trans (Finset.card_le_card (spaceSupp_mono inf_le_right))

end Lemma6

section SplitAndElim

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

lemma basis_split_var {U : Submodule K (SqFreeAlg ι K)} (hU : IsLinearSpace U)
    {m : ℕ} (hm : Module.finrank K U = m + 1) {x : ι} (hx : x ∈ spaceSupp U) :
    ∃ (u₁ : SqFreeAlg ι K) (b_rest : Fin m → SqFreeAlg ι K),
      deriv x u₁ = 0 ∧ u₁ + X x ∈ U ∧
      (∀ j, b_rest j ∈ U ∧ deriv x (b_rest j) = 0) ∧
      Submodule.span K (Set.range (Fin.cons (u₁ + X x) b_rest)) = U := by
  rw [mem_spaceSupp_iff] at hx
  rcases hx with ⟨v₀, hv₀U, hv₀c⟩
  let v₁ : SqFreeAlg ι K := (v₀.coeff {x})⁻¹ • v₀
  have hv₁U : v₁ ∈ U := U.smul_mem _ hv₀U
  have hv₁c : v₁.coeff {x} = 1 := by simp [v₁, inv_mul_cancel₀ hv₀c]
  let u₁ : SqFreeAlg ι K := elim x v₁
  have hu₁d : deriv x u₁ = 0 := deriv_elim_self x v₁
  have hv₁_eq : u₁ + X x = v₁ := by
    have := decomp_linear x (hU v₁ hv₁U)
    rw [hv₁c, one_smul] at this
    exact this.symm
  let φ : U →ₗ[K] K :=
    { toFun u := u.1.coeff {x}
      map_add' u v := rfl
      map_smul' c u := rfl }
  have hφ_surj : Function.Surjective φ := by
    intro c
    refine ⟨c • ⟨v₁, hv₁U⟩, ?_⟩
    simp [φ, hv₁c]
  have hker_dim : Module.finrank K (LinearMap.ker φ) = m := by
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hφ_surj
    rw [hrange, finrank_top, Module.finrank_self, hm] at h1
    omega
  let U₀ : Submodule K (SqFreeAlg ι K) := (LinearMap.ker φ).map U.subtype
  have hU₀_dim : Module.finrank K U₀ = m := by
    rw [Submodule.finrank_map_subtype_eq, hker_dim]
  let b₀ := Module.finBasisOfFinrankEq K U₀ hU₀_dim
  let b_rest : Fin m → SqFreeAlg ι K := fun j => (b₀ j : SqFreeAlg ι K)
  have hb_mem : ∀ j, b_rest j ∈ U := fun j => by
    have hj := (b₀ j).2
    rw [Submodule.mem_map] at hj
    rcases hj with ⟨y, _, heqy⟩
    change ↑(b₀ j) ∈ U
    rw [← heqy]
    exact y.2
  have hb_deriv : ∀ j, deriv x (b_rest j) = 0 := fun j => by
    have hj := (b₀ j).2
    rw [Submodule.mem_map] at hj
    rcases hj with ⟨y, hy, heqy⟩
    have hy0 : y.1.coeff {x} = 0 := hy
    have hd := deriv_isHomog_one x (hU y.1 y.2)
    change deriv x (b₀ j : SqFreeAlg ι K) = 0
    rw [← heqy]
    change deriv x (y.1 : SqFreeAlg ι K) = 0
    rw [hd, hy0, map_zero]
  refine ⟨u₁, b_rest, hu₁d, hv₁_eq.symm ▸ hv₁U, fun j => ⟨hb_mem j, hb_deriv j⟩, ?_⟩
  rw [hv₁_eq]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Fin.cases hv₁U hb_mem i
  · intro u huU
    let r : SqFreeAlg ι K := u - u.coeff {x} • v₁
    have hrU : r ∈ U := U.sub_mem huU (U.smul_mem _ hv₁U)
    have hrU₀ : r ∈ U₀ := by
      rw [Submodule.mem_map]
      refine ⟨⟨r, hrU⟩, ?_, rfl⟩
      change (u - u.coeff {x} • v₁).coeff {x} = 0
      rw [sub_coeff, smul_coeff, hv₁c, mul_one, sub_self]
    have hr_span : r ∈ Submodule.span K (Set.range b_rest) := by
      have : (⟨r, hrU₀⟩ : U₀) ∈ Submodule.span K (Set.range b₀) := by
        rw [b₀.span_eq]; trivial
      rw [Submodule.mem_span_range_iff_exists_fun] at this ⊢
      rcases this with ⟨c, hc⟩
      exact ⟨c, by simpa [b_rest] using congrArg Subtype.val hc⟩
    have hsub_span : Submodule.span K (Set.range b_rest) ≤
        Submodule.span K (Set.range (Fin.cons v₁ b_rest)) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨Fin.succ j, rfl⟩
    have hv₁_span : v₁ ∈ Submodule.span K (Set.range (Fin.cons v₁ b_rest)) :=
      Submodule.subset_span ⟨0, rfl⟩
    have hu_eq : u = r + u.coeff {x} • v₁ := by simp [r]
    rw [hu_eq]
    exact Submodule.add_mem _ (hsub_span hr_span) (Submodule.smul_mem _ _ hv₁_span)

lemma basis_split_subspace {U : Submodule K (SqFreeAlg ι K)} (hU : IsLinearSpace U)
    {m : ℕ} (hm : Module.finrank K U = m + 2) {V : Submodule K (SqFreeAlg ι K)}
    (hVU : V ≤ U) (hV_dim : Module.finrank K V = m + 1) {x : ι} (hx : x ∈ spaceSupp V) :
    ∃ (u₁ : SqFreeAlg ι K) (b_rest : Fin m → SqFreeAlg ι K) (u_last : SqFreeAlg ι K),
      deriv x u₁ = 0 ∧ u₁ + X x ∈ V ∧
      (∀ j, b_rest j ∈ V ∧ deriv x (b_rest j) = 0) ∧
      Submodule.span K (Set.range (Fin.cons (u₁ + X x) b_rest)) = V ∧
      u_last ∈ U ∧ u_last ∉ V ∧ deriv x u_last = 0 ∧
      Submodule.span K (Set.range (Fin.snoc (Fin.cons (u₁ + X x) b_rest) u_last)) = U := by
  have hV_lin : IsLinearSpace V := fun v hv => hU v (hVU hv)
  obtain ⟨u₁, b_rest, hu₁d, hv₁V, hb_rest, hspanV⟩ := basis_split_var hV_lin hV_dim hx
  let φ : U →ₗ[K] K :=
    { toFun u := u.1.coeff {x}
      map_add' u v := rfl
      map_smul' c u := rfl }
  have hv₁U : u₁ + X x ∈ U := hVU hv₁V
  have hv₁c : (u₁ + X x).coeff {x} = 1 := by
    have hu₁x : u₁.coeff {x} = 0 := by simpa using congrArg (fun z => z.coeff ∅) hu₁d
    rw [add_coeff, hu₁x, zero_add, X_coeff, if_pos rfl]
  have hφ_surj : Function.Surjective φ := by
    intro c
    refine ⟨c • ⟨u₁ + X x, hv₁U⟩, ?_⟩
    change (c • (u₁ + X x)).coeff {x} = c
    rw [smul_coeff, hv₁c, mul_one]
  have hker_dim : Module.finrank K (LinearMap.ker φ) = m + 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hφ_surj
    rw [hrange, finrank_top, Module.finrank_self, hm] at h1
    omega
  let U₀ : Submodule K (SqFreeAlg ι K) := (LinearMap.ker φ).map U.subtype
  have hU₀_dim : Module.finrank K U₀ = m + 1 := by
    rw [Submodule.finrank_map_subtype_eq, hker_dim]
  have hU₀U : U₀ ≤ U := Submodule.map_subtype_le U (LinearMap.ker φ)
  let V₀ : Submodule K (SqFreeAlg ι K) := U₀ ⊓ V
  have hsup_eq : U₀ ⊔ V = U := by
    apply le_antisymm (sup_le hU₀U hVU)
    intro u huU
    let r : SqFreeAlg ι K := u - u.coeff {x} • (u₁ + X x)
    have hrU : r ∈ U := U.sub_mem huU (U.smul_mem _ hv₁U)
    have hrU₀ : r ∈ U₀ := by
      rw [Submodule.mem_map]
      refine ⟨⟨r, hrU⟩, ?_, rfl⟩
      change (u - u.coeff {x} • (u₁ + X x)).coeff {x} = 0
      rw [sub_coeff, smul_coeff, hv₁c, mul_one, sub_self]
    have hu_eq : u = r + u.coeff {x} • (u₁ + X x) := by simp [r]
    rw [hu_eq]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hrU₀)
      (Submodule.mem_sup_right (V.smul_mem _ hv₁V))
  have hV₀_dim : Module.finrank K V₀ = m := by
    have hadd := Submodule.finrank_sup_add_finrank_inf_eq U₀ V
    rw [hsup_eq, hm, hU₀_dim, hV_dim] at hadd
    change m + 2 + Module.finrank K V₀ = m + 1 + (m + 1) at hadd
    omega
  have hne : V₀ ≠ U₀ := by
    intro h
    rw [h, hU₀_dim] at hV₀_dim
    omega
  obtain ⟨u_last, hu_lastU₀, hu_lastV₀⟩ : ∃ u ∈ U₀, u ∉ V₀ := by
    by_contra h
    push Not at h
    exact hne (le_antisymm inf_le_left h)
  have hu_lastU : u_last ∈ U := hU₀U hu_lastU₀
  have hu_lastV : u_last ∉ V := fun hv => hu_lastV₀ ⟨hu_lastU₀, hv⟩
  have hu_last_deriv : deriv x u_last = 0 := by
    rw [Submodule.mem_map] at hu_lastU₀
    rcases hu_lastU₀ with ⟨y, hy, rfl⟩
    have hy0 : y.1.coeff {x} = 0 := hy
    have hd := deriv_isHomog_one x (hU y.1 y.2)
    change deriv x y.1 = 0
    rw [hd, hy0, map_zero]
  refine ⟨u₁, b_rest, u_last, hu₁d, hv₁V, hb_rest, hspanV, hu_lastU, hu_lastV, hu_last_deriv, ?_⟩
  let bV : Fin (m + 1) → SqFreeAlg ι K := Fin.cons (u₁ + X x) b_rest
  have hspan_sup : Submodule.span K (Set.range (Fin.snoc bV u_last)) = V ⊔ Submodule.span K {u_last} := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      induction i using Fin.lastCases with
      | last =>
        rw [Fin.snoc_last]
        exact Submodule.mem_sup_right (Submodule.subset_span rfl)
      | cast j =>
        rw [Fin.snoc_castSucc]
        exact Submodule.mem_sup_left (hspanV ▸ Submodule.subset_span ⟨j, rfl⟩)
    · refine sup_le ?_ ?_
      · rw [← hspanV, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact Submodule.subset_span ⟨Fin.castSucc j, by simp [bV]⟩
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.subset_span ⟨Fin.last (m + 1), by simp⟩
  rw [hspan_sup]
  have hdisj : Disjoint V (Submodule.span K {u_last}) := by
    rw [disjoint_iff]
    ext z
    simp only [Submodule.mem_inf, Submodule.mem_bot, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨hzV, c, rfl⟩
      by_cases hc : c = 0
      · simp [hc]
      · exfalso; apply hu_lastV
        have := V.smul_mem c⁻¹ hzV
        rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    · rintro rfl; exact ⟨V.zero_mem, 0, by simp⟩
  have hu_ne0 : u_last ≠ 0 := fun h => hu_lastV (h ▸ V.zero_mem)
  have hsup_dim : Module.finrank K ↥(V ⊔ Submodule.span K {u_last}) = m + 2 := by
    have hadd := Submodule.finrank_sup_add_finrank_inf_eq V (Submodule.span K {u_last})
    rw [hdisj.eq_bot, finrank_bot, add_zero, hV_dim, finrank_span_singleton hu_ne0] at hadd
    exact hadd
  exact Submodule.eq_of_le_of_finrank_eq (sup_le hVU (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hu_lastU)))
    (by rw [hsup_dim, hm])

lemma elim_inj_of_ms1_ge_two {U : Submodule K (SqFreeAlg ι K)} (hU : IsLinearSpace U)
    (hms1 : ∀ W : Submodule K (SqFreeAlg ι K), W ≤ U → 1 ≤ Module.finrank K W → 2 ≤ (spaceSupp W).card)
    (x : ι) :
    (∀ u ∈ U, elim x u = 0 → u = 0) ∧
    IsLinearSpace (U.map (elim x)) ∧
    Module.finrank K ↥(U.map (elim x)) = Module.finrank K U ∧
    (∀ a : ℕ → ℕ, Covers U a → Covers (U.map (elim x)) (fun i => a i - 1)) := by
  have hinj : ∀ u ∈ U, elim x u = 0 → u = 0 := by
    intro u huU he0
    by_contra hne
    have hde := decomp_linear x (hU u huU)
    rw [he0, zero_add] at hde
    let W := Submodule.span K {u}
    have hWU : W ≤ U := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr huU)
    have hW1 : Module.finrank K W = 1 := finrank_span_singleton hne
    have hW2 := hms1 W hWU (by omega)
    have hsupp_sub : spaceSupp W ⊆ {x} := by
      intro z hz
      rw [mem_spaceSupp_iff] at hz
      rcases hz with ⟨w, hwW, hwc⟩
      rw [Submodule.mem_span_singleton] at hwW
      rcases hwW with ⟨c, rfl⟩
      rw [hde, smul_smul, smul_coeff, X_coeff] at hwc
      by_cases hzx : z = x
      · exact Finset.mem_singleton.mpr hzx
      · have : ({z} : Finset ι) ≠ {x} := fun h => hzx (Finset.singleton_injective h)
        simp [this] at hwc
    have hcard := Finset.card_le_card hsupp_sub
    simp at hcard
    omega
  have hlin' : IsLinearSpace (U.map (elim x)) := by
    rintro _ ⟨u, hu, rfl⟩
    exact isHomog_elim x (hU u hu)
  have hker_bot : LinearMap.ker ((elim x).comp U.subtype) = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨u, huU⟩ hu0
    rw [Submodule.mem_bot]
    ext
    exact congrArg Subtype.val (Subtype.ext (hinj u huU hu0))
  have hmap_eq : U.map (elim x) = LinearMap.range ((elim x).comp U.subtype) := by
    ext z
    simp [Submodule.mem_map, LinearMap.mem_range]
  have hdim' : Module.finrank K ↥(U.map (elim x)) = Module.finrank K U := by
    rw [hmap_eq]
    have h1 := LinearMap.finrank_range_add_finrank_ker ((elim x).comp U.subtype)
    rw [hker_bot, finrank_bot, add_zero] at h1
    exact h1
  refine ⟨hinj, hlin', hdim', ?_⟩
  intro a hUa W' hW'U' hW'1
  let W : Submodule K (SqFreeAlg ι K) := W'.comap (elim x) ⊓ U
  have hWU : W ≤ U := inf_le_right
  have hWmap : W.map (elim x) = W' := by
    apply le_antisymm
    · rintro _ ⟨w, ⟨hw1, _⟩, rfl⟩; exact hw1
    · intro w' hw'
      have hw'U' : w' ∈ U.map (elim x) := hW'U' hw'
      rw [Submodule.mem_map] at hw'U'
      rcases hw'U' with ⟨w, hwU, rfl⟩
      exact ⟨w, ⟨hw', hwU⟩, rfl⟩
  have hW_dim : Module.finrank K W = Module.finrank K W' := by
    have hkerW : LinearMap.ker ((elim x).comp W.subtype) = ⊥ := by
      rw [eq_bot_iff]
      rintro ⟨w, hwW⟩ hw0
      rw [Submodule.mem_bot]
      exact Subtype.ext (hinj w (hWU hwW) hw0)
    have hrangeW : W.map (elim x) = LinearMap.range ((elim x).comp W.subtype) := by
      ext z; simp [Submodule.mem_map, LinearMap.mem_range]
    have h1 := LinearMap.finrank_range_add_finrank_ker ((elim x).comp W.subtype)
    rw [hkerW, finrank_bot, add_zero, ← hrangeW, hWmap] at h1
    exact h1.symm
  have hWcov := hUa W hWU (by omega)
  rw [hW_dim] at hWcov
  have hsub : spaceSupp W ⊆ insert x (spaceSupp W') := by
    intro z hz
    rw [mem_spaceSupp_iff] at hz
    rcases hz with ⟨w, hwW, hwc⟩
    by_cases hzx : z = x
    · subst hzx; exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rw [mem_spaceSupp_iff]
      refine ⟨elim x w, hWmap ▸ Submodule.mem_map_of_mem hwW, ?_⟩
      have hnot : x ∉ ({z} : Finset ι) := fun h => hzx (Finset.mem_singleton.mp h).symm
      simpa [hnot] using hwc
  have hcard_le : (spaceSupp W).card ≤ (spaceSupp W').card + 1 :=
    (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  dsimp only
  omega

end SplitAndElim

section Theorem7

def PropA (K : Type*) [Field K] (n k : ℕ) : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (U : Submodule K (SqFreeAlg ι K)),
    IsLinearSpace U → Module.finrank K U = n → Covers U (fun i => 4 * i - 2 + 2 * k) →
    ∀ (b : Fin n → SqFreeAlg ι K), Submodule.span K (Set.range b) = U →
    ∀ f : SqFreeAlg ι K, IsHomog k f → f * ∏ j : Fin n, (b j) ^ 2 = 0 →
    f ∈ Ideal.span (U : Set (SqFreeAlg ι K))

def PropB (K : Type*) [Field K] (n k : ℕ) : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (U : Submodule K (SqFreeAlg ι K)),
    IsLinearSpace U → Module.finrank K U = n → Covers U (fun i => 4 * i - 3 + 2 * k) →
    ∀ (b : Fin n → SqFreeAlg ι K), Submodule.span K (Set.range b) = U →
    ∀ f : SqFreeAlg ι K, IsHomog (2 * n - 2 + k) f → (∀ u ∈ U, f * u = 0) →
    (k < 2 → f = 0) ∧ (2 ≤ k → ∃ d : SqFreeAlg ι K, IsHomog (k - 2) d ∧ f = d * ∏ j : Fin n, (b j) ^ 2)

private lemma thm7_base {K : Type*} [Field K] [CharP K 3] (k : ℕ) :
    PropB K 1 k ∧ PropA K 1 k := by
  constructor
  · intro ι _ _ U hU hdim hcov b hb f hf hfu
    have huU : b 0 ∈ U := hb ▸ Submodule.subset_span ⟨0, rfl⟩
    have hu_lin : IsHomog 1 (b 0) := hU (b 0) huU
    have hu_ne : b 0 ≠ 0 := by
      intro h0
      have hbot : U = ⊥ := by
        rw [← hb, Submodule.span_eq_bot]
        rintro _ ⟨j, rfl⟩
        fin_cases j; exact h0
      rw [hbot, finrank_bot] at hdim
      omega
    have hU_eq : U = Submodule.span K {b 0} := by
      rw [← hb]
      congr 1
      ext x
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨j, rfl⟩; fin_cases j; rfl
      · rintro rfl; exact ⟨0, rfl⟩
    have hsupp_eq : spaceSupp U = supp (b 0) := by
      ext z
      rw [mem_spaceSupp_iff, mem_supp_iff]
      constructor
      · rintro ⟨w, hw, hwc⟩
        rw [hU_eq, Submodule.mem_span_singleton] at hw
        rcases hw with ⟨c, rfl⟩
        rw [smul_coeff] at hwc
        exact fun h0 => hwc (by simp [h0])
      · intro h0; exact ⟨b 0, huU, h0⟩
    have hcov1 := hcov U le_rfl (by omega)
    rw [hdim, hsupp_eq] at hcov1
    have hcard : 2 * k + 1 ≤ (supp (b 0)).card := by dsimp only at hcov1; omega
    have hf' : IsHomog k f := by rwa [show 2 * 1 - 2 + k = k by omega] at hf
    obtain ⟨h1, h2⟩ := thm5_1 hu_lin hcard hf' (hfu (b 0) huU)
    refine ⟨h1, fun hk => ?_⟩
    obtain ⟨d, hd, hfd⟩ := h2 hk
    exact ⟨d, hd, by simpa using hfd⟩
  · intro ι _ _ U hU hdim hcov b hb f hf hfb
    have huU : b 0 ∈ U := hb ▸ Submodule.subset_span ⟨0, rfl⟩
    have hu_lin : IsHomog 1 (b 0) := hU (b 0) huU
    have hU_eq : U = Submodule.span K {b 0} := by
      rw [← hb]
      congr 1
      ext x
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨j, rfl⟩; fin_cases j; rfl
      · rintro rfl; exact ⟨0, rfl⟩
    have hsupp_eq : spaceSupp U = supp (b 0) := by
      ext z
      rw [mem_spaceSupp_iff, mem_supp_iff]
      constructor
      · rintro ⟨w, hw, hwc⟩
        rw [hU_eq, Submodule.mem_span_singleton] at hw
        rcases hw with ⟨c, rfl⟩
        rw [smul_coeff] at hwc
        exact fun h0 => hwc (by simp [h0])
      · intro h0; exact ⟨b 0, huU, h0⟩
    have hcov1 := hcov U le_rfl (by omega)
    rw [hdim, hsupp_eq] at hcov1
    have hcard : 2 * k + 2 ≤ (supp (b 0)).card := by dsimp only at hcov1; omega
    have hfb' : f * (b 0) ^ 2 = 0 := by simpa using hfb
    have hmem := thm5_2 hu_lin hcard hf hfb'
    have hspan_sub : Ideal.span ({b 0} : Set (SqFreeAlg ι K)) ≤ Ideal.span (U : Set (SqFreeAlg ι K)) :=
      Ideal.span_mono (Set.singleton_subset_iff.mpr huU)
    exact hspan_sub hmem

private lemma thm7_A_imp_B {K : Type*} [Field K] [CharP K 3] [Infinite K] (m k : ℕ)
    (ih : ∀ j, PropB K (m + 1) j ∧ PropA K (m + 1) j)
    (hA : k = 0 ∨ (0 < k ∧ PropA K (m + 2) (k - 1))) :
    PropB K (m + 2) k := by
  intro ι _ _ U hU hdim hcov b hb f hf hfu
  have ha_mono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ m + 2 →
      4 * i - 3 + 2 * k ≤ 4 * j - 3 + 2 * k := fun i j hi hij _ => by omega
  obtain ⟨V, hVU, hV_dim, hV_cov⟩ := lemma6_aux hU hdim (fun i => 4 * i - 3 + 2 * k) ha_mono hcov (m + 1) (by omega)
  have hV_lin : IsLinearSpace V := fun v hv => hU v (hVU hv)
  have hV_ne_bot : V ≠ ⊥ := fun h => by
    have h1 := hV_dim
    rw [h, finrank_bot] at h1
    omega
  obtain ⟨v₀, hv₀V, hv₀_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV_ne_bot
  obtain ⟨x, hx_supp⟩ := supp_nonempty_of_ne_zero (hV_lin v₀ hv₀V) hv₀_ne
  have hxV : x ∈ spaceSupp V := supp_subset_spaceSupp hv₀V hx_supp
  obtain ⟨u₁, b_rest, u_last, hu₁d, hv₁V, hb_rest, hspanV, hu_lastU, hu_lastV, hu_last_deriv, hspanU⟩ :=
    basis_split_subspace hU hdim hVU hV_dim hxV
  let bV : Fin (m + 1) → SqFreeAlg ι K := Fin.cons (u₁ + X x) b_rest
  let b_spec : Fin (m + 2) → SqFreeAlg ι K := Fin.snoc bV u_last
  have hbV_lin : ∀ j, IsHomog 1 (bV j) := fun j => by
    refine Fin.cases (hV_lin _ hv₁V) (fun j' => hV_lin _ (hb_rest j').1) j
  have hV_cov_B : Covers V (fun i => 4 * i - 3 + 2 * (k + 2)) := by
    refine covers_mono hV_cov fun i hi _ => ?_
    omega
  have hV_cov_A : Covers V (fun i => 4 * i - 2 + 2 * (k + 1)) := by
    refine covers_mono hV_cov fun i hi _ => ?_
    omega
  have hf_hom' : IsHomog (2 * (m + 1) - 2 + (k + 2)) f := by
    rwa [show 2 * (m + 1) - 2 + (k + 2) = 2 * (m + 2) - 2 + k by omega]
  obtain ⟨hB_prev, _⟩ := ih (k + 2)
  have ⟨_, hB_prev'⟩ := hB_prev V hV_lin hV_dim hV_cov_B bV hspanV f hf_hom'
    (fun u hu => hfu u (hVU hu))
  obtain ⟨g, hg, hfg⟩ := hB_prev' (by omega)
  rw [show k + 2 - 2 = k by omega] at hg
  let g' := rem (u₁ + X x) x g
  have hg'_hom : IsHomog k g' := isHomog_rem x (hV_lin _ hv₁V) g hg
  have hg'_deriv : deriv x g' = 0 := deriv_rem x g
  have hv₁c : (u₁ + X x).coeff {x} = 1 := by
    have : (deriv x (u₁ + X x)).coeff ∅ = 1 := by simp [hu₁d, deriv_X_self]
    simpa using this
  have hfg' : f = g' * ∏ j : Fin (m + 1), (bV j) ^ 2 := by
    have hdiff := sub_rem x (hV_lin _ hv₁V) (by rw [hv₁c]; exact one_ne_zero) g
    have hkill : (g - g') * ∏ j : Fin (m + 1), (bV j) ^ 2 = 0 := by
      have hprod_split : ∏ j : Fin (m + 1), (bV j) ^ 2 =
          (u₁ + X x) ^ 2 * ∏ j : Fin m, (b_rest j) ^ 2 := by
        rw [Fin.prod_univ_succ]
        rfl
      have hcube : (u₁ + X x) ^ 3 = 0 := linear_cube_eq_zero (hV_lin _ hv₁V)
      calc (g - g') * ∏ j : Fin (m + 1), (bV j) ^ 2
          = ((u₁ + X x).coeff {x})⁻¹ • (deriv x g * (u₁ + X x)) *
              ((u₁ + X x) ^ 2 * ∏ j : Fin m, (b_rest j) ^ 2) := by rw [hdiff, hprod_split]
        _ = ((u₁ + X x).coeff {x})⁻¹ • (deriv x g * ((u₁ + X x) ^ 3 * ∏ j : Fin m, (b_rest j) ^ 2)) := by
            rw [Algebra.smul_mul_assoc]; congr 1; ring
        _ = 0 := by rw [hcube, zero_mul, mul_zero, smul_zero]
    have : f - g' * ∏ j : Fin (m + 1), (bV j) ^ 2 = 0 := by
      calc f - g' * ∏ j : Fin (m + 1), (bV j) ^ 2
          = (g - g') * ∏ j : Fin (m + 1), (bV j) ^ 2 := by rw [hfg]; ring
        _ = 0 := hkill
    exact sub_eq_zero.mp this
  have hgul_zero : (g' * u_last) * ∏ j : Fin (m + 1), (bV j) ^ 2 = 0 := by
    calc (g' * u_last) * ∏ j : Fin (m + 1), (bV j) ^ 2
        = (g' * ∏ j : Fin (m + 1), (bV j) ^ 2) * u_last := by ring
      _ = f * u_last := by rw [← hfg']
      _ = 0 := hfu u_last hu_lastU
  have hgul_hom : IsHomog (k + 1) (g' * u_last) :=
    isHomog_mul hg'_hom (hU u_last hu_lastU)
  have hgul_ideal : g' * u_last ∈ Ideal.span (V : Set (SqFreeAlg ι K)) :=
    (ih (k + 1)).2 V hV_lin hV_dim hV_cov_A bV hspanV (g' * u_last) hgul_hom hgul_zero
  rcases hA with rfl | ⟨hk_pos, hA_prev⟩
  · -- Case `k = 0`
    obtain ⟨_, hdecomp⟩ := ideal_homog_decomp hV_lin hspanV hgul_ideal (k := 0)
    obtain ⟨a, ha0, hsum⟩ := hdecomp hgul_hom
    have hgu_eq : g'.coeff ∅ • u_last = ∑ j : Fin (m + 1), (a j).coeff ∅ • bV j := by
      have hg'0 := isHomog_zero_eq_algebraMap hg'_hom
      rw [hg'0, ← Algebra.smul_def] at hsum
      rw [hsum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have haj := isHomog_zero_eq_algebraMap (ha0 j)
      conv_lhs => rw [haj, ← Algebra.smul_def]
    have hmemV : g'.coeff ∅ • u_last ∈ V := by
      rw [hgu_eq]
      refine V.sum_mem fun j _ => V.smul_mem _ ?_
      exact hspanV ▸ Submodule.subset_span ⟨j, rfl⟩
    have hc0 : g'.coeff ∅ = 0 := by
      by_contra hne
      apply hu_lastV
      have := V.smul_mem (g'.coeff ∅)⁻¹ hmemV
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
    have hg'0 : g' = 0 := by
      rw [isHomog_zero_eq_algebraMap hg'_hom, hc0, map_zero]
    have hf0 : f = 0 := by rw [hfg', hg'0, zero_mul]
    exact ⟨fun _ => hf0, fun h => by omega⟩
  · -- Case `k ≥ 1`
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk_pos.ne'
    obtain ⟨_, hdecomp⟩ := ideal_homog_decomp hV_lin hspanV hgul_ideal (k := k' + 1)
    obtain ⟨a, ha_hom, hsum⟩ := hdecomp (by simpa using hgul_hom)
    have heu₁ : elim x u₁ = u₁ := by
      have := decomp x u₁
      rw [hu₁d, zero_mul, add_zero] at this
      exact this.symm
    have heu_last : elim x u_last = u_last := by
      have := decomp x u_last
      rw [hu_last_deriv, zero_mul, add_zero] at this
      exact this.symm
    have heb_rest : ∀ j, elim x (b_rest j) = b_rest j := fun j => by
      have := decomp x (b_rest j)
      rw [(hb_rest j).2, zero_mul, add_zero] at this
      exact this.symm
    have heg' : elim x g' = g' := by
      have := decomp x g'
      rw [hg'_deriv, zero_mul, add_zero] at this
      exact this.symm
    have hsum_split : g' * u_last = a 0 * (u₁ + X x) + ∑ j : Fin m, a (Fin.succ j) * b_rest j := by
      rw [hsum, Fin.sum_univ_succ]
      rfl
    have hE := congrArg (elim x) hsum_split
    simp only [elim_mul, map_add, heg', heu_last, map_sum, heu₁, elim_X_self, add_zero, heb_rest] at hE
    have hD := congrArg (deriv x) hsum_split
    simp only [deriv_mul, map_add, hg'_deriv, zero_mul, heg', hu_last_deriv, mul_zero, add_zero,
      heu₁, elim_X_self, deriv_isHomog_one x (hV_lin _ hv₁V), hv₁c, map_one, mul_one,
      map_sum, (hb_rest _).2, heb_rest] at hD
    -- From `hD`: `0 = elim x (a 0) + deriv x (a 0) * u₁ + ∑ j, deriv x (a (Fin.succ j)) * b_rest j`.
    -- Multiply `hD` by `u₁` and subtract from `hE`:
    have hcomb : g' * u_last + deriv x (a 0) * u₁ ^ 2 =
        ∑ j : Fin m, (elim x (a (Fin.succ j)) - deriv x (a (Fin.succ j)) * u₁) * b_rest j := by
      have hDu₁ := congrArg (fun z => z * u₁) hD
      simp only [zero_mul, add_mul, Finset.sum_mul] at hDu₁
      calc g' * u_last + deriv x (a 0) * u₁ ^ 2
          = (elim x (a 0) * u₁ + ∑ j : Fin m, elim x (a (Fin.succ j)) * b_rest j) +
              deriv x (a 0) * u₁ ^ 2 := by rw [hE]
        _ = (elim x (a 0) * u₁ + deriv x (a 0) * u₁ ^ 2 +
              ∑ j : Fin m, deriv x (a (Fin.succ j)) * b_rest j * u₁) +
            ∑ j : Fin m, (elim x (a (Fin.succ j)) - deriv x (a (Fin.succ j)) * u₁) * b_rest j := by
              have hsum_eq : ∑ j : Fin m, (elim x (a (Fin.succ j)) - deriv x (a (Fin.succ j)) * u₁) * b_rest j =
                  (∑ j : Fin m, elim x (a (Fin.succ j)) * b_rest j) -
                  (∑ j : Fin m, deriv x (a (Fin.succ j)) * b_rest j * u₁) := by
                rw [← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl fun j _ => ?_
                ring
              rw [hsum_eq]
              ring
        _ = 0 + ∑ j : Fin m, (elim x (a (Fin.succ j)) - deriv x (a (Fin.succ j)) * u₁) * b_rest j := by
              rw [show elim x (a 0) * u₁ + deriv x (a 0) * u₁ ^ 2 +
                ∑ j : Fin m, deriv x (a (Fin.succ j)) * b_rest j * u₁ =
                (deriv x (a 0) * u₁ + elim x (a 0) +
                  ∑ j : Fin m, deriv x (a (Fin.succ j)) * b_rest j) * u₁ by
                rw [add_mul, add_mul, Finset.sum_mul, mul_assoc (deriv x (a 0)), ← sq,
                  add_comm (deriv x (a 0) * u₁ ^ 2) _]]
              rw [← hD, zero_mul]
        _ = ∑ j : Fin m, (elim x (a (Fin.succ j)) - deriv x (a (Fin.succ j)) * u₁) * b_rest j := by
              rw [zero_add]
    have hsum_kill : (∑ j : Fin m, (elim x (a (Fin.succ j)) - deriv x (a (Fin.succ j)) * u₁) * b_rest j) *
        ∏ j : Fin m, (b_rest j) ^ 2 = 0 := by
      rw [Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro j _
      have hsplit : ∏ i : Fin m, (b_rest i) ^ 2 =
          (b_rest j) ^ 2 * ∏ i ∈ Finset.univ.erase j, (b_rest i) ^ 2 :=
        (Finset.mul_prod_erase Finset.univ (fun i => (b_rest i) ^ 2) (Finset.mem_univ j)).symm
      have hcube : (b_rest j) ^ 3 = 0 := linear_cube_eq_zero (hV_lin _ (hb_rest j).1)
      calc (elim x (a (Fin.succ j)) - deriv x (a (Fin.succ j)) * u₁) * b_rest j *
            ∏ i : Fin m, (b_rest i) ^ 2
          = (elim x (a (Fin.succ j)) - deriv x (a (Fin.succ j)) * u₁) *
              ((b_rest j) ^ 3 * ∏ i ∈ Finset.univ.erase j, (b_rest i) ^ 2) := by
            rw [hsplit]; ring
        _ = 0 := by rw [hcube, zero_mul, mul_zero]
    -- Also `g' * u_last * u_last^2 = 0`, so multiplying `hcomb` by `(∏ j, (b_rest j)^2) * u_last^2`:
    let U' := U.map (elim x)
    have hms1 : ∀ W ≤ U, 1 ≤ Module.finrank K W → 2 ≤ (spaceSupp W).card := by
      intro W hWU hW1
      have := hcov W hWU hW1
      dsimp only at this
      omega
    obtain ⟨_, hU'_lin, hU'_dim, hU'_cov⟩ := elim_inj_of_ms1_ge_two hU hms1 x
    have hU'_cov_A : Covers U' (fun i => 4 * i - 2 + 2 * k') := by
      have hc := hU'_cov (fun i => 4 * i - 3 + 2 * (k' + 1)) hcov
      refine covers_mono hc fun i hi _ => ?_
      omega
    let bU' : Fin (m + 2) → SqFreeAlg ι K := Fin.snoc (Fin.cons u₁ b_rest) u_last
    have hspanU' : Submodule.span K (Set.range bU') = U' := by
      have he_spec : ∀ i : Fin (m + 2), elim x (b_spec i) = bU' i := by
        intro i
        induction i using Fin.lastCases with
        | last => simp [b_spec, bU', heu_last]
        | cast j =>
          simp only [b_spec, bU', Fin.snoc_castSucc]
          refine Fin.cases ?_ ?_ j
          · simp [bV, heu₁, elim_X_self]
          · intro j'; simp [bV, heb_rest]
      dsimp only [U']
      rw [← hspanU, Submodule.map_span]
      congr 1
      ext z
      simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and]
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨i, he_spec i⟩
      · rintro ⟨i, rfl⟩; exact ⟨i, (he_spec i).symm⟩
    have hda0_hom : IsHomog k' (deriv x (a 0)) := isHomog_deriv x (ha_hom 0)
    have hda0_mul : deriv x (a 0) * ∏ i : Fin (m + 2), (bU' i) ^ 2 = 0 := by
      have hprodU' : ∏ i : Fin (m + 2), (bU' i) ^ 2 =
          u₁ ^ 2 * (∏ j : Fin m, (b_rest j) ^ 2) * u_last ^ 2 := by
        dsimp [bU']
        rw [Fin.prod_univ_castSucc, Fin.snoc_last]
        have h1 : ∏ i : Fin (m + 1), (bU' (Fin.castSucc i)) ^ 2 =
            u₁ ^ 2 * ∏ j : Fin m, (b_rest j) ^ 2 := by
          rw [Fin.prod_univ_succ]
          simp only [bU', Fin.snoc_castSucc, Fin.cons_zero, Fin.cons_succ]
        rw [h1]
      have hcomb_mul := congrArg (fun z => z * ((∏ j : Fin m, (b_rest j) ^ 2) * u_last ^ 2)) hcomb
      rw [add_mul, ← mul_assoc (∑ j : Fin m, _), hsum_kill, zero_mul] at hcomb_mul
      have hgu3 : g' * u_last * ((∏ j : Fin m, (b_rest j) ^ 2) * u_last ^ 2) = 0 := by
        have hcube : u_last ^ 3 = 0 := linear_cube_eq_zero (hU u_last hu_lastU)
        calc g' * u_last * ((∏ j : Fin m, (b_rest j) ^ 2) * u_last ^ 2)
            = g' * (∏ j : Fin m, (b_rest j) ^ 2) * u_last ^ 3 := by ring
          _ = 0 := by rw [hcube, mul_zero]
      rw [hgu3, zero_add] at hcomb_mul
      rw [hprodU']
      calc deriv x (a 0) * (u₁ ^ 2 * (∏ j : Fin m, (b_rest j) ^ 2) * u_last ^ 2)
          = deriv x (a 0) * u₁ ^ 2 * ((∏ j : Fin m, (b_rest j) ^ 2) * u_last ^ 2) := by ring
        _ = 0 := hcomb_mul
    have hda0_ideal : deriv x (a 0) ∈ Ideal.span (U' : Set (SqFreeAlg ι K)) :=
      hA_prev U' hU'_lin (hU'_dim.trans hdim) hU'_cov_A bU' hspanU' (deriv x (a 0)) hda0_hom hda0_mul
    obtain ⟨_, hdecomp_da⟩ := ideal_homog_decomp hU'_lin hspanU' hda0_ideal (k := k')
    have hc_decomp : ∃ c : Fin (m + 2) → SqFreeAlg ι K,
        (∀ i, IsHomog (k' - 1) (c i)) ∧
        (k' = 0 → c (Fin.last (m + 1)) = 0) ∧
        deriv x (a 0) = c 0 * u₁ + (∑ j : Fin m, c (Fin.castSucc (Fin.succ j)) * b_rest j) +
          c (Fin.last (m + 1)) * u_last := by
      cases k' with
      | zero =>
        have h0 := (ideal_homog_decomp hU'_lin hspanU' hda0_ideal (k := 0)).1 hda0_hom
        refine ⟨fun _ => 0, fun _ => isHomog_zero 0, fun _ => rfl, ?_⟩
        simp [h0]
      | succ k'' =>
        obtain ⟨c, hc_hom, hc_sum⟩ := (ideal_homog_decomp hU'_lin hspanU' hda0_ideal (k := k'')).2 hda0_hom
        refine ⟨fun i => c i, fun i => by simpa using hc_hom i, fun h => by omega, ?_⟩
        rw [hc_sum]
        have heq : ∑ i : Fin (m + 2), c i * bU' i =
            c 0 * u₁ + (∑ j : Fin m, c (Fin.castSucc (Fin.succ j)) * b_rest j) +
              c (Fin.last (m + 1)) * u_last := by
          rw [Fin.sum_univ_castSucc]
          simp only [bU', Fin.snoc_castSucc, Fin.snoc_last]
          rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero]
        exact heq
    rcases hc_decomp with ⟨c, hc_hom, hcn_zero, hda_eq⟩
    let cn := c (Fin.last (m + 1))
    have hcn_u1_kill : (g' + cn * u₁ ^ 2) * u_last * ∏ j : Fin m, (b_rest j) ^ 2 = 0 := by
      have hcomb2 := congrArg (fun z => z * ∏ j : Fin m, (b_rest j) ^ 2) hcomb
      rw [hsum_kill] at hcomb2
      have hu1_lin : IsHomog 1 u₁ := by
        have h1 := isHomog_elim x (hV_lin _ hv₁V)
        rwa [map_add, elim_X_self, add_zero, heu₁] at h1
      have hu1_cube : u₁ ^ 3 = 0 := linear_cube_eq_zero hu1_lin
      have hda_mul : deriv x (a 0) * u₁ ^ 2 * ∏ j : Fin m, (b_rest j) ^ 2 =
          cn * u₁ ^ 2 * u_last * ∏ j : Fin m, (b_rest j) ^ 2 := by
        rw [hda_eq, add_mul, add_mul, add_mul, add_mul]
        have h1 : c 0 * u₁ * u₁ ^ 2 * ∏ j : Fin m, (b_rest j) ^ 2 = 0 := by
          calc c 0 * u₁ * u₁ ^ 2 * ∏ j : Fin m, (b_rest j) ^ 2
              = c 0 * (u₁ ^ 3 * ∏ j : Fin m, (b_rest j) ^ 2) := by ring
            _ = 0 := by rw [hu1_cube, zero_mul, mul_zero]
        have h2 : (∑ j : Fin m, c (Fin.castSucc (Fin.succ j)) * b_rest j) * u₁ ^ 2 * ∏ j : Fin m, (b_rest j) ^ 2 = 0 := by
          rw [Finset.sum_mul, Finset.sum_mul]
          apply Finset.sum_eq_zero
          intro j _
          have hsplit : ∏ i : Fin m, (b_rest i) ^ 2 =
              (b_rest j) ^ 2 * ∏ i ∈ Finset.univ.erase j, (b_rest i) ^ 2 :=
            (Finset.mul_prod_erase Finset.univ (fun i => (b_rest i) ^ 2) (Finset.mem_univ j)).symm
          have hcube : (b_rest j) ^ 3 = 0 := linear_cube_eq_zero (hV_lin _ (hb_rest j).1)
          calc c (Fin.castSucc (Fin.succ j)) * b_rest j * u₁ ^ 2 * ∏ i : Fin m, (b_rest i) ^ 2
              = c (Fin.castSucc (Fin.succ j)) * u₁ ^ 2 * ((b_rest j) ^ 3 * ∏ i ∈ Finset.univ.erase j, (b_rest i) ^ 2) := by
                rw [hsplit]; ring
            _ = 0 := by rw [hcube, zero_mul, mul_zero]
        rw [h1, h2, zero_add, zero_add]
        ring
      rw [add_mul, hda_mul] at hcomb2
      calc (g' + cn * u₁ ^ 2) * u_last * ∏ j : Fin m, (b_rest j) ^ 2
          = g' * u_last * ∏ j : Fin m, (b_rest j) ^ 2 +
              cn * u₁ ^ 2 * u_last * ∏ j : Fin m, (b_rest j) ^ 2 := by ring
        _ = 0 := hcomb2
    -- Lift to `Option ι` with dummy variable `X none`!
    let y : SqFreeAlg (Option ι) K := X none
    let bY : Fin (m + 1) → SqFreeAlg (Option ι) K :=
      Fin.snoc (fun j => liftOpt (b_rest j)) (liftOpt u_last + y)
    let Y : Submodule K (SqFreeAlg (Option ι) K) := Submodule.span K (Set.range bY)
    have hY_lin : IsLinearSpace Y := by
      intro w hw
      rw [Submodule.mem_span_range_iff_exists_fun] at hw
      rcases hw with ⟨c', rfl⟩
      refine isHomog_sum fun i _ => isHomog_smul _ ?_
      induction i using Fin.lastCases with
      | last =>
        simp only [bY, Fin.snoc_last]
        exact isHomog_add (isHomog_liftOpt (hU u_last hu_lastU)) (isHomog_X none)
      | cast j =>
        simp only [bY, Fin.snoc_castSucc]
        exact isHomog_liftOpt (hV_lin _ (hb_rest j).1)
    have hproj_inj_U : ∀ u ∈ U, u.coeff {x} = 0 → True := fun _ _ _ => trivial
    -- Prove `bY` is linearly independent so `dim Y = m + 1`!
    have hbV_ind : LinearIndependent K bV := by
      have hcard_le := Fintype.card_fin (m + 1)
      exact linearIndependent_iff_card_eq_finrank_span.mpr (by
        change Fintype.card (Fin (m + 1)) = Module.finrank K ↥(Submodule.span K (Set.range bV))
        rw [hspanV, hV_dim, hcard_le])
    have hb_spec_ind : LinearIndependent K b_spec := by
      have hcard_le := Fintype.card_fin (m + 2)
      exact linearIndependent_iff_card_eq_finrank_span.mpr (by
        change Fintype.card (Fin (m + 2)) = Module.finrank K ↥(Submodule.span K (Set.range b_spec))
        rw [hspanU, hdim, hcard_le])
    have hbY_ind : LinearIndependent K bY := by
      rw [Fintype.linearIndependent_iff]
      intro c' hc'
      have hproj := congrArg projOpt hc'
      simp only [map_sum, map_smul, map_zero, bY] at hproj
      rw [Fin.sum_univ_castSucc] at hproj
      simp only [y, Fin.snoc_castSucc, Fin.snoc_last, map_add, projOpt_liftOpt, projOpt_X_none, add_zero] at hproj
      have hc_spec : ∑ i : Fin (m + 2),
          ((Fin.snoc (Fin.cons (0 : K) (fun j => c' (Fin.castSucc j)) : Fin (m + 1) → K)
            (c' (Fin.last m)) : Fin (m + 2) → K) i) • b_spec i = 0 := by
        rw [Fin.sum_univ_castSucc, Fin.snoc_last]
        simp only [b_spec, Fin.snoc_castSucc, Fin.snoc_last, Fin.sum_univ_succ, bV, Fin.cons_zero, Fin.cons_succ,
          zero_smul, zero_add]
        exact hproj
      have hall := (Fintype.linearIndependent_iff.mp hb_spec_ind) _ hc_spec
      intro i
      induction i using Fin.lastCases with
      | last =>
        have := hall (Fin.last (m + 1))
        simpa [Fin.snoc_last] using this
      | cast j =>
        have h1 := hall (Fin.castSucc (Fin.succ j))
        rw [Fin.snoc_castSucc, Fin.cons_succ] at h1
        exact h1
    have hY_dim : Module.finrank K Y = m + 1 := by
      rw [finrank_span_eq_card hbY_ind, Fintype.card_fin]
    -- Show `Covers Y (fun i => 4 * i - 2 + 2 * (k' + 1))`!
    have hY_cov : Covers Y (fun i => 4 * i - 2 + 2 * (k' + 1)) := by
      intro I hIY hI1
      let I0 : Submodule K (SqFreeAlg ι K) := I.map projOpt.toLinearMap
      have hI0U : I0 ≤ U := by
        rintro _ ⟨w, hwI, rfl⟩
        have hwY : w ∈ Y := hIY hwI
        rw [Submodule.mem_span_range_iff_exists_fun] at hwY
        rcases hwY with ⟨c', rfl⟩
        simp only [AlgHom.toLinearMap_apply, map_sum, map_smul, bY]
        refine U.sum_mem fun i _ => U.smul_mem _ ?_
        induction i using Fin.lastCases with
        | last =>
          simp only [y, Fin.snoc_last, map_add, projOpt_liftOpt, projOpt_X_none, add_zero]
          exact hu_lastU
        | cast j =>
          simp only [Fin.snoc_castSucc, projOpt_liftOpt]
          exact hVU (hb_rest j).1
      -- Check `projOpt` is injective on `Y`:
      have hproj_inj_Y : ∀ w ∈ Y, projOpt w = 0 → w = 0 := by
        intro w hwY hpw
        rw [Submodule.mem_span_range_iff_exists_fun] at hwY
        rcases hwY with ⟨c', rfl⟩
        have hproj : ∑ i : Fin (m + 1), c' i • projOpt (bY i) = 0 := by
          simpa [map_sum, map_smul] using hpw
        have hc_spec : ∑ i : Fin (m + 2),
            ((Fin.snoc (Fin.cons (0 : K) (fun j => c' (Fin.castSucc j)) : Fin (m + 1) → K)
              (c' (Fin.last m)) : Fin (m + 2) → K) i) • b_spec i = 0 := by
          rw [Fin.sum_univ_castSucc, Fin.snoc_last]
          simp only [b_spec, Fin.snoc_castSucc, Fin.sum_univ_succ, bV, Fin.cons_zero, Fin.cons_succ,
            zero_smul, zero_add]
          rw [Fin.sum_univ_castSucc] at hproj
          simpa [bY, y] using hproj
        have hall := (Fintype.linearIndependent_iff.mp hb_spec_ind) _ hc_spec
        apply Finset.sum_eq_zero
        intro i _
        induction i using Fin.lastCases with
        | last =>
          have := hall (Fin.last (m + 1))
          simp only [Fin.snoc_last] at this
          simp [this]
        | cast j =>
          have := hall (Fin.castSucc (Fin.succ j))
          simp only [Fin.snoc_castSucc, Fin.cons_succ] at this
          simp [this]
      have hI0_dim : Module.finrank K I0 = Module.finrank K I := by
        have hker : LinearMap.ker (projOpt.toLinearMap.comp I.subtype) = ⊥ := by
          rw [eq_bot_iff]
          rintro ⟨w, hwI⟩ hw0
          rw [Submodule.mem_bot]
          exact Subtype.ext (hproj_inj_Y w (hIY hwI) hw0)
        have hrange : I0 = LinearMap.range (projOpt.toLinearMap.comp I.subtype) := by
          ext z; simp [I0, Submodule.mem_map, LinearMap.mem_range]
        rw [hrange]
        have h1 := LinearMap.finrank_range_add_finrank_ker (projOpt.toLinearMap.comp I.subtype)
        rw [hker, finrank_bot, add_zero] at h1
        exact h1
      by_cases hnone : (none : Option ι) ∈ spaceSupp I
      · have hsub_supp : (spaceSupp I0).map ⟨some, Option.some_injective ι⟩ ⊆ spaceSupp I := by
          intro z hz
          rw [Finset.mem_map] at hz
          rcases hz with ⟨a, ha, rfl⟩
          rw [mem_spaceSupp_iff] at ha ⊢
          rcases ha with ⟨w0, hw0, hac⟩
          rcases hw0 with ⟨w, hwI, rfl⟩
          refine ⟨w, hwI, ?_⟩
          simpa [projOpt] using hac
        have hnot_none : none ∉ (spaceSupp I0).map ⟨some, Option.some_injective ι⟩ := by simp
        have hcard_I0 : (spaceSupp I0).card + 1 ≤ (spaceSupp I).card := by
          have hsub_ins : insert none ((spaceSupp I0).map ⟨some, Option.some_injective ι⟩) ⊆ spaceSupp I :=
            Finset.insert_subset_iff.mpr ⟨hnone, hsub_supp⟩
          have hcard := Finset.card_le_card hsub_ins
          rw [Finset.card_insert_of_notMem hnot_none, Finset.card_map] at hcard
          exact hcard
        have hcov_I0 := hcov I0 hI0U (by omega)
        rw [hI0_dim] at hcov_I0
        dsimp only at hcov_I0 ⊢
        omega
      · -- `none ∉ spaceSupp I`, so every `w ∈ I` has `none`-coeff `0`, hence `I0 ≤ V`!
        have hI0V : I0 ≤ V := by
          rintro _ ⟨w, hwI, rfl⟩
          have hwY : w ∈ Y := hIY hwI
          rw [Submodule.mem_span_range_iff_exists_fun] at hwY
          rcases hwY with ⟨c', rfl⟩
          have hc_none : (∑ i : Fin (m + 1), c' i • bY i).coeff {none} = 0 := by
            by_contra hc
            apply hnone
            rw [mem_spaceSupp_iff]
            exact ⟨_, hwI, hc⟩
          have hlast0 : c' (Fin.last m) = 0 := by
            have hsum_coeff : (∑ i : Fin (m + 1), c' i • bY i).coeff {none} =
                ∑ i : Fin (m + 1), c' i * (bY i).coeff {none} := by
              clear hc_none hwI
              induction (Finset.univ : Finset (Fin (m + 1))) using Finset.induction with
              | empty => simp
              | insert a s ha ih =>
                rw [Finset.sum_insert ha, add_coeff, Finset.sum_insert ha, ih, smul_coeff]
            rw [hsum_coeff, Fin.sum_univ_castSucc] at hc_none
            have hzero_cast : ∑ j : Fin m, c' (Fin.castSucc j) * (bY (Fin.castSucc j)).coeff {none} = 0 := by
              apply Finset.sum_eq_zero
              intro j _
              simp [bY, liftOpt]
            have hlast_one : (bY (Fin.last m)).coeff {none} = 1 := by
              simp [bY, y, liftOpt]
            rw [hzero_cast, zero_add, hlast_one, mul_one] at hc_none
            exact hc_none
          simp only [AlgHom.toLinearMap_apply, map_sum, map_smul, bY]
          rw [Fin.sum_univ_castSucc, hlast0, zero_smul, add_zero]
          refine V.sum_mem fun j _ => V.smul_mem _ ?_
          simp only [Fin.snoc_castSucc, projOpt_liftOpt]
          exact (hb_rest j).1
        have hsub_supp : (spaceSupp I0).map ⟨some, Option.some_injective ι⟩ ⊆ spaceSupp I := by
          intro z hz
          rw [Finset.mem_map] at hz
          rcases hz with ⟨a, ha, rfl⟩
          rw [mem_spaceSupp_iff] at ha ⊢
          rcases ha with ⟨w0, hw0, hac⟩
          rcases hw0 with ⟨w, hwI, rfl⟩
          refine ⟨w, hwI, ?_⟩
          simpa [projOpt] using hac
        have hcov_I0 := hV_cov I0 hI0V (by omega)
        rw [hI0_dim] at hcov_I0
        have hcard := (Finset.card_map ⟨some, Option.some_injective ι⟩).symm.le.trans (Finset.card_le_card hsub_supp)
        dsimp only at hcov_I0 ⊢
        omega
    -- Apply `PropA (m + 1) (k' + 1)` to `Y`!
    have hY_hom : IsHomog (k' + 1) (liftOpt (g' + cn * u₁ ^ 2)) := by
      refine isHomog_liftOpt (isHomog_add hg'_hom ?_)
      have hcn_hom : IsHomog (k' - 1) cn := by
        cases k' with
        | zero => dsimp only [cn]; rw [hcn_zero rfl]; exact isHomog_zero 0
        | succ k'' => exact hc_hom (Fin.last (m + 1))
      have hu1_sq_hom : IsHomog 2 (u₁ ^ 2) := by
        rw [sq]
        have hu1_lin : IsHomog 1 u₁ := by
          have h1 := isHomog_elim x (hV_lin _ hv₁V)
          rwa [map_add, elim_X_self, add_zero, heu₁] at h1
        exact isHomog_mul hu1_lin hu1_lin
      have hmul := isHomog_mul hcn_hom hu1_sq_hom
      -- wait: when `k' = 0`, `cn = 0`, so `0 * u₁^2 = 0` is `IsHomog 1`!
      cases k' with
      | zero =>
        dsimp only [cn]
        rw [hcn_zero rfl, zero_mul]
        exact isHomog_zero 1
      | succ k'' =>
        rwa [show k'' + 1 - 1 + 2 = k'' + 1 + 1 by omega] at hmul
    have hY_kill : liftOpt (g' + cn * u₁ ^ 2) * ∏ i : Fin (m + 1), (bY i) ^ 2 = 0 := by
      have hprodY : ∏ i : Fin (m + 1), (bY i) ^ 2 =
          (∏ j : Fin m, (liftOpt (b_rest j)) ^ 2) * (liftOpt u_last + y) ^ 2 := by
        rw [Fin.prod_univ_castSucc]
        simp only [bY, Fin.snoc_castSucc, Fin.snoc_last]
      have hy_sq : y ^ 2 = 0 := X_sq none
      have huy_sq : (liftOpt u_last + y) ^ 2 = liftOpt u_last * (liftOpt u_last + 2 * y) := by
        calc (liftOpt u_last + y) ^ 2
            = liftOpt u_last ^ 2 + 2 * (liftOpt u_last * y) + y ^ 2 := by ring
          _ = liftOpt u_last * (liftOpt u_last + 2 * y) := by rw [hy_sq, add_zero]; ring
      rw [hprodY, huy_sq]
      have hl := congrArg liftOpt hcn_u1_kill
      rw [map_mul, map_mul, map_prod, map_zero] at hl
      simp_rw [map_pow] at hl
      calc liftOpt (g' + cn * u₁ ^ 2) *
            ((∏ j : Fin m, liftOpt (b_rest j) ^ 2) * (liftOpt u_last * (liftOpt u_last + 2 * y)))
          = (liftOpt (g' + cn * u₁ ^ 2) * liftOpt u_last * ∏ j : Fin m, liftOpt (b_rest j) ^ 2) *
              (liftOpt u_last + 2 * y) := by ring
        _ = 0 := by rw [hl, zero_mul]
    have hY_ideal := (ih (k' + 1)).2 Y hY_lin hY_dim hY_cov bY rfl
      (liftOpt (g' + cn * u₁ ^ 2)) hY_hom hY_kill
    have hU_ideal_sum : g' + cn * u₁ ^ 2 ∈ Ideal.span (U : Set (SqFreeAlg ι K)) := by
      have hsub : Ideal.span (Y : Set (SqFreeAlg (Option ι) K)) ≤
          Ideal.comap projOpt.toRingHom (Ideal.span (U : Set (SqFreeAlg ι K))) := by
        rw [Ideal.span_le]
        intro w hwY
        change projOpt w ∈ Ideal.span (U : Set (SqFreeAlg ι K))
        have hwU : projOpt w ∈ U := by
          change w ∈ Submodule.span K (Set.range bY) at hwY
          rw [Submodule.mem_span_range_iff_exists_fun] at hwY
          rcases hwY with ⟨c', rfl⟩
          simp only [map_sum, map_smul, bY]
          refine U.sum_mem fun i _ => U.smul_mem _ ?_
          induction i using Fin.lastCases with
          | last =>
            simp only [y, Fin.snoc_last, map_add, projOpt_liftOpt, projOpt_X_none, add_zero]
            exact hu_lastU
          | cast j =>
            simp only [Fin.snoc_castSucc, projOpt_liftOpt]
            exact hVU (hb_rest j).1
        exact Ideal.subset_span hwU
      have hmem := hsub hY_ideal
      change projOpt (liftOpt (g' + cn * u₁ ^ 2)) ∈ Ideal.span (U : Set (SqFreeAlg ι K)) at hmem
      rwa [projOpt_liftOpt] at hmem
    have hu1_sq_ideal : u₁ ^ 2 ∈ Ideal.span (U : Set (SqFreeAlg ι K)) := by
      have hsq := sq_eq_add_mul_sub u₁ (X x) (X_sq x)
      rw [hsq]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (hVU hv₁V))
    have hg'_ideal : g' ∈ Ideal.span (U : Set (SqFreeAlg ι K)) := by
      have heq : g' = (g' + cn * u₁ ^ 2) - cn * u₁ ^ 2 := by ring
      rw [heq]
      exact Ideal.sub_mem _ hU_ideal_sum (Ideal.mul_mem_left _ _ hu1_sq_ideal)
    obtain ⟨_, hdecomp_g'⟩ := ideal_homog_decomp hU hspanU hg'_ideal (k := k')
    obtain ⟨h, hh_hom, hg'_sum⟩ := hdecomp_g' hg'_hom
    let h_last := h (Fin.last (m + 1))
    have hf_hlast : f = h_last * u_last * ∏ j : Fin (m + 1), (bV j) ^ 2 := by
      have hsum_split2 : g' = (∑ j : Fin (m + 1), h (Fin.castSucc j) * bV j) + h_last * u_last := by
        rw [hg'_sum, Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rfl
      have hkillV : (∑ j : Fin (m + 1), h (Fin.castSucc j) * bV j) * ∏ j : Fin (m + 1), (bV j) ^ 2 = 0 := by
        rw [Finset.sum_mul]
        apply Finset.sum_eq_zero
        intro j _
        have hsplit : ∏ i : Fin (m + 1), (bV i) ^ 2 =
            (bV j) ^ 2 * ∏ i ∈ Finset.univ.erase j, (bV i) ^ 2 :=
          (Finset.mul_prod_erase Finset.univ (fun i => (bV i) ^ 2) (Finset.mem_univ j)).symm
        have hcube : (bV j) ^ 3 = 0 := linear_cube_eq_zero (hbV_lin j)
        calc h (Fin.castSucc j) * bV j * ∏ i : Fin (m + 1), (bV i) ^ 2
            = h (Fin.castSucc j) * ((bV j) ^ 3 * ∏ i ∈ Finset.univ.erase j, (bV i) ^ 2) := by
              rw [hsplit]; ring
          _ = 0 := by rw [hcube, zero_mul, mul_zero]
      rw [hfg', hsum_split2, add_mul, hkillV, zero_add]
    have hh_kill : h_last * ∏ i : Fin (m + 2), (b_spec i) ^ 2 = 0 := by
      have hprod_spec : ∏ i : Fin (m + 2), (b_spec i) ^ 2 =
          (∏ j : Fin (m + 1), (bV j) ^ 2) * u_last ^ 2 := by
        rw [Fin.prod_univ_castSucc]
        simp only [b_spec, Fin.snoc_castSucc, Fin.snoc_last]
      rw [hprod_spec]
      calc h_last * ((∏ j : Fin (m + 1), (bV j) ^ 2) * u_last ^ 2)
          = (h_last * u_last * ∏ j : Fin (m + 1), (bV j) ^ 2) * u_last := by ring
        _ = f * u_last := by rw [← hf_hlast]
        _ = 0 := hfu u_last hu_lastU
    have hh_ideal : h_last ∈ Ideal.span (U : Set (SqFreeAlg ι K)) :=
      hA_prev U hU hdim (covers_mono hcov fun i _ _ => by omega) b_spec hspanU h_last (hh_hom _) hh_kill
    cases k' with
    | zero =>
      have hh0 := (ideal_homog_decomp hU hspanU hh_ideal (k := 0)).1 (hh_hom _)
      have hf0 : f = 0 := by rw [hf_hlast, hh0, zero_mul, zero_mul]
      exact ⟨fun _ => hf0, fun h => by omega⟩
    | succ k'' =>
      obtain ⟨d, hd_hom, hd_sum⟩ := (ideal_homog_decomp hU hspanU hh_ideal (k := k'')).2 (hh_hom _)
      let d_last := d (Fin.last (m + 1))
      have hf_spec : f = d_last * ∏ i : Fin (m + 2), (b_spec i) ^ 2 := by
        have hsum_d : h_last = (∑ j : Fin (m + 1), d (Fin.castSucc j) * bV j) + d_last * u_last := by
          rw [hd_sum, Fin.sum_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
          rfl
        have hkillV2 : (∑ j : Fin (m + 1), d (Fin.castSucc j) * bV j) * u_last * ∏ j : Fin (m + 1), (bV j) ^ 2 = 0 := by
          rw [Finset.sum_mul, Finset.sum_mul]
          apply Finset.sum_eq_zero
          intro j _
          have hsplit : ∏ i : Fin (m + 1), (bV i) ^ 2 =
              (bV j) ^ 2 * ∏ i ∈ Finset.univ.erase j, (bV i) ^ 2 :=
            (Finset.mul_prod_erase Finset.univ (fun i => (bV i) ^ 2) (Finset.mem_univ j)).symm
          have hcube : (bV j) ^ 3 = 0 := linear_cube_eq_zero (hbV_lin j)
          calc d (Fin.castSucc j) * bV j * u_last * ∏ i : Fin (m + 1), (bV i) ^ 2
              = d (Fin.castSucc j) * u_last * ((bV j) ^ 3 * ∏ i ∈ Finset.univ.erase j, (bV i) ^ 2) := by
                rw [hsplit]; ring
            _ = 0 := by rw [hcube, zero_mul, mul_zero]
        have hprod_spec : ∏ i : Fin (m + 2), (b_spec i) ^ 2 =
            (∏ j : Fin (m + 1), (bV j) ^ 2) * u_last ^ 2 := by
          rw [Fin.prod_univ_castSucc]
          simp only [b_spec, Fin.snoc_castSucc, Fin.snoc_last]
        rw [hf_hlast, hsum_d, add_mul, add_mul, hkillV2, zero_add, hprod_spec]
        ring
      have hb_spec_lin : ∀ i, IsHomog 1 (b_spec i) := fun i =>
        hU (b_spec i) (hspanU ▸ Submodule.subset_span ⟨i, rfl⟩)
      have hb_mem_spec : ∀ i, b_spec i ∈ Submodule.span K (Set.range b) := fun i =>
        hb.symm ▸ hspanU ▸ Submodule.subset_span ⟨i, rfl⟩
      obtain ⟨c_sc, hc_sc⟩ := prodSq_mem_span_prodSq (fun j => hU (b j) (hb ▸ Submodule.subset_span ⟨j, rfl⟩)) hb_mem_spec
      refine ⟨fun h => by omega, fun _ => ⟨c_sc • d_last, isHomog_smul _ (hd_hom _), ?_⟩⟩
      rw [hf_spec, hc_sc, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

private lemma thm7_B_imp_A {K : Type*} [Field K] [CharP K 3] [Infinite K] (m k : ℕ)
    (hB : PropB K (m + 2) k) (hA_prev : PropA K (m + 1) k) :
    PropA K (m + 2) k := by
  intro ι _ _ U hU hdim hcov b hb f hf hfb
  have hU_ne_bot : U ≠ ⊥ := fun h => by
    have h1 := hdim
    rw [h, finrank_bot] at h1
    omega
  obtain ⟨v₀, hv₀U, hv₀_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU_ne_bot
  obtain ⟨x, hx_supp⟩ := supp_nonempty_of_ne_zero (hU v₀ hv₀U) hv₀_ne
  have hxU : x ∈ spaceSupp U := supp_subset_spaceSupp hv₀U hx_supp
  obtain ⟨u₁, b_rest, hu₁d, hv₁U, hb_rest, hspanU⟩ := basis_split_var hU hdim hxU
  let b_spec : Fin (m + 2) → SqFreeAlg ι K := Fin.cons (u₁ + X x) b_rest
  have hb_lin : ∀ j, IsHomog 1 (b j) := fun j => hU (b j) (hb ▸ Submodule.subset_span ⟨j, rfl⟩)
  have hb_spec_lin : ∀ i, IsHomog 1 (b_spec i) := fun i => hU (b_spec i) (hspanU ▸ Submodule.subset_span ⟨i, rfl⟩)
  have hb_spec_in : ∀ i, b_spec i ∈ Submodule.span K (Set.range b) := fun i =>
    hb.symm ▸ hspanU ▸ Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨c_sc, hc_sc⟩ := prodSq_mem_span_prodSq hb_lin hb_spec_in
  have hf_spec : f * ∏ i : Fin (m + 2), (b_spec i) ^ 2 = 0 := by
    rw [hc_sc, Algebra.mul_smul_comm, hfb, smul_zero]
  let g := rem (u₁ + X x) x f
  have hg_hom : IsHomog k g := isHomog_rem x (hU _ hv₁U) f hf
  have hg_deriv : deriv x g = 0 := deriv_rem x f
  have hv₁c : (u₁ + X x).coeff {x} = 1 := by
    have : (deriv x (u₁ + X x)).coeff ∅ = 1 := by simp [hu₁d, deriv_X_self]
    simpa using this
  have hfg_ideal : f - g ∈ Ideal.span (U : Set (SqFreeAlg ι K)) := by
    rw [sub_rem x (hU _ hv₁U) (by rw [hv₁c]; exact one_ne_zero) f, Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.subset_span hv₁U))
  have hg_spec : g * ((u₁ + X x) ^ 2 * ∏ j : Fin (m + 1), (b_rest j) ^ 2) = 0 := by
    have hprod : ∏ i : Fin (m + 2), (b_spec i) ^ 2 = (u₁ + X x) ^ 2 * ∏ j : Fin (m + 1), (b_rest j) ^ 2 := by
      rw [Fin.prod_univ_succ]; rfl
    have hdiff := sub_rem x (hU _ hv₁U) (by rw [hv₁c]; exact one_ne_zero) f
    have hcube : (u₁ + X x) ^ 3 = 0 := linear_cube_eq_zero (hU _ hv₁U)
    have hkill : (f - g) * ((u₁ + X x) ^ 2 * ∏ j : Fin (m + 1), (b_rest j) ^ 2) = 0 := by
      rw [hdiff]
      calc (((u₁ + X x).coeff {x})⁻¹ • (deriv x f * (u₁ + X x))) * ((u₁ + X x) ^ 2 * ∏ j : Fin (m + 1), (b_rest j) ^ 2)
          = ((u₁ + X x).coeff {x})⁻¹ • (deriv x f * ((u₁ + X x) ^ 3 * ∏ j : Fin (m + 1), (b_rest j) ^ 2)) := by
            rw [Algebra.smul_mul_assoc]; congr 1; ring
        _ = 0 := by rw [hcube, zero_mul, mul_zero, smul_zero]
    rw [← hprod] at hkill
    calc g * ((u₁ + X x) ^ 2 * ∏ j : Fin (m + 1), (b_rest j) ^ 2)
        = f * ∏ i : Fin (m + 2), (b_spec i) ^ 2 - (f - g) * ∏ i : Fin (m + 2), (b_spec i) ^ 2 := by
          rw [hprod]; ring
      _ = 0 := by rw [hf_spec, hkill, sub_zero]
  have heg : elim x g = g := by
    have := decomp x g; rw [hg_deriv, zero_mul, add_zero] at this; exact this.symm
  have heb_rest : ∀ j, elim x (b_rest j) = b_rest j := fun j => by
    have := decomp x (b_rest j); rw [(hb_rest j).2, zero_mul, add_zero] at this; exact this.symm
  have heprod : elim x (∏ j : Fin (m + 1), (b_rest j) ^ 2) = ∏ j : Fin (m + 1), (b_rest j) ^ 2 := by
    rw [elim_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [sq, elim_mul, heb_rest]
  have hdprod : deriv x (∏ j : Fin (m + 1), (b_rest j) ^ 2) = 0 := by
    have h : ∀ s : Finset (Fin (m + 1)), deriv x (∏ j ∈ s, (b_rest j) ^ 2) = 0 := by
      intro s
      induction s using Finset.induction with
      | empty => simp [deriv_one]
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, deriv_mul, deriv_sq_of_deriv_zero x (hb_rest a).2, zero_mul,
          zero_add, ih, mul_zero]
    exact h Finset.univ
  have hderiv := congrArg (deriv x) hg_spec
  rw [deriv_mul, map_zero, hg_deriv, zero_mul, zero_add, heg,
    deriv_mul, deriv_sq_add_X x hu₁d, hdprod, mul_zero, add_zero, heprod] at hderiv
  have h2ne : (2 : K) ≠ 0 := by
    intro h2
    have h2' : ((2 : ℕ) : K) = 0 := by simpa using h2
    rw [CharP.cast_eq_zero_iff K 3 2] at h2'
    omega
  have hgu1 : (g * ∏ j : Fin (m + 1), (b_rest j) ^ 2) * u₁ = 0 := by
    have hmul := congrArg (fun z => (2 : K)⁻¹ • z) hderiv
    rw [smul_zero] at hmul
    calc (g * ∏ j : Fin (m + 1), (b_rest j) ^ 2) * u₁
        = (2 : K)⁻¹ • (g * ((2 : K) • u₁ * ∏ j : Fin (m + 1), (b_rest j) ^ 2)) := by
          rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, inv_mul_cancel₀ h2ne, one_smul]
          ring
      _ = 0 := hmul
  let U' := U.map (elim x)
  have hms1 : ∀ W ≤ U, 1 ≤ Module.finrank K W → 2 ≤ (spaceSupp W).card := by
    intro W hWU hW1
    have := hcov W hWU hW1
    dsimp only at this
    omega
  obtain ⟨_, hU'_lin, hU'_dim, hU'_cov⟩ := elim_inj_of_ms1_ge_two hU hms1 x
  have hU'_cov_B : Covers U' (fun i => 4 * i - 3 + 2 * k) := by
    have hc := hU'_cov (fun i => 4 * i - 2 + 2 * k) hcov
    refine covers_mono hc fun i hi _ => ?_
    omega
  let bU' : Fin (m + 2) → SqFreeAlg ι K := Fin.cons u₁ b_rest
  have hspanU' : Submodule.span K (Set.range bU') = U' := by
    have heu₁ : elim x u₁ = u₁ := by
      have := decomp x u₁; rw [hu₁d, zero_mul, add_zero] at this; exact this.symm
    have he_spec : ∀ i : Fin (m + 2), elim x (b_spec i) = bU' i := fun i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [b_spec, bU', heu₁, elim_X_self]
      · simp [b_spec, bU', heb_rest]
    dsimp only [U']
    rw [← hspanU, Submodule.map_span]
    congr 1
    ext z
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i, he_spec i⟩
    · rintro ⟨i, rfl⟩; exact ⟨i, (he_spec i).symm⟩
  have hkill_U' : ∀ u ∈ U', (g * ∏ j : Fin (m + 1), (b_rest j) ^ 2) * u = 0 := by
    intro u hu
    rw [← hspanU', Submodule.mem_span_range_iff_exists_fun] at hu
    rcases hu with ⟨c, rfl⟩
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [Algebra.mul_smul_comm]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [bU', hgu1]
    · simp only [bU', Fin.cons_succ]
      have hsplit : ∏ r : Fin (m + 1), (b_rest r) ^ 2 =
          (b_rest j) ^ 2 * ∏ r ∈ Finset.univ.erase j, (b_rest r) ^ 2 :=
        (Finset.mul_prod_erase Finset.univ (fun r => (b_rest r) ^ 2) (Finset.mem_univ j)).symm
      have hcube : (b_rest j) ^ 3 = 0 := linear_cube_eq_zero (hU _ (hb_rest j).1)
      calc c (Fin.succ j) • ((g * ∏ r : Fin (m + 1), (b_rest r) ^ 2) * b_rest j)
          = c (Fin.succ j) • (g * ((b_rest j) ^ 3 * ∏ r ∈ Finset.univ.erase j, (b_rest r) ^ 2)) := by
            congr 1; rw [hsplit]; ring
        _ = 0 := by rw [hcube, zero_mul, mul_zero, smul_zero]
  have hgp_hom : IsHomog (2 * (m + 2) - 2 + k) (g * ∏ j : Fin (m + 1), (b_rest j) ^ 2) := by
    have hp := isHomog_prod_sq (fun j => hU _ (hb_rest j).1)
    have hmul := isHomog_mul hg_hom hp
    rwa [show k + 2 * (m + 1) = 2 * (m + 2) - 2 + k by omega] at hmul
  obtain ⟨hB_lt, hB_ge⟩ := hB U' hU'_lin (hU'_dim.trans hdim) hU'_cov_B bU' hspanU'
    (g * ∏ j : Fin (m + 1), (b_rest j) ^ 2) hgp_hom hkill_U'
  let V_rest := Submodule.span K (Set.range b_rest)
  have hV_rest_U : V_rest ≤ U := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (hb_rest j).1
  have hV_rest_lin : IsLinearSpace V_rest := fun v hv => hU v (hV_rest_U hv)
  have hb_rest_ind : LinearIndependent K b_rest := by
    have hb_spec_ind : LinearIndependent K b_spec :=
      linearIndependent_iff_card_eq_finrank_span.mpr (by
        rw [Fintype.card_fin]
        change m + 2 = Module.finrank K ↥(Submodule.span K (Set.range b_spec))
        rw [hspanU, hdim])
    exact hb_spec_ind.comp Fin.succ (Fin.succ_injective _)
  have hV_rest_dim : Module.finrank K V_rest = m + 1 := by
    rw [finrank_span_eq_card hb_rest_ind, Fintype.card_fin]
  have hV_rest_cov : Covers V_rest (fun i => 4 * i - 2 + 2 * k) := covers_sub hV_rest_U hcov
  have hg_ideal : g ∈ Ideal.span (U : Set (SqFreeAlg ι K)) := by
    by_cases hk : k < 2
    · have hkill_V := hB_lt hk
      have hg_V := hA_prev V_rest hV_rest_lin hV_rest_dim hV_rest_cov b_rest rfl g hg_hom hkill_V
      exact Ideal.span_mono hV_rest_U hg_V
    · obtain ⟨h, hh_hom, hh_eq⟩ := hB_ge (by omega)
      have hh_eq' : g * ∏ j : Fin (m + 1), (b_rest j) ^ 2 =
          h * u₁ ^ 2 * ∏ j : Fin (m + 1), (b_rest j) ^ 2 := by
        rw [hh_eq]
        have hprodU' : ∏ i : Fin (m + 2), (bU' i) ^ 2 = u₁ ^ 2 * ∏ j : Fin (m + 1), (b_rest j) ^ 2 := by
          rw [Fin.prod_univ_succ]; rfl
        rw [hprodU']
        ring
      have hsub_kill : (g - h * u₁ ^ 2) * ∏ j : Fin (m + 1), (b_rest j) ^ 2 = 0 := by
        rw [sub_mul, hh_eq', sub_self]
      have heu1 : elim x u₁ = u₁ := by
        have := decomp x u₁; rw [hu₁d, zero_mul, add_zero] at this; exact this.symm
      have hu1_lin : IsHomog 1 u₁ := by
        have h1 := isHomog_elim x (hU _ hv₁U)
        rwa [map_add, elim_X_self, add_zero, heu1] at h1
      have hsub_hom : IsHomog k (g - h * u₁ ^ 2) := by
        refine isHomog_sub hg_hom ?_
        have h1 := isHomog_mul hh_hom (show IsHomog 2 (u₁ ^ 2) by rw [sq]; exact isHomog_mul hu1_lin hu1_lin)
        rwa [show k - 2 + 2 = k by omega] at h1
      have hg_sub_V := hA_prev V_rest hV_rest_lin hV_rest_dim hV_rest_cov b_rest rfl
        (g - h * u₁ ^ 2) hsub_hom hsub_kill
      have hg_sub_U : g - h * u₁ ^ 2 ∈ Ideal.span (U : Set (SqFreeAlg ι K)) :=
        Ideal.span_mono hV_rest_U hg_sub_V
      have hu1_sq_U : u₁ ^ 2 ∈ Ideal.span (U : Set (SqFreeAlg ι K)) := by
        rw [sq_eq_add_mul_sub u₁ (X x) (X_sq x)]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span hv₁U)
      have heq : g = (g - h * u₁ ^ 2) + h * u₁ ^ 2 := by ring
      rw [heq]
      exact Ideal.add_mem _ hg_sub_U (Ideal.mul_mem_left _ _ hu1_sq_U)
  have heqf : f = (f - g) + g := by ring
  rw [heqf]
  exact Ideal.add_mem _ hfg_ideal hg_ideal

theorem thm7 {K : Type*} [Field K] [CharP K 3] [Infinite K] (n : ℕ) (hn : 1 ≤ n) :
    ∀ k : ℕ, PropB K n k ∧ PropA K n k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  clear hn
  induction m with
  | zero => exact thm7_base
  | succ m ih =>
    intro k
    induction k with
    | zero =>
      have hB0 : PropB K (m + 2) 0 := thm7_A_imp_B m 0 ih (Or.inl rfl)
      exact ⟨hB0, thm7_B_imp_A m 0 hB0 (ih 0).2⟩
    | succ k ihk =>
      have hBk : PropB K (m + 2) (k + 1) := thm7_A_imp_B m (k + 1) ih (Or.inr ⟨Nat.succ_pos k, ihk.2⟩)
      exact ⟨hBk, thm7_B_imp_A m (k + 1) hBk (ih (k + 1)).2⟩

end Theorem7

section Theorem3

def mapCoeffs {ι R S : Type*} [DecidableEq ι] [CommRing R] [CommRing S] (φ : R →+* S) :
    SqFreeAlg ι R →+* SqFreeAlg ι S where
  toFun f := ⟨fun T => φ (f.coeff T)⟩
  map_one' := by
    apply ext; intro T
    by_cases hT : T = ∅ <;> simp [hT]
  map_mul' f g := by
    apply ext; intro T
    simp [mul_coeff]
  map_zero' := by
    apply ext; intro T; simp
  map_add' f g := by
    apply ext; intro T; simp

@[simp] lemma mapCoeffs_coeff {ι R S : Type*} [DecidableEq ι] [CommRing R] [CommRing S]
    (φ : R →+* S) (f : SqFreeAlg ι R) (T : Finset ι) :
    (mapCoeffs φ f).coeff T = φ (f.coeff T) := rfl

@[simp] lemma mapCoeffs_X {ι R S : Type*} [DecidableEq ι] [CommRing R] [CommRing S]
    (φ : R →+* S) (i : ι) :
    mapCoeffs φ (X (K := R) i) = X (K := S) i := by
  apply ext; intro T
  by_cases h : T = {i} <;> simp [h]

lemma mapCoeffs_smul {ι R S : Type*} [DecidableEq ι] [CommRing R] [CommRing S]
    (φ : R →+* S) (c : R) (f : SqFreeAlg ι R) :
    mapCoeffs φ (c • f) = φ c • mapCoeffs φ f := by
  apply ext; intro T; simp

lemma sum_coeff {α ι R : Type*} [DecidableEq ι] [CommRing R]
    (s : Finset α) (f : α → SqFreeAlg ι R) (T : Finset ι) :
    (∑ i ∈ s, f i).coeff T = ∑ i ∈ s, (f i).coeff T := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

theorem thm3_nonzero_coeff (n : ℕ) (hn : 1 ≤ n)
    (φ : Fin 4 → ((Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3))) :
    ∃ S : Finset (Fin 4 × Fin n), S.card = 2 * n ∧
      (∏ r : Fin n, (∑ s : Fin 4 × Fin n, (φ s.1 (Pi.single s.2 1) r) • X (K := ZMod 3) s) ^ 2).coeff S ≠ 0 := by
  classical
  let K := RatFunc (ZMod 3)
  have hcharK : CharP K 3 := ⟨fun m => by
    rw [← map_natCast (RatFunc.C : ZMod 3 →+* K) m, ← map_zero (RatFunc.C : ZMod 3 →+* K),
      RatFunc.C_injective.eq_iff]
    exact CharP.cast_eq_zero_iff (ZMod 3) 3 m⟩
  have hinfK : Infinite K :=
    Infinite.of_injective _ (RatFunc.algebraMap_injective (ZMod 3))
  let M : Fin n → Fin 4 × Fin n → ZMod 3 := fun r s => φ s.1 (Pi.single s.2 1) r
  let w3 : Fin n → SqFreeAlg (Fin 4 × Fin n) (ZMod 3) :=
    fun r => ∑ s : Fin 4 × Fin n, M r s • X s
  let w : Fin n → SqFreeAlg (Fin 4 × Fin n) K :=
    fun r => mapCoeffs (RatFunc.C : ZMod 3 →+* K) (w3 r)
  have hw_eq : ∀ r, w r = ∑ s : Fin 4 × Fin n, RatFunc.C (M r s) • X s := fun r => by
    simp [w, w3, map_sum, mapCoeffs_smul]
  have hw_lin : ∀ r, IsHomog 1 (w r) := fun r => by
    rw [hw_eq]
    exact isHomog_sum fun s _ => isHomog_smul _ (isHomog_X s)
  have hw_coeff : ∀ r (b : Fin 4) (j : Fin n),
      (w r).coeff {(b, j)} = RatFunc.C (M r (b, j)) := fun r b j => by
    rw [hw_eq, sum_coeff]
    simp only [smul_coeff, X_coeff, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single (b, j)]
    · simp
    · intro s _ hs
      have : ({(b, j)} : Finset (Fin 4 × Fin n)) ≠ {s} := fun h => hs (Finset.singleton_injective h).symm
      simp [this]
    · intro h; exact False.elim (h (Finset.mem_univ _))
  have hM_inv : ∀ (b : Fin 4) (r s : Fin n),
      ∑ j : Fin n, M r (b, j) * ((φ b).symm (Pi.single s 1) j) = if r = s then 1 else 0 := by
    intro b r s
    let v := (φ b).symm (Pi.single s 1)
    have hv_exp : v = ∑ j : Fin n, v j • Pi.single j (1 : ZMod 3) := by
      ext i; simp [Pi.single_apply]
    have hphi := congrArg (φ b) hv_exp
    rw [LinearEquiv.apply_symm_apply, map_sum] at hphi
    have hr := congrArg (fun f => f r) hphi
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul] at hr
    rw [Pi.single_apply] at hr
    rw [hr]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact mul_comm _ _
  have hblock_rec : ∀ (c : Fin n → K) (b : Fin 4) (s : Fin n),
      ∑ j : Fin n, (∑ r : Fin n, c r • w r).coeff {(b, j)} *
        RatFunc.C ((φ b).symm (Pi.single s 1) j) = c s := by
    intro c b s
    calc ∑ j : Fin n, (∑ r : Fin n, c r • w r).coeff {(b, j)} *
          RatFunc.C ((φ b).symm (Pi.single s 1) j)
        = ∑ j : Fin n, (∑ r : Fin n, c r * RatFunc.C (M r (b, j))) *
            RatFunc.C ((φ b).symm (Pi.single s 1) j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [sum_coeff]
          congr 1
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [smul_coeff, hw_coeff]
      _ = ∑ r : Fin n, c r * ∑ j : Fin n, RatFunc.C (M r (b, j)) *
            RatFunc.C ((φ b).symm (Pi.single s 1) j) := by
          have h1 : ∑ j : Fin n, (∑ r : Fin n, c r * RatFunc.C (M r (b, j))) *
                RatFunc.C ((φ b).symm (Pi.single s 1) j) =
              ∑ j : Fin n, ∑ r : Fin n, (c r * RatFunc.C (M r (b, j))) *
                RatFunc.C ((φ b).symm (Pi.single s 1) j) :=
            Finset.sum_congr rfl fun j _ => Finset.sum_mul _ _ _
          rw [h1, Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ r : Fin n, c r * RatFunc.C (if r = s then 1 else 0) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          congr 1
          simp_rw [← map_mul, ← map_sum]
          rw [hM_inv]
      _ = c s := by
          rw [Finset.sum_eq_single s]
          · simp
          · intro r _ hrs
            simp [hrs]
          · intro h; exact False.elim (h (Finset.mem_univ _))
  have hw_ind : LinearIndependent K w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc s
    have hcoeff0 : ∀ j : Fin n, (∑ r : Fin n, c r • w r).coeff {(0, j)} = 0 := fun j => by
      rw [hc, zero_coeff]
    have hrec := hblock_rec c 0 s
    simpa [hcoeff0] using hrec.symm
  let U : Submodule K (SqFreeAlg (Fin 4 × Fin n) K) := Submodule.span K (Set.range w)
  have hU_lin : IsLinearSpace U := fun u hu => by
    rw [Submodule.mem_span_range_iff_exists_fun] at hu
    rcases hu with ⟨c, rfl⟩
    exact isHomog_sum fun r _ => isHomog_smul _ (hw_lin r)
  have hU_dim : Module.finrank K U = n := by
    rw [finrank_span_eq_card hw_ind, Fintype.card_fin]
  have hU_cov : Covers U (fun i => 4 * i) := by
    intro W hWU hW1
    have hblock_le : ∀ b : Fin 4, Module.finrank K W ≤
        ((Finset.univ : Finset (Fin n)).filter (fun j => (b, j) ∈ spaceSupp W)).card := by
      intro b
      let Sb := (Finset.univ : Finset (Fin n)).filter (fun j => (b, j) ∈ spaceSupp W)
      let T : W →ₗ[K] (↥Sb → K) :=
        { toFun := fun u j => u.1.coeff {(b, j.1)}
          map_add' := fun u v => by ext j; simp
          map_smul' := fun c u => by ext j; simp }
      have hT_inj : Function.Injective T := by
        rw [injective_iff_map_eq_zero]
        rintro ⟨u, huW⟩ hTu
        apply Subtype.ext
        have huU : u ∈ U := hWU huW
        rw [Submodule.mem_span_range_iff_exists_fun] at huU
        rcases huU with ⟨c, rfl⟩
        have hcoeff0 : ∀ j : Fin n, (∑ r : Fin n, c r • w r).coeff {(b, j)} = 0 := by
          intro j
          by_cases hj : j ∈ Sb
          · exact congrArg (fun f => f ⟨j, hj⟩) hTu
          · by_contra hne
            apply hj
            rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ j, ?_⟩
            rw [mem_spaceSupp_iff]
            exact ⟨_, huW, hne⟩
        have hc0 : ∀ s, c s = 0 := fun s => by
          have hrec := hblock_rec c b s
          simpa [hcoeff0] using hrec.symm
        simp [hc0]
      have hker : LinearMap.ker T = ⊥ := LinearMap.ker_eq_bot.mpr hT_inj
      have hrk := LinearMap.finrank_range_add_finrank_ker T
      rw [hker, finrank_bot, add_zero] at hrk
      have hle := Submodule.finrank_le (LinearMap.range T)
      rw [hrk, Module.finrank_eq_card_basis (Pi.basisFun K ↥Sb), Fintype.card_coe] at hle
      exact hle
    let f_emb : Fin 4 → (Fin n ↪ Fin 4 × Fin n) :=
      fun b => ⟨fun j => (b, j), fun _ _ h => congrArg Prod.snd h⟩
    let Sb_lift : Fin 4 → Finset (Fin 4 × Fin n) := fun b =>
      ((Finset.univ : Finset (Fin n)).filter (fun j => (b, j) ∈ spaceSupp W)).map (f_emb b)
    have hsub : Finset.univ.biUnion Sb_lift ⊆ spaceSupp W := by
      intro p hp
      rw [Finset.mem_biUnion] at hp
      rcases hp with ⟨b, _, hpb⟩
      rw [Finset.mem_map] at hpb
      rcases hpb with ⟨j, hj, rfl⟩
      exact (Finset.mem_filter.mp hj).2
    have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin 4)) Sb_lift := by
      intro b₁ _ b₂ _ hb
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp₁ hp₂
      rw [Finset.mem_map] at hp₁ hp₂
      rcases hp₁ with ⟨j₁, _, rfl⟩
      rcases hp₂ with ⟨j₂, _, h2⟩
      exact hb (congrArg Prod.fst h2).symm
    have hcard_eq : (Finset.univ.biUnion Sb_lift).card = ∑ b : Fin 4, (Sb_lift b).card :=
      Finset.card_biUnion hdisj
    have hcard_le : 4 * Module.finrank K W ≤ (spaceSupp W).card := by
      calc 4 * Module.finrank K W
          = ∑ _b : Fin 4, Module.finrank K W := by simp [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ b : Fin 4, (Sb_lift b).card := by
            refine Finset.sum_le_sum fun b _ => ?_
            simpa [Sb_lift] using hblock_le b
        _ = (Finset.univ.biUnion Sb_lift).card := hcard_eq.symm
        _ ≤ (spaceSupp W).card := Finset.card_le_card hsub
    exact hcard_le
  have h7 := (thm7 (K := K) n hn 0).2 U hU_lin hU_dim (covers_mono hU_cov fun i _ _ => by omega)
    w rfl 1 isHomog_one
  have hprod_ne : ∏ r : Fin n, (w r) ^ 2 ≠ 0 := by
    intro hprod0
    have h1 : (1 : SqFreeAlg (Fin 4 × Fin n) K) * ∏ r : Fin n, (w r) ^ 2 = 0 := by
      rw [hprod0, mul_zero]
    have hmem := h7 h1
    have hc0 := mem_ideal_span_coeff_empty hU_lin hmem
    simp at hc0
  have hprod_map : ∏ r : Fin n, (w r) ^ 2 =
      mapCoeffs (RatFunc.C : ZMod 3 →+* K) (∏ r : Fin n, (w3 r) ^ 2) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [map_pow]
  have hne3 : ∃ S : Finset (Fin 4 × Fin n), (∏ r : Fin n, (w3 r) ^ 2).coeff S ≠ 0 := by
    by_contra hAll
    push Not at hAll
    have h0 : mapCoeffs (RatFunc.C : ZMod 3 →+* K) (∏ r : Fin n, (w3 r) ^ 2) = 0 := by
      apply ext; intro S
      rw [mapCoeffs_coeff, hAll S, map_zero, zero_coeff]
    exact hprod_ne (hprod_map.trans h0)
  rcases hne3 with ⟨S, hS_ne⟩
  have hw3_lin : ∀ r, IsHomog 1 (w3 r) := fun r =>
    isHomog_sum fun s _ => isHomog_smul _ (isHomog_X s)
  have hhom : IsHomog (2 * n) (∏ r : Fin n, (w3 r) ^ 2) := isHomog_prod_sq hw3_lin
  have hS_card : S.card = 2 * n := by
    by_contra hne
    exact hS_ne (hhom S hne)
  exact ⟨S, hS_card, hS_ne⟩

end Theorem3

section Nullstellensatz

lemma biUnion_card_eq_sum_imp_disjoint {β ι : Type*} [DecidableEq β] [DecidableEq ι]
    (I : Finset β) (F : β → Finset ι)
    (hcard : (I.biUnion F).card = ∑ r ∈ I, (F r).card) :
    ∀ r ∈ I, ∀ r' ∈ I, r ≠ r' → Disjoint (F r) (F r') := by
  induction I using Finset.induction with
  | empty => intro r hr; simp at hr
  | insert a I ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha] at hcard
    have huni := Finset.card_union_add_card_inter (F a) (I.biUnion F)
    have hle : (I.biUnion F).card ≤ ∑ r ∈ I, (F r).card := Finset.card_biUnion_le
    have hinter0 : (F a ∩ I.biUnion F).card = 0 := by omega
    have hsum_eq : (I.biUnion F).card = ∑ r ∈ I, (F r).card := by omega
    have hdisj_a : Disjoint (F a) (I.biUnion F) := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hinter0)
    have hI := ih hsum_eq
    intro r hr r' hr' hne
    rw [Finset.mem_insert] at hr hr'
    rcases hr with rfl | hr <;> rcases hr' with rfl | hr'
    · exact False.elim (hne rfl)
    · exact hdisj_a.mono_right (Finset.subset_biUnion_of_mem F hr')
    · exact (hdisj_a.mono_right (Finset.subset_biUnion_of_mem F hr)).symm
    · exact hI r hr r' hr' hne

lemma altSum_indicator {α R : Type*} [DecidableEq α] [CommRing R] (S A : Finset α) (hA : A ⊆ S) :
    ∑ T ∈ S.powerset, (-1 : R) ^ (S.card - T.card) * (if A ⊆ T then 1 else 0) =
      if A = S then 1 else 0 := by
  have hfilt : ∑ T ∈ S.powerset, (-1 : R) ^ (S.card - T.card) * (if A ⊆ T then 1 else 0) =
      ∑ T ∈ S.powerset.filter (fun T => A ⊆ T), (-1 : R) ^ (S.card - T.card) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun T _ => by split_ifs <;> simp
  rw [hfilt]
  have hbij : ∑ T ∈ S.powerset.filter (fun T => A ⊆ T), (-1 : R) ^ (S.card - T.card) =
      ∑ U ∈ (S \ A).powerset, (-1 : R) ^ ((S \ A).card - U.card) := by
    symm
    refine Finset.sum_bij (fun U _ => A ∪ U) ?_ ?_ ?_ ?_
    · intro U hU
      rw [Finset.mem_powerset] at hU
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.union_subset hA (hU.trans Finset.sdiff_subset), Finset.subset_union_left⟩
    · intro U₁ hU₁ U₂ hU₂ heq
      rw [Finset.mem_powerset] at hU₁ hU₂
      have hd₁ : Disjoint A U₁ := (disjoint_sdiff_self_right : Disjoint A (S \ A)).mono_right hU₁
      have hd₂ : Disjoint A U₂ := (disjoint_sdiff_self_right : Disjoint A (S \ A)).mono_right hU₂
      have := congrArg (fun X => X \ A) heq
      simpa [Finset.union_sdiff_cancel_left hd₁, Finset.union_sdiff_cancel_left hd₂] using this
    · intro T hT
      rw [Finset.mem_filter, Finset.mem_powerset] at hT
      refine ⟨T \ A, Finset.mem_powerset.mpr (Finset.sdiff_subset_sdiff hT.1 le_rfl), ?_⟩
      exact Finset.union_sdiff_of_subset hT.2
    · intro U hU
      rw [Finset.mem_powerset] at hU
      have hd : Disjoint A U := (disjoint_sdiff_self_right : Disjoint A (S \ A)).mono_right hU
      have hc1 : (A ∪ U).card = A.card + U.card := Finset.card_union_of_disjoint hd
      have hc2 : (S \ A).card = S.card - A.card := Finset.card_sdiff_of_subset hA
      have hc3 : A.card ≤ S.card := Finset.card_le_card hA
      congr 1
      omega
  rw [hbij]
  by_cases hAS : A = S
  · subst hAS
    simp
  · rw [if_neg hAS]
    have hne : (S \ A).Nonempty := Finset.sdiff_nonempty.mpr (fun h => hAS (Finset.Subset.antisymm hA h))
    obtain ⟨a, ha⟩ := hne
    have hprod0 : ∏ _x ∈ S \ A, ((1 : R) + (-1 : R)) = 0 :=
      Finset.prod_eq_zero ha (add_neg_cancel 1)
    rw [Finset.prod_add] at hprod0
    rw [← hprod0]
    refine Finset.sum_congr rfl fun U hU => ?_
    rw [Finset.mem_powerset] at hU
    simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
    rw [Finset.card_sdiff_of_subset hU]

lemma prod_coeff_eq_sum {β ι R : Type*} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]
    [CommRing R] (I : Finset β) (f : β → SqFreeAlg ι R) (S : Finset ι) :
    (∏ r ∈ I, f r).coeff S =
      ∑ F : β → Finset ι,
        if I.biUnion F = S ∧ (∀ r ∈ I, ∀ r' ∈ I, r ≠ r' → Disjoint (F r) (F r')) ∧
            (∀ r ∉ I, F r = ∅)
        then ∏ r ∈ I, (f r).coeff (F r) else 0 := by
  classical
  induction I using Finset.induction generalizing S with
  | empty =>
    by_cases hS : S = ∅
    · subst hS
      rw [Finset.prod_empty, one_coeff, if_pos rfl]
      symm
      rw [Finset.sum_eq_single (fun _ => ∅)]
      · simp
      · intro F _ hne
        rw [if_neg]
        intro h
        exact hne (funext fun r => h.2.2 r (Finset.notMem_empty r))
      · intro h; exact False.elim (h (Finset.mem_univ _))
    · rw [Finset.prod_empty, one_coeff, if_neg hS]
      symm
      apply Finset.sum_eq_zero
      intro F _
      rw [if_neg]
      intro h
      apply hS
      simpa using h.1.symm
  | insert a I ha ih =>
    rw [Finset.prod_insert ha, mul_coeff]
    have hstep : ∑ T ∈ S.powerset, (f a).coeff T * (∏ r ∈ I, f r).coeff (S \ T) =
        ∑ T ∈ S.powerset, ∑ F : β → Finset ι,
          if I.biUnion F = S \ T ∧ (∀ r ∈ I, ∀ r' ∈ I, r ≠ r' → Disjoint (F r) (F r')) ∧
              (∀ r ∉ I, F r = ∅)
          then (f a).coeff T * ∏ r ∈ I, (f r).coeff (F r) else 0 := by
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [ih (S \ T), Finset.mul_sum]
      refine Finset.sum_congr rfl fun F _ => by split_ifs <;> ring
    rw [hstep, ← Finset.sum_product']
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    refine Finset.sum_bij (fun p _ => Function.update p.2 a p.1) ?_ ?_ ?_ ?_
    · rintro ⟨T, F⟩ hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, Finset.mem_univ,
        true_and, and_true] at hp ⊢
      rcases hp with ⟨hTS, huni, hdisj, hout⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [Finset.biUnion_insert, Function.update_self]
        have hIu : I.biUnion (Function.update F a T) = I.biUnion F := by
          refine Finset.biUnion_congr rfl fun r hr => ?_
          rw [Function.update_of_ne (by rintro rfl; exact ha hr)]
        rw [hIu, huni, Finset.union_sdiff_of_subset hTS]
      · intro r hr r' hr' hne
        rw [Finset.mem_insert] at hr hr'
        rcases hr with rfl | hr <;> rcases hr' with rfl | hr'
        · exact False.elim (hne rfl)
        · rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact ha hr')]
          have hsub : F r' ⊆ S \ T := huni ▸ Finset.subset_biUnion_of_mem F hr'
          exact (disjoint_sdiff_self_right : Disjoint T (S \ T)).mono_right hsub
        · rw [Function.update_of_ne (by rintro rfl; exact ha hr), Function.update_self]
          have hsub : F r ⊆ S \ T := huni ▸ Finset.subset_biUnion_of_mem F hr
          exact ((disjoint_sdiff_self_right : Disjoint T (S \ T)).mono_right hsub).symm
        · rw [Function.update_of_ne (by rintro rfl; exact ha hr), Function.update_of_ne (by rintro rfl; exact ha hr')]
          exact hdisj r hr r' hr' hne
      · intro r hr
        rw [Finset.mem_insert, not_or] at hr
        rw [Function.update_of_ne hr.1]
        exact hout r hr.2
    · rintro ⟨T₁, F₁⟩ hp₁ ⟨T₂, F₂⟩ hp₂ heq
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, Finset.mem_univ,
        and_true] at hp₁ hp₂
      have hT : T₁ = T₂ := by
        have := congrFun heq a
        simpa using this
      subst hT
      congr 1
      funext r
      by_cases hra : r = a
      · rw [hra, hp₁.2.2.2 a ha, hp₂.2.2.2 a ha]
      · have := congrFun heq r
        simpa [Function.update_of_ne hra] using this
    · intro G hG
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG
      rcases hG with ⟨huni, hdisj, hout⟩
      refine ⟨⟨G a, Function.update G a ∅⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, Finset.mem_univ,
          and_true]
        have haS : G a ⊆ S := huni ▸ Finset.subset_biUnion_of_mem G (Finset.mem_insert_self a I)
        refine ⟨haS, ?_, ?_, ?_⟩
        · rw [← huni, Finset.biUnion_insert]
          have hIu : I.biUnion (Function.update G a ∅) = I.biUnion G := by
            refine Finset.biUnion_congr rfl fun r hr => ?_
            rw [Function.update_of_ne (by rintro rfl; exact ha hr)]
          rw [hIu]
          have hd : Disjoint (G a) (I.biUnion G) := by
            rw [Finset.disjoint_biUnion_right]
            intro r hr
            exact hdisj a (Finset.mem_insert_self a I) r (Finset.mem_insert_of_mem hr) (by rintro rfl; exact ha hr)
          exact (Finset.union_sdiff_cancel_left hd).symm
        · intro r hr r' hr' hne
          rw [Function.update_of_ne (by rintro rfl; exact ha hr), Function.update_of_ne (by rintro rfl; exact ha hr')]
          exact hdisj r (Finset.mem_insert_of_mem hr) r' (Finset.mem_insert_of_mem hr') hne
        · intro r hr
          by_cases hra : r = a
          · rw [hra]; exact Function.update_self a ∅ G
          · rw [Function.update_of_ne hra]
            exact hout r (by rw [Finset.mem_insert, not_or]; exact ⟨hra, hr⟩)
      · ext r
        by_cases hra : r = a
        · rw [hra]; simp
        · simp [Function.update_of_ne hra]
    · rintro ⟨T, F⟩ hp
      rw [Finset.prod_insert ha, Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun r hr => ?_
      rw [Function.update_of_ne (by rintro rfl; exact ha hr)]

noncomputable def cRow {n : ℕ} (m_row : Fin 4 × Fin n → ZMod 3) (v_r : ZMod 3)
    (A : Finset (Fin 4 × Fin n)) : ZMod 3 :=
  if A.card = 0 then 1 - v_r ^ 2
  else if A.card = 1 then ∑ s ∈ A, (2 * v_r * m_row s - (m_row s) ^ 2)
  else if A.card = 2 then - ((∑ s : Fin 4 × Fin n, m_row s • X (K := ZMod 3) s) ^ 2).coeff A
  else 0

lemma sq_linear_coeff {n : ℕ} (m_row : Fin 4 × Fin n → ZMod 3) (A : Finset (Fin 4 × Fin n)) :
    ((∑ s : Fin 4 × Fin n, m_row s • X (K := ZMod 3) s) ^ 2).coeff A =
      ∑ s : Fin 4 × Fin n, ∑ t : Fin 4 × Fin n,
        if s ≠ t ∧ A = {s, t} then m_row s * m_row t else 0 := by
  rw [sq, Finset.sum_mul]
  simp_rw [Finset.mul_sum, sum_coeff]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, smul_coeff]
  by_cases hst : s = t
  · subst hst
    rw [X_mul_X, zero_coeff, mul_zero]
    simp
  · have hxmul : (X (K := ZMod 3) s * X t).coeff A = if A = {s, t} then 1 else 0 := by
      rw [mul_coeff]
      by_cases hA : A = {s, t}
      · subst hA
        rw [if_pos rfl]
        rw [Finset.sum_eq_single {s}]
        · have hsdiff : ({s, t} : Finset (Fin 4 × Fin n)) \ {s} = {t} := by
            ext x
            simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, hx⟩
              · exact (hx rfl).elim
              · rfl
            · rintro rfl
              exact ⟨Or.inr rfl, Ne.symm hst⟩
          simp [hsdiff]
        · intro U _ hUs
          by_cases hU1 : U = {s}
          · exact False.elim (hUs hU1)
          · simp [hU1]
        · intro hs_mem
          exfalso; apply hs_mem
          rw [Finset.mem_powerset]
          exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self s {t})
      · rw [if_neg hA]
        apply Finset.sum_eq_zero
        intro U hU
        rw [Finset.mem_powerset] at hU
        by_cases hU1 : U = {s}
        · subst hU1
          have hne : A \ {s} ≠ {t} := by
            intro hdiff
            apply hA
            rw [(Finset.union_sdiff_of_subset hU).symm, hdiff]
            ext x; simp
          simp [hne]
        · simp [hU1]
    rw [hxmul]
    by_cases hA : A = {s, t}
    · simp [hst, hA]
    · simp [hst, hA]

lemma row_eval_eq {n : ℕ} (m_row : Fin 4 × Fin n → ZMod 3) (v_r : ZMod 3)
    (T : Finset (Fin 4 × Fin n)) :
    1 - ((∑ s ∈ T, m_row s) - v_r) ^ 2 = ∑ A ∈ T.powerset, cRow m_row v_r A := by
  have hpart : ∑ A ∈ T.powerset, cRow m_row v_r A =
      cRow m_row v_r ∅ +
      (∑ A ∈ T.powersetCard 1, cRow m_row v_r A) +
      (∑ A ∈ T.powersetCard 2, cRow m_row v_r A) := by
    have hsplit : T.powerset = {∅} ∪ T.powersetCard 1 ∪ T.powersetCard 2 ∪
        (T.powerset.filter (fun A => 3 ≤ A.card)) := by
      ext A
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_powerset, Finset.mem_powersetCard,
        Finset.mem_filter]
      constructor
      · intro hAT
        by_cases h0 : A.card = 0
        · left; left; left; exact Finset.card_eq_zero.mp h0
        · by_cases h1 : A.card = 1
          · left; left; right; exact ⟨hAT, h1⟩
          · by_cases h2 : A.card = 2
            · left; right; exact ⟨hAT, h2⟩
            · right; exact ⟨hAT, by omega⟩
      · rintro (((rfl | ⟨hAT, _⟩) | ⟨hAT, _⟩) | ⟨hAT, _⟩)
        · exact Finset.empty_subset T
        · exact hAT
        · exact hAT
        · exact hAT
    rw [hsplit]
    have hd1 : Disjoint {∅} (T.powersetCard 1) := by
      rw [Finset.disjoint_singleton_left, Finset.mem_powersetCard]
      intro ⟨_, hc⟩; simp at hc
    have hd2 : Disjoint ({∅} ∪ T.powersetCard 1) (T.powersetCard 2) := by
      rw [Finset.disjoint_left]
      intro A hA1 hA2
      rw [Finset.mem_powersetCard] at hA2
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_powersetCard] at hA1
      rcases hA1 with rfl | ⟨_, hc⟩
      · simp at hA2
      · omega
    have hd3 : Disjoint ({∅} ∪ T.powersetCard 1 ∪ T.powersetCard 2)
        (T.powerset.filter (fun A => 3 ≤ A.card)) := by
      rw [Finset.disjoint_left]
      intro A hA1 hA2
      rw [Finset.mem_filter] at hA2
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_powersetCard] at hA1
      rcases hA1 with ((rfl | ⟨_, hc⟩) | ⟨_, hc⟩)
      · simp at hA2
      · omega
      · omega
    rw [Finset.sum_union hd3, Finset.sum_union hd2, Finset.sum_union hd1, Finset.sum_singleton]
    have h3zero : ∑ A ∈ T.powerset.filter (fun A => 3 ≤ A.card), cRow m_row v_r A = 0 := by
      apply Finset.sum_eq_zero
      intro A hA
      rw [Finset.mem_filter] at hA
      have hc0 : A.card ≠ 0 := by omega
      have hc1 : A.card ≠ 1 := by omega
      have hc2 : A.card ≠ 2 := by omega
      simp [cRow, hc0, hc1, hc2]
    rw [h3zero, add_zero]
  rw [hpart]
  have h0 : cRow m_row v_r ∅ = 1 - v_r ^ 2 := by simp [cRow]
  have h1 : ∑ A ∈ T.powersetCard 1, cRow m_row v_r A =
      ∑ s ∈ T, (2 * v_r * m_row s - (m_row s) ^ 2) := by
    rw [Finset.sum_bij (fun s _ => ({s} : Finset (Fin 4 × Fin n)))]
    · intro s hs
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.singleton_subset_iff.mpr hs, Finset.card_singleton s⟩
    · intro s₁ _ s₂ _ heq
      exact Finset.singleton_injective heq
    · intro A hA
      rw [Finset.mem_powersetCard] at hA
      obtain ⟨s, rfl⟩ := Finset.card_eq_one.mp hA.2
      exact ⟨s, Finset.singleton_subset_iff.mp hA.1, rfl⟩
    · intro s _
      simp [cRow]
  have h2 : ∑ A ∈ T.powersetCard 2, cRow m_row v_r A =
      - ∑ s ∈ T, ∑ t ∈ T.erase s, m_row s * m_row t := by
    have hcoeff2 : ∑ A ∈ T.powersetCard 2,
        ((∑ s : Fin 4 × Fin n, m_row s • X (K := ZMod 3) s) ^ 2).coeff A =
        ∑ s ∈ T, ∑ t ∈ T.erase s, m_row s * m_row t := by
      simp_rw [sq_linear_coeff]
      rw [Finset.sum_comm]
      calc ∑ s : Fin 4 × Fin n, ∑ A ∈ T.powersetCard 2, ∑ t : Fin 4 × Fin n,
            (if s ≠ t ∧ A = {s, t} then m_row s * m_row t else 0)
          = ∑ s : Fin 4 × Fin n, ∑ t : Fin 4 × Fin n, ∑ A ∈ T.powersetCard 2,
            (if s ≠ t ∧ A = {s, t} then m_row s * m_row t else 0) := by
            refine Finset.sum_congr rfl fun s _ => Finset.sum_comm
        _ = ∑ s ∈ T, ∑ t ∈ T.erase s, m_row s * m_row t := by
            calc ∑ s : Fin 4 × Fin n, ∑ t : Fin 4 × Fin n, ∑ A ∈ T.powersetCard 2,
                  (if s ≠ t ∧ A = {s, t} then m_row s * m_row t else 0)
                = ∑ s : Fin 4 × Fin n, ∑ t : Fin 4 × Fin n,
                  if s ∈ T ∧ t ∈ T.erase s then m_row s * m_row t else 0 := by
                  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
                  by_cases hst : s ∈ T ∧ t ∈ T.erase s
                  · have hne : s ≠ t := (Finset.mem_erase.mp hst.2).1.symm
                    have hmem : ({s, t} : Finset (Fin 4 × Fin n)) ∈ T.powersetCard 2 := by
                      rw [Finset.mem_powersetCard]
                      refine ⟨Finset.insert_subset hst.1 (Finset.singleton_subset_iff.mpr (Finset.erase_subset s T hst.2)), ?_⟩
                      exact Finset.card_pair hne
                    rw [if_pos hst, Finset.sum_eq_single {s, t}]
                    · simp [hne]
                    · intro A _ hAne; simp [hAne]
                    · intro hno; exact False.elim (hno hmem)
                  · rw [if_neg hst]
                    apply Finset.sum_eq_zero
                    intro A hA
                    rw [Finset.mem_powersetCard] at hA
                    split_ifs with h
                    · exfalso; apply hst
                      have hsA : s ∈ A := h.2 ▸ Finset.mem_insert_self s {t}
                      have htA : t ∈ A := h.2 ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self t)
                      exact ⟨hA.1 hsA, Finset.mem_erase.mpr ⟨h.1.symm, hA.1 htA⟩⟩
                    · rfl
              _ = ∑ s : Fin 4 × Fin n, if s ∈ T then ∑ t ∈ T.erase s, m_row s * m_row t else 0 := by
                  refine Finset.sum_congr rfl fun s _ => ?_
                  by_cases hs : s ∈ T
                  · simp only [hs, true_and, ↓reduceIte]
                    rw [Finset.sum_ite_mem, Finset.univ_inter]
                  · simp [hs]
              _ = ∑ s ∈ T, ∑ t ∈ T.erase s, m_row s * m_row t := by
                  rw [Finset.sum_ite_mem, Finset.univ_inter]
    calc ∑ A ∈ T.powersetCard 2, cRow m_row v_r A
        = ∑ A ∈ T.powersetCard 2,
            - ((∑ s : Fin 4 × Fin n, m_row s • X (K := ZMod 3) s) ^ 2).coeff A := by
          refine Finset.sum_congr rfl fun A hA => ?_
          rw [Finset.mem_powersetCard] at hA
          simp [cRow, hA.2]
      _ = - ∑ A ∈ T.powersetCard 2,
            ((∑ s : Fin 4 × Fin n, m_row s • X (K := ZMod 3) s) ^ 2).coeff A := by
          rw [Finset.sum_neg_distrib]
      _ = - ∑ s ∈ T, ∑ t ∈ T.erase s, m_row s * m_row t := by rw [hcoeff2]
  rw [h0, h1, h2]
  have hsq : (∑ s ∈ T, m_row s) ^ 2 =
      (∑ s ∈ T, (m_row s) ^ 2) + ∑ s ∈ T, ∑ t ∈ T.erase s, m_row s * m_row t := by
    rw [sq, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [← Finset.add_sum_erase T (fun t => m_row s * m_row t) hs, sq, add_comm]
  calc 1 - ((∑ s ∈ T, m_row s) - v_r) ^ 2
      = 1 - v_r ^ 2 + 2 * v_r * (∑ s ∈ T, m_row s) - (∑ s ∈ T, m_row s) ^ 2 := by ring
    _ = 1 - v_r ^ 2 + (∑ s ∈ T, 2 * v_r * m_row s) -
          ((∑ s ∈ T, (m_row s) ^ 2) + ∑ s ∈ T, ∑ t ∈ T.erase s, m_row s * m_row t) := by
        rw [Finset.mul_sum, hsq]
    _ = 1 - v_r ^ 2 + ∑ s ∈ T, (2 * v_r * m_row s - (m_row s) ^ 2) +
          - ∑ s ∈ T, ∑ t ∈ T.erase s, m_row s * m_row t := by
        rw [Finset.sum_sub_distrib]
        ring

lemma nullstellensatz_zmod3 (n : ℕ) {S : Finset (Fin 4 × Fin n)} (hS_card : S.card = 2 * n)
    (M : Fin n → Fin 4 × Fin n → ZMod 3) (v : Fin n → ZMod 3)
    (hS_coeff : (∏ r : Fin n, (∑ s : Fin 4 × Fin n, M r s • X (K := ZMod 3) s) ^ 2).coeff S ≠ 0) :
    ∃ T ∈ S.powerset, ∀ r : Fin n, ∑ s ∈ T, M r s = v r := by
  classical
  by_contra hno
  push Not at hno
  have hz3_sq : ∀ x : ZMod 3, x ≠ 0 → x ^ 2 = 1 := by decide
  have hLHS : ∑ T ∈ S.powerset, (-1 : ZMod 3) ^ (S.card - T.card) *
      ∏ r : Fin n, (1 - ((∑ s ∈ T, M r s) - v r) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro T hT
    obtain ⟨r, hr⟩ := hno T hT
    have hdiff : ∑ s ∈ T, M r s - v r ≠ 0 := sub_ne_zero.mpr hr
    have hfac : 1 - (∑ s ∈ T, M r s - v r) ^ 2 = 0 := by rw [hz3_sq _ hdiff, sub_self]
    rw [Finset.prod_eq_zero (Finset.mem_univ r) hfac, mul_zero]
  have hRHS : ∑ T ∈ S.powerset, (-1 : ZMod 3) ^ (S.card - T.card) *
      ∏ r : Fin n, (1 - ((∑ s ∈ T, M r s) - v r) ^ 2) =
      (-1 : ZMod 3) ^ n *
        (∏ r : Fin n, (∑ s : Fin 4 × Fin n, M r s • X (K := ZMod 3) s) ^ 2).coeff S := by
    have hexp : ∀ T ∈ S.powerset, ∏ r : Fin n, (1 - ((∑ s ∈ T, M r s) - v r) ^ 2) =
        ∑ F : Fin n → Finset (Fin 4 × Fin n),
          (if Finset.univ.biUnion F ⊆ T then 1 else 0) * ∏ r : Fin n, cRow (M r) (v r) (F r) := by
      intro T _
      have hrow : ∀ r : Fin n, 1 - ((∑ s ∈ T, M r s) - v r) ^ 2 =
          ∑ A : Finset (Fin 4 × Fin n), if A ⊆ T then cRow (M r) (v r) A else 0 := fun r => by
        rw [row_eval_eq]
        symm
        calc ∑ A : Finset (Fin 4 × Fin n), (if A ⊆ T then cRow (M r) (v r) A else 0)
            = ∑ A : Finset (Fin 4 × Fin n), (if A ∈ T.powerset then cRow (M r) (v r) A else 0) := by
              refine Finset.sum_congr rfl fun A _ => by simp [Finset.mem_powerset]
          _ = ∑ A ∈ T.powerset, cRow (M r) (v r) A := by rw [Finset.sum_ite_mem, Finset.univ_inter]
      simp_rw [hrow]
      rw [Fintype.prod_sum (fun r (A : Finset (Fin 4 × Fin n)) => if A ⊆ T then cRow (M r) (v r) A else 0)]
      refine Finset.sum_congr rfl fun F _ => ?_
      have hbi : Finset.univ.biUnion F ⊆ T ↔ ∀ r : Fin n, F r ⊆ T := by
        rw [Finset.biUnion_subset]
        exact ⟨fun h r => h r (Finset.mem_univ r), fun h r _ => h r⟩
      by_cases hsub : ∀ r : Fin n, F r ⊆ T
      · rw [if_pos (hbi.mpr hsub), one_mul]
        refine Finset.prod_congr rfl fun r _ => if_pos (hsub r)
      · rw [if_neg (fun h => hsub (hbi.mp h)), zero_mul]
        push Not at hsub
        obtain ⟨r, hr⟩ := hsub
        exact Finset.prod_eq_zero (Finset.mem_univ r) (if_neg hr)
    calc ∑ T ∈ S.powerset, (-1 : ZMod 3) ^ (S.card - T.card) *
          ∏ r : Fin n, (1 - ((∑ s ∈ T, M r s) - v r) ^ 2)
        = ∑ T ∈ S.powerset, ∑ F : Fin n → Finset (Fin 4 × Fin n),
            ((-1 : ZMod 3) ^ (S.card - T.card) *
              (if Finset.univ.biUnion F ⊆ T then 1 else 0)) * ∏ r : Fin n, cRow (M r) (v r) (F r) := by
          refine Finset.sum_congr rfl fun T hT => ?_
          rw [hexp T hT, Finset.mul_sum]
          refine Finset.sum_congr rfl fun F _ => by ring
      _ = ∑ F : Fin n → Finset (Fin 4 × Fin n),
            (∑ T ∈ S.powerset, (-1 : ZMod 3) ^ (S.card - T.card) *
              (if Finset.univ.biUnion F ⊆ T then 1 else 0)) * ∏ r : Fin n, cRow (M r) (v r) (F r) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun F _ => by rw [Finset.sum_mul]
      _ = ∑ F : Fin n → Finset (Fin 4 × Fin n),
            (if Finset.univ.biUnion F = S then 1 else 0) * ∏ r : Fin n, cRow (M r) (v r) (F r) := by
          refine Finset.sum_congr rfl fun F _ => ?_
          by_cases hsubS : Finset.univ.biUnion F ⊆ S
          · rw [altSum_indicator S (Finset.univ.biUnion F) hsubS]
          · have hneS : Finset.univ.biUnion F ≠ S := fun h => hsubS (h ▸ le_rfl)
            rw [if_neg hneS, zero_mul]
            have hsum0 : ∑ T ∈ S.powerset, (-1 : ZMod 3) ^ (S.card - T.card) *
                (if Finset.univ.biUnion F ⊆ T then 1 else 0) = 0 := by
              apply Finset.sum_eq_zero
              intro T hT
              rw [Finset.mem_powerset] at hT
              have hnot : ¬ Finset.univ.biUnion F ⊆ T := fun h => hsubS (h.trans hT)
              simp [hnot]
            rw [hsum0, zero_mul]
      _ = (-1 : ZMod 3) ^ n *
            (∏ r : Fin n, (∑ s : Fin 4 × Fin n, M r s • X (K := ZMod 3) s) ^ 2).coeff S := by
          rw [prod_coeff_eq_sum Finset.univ _ S, Finset.mul_sum]
          refine Finset.sum_congr rfl fun F _ => ?_
          by_cases huni : Finset.univ.biUnion F = S
          · by_cases hcard2 : ∀ r : Fin n, (F r).card = 2
            · have hsum_eq : (Finset.univ.biUnion F).card = ∑ r : Fin n, (F r).card := by
                rw [huni, hS_card]
                simp [hcard2, Finset.sum_const, smul_eq_mul, mul_comm]
              have hdisj := biUnion_card_eq_sum_imp_disjoint Finset.univ F hsum_eq
              rw [if_pos huni, one_mul, if_pos ⟨huni, hdisj, fun r hr => False.elim (hr (Finset.mem_univ r))⟩]
              calc ∏ r : Fin n, cRow (M r) (v r) (F r)
                  = ∏ r : Fin n, - ((∑ s : Fin 4 × Fin n, M r s • X (K := ZMod 3) s) ^ 2).coeff (F r) := by
                    refine Finset.prod_congr rfl fun r _ => by simp [cRow, hcard2 r]
                _ = (-1 : ZMod 3) ^ n *
                      ∏ r : Fin n, ((∑ s : Fin 4 × Fin n, M r s • X (K := ZMod 3) s) ^ 2).coeff (F r) := by
                    rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin]
            · push Not at hcard2
              obtain ⟨r₀, hr₀⟩ := hcard2
              have hgt_or_all_le : ∃ r : Fin n, 2 < (F r).card := by
                by_contra hle2
                push Not at hle2
                have hle₀ := hle2 r₀
                have hsum_lt : ∑ r : Fin n, (F r).card < ∑ _r : Fin n, 2 :=
                  Finset.sum_lt_sum (fun r _ => hle2 r) ⟨r₀, Finset.mem_univ r₀, by omega⟩
                simp [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin] at hsum_lt
                have hbi : 2 * n ≤ ∑ r : Fin n, (F r).card := hS_card ▸ huni ▸ Finset.card_biUnion_le
                omega
              obtain ⟨r₁, hr₁⟩ := hgt_or_all_le
              have hcRow0 : cRow (M r₁) (v r₁) (F r₁) = 0 := by
                have hc0 : (F r₁).card ≠ 0 := by omega
                have hc1 : (F r₁).card ≠ 1 := by omega
                have hc2 : (F r₁).card ≠ 2 := by omega
                simp [cRow, hc0, hc1, hc2]
              have hLHS0 : (if Finset.univ.biUnion F = S then (1 : ZMod 3) else 0) *
                  ∏ r : Fin n, cRow (M r) (v r) (F r) = 0 := by
                rw [Finset.prod_eq_zero (Finset.mem_univ r₁) hcRow0, mul_zero]
              have hw_lin : IsHomog 1 (∑ s : Fin 4 × Fin n, M r₁ s • X (K := ZMod 3) s) :=
                isHomog_sum fun s _ => isHomog_smul _ (isHomog_X s)
              have hsq_hom : IsHomog 2 ((∑ s : Fin 4 × Fin n, M r₁ s • X (K := ZMod 3) s) ^ 2) := by
                rw [sq]; exact isHomog_mul hw_lin hw_lin
              have hcoeff0 : ((∑ s : Fin 4 × Fin n, M r₁ s • X (K := ZMod 3) s) ^ 2).coeff (F r₁) = 0 :=
                hsq_hom (F r₁) (by omega)
              have hprod0 : ∏ r : Fin n, ((∑ s : Fin 4 × Fin n, M r s • X (K := ZMod 3) s) ^ 2).coeff (F r) = 0 :=
                Finset.prod_eq_zero (Finset.mem_univ r₁) hcoeff0
              rw [hLHS0]
              split_ifs <;> simp [hprod0]
          · simp [huni]
  rw [hLHS] at hRHS
  have hpow_ne : (-1 : ZMod 3) ^ n ≠ 0 := pow_ne_zero n (by decide)
  exact hS_coeff ((mul_eq_zero.mp hRHS.symm).resolve_left hpow_ne)

end Nullstellensatz

end SqFreeAlg

open scoped Pointwise in
theorem yu25_proof : ∀ n : ℕ, ∀ A : Fin 4 → Set (𝔽₃ n),
    (∀ i, Green26.IsCube (A i)) → ∑ i, A i = Set.univ := by
  intro n A hA
  choose φ hφ using hA
  apply Set.eq_univ_iff_forall.mpr
  intro v
  rw [Set.mem_finsetSum]
  by_cases hn : n = 0
  · subst hn
    have hv : v = ∑ k : Fin 4, φ k 0 := by
      ext i; exact Fin.elim0 i
    refine ⟨fun k => φ k 0, fun {k} _ => ?_, hv.symm⟩
    rw [hφ k]
    refine ⟨0, fun i => Fin.elim0 i, rfl⟩
  · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
    obtain ⟨S, hS_card, hS_coeff⟩ := SqFreeAlg.thm3_nonzero_coeff n hn1 φ
    obtain ⟨T, _, hT⟩ := SqFreeAlg.nullstellensatz_zmod3 n hS_card _ v hS_coeff
    let c : Fin 4 → 𝔽₃ n := fun k j => if (k, j) ∈ T then 1 else 0
    have hc_cube : ∀ k, c k ∈ Green26.StandardCube n := fun k j => by
      dsimp [c]
      split_ifs <;> simp
    have hsum : ∑ k : Fin 4, φ k (c k) = v := by
      ext r
      rw [Finset.sum_apply]
      have hc_exp : ∀ k : Fin 4, c k = ∑ j : Fin n, c k j • Pi.single j (1 : ZMod 3) := fun k => by
        ext j; simp [Pi.single_apply]
      have hLHS : ∑ k : Fin 4, φ k (c k) r = ∑ s ∈ T, φ s.1 (Pi.single s.2 (1 : ZMod 3)) r := by
        calc ∑ k : Fin 4, φ k (c k) r
            = ∑ k : Fin 4, ∑ j : Fin n, c k j * φ k (Pi.single j (1 : ZMod 3)) r := by
              refine Finset.sum_congr rfl fun k _ => ?_
              conv_lhs => rw [hc_exp k, map_sum, Finset.sum_apply]
              simp only [map_smul, Pi.smul_apply, smul_eq_mul]
          _ = ∑ s : Fin 4 × Fin n, if s ∈ T then φ s.1 (Pi.single s.2 (1 : ZMod 3)) r else 0 := by
              rw [← Fintype.sum_prod_type']
              refine Finset.sum_congr rfl fun p _ => ?_
              dsimp [c]
              split_ifs <;> simp
          _ = ∑ s ∈ T, φ s.1 (Pi.single s.2 (1 : ZMod 3)) r := by
              rw [← Finset.sum_filter]
              refine Finset.sum_congr ?_ (fun _ _ => rfl)
              ext s
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hLHS, hT r]
    refine ⟨fun k => φ k (c k), fun {k} _ => ?_, hsum⟩
    rw [hφ k]
    exact ⟨c k, hc_cube k, rfl⟩

end OMA.Yu25

theorem OMA.solution : type_of% @Green26.green_26.variants.yu25 :=
  OMA.Yu25.yu25_proof
