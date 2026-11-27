import FormalConjectures.ErdosProblems.«402»

/-! Reduce the Szegedy--Zaharescu assertion to the primitive Graham bound and
the presence of one extremal divisor. All dilations and reciprocal families
are handled here, including attainment of the maximum in both model cases. -/

namespace OMA.R_Erdos402_erdos_402_variants_szegedy_zaharescu_weak_R1
open Finset Filter

/-- The Graham inequality, expressed without rational divisions, for primitive families. -/
def H1 : Prop := ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ, A.card=n → 0∉A → A.gcd id=1 →
  ∃ a∈A, ∃ b∈A, n ≤ a / a.gcd b

/-- At equality, the primitive family contains the unit or the common multiple. -/
def H2 : Prop := ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ, A.card=n → 0∉A → A.gcd id=1 →
  (∀ a∈A, ∀ b∈A, a / a.gcd b ≤ n) → (∃ a∈A, ∃ b∈A, a / a.gcd b=n) →
  1∈A ∨ A.lcm id∈A

section

private lemma ratio_scale (k a b : ℕ) (hk : 0<k) :
    (k*a)/((k*a).gcd (k*b)) = a/a.gcd b := by
  rw [Nat.gcd_mul_left,Nat.mul_div_mul_left _ _ hk]

private lemma score_scale (A : Finset ℕ) (k : ℕ) (hk : 0<k) :
    ((A.image (k*·)) ×ˢ (A.image (k*·))).sup (fun p => p.1 / p.1.gcd p.2) = (A ×ˢ A).sup (fun p => p.1 / p.1.gcd p.2) := by
  apply le_antisymm
  · apply Finset.sup_le
    rintro ⟨a,b⟩ hab
    obtain ⟨⟨i,hi,rfl⟩,⟨j,hj,rfl⟩⟩ := (mem_product.mp hab).imp mem_image.mp mem_image.mp
    change (k*i)/((k*i).gcd (k*j)) ≤ (A ×ˢ A).sup (fun p => p.1 / p.1.gcd p.2)
    rw [ratio_scale k i j hk]
    exact Finset.le_sup (f:=fun p : ℕ×ℕ => p.1 / p.1.gcd p.2) (b:=(i,j)) (mem_product.mpr ⟨hi,hj⟩)
  · apply Finset.sup_le
    rintro ⟨a,b⟩ hab
    obtain ⟨ha,hb⟩ := mem_product.mp hab
    change a/a.gcd b ≤ _
    rw [←ratio_scale k a b hk]
    exact Finset.le_sup (f:=fun p : ℕ×ℕ => p.1 / p.1.gcd p.2) (b:=(k*a,k*b))
        (mem_product.mpr ⟨mem_image_of_mem (k*·) ha,mem_image_of_mem (k*·) hb⟩)

/-- Complementing divisors of a common multiple reverses each directed gcd quotient. -/
private lemma reciprocal_ratio {i j T : ℕ} (hi : 0 < i) (hj : 0 < j) (hT : 0 < T)
    (di : i∣T) (dj : j∣T) :
    (T/i)/((T/i).gcd (T/j)) = j/(j.gcd i) := by
  have left : (i*j)*(T/i)=T*j := by
    calc _ = (T/i*i)*j := by ring
         _ = _ := by rw [Nat.div_mul_cancel di]
  have right : (i*j)*(T/j)=T*i := by
    calc _ = (T/j*j)*i := by ring
         _ = _ := by rw [Nat.div_mul_cancel dj]
  rw [← ratio_scale (i*j) (T/i) (T/j) (Nat.mul_pos hi hj),left,right,ratio_scale T j i hT]

private lemma model_bound {n T : ℕ} (hT : 0<T) (dvd : ∀ i∈Icc 1 n,i∣T) :
    (((Icc 1 n).image (T/·)) ×ˢ ((Icc 1 n).image (T/·))).sup (fun p => p.1 / p.1.gcd p.2) ≤ n := by
  apply Finset.sup_le
  rintro ⟨a,b⟩ hab
  obtain ⟨⟨i,hi,rfl⟩,⟨j,hj,rfl⟩⟩ := (mem_product.mp hab).imp mem_image.mp mem_image.mp
  change (T/i)/((T/i).gcd (T/j)) ≤ n
  rw [reciprocal_ratio (mem_Icc.mp hi).1 (mem_Icc.mp hj).1 hT (dvd i hi) (dvd j hj)]
  exact (Nat.div_le_self ..).trans (mem_Icc.mp hj).2

private lemma ordinary_score {n : ℕ} (hn : 0<n) : ((Icc 1 n) ×ˢ (Icc 1 n)).sup (fun p => p.1 / p.1.gcd p.2) = n := by
  apply le_antisymm
  · apply Finset.sup_le
    rintro ⟨a,b⟩ p
    exact (Nat.div_le_self ..).trans (mem_Icc.mp (mem_product.mp p).1).2
  · have pair : (n,1) ∈ Icc 1 n ×ˢ Icc 1 n := mem_product.mpr
      ⟨mem_Icc.mpr ⟨hn,le_rfl⟩,mem_Icc.mpr ⟨le_rfl,hn⟩⟩
    simpa using Finset.le_sup (f:=fun p : ℕ×ℕ => p.1 / p.1.gcd p.2) pair

private lemma reciprocal_score {n T : ℕ} (hn : 0<n) (hT : 0<T)
    (dvd : ∀ i∈Icc 1 n,i∣T) : (((Icc 1 n).image (T/·)) ×ˢ ((Icc 1 n).image (T/·))).sup (fun p => p.1 / p.1.gcd p.2) = n := by
  apply (model_bound hT dvd).antisymm
  have h1 : 1 ∈ Icc 1 n := mem_Icc.mpr ⟨le_rfl,hn⟩
  have hn' : n ∈ Icc 1 n := mem_Icc.mpr ⟨hn,le_rfl⟩
  have P : (T/1,T/n) ∈ (Icc 1 n).image (T/·) ×ˢ (Icc 1 n).image (T/·) := Finset.mem_product.mpr
    ⟨mem_image_of_mem (T/·) h1,mem_image_of_mem (T/·) hn'⟩
  have bound := Finset.le_sup (f:=fun p : ℕ×ℕ => p.1 / p.1.gcd p.2) (b:=(T/1,T/n)) P
  change (T/1)/((T/1).gcd (T/n)) ≤ _ at bound
  rw [reciprocal_ratio (by decide : 0<1) hn hT (dvd 1 h1) (dvd n hn')] at bound
  simpa only [Nat.gcd_one_right,Nat.div_one] using bound

private lemma primitive {A : Finset ℕ} (ha : A.Nonempty) (hz : 0∉A) :
    ∃ B : Finset ℕ, ∃ k>0, A=B.image (k*·) ∧ B.card=A.card ∧ 0∉B ∧ B.gcd id=1 := by
  obtain ⟨u,hu⟩ := ha
  have u0 : u≠0 := fun e => hz (e ▸ hu)
  let k := A.gcd id
  let B := A.image (·/k)
  have hk : 0<k := by
    apply Nat.pos_of_ne_zero
    intro e
    exact u0 ((A.gcd_eq_zero_iff.mp e) u hu)
  have recover (i) (hi:i∈A) : k*(i/k)=i := Nat.mul_div_cancel' (Finset.gcd_dvd (f:=id) hi)
  have hA : A = B.image (k*·) := by
    ext i
    constructor
    · intro hi
      exact mem_image.mpr ⟨i/k,mem_image_of_mem _ hi,recover _ hi⟩
    · intro hi
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hi
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hu
      rwa [recover _ hj]
  refine ⟨B,k,hk,hA,card_image_of_injOn (fun i hi j hj h => ?_),?_,?_⟩
  · change i/k=j/k at h
    rw [←recover i hi,←recover j hj,h]
  · intro h
    obtain ⟨i,hi,eq⟩ := mem_image.mp h
    have iz : i=0 := by calc
      i = k*(i/k) := (recover i hi).symm
      _ = 0 := by rw [eq,mul_zero]
    exact hz (iz ▸ hi)
  · dsimp [B]
    rw [Finset.gcd_image]
    exact gcd_div_id_eq_one hu u0

private lemma classify {B : Finset ℕ} {n : ℕ} (card : B.card=n) (hz : 0∉B)
    (ub : ∀ a∈B, ∀ b∈B, a/a.gcd b≤n) (extreme : 1∈B ∨ B.lcm id∈B) :
    B=Icc 1 n ∨ ∃ t>0, B=(Icc 1 n).image (t*(Icc 1 n).lcm id / ·) := by
  have positive (a) (ha : a∈B) : 0<a := Nat.pos_of_ne_zero (fun e => hz (e ▸ ha))
  have fill (F : Finset ℕ) (hc : F.card=n) (sub : F⊆Icc 1 n) : F=Icc 1 n :=
    eq_of_subset_of_card_le sub (by simp [hc])
  rcases extreme with unit|top
  · left
    apply fill _ card
    intro a ha
    exact mem_Icc.mpr ⟨positive a ha,by simpa using ub a ha 1 unit⟩
  · right
    let T := B.lcm id
    have tpos : 0<T := positive _ top
    have dvd (b) (hb : b∈B) : b∣T := Finset.dvd_lcm (f:=id) hb
    have inv (b) (hb:b∈B) : T/(T/b)=b := Nat.div_div_self (dvd b hb) tpos.ne'
    let I := B.image (T/·)
    have inj : Set.InjOn (T/·) (B:Set ℕ) := by
      intro a ha b hb e
      change T/a=T/b at e
      rw [←inv a ha,←inv b hb,e]
    have ir : I = Icc 1 n := by
      apply fill _ ((card_image_of_injOn inj).trans card)
      intro i hi
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hi
      apply mem_Icc.mpr
      refine ⟨Nat.div_pos (Nat.le_of_dvd tpos (dvd b hb)) (positive b hb),?_⟩
      simpa only [Nat.gcd_eq_right (dvd b hb)] using ub T top b hb
    have im : I.image (T/·)=B := by
      ext b
      constructor
      · intro hb
        obtain ⟨i,hi,rfl⟩ := mem_image.mp hb
        obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
        rwa [inv j hj]
      · intro hb
        exact mem_image.mpr ⟨T/b,mem_image_of_mem _ hb,inv b hb⟩
    have dt : (Icc 1 n).lcm id ∣ T := by
      apply Finset.lcm_dvd
      intro i hi
      rw [←ir] at hi
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hi
      exact Nat.div_dvd_of_dvd (dvd b hb)
    obtain ⟨t,ht⟩ := dt
    have good : 0<t := by
      by_contra! z
      have tz : t=0 := by omega
      rw [tz,mul_zero] at ht
      omega
    refine ⟨t,good,?_⟩
    rw [←im,ir,ht,Nat.mul_comm t _]

end

theorem main : H1 → H2 → type_of% @Erdos402.erdos_402.variants.szegedy_zaharescu_weak := by
  intro graham rigid
  filter_upwards [graham, rigid, eventually_ge_atTop 1] with n hg hr hn
  intro A hA hz
  obtain ⟨B,k,hk,ae,hB,bz,bg⟩ := primitive (A:=A) (card_pos.mp (by omega)) hz
  have card := hB.trans hA
  obtain ⟨u,hu,v,hv,uv⟩ := hg B card bz bg
  have ub (a) (ha:a∈B) (b) (hb:b∈B) : a/a.gcd b ≤ (B ×ˢ B).sup (fun p => p.1 / p.1.gcd p.2) :=
    Finset.le_sup (f:=fun p : ℕ×ℕ => p.1 / p.1.gcd p.2) (b:=(a,b)) (mem_product.mpr ⟨ha,hb⟩)
  have base := uv.trans (ub u hu v hv)
  have sc : (A ×ˢ A).sup (fun p => p.1 / p.1.gcd p.2) = (B ×ˢ B).sup (fun p => p.1 / p.1.gcd p.2) := ae ▸ score_scale B k hk
  change n ≤ (A ×ˢ A).sup (fun p => p.1 / p.1.gcd p.2) ∧ (n=(A ×ˢ A).sup (fun p => p.1 / p.1.gcd p.2) ↔ _)
  refine ⟨sc ▸ base,?_,?_⟩
  · intro eq
    have bound (a) (ha:a∈B) (b) (hb:b∈B) : a/a.gcd b ≤ n := (ub a ha b hb).trans_eq (eq.trans sc).symm
    have ends := hr B card bz bg bound ⟨u,hu,v,hv,(bound u hu v hv).antisymm uv⟩
    rcases classify card bz bound ends with bm|⟨t,ht,bm⟩
    · exact ⟨k,hk,Or.inl (by rw [ae,bm])⟩
    · refine ⟨k*t,Nat.mul_pos hk ht,Or.inr ?_⟩
      rw [ae,bm,image_image]
      apply image_congr
      intro i hi
      change k*(t*(Icc 1 n).lcm id/i)=k*t*(Icc 1 n).lcm id/i
      have dvd : i ∣ t*(Icc 1 n).lcm id := (Finset.dvd_lcm (f:=id) hi).trans (dvd_mul_left _ _)
      rw [Nat.mul_assoc, Nat.mul_div_assoc k dvd]
  · rintro ⟨t,ht,hm|hm⟩
    · rw [hm,score_scale _ _ ht]
      exact (ordinary_score hn).symm
    · rw [hm]
      have nz : (Icc 1 n).lcm id ≠ 0 := lcm_ne_zero_iff.mpr fun i hi => Nat.ne_of_gt (mem_Icc.mp hi).1
      exact (reciprocal_score hn (Nat.mul_pos ht (Nat.pos_of_ne_zero nz))
        (fun i hi => (Finset.dvd_lcm (f:=id) hi).trans (dvd_mul_left _ _))).symm

end OMA.R_Erdos402_erdos_402_variants_szegedy_zaharescu_weak_R1
