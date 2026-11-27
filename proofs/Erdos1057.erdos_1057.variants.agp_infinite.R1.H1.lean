import OMAReductions.R_Erdos1057_erdos_1057_variants_agp_infinite_R1

/-!
The van Emde Boas–Kruyswijk–Meshulam bound on the Davenport constant.
At each index select the most frequent character value among the surviving
characters. Each step removes at least a fraction 1/e until the remainder
has at most e elements. The product of the resulting linear factors then
vanishes on every character. In a product-one-free sequence, summing its
expansion over the dual instead gives the nonzero group order.
-/
namespace Mesh1057
open Finset Real
open scoped Classical
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

noncomputable def survivors (f : ℕ → α → β) (S : Finset α) (U : Finset ℕ) (w : ℕ → β) :=
  S.filter fun x => ∀ i∈U, f i x ≠ w i

theorem thin (f : ℕ → α → β) (R : Finset β) (hR : R.Nonempty)
    {e : ℕ} (he : 0 < e) (hc : R.card≤e) (hf : ∀ i x, f i x∈R)
    (U : Finset ℕ) (S : Finset α) : ∃ w : ℕ → β, (∀ i, w i∈R) ∧
    (survivors f S U w).card ≤ S.card-U.card ∧
    ((survivors f S U w).card:ℝ) ≤ S.card * exp (-(U.card:ℝ)/e) := by
  classical
  induction U using Finset.induction_on with
  | empty =>
    obtain ⟨y,hy⟩ := hR
    exact ⟨fun _ => y,fun _ => hy,by simp [survivors],by simp [survivors]⟩
  | @insert i U hi ih =>
    obtain ⟨w,hw,hlin,hexp⟩ := ih
    let A := survivors f S U w
    let fiber (y : β) := A.filter fun x => f i x=y
    obtain ⟨y,hy,hm⟩ := exists_max_image R (fun b => (fiber b).card) hR
    have hsum : ∑ b∈R,(fiber b).card = A.card := by
      dsimp only [fiber]
      exact sum_card_fiberwise_eq_card_filter .. |>.trans (by rw [filter_eq_self.mpr (fun x _ => hf i x)])
    have hmul : A.card ≤ e*(fiber y).card := calc
      A.card = ∑ b∈R,(fiber b).card := hsum.symm
      _ ≤ ∑ _b∈R,(fiber y).card := sum_le_sum hm
      _ ≤ e*(fiber y).card := by simpa using Nat.mul_le_mul_right (fiber y).card hc
    let w' := Function.update w i y
    have eq : survivors f S (insert i U) w' = A \ fiber y := by
      ext x
      simp only [survivors,mem_filter,Finset.forall_mem_insert,mem_sdiff,A,fiber]
      have H : (∀ j∈U,f j x ≠ w' j) ↔ (∀ j∈U,f j x ≠ w j) := by
        apply forall_congr'; intro j; apply forall_congr'; intro hj
        rw [show w' j=w j from Function.update_of_ne (show j ≠ i from fun E => hi (E ▸ hj)) ..]
      rw [H,show w' i=y from Function.update_self ..]
      tauto
    have hsize := card_sdiff_of_subset (filter_subset (fun x => f i x=y) A)
    have hle := card_le_card (filter_subset (fun x => f i x=y) A)
    change _ = A.card-(fiber y).card at hsize
    change (fiber y).card≤A.card at hle
    have hr : (0:ℝ)<e := by exact_mod_cast he
    refine ⟨w',fun j => by by_cases h : j=i <;> simp [w',Function.update,h,hw,hy],?_,?_⟩
    · rw [eq,hsize,card_insert_of_notMem hi]
      change A.card ≤ _ at hlin
      by_cases h : (fiber y).card=0
      · have hzero : A.card=0 := by simpa only [h,mul_zero,Nat.le_zero] using hmul
        simp [hzero]
      · omega
    · rw [eq,hsize,Nat.cast_sub hle,card_insert_of_notMem hi,Nat.cast_add_one]
      have hreal : (A.card:ℝ) ≤ (e:ℝ)*(fiber y).card := by exact_mod_cast hmul
      have hfrac := (div_le_iff₀ hr).mpr (mul_comm (e:ℝ) _ ▸ hreal)
      have hfac := Real.add_one_le_exp (-(1:ℝ)/e)
      calc (A.card:ℝ)-(fiber y).card ≤ (A.card:ℝ)*(1-1/e) := by rw [mul_sub,mul_one,mul_one_div]; linarith
           _ ≤ (A.card:ℝ)*exp (-1/e) := mul_le_mul_of_nonneg_left (by simpa only [neg_div,sub_eq_add_neg,add_comm] using hfac) (by positivity)
           _ ≤ ((S.card:ℝ)*exp (-(U.card:ℝ)/e))*exp (-1/e) := mul_le_mul_of_nonneg_right hexp (exp_pos _).le
           _ = (S.card:ℝ)*exp (-((U.card:ℝ)+1)/e) := by rw [mul_assoc,←exp_add]; congr 2; ring

theorem cover [Fintype α] [Nonempty α] (f : ℕ → α → β) (R : Finset β) (hR : R.Nonempty)
    {e : ℕ} (he : 0<e) (hc : R.card≤e) (hf : ∀ i x, f i x∈R)
    (hn : e ≤ Fintype.card α) (T : Finset ℕ)
    (hT : (e:ℝ)*(1+log ((Fintype.card α:ℝ)/e)) ≤ T.card) :
    ∃ w : ℕ → β, (∀ i,w i∈R) ∧ ∀ x, ∃ i∈T,f i x=w i := by
  classical
  let N := Fintype.card α
  let L := (e:ℝ)*log ((N:ℝ)/e)
  let k := ⌈L⌉₊
  have hpos : (0:ℝ)<e := by exact_mod_cast he
  have hN : (0:ℝ)<N := by exact_mod_cast he.trans_le hn
  have hL : 0≤L := mul_nonneg hpos.le (log_nonneg ((one_le_div hpos).mpr (by exact_mod_cast hn)))
  have hTk : k+e≤T.card := by
    have h : L+(e:ℝ)≤T.card := by dsimp [L,N]; linarith
    simpa only [k,Nat.ceil_add_natCast hL] using (show ⌈L+(e:ℝ)⌉₊≤T.card from Nat.ceil_le.mpr h)
  obtain ⟨U,hUT,hk⟩ := exists_subset_card_eq (show k≤T.card by omega)
  obtain ⟨u,hu,_,hcount⟩ := thin f R hR he hc hf U univ
  let A := survivors f univ U u
  have hA : A.card ≤ e := by
    have hkl : L ≤ (k:ℝ) := Nat.le_ceil _
    have hx : -(k:ℝ)/e ≤ -log ((N:ℝ)/e) := by
      apply (div_le_iff₀ hpos).mpr; dsimp [L] at hkl; linarith
    have hc' : (A.card:ℝ) ≤ (N:ℝ)*exp (-(k:ℝ)/e) := by simpa [A,N,hk] using hcount
    have hend : (N:ℝ)*exp (-log ((N:ℝ)/e))=e := by rw [exp_neg,exp_log (div_pos hN hpos)]; field_simp
    exact_mod_cast hc'.trans ((mul_le_mul_of_nonneg_left (exp_le_exp.mpr hx) hN.le).trans_eq hend)
  obtain ⟨v,hv,hc',_⟩ := thin f R hR he hc hf (T \ U) A
  rw [card_sdiff_of_subset hUT,hk] at hc'
  have hem : survivors f A (T \ U) v=∅ := card_eq_zero.mp (by omega)
  refine ⟨fun i => if i∈U then u i else v i, fun i => by by_cases h : i∈U <;> simp [h,hu,hv],?_⟩
  intro x
  by_contra! h
  have hx : x∈A := by
    apply mem_filter.mpr ⟨mem_univ _,?_⟩
    intro i hi; simpa [hi] using h i (hUT hi)
  have hx' : x∈survivors f A (T \ U) v := by
    apply mem_filter.mpr ⟨hx,?_⟩
    intro i hi; obtain ⟨h1,h2⟩ := mem_sdiff.mp hi
    simpa [h2] using h i h1
  simp [hem] at hx'
end Mesh1057



namespace Mesh1057
open Finset Real
abbrev Dual (G : Type*) [CommGroup G] := AddChar (Additive G) ℂ
def charHom {G : Type*} [CommGroup G] (ψ : Dual G) : G →* ℂ where
  toFun t := ψ (Additive.ofMul t)
  map_one' := ψ.map_zero_eq_one
  map_mul' x y := ψ.map_add_eq_mul _ _

theorem davenport (G : Type) [CommGroup G] [Finite G] (T : Finset ℕ) (g : ℕ → G)
    (hT : (Monoid.exponent G:ℝ)*(1+log ((Nat.card G:ℝ)/(Monoid.exponent G:ℝ))) ≤ T.card) :
    ∃ I⊆T, I.Nonempty ∧ ∏ i∈I,g i=1 := by
  classical
  letI := Fintype.ofFinite G
  let e := Monoid.exponent G
  have hd : e ∣ Fintype.card G := Group.exponent_dvd_card
  have he : 0 < e := Nat.pos_of_dvd_of_pos hd Fintype.card_pos
  let R := Polynomial.nthRootsFinset e (1:ℂ)
  have hR : R.Nonempty := ⟨1,(Polynomial.mem_nthRootsFinset he _).mpr (one_pow _)⟩
  have hcard : R.card≤e := (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots e 1)
  let f (i : ℕ) (ψ : Dual G) := charHom ψ (g i)
  have hf (i : ℕ) (ψ : Dual G) : f i ψ∈R := by
    apply (Polynomial.mem_nthRootsFinset he _).mpr
    change (charHom ψ (g i)) ^ Monoid.exponent G = 1
    rw [←map_pow,Monoid.pow_exponent_eq_one,map_one]
  have hdim : Fintype.card (Dual G) = Nat.card G := by
    rw [Nat.card_eq_fintype_card,AddChar.card_eq]
    exact Fintype.card_congr Additive.ofMul.symm
  have hle : e ≤ Fintype.card (Dual G) := by
    rw [hdim,Nat.card_eq_fintype_card]; exact Nat.le_of_dvd Fintype.card_pos hd
  obtain ⟨w,hw,hcover⟩ := cover f R hR he hcard hf hle T (by rwa [hdim])
  have hnz (i : ℕ) : w i≠0 := by
    have eq := (Polynomial.mem_nthRootsFinset he _).mp (hw i)
    rintro hz
    simp [hz,zero_pow he.ne'] at eq
  let b (i : ℕ) := -(w i)⁻¹
  have kill (ψ : Dual G) : ∏ i∈T,(1+b i*f i ψ)=0 := by
    obtain ⟨i,hi,equal⟩ := hcover ψ
    exact prod_eq_zero hi (by simp [b,equal,hnz i])
  by_contra! hfree
  have orth (I : Finset ℕ) (hI : I∈T.powerset) :
      (∑ ψ : Dual G, ∏ i∈I,(b i*f i ψ)) = if I=∅ then (Fintype.card G:ℂ) else 0 := by
    by_cases hi : I=∅
    · simp [hi,hdim,Nat.card_eq_fintype_card]
    · have hg := hfree I (mem_powerset.mp hI) (nonempty_iff_ne_empty.mpr hi)
      have H (ψ : Dual G) : (∏ i∈I,f i ψ) = ψ (Additive.ofMul (∏ i∈I,g i)) :=
        (map_prod (charHom ψ) g I).symm
      simp_rw [prod_mul_distrib,H]
      rw [←mul_sum,AddChar.sum_apply_eq_ite]
      have h0 : Additive.ofMul (∏ i∈I,g i)≠0 := hg
      rw [if_neg h0,if_neg hi,mul_zero]
  have hall : (∑ ψ : Dual G, ∏ i∈T,(1+b i*f i ψ)) = (Fintype.card G:ℂ) := by
    simp_rw [prod_one_add]
    rw [sum_comm,sum_congr rfl orth]
    simp
  simp only [kill,sum_const_zero] at hall
  exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) hall.symm
end Mesh1057


theorem OMA.solution : OMA.R_Erdos1057_erdos_1057_variants_agp_infinite_R1.H1 := Mesh1057.davenport
