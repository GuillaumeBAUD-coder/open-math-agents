import OMAReductions.R_Erdos713_erdos_713_parts_i_R1

-- Credit: @zarnab222-dev
/-!
Pruning leaves from a finite connected cyclic graph produces a connected
bipartite core J of minimum degree at least two. In any host of minimum
degree at least the order q of the original graph, each deleted leaf can
be reinserted using a fresh neighbor. Passing to such a host costs at most
q*n edges. The extremal numbers for F and J are therefore asymptotically
equivalent whenever the edge count divided by n tends to infinity.

For a four-cycle core we double-count ordered paths of length two for the
upper bound. Over a finite field we use the affine polarity graph on pairs
(x,y), with adjacency y+t=x*s for distinct vertices (x,y),(s,t). Padding
this construction at prime-square orders yields the sharp constant 1/2
provided primes approach every large integer from below with relative error
tending to zero. Bertrand's postulate already gives unconditional bounds of
order n^(3/2). For the classical four-cycle extremal problem see Brown,
"On graphs that do not contain a Thomsen graph" (1966), and Erdős, Rényi
and Sós, "On a problem of graph theory" (1966).
-/
open Finset SimpleGraph
open scoped Classical
namespace E713Polarity

theorem free_of_common {W : Type*} (X : SimpleGraph W)
    (one : ∀ a b u v, a≠b → X.Adj a u → X.Adj b u → X.Adj a v → X.Adj b v → u=v) :
    (completeBipartiteGraph (Fin 2) (Fin 2)).Free X := by
  rintro ⟨e⟩
  have edge (i j : Fin 2) : X.Adj (e (Sum.inl i)) (e (Sum.inr j)) :=
    e.toHom.map_rel' (show (completeBipartiteGraph (Fin 2) (Fin 2)).Adj (Sum.inl i) (Sum.inr j) from Or.inl ⟨rfl,rfl⟩)
  have ne : e (Sum.inl 0) ≠ e (Sum.inl 1) := fun h => (by decide : (0 : Fin 2) ≠ 1) (Sum.inl.inj (e.injective h))
  have eq := one _ _ _ _ ne (edge 0 0) (edge 1 0) (edge 0 1) (edge 1 1)
  exact (by decide : (0:Fin 2) ≠ 1) (Sum.inr.inj (e.injective eq))

theorem witness (K : Type*) [Field K] [Fintype K] :
    ∃ G : SimpleGraph (K × K), (completeBipartiteGraph (Fin 2) (Fin 2)).Free G ∧
      (Fintype.card K)^2*(Fintype.card K-1) ≤ 2*G.edgeFinset.card := by
  classical
  let G : SimpleGraph (K × K) := {
    Adj p q := p ≠ q ∧ p.2+q.2=p.1*q.1
    symm := ⟨by intro a b h; exact ⟨h.1.symm,by simpa only [add_comm b.2,mul_comm b.1] using h.2⟩⟩
    loopless := ⟨fun a h => h.1 rfl⟩ }
  refine ⟨G,?_,?_⟩
  · apply free_of_common
    intro a b u v ne au bu av bv
    have dx : a.1≠b.1 := by
      intro h
      apply ne
      apply Prod.ext h
      have h1 := au.2
      rw [h] at h1
      exact add_right_cancel (h1.trans bu.2.symm)
    have zero : (a.1-b.1)*(u.1-v.1)=0 := by
      linear_combination -au.2+bu.2+av.2-bv.2
    have x := sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left (sub_ne_zero.mpr dx))
    refine Prod.ext x ?_
    have h := au.2
    rw [x] at h
    exact add_left_cancel (h.trans av.2.symm)
  · have per (p : K × K) : Fintype.card K-1 ≤ G.degree p := by
      let f : K ↪ K × K := ⟨fun x => (x,p.1*x-p.2),fun x y h => congrArg Prod.fst h⟩
      let T := (univ : Finset K).erase p.1
      have sub : T.map f ⊆ G.neighborFinset p := by
        intro w hw
        obtain ⟨x,hx,rfl⟩ := mem_map.mp hw
        apply (G.mem_neighborFinset _ _).mpr
        refine ⟨fun eq => (mem_erase.mp hx).1 (congrArg Prod.fst eq).symm,?_⟩
        change p.2+(p.1*x-p.2)=p.1*x
        ring
      have h := card_le_card sub
      rw [card_map,G.card_neighborFinset_eq_degree] at h
      simpa [T] using h
    have h := sum_le_sum (s:=univ) fun p _ => per p
    rw [sum_const,card_univ,smul_eq_mul,Fintype.card_prod,G.sum_degrees_eq_twice_card_edges] at h
    rw [pow_two]
    convert! h using 1 <;> congr!
theorem common_of_free {W : Type*} (X : SimpleGraph W) (free : (completeBipartiteGraph (Fin 2) (Fin 2)).Free X)
    (a b u v : W) (ne : a ≠ b)
    (au : X.Adj a u) (bu : X.Adj b u) (av : X.Adj a v) (bv : X.Adj b v) : u=v := by
  by_contra uv
  let f : Fin 2 ⊕ Fin 2 → W := Sum.elim ![a,b] ![u,v]
  apply free
  refine ⟨⟨⟨f,?_⟩,?_⟩⟩
  · rintro (i|i) (j|j) h
    · simp [completeBipartiteGraph] at h
    · fin_cases i <;> fin_cases j <;> first | exact au | exact bu | exact av | exact bv
    · fin_cases i <;> fin_cases j <;> first | exact au.symm | exact bu.symm | exact av.symm | exact bv.symm
    · simp [completeBipartiteGraph] at h
  · have aU := au.ne
    have bU := bu.ne
    have aV := av.ne
    have bV := bv.ne
    rintro (i|i) (j|j) h <;> fin_cases i <;> fin_cases j <;> simp_all [f]

theorem edge_upper {W : Type*} [Fintype W] (X : SimpleGraph W) (free : (completeBipartiteGraph (Fin 2) (Fin 2)).Free X) :
    (2*X.edgeFinset.card)^2 ≤ Fintype.card W*(Fintype.card W*(Fintype.card W-1)+2*X.edgeFinset.card) := by
  classical
  let P (v : W) := (X.neighborFinset v).offDiag
  have pair : ((univ : Finset W) : Set W).PairwiseDisjoint P := by
    intro u _ v _ ne
    apply Finset.disjoint_left.mpr
    rintro ⟨a,b⟩ hu hv
    obtain ⟨ha,hb,ab⟩ := mem_offDiag.mp hu
    obtain ⟨ka,kb,_⟩ := mem_offDiag.mp hv
    exact ne (common_of_free X free a b u v ab ((X.mem_neighborFinset _ _).mp ha).symm
      ((X.mem_neighborFinset _ _).mp hb).symm ((X.mem_neighborFinset _ _).mp ka).symm
      ((X.mem_neighborFinset _ _).mp kb).symm)
  have sub : univ.biUnion P ⊆ (univ : Finset W).offDiag := by
    intro p hp
    obtain ⟨v,_,h⟩ := mem_biUnion.mp hp
    exact mem_offDiag.mpr ⟨mem_univ _,mem_univ _,(mem_offDiag.mp h).2.2⟩
  have cap := card_le_card sub
  rw [card_biUnion pair,Finset.offDiag_card,card_univ] at cap
  rw [← Nat.mul_sub_one] at cap
  have per (v) : (P v).card+X.degree v = X.degree v^2 := by
    change (X.neighborFinset v).offDiag.card + X.degree v = X.degree v^2
    rw [Finset.offDiag_card,X.card_neighborFinset_eq_degree]
    rw [← Nat.mul_sub_one]
    cases X.degree v with
    | zero => simp
    | succ d => simp; ring
  have sum := sum_congr (s₁:=(univ : Finset W)) rfl (fun v _ => per v)
  rw [sum_add_distrib,X.sum_degrees_eq_twice_card_edges] at sum
  have cs := sq_sum_le_card_mul_sum_sq (s:=(univ : Finset W)) (f:=fun v => X.degree v)
  rw [card_univ,X.sum_degrees_eq_twice_card_edges] at cs
  exact cs.trans (Nat.mul_le_mul_left _ (by omega))
theorem extremal_upper (n : ℕ) :
    (2*extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2)))^2 ≤ n*(n*(n-1)+2*extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2))) := by
  classical
  have nb : (completeBipartiteGraph (Fin 2) (Fin 2)) ≠ ⊥ := by
    intro empty
    have e : (completeBipartiteGraph (Fin 2) (Fin 2)).Adj (Sum.inl 0) (Sum.inr 0) := Or.inl ⟨rfl,rfl⟩
    rw [empty] at e
    exact e
  obtain ⟨X,_,hex⟩ := exists_isExtremal_free (V:=Fin n) nb
  obtain ⟨fr,he⟩ := isExtremal_free_iff.mp hex
  have bound := edge_upper X fr
  have eq : X.edgeFinset.card = extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2)) := by convert! he using 1 <;> simp
  rw [Fintype.card_fin] at bound
  convert! bound using 1 <;> rw [← eq] <;> congr!


end E713Polarity
namespace E713Amplify
theorem padding {V W : Type*} [Fintype W] (G : SimpleGraph V) (active : ∀ v, ¬G.IsIsolated v)
    (X : SimpleGraph W) (free : G.Free X) (m : ℕ) (fit : Fintype.card W ≤ m) :
    X.edgeFinset.card ≤ extremalNumber m G := by
  classical
  let k := m-Fintype.card W
  let Z := X ⊕g (⊥ : SimpleGraph (Fin k))
  have hf : G.Free Z := by
    rintro ⟨e⟩
    have original (v : V) : ∃ w : W, e v = Sum.inl w := by
      cases h : e v with
      | inl w => exact ⟨w,rfl⟩
      | inr i =>
        obtain ⟨u,adj⟩ := exists_adj_iff_not_isIsolated.mpr (active v)
        have a := e.toHom.map_rel' adj
        change Z.Adj (e v) (e u) at a
        rw [h] at a
        cases hu : e u with
        | inl t => rw [hu] at a; exact (not_adj_sum_inl_inr t i a.symm).elim
        | inr j => rw [hu] at a; exact (sum_adj_inr.mp a).elim
    choose f he using original
    apply free
    refine ⟨⟨⟨f,?_⟩,?_⟩⟩
    · intro a b adj
      have h := e.toHom.map_rel' adj
      change Z.Adj (e a) (e b) at h
      rw [he a,he b] at h
      exact sum_adj_inl.mp h
    · intro a b eq
      exact e.injective ((he a).trans ((congrArg Sum.inl eq).trans (he b).symm))
  have sumedges : Z.edgeFinset.card=X.edgeFinset.card := by
    simp only [Z,edgeFinset_card]
    have eq := Fintype.card_congr (edgeSetSumEquiv (G:=X) (H:=(⊥ : SimpleGraph (Fin k))))
    simpa using eq
  have hh := card_edgeFinset_le_extremalNumber hf
  have sz : Fintype.card (W ⊕ Fin k)=m := by simp [k,fit]
  simpa only [sumedges,sz] using hh



end E713Amplify
namespace E713Interpolation
open E713Polarity Filter Asymptotics
open scoped Topology

theorem active (v) : ¬(completeBipartiteGraph (Fin 2) (Fin 2)).IsIsolated v := by
  apply exists_adj_iff_not_isIsolated.mp
  cases v with
  | inl i => exact ⟨Sum.inr 0,Or.inl ⟨rfl,rfl⟩⟩
  | inr j => exact ⟨Sum.inl 0,Or.inr ⟨rfl,rfl⟩⟩

theorem lower (n p : ℕ) (prime : p.Prime) (fit : p^2 ≤ n) :
    p^3 ≤ 2*extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2)) + p^2 := by
  classical
  let : Fact p.Prime := ⟨prime⟩
  obtain ⟨G,free,edge⟩ := witness (ZMod p)
  have sz : Fintype.card (ZMod p × ZMod p) ≤ n := by simpa [pow_two] using fit
  have pad := E713Amplify.padding (completeBipartiteGraph (Fin 2) (Fin 2)) active G free n sz
  rw [ZMod.card] at edge
  have pp : p-1+1=p := by have := prime.pos; omega
  calc p^3 = p^2*((p-1)+1) := by rw [pp]; ring
       _ ≤ 2*extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2))+p^2 := by rw [Nat.mul_add,Nat.mul_one]; change _ ≤ 2*G.edgeFinset.card at edge; omega

theorem upper (n : ℕ) : 2*(extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2)) : ℝ) ≤ n*Real.sqrt n+n := by
  let e : ℝ := 2*(extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2)) : ℝ)
  have cheap : (2*extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2)))^2 ≤ n*(n*n+2*extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2))) := by
    apply (extremal_upper n).trans
    gcongr
    omega
  have h : e^2 ≤ (n:ℝ)*((n:ℝ)*(n:ℝ)+e) := by dsimp [e]; exact_mod_cast cheap
  have base : 0 ≤ (n:ℝ)*Real.sqrt n := by positivity
  have sq := Real.sq_sqrt (Nat.cast_nonneg n)
  change e ≤ _
  by_contra! large
  have pos : 0<e := by linarith [Nat.cast_nonneg (α:=ℝ) n]
  have L := mul_lt_mul_of_pos_right large pos
  have R := mul_le_mul_of_nonneg_left (show (n:ℝ)*Real.sqrt n ≤ e by linarith [Nat.cast_nonneg (α:=ℝ) n]) base
  nlinarith only [L,R,h,congrArg (fun x : ℝ => (n:ℝ)^2*x) sq]

/-- A uniform lower estimate independent of any prime-gap asymptotic. -/
theorem lower_uniform (n : ℕ) (large : 16 ≤ n) :
    (Nat.sqrt n)^3 ≤ 32*extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2)) := by
  let k := Nat.sqrt n
  have h4 : 4 ≤ k := Nat.le_sqrt.mpr (by omega)
  have hdiv : k/2 ≠ 0 := by omega
  obtain ⟨p,prime,lo,hi⟩ := Nat.exists_prime_lt_and_le_two_mul _ hdiv
  have pk : p ≤ k := by omega
  have half : k ≤ 2*p := by omega
  have fit : p^2 ≤ n := (Nat.pow_le_pow_left pk 2).trans (by simpa [pow_two,k] using Nat.sqrt_le n)
  have lb := lower n p prime fit
  have p2 : 2 ≤ p := prime.two_le
  have twice := Nat.mul_le_mul_left (p^2) p2
  have cube := Nat.pow_le_pow_left half 3
  change k^3 ≤ _
  nlinarith only [lb,twice,cube]

end E713Interpolation
namespace E713Interpolation
open E713Polarity Filter Asymptotics
open scoped Topology

theorem sqrt_floor_ratio : Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ)/Real.sqrt n) atTop (𝓝 1) := by
  have inv : Tendsto (fun n : ℕ => (Real.sqrt (n:ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using (tendsto_const_nhds (x:=(1:ℝ))).sub inv) tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have r : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    apply (le_div_iff₀ r).mpr
    rw [sub_mul,inv_mul_cancel₀ r.ne',one_mul]
    linarith [Real.real_sqrt_le_nat_sqrt_succ (a:=n)]
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have r : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    simpa only [div_le_one r] using (Real.nat_sqrt_le_real_sqrt (a:=n))

theorem square_asymptotic (p : ℕ → ℕ) (prime : ∀ᶠ k in atTop, (p k).Prime ∧ p k ≤ k)
    (dense : Tendsto (fun k : ℕ => (p k : ℝ)/k) atTop (𝓝 1)) :
    IsEquivalent atTop (fun n : ℕ => (extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2)) : ℝ))
      (fun n => (1/2:ℝ)*(n:ℝ)^(3/2:ℝ)) := by
  let r (n : ℕ) := Real.sqrt (n:ℝ)
  let t (n : ℕ) := p (Nat.sqrt n)
  have top : Tendsto Nat.sqrt atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop (k*k)] with n hn
    exact Nat.le_sqrt.mpr hn
  have near : Tendsto (fun n => (t n:ℝ)/r n) atTop (𝓝 1) := by
    have prod := (dense.comp top).mul sqrt_floor_ratio
    rw [one_mul] at prod
    apply prod.congr'
    filter_upwards [top.eventually (eventually_ge_atTop (1:ℕ))] with n hn
    change ((t n:ℝ)/(Nat.sqrt n:ℝ))*((Nat.sqrt n:ℝ)/r n) = _
    have h : (Nat.sqrt n:ℝ) ≠ 0 := by exact_mod_cast (show Nat.sqrt n ≠ 0 by omega)
    field_simp
  have inv : Tendsto (fun n => (r n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have low : Tendsto (fun n => ((t n:ℝ)/r n)^3-(r n)⁻¹) atTop (𝓝 1) := by simpa using (near.pow 3).sub inv
  have up : Tendsto (fun n => 1+(r n)⁻¹) atTop (𝓝 1) := by simpa using (tendsto_const_nhds (x:=(1:ℝ))).add inv
  have pos : ∀ᶠ n : ℕ in atTop, 0<(n:ℝ) := by filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn; exact_mod_cast (show 0<n by omega)
  have norm : Tendsto (fun n : ℕ => 2*(extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2)):ℝ)/((n:ℝ)*r n)) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' low up
    · filter_upwards [top.eventually prime,pos] with n hp hn
      have h := lower n (t n) hp.1 ((Nat.pow_le_pow_left hp.2 2).trans (by simpa [pow_two] using Nat.sqrt_le n))
      have fit : (t n)^2 ≤ n := (Nat.pow_le_pow_left hp.2 2).trans (by simpa [pow_two] using Nat.sqrt_le n)
      have hN : (t n)^3 ≤ 2*extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2))+n := h.trans (Nat.add_le_add_left fit _)
      have realN : (t n:ℝ)^3 ≤ 2*(extremalNumber n (completeBipartiteGraph (Fin 2) (Fin 2)):ℝ)+n := by exact_mod_cast hN
      have hr : 0<r n := Real.sqrt_pos.mpr hn
      have sq : r n ^2 = n := Real.sq_sqrt hn.le
      rw [← sq] at realN ⊢
      field_simp [hr.ne']
      nlinarith
    · filter_upwards [pos] with n hn
      have hr : 0<r n := Real.sqrt_pos.mpr hn
      have h := upper n
      apply (div_le_iff₀ (mul_pos hn hr)).mpr
      calc _ ≤ (n:ℝ)*r n+n := h
           _ = _ := by field_simp
  rw [isEquivalent_iff_tendsto_one]
  · apply norm.congr'
    filter_upwards [pos] with n hn
    have power : (n:ℝ)^(3/2:ℝ) = n*r n := by
      rw [show (3/2:ℝ) = 1+(1/2:ℝ) by norm_num,Real.rpow_add hn,Real.rpow_one,← Real.sqrt_eq_rpow]
    simp only [Pi.div_apply,power]
    ring
  · filter_upwards [pos] with n hn
    dsimp
    positivity
end E713Interpolation
/- Pruning leaves preserves embeddings into hosts of sufficiently high minimum degree. -/
open SimpleGraph Finset
open scoped Classical
namespace E713Prune

theorem extend_leaf {V W : Type*} [Fintype V] [Fintype W] (F : SimpleGraph V) (x y : V)
    (touch : F.Adj x y) (unique : ∀ z, F.Adj x z → z=y) (X : SimpleGraph W)
    (high : ∀ w, Fintype.card V ≤ X.degree w) (copy : F.induce {x}ᶜ ⊑ X) : F ⊑ X := by
  classical
  obtain ⟨e⟩ := copy
  let S : Set V := {x}ᶜ
  let away : y ∈ S := touch.ne.symm
  let T := (univ : Finset S).image (fun v => e v)
  have sz : Fintype.card S = Fintype.card V-1 := by
    change Fintype.card (↑({x}ᶜ : Set V)) = _
    rw [Fintype.card_compl_set]
    simp
  have size : T.card < (X.neighborFinset (e ⟨y,away⟩)).card := by
    have h : T.card ≤ (univ : Finset S).card := card_image_le
    rw [card_univ,sz] at h
    rw [X.card_neighborFinset_eq_degree]
    have pos := Fintype.card_pos_iff.mpr (show Nonempty V from ⟨x⟩)
    have hd := high (e ⟨y,away⟩)
    omega
  obtain ⟨z,hz,fresh⟩ := exists_mem_notMem_of_card_lt_card size
  have unused (v : S) : z ≠ e v := fun h => fresh (mem_image.mpr ⟨v,mem_univ _,h.symm⟩)
  let f (a : V) : W := if h : a=x then z else e ⟨a,h⟩
  have edge : X.Adj (e ⟨y,away⟩) z := (X.mem_neighborFinset _ _).mp hz
  refine ⟨⟨⟨f,?_⟩,?_⟩⟩
  · intro a b ab
    by_cases ax : a=x
    · subst a
      obtain rfl := unique _ ab
      simpa [f,ab.ne.symm] using edge.symm
    by_cases bx : b=x
    · subst b
      obtain rfl := unique _ ab.symm
      simpa [f,ab.ne] using edge
    exact (by simpa [f,ax,bx] using (e.toHom.map_rel' (show (F.induce S).Adj ⟨a,ax⟩ ⟨b,bx⟩ from ab)))
  · intro a b eq
    change f a=f b at eq
    by_cases ax : a=x <;> by_cases bx : b=x
    · exact ax.trans bx.symm
    · exact (unused ⟨b,bx⟩ (by simpa [f,ax,bx] using eq)).elim
    · exact (unused ⟨a,ax⟩ (by simpa [f,ax,bx] using eq.symm)).elim
    · exact congrArg Subtype.val (e.injective (by simpa [f,ax,bx] using eq))

theorem core {V : Type} [Fintype V] (F : SimpleGraph V) (conn : F.Connected)
    (bip : F.IsBipartite) (many : Fintype.card V ≤ F.edgeFinset.card) :
    ∃ (r : ℕ) (J : SimpleGraph (Fin r)), J.Connected ∧ J.IsBipartite ∧
      (∀ v, 2 ≤ J.degree v) ∧ J ⊑ F ∧
      ∀ (W : Type) [Fintype W] (X : SimpleGraph W),
        (∀ w, Fintype.card V ≤ X.degree w) → J ⊑ X → F ⊑ X := by
  classical
  by_cases min : ∀ v, 2 ≤ F.degree v
  · let e := Fintype.equivFin V
    let J := F.map e
    let iso : F ≃g J := Iso.map e F
    refine ⟨_,J,iso.connected_iff.mp conn,Colorable.of_hom iso.symm.toHom bip,?_,iso.symm.isContained,?_⟩
    · intro v
      obtain ⟨u,rfl⟩ := iso.surjective v
      have h := Fintype.card_congr (iso.mapNeighborSet u)
      have eq : F.degree u = J.degree (iso u) := by
        rw [← J.card_neighborSet_eq_degree,← F.card_neighborSet_eq_degree]
        convert! h using 1
      convert! (min u).trans_eq eq using 1 <;> congr!
    · intro W _ X _ h
      exact iso.isContained.trans h
  push Not at min
  obtain ⟨x,hx⟩ := min
  have nonsing : Nontrivial V := by
    by_contra! small
    let : Subsingleton V := small
    have h := Fintype.card_le_one_iff_subsingleton.mpr small
    have p := Fintype.card_pos_iff.mpr (show Nonempty V from ⟨x⟩)
    have n1 : Fintype.card V = 1 := by omega
    have bot : F=⊥ := by
      ext a b
      have e := Subsingleton.elim a b
      subst b
      simp
    subst F
    simp [n1] at many
  let : Nontrivial V := nonsing
  have pos := conn.preconnected.degree_pos_of_nontrivial x
  have deg : F.degree x=1 := by omega
  have adj := exists_adj_iff_not_isIsolated.mpr (fun h => by have := h.degree_eq_zero; omega : ¬ F.IsIsolated x)
  obtain ⟨y,xy⟩ := adj
  have single : (F.neighborSet x).Subsingleton := by
    intro a ha b hb
    apply card_le_one.mp (show (F.neighborFinset x).card ≤ 1 by rw [F.card_neighborFinset_eq_degree,deg]) a _ b _
    · exact (F.mem_neighborFinset x a).mpr ha
    · exact (F.mem_neighborFinset x b).mpr hb
  let S : Set V := {x}ᶜ
  let Y := F.induce S
  have pre : Y.Preconnected := conn.preconnected.induce_of_degree_eq_one (by
    intro v hv
    have eq : v=x := by simpa [S] using hv
    exact eq ▸ single)
  let : Nonempty S := ⟨⟨y,xy.ne.symm⟩⟩
  have cY : Y.Connected := ⟨pre⟩
  have bY : Y.IsBipartite := Colorable.of_hom (Copy.induce F S).toHom bip
  have sz : Fintype.card S = Fintype.card V-1 := by
    change Fintype.card (↑({x}ᶜ : Set V)) = _
    rw [Fintype.card_compl_set]
    simp
  have edges : Y.edgeFinset.card = F.edgeFinset.card-1 := by
    calc _ = (F.deleteIncidenceSet x).edgeFinset.card := F.card_edgeFinset_induce_compl_singleton x
         _ = _ := by rw [F.card_edgeFinset_deleteIncidenceSet,deg]
  have mY : Fintype.card S ≤ Y.edgeFinset.card := by rw [sz,edges]; omega
  obtain ⟨r,J,cj,bj,mj,sub,lift⟩ := core Y cY bY mY
  refine ⟨r,J,cj,bj,mj,sub.trans ⟨Copy.induce F S⟩,?_⟩
  intro W _ X high copy
  apply extend_leaf F x y xy (fun z hz => single hz xy) X high
  exact lift W X (fun w => (by rw [sz]; exact (Nat.sub_le ..).trans (high w))) copy
termination_by Fintype.card V
decreasing_by
  rw [sz]
  have := Fintype.card_pos_iff.mpr (show Nonempty V from ⟨x⟩)
  omega
end E713Prune

namespace E713Prune
open SimpleGraph Finset
open scoped Classical
theorem core_above {V : Type*} [Fintype V] [DecidableEq V]
    (X : SimpleGraph V) [DecidableRel X.Adj] (q C : ℕ)
    (large : q * Fintype.card V + C < X.edgeFinset.card) :
    ∃ U : Finset V, C < (X.induce (U : Set V)).edgeFinset.card ∧
      ∀ x : (U : Set V), q ≤ (X.induce (U : Set V)).degree x := by
  classical
  let edges (U : Finset V) := X.edgeFinset ∩ U.sym2
  have start : ∃ k, ∃ U : Finset V, U.card = k ∧ q*U.card+C < (edges U).card := by
    refine ⟨_,univ,rfl,?_⟩
    simpa [edges] using large
  obtain ⟨U,hU,dense⟩ := Nat.find_spec start
  have edgeCount : (edges U).card = (X.induce (U : Set V)).edgeFinset.card := by
    rw [← X.card_filter_edgeFinset_toFinset_subset, X.filter_edgeFinset_toFinset_subset]
  refine ⟨U,by rw [← edgeCount]; omega,?_⟩
  intro x
  let inside := X.neighborFinset x.val ∩ U
  have deg : (X.induce (U : Set V)).degree x = inside.card := by
    have mapEq := SimpleGraph.map_neighborFinset_induce (G := X) (s := (U : Set V)) x
    have count := congrArg Finset.card mapEq
    rw [card_map,card_neighborFinset_eq_degree,Finset.toFinset_coe] at count
    convert! count using 1 <;> congr!
  have cover : edges U ⊆ edges (U.erase x.val) ∪ inside.image (fun y => s(x.val,y)) := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro he
      obtain ⟨hab,hends⟩ := mem_inter.mp he
      obtain ⟨ha,hb⟩ := mk_mem_sym2_iff.mp hends
      have adj : X.Adj a b := X.mem_edgeFinset.mp hab
      by_cases ax : a = x.val
      · subst a
        exact mem_union_right _ (mem_image.mpr ⟨b,mem_inter.mpr
          ⟨(X.mem_neighborFinset x.val b).mpr adj,hb⟩,rfl⟩)
      by_cases bx : b = x.val
      · subst b
        exact mem_union_right _ (mem_image.mpr ⟨a,mem_inter.mpr
          ⟨(X.mem_neighborFinset x.val a).mpr adj.symm,ha⟩,Sym2.eq_swap⟩)
      exact mem_union_left _ (mem_inter.mpr ⟨hab,mk_mem_sym2_iff.mpr
        ⟨mem_erase.mpr ⟨ax,ha⟩,mem_erase.mpr ⟨bx,hb⟩⟩⟩)
  have lost := (card_le_card cover).trans (card_union_le ..)
  have cost : (inside.image (fun y => s(x.val,y))).card ≤ inside.card := card_image_le
  have smaller : (U.erase x.val).card < Nat.find start := hU ▸ card_erase_lt_of_mem x.property
  have thin : (edges (U.erase x.val)).card ≤ q * (U.erase x.val).card + C := by
    by_contra! h
    exact Nat.find_min start smaller ⟨_,rfl,h⟩
  have change := congrArg (q * ·) (card_erase_add_one x.property)
  simp only [Nat.mul_add,Nat.mul_one] at change
  omega

set_option maxHeartbeats 1200000 in
theorem profile {V J : Type} [Fintype V] [Fintype J] (F : SimpleGraph V) (H : SimpleGraph J)
    (sub : H ⊑ F) (active : ∀ v, ¬H.IsIsolated v)
    (lift : ∀ (W : Type) [Fintype W] (X : SimpleGraph W), (∀ w, Fintype.card V ≤ X.degree w) → H ⊑ X → F ⊑ X)
    (n : ℕ) : extremalNumber n H ≤ extremalNumber n F ∧
      extremalNumber n F ≤ Fintype.card V*n+extremalNumber n H := by
  classical
  constructor
  · have goal : extremalNumber (Fintype.card (Fin n)) H ≤ extremalNumber (Fintype.card (Fin n)) F := by
      apply (extremalNumber_le_iff ..).mpr
      intro X _ free
      exact card_edgeFinset_le_extremalNumber (H:=F) (G:=X) (fun ff => free (sub.trans ff))
    simpa using goal
  · rw [← Fintype.card_fin n,extremalNumber_le_iff]
    intro X _ free
    by_contra! large
    obtain ⟨U,many,high⟩ := core_above X (Fintype.card V) (extremalNumber (Fintype.card (Fin n)) H) large
    let Y := X.induce (U : Set (Fin n))
    have avoid : H.Free Y := by
      intro h
      apply free
      apply IsContained.trans _ (show Y ⊑ X from ⟨Copy.induce X (U : Set (Fin n))⟩)
      apply @lift (↑(U : Set (Fin n))) inferInstance Y _ h
      intro w
      convert! high w using 1 <;> congr!
    have fit : Fintype.card (↑(U : Set (Fin n))) ≤ Fintype.card (Fin n) :=
      (Fintype.card_coe U).le.trans (card_le_univ U)
    have cap := E713Amplify.padding H active Y avoid (Fintype.card (Fin n)) fit
    apply not_lt_of_ge cap
    convert! many using 1 <;> congr!
end E713Prune
/- A bounded additive loss per vertex is negligible in the superlinear regime. -/
open Filter Asymptotics
open scoped Topology
namespace E713Prune
theorem transfer (f g : ℕ → ℕ) (q : ℕ) (bounds : ∀ n, g n ≤ f n ∧ f n ≤ q*n+g n)
    (diverges : Tendsto (fun n : ℕ => (f n:ℝ)/n) atTop atTop) :
    Tendsto (fun n : ℕ => (g n:ℝ)/n) atTop atTop ∧
      IsEquivalent atTop (fun n : ℕ => (f n:ℝ)) (fun n => (g n:ℝ)) := by
  have npos : ∀ᶠ n : ℕ in atTop, 0 < (n:ℝ) := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    exact_mod_cast (show 0<n by omega)
  have up (n) : (f n:ℝ) ≤ (q:ℝ)*n+g n := by exact_mod_cast (bounds n).2
  constructor
  · apply tendsto_atTop.mpr
    intro x
    filter_upwards [tendsto_atTop.mp diverges (x+q),npos] with n hx hn
    have lower := (le_div_iff₀ hn).mp hx
    exact (le_div_iff₀ hn).mpr (by nlinarith only [lower,up n])
  · apply IsEquivalent.symm
    have pos : ∀ᶠ n : ℕ in atTop, 0 < (f n:ℝ) := by
      filter_upwards [tendsto_atTop.mp diverges 1,npos] with n h hn
      have lower := (le_div_iff₀ hn).mp h
      linarith
    rw [isEquivalent_iff_tendsto_one (pos.mono fun _ h => h.ne')]
    have inv : Tendsto (fun n : ℕ => ((f n:ℝ)/n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp diverges
    have low : Tendsto (fun n : ℕ => 1-(q:ℝ)*((f n:ℝ)/n)⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x:=(1:ℝ))).sub ((tendsto_const_nhds (x:=(q:ℝ))).mul inv)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' low tendsto_const_nhds
    · filter_upwards [pos] with n hp
      change 1-(q:ℝ)*((f n:ℝ)/n)⁻¹ ≤ (g n:ℝ)/f n
      rw [inv_div,mul_div_assoc']
      apply (sub_le_iff_le_add).mpr
      rw [← add_div]
      exact (le_div_iff₀ hp).mpr (by linarith [up n])
    · filter_upwards [pos] with n hp
      change (g n:ℝ)/f n ≤ 1
      exact (div_le_one hp).mpr (by exact_mod_cast (bounds n).1)
end E713Prune

open SimpleGraph Filter Asymptotics
open scoped Topology Classical

namespace OMA.R_Erdos713_erdos_713_parts_i_R1_H1_R1

/-- Prime orders can be chosen immediately below each large integer with relative error tending to zero. -/
def H1 : Prop := ∃ p : ℕ → ℕ, (∀ᶠ k in atTop, (p k).Prime ∧ p k ≤ k) ∧
    Tendsto (fun k : ℕ => (p k : ℝ)/k) atTop (𝓝 1)

/-- The superlinear power law for connected bipartite cores of minimum degree at least two,
excluding the four-cycle. -/
def H2 : Prop := ∀ (r : ℕ) (J : SimpleGraph (Fin r)), J.IsBipartite → J.Connected →
    (∀ v, 2 ≤ J.degree v) → ¬ Nonempty (J ≃g (completeBipartiteGraph (Fin 2) (Fin 2))) →
    Tendsto (fun n : ℕ => (extremalNumber n J : ℝ)/n) atTop atTop →
    ∃ α c : ℝ, α ∈ Set.Ioo 1 2 ∧ 0<c ∧ IsEquivalent atTop
      (fun n : ℕ => (extremalNumber n J : ℝ)) (fun n => c*(n:ℝ)^α)

theorem main : H1 → H2 → OMA.R_Erdos713_erdos_713_parts_i_R1.H1 := by
  intro primes cores q F bip _ _ conn cyclic growth
  classical
  have many : Fintype.card (Fin q) ≤ F.edgeFinset.card := by
    by_contra! few
    have weak := conn.card_vert_le_card_edgeSet_add_one
    have count : Nat.card F.edgeSet = F.edgeFinset.card := by rw [Nat.card_eq_fintype_card,edgeFinset_card]
    have size : Nat.card (Fin q) = Fintype.card (Fin q) := Nat.card_eq_fintype_card
    have tree := (isTree_iff_connected_and_card (G:=F)).mpr ⟨conn,by omega⟩
    exact cyclic tree.isAcyclic
  obtain ⟨r,J,cj,bj,mj,sub,lift⟩ := E713Prune.core F conn bip many
  have active (v) : ¬ J.IsIsolated v := by
    intro is
    have zero := is.degree_eq_zero
    have two := mj v
    omega
  have prof := E713Prune.profile F J sub active lift
  obtain ⟨growthJ,equiv⟩ := E713Prune.transfer (extremalNumber · F) (extremalNumber · J)
    (Fintype.card (Fin q)) prof growth
  by_cases square : Nonempty (J ≃g (completeBipartiteGraph (Fin 2) (Fin 2)))
  · obtain ⟨iso⟩ := square
    obtain ⟨p,prim,dense⟩ := primes
    refine ⟨3/2,1/2,by norm_num,by norm_num,equiv.trans ?_⟩
    simpa only [extremalNumber_congr_right iso] using E713Interpolation.square_asymptotic p prim dense
  · obtain ⟨a,c,ha,hc,power⟩ := cores r J bj cj mj square growthJ
    exact ⟨a,c,ha,hc,equiv.trans power⟩

end OMA.R_Erdos713_erdos_713_parts_i_R1_H1_R1
