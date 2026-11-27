import FormalConjectures.ErdosProblems.«556»
import Mathlib

/-!
Łuczak's asymptotic bound for Erdős 556 (`R(C_n;3) ≤ (4+ε)n`):
`luczak_asymptotic_even` (@green-notes) + `R1.H2` (@hananzlt, plby/lean-proofs
8822f7ddef30fadbd92e1c6ab4ed897af356af5e, Apache-2.0, Lean-Proofs Authors, Shuhao Song).
-/

abbrev O:=ℝ
abbrev SG:=SimpleGraph
abbrev FS:=Finset
abbrev FC:=Fintype.card
abbrev CG:=SimpleGraph.cycleGraph
abbrev CA {α β:Sort*} (f:α->β) {a b:α} (h:a=b):=congrArg f h
lemma D1 {α:Type*} {s t:FS α}:Disjoint s t->∀ ⦃a:α⦄,a∈s->a∉t:=Finset.disjoint_left.mp
lemma D2 {α:Type*} {s t:FS α}:(∀ ⦃a:α⦄,a∈s->a∉t)->Disjoint s t:=Finset.disjoint_left.mpr

section S1
namespace E1
open Filter SimpleGraph Finset
def H1:Prop:=∀ (t k:ℕ) (R:SG (Fin t)) [DecidableRel R.Adj],1<=k->(k-1)*t < R.edgeFinset.card->∃ M:R.Subgraph,M.IsMatching/\2*k<=M.verts.ncard/\∀ u ∈ M.verts,∀ v ∈ M.verts,R.Reachable u v
def H2:Prop:=∀ (d δ : O),0 < d->0 < δ->δ < 1->∃ η > (0: O),∀ (t:ℕ),∃ m₀ :ℕ,∀ (N n m k:ℕ) (G:SG (Fin N)) [DecidableRel G.Adj] (parts:Fin t->FS (Fin N)) (R:SG (Fin t)) (M:R.Subgraph),Even n->4<=n->1<=k->m₀<=m->(n: O)<=(1 - δ)*(2*(k: O)*(m: O))->Pairwise (fun i j=>Disjoint (parts i) (parts j))->(∀ i:Fin t,m<=(parts i).card/\(parts i).card<=m+1)->(∀ u v:Fin t,R.Adj u v->G.IsUniform η (parts u) (parts v)/\(d: O)<=(G.edgeDensity (parts u) (parts v): O))->M.IsMatching->2*k<=M.verts.ncard->(∀ u ∈ M.verts,∀ v ∈ M.verts,R.Reachable u v)->(CG n).IsContained G
lemma dc3 (N:ℕ)(c:Fin 3->SG (Fin N)) [∀ i,DecidableRel (c i).Adj] (m:(⊤ :SG (Fin N)).IsEdgeColouring c):∃ i:Fin 3,N*(N-1)<=6*(c i).edgeFinset.card:=by
 have f:(⊤ :SG (Fin N)).edgeFinset⊆(univ:FS (Fin 3)).biUnion (fun i=>(c i).edgeFinset):=by
  intro e k
  induction e using Sym2.ind with
  | _ x y =>
   rw [mem_edgeFinset,mem_edgeSet,top_adj] at k;have b:(⨆ i,c i).Adj x y:=by rw [<- m.1];exact (top_adj x y).mpr k
   rw [iSup_adj] at b;obtain ⟨i,b⟩:=b;exact mem_biUnion.mpr ⟨i,mem_univ i,mem_edgeFinset.mpr b⟩
 have a:(⊤ :SG (Fin N)).edgeFinset.card<=∑ i:Fin 3,(c i).edgeFinset.card:=(card_le_card f).trans card_biUnion_le
 have j:(⊤ :SG (Fin N)).edgeFinset.card=Nat.choose N 2:=by
  convert card_edgeFinset_top_eq_card_choose_two (V:=Fin N);simp
 have d:2*Nat.choose N 2=N*(N-1):=by
  rw [Nat.choose_two_right];exact Nat.mul_div_cancel' (Nat.even_mul_pred_self N).two_dvd
 rw [j] at a
 have l: ∑ i:Fin 3,(c i).edgeFinset.card=(c 0).edgeFinset.card+(c 1).edgeFinset.card+(c 2).edgeFinset.card:=by
  simp [Fin.sum_univ_three,add_assoc]
 have g:∃ i:Fin 3,Nat.choose N 2<=3*(c i).edgeFinset.card:=by
  by_contra! h;have n:=h 0;have p:=h 1;have q:=h 2;omega
 obtain ⟨i,b⟩:=g;exact ⟨i,by omega⟩
lemma rcg (N:ℕ)(hN:0 < N) (G:SG (Fin N)) [DecidableRel G.Adj] (hG:N*(N-1)<=6*G.edgeFinset.card) (η d: O)(X:0 < η) (hd:0<=d) (l:ℕ)(hl:l<=N) (C:0 < l):∃ (t:ℕ)(parts:Fin t->FS (Fin N)) (R:SG (Fin t)) (_:DecidableRel R.Adj),l<=t/\t<=SzemerediRegularity.bound η l/\Pairwise (fun i j=>Disjoint (parts i) (parts j))/\(∀ i:Fin t,N/t<=(parts i).card/\(parts i).card<=N/t+1)/\(∀ u v:Fin t,R.Adj u v->G.IsUniform η (parts u) (parts v)/\d<=(G.edgeDensity (parts u) (parts v): O))/\(N: O)*(N-1)/3<=(N: O)*(N+t)/t + η * (N+t)^2 + d*(N+t)^2 + 2*(R.edgeFinset.card: O)*((N/t:ℕ)+1: O)^2:=by
 classical
 have s:l<=Fintype.card (Fin N):=by simpa using hl
 obtain ⟨P,b,w,H,F⟩:=szemeredi_regularity G X s;set t:=P.parts.card;have h0:0 < t:=lt_of_lt_of_le C w;let e:Fin t ≃ P.parts:=(equivFin P.parts).symm;let parts:Fin t->FS (Fin N):=fun i=>(e i).1
 let R:SG (Fin t) :=
  { Adj:=fun u v=>u≠v/\G.IsUniform η (parts u) (parts v) /\
     d<=(G.edgeDensity (parts u) (parts v): O)
    symm:=⟨fun u v ⟨z,Y,f⟩=>⟨z.symm,Y.symm,by rwa [edgeDensity_comm]⟩⟩
    loopless:=⟨fun u ⟨z,_⟩=>z rfl⟩ }
 letI:DecidableRel R.Adj:=Classical.decRel R.Adj;refine ⟨t,parts,R,inferInstance,w,H,?_,?_,?_,?_⟩
 · intro i j h5;exact P.disjoint (e i).2 (e j).2 (fun h=>h5 (e.injective (Subtype.ext h)))
 · intro i;have n:parts i∈P.parts:=(e i).2;have L:=b.average_le_card_part n;have B:=b.card_part_le_average_add_one n;simp only [card_univ,Fintype.card_fin] at L B;exact ⟨L,B⟩
 · intro u v m;exact ⟨m.2.1,m.2.2⟩
 · have hA:(univ:FS (Fin N)).Nonempty:=⟨⟨0,hN⟩,mem_univ _⟩
   let a:FS (FS (Fin N) × FS (Fin N)) :=
    P.parts.offDiag.filter (fun uv=>G.IsUniform η uv.1 uv.2/\d<=(G.edgeDensity uv.1 uv.2: O))
   have hsub:(univ ×ˢ univ).filter (fun xy:Fin N × Fin N=>G.Adj xy.1 xy.2)⊆(P.nonUniforms G η).biUnion (fun uv=>uv.1 ×ˢ uv.2) ∪ P.parts.biUnion offDiag ∪ (P.sparsePairs G d).biUnion (fun uv=>G.interedges uv.1 uv.2) ∪ a.biUnion (fun uv=>G.interedges uv.1 uv.2):=by
    rintro ⟨x,y⟩ D;simp only [mem_filter,mem_product,mem_univ,true_and] at D;obtain ⟨U,M,Z⟩:=P.exists_mem (mem_univ x);obtain ⟨V,T,hy⟩:=P.exists_mem (mem_univ y);by_cases p:U=V
    · subst p;refine mem_union_left _ (mem_union_left _ (mem_union_right _ ?_));exact mem_biUnion.mpr ⟨U,M,mem_offDiag.mpr ⟨Z,hy,G.ne_of_adj D⟩⟩
    · by_cases r:G.IsUniform η U V
      · by_cases f:d<=(G.edgeDensity U V: O)
        · refine mem_union_right _ (mem_biUnion.mpr ⟨(U,V),?_,?_⟩)
          · exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨M,T,p⟩,r,f⟩
          · exact G.mk_mem_interedges_iff.mpr ⟨Z,hy,D⟩
        · refine mem_union_left _ (mem_union_right _ ?_);refine mem_biUnion.mpr ⟨(U,V),?_,G.mk_mem_interedges_iff.mpr ⟨Z,hy,D⟩⟩;exact (P.mk_mem_sparsePairs G U V d).mpr ⟨M,T,p,not_le.mp f⟩
      · refine mem_union_left _ (mem_union_left _ (mem_union_left _ ?_));refine mem_biUnion.mpr ⟨(U,V),?_,mem_product.mpr ⟨Z,hy⟩⟩;exact (P.mk_mem_nonUniforms G).mpr ⟨M,T,p,r⟩
   have k:2*G.edgeFinset.card<=((P.nonUniforms G η).biUnion (fun uv=>uv.1 ×ˢ uv.2)).card+(P.parts.biUnion offDiag).card+((P.sparsePairs G d).biUnion (fun uv=>G.interedges uv.1 uv.2)).card+(a.biUnion (fun uv=>G.interedges uv.1 uv.2)).card:=by
    have B:=G.two_mul_card_edgeFinset;rw [univ_product_univ] at hsub;have hc:=card_le_card hsub;rw [<- B] at hc
    exact hc.trans (by
     refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _);refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _);exact card_union_le _ _)
   have g:a.card=2*R.edgeFinset.card:=by
    have S:=R.two_mul_card_edgeFinset;rw [<- univ_product_univ] at S;rw [S];symm;refine card_bij (fun uv _=>(parts uv.1,parts uv.2)) ?_ ?_ ?_
    · intro ⟨u,v⟩ m;simp only [mem_filter,mem_product,mem_univ,true_and] at m;refine mem_filter.mpr ⟨mem_offDiag.mpr ⟨(e u).2,(e v).2,?_⟩,m.2.1,m.2.2⟩;exact fun h=>m.1 (e.injective (Subtype.ext h))
    · intro ⟨h9,h7⟩ _ ⟨h8,h6⟩ _ I;simp only [Prod.mk.injEq] at I;exact Prod.ext (e.injective (Subtype.ext I.1)) (e.injective (Subtype.ext I.2))
    · intro ⟨U,V⟩ p
      simp only [a,mem_filter,mem_offDiag] at p;obtain ⟨⟨M,T,z⟩,r,f⟩:=p;refine ⟨(e.symm ⟨U,M⟩,e.symm ⟨V,T⟩),?_,?_⟩
      · simp only [mem_filter,mem_product,mem_univ,true_and]
        refine ⟨fun h=>z ?_,?_,?_⟩
        · exact CA Subtype.val (e.symm.injective h)
        · simpa [parts] using r
        · simpa [parts] using f
      · simp [parts]
   have A:((a.biUnion (fun uv=>G.interedges uv.1 uv.2)).card: O)<=2*(R.edgeFinset.card: O)*((N/t:ℕ)+1: O)^2:=by
    have L:(a.biUnion (fun uv=>G.interedges uv.1 uv.2)).card<=∑ uv ∈ a,(G.interedges uv.1 uv.2).card:=card_biUnion_le
    have B: ∑ uv ∈ a,(G.interedges uv.1 uv.2).card<=a.card*(N/t+1)^2:=by
     calc ∑ uv ∈ a,(G.interedges uv.1 uv.2).card
      <= ∑ _uv ∈ a,(N/t+1)^2:=by
           refine sum_le_sum fun uv m=>?_
           have n:=mem_offDiag.mp (mem_filter.mp m).1;have Y:=b.card_part_le_average_add_one n.1;have hv:=b.card_part_le_average_add_one n.2.1;simp only [card_univ,Fintype.card_fin] at Y hv;rw [sq];exact (G.card_interedges_le_mul uv.1 uv.2).trans (Nat.mul_le_mul Y hv)
      _=a.card*(N/t+1)^2:=by simp
    have h3:(a.biUnion (fun uv=>G.interedges uv.1 uv.2)).card<=2*R.edgeFinset.card*(N/t+1)^2:=by
     rw [<- g];exact L.trans B
    exact_mod_cast h3
   have J:(((P.nonUniforms G η).biUnion (fun uv=>uv.1 ×ˢ uv.2)).card: O)<=η * ((N: O)+t)^2:=by
    have L:((P.nonUniforms G η).biUnion (fun uv=>uv.1 ×ˢ uv.2)).card<=∑ uv ∈ P.nonUniforms G η,uv.1.card*uv.2.card:=by
     calc ((P.nonUniforms G η).biUnion (fun uv=>uv.1 ×ˢ uv.2)).card
      <= ∑ uv ∈ P.nonUniforms G η,(uv.1 ×ˢ uv.2).card:=card_biUnion_le
      _=∑ uv ∈ P.nonUniforms G η,uv.1.card*uv.2.card:=by
       refine sum_congr rfl fun uv _=>card_product _ _
    have B:=b.sum_nonUniforms_lt' (𝕜:=O) hA X F;simp only [card_univ,Fintype.card_fin] at B
    have Q:(∑ uv ∈ P.nonUniforms G η,(#uv.1: O)*(#uv.2: O))<=η * ((N: O)+t)^2:=by
     simpa [t] using B.le
    calc (((P.nonUniforms G η).biUnion (fun uv=>uv.1 ×ˢ uv.2)).card: O)
     <= ((∑ uv ∈ P.nonUniforms G η,uv.1.card*uv.2.card:ℕ): O):=Nat.cast_le.mpr L
     _=∑ uv ∈ P.nonUniforms G η,(#uv.1: O)*(#uv.2: O):=by push_cast;rfl
     _<=η * ((N: O)+t)^2:=Q
   have h4:((P.parts.biUnion offDiag).card: O)<=(N: O)*((N: O)+t)/t:=by
    have h:=b.card_biUnion_offDiag_le' (𝕜:=O);simpa [t] using h
   have K:(((P.sparsePairs G d).biUnion (fun uv=>G.interedges uv.1 uv.2)).card: O)<=d*((N: O)+t)^2:=by
    have h:=b.card_interedges_sparsePairs_le' (G:=G) (ε:=d) hd;simpa [t] using h
   have W:(N: O)*((N: O)-1)/3<=2*(G.edgeFinset.card: O):=by
    have v0:(N: O)*((N: O)-1)<=6*(G.edgeFinset.card: O):=by
     have q:((N*(N-1):ℕ): O)<=((6*G.edgeFinset.card:ℕ): O):=Nat.cast_le.mpr hG;rw [Nat.cast_mul,Nat.cast_sub hN,Nat.cast_one] at q;push_cast at q;exact q
    linarith
   have E:2*(G.edgeFinset.card: O)<=(((P.nonUniforms G η).biUnion (fun uv=>uv.1 ×ˢ uv.2)).card: O)+((P.parts.biUnion offDiag).card: O)+(((P.sparsePairs G d).biUnion (fun uv=>G.interedges uv.1 uv.2)).card: O)+((a.biUnion (fun uv=>G.interedges uv.1 uv.2)).card: O):=by
    exact_mod_cast k
   linarith
lemma ceb (a η d: O)(N t k eR:ℕ) (g:0 < a) (m:a<=1) (S: η<=a/1000) (W:d<=a/1000) (r:0 < t) (F:0 < N) (I:1000/a<=(t: O)) (T:(t: O)<=a/10000*(N: O)) (h0:(k: O)<=(t: O)/(6+a/2)) (v:(N: O)*((N: O)-1)/3<=(N: O)*((N: O)+(t: O))/(t: O) + η * ((N: O)+(t: O))^2 + d*((N: O)+(t: O))^2 + 2*(eR: O)*((↑(N/t): O)+1)^2):(k-1)*t < eR:=by
 have b:(0: O) < (t: O):=by exact_mod_cast r
 have f:(0: O) < (N: O):=by exact_mod_cast F
 have l:(10000: O)/a<=(N: O)/(t: O):=by
  rw [div_le_div_iff₀ g b];have K:=(le_div_iff₀ (by norm_num:(0: O) < 10000)).mp (by linarith:(t: O)<=a*(N: O)/10000)
  linarith
 have B:(1: O)<=a/10000*((N: O)/(t: O)):=by
  have K:=(div_le_iff₀ g).mp l;linarith
 have C:(1: O)<=(t: O):=by exact_mod_cast r
 have H:(1: O)<=a/10000*(N: O):=by
  have h4:(N: O)/(t: O)<=(N: O):=div_le_self f.le C;nlinarith
 have z:(↑(N/t): O)<=(N: O)/(t: O):=(le_div_iff₀ b).mpr (by exact_mod_cast Nat.div_mul_le_self N t)
 have L:(N: O)+(t: O)<=(1+a/10000)*(N: O):=by linarith
 have p:(1-a/10000)*(N: O)<=(N: O)-1:=by linarith
 have J:(↑(N/t): O)+1<=(1+a/10000)*((N: O)/(t: O)):=by linarith
 have P:(1: O)/(t: O)<=a/1000:=by
  rw [div_le_div_iff₀ b (by norm_num),one_mul]
  linarith only [(div_le_iff₀ g).mp I]
 have R:(1-a/10000)/3*(N: O)^2<=(N: O)*((N: O)-1)/3:=by
  have hmul:=mul_le_mul_of_nonneg_left p f.le;linarith
 have j:(N: O)*((N: O)+(t: O))/(t: O)<=(a/1000)*(1+a/10000)*(N: O)^2:=by
  have K:(N: O)*((N: O)+(t: O))/(t: O)=((N: O)*((N: O)+(t: O)))*(1/(t: O)):=by ring
  rw [K]
  have V:(N: O)*((N: O)+(t: O))<=(N: O)*((1+a/10000)*(N: O)):=by
   gcongr
  calc ((N: O)*((N: O)+(t: O)))*(1/(t: O))
   <= ((N: O)*((1+a/10000)*(N: O)))*(a/1000):=by
        gcongr
   _=(a/1000)*(1+a/10000)*(N: O)^2:=by ring
 have n:(η + d)*((N: O)+(t: O))^2<=(a/500)*(1+a/10000)^2 * (N: O)^2:=by
  have Y:((N: O)+(t: O))^2<=((1+a/10000)*(N: O))^2:=by gcongr
  have h7: η + d<=a/500:=by linarith
  calc (η + d)*((N: O)+(t: O))^2
   <= (a/500)*((1+a/10000)*(N: O))^2:=by gcongr
   _=(a/500)*(1+a/10000)^2 * (N: O)^2:=by ring
 have i:2*(eR: O)*((↑(N/t): O)+1)^2<=2*(eR: O)*((1+a/10000)^2 * (N: O)^2/(t: O)^2):=by
  have Y:((↑(N/t): O)+1)^2<=((1+a/10000)*((N: O)/(t: O)))^2:=by
   gcongr
  have Q:((1+a/10000)*((N: O)/(t: O)))^2=(1+a/10000)^2 * (N: O)^2/(t: O)^2:=by ring
  rw [<- Q];gcongr
 have e:(0: O) < (N: O)^2:=by positivity
 have q:(1/3-0.0034*a)*(N: O)^2<=2*(eR: O)*((1+a/10000)^2 * (N: O)^2/(t: O)^2):=by
  have y:(a/1000)*(1+a/10000)<=0.0011*a:=by nlinarith only [g,m]
  have u:(1+a/10000)^2<=1.05:=by nlinarith only [g,m]
  have E:(a/500)*(1+a/10000)^2<=0.0021*a:=by
   nlinarith only [g,u]
  have D:1/3-0.0001*a<=(1-a/10000)/3:=by linarith
  have K:(1/3-0.0001*a)*(N: O)^2<=(N: O)*((N: O)-1)/3:=by
   nlinarith only [D,R,e]
  have V:(N: O)*((N: O)+(t: O))/(t: O)<=0.0011*a * (N: O)^2:=by
   nlinarith only [y,j,e]
  have h3:(η + d)*((N: O)+(t: O))^2<=0.0021*a * (N: O)^2:=by
   nlinarith only [E,n,e]
  have X: η * ((N: O)+(t: O))^2 + d*((N: O)+(t: O))^2<=0.0021*a * (N: O)^2:=by
   linarith only [h3,show (η + d)*((N: O)+(t: O))^2=η * ((N: O)+(t: O))^2 + d*((N: O)+(t: O))^2 by ring]
  have x:0<=a*(N: O)^2:=by positivity
  linarith only [v,K,V,X,i,x]
 have A:(1/3-0.0034*a)<=2*(eR: O)*(1+a/10000)^2/(t: O)^2:=by
  have M:2*(eR: O)*((1+a/10000)^2 * (N: O)^2/(t: O)^2)=(2*(eR: O)*(1+a/10000)^2/(t: O)^2)*(N: O)^2:=by ring
  rw [M] at q;exact le_of_mul_le_mul_right q e
 have w:(1/3-0.0034*a)*(t: O)^2<=2*(eR: O)*(1+a/10000)^2:=(le_div_iff₀ (by positivity)).mp A
 have U:((k-1:ℕ): O)*(t: O)<=(t: O)^2/(6+a/2):=by
  have h5:((k-1:ℕ): O)<=(k: O):=by exact_mod_cast Nat.sub_le k 1
  calc ((k-1:ℕ): O)*(t: O)
   <= (k: O)*(t: O):=by gcongr
   _<=((t: O)/(6+a/2))*(t: O):=by gcongr
   _=(t: O)^2/(6+a/2):=by ring
 have s:2*((t: O)^2/(6+a/2))*(1+a/10000)^2 < (1/3-0.0034*a)*(t: O)^2:=by
  have h6:0 < 6+a/2:=by linarith
  have Z:(0: O) < (t: O)^2:=by positivity
  suffices hcoef:2*(1+a/10000)^2 < (1/3-0.0034*a)*(6+a/2) by
   have hmul:2*((t: O)^2/(6+a/2))*(1+a/10000)^2=(2*(1+a/10000)^2/(6+a/2))*(t: O)^2:=by ring
   rw [hmul];exact mul_lt_mul_of_pos_right ((div_lt_iff₀ h6).mpr hcoef) Z
  nlinarith only [g,m]
 have h:((k-1:ℕ): O)*(t: O) < (eR: O):=by
  have G:(0: O) < 2*(1+a/10000)^2:=by positivity
  have K:2*(((k-1:ℕ): O)*(t: O))*(1+a/10000)^2<=2*((t: O)^2/(6+a/2))*(1+a/10000)^2:=by
   gcongr
  have V:2*(((k-1:ℕ): O)*(t: O))*(1+a/10000)^2 < 2*(eR: O)*(1+a/10000)^2:=by
   linarith only [K,s,w]
  nlinarith only [V,G]
 exact_mod_cast h
lemma bsb (a δ : O)(N n t m k:ℕ) (b:0 < a) (d:a<=1) (B: δ=a/20) (u:0 < t) (s:(0: O) < (n: O)) (v:1000/a<=(t: O)) (A:(t: O)<=a/10000*(N: O)) (D:(3+a)*(n: O)-1 < (N: O)) (j:10000/a<=3*(n: O)) (C:(t: O)/(6+a/2)-1 < (k: O)) (H:(N: O)/(t: O)-1 < (m: O)):(n: O)<=(1 - δ)*(2*(k: O)*(m: O)):=by
 have e:(0: O) < (t: O):=by exact_mod_cast u
 have p:(1: O) < (a/100)*((t: O)/(6+a/2)):=by
  rw [div_mul_div_comm,lt_div_iff₀ (by positivity)]
  have z:(1000: O)<=a*(t: O):=by linarith only [(div_le_iff₀ b).mp v]
  linarith
 have y:(1-a/100)*((t: O)/(6+a/2)) < (k: O):=by linarith
 have f:(10000: O)/a<=(N: O)/(t: O):=by
  rw [div_le_div_iff₀ b e];have z:=(le_div_iff₀ (by norm_num:(0: O) < 10000)).mp (by linarith:(t: O)<=a*(N: O)/10000)
  linarith
 have q:(1: O)<=a/10000*((N: O)/(t: O)):=by
  have z:=(div_le_iff₀ b).mp f;linarith
 have i:(1-a/10000)*((N: O)/(t: O)) < (m: O):=by linarith
 have x:(3+0.99*a)*(n: O)<=(N: O):=by
  have z:(1: O)<=0.01*a * (n: O):=by
   have J:=(div_le_iff₀ b).mp j;linarith
  linarith
 have w:(1-a/10000)*((3+0.99*a)*(n: O)/(t: O))<=(m: O):=by
  have z:(3+0.99*a)*(n: O)/(t: O)<=(N: O)/(t: O):=by gcongr
  have J:0<=(1-a/10000):=by linarith
  nlinarith only [z,J,i]
 have r:(1-a/20)*(2*((1-a/100)*((t: O)/(6+a/2)))*((1-a/10000)*((3+0.99*a)*(n: O)/(t: O))))<=(1 - δ)*(2*(k: O)*(m: O)):=by
  rw [B];have L:0<=(1-a/100)*((t: O)/(6+a/2)):=mul_nonneg (by linarith) (by positivity)
  have K:0<=(1-a/10000)*((3+0.99*a)*(n: O)/(t: O)):=mul_nonneg (by linarith) (by positivity)
  have M:0<=1-a/20:=by linarith
  gcongr
 have l:(1-a/20)*(2*((1-a/100)*((t: O)/(6+a/2)))*((1-a/10000)*((3+0.99*a)*(n: O)/(t: O))))=(2*(1-a/20)*(1-a/100)*(1-a/10000)*(3+0.99*a)/(6+a/2))*(n: O):=by
  field_simp
 have h:(1: O)<=2*(1-a/20)*(1-a/100)*(1-a/10000)*(3+0.99*a)/(6+a/2):=by
  rw [le_div_iff₀ (by linarith)]
  have F:1-0.061*a<=(1-a/20)*(1-a/100):=by nlinarith only [b,d]
  have E:1-0.062*a<=(1-a/20)*(1-a/100)*(1-a/10000):=by
   nlinarith only [b,d,F]
  have G:6+a/2<=2*(1-0.062*a)*(3+0.99*a):=by
   nlinarith only [b,d]
  have I:2*(1-0.062*a)*(3+0.99*a)<=2*(1-a/20)*(1-a/100)*(1-a/10000)*(3+0.99*a):=by
   nlinarith only [b,d,E]
  linarith only [G,I]
 have g:(n: O)<=(2*(1-a/20)*(1-a/100)*(1-a/10000)*(3+0.99*a)/(6+a/2))*(n: O):=by
  nlinarith only [h,s]
 linarith only [r,l,g]
lemma main:H1->H2->type_of% @Erdos556.erdos_556.variants.luczak_asymptotic_even:=by
 intro h1 h2 ε y1
 classical
 set b: O:=min ε 1;have p:0 < b:=lt_min y1 zero_lt_one;have z:b<=1:=min_le_right ε 1;have x7:b<=ε:=min_le_left ε 1;set d: O:=b/1000;set δ : O:=b/20;have hd:0 < d:=by positivity
 have x0:0 < δ:=by positivity
 have x3: δ < 1:=by dsimp [δ];linarith
 obtain ⟨Y,h4,g⟩:=h2 d δ hd x0 x3;set η : O:=min Y (b/1000);have x9:0 < η:=lt_min h4 (by positivity)
 have S: η<=Y:=min_le_left _ _;have h6: η<=b/1000:=min_le_right _ _;set l:ℕ:=Nat.ceil (1000/b);have B:1000/b<=(l: O):=Nat.le_ceil _
 have y4:1000<=l:=by
  have:(1000: O)<=1000/b:=by rw [le_div_iff₀ p];nlinarith
  exact_mod_cast this.trans B
 have K:0 < l:=by omega
 obtain ⟨a,E⟩ :∃ M,M=SzemerediRegularity.bound η l:=⟨_,rfl⟩;have h5:0 < a:=E ▸ SzemerediRegularity.bound_pos η l;have Z:l<=a:=E ▸ SzemerediRegularity.le_bound η l;obtain ⟨e,I⟩ :∃ mr,mr=(range (a+1)).sup (fun t=>(g t).choose):=⟨_,rfl⟩
 obtain ⟨J,w⟩ :∃ n0,n0=Nat.ceil ((10000*(a: O)/b+(e: O)*a + 100)/3)+4:=⟨_,rfl⟩;rw [Filter.eventually_atTop];refine ⟨J,fun n hn h9=>?_⟩
 have F:4<=J:=by rw [w];exact Nat.le_add_left 4 _
 have y3:4<=n:=F.trans hn;have h7:(0: O) < (n: O):=by exact_mod_cast (by omega:0 < n)
 obtain ⟨N,T⟩ :∃ N,N=Nat.floor ((3+b)*(n: O)):=⟨_,rfl⟩;have h8:(N: O)<=(3+b)*(n: O):=T ▸ Nat.floor_le (by positivity)
 have v6:(3+b)*(n: O)-1 < (N: O):=T ▸ Nat.sub_one_lt_floor _
 have v8:(10000*(a: O)/b+(e: O)*a + 100)/3<=(n: O):=by
  have y6:(J: O)<=(n: O):=by exact_mod_cast hn
  have y8:(10000*(a: O)/b+(e: O)*a + 100)/3<=(Nat.ceil ((10000*(a: O)/b+(e: O)*a + 100)/3): O):=Nat.le_ceil _
  have y2:((Nat.ceil ((10000*(a: O)/b+(e: O)*a + 100)/3):ℕ): O)<=(J: O):=by
   rw [w];exact_mod_cast Nat.le_add_right _ 4
  linarith
 have x6:10000*(a: O)/b+(e: O)*a + 99<=(N: O):=by
  have y2:(3+b)*(n: O)-1 ≥ 3*(n: O)-1:=by nlinarith
  linarith
 have L:0 < N:=by
  have:(1: O)<=(N: O):=by
   have:(0: O) < 10000*(a: O)/b+(e: O)*a:=by positivity
   linarith
  exact_mod_cast this
 have C:multicolourRamsey (CG n) 3<=N:=by
  apply Nat.sInf_le
  intro c hc;obtain ⟨ic,y0⟩:=dc3 N c hc;let G:=c ic
  have x8:l<=N:=by
   have h1:(l: O)<=(a: O):=by exact_mod_cast Z
   have h2:(a: O)<=10000*(a: O)/b:=by
    rw [le_div_iff₀ p];nlinarith only [p,z]
   have h3:(10000*(a: O)/b: O)<=(N: O):=by
    linarith [show (0: O)<=(e: O)*a + 99 by positivity]
   exact Nat.cast_le.mp (h1.trans (h2.trans h3))
  obtain ⟨t,parts,R,_,x1,v5,v0,y,A,W⟩:=rcg N L G y0 η d x9 hd.le l x8 K;rw [<- E] at v5;have j:0 < t:=lt_of_lt_of_le K x1;have h:(1000: O)/b<=(t: O):=B.trans (by exact_mod_cast x1)
  have x4:(1000: O)<=(t: O):=by
   have:(1000: O)<=1000/b:=by rw [le_div_iff₀ p];nlinarith only [p,z]
   exact this.trans h
  obtain ⟨m,H⟩ :∃ m,m=N/t:=⟨_,rfl⟩;obtain ⟨k,D⟩ :∃ k,k=Nat.floor ((t: O)/(6+b/2)):=⟨_,rfl⟩
  have x:(1: O)<=(t: O)/(6+b/2):=by
   rw [le_div_iff₀ (by linarith)];linarith
  have x2:1<=k:=by rw [D];exact Nat.le_floor (by simpa using x)
  have v3:(g t).choose<=m:=by
   have x5:(g t).choose<=e:=by
    rw [I];exact le_sup (f:=fun s=>(g s).choose) (mem_range.mpr (Nat.lt_succ_of_le v5))
   have hmul:e*t<=N:=by
    have h1:(e: O)*(t: O)<=(e: O)*(a: O):=by gcongr
    have h2:(e: O)*(a: O)<=(N: O):=by
     have:(0: O)<=10000*(a: O)/b+99:=by positivity
     linarith
    exact_mod_cast h1.trans h2
   rw [H];exact x5.trans ((Nat.le_div_iff_mul_le j).mpr hmul)
  have q:(t: O)<=b/10000*(N: O):=by
   have h1:(t: O)<=(a: O):=by exact_mod_cast v5
   have h2:10000*(a: O)/b<=(N: O):=by
    have:(0: O)<=(e: O)*a + 99:=by positivity
    linarith
   have h3:(a: O)<=b/10000*(N: O):=by
    rw [div_le_iff₀ p] at h2;linarith
   exact h1.trans h3
  have v7:(k: O)<=(t: O)/(6+b/2):=D ▸ Nat.floor_le (by positivity)
  have v4:(k-1)*t < R.edgeFinset.card :=
   ceb b η d N t k R.edgeFinset.card p z h6 le_rfl j L h q v7 W
  obtain ⟨M,P,X,Q⟩:=h1 t k R x2 v4
  have U:10000/b<=3*(n: O):=by
   have y7:(1: O)<=(a: O):=by exact_mod_cast h5
   have h1:(10000: O)<=10000*(a: O):=by linarith
   have y5:(10000: O)/b<=10000*(a: O)/b:=div_le_div_of_nonneg_right h1 p.le;have h2:(0: O)<=(e: O)*a + 100:=by positivity
   linarith
  have v1:(t: O)/(6+b/2)-1 < (k: O):=D ▸ Nat.sub_one_lt_floor _
  have v2:(N: O)/(t: O)-1 < (m: O):=by
   rw [H,sub_lt_iff_lt_add,div_lt_iff₀ (by exact_mod_cast j)]
   calc (N: O) < (↑(N/t*t + t): O):=by exact_mod_cast Nat.lt_div_mul_add j
    _=(↑(N/t)+1) * ↑t:=by push_cast;ring
  have h0:(n: O)<=(1 - δ)*(2*(k: O)*(m: O)) :=
   bsb b δ N n t m k p z rfl j h7 h q v6 U v1 v2
  have r:∀ i:Fin t,m<=(parts i).card/\(parts i).card<=m+1:=by
   rw [H];exact y
  exact ⟨ic,(g t).choose_spec N n m k G parts R M h9 y3 x2 v3 h0 v0 r (fun u v v9=>⟨(A u v v9).1.mono S,(A u v v9).2⟩) P X Q⟩
 have V:(multicolourRamsey (CG n) 3: O)<=(3 + ε)*(n: O):=by
  calc (multicolourRamsey (CG n) 3: O)
   <= (N: O):=by exact_mod_cast C
   _<=(3+b)*(n: O):=h8
   _<=(3 + ε)*(n: O):=by gcongr
 exact V
end E1
end S1
section S2
open Finset SimpleGraph
open SimpleGraph Finset
open scoped SimpleGraph
lemma h1p:E1.H1:=by
 intro t k R _ hk hd
 classical
 let S (c:R.ConnectedComponent):=univ.filter (fun x=>R.connectedComponentMk x=c)
 let u (e:Sym2 (Fin t)):=R.connectedComponentMk e.out.1;let E (c:R.ConnectedComponent):=R.edgeFinset.filter (fun e=>u e=c)
 have W: ∑ c,(S c).card=t:=by
  simpa [S] using sum_card_fiberwise_eq_card_filter (univ:FS (Fin t)) univ R.connectedComponentMk
 have Z: ∑ c,(E c).card=R.edgeFinset.card:=by
  simpa [E] using sum_card_fiberwise_eq_card_filter R.edgeFinset univ u
 obtain ⟨c,X⟩ :∃ c,(k-1)*(S c).card < (E c).card:=by
  by_contra! h;have T:=sum_le_sum (fun c (_:c∈univ)=>h c)
  rw [<- mul_sum,W,Z] at T;omega
 have j (x:Fin t):x∈S c↔x∈c.supp:=by simp [S]
 have l {x y:Fin t} (r:s(x,y)∈E c):x∈S c/\y∈S c:=by
  obtain ⟨V,B⟩:=mem_filter.mp r;have G:R.Adj x y:=mem_edgeFinset.mp V;have i:(s(x,y):Sym2 (Fin t)).out.1∈c.supp:=B;have H:=c.mem_supp_congr_adj G;rcases Sym2.mem_iff.mp (Sym2.out_fst_mem s(x,y)) with m | q
  · rw [m] at i;exact ⟨(j _).mpr i,(j _).mpr (H.mp i)⟩
  · rw [q] at i;exact ⟨(j _).mpr (H.mpr i),(j _).mpr i⟩
 have C:0 < (S c).card:=by
  obtain ⟨x,m⟩:=c.nonempty_supp;exact card_pos.mpr ⟨x,(j _).mpr m⟩
 let:NeZero (S c).card:=⟨C.ne'⟩;let p:S c ≃ Fin (S c).card:=equivFinOfCardEq rfl;let b (x:Fin t):Fin (S c).card:=if m:x∈S c then p ⟨x,m⟩ else 0
 have I {x y} (m:x∈S c) (q:y∈S c) (h:b x=b y):x=y:=by
  simp only [b,dif_pos m,dif_pos q] at h;exact CA Subtype.val (p.injective h)
 let color:Sym2 (Fin t)->Fin (S c).card:=Sym2.lift ⟨fun x y=>b x+b y,fun x y=>add_comm _ _⟩
 obtain ⟨a,_,Y⟩:=exists_lt_card_fiber_of_mul_lt_card_of_maps_to (s:=E c) (t:=univ) (f:=color) (fun _ _=>mem_univ _) (by simpa [Nat.mul_comm] using X)
 let F:=(E c).filter (fun e=>color e=a)
 have P:k<=F.card:=by
  change k-1 < F.card at Y;omega
 have d {x y z:Fin t} (q:s(x,y)∈F) (L:s(x,z)∈F):y=z:=by
  obtain ⟨r,N⟩:=mem_filter.mp q;obtain ⟨K,J⟩:=mem_filter.mp L;have h:b x+b y=b x+b z:=N.trans J.symm;exact I (l r).2 (l K).2 (add_left_cancel h)
 let M:R.Subgraph:={
  verts:=↑(F.biUnion Sym2.toFinset)
  Adj:=fun x y=>s(x,y)∈F
  adj_sub:=fun h=>mem_edgeFinset.mp (mem_filter.mp (mem_filter.mp h).1).1
  edge_vert:=fun {x y} h=>mem_biUnion.mpr ⟨_,h,Sym2.mem_toFinset.mpr (Sym2.mem_mk_left x y)⟩
  symm:=⟨fun x y h=>by rwa [Sym2.eq_swap]⟩ }
 have g {x:Fin t} (m:x∈M.verts):∃ y,s(x,y)∈F:=by
  obtain ⟨e,r,v⟩:=mem_biUnion.mp m;obtain ⟨y,rfl⟩:=Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp v);exact ⟨y,r⟩
 have D:(F:Set (Sym2 (Fin t))).PairwiseDisjoint Sym2.toFinset:=by
  intro e r f K Q;apply D2
  intro x m v;obtain ⟨y,rfl⟩:=Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp m);obtain ⟨z,rfl⟩:=Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp v);exact Q (CA (fun w=>s(x,w)) (d r K))
 have n {x:Fin t} (m:x∈M.verts):x∈c.supp:=by
  obtain ⟨y,q⟩:=g m;exact (j x).mp (l (mem_filter.mp q).1).1
 refine ⟨M,?_,?_,fun _ U _ hv=>c.reachable_of_mem_supp (n U) (n hv)⟩
 · intro x m;obtain ⟨y,q⟩:=g m;exact ⟨y,q,fun _ L=>d L q⟩
 · have A (e) (r:e∈F):e.toFinset.card=2 :=
    e.card_toFinset_of_not_isDiag (R.not_isDiag_of_mem_edgeFinset (mem_filter.mp (mem_filter.mp r).1).1)
   change 2*k<=(↑(F.biUnion Sym2.toFinset):Set (Fin t)).ncard;rw [Set.ncard_coe_finset,card_biUnion D,sum_const_nat A,Nat.mul_comm F.card];omega
end S2
section S3
open Finset SimpleGraph
open SimpleGraph Finset
namespace P2
private lemma cbl {N:ℕ} (G:SG (Fin N)) [DecidableRel G.Adj] {d η : O} (s:0 < η) {U V V':FS (Fin N)} (k:G.IsUniform η U V)(t:d<=(G.edgeDensity U V: O)) (w:0 < U.card) (x:0 < V.card) (n:V'⊆V)(a:(V.card: O) * η<=(V'.card: O)):((U.filter (fun u=>((G.neighborFinset u ∩ V').card: O)<=(d - η)*(V'.card: O))).card: O) < (U.card: O) * η:=by
 set B:=U.filter (fun u=>((G.neighborFinset u ∩ V').card: O)<=(d - η)*(V'.card: O))
 by_contra! l
 have m:0 < B.card:=by
  have p:(0: O) < (U.card: O) * η:=by positivity
  exact_mod_cast p.trans_le l
 have j:0 < V'.card:=by
  have p:(0: O) < (V.card: O) * η:=by positivity
  exact_mod_cast p.trans_le a
 have h:=k (filter_subset _ _) n l a
 have r:d - η < (G.edgeDensity B V': O):=by
  rw [abs_sub_lt_iff] at h;linarith
 have hsub:G.interedges B V'⊆B.biUnion (fun u=>(G.neighborFinset u ∩ V').image (fun v=>(u,v))):=by
  intro ⟨u,v⟩ f;rw [mk_mem_interedges_iff] at f;exact mem_biUnion.mpr ⟨u,f.1,mem_image.mpr ⟨v,mem_inter.mpr ⟨(G.mem_neighborFinset u v).mpr f.2.2,f.2.1⟩,rfl⟩⟩
 have e:(G.interedges B V').card<=∑ u ∈ B,(G.neighborFinset u ∩ V').card:=by
  calc (G.interedges B V').card
   <= (B.biUnion (fun u=>(G.neighborFinset u ∩ V').image (fun v=>(u,v)))).card:=card_le_card hsub
   _<=∑ u ∈ B,((G.neighborFinset u ∩ V').image (fun v=>(u,v))).card:=card_biUnion_le
   _<=∑ u ∈ B,(G.neighborFinset u ∩ V').card:=sum_le_sum fun _ _=>card_image_le
 have g:((G.interedges B V').card: O)<=(B.card: O)*((d - η)*(V'.card: O)):=by
  calc ((G.interedges B V').card: O)
   <= ((∑ u ∈ B,(G.neighborFinset u ∩ V').card:ℕ): O):=Nat.cast_le.mpr e
   _=∑ u ∈ B,((G.neighborFinset u ∩ V').card: O):=by push_cast;rfl
   _<=∑ _u ∈ B,(d - η)*(V'.card: O):=by
    refine sum_le_sum fun u q=>?_
    exact (mem_filter.mp q).2
   _=(B.card: O)*((d - η)*(V'.card: O)):=by simp [sum_const,nsmul_eq_mul]
 have b:(0: O) < (B.card: O)*(V'.card: O):=by positivity
 have i:(G.edgeDensity B V': O)<=d - η:=by
  rw [edgeDensity_def];push_cast;rw [div_le_iff₀ b];linarith
 linarith
private lemma eg2 {N:ℕ} (G:SG (Fin N)) [DecidableRel G.Adj] {d η : O} (y:0 < η) {U P a V₁ T₁ V₂ T₂ :FS (Fin N)} (B:P⊆U)(D:0 < U.card) (i:G.IsUniform η U V₁)(m:d<=(G.edgeDensity U V₁ : O)) (s:0 < V₁.card) (p:T₁⊆V₁)(k:(V₁.card: O) * η<=(T₁.card: O)) (j:G.IsUniform η U V₂)(q:d<=(G.edgeDensity U V₂ : O)) (n:0 < V₂.card) (r:T₂⊆V₂)(l:(V₂.card: O) * η<=(T₂.card: O)) (H:(a.card: O)+2 * (U.card: O) * η<=(P.card: O)):∃ u ∈ P,u ∉ a/\(d - η)*(T₁.card: O) < ((G.neighborFinset u ∩ T₁).card: O)/\(d - η)*(T₂.card: O) < ((G.neighborFinset u ∩ T₂).card: O):=by
 set B₁:=U.filter (fun u=>((G.neighborFinset u ∩ T₁).card: O)<=(d - η)*(T₁.card: O))
 set B₂:=U.filter (fun u=>((G.neighborFinset u ∩ T₂).card: O)<=(d - η)*(T₂.card: O))
 have z:(B₁.card: O) < (U.card: O) * η:=cbl G y i m D s p k;have A:(B₂.card: O) < (U.card: O) * η:=cbl G y j q D n r l;set b:=P \ (a ∪ B₁ ∪ B₂)
 have g:0 < b.card:=by
  have J:P.card<=b.card+(a ∪ B₁ ∪ B₂).card:=by
   calc P.card<=(b ∪ (a ∪ B₁ ∪ B₂)).card:=card_le_card (fun x F=>by
    by_cases h:x∈a ∪ B₁ ∪ B₂
    · exact mem_union_right _ h
    · exact mem_union_left _ (mem_sdiff.mpr ⟨F,h⟩))
    _<=b.card+(a ∪ B₁ ∪ B₂).card:=card_union_le _ _
  have K:(a ∪ B₁ ∪ B₂).card<=a.card+B₁.card+B₂.card:=(card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _);have C:P.card<=b.card+a.card+B₁.card+B₂.card:=by omega
  have I:((P.card: O))<=(b.card: O)+(a.card: O)+(B₁.card: O)+(B₂.card: O):=by
   exact_mod_cast C
  have E:(0: O) < (b.card: O):=by linarith
  exact_mod_cast E
 obtain ⟨u,v⟩:=card_pos.mp g;rw [mem_sdiff,mem_union,mem_union] at v;have w:u∈U:=B v.1;have e:u ∉ B₁:=fun h=>v.2 (Or.inl (Or.inr h))
 have f:u ∉ B₂:=fun h=>v.2 (Or.inr h)
 refine ⟨u,v.1,fun h=>v.2 (Or.inl (Or.inl h)),?_,?_⟩
 · by_contra! t;exact e (mem_filter.mpr ⟨w,t⟩)
 · by_contra! t;exact f (mem_filter.mpr ⟨w,t⟩)
private lemma nep {N:ℕ} (G:SG (Fin N)) [DecidableRel G.Adj] {d η : O} (l: η < d) {U V A' B':FS (Fin N)} (f:G.IsUniform η U V)(u:d<=(G.edgeDensity U V: O)) (g:A'⊆U)(n:B'⊆V) {cA cB:ℕ} (k:(U.card: O) * η<=(cA: O)) (m:(V.card: O) * η<=(cB: O)):∀ X⊆A',∀ Y⊆B',cA<=X.card->cB<=Y.card->∃ x ∈ X,∃ y ∈ Y,G.Adj x y:=by
 intro X t Y s j r;have p:(U.card: O) * η<=(X.card: O):=k.trans (Nat.cast_le.mpr j);have h:(V.card: O) * η<=(Y.card: O):=m.trans (Nat.cast_le.mpr r);have e:=f (t.trans g) (s.trans n) p h
 have a:(0: O) < (G.edgeDensity X Y: O):=by
  rw [abs_sub_lt_iff] at e;linarith
 have i:(G.interedges X Y).Nonempty:=by
  rw [edgeDensity_def] at a;push_cast at a;by_contra! q;simp [q] at a
 obtain ⟨⟨x,y⟩,b⟩:=i;rw [mk_mem_interedges_iff] at b;exact ⟨x,b.1,y,b.2.1,b.2.2⟩
private lemma spc {N:ℕ} (S:FS (Fin N)) (q:ℕ)(p:2*q<=S.card):∃ Res Cap Body:FS (Fin N),Res⊆S/\Cap⊆S/\Body⊆S/\Disjoint Res Cap/\Disjoint Res Body/\Disjoint Cap Body/\Res.card=q/\Cap.card=q/\Body.card=S.card-2*q:=by
 classical
 set L:=S.toList;have i:L.Nodup:=S.nodup_toList;have h:L.length=S.card:=S.length_toList;set L1:=L.take q;set L2:=(L.drop q).take q;set L3:=L.drop (2*q)
 have b:L1 ++ L2 ++ L3=L:=by
  have n:L2 ++ L3=L.drop q:=by
   simp only [L2,L3];rw [show 2*q=q+q by omega,<-List.drop_drop]
   exact List.take_append_drop q (L.drop q)
  rw [List.append_assoc,n];exact List.take_append_drop q L
 have a:(L1 ++ L2 ++ L3).Nodup:=b.symm ▸ i;have g:(L1 ++ L2).Nodup:=(List.nodup_append.mp a).1;have m:L1.Nodup:=(List.nodup_append.mp g).1;have k:L2.Nodup:=(List.nodup_append.mp g).2.1;have l:L3.Nodup:=(List.nodup_append.mp a).2.1;refine ⟨L1.toFinset,L2.toFinset,L3.toFinset,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · intro x j;rw [List.mem_toFinset] at j;exact S.mem_toList.mp (by show x∈L;rw [<- b];exact List.mem_append_left _ (List.mem_append_left _ j))
 · intro x j;rw [List.mem_toFinset] at j;exact S.mem_toList.mp (by show x∈L;rw [<- b];exact List.mem_append_left _ (List.mem_append_right _ j))
 · intro x j;rw [List.mem_toFinset] at j;exact S.mem_toList.mp (by show x∈L;rw [<- b];exact List.mem_append_right _ j)
 · rw [Finset.disjoint_left]
   intro x e f;rw [List.mem_toFinset] at e f;exact (List.nodup_append.mp g).2.2 x e x f rfl
 · rw [Finset.disjoint_left]
   intro x e d;rw [List.mem_toFinset] at e d;exact (List.nodup_append.mp a).2.2 x (List.mem_append_left _ e) x d rfl
 · rw [Finset.disjoint_left]
   intro x f d;rw [List.mem_toFinset] at f d;exact (List.nodup_append.mp a).2.2 x (List.mem_append_right _ f) x d rfl
 · rw [List.toFinset_card_of_nodup m,List.length_take,h];omega
 · rw [List.toFinset_card_of_nodup k,List.length_take,List.length_drop,h];omega
 · rw [List.toFinset_card_of_nodup l,List.length_drop,h]
private noncomputable def bpA {N:ℕ} (G:SG (Fin N)) (A' B':FS (Fin N)) (x y:Fin N):Prop:=((x∈A'/\y∈B')\/(x∈B'/\y∈A'))/\G.Adj x y
private lemma bpAs {N:ℕ} {G:SG (Fin N)} {A' B':FS (Fin N)} {x y:Fin N} (h:bpA G A' B' x y):bpA G A' B' y x:=⟨by rcases h.1 with ⟨b,a⟩ | ⟨b,a⟩ <;> [exact Or.inr ⟨a,b⟩;exact Or.inl ⟨a,b⟩],h.2.symm⟩
open Classical in
private noncomputable def dS {N:ℕ} (G:SG (Fin N)) [DecidableRel G.Adj] (A' B':FS (Fin N)) (cA cB:ℕ)(P:List (Fin N)) (D W:FS (Fin N)):List (Fin N) × FS (Fin N) × FS (Fin N):=if _:cA<=(D ∩ A').card\/cB<=(D ∩ B').card then (P,D,W) else match P with
 | []=>([],D,W)
 | v :: rest =>
  if hex:∃ w ∈ W,bpA G A' B' v w then dS G A' B' cA cB (hex.choose :: v :: rest) D (W.erase hex.choose)
  else dS G A' B' cA cB rest (insert v D) W
termination_by 2*W.card+P.length
decreasing_by
 · have a:(W.erase hex.choose).card < W.card:=card_erase_lt_of_mem hex.choose_spec.1;simp only [List.length_cons];omega
 · simp only [List.length_cons];omega
open Classical in
private lemma dSs {N:ℕ} (G:SG (Fin N)) [DecidableRel G.Adj] (A' B':FS (Fin N)) (U:Disjoint A' B')(cA cB:ℕ) (y:Fin N)(z:y∈A') (B:cB<=(G.neighborFinset y ∩ B').card):∀ n:ℕ,∀ (P:List (Fin N)) (D W:FS (Fin N)),2*W.card+P.length=n->P≠[]->P.getLast?=some y->P.Nodup->P.IsChain (bpA G A' B')->P.toFinset⊆A' ∪ B'->D⊆A' ∪ B'->W⊆A' ∪ B'->A' ∪ B'⊆P.toFinset ∪ D ∪ W->Disjoint D W->Disjoint D P.toFinset->Disjoint W P.toFinset->(∀ d ∈ D,∀ w ∈ W,¬ bpA G A' B' d w)->(D ∩ A').card<=cA->(D ∩ B').card<=cB->let e:=dS G A' B' cA cB P D W;e.1≠[]/\e.1.getLast?=some y/\e.1.Nodup/\e.1.IsChain (bpA G A' B')/\e.1.toFinset⊆A' ∪ B'/\e.2.1⊆A' ∪ B'/\e.2.2⊆A' ∪ B'/\A' ∪ B'⊆e.1.toFinset ∪ e.2.1 ∪ e.2.2/\(∀ d ∈ e.2.1,∀ w ∈ e.2.2,¬ bpA G A' B' d w)/\(e.2.1 ∩ A').card<=cA/\(e.2.1 ∩ B').card<=cB/\(cA<=(e.2.1 ∩ A').card\/cB<=(e.2.1 ∩ B').card):=by
 intro n
 induction n using Nat.strong_induction_on with
 | _ n ih =>
  intro P D W hn J g i j m t l u hDW hDP hWP hnoEdge hDA hDB;unfold dS;by_cases a:cA<=(D ∩ A').card\/cB<=(D ∩ B').card
  · simp only [dif_pos a];exact ⟨J,g,i,j,m,t,l,u,hnoEdge,hDA,hDB,a⟩
  · simp only [dif_neg a]
    rcases P with _ | ⟨v,f⟩
    · exact (J rfl).elim
    · by_cases s:∃ w ∈ W,bpA G A' B' v w
      · simp only [dif_pos s]
        set w:=s.choose;have E:w∈W:=s.choose_spec.1;have v0:bpA G A' B' v w:=s.choose_spec.2;have V:w∈A' ∪ B':=l E;have Y:w ∉ (v :: f).toFinset:=D1 hWP E;have X:w ∉ D:=Finset.disjoint_right.mp hDW E
        have L:2*(W.erase w).card+(w :: v :: f).length < n:=by
         have hc:=card_erase_lt_of_mem E;simp only [List.length_cons] at hn ⊢;omega
        refine ih _ L (w :: v :: f) D (W.erase w) rfl (by simp) ?_ ?_ ?_ ?_ t ?_ ?_ ?_ ?_ ?_ ?_ hDA hDB
        · simpa using g
        · exact List.nodup_cons.mpr ⟨by simpa [List.mem_toFinset] using Y,i⟩
        · exact List.IsChain.cons_cons (bpAs v0) j
        · intro x p
          rw [List.toFinset_cons,mem_insert] at p;rcases p with rfl | p
          · exact V
          · exact m p
        · exact (erase_subset w W).trans l
        · intro x p
          rcases mem_union.mp (u p) with A | hW
          · rcases mem_union.mp A with R | hD
            · rw [List.toFinset_cons,mem_union,mem_union,mem_insert];exact Or.inl (Or.inl (Or.inr R))
            · exact mem_union_left _ (mem_union_right _ hD)
          · by_cases h6:x=w
            · subst h6;rw [List.toFinset_cons,mem_union,mem_union,mem_insert];exact Or.inl (Or.inl (Or.inl rfl))
            · exact mem_union_right _ (mem_erase.mpr ⟨h6,hW⟩)
        · exact disjoint_of_subset_right (erase_subset w W) hDW
        · rw [List.toFinset_cons,disjoint_insert_right];exact ⟨X,hDP⟩
        · rw [List.toFinset_cons,disjoint_insert_right];exact ⟨notMem_erase w W,disjoint_of_subset_left (erase_subset w W) hWP⟩
        · intro d q x p;exact hnoEdge d q x (mem_of_mem_erase p)
      · simp only [dif_neg s]
        have T:v∈(v :: f).toFinset:=by simp
        have Q:v∈A' ∪ B':=m T;have I:v ∉ D:=Finset.disjoint_right.mp hDP T;have h9:v ∉ W:=Finset.disjoint_right.mp hWP T
        have h7:v ∉ f.toFinset:=by
         intro h;have:v∈f:=List.mem_toFinset.mp h;exact (List.nodup_cons.mp i).1 this
        have k:f≠[]:=by
         intro Z;subst Z;simp only [List.getLast?_singleton,Option.some.injEq] at g;subst g
         have M:G.neighborFinset v ∩ B'⊆D ∩ B':=by
          intro b C;rw [mem_inter,mem_neighborFinset] at C;have h0:b∈A' ∪ B':=mem_union_right _ C.2;rcases mem_union.mp (u h0) with A | hW
          · rcases mem_union.mp A with R | hD
            · rw [List.mem_toFinset,List.mem_singleton] at R;subst R;exact (D1 U z C.2).elim
            · exact mem_inter.mpr ⟨hD,C.2⟩
          · exact (s ⟨b,hW,Or.inl ⟨z,C.2⟩,C.1⟩).elim
         have v2:cB<=(D ∩ B').card:=B.trans (card_le_card M);exact a (Or.inr v2)
        have L:2*W.card+f.length < n:=by
         simp only [List.length_cons] at hn;omega
        have h8:((insert v D) ∩ A').card<=cA:=by
         by_cases h4:v∈A'
         · have:insert v D ∩ A'=insert v (D ∩ A'):=by
            ext x;simp only [mem_inter,mem_insert];exact ⟨fun ⟨S,H⟩=>S.elim Or.inl (fun q=>Or.inr ⟨q,H⟩),fun h=>h.elim (fun F=>⟨Or.inl F,F ▸ h4⟩) (fun ⟨q,ha⟩=>⟨Or.inr q,ha⟩)⟩
           rw [this,card_insert_of_notMem (fun h=>I (mem_inter.mp h).1)]
           have:(D ∩ A').card < cA:=not_le.mp (fun h=>a (Or.inl h))
           omega
         · have:insert v D ∩ A'=D ∩ A':=by
            ext x;simp only [mem_inter,mem_insert];exact ⟨fun ⟨S,H⟩=>⟨S.elim (fun F=>(h4 (F ▸ H)).elim) id,H⟩,fun ⟨q,ha⟩=>⟨Or.inr q,ha⟩⟩
           rw [this];exact (not_le.mp (fun h=>a (Or.inl h))).le
        have h3:((insert v D) ∩ B').card<=cB:=by
         by_cases h5:v∈B'
         · have:insert v D ∩ B'=insert v (D ∩ B'):=by
            ext x;simp only [mem_inter,mem_insert];exact ⟨fun ⟨S,H⟩=>S.elim Or.inl (fun q=>Or.inr ⟨q,H⟩),fun h=>h.elim (fun F=>⟨Or.inl F,F ▸ h5⟩) (fun ⟨q,C⟩=>⟨Or.inr q,C⟩)⟩
           rw [this,card_insert_of_notMem (fun h=>I (mem_inter.mp h).1)]
           have:(D ∩ B').card < cB:=not_le.mp (fun h=>a (Or.inr h))
           omega
         · have:insert v D ∩ B'=D ∩ B':=by
            ext x;simp only [mem_inter,mem_insert];exact ⟨fun ⟨S,H⟩=>⟨S.elim (fun F=>(h5 (F ▸ H)).elim) id,H⟩,fun ⟨q,C⟩=>⟨Or.inr q,C⟩⟩
           rw [this];exact (not_le.mp (fun h=>a (Or.inr h))).le
        refine ih _ L f (insert v D) W rfl k ?_ (List.nodup_cons.mp i).2 j.tail ?_ ?_ l ?_ ?_ ?_ ?_ ?_ h8 h3
        · rcases f with _ | ⟨r,rs⟩
          · exact (k rfl).elim
          · simpa using g
        · exact fun x p=>m (by simp [List.mem_toFinset] at p ⊢;right;exact p)
        · rw [insert_subset_iff];exact ⟨Q,t⟩
        · intro x p
          rcases mem_union.mp (u p) with A | hW
          · rcases mem_union.mp A with R | hD
            · simp only [List.toFinset_cons,mem_insert] at R
              rcases R with rfl | v1
              · exact mem_union_left _ (mem_union_right _ (mem_insert_self _ _))
              · exact mem_union_left _ (mem_union_left _ v1)
            · exact mem_union_left _ (mem_union_right _ (mem_insert_of_mem hD))
          · exact mem_union_right _ hW
        · exact disjoint_insert_left.mpr ⟨h9,hDW⟩
        · rw [disjoint_insert_left];exact ⟨h7,disjoint_of_subset_right (by intro x p;simp [List.mem_toFinset] at p ⊢;right;exact p) hDP⟩
        · exact disjoint_of_subset_right (by intro x p;simp [List.mem_toFinset] at p ⊢;right;exact p) hWP
        · intro d q w hw K
          rcases mem_insert.mp q with rfl | q
          · exact s ⟨w,hw,K⟩
          · exact hnoEdge d q w hw K
private lemma acp {N:ℕ} (G:SG (Fin N)):∀ (Q:List (Fin N)) (A' B':FS (Fin N)),Disjoint A' B'->Q≠[]->(∀ h:Q≠[],Q.head h∈A')->Q.IsChain (bpA G A' B')->Q.Nodup->(Q.toFinset ∩ A').card<=(Q.length+1)/2/\(Q.toFinset ∩ B').card<=Q.length/2/\(∀ i (w:i < Q.length),(Even i->Q[i]∈A')/\(Odd i->Q[i]∈B')):=by
 intro Q
 induction Q with
 | nil=>intro _ _ _ C;exact (C rfl).elim
 | cons a t ih =>
  intro A' B' l _ p f e;have k:a∈A':=p (by simp)
  have r:a ∉ B':=D1 l k;rcases t with _ | ⟨b,ts⟩
  · refine ⟨?_,?_,?_⟩
    · simp [k]
    · simp [r]
    · intro i w
      have D:i=0:=by simpa using w
      subst D;exact ⟨fun _=>k,fun d=>by simp at d⟩
  · have E:bpA G A' B' a b:=List.IsChain.rel_head f
    have A:b∈B':=by
     rcases E.1 with ⟨_,H⟩ | ⟨I,_⟩
     · exact H
     · exact (r I).elim
    have g:(b :: ts).IsChain (bpA G B' A'):=by
     refine f.tail.imp fun {x y} u=>?_
     rcases u.1 with ⟨z,F⟩ | ⟨z,F⟩
     · exact ⟨Or.inr ⟨z,F⟩,u.2⟩
     · exact ⟨Or.inl ⟨z,F⟩,u.2⟩
    have j:=ih B' A' l.symm (by simp) (fun _=>A) g (List.nodup_cons.mp e).2
    have v:a ∉ (b :: ts).toFinset:=by
     simpa [List.mem_toFinset] using (List.nodup_cons.mp e).1
    have n:(a :: b :: ts).toFinset ∩ A'=insert a ((b :: ts).toFinset ∩ A'):=by
     ext x;simp [k]
    have q:(a :: b :: ts).toFinset ∩ B'=(b :: ts).toFinset ∩ B':=by
     ext x;simp [r]
    refine ⟨?_,?_,?_⟩
    · rw [n,card_insert_of_notMem (fun h=>v (mem_inter.mp h).1)]
      have:=j.2.1;simp only [List.length_cons] at this ⊢;omega
    · rw [q];have:=j.1;simp only [List.length_cons] at this ⊢;omega
    · intro i w
      rcases i with _ | i
      · exact ⟨fun _=>k,fun d=>by simp at d⟩
      · have B:i < (b :: ts).length:=by simpa using w
        have m:=j.2.2 i B;refine ⟨fun s=>?_,fun d=>?_⟩
        · rcases Nat.even_or_odd i with h | h
          · exact absurd h (Nat.even_add_one.mp s)
          · exact m.2 h
        · rcases Nat.even_or_odd i with h | h
          · exact m.1 h
          · exact absurd h (Nat.odd_add_one.mp d)
private lemma dlp {N:ℕ} (G:SG (Fin N)) [DecidableRel G.Adj] (A' B':FS (Fin N)) (t:Disjoint A' B') {cA cB:ℕ} (v2:0 < cA) (v3:0 < cB) (e:∀ X⊆A',∀ Y⊆B',cA<=X.card->cB<=Y.card->∃ x ∈ X,∃ y ∈ Y,G.Adj x y) (d:Fin N)(l:d∈A') (u:cB<=(G.neighborFinset d ∩ B').card):∃ Q:List (Fin N),Q≠[]/\Q.head?=some d/\Q.Nodup/\Q.IsChain (bpA G A' B')/\Q.toFinset⊆A' ∪ B'/\2*(min A'.card B'.card-2*max cA cB)+1<=Q.length/\(∀ i (hi:i < Q.length),(Even i->Q[i]∈A')/\(Odd i->Q[i]∈B')):=by
 have m:d∈A' ∪ B':=mem_union_left _ l;set W₀:=(A' ∪ B').erase d
 have I:=dSs G A' B' t cA cB d l u (2*W₀.card+[d].length) [d] ∅ W₀ rfl (by simp) (by simp) (by simp) (by simp) (by simp [m]) (by simp) (erase_subset _ _) (fun x F=>by
  by_cases h:x=d
  · subst h;simp
  · exact mem_union_right _ (mem_erase.mpr ⟨h,F⟩))
  (by simp) (by simp) (by simp [W₀]) (by simp) (by simp) (by simp)
 set R:=dS G A' B' cA cB [d] ∅ W₀;set P:=R.1;set D:=R.2.1;set W:=R.2.2;obtain ⟨h0,B,s,p,L,h7,h4,H,g,h3,h5,K⟩:=I;set Q:=P.reverse;have q:Q≠[]:=by simpa [Q] using h0
 have n:Q.head?=some d:=by
  rw [List.head?_reverse];exact B
 have k:Q.Nodup:=List.nodup_reverse.mpr s
 have j:Q.IsChain (bpA G A' B'):=by
  rw [List.isChain_reverse]
  exact p.imp (fun {_ _} h=>bpAs h)
 have M:Q.toFinset⊆A' ∪ B':=by
  intro x F;exact L (by simpa [Q] using F)
 have f:=acp G Q A' B' t q (fun h=>by
  have:=List.head?_eq_some_head h;rw [n] at this;exact (Option.some.inj this).symm ▸ l) j k
 have h6:0 < Q.length:=List.length_pos_of_ne_nil q
 have T:2*(min A'.card B'.card-2*max cA cB)+1<=Q.length:=by
  rcases K with w | C
  · have v0:(W ∩ B').card < cB:=by
     by_contra! A;obtain ⟨x,F,y,hy,r⟩:=e (D ∩ A') inter_subset_right (W ∩ B') inter_subset_right w A;exact g x (mem_inter.mp F).1 y (mem_inter.mp hy).1 ⟨Or.inl ⟨(mem_inter.mp F).2,(mem_inter.mp hy).2⟩,r⟩
    have E:B'⊆(Q.toFinset ∩ B') ∪ (D ∩ B') ∪ (W ∩ B'):=by
     intro b hb;have S:b∈A' ∪ B':=mem_union_right _ hb;rcases mem_union.mp (H S) with J | hW
     · rcases mem_union.mp J with hP | hD
       · exact mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨by simpa [Q] using hP,hb⟩))
       · exact mem_union_left _ (mem_union_right _ (mem_inter.mpr ⟨hD,hb⟩))
     · exact mem_union_right _ (mem_inter.mpr ⟨hW,hb⟩)
    have h1:B'.card<=(Q.toFinset ∩ B').card+(D ∩ B').card+(W ∩ B').card :=
     (card_le_card E).trans ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
    have v1:=f.2.1;have h8:(D ∩ B').card<=cB:=h5;have U:=min_le_right A'.card B'.card;have h2:=le_max_right cA cB;omega
  · have v5:(W ∩ A').card < cA:=by
     by_contra! z;obtain ⟨x,F,y,hy,r⟩:=e (W ∩ A') inter_subset_right (D ∩ B') inter_subset_right z C;exact g y (mem_inter.mp hy).1 x (mem_inter.mp F).1 ⟨Or.inr ⟨(mem_inter.mp hy).2,(mem_inter.mp F).2⟩,r.symm⟩
    have v:A'⊆(Q.toFinset ∩ A') ∪ (D ∩ A') ∪ (W ∩ A'):=by
     intro a ha;have V:a∈A' ∪ B':=mem_union_left _ ha;rcases mem_union.mp (H V) with J | hW
     · rcases mem_union.mp J with hP | hD
       · exact mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨by simpa [Q] using hP,ha⟩))
       · exact mem_union_left _ (mem_union_right _ (mem_inter.mpr ⟨hD,ha⟩))
     · exact mem_union_right _ (mem_inter.mpr ⟨hW,ha⟩)
    have Z:A'.card<=(Q.toFinset ∩ A').card+(D ∩ A').card+(W ∩ A').card :=
     (card_le_card v).trans ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
    have v4:=f.1;have h9:(D ∩ A').card<=cA:=h3;have U:=min_le_left A'.card B'.card;have h2:=le_max_left cA cB;omega
 exact ⟨Q,q,n,k,j,M,T,f.2.2⟩
private lemma emp {t:ℕ} {R:SG (Fin t)} (M:R.Subgraph)(V:M.IsMatching):∀ (k:ℕ)(S:FS (Fin t)),(∀ x ∈ S,x∈M.verts)->(∀ x ∈ S,∀ y,M.Adj x y->y∈S)->2*k<=S.card->∃ a:List (Fin t × Fin t),a.length=k/\(∀ p ∈ a,M.Adj p.1 p.2)/\(∀ p ∈ a,p.1∈S/\p.2∈S)/\(a.flatMap (fun p=>[p.1,p.2])).Nodup:=by
 intro k
 induction k with
 | zero =>
  intro S _ _ _;exact ⟨[],rfl,by simp,by simp,by simp⟩
 | succ k ih =>
  intro S g d J;have I:S.Nonempty:=card_pos.mp (by omega)
  obtain ⟨u,n⟩:=I;obtain ⟨v,e,s⟩:=V (g u n);have H:v∈S:=d u n v e;have F:u≠v:=R.ne_of_adj (M.adj_sub e);set S':=(S.erase u).erase v;have j:∀ x ∈ S',x∈M.verts:=fun x G=>g x (mem_of_mem_erase (mem_of_mem_erase G))
  have i:∀ x ∈ S',∀ y,M.Adj x y->y∈S':=by
   intro x G y B;have N:=mem_of_mem_erase (mem_of_mem_erase G);have T:x≠v:=ne_of_mem_erase G;have P:x≠u:=ne_of_mem_erase (mem_of_mem_erase G);have K:=d x N y B;refine mem_erase.mpr ⟨?_,mem_erase.mpr ⟨?_,K⟩⟩
   · intro U;subst U;exact P (V.eq_of_adj_right B e)
   · intro L;subst L;exact T (s x B.symm)
  have l:2*k<=S'.card:=by
   have W:(S.erase u).card=S.card-1:=card_erase_of_mem n;have z:v∈S.erase u:=mem_erase.mpr ⟨F.symm,H⟩;have X:S'.card=(S.erase u).card-1:=card_erase_of_mem z;omega
  obtain ⟨a,D,E,b,r⟩:=ih S' j i l
  have C:u ∉ a.flatMap (fun p=>[p.1,p.2]):=by
   rw [List.mem_flatMap];rintro ⟨q,Q,m⟩;have f:=b q Q;simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at m;rcases m with rfl | rfl
   · exact ne_of_mem_erase (mem_of_mem_erase f.1) rfl
   · exact ne_of_mem_erase (mem_of_mem_erase f.2) rfl
  have A:v ∉ a.flatMap (fun p=>[p.1,p.2]):=by
   rw [List.mem_flatMap];rintro ⟨q,Q,m⟩;have f:=b q Q;simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at m;rcases m with rfl | rfl
   · exact ne_of_mem_erase f.1 rfl
   · exact ne_of_mem_erase f.2 rfl
  refine ⟨(u,v) :: a,by simp [D],?_,?_,?_⟩
  · intro p w
    rcases List.mem_cons.mp w with rfl | w
    · exact e
    · exact E p w
  · intro p w
    rcases List.mem_cons.mp w with rfl | w
    · exact ⟨n,H⟩
    · exact ⟨mem_of_mem_erase (mem_of_mem_erase (b p w).1),mem_of_mem_erase (mem_of_mem_erase (b p w).2)⟩
  · simp only [List.flatMap_cons,List.cons_append,List.nil_append,List.nodup_cons]
    refine ⟨?_,A,r⟩;simp only [List.mem_cons];rintro (rfl | h)
    · exact F rfl
    · exact C h
private lemma wbe {t:ℕ} {R:SG (Fin t)} {V:FS (Fin t)} {a b:Fin t} (g:a∈V)(e:b ∉ V) (d:R.Reachable a b):∃ x y:Fin t,R.Adj x y/\x∈V/\y ∉ V:=by
 obtain ⟨w⟩:=d
 induction w with
 | nil=>exact (e g).elim
 | @cons u v c huv _ ih =>
  by_cases f:v∈V
  · exact ih f e
  · exact ⟨u,v,huv,g,f⟩
private def spA {α :Type*} [DecidableEq α] (x: α)(a W:List (α × α × Bool)):List (α × α × Bool):=match W with
 | []=>a
 | e :: rest=>if e.1=x then a ++ e :: rest else e :: spA x a rest
private lemma ica {α :Type*} {r: α->α->Prop} {d e:List α} (f:d.IsChain r)(g:e.IsChain r) (h:∀ a ∈ d.getLast?,∀ b ∈ e.head?,r a b):(d ++ e).IsChain r:=by
 induction d with
 | nil=>simpa using g
 | cons x xs ih =>
  rcases xs with _ | ⟨y,ys⟩
  · simp only [List.nil_append,List.singleton_append]
    rcases e with _ | ⟨b,bs⟩
    · exact f
    · exact List.IsChain.cons_cons (h x (by simp) b (by simp)) g
  · simp only [List.cons_append];exact List.IsChain.cons_cons (List.IsChain.rel_head f) (ih f.tail (fun a j b i=>h a (by simpa using j) b i))
private lemma spAp {α :Type*} [DecidableEq α] (x: α)(h W:List (α × α × Bool)) (s:W≠[])(G:∃ e ∈ W,e.1=x) (g:W.IsChain (fun a b=>a.2.1=b.1)) (d:h≠[])(m:(h.head d).1=x) (n:(h.getLast d).2.1=x) (l:h.IsChain (fun a b=>a.2.1=b.1)):let W':=spA x h W;W'≠[]/\(∀ y:W'≠[],(W'.head y).1=(W.head s).1)/\(∀ y:W'≠[],W'.getLast y=W.getLast s)/\W'.length=W.length+h.length/\W'.IsChain (fun a b=>a.2.1=b.1)/\(∀ e,e∈W'↔e∈h\/e∈W)/\List.Perm (W'.filter (·.2.2)) (h.filter (·.2.2) ++ W.filter (·.2.2)):=by
 induction W with
 | nil=>exact (s rfl).elim
 | cons e rest ih =>
  unfold spA;by_cases B:e.1=x
  · rw [if_pos B]
    have C:h ++ e :: rest≠[]:=List.append_ne_nil_of_right_ne_nil _ (by simp)
    refine ⟨C,?_,?_,?_,?_,?_,?_⟩
    · intro y;rw [List.head_append_of_ne_nil d];simpa [B] using m
    · intro y;exact List.getLast_append_of_ne_nil _ (by simp)
    · simp;omega
    · refine ica l g ?_
      intro a H b J
      have E:a=h.getLast d:=(by
       rw [List.getLast?_eq_some_getLast d] at H;simpa using H:h.getLast d=a).symm
      have F:b=e:=(by simpa using J:e=b).symm
      subst E;subst F;simpa [B] using n
    · intro z;simp
    · rw [List.filter_append]
  · rw [if_neg B]
    have i:∃ e' ∈ rest,e'.1=x:=by
     rcases G with ⟨e',u,A⟩;rcases List.mem_cons.mp u with rfl | u
     · exact (B A).elim
     · exact ⟨e',u,A⟩
    have f:rest≠[]:=by
     rintro rfl;obtain ⟨e',u,_⟩:=i;exact (List.not_mem_nil u).elim
    obtain ⟨j,q,t,v,p,w,k⟩:=ih f i g.tail;refine ⟨by simp,?_,?_,?_,?_,?_,?_⟩
    · intro _;simp
    · intro y;rw [List.getLast_cons j,t j,List.getLast_cons f]
    · simp [v];omega
    · refine List.IsChain.cons_of_ne_nil j p ?_
      rw [q j];rcases rest with _ | ⟨r,rs⟩
      · exact (f rfl).elim
      · simp only [List.head_cons];exact List.isChain_iff_getElem.mp g 0 (by simp)
    · intro z;simp only [List.mem_cons,w];tauto
    · by_cases I:e.2.2=true
      · simp only [List.filter_cons,I,↓reduceIte];exact (k.cons e).trans (List.perm_middle.symm)
      · have D:e.2.2=false:=Bool.eq_false_iff.mpr I;simp only [List.filter_cons,D,Bool.false_eq_true,↓reduceIte];exact k
private lemma nfpu {α :Type*}:∀ (L:List (α × α)) (p q: α × α),(L.flatMap (fun r=>[r.1,r.2])).Nodup->p∈L->q∈L->(q.1=p.1\/q.1=p.2\/q.2=p.1\/q.2=p.2)->q=p:=by
 intro L
 induction L with
 | nil=>intro p q _ l;exact (List.not_mem_nil l).elim
 | cons a t ih =>
  intro p q b l m d;simp only [List.flatMap_cons,List.cons_append,List.nil_append,List.nodup_cons] at b;rcases List.mem_cons.mp l with j | f
  · rcases List.mem_cons.mp m with g | e
    · exact g.trans j.symm
    · exfalso
      have i:q.1∈t.flatMap (fun r=>[r.1,r.2]):=List.mem_flatMap.mpr ⟨q,e,by simp⟩
      have k:q.2∈t.flatMap (fun r=>[r.1,r.2]):=List.mem_flatMap.mpr ⟨q,e,by simp⟩
      rw [j] at d;rcases d with h | h | h | h
      · exact b.1 (List.mem_cons.mpr (Or.inr (h ▸ i)))
      · exact b.2.1 (h ▸ i)
      · exact b.1 (List.mem_cons.mpr (Or.inr (h ▸ k)))
      · exact b.2.1 (h ▸ k)
  · rcases List.mem_cons.mp m with g | e
    · exfalso
      have i:p.1∈t.flatMap (fun r=>[r.1,r.2]):=List.mem_flatMap.mpr ⟨p,f,by simp⟩
      have k:p.2∈t.flatMap (fun r=>[r.1,r.2]):=List.mem_flatMap.mpr ⟨p,f,by simp⟩
      rw [g] at d;rcases d with h | h | h | h
      · exact b.1 (List.mem_cons.mpr (Or.inr (h.symm ▸ i)))
      · exact b.1 (List.mem_cons.mpr (Or.inr (h.symm ▸ k)))
      · exact b.2.1 (h.symm ▸ i)
      · exact b.2.1 (h.symm ▸ k)
    · exact ih p q b.2.2 f e d
private lemma flit {α :Type*} [DecidableEq α] (L:List (α × α)) (B:L.Nodup)(V:FS α) (y y': α)(p: α × α) (n:p∈L)(e:(p.1=y/\p.2=y')\/(p.1=y'/\p.2=y)) (b:∀ q ∈ L,(q.1=y\/q.1=y')->q=p) (A:y ∉ V)(s:y' ∉ V):(L.filter (fun q=>decide (q.1∈insert y (insert y' V)))).length=(L.filter (fun q=>decide (q.1∈V))).length+1:=by
 induction L with
 | nil=>exact (List.not_mem_nil n).elim
 | cons a t ih =>
  have v:a ∉ t:=(List.nodup_cons.mp B).1;have D:t.Nodup:=(List.nodup_cons.mp B).2;rcases List.mem_cons.mp n with u | C
  · have i:decide (p.1∈V)=false:=by
     rw [decide_eq_false_iff_not];rcases e with ⟨l,_⟩ | ⟨l,_⟩
     · exact l ▸ A
     · exact l ▸ s
    have k:decide (p.1∈insert y (insert y' V))=true:=by
     rw [decide_eq_true_eq];rcases e with ⟨l,_⟩ | ⟨l,_⟩
     · exact l ▸ mem_insert_self _ _
     · exact l ▸ mem_insert_of_mem (mem_insert_self _ _)
    have g:t.filter (fun q=>decide (q.1∈insert y (insert y' V)))=t.filter (fun q=>decide (q.1∈V)):=by
     refine List.filter_congr fun q j=>?_
     have z:q≠p:=fun h=>v (u ▸ h ▸ j)
     have x:¬ (q.1=y\/q.1=y'):=fun h=>z (b q (List.mem_cons_of_mem _ j) h)
     have d:q.1∈insert y (insert y' V)↔q.1∈V:=by simp only [mem_insert];tauto
     simp only [d]
    rw [<- u];simp only [List.filter_cons,i,k,Bool.false_eq_true,↓reduceIte,g,List.length_cons]
  · have f:a≠p:=fun h=>v (h ▸ C)
    have w:¬ (a.1=y\/a.1=y'):=fun h=>f (b a List.mem_cons_self h)
    have d:a.1∈insert y (insert y' V)↔a.1∈V:=by simp only [mem_insert];tauto
    have m:decide (a.1∈insert y (insert y' V))=decide (a.1∈V):=by simp only [d]
    have r:=ih D C (fun q j h=>b q (List.mem_cons_of_mem _ j) h)
    simp only [List.filter_cons,m];cases h:decide (a.1∈V)
    · simp only [Bool.false_eq_true,↓reduceIte,r]
    · simp only [↓reduceIte,List.length_cons,r]
private lemma bcw {t:ℕ} {R:SG (Fin t)} (m:List (Fin t × Fin t)) (v7:m≠[])(A:∀ p ∈ m,R.Adj p.1 p.2) (d:(m.flatMap (fun p=>[p.1,p.2])).Nodup) (h4:∀ p ∈ m,∀ q ∈ m,R.Reachable p.1 q.1):∃ W:List (Fin t × Fin t × Bool),W≠[]/\(∀ e ∈ W,R.Adj e.1 e.2.1)/\W.IsChain (fun a b=>a.2.1=b.1)/\(∀ h:W≠[],(W.getLast h).2.1=(W.head h).1)/\(∀ h:W≠[],(W.getLast h).2.2=false)/\Even W.length/\2<=W.length/\W.length<=2*t/\m.length<=W.length/2/\(m.length=1->W.length=2)/\W.countP (·.2.2)=m.length/\((W.filter (·.2.2)).flatMap (fun e=>[e.1,e.2.1])).Nodup:=by
 classical
 rcases m with _ | ⟨⟨f,g⟩,Z⟩
 · exact (v7 rfl).elim
 have s:(f,g)∈(f,g) :: Z:=List.mem_cons_self;have H:R.Adj f g:=A _ s;have y2:f≠g:=R.ne_of_adj H;set W₀ :List (Fin t × Fin t × Bool):=[(f,g,true),(g,f,false)]
 set V₀ :FS (Fin t):={f,g};have v6:V₀.card=2:=card_pair y2
 have b0:2<=t:=by
  have B:V₀.card<=t:=by simpa using card_le_univ V₀
  omega
 by_cases y1:Z=[]
 · subst y1
   refine ⟨W₀,by simp [W₀],?_,List.IsChain.cons_cons rfl (List.IsChain.singleton _),by simp [W₀],by simp [W₀],⟨1,rfl⟩,by simp [W₀],by simp [W₀];omega,by simp [W₀],fun _=>by simp [W₀],by simp [W₀],by simp [W₀,y2]⟩
   intro e he;simp only [W₀,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at he;rcases he with rfl | rfl
   · exact H
   · exact H.symm
 set ch:=(f,g) :: Z
 have x3:ch.Nodup:=by
  have:∀ (L:List (Fin t × Fin t)),(L.flatMap (fun p=>[p.1,p.2])).Nodup->L.Nodup:=by
   intro L h
   induction L with
   | nil=>simp
   | cons a ts ih =>
    simp only [List.flatMap_cons,List.cons_append,List.nil_append,List.nodup_cons] at h;refine List.nodup_cons.mpr ⟨fun ha=>?_,ih h.2.2⟩
    exact h.1 (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨a,ha,List.mem_cons_self⟩))
  exact this ch d
 have a0:∀ n:ℕ,∀ (W:List (Fin t × Fin t × Bool)) (V:FS (Fin t)),t-V.card=n->W≠[]->(∀ e ∈ W,R.Adj e.1 e.2.1)->W.IsChain (fun a b=>a.2.1=b.1)->(∀ h:W≠[],(W.getLast h).2.1=(W.head h).1)->(∀ h:W≠[],(W.getLast h).2.2=false)->f∈V->(∀ e ∈ W,e.1∈V/\e.2.1∈V)->(∀ v ∈ V,∃ e ∈ W,e.1=v)->W.length=2*(V.card-1)->2<=V.card->(∀ p ∈ ch,(p.1∈V/\p.2∈V)\/(p.1 ∉ V/\p.2 ∉ V))->W.countP (·.2.2)=(ch.filter (fun p=>decide (p.1∈V))).length->((W.filter (·.2.2)).flatMap (fun e=>[e.1,e.2.1])).Nodup->∃ W':List (Fin t × Fin t × Bool),W'≠[]/\(∀ e ∈ W',R.Adj e.1 e.2.1)/\W'.IsChain (fun a b=>a.2.1=b.1)/\(∀ h:W'≠[],(W'.getLast h).2.1=(W'.head h).1)/\(∀ h:W'≠[],(W'.getLast h).2.2=false)/\Even W'.length/\2<=W'.length/\W'.length<=2*t/\ch.length<=W'.length/2/\(ch.length=1->W'.length=2)/\W'.countP (·.2.2)=ch.length/\((W'.filter (·.2.2)).flatMap (fun e=>[e.1,e.2.1])).Nodup:=by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
   intro W V hn U x2 S h9 h5 y5 x7 z9 x9 b1 J h0 M;by_cases h7:∀ p ∈ ch,p.1∈V/\p.2∈V
   · have v0:ch.filter (fun p=>decide (p.1∈V))=ch:=List.filter_eq_self.mpr fun p hp=>decide_eq_true (h7 p hp).1
     have v5:∀ z ∈ ch.flatMap (fun p=>[p.1,p.2]),z∈V:=by
      intro z hz;rw [List.mem_flatMap] at hz;obtain ⟨p,hp,y9⟩:=hz;rcases List.mem_cons.mp y9 with rfl | y9
      · exact (h7 p hp).1
      · rw [List.mem_singleton] at y9;subst y9;exact (h7 p hp).2
     have a9:2*ch.length<=V.card:=by
      have B:(ch.flatMap (fun p=>[p.1,p.2])).toFinset⊆V:=fun z hz=>v5 z (List.mem_toFinset.mp hz)
      have K:=card_le_card B;rw [List.toFinset_card_of_nodup d] at K
      have h3:(ch.flatMap (fun p=>[p.1,p.2])).length=2*ch.length:=by
       clear B K v5 v0 h7
       induction ch with
       | nil=>simp
       | cons a ts ihc=>simp [ihc];omega
      omega
     have a4:V.card<=t:=by simpa using card_le_univ V
     refine ⟨W,U,x2,S,h9,h5,?_,by omega,by omega,by omega,fun z5=>by exfalso;simp [ch] at z5;exact y1 z5,?_,M⟩
     · exact ⟨V.card-1,by omega⟩
     · rw [h0,v0]
   · push_neg at h7
     obtain ⟨p,y0,y7⟩:=h7
     have v3:p.1 ∉ V/\p.2 ∉ V:=by
      rcases J p y0 with h | h
      · exact (y7 h.1 h.2).elim
      · exact h
     obtain ⟨x,y,I,y4,x0⟩:=wbe y5 v3.1 (h4 (f,g) s p y0);obtain ⟨ex,z1,z3⟩:=z9 x y4;by_cases P:∃ q ∈ ch,q.1=y\/q.2=y
     · obtain ⟨q,w,a1⟩:=P
       set y':=if q.1=y then q.2 else q.1
       have l:(q.1=y/\q.2=y')\/(q.1=y'/\q.2=y):=by
        by_cases h:q.1=y
        · exact Or.inl ⟨h,by simp [y',h]⟩
        · exact Or.inr ⟨by simp [y',h],a1.resolve_left h⟩
       have v2:R.Adj y y':=by
        rcases l with ⟨B,K⟩ | ⟨B,K⟩
        · rw [<- B,<-K];exact A q w
        · rw [<- B,<-K];exact (A q w).symm
       have z4:y≠y':=R.ne_of_adj v2
       have x4:y' ∉ V:=by
        rcases J q w with h | h
        · exfalso
          rcases a1 with B | B
          · exact x0 (B ▸ h.1)
          · exact x0 (B ▸ h.2)
        · rcases l with ⟨_,K⟩ | ⟨B,_⟩
          · exact K ▸ h.2
          · exact B ▸ h.1
       set j:List (Fin t × Fin t × Bool):=[(x,y,false),(y,y',true),(y',y,false),(y,x,false)];have N:j≠[]:=by simp [j]
       have C:j.IsChain (fun a b=>a.2.1=b.1):=by
        simp only [j];exact List.IsChain.cons_cons rfl (List.IsChain.cons_cons rfl (List.IsChain.cons_cons rfl (List.IsChain.singleton _)))
       obtain ⟨y6,v4,F,x1,Q,u,G⟩:=spAp x j W U ⟨ex,z1,z3⟩ S N rfl rfl C;set W':=spA x j W;set V':=insert y (insert y' V)
       have Y:V'.card=V.card+2:=by
        have z0:y ∉ insert y' V:=by
         simp [z4,x0]
        rw [card_insert_of_notMem z0,card_insert_of_notMem x4]
       have a4:V.card<=t:=by simpa using card_le_univ V
       have a2:V'.card<=t:=by simpa using card_le_univ V'
       have z7:t-V'.card < n:=by omega
       refine ih _ z7 W' V' rfl y6 ?_ Q ?_ ?_ ?_ ?_ ?_ ?_ (by omega) ?_ ?_ ?_
       · intro e he
         rcases (u e).mp he with i | T
         · simp only [j,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at i
           rcases i with rfl | rfl | rfl | rfl
           · exact I
           · exact v2
           · exact v2.symm
           · exact I.symm
         · exact x2 e T
       · intro h';rw [F h',v4 h',h9 U]
       · intro h';rw [F h',h5 U]
       · exact mem_insert_of_mem (mem_insert_of_mem y5)
       · intro e he
         rcases (u e).mp he with i | T
         · simp only [j,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at i
           rcases i with rfl | rfl | rfl | rfl
           · exact ⟨mem_insert_of_mem (mem_insert_of_mem y4),mem_insert_self _ _⟩
           · exact ⟨mem_insert_self _ _,mem_insert_of_mem (mem_insert_self _ _)⟩
           · exact ⟨mem_insert_of_mem (mem_insert_self _ _),mem_insert_self _ _⟩
           · exact ⟨mem_insert_self _ _,mem_insert_of_mem (mem_insert_of_mem y4)⟩
         · have:=x7 e T;exact ⟨mem_insert_of_mem (mem_insert_of_mem this.1),mem_insert_of_mem (mem_insert_of_mem this.2)⟩
       · intro v hv
         simp only [V',mem_insert] at hv;rcases hv with z8 | a3 | hv
         · exact ⟨(y,y',true),(u _).mpr (Or.inl (by simp [j])),z8.symm⟩
         · exact ⟨(y',y,false),(u _).mpr (Or.inl (by simp [j])),a3.symm⟩
         · obtain ⟨e,v1,z6⟩:=z9 v hv;exact ⟨e,(u _).mpr (Or.inr v1),z6⟩
       · rw [x1,Y,x9];simp [j];omega
       · intro r hr
         rcases J r hr with ⟨v8,v9⟩ | ⟨v8,v9⟩
         · exact Or.inl ⟨mem_insert_of_mem (mem_insert_of_mem v8),mem_insert_of_mem (mem_insert_of_mem v9)⟩
         · by_cases h6:r=q
           · subst h6
             rcases l with ⟨B,K⟩ | ⟨B,K⟩
             · exact Or.inl ⟨B ▸ mem_insert_self _ _,K ▸ mem_insert_of_mem (mem_insert_self _ _)⟩
             · exact Or.inl ⟨B ▸ mem_insert_of_mem (mem_insert_self _ _),K ▸ mem_insert_self _ _⟩
           · refine Or.inr ⟨?_,?_⟩
             · simp only [V',mem_insert,not_or]
               refine ⟨fun h=>h6 (nfpu ch q r d w hr ?_),fun h=>h6 (nfpu ch q r d w hr ?_),v8⟩
               · rcases l with ⟨B,_⟩ | ⟨_,K⟩ <;> [exact Or.inl (h.trans B.symm);exact Or.inr (Or.inl (h.trans K.symm))]
               · rcases l with ⟨_,K⟩ | ⟨B,_⟩ <;> [exact Or.inr (Or.inl (h.trans K.symm));exact Or.inl (h.trans B.symm)]
             · simp only [V',mem_insert,not_or]
               refine ⟨fun h=>h6 (nfpu ch q r d w hr ?_),fun h=>h6 (nfpu ch q r d w hr ?_),v9⟩
               · rcases l with ⟨B,_⟩ | ⟨_,K⟩ <;> [exact Or.inr (Or.inr (Or.inl (h.trans B.symm)));exact Or.inr (Or.inr (Or.inr (h.trans K.symm)))]
               · rcases l with ⟨_,K⟩ | ⟨B,_⟩ <;> [exact Or.inr (Or.inr (Or.inr (h.trans K.symm)));exact Or.inr (Or.inr (Or.inl (h.trans B.symm)))]
       · rw [List.countP_eq_length_filter] at h0 ⊢
         have k:=G.length_eq;have E:j.filter (·.2.2)=[(y,y',true)]:=by simp [j]
         rw [E,List.length_append] at k;simp only [List.length_singleton] at k
         have y3:∀ r ∈ ch,(r.1=y\/r.1=y')->r=q:=by
          intro r hr h;refine nfpu ch q r d w hr ?_;rcases h with h | h
          · rcases l with ⟨B,_⟩ | ⟨_,K⟩
            · exact Or.inl (h.trans B.symm)
            · exact Or.inr (Or.inl (h.trans K.symm))
          · rcases l with ⟨_,K⟩ | ⟨B,_⟩
            · exact Or.inr (Or.inl (h.trans K.symm))
            · exact Or.inl (h.trans B.symm)
         rw [k,h0,flit ch x3 V y y' q w l y3 x0 x4];omega
       · have D:List.Perm ((W'.filter (·.2.2)).flatMap (fun e=>[e.1,e.2.1])) (y :: y' :: (W.filter (·.2.2)).flatMap (fun e=>[e.1,e.2.1])):=by
          have B:=G.flatMap (fun e _=>List.Perm.refl [e.1,e.2.1])
          simpa [j] using B
         rw [D.nodup_iff,List.nodup_cons,List.nodup_cons];refine ⟨?_,?_,M⟩
         · intro h
           rcases List.mem_cons.mp h with a8 | h
           · exact z4 a8
           · rw [List.mem_flatMap] at h
             rcases h with ⟨e,he,x5⟩;have v1:e∈W:=(List.mem_filter.mp he).1;rcases List.mem_cons.mp x5 with x5 | x5
             · exact x0 (x5 ▸ (x7 e v1).1)
             · rw [List.mem_singleton] at x5;exact x0 (x5 ▸ (x7 e v1).2)
         · rw [List.mem_flatMap]
           rintro ⟨e,he,h8⟩;have v1:e∈W:=(List.mem_filter.mp he).1;rcases List.mem_cons.mp h8 with h8 | h8
           · exact x4 (h8 ▸ (x7 e v1).1)
           · rw [List.mem_singleton] at h8
             exact x4 (h8 ▸ (x7 e v1).2)
     · push_neg at P
       set j:List (Fin t × Fin t × Bool):=[(x,y,false),(y,x,false)];have N:j≠[]:=by simp [j]
       have C:j.IsChain (fun a b=>a.2.1=b.1):=by
        simp only [j];exact List.IsChain.cons_cons rfl (List.IsChain.singleton _)
       obtain ⟨y6,v4,F,x1,Q,u,G⟩:=spAp x j W U ⟨ex,z1,z3⟩ S N rfl rfl C;set W':=spA x j W;set V':=insert y V;have Y:V'.card=V.card+1:=card_insert_of_notMem x0;have a2:V'.card<=t:=by simpa using card_le_univ V'
       have z7:t-V'.card < n:=by omega
       refine ih _ z7 W' V' rfl y6 ?_ Q ?_ ?_ ?_ ?_ ?_ ?_ (by omega) ?_ ?_ ?_
       · intro e he
         rcases (u e).mp he with i | T
         · simp only [j,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at i
           rcases i with rfl | rfl
           · exact I
           · exact I.symm
         · exact x2 e T
       · intro h';rw [F h',v4 h',h9 U]
       · intro h';rw [F h',h5 U]
       · exact mem_insert_of_mem y5
       · intro e he
         rcases (u e).mp he with i | T
         · simp only [j,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at i
           rcases i with rfl | rfl
           · exact ⟨mem_insert_of_mem y4,mem_insert_self _ _⟩
           · exact ⟨mem_insert_self _ _,mem_insert_of_mem y4⟩
         · have:=x7 e T;exact ⟨mem_insert_of_mem this.1,mem_insert_of_mem this.2⟩
       · intro v hv
         rcases mem_insert.mp hv with z8 | hv
         · exact ⟨(y,x,false),(u _).mpr (Or.inl (by simp [j])),z8.symm⟩
         · obtain ⟨e,v1,z6⟩:=z9 v hv;exact ⟨e,(u _).mpr (Or.inr v1),z6⟩
       · rw [x1,Y,x9];simp [j];omega
       · intro r hr
         rcases J r hr with ⟨v8,v9⟩ | ⟨v8,v9⟩
         · exact Or.inl ⟨mem_insert_of_mem v8,mem_insert_of_mem v9⟩
         · exact Or.inr ⟨fun h=>by
            rcases mem_insert.mp h with h | h
            · exact (P r hr).1 h
            · exact v8 h,
            fun h=>by
             rcases mem_insert.mp h with h | h
             · exact (P r hr).2 h
             · exact v9 h⟩
       · rw [List.countP_eq_length_filter] at h0 ⊢
         have k:=G.length_eq;have E:j.filter (·.2.2)=[]:=by simp [j]
         rw [E,List.nil_append] at k
         have y8:ch.filter (fun r=>decide (r.1∈V'))=ch.filter (fun r=>decide (r.1∈V)):=by
          refine List.filter_congr fun r hr=>?_
          have a6:r.1≠y:=fun h=>(P r hr).1 h
          simp [V',a6]
         rw [k,h0,y8]
       · have D:List.Perm ((W'.filter (·.2.2)).flatMap (fun e=>[e.1,e.2.1])) ((W.filter (·.2.2)).flatMap (fun e=>[e.1,e.2.1])):=by
          have B:=G.flatMap (fun e _=>List.Perm.refl [e.1,e.2.1])
          simpa [j] using B
         exact D.nodup_iff.mpr M
 have X:∀ p ∈ ch,(p.1∈V₀/\p.2∈V₀)\/(p.1 ∉ V₀/\p.2 ∉ V₀):=by
  intro p hp;by_cases x8:p=(f,g)
  · subst x8;exact Or.inl ⟨by simp [V₀],by simp [V₀]⟩
  · refine Or.inr ⟨?_,?_⟩
    · simp only [V₀,mem_insert,mem_singleton,not_or];exact ⟨fun h=>x8 (nfpu ch (f,g) p d s hp (Or.inl h)),fun h=>x8 (nfpu ch (f,g) p d s hp (Or.inr (Or.inl h)))⟩
    · simp only [V₀,mem_insert,mem_singleton,not_or];exact ⟨fun h=>x8 (nfpu ch (f,g) p d s hp (Or.inr (Or.inr (Or.inl h)))),fun h=>x8 (nfpu ch (f,g) p d s hp (Or.inr (Or.inr (Or.inr h))))⟩
 have x6:W₀.countP (·.2.2)=(ch.filter (fun p=>decide (p.1∈V₀))).length:=by
  have v0:ch.filter (fun p=>decide (p.1∈V₀))=[(f,g)]:=by
   simp only [ch,List.filter_cons,decide_eq_true (by simp [V₀]:f∈V₀),↓reduceIte,List.cons.injEq,true_and]
   rw [List.filter_eq_nil_iff]
   intro p hp
   have z2:p≠(f,g):=by
    intro h;subst h;simp only [ch,List.flatMap_cons,List.cons_append,List.nil_append,List.nodup_cons] at d;exact d.1 (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨(f,g),hp,List.mem_cons_self⟩))
   have v3:p.1 ∉ V₀:=by
    rcases X p (List.mem_cons_of_mem _ hp) with h | h
    · exfalso
      exact z2 (nfpu ch (f,g) p d s (List.mem_cons_of_mem _ hp) (Or.inl (by
       rcases mem_insert.mp h.1 with B | B
       · exact B
       · rw [mem_singleton] at B
         exfalso;exact z2 (nfpu ch (f,g) p d s (List.mem_cons_of_mem _ hp) (Or.inr (Or.inl B))))))
    · exact h.1
   simp [v3]
  simp [W₀,v0]
 refine a0 (t-V₀.card) W₀ V₀ rfl (by simp [W₀]) ?_ ?_ (by simp [W₀]) (by simp [W₀]) (by simp [V₀]) ?_ ?_ (by simp [W₀,v6]) (by omega) X x6 ?_
 · intro e he
   simp only [W₀,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at he;rcases he with rfl | rfl
   · exact H
   · exact H.symm
 · exact List.IsChain.cons_cons rfl (List.IsChain.singleton _)
 · intro e he;simp only [W₀,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at he;rcases he with rfl | rfl <;> simp [V₀]
 · intro v hv
   simp only [V₀,mem_insert,mem_singleton] at hv;rcases hv with a5 | a7
   · rw [a5];exact ⟨(f,g,true),by simp [W₀],rfl⟩
   · rw [a7];exact ⟨(g,f,false),by simp [W₀],rfl⟩
 · simp [W₀,y2]
private def asL {α :Type*} (B:ℕ)(W:List (α × α × Bool)) (D:ℕ):List ℕ:=match W with
 | []=>[]
 | e :: rest =>
  if e.2.2 then min B D :: asL B rest (D-min B D)
  else 0 :: asL B rest D
private lemma asLl {α :Type*} (B:ℕ):∀ (W:List (α × α × Bool)) (D:ℕ),(asL B W D).length=W.length:=by
 intro W
 induction W with
 | nil=>intro D;simp [asL]
 | cons e rest ih =>
  intro D;unfold asL;by_cases a:e.2.2=true <;> simp [a,ih]
private lemma asLp {α :Type*} (B:ℕ):∀ (W:List (α × α × Bool)) (D:ℕ),D<=W.countP (·.2.2)*B->(asL B W D).length=W.length/\(asL B W D).sum=D/\(∀ i (f:i < W.length),(asL B W D)[i]'(asLl B W D ▸ f)<=B)/\(∀ i (f:i < W.length),W[i].2.2=false->(asL B W D)[i]'(asLl B W D ▸ f)=0):=by
 intro W
 induction W with
 | nil =>
  intro D k;simp [asL] at k ⊢;omega
 | cons e rest ih =>
  intro D k;by_cases b:e.2.2=true
  · have p:D-min B D<=rest.countP (·.2.2)*B:=by
     have g:(e :: rest).countP (·.2.2)=rest.countP (·.2.2)+1:=by
      simp [List.countP_cons,b]
     rw [g,Nat.add_one_mul] at k;by_cases l:B<=D
     · rw [min_eq_left l];omega
     · rw [min_eq_right (Nat.le_of_not_le l)];simp
    obtain ⟨m,h,d,a⟩:=ih (D-min B D) p;refine ⟨asLl B (e :: rest) D,?_,?_,?_⟩
    · simp only [asL,if_pos b,List.sum_cons,h];omega
    · intro i f
      rcases i with _ | i
      · simp only [asL,if_pos b,List.getElem_cons_zero];exact min_le_left B D
      · simp only [asL,if_pos b,List.getElem_cons_succ];exact d i (by simpa using f)
    · intro i f j
      rcases i with _ | i
      · simp [b] at j
      · simp only [asL,if_pos b,List.getElem_cons_succ];exact a i (by simpa using f) (by simpa using j)
  · have n:e.2.2=false:=Bool.eq_false_iff.mpr b
    have g:(e :: rest).countP (·.2.2)=rest.countP (·.2.2):=by
     simp [List.countP_cons,n]
    rw [g] at k;obtain ⟨m,h,d,a⟩:=ih D k;refine ⟨asLl B (e :: rest) D,?_,?_,?_⟩
    · simp only [asL,if_neg b,List.sum_cons,zero_add,h]
    · intro i f
      rcases i with _ | i
      · simp only [asL,if_neg b,List.getElem_cons_zero];omega
      · simp only [asL,if_neg b,List.getElem_cons_succ];exact d i (by simpa using f)
    · intro i f j
      rcases i with _ | i
      · simp only [asL,if_neg b,List.getElem_cons_zero]
      · simp only [asL,if_neg b,List.getElem_cons_succ];exact a i (by simpa using f) (by simpa using j)
private lemma srls:∀ (l:List ℕ)(f:ℕ->ℕ),(∀ i (d:i < l.length),f i=l[i])->∑ i ∈ range l.length,f i=l.sum:=by
 intro l
 induction l with
 | nil=>simp
 | cons a t ih =>
  intro f b;rw [List.length_cons,sum_range_succ',List.sum_cons,add_comm];congr 1
  · exact b 0 (Nat.zero_lt_succ _)
  · exact ih (fun i=>f (i+1)) (fun i d=>by
     rw [b (i+1) (Nat.succ_lt_succ d),List.getElem_cons_succ])
private lemma cgcl {N n:ℕ} (G:SG (Fin N)) (J:4<=n) (d:List (Fin N)) (l:d.length=n) (q:d.Nodup)(w:∀ i (L:i+1 < d.length),G.Adj d[i] d[i+1]) (u:∀ h:0 < d.length,G.Adj d[d.length-1] d[0]):(CG n).IsContained G:=by
 have C:0 < n:=by omega
 haveI:NeZero n:=⟨by omega⟩
 let f:Fin n->Fin N:=fun i=>d[i.val]'(l ▸ i.isLt)
 have B:Function.Injective f:=by
  intro i j D;exact Fin.ext (CA (@Fin.val d.length) (List.nodup_iff_injective_getElem.mp q (a₁:=⟨i.val,l ▸ i.isLt⟩) (a₂:=⟨j.val,l ▸ j.isLt⟩) D))
 let A:(CG n) →g G:=⟨f,by
  intro a b F;have r:(a-b).val=1\/(b-a).val=1:=cycleGraph_adj'.mp F
  have e:∀ x y:Fin n,(y-x).val=1->G.Adj (f x) (f y):=by
   intro x y p
   have k:y.val=(x.val+1) % n:=by
    rw [Fin.coe_sub] at p;by_cases K:x.val<=y.val
    · have I:y.val-x.val=1:=by
       rw [show (n-x.val+y.val) % n=(n+(y.val-x.val)) % n by congr 1;omega,Nat.add_mod_left,Nat.mod_eq_of_lt (by omega)] at p
       exact p
      have:x.val+1 < n:=by omega
      rw [Nat.mod_eq_of_lt this];omega
    · have I:n-x.val+y.val=1:=by
       rw [Nat.mod_eq_of_lt (by omega)] at p;exact p
      have m:x.val=n-1:=by omega
      have t:y.val=0:=by omega
      rw [m,show n-1+1=n by omega,Nat.mod_self,t]
   rcases eq_or_ne (x.val+1) n with v | H
   · have t:y.val=0:=by rw [k,v,Nat.mod_self]
     have s:x.val=d.length-1:=by omega
     simpa [f,s,t] using u (l ▸ C)
   · have z:x.val+1 < d.length:=by omega
     have E:y.val=x.val+1:=by rw [k,Nat.mod_eq_of_lt (by omega)]
     simpa [f,E] using w x.val z
  rcases r with h | h
  · exact (e b a h).symm
  · exact e a b h⟩
 exact ⟨⟨A,fun i j h=>B h⟩⟩
private lemma acy {N n L:ℕ} (G:SG (Fin N)) (h6:4<=n) (X:0 < L) (z:ℕ->Fin N) (d:ℕ->List (Fin N)) (M:∀ i < L,d i≠[]) (x:∀ i < L,∀ h:d i≠[],(d i).head h=z i) (m:∀ i < L,(d i).Nodup) (p:∀ i < L,(d i).IsChain G.Adj) (F:∀ i < L,∀ h:d i≠[],G.Adj ((d i).getLast h) (z ((i+1) % L))) (U:∀ S < L,∀ R < L,S≠R->Disjoint (d S).toFinset (d R).toFinset) (W: ∑ i ∈ range L,(d i).length=n):(CG n).IsContained G:=by
 have J:∀ k:ℕ,1<=k->k<=L ->
  let e:=(List.range k).flatMap d;e≠[] /\
  (∀ h:e≠[],e.head h=z 0) /\
  (∀ h:e≠[],∀ hk:d (k-1)≠[],e.getLast h=(d (k-1)).getLast hk) /\
  e.Nodup /\
  e.IsChain G.Adj /\
  e.toFinset=(range k).biUnion (fun i=>(d i).toFinset) /\
  e.length=∑ i ∈ range k,(d i).length:=by
  intro k h2 q
  induction k with
  | zero=>omega
  | succ k ih =>
   rcases eq_or_lt_of_le h2 with h3 | h8
   · have h4:k=0:=by omega
     subst h4;have Q:d 0≠[]:=M 0 X;refine ⟨by simpa using Q,?_,?_,?_,?_,?_,?_⟩
     · intro _;simpa using x 0 X Q
     · intro _ _;simp
     · simpa using m 0 X
     · simpa using p 0 X
     · simp
     · simp
   · have V:1<=k:=by omega
     obtain ⟨j,K,I,D,y,E,T⟩:=ih V (by omega)
     have g:d k≠[]:=M k q;have H:d (k-1)≠[]:=M (k-1) (by omega)
     have w:(List.range (k+1)).flatMap d=(List.range k).flatMap d ++ d k:=by
      rw [List.range_succ,List.flatMap_append,List.flatMap_singleton]
     rw [w];set e:=(List.range k).flatMap d;have f:e ++ d k≠[]:=List.append_ne_nil_of_right_ne_nil _ g
     have A:Disjoint e.toFinset (d k).toFinset:=by
      rw [E,disjoint_biUnion_left]
      intro i Y;exact U i (by rw [mem_range] at Y;omega) k q (by rw [mem_range] at Y;omega)
     refine ⟨f,?_,?_,?_,?_,?_,?_⟩
     · intro h';rw [List.head_append_of_ne_nil j,K j]
     · intro h' _;simpa using List.getLast_append_of_ne_nil h' g
     · rw [List.nodup_append]
       refine ⟨D,m k q,fun a ha b Z h9=>?_⟩
       subst h9;exact D1 A (List.mem_toFinset.mpr ha) (List.mem_toFinset.mpr Z)
     · refine ica y (p k q) ?_
       intro a ha b Z
       have h5:a=e.getLast j:=(by
        rw [List.getLast?_eq_some_getLast j] at ha;simpa using ha:e.getLast j=a).symm
       have h7:b=(d k).head g:=(by
        rw [List.head?_eq_some_head g] at Z;simpa using Z:(d k).head g=b).symm
       subst h5;subst h7;rw [I j H,x k q g]
       have hmod:(k-1+1) % L=k:=by
        rw [show k-1+1=k by omega,Nat.mod_eq_of_lt q]
       simpa [hmod] using F (k-1) (by omega) H
     · rw [List.toFinset_append,E,range_add_one,biUnion_insert,union_comm]
     · rw [List.length_append,T,sum_range_succ]
 obtain ⟨h1,B,v,r,u,_,P⟩:=J L X le_rfl;set l:=(List.range L).flatMap d;have C:d (L-1)≠[]:=M (L-1) (by omega)
 refine cgcl G h6 l (P.trans W) r ?_ ?_
 · intro i Y;exact List.isChain_iff_getElem.mp u i Y
 · intro h0
   have f:l≠[]:=List.ne_nil_of_length_pos h0;have s:l[l.length-1]=l.getLast f:=(List.getLast_eq_getElem f).symm;have t:l[0]=l.head f:=(List.head_eq_getElem f).symm;rw [s,t,v f C,B f];have hmod:(L-1+1) % L=0:=by rw [show L-1+1=L by omega,Nat.mod_self]
   simpa [hmod] using F (L-1) (by omega) C
private lemma tid {α :Type*} [DecidableEq α]:∀ (W:List (α × α × Bool)),((W.filter (·.2.2)).flatMap (fun e=>[e.1,e.2.1])).Nodup->∀ (d f:ℕ)(i:d < W.length) (j:f < W.length),d < f->W[d].2.2=true->W[f].2.2=true->Disjoint ({W[d].1,W[d].2.1}:FS α) ({W[f].1,W[f].2.1}:FS α):=by
 intro W
 induction W with
 | nil=>intro _ d _ i;simp at i
 | cons e rest ih =>
  intro a d f i j w s v
  have h:((rest.filter (·.2.2)).flatMap (fun x=>[x.1,x.2.1])).Nodup:=by
   by_cases u:e.2.2=true
   · simp only [List.filter_cons,u,↓reduceIte,List.flatMap_cons,List.cons_append,List.nil_append,List.nodup_cons] at a;exact a.2.2
   · have t:e.2.2=false:=Bool.eq_false_iff.mpr u;simp only [List.filter_cons,t,Bool.false_eq_true,↓reduceIte] at a;exact a
  rcases d with _ | q <;> rcases f with _ | g
  · omega
  · simp only [List.getElem_cons_zero] at s
    simp only [List.filter_cons,s,↓reduceIte,List.flatMap_cons,List.cons_append,List.nil_append,List.nodup_cons] at a;have b:g < rest.length:=by simpa using j
    have l:rest[g]'b∈rest.filter (·.2.2):=List.mem_filter.mpr ⟨List.getElem_mem b,by simpa using v⟩
    have p:(rest[g]'b).1∈(rest.filter (·.2.2)).flatMap (fun x=>[x.1,x.2.1]):=List.mem_flatMap.mpr ⟨rest[g]'b,l,by simp⟩
    have m:(rest[g]'b).2.1∈(rest.filter (·.2.2)).flatMap (fun x=>[x.1,x.2.1]):=List.mem_flatMap.mpr ⟨rest[g]'b,l,by simp⟩
    rw [Finset.disjoint_left]
    intro z n r;simp only [List.getElem_cons_zero,List.getElem_cons_succ,mem_insert,mem_singleton] at n r;rcases n with rfl | rfl <;> rcases r with k | k
    · exact a.1 (List.mem_cons_of_mem _ (k ▸ p))
    · exact a.1 (List.mem_cons_of_mem _ (k ▸ m))
    · exact a.2.1 (k ▸ p)
    · exact a.2.1 (k ▸ m)
  · omega
  · exact ih h q g (by simpa using i) (by simpa using j) (by omega) (by simpa using s) (by simpa using v)
private lemma brs {N:ℕ} (G:SG (Fin N)) [DecidableRel G.Adj] {d η : O} (y4:0 < η) (v4: η < d) {U V S CapU BodyU BodyV:FS (Fin N)} (x7:S⊆U)(v0:CapU⊆U) (q:BodyU⊆U)(C:BodyV⊆V) (s:Disjoint U V)(z0:Disjoint S CapU) (z1:Disjoint S BodyU)(y9:Disjoint CapU BodyU) (y7:G.IsUniform η U V)(hd:d<=(G.edgeDensity U V: O)) (M:0 < U.card) (v1:0 < V.card) (c:ℕ)(y6:(U.card: O) * η<=(c: O)) (y3:(V.card: O) * η<=(c: O)) (v5:(c: O)<=(d - η)*(BodyU.card: O)) (y2:(U.card: O) * η<=(CapU.card: O)) (p:(U.card: O) * η<=(BodyU.card: O)) (x3:(V.card: O) * η<=(BodyV.card: O)) {zu zv:Fin N} (x6:zu∈S)(y5:(d - η)*(BodyV.card: O) < ((G.neighborFinset zu ∩ BodyV).card: O)) (v6:(d - η)*(CapU.card: O) < ((G.neighborFinset zv ∩ CapU).card: O)) (K:(U.card: O) * η<=(d - η)*(CapU.card: O)) (x5:3*((max U.card V.card: O) * η + 1)<=(d - η)*(BodyV.card: O)) (ℓ :ℕ) (hℓ1:1<=ℓ) (hℓ_len: ℓ<=min (BodyV.card-c) BodyU.card-2*c):∃ k:List (Fin N),k≠[]/\k.length=2 * ℓ + 1/\(∀ h:k≠[],k.head h=zu)/\(∀ h:k≠[],G.Adj (k.getLast h) zv)/\k.Nodup/\k.IsChain G.Adj/\k.toFinset⊆insert zu (BodyU ∪ BodyV ∪ CapU):=by
 set S_end:=G.neighborFinset zv ∩ CapU;have L:S_end⊆U:=inter_subset_right.trans v0;have n:(U.card: O) * η<=(S_end.card: O):=K.trans v6.le;have r:G.IsUniform η V U:=y7.symm;have Z:d<=(G.edgeDensity V U: O):=by rwa [edgeDensity_comm]
 set B_bad:=V.filter (fun y=>((G.neighborFinset y ∩ S_end).card: O)<=(d - η)*(S_end.card: O))
 have x1:(B_bad.card: O) < (V.card: O) * η:=cbl G y4 r Z v1 M L n;set Body'V:=BodyV \ B_bad;have g:Body'V⊆V:=sdiff_subset.trans C
 have v9:BodyV.card-c<=Body'V.card:=by
  have z4:B_bad.card<=c:=by
   have h1:(B_bad.card: O) < (c: O):=x1.trans_le y3;exact_mod_cast h1.le
  have h2:BodyV.card<=Body'V.card+B_bad.card:=by
   calc BodyV.card<=(Body'V ∪ B_bad).card:=card_le_card (fun x hx=>by
    by_cases h:x∈B_bad
    · exact mem_union_right _ h
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hx,h⟩))
    _<=Body'V.card+B_bad.card:=card_union_le _ _
  omega
 set P:=G.neighborFinset zu ∩ Body'V;have x2:P⊆V:=inter_subset_right.trans g
 have v3:((∅ :FS (Fin N)).card: O)+2 * (V.card: O) * η<=(P.card: O):=by
  have h1:(G.neighborFinset zu ∩ BodyV).card<=P.card+B_bad.card:=by
   calc (G.neighborFinset zu ∩ BodyV).card
    <= (P ∪ B_bad).card:=card_le_card (fun x hx=>by
         rw [mem_inter] at hx;by_cases h:x∈B_bad
         · exact mem_union_right _ h
         · exact mem_union_left _ (mem_inter.mpr ⟨hx.1,mem_sdiff.mpr ⟨hx.2,h⟩⟩))
    _<=P.card+B_bad.card:=card_union_le _ _
  have z8:((G.neighborFinset zu ∩ BodyV).card: O)<=(P.card: O)+(B_bad.card: O):=by
   exact_mod_cast h1
  have z2:(V.card: O)<=(max U.card V.card: O):=by exact_mod_cast le_max_right U.card V.card
  simp only [card_empty,Nat.cast_zero,zero_add];nlinarith
 obtain ⟨u,h0,_,A,_⟩:=eg2 G y4 x2 v1 r Z M q p r Z M q p v3;have t:u∈Body'V:=(mem_inter.mp h0).2;have x0:G.Adj zu u:=(G.mem_neighborFinset zu u).mp (mem_inter.mp h0).1
 have J:c<=(G.neighborFinset u ∩ BodyU).card:=by
  exact_mod_cast (v5.trans_lt A).le
 have h3:0 < c:=by
  have h1:(0: O) < (U.card: O) * η:=by positivity
  exact_mod_cast h1.trans_le y6
 have h9:Disjoint Body'V BodyU:=s.symm.mono g q;have h4:∀ X⊆Body'V,∀ Y⊆BodyU,c<=X.card->c<=Y.card->∃ x ∈ X,∃ y ∈ Y,G.Adj x y:=nep G v4 r Z g q y3 y6;obtain ⟨Q,x4,T,v2,v7,y0,y8,x9⟩:=dlp G Body'V BodyU h9 h3 h3 h4 u t J
 have h5:2 * ℓ - 1<=Q.length:=by
  have h1:min (BodyV.card-c) BodyU.card<=min Body'V.card BodyU.card:=by omega
  omega
 set Q':=Q.take (2 * ℓ - 1);have W:Q'.length=2 * ℓ - 1:=List.length_take_of_le h5;have l:Q'≠[]:=List.ne_nil_of_length_pos (by omega)
 have v8:Q'.head l=u:=by
  rw [List.head_eq_getElem l];simp only [Q',List.getElem_take];rw [<- List.head_eq_getElem x4,<-Option.some.injEq];rw [List.head?_eq_some_head x4] at T;exact T
 have h8:Q'.Nodup:=v2.take
 have h6:Q'.IsChain G.Adj:=by
  have h1:Q'.IsChain (bpA G Body'V BodyU):=v7.take (2 * ℓ - 1)
  exact h1.imp (fun {_ _} h=>h.2)
 have z:Q'.toFinset⊆BodyU ∪ BodyV:=by
  intro x hx;have x8:x∈Q:=List.mem_of_mem_take (List.mem_toFinset.mp hx);rcases mem_union.mp (y0 (List.mem_toFinset.mpr x8)) with hV | hU
  · exact mem_union_right _ (sdiff_subset hV)
  · exact mem_union_left _ hU
 set i:=Q'.getLast l
 have F:i=Q[2 * ℓ - 2]'(by omega):=by
  change Q'.getLast l=Q[2 * ℓ - 2]'(by omega)
  rw [List.getLast_eq_getElem l];simp only [Q',W];exact List.getElem_take
 have j:i∈Body'V:=by
  rw [F];exact (x9 (2 * ℓ - 2) (by omega)).1 ⟨ℓ - 1,by omega⟩
 have w:i ∉ B_bad:=(mem_sdiff.mp j).2;have R:i∈V:=g j
 have B:(d - η)*(S_end.card: O) < ((G.neighborFinset i ∩ S_end).card: O):=by
  by_contra! z7;exact w (mem_filter.mpr ⟨R,z7⟩)
 have D:0 < (G.neighborFinset i ∩ S_end).card:=by
  have y1:(0: O) < (S_end.card: O):=by
   have:(0: O) < (U.card: O) * η:=by positivity
   exact this.trans_le n
  have h1:(0: O) < (d - η)*(S_end.card: O):=mul_pos (sub_pos.mpr v4) y1;exact_mod_cast h1.trans B
 obtain ⟨e,m⟩:=card_pos.mp D;rw [mem_inter,mem_neighborFinset] at m;have f:e∈CapU:=(mem_inter.mp m.2).2;have I:G.Adj e zv:=((G.mem_neighborFinset zv e).mp (mem_inter.mp m.2).1).symm;set k:=zu :: (Q' ++ [e]);have E:k≠[]:=by simp [k]
 have v:zu ∉ BodyU ∪ BodyV:=by
  intro h;rcases mem_union.mp h with hU | hV
  · exact D1 z1 x6 hU
  · exact D1 s (x7 x6) (C hV)
 have H:e ∉ BodyU ∪ BodyV:=by
  intro h;rcases mem_union.mp h with hU | hV
  · exact D1 y9 f hU
  · exact D1 s (v0 f) (C hV)
 have h7:zu≠e:=fun h=>D1 z0 x6 (h ▸ f)
 refine ⟨k,E,?_,?_,?_,?_,?_,?_⟩
 · simp [k,W];omega
 · intro _;simp [k]
 · intro _
   have h1:k.getLast E=(Q' ++ [e]).getLast (by simp):=List.getLast_cons (by simp)
   rw [h1,List.getLast_append_singleton];exact I
 · rw [show k=zu :: (Q' ++ [e]) from rfl,List.nodup_cons]
   refine ⟨?_,?_⟩
   · simp only [List.mem_append,List.mem_singleton,not_or];exact ⟨fun h=>v (z (List.mem_toFinset.mpr h)),h7⟩
   · rw [List.nodup_append]
     refine ⟨h8,List.nodup_singleton _,fun a ha b hb z3=>?_⟩
     rw [List.mem_singleton] at hb;subst hb;subst z3;exact H (z (List.mem_toFinset.mpr ha))
 · refine List.IsChain.cons_of_ne_nil (by simp) ?_ ?_
   · refine ica h6 (List.isChain_singleton _) ?_
     intro a ha b hb
     have z5:a=i:=(by
      rw [List.getLast?_eq_some_getLast l] at ha;simpa using ha:i=a).symm
     have z6:b=e:=(by simpa using hb:e=b).symm
     subst z5;subst z6;exact m.1
   · rw [List.head_append_of_ne_nil l,v8];exact x0
 · intro x hx
   simp only [k,List.toFinset_cons,List.toFinset_append,List.toFinset_nil,mem_insert,mem_union,notMem_empty,or_false] at hx;rcases hx with rfl | x8 | rfl
   · exact mem_insert_self _ _
   · exact mem_insert_of_mem (mem_union_left _ (by
      have:=z x8;rcases mem_union.mp this with h | h
      · exact mem_union_left _ h
      · exact mem_union_right _ h))
   · exact mem_insert_of_mem (mem_union_right _ f)
set_option maxHeartbeats 800000 in
private lemma etv {N t:ℕ} (G:SG (Fin N)) [DecidableRel G.Adj] {d η : O} (y5:0 < η) (parts:Fin t->FS (Fin N)) (R:SG (Fin t)) (b:∀ i:Fin t,0 < (parts i).card) (hR:∀ u v:Fin t,R.Adj u v->G.IsUniform η (parts u) (parts v)/\d<=(G.edgeDensity (parts u) (parts v): O)) (g v8 h6:Fin t->FS (Fin N)) (f:∀ i,g i⊆parts i)(M:∀ i,v8 i⊆parts i) (h4:∀ i,h6 i⊆parts i)(Y:∀ i j,(parts j).card * η<=(g i).card) (W:∀ i j,(parts j).card * η<=(v8 i).card) (h7:∀ i j,(parts j).card * η<=(h6 i).card) (L:ℕ)(w w':ℕ->Fin t) (J:∀ i < L,R.Adj (w i) (w' i)) (v0:∀ i,i+1 < L->w' i=w (i+1)) (y3:w' (L-1)=w 0) (len:ℕ->ℕ) (a9:len (L-1)=0) (b7:2<=L) (x4:L=2->0 < len 0) (V:∀ i,(L: O)+2 * ((parts i).card: O) * η<=(g i).card) (s:∀ i j,(parts j).card * η<=(d - η)*(g i).card/\(L: O)+2 * ((parts j).card: O) * η<=(d - η)*(g i).card) (h9:∀ i j,(L: O)+2 * ((parts j).card: O) * η<=(d - η)*((d - η)*(g i).card)):∃ z:ℕ->Fin N,(∀ i < L,z i∈g (w i))/\(∀ H < L,∀ F < L,H≠F->z H≠z F)/\(∀ i (hi:i+1 < L),if 0 < len i then (d - η)*((h6 (w' i)).card: O) < ((G.neighborFinset (z i) ∩ h6 (w' i)).card: O) else if i+1 < L-1 then (d - η)*((g (w' i)).card: O) < ((G.neighborFinset (z i) ∩ g (w' i)).card: O) else (d - η)*((G.neighborFinset (z 0) ∩ g (w (L-1))).card: O) < ((G.neighborFinset (z i) ∩ (G.neighborFinset (z 0) ∩ g (w (L-1)))).card: O))/\(∀ i (hi:0 < i) (c5:i < L),if 0 < len (i-1) then (d - η)*((v8 (w (i-1))).card: O) < ((G.neighborFinset (z i) ∩ v8 (w (i-1))).card: O) else G.Adj (z (i-1)) (z i))/\G.Adj (z (L-1)) (z 0):=by
 classical
 let C:Fin N->FS (Fin N):=fun z0=>G.neighborFinset z0 ∩ g (w (L-1))
 let a:Fin N->(i:ℕ)->i+1 < L->FS (Fin N):=fun z0 i _ =>
  if 0 < len i then h6 (w' i)
  else if i+1 < L-1 then g (w' i)
  else C z0
 have v5:∀ z0 i (hi:i+1 < L),a z0 i hi⊆parts (w' i):=by
  intro z0 i hi;simp only [a];split_ifs with h1 h2
  · exact h4 _
  · exact f _
  · have x1:w (L-1)=w' i:=by
     have y8:i+1=L-1:=by omega
     rw [<- y8,<-v0 i hi]
    rw [<- x1];exact inter_subset_right.trans (f _)
 have a0:∀ k:ℕ,1<=k->k<=L->∃ z:ℕ->Fin N,(∀ i < k,z i∈g (w i))/\(∀ H < k,∀ F < k,H≠F->z H≠z F)/\(d - η)*((g (w (L-1))).card: O) < ((G.neighborFinset (z 0) ∩ g (w (L-1))).card: O)/\(∀ i (hi:i < k) (x0:i+1 < L),(d - η)*((a (z 0) i x0).card: O) < ((G.neighborFinset (z i) ∩ a (z 0) i x0).card: O))/\(∀ i (hi:0 < i) (v6:i < k),if 0 < len (i-1) then (d - η)*((v8 (w (i-1))).card: O) < ((G.neighborFinset (z i) ∩ v8 (w (i-1))).card: O)
  else G.Adj (z (i-1)) (z i)) /\
  (k=L->G.Adj (z (L-1)) (z 0)):=by
  intro k c0 a3
  induction k with
  | zero=>omega
  | succ k ih =>
   rcases eq_or_lt_of_le c0 with c2 | b2
   · have b4:k=0:=by omega
     subst b4;have c4:0+1 < L:=by omega
     let T1:=if 0 < len 0 then h6 (w' 0) else g (w' 0)
     have y1:T1⊆parts (w' 0):=by
      dsimp [T1];split_ifs <;> [exact h4 _;exact f _]
     have y4:(parts (w' 0)).card * η<=(T1.card: O):=by
      dsimp [T1];split_ifs <;> [exact h7 _ _;exact Y _ _]
     have z1:=hR (w 0) (w' 0) (J 0 (by omega))
     have a6:R.Adj (w 0) (w (L-1)):=by
      have:=J (L-1) (by omega)
      rw [y3] at this;exact this.symm
     have y9:=hR (w 0) (w (L-1)) a6
     have b5:((∅ :FS (Fin N)).card: O)+2 * ((parts (w 0)).card: O) * η<=(g (w 0)).card:=by
      simp only [card_empty,Nat.cast_zero,zero_add];exact le_trans (by linarith) (V (w 0))
     obtain ⟨z0,y0,_,y6,B⟩:=eg2 G y5 (f (w 0)) (b _) z1.1 z1.2 (b _) y1 y4 y9.1 y9.2 (b _) (f _) (Y _ _) b5;refine ⟨fun _=>z0,?_,?_,B,?_,?_,?_⟩
     · intro i hi;rw [show i=0 by omega];exact y0
     · intro H z7 F z6 a2;omega
     · intro i hi x0
       have b6:i=0:=by omega
       subst b6
       have S:a z0 0 x0=T1:=by
        dsimp [a,T1];by_cases h0:0 < len 0
        · simp [h0]
        · have b9:L≠2:=fun h2=>h0 (x4 h2)
          have c1:0+1 < L-1:=by omega
          simp [h0,c1]
       simpa [S] using y6
     · intro i hi v6;omega
     · intro y8;omega
   · obtain ⟨z,v2,v4,B,K,X,_⟩:=ih (by omega) (by omega)
     set e:=(range k).image z;have p:e.card<=L:=(card_image_le.trans (card_range k).le).trans (by omega)
     have x5:(parts (w (L-1))).card * η<=((C (z 0)).card: O):=(s (w (L-1)) (w (L-1))).1.trans B.le
     have v9:∀ i (hi:i+1 < L),(parts (w' i)).card * η<=((a (z 0) i hi).card: O):=by
      intro i hi;dsimp [a];split_ifs with h1 h2
      · exact h7 _ _
      · exact Y _ _
      · have x1:w (L-1)=w' i:=by
         have y8:i+1=L-1:=by omega
         rw [<- y8,<-v0 i hi]
        rw [<- x1];exact x5
     have z3:w' (k-1)=w k:=by
      simpa [show k-1+1=k by omega] using v0 (k-1) (by omega)
     have x6:R.Adj (w k) (w (k-1)):=by
      have:=J (k-1) (by omega)
      rw [z3] at this;exact this.symm
     have l:=hR (w k) (w (k-1)) x6;have h5:C (z 0)⊆parts (w (L-1)):=inter_subset_right.trans (f _);have z9:∃ zk:Fin N,zk∈g (w k)/\zk ∉ e/\(if 0 < len (k-1) then (d - η)*((v8 (w (k-1))).card: O) < ((G.neighborFinset zk ∩ v8 (w (k-1))).card: O)
      else G.Adj (z (k-1)) zk) /\
      (∀ D:k+1 < L,(d - η)*((a (z 0) k D).card: O) < ((G.neighborFinset zk ∩ a (z 0) k D).card: O)) /\
      (k=L-1->G.Adj zk (z 0)):=by
      by_cases m:0 < len (k-1)
      · by_cases D:k+1 < L
        · have q:=hR (w k) (w' k) (J k a3)
          have hP:(e.card: O)+2 * ((parts (w k)).card: O) * η<=(g (w k)).card:=by
           have x8:(e.card: O)<=(L: O):=Nat.cast_le.mpr p;linarith only [x8,V (w k)]
          obtain ⟨zk,U,y,Z,A⟩:=eg2 G y5 (f (w k)) (b _) l.1 l.2 (b _) (M _) (W _ _) q.1 q.2 (b _) (v5 (z 0) k D) (v9 k D) hP;refine ⟨zk,U,y,by simp [m,Z],fun _=>A,fun h=>by omega⟩
        · have I:k=L-1:=by omega
          have v3:C (z 0)⊆parts (w k):=by rw [I];exact h5
          have hP:(e.card: O)+2 * ((parts (w k)).card: O) * η<=((C (z 0)).card: O):=by
           have x8:(e.card: O)<=(L: O):=Nat.cast_le.mpr p;have y7:=(s (w (L-1)) (w k)).2;rw [I] at y7 ⊢;linarith only [x8,y7,B]
          obtain ⟨zk,U,y,Z,_⟩:=eg2 G y5 v3 (b _) l.1 l.2 (b _) (M _) (W _ _) l.1 l.2 (b _) (M _) (W _ _) hP;have r:zk∈g (w k):=by rw [I];exact (mem_inter.mp U).2
          have v1:G.Adj zk (z 0):=((G.mem_neighborFinset (z 0) zk).mp (mem_inter.mp U).1).symm;exact ⟨zk,r,y,by simp [m,Z],fun h=>(D h).elim,fun _=>v1⟩
      · have E:k-1+1 < L:=by omega
        have n:=K (k-1) (by omega) E
        by_cases D:k+1 < L
        · have Q:k-1+1 < L-1:=by omega
          have S:a (z 0) (k-1) E=g (w k):=by
           simp only [a,m,↓reduceIte,Q,z3]
          rw [S] at n;set P:=G.neighborFinset (z (k-1)) ∩ g (w k);have v3:P⊆parts (w k):=inter_subset_right.trans (f _)
          have hP:(e.card: O)+2 * ((parts (w k)).card: O) * η<=(P.card: O):=by
           have x8:(e.card: O)<=(L: O):=Nat.cast_le.mpr p;have y7:=(s (w k) (w k)).2;linarith only [x8,y7,n]
          have q:=hR (w k) (w' k) (J k a3);obtain ⟨zk,U,y,A,_⟩:=eg2 G y5 v3 (b _) q.1 q.2 (b _) (v5 (z 0) k D) (v9 k D) q.1 q.2 (b _) (v5 (z 0) k D) (v9 k D) hP;have r:zk∈g (w k):=(mem_inter.mp U).2;have T:G.Adj (z (k-1)) zk:=(G.mem_neighborFinset (z (k-1)) zk).mp (mem_inter.mp U).1;exact ⟨zk,r,y,by simp [m,T],fun _=>A,fun h=>by omega⟩
        · have I:k=L-1:=by omega
          have Q:¬ (k-1+1 < L-1):=by omega
          have S:a (z 0) (k-1) E=C (z 0):=by
           simp only [a,m,↓reduceIte,Q]
          rw [S] at n;set P:=G.neighborFinset (z (k-1)) ∩ C (z 0)
          have b0:e.card < P.card:=by
           have h1:(e.card: O)<=(L: O):=Nat.cast_le.mpr p
           have h2:(L: O) < (d - η)*((d - η)*((g (w (L-1))).card: O)):=by
            have b8:=h9 (w (L-1)) (w k)
            have hp:(0: O) < 2*((parts (w k)).card: O) * η:=by
             have:=b (w k);positivity
            linarith only [b8,hp]
           have h3:(d - η)*((d - η)*((g (w (L-1))).card: O)) < (d - η)*((C (z 0)).card: O):=by
            have b1:0 < d - η:=by
             have a4:=(s (w (L-1)) (w (L-1))).1
             have z4:(0: O) < (parts (w (L-1))).card * η:=by
              have:=b (w (L-1));positivity
             have a1:(0: O)<=(g (w (L-1))).card:=Nat.cast_nonneg _;nlinarith only [a4,z4,a1]
            exact mul_lt_mul_of_pos_left B b1
           exact_mod_cast (h1.trans_lt (h2.trans h3)).trans n
          have a8:(P \ e).Nonempty:=card_pos.mp (by
           have:P.card<=(P \ e).card+e.card:=by
            calc P.card<=((P \ e) ∪ e).card:=card_le_card (fun x hx=>by
             by_cases h:x∈e
             · exact mem_union_right _ h
             · exact mem_union_left _ (mem_sdiff.mpr ⟨hx,h⟩))
             _<=(P \ e).card+e.card:=card_union_le _ _
           omega)
          obtain ⟨zk,z8⟩:=a8;rw [mem_sdiff] at z8;have v7:=mem_inter.mp z8.1;have h8:=mem_inter.mp v7.2;have r:zk∈g (w k):=by rw [I];exact h8.2
          have T:G.Adj (z (k-1)) zk:=(G.mem_neighborFinset (z (k-1)) zk).mp v7.1;have v1:G.Adj zk (z 0):=((G.mem_neighborFinset (z 0) zk).mp h8.1).symm;exact ⟨zk,r,z8.2,by simp [m,T],fun h=>(D h).elim,fun _=>v1⟩
     obtain ⟨zk,r,y,x3,A,x2⟩:=z9;let z':ℕ->Fin N:=fun i=>if i=k then zk else z i
     have x9:z' 0=z 0:=if_neg (by omega:(0:ℕ)≠k)
     refine ⟨z',?_,?_,?_,?_,?_,?_⟩
     · intro i hi
       by_cases v6:i=k
       · subst v6;dsimp only [z'];rw [if_pos rfl];exact r
       · dsimp only [z'];rw [if_neg v6];exact v2 i (by omega)
     · intro H z7 F z6 a2
       by_cases h1:H=k <;> by_cases h2:F=k
       · exact (a2 (h1.trans h2.symm)).elim
       · subst h1;dsimp only [z'];rw [if_pos rfl,if_neg h2]
         intro x1;exact y (mem_image.mpr ⟨F,mem_range.mpr (by omega),x1.symm⟩)
       · subst h2;dsimp only [z'];rw [if_neg h1,if_pos rfl]
         intro x1;exact y (mem_image.mpr ⟨H,mem_range.mpr (by omega),x1⟩)
       · dsimp only [z'];rw [if_neg h1,if_neg h2];exact v4 H (by omega) F (by omega) a2
     · rw [x9];exact B
     · intro i hi x0
       rw [x9];by_cases v6:i=k
       · subst v6
         have x7:z' i=zk:=by dsimp [z'];exact if_pos rfl
         rw [x7];exact A x0
       · have z5:z' i=z i:=by dsimp [z'];exact if_neg v6
         rw [z5];exact K i (by omega) x0
     · intro i hi v6
       by_cases z2:i=k
       · subst z2
         have x7:z' i=zk:=by dsimp [z'];exact if_pos rfl
         have a7:z' (i-1)=z (i-1):=by dsimp [z'];exact if_neg (by omega:i-1≠i)
         rw [x7,a7];exact x3
       · have a5:i-1≠k:=by omega
         have z5:z' i=z i:=by dsimp [z'];exact if_neg z2
         have b3:z' (i-1)=z (i-1):=by dsimp [z'];exact if_neg a5
         rw [z5,b3];exact X i hi (by omega)
     · intro c3
       have I:k=L-1:=by omega
       subst I;rw [x9];simp only [z',if_pos rfl];exact x2 rfl
 obtain ⟨z,v2,v4,B,K,X,y2⟩:=a0 L (by omega) le_rfl
 refine ⟨z,v2,v4,?_,X,y2 rfl⟩
 intro i hi;have h:=K i (by omega) hi
 dsimp [a,C] at h;split_ifs at h ⊢ <;> exact h
end P2
set_option maxHeartbeats 800000 in
lemma h2p:E1.H2:=by
 intro d δ hd c2 x1;let d': O:=min d 1;have a1:0 < d':=lt_min hd zero_lt_one;have e6:d'<=1:=min_le_right d 1;have k9:d'<=d:=min_le_left d 1;let η : O:=min (d'/4) (min (δ / 16) (d'^2 * δ / 256));have V:0 < η:=lt_min (by positivity) (lt_min (by positivity) (by positivity))
 have u4: η<=d'/4:=min_le_left _ _;have z0: η<=δ / 16:=(min_le_right _ _).trans (min_le_left _ _);have v2: η<=d'^2 * δ / 256:=(min_le_right _ _).trans (min_le_right _ _);refine ⟨η,V,fun t=>?_⟩
 let C:ℕ:=Nat.ceil (256*(t: O)/(d'^2 * δ)+(t: O)/(1 - δ)+32 / δ + 32/(d' * δ))+32;refine ⟨C,fun N n m k G _ parts R M r0 k6 w7 hm r5 v5 I hR hM u6 e9=>?_⟩
 classical
 have q7:32<=m:=le_trans (by omega:32<=C) hm
 have z2:0 < m:=by omega
 have A:(0: O) < (m: O):=by exact_mod_cast z2
 have T:∀ i:Fin t,0 < (parts i).card:=fun i=>lt_of_lt_of_le z2 (I i).1
 have p2:2*k<=M.verts.toFinset.card:=by
  rwa [<- Set.ncard_eq_toFinset_card']
 obtain ⟨y6,h9,K,_,x7⟩ :=
  P2.emp M hM k M.verts.toFinset (fun x hx=>Set.mem_toFinset.mp hx) (fun x hx y k1=>Set.mem_toFinset.mpr (M.edge_vert k1.symm)) p2
 have y9:∃ u v:Fin t,R.Adj u v:=by
  have x5:y6≠[]:=by intro h;simp [h] at h9;omega
  obtain ⟨⟨u,v⟩,m0,h⟩:=List.exists_cons_of_ne_nil x5;exact ⟨u,v,M.adj_sub (K (u,v) (by simp [h]))⟩
 have m5:d<=1:=by
  obtain ⟨u,v,r4⟩:=y9;have F:=(hR u v r4).2
  have h2:(G.edgeDensity (parts u) (parts v): O)<=1:=by
   exact_mod_cast edgeDensity_le_one G (parts u) (parts v)
  linarith
 have r8: η < d:=by linarith
 have s:3/4*d'<=d - η:=by linarith
 have q1: η<=d'/256:=by
  have F:d'^2 * δ / 256<=d'*1/256:=by nlinarith
  linarith
 have p3: η<=d' * δ / 256:=by
  have F:d'^2 * δ / 256<=d' * δ / 256:=by nlinarith
  linarith
 have s2:0 < 1 - δ:=sub_pos.mpr x1
 have d2:(t: O)/(1 - δ)<=(m: O):=by
  have F:(256*(t: O)/(d'^2 * δ)+(t: O)/(1 - δ)+32 / δ + 32/(d' * δ))<=(C: O):=by
   calc _<=(Nat.ceil (256*(t: O)/(d'^2 * δ)+(t: O)/(1 - δ)+32 / δ + 32/(d' * δ)): O) :=
    Nat.le_ceil _
    _<=(C: O):=by simp only [C,Nat.cast_add,Nat.cast_ofNat];linarith
  have h2:(0: O)<=256*(t: O)/(d'^2 * δ):=by positivity
  have h3:(0: O)<=32 / δ:=by positivity
  have h4:(0: O)<=32/(d' * δ):=by positivity
  have h5:(C: O)<=(m: O):=Nat.cast_le.mpr hm;linarith
 have x4:256*(t: O)/(d'^2 * δ)<=(m: O):=by
  have F:(256*(t: O)/(d'^2 * δ)+(t: O)/(1 - δ)+32 / δ + 32/(d' * δ))<=(C: O):=by
   calc _<=(Nat.ceil (256*(t: O)/(d'^2 * δ)+(t: O)/(1 - δ)+32 / δ + 32/(d' * δ)): O) :=
    Nat.le_ceil _
    _<=(C: O):=by simp only [C,Nat.cast_add,Nat.cast_ofNat];linarith
  have h2:(0: O)<=(t: O)/(1 - δ):=by positivity
  have h3:(0: O)<=32 / δ:=by positivity
  have h4:(0: O)<=32/(d' * δ):=by positivity
  have h5:(C: O)<=(m: O):=Nat.cast_le.mpr hm;linarith
 have r9:32 / δ<=(m: O):=by
  have F:(256*(t: O)/(d'^2 * δ)+(t: O)/(1 - δ)+32 / δ + 32/(d' * δ))<=(C: O):=by
   calc _<=(Nat.ceil (256*(t: O)/(d'^2 * δ)+(t: O)/(1 - δ)+32 / δ + 32/(d' * δ)): O) :=
    Nat.le_ceil _
    _<=(C: O):=by simp only [C,Nat.cast_add,Nat.cast_ofNat];linarith
  have h2:(0: O)<=256*(t: O)/(d'^2 * δ):=by positivity
  have h3:(0: O)<=(t: O)/(1 - δ):=by positivity
  have h4:(0: O)<=32/(d' * δ):=by positivity
  have h5:(C: O)<=(m: O):=Nat.cast_le.mpr hm;linarith
 have q4:32/(d' * δ)<=(m: O):=by
  have F:(256*(t: O)/(d'^2 * δ)+(t: O)/(1 - δ)+32 / δ + 32/(d' * δ))<=(C: O):=by
   calc _<=(Nat.ceil (256*(t: O)/(d'^2 * δ)+(t: O)/(1 - δ)+32 / δ + 32/(d' * δ)): O) :=
    Nat.le_ceil _
    _<=(C: O):=by simp only [C,Nat.cast_add,Nat.cast_ofNat];linarith
  have h2:(0: O)<=256*(t: O)/(d'^2 * δ):=by positivity
  have h3:(0: O)<=(t: O)/(1 - δ):=by positivity
  have h4:(0: O)<=32 / δ:=by positivity
  have h5:(C: O)<=(m: O):=Nat.cast_le.mpr hm;linarith
 have b6:∃ r:ℕ,1<=r/\r<=k/\(n: O)<=(1 - δ)*(2*(r: O)*(m: O))/\(2<=r->(1 - δ)*(2*((r-1:ℕ): O)*(m: O)) < (n: O)):=by
  let S:FS ℕ:=(Icc (1:ℕ) k).filter (fun j=>(n: O)<=(1 - δ)*(2*(j: O)*(m: O)))
  have k2:k∈S:=mem_filter.mpr ⟨mem_Icc.mpr ⟨w7,le_rfl⟩,r5⟩;have q8:S.Nonempty:=⟨k,k2⟩;let r:=S.min' q8;have w5:r∈S:=min'_mem S q8;have c3:=mem_filter.mp w5;have c5:=mem_Icc.mp c3.1;refine ⟨r,c5.1,c5.2,c3.2,fun t1=>?_⟩
  by_contra! x6;have e7:r-1∈S:=mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,x6⟩
  have:=min'_le S (r-1) e7;omega
 obtain ⟨r,w2,w4,m4,n5⟩:=b6;set P:=y6.take r;have z5:P.length=r:=by rw [List.length_take,h9];exact min_eq_left w4
 have a5:P≠[]:=List.ne_nil_of_length_pos (by omega)
 have z3:∀ p ∈ P,R.Adj p.1 p.2:=fun p hp=>M.adj_sub (K p (List.mem_of_mem_take hp))
 have v8:(P.flatMap (fun p=>[p.1,p.2])).Nodup:=by
  have F:P.flatMap (fun p=>[p.1,p.2]) <+:y6.flatMap (fun p=>[p.1,p.2]):=(List.take_prefix r y6).flatMap (fun p=>[p.1,p.2])
  exact x7.sublist F.sublist
 have x2:∀ p ∈ P,∀ q ∈ P,R.Reachable p.1 q.1:=fun p hp q hq =>
  e9 p.1 (M.edge_vert (K p (List.mem_of_mem_take hp))) q.1 (M.edge_vert (K q (List.mem_of_mem_take hq)))
 obtain ⟨W,v7,s3,e1,p7,p0,q3,k4,b9,d7,c1,n3,z7⟩:=P2.bcw P a5 z3 v8 x2;rw [z5] at d7 c1 n3;set L:=W.length
 have u3:L<=n:=by
  rcases eq_or_lt_of_le w2 with rfl | t1
  · have:L=2:=c1 rfl;omega
  · have m2:=n5 t1
    have t6:2*(1 - δ)*(m: O) < (n: O):=by
     have F:(1: O)<=((r-1:ℕ): O):=by exact_mod_cast (by omega:1<=r-1)
     nlinarith
    have w9:(t: O)<=(1 - δ)*(m: O):=by linarith [(div_le_iff₀ s2).mp d2]
    have m7:(L: O)<=2*(t: O):=by exact_mod_cast b9
    have d1:(L: O) < (n: O):=by linarith
    exact_mod_cast d1.le
 obtain ⟨U,u0⟩:=r0;obtain ⟨z1,s8⟩:=q3;set D:=U-z1;have k7:n=L+2 * D:=by omega
 set B:=Nat.floor ((1 - δ)*(m: O))
 have q9:D<=r*B:=by
  have w1:(1 - δ)*(m: O) < (B: O)+1:=Nat.lt_floor_add_one _
  have F:(D: O)+(r: O)<=(U: O):=by
   have:z1 ≥ r:=by omega
   exact_mod_cast (by omega:D+r<=U)
  have h2:(U: O)<=(1 - δ)*(r: O)*(m: O):=by
   have m8:(n: O)=2*(U: O):=by exact_mod_cast (by omega:n=2*U)
   linarith
  have h3:(1 - δ)*(r: O)*(m: O) < (r: O)*((B: O)+1):=by
   have w8:(0: O) < (r: O):=by exact_mod_cast (by omega:0 < r)
   nlinarith
  have h4:(D: O) < (r: O)*(B: O):=by linarith
  have u9:D < r*B:=by exact_mod_cast h4
  exact u9.le
 set z6:=P2.asL B W D;obtain ⟨v6,x3,b2,h8⟩:=P2.asLp B W D (n3 ▸ q9);have h6:z6.length=L:=v6;let len:ℕ->ℕ:=fun i=>if h:i < L then z6[i]'(v6 ▸ h) else 0
 have b8:len (L-1)=0:=by
  simp only [len,dif_pos (by omega:L-1 < L)]
  refine h8 (L-1) (by omega) ?_
  have F:=p0 v7;rwa [List.getLast_eq_getElem v7] at F
 have d0:L=2->0 < len 0:=by
  intro t7;have u1:len 1=0:=by simpa [t7] using b8
  have s7:z1=1:=by omega
  have u5:0 < D:=by omega
  have k8:len 0+len 1=D:=by
   have y3:=P2.srls z6 len (fun i Q=>by
    have s1:i < L:=h6 ▸ Q;simp [len,s1])
   rw [h6,t7,x3] at y3;simpa [sum_range_succ] using y3
  omega
 set q:=Nat.ceil (δ / 8*(m: O));have v9: δ / 8*(m: O)<=(q: O):=Nat.le_ceil _;have b5:(q: O) < δ / 8*(m: O)+1:=Nat.ceil_lt_add_one (by positivity)
 have v3:2*q<=m:=by
  have F:(2*q: O) < δ / 4*(m: O)+2:=by linarith only [b5]
  have h2: δ / 4*(m: O)+2<=1/4*(m: O)+2:=by nlinarith only [x1,A]
  have h3:(1/4*(m: O)+2: O)<=(m: O):=by
   have:(32: O)<=(m: O):=by exact_mod_cast q7
   linarith only [this]
  exact_mod_cast (F.trans_le (h2.trans h3)).le
 have a4:∀ i:Fin t,∃ Res Cap Body:FS (Fin N),Res⊆parts i/\Cap⊆parts i/\Body⊆parts i/\Disjoint Res Cap/\Disjoint Res Body/\Disjoint Cap Body/\Res.card=q/\Cap.card=q/\Body.card=(parts i).card-2*q:=fun i=>P2.spc (parts i) q (v3.trans (I i).1)
 choose Res Cap Body hRes_sub hCap_sub hBody_sub hRC hRB hCB hRes_card hCap_card hBody_card using a4;set c:=Nat.ceil ((m+1: O) * η);have s4:(m+1: O) * η<=(c: O):=Nat.le_ceil _;have e8:(c: O) < (m+1: O) * η + 1:=Nat.ceil_lt_add_one (by positivity)
 have E:(m+1: O)<=2*(m: O):=by
  have:(1: O)<=(m: O):=by exact_mod_cast z2
  linarith only [this]
 have g:∀ i:Fin t,((parts i).card: O)<=(m: O)+1:=fun i=>by
  exact_mod_cast (I i).2
 have y2:∀ i:Fin t,((parts i).card: O) * η<=(c: O):=fun i=>(mul_le_mul_of_nonneg_right (g i) V.le).trans s4
 have y4:(m+1: O) * η<=(q: O):=by
  have F:(m+1: O) * η<=2*(m: O)*(δ / 16):=mul_le_mul E z0 V.le (by positivity)
  linarith only [F,v9]
 have e5:∀ i j:Fin t,((parts j).card: O) * η<=((Res i).card: O):=fun i j=>by
  rw [hRes_card i];exact (mul_le_mul_of_nonneg_right (g j) V.le).trans y4
 have z8:∀ i j:Fin t,((parts j).card: O) * η<=((Cap i).card: O):=fun i j=>by
  rw [hCap_card i];exact (mul_le_mul_of_nonneg_right (g j) V.le).trans y4
 have y1:∀ i:Fin t,(m: O)/2<=((Body i).card: O):=fun i=>by
  have d9:m-2*q<=(Body i).card:=by rw [hBody_card i];exact Nat.sub_le_sub_right (I i).1 _
  have n7:(m: O)-2*(q: O)<=((Body i).card: O):=by
   have:((m-2*q:ℕ): O)=(m: O)-2*(q: O):=by
    rw [Nat.cast_sub v3];push_cast;rfl
   rw [<- this];exact_mod_cast d9
  have k5:2*(q: O)<=δ / 4*(m: O)+2:=by linarith only [b5]
  have p9:(32: O)<=(m: O):=by exact_mod_cast q7
  nlinarith only [n7,k5,p9,x1,c2]
 have h7:∀ i j:Fin t,((parts j).card: O) * η<=((Body i).card: O):=fun i j=>by
  have F:((parts j).card: O) * η<=2*(m: O)*(δ / 16):=mul_le_mul ((g j).trans E) z0 V.le (by positivity)
  have h2:2*(m: O)*(δ / 16)<=(m: O)/2:=by nlinarith only [x1,A]
  exact F.trans (h2.trans (y1 i))
 have v0:∀ i y5 y0:Fin t,3*((max (parts y5).card (parts y0).card: O) * η + 1)<=(d - η)*((Body i).card: O):=by
  intro i y5 y0
  have t4:(max (parts y5).card (parts y0).card: O)<=(m: O)+1:=by
   exact_mod_cast max_le (I y5).2 (I y0).2
  have F:3*((max (parts y5).card (parts y0).card: O) * η + 1)<=3*(2*(m: O)*(d'/256)+1):=by
   have:(max (parts y5).card (parts y0).card: O) * η<=2*(m: O)*(d'/256):=mul_le_mul (t4.trans E) q1 V.le (by positivity)
   linarith only [this]
  have h2:(32: O)<=d'*(m: O):=by
   have w3:=(div_le_iff₀ (by positivity:0 < d' * δ)).mp q4
   have x6:d' * δ * (m: O)<=d'*(m: O):=mul_le_mul_of_nonneg_right (mul_le_of_le_one_right a1.le x1.le) A.le;linarith only [w3,x6,show (m: O)*(d' * δ)=d' * δ * (m: O) by ring]
  have h3:3*(2*(m: O)*(d'/256)+1)<=3/8*(d'*(m: O)):=by
   have x8:3*(2*(m: O)*(d'/256)+1)=3/128*(d'*(m: O))+3:=by ring
   rw [x8];linarith only [h2]
  have h4:3/8*(d'*(m: O))<=(d - η)*((Body i).card: O):=by
   have hb:=y1 i;nlinarith only [hb,s,a1,A]
  exact F.trans (h3.trans h4)
 have n2:∀ i:Fin t,(c: O)<=(d - η)*((Body i).card: O):=fun i=>by
  have F:(c: O)<=3*((max (parts i).card (parts i).card: O) * η + 1):=by
   have r7:(m: O)<=(parts i).card:=by exact_mod_cast (I i).1
   have t6:(m+1: O) * η<=2*((parts i).card: O) * η:=by
    nlinarith only [E,r7,V]
   simp only [max_self];linarith only [e8,t6]
  exact F.trans (v0 i i i)
 have t2:d'^2<=1:=by rw [sq];exact mul_le_one₀ e6 a1.le e6
 have b3:∀ i j:Fin t,((parts j).card: O) * η<=(d - η)*((Cap i).card: O):=by
  intro i j;rw [hCap_card i];have F:((parts j).card: O) * η<=2*(m: O)*(d' * δ / 256):=mul_le_mul ((g j).trans E) p3 V.le (by positivity)
  have h2:2*(m: O)*(d' * δ / 256)<=(3/4*d')*(δ / 8*(m: O)):=by
   have c0:0<=d' * δ * (m: O):=by positivity
   linarith only [c0,show 2*(m: O)*(d' * δ / 256)=(1/128)*(d' * δ * (m: O)) by ring,
    show (3/4*d')*(δ / 8*(m: O))=(3/32)*(d' * δ * (m: O)) by ring]
  have h3:(3/4*d')*(δ / 8*(m: O))<=(d - η)*(q: O):=mul_le_mul s v9 (by positivity) (by linarith only [s,a1])
  exact F.trans (h2.trans h3)
 have b1:∀ i:Fin t,(L: O)+2 * ((parts i).card: O) * η<=((Res i).card: O):=by
  intro i;rw [hRes_card i];have b0:(L: O)<=2*(t: O):=by exact_mod_cast b9
  have h0:2*(t: O)<=d'^2 * δ * (m: O)/128:=by
   have F:=(div_le_iff₀ (by positivity:0 < d'^2 * δ)).mp x4
   linarith only [F,show (m: O)*(d'^2 * δ)=d'^2 * δ * (m: O) by ring]
  have r2:2*((parts i).card: O) * η<=d'^2 * δ * (m: O)/64:=by
   have x6:=(g i).trans E;have F:=mul_le_mul x6 v2 V.le (by positivity)
   linarith only [F,show 2*(m: O)*(d'^2 * δ / 256)=d'^2 * δ * (m: O)/128 by ring]
  have k0:d'^2 * δ * (m: O)/128+d'^2 * δ * (m: O)/64<=δ / 8*(m: O):=by
   have z4:0<=δ * (m: O):=by positivity
   have r6:d'^2 * (δ * (m: O))<=1*(δ * (m: O)):=mul_le_mul_of_nonneg_right t2 z4;linarith only [r6,z4,show d'^2 * δ * (m: O)=d'^2 * (δ * (m: O)) by ring]
  linarith only [b0,h0,r2,k0,v9]
 have a9:∀ i j:Fin t,((parts j).card: O) * η<=(d - η)*((Res i).card: O)/\(L: O)+2 * ((parts j).card: O) * η<=(d - η)*((Res i).card: O):=by
  intro i j;rw [hRes_card i];have b0:(L: O)<=2*(t: O):=by exact_mod_cast b9
  have h0:2*(t: O)<=d'^2 * δ * (m: O)/128:=by
   have F:=(div_le_iff₀ (by positivity:0 < d'^2 * δ)).mp x4
   linarith only [F,show (m: O)*(d'^2 * δ)=d'^2 * δ * (m: O) by ring]
  have n6:2*((parts j).card: O) * η<=d'^2 * δ * (m: O)/64:=by
   have x6:=(g j).trans E;have F:=mul_le_mul x6 v2 V.le (by positivity)
   linarith only [F,show 2*(m: O)*(d'^2 * δ / 256)=d'^2 * δ * (m: O)/128 by ring]
  have t5:((parts j).card: O) * η<=d'^2 * δ * (m: O)/128:=by
   have x6:=(g j).trans E;have F:=mul_le_mul x6 v2 V.le (by positivity)
   linarith only [F,show 2*(m: O)*(d'^2 * δ / 256)=d'^2 * δ * (m: O)/128 by ring]
  have c7:(3/4*d')*(δ / 8*(m: O))<=(d - η)*(q: O):=mul_le_mul s v9 (by positivity) (by linarith only [s,a1])
  have a8:d'^2 * δ * (m: O)<=d' * δ * (m: O):=by
   have z4:0<=δ * (m: O):=by positivity
   have r6:d'^2<=d':=by rw [sq];exact mul_le_of_le_one_left a1.le e6
   have F:=mul_le_mul_of_nonneg_right r6 z4
   linarith only [F,show d'^2 * (δ * (m: O))=d'^2 * δ * (m: O) by ring,
    show d'*(δ * (m: O))=d' * δ * (m: O) by ring]
  have c0:0<=d' * δ * (m: O):=by positivity
  have hA:d'^2 * δ * (m: O)/128+d'^2 * δ * (m: O)/64<=(3/4*d')*(δ / 8*(m: O)):=by
   linarith only [a8,c0,show (3/4*d')*(δ / 8*(m: O))=3/32*(d' * δ * (m: O)) by ring]
  have hB:d'^2 * δ * (m: O)/128<=(3/4*d')*(δ / 8*(m: O)):=by
   linarith only [a8,c0,show (3/4*d')*(δ / 8*(m: O))=3/32*(d' * δ * (m: O)) by ring]
  exact ⟨t5.trans (hB.trans c7),by linarith only [b0,h0,n6,hA,c7]⟩
 have y8:∀ i j:Fin t,(L: O)+2 * ((parts j).card: O) * η<=(d - η)*((d - η)*((Res i).card: O)):=by
  intro i j;rw [hRes_card i];have b0:(L: O)<=2*(t: O):=by exact_mod_cast b9
  have h0:2*(t: O)<=d'^2 * δ * (m: O)/128:=by
   have F:=(div_le_iff₀ (by positivity:0 < d'^2 * δ)).mp x4
   linarith only [F,show (m: O)*(d'^2 * δ)=d'^2 * δ * (m: O) by ring]
  have n6:2*((parts j).card: O) * η<=d'^2 * δ * (m: O)/64:=by
   have x6:=(g j).trans E;have F:=mul_le_mul x6 v2 V.le (by positivity)
   linarith only [F,show 2*(m: O)*(d'^2 * δ / 256)=d'^2 * δ * (m: O)/128 by ring]
  have c7:(3/4*d')*((3/4*d')*(δ / 8*(m: O)))<=(d - η)*((d - η)*(q: O)):=by
   have u8:(3/4*d')*(δ / 8*(m: O))<=(d - η)*(q: O):=mul_le_mul s v9 (by positivity) (by linarith only [s,a1])
   exact mul_le_mul s u8 (by positivity) (by linarith only [s,a1])
  have hA:d'^2 * δ * (m: O)/128+d'^2 * δ * (m: O)/64<=(3/4*d')*((3/4*d')*(δ / 8*(m: O))):=by
   have c6:0<=d'^2 * δ * (m: O):=by positivity
   linarith only [c6,show (3/4*d')*((3/4*d')*(δ / 8*(m: O)))=9/128*(d'^2 * δ * (m: O)) by ring]
  linarith only [b0,h0,n6,hA,c7]
 let w:ℕ->Fin t:=fun i=>if h:i < L then W[i].1 else (W.head v7).1
 let w':ℕ->Fin t:=fun i=>if h:i < L then W[i].2.1 else (W.head v7).1
 have y7:∀ i (Q:i < L),R.Adj (w i) (w' i):=fun i Q=>by
  simp only [w,w',dif_pos Q];exact s3 W[i] (List.getElem_mem Q)
 have q2:∀ i (Q:i+1 < L),w' i=w (i+1):=fun i Q=>by
  simp only [w',w,dif_pos (by omega:i < L),dif_pos Q]
  exact List.isChain_iff_getElem.mp e1 i Q
 have p5:w' (L-1)=w 0:=by
  simp only [w',w,dif_pos (by omega:L-1 < L),dif_pos (by omega:0 < L)]
  have F:=p7 v7;rwa [List.getLast_eq_getElem v7,List.head_eq_getElem v7] at F
 obtain ⟨z,c4,v4,n1,z9,n9⟩ :=
  P2.etv G V parts R T hR Res Cap Body hRes_sub hCap_sub hBody_sub e5 z8 h7 L w w' y7 q2 p5 len b8 k4 d0 b1 a9 y8
 have hℓ_bound:∀ i (Q:i < L),len i<=min ((Body (w' i)).card-c) (Body (w i)).card-2*c:=by
  intro i Q
  have s9:len i<=B:=by
   simp only [len,dif_pos Q];exact b2 i Q
  have n4:(B: O)<=(1 - δ)*(m: O):=Nat.floor_le (by positivity)
  have n8:(c: O) < 2*(m: O)*(δ / 16)+1:=by
   have:(m+1: O) * η<=2*(m: O)*(δ / 16):=mul_le_mul E z0 V.le (by positivity)
   linarith only [this,e8]
  have e3:(q: O) < δ / 8*(m: O)+1:=b5
  have w0:(m: O)-2*(q: O)<=((Body (w i)).card: O):=by
   have d9:m-2*q<=(Body (w i)).card:=by
    rw [hBody_card (w i)];exact Nat.sub_le_sub_right (I (w i)).1 _
   have n7:((m-2*q:ℕ): O)=(m: O)-2*(q: O):=by
    rw [Nat.cast_sub v3];push_cast;rfl
   rw [<- n7];exact_mod_cast d9
  have u7:(m: O)-2*(q: O)<=((Body (w' i)).card: O):=by
   have d9:m-2*q<=(Body (w' i)).card:=by
    rw [hBody_card (w' i)];exact Nat.sub_le_sub_right (I (w' i)).1 _
   have n7:((m-2*q:ℕ): O)=(m: O)-2*(q: O):=by
    rw [Nat.cast_sub v3];push_cast;rfl
   rw [<- n7];exact_mod_cast d9
  have p9:(32: O)<=δ * (m: O):=by
   have:=(div_le_iff₀ c2).mp r9;linarith only [this]
  have F:(len i: O)<=(1 - δ)*(m: O):=(Nat.cast_le.mpr s9).trans n4
  have h2:(1 - δ)*(m: O)<=((Body (w' i)).card: O)-3*(c: O):=by
   nlinarith only [u7,n8,e3,p9,c2,x1,A]
  have h3:(1 - δ)*(m: O)<=((Body (w i)).card: O)-3*(c: O):=by
   nlinarith only [w0,n8,e3,p9,c2,x1,A]
  have m3:len i<=(Body (w' i)).card-3*c:=by
   have:(len i: O)+3 * (c: O)<=((Body (w' i)).card: O):=by linarith only [F,h2]
   have:len i+3 * c<=(Body (w' i)).card:=by exact_mod_cast this
   omega
  have m1:len i<=(Body (w i)).card-3*c:=by
   have:(len i: O)+3 * (c: O)<=((Body (w i)).card: O):=by linarith only [F,h3]
   have:len i+3 * c<=(Body (w i)).card:=by exact_mod_cast this
   omega
  omega
 have Z:∀ i:ℕ,i < L->∃ v1:List (Fin N),v1≠[]/\v1.length=2*len i+1/\(∀ h:v1≠[],v1.head h=z i)/\(∀ h:v1≠[],G.Adj (v1.getLast h) (z ((i+1) % L)))/\v1.Nodup/\v1.IsChain G.Adj/\(0 < len i->v1.toFinset⊆insert (z i) (Body (w i) ∪ Body (w' i) ∪ Cap (w i)))/\(len i=0->v1=[z i]):=by
  intro i Q;by_cases s5:0 < len i
  · have d4:i+1 < L:=by
     by_contra! m6;have:i=L-1:=by omega
     subst this;omega
    have hmod:(i+1) % L=i+1:=Nat.mod_eq_of_lt d4;have a2:=n1 i d4;simp only [s5,↓reduceIte] at a2;have a6:=z9 (i+1) (by omega) d4
    simp only [show i+1-1=i by omega,s5,↓reduceIte] at a6
    have p4:=hR (w i) (w' i) (y7 i Q)
    obtain ⟨v1,x5,q0,n0,e0,d3,c9,p8⟩ :=
     P2.brs G V r8 (hRes_sub (w i)) (hCap_sub (w i)) (hBody_sub (w i)) (hBody_sub (w' i)) (v5 (R.ne_of_adj (y7 i Q))) (hRC (w i)) (hRB (w i)) (hCB (w i)) p4.1 p4.2 (T (w i)) (T (w' i)) c (y2 (w i)) (y2 (w' i)) (n2 (w i)) (z8 (w i) (w i)) (h7 (w i) (w i)) (h7 (w' i) (w' i)) (c4 i Q) a2 a6 (b3 (w i) (w i)) (v0 (w' i) (w i) (w' i)) (len i) s5 (hℓ_bound i Q)
    refine ⟨v1,x5,q0,n0,?_,d3,c9,fun _=>p8,fun h=>by omega⟩
    rw [hmod];exact e0
  · have q5:len i=0:=by omega
    refine ⟨[z i],by simp,by simp [q5],fun _=>rfl,?_,List.nodup_singleton _,List.isChain_singleton _,fun h=>by omega,fun _=>rfl⟩
    intro _;simp only [List.getLast_singleton];by_cases d4:i+1 < L
    · have hmod:(i+1) % L=i+1:=Nat.mod_eq_of_lt d4
      rw [hmod];have hp:=z9 (i+1) (by omega) d4
      simpa [show i+1-1=i by omega,q5] using hp
    · have t9:i=L-1:=by omega
      subst t9;have hmod:(L-1+1) % L=0:=by rw [show L-1+1=L by omega,Nat.mod_self]
      rw [hmod];exact n9
 let H:ℕ->List (Fin N):=fun i=>if h:i < L then (Z i h).choose else []
 have a:∀ i (Q:i < L),H i≠[]/\(H i).length=2*len i+1/\(∀ h:H i≠[],(H i).head h=z i)/\(∀ h:H i≠[],G.Adj ((H i).getLast h) (z ((i+1) % L)))/\(H i).Nodup/\(H i).IsChain G.Adj/\(0 < len i->(H i).toFinset⊆insert (z i) (Body (w i) ∪ Body (w' i) ∪ Cap (w i)))/\(len i=0->H i=[z i]):=by
  intro i Q;simp only [H,dif_pos Q];exact (Z i Q).choose_spec
 have x0:∀ i (Q:i < L),0 < len i->W[i].2.2=true:=by
  intro i Q c6;by_contra p6;have hf:W[i].2.2=false:=Bool.eq_false_iff.mpr p6;have hz:=h8 i Q hf;simp only [len,dif_pos Q] at c6;rw [hz] at c6;omega
 have x9:∀ e < L,∀ b < L,e≠b->0 < len e->0 < len b->Disjoint ({w e,w' e}:FS (Fin t)) ({w b,w' b}:FS (Fin t)):=by
  intro e f b l x5 e4 e2;have u2:=x0 e f e4;have t0:=x0 b l e2;simp only [w,w',dif_pos f,dif_pos l];rcases lt_or_gt_of_ne x5 with r3 | r3
  · exact P2.tid W z7 e b f l r3 u2 t0
  · exact (P2.tid W z7 b e l f r3 t0 u2).symm
 have J:∀ e < L,∀ b < L,z e ∉ Body (w b) ∪ Body (w' b) ∪ Cap (w b):=by
  intro e f b l q6;have b4:z e∈Res (w e):=c4 e f;have r1:=hRes_sub (w e) b4;simp only [mem_union] at q6;rcases q6 with (t3 | t8) | hC
  · by_cases x8:w e=w b
    · rw [x8] at b4;exact Finset.disjoint_left.mp (hRB (w b)) b4 t3
    · exact Finset.disjoint_left.mp (v5 x8) r1 (hBody_sub _ t3)
  · by_cases x8:w e=w' b
    · rw [x8] at b4;exact Finset.disjoint_left.mp (hRB (w' b)) b4 t8
    · exact Finset.disjoint_left.mp (v5 x8) r1 (hBody_sub _ t8)
  · by_cases x8:w e=w b
    · rw [x8] at b4;exact Finset.disjoint_left.mp (hRC (w b)) b4 hC
    · exact Finset.disjoint_left.mp (v5 x8) r1 (hCap_sub _ hC)
 have a7:∀ e < L,∀ b < L,e≠b->Disjoint (H e).toFinset (H b).toFinset:=by
  intro e f b l x5;rw [Finset.disjoint_left]
  intro x Y X;by_cases F:0 < len e <;> by_cases h2:0 < len b
  · have p1:=(a e f).2.2.2.2.2.2.1 F Y
    have d8:=(a b l).2.2.2.2.2.2.1 h2 X
    rcases mem_insert.mp p1 with rfl | a0 <;>
     rcases mem_insert.mp d8 with d6 | a3
    · exact v4 e f b l x5 d6
    · exact J e f b l a3
    · exact J b l e f (d6 ▸ a0)
    · have hd:=x9 e f b l x5 F h2
      have d5:∃ u ∈ ({w e,w' e}:FS (Fin t)),x∈parts u:=by
       simp only [mem_union] at a0;rcases a0 with (h | h) | h
       · exact ⟨w e,by simp,hBody_sub _ h⟩
       · exact ⟨w' e,by simp,hBody_sub _ h⟩
       · exact ⟨w e,by simp,hCap_sub _ h⟩
      have c8:∃ v ∈ ({w b,w' b}:FS (Fin t)),x∈parts v:=by
       simp only [mem_union] at a3;rcases a3 with (h | h) | h
       · exact ⟨w b,by simp,hBody_sub _ h⟩
       · exact ⟨w' b,by simp,hBody_sub _ h⟩
       · exact ⟨w b,by simp,hCap_sub _ h⟩
      obtain ⟨u,hu,k3⟩:=d5;obtain ⟨v,hv,w6⟩:=c8;have r4:u≠v:=fun h=>D1 hd hu (h ▸ hv)
      exact Finset.disjoint_left.mp (v5 r4) k3 w6
  · have s0:len b=0:=by omega
    have p1:=(a e f).2.2.2.2.2.2.1 F Y;have d8:=(a b l).2.2.2.2.2.2.2 s0;rw [d8] at X;simp only [List.toFinset_cons,List.toFinset_nil,mem_insert,notMem_empty,or_false] at X;subst X;rcases mem_insert.mp p1 with d6 | a0
    · exact v4 b l e f x5.symm d6
    · exact J b l e f a0
  · have s6:len e=0:=by omega
    have p1:=(a e f).2.2.2.2.2.2.2 s6;have d8:=(a b l).2.2.2.2.2.2.1 h2 X;rw [p1] at Y;simp only [List.toFinset_cons,List.toFinset_nil,mem_insert,notMem_empty,or_false] at Y;subst Y;rcases mem_insert.mp d8 with d6 | a3
    · exact v4 e f b l x5 d6
    · exact J e f b l a3
  · have s6:len e=0:=by omega
    have s0:len b=0:=by omega
    rw [List.mem_toFinset,(a e f).2.2.2.2.2.2.2 s6,List.mem_singleton] at Y;rw [List.mem_toFinset,(a b l).2.2.2.2.2.2.2 s0,List.mem_singleton] at X;exact v4 e f b l x5 (Y.symm.trans X)
 have b7: ∑ i ∈ range L,(H i).length=n:=by
  have F: ∑ i ∈ range L,(H i).length=∑ i ∈ range L,(2*len i+1):=sum_congr rfl fun i Q=>(a i (mem_range.mp Q)).2.1
  rw [F,sum_add_distrib,sum_const,card_range,smul_eq_mul,mul_one,<-mul_sum]
  have h2: ∑ i ∈ range L,len i=D:=by
   have h3: ∑ i ∈ range L,len i=z6.sum:=by
    rw [<- h6]
    exact P2.srls z6 len (fun i Q=>by
     have s1:i < L:=h6 ▸ Q;simp [len,s1])
   exact h3.trans x3
  omega
 exact P2.acy G k6 (by omega) z H (fun i Q=>(a i Q).1) (fun i Q=>(a i Q).2.2.1) (fun i Q=>(a i Q).2.2.2.2.1) (fun i Q=>(a i Q).2.2.2.2.2.1) (fun i Q=>(a i Q).2.2.2.1) a7 b7
end S3
section _m
namespace E5
open SimpleGraph Finset
open scoped SimpleGraph Classical
structure q4 (V:Type*) where
 colour:V->V->Fin 3
 symm:∀ u v,colour u v=colour v u
def q4.graph {V:Type*} (c:q4 V) (i:Fin 3):SG V where
 Adj u v:=u≠v/\c.colour u v=i
 symm:= ⟨by
  intro u v h;exact ⟨h.1.symm,(c.symm v u).trans h.2⟩⟩
 loopless:= ⟨by simp⟩
@[simp] lemma q4.e4 {V:Type*} (c:q4 V)(i:Fin 3) (u v:V):(c.graph i).Adj u v↔u≠v/\c.colour u v=i:=Iff.rfl
def q4.comap {V W:Type*} (c:q4 V) (f:W->V):q4 W where
 colour u v:=c.colour (f u) (f v)
 symm u v:=c.symm (f u) (f v)
lemma q4.tY {V W:Type*} (c:q4 V)(f:W ↪ V) (i:Fin 3):(c.comap f).graph i=(c.graph i).comap f :=by ext u v;simp only [e4,comap,SimpleGraph.comap_adj];exact and_congr_left fun _=>f.injective.ne_iff.symm
def rr (n m:ℕ):Prop:= ∀ c:q4 (Fin m),∃ i:Fin 3,CG n ⊑ c.graph i
lemma rr.mono {n a b:ℕ} (h:rr n a)(d:a<=b):rr n b:=by intro c;let f:Fin a ↪ Fin b :=Fin.castLEEmb d;obtain ⟨i,e⟩ :=h (c.comap f);refine ⟨i,?_⟩;rw [c.tY f i] at e;exact e.trans (SimpleGraph.Embedding.comap f (c.graph i)).isContained
end E5
end _m
section e0
namespace E5.TC
open Finset
open scoped SimpleGraph
end E5.TC
namespace E5
open SimpleGraph
open scoped SimpleGraph
end E5
end e0
section _m
namespace E5
open SimpleGraph Finset
open scoped SimpleGraph Classical
abbrev wz:=Fin 3->Bool
abbrev q1:=Fin 3->Option Bool
def q0 (p:q1):FS wz:= univ.filter (fun v=>∀ i,p i=none\/p i =some (v i))
def q3 (p:q1):ℕ:= (univ.filter (fun i=>p i=none)).card
def cF (i:Fin 3)(b:Bool):q1:= fun j=>if j =i then some b else none
def qF:q1:=fun _=>none
lemma sM (p:q1):q3 p<=3 :=by
 have h :=card_le_univ (univ.filter (fun i:Fin 3=>p i=none))
 simpa only [q3,Fintype.card_fin] using h
lemma qU:∀ p:q1,(q0 p).card=2^q3 p :=by decide
lemma r4:∀ (i:Fin 3)(b:Bool),q3 (cF i b)=2:=by decide
lemma zx:q3 qF=3:=by decide
lemma sz:∀ p:q1,q3 p =3↔p=qF:=by decide
lemma u1:∀ p:q1,q3 p =2↔∃ (i:Fin 3)(b:Bool),p=cF i b:=by decide
lemma ru:∀ p q:q1,q3 p =1->q3 q =1->p≠q->((q0 p) ∩ (q0 q)).card≠1->Disjoint (q0 p) (q0 q) :=by decide
lemma ui:∀ (i j:Fin 3)(b c:Bool),Disjoint (q0 (cF i b)) (q0 (cF j c))↔i=j/\b≠c:=by decide
structure q6 (w:q1->O):Prop where
 nonneg:∀ p,0<=w p
 sum_four: ∑ p,w p=4
 vertex_zero:∀ p,q3 p =0->w p=0
 edge_le_one:∀ p,q3 p =1->w p<=1
 compatible:∀ p q,0 < w p->0 < w q->(q0 p ∩ q0 q).card≠1
def qb (p q:q1): O:= if Disjoint (q0 p) (q0 q) then 0 else 1
def qd (w:q1->O): O:= (∑ p,∑ q,qb p q*w p*w q) - ∑ p,(q3 p:O)*w p
def qm (w:q1->O) (p:q1): O:= 2* (∑ q,qb p q*w q)-q3 p
lemma sm (p q:q1):qb p q=qb q p:=by simp only [qb,disjoint_comm]
lemma vU (p:q1):qb p p=1:=by
 have d:0 < (q0 p).card:=by rw [qU];positivity
 have e:¬ Disjoint (q0 p) (q0 p) :=by
  simpa only [disjoint_self,bot_eq_empty,<- card_eq_zero] using Nat.ne_of_gt d
 simp only [qb,if_neg e]
lemma vh (E:FS q1)(S:FS wz) (e:∀ p ∈ E,q3 p =1) (d:(E:Set q1).Pairwise (fun p q=> Disjoint (q0 p) (q0 q))) (hsub:∀ p ∈ E,q0 p⊆S):2*E.card<=S.card:=by
 have g:(∑ p ∈ E,(q0 p).card)=2*E.card:=by
  calc
   (∑ p ∈ E,(q0 p).card)=∑ _p ∈ E,2:=by
    apply sum_congr rfl
    intro p i;rw [qU,e p i];norm_num
   _=2*E.card:=by simp [Nat.mul_comm]
 rw [<- g,<- card_biUnion d];apply card_le_card
 intro v j;obtain ⟨p,i,h⟩ :=mem_biUnion.mp j;exact hsub p i h
open scoped Classical in
noncomputable def ql (w:q1->O):FS q1:= univ.filter (fun p=>q3 p =1/\0 < w p)
lemma q6.s0 {w:q1->O} (l:q6 w):(ql w:Set q1).Pairwise (fun p q=> Disjoint (q0 p) (q0 q)) :=by intro p j q k i;obtain ⟨_,d,h⟩ :=mem_filter.mp j;obtain ⟨_,e,g⟩ :=mem_filter.mp k;exact ru p q d e i (l.compatible p q h g)
lemma q6.vl {w:q1->O} (g:q6 w):(ql w).card<=4:=by
 have h :=vh (ql w) univ (fun p e=> (mem_filter.mp e).2.1) g.s0 (fun _ _=> subset_univ _)
 have d:(univ:FS wz).card=8:=by decide
 rw [d] at h;omega
lemma vn {V P R:Type*} [Fintype V] [Fintype P] [DecidableEq P] [Semiring R] (d:V->P) (f:P->R):(∑ v,f (d v))=∑ p,((univ.filter (fun v=>d v =p)).card:R)*f p :=by
 classical
 have h :=sum_fiberwise' (univ:FS V) d f;simpa only [sum_const,nsmul_eq_mul] using h.symm
lemma aE {V P:Type*} [Fintype V] [Fintype P] [DecidableEq P] (d:V->P):(∑ p,(univ.filter (fun v=>d v =p)).card)=Fintype.card V :=by simpa using (vn d (fun _=>(1:ℕ))).symm
lemma yG {V P R:Type*} [Fintype V] [Fintype P] [DecidableEq P] [Semiring R] (d:V->P) (f:P->P->R):(∑ u,∑ v,f (d u) (d v))=∑ p,∑ q,((univ.filter (fun v=>d v =p)).card:R)*((univ.filter (fun v=>d v =q)).card:R)*f p q:=by
 classical
 calc
  _= ∑ u,∑ q,((univ.filter (fun v=>d v =q)).card:R)*f (d u) q :=by
   apply sum_congr rfl
   intro u _;exact vn d (f (d u))
  _= ∑ p,((univ.filter (fun v=>d v =p)).card:R)*(∑ q,((univ.filter (fun v=>d v =q)).card:R)*f p q) :=
   vn d (fun p=>∑ q,((univ.filter (fun v=>d v =q)).card:R)*f p q)
  _=_:=by simp only [mul_sum,mul_assoc]
lemma q7 {V:Type*} (G:SG V) [Fintype G.edgeSet]:G.edgeFinset.card=Nat.card G.edgeSet:= G.card_edgeSet.symm.trans Nat.card_eq_fintype_card.symm
lemma tf {V W:Type*} [Fintype V] [DecidableEq W] (G:SG V) [DecidableRel G.Adj] (f:V ↪ W)(A:FS W):((G.map f).induce (A:Set W)).edgeFinset.card= (G.induce ((univ.filter (fun v=>f v∈A):FS V):Set V)).edgeFinset.card:=by
 classical
 let B :=univ.filter (fun v:V=> f v∈A)
 let g:(B:Set V) ↪ (A:Set W) :=
  { toFun:=fun v=>⟨f v.val,(mem_filter.mp v.property).2⟩
    inj':=fun u v h=>Subtype.ext (f.injective (CA Subtype.val h))}
 have e:(G.map f).induce (A:Set W) ≃g (G.induce (B:Set V)).map g :=
  { toEquiv:=Equiv.refl _
    map_rel_iff':=by
     intro u v
     constructor
     · rintro ⟨d,a,b,i,l,k⟩
       change (G.map f).Adj u.val v.val
       refine ⟨fun h=>d (Subtype.ext h),a.val,b.val,i,?_,?_⟩
       · exact CA Subtype.val l
       · exact CA Subtype.val k
     · intro j
       change (G.map f).Adj u.val v.val at j
       obtain ⟨d,a,b,i,l,k⟩ :=j
       have m:a∈B:=mem_filter.mpr ⟨mem_univ _,l ▸ u.property⟩
       have n:b∈B:=mem_filter.mpr ⟨mem_univ _,k ▸ v.property⟩
       refine ⟨fun h=>d (CA Subtype.val h),⟨a,m⟩,⟨b,n⟩,i,?_,?_⟩
       · exact Subtype.ext l
       · exact Subtype.ext k}
 exact e.card_edgeFinset_eq.trans (card_edgeFinset_map g (G.induce (B:Set V)))
lemma t1 {V W:Type*} [Fintype V] [DecidableEq W] (f:V ↪ W)(A:FS W):(univ.filter (fun v=>f v∈A)).card<=A.card:=by
 classical
 let B :=univ.filter (fun v:V=> f v∈A)
 let g:(B:Set V) ↪ (A:Set W) :=
  { toFun:=fun v=>⟨f v.val,(mem_filter.mp v.property).2⟩
    inj':=fun u v h=>Subtype.ext (f.injective (CA Subtype.val h))}
 have h :=Fintype.card_le_of_injective g g.injective
 have d:Fintype.card (B:Set V)=B.card:=by
  calc
   Fintype.card (B:Set V)=(B:Set V).ncard:=Nat.card_eq_fintype_card.symm
   _=B.card:=Set.ncard_coe_finset B
 have e:Fintype.card (A:Set W)=A.card:=by
  calc
   Fintype.card (A:Set W)=(A:Set W).ncard:=Nat.card_eq_fintype_card.symm
   _=A.card:=Set.ncard_coe_finset A
 rw [d,e] at h;exact h
lemma x2 {V W:Type*} [Fintype V] [DecidableEq W] (G:SG V) [DecidableRel G.Adj] (f:V ↪ W)(D:O) (d:0<=D) (h:∀ S:FS V,((G.induce (S:Set V)).edgeFinset.card:O)<=D*S.card):∀ A:FS W,(((G.map f).induce (A:Set W)).edgeFinset.card:O)<=D*A.card:=by
 classical
 intro A;rw [tf G f A];apply (h _).trans;apply mul_le_mul_of_nonneg_left _ d;exact_mod_cast t1 f A
lemma ac {V W:Type*} (G:SG V)(f:V ↪ W) (S:FS V)(h:∀ a b,G.Adj a b->a∈S/\b∈S):∀ a b,(G.map f).Adj a b->a∈S.map f/\b∈S.map f :=by
 classical
 rintro a b ⟨_,u,v,d,rfl,rfl⟩;exact ⟨mem_map.mpr ⟨u,(h u v d).1,rfl⟩,mem_map.mpr ⟨v,(h u v d).2,rfl⟩⟩
lemma tW {V W:Type*} (G:SG V)(f:V ↪ W) (S:FS V)(h:∀ a b,G.Adj a b->a ∉ S/\b ∉ S):∀ a b,(G.map f).Adj a b->a ∉ S.map f/\b ∉ S.map f :=by
 classical
 rintro a b ⟨_,u,v,g,rfl,rfl⟩
 have d (x:V) (k:x ∉ S):f x ∉ S.map f :=by
  intro e;obtain ⟨y,j,i⟩ :=mem_map.mp e;exact k ((f.injective i) ▸ j)
 exact ⟨d u (h u v g).1,d v (h u v g).2⟩
def qJ {V:Type*} (d:V->q1):SG V where
 Adj u v:=Disjoint (q0 (d u)) (q0 (d v))
 symm:= ⟨fun _ _ h=>h.symm⟩
 loopless:= ⟨by
  intro v h
  have g:q0 (d v)=∅ :=by
   simpa only [disjoint_self,bot_eq_empty] using h
  have e:0 < (q0 (d v)).card:=by rw [qU];positivity
  rw [g,card_empty] at e;omega⟩
def qO (w:q1->O): O:= ∑ p,∑ q,if Disjoint (q0 p) (q0 q) then w p*w q else 0
lemma sb {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj]:2* (Nat.card G.edgeSet:O)=∑ u,∑ v,if G.Adj u v then (1:O) else 0 :=by
 classical
 have d (u:V):G.degree u=∑ v,if G.Adj u v then (1:ℕ) else 0 :=by
  rw [sum_boole,<- card_neighborFinset_eq_degree];congr 1;ext v;simp
 have h :=G.sum_degrees_eq_twice_card_edges;simp only [d,q7] at h;exact_mod_cast h.symm
lemma sY {V:Type*} [Fintype V] (d:V->q1):2* (Nat.card (qJ d).edgeSet:O)=qO (fun p=>((univ.filter (fun v=>d v =p)).card:O)) :=by
 classical
 rw [sb];have e:(∑ u,∑ v,if (qJ d).Adj u v then (1:O) else 0)=∑ u,∑ v,if Disjoint (q0 (d u)) (q0 (d v)) then (1:O)
  else 0 :=by
  apply sum_congr rfl
  intro u _;apply sum_congr rfl
  intro v _;by_cases h:Disjoint (q0 (d u)) (q0 (d v)) <;>
   simp [qJ,h]
 rw [e];rw [yG d (fun p q=> if Disjoint (q0 p) (q0 q) then (1:O) else 0)]
 unfold qO;apply sum_congr rfl
 intro p _;apply sum_congr rfl
 intro q _;split_ifs <;> simp
lemma zv (w:q1->O):qd w=(∑ p,w p)^2-qO w - ∑ p,(q3 p:O)*w p :=by
 have h:(∑ p,∑ q,qb p q*w p*w q)+qO w=(∑ p,w p)^2:=by
  calc
   _= ∑ p,∑ q,(qb p q*w p*w q+ if Disjoint (q0 p) (q0 q) then w p*w q else 0) :=by
    simp only [qO,sum_add_distrib]
   _= ∑ p,∑ q,w p*w q:=by
    apply sum_congr rfl
    intro p _;apply sum_congr rfl
    intro q _;unfold qb;split_ifs <;> simp
   _=_:=by
    simp only [pow_two,sum_mul,mul_sum];exact sum_comm
 unfold qd;linarith
lemma rq {V:Type*} {G:SG V} {u v:V} (p:G.Walk u v)(t:p.IsPath) (S:Set V)(n:v∈S):∃ w ∈ S,∃ q:G.Walk u w,q.IsPath/\q.length<=p.length/\q.support⊆p.support/\∀ x ∈ q.support,x∈S->x=w:=by
 classical
 let P (m:ℕ):Prop:= ∃ w ∈ S,∃ q:G.Walk u w,q.IsPath/\q.support⊆p.support/\q.length=m;have e:∃ m,P m:= ⟨p.length,v,n,p,t,List.Subset.refl _,rfl⟩;obtain ⟨w,D,q,s,hsub,g⟩ :=Nat.find_spec e
 have d {z:V} (i:z∈S) (r:G.Walk u z) (F:r.IsPath) (l:r.support⊆p.support):q.length<=r.length:=by
  rw [g];exact Nat.find_min' e ⟨z,i,r,F,l,rfl⟩
 refine ⟨w,D,q,s,d n p t (List.Subset.refl _),hsub,?_⟩
 intro x h j;by_contra k;have C:=q.length_takeUntil_lt_length h k;have y:=d j (q.takeUntil x h) (s.takeUntil h) (fun _ i=> hsub (q.support_takeUntil_subset_support h i))
 omega
lemma qr {V:Type*} {G:SG V} {u v w:V} (p:G.Walk u v)(q:G.Walk v w) (m:p.IsPath)(l:q.IsPath) (d:∀ x ∈ p.support,x∈q.support->x=v):(p.append q).IsPath:=by
 induction p with
 | nil=> simpa using l
 | @cons u z v huz p ih=>
  have j:=m.of_cons;have n:u ∉ p.support:= (Walk.cons_isPath_iff huz p).mp m |>.2;have i:u≠v:=fun h=>n (h ▸ p.end_mem_support)
  have g:u ∉ q.support:=fun h=>i (d u (by simp) h)
  have r:∀ x ∈ p.support,x∈q.support->x=v:= fun x e k=> d x (by simp [e]) k
  exact (ih q j l r).cons (by
   intro e;rcases (Walk.mem_support_append_iff _ _).mp e with e | e
   · exact n e
   · exact g e)
lemma qz {V:Type*} {G:SG V} {u v x:V} (p:G.Walk u v)(i:ℕ) (h:i<=p.length):x∈(p.take i).support↔∃ j,j<=i/\p.getVert j =x:=by
 constructor
 · intro k
   obtain ⟨j,d,g⟩ :=Walk.mem_support_iff_exists_getVert.mp k;have e:j<=i:=by simpa only [Walk.take_length,min_eq_left h] using g
   refine ⟨j,e,?_⟩;simpa only [Walk.take_getVert,inf_eq_right.mpr e] using d
 · rintro ⟨j,g,d⟩
   apply Walk.mem_support_iff_exists_getVert.mpr;refine ⟨j,?_,?_⟩
   · simpa only [Walk.take_getVert,inf_eq_right.mpr g] using d
   · simpa only [Walk.take_length,min_eq_left h] using g
lemma rd {V:Type*} {G:SG V} {u v x:V} (p:G.Walk u v)(i:ℕ) (k:i<=p.length):x∈(p.drop i).support↔∃ j,i<=j/\j<=p.length/\p.getVert j =x:=by
 constructor
 · intro h
   obtain ⟨j,d,g⟩ :=Walk.mem_support_iff_exists_getVert.mp h;rw [Walk.drop_length] at g;refine ⟨i+j,by omega,by omega,?_⟩
   simpa only [Walk.drop_getVert] using d
 · rintro ⟨j,e,g,d⟩
   apply Walk.mem_support_iff_exists_getVert.mpr;refine ⟨j-i,?_,?_⟩
   · simpa only [Walk.drop_getVert,Nat.add_sub_of_le e] using d
   · rw [Walk.drop_length];omega
lemma vJ {V:Type*} {G:SG V} {u v:V} (p:G.Walk u v)(q:p.IsPath) (i j:ℕ)(l:i < j) (r:j<=p.length):(p.take i).support.Disjoint (p.drop j).support:=by
 rw [List.disjoint_left]
 intro x n m;obtain ⟨a,s,e⟩:=(qz p i (by omega)).mp n
 obtain ⟨b,h,g,d⟩:=(rd p j r).mp m;have k:a=b:=q.getVert_injOn (by change a<=p.length;omega) g (e.trans d.symm)
 omega
def sX {V:Type*} {G:SG V} {u v:V} (p:G.Walk u v)(i j:ℕ) (d:i<=j):G.Walk (p.getVert i) (p.getVert j):=((p.drop i).take (j-i)).copy rfl (by
 rw [Walk.drop_getVert,Nat.add_sub_of_le d])
lemma y2 {V:Type*} {G:SG V} {u v:V} (p:G.Walk u v)(i j:ℕ) (d:i<=j) (e:j<=p.length):(sX p i j d).length=j-i:=by simp only [sX,Walk.length_copy,Walk.take_length,Walk.drop_length];exact min_eq_left (by omega)
lemma aj {V:Type*} {G:SG V} {u v:V} (p:G.Walk u v)(e:p.IsPath) (i j:ℕ)(d:i<=j):(sX p i j d).IsPath:=by simpa only [sX,Walk.isPath_copy] using ((e.drop i).take (j-i))
lemma vo {V:Type*} {G:SG V} {u v x:V} (p:G.Walk u v)(i j:ℕ) (g:i<=j) (l:j<=p.length):x∈(sX p i j g).support↔∃ a,i<=a/\a<=j/\p.getVert a =x:=by
 rw [sX,Walk.support_copy];have e:j-i<=(p.drop i).length:=by rw [Walk.drop_length];omega
 rw [qz (p.drop i) (j-i) e];constructor
 · rintro ⟨a,m,d⟩
   refine ⟨i+a,by omega,by omega,?_⟩
   simpa only [Walk.drop_getVert] using d
 · rintro ⟨a,h,k,d⟩
   refine ⟨a-i,by omega,?_⟩
   simpa only [Walk.drop_getVert,Nat.add_sub_of_le h] using d
def rF {V:Type*} {G:SG V} {v:V} (c:G.Walk v v)(i j:ℕ):G.Walk (c.getVert j) (c.getVert i):=(c.drop j).append (c.take i)
lemma uF {V:Type*} {G:SG V} {v:V} (c:G.Walk v v)(i j:ℕ) (d:i<=c.length):(rF c i j).length=c.length-j+i:=by simp only [rF,Walk.length_append,Walk.drop_length,Walk.take_length,min_eq_left d]
lemma x5 {V:Type*} {G:SG V} {v:V} (c:G.Walk v v)(k:c.IsCycle) (i j:ℕ)(m:i < j) (r:j<=c.length):(rF c i j).IsPath:=by
 apply qr (c.drop j) (c.take i) (k.isPath_drop (by omega)) (k.isPath_take (by omega))
 intro x e h;obtain ⟨a,q,t,d⟩:=(rd c j r).mp e;obtain ⟨b,s,g⟩:=(qz c i (by omega)).mp h
 by_cases n:a=c.length
 · rw [n,Walk.getVert_length] at d;exact d.symm
 · have l:=k.getVert_injOn' (by change a<=c.length-1;omega) (by change b<=c.length-1;omega) (d.trans g.symm)
   omega
lemma xU {V:Type*} {G:SG V} {v x:V} (c:G.Walk v v)(i j:ℕ) (h:i<=c.length) (l:j<=c.length) (k:x∈(rF c i j).support):x∈c.support:=by
 rcases (Walk.mem_support_append_iff (c.drop j) (c.take i)).mp k with e | g
 · obtain ⟨a,_,_,d⟩:=(rd c j l).mp e;exact d ▸ c.getVert_mem_support a
 · obtain ⟨a,_,d⟩:=(qz c i h).mp g;exact d ▸ c.getVert_mem_support a
lemma rA {V:Type*} {G:SG V} {v:V} (c:G.Walk v v)(l:c.IsCycle) (i j a:ℕ)(r:i<=a) (s:a<=j) (t:j < c.length) (w:c.getVert a∈(rF c i j).support):a=i\/a=j:=by
 rcases (Walk.mem_support_append_iff (c.drop j) (c.take i)).mp w with m | k
 · obtain ⟨b,q,x,d⟩:=(rd c j t.le).mp m
   by_cases g:b=c.length
   · rw [g,Walk.getVert_length] at d
     have h:=(l.getVert_endpoint_iff (by omega)).mp d.symm
     left;omega
   · have e:=l.getVert_injOn' (by change b<=c.length-1;omega) (by change a<=c.length-1;omega) d
     right;omega
 · obtain ⟨b,n,d⟩:=(qz c i (by omega)).mp k
   have e:=l.getVert_injOn' (by change b<=c.length-1;omega) (by change a<=c.length-1;omega) d
   left;omega
lemma wj {I V:Type*} [DecidableEq V] (A:FS I)(S:I->FS V) (m:ℕ)(d:∀ i ∈ A,∀ j ∈ A,i≠j->(S i ∩ S j).card<=m):(∑ i ∈ A,(S i).card)<=(A.biUnion S).card+A.card^2*m:=by
 classical
 induction A using Finset.induction_on with
 | empty=> simp
 | @insert i A hi ih=>
  have e:∀ a ∈ A,∀ b ∈ A,a≠b->(S a ∩ S b).card<=m:=by
   intro a y b v q;exact d a (mem_insert_of_mem y) b (mem_insert_of_mem v) q
  have t:=ih e
  have k:(S i ∩ A.biUnion S).card<=A.card*m:=by
   have hsub:S i ∩ A.biUnion S⊆A.biUnion (fun j=>S i ∩ S j) :=by
    intro x w;obtain ⟨s,r⟩ :=mem_inter.mp w;obtain ⟨j,g,n⟩ :=mem_biUnion.mp r;exact mem_biUnion.mpr ⟨j,g,mem_inter.mpr ⟨s,n⟩⟩
   calc
    (S i ∩ A.biUnion S).card<=(A.biUnion (fun j=>S i ∩ S j)).card:=card_le_card hsub
    _<=∑ j ∈ A,(S i ∩ S j).card:=card_biUnion_le
    _<=∑ _j ∈ A,m:=by
     apply sum_le_sum
     intro j g;exact d i (mem_insert_self _ _) j (mem_insert_of_mem g) (fun h=>hi (h.symm ▸ g))
    _=A.card*m:=by simp
  have l:=card_union_add_card_inter (S i) (A.biUnion S);rw [sum_insert hi,biUnion_insert,card_insert_of_notMem hi]
  calc
   (S i).card+ ∑ j ∈ A,(S j).card<=(S i).card+ (A.biUnion S).card+A.card^2*m:=by omega
   _= (S i ∪ A.biUnion S).card+ (S i ∩ A.biUnion S).card+A.card^2*m:=by omega
   _<=(S i ∪ A.biUnion S).card+A.card*m+A.card^2*m:=by omega
   _<=(S i ∪ A.biUnion S).card+ (A.card+1)^2*m:=by
    nlinarith [Nat.zero_le (A.card*m)]
lemma yl {I V:Type*} [Fintype I] [Fintype V] [DecidableEq V] (S:I->FS V) (d m:ℕ)(g:∀ i,d<=(S i).card) (k:Fintype.card V+(Fintype.card I)^2*m < Fintype.card I *d):∃ i j:I,i≠j/\m < (S i ∩ S j).card:=by
 classical
 by_contra! h
 have q:Fintype.card I *d<=∑ i,(S i).card:=by
  calc
   Fintype.card I *d= ∑ _i:I,d:=by simp
   _<=∑ i,(S i).card:=sum_le_sum fun i _=> g i
 have e:=wj univ S m (fun i _ j _ n=> h i j n)
 rw [card_univ] at e;have l:=card_le_univ (univ.biUnion S);omega
lemma vN {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (D d:ℕ)(s:0 < Fintype.card V) (k:Fintype.card V<=D *d) (e:∀ v,d<=G.degree v) (S:FS V)(t:2*S.card<=d) (a:Fin (4*D)->V):∃ i j:Fin (4*D),i≠j/\Fintype.card V/(2* (4*D)^2) < ((G.neighborFinset (a i) ∩ G.neighborFinset (a j)) \ S).card:=by
 classical
 let W (i:Fin (4*D)) :=G.neighborFinset (a i) \ S
 have h (i:Fin (4*D)):d-S.card<=(W i).card:=by
  have r:=e (a i);have hint:(S ∩ G.neighborFinset (a i)).card<=S.card:=card_le_card inter_subset_left;dsimp [W];rw [card_sdiff];rw [G.card_neighborFinset_eq_degree];omega
 have g:Fintype.card V+(4*D)^2* (Fintype.card V/(2* (4*D)^2)) < 4*D* (d-S.card) :=by
  have n:d<=2* (d-S.card) :=by omega
  have hmul:=Nat.mul_le_mul_left (2*D) n;have hdiv:=Nat.div_mul_le_self (Fintype.card V) (2* (4*D)^2);nlinarith
 obtain ⟨i,j,l,q⟩ :=yl W (d-S.card) (Fintype.card V/(2* (4*D)^2)) h (by simpa only [Fintype.card_fin] using g)
 refine ⟨i,j,l,?_⟩
 have m:W i ∩ W j= (G.neighborFinset (a i) ∩ G.neighborFinset (a j)) \ S:=by
  ext v;simp only [W,mem_inter,mem_sdiff];tauto
 rwa [m] at q
lemma wC {V:Type*} [Fintype V] (D L d:ℕ)(N:0 < L) (U:0 < Fintype.card V) (n:Fintype.card V<=D *d) (S:Fin (2*D*L)->FS V) (t:∀ i,d<=(S i).card):∃ (X:FS (Fin (2*D*L))) (W:FS V),L<=X.card/\Fintype.card V<=2 *D*2^ (2*D*L)*W.card/\∀ i ∈ X,∀ v ∈ W,v∈S i:=by
 classical
 let I :=Fin (2*D*L);let e (v:V):FS I :=univ.filter (fun i=>v∈S i)
 let A :=univ.filter (fun v=>L<=(e v).card)
 have z:(∑ i:I,(S i).card)=∑ v:V,(e v).card:=by
  have Q (i:I):(S i).card= ∑ v:V,if v∈S i then 1 else 0 :=by simp
  have T (v:V):(e v).card= ∑ i:I,if v∈S i then 1 else 0 :=by
   simp [e]
  simp_rw [Q,T];exact sum_comm
 have q:(2*D*L)*d<=∑ v:V,(e v).card:=by
  rw [<- z]
  calc
   (2*D*L)*d= ∑ _i:I,d:=by simp [I]
   _<=∑ i:I,(S i).card:=sum_le_sum fun i _=> t i
 have m (v:V):(e v).card<=L+if v∈A then 2 *D*L else 0 :=by
  by_cases s:v∈A
  · rw [if_pos s];have h :=card_le_univ (e v);simp only [I,Fintype.card_fin] at h;omega
  · rw [if_neg s]
    have h:¬ L<=(e v).card:=by simpa only [A,mem_filter,mem_univ,true_and] using s
    omega
 have l:(∑ v:V,(e v).card)<=L*Fintype.card V+(2*D*L)*A.card:=by
  calc
   (∑ v:V,(e v).card)<=∑ v:V,(L+if v∈A then 2 *D*L else 0):=sum_le_sum fun v _=> m v
   _=L*Fintype.card V+(2*D*L)*A.card:=by
    simp [sum_add_distrib,Nat.mul_comm]
 have R:Fintype.card V<=2 *D*A.card:=by
  have k:=Nat.mul_le_mul_left (2*L) n
  have h:L*Fintype.card V<=L*(2*D*A.card) :=by
   nlinarith only [q,l,k]
  exact (mul_le_mul_iff_right₀ N).mp h
 let g (X:FS I) :=A.filter (fun v=>e v =X)
 obtain ⟨X,_,C⟩ :=exists_max_image (univ:FS (FS I)) (fun X=>(g X).card) univ_nonempty
 have w:A.card= ∑ X:FS I,(g X).card:= card_eq_sum_card_fiberwise (fun v _=> mem_univ (e v))
 have r:A.card<=2^ (2*D*L)*(g X).card:=by
  rw [w]
  calc
   (∑ Y:FS I,(g Y).card)<=∑ _Y:FS I,(g X).card:= sum_le_sum fun Y _=> C Y (mem_univ Y)
   _=2^ (2*D*L)*(g X).card:=by simp [I]
 have j:Fintype.card V<=2 *D*2^ (2*D*L)*(g X).card:=by
  calc
   Fintype.card V<=2 *D*A.card:=R
   _<=2*D* (2^ (2*D*L)*(g X).card) :=Nat.mul_le_mul_left _ r
   _=2*D*2^ (2*D*L)*(g X).card:=by ring
 have y:(g X).Nonempty:=by
  apply card_pos.mp;by_contra h;have P:(g X).card=0:=by omega
  rw [P,mul_zero] at j;omega
 obtain ⟨v,s⟩ :=y;have F:= (mem_filter.mp s).1;have H:= (mem_filter.mp s).2
 have M:L<=X.card:=by
  rw [<- H];exact (mem_filter.mp F).2
 refine ⟨X,g X,M,j,?_⟩
 intro i K v s;have x:= (mem_filter.mp s).2;have J:i∈e v :=by rw [x];exact K
 exact (mem_filter.mp J).2
def xW {V:Type*} [DecidableEq V] {G:SG V} {z:V} (c:G.Walk z z)(W:FS V):FS ℕ:=(range c.length).filter (fun i=>c.getVert i∈W)
lemma ae {V:Type*} [DecidableEq V] {G:SG V} {z:V} (c:G.Walk z z)(m:c.IsCycle) (W:FS V)(l:∀ x ∈ W,x∈c.support):(xW c W).image c.getVert=W:=by
 ext x;constructor
 · intro g;obtain ⟨i,k,d⟩ :=mem_image.mp g;exact d ▸ (mem_filter.mp k).2
 · intro g
   obtain ⟨i,d,k⟩ :=Walk.mem_support_iff_exists_getVert.mp (l x g);by_cases j:i=c.length
   · have e:z=x:=by simpa only [j,Walk.getVert_length] using d
     apply mem_image.mpr;refine ⟨0,mem_filter.mpr ⟨mem_range.mpr (by have h :=m.three_le_length;omega),?_⟩,?_⟩
     · simpa only [Walk.getVert_zero,e] using g
     · simpa only [Walk.getVert_zero] using e
   · exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_range.mpr (by omega),d ▸ g⟩,d⟩
lemma ax {V:Type*} [DecidableEq V] {G:SG V} {z:V} (c:G.Walk z z)(h:c.IsCycle) (W:FS V)(m:∀ x ∈ W,x∈c.support):(xW c W).card=W.card:=by
 have e:Set.InjOn c.getVert (xW c W:Set ℕ) :=by
  intro i l j n g;have k:=mem_range.mp (mem_filter.mp l).1;have q:=mem_range.mp (mem_filter.mp n).1;exact h.getVert_injOn' (by change i<=c.length-1;omega) (by change j<=c.length-1;omega) g
 have d:=card_image_of_injOn e;rw [ae c h W m] at d;exact d.symm
lemma vC {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] {z:V} (c:G.Walk z z)(N:c.IsCycle) (D L d:ℕ)(M:0 < L) (l:Fintype.card V<=D *d) (e:∀ v,d<=G.degree v) (t:4*D*L<=c.length):∃ (A:FS ℕ)(W:FS V),A.card=L/\(∀ i ∈ A,i < 4*D*L/\Even i)/\(A.image c.getVert).card=L/\Fintype.card V<=2 *D*2^ (2*D*L)*W.card/\∀ i ∈ A,∀ w ∈ W,G.Adj (c.getVert i) w :=by
 classical
 obtain ⟨I,W,U,T,g⟩ :=wC D L d M (Fintype.card_pos_iff.mpr ⟨z⟩) l (fun i=>G.neighborFinset (c.getVert (2*i.val))) (fun i=>by simpa only [G.card_neighborFinset_eq_degree] using e (c.getVert (2*i.val)))
 obtain ⟨J,q,H⟩ :=exists_subset_card_eq U
 let f:Fin (2*D*L) ↪ ℕ:=
  ⟨fun i=>2 *i.val,by
   intro i j h;change 2 *i.val=2*j.val at h;exact Fin.ext (by omega)⟩
 let A :=J.map f;have y:A.card=L:=by simpa only [A,card_map] using H
 have k (i:ℕ) (m:i∈A):i < 4*D*L/\Even i :=by
  obtain ⟨a,C,rfl⟩ :=mem_map.mp m;have s:=a.isLt;change 2 *a.val < 4*D*L/\Even (2*a.val);have x:=Nat.mul_lt_mul_of_pos_left s (by decide:0 < 2)
  have K:2* (2*D*L)=4*D*L:=by ring
  rw [K] at x;exact ⟨x,⟨a.val,by omega⟩⟩
 have n:Set.InjOn c.getVert (A:Set ℕ) :=by
  intro i m j F r;have R:= (k i m).1;have Q:= (k j F).1;exact N.getVert_injOn' (by change i<=c.length-1;omega) (by change j<=c.length-1;omega) r
 refine ⟨A,W,y,k,(card_image_of_injOn n).trans y,T,?_⟩
 intro i m w P;obtain ⟨a,C,rfl⟩ :=mem_map.mp m;exact (G.mem_neighborFinset _ _).mp (g a (q C) w P)
lemma xB {V:Type*} [DecidableEq V] {G:SG V} {z:V} (c:G.Walk z z)(W:FS V) (N K Q M:ℕ)(t:M<=c.length) (g:N<=K*W.card) (w:2*K* (Q+M+1)<=N) (m:(W \ c.support.toFinset).card < Q):∃ U:FS V,U⊆W/\(∀ x ∈ U,x∈c.support)/\(∀ i,i<=M->c.getVert i ∉ U)/\N<=2*K*U.card:=by
 let P:=(c.take M).support.toFinset;let E :=W \ c.support.toFinset;let U:=(W ∩ c.support.toFinset) \ P
 have D:P.card<=M+1:=by
  have h :=List.toFinset_card_le (c.take M).support;simpa only [Walk.length_support,Walk.take_length,min_eq_left t] using h
 have d:W⊆U ∪ E ∪ P:=by
  intro x k;by_cases j:x∈P
  · exact mem_union_right _ j
  by_cases n:x∈c.support.toFinset
  · exact mem_union_left _ (mem_union_left _ (mem_sdiff.mpr ⟨mem_inter.mpr ⟨k,n⟩,j⟩))
  · exact mem_union_left _ (mem_union_right _ (mem_sdiff.mpr ⟨k,n⟩))
 have e:W.card<=U.card+Q+M+1:=by
  have q:=card_le_card d;have r:=card_union_le (U ∪ E) P;have s:=card_union_le U E;change E.card < Q at m;omega
 refine ⟨U,(sdiff_subset).trans inter_subset_left,?_,?_,?_⟩
 · intro x y;exact List.mem_toFinset.mp (mem_inter.mp (mem_sdiff.mp y).1).2
 · intro i v l;have C:c.getVert i∈P :=List.mem_toFinset.mpr ((qz c M t).mpr ⟨i,v,rfl⟩);exact (mem_sdiff.mp l).2 C
 · have hmul:=Nat.mul_le_mul_left K e;nlinarith only [g,w,hmul]
lemma xa (S:FS ℕ)(N Q:ℕ) (q:0 < Q) (v:∀ i ∈ S,i < N) (y:2* (N/Q+1) < S.card):∃ i ∈ S,∃ j ∈ S,i < j/\j < i+Q/\i%2=j%2:=by
 let f (i:ℕ):=(i/Q,i%2);let T :=range (N/Q+1) ×ˢ range 2;have t:T.card < S.card:=by simpa only [T,card_product,card_range,Nat.mul_comm] using y
 have x:∀ i ∈ S,f i∈T:=by
  intro i k;apply mem_product.mpr;refine ⟨mem_range.mpr ?_,mem_range.mpr (Nat.mod_lt _ (by decide))⟩
  exact Nat.lt_succ_of_le (Nat.div_le_div_right (v i k).le)
 obtain ⟨i,k,j,n,g,h⟩ :=exists_ne_map_eq_of_card_lt_of_maps_to t x;have hdiv:i/Q=j/Q:=CA Prod.fst h;have e:i%2=j%2:=CA Prod.snd h
 have d:j < i+Q/\i < j+Q:=by
  have m:=Nat.div_add_mod i Q;have w:=Nat.div_add_mod j Q;have r:=Nat.mod_lt i q;have s:=Nat.mod_lt j q;rw [hdiv] at m;omega
 rcases lt_or_gt_of_ne g with g | l
 · exact ⟨i,k,j,n,g,d.1,e⟩
 · exact ⟨j,n,i,k,l,d.2,e.symm⟩
lemma th (N K:ℕ)(d:0 < K) (e:4*K<=N):2* (N/ (4*K)+1)<=N/K:=by
 have g:1<=N/ (4*K):=(Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
 have hmul:=Nat.div_mul_le_self N (4*K)
 have hdiv:4* (N/ (4*K))<=N/K:=by
  apply (Nat.le_div_iff_mul_le d).mpr;nlinarith only [hmul]
 omega
lemma vE {V:Type*} {G:SG V} {u v:V} (p:G.Walk u v)(W:FS V) (q:∀ x ∈ W,x∈p.support)(N K:ℕ) (I:0 < K) (L:4*K<=N) (z:p.length < N) (l:N/K < W.card):∃ i j:ℕ,i < j/\j<=p.length/\j < i+4*K/\i%2=j%2/\p.getVert i∈W/\p.getVert j∈W :=by
 classical
 let S :=W.image (fun x=>p.support.idxOf x)
 have g (x:V) (k:x∈W):p.support.idxOf x<=p.length:=by
  have h :=List.idxOf_lt_length_of_mem (q x k);rw [Walk.length_support] at h;omega
 have s:Set.InjOn (fun x=>p.support.idxOf x) (W:Set V) :=by
  intro x k y r H;have h :=CA p.getVert H;simpa only [p.getVert_support_idxOf (q x k),p.getVert_support_idxOf (q y r)] using h
 have e:S.card=W.card:=card_image_of_injOn s
 have M (i:ℕ) (t:i∈S):i < N:=by
  obtain ⟨x,k,rfl⟩ :=mem_image.mp t;exact (g x k).trans_lt z
 have P:2* (N/ (4*K)+1) < S.card:=by
  rw [e];exact (th N K I L).trans_lt l
 obtain ⟨i,t,j,J,D,d,n⟩:=xa S N (4*K) (by omega) M P
 obtain ⟨x,k,C⟩ :=mem_image.mp t;obtain ⟨y,r,m⟩ :=mem_image.mp J;have w:p.getVert i =x:=by rw [<- C];exact p.getVert_support_idxOf (q x k)
 have F:p.getVert j =y:=by rw [<- m];exact p.getVert_support_idxOf (q y r)
 refine ⟨i,j,D,?_,d,n,w ▸ k,F ▸ r⟩;rw [<- m];exact g y r
lemma yJ (S:FS ℕ)(N Q L:ℕ) (r:0 < Q) (w:∀ i ∈ S,i < N) (y:2* (N/Q+1)*(L-1) < S.card):∃ T:FS ℕ,T⊆S/\T.card=L/\∀ i ∈ T,∀ j ∈ T,i%2=j%2/\j < i+Q:=by
 let f (i:ℕ):=(i/Q,i%2);let B :=range (N/Q+1) ×ˢ range 2
 have x:∀ i ∈ S,f i∈B:=by
  intro i h;apply mem_product.mpr;refine ⟨mem_range.mpr ?_,mem_range.mpr (Nat.mod_lt _ (by decide))⟩
  exact Nat.lt_succ_of_le (Nat.div_le_div_right (w i h).le)
 have g:B.card* (L-1) < S.card:=by
  simpa only [B,card_product,card_range,Nat.mul_comm (N/Q+1) 2] using y
 obtain ⟨b,_,C⟩ :=exists_lt_card_fiber_of_mul_lt_card_of_maps_to x g
 obtain ⟨T,l,m⟩ :=exists_subset_card_eq (show L<=(S.filter (fun i=>f i=b)).card by
  omega)
 refine ⟨T,l.trans (filter_subset _ _),m,?_⟩
 intro i h j t;have q:= (mem_filter.mp (l h)).2;have n:= (mem_filter.mp (l t)).2;have e:=q.trans n.symm;have hdiv:i/Q=j/Q:=CA Prod.fst e;have d:i%2=j%2:=CA Prod.snd e;refine ⟨d,?_⟩;have k:=Nat.div_add_mod i Q;have v:=Nat.div_add_mod j Q;have s:=Nat.mod_lt i r;have z:=Nat.mod_lt j r;rw [hdiv] at k;omega
lemma yL (N K L:ℕ)(h:0 < K) (i:0 < L) (j:8*K*L<=N):2* (N/ (8*K*L)+1)*(L-1) < N/ (2*K) :=by
 have g:0 < 8*K*L:=by positivity
 have k:1<=N/ (8*K*L):=(Nat.le_div_iff_mul_le g).mpr (by omega)
 have hmul:=Nat.div_mul_le_self N (8*K*L)
 have hdiv:4*L* (N/ (8*K*L))<=N/ (2*K) :=by
  apply (Nat.le_div_iff_mul_le (by omega)).mpr
  nlinarith only [hmul]
 have hsub:L-1+1=L:=by omega
 have d:0<=(N/ (8*K*L)-1)*(L-1) :=Nat.zero_le _;have e:N/ (8*K*L)-1+1=N/ (8*K*L) :=by omega
 nlinarith
lemma ys {V:Type*} {G:SG V} {z:V} (c:G.Walk z z)(F:c.IsCycle) (W:FS V)(w:∀ x ∈ W,x∈c.support) (M N K L:ℕ)(v:0 < K) (y:0 < L) (C:8*K*L<=N) (r:c.length<=N) (g:N<=2*K*W.card) (m:∀ i,i<=M->c.getVert i ∉ W):∃ B:FS ℕ,B.card=L/\(∀ i ∈ B,M < i/\i < c.length/\c.getVert i∈W)/\∀ i ∈ B,∀ j ∈ B,i%2=j%2/\j < i+8*K*L:=by
 classical
 let S :=xW c W;have d:S.card=W.card:=ax c F W w;have D (i:ℕ) (n:i∈S):i < N:= (mem_range.mp (mem_filter.mp n).1).trans_le r
 have hdiv:N/ (2*K)<=W.card:=by
  have h :=Nat.div_le_div_right g (c:=2*K);simpa only [Nat.mul_div_cancel_left W.card (by omega:0 < 2*K)] using h
 have e:2* (N/ (8*K*L)+1)*(L-1) < S.card:=by
  rw [d];exact (yL N K L v y C).trans_le hdiv
 obtain ⟨B,q,t,k⟩ :=yJ S N (8*K*L) L (by positivity) D e
 refine ⟨B,t,?_,k⟩
 intro i n;obtain ⟨s,l⟩ :=mem_filter.mp (q n);exact ⟨by by_contra h;exact m i (by omega) l,mem_range.mp s,l⟩
lemma vx {V:Type*} [DecidableEq V] {G:SG V} {w:V} (c:G.Walk w w)(C:c.IsCycle) (A:FS ℕ)(P:2<=A.card) (M:ℕ)(Q:M < c.length) (r:∀ i ∈ A,i<=M) (n:∀ i ∈ A,∀ j ∈ A,i%2=j%2) (Y:FS V)(L:∀ y ∈ Y,y ∉ c.support):∃ u ∈ A.image c.getVert,∃ v ∈ A.image c.getVert,u≠v/\∃ p:G.Walk u v,p.IsPath/\c.length<=p.length+M/\p.length%2=c.length%2/\∀ z ∈ p.support,z∈A.image c.getVert ∪ Y->z=u\/z=v:=by
 classical
 have d:A.Nonempty:=card_pos.mp (by omega)
 let i :=A.min' d;let j :=A.max' d;have l:i∈A:=A.min'_mem d;have e:j∈A:=A.max'_mem d;have H:i < j:=A.min'_lt_max'_of_card (by omega)
 have N:=r i l;have K:=r j e
 have F:c.getVert j≠c.getVert i :=by
  intro I;have h :=C.getVert_injOn' (by change j<=c.length-1;omega) (by change i<=c.length-1;omega) I
  omega
 refine ⟨c.getVert j,mem_image.mpr ⟨j,e,rfl⟩,c.getVert i,mem_image.mpr ⟨i,l,rfl⟩,F,rF c i j,x5 c C i j H (by omega),?_,?_,?_⟩
 · rw [uF c i j (by omega)]
   omega
 · rw [uF c i j (by omega)]
   have h :=n i l j e;omega
 · intro z J D
   rcases mem_union.mp D with s | x
   · obtain ⟨a,q,k⟩ :=mem_image.mp s
     have t:i<=a:=A.min'_le a q;have g:a<=j:=A.le_max' a q;have m:c.getVert a∈(rF c i j).support:=k ▸ J
     rcases rA c C i j a t g (by omega) m
      with hai | g
     · right;rw [<- k,hai]
     · left;rw [<- k,g]
   · exact (L z x (xU c i j (by omega) (by omega) J)).elim
lemma vb {V:Type*} {G:SG V} {z:V} (c:G.Walk z z)(D:c.IsCycle) (u v w y w':ℕ)(h0:u < v) (W:v < w) (h1:w < y) (N:y < w') (I:w' < c.length) (x:G.Adj (c.getVert u) (c.getVert y)) (C:G.Adj (c.getVert v) (c.getVert y)):∃ p:G.Walk (c.getVert w') (c.getVert w),p.IsPath/\p.length+v+w'=c.length+u+w+2/\(∀ a,u < a->a < v->c.getVert a ∉ p.support)/\(∀ a,w < a->a < w'->a≠y->c.getVert a ∉ p.support) :=by
 let q :=rF c u w';let r :=sX c v w (by omega)
 have X:q.IsPath:=x5 c D u w' (by omega) I.le
 have Y:r.IsPath:=by
  simp only [r,sX,Walk.isPath_copy];exact (D.isPath_drop (by omega:0 < v)).take (w-v)
 have d (a:ℕ) (l:u < a) (m:a < w'):c.getVert a ∉ q.support:=by
  intro j;have h :=rA c D u w' a l.le m.le I j;omega
 have g (a:V) (j:a∈r.support):∃ k,v<=k/\k<=w/\c.getVert k =a:= (vo c v w (by omega) (by omega)).mp j
 have L:c.getVert y ∉ q.support:=d y (by omega) N
 have M:c.getVert y ∉ r.support:=by
  intro hy;obtain ⟨k,H,J,Q⟩ :=g _ hy;have h :=D.getVert_injOn' (by change k<=c.length-1;omega) (by change y<=c.length-1;omega) Q
  omega
 have P:q.support.Disjoint r.support:=by
  rw [List.disjoint_left]
  intro a n s;obtain ⟨k,H,J,F⟩ :=g a s;exact d k (by omega) (by omega) (F ▸ n)
 let p:=(q.concat x).append (Walk.cons C.symm r)
 have hp:p.IsPath:=by
  apply qr (q.concat x) (Walk.cons C.symm r) (X.concat L x) ((Walk.cons_isPath_iff _ _).mpr ⟨Y,M⟩)
  intro a j R;simp only [Walk.support_concat,List.mem_append,List.mem_singleton] at j;simp only [Walk.support_cons,List.mem_cons] at R;rcases j with n | e
  · rcases R with e | s
    · exact e
    · exact (P n s).elim
  · exact e
 have i (a:ℕ) (l:u < a) (m:a < w') (K:¬ (v<=a/\a<=w)) (e:a≠y):c.getVert a ∉ p.support:=by
  intro j;rcases (Walk.mem_support_append_iff (q.concat x) (Walk.cons C.symm r)).mp j with j | j
  · simp only [Walk.support_concat,List.mem_append,List.mem_singleton] at j
    rcases j with n | t
    · exact d a l m n
    · exact e (D.getVert_injOn' (by change a<=c.length-1;omega) (by change y<=c.length-1;omega) t)
  · simp only [Walk.support_cons,List.mem_cons] at j
    rcases j with t | s
    · exact e (D.getVert_injOn' (by change a<=c.length-1;omega) (by change y<=c.length-1;omega) t)
    · obtain ⟨k,H,J,F⟩ :=g _ s
      have T:=D.getVert_injOn' (by change k<=c.length-1;omega) (by change a<=c.length-1;omega) F
      exact K (by omega)
 refine ⟨p,hp,?_,?_,?_⟩
 · simp only [p,q,r,Walk.length_append,Walk.length_concat,Walk.length_cons,uF c u w' (by omega),y2 c v w (by omega) (by omega)]
   omega
 · intro a l U;exact i a l (by omega) (by omega) (by omega)
 · intro a Z m e;exact i a (by omega) m (by omega) e
lemma vg {V:Type*} [DecidableEq V] {G:SG V} {z:V} (c:G.Walk z z)(hc:c.IsCycle) (A B:FS ℕ)(Q M H:ℕ) (hQ:0 < Q) (hA:A.card=Q+2) (hB:B.card=Q+3) (hM:M < c.length) (T:∀ a ∈ A,a<=M) (I:∀ b ∈ B,M < b/\b < c.length) (K:∀ a ∈ A,∀ b ∈ A,a%2=b%2) (P:∀ a ∈ B,∀ b ∈ B,a%2=b%2) (L:∀ a ∈ B,∀ b ∈ B,b < a+H) (d:∀ a ∈ A,∀ b ∈ B,G.Adj (c.getVert a) (c.getVert b)):∃ X Y:FS V,X.card=Q+2/\Y.card=Q/\Disjoint X Y/\(∀ x ∈ X,∀ y ∈ Y,G.Adj x y)/\∃ u ∈ X,∃ v ∈ X,u≠v/\∃ p:G.Walk u v,p.IsPath/\c.length<=p.length+M+H/\p.length%2=c.length%2/\∀ w ∈ p.support,w∈X ∪ Y->w=u\/w=v:=by
 classical
 have F:A.Nonempty:=card_pos.mp (by omega)
 have D:B.Nonempty:=card_pos.mp (by omega)
 let a :=A.min' F;let b :=A.max' F;let w :=B.min' D;let w':=B.max' D;have ha:a∈A:=A.min'_mem F;have hb:b∈A:=A.max'_mem F;have hw:w∈B:=B.min'_mem D;have n:w'∈B:=B.max'_mem D;have h6:a < b:=A.min'_lt_max'_of_card (by omega)
 have a6:w < w':=B.min'_lt_max'_of_card (by omega)
 have q:(B \ {w,w'}).Nonempty:=by
  apply card_pos.mp
  have h7:({w,w'}:FS ℕ).card<=2:= (card_insert_le _ _).trans (by simp)
  have hint:=card_le_card (show ({w,w'}:FS ℕ) ∩ B⊆{w,w'} from inter_subset_left);rw [card_sdiff];omega
 obtain ⟨y,hy⟩ :=q;have l:= (mem_sdiff.mp hy).1;have h4:y≠w:=fun h=>(mem_sdiff.mp hy).2 (by simp [h])
 have J:y≠w':=fun h=>(mem_sdiff.mp hy).2 (by simp [h])
 have b2:w < y:=lt_of_le_of_ne (B.min'_le y l) h4.symm;have Z:y < w':=lt_of_le_of_ne (B.le_max' y l) J;have c3:=T b hb;have c0:=T a ha;have c1:= (I w hw).1;have W:= (I w' n).2;have C (i:ℕ) (m:i∈A):i < c.length:= (T i m).trans_lt hM
 have r:Set.InjOn c.getVert (A:Set ℕ) :=by
  intro i m j hj U;exact hc.getVert_injOn' (by change i<=c.length-1;have h :=C i m;omega) (by change j<=c.length-1;have h :=C j hj;omega) U
 have g:Set.InjOn c.getVert (B:Set ℕ) :=by
  intro i m j hj U;exact hc.getVert_injOn' (by change i<=c.length-1;have h:=(I i m).2;omega) (by change j<=c.length-1;have h:=(I j hj).2;omega) U
 have h5:c.getVert a≠c.getVert b :=fun h=>(ne_of_lt h6) (r ha hb h)
 have h3:c.getVert w≠c.getVert y :=fun h=>h4 (g hw l h).symm
 have R:c.getVert w'≠c.getVert y :=fun h=>J (g n l h).symm
 let X:=(B.image c.getVert).erase (c.getVert y);let Y:=((A.image c.getVert).erase (c.getVert a)).erase (c.getVert b)
 have hX:X.card=Q+2:=by
  dsimp [X];rw [card_erase_of_mem (mem_image.mpr ⟨y,l,rfl⟩),card_image_of_injOn g,hB];omega
 have hY:Y.card=Q:=by
  dsimp [Y];rw [card_erase_of_mem (mem_erase.mpr ⟨h5.symm,mem_image.mpr ⟨b,hb,rfl⟩⟩),card_erase_of_mem (mem_image.mpr ⟨a,ha,rfl⟩),card_image_of_injOn r,hA];omega
 have e (x:V) (hx:x∈X) (v:V) (hv:v∈Y):G.Adj x v:=by
  obtain ⟨i,m,rfl⟩ :=mem_image.mp (mem_of_mem_erase hx);obtain ⟨j,hj,rfl⟩ :=mem_image.mp (mem_of_mem_erase (mem_of_mem_erase hv));exact (d j hj i m).symm
 have a2:Disjoint X Y:=by
  rw [Finset.disjoint_left]
  intro x hx hy;exact (e x hx x hy).ne rfl
 obtain ⟨p,hp,b4,s,t⟩ :=vb c hc a b w y w' h6 (by omega) b2 Z W (d a ha y l) (d b hb y l)
 refine ⟨X,Y,hX,hY,a2,e,c.getVert w',mem_erase.mpr ⟨R,mem_image.mpr ⟨w',n,rfl⟩⟩,c.getVert w,mem_erase.mpr ⟨h3,mem_image.mpr ⟨w,hw,rfl⟩⟩,(fun h=>(ne_of_lt a6) (g n hw h).symm),p,hp,?_,?_,?_⟩
 · have hd:=L w hw w' n;omega
 · have b3:=K a ha b hb;have b7:=P w hw w' n;omega
 · intro v hv h1
   rcases mem_union.mp h1 with h2 | N
   · have h9:= (mem_erase.mp h2).1
     obtain ⟨i,m,k⟩ :=mem_image.mp (mem_of_mem_erase h2);by_cases b1:i=w
     · right;rw [<- k,b1]
     by_cases h0:i=w'
     · left;rw [<- k,h0]
     have b6:w<=i:=B.min'_le i m;have b9:i<=w':=B.le_max' i m;have v4:i≠y:=fun h=>h9 (by rw [<- k,h])
     exact (t i (by omega) (by omega) v4 (k ▸ hv)).elim
   · have h8:= (mem_erase.mp N).1
     have b0:= (mem_erase.mp (mem_of_mem_erase N)).1;obtain ⟨i,m,k⟩ :=mem_image.mp (mem_of_mem_erase (mem_of_mem_erase N));have c5:a<=i:=A.min'_le i m;have c2:i<=b:=A.le_max' i m;have c4:i≠a:=fun h=>b0 (by rw [<- k,h])
     have b8:i≠b:=fun h=>h8 (by rw [<- k,h])
     exact (s i (by omega) (by omega) (k ▸ hv)).elim
def rR (D Q:ℕ) :=4*D* (Q+2)
def rl (D Q:ℕ) :=2*D*2^ (2*D* (Q+2))
def sd (D Q:ℕ) :=8*rl D Q* (Q+3)
lemma tl {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] {z:V} (c:G.Walk z z)(hc:c.IsCycle) (D d Q:ℕ)(hD:0 < D) (hQ:0 < Q) (F:Fintype.card V<=D *d) (q:∀ v,d<=G.degree v) (l:rR D Q < c.length) (t:2*rl D Q* (Q+rR D Q+1)<=Fintype.card V) (r:sd D Q<=Fintype.card V):∃ X Y:FS V,X.card=Q+2/\Y.card=Q/\Disjoint X Y/\(∀ x ∈ X,∀ y ∈ Y,G.Adj x y)/\∃ u ∈ X,∃ v ∈ X,u≠v/\∃ p:G.Walk u v,p.IsPath/\c.length<=p.length+rR D Q+sd D Q/\p.length%2=c.length%2/\∀ w ∈ p.support,w∈X ∪ Y->w=u\/w=v:=by
 classical
 let M :=rR D Q;let K :=rl D Q;let H :=sd D Q;obtain ⟨A,W,hA,Z,h6,C,e⟩ :=vC G c hc D (Q+2) d (by omega) F q l.le
 have h0 (i:ℕ) (n:i∈A):i<=M:= (Z i n).1.le
 have m (i:ℕ) (n:i∈A) (j:ℕ) (s:j∈A):i%2=j%2:=by
  have b0:=Nat.even_iff.mp (Z i n).2;have a6:=Nat.even_iff.mp (Z j s).2;omega
 let E :=W \ c.support.toFinset;by_cases J:Q<=E.card
 · obtain ⟨Y,h1,hY⟩ :=exists_subset_card_eq J
   have h7:Y⊆W:=h1.trans sdiff_subset
   have P (y:V) (hy:y∈Y):y ∉ c.support:=by
    intro h2;exact (mem_sdiff.mp (h1 hy)).2 (List.mem_toFinset.mpr h2)
   let X :=A.image c.getVert
   have g (x:V) (hx:x∈X) (y:V) (hy:y∈Y):G.Adj x y:=by
    obtain ⟨i,n,rfl⟩ :=mem_image.mp hx;exact e i n y (h7 hy)
   have h9:Disjoint X Y:=by
    rw [Finset.disjoint_left]
    intro x hx hy;exact (g x hx x hy).ne rfl
   obtain ⟨u,hu,v,hv,h4,p,hp,a2,R,N⟩:=vx c hc A (by omega) M l h0 m Y P
   exact ⟨X,Y,h6,hY,h9,g,u,hu,v,hv,h4,p,hp,by omega,R,N⟩
 · have hK:0 < K:=by dsimp [K,rl];positivity
   obtain ⟨U,v4,h8,T,I⟩ :=xB c W (Fintype.card V) K Q M l.le C t (Nat.lt_of_not_ge J)
   have h3:c.length<=Fintype.card V :=by
    have h :=hc.isPath_tail.length_lt;rw [Walk.length_tail] at h;have h5:=hc.three_le_length;omega
   obtain ⟨B,hB,L,k⟩ :=ys c hc U h8 M (Fintype.card V) K (Q+3) hK (by omega) r h3 I T
   have g (i:ℕ) (n:i∈A) (j:ℕ) (s:j∈B):G.Adj (c.getVert i) (c.getVert j) :=e i n _ (v4 (L j s).2.2);exact vg c hc A B Q M H hQ hA hB l h0 (fun j s=> ⟨(L j s).1,(L j s).2.1⟩) m (fun i n j s=> (k i n j s).1) (fun i n j s=> (k i n j s).2) g
lemma zg {V:Type*} {G:SG V} {u v:V} (p:G.Walk u v)(w:p.IsPath) (i j:ℕ)(s:i < j) (y:j<=p.length) (x:V)(F:x ∉ p.support) (r:G.Adj (p.getVert i) x) (C:G.Adj (p.getVert j) x):∃ q:G.Walk u v,q.IsPath/\q.length+j=p.length+i+2/\∀ z ∈ q.support,z∈p.support\/z=x:=by
 have D:i<=p.length:=s.le.trans y
 have l (z:V) (e:z∈(p.take i).support):z∈p.support:=by
  obtain ⟨a,_,n⟩:=(qz p i D).mp e;exact n ▸ p.getVert_mem_support a
 have d (z:V) (e:z∈(p.drop j).support):z∈p.support:=by
  obtain ⟨a,_,_,n⟩:=(rd p j y).mp e;exact n ▸ p.getVert_mem_support a
 let a:G.Walk u x:= (p.take i).concat r;let b:G.Walk x v:=Walk.cons C.symm (p.drop j);have I:a.IsPath:= (w.take i).concat (fun h=>F (l x h)) r
 have H:b.IsPath:= (Walk.cons_isPath_iff _ _).mpr ⟨w.drop j,fun h=>F (d x h)⟩
 have t:(a.append b).IsPath:=by
  apply qr a b I H
  intro z k g;simp only [a,Walk.support_concat,List.mem_append,List.mem_singleton] at k;simp only [b,Walk.support_cons,List.mem_cons] at g;rcases k with k | m
  · rcases g with m | g
    · exact m
    · exact ((vJ p w i j s y) k g).elim
  · exact m
 refine ⟨a.append b,t,?_,?_⟩
 · simp only [a,b,Walk.length_append,Walk.length_concat,Walk.length_cons,Walk.take_length,min_eq_left D,Walk.drop_length];omega
 · intro z e
   rcases (Walk.mem_support_append_iff a b).mp e with e | e
   · simp only [a,Walk.support_concat,List.mem_append,List.mem_singleton] at e;exact e.elim (fun h=>Or.inl (l z h)) Or.inr
   · simp only [b,Walk.support_cons,List.mem_cons] at e;exact e.elim Or.inr (fun h=>Or.inl (d z h))
lemma v7 {V:Type*} {G:SG V} {u v:V} (p:G.Walk u v)(n:p.IsPath) (i j:ℕ)(l:i+4<=j) (s:j<=p.length) (g:i%2=j%2) (x:V)(r:x ∉ p.support) (d:G.Adj (p.getVert i) x) (e:G.Adj (p.getVert j) x):∃ q:G.Walk u v,q.IsPath/\q.length < p.length/\p.length<=q.length+ (j-i)/\q.length%2=p.length%2/\∀ z ∈ q.support,z∈p.support\/z=x:=by
 obtain ⟨q,m,h,k⟩ :=zg p n i j (by omega) s x r d e
 exact ⟨q,m,by omega,by omega,by omega,k⟩
lemma zm {V:Type*} {G:SG V} {u v:V} (p:G.Walk u v)(H:p.IsPath) (i i' j j':ℕ)(X:i < i') (w:i'<=j) (L:j < j') (D:j'<=p.length) (h:G.Adj (p.getVert i) (p.getVert j)) (m:G.Adj (p.getVert i') (p.getVert j')):∃ q:G.Walk u v,q.IsPath/\q.length+i'+j'=p.length+i+j+2/\∀ z ∈ q.support,z∈p.support:=by
 have K:i<=p.length:=by omega
 have P:i'<=p.length:=by omega
 have J:j<=p.length:=by omega
 let a:=(p.take i).concat h;let b:=(sX p i' j w).reverse;let c :=Walk.cons m (p.drop j')
 have s (z:V) (t:z∈b.support):∃ k,i'<=k/\k<=j/\p.getVert k =z:=by
  apply (vo p i' j w J).mp;simpa only [b,Walk.support_reverse,List.mem_reverse] using t
 have ha:a.IsPath:=by
  apply (H.take i).concat
  intro t;obtain ⟨k,I,N⟩:=(qz p i K).mp t;have T:=H.getVert_injOn (by change k<=p.length;omega) J N
  omega
 have Z:b.IsPath:= (aj p H i' j w).reverse
 have Q:(a.append b).IsPath:=by
  apply qr a b ha Z
  intro z g y;simp only [a,Walk.support_concat,List.mem_append,List.mem_singleton] at g;rcases g with g | C
  · obtain ⟨k,I,d⟩:=(qz p i K).mp g
    obtain ⟨l,h2,W,R⟩ :=s z y;have h0:=H.getVert_injOn (by change k<=p.length;omega) (by change l<=p.length;omega) (d.trans R.symm)
    omega
  · exact C
 have Y:c.IsPath:=by
  apply (Walk.cons_isPath_iff _ _).mpr;refine ⟨H.drop j',?_⟩
  intro t;obtain ⟨k,h1,I,M⟩:=(rd p j' D).mp t;have U:=H.getVert_injOn I P M;omega
 have n (z:V) (t:z∈(a.append b).support):z∈(p.take j).support:=by
  apply (qz p j J).mpr;rcases (Walk.mem_support_append_iff a b).mp t with g | y
  · simp only [a,Walk.support_concat,List.mem_append,List.mem_singleton] at g
    rcases g with g | C
    · obtain ⟨k,I,d⟩:=(qz p i K).mp g;exact ⟨k,by omega,d⟩
    · exact ⟨j,le_rfl,C.symm⟩
  · obtain ⟨k,_,I,d⟩ :=s z y;exact ⟨k,I,d⟩
 have F:((a.append b).append c).IsPath:=by
  apply qr (a.append b) c Q Y
  intro z r e;simp only [c,Walk.support_cons,List.mem_cons] at e;rcases e with x | e
  · exact x
  · exact ((vJ p H j j' L D) (n z r) e).elim
 refine ⟨(a.append b).append c,F,?_,?_⟩
 · simp only [a,b,c,Walk.length_append,Walk.length_concat,Walk.take_length,min_eq_left K,Walk.length_reverse,y2 p i' j w J,Walk.length_cons,Walk.drop_length];omega
 · intro z t
   rcases (Walk.mem_support_append_iff (a.append b) c).mp t with r | e
   · obtain ⟨k,_,d⟩:=(qz p j J).mp (n z r);exact d ▸ p.getVert_mem_support k
   · simp only [c,Walk.support_cons,List.mem_cons] at e
     rcases e with x | e
     · exact x ▸ p.getVert_mem_support i'
     · obtain ⟨k,_,_,d⟩:=(rd p j' D).mp e;exact d ▸ p.getVert_mem_support k
lemma vf {V:Type*} {G:SG V} {u v:V} (p:G.Walk u v)(w:p.IsPath) (i i' j j':ℕ)(s:i+4<=i') (k:i'<=j) (n:j+2<=j') (l:j'<=p.length) (g:i%2=i'%2) (h:j%2=j'%2) (d:G.Adj (p.getVert i) (p.getVert j)) (e:G.Adj (p.getVert i') (p.getVert j')):∃ q:G.Walk u v,q.IsPath/\q.length < p.length/\p.length<=q.length+ (i'-i)+(j'-j)/\q.length%2=p.length%2/\∀ z ∈ q.support,z∈p.support:=by
 obtain ⟨q,t,m,r⟩ :=zm p w i i' j j' (by omega) k (by omega) l d e
 exact ⟨q,t,by omega,by omega,by omega,r⟩
lemma u8 {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (D d:ℕ)(hD:0 < D) (F:Fintype.card V<=D *d) (n:∀ v,d<=G.degree v) (hN:8* (4*D)^2<=Fintype.card V) (R:FS V)(hR:2* (R.card+16*D+1)<=d) {u v:V} (p:G.Walk u v)(hp:p.IsPath) (I:16*D<=p.length):∃ q:G.Walk u v,q.IsPath/\q.length < p.length/\p.length<=q.length+ (16*D+8* (4*D)^2)/\q.length%2=p.length%2/\∀ z ∈ q.support,z∈p.support\/z ∉ R:=by
 classical
 let S :=R ∪ (p.take (16*D)).support.toFinset
 have P:(p.take (16*D)).support.toFinset.card<=16*D+1:=by
  have h :=List.toFinset_card_le (p.take (16*D)).support;simpa only [Walk.length_support,Walk.take_length,min_eq_left I] using h
 have hS:2*S.card<=d:=by
  have h :=card_union_le R (p.take (16*D)).support.toFinset;change S.card<=R.card+ (p.take (16*D)).support.toFinset.card at h;omega
 let a (i:Fin (4*D)) :=p.getVert (4*i.val);have k:0 < Fintype.card V :=by nlinarith
 obtain ⟨w,r,b2,hc⟩ :=vN G D d k F n S hS a
 have m:∃ i j:Fin (4*D),i.val < j.val/\Fintype.card V/(2* (4*D)^2) < ((G.neighborFinset (a i) ∩ G.neighborFinset (a j)) \ S).card:=by
  have Z:w.val≠r.val:=fun h=>b2 (Fin.ext h)
  rcases lt_or_gt_of_ne Z with T | h5
  · exact ⟨w,r,T,hc⟩
  · refine ⟨r,w,h5,?_⟩;rwa [inter_comm]
 obtain ⟨i,j,T,y⟩ :=m;let W:=(G.neighborFinset (a i) ∩ G.neighborFinset (a j)) \ S
 have l (x:V) (U:x∈W):G.Adj (p.getVert (4*i.val)) x/\G.Adj (p.getVert (4*j.val)) x/\x ∉ S :=by
  obtain ⟨N,L⟩ :=mem_sdiff.mp U;obtain ⟨h9,h3⟩ :=mem_inter.mp N;exact ⟨(G.mem_neighborFinset _ _).mp h9,(G.mem_neighborFinset _ _).mp h3,L⟩
 have h6:4*j.val<=p.length:=by have h :=j.isLt;omega
 have X:4*i.val+4<=4*j.val:=by omega
 have J:(4*i.val) % 2= (4*j.val) % 2:=by omega
 by_cases Y:∃ x ∈ W,x ∉ p.support
 · obtain ⟨x,b1,U⟩ :=Y
   obtain ⟨h4,a2,L⟩ :=l x b1;have h8:x ∉ R:=fun h=>L (mem_union_left _ h)
   obtain ⟨q,hq,M,H,g,e⟩ :=
    v7 p hp (4*i.val) (4*j.val) X h6 J x U h4 a2
   refine ⟨q,hq,M,?_,g,?_⟩
   · have K:=j.isLt;omega
   · intro z hz
     rcases e z hz with h2 | h7
     · exact Or.inl h2
     · exact Or.inr (h7 ▸ h8)
 · have hW:∀ x ∈ W,x∈p.support:=by
    intro x U;by_contra h;exact Y ⟨x,U,h⟩
   have hK:0 < 2* (4*D)^2:=by positivity
   have b4:4* (2* (4*D)^2)<=Fintype.card V :=by nlinarith only [hN]
   obtain ⟨s,t,b6,ht,h1,C,h0,a6⟩ :=
    vE p W hW (Fintype.card V) (2* (4*D)^2) hK b4 hp.length_lt y
   have hs:16*D < s:=by
    by_contra h;have b3:s<=16*D:=by omega
    have v4:p.getVert s∈(p.take (16*D)).support:= (qz p (16*D) I).mpr ⟨s,b3,rfl⟩;exact (l _ h0).2.2 (mem_union_right R (List.mem_toFinset.mpr v4))
   have Q:s+2<=t:=by omega
   have b0:4*j.val<=s:=by have K:=j.isLt;omega
   obtain ⟨q,hq,M,H,g,e⟩ :=
    vf p hp (4*i.val) (4*j.val) s t X b0 Q ht J C (l _ h0).1 (l _ a6).2.1
   refine ⟨q,hq,M,?_,g,fun z hz=> Or.inl (e z hz)⟩
   have K:=j.isLt;omega
lemma zu {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (D d:ℕ)(Q:0 < D) (j:Fintype.card V<=D *d) (g:∀ v,d<=G.degree v) (U:8* (4*D)^2<=Fintype.card V) (R:FS V)(W:2* (R.card+16*D+1)<=d) (t:ℕ)(ht:16*D<=t) {u v:V} (p:G.Walk u v)(H:p.IsPath) (x:t<=p.length) (e:∀ z ∈ p.support,z∈R->z=u\/z=v):∃ q:G.Walk u v,q.IsPath/\q.length<=t/\t < q.length+ (16*D+8* (4*D)^2)/\q.length%2=p.length%2/\∀ z ∈ q.support,z∈R->z=u\/z=v:=by
 classical
 have J:∀ M:ℕ,∀ p:G.Walk u v,p.length=M->p.IsPath->t<=p.length->(∀ z ∈ p.support,z∈R->z=u\/z=v)->∃ q:G.Walk u v,q.IsPath/\q.length<=t/\t < q.length+ (16*D+8* (4*D)^2)/\q.length%2=p.length%2/\∀ z ∈ q.support,z∈R->z=u\/z=v:=by
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih=>
   intro p Z H T e;by_cases m:p.length<=t
   · exact ⟨p,H,m,by omega,rfl,e⟩
   obtain ⟨q,N,P,F,k,s⟩ :=
    u8 G D d Q j g U R W p H (by omega)
   have i:∀ z ∈ q.support,z∈R->z=u\/z=v:=by
    intro z X C;rcases s z X with I | n
    · exact e z I C
    · exact (n C).elim
   by_cases K:t<=q.length
   · obtain ⟨w,Y,L,y,l,r⟩:=ih q.length (by omega) q rfl N K i
     exact ⟨w,Y,L,y,l.trans k,r⟩
   · exact ⟨q,N,by omega,by omega,k,i⟩
 exact J p.length p rfl H x e
lemma yP {V:Type*} {G:SG V} {u v:V} (p:G.Walk u v)(e:p.length=G.dist u v) {i j:ℕ} (d:i<=j) (g:j<=p.length):G.dist (p.getVert i) (p.getVert j)=j-i:=by have hsub:= ((p.take j).isSubwalk_drop i).trans (p.isSubwalk_take j);have h :=length_eq_dist_of_subwalk e hsub;simpa only [Walk.drop_length,Walk.take_length,Walk.take_getVert,inf_eq_left.mpr g,inf_eq_right.mpr d] using h.symm
lemma sx {V:Type*} {G:SG V} {u v:V} (p:G.Walk u v)(k:p.length=G.dist u v) {i j:ℕ} (h:i+3<=j) (l:j<=p.length) (z:V):¬ (G.Adj (p.getVert i) z/\G.Adj (p.getVert j) z) :=by
 rintro ⟨g,e⟩;have d:=G.dist_le (Walk.cons g (Walk.cons e.symm Walk.nil));rw [yP p k (by omega) l] at d
 simp only [Walk.length_cons,Walk.length_nil] at d;omega
lemma sU {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] {u v:V} (p:G.Walk u v)(t:p.length=G.dist u v) (d:ℕ)(m:∀ w,d<=G.degree w):(p.length/3+1)*d<=Fintype.card V :=by
 classical
 let I :=Fin (p.length/3+1);let W (i:I) :=G.neighborSet (p.getVert (3*i.val));let f:(Σ i:I,W i)->V:=fun x=>x.2.val
 have e (i:I):3*i.val<=p.length:=by
  have D:=i.isLt;omega
 have q:Function.Injective f :=by
  rintro ⟨i,x⟩ ⟨j,y⟩ k
  have s:i=j:=by
   by_contra r;have l:i.val≠j.val:=fun h=>r (Fin.ext h)
   rcases lt_or_gt_of_ne l with s | z
   · apply sx p t (i:=3*i.val) (j:=3*j.val) (by omega) (e j) x.val
     refine ⟨x.property,?_⟩;have g:x.val=y.val:=k;rw [g];exact y.property
   · apply sx p t (i:=3*j.val) (j:=3*i.val) (by omega) (e i) y.val
     refine ⟨y.property,?_⟩;have g:x.val=y.val:=k;rw [<- g];exact x.property
  subst j;have g:x=y:=Subtype.ext k;subst y;rfl
 have C:=Fintype.card_le_of_injective f q
 have n:(p.length/3+1)*d<=Fintype.card (Σ i:I,W i) :=by
  rw [Fintype.card_sigma]
  calc
   (p.length/3+1)*d= ∑ _i:I,d:=by simp [I]
   _<=∑ i:I,Fintype.card (W i) :=by
    apply sum_le_sum
    intro i _;simpa only [W,card_neighborSet_eq_degree] using m (p.getVert (3*i.val))
 exact n.trans C
lemma xD {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (g:G.Connected)(d:ℕ) (k:0 < d) (h:∀ w,d<=G.degree w) (u v:V):∃ p:G.Walk u v,p.IsPath/\d*p.length < 3*Fintype.card V :=by
 classical
 obtain ⟨p,j,e⟩ :=g.exists_path_of_dist u v;refine ⟨p,j,?_⟩;have l:=sU G p e d h;have i:p.length < 3* (p.length/3+1) :=by omega
 nlinarith
def q8 {V:Type*} (G:SG V)(b:ℕ):Prop:= ∀ S:FS V,S.card<=b->(G.induce (S:Set V)ᶜ).Preconnected
lemma q8.mono {V:Type*} {G:SG V} {a b:ℕ} (h:q8 G b)(d:a<=b):q8 G a:= fun S e=> h S (e.trans d)
lemma qW {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (S:FS V)(v: ↥((S:Set V)ᶜ)):G.degree v.val<=(G.induce (S:Set V)ᶜ).degree v +S.card:=by
 classical
 have d:(G.induce (S:Set V)ᶜ).degree v=(G.neighborFinset v.val \ S).card:=by
  have h :=CA card (G.map_neighborFinset_induce v);simpa [<- sdiff_eq_inter_compl] using h
 rw [d,<- G.card_neighborFinset_eq_degree v.val];have h :=card_sdiff_add_card_inter (G.neighborFinset v.val) S;have e:=card_le_card (inter_subset_right (s₁:=G.neighborFinset v.val) (s₂:=S));omega
lemma sB {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (b d:ℕ)(e:q8 G b) (s:0 < d) (j:∀ w,d+b<=G.degree w) (S:FS V)(q:S.card<=b) (u v:V)(r:u ∉ S) (m:v ∉ S):∃ p:G.Walk u v,p.IsPath/\d*p.length < 3*Fintype.card V/\∀ x ∈ p.support,x ∉ S:=by
 classical
 let U:=(S:Set V)ᶜ;let u':U:= ⟨u,r⟩;let v':U:= ⟨v,m⟩;let:Nonempty U:=⟨u'⟩;have t:(G.induce U).Connected:= ⟨e S q⟩
 have i (w:U):d<=(G.induce U).degree w :=by
  have h :=qW G S w;have z:=j w.val;change G.degree w.val<=(G.induce U).degree w +S.card at h;omega
 obtain ⟨p,n,k⟩ :=xD (G.induce U) t d s i u' v';let f:G.induce U ↪g G :=SimpleGraph.Embedding.induce U;refine ⟨p.map f.toHom,n.map f.injective,?_,?_⟩
 · change d*(p.map f.toHom).length < 3*Fintype.card V;simp only [Walk.length_map];exact k.trans_le (Nat.mul_le_mul_left 3 (Fintype.card_le_of_injective (fun x:U=> x.val) Subtype.val_injective))
 · intro x l;change x∈(p.map f.toHom).support at l;rw [Walk.support_map,List.mem_map] at l;obtain ⟨y,_,C⟩ :=l;subst x;exact y.property
lemma uX {V:Type*} {G:SG V} {v:V} (p:G.Walk v v)(M:Odd p.length):∃ (w:V)(q:G.Walk w w),q.IsCycle/\Odd q.length/\q.length<=p.length:=by
 classical
 let P (m:ℕ):Prop:= ∃ (w:V) (q:G.Walk w w),Odd q.length/\q.length=m;have x:∃ m,P m:= ⟨p.length,v,p,M,rfl⟩;obtain ⟨w,q,e,t⟩ :=Nat.find_spec x
 have g {z:V} (r:G.Walk z z) (D:Odd r.length):q.length<=r.length:=by
  rw [t];exact Nat.find_min' x ⟨z,r,D,rfl⟩
 have d:¬ q.Nil:=by
  rw [Walk.not_nil_iff_lt_length];have hmod:=Nat.odd_iff.mp e;omega
 have l:q.tail.IsPath:=by
  apply Walk.isPath_iff_isSubwalk_imp_nil.mpr
  intro z r D;by_contra k;have J:0 < r.length:=Walk.not_nil_iff_lt_length.mp k;have y:=Walk.length_le_of_isSubwalk D;rw [Walk.length_tail] at y;by_cases i:Odd r.length
  · have:=g r i;omega
  · obtain ⟨a,b,K⟩ :=D
    have C:q.length=a.length+r.length+b.length+1:=by
     have h :=CA Walk.length K;simp only [Walk.length_tail,Walk.length_append] at h;have L:=Walk.not_nil_iff_lt_length.mp d;omega
    let s :=Walk.cons (q.adj_snd d) (a.append b)
    have F:s.length=a.length+b.length+1:=by
     simp only [s,Walk.length_cons,Walk.length_append]
    have n:Odd s.length:=by
     have H:=Nat.odd_iff.mp e;have I:=Nat.even_iff.mp (Nat.not_odd_iff_even.mp i);apply Nat.odd_iff.mpr;omega
    have:=g s n;omega
 have j:3<=q.length:=by
  have N:q.length≠1:=fun h=>(Walk.adj_of_length_eq_one h).ne rfl
  have hmod:=Nat.odd_iff.mp e;omega
 exact ⟨w,q,Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨l,j⟩,e,g p M⟩
lemma xJ {V:Type*} (G:SG V):G.Colorable 2↔∀ (v:V)(p:G.Walk v v),p.IsCycle->¬ Odd p.length:=by
 rw [two_colorable_iff_forall_loop_even];constructor
 · intro h v p _ e;exact (Nat.not_even_iff_odd.mpr e) (h v p)
 · intro h v p
   apply Nat.not_odd_iff_even.mp
   intro e;obtain ⟨w,q,g,d,_⟩ :=uX p e;exact h w q g d
lemma tr {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (g:G.Connected)(j:¬ G.Colorable 2) (d:ℕ)(L:0 < d) (C:∀ v,d<=G.degree v):∃ (w:V)(q:G.Walk w w),q.IsCycle/\Odd q.length/\d*q.length < 6*Fintype.card V +d:=by
 classical
 let e:V:=Classical.choice g.nonempty;let f (v:V):Fin 2:=⟨G.dist e v %2,Nat.mod_lt _ (by decide)⟩
 have I:∃ a b,G.Adj a b/\f a =f b:=by
  by_contra h;push Not at h;apply j
  exact ⟨{ toFun:=f,map_rel':=fun {a b} m=> h a b m}⟩
 obtain ⟨a,b,m,t⟩ :=I;obtain ⟨pa,_,F⟩ :=g.exists_path_of_dist e a;obtain ⟨pb,_,n⟩ :=g.exists_path_of_dist e b
 have i {x y:V} (r:G.Walk x y) (K:r.length=G.dist x y):d*r.length < 3*Fintype.card V :=by
  have M:=sU G r K d C;have s:r.length < 3* (r.length/3+1) :=by omega
  nlinarith
 have P:=i pa F;have N:=i pb n;let p:=(pa.concat m).append pb.reverse
 have s:p.length=pa.length+1+pb.length:=by
  simp only [p,Walk.length_append,Walk.length_concat,Walk.length_reverse]
 have H:Odd p.length:=by
  have D:=CA Fin.val t;change G.dist e a %2=G.dist e b %2 at D;rw [<- F,<- n] at D;apply Nat.odd_iff.mpr;omega
 have k:d*p.length < 6*Fintype.card V +d:=by nlinarith
 obtain ⟨w,q,J,l,z⟩ :=uX p H;exact ⟨w,q,J,l,(Nat.mul_le_mul_left d z).trans_lt k⟩
def qT {V:Type*} (G:SG V)(b:ℕ):Prop:= ∀ S:FS V,S.card<=b->¬ (G.induce (S:Set V)ᶜ).Colorable 2
lemma z3 {V:Type*} (G:SG V)(h:¬ G.Colorable 2):Nonempty V :=by
 by_contra hn;have:IsEmpty V :=not_nonempty_iff.mp hn;apply h
 refine ⟨{ toFun:=fun x=>isEmptyElim x,map_rel':= ?_}⟩
 intro x;exact isEmptyElim x
lemma xA {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (b d:ℕ)(i:q8 G b) (e:qT G b)(z:0 < d) (k:∀ w,d+b<=G.degree w) (S:FS V)(s:S.card<=b):∃ (w:V)(c:G.Walk w w),c.IsCycle/\Odd c.length/\d*c.length < 6*Fintype.card V +d/\∀ x ∈ c.support,x ∉ S:=by
 classical
 let U:=(S:Set V)ᶜ;have n:¬ (G.induce U).Colorable 2 :=e S s;have:Nonempty U :=z3 _ n;have C:(G.induce U).Connected:= ⟨i S s⟩
 have j (v:U):d<=(G.induce U).degree v :=by
  have h :=qW G S v;have D:=k v.val;change G.degree v.val<=(G.induce U).degree v +S.card at h;omega
 obtain ⟨w,c,m,l,t⟩ :=tr (G.induce U) C n d z j;let f:G.induce U ↪g G :=SimpleGraph.Embedding.induce U;refine ⟨f w,c.map f.toHom,m.map f.injective,?_,?_,?_⟩
 · simpa only [Walk.length_map] using l
 · simp only [Walk.length_map]
   have q:=Fintype.card_le_of_injective (fun x:U=> x.val) Subtype.val_injective
   omega
 · intro x r;rw [Walk.support_map,List.mem_map] at r;obtain ⟨y,_,F⟩ :=r;subst x;exact y.property
lemma wX {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (b d D:ℕ)(g:q8 G b) (hd:0 < d) (r:∀ w,d+b<=G.degree w) (hN:Fintype.card V<=D *d) (S:FS V)(P:S.card+3*D+1<=b) (C:Set V)(hC:C.Nontrivial) (N:∀ z ∈ C,z ∉ S)(u v:V) (hu:u ∉ S)(hv:v ∉ S) (h3:u≠v):∃ x ∈ C,∃ y ∈ C,∃ (p:G.Walk u x)(q:G.Walk v y),p.IsPath/\q.IsPath/\p.length < 3*D/\q.length < 3*D/\x≠y/\(∀ z ∈ p.support,z∈C->z=x)/\(∀ z ∈ q.support,z∈C->z=y)/\(∀ z ∈ p.support,z ∉ q.support)/\(∀ z ∈ p.support,z ∉ S)/\(∀ z ∈ q.support,z ∉ S) :=by
 classical
 obtain ⟨w,K,h0⟩ :=hC.exists_ne v;have l:(insert v S).card<=b:= (card_insert_le v S).trans (by omega)
 obtain ⟨p',h2,Y,k⟩ :=sB G b d g hd r (insert v S) l u w (by simpa using And.intro h3 hu) (by simpa using And.intro h0 (N w K))
 obtain ⟨x,U,p,hp,v4,H,L⟩ :=rq p' h2 C K;have i:p.length < 3*D:=by nlinarith
 have m (z:V) (F:z∈p.support):z ∉ insert v S:= k z (H F)
 have Q:p.support.toFinset.card<=3*D:=by
  have J:=List.toFinset_card_le p.support;rw [p.length_support] at J;omega
 let T :=S ∪ p.support.toFinset;have hT:T.card<=b:= (card_union_le S p.support.toFinset).trans (by omega)
 obtain ⟨z,I,X⟩ :=hC.exists_ne x
 have h5:z ∉ T:=by
  simp only [T,mem_union,List.mem_toFinset,not_or];exact ⟨N z I,fun h=>X (L z h I)⟩
 have W:v ∉ T:=by
  simp only [T,mem_union,List.mem_toFinset,not_or];exact ⟨hv,fun h=>m v h (mem_insert_self v S)⟩
 obtain ⟨q',h1,h7,j⟩ :=sB G b d g hd r T hT v z W h5;obtain ⟨y,h8,q,hq,h9,s,h4⟩ :=rq q' h1 C I;have e:q.length < 3*D:=by nlinarith
 have n (z:V) (F:z∈q.support):z ∉ T:=j z (s F);have M (z:V) (R:z∈p.support) (Z:z∈q.support):False:= n z Z (mem_union_right S (List.mem_toFinset.mpr R))
 have h6:x≠y:=by
  intro h;exact M x p.end_mem_support (h ▸ q.end_mem_support)
 refine ⟨x,U,y,h8,p,q,hp,hq,i,e,h6,L,h4,M,?_,?_⟩
 · intro z F t;exact m z F (mem_insert_of_mem t)
 · intro z F t;exact n z F (mem_union_left _ t)
lemma zH {V:Type*} {G:SG V} {w:V} (c:G.Walk w w)(z:c.IsCycle) (g:Odd c.length)(u v:V) (i:u∈c.support)(n:v∈c.support) (l:u≠v):∃ p q:G.Walk u v,p.IsPath/\q.IsPath/\p.length+q.length=c.length/\p.length%2≠q.length%2/\p.support⊆c.support/\q.support⊆c.support:=by
 classical
 let r :=c.rotate u i;have m:r.IsCycle:=z.rotate i;have d:v∈r.support:= (c.mem_support_rotate_iff u i).mpr n;let p :=r.takeUntil v d;let s :=r.dropUntil v d;have y:p.IsPath:=m.isPath_takeUntil d
 have t:s.IsPath:=by
  have e:(p.append s).IsCycle:=by
   simpa only [p,s,Walk.take_spec] using m
  exact e.isPath_of_append_right (Walk.not_nil_of_ne l)
 have j:p.length+s.reverse.length=c.length:=by
  have h :=CA Walk.length (r.take_spec d);simpa only [Walk.length_append,r,Walk.length_rotate,Walk.length_reverse] using h
 refine ⟨p,s.reverse,y,t.reverse,j,?_,?_,?_⟩
 · have C:=Nat.odd_iff.mp g;omega
 · intro x k;exact (c.mem_support_rotate_iff u i).mp (r.support_takeUntil_subset_support d k)
 · intro x k;rw [Walk.support_reverse,List.mem_reverse] at k;exact (c.mem_support_rotate_iff u i).mp (r.support_dropUntil_subset_support d k)
lemma rE {V:Type*} {G:SG V} {w u v x y:V} (c:G.Walk w w)(M:c.IsCycle) (n:Odd c.length)(p:G.Walk u x) (q:G.Walk v y)(T:p.IsPath) (K:q.IsPath)(P:x∈c.support) (R:y∈c.support)(H:x≠y) (C:∀ z ∈ p.support,z∈c.support->z=x) (F:∀ z ∈ q.support,z∈c.support->z=y) (D:∀ z ∈ p.support,z ∉ q.support):∃ p₀ p₁:G.Walk u v,p₀.IsPath/\p₁.IsPath/\p₀.length%2≠p₁.length%2/\p₀.length<=p.length+q.length+c.length/\p₁.length<=p.length+q.length+c.length/\(∀ z ∈ p₀.support,z∈p.support\/z∈q.support\/z∈c.support)/\(∀ z ∈ p₁.support,z∈p.support\/z∈q.support\/z∈c.support) :=by
 obtain ⟨a,b,Q,N,I,J,m,l⟩:=zH c M n x y P R H
 have h (r:G.Walk x y) (L:r.IsPath) (i:r.support⊆c.support):((p.append r).append q.reverse).IsPath:=by
  have t:=qr p r T L (fun z k e=> C z k (i e))
  apply qr (p.append r) q.reverse t K.reverse
  intro z k g;rw [Walk.support_reverse,List.mem_reverse] at g;rcases (Walk.mem_support_append_iff _ _).mp k with j | e
  · exact (D z j g).elim
  · exact F z g (i e)
 have d (r:G.Walk x y) (i:r.support⊆c.support) (z:V) (k:z∈((p.append r).append q.reverse).support):z∈p.support\/z∈q.support\/z∈c.support:=by
  rcases (Walk.mem_support_append_iff _ _).mp k with s | g
  · rcases (Walk.mem_support_append_iff _ _).mp s with j | e
    · exact Or.inl j
    · exact Or.inr (Or.inr (i e))
  · exact Or.inr (Or.inl (by simpa only [Walk.support_reverse,List.mem_reverse] using g))
 refine ⟨(p.append a).append q.reverse,(p.append b).append q.reverse,h a Q m,h b N l,?_,?_,?_,d a m,d b l⟩
 · simp only [Walk.length_append,Walk.length_reverse];omega
 · simp only [Walk.length_append,Walk.length_reverse];omega
 · simp only [Walk.length_append,Walk.length_reverse];omega
def qZ {V:Type*} (G:SG V)(L:ℕ) (u v:V)(S:FS V):Prop:= ∀ r:Fin 2,∃ p:G.Walk u v,p.IsPath/\p.length<=L/\p.length%2=r.val/\∀ x ∈ p.support,x≠u->x≠v->x∈S
lemma qZ.mono {V:Type*} {G:SG V} {L:ℕ} {u v:V} {S T:FS V} (h:qZ G L u v S)(g:S⊆T):qZ G L u v T :=by intro r;obtain ⟨p,m,e,d,k⟩ :=h r;exact ⟨p,m,e,d,fun x l j i=> g (k x l j i)⟩
lemma vz {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (b d D:ℕ)(i:q8 G (b+3*D+3)) (k:qT G (b+3*D+3)) (hd:0 < d) (I:∀ w,d+ (b+3*D+3)<=G.degree w) (hN:Fintype.card V<=D *d) (u v:V)(b3:u≠v) (S:FS V)(hS:S.card<=b):∃ T:FS V,qZ G (12*D+3) u v T/\T.card<=12*D+3/\Disjoint S T:=by
 classical
 let S₀:= (S.erase u).erase v;have h9:S₀.card<=b:= (card_le_card ((erase_subset v (S.erase u)).trans (erase_subset u S))).trans hS;let F :=insert u (insert v S₀)
 have hF:F.card<=b+3*D+3:=by
  have h1:=card_insert_le u (insert v S₀);have h2:=card_insert_le v S₀;dsimp [F];omega
 obtain ⟨w,c,hc,h5,h6,X⟩ :=xA G (b+3*D+3) d i k hd I F hF;have h3:c.length<=6*D:=by nlinarith
 let C:Set V:={z | z∈c.support}
 have hC:C.Nontrivial:=by
  refine ⟨w,c.start_mem_support,c.snd,?_,(c.adj_snd hc.not_nil).ne⟩;exact List.mem_of_mem_tail (Walk.snd_mem_tail_support hc.not_nil)
 have h4 (z:V) (R:z∈C):z ∉ S₀:=by
  intro P;exact X z R (mem_insert_of_mem (mem_insert_of_mem P))
 obtain ⟨x,v4,y,b8,p,q,hp,hq,a6,b7,b6,h8,b4,b1,Y,Z⟩ :=
  wX G (b+3*D+3) d D i hd I hN S₀ (by omega) C hC h4 u v (by simp [S₀]) (by simp [S₀]) b3
 obtain ⟨H,J,N,Q,b9,W,h0,L,M⟩:=rE c hc h5 p q hp hq v4 b8 b6 h8 b4 b1;let U:=(p.support.toFinset ∪ q.support.toFinset) ∪ c.support.toFinset;let T:=(U.erase u).erase v
 have K {z:V} (R:z∈p.support\/z∈q.support\/z∈c.support) (j:z≠u) (g:z≠v):z∈T:=by
  simp only [T,U,mem_erase,mem_union,List.mem_toFinset];exact ⟨g,j,by tauto⟩
 have s:T.card<=12*D+3:=by
  have c1:T.card<=U.card:= card_le_card ((erase_subset v (U.erase u)).trans (erase_subset u U));have c0:U.card<=p.support.toFinset.card+q.support.toFinset.card+ c.support.toFinset.card:= (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _);have l:=List.toFinset_card_le p.support;have m:=List.toFinset_card_le q.support;have t:=List.toFinset_card_le c.support;rw [p.length_support] at l;rw [q.length_support] at m;rw [c.length_support] at t;omega
 have a2:Disjoint S T:=by
  rw [Finset.disjoint_left]
  intro z P n;simp only [T,U,mem_erase,mem_union,List.mem_toFinset] at n
  have e:z∈S₀:=by
   simp only [S₀,mem_erase];exact ⟨n.1,n.2.1,P⟩
  rcases n.2.2 with (h7 | b2) | b0
  · exact Y z h7 e
  · exact Z z b2 e
  · exact h4 z b0 e
 refine ⟨T,?_,s,a2⟩
 intro r;by_cases h:H.length%2=r.val
 · exact ⟨H,N,by omega,h,fun z R j g=> K (L z R) j g⟩
 · have hr:J.length%2=r.val:=by have:=r.isLt;omega
   exact ⟨J,Q,by omega,hr,fun z R j g=> K (M z R) j g⟩
end E5
end _m
section cw
namespace E5.BN
open Finset
open scoped BigOperators
noncomputable section
open scoped Classical
def qv {Ω:Type*} [Fintype Ω] (e:Ω->O) (d:Ω->Prop): O:= ∑ x,if d x then e x else 0
variable {E:Type*} [DecidableEq E]
def q9 (U:FS E)(p:E->O) (S:FS E): O:= (∏ e ∈ S,p e) * ∏ e ∈ U \ S,(1-p e)
lemma yC (U:FS E)(p:E->O): ∑ S ∈ U.powerset,q9 U p S =1:=by simp only [q9];rw [<- prod_add];simp
lemma tO {U S:FS E} {p:E->O} (i:S⊆U)(d:∀ e ∈ U,0<=p e) (g:∀ e ∈ U,p e<=1):0<=q9 U p S :=by
 apply mul_nonneg
 · exact prod_nonneg fun e h=>d e (i h)
 · exact prod_nonneg fun e h=>sub_nonneg.mpr (g e (mem_sdiff.mp h).1)
lemma tS {U T:FS E} {p:E->O} {e:E} (h:e∈U)(j:T⊆U.erase e):q9 U p (insert e T)=p e *q9 (U.erase e) p T:=by
 have g:e ∉ T:=by
  intro i;exact (mem_erase.mp (j i)).1 rfl
 have d:U \ insert e T=U.erase e \ T :=by
  ext x;simp only [mem_sdiff,mem_insert,mem_erase];tauto
 simp only [q9,prod_insert g,d];ring
lemma zn {U:FS E} {p:E->O} {e:E} (i:e∈U): ∑ S ∈ U.powerset with e∈S,q9 U p S =p e:=by
 have h:U.powerset.filter (fun S=>e∈S)=(U.erase e).powerset.image (insert e) :=by
  ext S;simp only [mem_filter,mem_powerset,mem_image];constructor
  · rintro ⟨l,q⟩
    refine ⟨S.erase e,?_,?_⟩
    · intro x t;obtain ⟨n,k⟩ :=mem_erase.mp t;exact mem_erase.mpr ⟨n,l k⟩
    · simpa using insert_erase q
  · rintro ⟨T,m,rfl⟩;exact ⟨insert_subset i (m.trans (erase_subset _ _)),mem_insert_self _ _⟩
 rw [h,sum_image]
 · calc
    ∑ T ∈ (U.erase e).powerset,q9 U p (insert e T)=∑ T ∈ (U.erase e).powerset,p e*q9 (U.erase e) p T:=by
     apply sum_congr rfl
     intro T m;exact tS i (mem_powerset.mp m)
    _=p e* ∑ T ∈ (U.erase e).powerset,q9 (U.erase e) p T:=by
     rw [mul_sum]
    _=p e:=by rw [yC,mul_one]
 · intro A s B r j
   have g:e ∉ A:=by
    intro g;exact (mem_erase.mp ((mem_powerset.mp s) g)).1 rfl
   have d:e ∉ B:=by
    intro d;exact (mem_erase.mp ((mem_powerset.mp r) d)).1 rfl
   simpa [g,d] using CA (fun S:FS E=>S.erase e) j
lemma yc (U:FS E)(p:E->O): ∑ S ∈ U.powerset,q9 U p S*(S.card:O)=∑ e ∈ U,p e:=by
 calc
  ∑ S ∈ U.powerset,q9 U p S*(S.card:O)=∑ S ∈ U.powerset,∑ e ∈ U,if e∈S then q9 U p S else 0 :=by
   apply sum_congr rfl
   intro S j;rw [<- sum_filter]
   have d:U.filter (fun e=>e∈S)=S:=by
    ext e;simp only [mem_filter];constructor
    · exact fun h=>h.2
    · intro g;exact ⟨(mem_powerset.mp j) g,g⟩
   rw [d];simp [mul_comm]
  _= ∑ e ∈ U,∑ S ∈ U.powerset,if e∈S then q9 U p S else 0 :=by rw [sum_comm]
  _= ∑ e ∈ U,p e:=by
   apply sum_congr rfl
   intro e i;rw [<- sum_filter,zn i]
variable [Fintype E]
def AO (R S T:FS E):Prop:=S ∩ R=T ∩ R
def qP (R:FS E)(d:FS E->Prop):Prop:= ∀ S T,AO R S T->(d S↔d T)
omit [Fintype E] in
lemma xY {R R' S T:FS E} (i:R⊆R')(h:AO R' S T):AO R S T :=by
 unfold AO at h ⊢;ext e;have g:e∈S ∩ R'↔e∈T ∩ R':=by rw [h]
 simp only [mem_inter] at g ⊢;constructor
 · rintro ⟨k,d⟩;exact ⟨(g.mp ⟨k,i d⟩).1,d⟩
 · rintro ⟨j,d⟩;exact ⟨(g.mpr ⟨j,i d⟩).1,d⟩
omit [Fintype E] in
lemma a9 (R:FS E):qP R (fun _=>True) :=by intro S T d;simp
omit [Fintype E] in
lemma av {R T:FS E} {A B:FS E->Prop} (g:qP R A)(e:qP T B):qP (R ∪ T) (fun S=>A S/\B S) :=by intro S V d;have i:AO R S V :=xY subset_union_left d;have h:AO T S V :=xY subset_union_right d;exact and_congr (g S V i) (e S V h)
abbrev Subsets (U:Finset E):={S:Finset E //S⊆U}
def y1 (U:FS E):Subsets U ≃ ↥U.powerset:= Equiv.subtypeEquivRight (by intro S;simp)
def t4:Subsets (Finset.univ:FS E) ≃ FS E where
 toFun S :=S.1
 invFun S:=⟨S,subset_univ S⟩
 left_inv _S:=Subtype.ext rfl
 right_inv _S:=rfl
def tT {U V:FS E} (m:Disjoint U V):Subsets (U ∪ V) ≃ Subsets U × Subsets V where
 toFun S:=(⟨S.1 ∩ U,inter_subset_right⟩,⟨S.1 ∩ V,inter_subset_right⟩)
 invFun P:=⟨P.1.1 ∪ P.2.1,union_subset_union P.1.2 P.2.2⟩
 left_inv S :=by
  apply Subtype.ext;ext e;simp only [mem_union,mem_inter];constructor
  · intro h
    rcases h with h | h
    · exact h.1
    · exact h.1
  · intro l
    have i:e∈U\/e∈V:=by
     simpa only [mem_union] using S.2 l
    rcases i with k | j
    · exact Or.inl ⟨l,k⟩
    · exact Or.inr ⟨l,j⟩
 right_inv P :=by
  rcases P with ⟨A,B⟩;apply Prod.ext
  · apply Subtype.ext
    ext e;simp only [mem_inter,mem_union];constructor
    · rintro ⟨g | d,k⟩
      · exact g
      · exact False.elim ((Finset.disjoint_left.mp m) k (B.2 d))
    · intro g;exact ⟨Or.inl g,A.2 g⟩
  · apply Subtype.ext
    ext e;simp only [mem_inter,mem_union];constructor
    · rintro ⟨g | d,j⟩
      · exact False.elim ((Finset.disjoint_left.mp m) (A.2 g) j)
      · exact d
    · intro d;exact ⟨Or.inr d,B.2 d⟩
def qo (U:FS E)(p:E->O) (d:FS E->Prop): O:= ∑ S:Subsets U,if d S.1 then q9 U p S.1 else 0
lemma zp (U:FS E)(p:E->O): ∑ S:Subsets U,q9 U p S.1=1:=by
 calc
  (∑ S:Subsets U,q9 U p S.1)=∑ S: ↥U.powerset,q9 U p S.1:=by
   apply Fintype.sum_equiv (y1 U)
   intro S;rfl
  _= ∑ S ∈ U.powerset,q9 U p S :=by
   simpa using (Finset.sum_attach U.powerset (fun S:FS E=>q9 U p S))
  _=1:=yC U p
lemma wh (U:FS E)(p:E->O):qo U p (fun _=>True)=1:=by unfold qo;simpa using zp U p
lemma s1 (p:E->O) (d:FS E->Prop):qv (fun S:FS E=>q9 Finset.univ p S) d= qo Finset.univ p d:=by
 unfold qv qo;symm;apply Fintype.sum_equiv t4
 intro S;by_cases h:d S.1 <;> simp [h,t4]
omit [Fintype E] in
lemma xy {U V A B:FS E} {p:E->O} (g:Disjoint U V)(t:A⊆U) (s:B⊆V):q9 (U ∪ V) p (A ∪ B)=q9 U p A *q9 V p B :=by
 have r:Disjoint A B:=g.mono t s
 have m:(U ∪ V) \ (A ∪ B)=(U \ A) ∪ (V \ B) :=by
  ext e;simp only [mem_sdiff,mem_union];constructor
  · rintro ⟨i | h,j⟩
    · exact Or.inl ⟨i,fun l=>j (Or.inl l)⟩
    · exact Or.inr ⟨h,fun k=>j (Or.inr k)⟩
  · rintro (⟨i,l⟩ | ⟨h,k⟩)
    · refine ⟨Or.inl i,?_⟩
      rintro (n | q)
      · exact l n
      · exact (D1 g) i (s q)
    · refine ⟨Or.inr h,?_⟩
      rintro (n | q)
      · exact (D1 g) (t n) h
      · exact k q
 have d:Disjoint (U \ A) (V \ B):=g.mono sdiff_subset sdiff_subset;simp only [q9,prod_union r,m,prod_union d];ring
lemma sk {U V:FS E} {p:E->O} {A B:FS E->Prop} (m:Disjoint U V)(w:qP U A) (v:qP V B):qo (U ∪ V) p (fun S=>A S/\B S)=qo U p A *qo V p B :=by
 let g:Subsets (U ∪ V) ≃ Subsets U × Subsets V:=tT m;let d:Subsets (U ∪ V)->O:=fun S=>if A S.1/\B S.1 then q9 (U ∪ V) p S.1 else 0
 calc
  qo (U ∪ V) p (fun S=>A S/\B S)=∑ S:Subsets (U ∪ V),d S :=by
   unfold qo;apply sum_congr rfl
   intro S _;by_cases h:A S.1/\B S.1 <;> simp [d,h]
  _= ∑ P:Subsets U × Subsets V,d (g.symm P) :=by
   apply Fintype.sum_equiv g
   intro S;simp only [Equiv.symm_apply_apply]
  _= ∑ X:Subsets U,∑ Y:Subsets V,d (g.symm (X,Y)) :=by
   rw [Fintype.sum_prod_type]
  _= ∑ X:Subsets U,∑ Y:Subsets V,(if A X.1 then q9 U p X.1 else 0)*(if B Y.1 then q9 V p Y.1 else 0) :=by
   apply sum_congr rfl
   intro X _;apply sum_congr rfl
   intro Y _;have n:(g.symm (X,Y)).1=X.1 ∪ Y.1:=rfl
   have l:AO U (X.1 ∪ Y.1) X.1:=by
    unfold AO;ext e;simp only [mem_inter,mem_union];constructor
    · rintro ⟨j | i,r⟩
      · exact ⟨j,X.2 j⟩
      · exact False.elim ((D1 m) r (Y.2 i))
    · rintro ⟨j,r⟩;exact ⟨Or.inl j,r⟩
   have k:AO V (X.1 ∪ Y.1) Y.1:=by
    unfold AO;ext e;simp only [mem_inter,mem_union];constructor
    · rintro ⟨j | i,q⟩
      · exact False.elim ((D1 m) (X.2 j) q)
      · exact ⟨i,Y.2 i⟩
    · rintro ⟨i,q⟩;exact ⟨Or.inr i,q⟩
   have s:A (X.1 ∪ Y.1)↔A X.1:=w _ _ l;have t:B (X.1 ∪ Y.1)↔B Y.1:=v _ _ k
   rw [show d (g.symm (X,Y))=if A (X.1 ∪ Y.1)/\B (X.1 ∪ Y.1) then q9 (U ∪ V) p (X.1 ∪ Y.1) else 0 by
    change (if A (g.symm (X,Y)).1/\B (g.symm (X,Y)).1 then q9 (U ∪ V) p (g.symm (X,Y)).1 else 0)=_;rw [n]]
   rw [xy m X.2 Y.2];by_cases x:A X.1 <;> by_cases y:B Y.1 <;> simp_all
  _= (∑ X:Subsets U,if A X.1 then q9 U p X.1 else 0) * ∑ Y:Subsets V,if B Y.1 then q9 V p Y.1 else 0 :=by
   rw [sum_mul];apply sum_congr rfl
   intro X _;rw [mul_sum]
  _=qo U p A *qo V p B :=by
   rfl
lemma r9 {R:FS E} {p:E->O} {d:FS E->Prop} (h:qP R d):qv (fun S:FS E=>q9 Finset.univ p S) d= qo R p d:=by
 calc
  qv (fun S:FS E=>q9 Finset.univ p S) d= qo Finset.univ p d:= s1 p d
  _=qo R p d:=by
   have e:=sk (p:=p) (U:=R) (V:=Finset.univ \ R) (A:=d) (B:=fun _=>True) Finset.disjoint_sdiff h (a9 (Finset.univ \ R))
   have g:R ∪ (Finset.univ \ R)=(Finset.univ:FS E):=union_sdiff_of_subset (subset_univ R);rw [g] at e;simpa [wh] using e
lemma yz {R T:FS E} {p:E->O} {A B:FS E->Prop} (g:Disjoint R T)(e:qP R A) (d:qP T B):qv (fun S:FS E=>q9 Finset.univ p S) (fun S=>A S/\B S)=qv (fun S:FS E=>q9 Finset.univ p S) A*qv (fun S:FS E=>q9 Finset.univ p S) B :=by
 calc
  qv (fun S:FS E=>q9 Finset.univ p S) (fun S=>A S/\B S)=qo (R ∪ T) p (fun S=>A S/\B S):=r9 (av e d)
  _=qo R p A *qo T p B:=sk g e d
  _=qv (fun S:FS E=>q9 Finset.univ p S) A*qv (fun S:FS E=>q9 Finset.univ p S) B :=by
   rw [r9 e,r9 d]
end
end E5.BN
end cw
section du
namespace E5.BN
open Finset
open scoped BigOperators
noncomputable section
open scoped Classical
lemma dN {Ω:Type*} [Fintype Ω] (d:Ω->O) (e: ∑ x,d x =1) (A:Ω->Prop):qv d (fun x=>¬ A x)=1-qv d A :=by
 have g:qv d A +qv d (fun x=>¬ A x)=1:=by
  unfold qv;rw [<- sum_add_distrib,<- e];apply sum_congr rfl
  intro x _;by_cases h:A x <;> simp [h]
 linarith
lemma bu {Ω:Type*} [Fintype Ω] (d:Ω->O) (e:∀ x,0<=d x) (A B:Ω->Prop):qv d (fun x=>A x\/B x)<=qv d A +qv d B :=by
 unfold qv;rw [<- sum_add_distrib];apply sum_le_sum
 intro x _;by_cases h:A x <;> by_cases g:B x <;> simp [h,g,e x]
lemma a5 {Ω I:Type*} [Fintype Ω] [Fintype I] (d:Ω->O) (e:∀ x,0<=d x) (A:I->Ω->Prop):qv d (fun x=>∃ i,A i x)<=∑ i,qv d (A i) :=by
 unfold qv;rw [sum_comm];apply sum_le_sum
 intro x _;by_cases h:∃ i,A i x
 · obtain ⟨i,k⟩ :=h
   rw [if_pos ⟨i,k⟩];have g:=single_le_sum (s:= (univ:FS I)) (f:=fun j=>if A j x then d x else 0) (fun j _=> by split_ifs <;> simp_all) (mem_univ i)
   simpa only [if_pos k] using g
 · rw [if_neg h]
   apply sum_nonneg
   intro i _;split_ifs <;> simp_all
lemma aI {Ω:Type*} [Fintype Ω] (e X:Ω->O) (d:∀ x,0<=e x) (h:∀ x,0<=X x) (t:O):t*qv e (fun x=>t < X x)<=∑ x,e x *X x:=by
 unfold qv;rw [mul_sum];apply sum_le_sum
 intro x _;by_cases g:t < X x
 · rw [if_pos g,mul_comm t];exact mul_le_mul_of_nonneg_left g.le (d x)
 · rw [if_neg g,mul_zero];exact mul_nonneg (d x) (h x)
lemma wl {Ω:Type*} [Fintype Ω] (d:Ω->O) (e: ∑ x,d x =1) (A:Ω->Prop) (i:qv d A < 1):∃ x,¬ A x:=by
 by_contra h;push Not at h;have g:qv d A =1:=by simp [qv,h,e]
 linarith
variable {E:Type*} [Fintype E] [DecidableEq E]
lemma uM (p:E->O): ∑ S:FS E,q9 univ p S=1:=by
 have h :=s1 p (fun _=>True)
 simpa only [qv,if_true,wh] using h
omit [Fintype E] in
lemma zV (L:FS E):qP L (fun X=>L⊆X) :=by
 intro X Y e;unfold AO at e;constructor
 · intro h x d;have g:x∈X ∩ L:=mem_inter.mpr ⟨h d,d⟩;rw [e] at g;exact (mem_inter.mp g).1
 · intro i x d;have g:x∈Y ∩ L:=mem_inter.mpr ⟨i d,d⟩;rw [<- e] at g;exact (mem_inter.mp g).1
omit [Fintype E] in
lemma am {L:FS E} {A:FS E->Prop} (e:qP L A):qP L (fun X=>¬ A X) :=by intro X Y d;exact not_congr (e X Y d)
lemma au (p:E->O) (L:FS E):qv (q9 univ p) (fun X=>L⊆X)=∏ e ∈ L,p e:=by
 rw [r9 (zV L)];unfold qo;rw [sum_eq_single (⟨L,subset_rfl⟩ :Subsets L)]
 · simp [q9]
 · intro X _ g
   have d:¬ L⊆X.val:=by
    intro h;exact g (Subtype.ext (Subset.antisymm X.property h))
   simp [d]
 · simp
omit [Fintype E] in
lemma yf {I:Type*} (R:I->FS E) (A:I->FS E->Prop) (g:∀ i,qP (R i) (A i)) (J:FS I):qP (J.biUnion R) (fun S=>∀ i ∈ J,A i S) :=by
 classical
 intro S T e;constructor
 · intro h i d;have hsub:R i⊆J.biUnion R :=subset_biUnion_of_mem R d;exact (g i S T (xY hsub e)).mp (h i d)
 · intro h i d;have hsub:R i⊆J.biUnion R :=subset_biUnion_of_mem R d;exact (g i S T (xY hsub e)).mpr (h i d)
lemma yT {I:Type*} (p:E->O) (R:I->FS E) (A:I->FS E->Prop) (g:∀ i,qP (R i) (A i)) (J:FS I)(d:(J:Set I).Pairwise fun i j=> Disjoint (R i) (R j)):qv (q9 univ p) (fun S=>∀ i ∈ J,A i S)=∏ i ∈ J,qv (q9 univ p) (A i) :=by
 classical
 revert d
 induction J using Finset.induction_on with
 | empty=>
  intro _;simp [qv,uM]
 | @insert i J hi ih=>
  intro d
  have l:Disjoint (R i) (J.biUnion R) :=by
   rw [disjoint_biUnion_right]
   intro j k;exact d (mem_insert_self i J) (mem_insert_of_mem k) (by intro h;subst j;exact hi k)
  have e:(J:Set I).Pairwise fun i j=> Disjoint (R i) (R j):=d.mono (subset_insert i J)
  simp only [forall_mem_insert,prod_insert hi];rw [yz l (g i) (yf R A g J),ih e]
lemma tH {I:Type*} (q:O)(R:I->FS E) (J:FS I)(d:(J:Set I).Pairwise fun i j=> Disjoint (R i) (R j)):qv (q9 univ (fun _:E=> q)) (fun S=>∀ i ∈ J,¬ R i⊆S)=∏ i ∈ J,(1-q^ (R i).card) :=by
 classical
 rw [yT (fun _=>q) R (fun i S=> ¬ R i⊆S) (fun i=>am (zV (R i))) J d]
 apply prod_congr rfl
 intro i _;rw [dN _ (uM _) (fun S=>R i⊆S),au]
 simp
lemma yQ {I:Type*} (q:O)(h:0<=q) (g:q<=1) (R:I->FS E) (J:FS I)(d:(J:Set I).Pairwise fun i j=> Disjoint (R i) (R j)) (L:ℕ)(e:∀ i ∈ J,(R i).card<=L):qv (q9 univ (fun _:E=> q)) (fun S=>∀ i ∈ J,¬ R i⊆S)<=(1-q^L)^J.card:=by
 classical
 rw [tH q R J d]
 calc
  ∏ i ∈ J,(1-q^ (R i).card)<=∏ _i ∈ J,(1-q^L) :=by
   apply prod_le_prod
   · intro i _;exact sub_nonneg.mpr (pow_le_one₀ h g)
   · intro i k;exact sub_le_sub_left (pow_le_pow_of_le_one h g (e i k)) 1
  _= (1-q^L)^J.card:=by simp
omit [DecidableEq E] in
lemma wY {I:Type*} [Fintype I] (q:O)(n:0 < q) (w:q<=1) (L m:ℕ)(R:I->Fin m->FS E) (v:∀ i,(Set.univ:Set (Fin m)).Pairwise fun j k=> Disjoint (R i j) (R i k)) (l:∀ i j,(R i j).card<=L) (r:(Fintype.card I:O)*(1-q^L)^m < 1/2) (J:0 < Fintype.card E):∃ S:FS E,(S.card:O)<=2*q*Fintype.card E/\∀ i,∃ j,R i j⊆S:=by
 classical
 let d:FS E->O :=q9 univ (fun _=>q)
 have g (S:FS E):0<=d S:=tO (subset_univ S) (fun _ _=> n.le) (fun _ _=> w)
 have z: ∑ S,d S =1:=uM _
 have s: ∑ S:FS E,d S*(S.card:O)=q*Fintype.card E :=by
  simpa [d,mul_comm] using yc (univ:FS E) (fun _=>q)
 let t:O:=2*q*Fintype.card E
 have H:0 < t:=by
  dsimp [t];exact mul_pos (mul_pos (by norm_num) n) (by exact_mod_cast J)
 have C:qv d (fun S=>t < (S.card:O))<=1/2:=by
  apply (mul_le_mul_iff_right₀ H).mp
  calc
   t*qv d (fun S=>t < (S.card:O))<=∑ S:FS E,d S*(S.card:O):=aI d (fun S=>S.card) g (fun S=>by positivity) t
   _=t* (1/2) :=by rw [s];dsimp [t];ring
 let e:I->FS E->Prop:=fun i S=> ∀ j,¬ R i j⊆S
 have y (i:I):qv d (e i)<=(1-q^L)^m:=by
  simpa only [d,e,mem_univ,forall_true_left,card_univ,Fintype.card_fin] using yQ q n.le w (R i) univ (by simpa only [coe_univ] using v i) L (fun j _=> l i j)
 have D:qv d (fun S=>∃ i,e i S) < 1/2:=by
  calc
   qv d (fun S=>∃ i,e i S)<=∑ i,qv d (e i):=a5 d g e
   _<=∑ _i:I,(1-q^L)^m:=sum_le_sum (fun i _=> y i)
   _= (Fintype.card I:O)*(1-q^L)^m:=by simp
   _ < 1/2:=r
 have x:qv d (fun S=>t < (S.card:O)\/∃ i,e i S) < 1:=by
  have h :=bu d g (fun S=>t < (S.card:O)) (fun S=>∃ i,e i S)
  linarith
 obtain ⟨S,F⟩ :=wl d z _ x;refine ⟨S,le_of_not_gt (fun h=>F (Or.inl h)),?_⟩
 intro i;by_contra hi;push Not at hi;exact F (Or.inr ⟨i,hi⟩)
end
end E5.BN
end du
section _m
namespace E5
open SimpleGraph Finset
open scoped SimpleGraph Classical
lemma tt {E:Type*} (P:FS E->Prop) (L b m:ℕ)(k:m*L<=b) (d:∀ S:FS E,S.card<=b->∃ T:FS E,P T/\T.card<=L/\Disjoint S T):∃ R:Fin m->FS E,(∀ i,P (R i)/\(R i).card<=L)/\Pairwise (fun i j=> Disjoint (R i) (R j)) :=by
 classical
 induction m with
 | zero=>
  refine ⟨Fin.elim0,?_,?_⟩
  · intro i;exact Fin.elim0 i
  · intro i;exact Fin.elim0 i
 | succ m ih=>
  obtain ⟨R,q,r⟩ :=ih (by nlinarith)
  let S:=(univ:FS (Fin m)).biUnion R
  have v:S.card<=b:=by
   calc
    S.card<=∑ i:Fin m,(R i).card:=card_biUnion_le
    _<=∑ _i:Fin m,L:=sum_le_sum (fun i _=> (q i).2)
    _=m*L:=by simp
    _<=b:=by nlinarith
  obtain ⟨T,t,e,l⟩ :=d S v;have g (i:Fin m):Disjoint T (R i):=l.symm.mono_right (subset_biUnion_of_mem R (mem_univ i));refine ⟨Fin.cons T R,?_,?_⟩
  · intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact ⟨t,e⟩
    · exact q j
  · intro i j n
    revert n
    refine Fin.cases ?_ (fun i=>?_) i <;>
     refine Fin.cases ?_ (fun j=>?_) j
    · intro h;exact (h rfl).elim
    · intro _;exact g j
    · intro _;exact (g i).symm
    · intro h;exact r (fun s=> h (CA Fin.succ s))
lemma xq {E I:Type*} [Fintype I] (R:I->FS E) (T:FS E)(l:Pairwise (fun i j=> Disjoint (R i) (R j))) (d:∀ i,¬ Disjoint T (R i)):Fintype.card I<=T.card:=by
 classical
 have m:∀ i,∃ x,x∈T/\x∈R i:=by
  intro i;simpa only [Finset.disjoint_left,not_forall,not_not,exists_prop] using d i
 choose x hxT hxR using m;let f:I->T:=fun i=>⟨x i,hxT i⟩
 have e:Function.Injective f :=by
  intro i j h;by_contra g;have k:x i=x j:=CA Subtype.val h;exact Finset.disjoint_left.mp (l g) (hxR i) (k ▸ hxR j)
 simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f e
lemma y7 {E I:Type*} [Fintype I] (R:I->FS E) (T:FS E)(e:Pairwise (fun i j=> Disjoint (R i) (R j))) (d:T.card < Fintype.card I):∃ i,Disjoint T (R i) :=by
 classical
 by_contra h;push Not at h;exact (Nat.not_le_of_gt d) (xq R T e h)
lemma uA {E I:Type*} [Fintype E] [Fintype I] (P:I->FS E->Prop) (q:O)(x:0 < q) (w:q<=1) (L b m a:ℕ)(n:((a+1)*m)*L<=b) (e:∀ i S,S.card<=b->∃ T:FS E,P i T/\T.card<=L/\Disjoint S T) (r:(Fintype.card I:O)*(a+1)*(1-q^L)^m < 1/2) (N:0 < Fintype.card E):∃ S:FS E,(S.card:O)<=2*q*Fintype.card E/\∀ i T,T.card<=a->∃ U:FS E,U⊆S/\P i U/\U.card<=L/\Disjoint T U:=by
 classical
 have l (i:I) :=tt (P i) L b ((a+1)*m) n (e i);choose R hR hD using l;let Q (i:I × Fin (a+1)) (j:Fin m):FS E:=R i.1 (finProdFinEquiv (i.2,j))
 have H (i:I × Fin (a+1)):(Set.univ:Set (Fin m)).Pairwise fun j k=> Disjoint (Q i j) (Q i k) :=by
  intro j _ k _ C;apply hD i.1
  intro s;exact C (CA Prod.snd (finProdFinEquiv.injective s))
 have v (i:I × Fin (a+1)) (j:Fin m):(Q i j).card<=L:= (hR i.1 (finProdFinEquiv (i.2,j))).2
 have d:(Fintype.card (I × Fin (a+1)): O)*(1-q^L)^m < 1/2:=by
  simpa only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using r
 obtain ⟨S,K,t⟩ :=BN.wY q x w L m Q H v d N;refine ⟨S,K,?_⟩
 intro i T M;have J (g:Fin (a+1)):∃ j,Q (i,g) j⊆S :=t (i,g);choose j hj using J;let F (g:Fin (a+1)):FS E :=Q (i,g) (j g)
 have y:Pairwise (fun g h=> Disjoint (F g) (F h)) :=by
  intro g h z;apply hD i
  intro s;exact z (CA Prod.fst (finProdFinEquiv.injective s))
 obtain ⟨g,D⟩ :=y7 F T y (by simpa only [Fintype.card_fin] using Nat.lt_succ_of_le M)
 exact ⟨F g,hj g,(hR i (finProdFinEquiv (g,j g))).1,v (i,g) (j g),D⟩
def qY {V:Type*} (G:SG V)(L:ℕ) (u v:V)(S:FS V):Prop:= ∃ p:G.Walk u v,p.IsPath/\p.length<=L/\∀ x ∈ p.support,x≠u->x≠v->x∈S
lemma qY.mono {V:Type*} {G:SG V} {L:ℕ} {u v:V} {S T:FS V} (h:qY G L u v S)(e:S⊆T):qY G L u v T :=by obtain ⟨p,l,d,j⟩ :=h;exact ⟨p,l,d,fun x k i g=> e (j x k i g)⟩
lemma x6 {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (b d L:ℕ)(g:q8 G b) (z:0 < d) (i:∀ w,d+b<=G.degree w) (k:3*Fintype.card V<=d *L) (u v:V)(S:FS V) (y:S.card<=b):∃ T:FS V,qY G L u v T/\T.card<=L/\Disjoint S T:=by
 classical
 let S':= (S.erase u).erase v;have j:S'.card<=b:= (card_le_card ((erase_subset v (S.erase u)).trans (erase_subset u S))).trans y;obtain ⟨p,t,r,m⟩ :=sB G b d g z i S' j u v (by simp [S']) (by simp [S'])
 have h:p.length+1<=L:=by nlinarith
 let T:=(p.support.toFinset.erase u).erase v;refine ⟨T,⟨p,t,by omega,?_⟩,?_,?_⟩
 · intro x s q n;simp only [T,mem_erase,List.mem_toFinset];exact ⟨n,q,s⟩
 · calc
    T.card<=p.support.toFinset.card:= card_le_card ((erase_subset v _).trans (erase_subset u _))
    _<=p.support.length:=List.toFinset_card_le p.support
    _=p.length+1:=p.length_support
    _<=L:=h
 · rw [Finset.disjoint_left]
   intro x l e;simp only [T,mem_erase,List.mem_toFinset] at e;apply m x e.2.2;simp only [S',mem_erase];exact ⟨e.1,e.2.1,l⟩
lemma zM {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (b d L m a:ℕ)(i:q8 G b) (H:0 < d) (k:∀ w,d+b<=G.degree w) (g:3*Fintype.card V<=d *L) (e:((a+1)*m)*L<=b) (q:O)(t:0 < q) (l:q<=1) (h:(Fintype.card V:O)^2* (a+1)*(1-q^L)^m < 1/2) (J:0 < Fintype.card V):∃ R:FS V,(R.card:O)<=2*q*Fintype.card V/\∀ u v S,S.card<=a->qY G L u v (R \ S) :=by
 classical
 let P:(V × V)->FS V->Prop:=fun uv=> qY G L uv.1 uv.2
 have r (uv:V × V) (S:FS V) (z:S.card<=b):∃ T:FS V,P uv T/\T.card<=L/\Disjoint S T:= x6 G b d L i H k g uv.1 uv.2 S z
 have F:(Fintype.card (V × V): O)*(a+1)*(1-q^L)^m < 1/2:=by
  simpa only [Fintype.card_prod,Nat.cast_mul,pow_two] using h
 obtain ⟨R,D,j⟩ :=uA P q t l L b m a e r F J;refine ⟨R,D,?_⟩
 intro u v S z;obtain ⟨T,s,I,_,y⟩ :=j (u,v) S z;apply I.mono
 intro x C;exact mem_sdiff.mpr ⟨s C,fun n=> D1 y n C⟩
lemma s9 {V:Type*} {G:SG V} {u v:V} (p:G.Walk u v)(d:p.IsPath):u ∉ p.support.tail:=by have h :=d.support_nodup;rw [<- p.cons_tail_support,List.nodup_cons] at h;exact h.1
lemma qy {V:Type*} {G:SG V} {u v:V} (p q:G.Walk u v)(n:p.IsPath) (m:q.IsPath)(j:1 < p.length) (d:∀ x ∈ p.support,x∈q.support->x=u\/x=v):(p.append q.reverse).IsCycle:=by
 apply n.isCycle_append m.reverse _ (Or.inl j);rw [List.disjoint_left]
 intro x g h;have i:x∈p.support:=List.mem_of_mem_tail g
 have e:x∈q.support:=by
  simpa only [Walk.support_reverse,List.mem_reverse] using List.mem_of_mem_tail h
 rcases d x i e with l | k
 · exact s9 p n (l ▸ g)
 · exact s9 q.reverse m.reverse (k ▸ h)
lemma sZ {V:Type*} {G:SG V} {u v:V} (p:G.Walk u v)(s:p.IsPath) (i:1 < p.length) (L:ℕ)(R:FS V) (j:∀ x ∈ p.support,x ∉ R)(d:qZ G L u v R):∃ c:G.Walk u u,c.IsCycle/\Odd c.length/\p.length<=c.length/\c.length<=p.length+L:=by
 let r:Fin 2:=⟨(p.length+1) % 2,Nat.mod_lt _ (by decide)⟩
 obtain ⟨q,n,t,e,l⟩ :=d r
 have w:(p.append q.reverse).IsCycle:=by
  apply qy p q s n i
  intro x k m;by_cases h:x=u
  · exact Or.inl h
  by_cases g:x=v
  · exact Or.inr g
  exact (j x k (l x m h g)).elim
 refine ⟨p.append q.reverse,w,?_,?_,?_⟩
 · apply Nat.odd_iff.mpr;simp only [Walk.length_append,Walk.length_reverse];change q.length%2= (p.length+1) % 2 at e;omega
 · simp only [Walk.length_append,Walk.length_reverse];omega
 · simp only [Walk.length_append,Walk.length_reverse];omega
lemma rf {V:Type*} [DecidableEq V] (G:SG V)(L:ℕ) (hL:0 < L) (X Y:FS V)(i:Disjoint X Y) (d:∀ x ∈ X,∀ y ∈ Y,G.Adj x y)(hX:L+1<=X.card) (Z:L<=Y.card) (u v:V)(l:u∈X) (F:v∈X)(t:u≠v):∃ p:G.Walk u v,p.IsPath/\p.length=2*L/\∀ z ∈ p.support,z∈X ∪ Y:=by
 induction L generalizing X Y u v with
 | zero=> omega
 | succ L ih=>
  classical
  obtain ⟨y,j⟩ :=card_pos.mp (show 0 < Y.card by omega)
  have n:u≠y:=fun h=>D1 i l (h.symm ▸ j)
  have K:v≠y:=fun h=>D1 i F (h.symm ▸ j)
  by_cases J:L=0
  · subst L
    let p:G.Walk u v:=Walk.cons (d u l y j) (Walk.cons (d v F y j).symm Walk.nil);refine ⟨p,?_,rfl,?_⟩
    · apply (Walk.cons_isPath_iff _ _).mpr
      refine ⟨(Walk.cons_isPath_iff _ _).mpr ⟨?_,?_⟩,?_⟩
      · exact Walk.IsPath.nil
      · simpa using K.symm
      · simpa only [Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false,not_or] using And.intro n t
    · intro z g
      simp only [p,Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at g;rcases g with rfl | rfl | rfl
      · exact mem_union_left _ l
      · exact mem_union_right _ j
      · exact mem_union_left _ F
  · have s:(X \ {u,v}).Nonempty:=by
     apply card_pos.mp
     have W:({u,v}:FS V).card<=2:=by
      exact (card_insert_le _ _).trans (by simp)
     have hc:=card_le_card (show X ∩ {u,v}⊆({u,v}:FS V) from inter_subset_right);rw [card_sdiff,inter_comm];omega
    obtain ⟨w,P⟩ :=s;have D:w∈X:= (mem_sdiff.mp P).1;have N:w≠u:=fun h=>(mem_sdiff.mp P).2 (by simp [h])
    have M:w≠v:=by
     have U:= (mem_sdiff.mp P).2;exact fun h=>U (by simp [h])
    have Q:L+1<=(X.erase u).card:=by rw [card_erase_of_mem l];omega
    have H:L<=(Y.erase y).card:=by rw [card_erase_of_mem j];omega
    have r:Disjoint (X.erase u) (Y.erase y):=i.mono (erase_subset _ _) (erase_subset _ _);have e:∀ x ∈ X.erase u,∀ z ∈ Y.erase y,G.Adj x z:= fun x C z g=> d x (mem_of_mem_erase C) z (mem_of_mem_erase g)
    obtain ⟨q,T,m,k⟩ :=ih (by omega) (X.erase u) (Y.erase y) r e Q H w v (mem_erase.mpr ⟨N,D⟩) (mem_erase.mpr ⟨t.symm,F⟩) M
    have R:u ∉ q.support:=by
     intro h;rcases mem_union.mp (k u h) with C | g
     · exact (mem_erase.mp C).1 rfl
     · exact D1 i l (mem_of_mem_erase g)
    have I:y ∉ q.support:=by
     intro h;rcases mem_union.mp (k y h) with C | g
     · exact D1 i (mem_of_mem_erase C) j
     · exact (mem_erase.mp g).1 rfl
    let p:G.Walk u v:=Walk.cons (d u l y j) (Walk.cons (d w D y j).symm q);refine ⟨p,?_,?_,?_⟩
    · apply (Walk.cons_isPath_iff _ _).mpr;refine ⟨(Walk.cons_isPath_iff _ _).mpr ⟨T,I⟩,?_⟩;simpa only [Walk.support_cons,List.mem_cons,not_or] using And.intro n R
    · simp only [p,Walk.length_cons,m];omega
    · intro z g
      simp only [p,Walk.support_cons,List.mem_cons] at g;rcases g with rfl | rfl | g
      · exact mem_union_left _ l
      · exact mem_union_right _ j
      · exact (union_subset_union (erase_subset _ _) (erase_subset _ _)) (k z g)
lemma wq {V:Type*} [DecidableEq V] (G:SG V)(L:ℕ) (t:0 < L) (X Y:FS V)(h:Disjoint X Y) (d:∀ x ∈ X,∀ y ∈ Y,G.Adj x y)(s:L+1<=X.card) (r:L<=Y.card) (u v:V)(D:u∈X) (n:v∈X)(j:u≠v) (p:G.Walk u v)(C:p.IsPath) (g:1 < p.length) (e:∀ z ∈ p.support,z∈X ∪ Y->z=u\/z=v):∃ c:G.Walk u u,c.IsCycle/\c.length=p.length+2*L:=by
 obtain ⟨q,w,l,k⟩ :=rf G L t X Y h d s r u v D n j;refine ⟨p.append q.reverse,?_,?_⟩
 · exact qy p q C w g (fun z i m=> e z i (k z m))
 · simp only [Walk.length_append,Walk.length_reverse,l]
lemma u9 {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (D d:ℕ)(J:0 < D) (h:Fintype.card V<=D *d) (g:∀ v,d<=G.degree v) (M:8* (4*D)^2<=Fintype.card V) (X Y:FS V)(C:Disjoint X Y) (e:∀ x ∈ X,∀ y ∈ Y,G.Adj x y)(hX:16*D+8* (4*D)^2+1<=X.card) (Z:16*D+8* (4*D)^2<=Y.card) (N:2* ((X ∪ Y).card+16*D+1)<=d) (u v:V)(I:u∈X) (T:v∈X)(w:u≠v) (p:G.Walk u v)(W:p.IsPath) (s:∀ z ∈ p.support,z∈X ∪ Y->z=u\/z=v) (n:ℕ)(hn:32*D+8* (4*D)^2+4<=n) (R:n<=p.length+2) (m:n%2=p.length%2):∃ c:G.Walk u u,c.IsCycle/\c.length=n:=by
 obtain ⟨q,H,U,F,k,j⟩ :=zu G D d J h g M (X ∪ Y) N (n-2) (by omega) p W (by omega) s
 let L:=(n-q.length)/2;have t:q.length%2=n%2:=k.trans m.symm;have r:1 < q.length:=by omega
 have K:0 < L:=by dsimp [L];omega
 have P:L<=16*D+8* (4*D)^2:=by dsimp [L];omega
 have l:q.length+2*L=n:=by dsimp [L];omega
 obtain ⟨c,Q,i⟩ :=wq G L K X Y C e (by omega) (by omega) u v I T w q H r j
 exact ⟨c,Q,i.trans l⟩
lemma zG (D:ℕ)(U:0 < D):∃ e K:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (d:ℕ),e<=Fintype.card V->Fintype.card V<=D *d->(∀ v,d<=G.degree v)->∀ (z:V)(c:G.Walk z z),c.IsCycle->∀ n:ℕ,K<=n->n+K<=c.length->n%2=c.length%2->∃ (w:V)(q:G.Walk w w),q.IsCycle/\q.length=n:=by
 let Q :=16*D+8* (4*D)^2;let M :=rR D Q;let H :=sd D Q;let L :=rl D Q;let C :=2* (2*Q+16*D+3);let K :=M+H+ (32*D+8* (4*D)^2+4)+1;let e:=D*C+8* (4*D)^2+2*L* (Q+M+1)+H;have hQ:0 < Q:=by dsimp [Q];omega
 refine ⟨e,K,?_⟩
 intro V _ _ G _ d P g i z c hc n hn F J;have k:8* (4*D)^2<=Fintype.card V :=by dsimp [e] at P;omega
 have r:2*L* (Q+M+1)<=Fintype.card V :=by dsimp [e] at P;omega
 have m:H<=Fintype.card V :=by dsimp [e] at P;omega
 have W:D*C<=D*d:=by
  have h:D*C<=Fintype.card V :=by dsimp [e] at P;omega
  exact h.trans g
 have hC:C<=d:= (mul_le_mul_iff_right₀ U).mp W;have I:M < c.length:=by dsimp [K] at hn F;omega
 obtain ⟨X,Y,hX,hY,N,j,u,hu,v,hv,Z,p,hp,T,t,s⟩:=tl G c hc D d Q U hQ g i I r m
 have hR:2* ((X ∪ Y).card+16*D+1)<=d:=by
  rw [card_union_of_disjoint N,hX,hY];dsimp [C] at hC;omega
 have l:32*D+8* (4*D)^2+4<=n:=by dsimp [K] at hn;omega
 have x:n<=p.length+2:=by
  change c.length<=p.length+M+H at T;dsimp [K] at F;omega
 have h0:16*D+8* (4*D)^2+1<=X.card:=by
  change X.card=16*D+8* (4*D)^2+2 at hX;omega
 have R:16*D+8* (4*D)^2<=Y.card:=hY.ge;obtain ⟨q,hq,y⟩ :=u9 G D d U g i k X Y N j h0 R hR u v hu hv Z p hp s n l x (J.trans t.symm);exact ⟨u,q,hq,y⟩
lemma uR (D:ℕ)(x:0 < D):∃ e K:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (d n:ℕ),e<=Fintype.card V->Fintype.card V<=D *d->(∀ v,d<=G.degree v)->3<=n->Odd n->K<=n->¬ CG n ⊑ G->∀ (z:V)(c:G.Walk z z),c.IsCycle->Odd c.length->c.length < n+K:=by
 obtain ⟨e,K,k⟩ :=zG D x;refine ⟨e,K,?_⟩
 intro V _ _ G _ d n y h g H m s t z c F j;by_contra r;have l:n%2=c.length%2:= (Nat.odd_iff.mp m).trans (Nat.odd_iff.mp j).symm;obtain ⟨w,q,C,i⟩ :=k G d y h g z c F n s (by omega) l
 apply t;exact (cycleGraph_isContained_iff (by omega)).mpr ⟨w,q,C,i⟩
def dj {V:Type*} [DecidableEq V] (G:SG V) (S:FS V) (v:S):(G.induce (S:Set V)).induce ({v}ᶜ:Set S) ≃g G.induce (S.erase v.val:Set V) where
 toEquiv:=
  { toFun:=fun x=>⟨x.val.val,mem_erase.mpr ⟨by
     intro h
     exact x.property (Subtype.ext h),x.val.property⟩⟩
    invFun:=fun x=>⟨⟨x.val,(mem_erase.mp x.property).2⟩,by
     intro h
     exact (mem_erase.mp x.property).1 (CA Subtype.val h)⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl}
 map_rel_iff':=by intro x y;rfl
lemma rN {V:Type*} [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (S:FS V)(v:S):(G.induce (S.erase v.val:Set V)).edgeFinset.card+ (G.induce (S:Set V)).degree v=(G.induce (S:Set V)).edgeFinset.card:=by rw [<- (dj G S v).card_edgeFinset_eq];rw [card_edgeFinset_induce_compl_singleton,card_edgeFinset_deleteIncidenceSet];exact Nat.sub_add_cancel ((G.induce (S:Set V)).degree_le_card_edgeFinset v)
lemma a4 {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (d:O):∃ S:FS V,(G.edgeFinset.card:O)-d*Fintype.card V<=((G.induce (S:Set V)).edgeFinset.card:O)-d*S.card/\∀ v:S,d < (G.induce (S:Set V)).degree v :=by
 classical
 let g (S:FS V): O:= ((G.induce (S:Set V)).edgeFinset.card:O)-d*S.card;let e:O:= (G.edgeFinset.card:O)-d*Fintype.card V;let h:FS (FS V) :=univ.filter fun S=>e<=g S
 have l:(univ:FS V)∈h:=by
  have w:(G.induce ((univ:FS V):Set V)).edgeFinset.card= G.edgeFinset.card:=by
   rw [<- G.card_filter_edgeFinset_toFinset_subset univ];simp
  simp [h,g,e,w]
 obtain ⟨S,y,i⟩ :=h.exists_min_image card ⟨_,l⟩;have j:e<=g S:=(mem_filter.mp y).2;refine ⟨S,j,?_⟩
 intro v;by_contra k
 have q:((G.induce (S:Set V)).degree v:O)<=d:=by
  exact le_of_not_gt k
 let T :=S.erase v.val;have n:T.card+1=S.card:=card_erase_add_one v.property;have m:=rN G S v
 have s:((G.induce (T:Set V)).edgeFinset.card:O)+(G.induce (S:Set V)).degree v=(G.induce (S:Set V)).edgeFinset.card:=by
  exact_mod_cast m
 have r:(T.card:O)+1=S.card:=by exact_mod_cast n
 have x:T∈h:=by
  apply mem_filter.mpr;refine ⟨mem_univ _,?_⟩;dsimp [g] at j ⊢;nlinarith
 have t:=i T x;omega
noncomputable def sy {V:Type*} [DecidableEq V] (G:SG V)(S:FS V) (T:FS S):(G.induce (S:Set V)).induce (T:Set S) ≃g G.induce (T.map (Function.Embedding.subtype (fun v=>v∈S)):Set V) :=by
 let f: ↥(T:Set S)->↥(T.map (Function.Embedding.subtype (fun v=>v∈S)):Set V):=fun x=>⟨x.val.val,mem_map.mpr ⟨x.val,x.property,rfl⟩⟩
 have e:Function.Injective f :=by
  intro x y h;apply Subtype.ext;apply Subtype.ext;change (f x).val= (f y).val;exact CA Subtype.val h
 have d:Function.Surjective f :=by
  intro y;obtain ⟨x,j,i⟩ :=mem_map.mp y.property;exact ⟨⟨x,j⟩,Subtype.ext i⟩
 exact { toEquiv:=Equiv.ofBijective f ⟨e,d⟩,map_rel_iff':=Iff.rfl}
lemma u7 {V:Type*} [Finite V] (G:SG V) [DecidableRel G.Adj] (k η :O)(F:0<=η) (A:FS V)(I:k*A.card+η* (A.card:O)^2 < ((G.induce (A:Set V)).edgeFinset.card:O)):∃ S:FS V,S.Nonempty/\k*S.card+η* (S.card:O)^2 < ((G.induce (S:Set V)).edgeFinset.card:O)/\(∀ v:S,k < (G.induce (S:Set V)).degree v)/\∀ T:FS V,T.card < S.card->((G.induce (T:Set V)).edgeFinset.card:O)<=k*T.card+η* (T.card:O)^2:=by
 classical
 let:=Fintype.ofFinite V;let m:FS (FS V) :=univ.filter fun S=>k*S.card+η* (S.card:O)^2 < ((G.induce (S:Set V)).edgeFinset.card:O)
 have K:A∈m:=mem_filter.mpr ⟨mem_univ _,I⟩;obtain ⟨S,J,i⟩ :=m.exists_min_image card ⟨_,K⟩;have e:= (mem_filter.mp J).2
 have g (T:FS V) (H:T.card < S.card):((G.induce (T:Set V)).edgeFinset.card:O)<=k*T.card+η* (T.card:O)^2:=by
  by_contra hn;have r:T∈m:=mem_filter.mpr ⟨mem_univ _,lt_of_not_ge hn⟩;exact (Nat.not_le_of_gt H) (i T r)
 have j (v:S):k < (G.induce (S:Set V)).degree v :=by
  by_contra y;have D:=le_of_not_gt y;let T :=S.erase v.val;have w:T.card+1=S.card:=card_erase_add_one v.property;have s:(T.card:O)+1=S.card:=by exact_mod_cast w
  have t:=rN G S v
  have z:((G.induce (T:Set V)).edgeFinset.card:O)+(G.induce (S:Set V)).degree v=(G.induce (S:Set V)).edgeFinset.card:=by
   exact_mod_cast t
  have H:=g T (by omega)
  have x:=mul_nonneg F (by positivity:(0:O)<=2* (T.card:O)+1)
  rw [<- s] at e;nlinarith
 have d:S.Nonempty:=by
  by_contra h;have l:S.card=0:=card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp h)
  have q:Fintype.card (S:Set V)=S.card:=by
   calc
    Fintype.card (S:Set V)=(S:Set V).ncard:=Nat.card_eq_fintype_card.symm
    _=S.card:=Set.ncard_coe_finset S
  have C:= (G.induce (S:Set V)).card_edgeFinset_le_card_choose_two;rw [q,l] at C;norm_num only [Nat.choose_zero_succ] at C;have n:(G.induce (S:Set V)).edgeFinset.card=0:=Nat.eq_zero_of_le_zero C;simp [l,n] at e
 exact ⟨S,d,e,j,g⟩
lemma s5 {V:Type*} [Finite V] (G:SG V) [DecidableRel G.Adj] (k η :O)(i:0<=η) (A:FS V)(j:k*A.card+η* (A.card:O)^2 < ((G.induce (A:Set V)).edgeFinset.card:O)):∃ S:FS V,S.Nonempty/\k*S.card+η* (S.card:O)^2 < ((G.induce (S:Set V)).edgeFinset.card:O)/\(∀ v:S,k < (G.induce (S:Set V)).degree v)/\∀ T:FS S,T.card < S.card->(((G.induce (S:Set V)).induce (T:Set S)).edgeFinset.card:O)<=k*T.card+η* (T.card:O)^2:=by
 classical
 let:=Fintype.ofFinite V;obtain ⟨S,m,d,g,e⟩:=u7 G k η i A j;refine ⟨S,m,d,g,?_⟩
 intro T l;have h :=e (T.map (Function.Embedding.subtype (fun v=>v∈S))) (by simpa only [card_map] using l)
 rw [<- (sy G S T).card_edgeFinset_eq,card_map] at h;exact h
lemma yr (a b t N k β η e:O)(n:0<=a) (D:0<=b) (d:0<=t) (m:0<=k) (r:0<=η) (x:N=a+b+t) (F:t<=β) (s:β<=k) (C:k-β<=a) (z:k-β<=b) (g:β*N<=2*η* (k-β)^2) (H:e<=k* (a+b) + η* (a^2+b^2)+t*N):e<=k*N+η*N^2:=by
 have l:0<=k-β:=sub_nonneg.mpr s
 have q:(k-β)^2<=a*b:=by
  simpa only [pow_two] using mul_le_mul C z l n
 have i:=mul_le_mul_of_nonneg_left q (by positivity:0<=2*η)
 have h:0<=N:=by linarith
 have y:=mul_le_mul_of_nonneg_right F h;have w:=mul_nonneg m d;have j:=mul_nonneg r (mul_nonneg d (by linarith:0<=2*N-t))
 have v:k*N+η*N^2- (k* (a+b) + η* (a^2+b^2)+t*N)=k*t+η*t* (2*N-t)+2*η* (a*b)-t*N:=by
  rw [x];ring
 nlinarith
lemma rk {V:Type*} [Fintype V] [DecidableEq V] (G:SG V)(S:FS V) (h:¬ (G.induce (S:Set V)ᶜ).Preconnected):∃ A B:FS V,A.Nonempty/\B.Nonempty/\Disjoint A B/\Disjoint A S/\Disjoint B S/\A ∪ B ∪ S=univ/\∀ a ∈ A,∀ b ∈ B,¬ G.Adj a b:=by
 classical
 let U:=(S:Set V)ᶜ;let H :=G.induce U
 obtain ⟨u,v,y⟩ :∃ u v:U,¬ H.Reachable u v:=by
  simpa only [SimpleGraph.Preconnected,not_forall] using h
 let A:=({x:V | ∃ n:x ∉ S,H.Reachable u ⟨x,n⟩}:Set V).toFinset;let B:=(S ∪ A)ᶜ
 have m (x:V):x∈A↔∃ n:x ∉ S,H.Reachable u ⟨x,n⟩ :=by
  simp only [A,Set.mem_toFinset,Set.mem_ofPred_eq]
 have w:Disjoint A S:=by
  rw [Finset.disjoint_left]
  intro x n;exact ((m x).mp n).choose
 have D:Disjoint A B:=by
  rw [Finset.disjoint_left]
  intro x z i;exact (mem_compl.mp i) (mem_union_right S z)
 have r:Disjoint B S:=by
  rw [Finset.disjoint_left]
  intro x i q;exact (mem_compl.mp i) (mem_union_left A q)
 have g:A.Nonempty:= ⟨u.val,(m _).mpr ⟨u.property,.rfl⟩⟩
 have j:B.Nonempty:=by
  refine ⟨v.val,?_⟩;simp only [B,mem_compl,mem_union,not_or];refine ⟨v.property,?_⟩
  intro t;obtain ⟨_,d⟩:=(m _).mp t;exact y d
 have e:A ∪ B ∪ S=univ:=by
  calc
   A ∪ B ∪ S= (S ∪ A) ∪ (S ∪ A)ᶜ:=by dsimp [B];ac_rfl
   _=univ:=union_compl (S ∪ A)
 refine ⟨A,B,g,j,D,w,r,e,?_⟩
 intro a J b I F;obtain ⟨C,d⟩:=(m a).mp J;have k:b ∉ S:=fun h=>(mem_compl.mp I) (mem_union_left A h)
 have l:H.Adj ⟨a,C⟩ ⟨b,k⟩ :=F;have s:b∈A:= (m b).mpr ⟨k,d.trans l.reachable⟩;exact (mem_compl.mp I) (mem_union_right S s)
lemma qR {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (A B S:FS V)(d:A ∪ B ∪ S=univ) (e:∀ a ∈ A,∀ b ∈ B,¬ G.Adj a b)(a:V) (m:a∈A):G.degree a<=A.card+S.card:=by
 have hsub:G.neighborFinset a⊆A ∪ S :=by
  intro x k;have g:x∈A ∪ B ∪ S:=by rw [d];exact mem_univ _
  rcases mem_union.mp g with h | l
  · rcases mem_union.mp h with j | i
    · exact mem_union_left _ j
    · exact (e a m x i ((G.mem_neighborFinset a x).mp k)).elim
  · exact mem_union_right _ l
 rw [<- G.card_neighborFinset_eq_degree a];exact (card_le_card hsub).trans (card_union_le A S)
lemma vp {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (A B S:FS V)(j:A ∪ B ∪ S=univ) (g:∀ a ∈ A,∀ b ∈ B,¬ G.Adj a b):G.edgeFinset.card<=(G.induce (A:Set V)).edgeFinset.card+ (G.induce (B:Set V)).edgeFinset.card+S.card*Fintype.card V :=by
 classical
 let X :=G.edgeFinset.filter (fun e=>e.toFinset⊆A)
 let Y :=G.edgeFinset.filter (fun e=>e.toFinset⊆B)
 let Z :=S.biUnion (fun v=>G.incidenceFinset v)
 have h (v:V) (x:v ∉ S):v∈A\/v∈B:=by
  have l:v∈A ∪ B ∪ S:=by rw [j];exact mem_univ v
  exact mem_union.mp ((mem_union.mp l).resolve_right x)
 have i (e:Sym2 V) (k:e∈G.edgeFinset) (v:V) (x:v∈S) (y:v∈e):e∈Z:=by
  apply mem_biUnion.mpr;refine ⟨v,x,?_⟩;rw [G.incidenceFinset_eq_filter];exact mem_filter.mpr ⟨k,y⟩
 have d:G.edgeFinset⊆X ∪ Y ∪ Z:=by
  intro e k;rcases e with ⟨⟨u,v⟩⟩;by_cases m:u∈S
  · exact mem_union_right _ (i _ k u m (by simp))
  by_cases w:v∈S
  · exact mem_union_right _ (i _ k v w (by simp))
  have r:G.Adj u v:=by simpa using k
  rcases h u m with s | t <;> rcases h v w with n | q
  · apply mem_union_left;apply mem_union_left;exact mem_filter.mpr ⟨k,by simpa only [Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff] using And.intro s n⟩
  · exact (g u s v q r).elim
  · exact (g v n u t r.symm).elim
  · apply mem_union_left;apply mem_union_right;exact mem_filter.mpr ⟨k,by simpa only [Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff] using And.intro t q⟩
 have C:X.card= (G.induce (A:Set V)).edgeFinset.card:= G.card_filter_edgeFinset_toFinset_subset A;have z:Y.card= (G.induce (B:Set V)).edgeFinset.card:= G.card_filter_edgeFinset_toFinset_subset B
 have I:Z.card<=S.card*Fintype.card V :=by
  calc
   Z.card<=∑ v ∈ S,(G.incidenceFinset v).card:=card_biUnion_le
   _<=∑ _v ∈ S,Fintype.card V :=by
    apply sum_le_sum
    intro v _;rw [G.card_incidenceFinset_eq_degree];exact (G.degree_lt_card_verts v).le
   _=S.card*Fintype.card V :=by simp
 have F:=card_le_card d;have H:=card_union_le (X ∪ Y) Z;have D:=card_union_le X Y;omega
lemma sl {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (b:ℕ)(k η :O) (hk:0<=k) (M:0<=η) (L:(b:O)<=k) (i:(b:O)*Fintype.card V<=2 *η* (k-b)^2) (W:k*Fintype.card V +η* (Fintype.card V:O)^2 < (G.edgeFinset.card:O)) (m:∀ v,k < (G.degree v:O)) (g:∀ T:FS V,T.card < Fintype.card V->((G.induce (T:Set V)).edgeFinset.card:O)<=k*T.card+η* (T.card:O)^2):q8 G b:=by
 classical
 intro S X;by_contra r;obtain ⟨A,B,U,P,J,F,D,d,e⟩:=rk G S r;have n:Disjoint (A ∪ B) S :=disjoint_union_left.mpr ⟨F,D⟩
 have j:A.card+B.card+S.card=Fintype.card V :=by
  have h :=CA card d;simpa only [card_union_of_disjoint n,card_union_of_disjoint J,card_univ] using h
 have w:=U.card_pos;have N:=P.card_pos;have h1:=g A (by omega)
 have h0:=g B (by omega)
 have z:(S.card:O)<=b:=by exact_mod_cast X
 obtain ⟨a,C⟩ :=U;obtain ⟨c,I⟩ :=P;have t:=qR G A B S d e a C;have H:=qR G B A S (by rw [union_comm B A];exact d) (fun x Z y hy K=> e y hy x Z K.symm) c I
 have R:(G.degree a:O)<=(A.card:O)+S.card:=by exact_mod_cast t
 have Q:(G.degree c:O)<=(B.card:O)+S.card:=by exact_mod_cast H
 have ha:k- (b:O)<=A.card:=by have:=m a;linarith
 have Y:k- (b:O)<=B.card:=by have:=m c;linarith
 have q:=vp G A B S d e
 have s:(G.edgeFinset.card:O)<=((G.induce (A:Set V)).edgeFinset.card:O)+((G.induce (B:Set V)).edgeFinset.card:O)+(S.card:O)*Fintype.card V :=by
  exact_mod_cast q
 have l:=yr (A.card:O) (B.card:O) (S.card:O) (Fintype.card V:O) k (b:O) η (G.edgeFinset.card:O) (by positivity) (by positivity) (by positivity) hk M (by exact_mod_cast j.symm) z L ha Y i (by linarith)
 exact (not_le_of_gt W) l
lemma sR {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (b:ℕ)(k η :O) (q:0<=k) (m:0<=η) (n:(b:O)<=k) (g:(b:O)*Fintype.card V<=2 *η* (k-b)^2) (A:FS V)(r:k*A.card+η* (A.card:O)^2 < ((G.induce (A:Set V)).edgeFinset.card:O)):∃ S:FS V,S.Nonempty/\k*S.card+η* (S.card:O)^2 < ((G.induce (S:Set V)).edgeFinset.card:O)/\(∀ v:S,k < (G.induce (S:Set V)).degree v)/\q8 (G.induce (S:Set V)) b :=by
 classical
 obtain ⟨S,t,d,l,j⟩:=s5 G k η m A r
 have h:Fintype.card (S:Set V)=S.card:=by
  calc
   Fintype.card (S:Set V)=(S:Set V).ncard:=Nat.card_eq_fintype_card.symm
   _=S.card:=Set.ncard_coe_finset S
 have i:(Fintype.card (S:Set V): O)<=Fintype.card V :=by
  exact_mod_cast Fintype.card_le_of_injective (fun x:(S:Set V)=>x.val) Subtype.val_injective
 have e:(b:O)*Fintype.card (S:Set V)<=2*η* (k-b)^2:= (mul_le_mul_of_nonneg_left i (Nat.cast_nonneg b)).trans g;refine ⟨S,t,d,l,?_⟩;apply sl (G.induce (S:Set V)) b k η q m n e
 · simpa only [h] using d
 · exact l
 · intro T s;exact j T (by simpa only [h] using s)
lemma rc {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (S:FS V):G.edgeFinset.card<=(G.induce (S:Set V)ᶜ).edgeFinset.card+ S.card*Fintype.card V :=by
 classical
 let A :=G.edgeFinset.filter (fun e=>e.toFinset⊆Sᶜ)
 let B :=S.biUnion (fun v=>G.incidenceFinset v)
 have d:G.edgeFinset⊆A ∪ B:=by
  intro e k;by_cases h:e.toFinset⊆Sᶜ
  · exact mem_union_left _ (mem_filter.mpr ⟨k,h⟩)
  · obtain ⟨x,j,l⟩ :=not_subset.mp h
    have g:x∈S:=by simpa only [mem_compl,not_not] using l
    apply mem_union_right;apply mem_biUnion.mpr;refine ⟨x,g,?_⟩;rw [G.incidenceFinset_eq_filter];exact mem_filter.mpr ⟨k,by simpa using j⟩
 have n:A.card= (G.induce (S:Set V)ᶜ).edgeFinset.card:=by
  have h :=CA card (G.map_edgeFinset_induce (s:= (S:Set V)ᶜ));simp only [card_map] at h
  have i:G.edgeFinset ∩ ((S:Set V)ᶜ).toFinset.sym2=A:=by
   simp [A,G.filter_edgeFinset_toFinset_subset]
  rw [i] at h;exact h.symm
 have m:B.card<=S.card*Fintype.card V :=by
  calc
   B.card<=∑ v ∈ S,(G.incidenceFinset v).card:=card_biUnion_le
   _<=∑ _v ∈ S,Fintype.card V :=by
    apply sum_le_sum
    intro v _;rw [G.card_incidenceFinset_eq_degree];exact (G.degree_lt_card_verts v).le
   _=S.card*Fintype.card V :=by simp
 exact (card_le_card d).trans ((card_union_le A B).trans (by omega))
end E5
end _m
section dK
namespace E5.FN
open Filter _root_.Function
variable {α:Type*} [PartialOrder α] [hα:WellFoundedGT α] {f:α->α}
lemma Monotone.eventuallyConst_atTop {ι:Type*} [SemilatticeSup ι] [Nonempty ι] {g:ι->α} (h:Monotone g):EventuallyConst g atTop:=by
 rw [Filter.eventuallyConst_atTop];obtain ⟨x,j⟩ :∃ x,g x=_:=hα.wf.min_mem _ (Set.range_nonempty _);refine ⟨x,fun z i=>?_⟩
 have e:g x<=g z:=h i
 have d:¬g x < g z:=by
  simpa [j] using hα.wf.not_lt_min (Set.range g) (Set.mem_range_self z)
 exact (eq_of_le_of_not_lt e d).symm
lemma rH (d:id<=f) (x:α):EventuallyConst (fun n=>f^[n] x) atTop:= Monotone.eventuallyConst_atTop (fun _ _ h=>monotone_iterate_of_id_le d h x)
noncomputable def ai {f:ℕ->α} (d:EventuallyConst f atTop):=(eventuallyConst_atTop.mp d).choose
noncomputable def rT (d:id<=f) (x:α):ℕ:= ai (rH d x)
lemma wK (d:id<=f) (x:α):∀ m ≥ rT d x,f^[m] x =f^[rT d x] x:=(eventuallyConst_atTop.mp (rH d x)).choose_spec
noncomputable def v3 (d:id<=f) (x:α):=f^[rT d x] x
lemma t0 (d:id<=f) (x:α):IsFixedPt f (v3 d x) :=by unfold IsFixedPt;simp only [v3,<- iterate_succ_apply'];apply wK;simp
lemma tJ (d:id<=f) (x:α):x<=v3 d x :=by
 simp only [v3];conv_lhs=> rw [<- iterate_zero_apply f x]
 apply f.monotone_iterate_of_id_le d;simp
end E5.FN
end dK
section d0
namespace SimpleGraph
open Walk Function E5.FN Finset
open scoped List
variable {V:Type*} [Fintype V] [DecidableEq V] (G:SG V)
def rO:=by
 classical
 exact { (u,v):V × V | G.degree u +G.degree v ≥ (Fintype.card V)/\u≠v/\¬G.Adj u v}
noncomputable def qg:SG V :=by
 classical
 exact if h:(rO G).Nonempty then G ⊔ edge h.some.1 h.some.2
 else G
omit [DecidableEq V] in
lemma s6:G<=qg G :=by
 classical
 unfold qg;split_ifs with h;repeat simp
noncomputable def qE:=E5.FN.v3 s6 G
omit [DecidableEq V] in
lemma sa:(qg G \ G).edgeSet.Subsingleton:=by
 classical
 unfold qg;split_ifs with h
 · simp only [sup_sdiff_left_self,edgeSet_sdiff]
   apply Set.Subsingleton.anti (t:= (edge h.some.1 h.some.2).edgeSet)
   · have:h.some.1≠h.some.2:=h.some_mem.2.1;simp [edgeSet_edge_of_ne this]
   · apply Set.sdiff_subset
 · simp
omit [DecidableEq V] in
lemma xx {u v:V} (k:¬G.Adj u v)(l:G.qg.Adj u v):G.qg.deleteEdges {s(u,v)}=G:=by
 classical
 rw [<- edgeSet_inj];ext e;simp only [edgeSet_deleteEdges,Set.mem_sdiff,Set.mem_singleton_iff];apply Iff.intro
 · rintro ⟨i,j⟩
   by_contra h;have g:e∈(qg G \ G).edgeSet:=by simpa using ⟨i,h⟩
   have d:s(u,v)∈(qg G \ G).edgeSet:=by simpa using ⟨l,k⟩
   exact j <| (sa G) g d
 · intro m
   apply And.intro (edgeSet_mono (s6 G) m)
   intro n;simp only [n,mem_edgeSet] at m;exact k m
omit [DecidableEq V] in
lemma uY:qg G =G↔rO G=∅ :=by
 classical
 unfold qg;split_ifs with h
 · have:(G ⊔ edge h.some.1 h.some.2=G)↔False:=by
    rw [sup_eq_left,iff_false]
    intro e;have d:(edge h.some.1 h.some.2).Adj h.some.1 h.some.2:= (edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,h.some_mem.2.1⟩;exact h.some_mem.2.2 (e d)
   simp only [this,false_iff];simpa [<- Set.not_nonempty_iff_eq_empty] using h
 · simpa [<- Set.not_nonempty_iff_eq_empty] using h
omit [DecidableEq V] in
open Classical in
lemma zF:qg G =G↔∀ {u} {v},u≠v->G.degree u +G.degree v ≥ (Fintype.card V)->G.Adj u v:=by
 classical
 rw [uY];constructor
 · intro g u v d k;by_contra j;have i:(u,v)∈rO G:=⟨k,d,j⟩;rw [g] at i;exact i
 · intro h
   ext ⟨u,v⟩;constructor
   · intro d;exact (d.2.2 (h d.2.1 d.1)).elim
   · intro e;exact e.elim
omit [DecidableEq V] in
open Classical in
lemma zr {u v:V} (m:¬G.Adj u v)(i:G.qg.Adj u v):G.degree u +G.degree v ≥ (Fintype.card V) :=by
 classical
 have ne:(rO G).Nonempty:=by
  by_contra h;simp only [Set.nonempty_iff_ne_empty,<- uY,Decidable.not_not] at h;rw [h] at i;exact m i
 let w :=ne.some;have d:G.degree w.1+G.degree w.2 ≥ (Fintype.card V) :=ne.some_mem.1;have l:s(u,v)∈(qg G \ G).edgeSet:=by simpa using ⟨i,m⟩
 have k:s(w.1,w.2)∈(qg G \ G).edgeSet:=by
  have j:w.1≠w.2:=ne.some_mem.2.1;have g:¬G.Adj w.1 w.2:=ne.some_mem.2.2;have n:G.qg=G ⊔ edge w.1 w.2:=by simp [qg,ne,w]
  simpa [-Prod.mk.eta,n,edge_adj] using And.intro j g
 have e:= (sa G l k).symm;simp only [Prod.mk.eta,Sym2.eq,Sym2.rel_iff'] at e;rcases e with h | h
 · rw [h] at d;simpa using d
 · rw [h] at d;rw [add_comm];simpa using d
omit [DecidableEq V] in
lemma rs:G<=qE G :=by
 classical
 rw [qE];apply E5.FN.tJ
omit [DecidableEq V] in
open Classical in
lemma rK:∀ {u} {v},u≠v->G.qE.degree u +G.qE.degree v ≥ (Fintype.card V)->G.qE.Adj u v:=by
 classical
 have:qg (qE G)=qE G:=t0 s6 G;rwa [zF] at this
variable {G}
namespace Walk
variable {a:V} {p:G.Walk a a}
omit [Fintype V] in
protected lemma IsHamiltonianCycle.aC [Finite V] (d:p.IsHamiltonianCycle) {H:SG V} (h:∀ e ∈ p.edges,e∈H.edgeSet):(p.transfer H h).IsHamiltonianCycle:=by
 classical
 let:=Fintype.ofFinite V;rw [isHamiltonianCycle_iff_isCycle_and_length_eq];exact ⟨d.isCycle.transfer h,by simpa using d.length_eq⟩
omit [DecidableEq V] [Fintype V] in
private lemma IsCycle.rB (v:p.IsCycle) {d e:G.Dart} (w:d∈p.darts)(t:e∈p.darts) (h:d.fst=e.fst):d=e:=by
 classical
 obtain ⟨i,q,rfl⟩ :=List.getElem_of_mem w;obtain ⟨j,r,rfl⟩ :=List.getElem_of_mem t
 have g:p.getVert i =p.getVert j :=by
  simpa [p.darts_getElem_eq_getVert i q,p.darts_getElem_eq_getVert j r] using h
 have m:i<=p.length-1:=by
  have k:i < p.length:=by simpa using q
  omega
 have n:j<=p.length-1:=by
  have l:j < p.length:=by simpa using r
  omega
 have s:=v.getVert_injOn' m n g;subst j;rfl
omit [DecidableEq V] [Fintype V] in
private lemma IsCycle.zU (r:p.IsCycle) {d e:G.Dart} (s:d∈p.darts)(q:e∈p.darts) (h:d.snd=e.snd):d=e:=by
 classical
 obtain ⟨i,l,rfl⟩ :=List.getElem_of_mem s;obtain ⟨j,m,rfl⟩ :=List.getElem_of_mem q
 have g:p.getVert (i+1)=p.getVert (j+1) :=by
  simpa [p.darts_getElem_eq_getVert i l,p.darts_getElem_eq_getVert j m] using h
 have n:i < p.length:=by simpa using l
 have t:j < p.length:=by simpa using m
 have k:=r.getVert_injOn (show 1<=i +1/\i+1<=p.length by omega) (show 1<=j +1/\j+1<=p.length by omega) g
 have:i=j:=Nat.add_right_cancel k;subst j;rfl
omit [DecidableEq V] [Fintype V] in
private lemma uj {u v:V} {r:G.Walk u v} (g:r.support.dropLast.Nodup) {d e:G.Dart} (w:d∈r.darts)(t:e∈r.darts) (k:d.fst=e.fst):d=e:=by
 classical
 obtain ⟨i,n,rfl⟩ :=List.getElem_of_mem w;obtain ⟨j,q,rfl⟩ :=List.getElem_of_mem t;have l:i < r.support.dropLast.length:=by simpa using n
 have m:j < r.support.dropLast.length:=by simpa using q
 have h:r.support.dropLast[i]'l=r.support.dropLast[j]'m:=by
  simpa [r.fst_darts_getElem n,r.fst_darts_getElem q] using k
 have s:= (List.Nodup.getElem_inj_iff g).mp h;subst j;rfl
private lemma rV (h:p.length=Fintype.card V) (i:3<=Fintype.card V) (d:p.support.tail.toFinset=univ):p.IsHamiltonianCycle:=by
 classical
 rw [isHamiltonianCycle_iff_isCycle_and_length_eq];refine ⟨?_,h⟩;rw [isCycle_iff_isPath_tail_and_le_length];refine ⟨?_,by omega⟩
 apply IsPath.mk';rw [support_tail_of_not_nil p (by rw [not_nil_iff_lt_length,h];omega)]
 have g:p.support.tail.toFinset.card=p.support.tail.length:=by
  rw [d];simp [h]
 have e:((p.support.tail:Multiset V).toFinset.card= (p.support.tail:Multiset V).card) :=by simpa using g
 simpa using Multiset.toFinset_card_eq_card_iff_nodup.mp e
namespace IsHamiltonianCycle
omit [Fintype V]
variable (b:V)
private lemma yk (d:p.IsHamiltonianCycle):b∈p.support.tail:=by
 classical
 rw [<- support_tail_of_not_nil p d.not_nil];exact d.isHamiltonian_tail.mem_support b
private lemma zj (e:p.IsHamiltonianCycle):b∈p.support.dropLast:=by
 classical
 have g:b∈p.tail.support:=by
  simpa [support_tail_of_not_nil p e.not_nil] using e.yk b
 have d:b∈p.dropLast.support:= (List.Perm.mem_iff (support_tail_perm_support_dropLast p)).mp g;simpa [support_dropLast e.not_nil] using d
noncomputable def zf (e:p.IsHamiltonianCycle):G.Dart:= Exists.choose <| show ∃ d ∈ p.darts,d.fst=b by
 simpa [<- Walk.map_fst_darts] using e.zj b
noncomputable def qk (d:p.IsHamiltonianCycle):V:= (d.zf b).snd
lemma qH (g:p.IsHamiltonianCycle):∃ d ∈ p.darts,d.fst=b/\d.snd=g.qk b :=by
 classical
 unfold qk zf;generalize_proofs hd;have e:=hd.choose_spec;set d :=hd.choose;exact ⟨d,e.1,e.2,rfl⟩
lemma xe (r:p.IsHamiltonianCycle):Function.Injective r.qk:=by
 classical
 intro l m k;obtain ⟨q,j,g,d⟩ :=r.qH l;obtain ⟨n,i,e,h⟩ :=r.qH m
 have s:q=n:=r.isCycle.zU j i <| by
  rw [d,h];exact k
 rw [<- g,<- e,s]
lemma uE (q:p.IsHamiltonianCycle) {i:ℕ} (r:i < p.length) (l:p.getVert i =b):p.getVert (i+1)=q.qk b :=by
 classical
 have g:i < p.darts.length:=by simpa using r
 have m:p.darts[i]∈p.darts:=List.getElem_mem g;obtain ⟨d,s,j,h⟩ :=q.qH b
 have k:p.darts[i].fst=d.fst:=by
  rw [p.darts_getElem_eq_getVert i g,j];exact l
 have n:=q.isCycle.rB m s k;have e:=CA (fun z:G.Dart=>z.snd) n
 rw [p.darts_getElem_eq_getVert i g,h] at e;exact e
lemma tX (m:p.IsHamiltonianCycle)(q:b∈p.support) (c:V):((m.rotate q).qk c)=m.qk c :=by
 classical
 obtain ⟨j,l,g,d⟩:=(m.rotate q).qH c;obtain ⟨n,k,e,h⟩ :=m.qH c
 have i:j∈p.darts:=by
  simpa using (List.IsRotated.mem_iff (rotate_darts p b q)).mp l
 have r:j=n:=m.isCycle.rB i k <| by
  rw [g,e]
 rw [<- d,<- h,r]
variable {b}
lemma t7 (i:p.IsHamiltonianCycle):i.qk b≠b :=by
 classical
 obtain ⟨d,-,g,e⟩ :=i.qH b
 intro h;exact d.adj.ne (g.trans (e.trans h).symm)
lemma tL (e:p.IsHamiltonianCycle):e.qk (e.qk b)≠b:=by
 classical
 have m:b∈p.support:=e.mem_support b;let q :=p.rotate b m;have d:q.IsHamiltonianCycle:=e.rotate m;have r:3<=q.length:=d.isCycle.three_le_length;have j:q.getVert 0 =b:=by simp [q]
 have g:q.getVert 1 =d.qk b:=d.uE b (i:=0) (by omega) j
 have k:q.getVert 2 =d.qk (d.qk b):=d.uE (d.qk b) (i:=1) (by omega) g
 have l:∀ c,d.qk c =e.qk c :=by
  intro c;change (e.rotate m).qk c =e.qk c;exact IsHamiltonianCycle.tX b e m c
 simp only [l] at g k
 intro h;have n:q.getVert 0 =q.getVert 2 :=by rw [j,k,h]
 have:=d.isCycle.getVert_injOn' (show 0<=q.length-1 by omega) (show 2<=q.length-1 by omega) n
 omega
end IsHamiltonianCycle
end Walk
private lemma zi {u u' v v':V} {p:G.Walk u u'} (T:(Fintype.card V) ≥ 3) (K:p.support ~ univ.toList)(ne:v≠u') (L:G.Adj v u')(M:G.Adj v' u) (d:G.Dart)(R:d∈p.darts) (C:d.fst=v) (H:d.snd=v'):IsHamiltonian G :=by
 classical
 have l:v∈p.support:=by simp [List.Perm.mem_iff K]
 have e:¬(p.dropUntil v l).Nil:=not_nil_of_ne ne
 have m:(p.dropUntil v l).getVert 1 =v':=by
  have n:p.support.Nodup:=by
   rw [List.Perm.nodup_iff K];apply nodup_toList
  have D:p.support.dropLast.Nodup:=p.support.dropLast_prefix.nodup n
  have s:(p.dropUntil v l).firstDart e∈p.darts:=
   p.darts_dropUntil_subset_darts l ((p.dropUntil v l).firstDart_mem_darts e)
  have N:(p.dropUntil v l).firstDart e=d:= uj D s R (by simp [C])
  have J:=CA (fun z:G.Dart=>z.snd) N
  simpa [H] using J
 let q:=(p.takeUntil _ l)
  |>.append L.toWalk
  |>.append (p.dropUntil v l |>.tail |>.reverse.copy rfl m)
  |>.append M.toWalk
 suffices q.IsHamiltonianCycle from fun _=>⟨u,q,this⟩
 apply rV
 · have P:(p.takeUntil v l).length+ (p.dropUntil v l).length=p.length:=by
    have x:=CA Walk.length (p.take_spec l);simpa only [Walk.length_append] using x
   have:=calc
    p.length+1=p.support.length:=by simp
    _=univ.toList.length:=by apply List.Perm.length_eq K
    _= (Fintype.card V) :=by simp
   have:=Walk.length_tail_add_one e;simp [q,add_assoc];omega
 · assumption
 · simp only [tail_support_append,support_cons,support_nil,List.tail_cons,support_copy,support_reverse,List.append_assoc,List.cons_append,List.toFinset_append,List.toFinset_cons,List.toFinset_nil,insert_empty_eq,union_insert,eq_univ_iff_forall,mem_insert,mem_union,List.mem_toFinset,mem_singleton,notMem_empty,false_or,q]
   intro w;by_contra hw;simp only [not_or] at hw;rcases hw with ⟨I,t,F,y⟩
   have j:w∈p.support.tail:=by
    have mem:w∈p.support:=by simp [List.Perm.mem_iff K]
    rw [<- Walk.cons_tail_support] at mem;simp only [List.mem_cons] at mem;exact mem.resolve_left y
   have i:w ∉ (p.dropUntil v l).support.tail:=by
    have g:(p.dropUntil v l).support.tail≠[] :=by
     have Q:0 < (p.dropUntil v l).length:= not_nil_iff_lt_length.mp e;apply List.ne_nil_of_length_pos;rw [List.length_tail,length_support];omega
    have:(p.dropUntil v l).support.tail.getLast g=u':=by
     rw [List.getLast_tail,getLast_support]
    have k:w ∉ (p.dropUntil v l).support.tail.dropLast:=by
     simpa only [List.tail_reverse,List.mem_reverse,support_tail_of_not_nil _ e] using F
    intro r;rw [<- List.dropLast_append_getLast g,this,List.mem_append,List.mem_singleton] at r;exact r.elim k I
   have append:p.support.tail= (p.takeUntil v l).support.tail++ (p.dropUntil v l).support.tail:=by
    rw [<- tail_support_append,take_spec]
   simp only [append,List.mem_append] at j;rcases j with h | h
   · exact t h
   · exact i h
open Classical in
private lemma xN {u v:V} {q:G.qg.Walk u u} (k:q.IsHamiltonianCycle)(D:(Fintype.card V) ≥ 3) (C:G.degree u +G.degree v ≥ (Fintype.card V)) (z:v=k.qk u) (i:¬G.Adj u v):∃ w w' d,G.Adj w v/\G.Adj w' u/\d∈q.darts/\d.fst=w'/\d.snd=w:=by
 classical
 let X:=(k.qk ·) '' {w | G.Adj u w} \ {u}
 let Y:={w | G.Adj v w} \ {k.qk v}
 have s:G.degree u -1<=X.toFinset.card:=calc
  _= (G.neighborFinset u).card-1:=by simp
  _= (univ.filter (G.Adj u)).card-1:=by rw [neighborFinset_eq_filter]
  _<=((univ.filter (G.Adj u)).image (k.qk ·)).card- ({u}:FS _).card:=by
   simp [card_image_of_injective _ k.xe]
  _<=(((univ.filter (G.Adj u)).image (k.qk ·)) \ {u}).card:=by
   apply le_card_sdiff
  _=_:=by simp [X]
 have y:G.degree v -1<=Y.toFinset.card:=calc
  _= (G.neighborFinset v).card-1:=by simp
  _<=(univ.filter (G.Adj v)).card- ({k.qk v}:FS _).card:=by
   simp [neighborFinset_eq_filter]
  _<=(univ.filter (G.Adj v) \ {k.qk v}).card:=by
   apply le_card_sdiff
  _=_:=by simp [Y]
 have j:(X ∪ Y).toFinset.card<=(Fintype.card V)-3:=calc
  _<=({v,k.qk v,u}ᶜ:FS _).card:=by
   apply card_le_card;rw [subset_compl_comm]
   intro w g;simp only [mem_insert,mem_singleton,Set.toFinset_union,Set.toFinset_sdiff,Set.toFinset_image,Set.toFinset_ofPred,Set.toFinset_singleton,compl_union,mem_inter,mem_compl,mem_sdiff,mem_image,mem_filter,mem_univ,true_and,not_and,Decidable.not_not,forall_exists_index,and_imp,X,Y] at g ⊢;apply And.intro
   · intro w' e qk
     rcases g with g | g | g
     · rw [g,z] at qk;rw [k.xe qk] at e;simp at e
     · rw [g] at qk;rw [k.xe qk] at e;exact False.elim (i e)
     · exact g
   · intro e
     rcases g with g | g | g
     · rw [g] at e;simp at e
     · exact g
     · rw [g] at e;exact False.elim (i e.symm)
  _=_:=by
   suffices ({v,k.qk v,u}:FS _).card=3 by rw [card_compl,this]
   rw [card_insert_of_notMem,card_insert_of_notMem]
   · simp
   · simpa [z] using k.tL
   · simpa [z] using And.intro k.t7.symm k.t7
 have l:(X ∩ Y).toFinset.card≠0:=fun h=>by
  suffices (Fintype.card V)-2<=(Fintype.card V)-3 by omega
  calc
   _<=(G.degree u +G.degree v)-2:=Nat.sub_le_sub_right C _
   _<=(G.degree u -1)+(G.degree v -1) :=by omega
   _<=X.toFinset.card+Y.toFinset.card:=add_le_add s y
   _= (X ∪ Y).toFinset.card+ (X ∩ Y).toFinset.card:=by
    simpa [-Set.toFinset_card] using (card_union_add_card_inter _ _).symm
   _<=(Fintype.card V)-3+0:=add_le_add j (le_of_eq h)
   _= (Fintype.card V)-3:=by simp
 obtain ⟨w,g⟩ :=card_ne_zero.mp l;simp only [Set.toFinset_inter,Set.toFinset_sdiff,Set.toFinset_image,Set.toFinset_ofPred,Set.toFinset_singleton,mem_inter,mem_sdiff,mem_image,mem_filter,mem_univ,true_and,mem_singleton,X,Y] at g;rcases g with ⟨⟨⟨w',n,r⟩,-⟩,x,-⟩;obtain ⟨d,t,m⟩ :=k.qH w';rw [r] at m;exact ⟨w,w',d,x.symm,n.symm,t,m⟩
lemma yp (hG:IsHamiltonian (qg G)):IsHamiltonian G :=by
 classical
 by_cases trivial:Fintype.card V =1
 · exact absurd trivial
 · by_contra j
   obtain ⟨a,p,hp⟩ :=hG trivial
   obtain ⟨d,hd,J⟩ :∃ d ∈ p.darts,¬G.Adj d.fst d.snd:=by
    by_contra h;simp only [not_exists,not_and,Decidable.not_not] at h
    have n (e) (he:e∈p.edges):e∈G.edgeSet:=by
     simp only [edges,List.mem_map] at he;obtain ⟨d,hd,J⟩ :=he;rw [<- J];exact h _ hd
    let q :=p.transfer G n;suffices q.IsHamiltonianCycle from j (fun _=>⟨a,q,this⟩)
    exact hp.aC n
   set u :=d.fst;set v :=d.snd;have hu:u∈p.support:=Walk.dart_fst_mem_support_of_mem_darts _ hd;let q :=p.rotate u hu;have H:q.IsHamiltonianCycle:=hp.rotate hu
   have W:d∈q.darts:=by
    simpa [q] using List.IsRotated.mem_iff (rotate_darts p u hu) |>.mpr hd
   have g:¬q.Nil:=by
    erw [nil_rotate];exact hp.1.not_nil
   have m:q.getVert 1 =v:=by
    have Y:q.firstDart g=d:= H.isCycle.rB (q.firstDart_mem_darts g) W (by simp [u])
    have Z:=CA (fun z:G.qg.Dart=>z.snd) Y
    simpa [v] using Z
   have C:s(u,v) ∉ q.tail.edges:=by
    have:q=cons (q.adj_snd g) q.tail:=by
     exact (q.cons_tail_eq g).symm
    have:q.edges=s(u,v) ::q.tail.edges:=by
     simp only [this,edges_cons];simp [m]
    intro h;have M:=H.1.edges_nodup;rw [this] at M;exact List.not_nodup_cons_of_mem h M
   have t:G.qg.deleteEdges {s(u,v)}=G:=by
    exact xx _ J d.adj
   let q':=q.tail
    |>.toDeleteEdge s(u,v) C
    |>.transfer G (by
     simp (config:= {singlePass:=true}) only [<- t];exact edges_subset_edgeSet _)
    |>.copy m rfl
   have K:q'.support ~ univ.toList:=by
    rw [isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one] at H;simp only [transfer_transfer,support_copy,support_transfer,List.perm_iff_count,q']
    intro a;rw [List.count_eq_one_of_mem (nodup_toList _) (by simp)]
    simpa [support_tail_of_not_nil _ g] using H.2 _
   have hV:(Fintype.card V) ≥ 3:=H.length_eq ▸ H.isCycle.three_le_length;have I:=zr G J d.adj
   have R:v=H.qk u :=by
    obtain ⟨d',k,l,P⟩ :=H.qH u;have Y:d=d':= H.isCycle.rB W k (by simpa [u] using l.symm)
    change d.snd=H.qk u;rw [<- P];exact CA (fun z:G.qg.Dart=>z.snd) Y
   obtain ⟨w,w',d',hw,X,Q,k,l⟩:=xN H hV I R J
   have T:q'.support=q.support.tail:=by
    simp [q',support_tail_of_not_nil _ g]
   obtain ⟨i,U,hi⟩ :=List.getElem_of_mem Q;simp only [length_darts] at U;have x:i < q.darts.length:=by simpa using U
   rw [<- hi,q.darts_getElem_eq_getVert i x] at l;rw [<- hi,q.darts_getElem_eq_getVert i x] at k;change q.getVert i =w' at k;change q.getVert (i+1)=w at l
   have h1:i≠0:=by
    rintro rfl;have h0:u=w':=by simpa using k
    exact G.loopless.irrefl _ (h0 ▸ X.symm)
   have r:i-1 < q'.darts.length:=by
    have D:q'.length=q.length-1:=by
     simp [transfer_transfer,length_copy,length_transfer,q']
    simp [D];omega
   have F:(q'.darts[i-1]).fst=w':=by
    rw [q'.darts_getElem_eq_getVert (i-1) r];change q'.getVert (i-1)=w'
    rw [show q'.getVert (i-1)=q.tail.getVert (i-1) by
     simp only [Walk.getVert_eq_getD_support,support_copy,support_transfer,q']]
    rw [q.getVert_tail,show i -1+1=i by omega,k]
   have L:(q'.darts[i-1]).snd=w:=by
    rw [q'.darts_getElem_eq_getVert (i-1) r];change q'.getVert (i-1+1)=w
    rw [show q'.getVert (i-1+1)=q.tail.getVert (i-1+1) by
     simp only [Walk.getVert_eq_getD_support,support_copy,support_transfer,q']]
    rw [q.getVert_tail,show i -1+1+1=i+1 by omega,l]
   have N:w'≠u:=fun eq=>by simp [eq] at X
   have y:= zi hV K N X hw q'.darts[i-1] (List.getElem_mem r) F L;exact j y
private lemma yt {n} (d:¬IsHamiltonian G):¬IsHamiltonian (qg^[n] G) :=by
 classical
 induction n with
 | zero=> simpa
 | succ m ih=>
  rw [add_comm];contrapose ih;simp only [iterate_add_apply,iterate_one] at ih ⊢;exact yp ih
lemma sI:IsHamiltonian (qE G)↔IsHamiltonian G :=by
 classical
 apply Iff.intro <;> intro d
 · unfold qE E5.FN.v3 at d;contrapose d;exact yt d
 · exact IsHamiltonian.mono (rs _) d
private lemma wg (i:3<=Fintype.card V):(⊤ :SG V).IsHamiltonian:=by
 classical
 obtain ⟨r,h⟩ :∃ r,Fintype.card V =r+3:= ⟨Fintype.card V -3,by omega⟩
 let e:Fin (r+3) ≃ V:=by
  simpa [h] using (Fintype.equivFin V).symm
 let f:CG (r+3) →g (⊤ :SG V) :=
  ⟨fun x=>e x,fun {a b} d=>by
   simp only [top_adj,ne_eq];exact e.injective.ne d.ne⟩
 let p:=(cycleGraph.cycle r).map f
 intro _;refine ⟨f 0,p,?_⟩;rw [Walk.isHamiltonianCycle_iff_isCycle_and_length_eq];refine ⟨?_,?_⟩
 · exact cycleGraph.isCycle_cycle.map e.injective
 · simp [p,h]
lemma x3 [DecidableRel G.Adj] (e:(Fintype.card V) ≥ 3) (d:∀ u,2*G.degree u ≥ (Fintype.card V)):G.IsHamiltonian:=by
 classical
 suffices G.qE= (⊤ :SG V) from sI.mp (this ▸ wg e);rw [eq_top_iff]
 intro u v ne;simp only [top_adj,ne_eq] at ne;apply rK G ne
 calc
  (Fintype.card V)<=G.degree u +G.degree v :=by
   have:=d u;have:=d v;omega
  _<=G.qE.degree u +G.qE.degree v :=
   add_le_add (G.degree_le_of_le (v:=u) (rs G)) (G.degree_le_of_le (v:=v) (rs G))
end SimpleGraph
end d0
section _m
namespace E5
open SimpleGraph Finset
open scoped SimpleGraph Classical
lemma wH {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] {u v:V} (p:G.Walk u v)(n:p.IsHamiltonian) (s:3<=Fintype.card V) (k:Fintype.card V<=G.degree u +G.degree v):G.IsHamiltonian:=by
 classical
 have y:=n.length_eq;have l:2<=p.length:=by omega
 have r:u≠v:=by
  intro h;have w:p.getVert 0 =p.getVert p.length:=by simpa using h
  have C:0=p.length:=n.isPath.getVert_injOn (by simp) (by simp) w
  omega
 have i:=G.rs;have d:G.qE.Adj u v:=G.rK r (k.trans (Nat.add_le_add (G.degree_le_of_le (v:=u) i) (G.degree_le_of_le (v:=v) i)));have hsub:∀ e ∈ p.edges,e∈G.qE.edgeSet:= fun _ t=>edgeSet_mono i (p.edges_subset_edgeSet t)
 let p':=p.transfer G.qE hsub
 have j:p'.IsHamiltonian:=by
  apply (n.isPath.transfer hsub).isHamiltonian_of_mem
  intro x;rw [Walk.support_transfer];exact n.mem_support x
 let q :=Walk.cons d.symm p'
 have z:q.IsCycle:=by
  apply (Walk.cons_isCycle_iff p' d.symm).mpr;refine ⟨j.isPath,?_⟩
  intro t;have h :=j.isPath.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ t);have m:p'.length=p.length:=Walk.length_transfer p hsub;omega
 have g:q.IsHamiltonianCycle:=by
  apply Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr;refine ⟨z,?_⟩;dsimp only [q,p'];rw [Walk.length_cons,Walk.length_transfer];omega
 exact (SimpleGraph.sI (G:=G)).mp (fun _=>⟨v,q,g⟩)
lemma s7 {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] {u v:V} (p:G.Walk u v)(j:p.IsPath) (k:2<=p.length) (e:p.length+1<=(G.induce {x | x∈p.support}).degree ⟨u,p.start_mem_support⟩+(G.induce {x | x∈p.support}).degree ⟨v,p.end_mem_support⟩):CG (p.length+1) ⊑ G.induce {x | x∈p.support} :=by
 classical
 let S:Set V:={x | x∈p.support};let p':=p.induce S (fun _ m=>m)
 have h:p'.IsPath:=by
  apply (Walk.isPath_map_iff_of_injective (f:= (Embedding.induce (G:=G) S).toHom) (p:=p') (Embedding.induce (G:=G) S).injective).mp;rw [Walk.map_induce];exact j
 have g:p'.IsHamiltonian:=by
  apply h.isHamiltonian_of_mem
  intro x;rw [Walk.support_induce];simpa only [List.mem_attachWith] using (show x.val∈p.support from x.property)
 have d:Fintype.card S =p.length+1:=by
  have n:S= (p.support.toFinset:Set V) :=by ext x;simp [S]
  calc
   Fintype.card S =S.ncard:=Nat.card_eq_fintype_card.symm
   _=p.support.toFinset.card:=by rw [n,Set.ncard_coe_finset]
   _=p.length+1:=by
    rw [List.toFinset_card_of_nodup j.support_nodup,Walk.length_support]
 have l:=wH (G.induce S) p' g (by rw [d];omega) (by rw [d];exact e)
 obtain ⟨z,q,i⟩ :=l (by rw [d];omega)
 have r:CG (p.length+1) ⊑ G.induce S :=
  (cycleGraph_isContained_iff (by omega)).mpr ⟨z,q,i.isCycle,i.length_eq.trans d⟩
 exact r
lemma uz {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] {u v:V} (p:G.Walk u v)(g:p.IsPath) (e:2<=p.length) (d:p.length+1<=(G.induce {x | x∈p.support}).degree ⟨u,p.start_mem_support⟩+(G.induce {x | x∈p.support}).degree ⟨v,p.end_mem_support⟩):CG (p.length+1) ⊑ G:= (s7 G p g e d).trans (Embedding.induce {x | x∈p.support}).isContained
lemma vK {V:Type*} [Fintype V] [DecidableEq V] (G:SG V)(i:G.Connected) {v:V} (q:G.Walk v v)(m:q.IsCycle) (s:∀ {a b:V} (p:G.Walk a b),p.IsPath->p.length < q.length):G.IsHamiltonian:=by
 classical
 have j:∀ x,x∈q.support:=by
  intro x;by_contra n;obtain ⟨p⟩ :=i.preconnected v x
  obtain ⟨d,_,y,g⟩ :=p.exists_boundary_dart {z | z∈q.support} q.start_mem_support n;let r :=q.rotate d.fst y;have C:r.IsCycle:=m.rotate y
  have e:d.snd ∉ r.tail.support:=by
   intro k
   have h:d.snd∈r.support:=by
    rw [<- Walk.cons_support_tail C.not_nil];exact List.mem_cons_of_mem _ k
   exact g ((q.mem_support_rotate_iff d.fst y).mp h)
  have t:=C.isPath_tail.concat e d.adj;have l:=s _ t
  have w:(r.tail.concat d.adj).length=q.length:=by
   rw [Walk.length_concat,Walk.length_tail,Walk.length_rotate];exact Nat.sub_add_cancel (by have:=m.three_le_length;omega)
  rw [w] at l;exact l.false
 refine fun _=>⟨v,q,⟨m,?_⟩⟩
 apply m.isPath_tail.isHamiltonian_of_mem
 intro x;have n:=j x;rw [<- Walk.cons_tail_support q] at n;rcases List.mem_cons.mp n with rfl | n
 · exact q.tail.end_mem_support
 · rwa [Walk.support_tail_of_not_nil q m.not_nil]
lemma sD {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (S:Set V) [DecidablePred (·∈S)] (v:V)(g:v∈S) (d:∀ w,G.Adj v w->w∈S):(G.induce S).degree ⟨v,g⟩=G.degree v :=by
 classical
 let e:(G.induce S).neighborSet ⟨v,g⟩ ≃ G.neighborSet v :=
  { toFun:=fun w=>⟨w.val.val,w.property⟩
    invFun:=fun w=>⟨⟨w.val,d w.val w.property⟩,w.property⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl}
 rw [<- card_neighborSet_eq_degree,<- card_neighborSet_eq_degree];exact Fintype.card_congr e
lemma sV {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (k:G.Connected) {u v:V} (p:G.Walk u v)(t:p.IsPath) (e:∀ {a b:V} (q:G.Walk a b),q.IsPath->q.length<=p.length) (n:2<=p.length) (m:p.length+1<=G.degree u +G.degree v):G.IsHamiltonian:=by
 classical
 have g:∀ w,G.Adj u w->w∈p.support:=by
  intro w y;by_contra d;have s:(Walk.cons y.symm p).IsPath:= (Walk.cons_isPath_iff _ _).mpr ⟨t,d⟩;have h :=e _ s;simp only [Walk.length_cons] at h;omega
 have l:∀ w,G.Adj v w->w∈p.support:=by
  intro w y;by_contra d;have h :=e _ (t.concat d y);simp only [Walk.length_concat] at h;omega
 have j:=uz G p t n (by
  rw [sD G {x | x∈p.support} u p.start_mem_support g,sD G {x | x∈p.support} v p.end_mem_support l];exact m)
 obtain ⟨x,q,s,i⟩:=(cycleGraph_isContained_iff (by omega)).mp j
 apply vK G k q s
 intro a b r z;rw [i];exact Nat.lt_succ_of_le (e r z)
end E5
end _m
section dh
namespace E5
open SimpleGraph
lemma z8 {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (u:V)(k:2<=G.degree u):∃ (a b:V)(p:G.Walk a b),p.IsPath/\p.length=2:=by
 classical
 have h:1 < (G.neighborFinset u).card:=by
  rw [card_neighborFinset_eq_degree];omega
 obtain ⟨a,j,b,i,g⟩ :=Finset.one_lt_card.mp h;have e:G.Adj u a:= (G.mem_neighborFinset u a).mp j;have d:G.Adj u b:= (G.mem_neighborFinset u b).mp i;let p :=Walk.cons e.symm (Walk.cons d Walk.nil);refine ⟨a,b,p,?_,rfl⟩;simp [p,Walk.cons_isPath_iff,e.ne.symm,d.ne,g]
lemma ur {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (e:G.Connected)(d:ℕ) (t:2<=d) (g:∀ v,d<=G.degree v):∃ (u v:V)(p:G.Walk u v),p.IsPath/\min (2*d+1) (Fintype.card V)<=p.length+1:=by
 classical
 have:Nonempty V :=e.nonempty;obtain ⟨u,v,p,s,i⟩ :=Walk.exists_isPath_forall_isPath_length_le_length G;refine ⟨u,v,p,s,?_⟩;by_contra r;have m:p.length+1 < min (2*d+1) (Fintype.card V) :=by omega
 obtain ⟨a,b,q,j,n⟩ :=z8 G u (t.trans (g u))
 have l:2<=p.length:=by
  have h :=i a b q j;omega
 have k:=sV G e p s (fun {_ _} q j=> i _ _ q j) l (by
  have x:=g u;have w:=g v;omega)
 obtain ⟨z,q,j⟩ :=k (by omega)
 have h :=i _ _ q.tail j.isCycle.isPath_tail;rw [Walk.length_tail,j.length_eq] at h;omega
lemma wk {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (d:∀ {u v} (p:G.Walk u v),p.IsPath->p.length<=1) (v:V):G.degree v<=1 :=by
 classical
 by_contra h;obtain ⟨a,b,p,g,e⟩ :=z8 G v (by omega)
 have:=d p g;omega
lemma vW {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (e:∀ {u v} (p:G.Walk u v),p.IsPath->p.length<=0) (v:V):G.degree v =0:=by
 classical
 by_contra h
 have g:(G.neighborFinset v).Nonempty:=by
  rw [<- Finset.card_pos,card_neighborFinset_eq_degree];omega
 obtain ⟨w,j⟩ :=g;have d:G.Adj v w:= (G.mem_neighborFinset v w).mp j
 have i:(Walk.cons d Walk.nil).IsPath:=by
  simp [Walk.cons_isPath_iff,d.ne]
 have:=e _ i;simp only [Walk.length_cons,Walk.length_nil] at this;omega
lemma tc {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (C:G.ConnectedComponent) [Fintype C] [DecidableRel C.toSimpleGraph.Adj] (v:C):C.toSimpleGraph.degree v =G.degree v.val:=by
 classical
 let e:C.toSimpleGraph.neighborSet v ≃ G.neighborSet v.val:=
  { toFun:=fun w=>⟨w.val.val,w.property⟩
    invFun:=fun w=>⟨⟨w.val,C.mem_supp_of_adj_mem_supp v.property w.property⟩,w.property⟩
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl}
 rw [<- card_neighborSet_eq_degree,<- card_neighborSet_eq_degree];exact Fintype.card_congr e
lemma wP {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (k:ℕ)(r:2<=k) (i:∀ v,k < 2*G.degree v) (j:∀ {u v} (p:G.Walk u v),p.IsPath->p.length<=k) (v:V):G.degree v<=k :=by
 classical
 let C :=G.connectedComponentMk v
 have q:∀ w:C,k/2+1<=C.toSimpleGraph.degree w :=by
  intro w;rw [tc];have h :=i w.val;omega
 obtain ⟨a,b,p,n,m⟩ :=ur C.toSimpleGraph C.connected_toSimpleGraph (k/2+1) (by omega) q
 have l:(p.map C.toSimpleGraph_hom).IsPath:= n.map (by intro x y h;exact Subtype.ext h)
 have d:=j _ l;rw [Walk.length_map] at d;have g:Fintype.card C<=k +1:=by omega
 let v':C:= ⟨v,ConnectedComponent.connectedComponentMk_mem⟩;have e:=C.toSimpleGraph.degree_lt_card_verts v';rw [tc] at e;exact Nat.le_of_lt_succ (e.trans_le g)
lemma vi {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (k:ℕ)(d:∀ v,G.degree v<=k):2*G.edgeFinset.card<=k*Fintype.card V :=by
 classical
 calc
  2*G.edgeFinset.card= ∑ v,G.degree v :=G.sum_degrees_eq_twice_card_edges.symm
  _<=∑ _v:V,k:=Finset.sum_le_sum fun v _=> d v
  _=k*Fintype.card V :=by simp [Nat.mul_comm]
universe u
private lemma a3 (N:ℕ):∀ (V:Type u) [Fintype V] (G:SG V) [DecidableRel G.Adj],Fintype.card V =N->∀ k:ℕ,(∀ {a b:V} (p:G.Walk a b),p.IsPath->p.length<=k)->2*G.edgeFinset.card<=k*Fintype.card V :=by
 classical
 induction N using Nat.strong_induction_on with
 | h N ih=>
  intro V _ G _ m k d
  classical
  by_cases e:k<=1
  · apply vi G k
    intro v;rcases Nat.le_one_iff_eq_zero_or_eq_one.mp e with rfl | rfl
    · exact (vW G d v).le
    · exact wk G d v
  · have t:2<=k:=by omega
    by_cases g:∃ v,2*G.degree v<=k
    · obtain ⟨v,z⟩ :=g
      let S:Set V:={v}ᶜ;let H :=G.induce S
      have C:Fintype.card S =Fintype.card V -1:=by
       simpa [S] using Set.card_ne_eq v
      have r:0 < Fintype.card V :=Fintype.card_pos_iff.mpr ⟨v⟩;have q:Fintype.card S < N :=by omega
      have i:∀ {a b:S} (p:H.Walk a b),p.IsPath->p.length<=k:=by
       intro a b p w;let f:=(Embedding.induce (G:=G) S).toHom
       have n:(p.map f).IsPath:=w.map (by
        intro x y h;exact Subtype.ext h)
       simpa only [Walk.length_map] using d (p.map f) n
      have s:=ih (Fintype.card S) q S H rfl k i
      have l:H.edgeFinset.card+G.degree v =G.edgeFinset.card:=by
       dsimp [H,S];rw [card_edgeFinset_induce_compl_singleton,card_edgeFinset_deleteIncidenceSet];exact Nat.sub_add_cancel (G.degree_le_card_edgeFinset v)
      have j:Fintype.card S +1=Fintype.card V :=by omega
      nlinarith
    · apply vi G k
      apply wP G k t
      · intro v;by_contra h;exact g ⟨v,by omega⟩
      · exact d
lemma ty {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (k:ℕ)(d:∀ {a b:V} (p:G.Walk a b),p.IsPath->p.length<=k):2*G.edgeFinset.card<=k*Fintype.card V:=a3 (FC V) V G rfl k d
lemma z6 {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (k:ℕ)(g:k*Fintype.card V < 2 *G.edgeFinset.card):∃ (a b:V)(p:G.Walk a b),p.IsPath/\k < p.length:=by
 classical
 by_contra h;push Not at h;have e:=ty G k (fun p d=> h _ _ p d)
 omega
end E5
end dh
section db
namespace E5
open Filter
open scoped Topology
lemma y6 {r:O} (d:0<=r) (e:r < 1):Tendsto (fun n:ℕ=> ((n:O)+1)^2*r^n) atTop (𝓝 0) :=by
 have i:=tendsto_pow_const_mul_const_pow_of_lt_one 2 d e;have h:=tendsto_self_mul_const_pow_of_lt_one d e;have g:=tendsto_pow_atTop_nhds_zero_of_lt_one d e;convert (i.add (h.const_mul 2)).add g using 1
 · ext n;ring
 · norm_num
lemma ti (K:ℕ)(j:0 < K) (C:O)(l:0<=C) {r:O} (g:0<=r) (h:r < 1):Tendsto (fun n:ℕ=> (n:O)^2*C*r^ (n/K)) atTop (𝓝 0) :=by
 have hdiv:Tendsto (fun n:ℕ=> n /K) atTop atTop:= Nat.tendsto_div_const_atTop j.ne'
 have d:Tendsto (fun n:ℕ=> ((K:O)^2*C)*(((n/K:ℕ): O)+1)^2*r^ (n/K)) atTop (𝓝 0) :=by
  convert ((y6 g h).comp hdiv).const_mul ((K:O)^2*C) using 1
  · ext n;simp only [Function.comp_apply];ring
  · simp
 apply squeeze_zero (fun n=>by positivity) (fun n=>?_) d
 have m:n<=K* (n/K+1) :=by
  have hmod:=Nat.mod_lt n j;have e:=Nat.mod_add_div n K;nlinarith
 have k:(n:O)<=(K:O)*(((n/K:ℕ): O)+1) :=by
  exact_mod_cast m
 have i:(n:O)^2<=((K:O)*(((n/K:ℕ): O)+1))^2:=by
  gcongr
 calc
  (n:O)^2*C*r^ (n/K)<=((K:O)*(((n/K:ℕ): O)+1))^2*C*r^ (n/K):=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right i l) (pow_nonneg g _)
  _= ((K:O)^2*C)*(((n/K:ℕ): O)+1)^2*r^ (n/K) :=by ring
lemma uW (q:O)(d:0 < q) (e:q<=1) (L K a:ℕ)(j:0 < K):∀ᶠ n:ℕ in atTop,(n:O)^2* (a+1)*(1-q^L)^(n/K) < 1/2:=by
 have g:0<=1-q^L:=sub_nonneg.mpr (pow_le_one₀ d.le e);have i:1-q^L < 1:=by have:=pow_pos d L;linarith
 have h :=ti K j ((a:O)+1) (by positivity) g i
 exact h.eventually (gt_mem_nhds (by norm_num:(0:O) < 1/2))
end E5
end db
section dg
namespace E5
open SimpleGraph Finset Filter
lemma td {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (b d D m a:ℕ)(j:q8 G (b+3*D+3)) (e:qT G (b+3*D+3)) (N:0 < d) (r:∀ w,d+ (b+3*D+3)<=G.degree w) (K:Fintype.card V<=D *d) (g:((a+1)*m)*(12*D+3)<=b) (q:O)(l:0 < q) (k:q<=1) (i:(Fintype.card V:O)^2* (a+1)*(1-q^ (12*D+3))^m < 1/2) (U:0 < Fintype.card V):∃ R:FS V,(R.card:O)<=2*q*Fintype.card V/\∀ u v,u≠v->∀ S,S.card<=a->qZ G (12*D+3) u v (R \ S) :=by
 classical
 let I:={uv:V × V//uv.1≠uv.2};let P:I->FS V->Prop:=fun uv=> qZ G (12*D+3) uv.val.1 uv.val.2
 have t (uv:I) (S:FS V) (C:S.card<=b):∃ T:FS V,P uv T/\T.card<=12*D+3/\Disjoint S T:=
  vz G b d D j e N r K uv.val.1 uv.val.2 uv.property S C
 have W:(Fintype.card I:O)<=(Fintype.card V:O)^2:=by
  have h :=Fintype.card_le_of_injective (fun uv:I=> uv.val) Subtype.val_injective
  rw [Fintype.card_prod] at h;rw [pow_two];exact_mod_cast h
 have J:0<=1-q^ (12*D+3) :=sub_nonneg.mpr (pow_le_one₀ l.le k)
 have M:(Fintype.card I:O)*(a+1)*(1-q^ (12*D+3))^m < 1/2:=by
  apply lt_of_le_of_lt _ i;exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right W (by positivity)) (pow_nonneg J _)
 obtain ⟨R,L,n⟩ :=uA P q l k (12*D+3) b m a g t M U;refine ⟨R,L,?_⟩
 intro u v F S C;obtain ⟨T,y,Q,_,z⟩ :=n ⟨(u,v),F⟩ S C;apply Q.mono
 intro x H;exact mem_sdiff.mpr ⟨y H,fun s=> D1 z s H⟩
lemma xw (D B a:ℕ)(r:0 < B) (q:O)(j:0 < q) (i:q<=1):∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (b d:ℕ),N₀<=Fintype.card V->q8 G (b+3*D+3)->qT G (b+3*D+3)->(∀ w,d+ (b+3*D+3)<=G.degree w)->Fintype.card V<=D *d->Fintype.card V<=B *b->∃ R:FS V,(R.card:O)<=2*q*Fintype.card V/\∀ u v,u≠v->∀ S,S.card<=a->qZ G (12*D+3) u v (R \ S) :=by
 let L :=12*D+3;let K :=B* ((a+1)*L);have x:0 < L:=by dsimp [L];omega
 have t:0 < K:=Nat.mul_pos r (Nat.mul_pos (by omega) x)
 obtain ⟨k,h⟩ :=eventually_atTop.mp (uW q j i L K a t);refine ⟨max k 1,?_⟩
 intro V _ _ G _ b d F C l s y n;have z:0 < Fintype.card V :=by omega
 have g:0 < d:=by nlinarith
 let m :=Fintype.card V /K
 have e:((a+1)*m)*L<=b:=by
  have hmul:B* (((a+1)*m)*L)<=B*b:=by
   calc
    B* (((a+1)*m)*L)=m*K:=by dsimp [K];ring
    _<=Fintype.card V :=Nat.div_mul_le_self _ _
    _<=B*b:=n
  nlinarith
 exact td G b d D m a C l g s y e q j i (h _ (by omega)) z
end E5
end dg
section _m
namespace E5
open SimpleGraph Finset
open scoped SimpleGraph Classical
lemma wL {V:Type*} {G:SG V} (R:FS V)(L k:ℕ) (t:1<=k) (d:∀ u v,u≠v->qZ G L u v R) (e:∀ (w:V)(c:G.Walk w w),c.IsCycle->Odd c.length->c.length<=2*k) {u v:V} (p:G.Walk u v)(j:p.IsPath) (i:∀ x ∈ p.support,x ∉ R):p.length<=2*k:=by
 by_contra l
 have g:u≠v:=by
  intro h;have s:= ((j.nil_iff_eq).mpr h).length_eq_zero;omega
 obtain ⟨c,r,m,q,_⟩ :=sZ p j (by omega) L R i (d u v g)
 have n:=e u c r m;omega
lemma xO {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (R:FS V)(L k:ℕ) (r:1<=k) (l:∀ u v,u≠v->qZ G L u v R) (m:∀ (w:V)(c:G.Walk w w),c.IsCycle->Odd c.length->c.length<=2*k):G.edgeFinset.card<=(k+R.card)*Fintype.card V :=by
 classical
 let U:=(R:Set V)ᶜ;let H :=G.induce U;let f:H ↪g G :=SimpleGraph.Embedding.induce U
 have e {u v:U} (p:H.Walk u v) (s:p.IsPath):p.length<=2*k:=by
  have h :=wL R L k r l m (p.map f.toHom) (s.map f.injective) (by
   intro x q;rw [Walk.support_map,List.mem_map] at q;obtain ⟨y,_,t⟩ :=q;subst x;exact y.property)
  simpa only [Walk.length_map] using h
 have n:=ty H (2*k) e;have i:=Fintype.card_le_of_injective (fun x:U=> x.val) Subtype.val_injective
 have j:H.edgeFinset.card<=k*Fintype.card V :=by
  have hmul:=Nat.mul_le_mul_left k i;nlinarith
 have d:=rc G R;change G.edgeFinset.card<=H.edgeFinset.card+R.card*Fintype.card V at d;nlinarith
lemma ua (D B:ℕ)(r:0 < B) (q:O)(l:0 < q) (j:q<=1):∃ e:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (b d k:ℕ),e<=Fintype.card V->q8 G (b+3*D+3)->qT G (b+3*D+3)->(∀ w,d+ (b+3*D+3)<=G.degree w)->Fintype.card V<=D *d->Fintype.card V<=B *b->1<=k->(∀ (w:V)(c:G.Walk w w),c.IsCycle->Odd c.length->c.length<=2*k)->(G.edgeFinset.card:O)<=(k:O)*Fintype.card V+2*q* (Fintype.card V:O)^2:=by
 obtain ⟨e,g⟩ :=xw D B 0 r q l j;refine ⟨e,?_⟩
 intro V _ _ G _ b d k y F n s C H J I;obtain ⟨R,z,i⟩ :=g G b d y F n s C H
 have h (u v:V) (m:u≠v):qZ G (12*D+3) u v R :=by
  simpa only [sdiff_empty] using i u v m ∅ (by simp)
 have x:=xO G R (12*D+3) k J h I
 have t:(G.edgeFinset.card:O)<=((k:O)+R.card)*Fintype.card V :=by
  exact_mod_cast x
 have K:=mul_le_mul_of_nonneg_right z (Nat.cast_nonneg (FC V):(0:O)<=FC V);nlinarith
end E5
end _m
section cN
namespace E5
open SimpleGraph
universe u
variable {V:Type u} [Fintype V] [DecidableEq V]
variable {G:SG V}
def qh (G:SG V):Prop:= 3<=Fintype.card V/\G.Connected/\∀ v:V,(G.induce ({v}ᶜ:Set V)).Connected
namespace qh
omit [DecidableEq V] in
lemma xV (d:qh G):3<=Fintype.card V :=d.1
omit [DecidableEq V] in
lemma connected (d:qh G):G.Connected:=d.2.1
omit [DecidableEq V] in
lemma t9 (d:qh G)(v:V):(G.induce ({v}ᶜ:Set V)).Connected:= d.2.2 v
omit [DecidableEq V] in
lemma nontrivial (d:qh G):Nontrivial V :=by
 classical
 exact Fintype.one_lt_card_iff_nontrivial.mp (by
  have h :=d.xV;omega)
omit [DecidableEq V] in
lemma exists_ne (d:qh G)(v:V):∃ w:V,w≠v:=by
 classical
 let:=d.nontrivial;exact _root_.exists_ne v
omit [DecidableEq V] in
lemma dU (g:qh G)(v:V):∃ x y:V,x≠v/\y≠v/\x≠y:=by
 classical
 have d:2<=Fintype.card ({v}ᶜ:Set V) :=by
  rw [Fintype.card_compl_set,Set.card_singleton];have h :=g.xV;omega
 let:Nontrivial ({v}ᶜ:Set V):=Fintype.one_lt_card_iff_nontrivial.mp (by omega)
 obtain ⟨x,y,e⟩ :=exists_pair_ne ({v}ᶜ:Set V)
 have j:(x:V)≠v:=by
  simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using x.2
 have i:(y:V)≠v:=by
  simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using y.2
 exact ⟨x,y,j,i,fun h=>e (Subtype.ext h)⟩
omit [DecidableEq V] in
lemma sT (t:qh G)(z:V) {x y:V} (D:x≠z)(v:y≠z):∃ p:G.Walk x y,p.IsPath/\z ∉ p.support:=by
 classical
 let x':({z}ᶜ:Set V):=⟨x,D⟩
 let y':({z}ᶜ:Set V):=⟨y,v⟩;obtain ⟨p,C⟩:=(t.t9 z).exists_isPath x' y'
 let e:G.induce ({z}ᶜ:Set V) ↪g G:=SimpleGraph.Embedding.induce ({z}ᶜ:Set V);let q :=p.map e.toHom;have k:q.IsPath:=C.map e.injective
 have j:z ∉ q.support:=by
  intro s
  have d:q.support=p.support.map e :=by
   exact SimpleGraph.Walk.support_map e.toHom p
  rw [d,List.mem_map] at s;obtain ⟨w,F,r⟩ :=s
  have m:(w:V)≠z:=by
   simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using w.2
  exact m r
 have n:e x'=x:=by rfl
 have l:e y'=y:=by rfl
 let q':G.Walk x y:=q.copy n l;have i:q'.IsPath:= (SimpleGraph.Walk.isPath_copy q n l).2 k
 have h:z ∉ q'.support:=by
  simpa only [q',SimpleGraph.Walk.support_copy] using j
 exact ⟨q',i,h⟩
end qh
structure te (G:SG V) (A B:Set V) where
 a₁:V
 a₂:V
 b₁:V
 b₂:V
 p:G.Walk a₁ b₁
 q:G.Walk a₂ b₂
 p_isPath:p.IsPath
 q_isPath:q.IsPath
 a₁_mem:a₁∈A
 a₂_mem:a₂∈A
 b₁_mem:b₁∈B
 b₂_mem:b₂∈B
 disjoint_support:p.support.Disjoint q.support
 p_interior:∀ x ∈ p.support.tail.dropLast,x ∉ A ∪ B
 q_interior:∀ x ∈ q.support.tail.dropLast,x ∉ A ∪ B
namespace te
variable {A B:Set V}
end te
end E5
namespace E5
open SimpleGraph
lemma qh.iso {V W:Type*} [Fintype V] [Fintype W] {G:SG V} {H:SG W} (i:qh G)(e:G ≃g H):qh H :=by
 classical
 refine ⟨?_,i.connected.map e.toHom e.surjective,?_⟩
 · rw [<- Fintype.card_congr e.toEquiv];exact i.xV
 · intro w
   have d:Set.BijOn e ({e.symm w}ᶜ:Set V) ({w}ᶜ:Set W) :=by
    refine ⟨?_,e.injective.injOn,?_⟩
    · intro x l
      change e x≠w
      intro j;apply l;exact e.injective (j.trans (e.apply_symm_apply w).symm)
    · intro y k
      refine ⟨e.symm y,?_,e.apply_symm_apply y⟩
      intro h;exact k (e.symm.injective h)
   let f :=e.induce d;exact (i.t9 (e.symm w)).map f.toHom f.surjective
end E5
end cN
section dx
namespace E5
open SimpleGraph
universe u
variable {V:Type u} [Fintype V] [DecidableEq V]
variable {G:SG V}
variable {A B S:Set V}
namespace te
end te
namespace qh
end qh
structure x7 (G:SG V) (A B:Set V) where
 a₁:V
 a₂:V
 b₁:V
 b₂:V
 p:G.Walk a₁ b₁
 q:G.Walk a₂ b₂
 p_isPath:p.IsPath
 q_isPath:q.IsPath
 a₁_mem:a₁∈A
 a₂_mem:a₂∈A
 b₁_mem:b₁∈B
 b₂_mem:b₂∈B
 disjoint_support:p.support.Disjoint q.support
namespace x7
structure ee {a b:V} (p:G.Walk a b) (A B:Set V) where
 left:V
 right:V
 walk:G.Walk left right
 isPath:walk.IsPath
 left_mem:left∈A
 right_mem:right∈B
 support_subset:walk.support⊆p.support
 interior:∀ x ∈ walk.support.tail.dropLast,x ∉ A ∪ B
end x7
namespace qh
end qh
end E5
end dx
section cI
namespace E5
open SimpleGraph
variable {V:Type*} {G:SG V}
lemma yg {v:V} {c:G.Walk v v} (Q:c.IsCycle) {a b:V} (K:a∈c.support)(R:b∈c.support) (C:a≠b):∃ (p q:G.Walk a b),p.IsPath/\q.IsPath/\1<=p.length/\1<=q.length/\p.length+q.length=c.length/\(∀ x ∈ p.support,x∈q.support->x=a\/x=b)/\(∀ x,x∈c.support↔x∈p.support\/x∈q.support)/\(∀ e,e∈p.edges->e∈c.edges)/\(∀ e,e∈q.edges->e∈c.edges) :=by
 classical
 let c':G.Walk a a:=c.rotate a K;have F:c'.IsCycle:= (SimpleGraph.Walk.isCycle_rotate K).mpr Q;have j:b∈c'.support:= (SimpleGraph.Walk.mem_support_rotate_iff c a K).mpr R;let p:G.Walk a b:=c'.takeUntil b j;let r:G.Walk b a:=c'.dropUntil b j;let q:G.Walk a b:=r.reverse
 have d:p.append r =c':=by
  exact c'.take_spec j
 have s:p.IsPath:=F.isPath_takeUntil j
 have i:(p.append r).IsCycle:=by
  rw [d];exact F
 have m:r.IsPath:=by
  exact i.isPath_of_append_right (SimpleGraph.Walk.not_nil_of_ne C)
 have n:q.IsPath:=m.reverse
 have y:1<=p.length:=by
  have:0 < p.length:=SimpleGraph.Walk.not_nil_iff_lt_length.mp (SimpleGraph.Walk.not_nil_of_ne C);omega
 have w:1<=q.length:=by
  have:0 < r.length:=SimpleGraph.Walk.not_nil_iff_lt_length.mp (SimpleGraph.Walk.not_nil_of_ne C.symm);have:1<=r.length:=by omega
  simpa [q] using this
 have H:p.length+q.length=c.length:=by
  have:=CA SimpleGraph.Walk.length d;simpa [q,c',SimpleGraph.Walk.length_rotate] using this
 have g:(p.support.tail++r.support.tail).Nodup:=by
  rw [<- SimpleGraph.Walk.tail_support_append];rw [d];exact F.support_nodup
 have z:∀ x ∈ p.support,x∈q.support->x=a\/x=b:=by
  intro x N M;by_contra h;push Not at h;have J:x∈p.support.tail:= (SimpleGraph.Walk.mem_support_iff p).mp N |>.resolve_left h.1
  have L:x∈r.support:=by
   simpa [q,SimpleGraph.Walk.support_reverse] using M
  have I:x∈r.support.tail:= (SimpleGraph.Walk.mem_support_iff r).mp L |>.resolve_left h.2;exact (List.disjoint_of_nodup_append g J I)
 have D:∀ x,x∈c.support↔x∈p.support\/x∈q.support:=by
  intro x;rw [<- SimpleGraph.Walk.mem_support_rotate_iff c a K];change x∈c'.support↔x∈p.support\/x∈q.support;rw [<- d,SimpleGraph.Walk.mem_support_append_iff];simp only [q,SimpleGraph.Walk.support_reverse,List.mem_reverse]
 have t:∀ e:Sym2 V,e∈c'.edges↔e∈c.edges:=fun _=>(SimpleGraph.Walk.rotate_edges c a K).mem_iff
 have l:∀ e,e∈p.edges->e∈c.edges:=by
  intro e P;apply (t e).mp;exact SimpleGraph.Walk.edges_takeUntil_subset_edges c' j P
 have k:∀ e,e∈q.edges->e∈c.edges:=by
  intro e P;apply (t e).mp;apply SimpleGraph.Walk.edges_dropUntil_subset_edges c' j;simpa [q,SimpleGraph.Walk.edges_reverse] using P
 exact ⟨p,q,s,n,y,w,H,z,D,l,k⟩
end E5
end cI
section cL
namespace E5
open SimpleGraph
universe u
variable {V:Type u} [Fintype V] [DecidableEq V]
variable {G:SG V}
def rg (G:SG V)(x y:V):Prop:= ∃ (z:V) (c:G.Walk z z),c.IsCycle/\x∈c.support/\y∈c.support
abbrev sg (V:Type u) :=Sum V Bool
def qA (G:SG V) (A B:Set V):SG (sg V) where
 Adj s t:=
  match s,t with
  | Sum.inl x,Sum.inl y=>G.Adj x y
  | Sum.inl x,Sum.inr false=> x∈A
  | Sum.inr false,Sum.inl x=>x∈A
  | Sum.inl x,Sum.inr true=> x∈B
  | Sum.inr true,Sum.inl x=>x∈B
  | Sum.inr _,Sum.inr _=>False
 symm:= ⟨by
  intro s t h;cases s with
  | inl x =>
   cases t with
   | inl y=>exact h.symm
   | inr i=>cases i <;> exact h
  | inr i =>
   cases t with
   | inl x=>cases i <;> exact h
   | inr k=>cases i <;> cases k <;> exact False.elim h⟩
 loopless:= ⟨by
  intro s h;cases s with
  | inl x=>exact h.ne rfl
  | inr i=>cases i <;> exact False.elim h⟩
omit [DecidableEq V] [Fintype V] in
@[simp] lemma e3 {A B:Set V} {x y:V}:(qA G A B).Adj (Sum.inl x) (Sum.inl y)↔G.Adj x y:= Iff.rfl
omit [DecidableEq V] [Fintype V] in
@[simp] lemma dY {A B:Set V} {x:V}:(qA G A B).Adj (Sum.inl x) (Sum.inr false)↔x∈A:= Iff.rfl
omit [DecidableEq V] [Fintype V] in
@[simp] lemma u2 {A B:Set V} {x:V}:(qA G A B).Adj (Sum.inr false) (Sum.inl x)↔x∈A:= Iff.rfl
omit [DecidableEq V] [Fintype V] in
@[simp] lemma dM {A B:Set V} {x:V}:(qA G A B).Adj (Sum.inl x) (Sum.inr true)↔x∈B:= Iff.rfl
omit [DecidableEq V] [Fintype V] in
@[simp] lemma sJ {A B:Set V} {x:V}:(qA G A B).Adj (Sum.inr true) (Sum.inl x)↔x∈B:= Iff.rfl
def qn (G:SG V) (A B:Set V):G ↪g qA G A B where
 toFun:=Sum.inl
 inj':=Sum.inl_injective
 map_rel_iff':=Iff.rfl
namespace qh
omit [DecidableEq V] in
lemma vX (n:qh G) {x y:V} (j:G.Adj x y):∃ c:G.Walk x x,c.IsCycle/\y∈c.support:=by
 classical
 obtain ⟨r,s,P,L,z⟩ :=n.dU y;let t:V:=if r =x then s else r
 have C:t≠y:=by
  dsimp [t];split <;> assumption
 have D:t≠x:=by
  dsimp [t];split_ifs with hrx
  · exact fun F=>z (hrx.trans F.symm)
  · exact hrx
 obtain ⟨p,Q,v⟩ :=n.sT y j.ne C
 have d:¬ p.Nil:=by
  exact Walk.not_nil_of_ne D.symm
 let w:V:=p.snd;have m:G.Adj x w:=p.adj_snd d
 have I:w≠y:=by
  intro h;exact v (h ▸ List.mem_of_mem_tail (p.snd_mem_tail_support d))
 obtain ⟨e,l,i⟩:=n.sT x j.ne.symm m.ne.symm;let q:G.Walk y x:=e.concat m.symm;have J:q.IsPath:=l.concat i m.symm
 have k:s(x,y) ∉ q.edges:=by
  intro M;have H:s(y,x)∈q.edges:=by simpa [Sym2.eq_swap] using M
  have K:q.length=1:=J.length_eq_one_of_mem_edges H
  have g:e.length=0:=by
   have:q.length=e.length+1:=by simp [q]
   omega
  exact I (e.eq_of_length_eq_zero g).symm
 let c:G.Walk x x:=Walk.cons j q;have N:c.IsCycle:= (Walk.cons_isCycle_iff q j).2 ⟨J,k⟩;refine ⟨c,N,?_⟩;simp [c]
omit [DecidableEq V] [Fintype V] in
private lemma yM {z:V} {c:G.Walk z z} (K:c.IsCycle) {x w t:V} (y:x∈c.support)(L:w∈c.support) (M:t∈c.support)(F:x≠w):∃ r:G.Walk x w,r.IsPath/\t∈r.support/\(∀ v ∈ r.support,v∈c.support) :=by
 classical
 let c':G.Walk x x:=c.rotate x y;have C:c'.IsCycle:=K.rotate y
 have m:w∈c'.support:=by
  simpa [c'] using (c.mem_support_rotate_iff x y).2 L
 have H:t∈c'.support:=by
  simpa [c'] using (c.mem_support_rotate_iff x y).2 M
 let e:G.Walk x w:=c'.takeUntil w m;let d:G.Walk w x:=c'.dropUntil w m;let i:G.Walk x w:=d.reverse;have n:e.IsPath:=C.isPath_takeUntil m
 have s:i.IsPath:=by
  apply Walk.isPath_reverse_iff d |>.mpr
  have g:(e.append d).IsCycle:=by
   simpa [e,d] using C
  exact Walk.IsCycle.isPath_of_append_right (Walk.not_nil_of_ne F) g
 have j:∀ v ∈ e.support,v∈c.support:=by
  intro v I;have q:v∈c'.support:=c'.support_takeUntil_subset_support m I;exact (c.mem_support_rotate_iff x y).1 (by simpa [c'] using q)
 have k:∀ v ∈ i.support,v∈c.support:=by
  intro v I;have J:v∈d.support:=by simpa [i] using I
  have q:v∈c'.support:=c'.support_dropUntil_subset_support m J;exact (c.mem_support_rotate_iff x y).1 (by simpa [c'] using q)
 by_cases l:t∈e.support
 · exact ⟨e,n,l,j⟩
 · refine ⟨i,s,?_,k⟩
   have h:t∈(e.append d).support:=by
    simpa [e,d,Walk.take_spec c' m] using H
   rw [Walk.mem_support_append_iff] at h;have D:t∈d.support:=h.resolve_left l;simpa [i] using D
omit [DecidableEq V] [Fintype V] in
private lemma vT {g x y:V} (L:G.Adj x y)(n:rg G g x) (p:G.Walk y g)(hp:p.IsPath) (J:x ∉ p.support):rg G g y :=by
 classical
 rcases n with ⟨z,c,hc,k,hx⟩;by_cases K:y∈c.support
 · exact ⟨z,c,hc,k,K⟩
 let i:FS V :=c.support.toFinset
 have H:{v∈i | v∈p.support}.Nonempty:=by
  refine ⟨g,?_⟩;simp [i,k]
 obtain ⟨w,M,m,C⟩:=p.exists_mem_support_forall_mem_support_imp_eq i H;have h0:w∈c.support:=by simpa [i] using M
 have U:x≠w:=by
  intro h;exact J (h ▸ m)
 let q:G.Walk y w:=p.takeUntil w m;have hq:q.IsPath:=hp.takeUntil m;obtain ⟨r,hr,t,l⟩:=yM hc hx h0 k U;let e:G.Walk x y:=r.append q.reverse
 have I:r.support.Disjoint q.reverse.support.tail:=by
  rw [List.disjoint_left]
  intro v R j;have Z:v∈c.support:=l v R
  have T:v∈q.support:=by
   have:v∈q.reverse.support:=List.mem_of_mem_tail j;simpa using this
  have h1:v=w:=C v (by simpa [i] using Z) T
  subst v;have X:=hq.reverse.support_nodup.rel_head_tail j;exact X (by simp)
 have F:e.IsPath:=by
  simp only [Walk.isPath_def,e,Walk.support_append];exact List.Nodup.append hr.support_nodup hq.reverse.support_nodup.tail I
 have D:s(y,x) ∉ e.edges:=by
  intro he;simp only [e,Walk.edges_append,List.mem_append] at he;rcases he with N | Y
  · have Q:y∈r.support:=r.fst_mem_support_of_mem_edges N;exact K (l y Q)
  · have W:s(x,y)∈q.edges:=by
     simpa [Walk.edges_reverse,Sym2.eq_swap] using Y
    have P:x∈p.support:=by
     exact p.support_takeUntil_subset_support m (q.fst_mem_support_of_mem_edges W)
    exact J P
 let d:G.Walk y y:=Walk.cons L.symm e;have hd:d.IsCycle:= (Walk.cons_isCycle_iff e L.symm).2 ⟨F,D⟩;refine ⟨y,d,hd,?_,?_⟩
 · have:g∈e.support:=by
    simp only [e,Walk.mem_support_append_iff];exact Or.inl t
   simp only [d,Walk.support_cons,List.mem_cons];exact Or.inr this
 · simp [d]
omit [DecidableEq V] in
private lemma tV (j:qh G) {d x y:V} (h:d≠x)(g:G.Adj x y) (e:rg G d x):rg G d y :=by
 classical
 obtain ⟨p,k,i⟩ :=j.sT x g.ne.symm h;exact vT g e p k i
omit [DecidableEq V] in
private lemma ye (t:qh G) {e x:V}:∀ (l:List V),List.IsChain G.Adj (x::l)->e ∉ x::l->rg G e x->∀ y ∈ x ::l,rg G e y :=by
 classical
 intro l
 induction l generalizing x with
 | nil=>
  intro _ _ d y n;simp only [List.mem_singleton] at n;simpa [n] using d
 | cons v l ih=>
  intro m j d y n;have s:=List.isChain_cons_cons.mp m;have r:G.Adj x v:=s.1;have g:List.IsChain G.Adj (v::l) :=s.2
  have k:e≠x:=by
   intro h;exact j (by simp [h])
  have i:e ∉ v::l:=by
   intro h;exact j (List.mem_cons_of_mem x h)
  have q:rg G e v:=tV t k r d;simp only [List.mem_cons] at n;rcases n with rfl | n
  · exact d
  · exact ih g i q y (by simpa only [List.mem_cons] using n)
omit [DecidableEq V] in
private lemma yI (h:qh G) {d x y:V} (p:G.Walk x y)(i:p.IsPath) (g:d ∉ p.support)(e:rg G d x):rg G d y :=by
 classical
 exact ye h p.support.tail (by rw [p.cons_tail_support];exact p.isChain_adj_support) (by rw [p.cons_tail_support];exact g) e y (by rw [p.cons_tail_support];exact p.end_mem_support)
omit [DecidableEq V] in
lemma ar (g:qh G)(x:V):rg G x x :=by
 classical
 obtain ⟨t,h⟩ :=g.exists_ne x;obtain ⟨p,j⟩ :=g.connected.exists_isPath x t;have d:¬ p.Nil:=Walk.not_nil_of_ne h.symm;have e:G.Adj x p.snd:=p.adj_snd d;obtain ⟨c,i,-⟩ :=g.vX e;exact ⟨x,c,i,c.start_mem_support,c.start_mem_support⟩
omit [DecidableEq V] in
lemma dS (g:qh G)(x y:V):rg G x y :=by
 classical
 by_cases i:x=y
 · subst y;exact g.ar x
 obtain ⟨p,k⟩ :=g.connected.exists_isPath x y;cases p with
 | nil=> exact (i rfl).elim
 | @cons x v y h p =>
  have j:p.IsPath:=k.of_cons;have e:x ∉ p.support:= (Walk.cons_isPath_iff h p).1 k |>.2;obtain ⟨c,m,l⟩ :=g.vX h;have d:rg G x v:=⟨x,c,m,c.start_mem_support,l⟩;exact yI g p j e d
private lemma tB {W:Type*} {H:SG W} (r:W)(h:∀ w:W,Nonempty (H.Walk w r)):H.Connected:=by
 refine { preconnected:= ?_,nonempty:= ⟨r⟩}
 intro u v;obtain ⟨p⟩ :=h u;obtain ⟨q⟩ :=h v;exact ⟨p.append q.reverse⟩
private lemma r0 {W:Type*} {H:SG W} (z r:W)(F:r≠z) (h:∀ w:W,w≠z->∃ p:H.Walk w r,z ∉ p.support):(H.induce ({z}ᶜ:Set W)).Connected:=by
 classical
 let r':({z}ᶜ:Set W):=⟨r,by simpa using F⟩
 refine { preconnected:= ?_,nonempty:= ⟨r'⟩}
 intro u v
 have m:(u:W) ∉ ({z}:Set W) :=u.2
 have g:(v:W) ∉ ({z}:Set W) :=v.2;have D:(u:W)≠z:=fun j=>m (by simpa using j)
 have s:(v:W)≠z:=fun i=>g (by simpa using i)
 obtain ⟨p,y⟩ :=h u D;obtain ⟨q,t⟩ :=h v s;let w:H.Walk u v:=p.append q.reverse
 have C:∀ x ∈ w.support,x∈({z}ᶜ:Set W) :=by
  intro x n;rw [Walk.mem_support_append_iff] at n;simp only [Set.mem_compl_iff,Set.mem_singleton_iff];rcases n with k | l
  · exact fun d=>y (d ▸ k)
  · have e:x∈q.support:=by simpa using l
    exact fun d=>t (d ▸ e)
 let wi:=w.induce ({z}ᶜ:Set W) C;exact ⟨wi.copy (Subtype.ext rfl) (Subtype.ext rfl)⟩
omit [DecidableEq V] [Fintype V] in
private lemma wu (i:G.Connected)(A B:Set V) (x y:V):∃ p:(qA G A B).Walk (Sum.inl x) (Sum.inl y),∀ z ∈ p.support,z∈Set.range (Sum.inl:V->sg V) :=by
 classical
 obtain ⟨p⟩ :=i x y;let r :=p.map (qn G A B).toHom
 have j:∀ z ∈ r.support,z∈Set.range (Sum.inl:V->sg V) :=by
  intro z e;simp only [r,Walk.support_map,List.mem_map] at e;obtain ⟨w,-,rfl⟩ :=e;exact Set.mem_range_self w
 let h:(qn G A B) x =Sum.inl x :=rfl;let g:(qn G A B) y =Sum.inl y :=rfl;let r':=r.copy h g;have d:r'.support=r.support:=Walk.support_copy r h g;refine ⟨r',?_⟩
 intro z e;exact j z (d ▸ e)
omit [DecidableEq V] in
private lemma wr (h:qh G)(A B:Set V) (z:V) {x y:V} (j:x≠z)(i:y≠z):∃ p:(qA G A B).Walk (Sum.inl x) (Sum.inl y),Sum.inl z ∉ p.support:=by
 classical
 obtain ⟨p,-,e⟩ :=h.sT z j i;refine ⟨p.map (qn G A B).toHom,?_⟩
 intro d;change (qn G A B) z∈(p.map (qn G A B).toHom).support at d;rw [Walk.support_map,List.mem_map] at d;obtain ⟨w,k,g⟩ :=d;exact e ((Sum.inl_injective g) ▸ k)
omit [DecidableEq V] [Fintype V] in
private lemma tF (d:G.Connected) {A B:Set V} (h:A.Nonempty)(g:B.Nonempty):(qA G A B).Connected:=by
 classical
 obtain ⟨a,j⟩ :=h;obtain ⟨b,e⟩ :=g;apply tB (H:=qA G A B) (Sum.inl a)
 intro w;cases w with
 | inl x =>
  obtain ⟨p,-⟩ :=wu d A B x a;exact ⟨p⟩
 | inr i =>
  cases i with
  | false=> exact ⟨Walk.cons (u2.mpr j) Walk.nil⟩
  | true=>
   obtain ⟨p,-⟩ :=wu d A B b a;exact ⟨Walk.cons (sJ.mpr e) p⟩
omit [DecidableEq V] in
private lemma xh (h:qh G) {A B:Set V} (q:2<=A.ncard) (n:2<=B.ncard) (z:V):((qA G A B).induce ({Sum.inl z}ᶜ:Set (sg V))).Connected:=by
 classical
 obtain ⟨a,m,e⟩ :=A.exists_ne_of_one_lt_ncard (by omega) z
 obtain ⟨b,j,g⟩ :=B.exists_ne_of_one_lt_ncard (by omega) z
 apply r0 (H:=qA G A B) (Sum.inl z) (Sum.inl a) (by simpa)
 intro w l;cases w with
 | inl x =>
  have d:x≠z:=by
   intro d;exact l (by simp [d])
  exact wr h A B z d e
 | inr i =>
  cases i with
  | false=>
   refine ⟨Walk.cons (u2.mpr m) Walk.nil,?_⟩;simp [e.symm]
  | true=>
   obtain ⟨p,k⟩ :=wr h A B z g e;refine ⟨Walk.cons (sJ.mpr j) p,?_⟩;simpa using k
omit [DecidableEq V] [Fintype V] in
private lemma wV (g:G.Connected) {A B:Set V} (j:B.Nonempty):((qA G A B).induce ({Sum.inr false}ᶜ:Set (sg V))).Connected:=by
 classical
 obtain ⟨b,e⟩ :=j;apply r0 (H:=qA G A B) (Sum.inr false) (Sum.inl b) (by simp)
 intro w l;cases w with
 | inl x =>
  obtain ⟨p,d⟩ :=wu g A B x b;refine ⟨p,?_⟩
  intro h;obtain ⟨y,k⟩ :=d _ h;cases k
 | inr i =>
  cases i with
  | false=> exact (l rfl).elim
  | true=>
   refine ⟨Walk.cons (sJ.mpr e) Walk.nil,?_⟩;simp
omit [DecidableEq V] [Fintype V] in
private lemma wI (e:G.Connected) {A B:Set V} (g:A.Nonempty):((qA G A B).induce ({Sum.inr true}ᶜ:Set (sg V))).Connected:=by
 classical
 obtain ⟨a,l⟩ :=g;apply r0 (H:=qA G A B) (Sum.inr true) (Sum.inl a) (by simp)
 intro w k;cases w with
 | inl x =>
  obtain ⟨p,d⟩ :=wu e A B x a;refine ⟨p,?_⟩
  intro h;obtain ⟨y,j⟩ :=d _ h;cases j
 | inr i =>
  cases i with
  | false=>
   refine ⟨Walk.cons (u2.mpr l) Walk.nil,?_⟩;simp
  | true=> exact (k rfl).elim
omit [DecidableEq V] in
lemma yK (g:qh G) {A B:Set V} (k:2<=A.ncard) (j:2<=B.ncard):qh (qA G A B) :=by
 classical
 have e:A.Nonempty:= (Set.ncard_pos (Set.toFinite A)).mp (by omega)
 have d:B.Nonempty:= (Set.ncard_pos (Set.toFinite B)).mp (by omega)
 refine ⟨?_,tF g.connected e d,?_⟩
 · have h:=g.xV;simp [sg];omega
 · intro z
   cases z with
   | inl x=>exact xh g k j x
   | inr i =>
    cases i with
    | false=> exact wV g.connected d
    | true=> exact wI g.connected e
private structure w5 (G:SG V) (A B:Set V)
 (p:(qA G A B).Walk (Sum.inr false) (Sum.inr true)) where
 a:V
 b:V
 walk:(qA G A B).Walk (Sum.inl a) (Sum.inl b)
 isPath:walk.IsPath
 a_mem:a∈A
 b_mem:b∈B
 support_subset_tail:walk.support⊆p.support.tail
 old_support:∀ x ∈ walk.support,x∈Set.range (Sum.inl:V->sg V)
omit [DecidableEq V] [Fintype V] in
private lemma ya {A B:Set V} (p:(qA G A B).Walk (Sum.inr false) (Sum.inr true)) (K:p.IsPath):Nonempty (w5 G A B p) :=by
 classical
 have d:¬p.Nil:=Walk.not_nil_of_ne (by simp)
 have n:p.tail.IsPath:=K.tail
 have e:¬p.tail.Nil:=by
  intro H;have F:p.snd=Sum.inr true:=n.nil_iff_eq.mp H;have w:=p.adj_snd d;rw [F] at w;simp [qA] at w
 have J:p.tail.penultimate=p.penultimate:=by
  have h :=Walk.penultimate_cons_of_not_nil (p.adj_snd d) p.tail e;rw [p.cons_tail_eq d] at h;exact h.symm
 have j:=p.adj_snd d;have g:=p.adj_penultimate d;cases hs:p.snd with
 | inr i =>
  rw [hs] at j;cases i <;> simp [qA] at j
 | inl a =>
  rw [hs] at j;cases ht:p.penultimate with
  | inr i =>
   rw [ht] at g;cases i <;> simp [qA] at g
  | inl b =>
   rw [ht] at g;have M:a∈A:=by simpa using j
   have L:b∈B:=by simpa using g
   let k:=p.tail.dropLast;have C:k.IsPath:=K.tail.dropLast;have y:p.tail.penultimate=Sum.inl b :=J.trans ht;let m:(qA G A B).Walk (Sum.inl a) (Sum.inl b):=k.copy hs y
   have q:m.support⊆p.support.tail:=by
    intro x D;have l:x∈k.support:=by simpa [m] using D
    have s:x∈p.tail.support.dropLast:=by
     simpa [k,Walk.support_dropLast e] using l
    have t:x∈p.tail.support:=List.mem_of_mem_dropLast s;simpa [p.support_tail_of_not_nil d] using t
   have r:Sum.inr false ∉ p.support.tail:=by
    have I:=K.support_nodup;rw [<- p.cons_tail_support] at I;exact (List.nodup_cons.mp I).1
   have z:Sum.inr true ∉ m.support:=by
    intro D;have l:Sum.inr true∈k.support:=by simpa [m] using D
    have I:=K.tail.support_nodup;rw [<- p.tail.support_dropLast_concat e] at I;exact I.disjoint l (by simp)
   refine ⟨{
    a:=a
    b:=b
    walk:=m
    isPath:=by simpa [m] using C
    a_mem:=M
    b_mem:=L
    support_subset_tail:=q
    old_support:= ?_}⟩
   intro x D;cases x with
   | inl v=>exact ⟨v,rfl⟩
   | inr i =>
    cases i with
    | false=> exact (r (q D)).elim
    | true=> exact (z D).elim
omit [DecidableEq V] [Fintype V] in
private lemma ad {A B:Set V} {a b:V} (p:(qA G A B).Walk (Sum.inl a) (Sum.inl b)) (i:∀ x ∈ p.support,x∈Set.range (Sum.inl:V->sg V)):∃ q:G.Walk a b,q.map (qn G A B).toHom=p:=by
 classical
 let e :=qn G A B
 have d:∀ x ∈ p.support,x∈Set.range e :=by
  intro x m;obtain ⟨v,l⟩ :=i x m;refine ⟨v,?_⟩;change Sum.inl v =x;exact l
 let p':=p.induce (Set.range e) d;let g:=p'.map e.isoInduceRange.symm.toHom
 have k:e.isoInduceRange.symm ⟨Sum.inl a,Set.mem_range_self a⟩=a:=by
  exact e.isoInduceRange.symm_apply_apply a
 have j:e.isoInduceRange.symm ⟨Sum.inl b,Set.mem_range_self b⟩=b:=by
  exact e.isoInduceRange.symm_apply_apply b
 let q:G.Walk a b:=g.copy k j;refine ⟨q,?_⟩;apply Walk.ext_support
 calc
  (q.map (qn G A B).toHom).support= (g.map e.toHom).support:=by
   simp [q,e]
  _=p.support:=by
   simp only [g,Walk.support_map,List.map_map];change List.map (fun x:Set.range e=>e (e.isoInduceRange.symm x)) p'.support=p.support
   have h:(fun x:Set.range e=>e (e.isoInduceRange.symm x))=(fun x:Set.range e=>(x:sg V)) :=by
    funext x;exact CA Subtype.val (e.isoInduceRange.apply_symm_apply x)
   rw [h];change ((p.induce (Set.range e) d).support.map Subtype.val)=p.support;rw [Walk.support_induce];exact List.attachWith_map_subtype_val d
omit [DecidableEq V] [Fintype V] in
private lemma w5.tw {A B:Set V} {p:(qA G A B).Walk (Sum.inr false) (Sum.inr true)} (S:w5 G A B p):∃ q:G.Walk S.a S.b,q.IsPath/\q.map (qn G A B).toHom=S.walk:=by
 classical
 obtain ⟨q,e⟩ :=ad S.walk S.old_support;refine ⟨q,?_,e⟩
 have d:(q.map (qn G A B).toHom).IsPath:=by
  rw [Walk.isPath_def,e];exact S.isPath.support_nodup
 exact (Walk.isPath_map_iff_of_injective (f:= (qn G A B).toHom) (qn G A B).injective).mp d
omit [DecidableEq V] in
lemma yF (J:qh G) {A B:Set V} (L:2<=A.ncard) (D:2<=B.ncard):Nonempty (x7 G A B) :=by
 classical
 let H :=qA G A B;have I:qh H :=J.yK L D;obtain ⟨z,c,K,k,g⟩:=I.dS (Sum.inr false) (Sum.inr true);obtain ⟨p,q,M,F,-,-,-,l,-,-,-⟩:=yg K k g (by simp)
 obtain ⟨P⟩ :=ya p M;obtain ⟨Q⟩ :=ya q F;obtain ⟨pG,C,r⟩ :=P.tw;obtain ⟨qG,y,m⟩ :=Q.tw
 have n:pG.support.Disjoint qG.support:=by
  rw [List.disjoint_left]
  intro x w v
  have s:Sum.inl x∈P.walk.support:=by
   have d:(qn G A B) x∈(pG.map (qn G A B).toHom).support:=by
    rw [Walk.support_map];exact List.mem_map.mpr ⟨x,w,rfl⟩
   rw [r] at d;exact d
  have t:Sum.inl x∈Q.walk.support:=by
   have e:(qn G A B) x∈(qG.map (qn G A B).toHom).support:=by
    rw [Walk.support_map];exact List.mem_map.mpr ⟨x,v,rfl⟩
   rw [m] at e;exact e
  have i:Sum.inl x∈p.support:= List.mem_of_mem_tail (P.support_subset_tail s);have j:Sum.inl x∈q.support:= List.mem_of_mem_tail (Q.support_subset_tail t);rcases l (Sum.inl x) i j with h | h <;> simp at h
 exact ⟨{
  a₁:=P.a
  a₂:=Q.a
  b₁:=P.b
  b₂:=Q.b
  p:=pG
  q:=qG
  p_isPath:=C
  q_isPath:=y
  a₁_mem:=P.a_mem
  a₂_mem:=Q.a_mem
  b₁_mem:=P.b_mem
  b₂_mem:=Q.b_mem
  disjoint_support:=n}⟩
end qh
end E5
end cL
section _m
namespace E5
open SimpleGraph Finset
open scoped SimpleGraph Classical
private lemma y4 (A B C:Prop):((A↔B)↔(B↔C))↔(A↔C) :=by tauto
lemma xt {V:Type*} {G:SG V} (S:Set V)(colour:S->Bool) {u v:S} (p:G.Walk u.val v.val)(K:p.IsPath) (d:¬ (Even p.length↔(colour u↔colour v))):∃ a b:S,a.val≠b.val/\∃ q:G.Walk a.val b.val,q.IsPath/\¬ (Even q.length↔(colour a↔colour b))/\q.length<=p.length/\∀ z ∈ q.support,z≠a.val->z≠b.val->z ∉ S:=by
 classical
 let P (m:ℕ):Prop:= ∃ a b:S,∃ q:G.Walk a.val b.val,q.IsPath/\¬ (Even q.length↔(colour a↔colour b))/\q.length=m;have t:∃ m,P m:= ⟨p.length,u,v,p,K,d,rfl⟩;obtain ⟨a,b,q,w,j,n⟩ :=Nat.find_spec t
 have i {x y:S} (r:G.Walk x.val y.val) (l:r.IsPath) (H:¬ (Even r.length↔(colour x↔colour y))):q.length<=r.length:=by
  rw [n];exact Nat.find_min' t ⟨x,y,r,l,H,rfl⟩
 have e {x y:S} (r:G.Walk x.val y.val) (l:r.IsPath) (C:r.length < q.length):Even r.length↔(colour x↔colour y) :=by
  by_contra H;exact (Nat.not_le_of_gt C) (i (x:=x) (y:=y) r l H)
 have J:a.val≠b.val:=by
  intro h;have M:a=b:=Subtype.ext h;subst b;have g:= (Walk.isPath_iff_nil.mp w).length_eq_zero;exact j (by simp [g])
 refine ⟨a,b,J,q,w,j,i (x:=u) (y:=v) p K d,?_⟩
 intro z g I D F;let x:S:= ⟨z,F⟩;let r:G.Walk a.val x.val:=q.takeUntil z g;let s:G.Walk x.val b.val:=q.dropUntil z g;have l:=e (x:=a) (y:=x) r (w.takeUntil g) (q.length_takeUntil_lt_length g D);have L:=e (x:=x) (y:=b) s (w.dropUntil g) (q.length_dropUntil_lt_length g I)
 have k:q.length=r.length+s.length:=by
  have h :=CA Walk.length (q.take_spec g);simpa only [Walk.length_append] using h.symm
 apply j;rw [k,Nat.even_add,l,L];exact y4 _ _ _
lemma xC {V:Type*} {G:SG V} (S:Set V)(colour:(G.induce S).Coloring Bool) {u v:S} (p:(G.induce S).Walk u v) (y:p.IsPath)(k:1 < p.length) (q:G.Walk u.val v.val)(C:q.IsPath) (r:∀ z ∈ q.support,z≠u.val->z≠v.val->z ∉ S) (e:¬ (Even q.length↔(colour u↔colour v))):∃ c:G.Walk u.val u.val,c.IsCycle/\Odd c.length/\p.length<=c.length:=by
 let f:G.induce S ↪g G:={ toFun:=Subtype.val,inj':=Subtype.val_injective,map_rel_iff':=Iff.rfl}
 have n (z:V) (w:z∈(p.map f.toHom).support):z∈S:=by
  rw [Walk.support_map,List.mem_map] at w;obtain ⟨x,_,D⟩ :=w;subst z;exact x.property
 have d:((p.map f.toHom).append q.reverse).IsCycle:=by
  apply qy (p.map f.toHom) q (y.map f.injective) C (by simpa only [Walk.length_map] using k)
  intro z l s;by_cases j:z=u.val
  · exact Or.inl j
  by_cases i:z=v.val
  · exact Or.inr i
  exact (r z s j i (n z l)).elim
 have t:p.length%2≠q.length%2:=by
  intro h;apply e
  have m:Even q.length↔Even p.length:=by
   simp only [Nat.even_iff];omega
  exact m.trans (colour.even_length_iff_congr p)
 refine ⟨(p.map f.toHom).append q.reverse,d,?_,?_⟩
 · apply Nat.odd_iff.mpr;change ((p.map f.toHom).append q.reverse).length%2=1;simp only [Walk.length_append,Walk.length_map,Walk.length_reverse];omega
 · change p.length<=((p.map f.toHom).append q.reverse).length;simp only [Walk.length_append,Walk.length_map,Walk.length_reverse];omega
lemma ve {V:Type*} [Fintype V] {G:SG V} (M:qh G)(d:¬ G.Colorable 2) (S:Set V)(Q:2<=S.ncard) (colour:S->Bool):∃ a b:S,∃ p:G.Walk a.val b.val,p.IsPath/\¬ (Even p.length↔(colour a↔colour b)) :=by
 classical
 obtain ⟨w,c,l,D⟩ :∃ (w:V) (c:G.Walk w w),c.IsCycle/\Odd c.length:=by
  by_contra h;apply d;apply (xJ G).mpr
  intro w c l D;exact h ⟨w,c,l,D⟩
 let C:Set V:={z | z∈c.support}
 have J:C.Nontrivial:=by
  refine ⟨w,c.start_mem_support,c.snd,?_,(c.adj_snd l.not_nil).ne⟩;exact List.mem_of_mem_tail (Walk.snd_mem_tail_support l.not_nil)
 have e:2<=C.ncard:=Set.one_lt_ncard_iff_nontrivial.mpr J;obtain ⟨P⟩ :=M.yF Q e;obtain ⟨x,t,p,U,_,i,n⟩:=rq P.p P.p_isPath C P.b₁_mem;obtain ⟨y,I,q,K,_,g,F⟩:=rq P.q P.q_isPath C P.b₂_mem;have k (z:V) (m:z∈p.support) (v:z∈q.support):False:= P.disjoint_support (i m) (g v)
 have H:x≠y:=by
  intro h;exact k x p.end_mem_support (h ▸ q.end_mem_support)
 obtain ⟨r,s,L,T,j,_,_,_,_⟩:=rE c l D p q U K t I H n F k;let a:S:= ⟨P.a₁,P.a₁_mem⟩;let b:S:= ⟨P.a₂,P.a₂_mem⟩;by_cases h:Even r.length↔(colour a↔colour b)
 · refine ⟨a,b,s,T,?_⟩
   intro R;have N:=h.trans R.symm;simp only [Nat.even_iff] at N;apply j;omega
 · exact ⟨a,b,r,L,h⟩
lemma vu {V:Type*} [Fintype V] {G:SG V} (i:qh G)(d:¬ G.Colorable 2) (S:Set V)(m:2<=S.ncard) (colour:S->Bool):∃ a b:S,a.val≠b.val/\∃ p:G.Walk a.val b.val,p.IsPath/\¬ (Even p.length↔(colour a↔colour b))/\∀ z ∈ p.support,z≠a.val->z≠b.val->z ∉ S:=by
 classical
 obtain ⟨u,v,p,k,l⟩ :=ve i d S m colour;obtain ⟨a,b,e,q,j,h,_,g⟩:=xt S colour (u:=u) (v:=v) p k l;exact ⟨a,b,e,q,j,h,g⟩
lemma ub {V:Type*} [DecidableEq V] {G:SG V} (L:ℕ)(R:FS V) (j:∀ x y S,S.card<=L+1->qY G L x y (R \ S)) (u v:V)(M:u≠v) {a b:V} (p:G.Walk a b)(Y:p.IsPath) (W:0 < p.length) (g:∀ x ∈ p.support,x ∉ R/\x≠u/\x≠v):∃ q:G.Walk u v,q.IsPath/\p.length<=q.length/\q.length<=p.length+2*L:=by
 classical
 have T:a≠b:=by
  intro h;have X:= ((Y.nil_iff_eq).mpr h).length_eq_zero;omega
 have h1:a≠u:= (g a p.start_mem_support).2.1;have t:a≠v:= (g a p.start_mem_support).2.2;have h0:b≠u:= (g b p.end_mem_support).2.1
 obtain ⟨r,hr,K,D⟩ :=j u a {v} (by simp)
 have N:v ∉ r.support:=by
  intro hv;have h :=D v hv M.symm t.symm;exact (mem_sdiff.mp h).2 (mem_singleton_self v)
 have w (z:V) (d:z∈r.support) (e:z∈p.support):z=a:=by
  by_contra P;have U:= (g z e).2.1;exact (g z e).1 (mem_sdiff.mp (D z d U P)).1
 have Q:b ∉ r.support:=by
  intro h;exact T (w b h p.end_mem_support).symm
 have m:r.support.toFinset.card<=L+1:=by
  have h :=List.toFinset_card_le r.support;rw [r.length_support] at h;omega
 obtain ⟨s,hs,F,n⟩ :=j v b r.support.toFinset m
 have I (z:V) (d:z∈r.support) (i:z∈s.support):False:=by
  have k:z≠v:=fun h=>N (h ▸ d)
  have l:z≠b:=fun h=>Q (h ▸ d)
  exact (mem_sdiff.mp (n z i k l)).2 (List.mem_toFinset.mpr d)
 have J (z:V) (e:z∈p.support) (i:z∈s.support):z=b:=by
  by_contra l;have k:= (g z e).2.2;exact (g z e).1 (mem_sdiff.mp (n z i k l)).1
 have H:(r.append p).IsPath:=qr r p hr Y w
 have Z:((r.append p).append s.reverse).IsPath:=by
  apply qr (r.append p) s.reverse H hs.reverse
  intro z X C
  have i:z∈s.support:=by
   simpa only [Walk.support_reverse,List.mem_reverse] using C
  rcases (Walk.mem_support_append_iff _ _).mp X with d | e
  · exact (I z d i).elim
  · exact J z e i
 refine ⟨(r.append p).append s.reverse,Z,?_,?_⟩ <;>
  simp only [Walk.length_append,Walk.length_reverse] <;> omega
end E5
end _m
section cK
namespace E5
open SimpleGraph Filter
lemma sh (D B a:ℕ)(C:0 < D) (r:0 < B) (q:O)(k:0 < q) (j:q<=1):∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (b d:ℕ),N₀<=Fintype.card V->q8 G b->(∀ w,d+b<=G.degree w)->Fintype.card V<=D *d->Fintype.card V<=B *b->∃ R:FS V,(R.card:O)<=2*q*Fintype.card V/\∀ u v S,S.card<=a->qY G (3*D) u v (R \ S) :=by
 let L :=3*D;let K :=B* ((a+1)*L);have x:0 < L:=by dsimp [L];omega
 have t:0 < K:=Nat.mul_pos r (Nat.mul_pos (by omega) x)
 obtain ⟨l,i⟩ :=eventually_atTop.mp (uW q k j L K a t);refine ⟨max l 1,?_⟩
 intro V _ _ G _ b d F z s H n;have y:0 < Fintype.card V :=by omega
 have g:0 < d:=by nlinarith
 let m :=Fintype.card V /K
 have e:((a+1)*m)*L<=b:=by
  have hmul:B* (((a+1)*m)*L)<=B*b:=by
   calc
    B* (((a+1)*m)*L)=m*K:=by dsimp [K];ring
    _<=Fintype.card V :=Nat.div_mul_le_self _ _
    _<=B*b:=n
  nlinarith
 have h:3*Fintype.card V<=d *L:=by dsimp [L];nlinarith
 exact zM G b d L m a z g s h e q k j (i _ (by omega)) y
end E5
end cK
section _m
namespace E5
open SimpleGraph Finset
open scoped SimpleGraph Classical
lemma vA {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (L k:ℕ)(R:FS V) (j:∀ x y S,S.card<=L+1->qY G L x y (R \ S)) (I:(k+R.card+2)*Fintype.card V < G.edgeFinset.card) (u v:V)(s:u≠v):∃ p:G.Walk u v,p.IsPath/\2*k < p.length:=by
 classical
 let S :=insert u (insert v R);let U:=(S:Set V)ᶜ;let H :=G.induce U
 have C:S.card<=R.card+2:=by
  have J:=card_insert_le u (insert v R);have K:=card_insert_le v R;dsimp [S];omega
 have d:=rc G S;change G.edgeFinset.card<=H.edgeFinset.card+S.card*Fintype.card V at d;have hmul:=Nat.mul_le_mul_right (Fintype.card V) C;have F:k*Fintype.card V < H.edgeFinset.card:=by nlinarith
 have i:=Fintype.card_le_of_injective (fun x:U=> x.val) Subtype.val_injective
 have t:(2*k)*Fintype.card U < 2 *H.edgeFinset.card:=by
  have r:=Nat.mul_le_mul_left k i;nlinarith
 obtain ⟨a,b,p,D,e⟩ :=z6 H (2*k) t;let f:H ↪g G :=SimpleGraph.Embedding.induce U
 have n (x:V) (w:x∈(p.map f.toHom).support):x ∉ R/\x≠u/\x≠v:=by
  rw [Walk.support_map,List.mem_map] at w;obtain ⟨y,_,M⟩ :=w;subst x;have h :=y.property;change y.val ∉ insert u (insert v R) at h;simp only [mem_insert,not_or] at h;exact ⟨h.2.2,h.1,h.2.1⟩
 have m:0 < (p.map f.toHom).length:=by
  simpa only [Walk.length_map] using (Nat.lt_of_le_of_lt (Nat.zero_le _) e)
 obtain ⟨q,z,l,_⟩ :=ub L R j u v s (p.map f.toHom) (D.map f.injective) m n;simp only [Walk.length_map] at l;exact ⟨q,z,e.trans_le l⟩
lemma w1 (D B:ℕ)(x:0 < D) (s:0 < B) (q:O)(j:0 < q) (i:q<=1):∃ e:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (b d k:ℕ),e<=Fintype.card V->q8 G b->(∀ w,d+b<=G.degree w)->Fintype.card V<=D *d->Fintype.card V<=B *b->(k:O)*Fintype.card V +2*q* (Fintype.card V:O)^2+ 2*Fintype.card V < (G.edgeFinset.card:O)->∀ u v,u≠v->∃ p:G.Walk u v,p.IsPath/\2*k < p.length:=by
 obtain ⟨e,g⟩ :=sh D B (3*D+1) x s q j i;refine ⟨e,?_⟩
 intro V _ _ G _ b d k y F t C r H u v l;obtain ⟨R,z,h⟩ :=g G b d y F t C r;have hmul:=mul_le_mul_of_nonneg_right z (Nat.cast_nonneg (FC V):(0:O)<=FC V)
 have m:((k:O)+R.card+2)*Fintype.card V < (G.edgeFinset.card:O) :=by
  nlinarith
 have n:(k+R.card+2)*Fintype.card V < G.edgeFinset.card:=by exact_mod_cast m
 exact vA G (3*D) k R h n u v l
lemma xl {V:Type*} [Fintype V] {G:SG V} (n:qh G)(d:¬ G.Colorable 2) (S:Set V)(y:2<=S.ncard) (colour:(G.induce S).Coloring Bool) (k:ℕ)(z:1<=k) (g:∀ u v:S,u≠v->∃ p:(G.induce S).Walk u v,p.IsPath/\2*k < p.length):∃ (w:V)(c:G.Walk w w),c.IsCycle/\Odd c.length/\2*k < c.length:=by
 classical
 obtain ⟨u,v,j,q,t,e,m⟩:=vu n d S y colour;obtain ⟨p,x,i⟩ :=g u v (fun h=>j (CA Subtype.val h))
 obtain ⟨c,s,r,l⟩ :=xC S colour p x (by omega) q t m e
 exact ⟨u.val,c,s,r,i.trans_le l⟩
lemma ux (D B:ℕ)(F:0 < D) (z:0 < B) (q:O)(t:0 < q) (s:q<=1):∃ g:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (S:FS V)(b d k:ℕ),qh G->¬ G.Colorable 2->2<=S.card->g<=Fintype.card (S:Set V)->q8 (G.induce (S:Set V)) b->(∀ w:(S:Set V),d+b<=(G.induce (S:Set V)).degree w)->Fintype.card (S:Set V)<=D*d->Fintype.card (S:Set V)<=B*b->1<=k->(G.induce (S:Set V)).Colorable 2->(∀ (w:V)(c:G.Walk w w),c.IsCycle->Odd c.length->c.length<=2*k)->((G.induce (S:Set V)).edgeFinset.card:O)<=(k:O)*Fintype.card (S:Set V)+2*q* (Fintype.card (S:Set V): O)^2+ 2*Fintype.card (S:Set V) :=by
 obtain ⟨g,j⟩ :=w1 D B F z q t s;refine ⟨g,?_⟩
 intro V _ _ G _ S b d k C x I H K y J L N l M;by_contra he;have e:=lt_of_not_ge he;have i:=j (G.induce (S:Set V)) b d k H K y J L e;obtain ⟨colour⟩ :=l;let v:(G.induce (S:Set V)).Coloring Bool:= SimpleGraph.recolorOfEquiv _ finTwoEquiv colour;have h:2<=(S:Set V).ncard:=by simpa only [Set.ncard_coe_finset] using I
 obtain ⟨w,c,n,r,m⟩ :=xl C x (S:Set V) h v k N i;exact (Nat.not_le_of_gt m) (M w c n r)
noncomputable def bB {V:Type*} [DecidableEq V] (G:SG V)(S:FS V) (T:FS ↥((S:Set V)ᶜ)):(G.induce (S:Set V)ᶜ).induce (T:Set ↥((S:Set V)ᶜ))ᶜ ≃g G.induce (↑(S ∪ T.map (Function.Embedding.subtype (fun v=>v∈(S:Set V)ᶜ)):FS V):Set V)ᶜ:=by
 let U:=(S:Set V)ᶜ;let F :=S ∪ T.map (Function.Embedding.subtype (fun v=>v∈U))
 let f: ↥((T:Set U)ᶜ)->↥((F:Set V)ᶜ) :=fun x=>⟨x.val.val,by
  intro q;rcases mem_union.mp q with l | e
  · exact x.val.property l
  · obtain ⟨y,m,k⟩ :=mem_map.mp e;have n:y=x.val:=Subtype.ext k;exact x.property (n ▸ m)⟩
 have i:Function.Injective f :=by
  intro x y h;apply Subtype.ext;apply Subtype.ext;change (f x).val= (f y).val;exact CA Subtype.val h
 have d:Function.Surjective f :=by
  intro y;have j:y.val ∉ S:=fun h=>y.property (mem_union_left _ h)
  let x:U:= ⟨y.val,j⟩
  have e:x ∉ T:=by
   intro h;exact y.property (mem_union_right S (mem_map.mpr ⟨x,h,rfl⟩))
  exact ⟨⟨x,e⟩,rfl⟩
 exact { toEquiv:=Equiv.ofBijective f ⟨i,d⟩,map_rel_iff':=Iff.rfl}
lemma q8.e6 {V:Type*} {G:SG V} {b s:ℕ} (d:q8 G (b+s)) (S:FS V)(i:S.card<=s):q8 (G.induce (S:Set V)ᶜ) b :=by
 classical
 intro T g;let F :=S ∪ T.map (Function.Embedding.subtype (fun v=>v∈(S:Set V)ᶜ))
 have e:F.card<=b+s:=by
  have h :=card_union_le S (T.map (Function.Embedding.subtype (fun v=>v∈(S:Set V)ᶜ)))
  rw [card_map] at h;dsimp [F];omega
 exact (bB G S T).preconnected_iff.mpr (d F e)
noncomputable def cZ {V W:Type*} [DecidableEq V] [DecidableEq W] {G:SG V} {H:SG W} (e:G ≃g H) (S:FS V):G.induce (S:Set V)ᶜ ≃g H.induce (S.map e.toEquiv.toEmbedding:Set W)ᶜ where
 toEquiv:=
  { toFun:=fun x=>⟨e x.val,by
     intro i
     obtain ⟨y,h,d⟩ :=mem_map.mp i
     exact x.property (e.injective d ▸ h)⟩
    invFun:=fun y=>⟨e.symm y.val,by
     intro h
     exact y.property (mem_map.mpr ⟨e.symm y.val,h,e.apply_symm_apply y.val⟩)⟩
    left_inv:=fun x=>Subtype.ext (e.symm_apply_apply x.val)
    right_inv:=fun y=>Subtype.ext (e.apply_symm_apply y.val)}
 map_rel_iff':=by intro x y;exact e.map_adj_iff
lemma q8.iso {V W:Type*} {G:SG V} {H:SG W} {b:ℕ} (d:q8 G b)(e:G ≃g H):q8 H b:=by
 classical
 intro S i;have h :=d (S.map e.symm.toEquiv.toEmbedding) (by simpa only [card_map] using i)
 exact (cZ e.symm S).preconnected_iff.mpr h
def x8 {V:Type*} (G:SG V)(S T:Set V) (h:S=T):G.induce S ≃g G.induce T :=by subst T;exact SimpleGraph.Iso.refl
def xX {V:Type*} [DecidableEq V] (S:FS V)(T:FS S):FS V:=Tᶜ.map (Function.Embedding.subtype (fun v=>v∈S))
lemma ak {V:Type*} [DecidableEq V] (S:FS V)(T:FS S):(xX S T).card=S.card-T.card:=by simp only [xX,card_map,card_compl,Fintype.card_coe]
noncomputable def tk {V:Type*} [DecidableEq V] (G:SG V)(S:FS V) (T:FS S):(G.induce (S:Set V)).induce (T:Set S)ᶜ ≃g G.induce (xX S T:Set V):=(x8 (G.induce (S:Set V)) (T:Set S)ᶜ (↑(Tᶜ:FS S):Set S) (coe_compl T).symm).trans (sy G S Tᶜ)
lemma wW (D B:ℕ)(hD:0 < D) (hB:0 < B) (q:O)(F:0 < q) (z:q<=1):∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (S:FS V)(b d k:ℕ),qh G->¬ G.Colorable 2->N₀+ (b+3*D+3)+2<=S.card->q8 (G.induce (S:Set V)) (2* (b+3*D+3))->(∀ w:S,d+2* (b+3*D+3)<=(G.induce (S:Set V)).degree w)->S.card<=D*d->S.card<=B*b->1<=k->(∀ (w:V)(c:G.Walk w w),c.IsCycle->Odd c.length->c.length<=2*k)->((G.induce (S:Set V)).edgeFinset.card:O)<=(k:O)*S.card+2*q* (S.card:O)^2+ (b+3*D+5:ℕ)*(S.card:O) :=by
 obtain ⟨I,x⟩ :=ua D B hB q F z;obtain ⟨M,s⟩ :=ux D B hD hB q F z;refine ⟨max I M,?_⟩
 intro V _ _ G _ S b d k hG h2 hN hc hg hd hb hk ho
 classical
 let J :=G.induce (S:Set V);let t :=b+3*D+3
 have i:Fintype.card (S:Set V)=S.card:=by
  calc
   Fintype.card (S:Set V)=(S:Set V).ncard:=Nat.card_eq_fintype_card.symm
   _=S.card:=Set.ncard_coe_finset S
 have h3 (w:(S:Set V)) (c:J.Walk w w) (Q:c.IsCycle) (R:Odd c.length):c.length<=2*k:=by
  let f:J ↪g G :=SimpleGraph.Embedding.induce (S:Set V);have h :=ho (f w) (c.map f.toHom) (Q.map f.injective) (by simpa only [Walk.length_map] using R)
  simpa only [Walk.length_map] using h
 by_cases m:qT J t
 · have Z (w:(S:Set V)):d+ (b+3*D+3)<=J.degree w :=by
    have h :=hg w;change d +2* (b+3*D+3)<=J.degree w at h;omega
   have l:=x J b d k (by rw [i];omega) (hc.mono (by omega)) m Z (by simpa only [i] using hd) (by simpa only [i] using hb) hk h3
   rw [i] at l;have n:(0:O)<=(b+3*D+5:ℕ)*(S.card:O) :=by positivity
   exact l.trans (le_add_of_nonneg_right n)
 · obtain ⟨T,P,C⟩ :∃ T:FS (S:Set V),T.card<=t/\(J.induce (T:Set (S:Set V))ᶜ).Colorable 2 :=by
    simpa only [qT,not_forall,not_not,exists_prop] using m
   let K :=xX S T;let H :=J.induce (T:Set (S:Set V))ᶜ;let e:H ≃g G.induce (K:Set V) :=tk G S T;have hK:K.card=S.card-T.card:=ak S T;have L:K.card<=S.card:=by omega
   have j:Fintype.card (K:Set V)=K.card:=by
    calc
     Fintype.card (K:Set V)=(K:Set V).ncard:=Nat.card_eq_fintype_card.symm
     _=K.card:=Set.ncard_coe_finset K
   have Y:q8 H b:= (hc.mono (show b +t<=2* (b+3*D+3) by dsimp [t];omega)).e6 T P
   have h0 (w: ↥((T:Set (S:Set V))ᶜ)):d+b<=H.degree w :=by
    have h :=qW J T w;have N:=hg w.val;change d +2* (b+3*D+3)<=J.degree w.val at N;change J.degree w.val<=H.degree w +T.card at h;dsimp [t] at P;omega
   have W (v:(K:Set V)):d+b<=(G.induce (K:Set V)).degree v :=by
    calc
     d+b<=H.degree (e.symm v) :=h0 _
     _= (G.induce (K:Set V)).degree v :=by rw [<- e.degree_eq,e.apply_symm_apply]
   have y:(G.induce (K:Set V)).Colorable 2 :=C.of_hom e.symm.toHom;have l:=s G K b d k hG h2 (by dsimp [t] at P;omega) (by rw [j];dsimp [t] at P;omega) (Y.iso e) W (by rw [j];omega) (by rw [j];omega) hk y ho
   rw [j] at l;have h4:(K.card:O)<=S.card:=by exact_mod_cast L
   have h1:(k:O)*K.card+2*q* (K.card:O)^2+2*K.card<=(k:O)*S.card+2*q* (S.card:O)^2+2*S.card:=by
    gcongr
   have r:=rc J T;change J.edgeFinset.card<=H.edgeFinset.card+T.card*Fintype.card (S:Set V) at r;rw [e.card_edgeFinset_eq,i] at r;have U:(J.edgeFinset.card:O)<=((G.induce (K:Set V)).edgeFinset.card:O)+(T.card:O)*S.card:=by exact_mod_cast r
   have X:(T.card:O)<=(b+3*D+3:ℕ) :=by exact_mod_cast P
   have hmul:=mul_le_mul_of_nonneg_right X (Nat.cast_nonneg S.card:(0:O)<=S.card);push_cast at hmul ⊢;nlinarith
lemma uV (D B:ℕ)(hD:0 < D) (Y:0 < B) (q:O)(Q:0 < q) (N:q<=1):∃ e:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (b d k:ℕ)(r η :O),qh G->¬ G.Colorable 2->1<=k->0<=r->0<=η->((2* (b+3*D+3):ℕ): O)<=r->((2* (b+3*D+3):ℕ): O)*Fintype.card V<=2*η* (r- (2* (b+3*D+3):ℕ))^2->((d+2* (b+3*D+3):ℕ): O)<=r->Fintype.card V<=D *d->Fintype.card V<=B *b->((e+ (b+3*D+3)+2:ℕ): O)<=r->(k:O)+2*q*Fintype.card V+(b+3*D+5:ℕ)<=r->(∀ (w:V)(c:G.Walk w w),c.IsCycle->Odd c.length->c.length<=2*k)->∀ A:FS V,((G.induce (A:Set V)).edgeFinset.card:O)<=r*A.card+η* (A.card:O)^2:=by
 obtain ⟨e,C⟩ :=wW D B hD Y q Q N;refine ⟨e,?_⟩
 intro V _ _ G _ b d k r η hG X hk Z H ht j F t x M l ho A;by_contra hA;obtain ⟨S,hS,J,y,hc⟩ :=sR G (2* (b+3*D+3)) r η Z H ht j A (lt_of_not_ge hA)
 have s:Fintype.card (S:Set V)=S.card:=by
  calc
   Fintype.card (S:Set V)=(S:Set V).ncard:=Nat.card_eq_fintype_card.symm
   _=S.card:=Set.ncard_coe_finset S
 have i:S.card<=Fintype.card V :=card_le_univ S;obtain ⟨v,U⟩ :=hS;have T:=y ⟨v,U⟩;have n:= (G.induce (S:Set V)).degree_lt_card_verts ⟨v,U⟩;rw [s] at n;have I:((G.induce (S:Set V)).degree ⟨v,U⟩ : O) < S.card:=by exact_mod_cast n
 have m:e+ (b+3*D+3)+2<=S.card:=by
  have h:((e+ (b+3*D+3)+2:ℕ): O)<=S.card:=by linarith
  exact_mod_cast h
 have g (w:S):d+2* (b+3*D+3)<=(G.induce (S:Set V)).degree w :=by
  have h :=F.trans (y w).le;exact_mod_cast h
 have L:=C G S b d k hG X m hc g (i.trans t) (i.trans x) hk ho;have z:(S.card:O)<=Fintype.card V :=by exact_mod_cast i
 have W:=mul_le_mul_of_nonneg_right z (Nat.cast_nonneg S.card:(0:O)<=S.card);have R:=mul_le_mul_of_nonneg_left W (by positivity:(0:O)<=2*q)
 have P:=mul_le_mul_of_nonneg_right l (Nat.cast_nonneg S.card:(0:O)<=S.card);have K:=mul_nonneg H (sq_nonneg (S.card:O));nlinarith
private lemma zJ (ε B t N x:O)(e:0<=ε) (m:0<=t) (k:0<=N) (h:4096<=ε*B) (d:B*t<=2*N) (n:N<=32*x):2*t*N<=ε*x^2:=by
 have j:=mul_le_mul_of_nonneg_right h (by positivity:0<=2*t*N)
 have l:=mul_le_mul_of_nonneg_right d (by positivity:0<=2*ε*N)
 have g:N^2<=(32*x)^2:=by gcongr
 have i:=mul_le_mul_of_nonneg_left g e;nlinarith
private lemma tG (N B:ℕ)(d:0 < B) (h:B<=N):N<=2*B* (N/B) :=by have g:1<=N/B:=Nat.div_pos h d;have hmod:=Nat.mod_lt N d;have e:=Nat.mod_add_div N B;have hmul:=Nat.mul_le_mul_left B g;nlinarith
lemma ay (ε:O)(q:0 < ε) (B e N k:ℕ)(L:128<=B) (m:4096<=ε*B) (X:195*B<=N) (s:64* (e+2)<=N) (W:N<=16*k):∃ b d:ℕ,N<=64*d/\N<=(2*B)*b/\((2* (b+195):ℕ): O)<=(k:O) + ε*N/2/\((2* (b+195):ℕ): O)*N<=ε* ((k:O) + ε*N/2- (2* (b+195):ℕ))^2/\((d+2* (b+195):ℕ): O)<=(k:O) + ε*N/2/\((e+ (b+195)+2:ℕ): O)<=(k:O) + ε*N/2/\(k:O) + ε/8*N+ (b+197:ℕ)<=(k:O) + ε*N/2:=by
 let b :=N/B;let d :=N/32;let t :=b+195;let r:O:= (k:O) + ε*N/2;have w:0 < B:=by omega
 have y:B<=N:=by nlinarith
 have C:N<=(2*B)*b:=tG N B w y;have H:N<=64*d:=by dsimp [d];omega
 have T:b*B<=N:=Nat.div_mul_le_self _ _;have D:B*t<=2*N:=by dsimp [t];nlinarith
 have n:(B:O)*t<=2*N:=by exact_mod_cast D
 have v:(128:O)<=B:=by exact_mod_cast L
 have J:(64:O)*t<=N:=by
  have h :=mul_le_mul_of_nonneg_right v (Nat.cast_nonneg t:(0:O)<=t);nlinarith
 have U:(32:O)*d<=N:=by
  have h:d*32<=N:=Nat.div_mul_le_self _ _;exact_mod_cast (by nlinarith:32*d<=N)
 have M:(N:O)<=16*k:=by exact_mod_cast W
 have Q:(k:O)<=r:=by dsimp [r];exact le_add_of_nonneg_right (by positivity)
 have g:(d:O)+2*t<=r:=by nlinarith
 have I:(2:O)*t<=r:=by have:= (Nat.cast_nonneg d:(0:O)<=d);linarith
 have R:(N:O)<=32* (r-2*t) :=by nlinarith
 have i:=zJ ε B t N (r-2*t) q.le (Nat.cast_nonneg _) (Nat.cast_nonneg _) m n R;have z:(64:O)*((e:O)+2)<=N:=by exact_mod_cast s
 have l:(e:O)+t+2<=r:=by nlinarith
 have x:(B:O)<=N:=by exact_mod_cast y
 have K:(4096:O)<=ε*N:= m.trans (mul_le_mul_of_nonneg_left x q.le)
 have P:(8:O)*t<=ε*N:=by
  have Y:=mul_le_mul_of_nonneg_right (show (16:O)<=ε*B by linarith) (Nat.cast_nonneg t:(0:O)<=t)
  have Z:=mul_le_mul_of_nonneg_left n q.le;nlinarith
 have j:(k:O) + ε/8*N+ ((t:O)+2)<=r:=by
  dsimp [r];nlinarith
 refine ⟨b,d,H,C,?_,?_,?_,?_,?_⟩
 · simpa only [Nat.cast_mul,Nat.cast_ofNat,r,t] using I
 · simpa only [Nat.cast_mul,Nat.cast_ofNat,r,t] using i
 · simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,r,t] using g
 · simpa only [Nat.cast_add,Nat.cast_ofNat,r,t] using l
 · have F:b+197=t+2:=by dsimp [t]
   simpa only [F,Nat.cast_add,Nat.cast_ofNat,r] using j
lemma v2 (ε:O)(F:0 < ε) (R:ε<=1):∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (k:ℕ),N₀<=Fintype.card V->Fintype.card V<=16*k->qh G->¬ G.Colorable 2->(∀ (w:V)(c:G.Walk w w),c.IsCycle->Odd c.length->c.length<=2*k)->∀ A:FS V,((G.induce (A:Set V)).edgeFinset.card:O)<=((k:O) + ε*Fintype.card V)*A.card:=by
 obtain ⟨B,Y⟩ :=exists_nat_gt ((4096:O) / ε+128);have J:(0:O)<=4096/ε:=by positivity
 have n:(128:O)<=B:=by linarith
 have z:128<=B:=by exact_mod_cast n
 have I:(4096:O)<=ε*B:=by
  have h:(4096:O) / ε < B:=by linarith
  have h':= (div_lt_iff₀ F).mp h;nlinarith
 have C:0 < 2*B:=by omega
 have s:0 < ε/16:=by positivity
 have H:ε/16<=1:=by linarith
 obtain ⟨j,x⟩ :=uV 64 (2*B) (by decide) C (ε/16) s H
 refine ⟨max (195*B) (64* (j+2)),?_⟩
 intro V _ _ G _ k Z W T Q U;let N :=Fintype.card V;have g:195*B<=N:=by dsimp [N];omega
 have e:64* (j+2)<=N:=by dsimp [N];omega
 have t:1<=k:=by dsimp [N] at g;nlinarith
 obtain ⟨b,d,P,K,X,l,i,q,m⟩:=ay ε F B j N k z I g e W;have r:2* (ε/2)=ε:=by ring
 have D:2* (ε/16)=ε/8:=by ring
 have v:=x G b d k ((k:O) + ε*N/2) (ε/2) T Q t (by positivity) (by positivity) (by simpa [Nat.add_assoc] using X) (by simpa [Nat.add_assoc,r] using l) (by simpa [Nat.add_assoc] using i) P K (by simpa [Nat.add_assoc] using q) (by simpa [Nat.add_assoc,D] using m) U
 intro A;have hA:=v A;have y:(A.card:O)<=N:=by exact_mod_cast card_le_univ A
 have L:=mul_le_mul_of_nonneg_right y (Nat.cast_nonneg A.card:(0:O)<=A.card);have M:=mul_le_mul_of_nonneg_left L (by positivity:(0:O)<=ε/2)
 change ((G.induce (A:Set V)).edgeFinset.card:O)<=((k:O) + ε*N)*A.card;nlinarith
lemma xz (ε:O)(h:0 < ε):∃ d:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (k:ℕ),d<=Fintype.card V->Fintype.card V<=16*k->qh G->¬ G.Colorable 2->(∀ (w:V)(c:G.Walk w w),c.IsCycle->Odd c.length->c.length<=2*k)->∀ A:FS V,((G.induce (A:Set V)).edgeFinset.card:O)<=((k:O) + ε*Fintype.card V)*A.card:=by
 have g:0 < min ε 1:=lt_min h (by norm_num)
 obtain ⟨d,e⟩ :=v2 (min ε 1) g (min_le_right _ _);refine ⟨d,?_⟩
 intro V _ _ G _ k n m j i l A;apply (e G k n m j i l A).trans;gcongr;exact min_le_left ε 1
def rp {V:Type*} (G:SG V) (P:FS (FS V)):SG V where
 Adj u v:=G.Adj u v/\∃ A ∈ P,u∈A/\v∈A
 symm:= ⟨by
  rintro u v ⟨d,A,g,i,e⟩;exact ⟨d.symm,A,g,e,i⟩⟩
 loopless:= ⟨by intro u h;exact h.1.ne rfl⟩
lemma ah {V:Type*} (G:SG V)(P:FS (FS V)):rp G P<=G:=fun _ _ h=>h.1
lemma xE {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (P:FS (FS V)) [DecidableRel (rp G P).Adj] (t:(P:Set (FS V)).Pairwise Disjoint):(rp G P).edgeFinset.card= ∑ A ∈ P,(G.induce (A:Set V)).edgeFinset.card:=by
 classical
 let E (A:FS V) :=G.edgeFinset.filter (fun e=>e.toFinset⊆A)
 have d:(rp G P).edgeFinset=P.biUnion E :=by
  ext e;rcases e with ⟨⟨u,v⟩⟩;change s(u,v)∈(rp G P).edgeFinset↔s(u,v)∈P.biUnion E;rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet];change (G.Adj u v/\∃ A ∈ P,u∈A/\v∈A)↔s(u,v)∈P.biUnion E;simp only [mem_edgeFinset,mem_edgeSet,mem_biUnion,E,mem_filter,Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff];constructor
  · rintro ⟨g,A,j,n,i⟩;exact ⟨A,j,g,n,i⟩
  · rintro ⟨A,j,g,n,i⟩;exact ⟨g,A,j,n,i⟩
 have h:(P:Set (FS V)).Pairwise fun A B=> Disjoint (E A) (E B) :=by
  intro A j B q k;rw [Finset.disjoint_left]
  intro e m l;have w:= (mem_filter.mp m).2;have r:= (mem_filter.mp l).2;obtain ⟨v,i⟩ :=nonempty_iff_ne_empty.mpr (Sym2.toFinset_ne_empty e);exact Finset.disjoint_left.mp (t j q k) (w i) (r i)
 rw [d,card_biUnion h];apply sum_congr rfl
 intro A _;exact G.card_filter_edgeFinset_toFinset_subset A
lemma a1 {V:Type*} (G:SG V)(P:FS (FS V)) (n:ℕ) [NeZero n] (r:(P:Set (FS V)).Pairwise Disjoint) (d:∀ A ∈ P,(G.induce (A:Set V)).Colorable n):(rp G P).Colorable n :=by
 classical
 let C (A:P):(G.induce (A.val:Set V)).Coloring (Fin n):=Classical.choice (d A.val A.property);let Q (v:V):Prop:= ∃ A:P,v∈A.val;let f (v:V):Fin n :=if h:Q v then C (Classical.choose h) ⟨v,Classical.choose_spec h⟩ else 0
 have m (A:P) (v:V) (g:v∈A.val):f v =C A ⟨v,g⟩ :=by
  have e:Q v:= ⟨A,g⟩;dsimp [f];rw [dif_pos e]
  have l:Classical.choose e=A:=by
   apply Subtype.ext;by_contra i;exact Finset.disjoint_left.mp (r (Classical.choose e).property A.property i) (Classical.choose_spec e) g
  subst l;rfl
 refine ⟨{ toFun:=f,map_rel':= ?_}⟩
 intro u v j;obtain ⟨q,A,k,s,g⟩ :=j;rw [m ⟨A,k⟩ u s,m ⟨A,k⟩ v g];exact (C ⟨A,k⟩).valid q
def qp {V:Type*} [DecidableEq V] (G:SG V)(r:ℕ) (P:FS (FS V)):Prop:= (P:Set (FS V)).Pairwise Disjoint/\∀ A ∈ P,r < A.card/\qh (G.induce (A:Set V))
lemma qp.nonempty {V:Type*} [DecidableEq V] {G:SG V} {r:ℕ} {P:FS (FS V)} (e:qp G r P) {A:FS V} (d:A∈P):A.Nonempty:= card_pos.mp ((Nat.zero_le r).trans_lt (e.2 A d).1)
def s4 {V:Type*} [DecidableEq V] (S:FS V)(P:FS (FS S)):FS (FS V):=P.map (mapEmbedding (Function.Embedding.subtype (fun v=>v∈S))).toEmbedding
lemma vH {V:Type*} [DecidableEq V] (S:FS V)(P:FS (FS S)) (A:FS V):A∈s4 S P↔∃ T ∈ P,T.map (Function.Embedding.subtype (fun v=>v∈S))=A:=by exact mem_map
lemma rP {V:Type*} [DecidableEq V] {S:FS V} {P:FS (FS S)} {A:FS V} (g:A∈s4 S P):A⊆S:=by
 obtain ⟨T,_,rfl⟩:=(vH S P A).mp g
 intro x e;obtain ⟨y,_,d⟩ :=mem_map.mp e;exact d ▸ y.property
lemma qp.lift {V:Type*} [DecidableEq V] {G:SG V} {r:ℕ} {S:FS V} {P:FS (FS S)} (g:qp (G.induce (S:Set V)) r P):qp G r (s4 S P) :=by
 constructor
 · intro A i B j e;obtain ⟨T,d,rfl⟩:=(vH S P A).mp i;obtain ⟨U,k,rfl⟩:=(vH S P B).mp j;apply (disjoint_map _).mpr;exact g.1 d k (fun h=>e (CA (map _) h))
 · intro A i
   obtain ⟨T,d,rfl⟩:=(vH S P A).mp i;refine ⟨by simpa only [card_map] using (g.2 T d).1,?_⟩
   exact (g.2 T d).2.iso (sy G S T)
lemma vF {V:Type*} [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (S:FS V)(P:FS (FS S)):(∑ A ∈ s4 S P,(G.induce (A:Set V)).edgeFinset.card)=∑ T ∈ P,((G.induce (S:Set V)).induce (T:Set S)).edgeFinset.card:=by
 rw [s4,sum_map];apply sum_congr rfl
 intro T _;exact (sy G S T).card_edgeFinset_eq.symm
lemma ab {V:Type*} [DecidableEq V] {S T:FS V} (h:Disjoint S T)(P:FS (FS S)) (Q:FS (FS T)) (k:∀ A ∈ P,A.Nonempty):Disjoint (s4 S P) (s4 T Q) :=by
 rw [Finset.disjoint_left]
 intro A e g;have j:=rP e;have i:=rP g;obtain ⟨U,m,rfl⟩:=(vH S P A).mp e;obtain ⟨x,l⟩ :=k U m;have d:x.val∈U.map (Function.Embedding.subtype (fun v=>v∈S)):=mem_map.mpr ⟨x,l,rfl⟩
 exact D1 h (j d) (i d)
lemma qp.union {V:Type*} [DecidableEq V] {G:SG V} {r:ℕ} {P Q:FS (FS V)} (l:qp G r P)(m:qp G r Q) (d:∀ A ∈ P,∀ B ∈ Q,Disjoint A B):qp G r (P ∪ Q) :=by
 constructor
 · intro A k B n e
   rcases mem_union.mp k with j | h <;> rcases mem_union.mp n with g | i
   · exact l.1 j g e
   · exact d A j B i
   · exact (d B g A h).symm
   · exact m.1 h i e
 · intro A k;exact (mem_union.mp k).elim (l.2 A) (m.2 A)
lemma uU {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (S:FS V):G.edgeFinset.card<=(G.induce (S:Set V)ᶜ).edgeFinset.card+ ∑ v ∈ S,G.degree v :=by
 classical
 let A :=G.edgeFinset.filter (fun e=>e.toFinset⊆Sᶜ)
 let B :=S.biUnion (fun v=>G.incidenceFinset v)
 have d:G.edgeFinset⊆A ∪ B:=by
  intro e k;by_cases h:e.toFinset⊆Sᶜ
  · exact mem_union_left _ (mem_filter.mpr ⟨k,h⟩)
  · obtain ⟨x,j,l⟩ :=not_subset.mp h
    have g:x∈S:=by simpa only [mem_compl,not_not] using l
    apply mem_union_right;apply mem_biUnion.mpr;refine ⟨x,g,?_⟩;rw [G.incidenceFinset_eq_filter];exact mem_filter.mpr ⟨k,by simpa using j⟩
 have n:A.card= (G.induce (S:Set V)ᶜ).edgeFinset.card:=by
  have h :=CA card (G.map_edgeFinset_induce (s:= (S:Set V)ᶜ));simp only [card_map] at h
  have i:G.edgeFinset ∩ ((S:Set V)ᶜ).toFinset.sym2=A:=by
   simp [A,G.filter_edgeFinset_toFinset_subset]
  rw [i] at h;exact h.symm
 have m:B.card<=∑ v ∈ S,G.degree v :=by
  simpa only [G.card_incidenceFinset_eq_degree] using (card_biUnion_le:B.card<=∑ v ∈ S,(G.incidenceFinset v).card)
 exact (card_le_card d).trans ((card_union_le A B).trans (by omega))
lemma rU {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (S:FS V)(d:ℕ) (g:∀ v ∈ S,G.degree v<=d):G.edgeFinset.card<=(G.induce (S:Set V)ᶜ).edgeFinset.card+S.card*d:=by
 have e:(∑ v ∈ S,G.degree v)<=S.card*d:=by
  calc
   (∑ v ∈ S,G.degree v)<=∑ _v ∈ S,d:=sum_le_sum g
   _=S.card*d:=by simp
 exact (uU G S).trans (by omega)
lemma ze (r a b s N:ℕ)(h:r < a) (g:r < b) (i:s<=1) (k:a+b+s=N):(r+1)^2*a+a^2+ ((r+1)^2*b+b^2)+(r+1)*(s*N)<=(r+1)^2*N+N^2:=by
 have d:r+1<=a:=h;have e:r+1<=b:=g;have j:=Nat.mul_le_mul_right b d;have l:=Nat.mul_le_mul_right a e
 interval_cases s <;> nlinarith
lemma uw {V:Type*} [Fintype V] [DecidableEq V] (G:SG V)(g:3<=Fintype.card V) (t:¬ qh G):∃ A B S:FS V,A.Nonempty/\B.Nonempty/\Disjoint A B/\Disjoint A S/\Disjoint B S/\A ∪ B ∪ S=univ/\S.card<=1/\∀ a ∈ A,∀ b ∈ B,¬ G.Adj a b:=by
 classical
 have n:∃ S:FS V,S.card<=1/\¬ (G.induce (S:Set V)ᶜ).Preconnected:=by
  by_cases r:G.Connected
  · have j:∃ v:V,¬ (G.induce ({v}ᶜ:Set V)).Connected:=by
     by_contra! h;exact t ⟨g,r,h⟩
    obtain ⟨v,j⟩ :=j
    refine ⟨{v},by simp,?_⟩
    rw [coe_singleton]
    intro m
    have x:0 < Fintype.card ({v}ᶜ:Set V) :=by
     rw [Fintype.card_compl_set,Set.card_singleton];omega
    let:Nonempty ({v}ᶜ:Set V) :=Fintype.card_pos_iff.mp x;exact j ⟨m⟩
  · refine ⟨∅,by simp,?_⟩
    rw [coe_empty,Set.compl_empty]
    intro m;let:Nonempty V :=Fintype.card_pos_iff.mp (by omega)
    exact r ⟨(G.induceUnivIso.preconnected_iff).mp m⟩
 obtain ⟨S,y,i⟩ :=n;obtain ⟨A,B,w,s,k,q,l,d,e⟩:=rk G S i;exact ⟨A,B,S,w,s,k,q,l,d,y,e⟩
lemma tp {V:Type*} [Fintype V] [DecidableEq V] (A B S:FS V)(g:Disjoint A B) (i:Disjoint A S)(e:Disjoint B S) (d:A ∪ B ∪ S=univ):A.card+B.card+S.card=Fintype.card V :=by have h :=CA card d;rwa [card_union_of_disjoint (disjoint_union_left.mpr ⟨i,e⟩),card_union_of_disjoint g,card_univ] at h
end E5
end _m
section d2
namespace E5
open SimpleGraph Finset
private lemma yu (r N e:ℕ)(d:N<=r) (j:2*e<=N*N):(r+1)*e<=(r+1)^2*N+N^2:=by
 have i:=Nat.mul_le_mul_right N d;have g:e<=(r+1)*N:=by nlinarith
 have h:=Nat.mul_le_mul_left (r+1) g;nlinarith
private lemma tZ (r a b N e f s:ℕ)(i:a+b=N) (d:e<=f+a* (r+1)) (g:(r+1)*f<=(r+1)*s+ (r+1)^2*b+b^2):(r+1)*e<=(r+1)*s+ (r+1)^2*N+N^2:=by have h :=Nat.mul_le_mul_left (r+1) d;nlinarith
universe u
private lemma xP (N:ℕ):∀ (V:Type u) [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj],Fintype.card V =N->∀ r:ℕ,2<=r->∃ P:FS (FS V),qp G r P/\(r+1)*G.edgeFinset.card<=(r+1)*(∑ A ∈ P,(G.induce (A:Set V)).edgeFinset.card)+(r+1)^2*Fintype.card V+(Fintype.card V)^2:=by
 induction N using Nat.strong_induction_on with
 | h N ih=>
  intro V _ _ G _ h3 r W
  classical
  by_cases k:Fintype.card V<=r
  · refine ⟨∅,⟨by simp,by simp⟩,?_⟩
    simp only [sum_empty,mul_zero,zero_add];apply yu r (Fintype.card V) G.edgeFinset.card k
    calc
     2*G.edgeFinset.card= ∑ v,G.degree v :=G.sum_degrees_eq_twice_card_edges.symm
     _<=∑ _v:V,Fintype.card V :=sum_le_sum fun v _=> (G.degree_lt_card_verts v).le
     _=Fintype.card V *Fintype.card V :=by simp
  by_cases w:qh G
  · let e:G.induce (↑(univ:FS V):Set V) ≃g G:=(x8 G _ _ Finset.coe_univ).trans G.induceUnivIso
    have hc:qh (G.induce (↑(univ:FS V):Set V)):=w.iso e.symm
    have L:(G.induce (↑(univ:FS V):Set V)).edgeFinset.card=G.edgeFinset.card:=by
     exact e.card_edgeFinset_eq
    refine ⟨{univ},⟨by simp,?_⟩,?_⟩
    · intro A z;have h9:A=univ:=mem_singleton.mp z;subst A;exact ⟨by simpa only [card_univ] using Nat.lt_of_not_ge k,hc⟩
    · simp only [sum_singleton,L];omega
  have d:∀ A:FS V,A.Nonempty->A.card < Fintype.card V->(∀ v ∈ A,G.degree v<=r +1)->∃ P:FS (FS V),qp G r P/\(r+1)*G.edgeFinset.card<=(r+1)*(∑ A ∈ P,(G.induce (A:Set V)).edgeFinset.card)+(r+1)^2*Fintype.card V+(Fintype.card V)^2:=by
   intro A z h7 H;let T :=Aᶜ;have t:Fintype.card (T:Set V)=T.card:=Fintype.card_coe T
   have m:A.card+T.card=Fintype.card V :=by
    dsimp [T];rw [card_compl];exact Nat.add_sub_of_le (card_le_univ A)
   have C:Fintype.card (T:Set V) < N:=by
    have h8:=card_pos.mpr z;omega
   obtain ⟨P,M,q⟩ :=ih (Fintype.card (T:Set V)) C (T:Set V) (G.induce (T:Set V)) rfl r W;refine ⟨s4 T P,M.lift,?_⟩;rw [vF];rw [t] at q;have L:=rU G A (r+1) H
   have h5:G.edgeFinset.card<=(G.induce (T:Set V)).edgeFinset.card+ A.card* (r+1) :=by
    have h4:= (x8 G (A:Set V)ᶜ (T:Set V) (Finset.coe_compl A).symm).card_edgeFinset_eq;rw [h4] at L;exact L
   exact tZ r A.card T.card (Fintype.card V) _ _ _ m h5 q
  obtain ⟨A,B,S,z,hB,y,h0,Z,i,hS,j⟩:=uw G (by omega) w
  have m:=tp A B S y h0 Z i;have U:=card_pos.mpr z;have h6:=card_pos.mpr hB;by_cases D:A.card<=r
  · apply d A z (by omega)
    intro v hv;have hd:=qR G A B S i j v hv;omega
  by_cases I:B.card<=r
  · apply d B hB (by omega)
    intro v hv;have n:B ∪ A ∪ S=univ:=by rw [union_comm B A];exact i
    have l:∀ b ∈ B,∀ a ∈ A,¬ G.Adj b a:= fun b hb a ha F=> j a ha b hb F.symm
    have hd:=qR G B A S n l v hv;omega
  have h1:Fintype.card (A:Set V)=A.card:=Fintype.card_coe A;have R:Fintype.card (B:Set V)=B.card:=Fintype.card_coe B;obtain ⟨P,M,q⟩ :=ih (Fintype.card (A:Set V)) (by omega) (A:Set V) (G.induce (A:Set V)) rfl r W
  obtain ⟨Q,hQ,J⟩ :=ih (Fintype.card (B:Set V)) (by omega) (B:Set V) (G.induce (B:Set V)) rfl r W
  have h2:Disjoint (s4 A P) (s4 B Q):=ab y P Q (fun _ h=> M.nonempty h)
  refine ⟨s4 A P ∪ s4 B Q,M.lift.union hQ.lift ?_,?_⟩
  · intro X hX Y hY;exact y.mono (rP hX) (rP hY)
  · rw [sum_union h2,vF,vF]
    rw [h1] at q;rw [R] at J;have x:=vp G A B S i j;have s:=Nat.mul_le_mul_left (r+1) x;have K:=ze r A.card B.card S.card (Fintype.card V) (by omega) (by omega) hS m
    nlinarith only [q,J,s,K]
lemma zY {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (r:ℕ)(d:2<=r):∃ P:FS (FS V),qp G r P/\(r+1)*G.edgeFinset.card<=(r+1)*(∑ A ∈ P,(G.induce (A:Set V)).edgeFinset.card)+(r+1)^2*Fintype.card V+(Fintype.card V)^2:= xP (FC V) V G rfl r d
end E5
end d2
section _m
namespace E5
open SimpleGraph Finset
open scoped SimpleGraph Classical
private lemma yH (r N e s:ℕ)(ε:O) (h:0 < ε) (m:2<=ε* (r+1)) (k:2* (r+1)<=ε*N) (j:(r+1)*e<=(r+1)*s+ (r+1)^2*N+N^2):(e:O)<=s+ε* (N:O)^2:=by
 have g:((r:O)+1)*e<=((r:O)+1)*s+ ((r:O)+1)^2*N+ (N:O)^2:=by exact_mod_cast j
 have i:=mul_le_mul_of_nonneg_right k (by positivity:(0:O)<=((r:O)+1)*N)
 have l:=mul_le_mul_of_nonneg_right m (by positivity:(0:O)<=(N:O)^2)
 have d:((r:O)+1)*e<=((r:O)+1)*(s+ε* (N:O)^2) :=by
  nlinarith only [g,i,l]
 exact (mul_le_mul_iff_right₀ (by positivity:(0:O) < (r:O)+1)).mp d
lemma wF (ε:O)(g:0 < ε) (R:ℕ):∃ d:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj],d<=Fintype.card V->∃ P:FS (FS V),qp G R P/\(G.edgeFinset.card:O)<=(∑ A ∈ P,((G.induce (A:Set V)).edgeFinset.card:O)) + ε* (Fintype.card V:O)^2:=by
 obtain ⟨r,x⟩ :=exists_nat_gt ((R:O)+2+2/ε);have hdiv:(0:O)<=2/ε:=by positivity
 have q:R<=r:=by exact_mod_cast (show (R:O)<=r by linarith)
 have n:2<=r:=by exact_mod_cast (show (2:O)<=r by linarith)
 have k:(2:O)<=ε* (r+1) :=by
  have t:2/ε < (r:O)+1:=by linarith [Nat.cast_nonneg R (α:=O)]
  have v:= (div_lt_iff₀ g).mp t;nlinarith
 obtain ⟨d,i⟩ :=exists_nat_gt (2* ((r:O)+1) / ε);refine ⟨d,?_⟩
 intro V _ _ G _ w;obtain ⟨P,l,m⟩ :=zY G r n;have e:(d:O)<=FC V :=by exact_mod_cast w
 have j:2* ((r:O)+1)<=ε*Fintype.card V :=by
  have t:= (div_lt_iff₀ g).mp (i.trans_le e);nlinarith
 refine ⟨P,⟨l.1,fun A s=> ⟨q.trans_lt (l.2 A s).1,(l.2 A s).2⟩⟩,?_⟩
 have h :=yH r (FC V) G.edgeFinset.card (∑ A ∈ P,(G.induce (A:Set V)).edgeFinset.card) ε g k j m;simpa only [Nat.cast_sum] using h
lemma zo {V:Type*} (G:SG V) [DecidableRel G.Adj] (A:FS V)(d:O) (h:∀ T:FS A,(((G.induce (A:Set V)).induce (T:Set A)).edgeFinset.card:O)<=d*T.card):∀ S:FS V,S⊆A->((G.induce (S:Set V)).edgeFinset.card:O)<=d*S.card:=by
 classical
 intro S m;let T:FS A :=S.subtype (fun v=>v∈A)
 have i:T.map (Function.Embedding.subtype (fun v=>v∈A))=S:= subtype_map_of_mem (fun v l=> m l)
 have j:T.card=S.card:=by
  have n:=CA card i;simpa only [card_map] using n
 let e:(G.induce (A:Set V)).induce (T:Set A) ≃g G.induce (S:Set V) :=
  (sy G A T).trans (x8 G _ _ (CA (fun U:FS V=>(U:Set V)) i))
 have k:=h T;rw [e.card_edgeFinset_eq,j] at k;exact k
lemma xs {V:Type*} [Finite V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (P:FS (FS V)) [DecidableRel (rp G P).Adj] (S:FS V):((rp G P).induce (S:Set V)).edgeFinset.card<=∑ A ∈ P,(G.induce (↑(A ∩ S):Set V)).edgeFinset.card:=by
 classical
 let:=Fintype.ofFinite V;let E (A:FS V) :=G.edgeFinset.filter (fun e=>e.toFinset⊆A ∩ S)
 let F:=(rp G P).edgeFinset.filter (fun e=>e.toFinset⊆S)
 have d:F⊆P.biUnion E :=by
  intro e g;obtain ⟨g,k⟩ :=mem_filter.mp g;rcases e with ⟨⟨u,v⟩⟩;rw [mem_edgeFinset,mem_edgeSet] at g;obtain ⟨h,A,m,n,l⟩ :=g;apply mem_biUnion.mpr;refine ⟨A,m,mem_filter.mpr ⟨?_,?_⟩⟩
  · simpa using h
  · have i:u∈S:=k (by simp)
    have j:v∈S:=k (by simp)
    simpa only [Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff,mem_inter] using And.intro (And.intro n i) (And.intro l j)
 calc
  ((rp G P).induce (S:Set V)).edgeFinset.card=F.card:= ((rp G P).card_filter_edgeFinset_toFinset_subset S).symm
  _<=(P.biUnion E).card:=card_le_card d
  _<=∑ A ∈ P,(E A).card:=card_biUnion_le
  _= ∑ A ∈ P,(G.induce (↑(A ∩ S):Set V)).edgeFinset.card:=by
   apply sum_congr rfl
   intro A _;exact G.card_filter_edgeFinset_toFinset_subset (A ∩ S)
lemma z0 {V:Type*} [DecidableEq V] (P:FS (FS V)) (j:(P:Set (FS V)).Pairwise Disjoint) (S:FS V):(∑ A ∈ P,(A ∩ S).card)<=S.card:=by
 have d:(P:Set (FS V)).Pairwise fun A B=> Disjoint (A ∩ S) (B ∩ S) :=by
  intro A k B i e;exact (j k i e).mono (inter_subset_left) (inter_subset_left)
 rw [<- card_biUnion d];apply card_le_card
 intro v h;obtain ⟨A,_,g⟩ :=mem_biUnion.mp h;exact (mem_inter.mp g).2
lemma z5 {V:Type*} [Finite V] (G:SG V) [DecidableRel G.Adj] (P:FS (FS V)) [DecidableRel (rp G P).Adj] (j:(P:Set (FS V)).Pairwise Disjoint) (d:O)(i:0<=d) (h:∀ A ∈ P,∀ S:FS V,S⊆A->((G.induce (S:Set V)).edgeFinset.card:O)<=d*S.card):∀ S:FS V,(((rp G P).induce (S:Set V)).edgeFinset.card:O)<=d*S.card:=by
 classical
 let:=Fintype.ofFinite V
 intro S
 have e:(∑ A ∈ P,((A ∩ S).card:O))<=S.card:=by
  exact_mod_cast z0 P j S
 calc
  (((rp G P).induce (S:Set V)).edgeFinset.card:O)<=∑ A ∈ P,((G.induce (↑(A ∩ S):Set V)).edgeFinset.card:O) :=by
   exact_mod_cast xs G P S
  _<=∑ A ∈ P,d* (A ∩ S).card:=by
   apply sum_le_sum
   intro A g;exact h A g (A ∩ S) inter_subset_left
  _=d* ∑ A ∈ P,((A ∩ S).card:O):=(mul_sum _ _ _).symm
  _<=d*S.card:=mul_le_mul_of_nonneg_left e i
open scoped Classical in
lemma xK (ε:O)(t:0 < ε):∃ i:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (k:ℕ),i<=Fintype.card V->Fintype.card V<=16*k->(∀ (w:V)(c:G.Walk w w),c.IsCycle->Odd c.length->c.length<=2*k)->∃ (B F:SG V)(S:FS V),B<=G/\F<=G/\B.Colorable 2/\(∀ u v,B.Adj u v->u ∉ S/\v ∉ S)/\(∀ u v,F.Adj u v->u∈S/\v∈S)/\(G.edgeFinset.card:O)<=B.edgeFinset.card+F.edgeFinset.card+ ε* (Fintype.card V:O)^2/\(∀ A:FS V,((F.induce (A:Set V)).edgeFinset.card:O)<=((k:O) + ε*Fintype.card V)*A.card) :=by
 obtain ⟨R,hR⟩ :=xz ε t;obtain ⟨i,q⟩ :=wF ε t R;refine ⟨i,?_⟩
 intro V _ _ G _ k hN hk ho
 classical
 obtain ⟨P,z,Y⟩ :=q G hN;let Q:FS (FS V) :=P.filter (fun A=>(G.induce (A:Set V)).Colorable 2)
 let T:FS (FS V) :=P.filter (fun A=>¬ (G.induce (A:Set V)).Colorable 2)
 let S:FS V :=T.biUnion id;let B :=rp G Q;let F :=rp G T;have j:Q⊆P:=filter_subset _ _;have d:T⊆P:=filter_subset _ _;have hQ:(Q:Set (FS V)).Pairwise Disjoint:=z.1.mono j;have hT:(T:Set (FS V)).Pairwise Disjoint:=z.1.mono d;have hB:B.Colorable 2 :=a1 G Q 2 hQ (fun A l=> (mem_filter.mp l).2)
 have D:Disjoint Q T:=by
  rw [Finset.disjoint_left]
  intro A L J;exact (mem_filter.mp J).2 (mem_filter.mp L).2
 have e:Q ∪ T=P:=filter_union_filter_not_eq _ _
 have X:B.edgeFinset.card+F.edgeFinset.card= ∑ A ∈ P,(G.induce (A:Set V)).edgeFinset.card:=by
  rw [xE G Q hQ,xE G T hT,<-sum_union D,e]
 refine ⟨B,F,S,ah G Q,ah G T,hB,?_,?_,?_,?_⟩
 · intro u v r
   obtain ⟨_,A,l,M,W⟩ :=r
   have m (x:V) (hx:x∈A):x ∉ S:=by
    intro H;obtain ⟨C,hC,K⟩ :=mem_biUnion.mp H
    have Z:A≠C:=by
     intro he;subst C;exact D1 D l hC
    exact Finset.disjoint_left.mp (z.1 (j l) (d hC) Z) hx K
   exact ⟨m u M,m v W⟩
 · intro u v r;obtain ⟨_,A,l,M,W⟩ :=r;exact ⟨mem_biUnion.mpr ⟨A,l,M⟩,mem_biUnion.mpr ⟨A,l,W⟩⟩
 · have s:(B.edgeFinset.card:O)+F.edgeFinset.card= ∑ A ∈ P,((G.induce (A:Set V)).edgeFinset.card:O) :=by exact_mod_cast X
   rw [s];exact Y
 · apply z5 G T hT ((k:O) + ε*Fintype.card V) (by positivity)
   intro A l;have h0:R < A.card:= (z.2 A (d l)).1;have y:Fintype.card (A:Set V)=A.card:=Fintype.card_coe A
   have N:Fintype.card (A:Set V)<=16*k:=by
    rw [y];exact (card_le_univ A).trans hk
   have I (w:(A:Set V)) (c:(G.induce (A:Set V)).Walk w w) (hc:c.IsCycle) (n:Odd c.length):c.length<=2*k:=by
    let f:G.induce (A:Set V) ↪g G :=SimpleGraph.Embedding.induce (A:Set V);have h :=ho (f w) (c.map f.toHom) (hc.map f.injective) (by simpa only [Walk.length_map] using n)
    simpa only [Walk.length_map] using h
   have hd:=hR (G.induce (A:Set V)) k (by omega) N (z.2 A (d l)).2 (mem_filter.mp l).2 I
   apply zo G A
   intro U;apply (hd U).trans;gcongr;rw [y];exact_mod_cast card_le_univ A
open scoped Classical in
lemma vd (ε:O)(C:0 < ε):∃ n₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (n:ℕ),n₀<=n->Odd n->n<=Fintype.card V->Fintype.card V<=4 *n->(¬ CG n ⊑ G)->∃ (B F:SG V)(T:FS V),B<=G/\F<=G/\B.Colorable 2/\(∀ u v,B.Adj u v->u ∉ T/\v ∉ T)/\(∀ u v,F.Adj u v->u∈T/\v∈T)/\(G.edgeFinset.card:O)<=B.edgeFinset.card+F.edgeFinset.card+ ε* (Fintype.card V:O)^2/\(∀ A:FS V,((F.induce (A:Set V)).edgeFinset.card:O)<=((n:O)/2+ε*Fintype.card V)*A.card) :=by
 obtain ⟨D,r⟩ :=exists_nat_gt (2/ε)
 have hD:0 < D:=by
  have hp:0 < 2/ε:=by positivity
  have c0:0 < (D:O) :=hp.trans r;exact_mod_cast c0
 have a2:2<=ε* (D:O) :=by
  have h:=(div_lt_iff₀ C).mp r;nlinarith
 obtain ⟨h8,K,h2⟩ :=uR D hD;obtain ⟨b0,J⟩ :=xK (ε/2) (by positivity)
 obtain ⟨M,hM⟩ :=exists_nat_ge ((K:O) / ε)
 have c5:(K:O)<=ε*M:=by
  have h:=(div_le_iff₀ C).mp hM;nlinarith
 let R :=max h8 b0;refine ⟨max (D* (R+1)) (max K (max M 3)),?_⟩
 intro V _ _ G _ n hn b2 c9 b8 c3
 classical
 let N :=Fintype.card V;let q :=N/D;have d1:3<=n:=by omega
 have c1:K<=n:=by omega
 have c2:(K:O)<=ε*N:=by
  have b6:M<=N:=by omega
  exact c5.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast b6) C.le)
 have c4:(D:O)*q<=N:=by exact_mod_cast (Nat.mul_div_le N D)
 have I:2* (q:O)<=ε*N:=by
  have Y:=mul_le_mul_of_nonneg_right a2 (show 0<=(q:O) by positivity)
  have Z:=mul_le_mul_of_nonneg_left c4 C.le;nlinarith only [Y,Z]
 have X:(q:O)*N<=ε/2* (N:O)^2:=by
  have h :=mul_le_mul_of_nonneg_right I (show 0<=(N:O) by positivity)
  nlinarith only [h]
 obtain ⟨S,Q,z⟩ :=a4 G (q:O)
 have d:Fintype.card (S:Set V)=S.card:=by
  calc
   Fintype.card (S:Set V)=(S:Set V).ncard:=Nat.card_eq_fintype_card.symm
   _=S.card:=Set.ncard_coe_finset S
 have W:S.card<=N:=card_le_univ S
 have e:(G.edgeFinset.card:O)<=(G.induce (S:Set V)).edgeFinset.card+ ε/2* (N:O)^2:=by
  have H:0<=(q:O)*S.card:=by positivity
  change (G.edgeFinset.card:O)-(q:O)*N<=((G.induce (S:Set V)).edgeFinset.card:O)-(q:O)*S.card at Q;linarith
 by_cases g:S= ∅
 · have L:(G.induce (S:Set V)).edgeFinset.card=0:=by
    have h:=(G.induce (S:Set V)).card_edgeFinset_le_card_choose_two;have b9:S.card=0:=by rw [g,card_empty]
    rw [d,b9] at h;exact Nat.eq_zero_of_le_zero (by simpa only [Nat.choose_zero_succ] using h)
   rw [L,Nat.cast_zero,zero_add] at e;refine ⟨⊥,⊥,∅,bot_le,bot_le,?_,?_,?_,?_,?_⟩
   · exact ⟨{ toFun:=fun _=>(0:Fin 2),map_rel':=fun h=>h.elim}⟩
   · intro u v h;exact h.elim
   · intro u v h;exact h.elim
   · have h7:Nat.card (⊥ :SG V).edgeSet=0:=by
      rw [edgeSet_bot];simp
     have H:0<=ε* (N:O)^2:=by positivity
     have y:(G.edgeFinset.card:O)<=ε* (N:O)^2:=by linarith
     simpa only [q7,h7,Nat.cast_zero,zero_add] using y
   · intro A
     have he:Nat.card (((⊥ :SG V).induce (A:Set V)).edgeSet)=0:=by
      change Nat.card (⊥ :SG (A:Set V)).edgeSet=0;rw [edgeSet_bot];simp
     simpa only [q7,he,Nat.cast_zero] using (show (0:O)<=((n:O)/2+ε*Fintype.card V)*A.card by positivity)
 · have d2:R+1<=q:=by
    apply (Nat.le_div_iff_mul_le hD).mpr;have b4:D* (R+1)<=n:=by omega
    exact (by simpa only [Nat.mul_comm] using b4.trans c9)
   obtain ⟨s,hs⟩ :=nonempty_iff_ne_empty.mpr g
   have j (v:(S:Set V)):q+1<=(G.induce (S:Set V)).degree v :=by
    have h:q < (G.induce (S:Set V)).degree v :=by exact_mod_cast z v
    omega
   have i:R<=Fintype.card (S:Set V) :=by
    have Y:=j ⟨s,hs⟩;have Z:= (G.induce (S:Set V)).degree_lt_card_verts ⟨s,hs⟩;omega
   have P:Fintype.card (S:Set V)<=D* (q+1) :=by
    rw [d];exact W.trans (Nat.lt_mul_div_succ N hD).le
   have b1:¬ CG n ⊑ G.induce (S:Set V) :=fun h=>c3 (h.trans (Embedding.induce (S:Set V)).isContained)
   have a6:=h2 (G.induce (S:Set V)) (q+1) n (by dsimp only [R] at i;omega) P j d1 b2 c1 b1
   let k:=(n+K)/2
   have c7:Fintype.card (S:Set V)<=16*k:=by
    rw [d];have h:4*n<=16*k:=by dsimp only [k];omega
    exact W.trans (b8.trans h)
   have m (v:(S:Set V)) (w:(G.induce (S:Set V)).Walk v v) (hw:w.IsCycle) (ho:Odd w.length):w.length<=2*k:=by
    have h :=a6 v w hw ho;dsimp only [k];omega
   obtain ⟨B,F,T,d0,b7,h5,h1,h9,hE,h4⟩:=J (G.induce (S:Set V)) k (by dsimp only [R] at i;omega) c7 m
   let f:(S:Set V) ↪ V:=Function.Embedding.subtype _;have h3:B.map f<=G:=(map_le_iff_le_comap f B G).mpr d0;have h0:F.map f<=G:=(map_le_iff_le_comap f F G).mpr b7;refine ⟨B.map f,F.map f,T.map f,h3,h0,h5.map f,tW B f T h1,ac F f T h9,?_,?_⟩
   · have x:=card_edgeFinset_map f B
     have t:=card_edgeFinset_map f F;simp only [q7] at x t ⊢;rw [x,t];have l:(S.card:O)<=N:=by exact_mod_cast W
     have c6:(S.card:O)^2<=(N:O)^2:=by nlinarith
     have b3:=mul_le_mul_of_nonneg_left c6 (show 0<=ε /2 by positivity)
     rw [d] at hE;simp only [q7] at hE e;change (Nat.card G.edgeSet:O)<=(Nat.card B.edgeSet:O)+Nat.card F.edgeSet+ε* (N: O)^2;linarith
   · have U:2* (k:O)<=(n:O)+K:=by
      exact_mod_cast (show 2 *k<=n+K from Nat.mul_div_le (n+K) 2)
     have l:(Fintype.card (S:Set V): O)<=N:=by rw [d];exact_mod_cast W
     have hmul:=mul_le_mul_of_nonneg_left l C.le
     have h6:(k:O) + ε/2*Fintype.card (S:Set V)<=(n:O)/2+ε*N:=by
      nlinarith only [U,c2,hmul]
     have v4:=x2 F f ((k:O) + ε/2*Fintype.card (S:Set V)) (by positivity) h4
     intro A;have y:= (v4 A).trans (mul_le_mul_of_nonneg_right h6 (by positivity))
     simpa only [q7] using y
instance q4.graphDecidableAdj {V:Type*} [DecidableEq V] (c:q4 V)(i:Fin 3):DecidableRel (c.graph i).Adj:= fun u v=> inferInstanceAs (Decidable (u≠v/\c.colour u v=i))
lemma sN (i:Fin 3):i=0\/i=1\/i=2:=by omega
lemma q4.r7 {V:Type*} (c:q4 V)(S:FS V) (i j k:Fin 3)(e:∀ a:Fin 3,a=i\/a=j\/a=k) (m:∀ u ∈ S,∀ v ∈ S,¬ (c.graph i).Adj u v) (n:∀ u ∈ S,∀ v ∈ S,¬ (c.graph j).Adj u v):(c.graph k).IsClique (S:Set V) :=by
 intro u l v g d;rcases e (c.colour u v) with h | h | h
 · exact (m u l v g ⟨d,h⟩).elim
 · exact (n u l v g ⟨d,h⟩).elim
 · exact ⟨d,h⟩
def qc (i:Fin 4):wz:= ![![false,false,false],![false,true,true],![true,false,true],![true,true,false]] i
def qu (i:Fin 4)(a:Fin 3):q1:= fun j=>if j =a then none else some (qc i j)
def vI (i:Fin 4)(a:Fin 3):wz:= fun j=>if j =a then !(qc i j) else qc i j
lemma yh:∀ (i:Fin 4)(a:Fin 3),q3 (qu i a)=1:=by decide
lemma r5:∀ (i:Fin 4)(a:Fin 3),qc i∈q0 (qu i a) :=by decide
lemma un:∀ (i:Fin 4)(a:Fin 3),vI i a∈q0 (qu i a) :=by decide
lemma tq:∀ p:q1,q3 p =1->∃ (i:Fin 4)(a:Fin 3),p=qu i a:=by decide
def qV (p q:q1)(i:Fin 3):Prop:= (p i =some false/\q i =some true)\/(p i =some true/\q i =some false)
instance (p q:q1)(i:Fin 3):Decidable (qV p q i):=inferInstanceAs (Decidable ((p i =some false/\q i =some true)\/(p i =some true/\q i =some false)))
def q5 (p q:q1)(i:Fin 3):Prop:= qV p q i/\∀ j,j≠i->¬ qV p q j
instance (p q:q1)(i:Fin 3):Decidable (q5 p q i):=inferInstanceAs (Decidable (qV p q i/\∀ j,j≠i->¬ qV p q j))
def uf (p:Fin 4->q1) (k:Fin 3->Fin 3):Prop:= q5 (p 0) (p 2) (k 0)/\q5 (p 1) (p 3) (k 0)/\q5 (p 0) (p 1) (k 1)/\q5 (p 2) (p 3) (k 1)
def uq (p:Fin 4->q1) (k:Fin 3->Fin 3):Prop:= q5 (p 0) (p 2) (k 0)/\q5 (p 0) (p 3) (k 0)/\q5 (p 1) (p 2) (k 0)/\q5 (p 1) (p 3) (k 0)/\q5 (p 0) (p 1) (k 1)/\q5 (p 2) (p 3) (k 2)
instance (p:Fin 4->q1) (k:Fin 3->Fin 3):Decidable (uf p k):=inferInstanceAs (Decidable (q5 (p 0) (p 2) (k 0)/\q5 (p 1) (p 3) (k 0)/\q5 (p 0) (p 1) (k 1)/\q5 (p 2) (p 3) (k 1)))
instance (p:Fin 4->q1) (k:Fin 3->Fin 3):Decidable (uq p k):=inferInstanceAs (Decidable (q5 (p 0) (p 2) (k 0)/\q5 (p 0) (p 3) (k 0)/\q5 (p 1) (p 2) (k 0)/\q5 (p 1) (p 3) (k 0)/\q5 (p 0) (p 1) (k 1)/\q5 (p 2) (p 3) (k 2)))
structure q2 {V:Type*} (c:q4 V) (E D:O) where
 bipartite:Fin 3->SG V
 sparse:Fin 3->SG V
 stars:Fin 3->FS V
 bicolouring:∀ i,(bipartite i).Coloring Bool
 bipartite_le:∀ i,bipartite i<=c.graph i
 sparse_le:∀ i,sparse i<=c.graph i
 bipartite_off:∀ i u v,(bipartite i).Adj u v->u ∉ stars i/\v ∉ stars i
 sparse_on:∀ i u v,(sparse i).Adj u v->u∈stars i/\v∈stars i
 edge_loss:∀ i,(Nat.card (c.graph i).edgeSet:O)<=Nat.card (bipartite i).edgeSet+Nat.card (sparse i).edgeSet+E
 hereditary_density:∀ i (A:FS V),(Nat.card ((sparse i).induce (A:Set V)).edgeSet:O)<=D*A.card
lemma wZ (ε:O)(h:0 < ε):∃ d:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (c:q4 V)(n:ℕ),d<=n->Odd n->n<=Fintype.card V->Fintype.card V<=4 *n->(∀ i,¬ CG n ⊑ c.graph i)->Nonempty (q2 c (ε* (Fintype.card V:O)^2) ((n:O)/2+ε*Fintype.card V)) :=by
 obtain ⟨d,e⟩ :=vd ε h;refine ⟨d,?_⟩
 intro V _ _ c n m g k j l
 classical
 choose B F T hBG hFG hcol hBoff hFon he hden using fun i=>e (c.graph i) n m g k j (l i)
 refine ⟨{
  bipartite:=B
  sparse:=F
  stars:=T
  bicolouring:=fun i=>(B i).recolorOfEquiv finTwoEquiv (Classical.choice (hcol i))
  bipartite_le:=hBG
  sparse_le:=hFG
  bipartite_off:=hBoff
  sparse_on:=hFon
  edge_loss:= ?_
  hereditary_density:= ?_}⟩
 · intro i;simpa only [q7] using he i
 · intro i A;simpa only [q7] using hden i A
def q2.profile {V:Type*} [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D)(v:V):q1:= fun i=>if v∈h.stars i then none else some (h.bicolouring i v)
def q2.qa {V:Type*} [Fintype V] [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D)(p:q1):FS V:=univ.filter (fun v=>h.profile v =p)
def q2.retained {V:Type*} {c:q4 V} {E D:O} (h:q2 c E D):SG V:=⨆ i,h.bipartite i ⊔ h.sparse i
def q2.missing {V:Type*} {c:q4 V} {E D:O} (h:q2 c E D):SG V:=h.retainedᶜ
lemma q2.ry {V:Type*} [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D)(i:Fin 3) (u v:V)(d:(h.bipartite i).Adj u v):qV (h.profile u) (h.profile v) i :=by have g:= (h.bipartite_off i u v d).1;have j:= (h.bipartite_off i u v d).2;have e:= (h.bicolouring i).valid d;simp only [qV,profile,if_neg g,if_neg j,Option.some.injEq];cases huval:h.bicolouring i u <;> cases hvval:h.bicolouring i v <;> simp_all
lemma q2.z1 {V:Type*} [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D)(i:Fin 3) (u v:V)(d:(h.sparse i).Adj u v):h.profile u i=none/\h.profile v i=none:=by have e:= (h.sparse_on i u v d).1;have g:= (h.sparse_on i u v d).2;simp only [profile,if_pos e,if_pos g,and_self]
lemma q2.r3 {V:Type*} [Fintype V] [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D)(p:q1) (v:V):v∈h.qa p↔h.profile v =p:=by simp only [qa,mem_filter,mem_univ,true_and]
lemma q2.tK {V:Type*} [Fintype V] [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D)(p q:q1) (g:p≠q):Disjoint (h.qa p) (h.qa q) :=by
 apply D2
 intro v e d;exact g ((h.r3 p v).mp e |>.symm.trans ((h.r3 q v).mp d))
lemma q2.xF {V:Type*} [Fintype V] [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D):(∑ p,(h.qa p).card)=Fintype.card V :=aE h.profile
lemma q2.aK {V:Type*} [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D)(v:V) (i:Fin 3):h.profile v i=none↔v∈h.stars i :=by by_cases d:v∈h.stars i <;> simp [profile,d]
lemma q2.tQ {V:Type*} [Fintype V] [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D):(∑ i,(h.stars i).card)=∑ p,q3 p*(h.qa p).card:=by
 classical
 have d (i:Fin 3):(h.stars i).card= ∑ v,if h.profile v i=none then 1 else 0 :=by
  rw [sum_boole];congr 1;ext v;simp only [mem_filter,mem_univ,true_and,h.aK]
 calc
  _= ∑ i,∑ v,if h.profile v i=none then 1 else 0 :=sum_congr rfl (fun i _=> d i)
  _= ∑ v,∑ i,if h.profile v i=none then 1 else 0 :=sum_comm
  _= ∑ v,q3 (h.profile v) :=by
   apply sum_congr rfl
   intro v _;rw [q3,sum_boole];simp only [Nat.cast_id]
  _= ∑ p,(h.qa p).card*q3 p :=vn h.profile q3
  _=_:=sum_congr rfl (fun _ _=> Nat.mul_comm _ _)
lemma vZ {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj]:G.edgeFinset.card+Gᶜ.edgeFinset.card= (Fintype.card V).choose 2 :=by
 classical
 have g:Disjoint G.edgeFinset Gᶜ.edgeFinset:=by
  rw [Finset.disjoint_left]
  intro e m i;rcases e with ⟨⟨u,v⟩⟩;have l:G.Adj u v:=by simpa using m
  have n:Gᶜ.Adj u v:=by simpa using i
  have k:u≠v/\¬ G.Adj u v:=by simpa only [compl_adj] using n
  exact k.2 l
 have d:G.edgeFinset ∪ Gᶜ.edgeFinset= (⊤ :SG V).edgeFinset:=by
  ext e;rcases e with ⟨⟨u,v⟩⟩;simp only [mem_union,mem_edgeFinset,mem_edgeSet,top_adj,compl_adj];constructor
  · rintro (h | h)
    · exact h.ne
    · exact h.1
  · intro j
    by_cases h:G.Adj u v
    · exact Or.inl h
    · exact Or.inr ⟨j,h⟩
 calc
  G.edgeFinset.card+Gᶜ.edgeFinset.card= (G.edgeFinset ∪ Gᶜ.edgeFinset).card:= (card_union_of_disjoint g).symm
  _= (Fintype.card V).choose 2 :=by rw [d,card_edgeFinset_top_eq_card_choose_two]
lemma rn {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj]:2* ((G.edgeFinset.card:O)+Gᶜ.edgeFinset.card)=(Fintype.card V:O)*((Fintype.card V:O)-1) :=by
 have h:(G.edgeFinset.card:O)+Gᶜ.edgeFinset.card= ((Fintype.card V).choose 2:O) :=by
  exact_mod_cast vZ G
 rw [h,Nat.cast_choose_two];ring
lemma uh {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj]:2* (G.edgeFinset.card:O)<=(Fintype.card V:O)*((Fintype.card V:O)-1) :=by
 classical
 have h:(G.edgeFinset.card:O)<=((Fintype.card V).choose 2:O) :=by
  exact_mod_cast G.card_edgeFinset_le_card_choose_two
 rw [Nat.cast_choose_two] at h;linarith
lemma z9 {V:Type*} (G:SG V)(S:Set V):(G.induce S)ᶜ=Gᶜ.induce S :=by ext x y;simp only [compl_adj,induce_adj,ne_eq,Subtype.coe_inj]
open scoped Classical in
lemma c8 {V I:Type*} [Fintype V] [DecidableEq V] [Fintype I] (G:I->SG V):(⨆ i,G i).edgeFinset=univ.biUnion (fun i=>(G i).edgeFinset) :=by ext e;simp only [mem_edgeFinset,edgeSet_iSup,Set.mem_iUnion,mem_biUnion,mem_univ,true_and]
lemma wD {V I:Type*} [Finite V] [Fintype I] (G:I->SG V) (d:∀ i j,i≠j->Disjoint (G i) (G j)):Nat.card (⨆ i,G i).edgeSet= ∑ i,Nat.card (G i).edgeSet:=by
 classical
 let:=Fintype.ofFinite V
 have g:((univ:FS I):Set I).Pairwise (fun i j=> Disjoint (G i).edgeFinset (G j).edgeFinset) :=by
  intro i _ j _ e;exact SimpleGraph.disjoint_edgeFinset.mpr (d i j e)
 have h:(⨆ i,G i).edgeFinset.card= ∑ i,(G i).edgeFinset.card:=by
  rw [c8,card_biUnion g]
 simpa only [q7] using h
lemma yD {V:Type*} [Finite V] (G H:SG V)(d:Disjoint G H):Nat.card (G ⊔ H).edgeSet=Nat.card G.edgeSet+Nat.card H.edgeSet:=by
 classical
 let:=Fintype.ofFinite V
 have h:(G ⊔ H).edgeFinset.card=G.edgeFinset.card+H.edgeFinset.card:=by
  rw [edgeFinset_sup,card_union_of_disjoint (SimpleGraph.disjoint_edgeFinset.mpr d)]
 simpa only [q7] using h
lemma v1 {V:Type*} [Finite V] (G:SG V):Nat.card G.edgeSet+Nat.card Gᶜ.edgeSet=Nat.card (⊤ :SG V).edgeSet:=by
 classical
 let:=Fintype.ofFinite V;have h :=vZ G;have d:=card_edgeFinset_top_eq_card_choose_two (V:=V);simp only [q7] at h d;exact h.trans d.symm
lemma q4.zs {V:Type*} (c:q4 V)(i j:Fin 3) (d:i≠j):Disjoint (c.graph i) (c.graph j) :=by
 apply SimpleGraph.disjoint_left.mpr
 intro u v g e;exact d (g.2.symm.trans e.2)
lemma q4.aF {V:Type*} (c:q4 V):(⨆ i,c.graph i)=⊤ :=by
 ext u v;rw [iSup_adj,top_adj];constructor
 · rintro ⟨i,e⟩;exact e.1
 · intro d;exact ⟨c.colour u v,d,rfl⟩
lemma q4.bz {V:Type*} [Finite V] (c:q4 V):(∑ i,Nat.card (c.graph i).edgeSet)=Nat.card (⊤ :SG V).edgeSet:=by
 classical
 let:=Fintype.ofFinite V;have h :=wD c.graph c.zs;rw [c.aF] at h;exact h.symm
lemma q2.co {V:Type*} {c:q4 V} {E D:O} (h:q2 c E D)(i:Fin 3):Disjoint (h.bipartite i) (h.sparse i) :=by
 apply SimpleGraph.disjoint_left.mpr
 intro u v d e;exact (h.bipartite_off i u v d).1 (h.sparse_on i u v e).1
lemma q2.zD {V:Type*} [Finite V] {c:q4 V} {E D:O} (h:q2 c E D):Nat.card h.retained.edgeSet= ∑ i,(Nat.card (h.bipartite i).edgeSet+Nat.card (h.sparse i).edgeSet) :=by
 classical
 let:=Fintype.ofFinite V
 have d (i j:Fin 3) (e:i≠j):Disjoint (h.bipartite i ⊔ h.sparse i) (h.bipartite j ⊔ h.sparse j) :=
  (c.zs i j e).mono (sup_le (h.bipartite_le i) (h.sparse_le i)) (sup_le (h.bipartite_le j) (h.sparse_le j))
 dsimp only [retained];rw [wD _ d];apply sum_congr rfl
 intro i _;exact yD _ _ (h.co i)
lemma q2.v9 {V:Type*} [Finite V] {c:q4 V} {E D:O} (h:q2 c E D):(Nat.card h.missing.edgeSet:O)<=3*E:=by
 classical
 let:=Fintype.ofFinite V
 have e:(∑ i,(Nat.card (c.graph i).edgeSet:O))=Nat.card (⊤ :SG V).edgeSet:=by
  exact_mod_cast c.bz
 have g:(Nat.card h.retained.edgeSet:O)=∑ i,((Nat.card (h.bipartite i).edgeSet:O)+Nat.card (h.sparse i).edgeSet) :=by
  exact_mod_cast h.zD
 have d:(Nat.card h.retained.edgeSet:O)+Nat.card h.missing.edgeSet= Nat.card (⊤ :SG V).edgeSet:=by
  exact_mod_cast v1 h.retained
 have j:(∑ i,(Nat.card (c.graph i).edgeSet:O))<=(∑ i,((Nat.card (h.bipartite i).edgeSet:O)+Nat.card (h.sparse i).edgeSet))+3*E:=by
  calc
   _<=∑ i,((Nat.card (h.bipartite i).edgeSet:O)+Nat.card (h.sparse i).edgeSet+E):=sum_le_sum (fun i _=> h.edge_loss i)
   _=_:=by rw [sum_add_distrib];simp
 linarith
lemma q2.tU {V:Type*} [Finite V] {c:q4 V} {E D:O} (h:q2 c E D)(i:Fin 3):(Nat.card (h.sparse i).edgeSet:O)<=D* (h.stars i).card:=by
 classical
 let:=Fintype.ofFinite V
 have e:(h.sparse i).support⊆(h.stars i:Set V) :=by
  intro u k;obtain ⟨v,g⟩ :=k;exact (h.sparse_on i u v g).1
 have d:= (h.sparse i).card_edgeFinset_induce_of_support_subset e;simp only [q7] at d;have j:=h.hereditary_density i (h.stars i);rw [d] at j;exact j
lemma re:∀ (p q:q1)(i:Fin 3),qV p q i->Disjoint (q0 p) (q0 q) :=by decide
lemma uc:∀ (p q:q1)(i:Fin 3),(q0 p ∩ q0 q).card=1->¬ (p i =none/\q i =none) :=by decide
lemma xm:∀ p:q1,q3 p =1->∃ i,p i=none/\∀ j,p j=none->j=i:=by decide
lemma xj {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (B:FS V)(u:V) (h:∀ v ∈ B,u≠v->G.Adj u v):B.card<=G.degree u +1:=by
 classical
 have hsub:B.erase u⊆G.neighborFinset u :=by
  intro v e;exact (G.mem_neighborFinset u v).mpr (h v (mem_of_mem_erase e) (mem_erase.mp e).1.symm)
 have d:=card_le_card hsub;rw [card_neighborFinset_eq_degree] at d;by_cases g:u∈B
 · rw [card_erase_of_mem g] at d;omega
 · rw [erase_eq_of_notMem g] at d;omega
lemma xb {V:Type*} [Fintype V] (G:SG V)(A B:FS V) (h:∀ u ∈ A,∀ v ∈ B,u≠v->G.Adj u v):A.card*B.card<=2*Nat.card G.edgeSet+Fintype.card V :=by
 classical
 calc
  A.card*B.card= ∑ _u ∈ A,B.card:=by simp
  _<=∑ u ∈ A,(G.degree u +1):=sum_le_sum (fun u d=> xj G B u (h u d))
  _= (∑ u ∈ A,G.degree u)+A.card:=by rw [sum_add_distrib];simp
  _<=(∑ u,G.degree u)+Fintype.card V:=Nat.add_le_add (sum_le_sum_of_subset (subset_univ _)) (card_le_univ A)
  _=_:=by rw [G.sum_degrees_eq_twice_card_edges,q7]
lemma zW {V:Type*} [Finite V] (G H:SG V)(h:G<=H):Nat.card G.edgeSet<=Nat.card H.edgeSet:=by
 classical
 let:=Fintype.ofFinite V;have d:=card_le_card (edgeFinset_mono h);simpa only [q7] using d
lemma t2 {V:Type*} [Finite V] (G:SG V)(S:FS V):Nat.card (G.induce (S:Set V)).edgeSet<=Nat.card G.edgeSet:=by
 classical
 let:=Fintype.ofFinite V;let f:=(Embedding.induce (G:=G) (S:Set V)).toCopy.mapEdgeSet;have h :=Fintype.card_le_of_injective f f.injective;simpa only [<- Nat.card_eq_fintype_card] using h
lemma yx {V:Type*} [Fintype V]:2* (Nat.card (⊤ :SG V).edgeSet:O)+Fintype.card V=(Fintype.card V:O)^2:=by
 classical
 rw [sb]
 have e:(∑ u:V,∑ v:V,if u =v then (1:O) else 0)=Fintype.card V :=by
  simp
 rw [<- e]
 calc
  _= ∑ u:V,∑ v:V,((if (⊤ :SG V).Adj u v then (1:O) else 0)+if u =v then 1 else 0) :=by simp only [sum_add_distrib]
  _= ∑ _u:V,∑ _v:V,(1:O) :=by
   apply sum_congr rfl
   intro u _;apply sum_congr rfl
   intro v _;by_cases d:u=v <;> simp [top_adj,d]
  _=_:=by simp [pow_two]
def q2.bipartiteUnion {V:Type*} {c:q4 V} {E D:O} (h:q2 c E D):SG V:=⨆ i,h.bipartite i
lemma q2.vm {V:Type*} [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D):h.bipartiteUnion<=qJ h.profile:=by intro u v d;obtain ⟨i,e⟩ :=iSup_adj.mp d;exact re _ _ _ (h.ry i u v e)
lemma q2.yj {V:Type*} [Finite V] {c:q4 V} {E D:O} (h:q2 c E D):Nat.card h.bipartiteUnion.edgeSet= ∑ i,Nat.card (h.bipartite i).edgeSet:=by
 classical
 let:=Fintype.ofFinite V;apply wD
 intro i j d;exact (c.zs i j d).mono (h.bipartite_le i) (h.bipartite_le j)
lemma q2.yE {V:Type*} [Fintype V] [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D):(Fintype.card V:O)^2<=Fintype.card V+2*Nat.card h.bipartiteUnion.edgeSet+ 2*D* (∑ p,(q3 p:O)*(h.qa p).card)+6*E:=by
 have g:(Nat.card h.retained.edgeSet:O)=(Nat.card h.bipartiteUnion.edgeSet:O) + ∑ i,(Nat.card (h.sparse i).edgeSet:O) :=by
  have e:=h.zD;rw [sum_add_distrib,<- h.yj] at e;exact_mod_cast e
 have l:(∑ i,(Nat.card (h.sparse i).edgeSet:O))<=D* (∑ p,(q3 p:O)*(h.qa p).card) :=by
  calc
   _<=∑ i,D* (h.stars i).card:=sum_le_sum (fun i _=> h.tU i)
   _=D* (∑ i,((h.stars i).card:O)):=(mul_sum _ _ _).symm
   _=_:=by
    congr 1;exact_mod_cast h.tQ
 have d:(Nat.card h.retained.edgeSet:O)+Nat.card h.missing.edgeSet= Nat.card (⊤ :SG V).edgeSet:=by
  exact_mod_cast v1 h.retained
 have j:=h.v9;have k:=yx (V:=V);linarith
lemma q2.yS {V:Type*} [Fintype V] [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D)(n:O):(Fintype.card V:O)^2- qO (fun p=>((h.qa p).card:O))-n* (∑ p,(q3 p:O)*(h.qa p).card)<=Fintype.card V+(2*D-n)*(∑ p,(q3 p:O)*(h.qa p).card)+6*E:=by
 have d:=sY h.profile
 have e:(Nat.card h.bipartiteUnion.edgeSet:O)<=Nat.card (qJ h.profile).edgeSet:=by
  exact_mod_cast zW _ _ h.vm
 have g:=h.yE;change 2*(Nat.card (qJ h.profile).edgeSet:O)=qO (fun p=>((h.qa p).card:O)) at d
 nlinarith
lemma q2.wR {V:Type*} [Fintype V] [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D):(∑ p,(q3 p:O)*(h.qa p).card)<=3*Fintype.card V :=by
 have d:(∑ i,(h.stars i).card)<=3*Fintype.card V :=by
  calc
   _<=∑ _i:Fin 3,Fintype.card V :=sum_le_sum (fun i _=> card_le_univ _)
   _=_:=by simp
 rw [h.tQ] at d;exact_mod_cast d
lemma q2.uZ {V:Type*} [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D)(u v:V) (j:u≠v)(d:(q0 (h.profile u) ∩ q0 (h.profile v)).card=1):h.missing.Adj u v:=by
 rw [missing,compl_adj];refine ⟨j,?_⟩
 intro e;obtain ⟨i,l⟩ :=iSup_adj.mp e;rcases l with k | n
 · have g:=re _ _ i (h.ry i u v k);have m:q0 (h.profile u) ∩ q0 (h.profile v)=∅:=disjoint_iff_inter_eq_empty.mp g;rw [m,card_empty] at d;omega
 · exact uc _ _ i d (h.z1 i u v n)
lemma q2.su {V:Type*} [Fintype V] [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D)(p q:q1) (g:(q0 p ∩ q0 q).card=1):((h.qa p).card:O)*(h.qa q).card<=6*E+Fintype.card V :=by
 classical
 have d:∀ u ∈ h.qa p,∀ v ∈ h.qa q,u≠v->h.missing.Adj u v:=by
  intro u k v i e;apply h.uZ u v e;rw [(h.r3 p u).mp k,(h.r3 q v).mp i];exact g
 have l:=xb h.missing (h.qa p) (h.qa q) d;have j:((h.qa p).card:O)*(h.qa q).card<=2* (Nat.card h.missing.edgeSet:O)+Fintype.card V :=by exact_mod_cast l
 have m:=h.v9;linarith
lemma q2.zQ {V:Type*} [Fintype V] [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D)(p:q1) (e:q3 p =0):((h.qa p).card:O)^2<=6*E+Fintype.card V :=by
 have d:(q0 p ∩ q0 p).card=1:=by
  rw [inter_self,qU,e];rfl
 simpa only [pow_two] using h.su p p d
lemma q2.w4 {V:Type*} [Fintype V] [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D)(p:q1) (i:Fin 3)(g:∀ j,p j=none->j=i) (u v:V)(C:u∈h.qa p) (t:v∈h.qa p)(d:(c.graph i)ᶜ.Adj u v):h.missing.Adj u v:=by
 rw [missing,compl_adj];refine ⟨d.1,?_⟩
 intro l;obtain ⟨j,z⟩ :=iSup_adj.mp l;have k:= (h.r3 p u).mp C;have n:= (h.r3 p v).mp t;rcases z with w | s
 · have e:=h.ry j u v w
   rw [k,n] at e
   rcases e with ⟨q,r⟩ | ⟨r,q⟩ <;>
    have y:(some false:Option Bool)=some true:=q.symm.trans r <;> cases y
 · have m:= (h.z1 j u v s).1;rw [k] at m;have x:=g j m;subst j;exact d.2 (h.sparse_le i s)
lemma wo {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (A:FS V)(v:V) (g:v∈A)(d:∀ u ∈ A,u≠v->G.Adj v u):A.card<=G.degree v +1:=by
 classical
 have hsub:A.erase v⊆G.neighborFinset v :=by
  intro u e;rw [mem_erase] at e;exact (G.mem_neighborFinset v u).mpr (d u e.2 e.1)
 have h :=card_le_card hsub;rw [card_erase_of_mem g,G.card_neighborFinset_eq_degree] at h;have i:=card_pos.mpr ⟨v,g⟩;omega
lemma zO {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (A:FS V)(d:ℕ) (D:3<=Fintype.card V) (z:Fintype.card V +2*d<=2*A.card) (l:∀ v ∈ A,A.card<=G.degree v +d) (r:∀ v ∉ A,Fintype.card V -A.card+1<=G.degree v):G.IsHamiltonian:=by
 classical
 let H :=G.qE;have q:G<=H:=G.rs;have C:A.card<=Fintype.card V :=card_le_univ A
 have j (u v:V) (i:u∈A) (k:v∈A) (m:u≠v):H.Adj u v:=by
  apply G.rK m;change Fintype.card V<=H.degree u +H.degree v;have w:= (l u i).trans (Nat.add_le_add_right (G.degree_le_of_le q) d);have t:= (l v k).trans (Nat.add_le_add_right (G.degree_le_of_le q) d);omega
 have n (u:V) (i:u∈A):A.card<=H.degree u +1:=by
  apply wo H A u i
  intro v k y;exact j u v i k y.symm
 have e (u v:V) (i:u∈A) (k:v ∉ A):H.Adj u v:=by
  have m:u≠v:=fun h=>k (h ▸ i)
  apply G.rK m;change Fintype.card V<=H.degree u +H.degree v;have w:=n u i;have t:= (r v k).trans (G.degree_le_of_le q);omega
 have g (u:V) (i:u ∉ A):A.card<=H.degree u :=by
  have hsub:A⊆H.neighborFinset u :=by
   intro v k;exact (H.mem_neighborFinset u v).mpr (e v u k i).symm
  exact card_le_card hsub
 have s:H= ⊤ :=by
  apply top_unique
  intro u v m;have x:u≠v:=by simpa only [top_adj] using m
  by_cases i:u∈A
  · by_cases k:v∈A
    · exact j u v i k x
    · exact e u v i k
  · by_cases k:v∈A
    · exact (e v u k i).symm
    · apply G.rK x;change Fintype.card V<=H.degree u +H.degree v;have w:=g u i;have t:=g v k;omega
 apply G.sI.mp;change H.IsHamiltonian;rw [s];apply SimpleGraph.x3 D
 intro v;rw [((⊤ :SG V).degree_eq_card_sub_one v).mpr (by simp [IsUniversal])]
 omega
lemma wS {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (S:FS V)(v:(S:Set V)):(G.induce (S:Set V)).degree v=(G.neighborFinset v.val ∩ S).card:=by
 classical
 have h :=CA card (G.map_neighborFinset_induce v);simpa only [card_map,card_neighborFinset_eq_degree,toFinset_coe,<-SimpleGraph.card_neighborSet_eq_degree,<- Nat.card_eq_fintype_card] using h
lemma wE {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (A W:FS V)(d:ℕ) (m:Disjoint A W)(s:3<=A.card+W.card) (r:W.card+2*d<=A.card) (k:∀ v ∈ A,A.card<=(G.neighborFinset v ∩ A).card+d) (n:∀ v ∈ W,W.card+1<=(G.neighborFinset v ∩ A).card):(G.induce ((A ∪ W:FS V):Set V)).IsHamiltonian:=by
 classical
 let S :=A ∪ W;let H :=G.induce (S:Set V);let A':FS (S:Set V) :=univ.filter (fun v=>v.val∈A)
 have g:Fintype.card (S:Set V)=A.card+W.card:=by
  calc
   Fintype.card (S:Set V)=(S:Set V).ncard:=Nat.card_eq_fintype_card.symm
   _=S.card:=Set.ncard_coe_finset S
   _=A.card+W.card:=card_union_of_disjoint m
 have h:A'.image Subtype.val=A:=by
  ext v;simp only [A',mem_image,mem_filter,mem_univ,true_and];constructor
  · rintro ⟨x,t,rfl⟩;exact t
  · intro l;exact ⟨⟨v,mem_union_left W l⟩,l,rfl⟩
 have e:A'.card=A.card:=by
  rw [<- h,card_image_of_injective _ Subtype.val_injective]
 have i (v:(S:Set V)):(G.neighborFinset v.val ∩ A).card<=H.degree v :=by
  rw [wS];apply card_le_card;exact inter_subset_inter_left (subset_union_left:A⊆S)
 apply zO H A' d
 · simpa only [g] using s
 · rw [g,e];omega
 · intro v l;have j:v.val∈A:= (mem_filter.mp l).2;rw [e];exact (k v.val j).trans (Nat.add_le_add_right (i v) d)
 · intro v l
   have j:v.val ∉ A:=by simpa only [A',mem_filter,mem_univ,true_and] using l
   have q:v.val∈W:= (mem_union.mp v.property).resolve_left j;rw [g,e,Nat.add_sub_cancel_left];exact (n v.val q).trans (i v)
lemma sr {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (A W:FS V)(d:ℕ) (e:Disjoint A W)(m:3<=A.card+W.card) (i:W.card+2*d<=A.card) (h:∀ v ∈ A,A.card<=(G.neighborFinset v ∩ A).card+d) (k:∀ v ∈ W,W.card+1<=(G.neighborFinset v ∩ A).card):∃ (v:V)(c:G.Walk v v),c.IsCycle/\c.length=A.card+W.card:=by
 classical
 let S :=A ∪ W
 have g:Fintype.card (S:Set V)=A.card+W.card:=by
  calc
   Fintype.card (S:Set V)=(S:Set V).ncard:=Nat.card_eq_fintype_card.symm
   _=S.card:=Set.ncard_coe_finset S
   _=A.card+W.card:=card_union_of_disjoint e
 have j:(G.induce (S:Set V)).IsHamiltonian:= wE G A W d e m i h k;let:Nontrivial (S:Set V) :=Fintype.one_lt_card_iff_nontrivial.mp (by omega)
 obtain ⟨v⟩:=(inferInstance:Nonempty (S:Set V));obtain ⟨c,l⟩ :=j.exists_isHamiltonianCycle v;refine ⟨(Embedding.induce (S:Set V)).toHom v,c.map (Embedding.induce (S:Set V)).toHom,l.isCycle.map Subtype.val_injective,?_⟩;rw [Walk.length_map,l.length_eq,g]
lemma a7 {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (S:FS V): ∑ v ∈ S,(G.neighborFinset v ∩ S).card= 2* (G.induce (S:Set V)).edgeFinset.card:=by
 classical
 rw [<- (G.induce (S:Set V)).sum_degrees_eq_twice_card_edges];simp_rw [wS];exact (sum_coe_sort S (fun v=>(G.neighborFinset v ∩ S).card)).symm
lemma vk {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (S:FS V)(r:ℕ):∃ A:FS V,A⊆S/\r* (S.card-A.card)<=2* (G.induce (S:Set V)).edgeFinset.card/\∀ v ∈ A,(G.neighborFinset v ∩ S).card<=r:=by
 classical
 let A :=S.filter (fun v=>(G.neighborFinset v ∩ S).card<=r)
 have e:A⊆S:=filter_subset _ _;refine ⟨A,e,?_,fun v g=> (mem_filter.mp g).2⟩
 have d (v:V) (g:v∈S \ A):r<=(G.neighborFinset v ∩ S).card:=by
  have j:= (mem_sdiff.mp g).1;have i:= (mem_sdiff.mp g).2
  have k:¬ (G.neighborFinset v ∩ S).card<=r:=by
   intro h;exact i (mem_filter.mpr ⟨j,h⟩)
  omega
 calc
  r* (S.card-A.card)=∑ _v ∈ S \ A,r:=by
   rw [sum_const,smul_eq_mul,card_sdiff,inter_eq_left.mpr e,Nat.mul_comm]
  _<=∑ v ∈ S \ A,(G.neighborFinset v ∩ S).card:=sum_le_sum d
  _<=∑ v ∈ S,(G.neighborFinset v ∩ S).card:= sum_le_sum_of_subset sdiff_subset
  _=2* (G.induce (S:Set V)).edgeFinset.card:=a7 G S
lemma r1 {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (S:FS V)(v:V) (k:v∈S):(G.neighborFinset v ∩ S).card+ (Gᶜ.neighborFinset v ∩ S).card+1=S.card:=by
 classical
 have g:Disjoint (G.neighborFinset v ∩ S) (Gᶜ.neighborFinset v ∩ S) :=by
  apply D2
  intro u e j;have h:=(G.mem_neighborFinset v u).mp (mem_inter.mp e).1;have l:= (Gᶜ.mem_neighborFinset v u).mp (mem_inter.mp j).1;exact (show ¬ G.Adj v u from l.2) h
 have d:(G.neighborFinset v ∩ S) ∪ (Gᶜ.neighborFinset v ∩ S)=S.erase v :=by
  ext u;simp only [mem_union,mem_inter,mem_neighborFinset,compl_adj,mem_erase];constructor
  · rintro (⟨h,e⟩ | ⟨⟨h,_⟩,e⟩)
    · exact ⟨h.ne.symm,e⟩
    · exact ⟨h.symm,e⟩
  · rintro ⟨i,e⟩
    by_cases h:G.Adj v u
    · exact Or.inl ⟨h,e⟩
    · exact Or.inr ⟨⟨i.symm,h⟩,e⟩
 have h :=CA card d;rw [card_union_of_disjoint g,card_erase_of_mem k] at h;have m:=card_pos.mpr ⟨v,k⟩;omega
lemma sL {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (A S:FS V)(r:ℕ) (e:A⊆S)(d:∀ v ∈ A,(Gᶜ.neighborFinset v ∩ S).card<=r):∀ v ∈ A,A.card<=(G.neighborFinset v ∩ A).card+ (r+1) :=by intro v g;have h :=r1 G A v g;have i:(Gᶜ.neighborFinset v ∩ A).card<=r:= (card_le_card (inter_subset_inter_left e)).trans (d v g);omega
lemma uN {V:Type*} [Finite V] (G:SG V)(S:FS V) (n:ℕ)(I:8<=n) (t:¬ CG n ⊑ G):n*S.card<=n*n+16*Nat.card (Gᶜ.induce (S:Set V)).edgeSet:=by
 classical
 let:=Fintype.ofFinite V;let q :=n/4;obtain ⟨A,l,g,d⟩ :=vk Gᶜ S q
 have z:A.card < n:=by
  by_contra s;obtain ⟨C,r,h⟩ :=exists_subset_card_eq (show n<=A.card by omega)
  have w:C⊆S:=r.trans l;have e:∀ v ∈ C,C.card<=(G.neighborFinset v ∩ C).card+ (q+1):=sL G C S q w (fun v y=> d v (r y))
  obtain ⟨v,c,H,k⟩ :=sr G C ∅ (q+1) (by simp) (by simp only [card_empty,add_zero,h];omega) (by simp only [card_empty,zero_add,h];dsimp only [q];omega) e (by intro v y;simp at y)
  apply t;apply (cycleGraph_isContained_iff (by omega:2 < n)).mpr
  exact ⟨v,c,H,by simpa only [card_empty,add_zero,h] using k⟩
 have F:n<=8*q:=by dsimp only [q];omega
 have i:=Nat.mul_le_mul_right (S.card-A.card) F;rw [q7] at g
 have D:n* (S.card-A.card)<=16*Nat.card (Gᶜ.induce (S:Set V)).edgeSet:=by
  nlinarith only [i,g]
 have x:=card_le_card l;have j:=Nat.sub_add_cancel x;have m:=Nat.mul_le_mul_left n z.le;nlinarith only [D,j,m]
lemma q2.t5 {V:Type*} [Fintype V] [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D)(n:ℕ) (r:8<=n) (q:∀ i,¬ CG n ⊑ c.graph i)(p:q1) (s:q3 p =1):(n:O)*(h.qa p).card<=(n:O)^2+48*E:=by
 classical
 obtain ⟨i,t,g⟩ :=xm p s;let S :=h.qa p
 have hsub:(c.graph i)ᶜ.induce (S:Set V)<=h.missing.induce (S:Set V) :=by
  intro u v m;exact h.w4 p i g u.val v.val u.property v.property m
 have e:Nat.card ((c.graph i)ᶜ.induce (S:Set V)).edgeSet<=Nat.card h.missing.edgeSet:= (zW _ _ hsub).trans (t2 h.missing S);have d:=uN (c.graph i) S n r (q i)
 have k:(n:O)*S.card<=(n:O)^2+ 16* (Nat.card ((c.graph i)ᶜ.induce (S:Set V)).edgeSet:O) :=by
  rw [pow_two];exact_mod_cast d
 have l:(Nat.card ((c.graph i)ᶜ.induce (S:Set V)).edgeSet:O)<=Nat.card h.missing.edgeSet:=by exact_mod_cast e
 have j:=h.v9;change (n:O)*S.card<=(n:O)^2+48*E;linarith
def qQ (x y:q1->O): O:= ∑ p,∑ q,qb p q*x p*y q
def u0 (x:q1->O): O:= ∑ p,(q3 p:O)*x p
lemma yO (w:q1->O):qd w =qQ w w-u0 w :=rfl
lemma tD (x y z:q1->O):qQ (x+y) z =qQ x z+qQ y z:=by simp only [qQ,Pi.add_apply,mul_add,add_mul,sum_add_distrib]
lemma x4 (x y z:q1->O):qQ x (y+z)=qQ x y+qQ x z:=by simp only [qQ,Pi.add_apply,mul_add,sum_add_distrib]
lemma aD (x y:q1->O):qQ x y=qQ y x:=by
 rw [qQ,sum_comm];apply sum_congr rfl
 intro p _;apply sum_congr rfl
 intro q _;rw [sm q p];ring
lemma u3 (x:q1->O) (p:q1)(t:O):qQ (Pi.single p t) x =t* ∑ q,qb p q*x q:=by
 classical
 simp [qQ,Pi.single_apply,mul_ite,mul_sum,mul_comm,mul_left_comm]
lemma ym (x:q1->O) (p:q1)(t:O):qQ x (Pi.single p t)=t* ∑ q,qb p q*x q:=by rw [aD,u3]
lemma yb (p:q1)(s t:O):qQ (Pi.single p s) (Pi.single p t)=s*t:=by
 classical
 rw [u3];simp [Pi.single_apply,mul_ite,vU]
lemma dd (x y:q1->O):u0 (x+y)=u0 x +u0 y:=by simp only [u0,Pi.add_apply,mul_add,sum_add_distrib]
lemma aA (p:q1)(t:O):u0 (Pi.single p t)=q3 p *t:=by
 classical
 simp [u0,Pi.single_apply,mul_ite]
lemma rI (w:q1->O) (p:q1)(t:O):qd (w+Pi.single p t)=qd w +t*qm w p+t^2:=by simp only [yO];rw [tD,x4,x4,ym,u3,yb,dd,aA];dsimp [qm];ring
lemma uk (w:q1->O) (p q:q1)(t:O):qm (w+Pi.single p t) q =qm w q+2*t*qb q p:=by
 classical
 simp only [qm,Pi.add_apply,mul_add,sum_add_distrib]
 have d:(∑ r,qb q r* (Pi.single p t:q1->O) r)=qb q p*t :=by
  simp [Pi.single_apply,mul_ite]
 rw [d];ring
def up (w:q1->O) (p q:q1)(t:O):q1->O:= (w+Pi.single p t)+Pi.single q (-t)
def qx (w:q1->O) (p q:q1):q1->O:= up w p q (w q)
lemma xT (w:q1->O) (p q:q1)(t:O) (d:qb p q=1):qd (up w p q t)=qd w +t* (qm w p-qm w q) :=by rw [up,rI,rI,uk,sm q p,d];ring
lemma zl (w:q1->O) (p q:q1)(t:O) (d:qb p q=1):qm (up w p q t) p -qm (up w p q t) q=qm w p-qm w q:=by simp only [up,uk,vU,sm q p,d];ring
lemma uG (w:q1->O) (p q:q1)(d:p≠q):qx w p q q=0:=by
 classical
 simp [qx,up,Ne.symm d]
lemma uH (w:q1->O) (p q:q1)(d:p≠q):qx w p q p=w p+w q:=by
 classical
 simp [qx,up,d]
lemma rL (w:q1->O) (p q r:q1)(d:r≠p) (e:r≠q):qx w p q r=w r:=by
 classical
 simp [qx,up,d,e]
lemma si (w:q1->O) (p q:q1)(j:0<=w p) (i:0<=w q) (e:qb p q=1):qd (qx w p q)<=qd w\/qd (qx w q p)<=qd w :=by
 by_cases d:qm w p<=qm w q
 · left;rw [qx,xT w p q (w q) e];have h :=mul_nonpos_of_nonneg_of_nonpos i (sub_nonpos.mpr d);linarith
 · right
   have g:qb q p=1:= (sm q p).trans e;rw [qx,xT w q p (w p) g];have h :=mul_nonpos_of_nonneg_of_nonpos j (by linarith:qm w q-qm w p<=0)
   linarith
lemma e1 (w:q1->O) (p q:q1)(t:O):(∑ r,up w p q t r)=∑ r,w r:=by
 classical
 simp [up,Pi.add_apply,sum_add_distrib]
lemma v0 {w:q1->O} {p q r:q1} (g:p≠q)(i:0 < w p) (h:0 < qx w p q r):0 < w r :=by
 by_cases e:r=p
 · exact e ▸ i
 by_cases d:r=q
 · rw [d,uG w p q g] at h;exact h.false.elim
 · rwa [rL w p q r e d] at h
lemma q6.transfer {w:q1->O} (i:q6 w)(p q:q1) (g:p≠q)(m:0 < w p) (k:2<=q3 p) (l:2<=q3 q):q6 (qx w p q) :=by
 constructor
 · intro r
   by_cases e:r=p
   · rw [e,uH w p q g];exact add_nonneg (i.nonneg p) (i.nonneg q)
   by_cases d:r=q
   · rw [d,uG w p q g]
   · rw [rL w p q r e d];exact i.nonneg r
 · rw [qx,e1];exact i.sum_four
 · intro r j
   have e:r≠p:=by intro h;subst r;omega
   have d:r≠q:=by intro h;subst r;omega
   rw [rL w p q r e d];exact i.vertex_zero r j
 · intro r j
   have e:r≠p:=by intro h;subst r;omega
   have d:r≠q:=by intro h;subst r;omega
   rw [rL w p q r e d];exact i.edge_le_one r j
 · intro r s j n;exact i.compatible r s (v0 g m j) (v0 g m n)
open scoped Classical in
noncomputable def qe (w:q1->O):FS q1:= univ.filter (fun p=>2<=q3 p/\0 < w p)
lemma za {w:q1->O} (l:q6 w)(p q:q1) (e:p≠q)(k:0 < w p) (d:2<=q3 p):qe (qx w p q)=(qe w).erase q :=by
 classical
 ext r;simp only [qe,mem_filter,mem_univ,true_and,mem_erase];by_cases j:r=p
 · subst r;rw [uH w p q e];have g:0 < w p+w q:=add_pos_of_pos_of_nonneg k (l.nonneg q);exact ⟨fun _=>⟨e,d,k⟩,fun _=>⟨d,g⟩⟩
 by_cases i:r=q
 · subst r;rw [uG w p q e];simp
 · rw [rL w p q r j i];exact ⟨fun h=>⟨i,h⟩,fun h=>h.2⟩
lemma rh {w:q1->O} (j:q6 w)(p q:q1) (g:p≠q)(i:0 < w p) (h:0 < w q) (d:2<=q3 p) (e:2<=q3 q):(qe (qx w p q)).card < (qe w).card:=by
 classical
 rw [za j p q g i d];exact card_erase_lt_of_mem (mem_filter.mpr ⟨mem_univ q,e,h⟩)
lemma yW (w:q1->O) (j:q6 w):∃ v:q1->O,q6 v/\(qe v:Set q1).Pairwise (fun p q=> Disjoint (q0 p) (q0 q))/\qd v<=qd w :=by
 classical
 have t:∀ M:ℕ,∀ w:q1->O,q6 w->(qe w).card=M->∃ v:q1->O,q6 v/\(qe v:Set q1).Pairwise (fun p q=> Disjoint (q0 p) (q0 q))/\qd v<=qd w :=by
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih=>
   intro w j J;by_cases g:(qe w:Set q1).Pairwise (fun p q=> Disjoint (q0 p) (q0 q))
   · exact ⟨w,j,g,le_rfl⟩
   simp only [Set.Pairwise] at g;push Not at g;obtain ⟨p,r,q,m,i,n⟩ :=g;have d:= (mem_filter.mp r).2.1;have e:= (mem_filter.mp m).2.1;have D:= (mem_filter.mp r).2.2;have s:= (mem_filter.mp m).2.2;have l:qb p q=1:=by simp only [qb,if_neg n]
   have k (x:q1->O) (F:q6 x) (I:(qe x).card < (qe w).card) (y:qd x<=qd w):∃ v:q1->O,q6 v/\(qe v:Set q1).Pairwise (fun p q=> Disjoint (q0 p) (q0 q))/\qd v<=qd w :=by
    obtain ⟨v,H,C,z⟩ :=ih (qe x).card (by omega) x F rfl
    exact ⟨v,H,C,z.trans y⟩
   rcases si w p q (j.nonneg p) (j.nonneg q) l with
    hE | hE
   · exact k (qx w p q) (j.transfer p q i D d e) (rh j p q i D s d e) hE
   · exact k (qx w q p) (j.transfer q p i.symm s e d) (rh j q p i.symm s D e d) hE
 exact t (qe w).card w j rfl
lemma ws (x:q1->O) (d:∀ p q,p≠q->qb p q*x p*x q=0):qQ x x= ∑ p,x p^2:=by
 unfold qQ;apply sum_congr rfl
 intro p _;rw [sum_eq_single p]
 · rw [vU];ring
 · intro q _ e;exact d p q e.symm
 · intro g;exact (g (mem_univ p)).elim
lemma vB (x:q1->O) (S:FS q1)(d:∀ p,p ∉ S->x p=0) (i:∀ p ∈ S,q3 p =1) (h:(S:Set q1).Pairwise (fun p q=> Disjoint (q0 p) (q0 q))):qd x=(∑ p ∈ S,x p^2) - ∑ p ∈ S,x p:=by
 classical
 have g (p q:q1) (k:p≠q):qb p q*x p*x q=0:=by
  by_cases e:p∈S
  · by_cases m:q∈S
    · simp only [qb,if_pos (h e m k),zero_mul]
    · rw [d q m,mul_zero]
  · rw [d p e,mul_zero,zero_mul]
 have l:(∑ p,x p^2)=∑ p ∈ S,x p^2:=by
  symm;apply sum_subset (subset_univ S)
  intro p _ e;rw [d p e];norm_num
 have j:u0 x=∑ p ∈ S,x p:=by
  calc
   u0 x=∑ p ∈ S,(q3 p:O)*x p :=by
    symm;apply sum_subset (subset_univ S)
    intro p _ e;rw [d p e,mul_zero]
   _= ∑ p ∈ S,x p:=by
    apply sum_congr rfl
    intro p e;rw [i p e];norm_num
 rw [yO,ws x g,l,j]
lemma tE (p:q1):qb qF p =1:=by
 have d:q0 qF=univ:=by decide
 have e:(q0 p).Nonempty:=by
  apply card_pos.mp;rw [qU];positivity
 have g:¬ Disjoint (q0 qF) (q0 p) :=by
  intro i;obtain ⟨v,h⟩ :=e;exact D1 i (by rw [d];exact mem_univ v) h
 simp only [qb,if_neg g]
lemma xg (x:q1->O):qm x qF=2* (∑ p,x p)-3:=by simp only [qm,tE,one_mul,zx,Nat.cast_ofNat]
lemma wT {I:Type*} (S:FS I)(f:I->O) (m:ℕ)(d:S.card<=m):(∑ i ∈ S,f i)^2<=(m:O) * ∑ i ∈ S,f i^2:=by
 have h :=sum_mul_sq_le_sq_mul_sq S f (fun _=>(1:O))
 have e:(∑ i ∈ S,f i)^2<=(S.card:O) * ∑ i ∈ S,f i^2:=by
  simpa only [mul_one,one_pow,sum_const,nsmul_eq_mul,mul_one,mul_comm] using h
 apply e.trans;apply mul_le_mul_of_nonneg_right (by exact_mod_cast d)
 exact sum_nonneg fun i _=> sq_nonneg (f i)
lemma zC {I:Type*} (S:FS I)(f:I->O) (d:∀ i ∈ S,f i<=1):(∑ i ∈ S,f i)<=S.card:=by
 calc
  (∑ i ∈ S,f i)<=∑ _i ∈ S,(1:O) :=sum_le_sum d
  _=S.card:=by simp
lemma uB {I:Type*} (S:FS I)(f:I->O) (m:ℕ)(e:S.card<=m) (l:∀ i ∈ S,f i<=1) (d: ∑ i ∈ S,f i= (m:O)):S.card=m/\∀ i ∈ S,f i=1:=by
 have k:(m:O)<=S.card:=by rw [<- d];exact zC S f l
 have q:S.card=m:=by exact_mod_cast le_antisymm (by exact_mod_cast e) k
 refine ⟨q,?_⟩
 intro i n;by_contra g;have h:(∑ j ∈ S,f j) < ∑ _j ∈ S,(1:O):=sum_lt_sum l ⟨i,n,lt_of_le_of_ne (l i n) g⟩;simp only [d,sum_const,nsmul_eq_mul,mul_one,q,lt_self_iff_false] at h
lemma q6.aB {w:q1->O} (d:q6 w):(∑ p ∈ ql w,w p)^2<=4* ∑ p ∈ ql w,w p^2:=by exact wT (ql w) w 4 d.vl
lemma a8 (z E S:O)(e:0<=z) (h:0<=E) (d:E+z=4) (i:E^2<=4*S):z<=z^2+2*z*E+S-E-3*z:=by have g:0<=z*E:=mul_nonneg e h;nlinarith
lemma xZ (g h e d k l:O)(n:0<=e) (i:e<=2) (m:0<=d) (j:d<=2) (w:e^2<=2*k) (v:d^2<=2*l) (s:g+e+h+d=4):0<=g^2+2*g*e+k-2*g-e+ (h^2+2*h*d+l-2*h-d) :=by have r:=mul_nonneg n (sub_nonneg.mpr i);have q:=mul_nonneg m (sub_nonneg.mpr j);have t:=sq_nonneg (g+e-2);have x:=sq_nonneg (h+d-2);nlinarith
lemma y5 (g i e d n q:O)(s:0<=e) (m:e<=2) (v:0<=d) (l:d<=2) (C:e^2<=2*n) (H:d^2<=2*q) (y:g+e+i+d=4) (F:g^2+2*g*e+n-2*g-e+ (i^2+2*i*d+q-2*i-d)=0):g+e=2/\i+d=2/\(e=0\/e=2)/\(d=0\/d=2) :=by
 have x:=mul_nonneg s (sub_nonneg.mpr m);have w:=mul_nonneg v (sub_nonneg.mpr l);have z:=sq_nonneg (g+e-2);have D:=sq_nonneg (i+d-2);have r:g+e=2:=by nlinarith
 have t:i+d=2:=by nlinarith
 have j:e* (2-e)=0:=by nlinarith
 have k:d* (2-d)=0:=by nlinarith
 refine ⟨r,t,?_,?_⟩
 · rcases mul_eq_zero.mp j with h | h
   · exact Or.inl h
   · right;linarith
 · rcases mul_eq_zero.mp k with h | h
   · exact Or.inl h
   · right;linarith
lemma q6.u6 {w:q1->O} (r:q6 w)(n:∀ p,2<=q3 p->p≠qF->w p =0):w qF<=qd w :=by
 classical
 let E :=ql w;let x (p:q1): O:=if p =qF then 0 else w p
 have y (p:q1) (l:p∈E):x p =w p:=by
  have C:= (mem_filter.mp l).2.1;have v:p≠qF:=by intro h;subst p;rw [zx] at C;omega
  exact if_neg v
 have g (p:q1) (l:p ∉ E):x p =0:=by
  by_cases i:p=qF
  · exact if_pos i
  rw [show x p=w p from if_neg i];by_cases z:q3 p =0
  · exact r.vertex_zero p z
  by_cases t:q3 p =1
  · have s:¬ 0 < w p:=fun h=>l (mem_filter.mpr ⟨mem_univ p,t,h⟩)
    exact le_antisymm (le_of_not_gt s) (r.nonneg p)
  · exact n p (by omega) i
 have d:w=x+Pi.single qF (w qF) :=by
  funext p;by_cases i:p=qF
  · subst p;simp [x]
  · simp [x,i]
 have m:(∑ p,x p)=∑ p ∈ E,w p:=by
  calc
   (∑ p,x p)=∑ p ∈ E,x p:=by
    symm;exact sum_subset (subset_univ E) (fun p _ l=> g p l)
   _= ∑ p ∈ E,w p:=sum_congr rfl y
 have e:qd x=(∑ p ∈ E,w p^2) - ∑ p ∈ E,w p:=by
  rw [vB x E g (fun p l=> (mem_filter.mp l).2.1) r.s0]
  congr 1
  · exact sum_congr rfl (fun p l=> CA (fun a:O=> a ^2) (y p l))
  · exact sum_congr rfl y
 have j:(∑ p ∈ E,w p)+w qF=4:=by
  calc
   (∑ p ∈ E,w p)+w qF= (∑ p,x p)+w qF:=by rw [m]
   _= ∑ p,((x+Pi.single qF (w qF)):q1->O) p :=by
    simp [Pi.add_apply,sum_add_distrib]
   _= ∑ p,w p:=CA (fun f:q1->O=> ∑ p,f p) d.symm
   _=4:=r.sum_four
 have q:qd w=(∑ p ∈ E,w p^2)-(∑ p ∈ E,w p)+w qF* (2* (∑ p ∈ E,w p)-3)+(w qF)^2:=by
  calc
   qd w =qd (x+Pi.single qF (w qF)) :=CA qd d
   _=_:=by rw [rI,e,xg,m]
 have k:=a8 (w qF) (∑ p ∈ E,w p) (∑ p ∈ E,w p^2) (r.nonneg qF) (sum_nonneg fun p _=> r.nonneg p) j r.aB
 rw [q];nlinarith only [k]
lemma z4:∀ (i:Fin 3)(b:Bool),cF i b≠cF i (!b) :=by decide
lemma se:∀ (i:Fin 3)(b:Bool) (p:q1),q3 p =1->(q0 p ∩ q0 (cF i b)).card≠1->q0 p⊆q0 (cF i b)\/q0 p⊆q0 (cF i (!b)) :=by decide
lemma ta:∀ (i:Fin 3)(b:Bool) (p:q1),q3 p =1->¬ (q0 p⊆q0 (cF i b)/\q0 p⊆q0 (cF i (!b))) :=by decide
lemma tC {p q:q1} (hsub:q0 q⊆q0 p):qb p q=1:=by
 have d:(q0 q).Nonempty:=by
  apply card_pos.mp;rw [qU];positivity
 have e:¬ Disjoint (q0 p) (q0 q) :=by
  intro h;obtain ⟨v,g⟩ :=d;exact D1 h (hsub g) g
 simp only [qb,if_neg e]
lemma zZ (i:Fin 3)(b:Bool):qb (cF i b) (cF i (!b))=0:=by
 have e:b≠!b:=by cases b <;> decide
 have d:= (ui i i b (!b)).mpr ⟨rfl,e⟩;simp only [qb,if_pos d]
lemma we (i:Fin 3)(b:Bool) (p:q1)(hsub:q0 p⊆q0 (cF i (!b))):qb (cF i b) p =0:=by
 have e:b≠!b:=by cases b <;> decide
 have d:= ((ui i i b (!b)).mpr ⟨rfl,e⟩).mono_right hsub;simp only [qb,if_pos d]
noncomputable def qf (w:q1->O) (i:Fin 3)(b:Bool):FS q1:= (ql w).filter (fun p=>q0 p⊆q0 (cF i b))
lemma ut (w:q1->O) (i:Fin 3)(b:Bool):qf w i b⊆ql w :=filter_subset _ _
lemma q6.uL {w:q1->O} (e:q6 w)(i:Fin 3) (b:Bool):(qf w i b).card<=2:=by
 have h :=vh (qf w i b) (q0 (cF i b)) (fun p d=> (mem_filter.mp (mem_filter.mp d).1).2.1) (e.s0.mono (ut w i b)) (fun p d=> (mem_filter.mp d).2)
 rw [qU,r4] at h;norm_num at h;omega
lemma w0 (w:q1->O) (i:Fin 3)(b:Bool):Disjoint (qf w i b) (qf w i (!b)) :=by
 rw [Finset.disjoint_left]
 intro p d g;have e:= (mem_filter.mp (mem_filter.mp d).1).2.1;exact ta i b p e ⟨(mem_filter.mp d).2,(mem_filter.mp g).2⟩
lemma xc {w:q1->O} (j:q6 w)(i:Fin 3) (b:Bool)(g:0 < w (cF i b)):qf w i b ∪ qf w i (!b)=ql w :=by
 apply Subset.antisymm
 · exact union_subset (ut w i b) (ut w i (!b))
 · intro p e
   have k:= (mem_filter.mp e).2.1;have d:= (mem_filter.mp e).2.2;rcases se i b p k (j.compatible p (cF i b) d g) with h | h
   · exact mem_union_left _ (mem_filter.mpr ⟨e,h⟩)
   · exact mem_union_right _ (mem_filter.mpr ⟨e,h⟩)
lemma q6.ud {w:q1->O} (d:q6 w)(i:Fin 3) (b:Bool):(∑ p ∈ qf w i b,w p)<=2:=by
 apply (zC (qf w i b) w ?_).trans
 · exact_mod_cast d.uL i b
 · intro p e;exact d.edge_le_one p (mem_filter.mp (mem_filter.mp e).1).2.1
lemma q6.sf {w:q1->O} (d:q6 w)(i:Fin 3) (b:Bool):(∑ p ∈ qf w i b,w p)^2<=2* ∑ p ∈ qf w i b,w p^2:= wT (qf w i b) w 2 (d.uL i b)
lemma sG (w x:q1->O) (i:Fin 3)(b:Bool) (j:∀ p ∈ ql w,x p=w p) (d:∀ p,p ∉ ql w->x p=0) (e:∀ p ∈ ql w,q0 p⊆q0 (cF i b)\/q0 p⊆q0 (cF i (!b))):qm x (cF i b)=2* (∑ p ∈ qf w i b,w p)-2:=by
 classical
 have g:(∑ p,qb (cF i b) p *x p)=∑ p ∈ qf w i b,w p:=by
  calc
   (∑ p,qb (cF i b) p *x p)=∑ p ∈ ql w,qb (cF i b) p *x p:=by
    symm;apply sum_subset (subset_univ _)
    intro p _ h;rw [d p h,mul_zero]
   _= ∑ p ∈ qf w i b,w p:=by
    rw [qf,sum_filter];apply sum_congr rfl
    intro p h;rw [j p h];by_cases hsub:q0 p⊆q0 (cF i b)
    · rw [if_pos hsub,tC hsub,one_mul]
    · rw [if_neg hsub,we i b p ((e p h).resolve_left hsub),zero_mul]
 simp only [qm,g,r4,Nat.cast_ofNat]
lemma q6.sQ {w:q1->O} (k:q6 w)(i:Fin 3) (b:Bool)(m:0 < w (cF i b)) (K:∀ r,2<=q3 r->r≠cF i b->r≠cF i (!b)->w r =0):0<=qd w/\(qd w =0->w (cF i b)+(∑ r ∈ qf w i b,w r)=2/\w (cF i (!b))+(∑ r ∈ qf w i (!b),w r)=2/\((∑ r ∈ qf w i b,w r)=0\/(∑ r ∈ qf w i b,w r)=2)/\((∑ r ∈ qf w i (!b),w r)=0\/(∑ r ∈ qf w i (!b),w r)=2)) :=by
 classical
 let p :=cF i b;let q :=cF i (!b);have P:p≠q:=z4 i b;let E :=ql w;let x (r:q1): O:=if r =p\/r=q then 0 else w r
 have Q (r:q1) (t:r∈E):x r =w r:=by
  have R:= (mem_filter.mp t).2.1
  have L:r≠p:=by
   intro h;subst r;change q3 (cF i b)=1 at R;rw [r4] at R;omega
  have M:r≠q:=by
   intro h;subst r;change q3 (cF i (!b))=1 at R;rw [r4] at R;omega
  exact if_neg (not_or.mpr ⟨L,M⟩)
 have d (r:q1) (t:r ∉ E):x r =0:=by
  by_cases e:r=p\/r=q
  · exact if_pos e
  rw [show x r=w r from if_neg e];by_cases U:q3 r =0
  · exact k.vertex_zero r U
  by_cases T:q3 r =1
  · have W:¬ 0 < w r:=fun h=>t (mem_filter.mpr ⟨mem_univ r,T,h⟩)
    exact le_antisymm (le_of_not_gt W) (k.nonneg r)
  · exact K r (by omega) (not_or.mp e).1 (not_or.mp e).2
 have l:w= (x+Pi.single p (w p))+Pi.single q (w q) :=by
  funext r;by_cases L:r=p
  · subst r;simp [x,P]
  by_cases M:r=q
  · subst r;simp [x,Ne.symm P]
  · simp [x,L,M]
 have N:(∑ r,x r)=∑ r ∈ E,w r:=by
  calc
   (∑ r,x r)=∑ r ∈ E,x r:=by
    symm;exact sum_subset (subset_univ E) (fun r _ t=> d r t)
   _= ∑ r ∈ E,w r:=sum_congr rfl Q
 have H:qd x=(∑ r ∈ E,w r^2) - ∑ r ∈ E,w r:=by
  rw [vB x E d (fun r t=> (mem_filter.mp t).2.1) k.s0]
  congr 1
  · exact sum_congr rfl (fun r t=> CA (fun a:O=> a ^2) (Q r t))
  · exact sum_congr rfl Q
 let j:= ∑ r ∈ qf w i b,w r;let g:= ∑ r ∈ qf w i (!b),w r;let n:= ∑ r ∈ qf w i b,w r^2;let y:= ∑ r ∈ qf w i (!b),w r^2
 have v:(∑ r ∈ E,w r)=j+g:=by
  dsimp only [E];rw [<- xc k i b m,sum_union (w0 w i b)]
 have D:(∑ r ∈ E,w r^2)=n+y:=by
  dsimp only [E];rw [<- xc k i b m,sum_union (w0 w i b)]
 have F (r:q1) (t:r∈E):q0 r⊆q0 p\/q0 r⊆q0 q :=
  se i b r (mem_filter.mp t).2.1 (k.compatible r p (mem_filter.mp t).2.2 m)
 have z:qm x p=2*j-2:= sG w x i b Q d F
 have C:qm x q=2*g-2:=by
  apply sG w x i (!b) Q d
  intro r t;simpa only [Bool.not_not] using (F r t).symm
 have s:w p+j+w q+g=4:=by
  have X:(∑ r,x r)+w p +w q=4:=by
   calc
    (∑ r,x r)+w p +w q= ∑ r,(((x+Pi.single p (w p))+Pi.single q (w q)):q1->O) r :=by
     simp [Pi.add_apply,sum_add_distrib]
    _= ∑ r,w r:=CA (fun f:q1->O=> ∑ r,f r) l.symm
    _=4:=k.sum_four
  rw [N,v] at X;linarith
 have J:qb q p=0:= (sm q p).trans (zZ i b)
 have I:qd w=(w p)^2+2*w p*j+n-2*w p-j+ ((w q)^2+2*w q*g+y-2*w q-g) :=by
  calc
   qd w =qd ((x+Pi.single p (w p))+Pi.single q (w q)):=CA qd l
   _=_:=by
    rw [rI,rI,uk,z,C,J,H,v,D];ring
 constructor
 · rw [I];exact xZ (w p) (w q) j g n y (sum_nonneg fun r _=> k.nonneg r) (k.ud i b) (sum_nonneg fun r _=> k.nonneg r) (k.ud i (!b)) (k.sf i b) (k.sf i (!b)) s
 · intro d;rw [I] at d;exact y5 (w p) (w q) j g n y (sum_nonneg fun r _=> k.nonneg r) (k.ud i b) (sum_nonneg fun r _=> k.nonneg r) (k.ud i (!b)) (k.sf i b) (k.sf i (!b)) s d
lemma q6.zc {w:q1->O} (g:q6 w)(i:Fin 3) (b:Bool)(e:0 < w (cF i b)) (d:∀ r,2<=q3 r->r≠cF i b->r≠cF i (!b)->w r =0):0<=qd w:=(g.sQ i b e d).1
lemma u5:∀ (i:Fin 3)(b:Bool) (p:q1),2<=q3 p->Disjoint (q0 (cF i b)) (q0 p)->p=cF i (!b) :=by decide
lemma uy (w:q1->O) (s:q6 w)(m:(qe w:Set q1).Pairwise (fun p q=> Disjoint (q0 p) (q0 q))):0<=qd w :=by
 classical
 by_cases e:∃ p:q1,q3 p =2/\0 < w p
 · obtain ⟨p,d,H⟩ :=e
   obtain ⟨i,b,rfl⟩:=(u1 p).mp d;apply s.zc i b H
   intro r D x y;by_contra g;have l:0 < w r:=lt_of_le_of_ne (s.nonneg r) (Ne.symm g);have C:cF i b∈qe w:=mem_filter.mpr ⟨mem_univ _,by rw [r4],H⟩
   have v:r∈qe w :=mem_filter.mpr ⟨mem_univ _,D,l⟩;exact y (u5 i b r D (m C v x.symm))
 · have j:∀ p,2<=q3 p->p≠qF->w p =0:=by
    intro p d n;have z:q3 p≠3 :=fun h=>n ((sz p).mp h)
    have F:=sM p;have k:q3 p =2:=by omega
    have t:¬ 0 < w p:=fun h=>e ⟨p,k,h⟩
    exact le_antisymm (le_of_not_gt t) (s.nonneg p)
   exact (s.nonneg qF).trans (s.u6 j)
lemma zS (w:q1->O) (h:q6 w):0<=qd w :=by obtain ⟨v,g,e,d⟩ :=yW w h;exact (uy v g e).trans d
structure qs (w:q1->O):Prop where
 normalized:∀ p,0 < w p->(q3 p =1/\w p=1)\/(q3 p =2/\w p=2)
 disjoint:∀ p q,p≠q->0 < w p->0 < w q->Disjoint (q0 p) (q0 q)
open scoped Classical in
noncomputable def qj (w:q1->O):FS q1:= univ.filter (fun p=>0 < w p)
lemma q6.eq_zero_of_not_pos {w:q1->O} (e:q6 w)(p:q1) (d:¬ 0 < w p):w p =0:= le_antisymm (le_of_not_gt d) (e.nonneg p)
lemma q6.tA {w:q1->O} (d:q6 w):(∑ p ∈ qj w,w p)=4:=by
 classical
 calc
  (∑ p ∈ qj w,w p)=∑ p,w p:=by
   apply sum_subset (subset_univ _)
   intro p _ e;apply d.eq_zero_of_not_pos
   intro h;exact e (mem_filter.mpr ⟨mem_univ p,h⟩)
  _=4:=d.sum_four
lemma qs.zh {w:q1->O} (h:qs w)(p:q1) (g:0 < w p):((q0 p).card:O)=2*w p:=by
 rcases h.normalized p g with ⟨d,e⟩ | ⟨d,e⟩ <;>
  rw [qU,d,e] <;> norm_num
lemma qs.cover {w:q1->O} (l:qs w)(n:q6 w):(qj w).biUnion q0=univ:=by
 classical
 have d:(qj w:Set q1).Pairwise (fun p q=> Disjoint (q0 p) (q0 q)) :=by
  intro p j q m k;exact l.disjoint p q k (mem_filter.mp j).2 (mem_filter.mp m).2
 have e:(∑ p ∈ qj w,((q0 p).card:O))=8:=by
  calc
   (∑ p ∈ qj w,((q0 p).card:O))=∑ p ∈ qj w,2*w p:= sum_congr rfl (fun p j=> l.zh p (mem_filter.mp j).2)
   _=2* ∑ p ∈ qj w,w p:= (mul_sum _ _ _).symm
   _=8:=by rw [n.tA];norm_num
 have g:(∑ p ∈ qj w,(q0 p).card)=8:=by
  exact_mod_cast e
 have i:((qj w).biUnion q0).card=8:=by
  rw [card_biUnion d,g]
 have h:(univ:FS wz).card=8:=by decide
 exact eq_of_subset_of_card_le (subset_univ _) (by omega)
lemma qs.ts {w:q1->O} (l:qs w)(n:q6 w) (S:FS wz):(∑ p ∈ qj w,(q0 p ∩ S).card)=S.card:=by
 classical
 have g:(qj w:Set q1).Pairwise (fun p q=> Disjoint (q0 p ∩ S) (q0 q ∩ S)) :=by
  intro p i q m k;exact (l.disjoint p q k (mem_filter.mp i).2 (mem_filter.mp m).2).mono inter_subset_left inter_subset_left
 have d:(qj w).biUnion (fun p=>q0 p ∩ S)=S:=by
  ext v;constructor
  · intro j;obtain ⟨p,i,e⟩ :=mem_biUnion.mp j;exact (mem_inter.mp e).2
  · intro j
    have h:v∈(qj w).biUnion q0:=by
     rw [l.cover n];exact mem_univ v
    obtain ⟨p,i,e⟩ :=mem_biUnion.mp h;exact mem_biUnion.mpr ⟨p,i,mem_inter.mpr ⟨e,j⟩⟩
 rw [<- card_biUnion g,d]
lemma q6.a0 {w:q1->O} (k:q6 w)(g:∀ p,q3 p≠1->w p=0):qs w :=by
 classical
 have d (p:q1) (e:0 < w p):q3 p =1:=by
  by_contra h;rw [g p h] at e;exact e.false
 have l:(∑ p ∈ ql w,w p)=4:=by
  calc
   (∑ p ∈ ql w,w p)=∑ p,w p:=by
    apply sum_subset (subset_univ _)
    intro p _ e;apply k.eq_zero_of_not_pos
    intro i;exact e (mem_filter.mpr ⟨mem_univ p,d p i,i⟩)
   _=4:=k.sum_four
 obtain ⟨_,j⟩ :=uB (ql w) w 4 k.vl (fun p e=> k.edge_le_one p (mem_filter.mp e).2.1) l
 constructor
 · intro p e;exact Or.inl ⟨d p e,j p (mem_filter.mpr ⟨mem_univ p,d p e,e⟩)⟩
 · intro p q m e n;exact ru p q (d p e) (d q n) m (k.compatible p q e n)
lemma q6.wy {w:q1->O} (j:q6 w)(d:∀ p,2<=q3 p->p≠qF->w p =0) (e:qd w =0):qs w :=by
 have g:w qF=0:=by
  have h :=j.u6 d;rw [e] at h;exact le_antisymm h (j.nonneg qF)
 apply j.a0
 intro p l;by_cases k:q3 p =0
 · exact j.vertex_zero p k
 by_cases i:p=qF
 · exact i ▸ g
 · exact d p (by omega) i
lemma q6.wO {w:q1->O} (y:q6 w)(i:Fin 3) (b:Bool)(v:0 < w (cF i b)) (n:∀ r,2<=q3 r->r≠cF i b->r≠cF i (!b)->w r =0) (H:qd w =0):qs w :=by
 classical
 let p :=cF i b;let q :=cF i (!b);have h2:p≠q:=z4 i b;obtain ⟨m,e,J,x⟩:=(y.sQ i b v n).2 H
 have g:(∑ r ∈ qf w i b,w r)=0:=by
  rcases J with h | h
  · exact h
  · rw [h] at m;linarith
 have Z:w p=2:=by
  rw [g] at m;simpa only [add_zero] using m
 have h1:w q=0\/w q=2:=by
  rcases x with h | h
  · right;rw [h] at e;simpa only [add_zero] using e
  · left;rw [h] at e;change w q+2=2 at e;linarith
 have I (r:q1) (j:q3 r =1) (l:0 < w r):w r =1/\q0 r⊆q0 q/\w q=0:=by
  have Q:r∈ql w :=mem_filter.mpr ⟨mem_univ r,j,l⟩
  have W:¬ q0 r⊆q0 p :=by
   intro hsub;have C:r∈qf w i b :=mem_filter.mpr ⟨Q,hsub⟩;have P:=single_le_sum (fun s _=> y.nonneg s) C
   rw [g] at P;linarith
  have hsub:q0 r⊆q0 q:=(se i b r j (y.compatible r p l v)).resolve_left W;have C:r∈qf w i (!b) :=mem_filter.mpr ⟨Q,hsub⟩
  have t:(∑ s ∈ qf w i (!b),w s)=2:=by
   rcases x with h | h
   · have P:=single_le_sum (fun s _=> y.nonneg s) C
     rw [h] at P;linarith
   · exact h
  obtain ⟨_,M⟩ :=uB (qf w i (!b)) w 2 (y.uL i (!b)) (fun s D=> y.edge_le_one s (mem_filter.mp (mem_filter.mp D).1).2.1) t
  have z:w q=0:=by rw [t] at e;change w q+2=2 at e;linarith
  exact ⟨M r C,hsub,z⟩
 have d (r:q1) (l:0 < w r):r=p\/r=q\/(q3 r =1/\w r=1/\q0 r⊆q0 q/\w q=0) :=by
  by_cases R:r=p
  · exact Or.inl R
  by_cases T:r=q
  · exact Or.inr (Or.inl T)
  have j:q3 r =1:=by
   by_contra hd;by_cases h0:q3 r =0
   · rw [y.vertex_zero r h0] at l;exact l.false
   · rw [n r (by omega) R T] at l
     exact l.false
  exact Or.inr (Or.inr ⟨j,I r j l⟩)
 have k:Disjoint (q0 p) (q0 q):=(ui i i b (!b)).mpr ⟨rfl,by cases b <;> decide⟩
 constructor
 · intro r l
   rcases d r l with rfl | rfl | ⟨hd,y,_,_⟩
   · exact Or.inr ⟨r4 i b,Z⟩
   · have Y:w q=2:=h1.resolve_left (ne_of_gt l);exact Or.inr ⟨r4 i (!b),Y⟩
   · exact Or.inl ⟨hd,y⟩
 · intro r s N l D
   rcases d r l with rfl | rfl | ⟨X,h4,F,K⟩
   · rcases d s D with rfl | rfl | ⟨U,h3,L,_⟩
     · exact (N rfl).elim
     · exact k
     · exact k.mono_right L
   · rcases d s D with rfl | rfl | ⟨_,_,_,K⟩
     · exact k.symm
     · exact (N rfl).elim
     · rw [K] at l;exact l.false.elim
   · rcases d s D with rfl | rfl | ⟨U,_,_,_⟩
     · exact (k.mono_right F).symm
     · rw [K] at D;exact D.false.elim
     · exact ru r s X U N (y.compatible r s l D)
lemma w9:∀ p q:q1,q3 p =2->q3 q =2->p≠q->¬ Disjoint (q0 p) (q0 q)->(q0 p ∩ q0 q).card=2:=by decide
lemma qs.tN {w:q1->O} (g:qs w)(i:q6 w) (p:q1)(j:0 < w p):qm w p=2*w p-q3 p :=by
 classical
 unfold qm;rw [sum_eq_single p]
 · rw [vU,one_mul]
 · intro q _ d
   by_cases e:0 < w q
   · simp only [qb,if_pos (g.disjoint p q d.symm j e),zero_mul]
   · rw [i.eq_zero_of_not_pos q e,mul_zero]
 · intro h;exact (h (mem_univ p)).elim
lemma qs.zK {w:q1->O} (I:qs w)(J:q6 w) (p q:q1)(K:0 < w p) (n:q3 p =2) (d:q3 q =2) (C:p≠q)(e:¬ Disjoint (q0 p) (q0 q)):4<=qm w q:=by
 classical
 have D:w p=2:=by
  rcases I.normalized p K with ⟨x,_⟩ | ⟨_,h⟩
  · omega
  · exact h
 have g:=w9 p q n d C e
 have m:qb q p=1:=by
  have t:¬ Disjoint (q0 q) (q0 p) :=fun h=>e h.symm
  simp only [qb,if_neg t]
 have j:(∑ r ∈ qj w,((q0 r ∩ q0 q).card:O))=4:=by
  have h :=I.ts J (q0 q);rw [qU,d] at h;exact_mod_cast h
 have l (r:q1) (y:r∈qj w):((q0 r ∩ q0 q).card:O)+(if r =p then 2 else 0)<=2* (qb q r*w r) :=by
  by_cases z:r=p
  · subst r;rw [g,if_pos rfl,m,D];norm_num
  rw [if_neg z,add_zero];by_cases x:Disjoint (q0 q) (q0 r)
  · have F:q0 r ∩ q0 q=∅ :=disjoint_iff_inter_eq_empty.mp x.symm;simp only [F,card_empty,Nat.cast_zero,qb,if_pos x,zero_mul,mul_zero,le_refl]
  · have v:((q0 r ∩ q0 q).card:O)<=(q0 r).card:=by
     exact_mod_cast card_le_card (show q0 r ∩ q0 q⊆q0 r from inter_subset_left)
    rw [I.zh r (mem_filter.mp y).2] at v;simpa only [qb,if_neg x,one_mul] using v
 have i:=sum_le_sum l;have H:p∈qj w :=mem_filter.mpr ⟨mem_univ p,K⟩
 have s:(∑ r ∈ qj w,qb q r*w r)=∑ r,qb q r*w r:=by
  apply sum_subset (subset_univ _)
  intro r _ y;have F:w r=0:=J.eq_zero_of_not_pos r (fun h=>y (mem_filter.mpr ⟨mem_univ r,h⟩))
  rw [F,mul_zero]
 rw [sum_add_distrib,j] at i;have k:(∑ r ∈ qj w,if r =p then (2:O) else 0)=2:=by simp [H]
 rw [k,<- mul_sum,s] at i;simp only [qm,d,Nat.cast_ofNat];linarith only [i]
lemma qs.yU {w:q1->O} (r:qs w)(s:q6 w) (p q:q1)(t:0 < w p) (k:2<=q3 p) (v:2<=q3 q) (l:p≠q)(e:qb p q=1):qm w p < qm w q:=by
 have d:q3 p =2/\w p=2:=by
  rcases r.normalized p t with ⟨z,_⟩ | h
  · omega
  · exact h
 have j:qm w p=2:=by
  rw [r.tN s p t,d.1,d.2];norm_num
 rw [j];by_cases m:q3 q =3
 · have x:q=qF:= (sz q).mp m;rw [x,xg,s.sum_four];norm_num
 · have i:=sM q
   have n:q3 q =2:=by omega
   have g:¬ Disjoint (q0 p) (q0 q) :=by
    intro h;simp only [qb,if_pos h] at e;norm_num at e
   have y:=r.zK s p q t d.1 n l g;linarith
lemma sK (w:q1->O) (s:q6 w)(m:(qe w:Set q1).Pairwise (fun p q=> Disjoint (q0 p) (q0 q))) (d:qd w =0):qs w :=by
 classical
 by_cases g:∃ p:q1,q3 p =2/\0 < w p
 · obtain ⟨p,e,F⟩ :=g
   obtain ⟨i,b,rfl⟩:=(u1 p).mp e;apply s.wO i b F ?_ d
   intro r C v x;by_contra j;have l:0 < w r:=lt_of_le_of_ne (s.nonneg r) (Ne.symm j);have z:cF i b∈qe w:=mem_filter.mpr ⟨mem_univ _,by rw [r4],F⟩
   have t:r∈qe w :=mem_filter.mpr ⟨mem_univ _,C,l⟩;exact x (u5 i b r C (m z t v.symm))
 · apply s.wy ?_ d
   intro p e n;have y:q3 p≠3 :=fun h=>n ((sz p).mp h)
   have D:=sM p;have k:q3 p =2:=by omega
   exact s.eq_zero_of_not_pos p (fun h=>g ⟨p,k,h⟩)
lemma xf {w:q1->O} (s:q6 w)(p q:q1) (i:p≠q)(r:0 < w p) (n:0 < w q) (e:2<=q3 p) (g:2<=q3 q) (d:qb p q=1) (t:qs (qx w p q)):qd (qx w p q) < qd w :=by
 have l:=s.transfer p q i r e g
 have k:0 < qx w p q p:=by
  rw [uH w p q i];exact add_pos r n
 have m:=t.yU l p q k e g i d;have h:=zl w p q (w q) d;change qm (qx w p q) p -qm (qx w p q) q=qm w p-qm w q at h;have hneg:qm w p-qm w q < 0:=by linarith
 have j:=mul_neg_of_pos_of_neg n hneg;rw [qx,xT w p q (w q) d];linarith
lemma y9 (w:q1->O) (l:q6 w)(j:qd w =0):qs w :=by
 classical
 have C:∀ M:ℕ,∀ w:q1->O,q6 w->(qe w).card=M->qd w =0->qs w :=by
  intro M
  induction M using Nat.strong_induction_on with
  | h M ih=>
   intro w l J j;by_cases z:(qe w:Set q1).Pairwise (fun p q=> Disjoint (q0 p) (q0 q))
   · exact sK w l z j
   simp only [Set.Pairwise] at z;push Not at z;obtain ⟨p,y,q,s,k,x⟩ :=z;have d:= (mem_filter.mp y).2.1;have e:= (mem_filter.mp s).2.1;have m:= (mem_filter.mp y).2.2;have r:= (mem_filter.mp s).2.2;have i:qb p q=1:=by simp only [qb,if_neg x]
   have g (p q:q1) (k:p≠q) (m:0 < w p) (r:0 < w q) (d:2<=q3 p) (e:2<=q3 q) (i:qb p q=1) (v:qd (qx w p q)<=qd w):False:=by
    have t:=l.transfer p q k m d e;have F:=rh l p q k m r d e;have H:qd (qx w p q)=0:= le_antisymm (by rwa [j] at v) (zS _ t)
    have I:=ih (qe (qx w p q)).card (by omega) (qx w p q) t rfl H
    have n:=xf l p q k m r d e i I;rw [H,j] at n;exact n.false
   rcases si w p q (l.nonneg p) (l.nonneg q) i with
    v | v
   · exact (g p q k m r d e i v).elim
   · have D:qb q p=1:= (sm q p).trans i;exact (g q p k.symm r m e d D v).elim
 exact C (qe w).card w l rfl j
lemma qs.ct {w:q1->O} (k:qs w)(g:q6 w):qd w =0:=by
 classical
 have d (p q:q1) (h:p≠q):qb p q*w p*w q=0:=by
  by_cases e:0 < w p
  · by_cases j:0 < w q
    · simp only [qb,if_pos (k.disjoint p q h e j),zero_mul]
    · rw [g.eq_zero_of_not_pos q j,mul_zero]
  · rw [g.eq_zero_of_not_pos p e,mul_zero,zero_mul]
 rw [yO,ws w d,u0,<- sum_sub_distrib];apply sum_eq_zero
 intro p _;by_cases e:0 < w p
 · rcases k.normalized p e with ⟨l,i⟩ | ⟨l,i⟩ <;> rw [l,i] <;> norm_num
 · rw [g.eq_zero_of_not_pos p e];ring
end E5
end _m
section bF
namespace E5
open Finset Filter
open scoped Topology
structure qN (w:q1->O) (δ:O):Prop where
 nonneg:∀ p,0<=w p
 sum_close: |∑ p,w p-4|<=δ
 vertex_small:∀ p,q3 p =0->w p<=δ
 edge_bound:∀ p,q3 p =1->w p<=1+δ
 incompatible_small:∀ p q,(q0 p ∩ q0 q).card=1->w p*w q<=δ
 energy_small:qd w<=δ
lemma qN.mono {w:q1->O} {δ ε :O} (h:qN w δ)(d:δ<=ε):qN w ε:=by
 refine ⟨h.nonneg,h.sum_close.trans d,?_,?_,?_,h.energy_small.trans d⟩
 · intro p g;exact (h.vertex_small p g).trans d
 · intro p g;exact (h.edge_bound p g).trans (add_le_add le_rfl d)
 · intro p q e;exact (h.incompatible_small p q e).trans d
lemma qN.le_five {w:q1->O} {δ:O} (h:qN w δ)(e:δ<=1) (p:q1):w p<=5 :=by
 have d:= (abs_le.mp h.sum_close).2;have g:w p<=∑ q,w q:=single_le_sum (fun q _=> h.nonneg q) (mem_univ p)
 linarith
lemma qN.dP {w:q1->O} (h:qN w 0):q6 w/\qs w :=by
 have g:q6 w :=by
  refine ⟨h.nonneg,?_,?_,?_,?_⟩
  · have j:=abs_le.mp h.sum_close;linarith
  · intro p d;exact le_antisymm (h.vertex_small p d) (h.nonneg p)
  · intro p d;simpa only [add_zero] using h.edge_bound p d
  · intro p q d i e;have hmul:=h.incompatible_small p q e;exact (not_lt_of_ge hmul) (mul_pos d i)
 exact ⟨g,y9 w g (le_antisymm h.energy_small (zS w g))⟩
lemma xH:Continuous qd:=by unfold qd;fun_prop
lemma tj {w:ℕ->q1->O} {δ:ℕ->O} {v:q1->O} (g:∀ n,qN (w n) (δ n)) (d:Tendsto δ atTop (𝓝 0)) (k:Tendsto w atTop (𝓝 v)):q6 v/\qs v :=by
 have e (p:q1):Tendsto (fun n=>w n p) atTop (𝓝 (v p)):=(tendsto_pi_nhds.mp k) p
 have l:Tendsto (fun n=>∑ p,w n p) atTop (𝓝 (∑ p,v p)):=tendsto_finsetSum univ (fun p _=> e p)
 have m:Tendsto (fun n=>qd (w n)) atTop (𝓝 (qd v)):=(xH.tendsto v).comp k
 apply qN.dP;constructor
 · intro p;exact ge_of_tendsto' (e p) (fun n=>(g n).nonneg p)
 · exact le_of_tendsto_of_tendsto' ((l.sub_const 4).abs) d (fun n=>(g n).sum_close)
 · intro p j;exact le_of_tendsto_of_tendsto' (e p) d (fun n=>(g n).vertex_small p j)
 · intro p j
   have h :=le_of_tendsto_of_tendsto' (e p) (tendsto_const_nhds.add d) (fun n=>(g n).edge_bound p j)
   simpa only [add_zero] using h
 · intro p q i;exact le_of_tendsto_of_tendsto' ((e p).mul (e q)) d (fun n=>(g n).incompatible_small p q i)
 · exact le_of_tendsto_of_tendsto' m d (fun n=>(g n).energy_small)
end E5
end bF
section _m
namespace E5
open SimpleGraph Finset
open scoped SimpleGraph Classical
lemma tP (w:q1->O) (n:O):qO (fun p=>w p/n)=qO w /n^2:=by
 unfold qO;simp only [sum_div];apply sum_congr rfl
 intro p _;apply sum_congr rfl
 intro q _;split_ifs <;> simp [div_mul_div_comm,pow_two]
lemma yX (w:q1->O) (n:O)(e:n≠0):qd (fun p=>w p/n)*n^2= (∑ p,w p)^2-qO w -n* (∑ p,(q3 p:O)*w p) :=by
 rw [zv,tP,<- sum_div]
 have d:(∑ p,(q3 p:O)*(w p /n))=(∑ p,(q3 p:O)*w p)/n:=by
  simp only [sum_div,mul_div_assoc]
 rw [d];field_simp
noncomputable def q2.rQ {V:Type*} [Fintype V] [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D)(n:O) (p:q1): O:= (h.qa p).card/n
lemma q2.aH {V:Type*} [Fintype V] [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D)(n:O):(∑ p,h.rQ n p)=Fintype.card V /n:=by unfold rQ;rw [<- sum_div];congr 1;exact_mod_cast h.xF
lemma q2.uC {V:Type*} [Fintype V] [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D)(n:O) (d:n≠0):qd (h.rQ n)*n^2= (Fintype.card V:O)^2- qO (fun p=>((h.qa p).card:O))-n* (∑ p,(q3 p:O)*(h.qa p).card) :=by
 unfold rQ;rw [yX _ n d]
 have e:(∑ p,((h.qa p).card:O))=Fintype.card V :=by
  exact_mod_cast h.xF
 rw [e]
lemma q2.yw {V:Type*} [Fintype V] [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D)(n:ℕ) (y:8<=n) (w:∀ i,¬ CG n ⊑ c.graph i)(δ:O) (s:0<=δ) (k: |(Fintype.card V:O)-4*n|<=δ*n) (g:6*E+Fintype.card V<=δ ^2* (n:O)^2) (m:48*E<=δ* (n:O)^2) (j:6*E+Fintype.card V<=δ * (n:O)^2) (e:(Fintype.card V:O)+(2*D-n)*(∑ p,(q3 p:O)*(h.qa p).card)+6*E<=δ* (n:O)^2):qN (h.rQ n) δ :=by
 have d:(0:O) < n:=by exact_mod_cast (show 0 < n by omega)
 have l:(0:O) < (n:O)^2:=sq_pos_of_pos d;refine ⟨?_,?_,?_,?_,?_,?_⟩
 · intro p;exact div_nonneg (Nat.cast_nonneg _) d.le
 · rw [h.aH]
   have r:(Fintype.card V:O)/n-4= (Fintype.card V -4*n)/n:=by
    field_simp
   rw [r,abs_div,abs_of_pos d];exact (div_le_iff₀ d).mpr k
 · intro p t
   apply (div_le_iff₀ d).mpr;have x:= (h.zQ p t).trans g;have C:(0:O)<=(h.qa p).card:=by positivity
   have z:=mul_nonneg s d.le;nlinarith
 · intro p t;apply (div_le_iff₀ d).mpr;have x:=h.t5 n y w p t;nlinarith
 · intro p q v;dsimp only [rQ];rw [div_mul_div_comm,<- pow_two];apply (div_le_iff₀ l).mpr;exact (h.su p q v).trans j
 · have F:=h.uC n d.ne';have x:= (h.yS n).trans e;nlinarith
lemma vy (δ:O)(k:0 < δ):∃ ε :O,0 < ε/\ε<=δ/\∃ n₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (c:q4 V)(n:ℕ),n₀<=n->Fintype.card V =4*n-3->(∀ i,¬ CG n ⊑ c.graph i)->∀ h:q2 c (ε* (Fintype.card V:O)^2) ((n:O)/2+ε*Fintype.card V),qN (h.rQ n) δ :=by
 let t:O:=min δ (min (δ^2) 1);have N:0 < t:=lt_min k (lt_min (sq_pos_of_pos k) zero_lt_one);have g:t<=δ:=min_le_left _ _;have j:t<=δ^2:= (min_le_right _ _).trans (min_le_left _ _);let ε :O:=t/100000;have q:0 < ε:=div_pos N (by norm_num)
 have l:ε<=δ:=by
  have C:ε<=t:=by dsimp only [ε];nlinarith
  exact C.trans g
 obtain ⟨m,T⟩ :=exists_nat_ge (100000/t);refine ⟨ε,q,l,max 8 m,?_⟩
 intro V _ _ c n Q X H h;have J:8<=n:= (le_max_left _ _).trans Q;have I:m<=n:= (le_max_right _ _).trans Q;have e:(0:O) < n:=by exact_mod_cast (show 0 < n by omega)
 have P:100000<=t*n:=by
  have z:(m:O)<=n:=by exact_mod_cast I
  have L:= (div_le_iff₀ N).mp (T.trans z);nlinarith
 have K:(Fintype.card V:O)=4*n-3:=by
  have L:Fintype.card V +3=4*n:=by omega
  have U:(Fintype.card V:O)+3=4*n:=by exact_mod_cast L
  linarith
 have d:(0:O)<=Fintype.card V :=by positivity
 have R:(Fintype.card V:O)<=4*n:=by linarith
 have s:(Fintype.card V:O)^2<=16* (n:O)^2:=by nlinarith
 have M:100000*ε=t:=by dsimp only [ε];ring
 have D:100000* (n:O)<=t* (n:O)^2:=by
  nlinarith [mul_le_mul_of_nonneg_right P e.le]
 have w:(Fintype.card V:O)+48* (ε* (Fintype.card V:O)^2)<=t* (n:O)^2:=by
  have v:=mul_le_mul_of_nonneg_left s q.le;have r:100000*ε* (n:O)^2=t* (n:O)^2:=by rw [M]
  nlinarith [mul_nonneg N.le (sq_nonneg (n:O))]
 have F:=mul_le_mul_of_nonneg_right g (sq_nonneg (n:O));have y:=mul_le_mul_of_nonneg_right j (sq_nonneg (n:O));have Y:0<=ε* (Fintype.card V:O)^2:=mul_nonneg q.le (sq_nonneg _);apply h.yw n J H δ k.le
 · rw [K]
   have x: |4* (n:O)-3-4*n|=3:=by ring_nf;norm_num
   rw [x];have L:=mul_le_mul_of_nonneg_right g e.le;linarith
 · linarith
 · linarith
 · linarith
 · have W:=h.wR
   have hmul:=mul_le_mul_of_nonneg_left W (mul_nonneg (by positivity:(0:O)<=2*ε) d)
   nlinarith
lemma yq {V:Type*} [Finite V] (G H:SG V)(g:G<=H):Nat.card H.edgeSet=Nat.card G.edgeSet+Nat.card (H ⊓ Gᶜ).edgeSet:=by
 classical
 have h:G ⊔ (H ⊓ Gᶜ)=H:=by
  ext u v;constructor
  · rintro (e | ⟨d,_⟩)
    · exact g e
    · exact d
  · intro d
    by_cases e:G.Adj u v
    · exact Or.inl e
    · exact Or.inr ⟨d,d.ne,e⟩
 have i:Disjoint G (H ⊓ Gᶜ) :=by
  apply SimpleGraph.disjoint_left.mpr
  intro u v e d;exact d.2.2 e
 have d:=yD _ _ i;rwa [h] at d
def q2.qI {V:Type*} [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D):SG V:=qJ h.profile ⊓ h.bipartiteUnionᶜ
lemma q2.zE {V:Type*} [Finite V] [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D):(Nat.card (qJ h.profile).edgeSet:O)=Nat.card h.bipartiteUnion.edgeSet+Nat.card h.qI.edgeSet:=by exact_mod_cast yq _ _ h.vm
lemma q2.tn {V:Type*} [Fintype V] [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D)(n:O) (g:n≠0):2* (Nat.card h.qI.edgeSet:O)<=Fintype.card V+(2*D-n)*(∑ p,(q3 p:O)*(h.qa p).card)+6*E-qd (h.rQ n)*n^2:=by
 have j:=h.uC n g;have d:=sY h.profile;have e:=h.zE;have i:=h.yE;change 2*(Nat.card (qJ h.profile).edgeSet:O)=qO (fun p=>((h.qa p).card:O)) at d
 nlinarith
lemma q2.s2 {V:Type*} [Fintype V] [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D)(p q:q1) (i:Fin 3)(e:q5 p q i) (u v:V)(w:u∈h.qa p) (t:v∈h.qa q)(d:¬ (c.graph i).Adj u v):h.qI.Adj u v:=by
 have m:= (h.r3 p u).mp w;have n:= (h.r3 q v).mp t
 have k:(qJ h.profile).Adj u v:=by
  change Disjoint (q0 (h.profile u)) (q0 (h.profile v));rw [m,n];exact re _ _ i e.1
 refine ⟨k,k.ne,?_⟩
 intro s;obtain ⟨j,r⟩ :=iSup_adj.mp s;have g:=h.ry j u v r;rw [m,n] at g
 have l:j=i:=by
  by_contra l;exact e.2 j l g
 subst j;exact d (h.bipartite_le i r)
end E5
end _m
section cb
namespace E5
open Finset Filter
open scoped Topology
lemma uQ (η:O)(y:0 < η):∃ δ :O,0 < δ/\∀ w:q1->O,qN w δ->∃ v:q1->O,q6 v/\qs v/\(∀ p,|w p -v p| < η)/\|qd w| < η:=by
 classical
 by_contra z
 have s (δ:O) (C:0 < δ):∃ w:q1->O,qN w δ/\¬ ∃ v:q1->O,q6 v/\qs v/\(∀ p,|w p -v p| < η)/\|qd w| < η:=by
  by_contra h;apply z;refine ⟨δ,C,?_⟩
  intro w t;by_contra x;exact h ⟨w,t,x⟩
 let ε :ℕ->O:=fun n=>1/((n:O)+1)
 have j (n:ℕ):0 < ε n :=by dsimp only [ε];positivity
 have q (n:ℕ): ε n<=1 :=by
  dsimp only [ε];apply (div_le_one (by positivity:0 < (n:O)+1)).mpr
  have z:0<=(n:O) :=by positivity
  linarith
 choose w t hfar using fun n=>s (ε n) (j n)
 let K:Set (q1->O) :=Set.Icc (fun _=>0) (fun _=>5)
 have g:IsCompact K :=isCompact_Icc;have F (n:ℕ):w n∈K:=⟨(t n).nonneg,fun p=>(t n).le_five (q n) p⟩
 obtain ⟨v,M,φ,D,x⟩ :=g.tendsto_subseq F;have H:Tendsto ε atTop (𝓝 0) :=tendsto_one_div_add_atTop_nhds_zero_nat;have k:Tendsto (ε ∘ φ) atTop (𝓝 0) :=H.comp D.tendsto_atTop;obtain ⟨d,e⟩ :=tj (fun n=>t (φ n)) k x
 have m (p:q1):∀ᶠ n in atTop,|w (φ n) p -v p| < η:=by
  have L:= (tendsto_pi_nhds.mp x) p;simpa only [Real.dist_eq,Function.comp_apply] using (Metric.tendsto_nhds.mp L) η y
 have r:∀ᶠ n in atTop,∀ p,|w (φ n) p -v p| < η:=Filter.eventually_all.mpr m
 have i:Tendsto (fun n=>qd (w (φ n))) atTop (𝓝 0) :=by
  have J:= (xH.tendsto v).comp x;rwa [e.ct d] at J
 have l:∀ᶠ n in atTop,|qd (w (φ n))| < η:=by
  simpa only [Real.dist_eq,sub_zero] using (Metric.tendsto_nhds.mp i) η y
 obtain ⟨n,z,I⟩:=(r.and l).exists;exact hfar (φ n) ⟨v,d,e,z,I⟩
end E5
end cb
section _m
namespace E5
open SimpleGraph Finset
open scoped SimpleGraph Classical
lemma v5 (η:O)(Z:0 < η):∃ n₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (c:q4 V)(n:ℕ),n₀<=n->Odd n->Fintype.card V =4*n-3->(∀ i,¬ CG n ⊑ c.graph i)->∃ E D:O,∃ h:q2 c E D,∃ v:q1->O,q6 v/\qs v/\(∀ p,|h.rQ n p-v p| < η)/\(Nat.card h.qI.edgeSet:O)<=η* (n:O)^2:=by
 let α :O:=η/1000;have hα:0 < α:=div_pos Z (by norm_num)
 have y:α < η:=by dsimp only [α];linarith
 obtain ⟨e,s,j⟩ :=uQ α hα;let δ :O:=min e α;have Y:0 < δ:=lt_min s hα;obtain ⟨ε,P,z,w,l⟩ :=vy δ Y;have J:ε<=α:=z.trans (min_le_right _ _);obtain ⟨x,q⟩ :=wZ ε P;obtain ⟨m,hm⟩ :=exists_nat_ge (4/α);refine ⟨max 8 (max m (max w x)),?_⟩
 intro V _ _ c n X W hN Q;have h4:8<=n:= (le_max_left _ _).trans X;have C:m<=n:= (le_max_left _ _).trans ((le_max_right _ _).trans X);have F:w<=n:= (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans X));have I:x<=n:= (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans X));have g:(0:O) < n:=by exact_mod_cast (show 0 < n by omega)
 have r:Fintype.card V<=4 *n:=by omega
 have h1:n<=Fintype.card V :=by omega
 obtain ⟨h⟩ :=q c n I W h1 r Q;have hw:= (l c n F hN Q h).mono (min_le_left e α);obtain ⟨v,hv,ht,t,k⟩ :=j _ hw;refine ⟨_,_,h,v,hv,ht,fun p=>(t p).trans y,?_⟩
 have d:(0:O)<=Fintype.card V :=by positivity
 have h2:(Fintype.card V:O)<=4*n:=by exact_mod_cast r
 have M:(Fintype.card V:O)^2<=16* (n:O)^2:=by nlinarith
 have R:4<=α*n:=by
  have h0:(m:O)<=n:=by exact_mod_cast C
  have hh:= (div_le_iff₀ hα).mp (hm.trans h0);nlinarith
 have U:(Fintype.card V:O)<=α* (n:O)^2:=by
  nlinarith [mul_le_mul_of_nonneg_right R g.le]
 have N:ε* (Fintype.card V:O)^2<=16*α* (n:O)^2:=by
  have hh:=mul_le_mul_of_nonneg_left M P.le;have h3:=mul_le_mul_of_nonneg_right J (sq_nonneg (n:O));nlinarith
 have hW:=h.wR;have L:=mul_le_mul_of_nonneg_left hW (mul_nonneg (by positivity:(0:O)<=2*ε) d)
 have he:= (abs_lt.mp k).1;have K:=mul_le_mul_of_nonneg_right (le_of_lt he) (sq_nonneg (n:O));have hb:=h.tn n g.ne';have H:1000*α=η:=by dsimp only [α];ring
 have T:1000*α* (n:O)^2=η* (n:O)^2:=by rw [H]
 nlinarith [mul_nonneg hα.le (sq_nonneg (n:O))]
structure qi {V:Type*} [DecidableEq V] (G:SG V)
 [DecidableRel G.Adj] (X Y:FS V) (d:ℕ):Prop where
 left:∀ x ∈ X,(Y.filter (fun y=>¬ G.Adj x y)).card<=d
 right:∀ y ∈ Y,(X.filter (fun x=>¬ G.Adj y x)).card<=d
lemma qi.mono {V:Type*} [DecidableEq V] {G:SG V} [DecidableRel G.Adj] {X Y X' Y':FS V} {d:ℕ} (h:qi G X Y d)(e:X'⊆X) (g:Y'⊆Y):qi G X' Y' d :=by
 constructor
 · intro x j;exact (card_le_card (filter_subset_filter _ g)).trans (h.left x (e j))
 · intro y i;exact (card_le_card (filter_subset_filter _ e)).trans (h.right y (g i))
lemma qi.symm {V:Type*} [DecidableEq V] {G:SG V} [DecidableRel G.Adj] {X Y:FS V} {d:ℕ} (h:qi G X Y d):qi G Y X d:= ⟨h.right,h.left⟩
lemma r6 {V:Type*} (G:SG V) [DecidableRel G.Adj] (x:V)(Y F:FS V) (d:ℕ)(g:(Y.filter (fun y=>¬ G.Adj x y)).card<=d) (i:F.card+d < Y.card):∃ y ∈ Y,y ∉ F/\G.Adj x y:=by
 classical
 let B :=Y.filter (fun y=>¬ G.Adj x y)
 have m:(F ∪ B).card < Y.card:= (card_union_le F B).trans_lt ((Nat.add_le_add_left g F.card).trans_lt i);obtain ⟨y,l,e⟩ :=exists_mem_notMem_of_card_lt_card m;have k:y ∉ F:=fun h=>e (mem_union_left _ h)
 have j:y ∉ B:=fun h=>e (mem_union_right _ h)
 refine ⟨y,l,k,?_⟩;by_contra h;exact j (mem_filter.mpr ⟨l,h⟩)
lemma x9 {V:Type*} (G:SG V) [DecidableRel G.Adj] (u v:V)(Y:FS V) (d:ℕ)(k:(Y.filter (fun y=>¬ G.Adj u y)).card<=d) (l:(Y.filter (fun y=>¬ G.Adj v y)).card<=d) (i:2*d < Y.card):∃ y ∈ Y,G.Adj u y/\G.Adj v y:=by
 classical
 obtain ⟨y,j,e,g⟩ :=r6 G u Y (Y.filter (fun y=>¬ G.Adj v y)) d k (by omega)
 refine ⟨y,j,g,?_⟩;by_contra h;exact e (mem_filter.mpr ⟨j,h⟩)
lemma q2.tb {V:Type*} [Fintype V] [DecidableEq V] {c:q4 V} {E D:O} (h:q2 c E D)(d:ℕ):∃ Z:FS V,d*Z.card<=2*Nat.card h.qI.edgeSet/\∀ p q:q1,∀ i:Fin 3,q5 p q i->qi (c.graph i) (h.qa p \ Z) (h.qa q \ Z) d :=by
 classical
 obtain ⟨K,_,g,e⟩ :=vk h.qI univ d;let Z:FS V :=univ \ K;have z:Z.card=Fintype.card V -K.card:=by simp [Z,card_sdiff]
 have C:Nat.card (h.qI.induce ((univ:FS V):Set V)).edgeSet= Nat.card h.qI.edgeSet:=by
  have m:h.qI.support⊆((univ:FS V):Set V):=fun _ _=> mem_univ _
  have w:=h.qI.card_edgeFinset_induce_of_support_subset m;simpa only [q7] using w
 have F:d*Z.card<=2*Nat.card h.qI.edgeSet:=by
  simp only [q7,card_univ] at g;rw [C] at g;rwa [z]
 refine ⟨Z,F,?_⟩
 intro p q i k
 have v {x:V} (l:x ∉ Z):x∈K:=by simpa [Z] using l
 constructor
 · intro x l
   have r:=v (mem_sdiff.mp l).2
   have hsub:((h.qa q \ Z).filter (fun y=>¬ (c.graph i).Adj x y))⊆h.qI.neighborFinset x ∩ univ:=by
    intro y n;obtain ⟨n,j⟩ :=mem_filter.mp n;exact mem_inter.mpr ⟨(mem_neighborFinset _ _ _).mpr (h.s2 p q i k x y (mem_sdiff.mp l).1 (mem_sdiff.mp n).1 j),mem_univ _⟩
   exact (card_le_card hsub).trans (e x r)
 · intro y n
   have t:=v (mem_sdiff.mp n).2
   have hsub:((h.qa p \ Z).filter (fun x=>¬ (c.graph i).Adj y x))⊆h.qI.neighborFinset y ∩ univ:=by
    intro x l;obtain ⟨l,s⟩ :=mem_filter.mp l;have j:¬ (c.graph i).Adj x y:=fun j=> s j.symm
    exact mem_inter.mpr ⟨(mem_neighborFinset _ _ _).mpr (h.s2 p q i k x y (mem_sdiff.mp l).1 (mem_sdiff.mp n).1 j).symm,mem_univ _⟩
   exact (card_le_card hsub).trans (e y t)
structure rv {V:Type*} [DecidableEq V]
 (c:q4 V) (n:ℕ) (η:O) where
 weight:q1->O
 admissible:q6 weight
 tiling:qs weight
 sets:q1->FS V
 disjoint:∀ p q,p≠q->Disjoint (sets p) (sets q)
 size_lower:∀ p,(weight p -η)*n<=(sets p).card
 size_upper:∀ p,((sets p).card:O)<=(weight p +η)*n
 defect:ℕ
 defect_le:(defect:O)<=η*n
 dense:∀ p q i,q5 p q i->qi (c.graph i) (sets p) (sets q) defect
lemma zI (η:O)(P:0 < η):∃ n₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (c:q4 V)(n:ℕ),n₀<=n->Odd n->Fintype.card V =4*n-3->(∀ i,¬ CG n ⊑ c.graph i)->Nonempty (rv c n η) :=by
 let τ :O:=min (η/4) (η^2/100);have T:0 < τ:=lt_min (by positivity) (by positivity)
 have t:τ<=η/4:=min_le_left _ _;have y:τ<=η^2/100:=min_le_right _ _;obtain ⟨x,r⟩ :=v5 τ T;obtain ⟨m,hm⟩ :=exists_nat_ge (8/η);refine ⟨max 1 (max m x),?_⟩
 intro V _ _ c n Y N hN R
 classical
 have C:x<=n:= (le_max_right _ _).trans ((le_max_right _ _).trans Y);have U:m<=n:= (le_max_left _ _).trans ((le_max_right _ _).trans Y);have e:(0:O) < n:=by exact_mod_cast (show 0 < n by omega)
 have h2:8<=η*n:=by
  have M:(m:O)<=n:=by exact_mod_cast U
  have hh:= (div_le_iff₀ P).mp (hm.trans M);nlinarith
 obtain ⟨E,D,h,v,hv,ht,k,H⟩ :=r c n C N hN R;let d:ℕ:= ⌊η*n/4⌋₊;have h1:(d:O)<=η*n/4:=Nat.floor_le (by positivity)
 have h0:η*n/4 < (d:O)+1:=Nat.lt_floor_add_one _;have K:η*n/8<=(d:O) :=by linarith
 obtain ⟨Z,s,w⟩ :=h.tb d
 have I:(d:O)*Z.card<=2* (Nat.card h.qI.edgeSet:O) :=by
  exact_mod_cast s
 have l:(0:O)<=Z.card:=by positivity
 have hZ:(Z.card:O)<=η*n/2:=by
  have J:=mul_le_mul_of_nonneg_right K l;have z:=mul_le_mul_of_nonneg_right y (sq_nonneg (n:O));have X:0 < η*n:=mul_pos P e;nlinarith
 let A:q1->FS V :=fun p=>h.qa p \ Z
 refine ⟨{
  weight:=v
  admissible:=hv
  tiling:=ht
  sets:=A
  disjoint:=fun p q Q=> (h.tK p q Q).mono sdiff_subset sdiff_subset
  size_lower:= ?_
  size_upper:= ?_
  defect:=d
  defect_le:=by linarith
  dense:=w}⟩
 · intro p
   have W:= (abs_lt.mp (k p)).1
   have j:v p-τ < ((h.qa p).card:O)/n:=by
    change-τ < ((h.qa p).card:O)/n-v p at W;linarith
   have L:= (lt_div_iff₀ e).mp j;have hc:=card_sdiff_add_card_inter (h.qa p) Z;have hi:=card_le_card (inter_subset_right:h.qa p ∩ Z⊆Z)
   have F:((h.qa p).card:O)<=(A p).card+ (Z.card:O) :=by
    exact_mod_cast (show (h.qa p).card<=(A p).card+Z.card by dsimp only [A];omega)
   have g:=mul_le_mul_of_nonneg_right t e.le;nlinarith
 · intro p
   have W:= (abs_lt.mp (k p)).2
   have j:((h.qa p).card:O)/n < v p +τ:=by
    change ((h.qa p).card:O)/n-v p < τ at W;linarith
   have L:= (div_lt_iff₀ e).mp j
   have F:((A p).card:O)<=(h.qa p).card:=by
    exact_mod_cast card_le_card (sdiff_subset:A p⊆h.qa p)
   have g:=mul_le_mul_of_nonneg_right t e.le;nlinarith
lemma wJ:∀ (i:Fin 3)(b:Bool) (q:q1),Disjoint (q0 (cF i b)) (q0 q)->q5 (cF i b) q i:=by decide
lemma qs.af {w:q1->O} (l:qs w)(m:q6 w) (i:Fin 3)(b:Bool) (n:0 < w (cF i b)):∃ q:q1,q≠cF i b/\0 < w q/\q5 (cF i b) q i:=by
 classical
 have d:w (cF i b)=2:=by
  rcases l.normalized _ n with ⟨t,_⟩ | ⟨_,s⟩
  · rw [r4] at t;omega
  · exact s
 have j:∃ q:q1,q≠cF i b/\0 < w q :=by
  by_contra hn;have r (q:q1) (g:q≠cF i b):w q =0:= m.eq_zero_of_not_pos q (fun e=> hn ⟨q,g,e⟩)
  have k:(∑ q,w q)=w (cF i b) :=by
   apply sum_eq_single (cF i b)
   · intro q _ g;exact r q g
   · simp
  rw [m.sum_four,d] at k;norm_num at k
 obtain ⟨q,h,g⟩ :=j;exact ⟨q,h,g,wJ i b q (l.disjoint _ _ h.symm n g)⟩
lemma s8 {V:Type*} [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (L d:ℕ)(hL:0 < L) (X Y:FS V)(g:Disjoint X Y) (e:qi G X Y d)(hX:L+2*d+1<=X.card) (Z:L+2*d<=Y.card) (u v:V)(i:u∈X) (T:v∈X)(s:u≠v):∃ p:G.Walk u v,p.IsPath/\p.length=2*L/\∀ z ∈ p.support,z∈X ∪ Y:=by
 induction L generalizing X Y u v with
 | zero=> omega
 | succ L ih=>
  classical
  by_cases K:L=0
  · subst L
    obtain ⟨y,j,k,n⟩ :=x9 G u v Y d (e.left u i) (e.left v T) (by omega)
    let p:G.Walk u v:=Walk.cons k (Walk.cons n.symm Walk.nil);have C:u ∉ Y:=D1 g i;refine ⟨p,?_,rfl,?_⟩
    · apply (Walk.cons_isPath_iff _ _).mpr;refine ⟨Walk.IsPath.of_adj n.symm,?_⟩;simp only [Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false,not_or];exact ⟨fun h=>C (h ▸ j),s⟩
    · intro z r
      simp only [p,Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at r;rcases r with h | h | h
      · exact h ▸ mem_union_left Y i
      · exact h ▸ mem_union_right X j
      · exact h ▸ mem_union_left Y T
  · obtain ⟨y,j,_,k⟩ :=r6 G u Y ∅ d (e.left u i) (by simp only [card_empty];omega)
    have I:({u,v}:FS V).card<=2:=by
     have h :=card_insert_le u ({v}:FS V);simp only [card_singleton] at h;omega
    obtain ⟨x,W,t,M⟩ :=r6 G y X {u,v} d (e.right y j) (by omega)
    have F:x≠u:=fun h=>t (by simp [h])
    have N:x≠v:=fun h=>t (by simp [h])
    have D:x∈X.erase u :=mem_erase.mpr ⟨F,W⟩;have P:v∈X.erase u :=mem_erase.mpr ⟨s.symm,T⟩;have Q:L+2*d+1<=(X.erase u).card:=by rw [card_erase_of_mem i];omega
    have w:L+2*d<=(Y.erase y).card:=by rw [card_erase_of_mem j];omega
    obtain ⟨q,U,J,l⟩ :=ih (by omega) (X.erase u) (Y.erase y) (g.mono (erase_subset _ _) (erase_subset _ _)) (e.mono (erase_subset _ _) (erase_subset _ _)) Q w x v D P N
    have R:u ∉ q.support:=by
     intro h;rcases mem_union.mp (l u h) with h | h
     · exact (mem_erase.mp h).1 rfl
     · exact (D1 g i) (mem_of_mem_erase h)
    have H:y ∉ q.support:=by
     intro h;rcases mem_union.mp (l y h) with h | h
     · exact (D1 g (mem_of_mem_erase h)) j
     · exact (mem_erase.mp h).1 rfl
    have m:u≠y:=fun h=>(D1 g i) (h ▸ j)
    let p:G.Walk u v:=Walk.cons k (Walk.cons M q);refine ⟨p,?_,?_,?_⟩
    · apply (Walk.cons_isPath_iff _ _).mpr;refine ⟨(Walk.cons_isPath_iff _ _).mpr ⟨U,H⟩,?_⟩;simpa only [Walk.support_cons,List.mem_cons,not_or] using ⟨m,R⟩
    · simp only [p,Walk.length_cons,J];omega
    · intro z r
      simp only [p,Walk.support_cons,List.mem_cons] at r;rcases r with h | h | h
      · exact h ▸ mem_union_left Y i
      · exact h ▸ mem_union_right X j
      · exact (union_subset_union (erase_subset _ _) (erase_subset _ _)) (l z h)
lemma rt {V:Type*} [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (L d:ℕ)(H:2<=L) (X Y:FS V)(e:Disjoint X Y) (g:qi G X Y d)(F:L+2*d<=X.card) (D:L+2*d<=Y.card) (u v:V)(C:u∈X) (k:v∈Y):∃ p:G.Walk u v,p.IsPath/\p.length=2*L-1/\∀ z ∈ p.support,z∈X ∪ Y:=by
 classical
 obtain ⟨x,y,r,i⟩ :=r6 G v X {u} d (g.right v k) (by simp only [card_singleton];omega)
 have n:u≠x:=by
  intro h;exact r (by simp [h])
 have m:L-1+2*d<=(Y.erase v).card:=by rw [card_erase_of_mem k];omega
 obtain ⟨q,w,s,j⟩ :=s8 G (L-1) d (by omega) X (Y.erase v) (e.mono_right (erase_subset _ _)) (g.mono Subset.rfl (erase_subset _ _)) (by omega) m u x C y n
 have l:v ∉ q.support:=by
  intro h;rcases mem_union.mp (j v h) with h | h
  · exact (D1 e h) k
  · exact (mem_erase.mp h).1 rfl
 refine ⟨q.concat i.symm,w.concat l i.symm,?_,?_⟩
 · rw [Walk.length_concat,s];omega
 · intro z t
   rw [Walk.support_concat,List.mem_append,List.mem_singleton] at t;rcases t with h | h
   · exact (union_subset_union Subset.rfl (erase_subset _ _)) (j z h)
   · exact h ▸ mem_union_right X k
lemma yV {m:ℕ} {i j:Fin m} (d:i.val < j.val):(CG m).Adj i j↔i.val+1=j.val\/(i.val=0/\j.val+1=m) :=by rw [cycleGraph_adj',Fin.coe_sub_iff_lt.mpr d,Fin.sub_val_of_le d.le];have g:=i.isLt;have e:=j.isLt;omega
lemma qX {V:Type*} (G:SG V)(m:ℕ) (x:3<=m) (f:ℕ->V) (r:Set.InjOn f (Set.Iio m)) (n:∀ i,i+1 < m->G.Adj (f i) (f (i+1))) (g:G.Adj (f (m-1)) (f 0)):∃ (v:V)(c:G.Walk v v),c.IsCycle/\c.length=m:=by
 have w:Function.Injective (fun i:Fin m=>f i.val) :=by
  intro i j d;exact Fin.ext (r i.isLt j.isLt d)
 have q:∀ i j:Fin m,(CG m).Adj i j->G.Adj (f i.val) (f j.val) :=by
  intro i j d;have t:i.val≠j.val:=fun h=>d.ne (Fin.ext h)
  wlog hlt:i.val < j.val generalizing i j
  · exact (this j i d.symm t.symm (by omega)).symm
  rcases (yV hlt).mp d with l | ⟨k,s⟩
  · simpa only [l] using n i.val (by omega)
  · have e:j.val=m-1:=by omega
    simpa only [k,e] using g.symm
 apply (cycleGraph_isContained_iff (by omega:2 < m)).mp
 exact ⟨{ toHom:= { toFun:=fun i=>f i.val,map_rel':=fun h=>q _ _ h },injective':=w}⟩
lemma r2 {V:Type*} {G:SG V} {u v:V} (p:G.Walk u v)(e:p.IsPath) (d:2<=p.length) (h:G.Adj u v):∃ c:G.Walk u u,c.IsCycle/\c.length=p.length+1:=by
 let q:G.Walk u v:=Walk.cons h Walk.nil;have g:q.IsPath:=by simp [q,h.ne]
 refine ⟨p.append q.reverse,?_,?_⟩
 · apply qy p q e g (by omega)
   intro x _ i;simpa only [q,Walk.support_cons,Walk.support_nil,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using i
 · simp [q]
def qq (j k:ℕ):ℕ:=if k =0 then 0 else if k < j then j +1-k else k +1
lemma zB (m j k:ℕ)(g:2<=j) (d:j+1 < m) (e:k < m-1):qq j k < m:=by unfold qq;split_ifs <;> omega
lemma y0 (j:ℕ)(d:2<=j):Function.Injective (qq j) :=by intro a b h;unfold qq at h;split_ifs at h <;> omega
lemma ro {V:Type*} [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (X Y:FS V)(r d:ℕ) (t:1<=r) (g:Disjoint X Y)(h:qi G X Y d) (n:r+2*d+1<=X.card) (m:r+2*d<=Y.card) (j:¬ CG (2*r+1) ⊑ G):∀ u ∈ X,∀ v ∈ X,¬ G.Adj u v:=by
 intro u s v l e;obtain ⟨p,q,k,_⟩ :=s8 G r d t X Y g h n m u v s l e.ne;obtain ⟨c,w,i⟩ :=r2 p q (by omega) e
 exact j ((cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr ⟨u,c,w,by omega⟩)
lemma rG {V:Type*} [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (X Y:FS V)(r d:ℕ) (z:2<=r) (m:Disjoint X Y)(k:qi G X Y d) (D:r+2*d<=X.card) (C:r+2*d<=Y.card) (w:¬ CG (2*r+1) ⊑ G) (x:V)(q:x ∉ X) (t:x ∉ Y)(u v:V) (y:u∈X)(H:v∈Y):¬ (G.Adj x u/\G.Adj x v) :=by
 rintro ⟨n,l⟩;obtain ⟨p,I,g,j⟩ :=rt G r d z X Y m k D C u v y H
 have s:x ∉ p.support:=by
  intro h;rcases mem_union.mp (j x h) with h | h
  · exact q h
  · exact t h
 obtain ⟨c,F,i⟩ :=r2 (p.concat l.symm) (I.concat s l.symm) (by rw [Walk.length_concat,g];omega) n.symm
 have e:c.length=2*r+1:=by
  rw [Walk.length_concat,g] at i;omega
 exact w ((cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr ⟨u,c,F,e⟩)
lemma rv.zz {V:Type*} [DecidableEq V] {c:q4 V} {r:ℕ} {η:O} (h:rv c (2*r+1) η) (l:1<=r) (g:η<=1/100) (p:q1)(m:0 < h.weight p):r+2*h.defect+1<=(h.sets p).card:=by
 have n:1<=h.weight p :=by
  rcases h.tiling.normalized p m with ⟨_,k⟩ | ⟨_,k⟩ <;> norm_num [k]
 have e:=h.size_lower p;have s:=h.defect_le;have q:(1:O)<=r:=by exact_mod_cast l
 have i:(0:O)<=2*r+1:=by positivity
 have t:=mul_le_mul_of_nonneg_right n i;have j:=mul_le_mul_of_nonneg_right g i
 have d:(r:O)+2*h.defect+1<=(h.sets p).card:=by
  push_cast at e s;nlinarith
 exact_mod_cast d
lemma rv.t8 {V:Type*} [DecidableEq V] {c:q4 V} {r:ℕ} {η:O} (h:rv c (2*r+1) η) (j:1<=r) (e:η<=1/100) (k:∀ i,¬ CG (2*r+1) ⊑ c.graph i) (i:Fin 3)(b:Bool) (l:0 < h.weight (cF i b)):∀ u ∈ h.sets (cF i b),∀ v ∈ h.sets (cF i b),¬ (c.graph i).Adj u v:=by obtain ⟨q,g,m,d⟩ :=h.tiling.af h.admissible i b l;apply ro (c.graph i) (h.sets (cF i b)) (h.sets q) r h.defect j (h.disjoint _ _ g.symm) (h.dense _ _ i d) (h.zz j e _ l) _ (k i);have n:=h.zz j e q m;omega
lemma tm:∀ p:q1,q3 p =1->∃ a:Fin 3,∀ l:Fin 4,qc l∈q0 p->qu l a=p:=by decide
lemma xu:∀ (p:q1)(l m:Fin 4),q3 p =1->qc l∈q0 p->qc m∈q0 p->l =m:=by decide
lemma zw:∀ (i a:Fin 3)(b:Bool) (l:Fin 4),a≠i->qc l∈q0 (cF i b)->q0 (qu l a)⊆q0 (cF i b) :=by decide
lemma yv:∀ (i k:Fin 3)(b:Bool) (l m:Fin 4),k≠i->l≠m->qc l∈q0 (cF i b)->qc m∈q0 (cF i b)->qc l k≠qc m k:=by decide
lemma xv:∀ (i a:Fin 3)(b:Bool) (l m:Fin 4),a≠i->l≠m->qc l∈q0 (cF i b)->qc m∈q0 (cF i b)->Disjoint (q0 (qu l a)) (q0 (qu m a)) :=by decide
lemma xM:∀ (i a k z:Fin 3)(b:Bool) (l m:Fin 4),a≠i->k≠i->a≠k->qc l∈q0 (cF i b)->qc m∈q0 (cF i b)->q5 (qu l a) (qu m a) z->z =k:=by decide
lemma z7:∀ p q:q1,Disjoint (q0 p) (q0 q)->∃ i,qV p q i :=by decide
lemma rz:∀ p p':q1,∀ (i:Fin 3)(b:Bool),q0 p'⊆q0 p->p i=some b->p' i =some b :=by decide
lemma um (p q p' q':q1)(i:Fin 3) (l:q0 p'⊆q0 p)(k:q0 q'⊆q0 q) (d:qV p q i):qV p' q' i :=by
 rcases d with ⟨h,e⟩ | ⟨j,g⟩
 · exact Or.inl ⟨rz p p' i false l h,rz q q' i true k e⟩
 · exact Or.inr ⟨rz p p' i true l j,rz q q' i false k g⟩
lemma wp (p q p' q':q1)(i:Fin 3) (g:Disjoint (q0 p) (q0 q)) (l:q0 p'⊆q0 p)(k:q0 q'⊆q0 q) (e:q5 p' q' i):q5 p q i :=by
 obtain ⟨j,h⟩ :=z7 p q g
 have d:j=i:=by
  by_contra d;exact e.2 j d (um p q p' q' j l k h)
 subst j;refine ⟨h,?_⟩
 intro j d h;exact e.2 j d (um p q p' q' j l k h)
lemma rY {V:Type*} [DecidableEq V] (G:SG V)(L:ℕ) (R:0 < L) (X Y:FS V)(k:Disjoint X Y) (d:∀ x ∈ X,∀ y ∈ Y,G.Adj x y)(Q:L<=X.card) (P:L<=Y.card) (u v:V)(l:u∈X) (g:v∈Y):∃ p:G.Walk u v,p.IsPath/\p.length=2*L-1/\∀ z ∈ p.support,z∈X ∪ Y:=by
 classical
 by_cases N:L=1
 · subst L
   let p:=(d u l v g).toWalk;refine ⟨p,Walk.IsPath.of_adj _,rfl,?_⟩
   intro z m;have C:z=u\/z=v:=by simpa [p,SimpleGraph.Adj.toWalk] using m
   exact C.elim (fun h=>h ▸ mem_union_left _ l) (fun h=>h ▸ mem_union_right _ g)
 · have H:(X.erase u).Nonempty:=by
    apply card_pos.mp;rw [card_erase_of_mem l];omega
   obtain ⟨x,I⟩ :=H;have j:=mem_of_mem_erase I;have s:u≠x:= (mem_erase.mp I).1.symm;have r:L-1<=(Y.erase v).card:=by rw [card_erase_of_mem g];omega
   obtain ⟨q,J,w,i⟩ :=rf G (L-1) (by omega) X (Y.erase v) (k.mono_right (erase_subset _ _)) (fun a M b K=> d a M b (mem_of_mem_erase K)) (by omega) r u x l j s
   have e:v ∉ q.support:=by
    intro e;rcases mem_union.mp (i v e) with D | t
    · exact D1 k D g
    · exact (mem_erase.mp t).1 rfl
   refine ⟨q.concat (d x j v g),J.concat e _,?_,?_⟩
   · rw [Walk.length_concat,w];omega
   · intro z m
     rw [Walk.support_concat,List.mem_append,List.mem_singleton] at m;rcases m with F | n
     · exact (union_subset_union (Subset.refl X) (erase_subset _ _)) (i z F)
     · exact n ▸ mem_union_right X g
lemma vw {V:Type*} [DecidableEq V] (G:SG V)(L:ℕ) (H:2<=L) (X Y:FS V)(j:Disjoint X Y) (d:∀ x ∈ X,∀ y ∈ Y,G.Adj x y)(C:L<=X.card) (w:L<=Y.card):∃ (u:V)(c:G.Walk u u),c.IsCycle/\c.length=2*L/\∀ z ∈ c.support,z∈X ∪ Y:=by
 classical
 obtain ⟨u,s⟩ :=card_pos.mp (show 0 < X.card by omega)
 obtain ⟨v,i⟩ :=card_pos.mp (show 0 < Y.card by omega)
 obtain ⟨p,D,m,r⟩ :=rY G L (by omega) X Y j d C w u v s i
 let q:=(d u s v i).toWalk;have F:q.IsPath:=Walk.IsPath.of_adj _
 have h (z:V) (e:z∈q.support):z=u\/z=v:=by
  simpa [q,SimpleGraph.Adj.toWalk] using e
 refine ⟨u,p.append q.reverse,qy p q D F (by omega) (fun z _ e=> h z e),?_,?_⟩
 · simp only [Walk.length_append,Walk.length_reverse,q,SimpleGraph.Adj.toWalk,Walk.length_cons,Walk.length_nil,m];omega
 · intro z e
   rcases (Walk.mem_support_append_iff p q.reverse).mp e with l | t
   · exact r z l
   · have g:z∈q.support:=by simpa only [Walk.support_reverse,List.mem_reverse] using t
     rcases h z g with n | k
     · exact n ▸ mem_union_left _ s
     · exact k ▸ mem_union_right _ i
lemma sP {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (L b:ℕ)(F:2<=L) (e:∀ v,L+b<=G.degree v) (z:¬ CG (2*L) ⊑ Gᶜ):q8 G b:=by
 classical
 intro S M;by_contra r;obtain ⟨A,B,J,D,w,_,_,i,d⟩:=rk G S r;obtain ⟨a,K⟩ :=J;obtain ⟨n,q⟩ :=D
 have l:L<=A.card:=by
  have H:=qR G A B S i d a K;have t:=e a;omega
 have m:L<=B.card:=by
  have k:B ∪ A ∪ S=univ:=by rw [union_comm B A];exact i
  have j:∀ u ∈ B,∀ v ∈ A,¬ G.Adj u v:= fun u x v y C=> d v y u x C.symm
  have H:=qR G B A S k j n q;have t:=e n;omega
 have g (u:V) (x:u∈A) (v:V) (y:v∈B):Gᶜ.Adj u v:=by
  rw [compl_adj];refine ⟨?_,d u x v y⟩
  intro h;exact D1 w x (h ▸ y)
 obtain ⟨u,c,I,s,_⟩ :=vw Gᶜ L F A B w g l m;exact z ((cycleGraph_isContained_iff (by omega)).mpr ⟨u,c,I,s⟩)
lemma vc {V:Type*} {G:SG V} {u v:V} (p:G.Walk u v)(s:p.IsPath) (j:1 < p.length) (K:ℕ)(R:FS V) (g:∀ x ∈ p.support,x ∉ R)(d:qY G K u v R):∃ c:G.Walk u u,c.IsCycle/\p.length+1<=c.length:=by
 obtain ⟨q,t,_,m⟩ :=d
 have k:u≠v:=by
  intro h;have y:= (s.nil_iff_eq.mpr h).length_eq_zero;omega
 have r:0 < q.length:=Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne k)
 have w:(p.append q.reverse).IsCycle:=by
  apply qy p q s t j
  intro x l n;by_cases i:x=u
  · exact Or.inl i
  by_cases e:x=v
  · exact Or.inr e
  exact (g x l (m x n i e)).elim
 refine ⟨p.append q.reverse,w,?_⟩;simp only [Walk.length_append,Walk.length_reverse];omega
lemma xQ {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (L b K:ℕ)(C:2<=L) (R:FS V)(D:R.card<=b) (j:q8 G b)(d:∀ v,L+R.card<=G.degree v) (M:2*L+R.card<=Fintype.card V) (k:∀ u v,qY G K u v R):∃ (u:V)(c:G.Walk u u),c.IsCycle/\2*L<=c.length:=by
 classical
 let U:=(R:Set V)ᶜ
 have t:Fintype.card (R:Set V)=R.card:=by
  calc
   Fintype.card (R:Set V)=(R:Set V).ncard:=Nat.card_eq_fintype_card.symm
   _=R.card:=Set.ncard_coe_finset R
 have H:Fintype.card U =Fintype.card V -R.card:=by
  simp only [U,Fintype.card_compl_set,t]
 have l:2*L<=Fintype.card U :=by omega
 let:Nonempty U :=Fintype.card_pos_iff.mp (by omega)
 have F:(G.induce U).Connected:= ⟨j R D⟩
 have m (v:U):L<=(G.induce U).degree v :=by
  have h :=qW G R v;have J:=d v.val;change G.degree v.val<=(G.induce U).degree v +R.card at h;omega
 obtain ⟨u,v,p,I,w⟩ :=ur (G.induce U) F L C m;let f:G.induce U ↪g G :=SimpleGraph.Embedding.induce U;have s:(p.map f.toHom).IsPath:=I.map f.injective;have i:1 < (p.map f.toHom).length:=by rw [Walk.length_map];omega
 have q (x:V) (z:x∈(p.map f.toHom).support):x ∉ R:=by
  rw [Walk.support_map,List.mem_map] at z;obtain ⟨y,_,r⟩ :=z;exact r ▸ y.property
 obtain ⟨c,n,e⟩ :=vc (p.map f.toHom) s i K R q (k (f u) (f v));refine ⟨f u,c,n,?_⟩;rw [Walk.length_map] at e;omega
lemma uI (D B:ℕ)(Q:0 < D) (F:0 < B):∃ j:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (L b:ℕ),j<=Fintype.card V->2<=L->Fintype.card V<=D *L->Fintype.card V<=B *b->(∀ v,L+b<=G.degree v)->¬ CG (2*L) ⊑ Gᶜ->(∀ (z:V)(c:G.Walk z z),c.IsCycle->c.length < 2*L)->Fintype.card V < 2 *L+b:=by
 have H:(0:O) < B:=by exact_mod_cast F
 let q:O:=1/ (2*B);have P:0 < q:=by dsimp [q];positivity
 have C:q<=1:=by
  dsimp [q];apply (div_le_iff₀ (by positivity:(0:O) < 2*B)).mpr
  have K:(1:O)<=B:=by exact_mod_cast F
  linarith
 obtain ⟨j,n⟩ :=sh D B 0 Q F q P C;refine ⟨j,?_⟩
 intro V _ _ G _ L b T M k e d t i
 classical
 have N:=sP G L b M d t;obtain ⟨R,g,w⟩ :=n G b L T N d k e
 have U:R.card<=b:=by
  have I:(Fintype.card V:O)<=(B:O)*b:=by exact_mod_cast e
  have m:(Fintype.card V:O)/B<=b:= (div_le_iff₀ H).mpr (by nlinarith only [I])
  have J:2*q*Fintype.card V=(Fintype.card V:O)/B:=by
   dsimp [q];field_simp
  rw [J] at g;exact_mod_cast g.trans m
 have s (u v:V):qY G (3*D) u v R :=by
  have h :=w u v ∅ (by simp)
  simpa only [sdiff_empty] using h
 by_contra y
 have r (v:V):L+R.card<=G.degree v :=by
  have h :=d v;omega
 obtain ⟨z,c,x,l⟩ :=xQ G L b (3*D) M R U N r (by omega) s
 exact (i z c x).not_ge l
lemma wU {V:Type*} [Fintype V] (G:SG V) [DecidableRel G.Adj] (d:O)(a:ℕ) (C:a<=Fintype.card V):∃ S:FS V,a<=S.card/\(G.edgeFinset.card:O)-d*Fintype.card V<=((G.induce (S:Set V)).edgeFinset.card:O)-d*S.card/\(S.card=a\/∀ v:S,d < (G.induce (S:Set V)).degree v) :=by
 classical
 let g (S:FS V): O:= ((G.induce (S:Set V)).edgeFinset.card:O)-d*S.card;let e:O:= (G.edgeFinset.card:O)-d*Fintype.card V;let h:FS (FS V) :=univ.filter fun S=>a<=S.card/\e<=g S
 have m:(univ:FS V)∈h:=by
  have x:(G.induce (↑(univ:FS V):Set V)).edgeFinset.card=G.edgeFinset.card:=by
   rw [<- G.card_filter_edgeFinset_toFinset_subset univ];simp
  simp [h,g,e,x,C]
 obtain ⟨S,y,i⟩ :=h.exists_min_image card ⟨_,m⟩;obtain ⟨w,k⟩:=(mem_filter.mp y).2;refine ⟨S,w,k,?_⟩;by_cases l:S.card=a
 · exact Or.inl l
 right
 intro v;by_contra j;have r:((G.induce (S:Set V)).degree v:O)<=d:=le_of_not_gt j;let T :=S.erase v.val;have q:T.card+1=S.card:=card_erase_add_one v.property;have n:=rN G S v
 have t:((G.induce (T:Set V)).edgeFinset.card:O)+(G.induce (S:Set V)).degree v=(G.induce (S:Set V)).edgeFinset.card:=by
  exact_mod_cast n
 have s:(T.card:O)+1=S.card:=by exact_mod_cast q
 have z:T∈h:=by
  apply mem_filter.mpr;refine ⟨mem_univ _,by omega,?_⟩
  dsimp [g] at k ⊢;nlinarith
 have D:=i T z;omega
def qK {V:Type*} (G:SG V)(m:ℕ):Prop:= ∀ (v:V) (c:G.Walk v v),c.IsCycle->c.length < m
lemma qK.of_embedding {V W:Type*} {G:SG V} {H:SG W} {m:ℕ} (d:qK H m)(f:G ↪g H):qK G m:=by intro v c e;have h :=d (f v) (c.map f.toHom) (e.map f.injective);simpa only [Walk.length_map] using h
lemma qK.induce {V:Type*} {G:SG V} {m:ℕ} (d:qK G m)(S:Set V):qK (G.induce S) m:=d.of_embedding (SimpleGraph.Embedding.induce S)
def yy {V:Type*} (G:SG V) (S:Set V):(G.induce S)ᶜ ↪g Gᶜ where
 toFun:=Subtype.val
 inj':=Subtype.val_injective
 map_rel_iff':=by
  intro x y;change Gᶜ.Adj x.val y.val↔(G.induce S)ᶜ.Adj x y;simp only [compl_adj,induce_adj,ne_eq,Subtype.coe_inj]
lemma qK.yB {V:Type*} {G:SG V} {m:ℕ} (d:qK Gᶜ m)(S:Set V):qK (G.induce S)ᶜ m:=d.of_embedding (yy G S)
lemma qK.eb {V:Type*} {G:SG V} {m:ℕ} (g:qK G m)(n:ℕ) (k:3<=n) (i:m<=n):¬ CG n ⊑ G :=by
 intro h;obtain ⟨v,c,j,e⟩:=(cycleGraph_isContained_iff (by omega)).mp h
 have d:=g v c j;omega
lemma vS (D B:ℕ)(I:0 < D) (C:0 < B):∃ g:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (L b:ℕ),g<=L->2<=L->L+b+1<=Fintype.card V->Fintype.card V<=D *L->Fintype.card V<=B *b->qK G (2*L)->qK Gᶜ (2*L)->∃ S:FS V,L+b+1<=S.card/\S.card<=2*L+b/\(G.edgeFinset.card:O)-(L+b:ℕ)*Fintype.card V<=((G.induce (S:Set V)).edgeFinset.card:O)-(L+b:ℕ)*S.card:=by
 obtain ⟨g,m⟩ :=uI D B I C;refine ⟨g,?_⟩
 intro V _ _ G _ L b q J j t s H x
 classical
 obtain ⟨S,i,d,l⟩ :=wU G ((L+b:ℕ): O) (L+b+1) j;refine ⟨S,i,?_,d⟩;rcases l with y | r
 · omega
 · have F:Fintype.card (S:Set V)=S.card:=by
    calc
     Fintype.card (S:Set V)=(S:Set V).ncard:=Nat.card_eq_fintype_card.symm
     _=S.card:=Set.ncard_coe_finset S
   have z:=card_le_univ S
   have e (v:(S:Set V)):L+b<=(G.induce (S:Set V)).degree v :=by
    have h:L+b < (G.induce (S:Set V)).degree v :=by exact_mod_cast r v
    exact h.le
   have k:=H.induce (S:Set V);have n:= (x.yB (S:Set V)).eb (2*L) (by omega) le_rfl
   have w:=m (G.induce (S:Set V)) L b (by omega) J (by omega) (by omega) e n k
   omega
lemma xn (L b s:O)(g:0<=L) (d:L+b+1<=s) (e:s<=2*L+b):L* (2*L+b-s)<=((2*L+b)^2- (2* (L+b)+1)*(2*L+b))-(s^2- (2* (L+b)+1)*s) :=by have h :=mul_nonneg (sub_nonneg.mpr e) (sub_nonneg.mpr d);nlinarith
lemma yN (L b N:O)(l:0<=L) (j:1<=b) (i:4*L-b<=N) (d:N<=4*L):4* (L+b)*N+ 2* ((2*L+b)^2- (2* (L+b)+1)*(2*L+b))-N^2+N<=24*b*L:=by
 have e:0<=4* (L+b)-N:=by linarith
 have g:4* (L+b)-N<=5*b:=by linarith
 have hmul:=mul_le_mul d g e (by positivity:(0:O)<=4*L)
 have h:0<=(2*L+b)*(b+1) :=by positivity
 have k:=mul_le_mul_of_nonneg_right j l;nlinarith
lemma vM (L b N s t e f eS eT:O)(n:0 < L) (F:1<=b) (v:4*L-b<=N) (z:N<=4*L) (x:L+b+1<=s) (l:s<=2*L+b) (y:L+b+1<=t) (m:t<=2*L+b) (k:2* (e+f)=N* (N-1)) (C:e- (L+b)*N<=eS- (L+b)*s) (D:f- (L+b)*N<=eT- (L+b)*t) (q:2*eS<=s* (s-1)) (r:2*eT<=t* (t-1)):2*L-24*b<=s/\2*L-24*b<=t/\s* (s-1)-2*eS<=24*b*L/\t* (t-1)-2*eT<=24*b*L:=by
 have H:=xn L b s n.le x l;have K:=xn L b t n.le y m;have w:=yN L b N n.le F v z
 have d:L* (2*L+b-s)+L* (2*L+b-t)+(s* (s-1)-2*eS)+(t* (t-1)-2*eT)<=24*b*L:=by
  nlinarith only [H,K,w,k,C,D]
 have i:0<=L* (2*L+b-s) :=mul_nonneg n.le (sub_nonneg.mpr l);have h:0<=L* (2*L+b-t) :=mul_nonneg n.le (sub_nonneg.mpr m);have j:L* (2*L+b-s)<=L* (24*b) :=by nlinarith only [d,h,q,r]
 have g:L* (2*L+b-t)<=L* (24*b) :=by nlinarith only [d,i,q,r]
 have J:= (mul_le_mul_iff_right₀ n).mp j;have I:= (mul_le_mul_iff_right₀ n).mp g;refine ⟨by linarith,by linarith,?_,?_⟩ <;> nlinarith only [d,i,h,q,r]
lemma vQ (B:ℕ)(X:0 < B):∃ m:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (L b:ℕ),m<=L->2<=L->1<=b->b<=L->4*L<=Fintype.card V +b->Fintype.card V<=4 *L->Fintype.card V<=B *b->qK G (2*L)->qK Gᶜ (2*L)->∃ S T:FS V,2*L<=S.card+24*b/\S.card<=2*L+b/\2*L<=T.card+24*b/\T.card<=2*L+b/\((Gᶜ.induce (S:Set V)).edgeFinset.card:O)<=12* (b:O)*L/\((G.induce (T:Set V)).edgeFinset.card:O)<=12* (b:O)*L:=by
 obtain ⟨m,n⟩ :=vS 4 B (by decide) X
 refine ⟨m,?_⟩
 intro V _ _ G _ L b i W Z Y D q j R z
 classical
 have l:L+b+1<=Fintype.card V :=by omega
 obtain ⟨S,F,v,P⟩ :=n G L b i W l q j R z;obtain ⟨T,H,t,Q⟩ :=n Gᶜ L b i W l q j z (by simpa only [compl_compl] using R)
 have d (U:FS V):Fintype.card (U:Set V)=U.card:=by
  calc
   Fintype.card (U:Set V)=(U:Set V).ncard:=Nat.card_eq_fintype_card.symm
   _=U.card:=Set.ncard_coe_finset U
 have J:=uh (G.induce (S:Set V));have K:=uh (Gᶜ.induce (T:Set V));rw [d S] at J;rw [d T] at K
 have w:4* (L:O)-b<=Fintype.card V :=by
  have h:4* (L:O)<=(Fintype.card V:O)+b:=by exact_mod_cast D
  linarith
 have C:(G.edgeFinset.card:O)-((L:O)+b)*Fintype.card V<=((G.induce (S:Set V)).edgeFinset.card:O)-((L:O)+b)*S.card:=by
  simpa only [Nat.cast_add] using P
 have I:(Gᶜ.edgeFinset.card:O)-((L:O)+b)*Fintype.card V<=((Gᶜ.induce (T:Set V)).edgeFinset.card:O)-((L:O)+b)*T.card:=by
  simpa only [Nat.cast_add] using Q
 obtain ⟨hs,ht,r,s⟩ :=vM (L:O) b (Fintype.card V) S.card T.card G.edgeFinset.card Gᶜ.edgeFinset.card (G.induce (S:Set V)).edgeFinset.card (Gᶜ.induce (T:Set V)).edgeFinset.card (by exact_mod_cast (show 0 < L by omega)) (by exact_mod_cast Z) w (by exact_mod_cast q) (by exact_mod_cast F) (by exact_mod_cast v) (by exact_mod_cast H) (by exact_mod_cast t) (rn G) C I J K
 have M:2*L<=S.card+24*b:=by
  exact_mod_cast (show 2*(L:O)<=(S.card:O)+24*b by linarith only [hs])
 have N:2*L<=T.card+24*b:=by
  exact_mod_cast (show 2*(L:O)<=(T.card:O)+24*b by linarith only [ht])
 have y:(G.induce (S:Set V))ᶜ ≃g Gᶜ.induce (S:Set V) :=by
  rw [z9]
 have x:(Gᶜ.induce (T:Set V))ᶜ ≃g G.induce (T:Set V) :=by
  rw [z9,compl_compl]
 have k:=rn (G.induce (S:Set V));have e:=rn (Gᶜ.induce (T:Set V));rw [y.card_edgeFinset_eq,d S] at k;rw [x.card_edgeFinset_eq,d T] at e;exact ⟨S,T,M,v,N,t,by nlinarith only [k,r],by nlinarith only [e,s]⟩
lemma wQ {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (A S:FS V)(d:ℕ) (g:A⊆S)(e:∀ v ∈ S,S.card<=(G.neighborFinset v ∩ S).card+d):∀ v ∈ A,A.card<=(G.neighborFinset v ∩ A).card+d:=by intro v h;have k:=r1 G S v (g h);have j:=r1 G A v h;have l:=e v (g h);have i:(Gᶜ.neighborFinset v ∩ A).card<=(Gᶜ.neighborFinset v ∩ S).card:= card_le_card (inter_subset_inter_left g);omega
lemma vv {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (A B S T:FS V)(r:ℕ) (j:A⊆S)(g:B⊆T) (m:∀ v ∈ A,(Gᶜ.neighborFinset v ∩ S).card<=r) (l:∀ v ∈ B,(G.neighborFinset v ∩ T).card<=r):(A ∩ B).card<=2*r+1:=by
 classical
 by_cases d:(A ∩ B).Nonempty
 · obtain ⟨v,e⟩ :=d
   have h :=r1 G (A ∩ B) v e
   have k:(G.neighborFinset v ∩ (A ∩ B)).card<=r:=by
    apply (card_le_card (inter_subset_inter_left ((inter_subset_right:A ∩ B⊆B).trans g))).trans;exact l v (mem_inter.mp e).2
   have i:(Gᶜ.neighborFinset v ∩ (A ∩ B)).card<=r:=by
    apply (card_le_card (inter_subset_inter_left ((inter_subset_left:A ∩ B⊆A).trans j))).trans;exact m v (mem_inter.mp e).1
   omega
 · rw [not_nonempty_iff_eq_empty.mp d,card_empty];omega
lemma zL {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (S T:FS V)(r t:ℕ) (y:0 < r) (z:2* (Gᶜ.induce (S:Set V)).edgeFinset.card<=r*t) (C:2* (G.induce (T:Set V)).edgeFinset.card<=r*t):∃ A B:FS V,A⊆S/\B⊆T/\Disjoint A B/\S.card<=A.card+t+2*r+1/\T.card<=B.card+t/\(∀ v ∈ A,A.card<=(G.neighborFinset v ∩ A).card+ (r+1))/\(∀ v ∈ B,B.card<=(Gᶜ.neighborFinset v ∩ B).card+ (r+1)) :=by
 classical
 obtain ⟨A,h,g,x⟩ :=vk Gᶜ S r;obtain ⟨B,e,d,s⟩ :=vk G T r;have k:S.card-A.card<=t:=Nat.le_of_mul_le_mul_left (g.trans z) y;have l:T.card-B.card<=t:=Nat.le_of_mul_le_mul_left (d.trans C) y;have m:=vv G A B S T r h e x s;have j:Disjoint (A \ B) B :=D2 fun _ i=> (mem_sdiff.mp i).2
 refine ⟨A \ B,B,sdiff_subset.trans h,e,j,?_,?_,?_,?_⟩
 · have n:=card_sdiff_add_card_inter A B;omega
 · omega
 · apply sL G (A \ B) S r (sdiff_subset.trans h)
   intro v i;exact x v (mem_sdiff.mp i).1
 · apply sL Gᶜ B T r e
   intro v i;have q:Gᶜᶜ.neighborFinset v =G.neighborFinset v :=by ext w;simp
   rw [q];exact s v i
lemma ss {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (A:FS V)(v:V):(G.neighborFinset v ∩ A).card= ∑ u ∈ A,if G.Adj v u then 1 else 0 :=by rw [sum_boole];congr 1;ext u;simp only [mem_inter,mem_neighborFinset,mem_filter,and_comm]
lemma tI {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (A B:FS V): ∑ v ∈ B,(G.neighborFinset v ∩ A).card= ∑ u ∈ A,(G.neighborFinset u ∩ B).card:=by
 simp_rw [ss];rw [sum_comm];apply sum_congr rfl
 intro u d;apply sum_congr rfl
 intro v e;simp only [G.adj_comm]
lemma zN {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (A B:FS V)(d:Disjoint A B):(∑ v ∈ B,(G.neighborFinset v ∩ A).card)+(∑ u ∈ A,(Gᶜ.neighborFinset u ∩ B).card)=A.card*B.card:=by
 classical
 rw [tI G A B,<- sum_add_distrib]
 have e (u:V) (j:u∈A):(G.neighborFinset u ∩ B).card+ (Gᶜ.neighborFinset u ∩ B).card=B.card:=by
  rw [ss,ss,<- sum_add_distrib]
  calc
   (∑ v ∈ B,((if G.Adj u v then 1 else 0)+if Gᶜ.Adj u v then 1 else 0))=∑ _v ∈ B,1:=by
    apply sum_congr rfl
    intro v i;have g:u≠v:=fun h=>(D1 d j) (h ▸ i)
    by_cases h:G.Adj u v <;> simp [compl_adj,g,h]
   _=B.card:=by simp
 simp_rw [sum_congr rfl e];simp
lemma vG {V:Type*} (B:FS V)(f:V->ℕ) (a k:ℕ)(g:∀ v ∈ B,f v<=a) (d:(B.filter (fun v=>k +1<=f v)).card<=k): ∑ v ∈ B,f v<=k* (a+B.card) :=by
 classical
 let C :=B.filter (fun v=>k +1<=f v)
 have e:C⊆B:=filter_subset _ _
 have q: ∑ v ∈ C,f v<=C.card*a:=by
  calc
   _<=∑ _v ∈ C,a:=sum_le_sum fun v i=> g v (e i)
   _=_:=by simp
 have r: ∑ v ∈ B \ C,f v<=(B \ C).card*k:=by
  calc
   _<=∑ _v ∈ B \ C,k:=by
    apply sum_le_sum
    intro v i
    have t:¬ k+1<=f v:=by
     intro h;exact (mem_sdiff.mp i).2 (mem_filter.mpr ⟨(mem_sdiff.mp i).1,h⟩)
    omega
   _=_:=by simp
 have n:C.card<=k:=d;have m:(B \ C).card<=B.card:=card_le_card sdiff_subset;have s:=sum_sdiff e (f:=f);have j:=Nat.mul_le_mul_right a n;have l:=Nat.mul_le_mul_right k m;nlinarith
lemma zR {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (A B:FS V)(a k:ℕ) (h:Disjoint A B)(q:A.card=a) (m:B.card=a) (n:4*k < a):(∃ W⊆B,W.card=k/\∀ v ∈ W,k+1<=(G.neighborFinset v ∩ A).card)\/(∃ W⊆A,W.card=k/\∀ v ∈ W,k+1<=(Gᶜ.neighborFinset v ∩ B).card) :=by
 classical
 let R :=B.filter (fun v=>k +1<=(G.neighborFinset v ∩ A).card)
 let C :=A.filter (fun v=>k +1<=(Gᶜ.neighborFinset v ∩ B).card)
 by_cases t:k<=R.card
 · obtain ⟨W,e,r⟩ :=exists_subset_card_eq t;exact Or.inl ⟨W,e.trans (filter_subset _ _),r,fun v l=> (mem_filter.mp (e l)).2⟩
 by_cases s:k<=C.card
 · obtain ⟨W,i,r⟩ :=exists_subset_card_eq s;exact Or.inr ⟨W,i.trans (filter_subset _ _),r,fun v l=> (mem_filter.mp (i l)).2⟩
 have g:=vG B (fun v=>(G.neighborFinset v ∩ A).card) a k (fun v _=> (card_le_card inter_subset_right).trans q.le) (show R.card<=k by omega)
 have d:=vG A (fun v=>(Gᶜ.neighborFinset v ∩ B).card) a k (fun v _=> (card_le_card inter_subset_right).trans m.le) (show C.card<=k by omega)
 have j:=zN G A B h;rw [m] at g;rw [q] at d;rw [q,m] at j;have w:0 < a:=by omega
 exfalso;nlinarith
lemma x1 {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (A B:FS V)(a k d:ℕ) (n:Disjoint A B)(C:a<=A.card) (z:a<=B.card) (h:4*k < a) (t:k+2*d<=a) (D:3<=a+k) (q:∀ v ∈ A,A.card<=(G.neighborFinset v ∩ A).card+d) (m:∀ v ∈ B,B.card<=(Gᶜ.neighborFinset v ∩ B).card+d):(∃ (v:V)(c:G.Walk v v),c.IsCycle/\c.length=a+k)\/(∃ (v:V)(c:Gᶜ.Walk v v),c.IsCycle/\c.length=a+k) :=by
 classical
 obtain ⟨A',j,x⟩ :=exists_subset_card_eq C;obtain ⟨B',i,w⟩ :=exists_subset_card_eq z;have e:Disjoint A' B':=n.mono j i;have l:=wQ G A' A d j q;have g:=wQ Gᶜ B' B d i m
 rcases zR G A' B' a k e x w h with
  ⟨W,hWB,hW,hgood⟩ | ⟨W,hWA,hW,hgood⟩
 · left
   obtain ⟨v,c,y,r⟩ :=sr G A' W d (e.mono_right hWB) (by omega) (by omega) l (fun v s=> by simpa only [hW] using hgood v s)
   exact ⟨v,c,y,by omega⟩
 · right
   obtain ⟨v,c,y,r⟩ :=sr Gᶜ B' W d (e.symm.mono_right hWA) (by omega) (by omega) g (fun v s=> by simpa only [hW] using hgood v s)
   exact ⟨v,c,y,by omega⟩
lemma ag (L b:ℕ)(j:200<=L) (i:1<=b) (d:100000*b<=L):0 < L/100/\24*b*L<=(L/100)*(L/10)/\24*b+L/10+2* (L/100)+1<=L/4/\4* (L/4) < 2*L-L/4/\L/4+2* (L/100+1)<=2*L-L/4/\(2*L-L/4)+L/4=2*L:=by
 have e:24*b*L<=(L/100)*(L/10) :=by
  have h:480*b<=L/100:=by omega
  have g:L<=20* (L/10) :=by omega
  calc
   24*b*L<=24*b* (20* (L/10)) :=Nat.mul_le_mul_left _ g
   _= (480*b)*(L/10) :=by ring
   _<=(L/100)*(L/10) :=Nat.mul_le_mul_right _ h
 exact ⟨by omega,e,by omega,by omega,by omega,by omega⟩
lemma st (B:ℕ)(Q:0 < B):∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (L b:ℕ),N₀<=L->1<=b->100000*b<=L->4*L<=Fintype.card V +b->Fintype.card V<=4 *L->Fintype.card V<=B *b->qK G (2*L)->qK Gᶜ (2*L)->False:=by
 obtain ⟨s,n⟩ :=vQ B Q;refine ⟨max s 200,?_⟩
 intro V _ _ G _ L b y N k r x e K q
 classical
 obtain ⟨S,T,J,P,M,H,g,j⟩:=n G L b (by omega) (by omega) N (by omega) r x e K q
 obtain ⟨W,t,F,d,m,I⟩ :=ag L b (by omega) N k
 have z:2* (Gᶜ.induce (S:Set V)).edgeFinset.card<=24*b*L:=by
  exact_mod_cast (show 2*((Gᶜ.induce (S:Set V)).edgeFinset.card:O)<=24* (b:O)*L by nlinarith only [g])
 have D:2* (G.induce (T:Set V)).edgeFinset.card<=24*b*L:=by
  exact_mod_cast (show 2*((G.induce (T:Set V)).edgeFinset.card:O)<=24* (b:O)*L by nlinarith only [j])
 obtain ⟨A,C,X,h0,w,Y,U,Z,R⟩:=zL G S T (L/100) (L/10) W (z.trans t) (D.trans t);have i:2*L-L/4<=A.card:=by omega
 have l:2*L-L/4<=C.card:=by omega
 rcases x1 G A C (2*L-L/4) (L/4) (L/100+1) w i l d m (by omega) Z R with
  ⟨v,c,hc,hlen⟩ | ⟨v,c,hc,hlen⟩
 · have h :=K v c hc;omega
 · have h :=q v c hc;omega
lemma w7:∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (L:ℕ),N₀<=L->4*L-L/100000<=Fintype.card V->(∃ (v:V)(c:G.Walk v v),c.IsCycle/\2*L<=c.length)\/(∃ (v:V)(c:Gᶜ.Walk v v),c.IsCycle/\2*L<=c.length) :=by
 obtain ⟨i,h⟩ :=st 800000 (by decide)
 refine ⟨max i 200000,?_⟩
 intro V _ _ G _ L q n
 classical
 by_contra g
 have m:qK G (2*L) :=by
  intro v c l;by_contra! e;exact g (Or.inl ⟨v,c,l,e⟩)
 have j:qK Gᶜ (2*L) :=by
  intro v c l;by_contra! e;exact g (Or.inr ⟨v,c,l,e⟩)
 obtain ⟨S,_,k⟩ :=exists_subset_card_eq (show 4 *L-L/100000<=(univ:FS V).card by simpa using n)
 have d:Fintype.card (S:Set V)=4*L-L/100000:=by
  calc
   Fintype.card (S:Set V)=(S:Set V).ncard:=Nat.card_eq_fintype_card.symm
   _=S.card:=Set.ncard_coe_finset S
   _=4*L-L/100000:=k
 apply h (G.induce (S:Set V)) L (L/100000) (by omega) (by omega) (by omega)
 · rw [d];omega
 · rw [d];omega
 · rw [d];omega
 · exact m.induce (S:Set V)
 · exact j.yB S
end E5
end _m
section bi
namespace E5
open SimpleGraph Fin.NatCast
lemma qL {m:ℕ} [NeZero m] (d:2<=m) (i:Fin m):(CG m).Adj i (i+1) :=by rw [cycleGraph_adj'];right;rw [add_sub_cancel_left];change 1 %m=1;exact Nat.mod_eq_of_lt (by omega)
def sO {V:Type*} {G:SG V} {m:ℕ} [NeZero m] (f:(CG m).Copy G) (i:Fin m):(CG m).Copy G where
 toHom:=
  { toFun:=fun j=>f (i+j)
    map_rel':=by
     intro a b h
     apply f.toHom.map_rel
     simpa only [cycleGraph_adj',add_sub_add_left_eq_sub] using h }
 injective':=f.injective.comp (add_right_injective i)
@[simp] lemma va {V:Type*} {G:SG V} {m:ℕ} [NeZero m] (f:(CG m).Copy G) (i j:Fin m):sO f i j =f (i+j) :=rfl
def rD (k:ℕ):ℕ:=if k =0 then 0 else k +1
lemma tx (m k:ℕ)(d:2<=m) (e:k < m-1):rD k < m :=by unfold rD;split_ifs <;> omega
lemma tu:Function.Injective rD:=by intro a b h;unfold rD at h;split_ifs at h <;> omega
lemma xo {V:Type*} {G:SG V} {m:ℕ} [NeZero m] (s:4<=m) (f:(CG m).Copy G) (h:G.Adj (f 0) (f 2)):∃ (v:V)(c:G.Walk v v),c.IsCycle/\c.length=m-1:=by
 apply qX G (m-1) (by omega) (fun k=>f (↑(rD k):Fin m))
 · intro a r b q l
   have n:=CA Fin.val (f.injective l);simp only [Fin.val_natCast,Nat.mod_eq_of_lt (tx m a (by omega) r),Nat.mod_eq_of_lt (tx m b (by omega) q)] at n
   exact tu n
 · intro k t
   by_cases i:k=0
   · subst k;simpa [rD] using h
   · have j:=f.toHom.map_rel (qL (by omega:2<=m) (↑(k+1):Fin m))
     simpa [rD,i,Nat.cast_add] using j
 · have e:rD (m-1-1)=m-1:=by unfold rD;split_ifs <;> omega
   have g:(↑(m-1):Fin m)+1=0:=by
    change (↑(m-1):Fin m)+(↑(1:ℕ):Fin m)=0;rw [<- Nat.cast_add,Nat.sub_add_cancel (by omega:1<=m)]
    simp
   have j:=f.toHom.map_rel (qL (by omega:2<=m) (↑(m-1):Fin m))
   have d:rD 0 =0:=by simp [rD]
   rw [e,d];change G.Adj (f.toHom (↑(m-1):Fin m)) (f.toHom (0:Fin m));simpa only [g] using j
lemma qB {V:Type*} {G:SG V} {m:ℕ} [NeZero m] (j:4<=m) (f:(CG m).Copy G) (e:¬ CG (m-1) ⊑ G) (i:Fin m):Gᶜ.Adj (f i) (f (i+2)) :=by
 rw [compl_adj];refine ⟨?_,?_⟩
 · intro h
   have k:=f.injective h
   have l:(2:Fin m)=0:=by
    apply add_left_cancel (a:=i);simpa only [add_zero] using k.symm
   have g:2%m=0:=CA Fin.val l;rw [Nat.mod_eq_of_lt (by omega:2 < m)] at g
   omega
 · intro h
   have d:G.Adj (sO f i 0) (sO f i 2) :=by
    simpa only [va,add_zero] using h
   exact e ((cycleGraph_isContained_iff (by omega:2 < m-1)).mpr (xo j (sO f i) d))
end E5
end bi
section bg
namespace E5
open SimpleGraph Fin.NatCast
lemma vj {m:ℕ} [NeZero m] (g:Odd m):Function.Injective (fun i:Fin m=>i +i) :=by
 intro i j d;obtain ⟨r,q⟩ :=g;have k:=i.isLt;have l:=j.isLt;have e:=CA Fin.val d;simp only [Fin.val_add] at e
 have hmod (x:ℕ) (n:x < m):(x+x) % m= if x +x < m then x +x else x +x-m:=by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
 rw [hmod i.val k,hmod j.val l] at e;apply Fin.ext;split_ifs at e <;> omega
lemma zT {m:ℕ} [NeZero m] (e:2<=m) (i j:Fin m):(CG m).Adj i j↔i=j+1\/j=i+1:=by
 obtain ⟨k,d⟩ :∃ k,m=k+2:= ⟨m-2,by omega⟩
 subst m;rw [cycleGraph_adj];simp only [sub_eq_iff_eq_add,add_comm]
def tv {V:Type*} {G H:SG V} {m:ℕ} [NeZero m] (l:2<=m) (e:Odd m) (f:(CG m).Copy G) (d:∀ i:Fin m,H.Adj (f i) (f (i+2))):(CG m).Copy H where
 toHom:=
  { toFun:=fun i=>f (i+i)
    map_rel':=by
     intro i j g
     rcases (zT l i j).mp g with h | h
     · subst i
       have k:(j+1)+(j+1)=(j+j)+2:=by
        calc
         _= (j+j)+((1:Fin m)+1) :=by abel
         _=_:=CA ((j+j) + ·) (Nat.cast_add 1 1).symm
       rw [k]
       exact (d (j+j)).symm
     · subst j
       have k:(i+1)+(i+1)=(i+i)+2:=by
        calc
         _= (i+i)+((1:Fin m)+1) :=by abel
         _=_:=CA ((i+i) + ·) (Nat.cast_add 1 1).symm
       rw [k]
       exact d (i+i)}
 injective':=f.injective.comp (vj e)
@[simp] lemma e7 {V:Type*} {G H:SG V} {m:ℕ} [NeZero m] (g:2<=m) (e:Odd m)(f:(CG m).Copy G) (d:∀ i:Fin m,H.Adj (f i) (f (i+2))) (i:Fin m):tv g e f d i =f (i+i) :=rfl
lemma w6 {V:Type*} {G:SG V} {m:ℕ} [NeZero m] (s:5<=m) (d:Odd m)(f:(CG m).Copy G) (n:¬ CG (m-1) ⊑ G) (l:¬ CG (m-1) ⊑ Gᶜ) (i:Fin m):G.Adj (f i) (f (i+4)) :=by
 have k:=qB (by omega:4<=m) f n
 let g :=tv (by omega:2<=m) d f k
 have e:Function.Surjective (fun j:Fin m=>j +j):=(Finite.injective_iff_surjective).mp (vj d)
 obtain ⟨j,q⟩ :=e i;change j +j=i at q;have h :=qB (by omega:4<=m) g l j
 change Gᶜᶜ.Adj (f (j+j)) (f ((j+2)+(j+2))) at h
 have r:(j+2)+(j+2)=(j+j)+4:=by
  calc
   _= (j+j)+((2:Fin m)+2) :=by abel
   _=_:=CA ((j+j) + ·) (Nat.cast_add 2 2).symm
 rw [r,q] at h;simpa only [compl_compl] using h
end E5
end bg
section bH
namespace E5
open SimpleGraph Fin.NatCast
def qt (k:ℕ):ℕ:=if k =0 then 0 else if k<=3 then 4 -k else k +1
lemma xd:Function.Injective qt:=by intro a b h;unfold qt at h;split_ifs at h <;> omega
lemma vY (m k:ℕ)(d:7<=m) (e:k < m-1):qt k < m :=by unfold qt;split_ifs <;> omega
lemma wa {V:Type*} {G:SG V} {m:ℕ} [NeZero m] (r:7<=m) (f:(CG m).Copy G) (q:G.Adj (f 0) (f 3)) (l:G.Adj (f 1) (f 5)):∃ (v:V)(c:G.Walk v v),c.IsCycle/\c.length=m-1:=by
 apply qX G (m-1) (by omega) (fun k=>f (qt k:Fin m))
 · intro a C b w j;have t:=CA Fin.val (f.injective j);simp only [Fin.val_natCast,Nat.mod_eq_of_lt (vY m a r C),Nat.mod_eq_of_lt (vY m b r w)] at t;exact xd t
 · intro k D
   by_cases i:k=0
   · subst k;simpa [qt] using q
   by_cases z:k=1
   · subst k
     have h:=(f.toHom.map_rel (qL (by omega:2<=m) (2:Fin m))).symm
     have n:(2:Fin m)+1=3:= (Nat.cast_add 2 1).symm;simpa [qt,n] using h
   by_cases y:k=2
   · subst k
     have h:=(f.toHom.map_rel (qL (by omega:2<=m) (1:Fin m))).symm
     have n:(1:Fin m)+1=2:= (Nat.cast_add 1 1).symm;simpa [qt,n] using h
   by_cases x:k=3
   · subst k;simpa [qt] using l
   · have s:3 < k:=by omega
     have h :=f.toHom.map_rel (qL (by omega:2<=m) (↑(k+1):Fin m))
     simpa [qt,i,show ¬ k<=3 by omega,
      show ¬ k+1<=3 by omega,Nat.cast_add] using h
 · have e:qt (m-1-1)=m-1:=by
    unfold qt;split_ifs <;> omega
   have d:qt 0 =0:=by simp [qt]
   rw [e,d];change G.Adj (f.toHom (↑(m-1):Fin m)) (f.toHom (0:Fin m))
   have g:(↑(m-1):Fin m)+1=0:=by
    change (↑(m-1):Fin m)+(↑(1:ℕ):Fin m)=0;rw [<- Nat.cast_add,Nat.sub_add_cancel (by omega:1<=m)]
    simp
   simpa only [g] using f.toHom.map_rel (qL (by omega:2<=m) (↑(m-1):Fin m))
lemma vV {V:Type*} {G:SG V} {m:ℕ} [NeZero m] (q:7<=m) (k:Odd m)(f:(CG m).Copy G) (e:¬ CG (m-1) ⊑ G) (d:¬ CG (m-1) ⊑ Gᶜ) (i:Fin m):Gᶜ.Adj (f i) (f (i+3)) :=by
 rw [compl_adj];refine ⟨?_,?_⟩
 · intro h
   have r:=f.injective h
   have t:(3:Fin m)=0:=by
    apply add_left_cancel (a:=i);simpa only [add_zero] using r.symm
   have n:3%m=0:=CA Fin.val t;rw [Nat.mod_eq_of_lt (by omega:3 < m)] at n
   omega
 · intro h
   let g :=sO f i
   have l:G.Adj (g 0) (g 3) :=by
    simpa only [g,va,add_zero] using h
   have j:=w6 (by omega:5<=m) k g e d 1
   have s:(1:Fin m)+4=5:= (Nat.cast_add 1 4).symm;rw [s] at j;exact e ((cycleGraph_isContained_iff (by omega:2 < m-1)).mpr (wa q g l j))
end E5
end bH
section bR
namespace E5
open SimpleGraph Fin.NatCast
def xR (m s a b:ℕ):Prop:= a+s=b\/b+s=a\/a+s=b+m\/b+s=a+m
lemma s3 {V:Type*} {G:SG V} {m:ℕ} [NeZero m] (f:Fin m->V) (s:ℕ)(g:∀ i,G.Adj (f i) (f (i+ (s:Fin m)))) (a b:ℕ)(h:xR m s a b):G.Adj (f (a:Fin m)) (f (b:Fin m)) :=by
 have d (a b:ℕ) (e:a+s=b\/a+s=b+m):G.Adj (f (a:Fin m)) (f (b:Fin m)) :=by
  have j:(a:Fin m)+(s:Fin m)=(b:Fin m) :=by
   rw [<- Nat.cast_add];rcases e with h | h
   · rw [h]
   · rw [h,Nat.cast_add,Fin.natCast_self,add_zero]
  simpa only [j] using g (a:Fin m)
 rcases h with h | h | h | h
 · exact d a b (Or.inl h)
 · exact (d b a (Or.inl h)).symm
 · exact d a b (Or.inr h)
 · exact (d b a (Or.inr h)).symm
def qD (r k:ℕ):ℕ:= if k =0 then 0 else if k =1 then 3 else if k < r then 2 *k+2 else if k =r then 1 else if k < 2 *r-1 then 4 *r+1-2*k else 2
lemma xG (r k:ℕ)(e:3<=r) (d:k < 2*r):qD r k < 2*r+1:=by unfold qD;split_ifs <;> omega
lemma zt (r:ℕ)(h:3<=r):Set.InjOn (qD r) (Set.Iio (2*r)) :=by intro a g b e d;change a < 2 *r at g;change b < 2 *r at e;unfold qD at d;split_ifs at d <;> omega
lemma yY (r k:ℕ)(e:3<=r) (d:k+1 < 2*r):xR (2*r+1) 2 (qD r k) (qD r (k+1))\/xR (2*r+1) 3 (qD r k) (qD r (k+1)) :=by unfold qD xR;split_ifs <;> first | contradiction | omega
lemma w2 {V:Type*} {G:SG V} (r:ℕ)(g:3<=r) (f:Fin (2*r+1)->V) (w:Function.Injective f)(n:∀ i,G.Adj (f i) (f (i+2))) (t:∀ i,G.Adj (f i) (f (i+3))):∃ (v:V)(c:G.Walk v v),c.IsCycle/\c.length=2*r:=by
 apply qX G (2*r) (by omega) (fun k=>f (qD r k:Fin (2*r+1)))
 · intro a q b l j;have m:=CA Fin.val (w j);simp only [Fin.val_natCast,Nat.mod_eq_of_lt (xG r a g q),Nat.mod_eq_of_lt (xG r b g l)] at m;exact zt r g q l m
 · intro k s
   rcases yY r k g s with h | h
   · exact s3 f 2 n _ _ h
   · exact s3 f 3 t _ _ h
 · have e:qD r (2*r-1)=2:=by
    unfold qD;split_ifs <;> omega
   have d:qD r 0=0:=by simp [qD]
   apply s3 f 2 n;rw [e,d];exact Or.inr (Or.inl rfl)
end E5
end bR
section _m
namespace E5
open SimpleGraph Finset
open scoped SimpleGraph Classical
lemma rS {V:Type*} (G:SG V)(m:ℕ) (i:7<=m) (g:Odd m)(n:CG m ⊑ G):CG (m-1) ⊑ G\/CG (m-1) ⊑ Gᶜ:=by
 classical
 by_contra hn;have e:(¬ CG (m-1) ⊑ G)/\(¬ CG (m-1) ⊑ Gᶜ) :=not_or.mp hn;obtain ⟨r,q⟩ :=g;have l:m=2*r+1:=by omega
 subst m;obtain ⟨f⟩ :=n;have k:=qB (by omega:4<=2*r+1) f e.1
 have j:=vV i ⟨r,by omega⟩ f e.1 e.2
 obtain ⟨v,c,d,h⟩ :=w2 r (by omega) f f.injective k j
 apply e.2;apply (cycleGraph_isContained_iff (by omega:2 < 2*r+1-1)).mpr
 exact ⟨v,c,d,by omega⟩
lemma vq {V:Type*} (G:SG V)(n:ℕ) (w:7<=n) (t:¬ CG n ⊑ G)(k:¬ CG n ⊑ Gᶜ) (e:∃ m,n<=m/\(CG m ⊑ G\/CG m ⊑ Gᶜ)):∃ m,n < m/\Even m/\(CG m ⊑ G\/CG m ⊑ Gᶜ)/\¬ CG (m-1) ⊑ G/\¬ CG (m-1) ⊑ Gᶜ:=by
 classical
 let m :=Nat.find e;have q:=Nat.find_spec e;change n<=m/\(CG m ⊑ G\/CG m ⊑ Gᶜ) at q
 have s:n < m:=by
  have v:m≠n:=by
   intro h;rcases q.2 with r | g
   · exact t (h ▸ r)
   · exact k (h ▸ g)
  omega
 have d:¬ (CG (m-1) ⊑ G\/CG (m-1) ⊑ Gᶜ) :=by
  intro h;apply Nat.find_min e (show m -1 < Nat.find e by change m -1 < m;omega)
  exact ⟨by omega,h⟩
 have i:Even m :=by
  rcases Nat.even_or_odd m with h | h
  · exact h
  · exfalso
    rcases q.2 with r | g
    · exact d (rS G m (by omega) h r)
    · rcases rS Gᶜ m (by omega) h g with l | j
      · exact d (Or.inr l)
      · exact d (Or.inl (by simpa only [compl_compl] using j))
 exact ⟨m,s,i,q.2,fun h=>d (Or.inl h),fun h=>d (Or.inr h)⟩
end E5
end _m
section bs
namespace E5
open SimpleGraph Fin.NatCast
def yZ {V:Type*} {G:SG V} {m:ℕ} [NeZero m] (f:(CG m).Copy G):(CG m).Copy G where
 toHom:=
  { toFun:=fun i=>f (-i)
    map_rel':=by
     intro a b h
     apply f.toHom.map_rel
     simpa only [cycleGraph_adj',neg_sub_neg,or_comm] using h }
 injective':=f.injective.comp neg_injective
@[simp] lemma tg {V:Type*} {G:SG V} {m:ℕ} [NeZero m] (f:(CG m).Copy G) (i:Fin m):yZ f i=f (-i) :=rfl
lemma uK {m:ℕ} [NeZero m] (a b:ℕ)(h:a+b=m): -(a:Fin m)=(b:Fin m) :=by apply neg_eq_iff_add_eq_zero.mpr;rw [<- Nat.cast_add,h,Fin.natCast_self]
lemma v6 {V:Type*} {G:SG V} {m:ℕ} [NeZero m] (f:(CG m).Copy G) (j:ℕ)(t:2<=j) (r:j+1 < m) (i:G.Adj (f 0) (f (j:Fin m))) (h:G.Adj (f 2) (f (↑(j+1):Fin m))):∃ (v:V)(c:G.Walk v v),c.IsCycle/\c.length=m-1:=by
 apply qX G (m-1) (by omega) (fun k=>f (qq j k:Fin m))
 · intro a C b y s;have x:=CA Fin.val (f.injective s);simp only [Fin.val_natCast,Nat.mod_eq_of_lt (zB m j a t r C),Nat.mod_eq_of_lt (zB m j b t r y)] at x;exact y0 j t x
 · intro k F
   by_cases z:k=0
   · subst k;simpa [qq,show 1 < j by omega] using i
   by_cases w:k+1 < j
   · have g:= (f.toHom.map_rel (qL (by omega:2<=m) (↑(j-k):Fin m))).symm
     have e:qq j k=j-k+1:=by unfold qq;split_ifs <;> omega
     have d:qq j (k+1)=j-k:=by simp [qq,w]
     simpa only [e,d,Nat.cast_add,Nat.cast_one,Copy.toHom_apply] using g
   by_cases D:k+1=j
   · have e:qq j k=2:=by unfold qq;split_ifs <;> omega
     have d:qq j (k+1)=j+1:=by
      unfold qq;split_ifs <;> omega
     simpa only [e,d,Nat.cast_ofNat] using h
   · have e:qq j k=k+1:=by unfold qq;split_ifs <;> omega
     have d:qq j (k+1)=(k+1)+1:=by
      unfold qq;split_ifs <;> omega
     have g:=f.toHom.map_rel (qL (by omega:2<=m) (↑(k+1):Fin m))
     simpa only [e,d,Nat.cast_add,Nat.cast_one,Copy.toHom_apply] using g
 · have n:qq j (m-1-1)=m-1:=by
    unfold qq;split_ifs <;> omega
   have l:qq j 0=0:=by simp [qq]
   rw [n,l];change G.Adj (f.toHom (↑(m-1):Fin m)) (f.toHom (0:Fin m))
   have q:(↑(m-1):Fin m)+1=0:=by
    change (↑(m-1):Fin m)+(↑(1:ℕ):Fin m)=0;rw [<- Nat.cast_add,Nat.sub_add_cancel (by omega:1<=m)]
    simp
   simpa only [q] using f.toHom.map_rel (qL (by omega:2<=m) (↑(m-1):Fin m))
lemma sc {V:Type*} {G:SG V} {m:ℕ} [NeZero m] (f:(CG m).Copy G) (j:ℕ)(l:2<=j) (h:j+1 < m) (i:¬ CG (m-1) ⊑ G) (e:G.Adj (f 0) (f (j:Fin m))):Gᶜ.Adj (f 2) (f (↑(j+1):Fin m)) :=by
 rw [compl_adj];refine ⟨?_,?_⟩
 · intro k
   have g:=CA Fin.val (f.injective k);change 2 %m= (j+1) % m at g;rw [Nat.mod_eq_of_lt (by omega:2 < m),Nat.mod_eq_of_lt h] at g
   omega
 · intro d;exact i ((cycleGraph_isContained_iff (by omega:2 < m-1)).mpr (v6 f j l h e d))
end E5
end bs
section aU
namespace E5
open SimpleGraph Fin.NatCast
def qw (t a k:ℕ):ℕ:= if k < t -1 then 2 *k+2 else if k-(t-1) < a then 2*(a-1- (k- (t-1)))+1 else 2*(a+t-1- (k- (t-1)))+1
lemma xp (t a k:ℕ)(g:2<=a) (d:a+2<=t) (e:k < 2*t-1):qw t a k < 2 *t:=by unfold qw;split_ifs <;> omega
lemma zb (t a:ℕ)(i:2<=a) (g:a+2<=t):Set.InjOn (qw t a) (Set.Iio (2*t-1)) :=by intro k d l e h;change k < 2 *t-1 at d;change l < 2 *t-1 at e;unfold qw at h;split_ifs at h <;> omega
lemma yR (t a k:ℕ)(h:2<=a) (e:a+2<=t) (g:k+1 < 2*t-1) (d:k≠t-2):xR (2*t) 2 (qw t a k) (qw t a (k+1)) :=by unfold qw xR;split_ifs <;> first | contradiction | omega
lemma wm {V:Type*} {G:SG V} (t a:ℕ) [NeZero (2*t)] (w:2<=a) (g:a+2<=t) (f:Fin (2*t)->V) (C:Function.Injective f)(z:∀ i,G.Adj (f i) (f (i+2))) (e:G.Adj (f 2) (f (↑(2*a+1):Fin (2*t)))) (d:G.Adj (f (↑(2*t-2):Fin (2*t))) (f (↑(2*a-1):Fin (2*t)))):∃ (v:V)(c:G.Walk v v),c.IsCycle/\c.length=2*t-1:=by
 apply qX G (2*t-1) (by omega) (fun k=>f (qw t a k:Fin (2*t)))
 · intro k s l y h;have x:=CA Fin.val (C h);simp only [Fin.val_natCast,Nat.mod_eq_of_lt (xp t a k w g s),Nat.mod_eq_of_lt (xp t a l w g y)] at x;exact zb t a w g s y x
 · intro k s
   by_cases j:k=t-2
   · have r:qw t a k =2*t-2:=by
      unfold qw;split_ifs <;> omega
     have q:qw t a (k+1)=2*a-1:=by
      unfold qw;split_ifs <;> omega
     simpa only [r,q] using d
   · exact s3 f 2 z _ _ (yR t a k w g s j)
 · have n:qw t a (2*t-1-1)=2*a+1:=by
    unfold qw;split_ifs <;> omega
   have m:qw t a 0 =2:=by
    unfold qw;split_ifs <;> omega
   simpa only [n,m,Nat.cast_ofNat] using e.symm
end E5
end aU
section bm
namespace E5
open SimpleGraph Fin.NatCast
lemma tM {V:Type*} {G:SG V} (t a:ℕ) [NeZero (2*t)] (r:2<=a) (n:a+2<=t) (f:(CG (2*t)).Copy G) (k:¬ CG (2*t-1) ⊑ G) (l:¬ CG (2*t-1) ⊑ Gᶜ):¬ G.Adj (f 0) (f (↑(2*a):Fin (2*t))) :=by
 intro h;have e:=sc f (2*a) (by omega) (by omega) k h
 let g :=yZ f;have hneg: -(↑(2* (t-a)):Fin (2*t))=(↑(2*a):Fin (2*t)):=uK _ _ (by omega)
 have m:G.Adj (g 0) (g (↑(2* (t-a)):Fin (2*t))) :=by
  simpa only [g,tg,neg_zero,hneg] using h
 have d:=sc g (2* (t-a)) (by omega) (by omega) k m
 change Gᶜ.Adj (f (-(2:Fin (2*t)))) (f (-(↑(2* (t-a)+1):Fin (2*t)))) at d;have j: -(2:Fin (2*t))=(↑(2*t-2):Fin (2*t)):=uK 2 (2*t-2) (by omega)
 have i: -(↑(2* (t-a)+1):Fin (2*t))=(↑(2*a-1):Fin (2*t)):=uK _ _ (by omega)
 rw [j,i] at d;have q:=qB (by omega:4<=2*t) f k
 exact l ((cycleGraph_isContained_iff (by omega:2 < 2*t-1)).mpr (wm t a r n f f.injective q e d))
lemma zd {V:Type*} {G:SG V} (t a:ℕ) [NeZero (2*t)] (m:4<=t) (n:1<=a) (l:a < t) (f:(CG (2*t)).Copy G) (d:¬ CG (2*t-1) ⊑ G) (e:¬ CG (2*t-1) ⊑ Gᶜ):Gᶜ.Adj (f 0) (f (↑(2*a):Fin (2*t))) :=by
 by_cases k:a=1
 · subst a
   have h :=qB (by omega:4<=2*t) f d 0
   simpa only [zero_add,Nat.mul_one,Nat.cast_ofNat] using h
 by_cases g:a+1=t
 · have h :=qB (by omega:4<=2*t) f d (↑(2*a):Fin (2*t))
   have i:(↑(2*a):Fin (2*t))+2=0:=by
    change (↑(2*a):Fin (2*t))+(↑(2:ℕ):Fin (2*t))=0;rw [<- Nat.cast_add,show 2 *a+2=2*t by omega,Fin.natCast_self]
   rw [i] at h;exact h.symm
 rw [compl_adj];refine ⟨?_,tM t a (by omega) (by omega) f d e⟩
 intro i;have j:=CA Fin.val (f.injective i);change 0=(2*a) % (2*t) at j;rw [Nat.mod_eq_of_lt (by omega:2*a < 2*t)] at j
 omega
lemma w3 {V:Type*} {G:SG V} (t a:ℕ) [NeZero (2*t)] (h:4<=t) (j:1<=a) (e:a < t) (f:(CG (2*t)).Copy G) (g:¬ CG (2*t-1) ⊑ G) (d:¬ CG (2*t-1) ⊑ Gᶜ) (i:Fin (2*t)):Gᶜ.Adj (f i) (f (i+ (↑(2*a):Fin (2*t)))) :=by simpa only [va,add_zero] using zd t a h j e (sO f i) g d
lemma z2 {V:Type*} {G:SG V} (t:ℕ) [NeZero (2*t)] (r:4<=t) (f:(CG (2*t)).Copy G) (n:¬ CG (2*t-1) ⊑ G) (k:¬ CG (2*t-1) ⊑ Gᶜ) (i j:Fin (2*t)) (l:i≠j)(g:i.val%2=j.val%2):Gᶜ.Adj (f i) (f j) :=by
 have d:i.val≠j.val:=fun h=>l (Fin.ext h)
 wlog hij:i.val < j.val generalizing i j
 · exact (this j i l.symm g.symm d.symm (by omega)).symm
 let a:=(j.val-i.val)/2;have e:i.val+2*a=j.val:=by dsimp only [a];omega
 have s:1<=a:=by omega
 have m:a < t:=by have v:=j.isLt;omega
 have q:i+ (↑(2*a):Fin (2*t))=j:=by
  apply Fin.ext;simp only [Fin.val_add,Fin.val_natCast,Nat.mod_eq_of_lt (show 2 *a < 2*t by omega),e,Nat.mod_eq_of_lt j.isLt]
 have h :=w3 t a r s m f n k i;simpa only [q] using h
end E5
end bm
section _m
namespace E5
open SimpleGraph Finset
open scoped SimpleGraph Classical
def zq (t:ℕ)(b:Fin 2) (i:Fin t):Fin (2*t):=⟨2*i.val+b.val,by have e:=i.isLt;have d:=b.isLt;omega⟩
lemma yo (t:ℕ)(b:Fin 2):Function.Injective (zq t b) :=by intro i j h;have d:=CA Fin.val h;change 2 *i.val+b.val=2*j.val+b.val at d;apply Fin.ext;omega
noncomputable def wv {V:Type*} [DecidableEq V] {G:SG V} {t:ℕ} (f:(CG (2*t)).Copy G) (b:Fin 2):FS V:=univ.image (fun i:Fin t=>f (zq t b i))
lemma tz {V:Type*} [DecidableEq V] {G:SG V} {t:ℕ} (f:(CG (2*t)).Copy G) (b:Fin 2):(wv f b).card=t:=by
 classical
 have d:Function.Injective (fun i:Fin t=>f (zq t b i)):=f.injective.comp (yo t b)
 rw [wv,card_image_of_injective _ d,card_univ,Fintype.card_fin]
lemma aa {V:Type*} [DecidableEq V] {G:SG V} {t:ℕ} (f:(CG (2*t)).Copy G):Disjoint (wv f 0) (wv f 1) :=by
 classical
 apply D2
 intro v d e;obtain ⟨i,_,k⟩ :=mem_image.mp d;obtain ⟨j,_,g⟩ :=mem_image.mp e;have h :=CA Fin.val (f.injective (k.trans g.symm));change 2 *i.val+0=2*j.val+1 at h;omega
lemma zA {V:Type*} [DecidableEq V] {G:SG V} {t:ℕ} [NeZero (2*t)] (n:4<=t) (f:(CG (2*t)).Copy G) (g:¬ CG (2*t-1) ⊑ G) (d:¬ CG (2*t-1) ⊑ Gᶜ) (b:Fin 2):Gᶜ.IsClique ((wv f b:FS V):Set V) :=by
 classical
 intro u q v m e;obtain ⟨i,_,k⟩ :=mem_image.mp q;obtain ⟨j,_,l⟩ :=mem_image.mp m;rw [<- k,<- l];apply z2 t n f g d
 · intro h;exact e (k.symm.trans ((CA f h).trans l))
 · change (2*i.val+b.val) % 2= (2*j.val+b.val) % 2;omega
lemma yn {V:Type*} (G:SG V)(t:ℕ) (g:4<=t) (h:CG (2*t) ⊑ G) (e:¬ CG (2*t-1) ⊑ G) (d:¬ CG (2*t-1) ⊑ Gᶜ):∃ A B:FS V,Disjoint A B/\A.card=t/\B.card=t/\Gᶜ.IsClique (A:Set V)/\Gᶜ.IsClique (B:Set V) :=by
 classical
 let:NeZero (2*t):=⟨by omega⟩
 obtain ⟨f⟩ :=h;exact ⟨wv f 0,wv f 1,aa f,tz f 0,tz f 1,zA g f e d 0,zA g f e d 1⟩
lemma yi {V:Type*} [Fintype V] [DecidableEq V] (d:3<=Fintype.card V) (a b:V)(k:a≠b):∃ p:(⊤ :SG V).Walk a b,p.IsHamiltonian:=by
 classical
 have j:(⊤ :SG V).IsHamiltonian:=by
  apply SimpleGraph.x3 d
  intro v;rw [((⊤ :SG V).degree_eq_card_sub_one v).mpr (by simp [IsUniversal])]
  omega
 let:Nontrivial V :=Fintype.one_lt_card_iff_nontrivial.mp (by omega)
 obtain ⟨q,l⟩ :=j.exists_isHamiltonianCycle b;let e :=Equiv.swap q.snd a;let f:=(Iso.completeGraph e).toHom;have h:f q.snd=a:=Equiv.swap_apply_left _ _;have g:f b=b:=Equiv.swap_apply_of_ne_of_ne (q.adj_snd l.isCycle.not_nil).ne k.symm;let p:=(q.tail.map f).copy h g;refine ⟨p,?_⟩;have i:=l.isHamiltonian_tail.map f e.bijective;simpa only [p,Walk.IsHamiltonian,Walk.support_copy] using i
def wt {V:Type*} (G:SG V) (a b:V):SG (Option V) where
 Adj
  | some u,some v=>G.Adj u v
  | none,some v=>v =a\/v=b
  | some u,none=> u =a\/u=b
  | none,none=> False
 symm:= ⟨by rintro (_ | u) (_ | v) h <;> first | exact h | exact h.symm⟩
 loopless:= ⟨by rintro (_ | u) <;> first | exact not_false | exact G.loopless.irrefl u⟩
@[simp] lemma e9 {V:Type*} (G:SG V)(a b u v:V):(wt G a b).Adj (some u) (some v)↔G.Adj u v:=Iff.rfl
@[simp] lemma e8 {V:Type*} (G:SG V)(a b v:V):(wt G a b).Adj none (some v)↔v=a\/v=b:=Iff.rfl
lemma rJ {V:Type*} (G:SG V)(A:FS V) (I:G.IsClique (A:Set V)) (L:ℕ)(K:2<=L) (j:L+1<=A.card) (u v:V)(H:u∈A) (J:v∈A)(s:u≠v):∃ p:G.Walk u v,p.IsPath/\p.length=L/\∀ x ∈ p.support,x∈A:=by
 classical
 have i:({u,v}:FS V)⊆A:=by
  simp only [insert_subset_iff,singleton_subset_iff];exact ⟨H,J⟩
 have d:({u,v}:FS V).card<=L+1:=by
  have h :=card_insert_le u ({v}:FS V);simp only [card_singleton] at h;omega
 obtain ⟨B,l,e,m⟩ :=exists_subsuperset_card_eq i d j;have z:u∈B:=l (by simp)
 have r:v∈B:=l (by simp)
 have k:Fintype.card (B:Set V)=L+1:=by
  calc
   Fintype.card (B:Set V)=(B:Set V).ncard:=Nat.card_eq_fintype_card.symm
   _=B.card:=Set.ncard_coe_finset B
   _=L+1:=m
 let f:(⊤ :SG (B:Set V)) →g G :=
  { toFun:=Subtype.val
    map_rel':=by
     intro x y w
     apply I (e x.property) (e y.property)
     intro C
     have t:x≠y:=by simpa only [top_adj] using w
     exact t (Subtype.ext C)}
 obtain ⟨q,D⟩ :=yi (V:= (B:Set V)) (by omega) ⟨u,z⟩ ⟨v,r⟩ (fun h=>s (CA Subtype.val h))
 refine ⟨q.map f,D.isPath.map Subtype.val_injective,?_,?_⟩
 · rw [Walk.length_map,D.length_eq,k];omega
 · intro x F;rw [Walk.support_map,List.mem_map] at F;obtain ⟨y,_,n⟩ :=F;exact n ▸ e y.property
lemma ri {V:Type*} {G:SG V} {a a' b b':V} (A B:FS V)(i:Disjoint A B) (s:b'∈B)(p:G.Walk a a') (q:G.Walk b' b)(D:p.IsPath) (y:q.IsPath)(F:2<=p.length) (k:∀ x ∈ p.support,x∈A)(l:∀ x ∈ q.support,x∈B) (t:G.Adj a b)(d:G.Adj a' b'):∃ (v:V)(c:G.Walk v v),c.IsCycle/\c.length=p.length+q.length+2:=by
 classical
 have w:b' ∉ p.support:=fun h=>(D1 i (k b' h)) s
 have r:(p.concat d).IsPath:=D.concat w d
 have g:∀ x ∈ (p.concat d).support,x∈q.support->x=b':=by
  intro x e m;simp only [Walk.support_concat,List.mem_append,List.mem_singleton] at e;rcases e with e | n
  · exact ((D1 i (k x e)) (l x m)).elim
  · exact n
 have z:=qr (p.concat d) q r y g;obtain ⟨c,C,j⟩ :=r2 ((p.concat d).append q) z (by simp only [Walk.length_append,Walk.length_concat];omega) t
 refine ⟨a,c,C,?_⟩;simp only [Walk.length_append,Walk.length_concat] at j;omega
lemma vO {V:Type*} (G:SG V)(A B:FS V) (e:Disjoint A B)(F:G.IsClique (A:Set V)) (x:G.IsClique (B:Set V)) (L M:ℕ)(z:2<=L) (J:2<=M) (l:L+1<=A.card) (h:M+1<=B.card) (a a' b b':V)(H:a∈A) (n:a'∈A)(D:b∈B) (g:b'∈B)(m:a≠a') (r:b≠b')(s:G.Adj a b) (d:G.Adj a' b'):∃ (v:V)(c:G.Walk v v),c.IsCycle/\c.length=L+M+2:=by
 classical
 obtain ⟨p,I,j,k⟩ :=rJ G A F L z l a a' H n m;obtain ⟨q,y,t,i⟩ :=rJ G B x M J h b' b g D r.symm;obtain ⟨v,c,C,w⟩ :=ri A B e g p q I y (by omega) k i s d
 exact ⟨v,c,C,by omega⟩
lemma rj {V:Type*} (G:SG V)(A B:FS V) (e:Disjoint A B)(t:G.IsClique (A:Set V)) (s:G.IsClique (B:Set V)) (r:ℕ)(y:3<=r) (h:r+1<=A.card) (n:r+1<=B.card) (l:¬ CG (2*r+1) ⊑ G) (a a' b b':V)(w:a∈A) (j:a'∈A)(q:b∈B) (k:b'∈B)(i:G.Adj a b) (g:G.Adj a' b'):a=a'\/b=b':=by
 classical
 by_contra! d;obtain ⟨v,c,x,m⟩ :=vO G A B e t s r (r-1) (by omega) (by omega) h (by omega) a a' b b' w j q k d.1 d.2 i g
 apply l;apply (cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr
 exact ⟨v,c,x,by omega⟩
lemma ra {V:Type*} (A B:FS V)(R:V->V->Prop) (e:∀ a ∈ A,∀ a' ∈ A,∀ b ∈ B,∀ b' ∈ B,R a b->R a' b'->a=a'\/b=b'):∃ S:FS V,S.card<=1/\∀ a ∈ A,∀ b ∈ B,R a b->a∈S\/b∈S:=by
 classical
 by_cases k:∃ a ∈ A,∃ b ∈ B,R a b
 · obtain ⟨a,s,b,j,i⟩ :=k
   by_cases g:∀ u ∈ A,∀ v ∈ B,R u v->u=a
   · refine ⟨{a},by simp,?_⟩
     intro u r v q h;exact Or.inl (by simpa using g u r v q h)
   · push Not at g
     obtain ⟨c,y,d,C,n,m⟩ :=g;have z:d=b:= (e c y a s d C b j n i).resolve_left m;subst d
     refine ⟨{b},by simp,?_⟩
     intro u r v q h
     have x:v=b:=by
      by_contra l;have t:= (e u r a s v q b j h i).resolve_right l;have w:= (e u r c y v q b j h n).resolve_right l;exact m (w.symm.trans t)
     exact Or.inr (by simpa using x)
 · refine ⟨∅,by simp,?_⟩
   intro a s b j i;exact (k ⟨a,s,b,j,i⟩).elim
lemma sp {V:Type*} [DecidableEq V] (G:SG V)(A B S:FS V) (e:Disjoint A B)(d:∀ a ∈ A,∀ b ∈ B,G.Adj a b->a∈S\/b∈S):∀ a ∈ A \ S,∀ b ∈ B \ S,Gᶜ.Adj a b:=by
 intro a j b g;rw [compl_adj];refine ⟨?_,?_⟩
 · intro k;exact (D1 e (mem_sdiff.mp j).1) (k ▸ (mem_sdiff.mp g).1)
 · intro i
   rcases d a (mem_sdiff.mp j).1 b (mem_sdiff.mp g).1 i with h | h
   · exact (mem_sdiff.mp j).2 h
   · exact (mem_sdiff.mp g).2 h
def rW {V:Type*} (G:SG V)(r:ℕ):Prop:= ∃ A B:FS V,Disjoint A B/\r<=A.card/\r<=B.card/\G.IsClique (A:Set V)/\G.IsClique (B:Set V)/\∀ a ∈ A,∀ b ∈ B,Gᶜ.Adj a b
lemma sw {V:Type*} (G:SG V)(r t:ℕ) (F:3<=r) (H:r+1<=t) (I:CG (2*t) ⊑ G) (v:¬ CG (2*t-1) ⊑ G) (k:¬ CG (2*t-1) ⊑ Gᶜ) (d:¬ CG (2*r+1) ⊑ Gᶜ):rW Gᶜ r :=by
 classical
 obtain ⟨A,B,e,J,D,z,y⟩ :=yn G t (by omega) I v k
 have j:=rj Gᶜ A B e z y r F (by omega) (by omega) d
 obtain ⟨S,L,i⟩ :=ra A B Gᶜ.Adj (fun a n a' w b m b' x h l=> j a a' b b' n w m x h l)
 have g (C:FS V) (K:r+1<=C.card):r<=(C \ S).card:=by
  have q:=card_sdiff_add_card_inter C S;have s:(C ∩ S).card<=S.card:=card_le_card inter_subset_right;omega
 refine ⟨A \ S,B \ S,e.mono sdiff_subset sdiff_subset,g A (by omega),g B (by omega),?_,?_,?_⟩
 · intro a n b m h;exact z (mem_sdiff.mp n).1 (mem_sdiff.mp m).1 h
 · intro a n b m h;exact y (mem_sdiff.mp n).1 (mem_sdiff.mp m).1 h
 · exact sp Gᶜ A B S e i
lemma wA {V:Type*} (G:SG V)(r:ℕ) (w:3<=r) (l:¬ CG (2*r+1) ⊑ G) (j:¬ CG (2*r+1) ⊑ Gᶜ) (n:∃ m,2*r+1<=m/\(CG m ⊑ G\/CG m ⊑ Gᶜ)):rW G r\/rW Gᶜ r :=by
 classical
 obtain ⟨m,s,i,g,e,d⟩:=vq G (2*r+1) (by omega) l j n
 obtain ⟨t,x⟩ :=i;have q:m=2*t:=by omega
 rw [q] at g e d s;rcases g with v | v
 · exact Or.inr (sw G r t w (by omega) v e d j)
 · left
   have h:¬ CG (2*t-1) ⊑ Gᶜᶜ:=by simpa only [compl_compl] using e
   have k:¬ CG (2*r+1) ⊑ Gᶜᶜ:=by simpa only [compl_compl] using l
   simpa only [compl_compl] using sw Gᶜ r t w (by omega) v d h k
lemma vr:∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (r:ℕ),N₀<=r->4* (r+1)-(r+1)/100000<=Fintype.card V->(¬ CG (2*r+1) ⊑ G)->(¬ CG (2*r+1) ⊑ Gᶜ)->rW G r\/rW Gᶜ r :=by
 obtain ⟨g,d⟩ :=w7;refine ⟨max g 3,?_⟩
 intro V _ _ G _ r l k i e;apply wA G r (by omega) i e
 rcases d G (r+1) (by omega) k with ⟨v,c,j,h⟩ | ⟨v,c,j,h⟩
 · refine ⟨c.length,by omega,Or.inl ?_⟩
   exact (cycleGraph_isContained_iff (by omega:2 < c.length)).mpr ⟨v,c,j,rfl⟩
 · refine ⟨c.length,by omega,Or.inr ?_⟩
   exact (cycleGraph_isContained_iff (by omega:2 < c.length)).mpr ⟨v,c,j,rfl⟩
lemma rb {V:Type*} (G:SG V)(A B:FS V) (r:ℕ)(q:1<=r) (g:Disjoint A B)(l:r+1<=A.card) (j:r<=B.card) (d:∀ a ∈ A,∀ b ∈ B,G.Adj a b)(u v:V) (n:u∈A)(k:v∈A) (e:G.Adj u v):∃ (w:V)(c:G.Walk w w),c.IsCycle/\c.length=2*r+1:=by
 classical
 obtain ⟨p,m,i,_⟩ :=rf G r q A B g d l j u v n k e.ne;obtain ⟨c,s,h⟩ :=r2 p m (by omega) e
 exact ⟨u,c,s,by omega⟩
lemma rx {V:Type*} (G:SG V)(A B:FS V) (r:ℕ)(z:1<=r) (k:Disjoint A B)(D:r<=A.card) (t:r<=B.card) (d:∀ a ∈ A,∀ b ∈ B,G.Adj a b)(x u v:V) (s:x ∉ A)(q:x ∉ B) (y:u∈A)(F:v∈B) (l:G.Adj x u)(j:G.Adj x v):∃ (w:V)(c:G.Walk w w),c.IsCycle/\c.length=2*r+1:=by
 classical
 obtain ⟨p,H,e,i⟩ :=rY G r z A B k d D t u v y F
 have m:x ∉ p.support:=by
  intro h;rcases mem_union.mp (i x h) with h | h
  · exact s h
  · exact q h
 have n:=H.concat m j.symm;obtain ⟨c,C,g⟩ :=r2 (p.concat j.symm) n (by rw [Walk.length_concat,e];omega) l.symm
 refine ⟨u,c,C,?_⟩;rw [Walk.length_concat,e] at g;omega
lemma uT {V:Type*} [DecidableEq V] (G:SG V)(A S:FS V) (j:A⊆S)(d:∀ a ∈ A,∀ s ∈ S,a≠s->G.Adj a s) (u:V)(l:u∈S):G.IsClique ((insert u A:FS V):Set V) :=by
 intro x n y k e;rcases mem_insert.mp n with m | i
 · subst x
   rcases mem_insert.mp k with h | g
   · exact (e h.symm).elim
   · exact (d y g u l e.symm).symm
 · rcases mem_insert.mp k with h | g
   · subst y;exact d x i u l e
   · exact d x i y (j g) e
lemma sC {V:Type*} (G:SG V)(A S:FS V) (m:A⊆S)(d:∀ a ∈ A,∀ s ∈ S,a≠s->G.Adj a s) (L:ℕ)(H:3<=L) (C:L<=A.card) (u v:V)(w:u∈S) (z:v∈S)(l:v ∉ A) (r:u≠v):∃ p:G.Walk u v,p.IsPath/\p.length=L/\∀ x ∈ p.support,x∈S:=by
 classical
 have q:(A.erase u).Nonempty:=by
  apply card_pos.mp
  have I:A.card-1<=(A.erase u).card:=by
   by_cases h:u∈A
   · rw [card_erase_of_mem h]
   · rw [erase_eq_of_notMem h];omega
  omega
 obtain ⟨a,y⟩ :=q;have i:=mem_of_mem_erase y;have n:u≠a:= (mem_erase.mp y).1.symm;have F:L<=(insert u A).card:=C.trans (card_le_card (subset_insert _ _));obtain ⟨p,D,k,e⟩ :=rJ G (insert u A) (uT G A S m d u w) (L-1) (by omega) (by omega) u a (mem_insert_self _ _) (mem_insert_of_mem i) n
 have t:v ∉ insert u A:=by
  simp only [mem_insert,not_or];exact ⟨r.symm,l⟩
 have j:G.Adj a v:=d a i v z (fun h=>l (h ▸ i))
 refine ⟨p.concat j,D.concat (fun h=>t (e v h)) j,?_,?_⟩
 · rw [Walk.length_concat,k];omega
 · intro x g
   rw [Walk.support_concat,List.mem_append,List.mem_singleton] at g;rcases g with g | g
   · rcases mem_insert.mp (e x g) with g | g
     · exact g ▸ w
     · exact m g
   · exact g ▸ z
lemma sF {V:Type*} (G:SG V)(A S:FS V) (h:A⊆S)(e:∀ a ∈ A,∀ s ∈ S,a≠s->G.Adj a s) (L:ℕ)(F:3<=L) (H:L<=A.card) (M:L+1<=S.card) (u v:V)(D:u∈S) (I:v∈S)(k:u≠v):∃ p:G.Walk u v,p.IsPath/\p.length=L/\∀ x ∈ p.support,x∈S:=by
 classical
 by_cases l:v∈A
 · by_cases n:u∈A
   · by_cases m:L+1<=A.card
     · have i:G.IsClique (A:Set V) :=fun _ K _ J C=> e _ K _ (h J) C
       obtain ⟨p,t,g,d⟩ :=rJ G A i L (by omega) m u v n l k
       exact ⟨p,t,g,fun x z=> h (d x z)⟩
     · obtain ⟨x,q,w⟩ :=exists_mem_notMem_of_card_lt_card (show A.card < S.card by omega)
       have j:L+1<=(insert x A).card:=by rw [card_insert_of_notMem w];omega
       obtain ⟨p,t,g,d⟩ :=rJ G (insert x A) (uT G A S h e x q) L (by omega) j u v (mem_insert_of_mem n) (mem_insert_of_mem l) k
       refine ⟨p,t,g,?_⟩
       intro y r;rcases mem_insert.mp (d y r) with r | r
       · exact r ▸ q
       · exact h r
   · obtain ⟨p,t,g,d⟩ :=sC G A S h e L F H v u I D n k.symm
     refine ⟨p.reverse,t.reverse,by simpa only [Walk.length_reverse] using g,?_⟩
     intro x z;exact d x (by simpa only [Walk.support_reverse,List.mem_reverse] using z)
 · exact sC G A S h e L F H u v D I l k
lemma wn {V:Type*} (G:SG V)(A B:FS V) (r:ℕ)(y:1<=r) (g:Disjoint A B)(w:r<=A.card) (v:r<=B.card) (d:∀ a ∈ A,∀ b ∈ B,Gᶜ.Adj a b)(q:¬ CG (2*r+1) ⊑ Gᶜ) (x:V)(j:x ∉ A) (i:x ∉ B):(∀ a ∈ A,G.Adj x a)\/(∀ b ∈ B,G.Adj x b) :=by
 classical
 by_contra h;push Not at h;obtain ⟨⟨a,t,m⟩,⟨b,s,l⟩⟩ :=h
 have k:Gᶜ.Adj x a:=by
  rw [compl_adj];exact ⟨fun n=> j (n ▸ t),m⟩
 have e:Gᶜ.Adj x b:=by
  rw [compl_adj];exact ⟨fun n=> i (n ▸ s),l⟩
 exact q ((cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr (rx Gᶜ A B r y g w v d x a b j i t s k e))
lemma yd {V:Type*} [Fintype V] [DecidableEq V] (G:SG V)(A B:FS V) (r:ℕ)(M:1<=r) (e:Disjoint A B)(v:r<=A.card) (l:r<=B.card) (P:G.IsClique (A:Set V)) (L:G.IsClique (B:Set V)) (d:∀ a ∈ A,∀ b ∈ B,Gᶜ.Adj a b)(q:¬ CG (2*r+1) ⊑ Gᶜ):∃ S T:FS V,Disjoint S T/\S ∪ T=univ/\A⊆S/\B⊆T/\(∀ a ∈ A,∀ s ∈ S,a≠s->G.Adj a s)/\(∀ b ∈ B,∀ t ∈ T,b≠t->G.Adj b t) :=by
 classical
 let X :=univ.filter (fun x=>x ∉ B/\∀ a ∈ A,G.Adj x a)
 let S :=A ∪ X;let T :=Sᶜ;have j:A⊆S:=subset_union_left
 have m:∀ b ∈ B,b ∉ S:=by
  intro b i J;rcases mem_union.mp J with n | w
  · exact (D1 e n) i
  · exact (mem_filter.mp w).2.1 i
 have I:B⊆T:=fun b i=> mem_compl.mpr (m b i)
 refine ⟨S,T,disjoint_compl_right,union_compl S,j,I,?_,?_⟩
 · intro a K s N F
   rcases mem_union.mp N with y | H
   · exact P K y F
   · exact ((mem_filter.mp H).2.2 a K).symm
 · intro b i t Q D
   have k:t ∉ S:=mem_compl.mp Q;by_cases g:t∈B
   · exact L i g D
   · have C:t ∉ A:=fun h=>k (j h)
     rcases wn G A B r M e v l d q t C g with h | h
     · have z:t∈X:=mem_filter.mpr ⟨mem_univ _,g,h⟩;exact (k (mem_union_right A z)).elim
     · exact (h b i).symm
lemma r8 {V:Type*} (G:SG V)(A B S T:FS V) (r:ℕ)(P:4<=r) (n:A⊆S)(j:B⊆T) (L:r<=A.card) (F:r<=B.card) (e:∀ a ∈ A,∀ s ∈ S,a≠s->G.Adj a s) (d:∀ b ∈ B,∀ t ∈ T,b≠t->G.Adj b t) (h:Disjoint S T)(I:r+1<=S.card) (w:¬ CG (2*r+1) ⊑ G) (a a' b b':V)(M:a∈S) (x:a'∈S)(K:b∈T) (i:b'∈T)(y:G.Adj a b) (g:G.Adj a' b'):a=a'\/b=b':=by
 classical
 by_contra! k;obtain ⟨p,N,m,C⟩ :=sF G A S n e r (by omega) L I a a' M x k.1
 have Q:r<=T.card:=F.trans (card_le_card j);obtain ⟨q,H,z,l⟩ :=sF G B T j d (r-1) (by omega) (by omega) (by omega) b' b i K k.2.symm
 obtain ⟨v,c,J,D⟩ :=ri S T h i p q N H (by omega) C l y g
 exact w ((cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr ⟨v,c,J,by omega⟩)
lemma vt {V:Type*} [Fintype V] [DecidableEq V] (G:SG V)(A B S T:FS V) (r:ℕ)(y:4<=r) (k:A⊆S)(q:B⊆T) (C:r<=A.card) (x:r<=B.card) (e:∀ a ∈ A,∀ s ∈ S,a≠s->G.Adj a s) (d:∀ b ∈ B,∀ t ∈ T,b≠t->G.Adj b t) (g:Disjoint S T)(i:S ∪ T=univ) (I:2*r < Fintype.card V) (l:¬ CG (2*r+1) ⊑ G):∃ Z:FS V,Z.card<=1/\∀ s ∈ S,∀ t ∈ T,G.Adj s t->s∈Z\/t∈Z:=by
 have w:S.card+T.card=Fintype.card V :=by
  rw [<- card_union_of_disjoint g,i,card_univ]
 apply ra S T G.Adj
 intro a D a' m b z b' n v j;by_cases F:r+1<=S.card
 · exact r8 G A B S T r y k q C x e d g F l a a' b b' D m z n v j
 · have H:r+1<=T.card:=by omega
   have h :=r8 G B A T S r y q k x C d e g.symm H l b b' a a' z n D m v.symm j.symm;exact h.symm
lemma qS {V:Type*} (G:SG V)(A S:FS V) (r:ℕ)(J:1<=r) (t:A⊆S)(L:r+1<=A.card) (N:2*r+1<=S.card) (d:∀ a ∈ A,∀ s ∈ S,a≠s->G.Adj a s):∃ (v:V)(c:G.Walk v v),c.IsCycle/\c.length=2*r+1:=by
 classical
 obtain ⟨C,i,m⟩ :=exists_subset_card_eq L;have k:C⊆S:=i.trans t
 have g:r<=(S \ C).card:=by
  rw [card_sdiff,inter_eq_left.mpr k,m];omega
 obtain ⟨W,l,K⟩ :=exists_subset_card_eq g
 have j:Disjoint C W:=by
  apply D2
  intro x M z;exact (mem_sdiff.mp (l z)).2 M
 have e:∀ a ∈ C,∀ w ∈ W,G.Adj a w:=by
  intro a H w F;have n:= (mem_sdiff.mp (l F)).1;have q:a≠w:=fun h=>(D1 j H) (h ▸ F)
  exact d a (i H) w n q
 obtain ⟨u,D,v,I,y⟩ :=one_lt_card.mp (show 1 < C.card by omega)
 exact rb G C W r J j (by omega) (by omega) e u v D I (d u (i D) v (k I) y)
lemma uu {V:Type*} [DecidableEq V] (G:SG V)(A S:FS V) (r:ℕ)(q:1<=r) (t:r<=A.card) (w:r+1<=(S \ A).card) (e:∀ a ∈ A,∀ s ∈ S,a≠s->G.Adj a s) (l:¬ CG (2*r+1) ⊑ G):Gᶜ.IsClique ((S \ A:FS V):Set V) :=by
 classical
 have i:Disjoint (S \ A) A :=D2 fun _ j=> (mem_sdiff.mp j).2
 have d:∀ x ∈ S \ A,∀ a ∈ A,G.Adj x a:=by
  intro x j a m;exact (e a m x (mem_sdiff.mp j).1 (fun h=>(mem_sdiff.mp j).2 (h ▸ m))).symm
 intro u y v n k;rw [compl_adj];refine ⟨k,?_⟩
 intro g;exact l ((cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr (rb G (S \ A) A r q i w t d u v y n g))
lemma vP {V:Type*} (G:SG V)(A S:FS V) (k:A⊆S)(j:S.card<=A.card+1) (d:∀ a ∈ A,∀ s ∈ S,a≠s->G.Adj a s):G.IsClique (S:Set V) :=by
 classical
 have g:(S \ A).card<=1:=by rw [card_sdiff,inter_eq_left.mpr k];omega
 intro u m v l e;by_cases h:u∈A
 · exact d u h v l e
 by_cases i:v∈A
 · exact (d v i u m e.symm).symm
 exact (e (card_le_one.mp g u (mem_sdiff.mpr ⟨m,h⟩) v (mem_sdiff.mpr ⟨l,i⟩))).elim
lemma vR {V:Type*} (G:SG V)(S T:FS V) (r:ℕ)(q:1<=r) (h:Disjoint S T)(m:r+1<=S.card) (l:r<=T.card) (d:∀ s ∈ S,∀ t ∈ T,Gᶜ.Adj s t)(j:¬ CG (2*r+1) ⊑ Gᶜ):G.IsClique (S:Set V) :=by
 classical
 intro u n v k i;by_contra g;have e:Gᶜ.Adj u v:=by rw [compl_adj];exact ⟨i,g⟩
 exact j ((cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr (rb Gᶜ S T r q h m l d u v n k e))
lemma uS {V:Type*} (G:SG V)(A S T:FS V) (r:ℕ)(q:1<=r) (l:A⊆S)(D:r<=A.card) (I:2*r+2<=S.card) (J:r-1<=T.card) (m:Disjoint S T)(i:∀ s ∈ S,∀ t ∈ T,Gᶜ.Adj s t) (e:∀ a ∈ A,∀ s ∈ S,a≠s->G.Adj a s) (k:¬ CG (2*r+1) ⊑ G) (j:¬ CG (2*r+1) ⊑ Gᶜ):False:=by
 classical
 by_cases g:r+1<=A.card
 · exact k ((cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr (qS G A S r q l g (by omega) e))
 have v:A.card=r:=by omega
 let X :=S \ A
 have H:r+2<=X.card:=by
  dsimp only [X];rw [card_sdiff,inter_eq_left.mpr l,v];omega
 have h:Gᶜ.IsClique (X:Set V) :=
  uu G A S r q D (show r +1<=X.card by omega) e k
 have w:Disjoint X T:=m.mono_left sdiff_subset
 have F:2*r+1<=(X ∪ T).card:=by
  rw [card_union_of_disjoint w];omega
 have d:∀ x ∈ X,∀ y ∈ X ∪ T,x≠y->Gᶜ.Adj x y:=by
  intro x C y n z;rcases mem_union.mp n with n | n
  · exact h C n z
  · exact i x (mem_sdiff.mp C).1 y n
 exact j ((cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr (qS Gᶜ X (X ∪ T) r q subset_union_left (by omega) F d))
lemma sE {V:Type*} [Fintype V] [DecidableEq V] (G:SG V)(A S T Z:FS V) (r:ℕ)(L:1<=r) (C:A⊆S)(N:r<=A.card) (U:r<=T.card) (j:∀ a ∈ A,∀ s ∈ S,a≠s->G.Adj a s) (e:Disjoint S T)(i:S ∪ T=univ) (R:3*r+2<=Fintype.card V) (K:Z.card<=1) (g:∀ s ∈ S \ Z,∀ t ∈ T \ Z,Gᶜ.Adj s t)(D:¬ CG (2*r+1) ⊑ G) (m:¬ CG (2*r+1) ⊑ Gᶜ):r<=(T \ Z).card:=by
 classical
 by_contra q;have v:=card_sdiff_add_card_inter T Z;have n:(T ∩ Z).card<=1:= (card_le_card inter_subset_right).trans K;have Q:T.card=r:=by omega
 have k:(T ∩ Z).Nonempty:=card_pos.mp (by omega)
 obtain ⟨z,I⟩ :=k
 have y:Z⊆T:=by
  intro x P;have M:x=z:=card_le_one.mp K x P z (mem_inter.mp I).2;exact M ▸ (mem_inter.mp I).1
 have F:Disjoint S Z:=e.mono_right y
 have l:S \ Z=S:=by
  ext s;constructor
  · exact fun h=>(mem_sdiff.mp h).1
  · intro J;exact mem_sdiff.mpr ⟨J,D1 F J⟩
 have H:S.card+T.card=Fintype.card V :=by
  rw [<- card_union_of_disjoint e,i,card_univ]
 have w:2*r+2<=S.card:=by omega
 have d:∀ s ∈ S,∀ t ∈ T \ Z,Gᶜ.Adj s t:=by simpa only [l] using g
 exact uS G A S (T \ Z) r L C N w (by omega) (e.mono_right sdiff_subset) d j D m
def uP {V:Type*} [Fintype V] [DecidableEq V] (G:SG V)(r:ℕ):Prop:= ∃ S T Z:FS V,Z.card<=1/\Disjoint S T/\S ∪ T=univ \ Z/\G.IsClique (S:Set V)/\G.IsClique (T:Set V)/\(∀ s ∈ S,∀ t ∈ T,Gᶜ.Adj s t)/\S.card<=2*r/\T.card<=2*r
lemma rX {V:Type*} (G:SG V)(S:FS V) (r:ℕ)(k:1<=r) (d:G.IsClique (S:Set V)) (g:¬ CG (2*r+1) ⊑ G):S.card<=2*r:=by
 classical
 by_contra h;exact g ((cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr (qS G S S r k Subset.rfl (by omega) (by omega) (fun _ j _ i e=> d j i e)))
lemma rC {V:Type*} [DecidableEq V] (G:SG V)(A S T Z:FS V) (r:ℕ)(C:1<=r) (q:A⊆S)(D:r<=A.card) (h:∀ a ∈ A,∀ s ∈ S,a≠s->G.Adj a s) (k:Disjoint S T)(x:Z.card<=1) (y:r<=(T \ Z).card) (e:∀ s ∈ S \ Z,∀ t ∈ T \ Z,Gᶜ.Adj s t)(j:¬ CG (2*r+1) ⊑ Gᶜ):G.IsClique ((S \ Z:FS V):Set V) :=by
 by_cases g:r+1<=(S \ Z).card
 · exact vR G (S \ Z) (T \ Z) r C (k.mono sdiff_subset sdiff_subset) g y e j
 · have l:=card_sdiff_add_card_inter S Z
   have m:(S ∩ Z).card<=1:= (card_le_card inter_subset_right).trans x;have i:S.card<=A.card+1:=by omega
   have d:=vP G A S q i h
   intro u z v w n;exact d (mem_sdiff.mp z).1 (mem_sdiff.mp w).1 n
lemma sH {V:Type*} [Fintype V] [DecidableEq V] (G:SG V)(r:ℕ) (M:4<=r) (K:3*r+2<=Fintype.card V) (H:rW G r)(y:¬ CG (2*r+1) ⊑ G) (m:¬ CG (2*r+1) ⊑ Gᶜ):uP G r:=by
 classical
 obtain ⟨A,B,J,z,q,P,L,n⟩ :=H;obtain ⟨S,T,g,e,D,F,k,j⟩:=yd G A B r (by omega) J z q P L n m
 obtain ⟨Z,I,C⟩ :=vt G A B S T r M D F z q k j g e (by omega) y
 have d:=sp G S T Z g C;have l:∀ t ∈ T \ Z,∀ s ∈ S \ Z,Gᶜ.Adj t s:= fun t Q s N=> (d s N t Q).symm
 have w:=sE G A S T Z r (by omega) D z (q.trans (card_le_card F)) k g e K I d y m
 have x:T ∪ S=univ:=by simpa only [union_comm] using e
 have v:=sE G B T S Z r (by omega) F q (z.trans (card_le_card D)) j g.symm x K I l y m
 have h:=rC G A S T Z r (by omega) D z k g I w d m
 have i:=rC G B T S Z r (by omega) F q j g.symm I v l m
 refine ⟨S \ Z,T \ Z,Z,I,g.mono sdiff_subset sdiff_subset,?_,h,i,d,rX G (S \ Z) r (by omega) h y,rX G (T \ Z) r (by omega) i y⟩
 rw [<- union_sdiff_distrib,e]
lemma wd:∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (r:ℕ),N₀<=r->4* (r+1)-(r+1)/100000<=Fintype.card V->(¬ CG (2*r+1) ⊑ G)->(¬ CG (2*r+1) ⊑ Gᶜ)->uP G r\/uP Gᶜ r :=by
 obtain ⟨j,e⟩ :=vr;refine ⟨max j 4,?_⟩
 intro V _ _ G _ r l k g d
 have i:3*r+2<=Fintype.card V :=by
  have hdiv:=Nat.div_le_self (r+1) 100000;omega
 rcases e G r (by omega) k g d with h | h
 · exact Or.inl (sH G r (by omega) i h g d)
 · right
   apply sH Gᶜ r (by omega) i h d
   simpa only [compl_compl] using g
structure v8 {V:Type*} [DecidableEq V]
 (c:q4 V) (A:FS V) (r:ℕ) (j k:Fin 3) where
 first:FS V
 second:FS V
 first_subset:first⊆A
 second_subset:second⊆A
 disjoint:Disjoint first second
 card_cover:A.card<=first.card+second.card+1
 first_clique:(c.graph j).IsClique (first:Set V)
 second_clique:(c.graph j).IsClique (second:Set V)
 cross:∀ u ∈ first,∀ v ∈ second,(c.graph k).Adj u v
 first_card_le:first.card<=2*r
 second_card_le:second.card<=2*r
lemma q4.w8 {V:Type*} (c:q4 V)(A:Set V) (i j k:Fin 3)(e:∀ a:Fin 3,a=i\/a=j\/a=k) (m:j≠k)(q:∀ u ∈ A,∀ v ∈ A,¬ (c.graph i).Adj u v):((c.graph j).induce A)ᶜ= (c.graph k).induce A :=by
 ext u v;constructor
 · rintro ⟨h,n⟩
   have d:u.val≠v.val:=fun l=> h (Subtype.ext l)
   refine ⟨d,?_⟩;rcases e (c.colour u.val v.val) with r | s | g
   · exact (q u.val u.property v.val v.property ⟨d,r⟩).elim
   · exact (n ⟨d,s⟩).elim
   · exact g
 · intro g
   refine ⟨fun l=> g.1 (CA Subtype.val l),?_⟩
   intro n;exact m (n.2.symm.trans g.2)
lemma sj {V:Type*} [DecidableEq V] (c:q4 V)(A:FS V) (r:ℕ)(j k:Fin 3) (n:((c.graph j).induce (A:Set V))ᶜ= (c.graph k).induce (A:Set V)) (h:uP ((c.graph j).induce (A:Set V)) r):Nonempty (v8 c A r j k) :=by
 classical
 obtain ⟨S,T,Z,N,g,q,K,L,e,x,I⟩ :=h;let f:(A:Set V) ↪ V:= ⟨Subtype.val,Subtype.val_injective⟩
 have hsub (U:FS (A:Set V)):U.map f⊆A :=by
  intro u i;obtain ⟨v,_,rfl⟩ :=mem_map.mp i;exact v.property
 have d (U:FS (A:Set V)) (M:((c.graph j).induce (A:Set V)).IsClique (U:Set (A:Set V))):(c.graph j).IsClique ((U.map f:FS V):Set V) :=by
  intro u i v w F;obtain ⟨u',H,rfl⟩ :=mem_map.mp i;obtain ⟨v',C,rfl⟩ :=mem_map.mp w;exact M H C (fun l=> F (CA f l))
 refine ⟨{
  first:=S.map f
  second:=T.map f
  first_subset:=hsub S
  second_subset:=hsub T
  disjoint:= ?_
  card_cover:= ?_
  first_clique:=d S K
  second_clique:=d T L
  cross:= ?_
  first_card_le:=by simpa only [card_map] using x
  second_card_le:=by simpa only [card_map] using I}⟩
 · apply D2
   intro u i w;obtain ⟨s,D,y⟩ :=mem_map.mp i;obtain ⟨t,J,z⟩ :=mem_map.mp w;exact D1 g D ((f.injective (z.trans y.symm)) ▸ J)
 · rw [card_map,card_map]
   have l:=CA card q;rw [card_union_of_disjoint g,card_sdiff,inter_univ,card_univ] at l
   have m:Fintype.card (A:Set V)=A.card:=by
    calc
     _= (A:Set V).ncard:=Nat.card_eq_fintype_card.symm
     _=A.card:=Set.ncard_coe_finset A
   rw [m] at l;omega
 · intro u i v w;obtain ⟨s,D,rfl⟩ :=mem_map.mp i;obtain ⟨t,J,rfl⟩ :=mem_map.mp w;have l:=e s D t J;rw [n] at l;exact l
lemma vs:∃ d:ℕ,∀ {V:Type*} [DecidableEq V] (c:q4 V)(A:FS V) (r:ℕ)(i:Fin 3),d<=r->4* (r+1)-(r+1)/100000<=A.card->(∀ u ∈ A,∀ v ∈ A,¬ (c.graph i).Adj u v)->(∀ a,¬ CG (2*r+1) ⊑ c.graph a)->∃ j k:Fin 3,j≠i/\k≠i/\j≠k/\Nonempty (v8 c A r j k) :=by
 obtain ⟨d,g⟩ :=wd;refine ⟨d,?_⟩
 intro V _ c A r i F I n z
 classical
 have e:∀ i:Fin 3,∃ j k:Fin 3,j≠i/\k≠i/\j≠k/\∀ a:Fin 3,a=i\/a=j\/a=k:=by decide
 obtain ⟨j,k,q,s,l,m⟩ :=e i;have t:=c.w8 (A:Set V) i j k m l n;have D (a:Fin 3):¬ CG (2*r+1) ⊑ (c.graph a).induce (A:Set V):=fun H=> z a (H.trans ⟨Copy.induce _ _⟩)
 have h:Fintype.card (A:Set V)=A.card:=by
  calc
   _= (A:Set V).ncard:=Nat.card_eq_fintype_card.symm
   _=A.card:=Set.ncard_coe_finset A
 have C:4* (r+1)-(r+1)/100000<=Fintype.card (A:Set V) :=by rwa [h]
 have x:¬ CG (2*r+1) ⊑ ((c.graph j).induce (A:Set V))ᶜ:=by
  rw [t];exact D k
 rcases g ((c.graph j).induce (A:Set V)) r F C (D j) x with w | w
 · exact ⟨j,k,q,s,l,sj c A r j k t w⟩
 · have y:((c.graph k).induce (A:Set V))ᶜ= (c.graph j).induce (A:Set V) :=by
    rw [<- t,compl_compl]
   rw [t] at w;exact ⟨k,j,s,q,l.symm,sj c A r k j y w⟩
structure sW {V:Type*} [DecidableEq V]
 (c:q4 V) (p:q1) (A:FS V) (L d:ℕ) where
 direction:Fin 3
 cores:Fin 4->FS V
 subprofile:∀ l,qc l∈q0 p->q0 (qu l direction)⊆q0 p
 subset:∀ l,qc l∈q0 p->cores l⊆A
 large:∀ l,qc l∈q0 p->L<=(cores l).card
 profile_disjoint:∀ l m,l≠m->qc l∈q0 p->qc m∈q0 p->Disjoint (q0 (qu l direction)) (q0 (qu m direction))
 core_disjoint:∀ l m,l≠m->qc l∈q0 p->qc m∈q0 p->Disjoint (cores l) (cores m)
 dense:∀ l m,qc l∈q0 p->qc m∈q0 p->∀ i,q5 (qu l direction) (qu m direction) i->qi (c.graph i) (cores l) (cores m) d
lemma xL {V:Type*} [DecidableEq V] (c:q4 V)(p:q1) (A:FS V)(L d:ℕ) (r:q3 p =1) (s:L<=A.card):Nonempty (sW c p A L d) :=by
 obtain ⟨a,w⟩ :=tm p r;have e (l m:Fin 4) (g:qc l∈q0 p) (j:qc m∈q0 p):l=m:= xu p l m r g j
 refine ⟨{
  direction:=a
  cores:=fun _=>A
  subprofile:=fun l g=> by rw [w l g]
  subset:=fun _ _=> Subset.rfl
  large:=fun _ _=> s
  profile_disjoint:=fun l m k g j=> (k (e l m g j)).elim
  core_disjoint:=fun l m k g j=> (k (e l m g j)).elim
  dense:= ?_}⟩
 intro l m g j i n;have q:=e l m g j;subst m;have v:=re _ _ i n.1
 have t:q0 (qu l a)=∅ :=by
  simpa only [disjoint_self,bot_eq_empty] using v
 have h:=r5 l a;rw [t] at h;exact (notMem_empty _ h).elim
def bC {V:Type*} (S T:FS V)(b:Bool):FS V :=if b then T else S
lemma b5 {V:Type*} {S T A:FS V} (e:S⊆A)(d:T⊆A) (b:Bool):bC S T b⊆A :=by cases b <;> assumption
lemma aL {V:Type*} {S T:FS V} {L:ℕ} (e:L<=S.card) (d:L<=T.card) (b:Bool):L<=(bC S T b).card:=by cases b <;> assumption
lemma aG {V:Type*} {S T:FS V} (d:Disjoint S T)(a b:Bool) (e:a≠b):Disjoint (bC S T a) (bC S T b) :=by
 cases a <;> cases b
 · exact (e rfl).elim
 · exact d
 · exact d.symm
 · exact (e rfl).elim
lemma d5 {V:Type*} {G:SG V} {S T:FS V} (d:∀ u ∈ S,∀ v ∈ T,G.Adj u v)(a b:Bool) (e:a≠b):∀ u ∈ bC S T a,∀ v ∈ bC S T b,G.Adj u v:=by
 cases a <;> cases b
 · exact (e rfl).elim
 · exact d
 · exact fun u g v h=> (d v h u g).symm
 · exact (e rfl).elim
lemma x0 {V:Type*} [DecidableEq V] (G:SG V) [DecidableRel G.Adj] (S T:FS V)(d:ℕ) (e:∀ u ∈ S,∀ v ∈ T,G.Adj u v):qi G S T d:=by
 constructor
 · intro u j
   have i:T.filter (fun v=>¬ G.Adj u v)=∅ :=by
    apply filter_eq_empty_iff.mpr
    intro v g h;exact h (e u j v g)
   rw [i,card_empty];exact Nat.zero_le _
 · intro v g
   have i:S.filter (fun u=>¬ G.Adj v u)=∅ :=by
    apply filter_eq_empty_iff.mpr
    intro u j h;exact h (e u j v g).symm
   rw [i,card_empty];exact Nat.zero_le _
lemma xS {V:Type*} [DecidableEq V] (c:q4 V)(A:FS V) (r L d:ℕ)(i j k:Fin 3) (b:Bool)(t:j≠i) (w:k≠i)(x:j≠k) (e:v8 c A r j k)(F:L<=e.first.card) (D:L<=e.second.card):Nonempty (sW c (cF i b) A L d) :=by
 let B:Fin 4->FS V :=fun l=>bC e.first e.second (qc l k)
 have h (l m:Fin 4) (g:l≠m) (n:qc l∈q0 (cF i b)) (q:qc m∈q0 (cF i b)):qc l k≠qc m k:=yv i k b l m w g n q
 refine ⟨{
  direction:=j
  cores:=B
  subprofile:=fun l n=> zw i j b l t n
  subset:=fun l _=> b5 e.first_subset e.second_subset _
  large:=fun l _=> aL F D _
  profile_disjoint:=fun l m g n q=> xv i j b l m t g n q
  core_disjoint:=fun l m g n q=> aG e.disjoint _ _ (h l m g n q)
  dense:= ?_}⟩
 intro l m n q z s;have H:=xM i j k z b l m t w x n q s;subst z
 have g:l≠m:=by
  intro C;subst m;have v:=re _ _ k s.1
  have C:q0 (qu l j)=∅ :=by
   simpa only [disjoint_self,bot_eq_empty] using v
  have y:=r5 l j;rw [C] at y;exact notMem_empty _ y
 apply x0;exact d5 e.cross _ _ (h l m g n q)
noncomputable def qC:O:=1/100000000
lemma y8:0 < qC:=by norm_num [qC]
lemma vL (r d M:ℕ)(η:O) (j:10<=r) (g:η<=1/100) (k:(d:O)<=η* (2*r+1)) (l:(1-η)*(2*r+1)<=(M:O)):r+2*d+3<=M:=by
 have i:(10:O)<=r:=by exact_mod_cast j
 have e:=mul_le_mul_of_nonneg_right g (by positivity:(0:O)<=2*r+1)
 have h:(r:O)+2*d+3<=M:=by nlinarith
 exact_mod_cast h
lemma wx (r M:ℕ)(h:1000000<=r) (e:(2-qC)*(2*r+1)<=(M:O)):4* (r+1)-(r+1)/100000<=M:=by
 have d:(199999999:O)*(2*r+1)<=100000000*M:=by
  dsimp only [qC] at e;nlinarith
 have g:199999999* (2*r+1)<=100000000*M:=by exact_mod_cast d
 omega
lemma wG:∃ R₀:ℕ,∀ {V:Type*} [DecidableEq V] (c:q4 V)(r:ℕ),R₀<=r->(∀ i,¬ CG (2*r+1) ⊑ c.graph i)->∀ h:rv c (2*r+1) qC,∀ p,0 < h.weight p->Nonempty (sW c p (h.sets p) (r+2*h.defect+3) h.defect) :=by
 obtain ⟨n,y⟩ :=vs;refine ⟨max n 1000000,?_⟩
 intro V _ c r H w h p I;have l:1000000<=r:= (le_max_right _ _).trans H;have q:n<=r:= (le_max_left _ _).trans H;have m:qC<=1/100:=by norm_num [qC]
 have D:(h.defect:O)<=qC* (2*r+1) :=by
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using h.defect_le
 have x:=h.size_lower p;push_cast at x;rcases h.tiling.normalized p I with ⟨e,g⟩ | ⟨e,g⟩
 · rw [g] at x;exact xL c p (h.sets p) _ h.defect e (vL r h.defect _ _ (by omega) m D x)
 · obtain ⟨i,b,rfl⟩:=(u1 p).mp e
   rw [g] at x;have s:=wx r _ l x;have t:=h.t8 (by omega) m w i b I
   obtain ⟨j,k,z,C,F,⟨d⟩⟩ :=y c (h.sets (cF i b)) r i q s t w
   have K:(1-qC)*(2*r+1)<=(d.first.card:O) :=by
    have v:((h.sets (cF i b)).card:O)<=d.first.card+d.second.card+1:=by
     exact_mod_cast d.card_cover
    have M:(d.second.card:O)<=2*r:=by exact_mod_cast d.second_card_le
    nlinarith
   have L:(1-qC)*(2*r+1)<=(d.second.card:O) :=by
    have v:((h.sets (cF i b)).card:O)<=d.first.card+d.second.card+1:=by
     exact_mod_cast d.card_cover
    have J:(d.first.card:O)<=2*r:=by exact_mod_cast d.first_card_le
    nlinarith
   exact xS c _ r _ h.defect i j k b z C F d (vL r h.defect _ _ (by omega) m D K) (vL r h.defect _ _ (by omega) m D L)
structure yA {V:Type*} [DecidableEq V]
 (c:q4 V) (L d:ℕ) where
 profiles:Fin 4->q1
 cores:Fin 4->FS V
 dimension:∀ l,q3 (profiles l)=1
 profile_disjoint:∀ l m,l≠m->Disjoint (q0 (profiles l)) (q0 (profiles m))
 core_disjoint:∀ l m,l≠m->Disjoint (cores l) (cores m)
 large:∀ l,L<=(cores l).card
 dense:∀ l m i,q5 (profiles l) (profiles m) i->qi (c.graph i) (cores l) (cores m) d
lemma ww {V:Type*} [DecidableEq V] {c:q4 V} {n L:ℕ} {η:O} (h:rv c n η)(v:∀ p,0 < h.weight p->Nonempty (sW c p (h.sets p) L h.defect)):Nonempty (yA c L h.defect) :=by
 classical
 have y (l:Fin 4):∃ p:q1,0 < h.weight p/\qc l∈q0 p :=by
  have z:qc l∈(qj h.weight).biUnion q0:=by
   rw [h.tiling.cover h.admissible];exact mem_univ _
  obtain ⟨p,x,j⟩ :=mem_biUnion.mp z;exact ⟨p,(mem_filter.mp x).2,j⟩
 choose p x j using y
 let P:Fin 4->{q:q1//0 < h.weight q} :=fun l=>⟨p l,x l⟩
 let R (q:{q:q1//0 < h.weight q}):sW c q.val (h.sets q.val) L h.defect:= Classical.choice (v q.val q.property);have d (l:Fin 4):qc l∈q0 (P l).val:=j l;have g (l m:Fin 4) (w:P l≠P m):(P l).val≠(P m).val:= fun e=> w (Subtype.ext e)
 refine ⟨{
  profiles:=fun l=>qu l (R (P l)).direction
  cores:=fun l=>(R (P l)).cores l
  dimension:=fun l=>yh l _
  profile_disjoint:= ?_
  core_disjoint:= ?_
  large:=fun l=>(R (P l)).large l (d l)
  dense:= ?_}⟩
 · intro l m s
   by_cases e:P l=P m
   · have t:qc m∈q0 (P l).val:=by rw [e];exact d m
     rw [<- e];exact (R (P l)).profile_disjoint l m s (d l) t
   · exact (h.tiling.disjoint _ _ (g l m e) (P l).property (P m).property).mono ((R (P l)).subprofile l (d l)) ((R (P m)).subprofile m (d m))
 · intro l m s
   by_cases e:P l=P m
   · have t:qc m∈q0 (P l).val:=by rw [e];exact d m
     rw [<- e];exact (R (P l)).core_disjoint l m s (d l) t
   · exact (h.disjoint _ _ (g l m e)).mono ((R (P l)).subset l (d l)) ((R (P m)).subset m (d m))
 · intro l m i k
   by_cases e:P l=P m
   · have t:qc m∈q0 (P l).val:=by rw [e];exact d m
     rw [<- e] at k ⊢;exact (R (P l)).dense l m (d l) t i k
   · have r:=wp (P l).val (P m).val _ _ i (h.tiling.disjoint _ _ (g l m e) (P l).property (P m).property) ((R (P l)).subprofile l (d l)) ((R (P m)).subprofile m (d m)) k;exact (h.dense _ _ i r).mono ((R (P l)).subset l (d l)) ((R (P m)).subset m (d m))
lemma zk:∀ d:Fin 4->Fin 3,Function.Injective (fun i=>vI i (d i))->d= ![0,0,0,0]\/d= ![0,1,1,0]\/d= ![2,0,2,0]\/d= ![1,0,0,1]\/d= ![1,1,1,1]\/d= ![2,2,1,1]\/d= ![0,2,0,2]\/d= ![1,1,2,2]\/d= ![2,2,2,2] :=by decide
lemma xr (d:Fin 4->Fin 3) (e:Function.Injective (fun i=>vI i (d i))):∃ (s:Fin 4->Fin 4) (k:Fin 3->Fin 3),Function.Injective s/\Function.Injective k/\(uf (fun i=>qu (s i) (d (s i))) k\/uq (fun i=>qu (s i) (d (s i))) k) :=by
 rcases zk d e with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
 · refine ⟨![0,2,3,1],![1,2,0],by decide,by decide,?_⟩
   exact Or.inl (by decide)
 · refine ⟨![0,3,1,2],![2,1,0],by decide,by decide,?_⟩
   exact Or.inr (by decide)
 · refine ⟨![0,2,1,3],![1,0,2],by decide,by decide,?_⟩
   exact Or.inr (by decide)
 · refine ⟨![0,3,1,2],![2,0,1],by decide,by decide,?_⟩
   exact Or.inr (by decide)
 · refine ⟨![0,1,3,2],![0,2,1],by decide,by decide,?_⟩
   exact Or.inl (by decide)
 · refine ⟨![0,1,2,3],![0,1,2],by decide,by decide,?_⟩
   exact Or.inr (by decide)
 · refine ⟨![0,2,1,3],![1,2,0],by decide,by decide,?_⟩
   exact Or.inr (by decide)
 · refine ⟨![0,1,2,3],![0,2,1],by decide,by decide,?_⟩
   exact Or.inr (by decide)
 · refine ⟨![0,1,2,3],![0,1,2],by decide,by decide,?_⟩
   exact Or.inl (by decide)
lemma uO (p:Fin 4->q1) (q:∀ i,q3 (p i)=1) (l:∀ i j,i≠j->Disjoint (q0 (p i)) (q0 (p j))):∃ (s:Fin 4->Fin 4) (k:Fin 3->Fin 3),Function.Injective s/\Function.Injective k/\(uf (fun i=>p (s i)) k\/uq (fun i=>p (s i)) k) :=by
 classical
 choose a b hab using fun i=>tq (p i) (q i)
 have x:Function.Injective a :=by
  intro i j h;by_contra n;have w:=l i j n
  have r:qc (a i)∈q0 (p i) :=by
   rw [hab i];exact r5 (a i) (b i)
  have v:qc (a i)∈q0 (p j) :=by
   rw [hab j,h];exact r5 (a j) (b j)
  exact (D1 w r) v
 let e:Fin 4 ≃ Fin 4 :=Equiv.ofBijective a ⟨x,(Finite.injective_iff_surjective).mp x⟩;let d:Fin 4->Fin 3 :=fun i=>b (e.symm i)
 have g (i:Fin 4):p (e.symm i)=qu i (d i) :=by
  rw [hab (e.symm i)];have r:a (e.symm i)=i:=e.apply_symm_apply i;rw [r]
 have m:Function.Injective (fun i=>vI i (d i)) :=by
  intro i j h;change vI i (d i)=vI j (d j) at h;by_contra n;have w:=l (e.symm i) (e.symm j) (e.symm.injective.ne n)
  have r:vI i (d i)∈q0 (p (e.symm i)) :=by
   rw [g i];exact un i (d i)
  have v:vI i (d i)∈q0 (p (e.symm j)) :=by
   rw [g j,h];exact un j (d j)
  exact (D1 w r) v
 obtain ⟨s,k,y,z,C⟩ :=xr d m;refine ⟨fun i=>e.symm (s i),k,e.symm.injective.comp y,z,?_⟩
 have t:(fun i=>p (e.symm (s i)))=(fun i=>qu (s i) (d (s i))) :=by
  funext i;exact g (s i)
 rwa [t]
def q4.relabel {V:Type*} (c:q4 V) (e:Fin 3 ≃ Fin 3):q4 V where
 colour u v:=e.symm (c.colour u v)
 symm u v:=CA e.symm (c.symm u v)
lemma q4.dZ {V:Type*} (c:q4 V)(e:Fin 3 ≃ Fin 3) (i:Fin 3):(c.relabel e).graph i =c.graph (e i) :=by ext u v;simp only [e4,relabel,Equiv.symm_apply_eq]
lemma vD {V I:Type*} [Fintype V] [Fintype I] (G:I->SG V) (A:I->FS V) (r:ℕ)(y:1<=r) (w:∀ i,r+1<=(A i).card) (d:∀ i,(G i).IsClique (A i:Set V)) (n:∀ i,¬ CG (2*r+1) ⊑ G i) (e:∀ x:V,∃ i,x∈A i\/∀ a ∈ A i,(G i).Adj x a):Fintype.card V<=2 *r*Fintype.card I :=by
 classical
 let S:I->FS V :=fun i=>univ.filter (fun x=>x∈A i\/∀ a ∈ A i,(G i).Adj x a)
 have m (i:I):A i⊆S i:=by
  intro x l;exact mem_filter.mpr ⟨mem_univ _,Or.inl l⟩
 have j (i:I):∀ a ∈ A i,∀ x ∈ S i,a≠x->(G i).Adj a x:=by
  intro a t x l s;rcases (mem_filter.mp l).2 with q | l
  · exact d i t q s
  · exact (l a t).symm
 have k (i:I):(S i).card<=2*r:=by
  by_contra h;exact n i ((cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr (qS (G i) (A i) (S i) r y (m i) (w i) (by omega) (j i)))
 have g:univ.biUnion S=(univ:FS V) :=by
  apply eq_univ_iff_forall.mpr
  intro x;obtain ⟨i,v⟩ :=e x;exact mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨mem_univ _,v⟩⟩
 calc
  Fintype.card V=(univ.biUnion S).card:=by rw [g,card_univ]
  _<=∑ i,(S i).card:=card_biUnion_le
  _<=∑ _i:I,2*r:=sum_le_sum fun i _=> k i
  _=2*r*Fintype.card I :=by simp [Nat.mul_comm]
structure rM {V:Type*} [DecidableEq V]
 (c:q4 V) (A:Fin 4->FS V) (d:ℕ):Prop where
 disjoint:∀ i j,i≠j->Disjoint (A i) (A j)
 red02:qi (c.graph 0) (A 0) (A 2) d
 red03:qi (c.graph 0) (A 0) (A 3) d
 red12:qi (c.graph 0) (A 1) (A 2) d
 red13:qi (c.graph 0) (A 1) (A 3) d
 blue01:qi (c.graph 1) (A 0) (A 1) d
 green23:qi (c.graph 2) (A 2) (A 3) d
def qM (i:Fin 4):Fin 3 :=if i.val < 2 then 2 else 1
lemma y3:∀ k:Fin 4->Fin 3,k 0≠2->k 1≠2->k 2≠1->k 3≠1->(k 0 =0/\k 2=0)\/(k 0 =0/\k 3=0)\/(k 1 =0/\k 2=0)\/(k 1 =0/\k 3=0)\/(k 0 =1/\k 1=1)\/(k 2 =2/\k 3=2) :=by decide
lemma rM.zP {V:Type*} [DecidableEq V] {c:q4 V} {A:Fin 4->FS V} {d:ℕ} (h:rM c A d)(r:ℕ) (t:2<=r) (g:∀ i,r+2*d+1<=(A i).card) (m:∀ k,¬ CG (2*r+1) ⊑ c.graph k):∀ i,(c.graph (qM i)).IsClique (A i:Set V) :=by
 have e (i j:Fin 4) (k:Fin 3) (l:i≠j) (q:qi (c.graph k) (A i) (A j) d):∀ u ∈ A i,∀ v ∈ A i,¬ (c.graph k).Adj u v:=
  ro (c.graph k) (A i) (A j) r d (by omega) (h.disjoint i j l) q (g i) (by have s:=g j;omega) (m k)
 intro i;fin_cases i
 · apply c.r7 (A 0) 0 1 2 sN
   · exact e 0 2 0 (by decide) h.red02
   · exact e 0 1 1 (by decide) h.blue01
 · apply c.r7 (A 1) 0 1 2 sN
   · exact e 1 2 0 (by decide) h.red12
   · exact e 1 0 1 (by decide) h.blue01.symm
 · apply c.r7 (A 2) 0 2 1 (fun k=>by
    have n:=sN k;tauto)
   · exact e 2 0 0 (by decide) h.red02.symm
   · exact e 2 3 2 (by decide) h.green23
 · apply c.r7 (A 3) 0 2 1 (fun k=>by
    have n:=sN k;tauto)
   · exact e 3 0 0 (by decide) h.red03.symm
   · exact e 3 2 2 (by decide) h.green23.symm
lemma rM.u4 {V:Type*} [DecidableEq V] {c:q4 V} {A:Fin 4->FS V} {d:ℕ} (h:rM c A d)(r:ℕ) (D:2<=r) (m:∀ i,r+2*d+1<=(A i).card) (t:∀ k,¬ CG (2*r+1) ⊑ c.graph k) (x:V)(s:∀ i,x ∉ A i):∃ i,∀ a ∈ A i,(c.graph (qM i)).Adj x a:=by
 classical
 by_contra hn;push Not at hn;choose u hu hbad using hn
 have n (i:Fin 4):x≠u i :=by
  intro l;exact s i (l.symm ▸ hu i)
 have g (i:Fin 4):c.colour x (u i)≠qM i:=fun l=> hbad i ⟨n i,l⟩
 have e (i j:Fin 4) (k:Fin 3) (q:i≠j) (C:qi (c.graph k) (A i) (A j) d):¬ (c.colour x (u i)=k/\c.colour x (u j)=k) :=by
  intro l;apply rG (c.graph k) (A i) (A j) r d D (h.disjoint i j q) C (by have F:=m i;omega) (by have H:=m j;omega) (t k) x (s i) (s j) (u i) (u j) (hu i) (hu j)
  exact ⟨⟨n i,l.1⟩,⟨n j,l.2⟩⟩
 have v:c.colour x (u 0)≠2:=by simpa [qM] using g 0
 have w:c.colour x (u 1)≠2:=by simpa [qM] using g 1
 have z:c.colour x (u 2)≠1:=by simpa [qM] using g 2
 have y:c.colour x (u 3)≠1:=by simpa [qM] using g 3
 rcases y3 (fun i=>c.colour x (u i)) v w z y with
  l | l | l | l | l | l
 · exact e 0 2 0 (by decide) h.red02 l
 · exact e 0 3 0 (by decide) h.red03 l
 · exact e 1 2 0 (by decide) h.red12 l
 · exact e 1 3 0 (by decide) h.red13 l
 · exact e 0 1 1 (by decide) h.blue01 l
 · exact e 2 3 2 (by decide) h.green23 l
lemma uo {V:Type*} [Fintype V] [DecidableEq V] (c:q4 V)(A:Fin 4->FS V) (r d:ℕ)(s:2<=r) (w:8*r < Fintype.card V) (h:rM c A d)(e:∀ i,r+2*d+1<=(A i).card):∃ k,CG (2*r+1) ⊑ c.graph k :=by
 classical
 by_contra hn;have m:∀ k,¬ CG (2*r+1) ⊑ c.graph k :=fun k t=> hn ⟨k,t⟩
 have g:=h.zP r s e m
 have j:∀ x:V,∃ i,x∈A i\/∀ a ∈ A i,(c.graph (qM i)).Adj x a:=by
  intro x;by_cases q:∃ i,x∈A i
  · obtain ⟨i,n⟩ :=q;exact ⟨i,Or.inl n⟩
  · have v:∀ i,x ∉ A i:=fun i n=> q ⟨i,n⟩
    obtain ⟨i,n⟩ :=h.u4 r s e m x v;exact ⟨i,Or.inr n⟩
 have l:=vD (fun i=>c.graph (qM i)) A r (by omega) (fun i=>by have n:=e i;omega) g (fun i=>m (qM i)) j
 simp only [Fintype.card_fin] at l;omega
lemma ue {V:Type*} {G:SG V} {a a' b b' x:V} (X Y:FS V)(l:Disjoint X Y) (s:x ∉ X)(t:x ∉ Y) (D:b'∈Y)(p:G.Walk a a') (q:G.Walk b' b)(K:p.IsPath) (I:q.IsPath)(L:1<=p.length) (j:∀ z ∈ p.support,z∈X)(F:∀ z ∈ q.support,z∈Y) (e:G.Adj x a)(w:G.Adj x b) (H:G.Adj a' b'):∃ (v:V)(c:G.Walk v v),c.IsCycle/\c.length=p.length+q.length+3:=by
 classical
 have n:x ∉ p.support:=fun h=>s (j x h)
 have y:(Walk.cons e p).IsPath:= (Walk.cons_isPath_iff _ _).mpr ⟨K,n⟩
 have g:Disjoint (insert x X) Y :=by
  apply D2
  intro z d k;rcases mem_insert.mp d with r | C
  · exact t (r ▸ k)
  · exact (D1 l C) k
 have m:∀ z ∈ (Walk.cons e p).support,z∈insert x X:=by
  intro z d;rw [Walk.support_cons,List.mem_cons] at d;rcases d with d | d
  · exact mem_insert.mpr (Or.inl d)
  · exact mem_insert_of_mem (j z d)
 obtain ⟨v,c,J,i⟩ :=ri (insert x X) Y g D (Walk.cons e p) q y I (by rw [Walk.length_cons];omega) m F w H
 exact ⟨v,c,J,by rw [Walk.length_cons] at i;omega⟩
lemma rm {V:Type*} [DecidableEq V] (c:q4 V)(A:Fin 4->FS V) (r d:ℕ)(hr:4<=r) (g:∀ i j,i≠j->Disjoint (A i) (A j)) (e:∀ i,r+2*d+1<=(A i).card) (m:qi (c.graph 0) (A 0) (A 2) d) (l:qi (c.graph 0) (A 1) (A 3) d) (s:∀ b ∈ A 1,∀ z ∈ A 2,¬ (c.graph 2).Adj b z) (x:V)(y:∀ i,x ∉ A i) (u:Fin 4->V) (F:∀ i,u i∈A i)(T:(c.graph 0).Adj x (u 0)) (U:(c.graph 0).Adj x (u 3)) (W:(c.graph 1).Adj x (u 1)) (X:(c.graph 1).Adj x (u 2)):CG (2*r+1) ⊑ c.graph 0\/CG (2*r+1) ⊑ c.graph 1 :=by
 classical
 by_cases D:∃ b ∈ A 1,∃ z ∈ A 2,(c.graph 0).Adj b z
 · obtain ⟨b,t,z,C,Q⟩ :=D
   obtain ⟨p,Z,K,P⟩ :=rt (c.graph 0) (r-2) d (by omega) (A 0) (A 2) (g 0 2 (by decide)) m (by have h :=e 0;omega) (by have h :=e 2;omega) (u 0) z (F 0) C
   obtain ⟨q,R,N,H⟩ :=rt (c.graph 0) 2 d (by decide) (A 1) (A 3) (g 1 3 (by decide)) l (by have h :=e 1;omega) (by have h :=e 3;omega) b (u 3) t (F 3)
   have M:Disjoint (A 0 ∪ A 2) (A 1 ∪ A 3) :=by
    rw [disjoint_union_left,disjoint_union_right,disjoint_union_right];exact ⟨⟨g 0 1 (by decide),g 0 3 (by decide)⟩,⟨g 2 1 (by decide),g 2 3 (by decide)⟩⟩
   have I:x ∉ A 0 ∪ A 2:=by simp only [mem_union,not_or];exact ⟨y 0,y 2⟩
   have J:x ∉ A 1 ∪ A 3:=by simp only [mem_union,not_or];exact ⟨y 1,y 3⟩
   obtain ⟨v,w,Y,L⟩ :=ue (A 0 ∪ A 2) (A 1 ∪ A 3) M I J (mem_union_left _ t) p q Z R (by omega) P H T U Q.symm
   left;exact (cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr ⟨v,w,Y,by omega⟩
 · have n:∀ b ∈ A 1,∀ z ∈ A 2,(c.graph 1).Adj b z:=by
    intro b t z C;have k:b≠z:=fun h=>(Finset.disjoint_left.mp (g 1 2 (by decide)) t) (h ▸ C)
    rcases sN (c.colour b z) with h | h | h
    · exact (D ⟨b,t,z,C,⟨k,h⟩⟩).elim
    · exact ⟨k,h⟩
    · exact (s b t z C ⟨k,h⟩).elim
   right;exact (cycleGraph_isContained_iff (by omega:2 < 2*r+1)).mpr (rx (c.graph 1) (A 1) (A 2) r (by omega) (g 1 2 (by decide)) (by have h :=e 1;omega) (by have h :=e 2;omega) n x (u 1) (u 2) (y 1) (y 2) (F 1) (F 2) W X)
structure FP {V:Type*} [DecidableEq V]
 (c:q4 V) (A:Fin 4->FS V) (d:ℕ):Prop where
 disjoint:∀ i j,i≠j->Disjoint (A i) (A j)
 red02:qi (c.graph 0) (A 0) (A 2) d
 red13:qi (c.graph 0) (A 1) (A 3) d
 blue01:qi (c.graph 1) (A 0) (A 1) d
 blue23:qi (c.graph 1) (A 2) (A 3) d
structure rZ {V:Type*} [DecidableEq V]
 (c:q4 V) (A:Fin 4->FS V) (d:ℕ):Prop
 extends FP c A d where
 noGreen03:∀ a ∈ A 0,∀ b ∈ A 3,¬ (c.graph 2).Adj a b
 noGreen12:∀ a ∈ A 1,∀ b ∈ A 2,¬ (c.graph 2).Adj a b
lemma FP.zP {V:Type*} [DecidableEq V] {c:q4 V} {A:Fin 4->FS V} {d:ℕ} (h:FP c A d)(r:ℕ) (s:2<=r) (g:∀ i,r+2*d+1<=(A i).card) (m:∀ k,¬ CG (2*r+1) ⊑ c.graph k):∀ i,(c.graph 2).IsClique (A i:Set V) :=by
 have e (i j:Fin 4) (k:Fin 3) (l:i≠j) (n:qi (c.graph k) (A i) (A j) d):∀ u ∈ A i,∀ v ∈ A i,¬ (c.graph k).Adj u v:=
  ro (c.graph k) (A i) (A j) r d (by omega) (h.disjoint i j l) n (g i) (by have q:=g j;omega) (m k)
 intro i;apply c.r7 (A i) 0 1 2 sN
 · fin_cases i
   · exact e 0 2 0 (by decide) h.red02
   · exact e 1 3 0 (by decide) h.red13
   · exact e 2 0 0 (by decide) h.red02.symm
   · exact e 3 1 0 (by decide) h.red13.symm
 · fin_cases i
   · exact e 0 1 1 (by decide) h.blue01
   · exact e 1 0 1 (by decide) h.blue01.symm
   · exact e 2 3 1 (by decide) h.blue23
   · exact e 3 2 1 (by decide) h.blue23.symm
lemma t6:∀ k:Fin 4->Fin 3,(∀ i,k i≠2)->(k 0 =0/\k 2=0)\/(k 1 =0/\k 3=0)\/(k 0 =1/\k 1=1)\/(k 2 =1/\k 3=1)\/(k 0 =0/\k 1=1/\k 2=1/\k 3=0)\/(k 0 =1/\k 1=0/\k 2=0/\k 3=1) :=by decide
def sn (i:Fin 4):Fin 4:=![1,0,3,2] i
lemma zX:Function.Injective sn:=by decide
lemma rZ.u4 {V:Type*} [DecidableEq V] {c:q4 V} {A:Fin 4->FS V} {d:ℕ} (h:rZ c A d)(r:ℕ) (y:4<=r) (m:∀ i,r+2*d+1<=(A i).card) (s:∀ k,¬ CG (2*r+1) ⊑ c.graph k) (x:V)(w:∀ i,x ∉ A i):∃ i,∀ a ∈ A i,(c.graph 2).Adj x a:=by
 classical
 by_contra hn;push Not at hn;choose u hu hbad using hn;have l (i:Fin 4):x≠u i :=by intro g;exact w i (g.symm ▸ hu i)
 have q (i:Fin 4):c.colour x (u i)≠2:=fun g=> hbad i ⟨l i,g⟩
 have e (i j:Fin 4) (k:Fin 3) (t:i≠j) (z:qi (c.graph k) (A i) (A j) d):¬ (c.colour x (u i)=k/\c.colour x (u j)=k) :=by
  intro g;apply rG (c.graph k) (A i) (A j) r d (by omega) (h.disjoint i j t) z (by have C:=m i;omega) (by have D:=m j;omega) (s k) x (w i) (w j) (u i) (u j) (hu i) (hu j)
  exact ⟨⟨l i,g.1⟩,⟨l j,g.2⟩⟩
 rcases t6 (fun i=>c.colour x (u i)) q with
  g | g | g | g | g | g
 · exact e 0 2 0 (by decide) h.red02 g
 · exact e 1 3 0 (by decide) h.red13 g
 · exact e 0 1 1 (by decide) h.blue01 g
 · exact e 2 3 1 (by decide) h.blue23 g
 · have n:=rm c A r d y h.disjoint m h.red02 h.red13 h.noGreen12 x w u hu ⟨l 0,g.1⟩ ⟨l 3,g.2.2.2⟩ ⟨l 1,g.2.1⟩ ⟨l 2,g.2.2.1⟩;exact n.elim (s 0) (s 1)
 · let A':=fun i=>A (sn i)
   let u':=fun i=>u (sn i)
   have v:∀ i j,i≠j->Disjoint (A' i) (A' j):=fun i j t=> h.disjoint _ _ (zX.ne t)
   have n:=rm c A' r d y v (fun i=>m (sn i)) h.red13 h.red02 h.noGreen03 x (fun i=>w (sn i)) u' (fun i=>hu (sn i)) ⟨l 1,g.2.1⟩ ⟨l 2,g.2.2.1⟩ ⟨l 0,g.1⟩ ⟨l 3,g.2.2.2⟩
   exact n.elim (s 0) (s 1)
lemma sA {V:Type*} [Fintype V] [DecidableEq V] (c:q4 V)(A:Fin 4->FS V) (r d:ℕ)(v:4<=r) (w:8*r < Fintype.card V) (h:rZ c A d)(e:∀ i,r+2*d+1<=(A i).card):∃ k,CG (2*r+1) ⊑ c.graph k :=by
 classical
 by_contra hn;have m:∀ k,¬ CG (2*r+1) ⊑ c.graph k :=fun k s=> hn ⟨k,s⟩
 have g:=h.toFP.zP r (by omega) e m
 have j:∀ x:V,∃ i,x∈A i\/∀ a ∈ A i,(c.graph 2).Adj x a:=by
  intro x;by_cases q:∃ i,x∈A i
  · obtain ⟨i,n⟩ :=q;exact ⟨i,Or.inl n⟩
  · have t:∀ i,x ∉ A i:=fun i n=> q ⟨i,n⟩
    obtain ⟨i,n⟩ :=h.u4 r v e m x t;exact ⟨i,Or.inr n⟩
 have l:=vD (fun _:Fin 4=>c.graph 2) A r (by omega) (fun i=>by have n:=e i;omega) g (fun _=>m 2) j
 simp only [Fintype.card_fin] at l;omega
lemma FP.al {V:Type*} [DecidableEq V] {c:q4 V} {A:Fin 4->FS V} {d:ℕ} (h:FP c A d)(r:ℕ) (Q:4<=r) (g:∀ i,r+2*d+3<=(A i).card) (F:∀ k,¬ CG (2*r+1) ⊑ c.graph k):∃ C:Fin 4->FS V,rZ c C d/\∀ i,r+2*d+1<=(C i).card:=by
 classical
 have e:=h.zP r (by omega) (fun i=>by have J:=g i;omega) F
 have w:=rj (c.graph 2) (A 0) (A 3) (h.disjoint 0 3 (by decide)) (e 0) (e 3) r (by omega) (by have J:=g 0;omega) (by have J:=g 3;omega) (F 2)
 have x:=rj (c.graph 2) (A 1) (A 2) (h.disjoint 1 2 (by decide)) (e 1) (e 2) r (by omega) (by have J:=g 1;omega) (by have J:=g 2;omega) (F 2)
 obtain ⟨q,L,n⟩ :=ra (A 0) (A 3) (c.graph 2).Adj (fun a D a' H b z b' I m y=> w a a' b b' D H z I m y)
 obtain ⟨s,K,l⟩ :=ra (A 1) (A 2) (c.graph 2).Adj (fun a D a' H b z b' I m y=> x a a' b b' D H z I m y)
 let Z :=q ∪ s;let C :=fun i=>A i \ Z
 have N:Z.card<=2:= (card_union_le q s).trans (by omega)
 have hsub (i:Fin 4):C i⊆A i:=sdiff_subset
 have P:FP c C d :=
  { disjoint:=fun i j M=> (h.disjoint i j M).mono (hsub i) (hsub j)
    red02:=h.red02.mono (hsub 0) (hsub 2)
    red13:=h.red13.mono (hsub 1) (hsub 3)
    blue01:=h.blue01.mono (hsub 0) (hsub 1)
    blue23:=h.blue23.mono (hsub 2) (hsub 3)}
 have t:∀ a ∈ C 0,∀ b ∈ C 3,¬ (c.graph 2).Adj a b:=by
  intro a D b z m;rcases n a (hsub 0 D) b (hsub 3 z) m with h | h
  · exact (mem_sdiff.mp D).2 (mem_union_left s h)
  · exact (mem_sdiff.mp z).2 (mem_union_left s h)
 have v:∀ a ∈ C 1,∀ b ∈ C 2,¬ (c.graph 2).Adj a b:=by
  intro a D b z m;rcases l a (hsub 1 D) b (hsub 2 z) m with h | h
  · exact (mem_sdiff.mp D).2 (mem_union_right q h)
  · exact (mem_sdiff.mp z).2 (mem_union_right q h)
 refine ⟨C,{ toFP:=P,noGreen03:=t,noGreen12:=v},?_⟩
 intro i;have R:=card_sdiff_add_card_inter (A i) Z;have J:((A i) ∩ Z).card<=2:= (card_le_card inter_subset_right).trans N;have T:=g i;change r +2*d+1<=(A i \ Z).card;omega
lemma ul {V:Type*} [Fintype V] [DecidableEq V] (c:q4 V)(A:Fin 4->FS V) (r d:ℕ)(l:4<=r) (q:8*r < Fintype.card V) (h:FP c A d)(e:∀ i,r+2*d+3<=(A i).card):∃ k,CG (2*r+1) ⊑ c.graph k :=by
 classical
 by_contra hn;have j:∀ k,¬ CG (2*r+1) ⊑ c.graph k :=fun k n=> hn ⟨k,n⟩
 obtain ⟨C,m,g⟩ :=h.al r l e j;exact hn (sA c C r d l q m g)
lemma uJ {V:Type*} [Fintype V] [DecidableEq V] (c:q4 V)(r d:ℕ) (N:4<=r) (K:8*r < Fintype.card V) (h:yA c (r+2*d+3) d):∃ i,CG (2*r+1) ⊑ c.graph i :=by
 classical
 obtain ⟨s,k,P,L,z⟩ :=uO h.profiles h.dimension h.profile_disjoint;let e:Fin 3 ≃ Fin 3 :=Equiv.ofBijective k ⟨L,(Finite.injective_iff_surjective).mp L⟩;let c':=c.relabel e;let A:Fin 4->FS V :=fun i=>h.cores (s i)
 have m (i:Fin 3):c'.graph i =c.graph (k i) :=c.dZ e i;have t (i j:Fin 4) (D:i≠j):Disjoint (A i) (A j):=h.core_disjoint _ _ (P.ne D);have n (i:Fin 4):r+2*d+3<=(A i).card:=h.large (s i)
 have g (a b:Fin 4) (i:Fin 3) (C:q5 (h.profiles (s a)) (h.profiles (s b)) (k i)):qi (c'.graph i) (A a) (A b) d :=by
  have M:=h.dense (s a) (s b) (k i) C;simpa only [m] using M
 have q:∃ i,CG (2*r+1) ⊑ c'.graph i :=by
  rcases z with I | I
  · obtain ⟨v,y,x,w⟩ :=I;have l:FP c' A d:= ⟨t,g 0 2 0 v,g 1 3 0 y,g 0 1 1 x,g 2 3 1 w⟩;exact ul c' A r d N K l n
  · obtain ⟨v,F,H,y,x,w⟩ :=I
    have l:rM c' A d:=
     ⟨t,g 0 2 0 v,g 0 3 0 F,g 1 2 0 H,g 1 3 0 y,g 0 1 1 x,g 2 3 2 w⟩
    exact uo c' A r d (by omega) K l (fun i=>by have M:=n i;omega)
 obtain ⟨i,J⟩ :=q;rw [m] at J;exact ⟨k i,J⟩
lemma wM:∃ n₀:ℕ,∀ n:ℕ,n₀<=n->Odd n->rr n (4*n-3) :=by
 obtain ⟨l,g⟩:=zI qC y8;obtain ⟨m,d⟩ :=wG;refine ⟨max l (2*max m 4 +1),?_⟩
 intro n y e c
 classical
 obtain ⟨r,z⟩ :=e;have v:n=2*r+1:=by omega
 subst n;have j:l<=2*r+1:= (le_max_left _ _).trans y;have s:m<=r:=by omega
 have w:4<=r:=by omega
 have e:Odd (2*r+1):=⟨r,by omega⟩
 by_contra q;have t:∀ i,¬ CG (2*r+1) ⊑ c.graph i :=fun i x=> q ⟨i,x⟩
 obtain ⟨h⟩ :=g c (2*r+1) j e (by simp only [Fintype.card_fin]) t
 obtain ⟨cores⟩ :=ww h (d c r s t h)
 have k:8*r < Fintype.card (Fin (4* (2*r+1)-3)) :=by
  simp only [Fintype.card_fin];omega
 exact q (uJ c r h.defect w k cores)
end E5
end _m
namespace O5
open SimpleGraph
lemma ap {V:Type*} (c:Fin 3->SG V) (r:(⊤ :SG V).IsEdgeColouring c):∃ d:E5.q4 V,∀ i,d.graph i =c i:=by
 classical
 have g (u v:V) (l:u≠v):∃ i,(c i).Adj u v:=by
  apply iSup_adj.mp;rw [<- r.1];exact (top_adj _ _).mpr l
 have e {u v:V} {i j:Fin 3} (n:(c i).Adj u v) (s:(c j).Adj u v):i=j:=by
  by_contra q;exact (disjoint_iff_inf_le.mp (r.2 i j q)) ⟨n,s⟩
 let m (u v:V):Fin 3:=if h:u=v then 0 else Classical.choose (g u v h)
 have k {u v:V} (h:u≠v):(c (m u v)).Adj u v:=by
  dsimp only [m];rw [dif_neg h];exact Classical.choose_spec (g u v h)
 have symm (u v:V):m u v=m v u:=by
  by_cases l:u=v
  · subst v;rfl
  · exact e (k l) (k (Ne.symm l)).symm
 let d:E5.q4 V:=⟨m,symm⟩;refine ⟨d,?_⟩
 intro i;ext u v;change (u≠v/\m u v=i)↔(c i).Adj u v;constructor
 · rintro ⟨l,n⟩;simpa only [n] using k l
 · intro n;exact ⟨n.ne,e (k n.ne) n⟩
end O5

theorem OMA.solution : type_of% @Erdos556.erdos_556.variants.luczak_asymptotic := by
 intro e he
 have hev:∀ᶠ n:ℕ in Filter.atTop,Even n->SimpleGraph.multicolourRamsey (CG n) 3<=4*n:=by
  filter_upwards [E1.main h1p h2p 1 zero_lt_one] with n hn h
  have h4:(SimpleGraph.multicolourRamsey (CG n) 3:O)<=((4*n:ℕ):O):=by have:=hn h;push_cast;linarith
  exact_mod_cast h4
 have hod:∀ᶠ n:ℕ in Filter.atTop,Odd n->SimpleGraph.multicolourRamsey (CG n) 3<=4*n:=by
  obtain ⟨m,hm⟩:=E5.wM
  filter_upwards [Filter.eventually_ge_atTop m] with n hn ho
  have hl:SimpleGraph.multicolourRamsey (CG n) 3<=4*n-3:=by
   unfold SimpleGraph.multicolourRamsey;apply Nat.sInf_le;intro c hc
   obtain ⟨d,hd⟩:=O5.ap c hc;obtain ⟨i,hi⟩:=hm n hn ho d;rw [hd] at hi;exact ⟨i,hi⟩
  exact hl.trans (Nat.sub_le _ _)
 filter_upwards [hev,hod] with n h1 h2
 have hn:=(Nat.even_or_odd n).elim h1 h2
 calc _<=((4*n:ℕ):O):=by exact_mod_cast hn
  _<=(4+e)*n:=by push_cast;nlinarith [mul_nonneg he.le (Nat.cast_nonneg (α:=O) n)]
