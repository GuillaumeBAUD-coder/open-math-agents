import OMAReductions.R_Erdos142_erdos_142_variants_lower_R3
import Mathlib
/- Port of Kelley-Meka (plby/lean-proofs, YaelDillies/LeanAPAP & AddCombi, Apache-2.0) + bridge (@TomsBack), golfed. -/
open MeasureTheory
open scoped NNReal ENNReal
abbrev Α:=DiscreteMeasurableSpace
abbrev Β:=DecidableEq
abbrev Γ:=AddCommGroup
abbrev Δ:=Fintype
abbrev Ε:=AddChar
abbrev Ζ:=RCLike
open Real (log exp pi)
open Set (indicator)
open Fintype (piFinset)
open Function (Injective)
alias Ò:= Finset.sum_congr
alias Q0:= AddChar.norm_apply
alias ᾰ:= Real.exp_pos
alias ᾞ:= smul_eq_mul
alias Ἣ:= mul_one
alias Q4:= Nat.le_mul_of_pos_right
alias Q5:= Nat.cast_nonneg
alias Ῐ:= mul_left_comm
alias Q7:= mul_mul_mul_comm
alias ᾝ:= abs_nonneg
alias ᾜ:= div_le_one
alias è:= congrArg
alias ἦ:= Real.log_pow
alias ἳ:= abs_of_nonneg
alias ὶ:= Finset.sum_comm
alias ᾛ:= Finset.sum_filter
alias ἲ:= div_le_iff₀
alias ᾆ:= Real.log_le_log
alias ἥ:= pow_nonneg
alias ᾯ:= Finset.sum_le_sum
alias QJ:= Finset.sum_sub_distrib
alias ᾮ:= Real.norm_eq_abs
alias Ἀ:= mul_pow
alias Ἃ:= mul_pos
alias ᾭ:= mul_right_comm
alias ἑ:= norm_mul
alias Ὑ:= Nat.mul_pos
alias QQ:= Nat.mul_le_mul_right
alias QR:= Nat.pow_le_pow_right
alias ᾚ:= nsmul_eq_mul
alias ἃ:= one_mul
alias Ἂ:= pow_mul
alias ᾙ:= lt_of_not_ge
alias ὤ:= mul_le_mul
alias QX:= Real.log_le_sub_one_of_pos
alias QY:= AddCircle.homeomorphCircle_apply
alias ῗ:= translate_apply
alias ἂ:= mul_le_mul_of_nonneg_right
alias á:= Finset.mul_sum
alias ἐ:= Fintype.sum_equiv
alias ñ:= Real.log_mul
alias ὅ:= Set.indicator_apply
alias å:= mul_nonneg
alias à:= mul_assoc
alias ἤ:= pow_le_pow_left₀
alias ὄ:= Nat.mul_le_mul_left
alias ἇ:= le_div_iff₀
alias Ἕ:= Finset.sum_mul
alias ὣ:= Finset.card_le_card
alias Ἲ:= Real.log_nonneg
alias ἱ:= div_eq_mul_inv
alias ä:= mul_comm
alias Ἱ:= sub_eq_add_neg
alias ῖ:= div_le_div_of_nonneg_right
alias R0:= pow_sub_one_mul
alias R1:= Fintype.card_le_of_injective
alias R2:= ENNReal.some_eq_coe
alias R3:= RCLike.conj_to_real
alias R4:= Nat.pow_le_pow_left
alias ΐ:= two_mul
alias ῆ:= one_div
alias R7:= Real.exp_add
alias R8:= Nat.mul_comm
alias R9:= div_le_div_iff_of_pos_right
alias RA:= Real.norm_of_nonneg
alias ᾬ:= pow_succ
alias RD:= Pi.smul_apply
alias ᾅ:= pow_pos
alias RG:= NNReal.smul_def
alias RH:= one_le_pow₀
alias RI:= Subtype.ext
alias RJ:= inv_le_inv₀
alias ᾘ:= map_sum
alias ᾫ:= pow_add
alias RM:= Pi.add_apply
alias RN:= Real.rpow_natCast
alias RO:= AddChar.sub_apply
alias ή:= if_pos
alias RQ:= mul_le_of_le_one_left
alias RR:= nonempty_fintype
alias RS:= div_nonneg
alias RT:= abs_of_pos
alias ᾪ:= map_mul
alias ῒ:= add_comm
alias RW:= Fintype.expect_equiv
alias RX:= Fintype.mem_piFinset
alias RY:= Nat.lt_floor_add_one
alias RZ:= Nat.add_le_add_right
alias Ra:= Nat.mul_le_mul
alias Rb:= div_le_div_of_nonneg_left
alias Rc:= starRingEnd_apply
alias ῑ:= not_lt_of_ge
alias Re:= norm_nonneg
alias Rf:= Complex.norm_real
alias ῄ:= pow_ne_zero
alias Rh:= Function.comp_apply
alias Ri:= div_eq_inv_mul
alias Rj:= Fintype.expect_eq_sum_div_card
alias Rk:= Fintype.exists_lt_card_fiber_of_mul_lt_card
alias ῐ:= mul_ne_zero
alias Rm:= Nat.cast_mul
alias ὗ:= div_pos
alias Ro:= Finset.sum_subset
alias Rp:= Finset.mem_insert
alias Rq:= norm_sum_le
alias Rr:= Nat.le_ceil
alias Rs:= sub_add_cancel
alias Rt:= Pi.one_apply
alias Rv:= Nat.cast_pow
alias Rw:= Pi.sub_apply
alias Rx:= Fintype.card_coe
alias Ry:= Finset.sum_le_sum_of_subset_of_nonneg
alias Rz:= AddChar.inv_apply_eq_conj
alias S0:= Real.rpow_mul
alias S2:= NNReal.HolderConjugate.conjExponent
alias S3:= Nat.ceil_mono
alias S4:= Real.rpow_inv_rpow
alias S5:= mul_div_right_comm
alias S6:= DFunLike.congr_fun
alias S7:= Finset.subset_univ
alias S8:= sub_left_injective
alias S9:= NNReal.coe_natCast
alias SA:= Finite.bddAbove_range
alias SB:= Fintype.piFinset_univ
alias SC:= le_antisymm
alias SD:= two_ne_zero
alias SE:= NNReal.coe_inv
alias SF:= le_rfl
alias SG:= le_abs_self
alias SH:= mul_div_cancel_left₀
alias SI:= lt_of_lt_of_le
alias SJ:= pow_le_pow_of_le_one
alias SK:= NNReal.coe_mul
alias SL:= Fintype.card_subtype
alias SM:= lt_of_le_of_ne
alias SN:= Fintype.card_ne_zero
alias SO:= Finset.sum_erase_add
alias SP:= lt_div_iff₀
alias SQ:= Real.rpow_pos_of_pos
alias SR:= congr_fun
alias SS:= boole_mul
alias SU:= abs_mul
alias SV:= RCLike.inner_apply'
alias SW:= Real.log_le_log_iff
alias SX:= Equiv.subLeft_apply
alias SY:= sq_pos_of_pos
alias SZ:= Nat.mul_assoc
alias Sa:= tendsto_natCast_atTop_atTop
alias Sb:= RCLike.inner_apply
alias Sc:= Real.pow_rpow_inv_natCast
alias Sd:= Finset.inter_subset_right
alias Se:= pow_le_pow_right₀
alias Sf:= Real.rpow_le_rpow
alias Sg:= RCLike.wInner_one_eq_sum
alias Sh:= Finset.inter_subset_left
alias Si:= Finset.sum_apply
alias Sj:= le_trans
alias Sk:= mul_lt_mul_of_pos_right
alias Sl:= Nat.mod_eq_of_lt
alias Sm:= Finset.mem_of_mem_erase
alias Sn:= max_le_max_right
alias So:= Nat.cast_two
alias Sq:= mul_le_of_le_one_right
alias Sr:= add_le_add
alias Ss:= le_add_of_nonneg_right
alias St:= AddChar.map_add_eq_mul
alias Su:= abs_sub_comm
alias Sv:= Real.log_pos
alias Sw:= Finset.ne_of_mem_erase
alias Sx:= ENNReal.HolderConjugate.eq_top_iff_eq_one
alias Sy:= div_le_div_iff₀
alias Sz:= Finset.mem_univ
alias T0:= starRingEnd_self_apply
alias T2:= even_two_mul
alias T3:= Nat.cast_add
alias T4:= tsub_le_self
alias T6:= mul_lt_mul_of_pos_left
alias T7:= Finset.sum_add_distrib
alias T8:= Real.closedBall_eq_Icc
alias T9:= Nat.le_mul_of_pos_left
alias TA:= inv_mul_le_iff₀
alias TB:= ZMod.natCast_eq_natCast_iff'
alias TC:= Fintype.card_pi
alias TD:= AddCircle.injective_toCircle
alias TE:= abs_div
alias TF:= pow_sum_div_card_le_sum_pow
alias TG:= Fintype.card_piFinset_const
alias TH:= AddChar.expect_apply_eq_ite
alias TI:= pow_two
alias TJ:= smul_mul_assoc
alias TK:= inv_mul_eq_div
alias TL:= add_sub_cancel
alias TM:= true_and
alias TN:= NNReal.coe_one
alias TO:= neg_le_neg
alias TP:= Finset.sum_div
alias TQ:= Finset.abs_sum_le_sum_abs
alias TR:= Pi.conj_apply
alias TS:= Real.rpow_neg
alias TU:= apply_ite
alias TV:= AddChar.map_neg_eq_conj
alias TW:= Finset.prod_mul_distrib
alias TX:= Finset.exists_max_image
alias TY:= div_pow
alias TZ:= le_of_mul_le_mul_right
alias Ta:= Real.mul_self_sqrt
alias Tb:= Set.mem_vadd_set_iff_neg_vadd_mem
alias Tc:= mul_add
alias Td:= mul_ite
alias Te:= inv_pow
alias Tf:= eq_or_ne
alias Tg:= Real.coe_toNNReal
alias Th:= Real.rpow_le_rpow_of_exponent_ge
alias Ti:= Nat.floor_le
alias Tj:= Finset.sum_le_univ_sum_of_nonneg
alias Tk:= ENNReal.HolderConjugate.ne_zero
alias Tl:= RCLike.conj_conj
alias Tm:= and_assoc
alias Tn:= Real.rpow_nonneg
alias To:= not_nonempty_iff
alias Tp:= Finset.sum_sub_sum_mem_addSpan
alias Tq:= Finset.sum_const
alias Tr:= Nat.lt_succ_self
alias Ts:= AddCircle.norm_coe_eq_abs_iff
alias Tt:= Finset.sum_lt_sum_of_nonempty
alias Tu:= le_max_left
alias Tv:= div_lt_iff₀
alias Tw:= mul_inv_cancel₀
alias Tx:= pos_iff_ne_zero
alias Ty:= Nat.succ_le_iff
alias Tz:= div_mul_cancel₀
alias U0:= NNReal.coe_le_coe
alias U1:= one_pos
alias U2:= AddChar.neg_apply
alias U3:= AddChar.add_apply
alias U4:= Real.sqrt_eq_rpow
alias U5:= Nat.zero_lt_of_lt
alias U6:= Nat.mul_left_comm
alias UA:= Complex.norm_natCast
alias UB:= Fintype.sum_mul_sum
alias UC:= isEmpty_or_nonempty
alias UD:= ENNReal.none_eq_top
alias UE:= translate_sub_right
alias UF:= Finset.mem_symmDiff
alias UG:= addRothNumber_spec
alias UH:= CharP.cast_eq_zero
alias UI:= algebraMap.coe_pow
alias UJ:= ENNReal.toReal_pos
alias UK:= ENNReal.toReal_mul
alias UL:= Fintype.sum_ite_eq
alias UM:= one_add_mul_le_pow
alias UN:= Finset.sum_eq_zero
alias UO:= Finset.prod_le_one
alias UP:= abs_add_le
alias UQ:= not_ne_iff
alias UR:= tendsto_rpow_atTop
alias US:= add_mul
alias UT:= sub_div
alias UU:= Finset.mem_filter
alias UW:= div_le_one_of_le₀
alias UX:= Complex.conj_mul'
alias UY:= mul_sub
alias UZ:= Finset.sum_nonneg
alias Ua:= Finset.mem_union_right
alias Ub:= AddCircle.toCircle_add
alias Uc:= Nat.floor_lt
alias Ud:= AddChar.map_neg_eq_inv
alias Ue:= ENNReal.toReal_natCast
alias Uf:= Real.sq_sqrt
alias Ug:= Finset.mem_vadd_finset
alias Uh:= Real.exp_neg
alias Ui:= Real.log_div
alias Uj:= le_of_mul_le_mul_left
alias Uk:= Complex.normSq_nonneg
alias Ul:= Fintype.sum_prod_type
alias Um:= Finset.mem_union_left
alias Un:= Complex.re_ofReal_mul
alias Uo:= Classical.choose_spec
alias Up:= norm_inv
alias Uq:= ne_of_gt
alias Ur:= Function.mem_support
alias Us:= zero_le_one
alias Ut:= Equiv.subRight_apply
alias Uu:= congrFun
alias Uv:= min_le_left
alias Uw:= one_le_inv₀
alias Ux:= Finset.card_powerset
alias Uy:= pow_le_one₀
alias Uz:= vadd_eq_add
alias Å:= mul_le_mul_of_nonneg_left
open MeasureTheory
section
namespace w1
open Erdos142 Finset
def yG (k N:ℕ):Set ℕ:=
 {Finset.card S | (S) (_:S⊆Finset.Icc 1 N) (_:(S:Set ℕ).IsAPOfLengthFree k)}
lemma qi {k N x:ℕ}:x∈yG k N ↔
  ∃ S:Finset ℕ,S⊆Finset.Icc 1 N∧(S:Set ℕ).IsAPOfLengthFree k∧S.card=x:=by
 constructor
 ·rintro ⟨S,h1,h2,ώ⟩
  exact ⟨S,h1,h2,ώ⟩
 ·rintro ⟨S,h1,h2,ώ⟩
  exact ⟨S,h1,h2,ώ⟩
lemma Cx (k:ℕ):(∅:Set ℕ).IsAPOfLengthFree k:=by
 intro t ht D3
 have h:=D3.card
 rw[Set.subset_empty_iff.mp ht] at h
 simp at h
 simp[←h]
lemma w2 (k N:ℕ):BddAbove (yG k N):=by
 refine ⟨N, ?_⟩
 intro x hx
 obtain ⟨S,Ø, -,rfl⟩:=qi.1 hx
 simpa using card_le_card Ø
lemma xi (k N:ℕ):(yG k N).Nonempty:=
 ⟨0,qi.2 ⟨∅,by simp,by simpa using Cx k,by simp⟩⟩
lemma M0 {k N:ℕ} (S:Finset ℕ) (Ø:S⊆Finset.Icc 1 N)
  (hf:(S:Set ℕ).IsAPOfLengthFree k):S.card≤r k N:=
 le_csSup (w2 k N) (qi.2 ⟨S,Ø,hf,rfl⟩)
lemma FL (k N:ℕ): ∃ S:Finset ℕ,S⊆Finset.Icc 1 N ∧
  (S:Set ℕ).IsAPOfLengthFree k∧S.card=r k N:=
 qi.1 (Nat.sSup_mem (xi k N) (w2 k N))
lemma FM {k:ℕ} (hk:2≤k) (S:Set ℕ) :
  S.IsAPOfLengthFree k↔ ∀ a d:ℕ,0<d→ ¬ (∀ i<k,a+i*d∈S):=by
 constructor
 ·intro h a d hd z9
  have hinj:Injective (λ i:ℕ=>a+i*d):=by
   intro i j hij
   have:i*d=j*d:=by simpa using hij
   exact Nat.eq_of_mul_eq_mul_right hd this
  have D3:Set.IsAPOfLength (((Finset.range k).image (λ i=>a+i*d):Finset ℕ):Set ℕ) (k:ℕ∞):=by
   refine ⟨a,d, ?_, ?_⟩
   ·show Set.encard _=_
    rw[Set.encard_coe_eq_coe_finsetCard,card_image_of_injective _ hinj,card_range]
   ·ext x
    simp[ᾞ]
  have Ὂ:(((Finset.range k).image (λ i=>a+i*d):Finset ℕ):Set ℕ)⊆S:=by
   intro x hx
   simp only[coe_image,coe_range,Set.mem_image,Set.mem_Iio] at hx
   obtain ⟨i,hi,rfl⟩:=hx
   exact z9 i hi
  have:=h _ Ὂ D3
  have:k≤1:=by exact_mod_cast this
  omega
 ·intro h t ht D3
  exfalso
  obtain ⟨a,d,ch,heq⟩:=D3
  rcases Nat.eq_zero_or_pos d with hd | hd
  ·subst hd
   have:t={a}:=by
    rw[heq]
    ext x
    simp only[smul_zero,add_zero,Set.mem_ofPred_eq,Set.mem_singleton_iff]
    constructor
    ·rintro ⟨n, -,rfl⟩
     rfl
    ·rintro rfl
     exact ⟨0,by exact_mod_cast(by omega:0<k),rfl⟩
   rw[this] at ch
   simp at ch
   have:k=1:=by exact_mod_cast ch.symm
   omega
  ·apply h a d hd
   intro i hi
   apply ht
   rw[heq]
   exact ⟨i,by exact_mod_cast hi,by simp[ᾞ]⟩
lemma tR (S:Set ℕ):S.IsAPOfLengthFree ((3:ℕ):ℕ∞)↔ThreeAPFree S:=by
 rw[FM (by norm_num)]
 constructor
 ·intro h a ha b hb c hc ᾊ
  by_contra ᾱ
  rcases lt_or_gt_of_ne ᾱ with Ί | PY
  ·apply h a (b-a) (by omega)
   intro i hi
   interval_cases i
   ·simpa using ha
   ·have e:a+1*(b-a)=b:=by omega
    rw[e]
    exact hb
   ·have e:a+2*(b-a)=c:=by omega
    rw[e]
    exact hc
  ·apply h c (b-c) (by omega)
   intro i hi
   interval_cases i
   ·simpa using hc
   ·have e:c+1*(b-c)=b:=by omega
    rw[e]
    exact hb
   ·have e:c+2*(b-c)=a:=by omega
    rw[e]
    exact ha
 ·intro h a d hd z9
  have h0:=z9 0 (by norm_num)
  have h1:=z9 1 (by norm_num)
  have h2:=z9 2 (by norm_num)
  have:=h h0 h1 h2 (by ring)
  omega
lemma r4 (N:ℕ):r 3 N=addRothNumber (Finset.Icc 1 N):=by
 apply SC
 ·obtain ⟨S,Ø,hf,hc⟩:=FL 3 N
  rw[←hc]
  exact((tR _).1 hf).le_addRothNumber Ø
 ·obtain ⟨S,Ø,hc,hf⟩:=UG (Finset.Icc 1 N)
  rw[←hc]
  exact M0 S Ø ((tR _).2 hf)
end w1
end
section
open Finset Function
section
variable {ι α ip:Type*}
section CommMonoidWithZero
variable [CommMonoidWithZero ip] [Β α]
lemma mQ [Δ α] (s:Finset ι) (t:ι→Finset α) (x:α) :
  (indicator (↑(s.inf t)) λ _↦(1:ip)) x= ∏ i∈s,(indicator (t i) λ _↦(1:_)) x:=by simp[ὅ,mem_inf,prod_boole]
end CommMonoidWithZero
end
end
section
open scoped Pointwise
section
variable {α G ip:Type*}
section yH
variable [One ip] [Zero ip] [AddGroup G] [AddAction G α]
@[simp] lemma D4 (g:G) (s:Set α) (a:α):(indicator (g+ᵥ s) λ _↦(1:ip)) a=(indicator s λ _↦(1:_)) (-g+ᵥ a):=by
 classical simp[ὅ,Tb]
end yH
end
end
section
open scoped Pointwise
section
variable {G ip:Type*}
section yH
variable [One ip] [Zero ip] [AddGroup G]
@[simp] lemma FJ (s:Set G) (a:G):(indicator (-s) λ _↦(1:ip)) a=(indicator s λ _↦(1:_)) (-a):=by
 classical simp[ὅ]
end yH
end
end
section
section
variable {F α β ip Ὠ:Type*}
namespace Set
variable [MonoidWithZero ip] [MonoidWithZero Ὠ] {s:Set α}
lemma iq (s t:Set α) (x:α):(indicator (s∩t) λ _↦(1:ip)) x=(indicator s λ _↦(1:_)) x*(indicator t λ _↦(1:_)) x:=by
 classical simp[indicator_apply, ←ite_and,and_comm]
lemma rj [FunLike F ip Ὠ] [MonoidWithZeroHomClass F ip Ὠ] (f:F) (s:Set α)
  (x:α):f ((indicator s λ _↦(1:_)) x)=(indicator s λ _↦(1:_)) x:=by classical exact MonoidWithZeroHom.map_ite_one_zero ..
variable [Nontrivial ip] {a:α}
lemma qn:(indicator s λ _↦(1:ip)) a≠0↔a∈s:=by
 classical exact one_ne_zero.ite_ne_right_iff
variable (ip) in
@[simp] lemma j0:(indicator s λ _↦(1:ip)).support=s:=by
 ext; exact qn
end Set
end
end
section
section
open scoped Pointwise translate
variable {G ip:Type*}
section Semiring
variable [One ip] [Zero ip] [Γ G]
variable (ip) in
lemma sU (a:G) (s:Set G):τ a (indicator s λ _↦(1:ip))=(indicator (a+ᵥ s) λ _↦(1:_)):=by
 classical ext; simp[ὅ,Tb,sub_eq_neg_add]
end Semiring
end
end
section
section
open ENNReal
namespace MeasureTheory
variable {𝕜 α:Type*} {m:MeasurableSpace α} {μ:Measure α} [NormedRing 𝕜]
lemma qV {p q r:ℝ≥0∞} {f g:α→𝕜} (hf:AEStronglyMeasurable f μ)
  (hg:AEStronglyMeasurable g μ) [HolderTriple p q r] :
  eLpNorm (f*g) r μ≤eLpNorm f p μ*eLpNorm g q μ:=by
 simpa using eLpNorm_smul_le_mul_eLpNorm hg hf
end MeasureTheory
end
end
section
section
open Finset Fintype Function
open scoped ComplexConjugate NNReal Pointwise translate
variable {G H R S:Type*} [Β G] [Γ G]
section CommSemiring
variable [CommSemiring R]
def uK:G→R:=λ a↦if a=0 then 1 else 0
@[simp] lemma yI (a:G):(uK a:R)=if a=0 then 1 else 0:=rfl
variable [StarRing R]
end CommSemiring
variable [Δ G]
section CommSemiring
variable [CommSemiring R] {f g:G→R}
def Χ (f g:G→R):G→R:=λ a↦ ∑ x:G × G with x.1+x.2=a ,f x.1*g x.2
lemma Ώ (f g:G→R) (a:G) :
  ((Χ f g)) a= ∑ x:G × G with x.1+x.2=a,f x.1*g x.2:=rfl
lemma Cy (f g h:G→R):(Χ ((f+g)) h)=(Χ f h)+(Χ g h):=by
 ext; simp[Ώ,US,sum_add_distrib]
lemma tn [DistribSMul H R] [IsScalarTower H R R] (c:H) (f g:G→R) :
  (Χ (c•f) g)=c•((Χ f g)):=by ext a; simp[Ώ,smul_sum,TJ]
lemma Bv [DistribSMul H R] [SMulCommClass H R R] (c:H) (f g:G→R) :
  (Χ f (c•g))=c•((Χ f g)):=by ext a; simp[Ώ,smul_sum,mul_smul_comm]
@[simp] lemma FN (a:G) (f g:G→R):(Χ (τ a f) g)=τ a ((Χ f g)):=
 funext λ b↦sum_equiv ((Equiv.subRight a).prodCongr<| Equiv.refl _)
  (by simp[sub_add_eq_add_sub]) (by simp)
lemma ᾼ (f g:G→R):(Χ f g)=(Χ g f):=
 funext λ a↦sum_equiv (Equiv.prodComm _ _) (by simp[ῒ])<| by simp[ä]
lemma uL [Monoid H] [DistribMulAction H R] [IsScalarTower H R R]
  [SMulCommClass H R R] (c d:H) (f g:G→R):(c*d)•((Χ f g))=(Χ (c•f) (d•g)):=by
 rw[tn,Bv,mul_smul]
lemma iS (f g h:G→R):(Χ ((Χ f g)) h)=(Χ f (((Χ g h)))):=by
 ext a
 simp only[sum_mul,mul_sum,Ώ,Finset.sum_sigma']
 apply sum_nbij' (λ ⟨(_b,c),(d,e)⟩↦⟨(d,e+c),(e,c)⟩)
  (λ ⟨(b,_c),(d,e)⟩↦⟨(b+d,e),(b,d)⟩)<;>aesop (add simp[add_assoc,à])
lemma xj (f g h:G→R):(Χ f (((Χ g h))))=(Χ g (((Χ f h)))):=by
 rw[←iS, ←iS,ᾼ g]
lemma ir (f g h i:G→R):(Χ ((Χ f g)) (((Χ h i))))=(Χ ((Χ f h)) (((Χ g i)))):=by
 rw[iS,iS,xj g]
lemma xT [CommSemiring S] (m:R→+* S) (f g:G→R) (a:G) :
  m (((Χ f g)) a)=((Χ (m ∘ f) (m ∘ g))) a:=by simp[Ώ,ᾘ,ᾪ]
lemma rk (f g:G→R) (a:G):((Χ f g)) a= ∑ t,f (a-t)*g t:=by
 rw[Ώ]; apply sum_nbij' Prod.snd (λ b↦(a-b,b))<;>aesop
lemma ᾂ (f g:G→R) (a:G):((Χ f g)) a= ∑ t,f t*g (a-t):=by
 rw[ᾼ,rk]; simp_rw[ä]
lemma r5 (f g:G→R) (a b:G):((Χ f g)) (a+b)= ∑ t,f (a+t)*g (b-t):=
 (rk _ _ _).trans<| ἐ (Equiv.subLeft b) _ _ λ t↦by
  simp[add_sub_assoc]
lemma tS (f g h:G→R): ∑ a,((Χ f g)) a*h a= ∑ a, ∑ b,f a*g b*h (a+b):=by
 simp_rw[ᾂ,sum_mul]
 rw[sum_comm]
 exact sum_congr rfl λ x _↦ἐ (Equiv.subRight x) _ _ λ y↦by simp
lemma uM (f g:G→R): ∑ a,((Χ f g)) a=(∑ a,f a)* ∑ a,g a:=by
 simpa only[UB,Rt,Ἣ] using tS f g 1
lemma tT (f g:G→R):support ((Χ f g))⊆support f+support g:=by
 rintro a ha
 obtain ⟨x,hx,h⟩:=exists_ne_zero_of_sum_ne_zero ha
 exact ⟨_,left_ne_zero_of_mul h,_,right_ne_zero_of_mul h,(mem_filter.1 hx).2⟩
variable [StarRing R]
def al (f g:G→R):G→R:=λ a↦ ∑ x:G × G with x.1-x.2=a,f x.1*conj g x.2
lemma ᾥ (f g:G→R) (a:G) :
  ((al f g)) a= ∑ x:G × G with x.1-x.2=a ,f x.1*conj g x.2:=rfl
@[simp] lemma I1 (f:G→R):(al f 0)=0:=by ext; simp[ᾥ]
@[simp] lemma I2 (f:G→R):(al 0 f)=0:=by ext; simp[ᾥ]
@[simp] lemma FO (f:G→R):(al f ((λ _↦0)))=0:=by ext; simp[ᾥ]
lemma Bw (f g h:G→R):(al f ((g+h)))=(al f g)+(al f h):=by
 ext; simp[ᾥ,Tc,sum_add_distrib]
lemma Bx (f g h:G→R):(al ((f+g)) h)=(al f h)+(al g h):=by
 ext; simp[ᾥ,US,sum_add_distrib]
lemma oB [DistribSMul H R] [IsScalarTower H R R] (c:H) (f g:G→R) :
  (al (c•f) g)=c•((al f g)):=by ext; simp[ᾥ,smul_sum,TJ]
lemma oC [Star H] [DistribSMul H R] [SMulCommClass H R R] [StarModule H R] (c:H)
  (f g:G→R):(al f (c•g))=star c•((al f g)):=by
 ext; simp[ᾥ,smul_sum,mul_smul_comm,Rc,star_smul]
@[simp] lemma rl (a:G) (f g:G→R):(al (τ a f) g)=τ a ((al f g)):=
 funext λ b↦sum_equiv ((Equiv.subRight a).prodCongr<| Equiv.refl _)
  (by simp[sub_right_comm _ a]) (by simp)
@[simp] lemma iM (f g:G→R):(Χ f (conjneg g))=(al f g):=
 funext λ a↦sum_equiv ((Equiv.refl _).prodCongr<| Equiv.neg _) (by simp) (by simp)
@[simp] lemma FK (f g:G→R) (a:G):conj (((Χ f g)) a)=((Χ (conj f) (conj g))) a:=by
 simp only[TR,Ώ,ᾘ,ᾪ]
@[simp] lemma pL (f g:G→R):conjneg ((Χ f g))=(Χ (conjneg f) (conjneg g)):=by
 funext a
 simp only[Ώ,conjneg_apply,ᾘ,ᾪ]
 exact sum_equiv (Equiv.neg _) (by simp[←neg_eq_iff_eq_neg,ῒ]) (by simp)
@[simp] lemma xU (f g:G→R):conjneg ((al f g))=(al g f):=by
 simp_rw[←iM,pL,conjneg_conjneg,ᾼ]
lemma kr (f g h i:G→R):(Χ ((al f g)) (((al h i))))=(al ((Χ f h)) (((Χ g i)))):=by
 simp_rw[←iM,pL,ir]
lemma eL (f g:G→R) (a:G):((al f g)) a= ∑ t,f t*conj (g (t-a)):=by
 simp[←iM,ᾂ]
lemma wT (f g:G→R) (a:G):((al f g)) (-a)=conj (((al g f)) a):=by
 rw[←xU f,conjneg_apply,Complex.conj_conj]
lemma rm (f g:G→R) (a b:G) :
  ((al f g)) (a-b)= ∑ t,f (a+t)*conj (g (b+t)):=by
 simp[←iM,Ἱ,r5,ῒ]
lemma lM (f g h:G→R) :
  ∑ a,((al f g)) a*h a= ∑ a, ∑ b,f a*conj (g b)*h (a-b):=by
 simp_rw[eL,sum_mul]
 rw[sum_comm]
 exact Fintype.sum_congr _ _ λ x↦ἐ (Equiv.subLeft x) _ _ λ y↦by simp
lemma jJ (f g:G→R): ∑ a,((al f g)) a=(∑ a,f a)* ∑ a,conj (g a):=by
 simpa only[UB,Rt,Ἣ] using lM f g 1
end CommSemiring
section CommRing
variable [CommRing R]
@[simp] lemma Cz (f g:G→R):(Χ (-f) g)= -((Χ f g)):=by ext; simp[Ώ]
lemma CA (f g h:G→R):(Χ ((f-g)) h)=(Χ f h)-(Χ g h):=by
 simp only[Ἱ,Cy,Cz]
variable [StarRing R]
@[simp] lemma By (f g:G→R):(al f (-g))= -((al f g)):=by ext; simp[ᾥ]
@[simp] lemma Bz (f g:G→R):(al (-f) g)= -((al f g)):=by ext; simp[ᾥ]
lemma BA (f g h:G→R):(al f ((g-h)))=(al f g)-(al f h):=by
 simp only[Ἱ,Bw,By]
lemma BB (f g h:G→R):(al ((f-g)) h)=(al f h)-(al g h):=by
 simp only[Ἱ,Bx,Bz]
end CommRing
namespace RCLike
variable {𝕜:Type} [Ζ 𝕜] (f g:G→ℝ) (a:G)
@[simp] lemma rx:(↑(((Χ f g)) a):𝕜)=((Χ ((↑) ∘ f) ((↑) ∘ g))) a:=
 xT (algebraMap ℝ 𝕜) _ _ _
@[simp] lemma lg:(↑(((al f g)) a):𝕜)=((al ((↑) ∘ f) ((↑) ∘ g))) a:=by simp[ᾥ]
@[simp] lemma oD:((↑):ℝ→𝕜) ∘ ((Χ f g))=(Χ ((↑) ∘ f) ((↑) ∘ g)):=funext<| rx _ _
@[simp] lemma gF:((↑):ℝ→𝕜) ∘ ((al f g))=(al ((↑) ∘ f) ((↑) ∘ g)):=funext<| lg _ _
end RCLike
namespace Complex
variable (f g:G→ℝ) (n:ℕ) (a:G)
@[simp] lemma zI:(↑(((Χ f g)) a):ℂ)=((Χ ((↑) ∘ f) ((↑) ∘ g))) a:=RCLike.rx _ _ _
@[simp] lemma yJ:(↑(((al f g)) a):ℂ)=((al ((↑) ∘ f) ((↑) ∘ g))) a:=RCLike.lg _ _ _
@[simp] lemma qo:((↑):ℝ→ℂ) ∘ ((Χ f g))=(Χ ((↑) ∘ f) ((↑) ∘ g)):=
 funext<| zI _ _
@[simp] lemma pB:((↑):ℝ→ℂ) ∘ ((al f g))=(al ((↑) ∘ f) ((↑) ∘ g)):=
 funext<| yJ _ _
end Complex
namespace NNReal
variable (f g:G→ℝ≥0) (a:G)
@[simp] lemma rx:(↑(((Χ f g)) a):ℝ)=((Χ ((↑) ∘ f) ((↑) ∘ g))) a:=xT NNReal.toRealHom _ _ _
@[simp] lemma lg:(↑(((al f g)) a):ℝ)=((al ((↑) ∘ f) ((↑) ∘ g))) a:=by simp[ᾥ,coe_sum]
@[simp] lemma oD:((↑):_→ℝ) ∘ ((Χ f g))=(Χ ((↑) ∘ f) ((↑) ∘ g)):=
 funext<| rx _ _
@[simp] lemma gF:((↑):_→ℝ) ∘ ((al f g))=(al ((↑) ∘ f) ((↑) ∘ g)):=
 funext<| lg _ _
end NNReal
section CommSemiring
variable [CommSemiring R] {f g:G→R} {n:ℕ}
def ἶ (f:G→R):ℕ→G→R
 | 0=>uK
 | n+1=>(Χ (ἶ f n) f)
@[simp] lemma IY (f:G→R):(ἶ f 0)=uK:=rfl
lemma vl (f:G→R) (n:ℕ):(ἶ f ((n+1)))=(Χ ((ἶ f n)) f):=rfl
lemma yK (f:G→R) (n:ℕ):(ἶ f ((n+1)))=(Χ f ((ἶ f n))):=ᾼ _ _
@[simp] lemma vm [Monoid H] [DistribMulAction H R] [IsScalarTower H R R]
  [SMulCommClass H R R] (c:H) (f:G→R): ∀ n,(ἶ ((c•f)) n)=c^n•(ἶ f n)
 | 0=>by simp
 | n+1=>by simp_rw[vl,vm _ _ n,ᾬ,uL]
variable [StarRing R]
end CommSemiring
end
end
section
open Finset Function
open Fintype (card)
open scoped BigOperators ComplexConjugate Pointwise translate
section
variable {K L α G:Type*}
section DivisionSemiring
variable [DivisionSemiring K] [DivisionSemiring L] {s:Finset α}
noncomputable def mu (s:Finset α):α→K:=(#s:K)⁻¹ •(indicator s λ _↦(1:_))
lemma υ [Β α] (x:α):mu s x=(#s:K)⁻¹ *ite (x∈s) 1 0:=by
 simp[mu,ὅ]
@[simp] lemma FQ:(mu ∅:α→K)=0:=by ext; simp[mu]
lemma xV (f:K→+* L) (s:Finset α) (x:α):f (mu s x)=mu s x:=by
 simp_rw[mu,RD,ᾞ,ᾪ,Set.rj,map_inv₀,map_natCast]
section Nontrivial
variable [CharZero K] {a:α}
@[simp] lemma FR:(@mu K _ _) s a=0↔a∉s:=by
 classical
 simp only[υ,mul_boole,ite_eq_right_iff,inv_eq_zero,Nat.cast_eq_zero,card_eq_zero]
 refine imp_congr_right λ ha↦ ?_
 simp only[ne_empty_of_mem ha]
variable (K)
@[simp] lemma jo (s:Finset α):support ((@mu K _ _) s)=s:=by ext; simp
end Nontrivial
variable (K)
lemma l5 [CharZero K] (s:Finset α): #s•(@mu K _ _) s=(indicator s λ _↦(1:_)):=by
 classical
 ext x:1
 simp only[RD,υ,Td,Ἣ,mul_zero,smul_ite,ᾚ,
  ὅ,SetLike.mem_coe]
 split_ifs with h
 ·have:s.Nonempty:=⟨_,h⟩
  simp[this.ne_empty]
 ·simp
lemma qr [CharZero K] (s:Finset α) (x:α): #s•(@mu K _ _) s x=(indicator s λ _↦(1:_)) x:=
 SR (l5 K _) _
@[simp] lemma ᾢ [CharZero K] [Δ α] (hs:s.Nonempty): ∑ x,(@mu K _ _) s x=1:=by
 classical
 simpa[υ] using Tw (Nat.cast_ne_zero.2 hs.card_pos.ne')
section Group
variable [AddGroup G] [AddAction G α] [Β α]
@[simp] lemma NL (g:G) (s:Finset α) (a:α):(@mu K _ _) (g+ᵥ s) a=mu s (-g+ᵥ a):=by
 simp[υ,neg_vadd_mem_iff]
end Group
section Group
variable [AddGroup α] [Β α]
@[simp] lemma N4 (s:Finset α) (a:α):(@mu K _ _) (-s) a=mu s (-a):=by simp[mu]
end Group
lemma vI [Γ G] [Β G] (a:G) (s:Finset G) :
  τ a ((@mu K _ _) s)=mu (a+ᵥ s):=by
 ext; simp[υ, ←neg_vadd_mem_iff,sub_eq_neg_add]
end DivisionSemiring
section Semifield
variable (K) [Semifield K] {s:Finset G}
variable [StarRing K]
@[simp] lemma CB [Γ G] [Β G] (s:Finset G) :
  conjneg ((@mu K _ _) s)=mu (-s):=by ext; simp[υ]; split_ifs<;>simp
end Semifield
section LinearOrderedSemifield
variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] {s:Finset α}
@[simp] lemma õ:0≤(@mu K _ _) s:=λ a↦by classical rw[υ]; split_ifs<;>simp
end LinearOrderedSemifield
namespace Complex
variable (s:Finset α) (a:α)
@[simp] lemma D5: ↑((@mu (ℝ) _ _) s a)=(@mu (ℂ) _ _) s a:=xV (algebraMap ℝ ℂ) ..
@[simp] lemma yL:(↑) ∘ (@mu (ℝ) _ _) s=(@mu (ℂ) _ _) s:=funext<| D5 _
end Complex
namespace RCLike
variable {𝕜:Type*} [Ζ 𝕜] (s:Finset α) (a:α)
@[simp] lemma Aa: ↑((@mu (ℝ) _ _) s a)=(@mu 𝕜 _ _) s a:=xV (algebraMap ℝ 𝕜) _ _
@[simp] lemma iF:(↑) ∘ (@mu (ℝ) _ _) s=(@mu 𝕜 _ _) s:=funext<| Aa _
end RCLike
namespace NNReal
open scoped NNReal
@[simp] lemma Aa (s:Finset α) (x:α): ↑((@mu (ℝ≥0) _ _) s x)=(@mu (ℝ) _ _) s x:=xV NNReal.toRealHom _ _
@[simp] lemma iF (s:Finset α):(↑) ∘ (@mu (ℝ≥0) _ _) s=(@mu (ℝ) _ _) s:=funext<| Aa _
end NNReal
end
end
section
section
open Finset Fintype Function
open scoped BigOperators ComplexConjugate NNReal Pointwise translate
variable {G R γ:Type*} [Δ G] [Β G] [Γ G]
section CommSemiring
variable [CommSemiring R] {f g:G→R} {n:ℕ}
lemma j1 (s:Finset G) :
  ∀ (n:ℕ) (a:G),((ἶ ((indicator s λ _↦(1:R))) n)) a= #{x∈(piFinset λ _:Fin n↦s) | ∑ i,x i=a}
 | 0,a=>by simp[TU card,eq_comm]
 | n+1,a=>by
  simp_rw[yK,ᾂ,j1,ὅ,
   SS,sum_ite,mem_coe,filter_univ_mem,sum_const_zero,add_zero, ←Nat.cast_sum,
   ←Finset.card_sigma]
  congr 1
  refine card_equiv ((Equiv.sigmaEquivProd ..).trans<| Fin.consEquiv λ _↦G) ?_
  aesop (add simp[Fin.sum_cons,Fin.forall_fin_succ])
lemma pn (s:Finset G) (n:ℕ) (f:G→R) :
  (Χ ((ἶ ((indicator s λ _↦(1:_))) n)) f)= ∑ a∈(piFinset λ _:Fin n↦s),τ (∑ i,a i) f:=by
 ext b
 simp only[ᾂ,j1,Si,ῗ,
  ←ᾚ, ←sum_const,Finset.sum_fiberwise']
variable [StarRing R]
end CommSemiring
section Semifield
variable [Semifield R] [CharZero R]
lemma vJ (s:Finset G) (n:ℕ) (f:G→R) :
  (Χ ((ἶ (mu s) n)) f)=𝔼 a∈piFinset (λ _:Fin n↦s),τ (∑ i,a i) f:=by
 simp only[mu,vm,Te,tn,pn,expect,
  card_piFinset_const,Rv]
 rw[←NNRat.cast_smul_eq_nnqsmul R]
 push_cast
 rfl
variable [StarRing R]
end Semifield
end
end
section
section
open Finset hiding card
open Function ProbabilityTheory Real
open Fintype (card)
open scoped BigOperators ComplexConjugate ENNReal NNReal translate
variable {α 𝕜 R E:Type*} [MeasurableSpace α]
namespace MeasureTheory
section NormedAddCommGroup
variable [NormedAddCommGroup E] {p q:ℝ≥0∞} {f g h:α→E}
noncomputable def ð (p:ℝ≥0∞) (f:α→E):ℝ:=lpNorm f p (uniformOn .univ)
@[simp] lemma yM:0≤(ð p f):=by simp[ð]
variable [Finite α]
omit [Finite α]
variable [Α α] [Δ α]
lemma mR (iu:p≠0) (hp:p≠∞) (f:α→E) :
  (ð p f)=(𝔼 i, ‖f i‖ ^p.toReal)^p.toReal⁻¹:=by
 simp[ð,uniformOn,lpNorm_eq_integral_norm_rpow_toReal iu hp .of_discrete,
  integral_fintype,cond_apply,expect_eq_sum_div_card,Ri, ←mul_sum,Measure.real]
lemma tp {p:ℝ≥0} (hp:p≠0) (f:α→E) :
  (ð p f)=(𝔼 i, ‖f i‖ ^(p:ℝ))^(p⁻¹ :ℝ):=
 mR (by simpa using hp) (by simp) _
lemma qs {p:ℝ≥0} (hp:p≠0) (f:α→E) :
  (ð p f)^(p:ℝ)=𝔼 i, ‖f i‖ ^(p:ℝ):=by
 rw[tp hp,S4]<;>positivity
lemma qW {p:ℕ} (hp:p≠0) (f:α→E) :
  (ð p f)^p=𝔼 i, ‖f i‖ ^p:=by
 simpa using qs (Nat.cast_ne_zero.2 hp) f
lemma ry (f:α→E):(ð 2 f)^2=𝔼 i, ‖f i‖ ^2:=by
 simpa using qW SD _
lemma tq (f:α→E):(ð 1 f)=𝔼 i, ‖f i‖:=by
 simp[mR]
omit [Δ α]
variable [Finite α]
lemma oE (f:α→E):(ð (∞) f)= ⨆ i, ‖f i‖:=by
 cases UC α<;>simp[ð,lpNorm_exponent_top_eq_essSup]
omit [Finite α]
end NormedAddCommGroup
end MeasureTheory
end
end
section
section
open Finset Function Real
open scoped BigOperators ComplexConjugate ENNReal NNReal NNRat
variable {α 𝕜 R E:Type*} [MeasurableSpace α]
namespace MeasureTheory
variable [NormedAddCommGroup E] {p q:ℝ≥0∞} {f g h:α→E}
noncomputable def aJ (p:ℝ≥0∞) (f:α→E):ℝ:=lpNorm f p .count
@[simp] lemma ᾧ:0≤(aJ p f):=by simp[aJ]
@[simp] lemma n7 (f:α→E):(aJ 0 f)=0:=by simp[aJ]
@[simp] lemma Ac (p:ℝ≥0∞):(aJ p ((0:α→E)))=0:=by simp[aJ]
lemma r6 (f g:α→E) (p:ℝ≥0∞):(aJ p (f-g))=(aJ p (g-f)):=by
 simp[aJ,lpNorm_sub_comm]
@[simp] lemma Ad (hf:StronglyMeasurable f) (p:ℝ≥0∞):(aJ p (λ i↦ ‖f i‖))=(aJ p f):=
 lpNorm_norm hf.aestronglyMeasurable _
section NormedField
variable [NormedField 𝕜] {p:ℝ≥0∞} {f g:α→𝕜}
lemma vK [Module 𝕜 E] [NormSMulClass 𝕜 E] (c:𝕜) (f:α→E) :
  (aJ p (c•f))= ‖c‖ *(aJ p f):=by simp[aJ,lpNorm_const_smul]
lemma zJ [NormedSpace ℝ E] (n:ℕ) (f:α→E) (p:ℝ≥0∞) :
  (aJ p (n•f))=n•(aJ p f):=by simp[aJ,lpNorm_nsmul]
variable [NormedSpace ℝ 𝕜]
end NormedField
section RCLike
variable {p:ℝ≥0∞}
@[simp] lemma Ae [Ζ R] (f:α→R):(aJ p (conj f))=(aJ p f):=lpNorm_conj ..
end RCLike
section DiscreteMeasurableSpace
variable [Α α] [Finite α]
lemma yN (hp:1≤p):(aJ p (f+g))≤(aJ p f)+(aJ p g):=
 lpNorm_add_le .of_discrete hp
lemma yO (hp:1≤p):(aJ p (f-g))≤(aJ p f)+(aJ p g):=
 lpNorm_sub_le .of_discrete hp
lemma wU [Module ℚ≥0 E] [NormedSpace ℝ E] {ι:Type*} {s:Finset ι} {f:ι→α→E}
  (hp:1≤p):(aJ p (𝔼 i∈s,f i))≤𝔼 i∈s,(aJ p (f i)):=
 lpNorm_expect_le (λ _ _↦ .of_discrete) hp
lemma er (hp:1≤p) :
  (aJ p (f-h))≤(aJ p (f-g))+(aJ p (g-h)):=
 lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub .of_discrete .of_discrete hp
end DiscreteMeasurableSpace
variable [Δ α]
variable [Α α]
lemma iv (iu:p≠0) (hp:p≠∞) (f:α→E) :
  (aJ p f)=(∑ i, ‖f i‖ ^p.toReal)^p.toReal⁻¹:=by
 simp[aJ,lpNorm_eq_integral_norm_rpow_toReal iu hp .of_discrete,integral_fintype]
lemma ln {p:ℝ≥0} (hp:p≠0) (f:α→E) :
  (aJ p f)=(∑ i, ‖f i‖ ^(p:ℝ))^(p⁻¹ :ℝ):=
 iv (by simpa using hp) (by simp) _
lemma iT {p:ℝ≥0} (hp:p≠0) (f:α→E) :
  (aJ p f)^(p:ℝ)= ∑ i, ‖f i‖ ^(p:ℝ):=by
 rw[ln hp,S4 (by positivity) (mod_cast hp)]
lemma gz {p:ℕ} (hp:p≠0) (f:α→E):(aJ p f)^p= ∑ i, ‖f i‖ ^p:=by
 simpa using iT (Nat.cast_ne_zero.2 hp) f
lemma ts (f:α→E):(aJ 2 f)^2= ∑ i, ‖f i‖ ^2:=by
 simpa using gz SD _
lemma ek (f:α→E):(aJ 1 f)= ∑ i, ‖f i‖:=by simp[iv]
omit [Δ α]
variable [Finite α]
lemma dw (f:α→E):(aJ (∞) f)= ⨆ i, ‖f i‖:=by
 cases UC α<;>simp[aJ,lpNorm_exponent_top_eq_essSup]
lemma vw {i:α}: ‖f i‖ ≤(aJ (∞) f):=by
 rw[dw]; exact le_ciSup (f:=λ i↦ ‖f i‖) (SA _) i
omit [Finite α]
variable [Δ α]
end MeasureTheory
end
end
section
section
open Finset Function Real
open scoped BigOperators ComplexConjugate ENNReal NNReal translate
namespace MeasureTheory
variable {ι G 𝕜 E R:Type*} [Finite ι] {I3:MeasurableSpace ι} [Α ι]
section Indicator
variable [Ζ R] {s:Finset ι} {p:ℝ≥0}
lemma kX (hp:p≠0) (s:Finset ι) :
  (aJ p ((indicator ((s:Set ι)) λ _↦(1:R))))^(p:ℝ)= #s:=by
 classical
 cases RR ι
 have: ∀ x,(ite (x∈s) 1 0:ℝ)^(p:ℝ) =
  ite (x∈s) (1^(p:ℝ)) (0^(p:ℝ)):=λ x↦by split_ifs<;>simp
 simp[iT,hp,ὅ,TU norm, -sum_const,
  card_eq_sum_ones]
lemma n8 (hp:p≠0) (s:Finset ι) :
  (aJ p ((indicator ((s:Set ι)) λ _↦(1:R))))= #s^(p⁻¹ :ℝ):=by
 refine(eq_rpow_inv ?_ ?_ ?_).2 (kX ?_ _)<;>first | positivity | exact ᾧ
lemma rA {p:ℕ} (hp:p≠0) (s:Finset ι) :
  (aJ p ((indicator ((s:Set ι)) λ _↦(1:R))))^(p:ℝ)= #s:=by
 simpa using kX (Nat.cast_ne_zero.2 hp) s
lemma r7 (s:Finset ι):(aJ 2 ((indicator ((s:Set ι)) λ _↦(1:R))))^2= #s:=by
 simpa using rA SD s
@[simp] lemma tU (s:Finset ι):(aJ 2 ((indicator ((s:Set ι)) λ _↦(1:R))))=Real.sqrt #s:=by
 rw[eq_comm,sqrt_eq_iff_eq_sq,r7]<;>first | positivity | exact ᾧ
lemma rB (hp:1≤p) (hs:s.Nonempty):(aJ p ((@mu R _ _) s))= #s^((p:ℝ)⁻¹ -1):=by
 rw[mu,vK ((#s)⁻¹ :R) ((indicator ((s:Set ι)) λ _↦(1:R))),n8,Up,
  RCLike.norm_natCast,TK, ←Real.rpow_sub_one]<;>positivity
lemma zK (hp:1≤p):(aJ p ((@mu R _ _) s))≤ #s^(p⁻¹ -1:ℝ):=by
 obtain rfl | hs:=s.eq_empty_or_nonempty
 ·simp only[FQ,Ac,card_empty,UH,SE]
  positivity
 ·exact(rB hp hs).le
@[simp] lemma uN (hs:s.Nonempty):(aJ 1 ((@mu R _ _) s))=1:=by
 simpa using rB SF hs
lemma rn:(aJ 1 ((@mu R _ _) s))≤1:=by simpa using zK SF
@[simp] lemma CD (hs:s.Nonempty):(aJ 2 ((@mu R _ _) s))= #s^(-2⁻¹ :ℝ):=by
 have:(2⁻¹ -1:ℝ)= -2⁻¹:=by norm_num
 simpa[sqrt_eq_rpow,this] using rB one_le_two (R:=R) hs
end Indicator
section aJ
variable {mG:MeasurableSpace G} [Α G] [Γ G] [Finite G]
 {p:ℝ≥0∞}
@[simp] lemma jY [NormedAddCommGroup E] (a:G) (f:G→E):(aJ p (τ a f))=(aJ p f):=by
 cases RR G
 obtain p | p:=p
 ·simp only[dw,UD,ῗ]
  exact(Equiv.subRight _).iSup_congr λ _↦rfl
 obtain rfl | hp:=Tf p 0
 ·simp only[n7,R2,ENNReal.coe_zero]
 ·simp only[ln hp,R2,ῗ]
  congr 1
  exact ἐ (Equiv.subRight _) _ _ λ _↦rfl
@[simp] lemma G4 [Ζ E] (f:G→E):(aJ p (conjneg f))=(aJ p f):=by
 cases RR G
 simp only[conjneg,Ae]
 obtain p | p:=p
 ·simp only[dw,UD]
  exact(Equiv.neg _).iSup_congr λ _↦rfl
 obtain rfl | hp:=Tf p 0
 ·simp only[n7,R2,ENNReal.coe_zero]
 ·simp only[ln hp,R2]
  congr 1
  exact ἐ (Equiv.neg _) _ _ λ _↦rfl
lemma pM [NormedAddCommGroup E] (hp:1≤p) {ι:Type*} (s:Finset ι)
  (a:ι→G) (f:G→E):(aJ p (τ (∑ i∈s,a i) f-f))≤ ∑ i∈s,(aJ p (τ (a i) f-f)):=by
 induction s using Finset.cons_induction with
 | empty=>simp
 | cons i s ih hs =>
 calc
  _=(aJ p (τ (∑ j∈s,a j) (τ (a i) f-f)+(τ (∑ j∈s,a j) f-f))):=by
   rw[sum_cons,translate_add',UE,sub_add_sub_cancel]
  _≤(aJ p (τ (∑ j∈s,a j) (τ (a i) f-f)))+ ∑ j∈s,(aJ p ((τ (a j) f-f))):=by
   grw[yN hp,hs]
  _=_:=by rw[jY,sum_cons]
end aJ
end MeasureTheory
end
end
section
section
open Finset Function MeasureTheory RCLike Real
open scoped ComplexConjugate ENNReal NNReal Pointwise translate
variable {G 𝕜:Type*} [Δ G] [Β G] [Γ G]
section RCLike
variable [Ζ 𝕜] {p:ℝ≥0∞}
lemma tV (f g:G→𝕜) (a:G):((al f g)) a=conj ⟪f,τ a g⟫_[𝕜]:=by
 simp[wInner_one_eq_sum,eL,ᾘ,ä]
lemma qt (f g h:G→𝕜):⟪f,(al g h)⟫_[𝕜]=⟪conj g,(Χ (conj f) (conj h))⟫_[𝕜]:=by
 calc
  _= ∑ b, ∑ a,g a*conj (h b)*conj (f (a-b)):=by
   simp_rw[wInner_one_eq_sum,Sb,lM]
   exact sum_comm
  _= ∑ b, ∑ a,conj (f a)*conj (h b)*g (a+b):=by
   simp_rw[←Fintype.sum_prod_type']
   exact ἐ ((Equiv.refl _).prodShear Equiv.subRight) _ _
    (by simp[mul_rotate,ᾭ])
  _=_:=by
   simp_rw[wInner_one_eq_sum,Sb,tS,TR,
    Tl]
   exact sum_comm
lemma wV (f g h:G→𝕜):⟪f,(Χ g h)⟫_[𝕜]=⟪conj g,(al (conj f) (conj h))⟫_[𝕜]:=by
 simp_rw[qt,Tl]
lemma vL (f g h:G→𝕜):⟪(al f g),h⟫_[𝕜]=⟪(Χ (conj h) (conj g)),conj f⟫_[𝕜]:=by
 rw[←conj_wInner_symm,qt,conj_wInner_symm]
lemma ro (f g h:G→𝕜):⟪(Χ f g),h⟫_[𝕜]=⟪(al (conj h) (conj g)),conj f⟫_[𝕜]:=by
 rw[←conj_wInner_symm,wV,conj_wInner_symm]
lemma kY (f g h:G→𝕜) :
  ⟪(al f g),h⟫_[𝕜]=⟪f,(Χ h g)⟫_[𝕜]:=by
 rw[vL]; simp[wInner_one_eq_sum,ä]
variable [MeasurableSpace G] [Α G]
lemma wW {p:ℝ≥0} (hp:1≤p) (f g:G→𝕜) :
  (aJ p ((Χ f g)))≤(aJ p f)*(aJ 1 g):=by
 obtain rfl | hp:=hp.eq_or_lt
 ·simp_rw[ENNReal.coe_one,ek,sum_mul_sum,ᾂ]
  calc
   _ ≤ ∑ x, ∑ y, ‖f y*g (x-y)‖:=
    sum_le_sum λ x _↦Rq _ _
   _=_:= ?_
  rw[sum_comm]
  simp_rw[ἑ]
  exact sum_congr rfl λ x _↦ἐ (Equiv.subRight x) _ _ λ _↦rfl
 have iu:=zero_lt_one.trans hp
 have h1:=ᾧ (p:=(p:ℝ≥0∞)) (f:=Χ f g)
 have h2:=ᾧ (p:=(p:ℝ≥0∞)) (f:=f)
 have ώ:=ᾧ (p:=1) (f:=g)
 rw[←rpow_le_rpow_iff _ _ iu,mul_rpow]
 any_goals positivity
 dsimp
 simp_rw[iT iu.ne',ᾂ]
 have I4:(p:ℝ).HolderConjugate (1-(p:ℝ)⁻¹)⁻¹:=
  ⟨by simp,mod_cast iu,by bound⟩
 have (x:G): ‖∑ y,f y*g (x-y)‖ ^(p:ℝ) ≤
   (∑ y, ‖f y‖ ^(p:ℝ)* ‖g (x-y)‖)*(∑ y, ‖g (x-y)‖)^(p-1:ℝ):=by
  rw[←le_rpow_inv_iff_of_pos,mul_rpow, ←rpow_mul,sub_one_mul,Tw]
  any_goals positivity
  calc
   _≤ ∑ y, ‖f y*g (x-y)‖:=Rq _ _
   _= ∑ y, ‖f y‖ * ‖g (x-y)‖ ^(p:ℝ)⁻¹ * ‖g (x-y)‖ ^(1-(p:ℝ)⁻¹):= ?_
   _≤_:=inner_le_Lp_mul_Lq _ _ _ I4
   _=_:= ?_
  ·congr with t
   rw[ἑ,à, ←rpow_add' (by positivity),TL,rpow_one]
   simp
  ·have:1-(p:ℝ)⁻¹ ≠0:=sub_ne_zero.2 (inv_ne_one.2<| NNReal.coe_ne_one.2 hp.ne').symm
   simp[mul_rpow,rpow_nonneg,iu.ne',this,abs_rpow_of_nonneg]
 calc
  _ ≤
    ∑ x,(∑ y, ‖f y‖ ^(p:ℝ)* ‖g (x-y)‖)*(∑ y, ‖g (x-y)‖)^(p-1:ℝ):=
   sum_le_sum λ i _↦this _
  _=_:= ?_
 have hg: ∀ x, ∑ y, ‖g (x-y)‖ =(aJ 1 g):=by
  simp_rw[ek]
  exact λ x↦ἐ (Equiv.subLeft _) _ _ λ _↦rfl
 have hg': ∀ y, ∑ x, ‖g (x-y)‖ =(aJ 1 g):=by
  simp_rw[ek]
  exact λ x↦ἐ (Equiv.subRight _) _ _ λ _↦rfl
 simp_rw[hg]
 rw[←sum_mul,sum_comm]
 simp_rw[←mul_sum,hg']
 rw[←sum_mul,à, ←rpow_one_add' (by positivity),TL]
 rw[TL]
 positivity
end RCLike
section Real
variable [MeasurableSpace G] [Α G] {f g:G→ℝ} {n:ℕ}
lemma yP (hf:0≤f) (hg:0≤g):(aJ 1 ((Χ f g)))=(aJ 1 f)*(aJ 1 g):=by
 have: ∀ x,0≤ ∑ y,f y*g (x-y):=λ x↦sum_nonneg λ y _↦å (hf _) (hg _)
 simp[ek, ←uM,ᾂ,norm_of_nonneg (this _),
  norm_of_nonneg (hf _),norm_of_nonneg (hg _)]
lemma xW (hf:0≤f) (hg:0≤g):(aJ 1 ((al f g)))=(aJ 1 f)*(aJ 1 g):=by
 simpa using yP hf (conjneg_nonneg.2 hg)
end Real
end
end
section
section
open Finset Function MeasureTheory RCLike Real
open scoped ComplexConjugate ENNReal NNReal NNRat
variable {ι 𝕜 S:Type*} [Δ ι]
namespace RCLike
variable [Ζ 𝕜] {I3:MeasurableSpace ι} [Α ι] {f:ι→𝕜}
@[simp] lemma xX {_:MeasurableSpace ι} [Α ι] (f:ι→𝕜) :
  ⟪f,f⟫_[𝕜]=(((aJ 2 f):ℝ):𝕜)^2:=by
 simp_rw[←UI]
 simp[ts,wInner_one_eq_sum]
end RCLike
namespace MeasureTheory
section Real
variable {α:Type*} {w3:MeasurableSpace α} [Α α] [Δ α] {p q:ℝ≥0∞}
 {f g:α→ℝ}
lemma ng (p q:ℝ≥0∞) [p.HolderConjugate q] :
  ⟪f,g⟫_[ℝ]≤(aJ p f)*(aJ q g):=by
 have Ὶ := Tk p q
 have Ῑ := Tk q p
 have yQ:⟪f,g⟫_[ℝ]= ∑ i,f i*g i:=by simp[wInner_one_eq_sum,ä]
 have N5 i:f i*g i≤ ‖f i‖ * ‖g i‖:=
  (SG _).trans_eq (by rw[SU]; simp[ᾮ])
 obtain rfl | Af:=Tf p ∞
 ·obtain rfl:q=1:=(Sx ∞ q).mp rfl
  simp only[yQ,ek,norm_eq_abs,dw,mul_sum]
  gcongr ∑ _, ?_ with i
  grw[SG (_*_),SU, ←le_ciSup (SA _)]
 obtain rfl | MF:=Tf q ∞
 ·obtain rfl:p=1:=(Sx ∞ p).mp rfl
  simp only[yQ,ek,norm_eq_abs,dw,sum_mul]
  gcongr ∑ _, ?_ with i
  grw[SG (_*_),SU, ←le_ciSup (SA _)]
 have N6 := UJ Ὶ Af
 have N7 := UJ Ῑ MF
 have uO:Real.HolderConjugate p.toReal q.toReal:=by
  simpa using ENNReal.HolderTriple.toReal (p:=p) (q:=q) (r:=1) N6 N7
 rw[yQ,iv Ὶ Af,iv Ῑ MF]
 simpa using Real.inner_le_Lp_mul_Lq Finset.univ f g uO
end Real
section mv
variable {α:Type*} {w3:MeasurableSpace α} [Α α] [Δ α] [Ζ 𝕜]
 {p q r:ℝ≥0∞} {f g:α→𝕜}
lemma vM (f g:α→𝕜): ‖⟪f,g⟫_[𝕜]‖ ≤⟪λ a↦ ‖f a‖,λ a↦ ‖g a‖⟫_[ℝ]:=by
 grw[wInner_one_eq_sum,Rq]; simp[wInner_one_eq_sum]
lemma lq (p q:ℝ≥0∞) [p.HolderConjugate q] :
  ‖⟪f,g⟫_[𝕜]‖ ≤(aJ p f)*(aJ q g):=
 calc
  _≤⟪λ a↦ ‖f a‖,λ a↦ ‖g a‖⟫_[ℝ]:=vM _ _
  _≤(aJ p (λ a↦ ‖f a‖))*(aJ q (λ a↦ ‖g a‖)):=ng _ _
  _=(aJ p f)*(aJ q g):=by simp_rw[Ad .of_discrete]
omit [Δ α]
variable [Finite α]
lemma yR (p q:ℝ≥0∞) [p.HolderTriple q r]:(aJ r (f*g))≤(aJ p f)*(aJ q g):=by
 cases RR α
 change lpNorm (f*g) r .count≤lpNorm f p .count*lpNorm g q .count
 have N5:AEStronglyMeasurable (f*g) .count:= .of_discrete
 grw[←toReal_eLpNorm .of_discrete, ←toReal_eLpNorm .of_discrete, ←toReal_eLpNorm .of_discrete,
  ←UK, ←qV (r:=r) .of_discrete .of_discrete]
 exact(ENNReal.mul_lt_top eLpNorm_lt_top_of_finite eLpNorm_lt_top_of_finite).ne
end mv
end MeasureTheory
end
end
section
open Finset Fintype Nat Real
variable {ι:Type*} {A:Finset ι} {m n:ℕ}
lemma step_one (ξ:A.Nonempty) (f:ι→ℝ) (a:Fin n→ι)
  (hf: ∀ i, ∑ a∈(piFinset λ _:Fin n↦A),f (a i)=0) :
  |∑ i,f (a i)| ^(m+1) ≤
   (∑ b∈(piFinset λ _:Fin n↦A), |∑ i,(f (a i)-f (b i))| ^(m+1))/ #A^n:=by
 let B:=(piFinset λ _:Fin n↦A)
 calc
  _
   = |∑ i,(f (a i)-(∑ b∈B,f (b i))/ #B)| ^(m+1):=by
   simp only[B,hf,sub_zero,zero_div]
  _= |(∑ b∈B, ∑ i,(f (a i)-f (b i)))/ #B| ^(m+1):=by
   simp only[sum_sub_distrib]
   rw[sum_const,UT,sum_comm,sum_div,ᾚ,card_piFinset,prod_const,
    Finset.card_univ,Fintype.card_fin,Rv,SH]
   positivity
  _= |∑ b∈B, ∑ i,(f (a i)-f (b i))| ^(m+1)/ #B^(m+1):=by
   rw[TE,TY,Nat.abs_cast]
  _≤(∑ b∈B, |∑ i,(f (a i)-f (b i))|)^(m+1)/ #B^(m+1):=by
   gcongr; exact IsAbsoluteValue.abv_sum _ _ _
  _=(∑ b∈B, |∑ i,(f (a i)-f (b i))|)^(m+1)/ #B^m/ #B:=by
   rw[div_div, ←pow_succ]
  _≤(∑ b∈B, |∑ i,(f (a i)-f (b i))| ^(m+1))/ #B:=by
   gcongr; exact TF (λ _ _↦ᾝ _) _
  _=_:=by simp[B]
lemma D6 (ξ:A.Nonempty) (f:ι→ℝ) (hf: ∀ i, ∑ a∈(piFinset λ _:Fin n↦A),f (a i)=0) (m:ℕ)
  (a:Fin n→ι) :
  |∑ i,f (a i)| ^m≤(∑ b∈(piFinset λ _:Fin n↦A), |∑ i,(f (a i)-f (b i))| ^m)/ #A^n:=by
 cases m
 ·simp only[pow_zero,sum_const,prod_const,Nat.smul_one_eq_cast,Finset.card_fin,
   card_piFinset, ←Rv]
  rw[div_self]
  rw[Nat.cast_ne_zero, ←Tx]
  exact ᾅ (Finset.card_pos.2 ξ) _
 exact step_one ξ f a hf
lemma Ag (A:Finset ι) (f:ι→ℝ) (ε:Fin n→ℝ)
  (hε:ε∈(piFinset λ _:Fin n↦(({-1,1}:Finset ℝ)))) (g:(Fin n→ℝ)→ℝ) :
  ∑ a∈(piFinset λ _:Fin n↦A), ∑ b∈(piFinset λ _:Fin n↦A),g (ε*(f ∘ a-f ∘ b)) =
   ∑ a∈(piFinset λ _:Fin n↦A), ∑ b∈(piFinset λ _:Fin n↦A),g (f ∘ a-f ∘ b):=by
 rw[←sum_product', ←sum_product']
 let n9:(Fin n→ι) × (Fin n→ι)→(Fin n→ι) × (Fin n→ι):=by
  intro xy
  exact(λ i↦if ε i=1 then xy.1 i else xy.2 i,λ i↦if ε i=1 then xy.2 i else xy.1 i)
 have h₁: ∀ a∈((piFinset λ _:Fin n↦A)) ×ˢ ((piFinset λ _:Fin n↦A)),n9 a∈((piFinset λ _:Fin n↦A)) ×ˢ ((piFinset λ _:Fin n↦A)):=by
  simp only[mem_product,mem_piFinset, ←forall_and,n9]
  intro a h i
  split_ifs
  ·exact h i
  ·exact(h i).symm
 have h₂: ∀ a∈((piFinset λ _:Fin n↦A)) ×ˢ ((piFinset λ _:Fin n↦A)),n9 (n9 a)=a:=λ a _↦by
  ext<;>simp only[n9]<;>split_ifs<;>rfl
 refine sum_nbij' n9 n9 h₁ h₁ h₂ h₂ ?_
 ·rintro ⟨a,b⟩ _
  congr with i:1
  simp only[mem_piFinset,mem_insert,mem_singleton] at hε
  simp only[Pi.mul_apply,Rw,Rh,n9]
  split_ifs with h
  ·simp[h]
  rw[(hε i).resolve_right h]
  ring
lemma FT (f:ι→ℝ) :
  ∑ a∈(piFinset λ _:Fin n↦A), ∑ b∈(piFinset λ _:Fin n↦A),(∑ i,(f (a i)-f (b i)))^(2*m) =
   2⁻¹ ^n* ∑ ε∈(piFinset λ _:Fin n↦(({-1,1}:Finset ℝ))),
    ∑ a∈(piFinset λ _:Fin n↦A), ∑ b∈(piFinset λ _:Fin n↦A),(∑ i,ε i*(f (a i)-f (b i)))^(2*m):=by
 let B:=(piFinset λ _:Fin n↦A)
 have: ∀ ε∈(piFinset λ _:Fin n↦(({-1,1}:Finset ℝ))),
  ∑ a∈B, ∑ b∈B,(∑ i,ε i*(f (a i)-f (b i)))^(2*m) =
   ∑ a∈B, ∑ b∈B,(∑ i,(f (a i)-f (b i)))^(2*m):=
  λ ε hε↦Ag A f _ hε λ z:Fin n→ℝ↦univ.sum z^(2*m)
 rw[Ò rfl this,sum_const,card_piFinset_const,card_pair,ᾚ,
  Rv,So,Te,inv_mul_cancel_left₀]
 ·positivity
 ·norm_num
lemma CE (f:ι→ℝ) :
  ∑ ε∈(piFinset λ _:Fin n↦(({-1,1}:Finset ℝ))),
   ∑ a∈(piFinset λ _:Fin n↦A), ∑ b∈(piFinset λ _:Fin n↦A),(∑ i,ε i*(f (a i)-f (b i)))^(2*m) =
   ∑ a∈(piFinset λ _:Fin n↦A), ∑ b∈(piFinset λ _:Fin n↦A), ∑ k∈piAntidiag univ (2*m),
     (multinomial univ k* ∏ t,(f (a t)-f (b t))^k t) *
      ∑ ε∈(piFinset λ _:Fin n↦(({-1,1}:Finset ℝ))), ∏ t,ε t^k t:=by
 simp only[@sum_comm _ _ (Fin n→ℝ) _ _ ((piFinset λ _:Fin n↦A)),sum_pow_eq_sum_piAntidiag]
 refine sum_congr rfl λ a _↦ ?_
 refine sum_congr rfl λ b _↦ ?_
 simp only[Ἀ,prod_mul_distrib, @sum_comm _ _ (Fin n→ℝ), ←mul_sum, ←sum_mul]
 refine sum_congr rfl λ k _↦ ?_
 rw[←à,ᾭ]
lemma D7 {k:Fin n→ℕ} :
  ∑ ε∈(piFinset λ _:Fin n↦(({-1,1}:Finset ℝ))), ∏ t,ε t^k t=2^n*ite (∀ i,Even (k i)) 1 0:=by
 calc
  _= ∏ i, ∑ j∈({-1,1}:Finset ℝ),j^k i:=by rw[←sum_prod_piFinset]
  _= ∏ i,if Even (k i) then 2 else 0:=by
   congr with i
   split_ifs<;>simp_all[sum_pair (show(-1:ℝ)≠1 by norm_num),one_add_one_eq_two]
  _=_:=by simp[Fintype.prod_ite_zero]
lemma FU {f:ι→ℝ} {a b:Fin n→ι} :
  ∑ k∈piAntidiag univ m,
    (multinomial univ λ a↦2*k a:ℝ)* ∏ i,(f (a i)-f (b i))^(2*k i) ≤
   m^m*(∑ i,(f (a i)-f (b i))^2)^m:=by
 rw[sum_pow_eq_sum_piAntidiag,mul_sum]
 refine sum_le_sum λ k hk↦ ?_
 rw[mem_piAntidiag] at hk
 simp only[←à,Ἂ]
 gcongr
 norm_cast
 refine multinomial_two_mul_le_mul_multinomial.trans ?_
 rw[hk.1]
lemma CF {f:ι→ℝ} {a b:Fin n→ι} :
  m^m*(∑ i,(f (a i)-f (b i))^2:ℝ)^m ≤
   m^m*2^m*(∑ i,(f (a i)^2+f (b i)^2))^m:=by
 rw[←Ἀ, ←Ἀ, ←Ἀ,à,mul_sum _ _ (2:ℝ)]
 gcongr with i
 exact add_sq_le.trans_eq (by simp)
lemma CI {f:ι→ℝ} {a b:Fin n→ι} :
  m^m*2^m*(∑ i,(f (a i)^2+f (b i)^2))^m ≤
   m^m*2^(m+(m-1)) *
    ((∑ i,f (a i)^2)^m+(∑ i,f (b i)^2)^m):=by
 rw[ᾫ, ←à _ _ (2^_),à _ (2^(m-1)),sum_add_distrib]
 gcongr
 refine add_pow_le ?_ ?_ m<;>positivity
lemma FV {f : ι → ℝ} (hm : 1 ≤ m) (ξ : A.Nonempty) :
    (∑ a ∈ (piFinset λ _ : Fin n ↦ A), ∑ b ∈ (piFinset λ _ : Fin n ↦ A), ∑ k ∈ piAntidiag univ m,
      ↑(multinomial univ λ i ↦ 2 * k i) * ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) / #A ^ n
        ≤ (4 * m) ^ m * ∑ a ∈ (piFinset λ _ : Fin n ↦ A), (∑ i, f (a i) ^ 2) ^ m:= by
  let B:= (piFinset λ _ : Fin n ↦ A)
  calc
    _
      ≤ (∑ a ∈ B, ∑ b ∈ B, m ^ m * 2 ^ (m + (m - 1)) *
          ((∑ i, f (a i) ^ 2) ^ m + (∑ i, f (b i) ^ 2) ^ m) : ℝ) / #A ^ n:= by
      gcongr; exact FU.trans <| CF.trans CI
    _ = _:= by
      simp only [mul_add, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
      rw [← mul_add, ← two_mul, ← mul_assoc 2, ← mul_assoc 2, mul_right_comm 2, ← _root_.pow_succ',
        add_assoc, Nat.sub_add_cancel hm, pow_add, ← mul_pow, ← mul_pow, card_piFinset, prod_const,
        Finset.card_univ, Fintype.card_fin, Nat.cast_pow, mul_div_cancel_left₀]
      · norm_num
        dsimp [B]
      · positivity
section
namespace Real
lemma tu (m:ℕ) (f:ι→ℝ) (hf: ∀ i, ∑ a∈(piFinset λ _:Fin n↦A),f (a i)=0) :
  ∑ a∈(piFinset λ _:Fin n↦A),(∑ i,f (a i))^(2*m) ≤
   (4*m)^m* ∑ a∈(piFinset λ _:Fin n↦A),(∑ i,f (a i)^2)^m:=by
 obtain rfl | hm:=m.eq_zero_or_pos
 ·simp
 have Ὲ:1≤ m:=by rwa[Ty]
 obtain rfl | ξ:=A.eq_empty_or_nonempty
 ·cases n<;>cases m<;>simp
 let B:=(piFinset λ _:Fin n↦A)
 calc
  ∑ a∈B,(∑ i,f (a i))^(2*m)
   ≤ ∑ a∈(piFinset λ _:Fin n↦A),(∑ b∈B, |∑ i,(f (a i)-f (b i))| ^(2*m))/ #A^n:=by
   gcongr; simpa[Ἂ,sq_abs] using D6 ξ f hf (2*m) _
  _=(∑ a∈(piFinset λ _:Fin n↦A), ∑ b∈(piFinset λ _:Fin n↦A), ∑ k∈piAntidiag univ (2*m) with ∀ i,2∣k i,
    multinomial univ (λ i↦k i)* ∏ t,(f (a t)-f (b t))^k t)/ #A^n:=by
   rw[←sum_div]
   simp only[Ἂ,sq_abs]
   simp only[←Ἂ]
   rw[FT,CE,ä,Te, ←ἱ,div_div]
   simp only[D7,Td,mul_zero,Ἣ, ←sum_filter, ←sum_mul,even_iff_two_dvd]
   rw[ä,mul_div_mul_left]
   positivity
  _=(∑ a∈(piFinset λ _:Fin n↦A), ∑ b∈(piFinset λ _:Fin n↦A), ∑ k∈(piAntidiag univ m).map
     ⟨(2•·),λ _ _ h↦funext λ i↦mul_right_injective₀ SD (SR h i)⟩,
    multinomial univ (λ i↦k i)* ∏ t,(f (a t)-f (b t))^k t)/ #A^n:=by
   rw[map_nsmul_piAntidiag_univ m (ι:=Fin n) (n:=2) SD]; congr!
  _=(∑ a∈(piFinset λ _:Fin n↦A), ∑ b∈(piFinset λ _:Fin n↦A), ∑ k∈piAntidiag univ m,
    multinomial univ (λ i↦2*k i)* ∏ t,(f (a t)-f (b t))^(2*k t))/ #A^n:=by
   simp
  _≤_:=FV Ὲ ξ
lemma g8 (hm:m≠0) (f:ι→ℝ) (hf: ∀ i, ∑ a∈(piFinset λ _:Fin n↦A),f (a i)=0) :
  ∑ a∈(piFinset λ _:Fin n↦A),(∑ i,f (a i))^(2*m) ≤
   (4*m)^m*n^(m-1)* ∑ a∈(piFinset λ _:Fin n↦A), ∑ i,f (a i)^(2*m):=by
 obtain _ | m:=m
 ·simp at hm
 obtain rfl | hn:=n.eq_zero_or_pos
 ·simp
 calc
  ∑ a∈(piFinset λ _:Fin n↦A),(∑ i,f (a i))^(2*(m+1))
   ≤ (4* ↑(m+1))^(m+1)* ∑ a∈(piFinset λ _:Fin n↦A),(∑ i,f (a i)^2)^(m+1):=
   tu _ f hf
  _≤(4* ↑(m+1))^(m+1)*(∑ a∈(piFinset λ _:Fin n↦A),n^m* ∑ i,f (a i)^(2*(m+1))):= ?_
  _≤(4* ↑(m+1))^(m+1)*n^m* ∑ a∈(piFinset λ _:Fin n↦A), ∑ i,f (a i)^(2*(m+1)):=by
   simp_rw[à,mul_sum]; rfl
 gcongr with a
 rw[←div_le_iff₀' (by positivity)]
 simpa only[Finset.card_fin,Ἂ] using
  TF (f:=λ i↦f (a i)^2) (s:=univ) (λ i _↦by positivity) m
end Real
namespace RCLike
variable {𝕜:Type*} [Ζ 𝕜]
lemma g8 (hm:m≠0) (f:ι→𝕜) (hf: ∀ i, ∑ a∈(piFinset λ _:Fin n↦A),f (a i)=0) :
  ∑ a∈(piFinset λ _:Fin n↦A), ‖∑ i,f (a i)‖ ^(2*m) ≤
   (8*m)^m*n^(m-1)* ∑ a∈(piFinset λ _:Fin n↦A), ∑ i, ‖f (a i)‖ ^(2*m):=by
 let f₁ x:ℝ:=re (f x)
 let f₂ x:ℝ:=im (f x)
 let B:=(piFinset λ _:Fin n↦A)
 have K0 i: ∑ a∈B,f₁ (a i)=0:=by rw[←ᾘ,hf,map_zero]
 have K1 i: ∑ a∈B,f₂ (a i)=0:=by rw[←ᾘ,hf,map_zero]
 have h₁:=Real.g8 hm _ K0
 have h₂:=Real.g8 hm _ K1
 simp only[Ἂ,RCLike.norm_sq_eq_def]
 simp only[←sq,ᾘ,ᾘ]
 calc
  ∑ a∈B,((∑ i,re (f (a i)))^2+(∑ i,im (f (a i)))^2)^m ≤
    ∑ a∈B,
     2^(m-1)*(((∑ i,re (f (a i)))^2)^m+((∑ i,im (f (a i)))^2)^m):=by
   gcongr with a; apply add_pow_le<;>positivity
  _=2^(m-1)*(∑ a∈B,(∑ i,re (f (a i)))^(2*m) +
     ∑ a∈B,(∑ i,im (f (a i)))^(2*m)):=by
   simp only[←sum_add_distrib,mul_sum,Ἂ]
  _≤2^(m-1)*((4*m)^m*n^(m-1) *
     ∑ a∈B, ∑ i,re (f (a i))^(2*m)+(4*m)^m*n^(m-1) *
     ∑ a∈B, ∑ i,im (f (a i))^(2*m)):=by gcongr
  _=2^(m-1)*((4*m)^m*n^(m-1) *
     ∑ a∈B, ∑ i,(re (f (a i))^(2*m)+im (f (a i))^(2*m))):=by
   simp_rw[sum_add_distrib,Tc]
  _≤2^(m-1)*((4*m)^m*n^(m-1) *
     ∑ a∈B, ∑ i,2*(re (f (a i))^2+im (f (a i))^2)^m):=by
   simp_rw[Ἂ]; gcongr; apply pow_add_pow_le'<;>positivity
  _=(8*m)^m*n^(m-1)* ∑ a∈B, ∑ i,(re (f (a i))^2+im (f (a i))^2)^m:=by
   simp_rw[←mul_sum,show(8:ℝ)=2*4 by norm_num,Ἀ, ←R0 hm (2:ℝ)]
   ring
end RCLike
end
end
section
open scoped Pointwise Combinatorics.Additive translate
section
variable {α:Type*} {g:α→ℝ} {c ε:ℝ} {A:Finset α}
open Finset
lemma D8 (hc:0<c) (hg: ∀ a∈A,0≤g a) (h: ∑ a∈A,g a≤ε*c* #A) :
  (1-ε)* #A≤ #{a∈A | g a≤c}:=by
 classical
 have:=h.trans'
  (sum_le_sum_of_subset_of_nonneg (filter_subset (¬g ·≤c) A) λ i hi _↦hg _ hi)
 have:=
  (card_nsmul_le_sum _ _ c (by simp+contextual [le_of_lt])).trans this
 rw[ᾚ,ᾭ] at this
 have:=TZ this hc
 rw[filter_not,cast_card_sdiff (filter_subset _ _)] at this
 linarith only[this]
lemma x0 (hc:0≤c) (hε:0≤ε) (hg: ∀ a∈A,0≤g a)
  (h: ∑ a∈A,g a≤ε*c* #A):(1-ε)* #A≤ #{a∈A | g a≤c}:=by
 rcases hc.lt_or_eq with (hc | rfl)
 ·exact D8 hc hg h
 simp only[mul_zero,zero_mul] at h
 classical
 rw[one_sub_mul,sub_le_comm, ←cast_card_sdiff (filter_subset _ A), ←filter_not,
  filter_false_of_mem]
 ·simp only[card_empty,UH]; positivity
 intro i hi
 rw[(sum_eq_zero_iff_of_nonneg hg).1 (h.antisymm (sum_nonneg hg)) i hi]
 simp
end
open Finset Real
open scoped BigOperators Pointwise NNReal ENNReal
variable {G:Type*} [Δ G] {A S:Finset G} {f:G→ℂ} {x ε K:ℝ} {k m:ℕ}
section
variable [MeasurableSpace G] [Α G]
open MeasureTheory in
lemma BC (hε:0<ε) (hm:1≤ m) (hk:64*m/ε^2≤k) :
  (8*m)^m*k^(m-1)* #A^k*k*(2*(aJ (2*m) f):ℝ)^(2*m) ≤
   1/2*((k*ε)^(2*m)* ∑ i:G, ‖f i‖ ^(2*m))* #A^k:=by
 have yS:((2*m:ℕ):ℝ≥0∞)=2*m:=by rw[Rm,So]
 have Ὲ:2*m≠0:=by
  refine ῐ two_pos.ne' ?_
  rw[←Tx, ←Ty]
  exact hm
 rw[Ἀ (2:ℝ), ←yS, ←gz Ὲ f, ←à, ←à,
  ᾭ _ (#A^k:ℝ),ᾭ _ (#A^k:ℝ),
  ᾭ _ (#A^k:ℝ)]
 rw[div_le_iff₀' (by positivity)] at hk
 have N8:=ᾧ (p:=((2*m:ℕ):ℝ≥0∞)) (f:=f)
 gcongr ?_*_*_
 calc
  (8*m:ℝ)^m*k^(m-1)*k*2^(2*m)
   = (8*m)^m*2^(2*m)*(k^(m-1)*k):=by ring
  _=(64*m*k/2)^m:=by rw[R0 (by omega),Ἂ, ←Ἀ]; ring
  _≤(ε^2*k*k/2)^m:=by gcongr
  _=(k*ε)^(2*m)/2^m:=by ring_nf; simp_rw[ῆ]
  _≤(k*ε)^(2*m)/2^1:=by gcongr; norm_num
  _=1/2*(k*ε)^(2*m):=by ring
end
variable [Β G] [Γ G]
lemma xk (hm:1≤ m) (x:G) :
  ∑ a∈(piFinset λ _:Fin k↦A), ‖∑ i,f (x-a i)-(k•((Χ (mu A) f))) x‖ ^(2*m) ≤
   (8*m)^m*k^(m-1) *
    ∑ a∈(piFinset λ _:Fin k↦A), ∑ i, ‖f (x-a i)-((Χ (mu A) f)) x‖ ^(2*m):=by
 let f':G→ℂ:=λ a↦f (x-a)-((Χ (mu A) f)) x
 refine(RCLike.g8 (by linarith only[hm]) f' ?_).trans_eq' ?_
 ·intro i
  rw[Fintype.sum_piFinset_apply,sum_sub_distrib]
  simp only[sum_const]
  rw[←RD (card A), ←tn,l5,ᾂ]
  simp only[SS,ὅ,mem_coe]
  rw[←sum_filter,filter_mem_eq_inter,univ_inter,sub_self,smul_zero]
 congr with a:1
 simp only[sum_sub_distrib,RD,sum_const,card_fin,f']
variable [MeasurableSpace G]
namespace gl
def CJ (k m:ℕ) (ε:ℝ) (f:G→ℂ) (A:Finset G) (a:Fin k→G):Prop:=
 (aJ (2*m) (λ x:G↦ ∑ i,f (x-a i)-(k•((Χ (mu A) f))) x))≤k*ε*(aJ (2*m) f)
noncomputable instance:DecidablePred (CJ k m ε f A):=Classical.decPred _
noncomputable def l (k m:ℕ) (ε:ℝ) (f:G→ℂ) (A:Finset G):Finset (Fin k→G):=
 {x∈(piFinset λ _:Fin k↦A) | CJ k m ε f A x}
lemma yT (hε:0<ε) (hm:1≤ m)
  (h: ∑ a∈(piFinset λ _:Fin k↦A),
    ((aJ (2*m) (λ x:G↦ ∑ i:Fin k,f (x-a i)-(k•((Χ (mu A) f))) x))^(2*m):ℝ) ≤
   1/2*(k*ε*(aJ (2*m) f))^(2*m)* #A^k) :
  (#A^k:ℝ)/2≤ #(l k m ε f A):=by
 rw[←Rv, ←TG] at h
 have N8:=ᾧ (p:=2*m) (f:=f)
 have:=x0 (by positivity) (by norm_num)
  (λ _ _↦ἥ ᾧ _) h
 norm_num1 at this
 rw[TG,ä,mul_one_div,Rv] at this
 refine this.trans_eq ?_
 rw[l]
 congr with a:3
 refine pow_le_pow_iff_left₀ ?_ ?_ ?_<;>first | positivity | exact ᾧ
variable [Α G]
open MeasureTheory in
lemma xl (hm:1≤ m) (ξ:A.Nonempty) :
  (8*m)^m*k^(m-1)* ∑ a∈(piFinset λ _:Fin k↦A), ∑ i,(aJ (2*m) (τ (a i) f-(Χ (mu A) f)))^(2*m) ≤
   (8*m)^m*k^(m-1)* ∑ _a∈(piFinset λ _:Fin k↦A), ∑ _i:Fin k,(2*(aJ (2*m) f))^(2*m):=by
 have yS:((2*m:ℕ):ℝ≥0∞)=2*m:=by rw[Rm,So]
 have Ὲ:1<2*m:=(ὄ 2 hm).trans_lt'<| by norm_num1
 have M1:(1:ℝ≥0∞)≤2*m:=by rw[←yS,Nat.one_le_cast]; exact Ὲ.le
 gcongr
 ·exact ᾧ
 refine(yO M1).trans ?_
 rw[jY,ΐ (aJ (2*m) f),add_le_add_iff_left]
 have K2:((2*m:ℝ≥0):ℝ≥0∞)=2*m:=by
  rw[ENNReal.coe_mul,ENNReal.coe_two,ENNReal.coe_natCast]
 have:(1:ℝ≥0)<2*m:=by
  rw[←So, ←Rm,Nat.one_lt_cast]
  exact Ὲ
 rw[←K2,ᾼ]
 refine(wW this.le _ _).trans ?_
 rw[uN ξ,Ἣ]
open MeasureTheory in
lemma Ho (hε:0<ε) (hm:1≤ m) (hk:(64:ℝ)*m/ε^2≤k) :
  (#A^k:ℝ)/2≤ #(l k m ε f A):=by
 have:0<k:=by
  rw[← @Nat.cast_pos ℝ]
  refine hk.trans_lt' ?_
  refine ὗ (Ἃ (by norm_num1) ?_) (ᾅ hε _)
  rw[Nat.cast_pos, ←Ty]
  exact hm
 rcases A.eq_empty_or_nonempty with (rfl | ξ)
 ·simp[zero_pow this.ne']
 refine yT hε hm ?_
 have Ὲ:2*m≠0:=by linarith
 have yS:((2*m:ℕ):ℝ≥0∞)=2*m:=by rw[Rm,So]
 rw[←yS,Ἀ]
 simp only[gz Ὲ]
 rw[sum_comm]
 have: ∀ x:G, ∑ a∈(piFinset λ _:Fin k↦A),
   ‖∑ i,f (x-a i)-(k•((Χ (mu A) f))) x‖ ^(2*m) ≤
  (8*m)^m*k^(m-1) *
   ∑ a∈(piFinset λ _:Fin k↦A), ∑ i, ‖f (x-a i)-((Χ (mu A) f)) x‖ ^(2*m):=
  xk hm
 refine(sum_le_sum λ x _↦this x).trans ?_
 rw[←mul_sum]
 simp only[@sum_comm _ _ G]
 have (a:Fin k→G) (i:Fin k) :
   ∑ x, ‖f (x-a i)-((Χ (mu A) f)) x‖ ^(2*m)=(aJ (2*m) (τ (a i) f-(Χ (mu A) f)))^(2*m):=by
  rw[←yS,gz Ὲ]
  simp only[Rw,ῗ]
 simp only[this]
 have :
  (8*m)^m*k^(m-1)* ∑ a∈(piFinset λ _:Fin k↦A), ∑ i,(aJ (2*m) (τ (a i) f-(Χ (mu A) f)))^(2*m) ≤
   (8*m)^m*k^(m-1)* ∑ a∈(piFinset λ _:Fin k↦A), ∑ i,(2*(aJ (2*m) f))^(2*m):=
  xl hm ξ
 refine Sj (mod_cast this) ?_
 simpa[à] using BC hε hm hk
open MeasureTheory in
lemma pN {t:G} {a:Fin k→G} (ha:a∈l k m ε f A)
  (ἠ:(a+λ _↦t)∈l k m ε f A) (hk:0<k) (hm:1≤ m) :
  (aJ (2*m) (τ (-t) ((Χ (mu A) f))-(Χ (mu A) f)))≤2*ε*(aJ (2*m) f):=by
 let f₁:G→ℂ:=λ x↦ ∑ i,f (x-a i)
 let f₂:G→ℂ:=λ x↦ ∑ i,f (x-a i-t)
 have hp:(1:ℝ≥0∞)≤2*m:=by norm_cast; linarith
 have h₁:(aJ (2*m) (f₁-k•((Χ (mu A) f))))≤k*ε*(aJ (2*m) f):=by
  rw[l,UU] at ha ; exact ha.2
 have h₂:(aJ (2*m) (f₂-k•((Χ (mu A) f))))≤k*ε*(aJ (2*m) f):=by
  rw[l,UU,CJ] at ἠ
  refine ἠ.2.trans_eq' ?_
  congr with i:1
  simp[sub_sub,f₂]
 have h₃:f₂=τ t f₁:=by
  ext i:1
  rw[ῗ]
  refine Ò rfl λ j _↦ ?_
  rw[sub_right_comm]
 have Hp:(aJ (2*m) (τ t f₁-k•((Χ (mu A) f))))=(aJ (2*m) (τ (-t) (τ t f₁-k•((Χ (mu A) f))))):=by
  rw[jY]
 have M3:(aJ (2*m) (τ t f₁-k•((Χ (mu A) f))))=(aJ (2*m) (f₁-τ (-t) (k•((Χ (mu A) f))))):=by
  rw[Hp,UE,translate_translate]
  simp
 have NM:(aJ (2*m) (τ (-t) (k•((Χ (mu A) f)))-f₁))≤k*ε*(aJ (2*m) f):=by
  rwa[r6, ←M3, ←h₃]
 have:(0:ℝ)<k:=by positivity
 refine Uj ?_ this
 rw[←ᾚ, ←zJ _ (_-(Χ (mu A) f)),nsmul_sub, ←
  translate_smul_right (-t) ((Χ (mu A) f)) k,à,Ῐ,ΐ ((k:ℝ)*_), ←
  à]
 calc
  _
   ≤ (aJ (2*m) (τ (-t) (k•((Χ (mu A) f)))-f₁))+(aJ (2*m) (f₁-k•((Χ (mu A) f)))):=
   er (mod_cast hp)
  _≤k*ε*(aJ (2*m) f)+k*ε*(aJ (2*m) f):=by gcongr
end gl
end
section
section
open Finset Function Real
open scoped ComplexConjugate NNReal Pointwise
variable {G R:Type*} [Δ G] [Β G] [Γ G]
section lr
variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {f g:G→R}
lemma zL (hf:0≤f) (hg:0≤g):0≤(Χ f g):=
 λ _a↦sum_nonneg λ _x _↦å (hf _) (hg _)
lemma pC (hf:0≤f) (hg:0≤g) (a:G):0≤((Χ f g)) a:=
 zL hf hg _
variable [StarRing R] [StarOrderedRing R]
lemma iN (hf:0≤f) (hg:0≤g):0≤(al f g):=
 λ _a↦sum_nonneg λ _x _↦å (hf _)<| star_nonneg_iff.2<| hg _
lemma dM (hf:0≤f) (hg:0≤g) (a:G):0≤((al f g)) a:=
 iN hf hg _
end lr
section iw
variable [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] {f g:G→R}
@[simp] lemma tW (hf:0≤f) (hg:0≤g) :
  support ((Χ f g))=support f+support g:=by
 refine(tT _ _).antisymm ?_
 rintro _ ⟨a,ha,b,hb,rfl⟩
 rw[mem_support,r5]
 exact Uq<| sum_pos' (λ c _↦å (hf _)<| hg _) ⟨0,mem_univ _,
  Ἃ ((hf _).lt_of_ne'<| by simpa using ha)<| (hg _).lt_of_ne'<| by simpa using hb⟩
variable [StarRing R] [StarOrderedRing R]
@[simp] lemma f8 (hf:0≤f) (hg:0≤g):support ((al f g))=support f-support g:=by
 simpa[Ἱ] using tW hf (conjneg_nonneg.2 hg)
end iw
end
end
section
section
open Finset Function Real MeasureTheory
open scoped ComplexConjugate ENNReal NNReal translate
variable {α 𝕜 E:Type*} [MeasurableSpace α]
section NormedAddCommGroup
variable [NormedAddCommGroup E] {p q:ℝ≥0∞} {w:α→ℝ≥0} {f g h:α→E}
noncomputable def b0 (p:ℝ≥0∞) (w:α→ℝ≥0) (f:α→E):ℝ:=
 lpNorm f p<| .sum λ i↦w i• .dirac i
@[simp] lemma tX:0≤(b0 p w f):=by simp[b0]
@[simp] lemma I5 (w:α→ℝ≥0):(b0 p w ((0:α→E)))=0:=by simp[b0]
@[simp] lemma KR (w:α→ℝ≥0) (f:α→E):(b0 p w (-f))=(b0 p w f):=by
 simp[b0]
lemma Ah [NormedField 𝕜] [NormedSpace 𝕜 E] (c:𝕜) (f:α→E) (p:ℝ≥0∞) (w:α→ℝ≥0) :
  (b0 p w (c•f))= ‖c‖₊*(b0 p w f):=lpNorm_const_smul ..
lemma zM [NormedSpace ℝ E] (n:ℕ) (f:α→E) (p:ℝ≥0∞) (w:α→ℝ≥0) :
  (b0 p w (n•f))=n•(b0 p w f):=lpNorm_nsmul ..
variable [Finite α]
variable [Δ α] [Α α]
lemma lu (iu:p≠0) (hp:p≠∞) (w:α→ℝ≥0) (f:α→E) :
  (b0 p w f)=(∑ i,w i• ‖f i‖ ^p.toReal)^p.toReal⁻¹:=by
 simp[b0,lpNorm_eq_integral_norm_rpow_toReal iu hp .of_discrete,RG,
  integral_finsetSum_measure]
lemma r8 {p:ℝ≥0} (hp:p≠0) (w:α→ℝ≥0) (f:α→E) :
  (b0 p w f)^(p:ℝ)= ∑ i,w i• ‖f i‖ ^(p:ℝ):=by
 rw[lu (mod_cast hp) (by simp),ENNReal.coe_toReal,
  S4 _ (mod_cast hp)]
 simp only[RG,ᾞ]
 positivity
lemma jd {p:ℕ} (hp:p≠0) (w:α→ℝ≥0) (f:α→E) :
  (b0 p w f)^p= ∑ i,w i• ‖f i‖ ^p:=by
 simpa using r8 (Nat.cast_ne_zero.2 hp) w f
omit [Δ α]
section one_le
lemma yU (hp:1≤p) (w:α→ℝ≥0) (f g:α→E) :
  (b0 p w (f+g))≤(b0 p w f)+(b0 p w g):=lpNorm_add_le .of_discrete hp
lemma qX (hp:1≤p) (w:α→ℝ≥0) (f g:α→E) :
  (b0 p w f)≤(b0 p w (f+g))+(b0 p w g):=by simpa using yU hp w (f+g) (-g)
end one_le
end NormedAddCommGroup
end
end
section
section
namespace Finset
variable {α R:Type*} [Δ α] [Semiring R]
@[simp] lemma rp (s:Finset α): ∑ x,(indicator ((s:Set α)) λ _↦(1:R)) x= #s:=by
 classical simp[ὅ]
lemma lN (s:Finset α): #s= ∑ x,(indicator ((s:Set α)) λ _↦(1:_)) x:=
 (rp _).symm
end Finset
end
end
section
section
namespace Set
variable {α M:Type*} [Zero M] [One M]
section Preorder
variable [Preorder M] [ZeroLEOneClass M] {s:Set α}
@[simp] lemma cY:0≤ s.indicator (λ _↦(1:M)):=
 indicator_nonneg (by simp)
end Preorder
end Set
end
end
section
section
open Finset Fintype Function MeasureTheory RCLike Real
open scoped ENNReal NNReal Pointwise
variable {G:Type*} [Β G] [Δ G] [Γ G] {p:ℕ} {Τ ζ A:Finset G}
 {ε δ:ℝ}
private def c (p:ℕ) (A:Finset G) (s:Fin p→G):Finset G:=univ.inf λ i↦s i+ᵥ A
private lemma Ca (p:ℕ) (Τ ζ A:Finset G) (f:G→ℝ) :
  ∑ s,⟪(al ((indicator (↑(Τ∩c p A s)) λ _↦(1:(ℝ)))) ((indicator (↑(ζ∩c p A s)) λ _↦(1:_)))),f⟫_[ℝ] =
   (#Τ* #ζ)• ∑ x,((al ((@mu (ℝ) _ _) Τ) (mu ζ))) x*((al ((indicator A λ _↦(1:_))) ((indicator A λ _↦(1:_))))) x^p*f x:=by
 simp_rw[à]
 simp only[wInner_one_eq_sum,inner_apply',R3,mul_sum,sum_mul,smul_sum,
  @sum_comm _ _ (Fin p→G),lM,rm,Fintype.sum_pow,
  Set.rj]
 congr with ey
 congr with b₂
 refine ἐ (Equiv.neg _) _ _ λ s↦ ?_
 rw[←TJ,mul_smul_mul_comm,qr,qr,
  coe_inter,coe_inter,Set.iq,Set.iq,
  Q7,prod_mul_distrib]
 simp[c,mQ,Ἱ,à,ῒ]
private lemma K3 (p:ℕ) (B A:Finset G): ∑ s, #(B∩c p A s)= #A^p* #B:=by
 simp only[lN,Set.iq,c,mQ,
  mul_sum,sum_mul,coe_inter,coe_vadd_finset,sum_pow', @sum_comm G,SB,
  ←sU,ῗ]
 congr with x
 exact ἐ (Equiv.subLeft λ _↦x) _ _ λ s↦ä _ _
private lemma x1 (p:ℕ) (B A:Finset G) :
  ∑ s,(#(B∩c p A s):ℝ)= #A^p* #B:=by
 rw[←Nat.cast_sum,K3]; norm_cast
variable [MeasurableSpace G]
noncomputable def s (p:ℝ≥0) (ε:ℝ) (Τ ζ A:Finset G):Finset G:=
 {x | (1-ε)*(b0 p ((al (mu Τ) (mu ζ))) ((al ((indicator ((A:Set G)) λ _↦(1:(ℝ)))) ((indicator A λ _↦(1:_))))))<((al ((indicator A λ _↦(1:_))) ((indicator A λ _↦(1:_))))) x}
@[simp] lemma K4 {p:ℝ≥0} {ε:ℝ} {Τ ζ A:Finset G} {x:G} :
  x∈s p ε Τ ζ A ↔
   (1-ε)*(b0 p ((al (mu Τ) (mu ζ))) ((al ((indicator ((A:Set G)) λ _↦(1:(ℝ)))) ((indicator A λ _↦(1:_))))))<((al ((indicator A λ _↦(1:_))) ((indicator A λ _↦(1:_))))) x:=by simp[s]
lemma I6 {p : ℝ≥0} {ε : ℝ} {Τ ζ A : Finset G} {x : G} :
    x ∈ s p ε Τ ζ A ↔ (1 - ε) * (_root_.b0 p ((_root_.al (_root_.mu Τ) (_root_.mu ζ))) ((_root_.al ((@_root_.mu (ℝ) _ _) A) (_root_.mu A)))) < ((_root_.al (_root_.mu A) (_root_.mu A))) x:= by
  obtain rfl | ξ:= A.eq_empty_or_nonempty
  · simp
  · simp [← l5, -nsmul_eq_mul, oB, oC, zM, ξ.card_pos]
variable [Α G]
private lemma jq (hp:p≠0) (É:(Τ∩ζ).Nonempty) (ξ:A.Nonempty) :
  (0:ℝ)<(b0 p ((al (mu Τ) (mu ζ))) ((al ((indicator A λ _↦(1:(ℝ)))) ((indicator A λ _↦(1:_))))))^p:=by
 rw[jd (by positivity)]
 refine sum_pos' (λ x _↦by positivity) ⟨0,mem_univ _,smul_pos ?_<| ᾅ ?_ _⟩
 ·rwa[Tx, ←Ur,f8,jo,jo,
   ←coe_sub,mem_coe,zero_mem_sub_iff,not_disjoint_iff_nonempty_inter]<;>exact õ
 ·rw[norm_pos_iff, ←Ur,f8,Set.j0]
  any_goals exact Set.cY
  exact ξ.to_set.zero_mem_sub
lemma N9 (hp₂:2≤p) (f:G→ℝ≥0) (hf: ∃ x,x∈Τ-ζ∧x∈A-A∧x∈f.support)
  (É:(Τ∩ζ).Nonempty) (ξ:A.Nonempty) :
  ∃ aX,aX⊆Τ∧ ∃ a3,a3⊆ζ ∧
   ⟪(al ((@mu (ℝ) _ _) aX) (mu a3)),(↑) ∘ f⟫_[ℝ]*(b0 p ((al (mu Τ) (mu ζ))) ((al ((indicator A λ _↦(1:(ℝ)))) ((indicator A λ _↦(1:_))))))^p
    ≤ 2* ∑ x,((al (mu Τ) (mu ζ))) x*((al ((indicator A λ _↦(1:(ℝ)))) ((indicator A λ _↦(1:_))))) x^p*f x ∧
   (4:ℝ) ⁻¹ *(b0 p ((al (mu Τ) (mu ζ))) ((al ((indicator A λ _↦(1:(ℝ)))) ((indicator A λ _↦(1:_))))))^(2*p)/ #A^(2*p)
    ≤ #aX/ #Τ ∧
   (4:ℝ) ⁻¹ *(b0 p ((al (mu Τ) (mu ζ))) ((al ((indicator A λ _↦(1:(ℝ)))) ((indicator A λ _↦(1:_))))))^(2*p)/ #A^(2*p)
    ≤ #a3/ #ζ:=by
 have:=É.mono inter_subset_left
 have:=É.mono inter_subset_right
 have iu:p≠0:=by positivity
 have:=jq iu É ξ
 set M:ℝ:=
  2 ⁻¹ *(b0 p ((al (mu Τ) (mu ζ))) ((al ((indicator A λ _↦(1:(ℝ)))) ((indicator A λ _↦(1:_))))))^p*(sqrt #Τ*sqrt #ζ)/ #A^p
   with Ai
 have ἄ:0<M:=by rw[Ai]; positivity
 replace hf:0< ∑ x,((al ((@mu (ℝ) _ _) Τ) (mu ζ))) x*((al ((indicator A λ _↦(1:_))) ((indicator A λ _↦(1:_))))) x^p*f x:=by
  have:0≤(al ((@mu (ℝ) _ _) Τ) (mu ζ))*((al ((indicator A λ _↦(1:_))) ((indicator A λ _↦(1:_)))))^p*(↑) ∘ f:=
   å (å (iN õ õ)<| ἥ
    (iN Set.cY Set.cY) _) λ _↦by simp
  refine Fintype.sum_pos<| this.lt_iff_ne'.2<| support_nonempty_iff.1 ?_
  simp only[support_comp_eq,Set.Nonempty,Tm,support_mul',f8,
   Set.cY,õ,Set.j0,jo,
   NNReal.coe_eq_zero,iff_self,forall_const,Set.mem_inter_iff, ←coe_sub,mem_coe,
   support_pow' _ iu,hf]
 set aX:=λ s↦Τ∩c p A s
 set a3:=λ s↦ζ∩c p A s
 set g:(Fin p→G)→ℝ:=λ s↦ #(aX s)* #(a3 s) with D9
 have hg: ∀ s,0≤g s:=λ s↦by rw[D9]; dsimp; positivity
 have Aj: ∑ s,g s= #Τ* #ζ*(b0 p ((al (mu Τ) (mu ζ))) ((al ((indicator A λ _↦(1:(ℝ)))) ((indicator A λ _↦(1:_))))))^p:=by
  have Ea:0≤(al ((indicator ((A:Set G)) λ _↦(1:(ℝ)))) ((indicator A λ _↦(1:_)))):=
   iN Set.cY Set.cY
  simpa only[jd iu,norm_of_nonneg (Ea _),RG,
   NNReal.lg,NNReal.iF,wInner_one_eq_sum,Rt,inner_apply',
   ←coe_inter,conj_to_real,Ἣ,jJ,rp,ᾚ,
   Rm,g,aX,a3] using! Ca p Τ ζ A 1
 suffices ∑ s,⟪(al ((indicator (aX s) λ _↦(1:(ℝ)))) ((indicator (a3 s) λ _↦(1:_)))),(↑) ∘ f⟫_[ℝ]*(b0 p ((al (mu Τ) (mu ζ))) ((al ((indicator A λ _↦(1:(ℝ)))) ((indicator A λ _↦(1:_))))))^p
  < ∑ s,(indicator (({s | M^2≤g s}:Finset _)) λ _↦(1:_)) s*g s *
    (2* ∑ x,((al (mu Τ) (mu ζ))) x*((al ((indicator A λ _↦(1:(ℝ)))) ((indicator A λ _↦(1:_))))) x^p*f x) by
  obtain ⟨s, -,hs⟩:=exists_lt_of_sum_lt this
  refine ⟨_,inter_subset_left (s₂:=c p A s),_,inter_subset_left (s₂:=c p A s), ?_⟩
  simp only[ὅ,SS] at hs
  split_ifs at hs with h; swap
  ·simp only[zero_mul,wInner_one_eq_sum,Rh,SV,
    R3] at hs
   have:0≤(al ((indicator ((aX s:Set G)) λ _↦(1:(ℝ)))) ((indicator (a3 s) λ _↦(1:_)))):=
    iN Set.cY Set.cY
   cases hs.not_ge<|
    å (sum_nonneg λ x _↦å (this _)<| by positivity)<| by positivity
  have:(4:ℝ) ⁻¹ *(b0 p ((al (mu Τ) (mu ζ))) ((al ((indicator A λ _↦(1:(ℝ)))) ((indicator A λ _↦(1:_))))))^(2*p)/ #A^(2*p)
   ≤ #(aX s)/ #Τ*(#(a3 s)/ #ζ):=by
   rw[div_mul_div_comm,ἇ (by positivity)]
   simpa[D9,Ai,Ἀ,TY,pow_mul',show(2:ℝ)^2=4 by norm_num,
    S5] using h
  refine ⟨(lt_of_mul_lt_mul_left (hs.trans_eq' ?_)<| hg s).le,this.trans<|
   Sq ?_<| UW ?_ ?_,this.trans<|
   RQ ?_<| UW ?_ ?_⟩
  ·simp_rw[aX,a3,g, ←l5,oB,oC, ←Nat.cast_smul_eq_nsmul ℝ,
    wInner_smul_left,ᾞ,star_trivial,à,aX,a3]
  any_goals positivity
  all_goals exact Nat.cast_le.2<| card_mono inter_subset_left
 rw[←sum_mul,Ca,ᾚ,Rm, ←sum_mul,ᾭ, ←Aj,
  Ῐ, ←à]
 simp only[ὅ,SS,mem_coe,mem_filter,mem_univ,TM, ←sum_filter,
  mul_lt_mul_iff_left₀ hf,Rh]
 by_cases h: ∀ s,g s≠0→M^2≤g s
 ·rw[←sum_filter_ne_zero (s:=filter _ _),Finset.filter_comm,
   filter_true_of_mem λ s hs↦h s (mem_filter.1 hs).2, ←sum_filter_ne_zero]
  refine lt_mul_of_one_lt_left (sum_pos (λ s hs↦(h _ (mem_filter.1 hs).2).trans_lt'<|
   by positivity) ?_) one_lt_two
  rw[←sum_filter_ne_zero] at Aj
  exact nonempty_of_sum_ne_zero<| Aj.trans_ne<| by positivity
 push Not at h
 obtain ⟨s,hs⟩:=h
 suffices h:(2:ℝ)* ∑ s with g s<M^2,g s< ∑ s,g s by
  refine(le_or_lt_of_add_le_add ?_).resolve_left h.not_ge
  simp_rw[←not_le, ←compl_filter, ←ΐ, ←Tc,sum_compl_add_sum]
  rfl
 rw[←lt_div_iff₀' (zero_lt_two' ℝ),Ri]
 calc
  ∑ s with g s<M^2,g s= ∑ s with g s<M^2∧g s≠0,Real.sqrt (g s)*Real.sqrt (g s)
    := by simp_rw[mul_self_sqrt (hg _), ←filter_filter,sum_filter_ne_zero]
  _< ∑ s with g s<M^2∧g s≠0,M*Real.sqrt (g s)
   := sum_lt_sum_of_nonempty ⟨s,mem_filter.2 ⟨mem_univ _,hs.symm⟩⟩ ?_
  _≤ ∑ s,M*Real.sqrt (g s):=sum_le_univ_sum_of_nonneg λ s↦by positivity
  _=M*(∑ s,Real.sqrt #(aX s)*Real.sqrt #(a3 s))
   := by simp_rw[mul_sum,g,sqrt_mul<| Q5 _]
  _≤M*(Real.sqrt (∑ s, #(aX s))*Real.sqrt (∑ s, #(a3 s))):=by
   gcongr; exact sum_sqrt_mul_sqrt_le _ λ i↦by positivity λ i↦by positivity
  _=_:= ?_
 ·simp only[mem_filter,mem_univ,TM,and_imp]
  exact λ s Oa hs↦Sk ((sqrt_lt' ἄ).2 Oa)<|
   sqrt_pos.2<| (hg _).lt_of_ne' hs
 rw[x1,x1,sqrt_mul',sqrt_mul',Q7 (Real.sqrt _),mul_self_sqrt,
  ←à,Ai,Tz, ←sqrt_mul,à,mul_self_sqrt,Aj,ᾭ,
  à]
 all_goals positivity
lemma Hq (Τ ζ:Finset G) (hε:0<ε) (Ak:ε≤1) (Cc:0<δ) (hp:Even p)
  (hp₂:2≤p) (FW:ε⁻¹ *log (2/δ)≤p) (É:(Τ∩ζ).Nonempty) (ξ:A.Nonempty)
  (hf: ∃ x,x∈Τ-ζ∧x∈A-A∧x∉s p ε Τ ζ A) :
  ∃ aX,aX⊆Τ∧ ∃ a3,a3⊆ζ∧1-δ≤ ∑ x∈s p ε Τ ζ A,((al (mu aX) (mu a3))) x ∧
    (4:ℝ)⁻¹ *(b0 p ((al (mu Τ) (mu ζ))) ((al ((indicator A λ _↦(1:(ℝ)))) ((indicator A λ _↦(1:_))))))^(2*p)/ #A^(2*p) ≤
      #aX/ #Τ ∧
     (4:ℝ)⁻¹ *(b0 p ((al (mu Τ) (mu ζ))) ((al ((indicator A λ _↦(1:(ℝ)))) ((indicator A λ _↦(1:_))))))^(2*p)/ #A^(2*p) ≤
      #a3/ #ζ:=by
 obtain ⟨aX,I7,a3,I8,h,r9,sa⟩:=
  N9 hp₂ (indicator ((s p ε Τ ζ A)ᶜ) λ _↦(1:_))
   (by simpa only[Set.j0,coe_compl,Set.mem_compl_iff,mem_coe]) É ξ
 refine ⟨aX,I7,a3,I8, ?_,r9,sa⟩
 have iu:0<p:=by positivity
 have aux (c:Finset G) (r)
  (h:(4:ℝ)⁻¹ *(b0 p ((al (mu Τ) (mu ζ))) ((al ((indicator A λ _↦(1:(ℝ)))) ((indicator A λ _↦(1:_))))))^(2*p)/ #A^(2*p)≤ #c/r) :
  c.Nonempty:=by
  simp_rw[nonempty_iff_ne_empty]
  rintro rfl
  simp[pow_mul',TA (zero_lt_four' ℝ),div_nonpos_iff,
   (ᾅ (jq iu.ne' É ξ) 2).not_ge,iu.ne',ξ.ne_empty] at h
 have ἔ:aX.Nonempty:=aux _ _ r9
 have Ἥ:a3.Nonempty:=aux _ _ sa
 clear r9 sa aux
 rw[sub_le_comm]
 calc
  _= ∑ x∈(s p ε Τ ζ A)ᶜ,((al (mu aX) (mu a3))) x:= ?_
  _=⟪(al ((@mu (ℝ) _ _) aX) (mu a3)),(↑) ∘ (indicator ((s (↑p) ε Τ ζ A)ᶜ) λ _↦(1:(ℝ≥0)))⟫_[ℝ]:=by
   simp[wInner_one_eq_sum, -mem_compl, -K4,ὅ]
   simp only[←ite_not (_∈s p ε Τ ζ A), ←mem_compl,TU]
   simp[-mem_compl]
  _≤_:=(ἇ<| jq iu.ne' É ξ).2 h
  _≤_:= ?_
 ·simp_rw[sub_eq_iff_eq_add',sum_add_sum_compl,jJ,xV]
  rw[ᾢ _ ἔ,ᾢ _ Ἥ,ἃ]
 rw[ἲ (jq iu.ne' É ξ), ←le_div_iff₀' (zero_lt_two' ℝ)]
 simp only[TU NNReal.toReal,ὅ,TN,NNReal.coe_zero,
  mul_boole,Fintype.sum_ite_mem,S5, ←coe_compl,mem_coe]
 calc
  ∑ x∈(s p ε Τ ζ A)ᶜ,((al (mu Τ) (mu ζ))) x*((al ((indicator A λ _↦(1:_))) ((indicator A λ _↦(1:_))))) x^p ≤
    ∑ x∈(s p ε Τ ζ A)ᶜ,
     ((al (mu Τ) (mu ζ))) x*((1-ε)*(b0 p ((al (mu Τ) (mu ζ))) ((al ((indicator A λ _↦(1:(ℝ)))) ((indicator A λ _↦(1:_)))))))^p:=by
   gcongr with x hx
   ·exact dM õ õ x
   ·exact dM Set.cY Set.cY _
   ·simpa using hx
  _≤ ∑ x,((al (mu Τ) (mu ζ))) x*((1-ε)*(b0 p ((al (mu Τ) (mu ζ))) ((al ((indicator A λ _↦(1:(ℝ)))) ((indicator A λ _↦(1:_)))))))^p:=by
   gcongr
   ·intros
    exact å (dM õ õ _)<| hp.pow_nonneg _
   ·exact subset_univ _
  _=(aJ 1 ((@mu (ℝ) _ _) Τ))*(aJ 1 ((@mu (ℝ) _ _) ζ))*((1-ε)^p*(b0 p ((al (mu Τ) (mu ζ))) ((al ((indicator A λ _↦(1:(ℝ)))) ((indicator A λ _↦(1:_))))))^p)
   := ?_
  _≤_:=
   RQ (å (hp.pow_nonneg _)<| hp.pow_nonneg _)<|
    mul_le_one₀ rn ᾧ rn
  _≤_:=ἂ ?_<| hp.pow_nonneg _
 ·have:0≤(al ((@mu (ℝ) _ _) Τ) (mu ζ)):=iN õ õ
  simp_rw[←xW õ õ,ek,
   RA (this _),sum_mul,Ἀ]
 calc
  (1-ε)^p≤exp (-ε)^p:=by gcongr; exact one_sub_le_exp_neg _
  _=exp (-(ε*p)):=by rw[←neg_mul,exp_mul,rpow_natCast]
  _≤exp (-log (2/δ)):=
   (exp_monotone<| TO<| (TA<| by positivity).1 FW)
  _=δ/2:=by rw[exp_neg,exp_log,inv_div]; positivity
end
end
section
section
open Finset hiding card
open Fintype (card)
open Function MeasureTheory RCLike Real
open scoped ComplexConjugate ComplexOrder NNReal ENNReal
variable {G:Type*} [Δ G] [Β G] [Γ G]
 {ν:G→ℝ≥0} {f:G→ℝ} {g h:G→ℂ} {ε:ℝ} {p:ℕ}
lemma wX {f:G→ℂ} (hf:(al g g)=f) (â:(al h h)=(↑) ∘ ν) (k:ℕ) :
  0≤⟪f^k,(↑) ∘ ν⟫_[ℂ]:=by
 calc
  0≤ ∑ z:Fin k→G,(‖∑ x,(∏ i,conj (g (x+z i)))*h x‖ :ℂ)^2:=by positivity
  _= ∑ x:G, ∑ yz:G × G with yz.1-yz.2=x,
     h yz.1*conj h yz.2*conj (((al g g)) (yz.1-yz.2))^k:= ?_
  _= ∑ x:G, ∑ yz:G × G with yz.1-yz.2=x,
     h yz.1*conj h yz.2*conj (((al g g)) x)^k:=by
    congr! with x _ yz Ob
    simpa using Ob
  _=_:=by
   rw[←hf, ←â,wInner_one_eq_sum]
   simp only[Pi.pow_apply,Sb,map_pow]
   simp_rw[ᾥ h,sum_mul]
 simp_rw[rm,sum_fiberwise, ←univ_product_univ,sum_product]
 simp only[sum_pow',sum_mul_sum,ᾪ,T0,SB,
  ←UX,ᾘ,map_prod]
 simp only[mul_sum, @sum_comm _ _ (Fin k→G),ä (conj _),prod_mul_distrib,TR]
 rw[sum_comm]
 congr with x
 congr with y
 congr with z
 group
lemma xm {f:G→ℝ} (hf:(al g g)=(↑) ∘ f) (â:(al h h)=(↑) ∘ ν) (k:ℕ) :
  (0:ℝ)≤⟪(↑) ∘ ν,f^k⟫_[ℝ]:=by
 simpa[←Complex.zero_le_real,wInner_one_eq_sum,ä] using wX hf â k
variable [MeasurableSpace G] [Α G]
end
end
section
section
open Finset hiding card
open Fintype (card)
open Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ENNReal NNReal NNRat
variable {ι κ 𝕜:Type*} [Δ ι]
namespace RCLike
variable [Ζ 𝕜] {I3:MeasurableSpace ι} [Α ι] {f:ι→𝕜}
@[simp] lemma wInner_cWeight_self (f:ι→𝕜) :
  ⟪f,f⟫ₙ_[𝕜]=(((ð 2 f):ℝ):𝕜)^2:=by
 simp_rw[←UI]
 simp[ry,wInner_cWeight_eq_expect]
end RCLike
namespace MeasureTheory
section mv
variable {α:Type*} {w3:MeasurableSpace α} [Α α] [Δ α] [Ζ 𝕜]
 {p q r:ℝ≥0∞} {f g:α→𝕜}
omit [Δ α]
variable [Finite α]
lemma yV (p q:ℝ≥0∞) (_hr₀:r≠0) [PS:ENNReal.HolderTriple p q r] :
  (ð r (f*g))≤(ð p f)*(ð q g):=by
 cases RR α
 set μ:=ProbabilityTheory.uniformOn (Set.univ:Set α) with Hr
 have Oc:IsFiniteMeasure μ:=by rw[Hr]; infer_instance
 have M4:MemLp (f*g) r μ:=MemLp.of_discrete
 have FX:MemLp f p μ:=MemLp.of_discrete
 have FY:MemLp g q μ:=MemLp.of_discrete
 have Od: ∀ᵐ x ∂μ, ‖f x*g x‖₊≤(1:ℝ≥0)* ‖f x‖₊* ‖g x‖₊:=
  .of_forall λ x↦by rw[ἃ]; exact nnnorm_mul_le _ _
 have key:eLpNorm (λ x↦f x*g x) r μ
   ≤ ((1:ℝ≥0):ℝ≥0∞)*eLpNorm f p μ*eLpNorm g q μ:=
  eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p:=p) (q:=q) (r:=r)
   FX.aestronglyMeasurable FY.aestronglyMeasurable (·*·) 1 Od
 change lpNorm _ _ μ≤lpNorm _ _ μ*lpNorm _ _ μ
 rw[←toReal_eLpNorm M4.aestronglyMeasurable,
   ←toReal_eLpNorm FX.aestronglyMeasurable,
   ←toReal_eLpNorm FY.aestronglyMeasurable,
   ←UK]
 apply ENNReal.toReal_mono
 ·exact ENNReal.mul_ne_top FX.eLpNorm_ne_top FY.eLpNorm_ne_top
 ·simpa[Pi.mul_def] using key
end mv
section mv
variable {α:Type*} {w3:MeasurableSpace α} [Α α] [Δ α] [Ζ 𝕜]
 {p q r:ℝ≥0∞} {f g:α→𝕜}
omit [Δ α] in
lemma tY [Finite α] (p q:ℝ≥0∞) [hpq:ENNReal.HolderConjugate p q] :
  (ð 1 (f*g))≤(ð p f)*(ð q g):=yV _ _ one_ne_zero
end mv
end MeasureTheory
end
end
section
section
open AddChar Finset Fintype Function MeasureTheory RCLike
open scoped BigOperators ComplexConjugate ComplexOrder ENNReal NNReal translate
variable {G:Type*} [Γ G] [Δ G] {f:G→ℂ} {ψ:Ε G ℂ} {n:ℕ}
noncomputable def π (f:G→ℂ):Ε G ℂ→ℂ:=λ ψ↦⟪ψ,f⟫_[ℂ]
lemma Ú (f:G→ℂ) (ψ:Ε G ℂ):π f ψ=⟪ψ,f⟫_[ℂ]:=rfl
lemma pD [MeasurableSpace G] [Α G] (f:G→ℂ)
  (ψ:Ε G ℂ): ‖π f ψ‖ ≤(aJ 1 f):=by
 grw[Ú,lq ∞ 1,dw]
 simp[Q0]
lemma qY [MeasurableSpace G] [Α G] (f:G→ℂ) :
  (ð (∞) (π f))≤(aJ 1 f):=by
 rw[oE]; exact ciSup_le λ ψ↦pD f ψ
@[simp] lemma vN (f g:G→ℂ):⟪π f,π g⟫ₙ_[ℂ]=⟪f,g⟫_[ℂ]:=by
 classical
 unfold π
 simp_rw[wInner_one_eq_sum,wInner_cWeight_eq_expect,inner_apply',ᾘ,ᾪ,
  T0,sum_mul,mul_sum,expect_sum_comm,Q7 _ (conj<| f _),
  ←expect_mul, ←Rz, ←map_neg_eq_inv, ←map_add_eq_mul,
  TH,add_neg_eq_zero,SS,UL]
@[simp] lemma w5 [MeasurableSpace G] [Α G] (f:G→ℂ) :
  (ð 2 (π f))=(aJ 2 f):=by
 refine(sq_eq_sq₀ lpNorm_nonneg lpNorm_nonneg).1<| Complex.ofReal_injective ?_
 push_cast
 simpa[ð,aJ,RCLike.wInner_cWeight_self,xX] using vN f f
lemma vn (f:G→ℂ) (a:G):𝔼 ψ,π f ψ*ψ a=f a:=by
 classical
 simp_rw[π,wInner_one_eq_sum,inner_apply',sum_mul,expect_sum_comm,ᾭ _ (f _),
  ←expect_mul, ←Rz,TK, ←map_sub_eq_div,
  TH,sub_eq_zero,SS,UL]
@[simp] lemma Al [Β G]:π (uK:G→ℂ)=1:=by
 ext; simp[yI,Ú,wInner_one_eq_sum]
variable [Β G]
lemma sb (f g:G→ℂ) (ψ:Ε G ℂ):π ((Χ f g)) ψ=π f ψ*π g ψ:=by
 simp_rw[π,wInner_one_eq_sum,inner_apply,ᾂ,mul_sum,sum_mul,
  ←sum_product',univ_product_univ]
 refine ἐ ((Equiv.prodComm _ _).trans<|
  ((Equiv.refl _).prodShear Equiv.subRight).trans<| Equiv.prodComm _ _)  _ _ λ (a,b)↦ ?_
 simp[Q7, ←ᾪ, ←map_add_eq_mul]
@[simp] lemma x2 (f g:G→ℂ):π ((Χ f g))=π f*π g:=funext<| sb _ _
@[simp] lemma vO (f:G→ℂ): ∀ n,π ((ἶ f n))=π f^n
 | 0=>Al
 | n+1=>by simp[vl,ᾬ,vO]
@[simp] lemma vP (f:G→ℂ) (n:ℕ) (ψ:Ε G ℂ) :
  π ((ἶ f n)) ψ=π f ψ^n:=SR (vO _ _) _
end
end
section
open scoped BigOperators
namespace ay
open Finset
abbrev ρ (G:Type*) [Γ G]:=G→+ AddCircle (1:ℝ)
structure aj (G:Type*) [Γ G] where
 í:Finset (ρ G)
 Υ:ρ G→ℝ≥0
namespace aj
variable {G H:Type*} [Γ G] [Γ H]
def Ι (B:aj G):ℕ:=B.í.card
def ai (B:aj G) (t:ℝ≥0):aj G where
 í:=B.í
 Υ γ:=t*B.Υ γ
@[simp] lemma KS (B:aj G) (t:ℝ≥0) :
  (B.ai t).í=B.í:=rfl
@[simp] lemma oF (B:aj G) (t:ℝ≥0) (γ:ρ G) :
  (B.ai t).Υ γ=t*B.Υ γ:=rfl
@[simp] lemma f6 (B:aj G) (t:ℝ≥0) :
  (B.ai t).Ι=B.Ι:=rfl
@[simp] lemma oG (B:aj G):B.ai 1=B:=by
 cases B
 simp[ai]
@[simp] lemma vo (B:aj G) (s t:ℝ≥0) :
  (B.ai s).ai t=B.ai (t*s):=by
 cases B
 simp[ai,à]
noncomputable def Η [Δ G] (B:aj G):Finset G:=by
 classical
 exact Finset.univ.filter λ x ↦
  ∀ γ∈B.í, ‖γ x‖ ≤(B.Υ γ:ℝ)
@[simp] lemma mem_carrier [Δ G] (B:aj G) (x:G) :
  x∈B.Η↔ ∀ γ∈B.í, ‖γ x‖ ≤(B.Υ γ:ℝ):=by
 classical
 simp[Η]
lemma se [Δ G] (B:aj G):0∈B.Η:=by
 rw[mem_carrier]
 intro γ oa
 simp
lemma aE [Δ G] (B:aj G):B.Η.Nonempty:=
 ⟨0,B.se⟩
lemma ec [Δ G] {B:aj G} {x:G} :
  -x∈B.Η↔x∈B.Η:=by
 simp only[mem_carrier]
 constructor<;>intro hx γ oa
 ·simpa only[map_neg,norm_neg] using hx γ oa
 ·simpa only[map_neg,norm_neg] using hx γ oa
lemma b5 [Δ G] {B:aj G} {s t:ℝ≥0} (Ἳ:s≤t) :
  (B.ai s).Η⊆(B.ai t).Η:=by
 intro x hx
 rw[mem_carrier] at hx ⊢
 intro γ oa
 have ú:(s:ℝ)*(B.Υ γ:ℝ) ≤
   (t:ℝ)*(B.Υ γ:ℝ):=by
  gcongr
 exact(hx γ oa).trans ú
lemma e8 [Δ G] {B:aj G} {s t:ℝ≥0} {x y:G}
  (hx:x∈(B.ai s).Η) (hy:y∈(B.ai t).Η) :
  x+y∈(B.ai (s+t)).Η:=by
 rw[mem_carrier] at hx hy ⊢
 intro γ oa
 rw[map_add]
 calc
  _ ≤ ‖γ x‖ + ‖γ y‖:=norm_add_le _ _
  _≤(s:ℝ)*(B.Υ γ:ℝ)+(t:ℝ)*(B.Υ γ:ℝ):=
   Sr (hx γ oa) (hy γ oa)
  _=((s+t:ℝ≥0):ℝ)*(B.Υ γ:ℝ):=by
   push_cast
   ring
lemma j2 [Δ G] {B:aj G} {s t:ℝ≥0} {x y:G}
  (hx:x∈(B.ai s).Η) (hy:y∈(B.ai t).Η) :
  x-y∈(B.ai (s+t)).Η:=by
 rw[Ἱ]
 exact e8 hx (ec.mpr hy)
noncomputable def map (B:aj G) (e:G ≃+ H):aj H:=by
  classical
  exact
    { í:=B.í.image λ γ↦γ.comp e.symm.toAddMonoidHom
      Υ:=λ δ↦B.Υ (δ.comp e.toAddMonoidHom) }
@[simp] lemma MG (B:aj G) (e:G ≃+ H) (δ:ρ H) :
    (B.map e).Υ δ=B.Υ (δ.comp e.toAddMonoidHom):=by
  classical
  simp[map]
@[simp] lemma vQ (B:aj G) (e:G ≃+ H) (δ:ρ H) :
  δ∈(B.map e).í ↔
   ∃ γ∈B.í,γ.comp e.symm.toAddMonoidHom=δ:=by
 classical
 simp[map]
private lemma vx (e:G ≃+ H) :
  Injective (λ γ:ρ G↦γ.comp e.symm.toAddMonoidHom):=by
 intro γ δ h
 ext x
 have hx:=S6 h (e x)
 simpa using hx
@[simp] lemma Am (B:aj G) (e:G ≃+ H) :
  (B.map e).Ι=B.Ι:=by
 classical
 rw[Ι,Ι,map]
 exact Finset.card_image_iff.mpr (vx e).injOn
private lemma sf (B:aj G) (e:G ≃+ H)
    (γ:ρ G) :
    (B.map e).Υ (γ.comp e.symm.toAddMonoidHom)=B.Υ γ:=by
  change B.Υ ((γ.comp e.symm.toAddMonoidHom).comp e.toAddMonoidHom)=B.Υ γ
  apply è B.Υ
  ext x
  simp
@[simp] lemma oH [Δ G] [Δ H]
  (B:aj G) (e:G ≃+ H) (x:G) :
  e x∈(B.map e).Η↔x∈B.Η:=by
 classical
 rw[mem_carrier,mem_carrier]
 constructor
 ·intro hx γ oa
  have CK :=
         vQ B e _ |>.mpr ⟨γ,oa,rfl⟩
  have hh:=hx (γ.comp e.symm.toAddMonoidHom) CK
  rw[sf] at hh
  have An:(γ.comp e.symm.toAddMonoidHom) (e x)=γ x:=by simp
  rwa[An] at hh
 ·intro hx δ Cc
  rcases (vQ B e δ).mp Cc with ⟨γ,oa,rfl⟩
  rw[sf]
  have An:(γ.comp e.symm.toAddMonoidHom) (e x)=γ x:=by simp
  rw[An]
  exact hx γ oa
@[simp] lemma kA [Δ G] [Δ H]
  (B:aj G) (e:G ≃+ H) :
  (B.map e).Η.card=B.Η.card:=by
 classical
 symm
 apply Finset.card_bijective e e.bijective
 intro x
 exact(oH B e x).symm
noncomputable def eK (N:ℕ) (î:Odd N):ZMod N ≃+ ZMod N:=by
  let f:ZMod N→+ ZMod N:=
    { toFun:=λ x↦x+x
      map_zero':=by simp
      map_add':=by
        intro x y
        abel }
  have K5:IsUnit (2:ZMod N):=
    (ZMod.isUnit_iff_coprime 2 N).2 (Nat.coprime_two_left.mpr î)
  have Hs :=
    IsUnit.isUnit_iff_mulLeft_bijective.mp K5
  have M5:Function.Bijective f:=by
    simpa only[f,AddMonoidHom.coe_mk,ZeroHom.coe_mk,ΐ] using Hs
  exact AddEquiv.ofBijective f M5
@[simp] lemma sV (N:ℕ) (î:Odd N) (x:ZMod N) :
    eK N î x=x+x:=by
  simp[eK]
@[simp] lemma tZ (N:ℕ) [NeZero N] (î:Odd N)
  (B:aj (ZMod N)) :
  (B.map (eK N î)).Η.card=B.Η.card:=
 kA B (eK N î)
end aj
end ay
end
section
open Finset
open scoped NNReal
namespace ay.br
noncomputable section
variable {G:Type*} [Γ G] [Δ G] [Β G]
structure aY (G:Type*) [Γ G] [Δ G]
  [Β G] where
 ba:aj G
 Ψ:ℝ≥0
 Ï:ℝ≥0
 é:0< Ï∧Ï≤Ψ ∧
  (ba.ai (Ψ+Ï)).Η.card ≤
   2*(ba.ai (Ψ-Ï)).Η.card
 set:Finset G
 nonempty:set.Nonempty
 mw:set⊆(ba.ai Ψ).Η
namespace aY
def e9 (s:aY G):Finset G:=
 (s.ba.ai s.Ψ).Η
def Ξ (s:aY G):ℝ:=
 (s.set.card:ℝ)/s.e9.card
def Ι (s:aY G):ℕ:=s.ba.Ι
def card (s:aY G):ℕ:=s.e9.card
lemma sg (s:aY G):s.e9.Nonempty:=
 (s.ba.ai s.Ψ).aE
lemma ὰ (s:aY G):0<s.Ξ:=
       ὗ (by exact_mod_cast s.nonempty.card_pos)
  (by exact_mod_cast s.sg.card_pos)
lemma Ö (s:aY G):s.Ξ≤1:=by
 rw[Ξ,ᾜ (by exact_mod_cast s.sg.card_pos)]
 exact_mod_cast ὣ s.mw
end aY
def dk (q:ℝ) (aq:ℕ) (Á:ℝ)
  (s t:aY G):Prop:=
 q*s.Ξ≤t.Ξ ∧
  t.Ι≤ s.Ι+aq ∧
  exp (-Á)*(s.card:ℝ)≤(t.card:ℝ)
inductive eu (q:ℝ) (aq:ℕ) (Á:ℝ) :
  ℕ→aY G→aY G→Prop
 | nil (s:aY G):eu q aq Á 0 s s
 | cons {n:ℕ} {s t u:aY G}
   (Ἳ:dk q aq Á s t)
   (ῠ:eu q aq Á n t u) :
   eu q aq Á (n+1) s u
namespace eu
lemma qZ {q:ℝ} {aq:ℕ} {Á:ℝ}
  (hq:0≤q) {n:ℕ} {s t:aY G}
  (h:eu q aq Á n s t) :
  q^n*s.Ξ≤t.Ξ:=by
 induction h with
 | nil s=>simp
 | @cons n s t u Ἳ ῠ ih =>
   have uP := ἥ hq n
   calc
    _ =q^n*(q*s.Ξ):=by
     rw[ᾬ]
     ring
    _≤q^n*t.Ξ:=
     Å Ἳ.1 uP
    _≤u.Ξ:=ih
lemma card_bound {q:ℝ} {aq:ℕ} {Á:ℝ}
  {n:ℕ} {s t:aY G}
  (h:eu q aq Á n s t) :
  exp (-(n:ℝ)*Á)*(s.card:ℝ)≤(t.card:ℝ):=by
 induction h with
 | nil s=>simp
 | @cons n s t u Ἳ ῠ ih =>
   have BD:0≤exp (-(n:ℝ)*Á):=
    (ᾰ _).le
   calc
    _ =
      exp (-(n:ℝ)*Á) *
       (exp (-Á)*(s.card:ℝ)):=by
     rw[show-((n+1:ℕ):ℝ)*Á =
       (-(n:ℝ)*Á)+(-Á) by
      push_cast
      ring,
      R7]
     ring
    _≤exp (-(n:ℝ)*Á)*(t.card:ℝ):=
     Å Ἳ.2.2 BD
    _≤(u.card:ℝ):=ih
end eu
def nK (L:ℕ) (Ξ:ℝ):Prop:=
 1/(2:ℝ)^L≤Ξ
end
end ay.br
end
section
open Finset Function
open scoped BigOperators NNReal
namespace ay
section Moments
variable {X:Type*} [Δ X] [Β X]
def iP (ν f:X→ℝ) (k:ℕ):ℝ:=
 ∑ x:X,ν x*f x^k
def È (ν f:X→ℝ) (k:ℕ):ℝ:=
 ∑ x:X,ν x* |f x| ^k
omit [Β X] in
lemma dx {ν f:X→ℝ} (â: ∀ x,0≤ν x) (k:ℕ) :
  0≤È ν f k:=
       sum_nonneg λ x _↦å (â x) (ἥ (ᾝ _) _)
noncomputable def ᾩ (ε:ℝ):ℕ:=
 Nat.ceil (60/ε^2)
noncomputable def ῌ (ε:ℝ) (p:ℕ):ℕ:=
 2*p*ᾩ ε
lemma ix {ε:ℝ} (hε:0<ε) :
  0<ᾩ ε:=by
 rw[ᾩ,Nat.ceil_pos]
 positivity
lemma sh (ε:ℝ) (p:ℕ) :
  Even (ῌ ε p):=by
 refine ⟨p*ᾩ ε, ?_⟩
 simp[ῌ,ΐ,US]
lemma sW {ε:ℝ} {p:ℕ} (hε:0<ε) (hp:p≠0) :
  0<ῌ ε p:=by
 simp[ῌ,ix hε,Nat.pos_of_ne_zero hp]
lemma q0 {ε:ℝ} (_hε:0<ε) :
  60/ε^2≤ᾩ ε:=by
 simpa[ᾩ] using Rr (60/ε^2)
private lemma oI {a b:ℝ} {n:ℕ}
  (ha:0≤a) (hb:0≤b) (hn:1≤n) :
  (a+b)^n≤2^(n-1)*(a^n+b^n):=by
 let a':ℝ≥0:=⟨a,ha⟩
 let b':ℝ≥0:=⟨b,hb⟩
 have h:=NNReal.rpow_add_le_mul_rpow_add_rpow a' b'
  (p:=(n:ℝ)) (by exact_mod_cast hn)
 exact_mod_cast h
omit [Β X] in
lemma mV
  {ν f:X→ℝ} {ε:ℝ} {p:ℕ}
  (â: ∀ x,0≤ν x) (ob: ∑ x:X,ν x=1)
  (Ao: ∀ k:ℕ,0≤ iP ν f k)
  (qu:0<ε) (Ak:ε≤1) (hp:5≤p) (CL:Odd p)
  (Ὤ:ε^p≤È ν f p) :
  ∃ p':ℕ,0<p'∧Even p'∧p'≤ῌ ε p ∧
   (1+ε/2)^p'≤È ν (f+1) p':=by
 classical
 have Ὶ:p≠0:=Uq (SI (by norm_num) hp)
 have FZ:Even (p-1):=Nat.Odd.sub_odd CL odd_one
 have Eb :
   ε^p≤2* ∑ i:X,ν i*((f^(p-1)) i*(f i)⁺):=by
  calc
   ε^p≤È ν f p:=Ὤ
   _= ∑ i:X,ν i*((f^(p-1)) i* |f i|):=by
    unfold È
    apply sum_congr rfl
    intro i _
    congr 1
    change |f i| ^p=f i^(p-1)* |f i|
    rw[←ἳ (FZ.pow_nonneg (f i)),abs_pow,
     R0 Ὶ]
   _≤ iP ν f p +
     ∑ i:X,ν i*((f^(p-1)) i* |f i|):=
    le_add_of_nonneg_left (Ao p)
   _= ∑ i:X,ν i*((f^(p-1)) i*(f i+ |f i|)):=by
    simp[iP,Tc,sum_add_distrib,R0 Ὶ]
   _= ∑ i:X,ν i*((f^(p-1)) i*(2•(f i)⁺)):=by
    simp[add_abs_eq_two_nsmul_posPart]
   _=2* ∑ i:X,ν i*((f^(p-1)) i*(f i)⁺):=by
    simp[mul_sum]
    ring_nf
 let P:Finset X:=Finset.univ.filter λ i↦0≤f i
 let T:Finset X:=Finset.univ.filter λ i↦3/4*ε≤f i
 have Oe:T⊆P:=by
  intro i hi
  simp only[P,T,mem_filter,mem_univ,TM] at hi ⊢
  exact Sj (by positivity) hi
 have ὼ :
   (2:ℝ)⁻¹ *ε^p≤ ∑ i∈P,ν i*(f^p) i:=by
  rw[TA (by norm_num:(0:ℝ)<2),sum_filter]
  simpa[P,Pi.posPart_apply,posPart_eq_ite,R0 Ὶ] using Eb
 have Ap :
   ∑ i∈P \ T,ν i*(f^p) i≤(4:ℝ)⁻¹ *ε^p:=by
  calc
   _≤ ∑ i∈P \ T,ν i*(3/4*ε)^p:=by
    apply sum_le_sum
    intro i hi
    have G5:=hi
    simp only[mem_sdiff,P,T,mem_filter,mem_univ,TM,not_le] at G5
    exact Å (ἤ G5.1 G5.2.le p) (â i)
   _=(3/4)^p*ε^p* ∑ i∈P \ T,ν i:=by
    rw[←sum_mul]
    simp[Ἀ]
    ring
   _≤(4:ℝ)⁻¹ *ε^p* ∑ i:X,ν i:=by
    have hpow:(3/4:ℝ)^p≤(4:ℝ)⁻¹:=by
     calc
      (3/4:ℝ)^p≤(3/4:ℝ)^5:=by
       exact SJ (by norm_num) (by norm_num) hp
      _≤(4:ℝ)⁻¹:=by norm_num
    calc
     (3/4)^p*ε^p* ∑ i∈P \ T,ν i ≤
       (4:ℝ)⁻¹ *ε^p* ∑ i∈P \ T,ν i:=
      ἂ
       (ἂ hpow (ἥ qu.le p))
       (sum_nonneg λ i _↦â i)
     _≤(4:ℝ)⁻¹ *ε^p* ∑ i:X,ν i:=
      Å
       (sum_le_univ_sum_of_nonneg λ i↦â i)
       (å (by norm_num) (ἥ qu.le p))
   _=(4:ℝ)⁻¹ *ε^p:=by rw[ob,Ἣ]
 have Aq :
   (4:ℝ)⁻¹ *ε^p≤ ∑ i∈T,ν i*(f^p) i:=by
  calc
   (4:ℝ)⁻¹ *ε^p =
     (2:ℝ)⁻¹ *ε^p-(4:ℝ)⁻¹ *ε^p:=by ring
   _≤(∑ i∈P,ν i*(f^p) i) -
     ∑ i∈P \ T,ν i*(f^p) i:=sub_le_sub ὼ Ap
   _= ∑ i∈T,ν i*(f^p) i:=by
    rw[sum_sdiff_eq_sub Oe]
    ring
 have G6:0≤ ∑ i∈T,ν i*(f^p) i:=
  (å (by norm_num) (ἥ qu.le p)).trans Aq
 have Of :
   (∑ i∈T,ν i*(f^p) i)^2 ≤
    (∑ i∈T,ν i)* ∑ i∈T,ν i*(f^(2*p)) i:=by
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul T
  ·intro i _
   exact â i
  ·intro i _
   exact å (â i) ((T2 p).pow_nonneg (f i))
  ·intro i _
   dsimp
   rw[show 2*p=p*2 by omega,Ἂ,Ἀ]
   ring_nf
   exact SF
 have I9 :
   ((4:ℝ)⁻¹ *ε^p)^2 ≤
    (∑ i∈T,ν i)*È ν f (2*p):=by
  calc
   _≤(∑ i∈T,ν i*(f^p) i)^2:=
    ἤ (å (by norm_num) (ἥ qu.le p)) Aq 2
   _≤(∑ i∈T,ν i)* ∑ i∈T,ν i*(f^(2*p)) i:= Of
   _≤(∑ i∈T,ν i)*È ν f (2*p):=by
    apply Å _ (sum_nonneg λ i _↦â i)
    unfold È
    have heq :
      (∑ i∈T,ν i*(f^(2*p)) i) =
       ∑ i∈T,ν i* |f i| ^(2*p):=by
     apply sum_congr rfl
     intro i _
     simp only[Pi.pow_apply]
     rw[(T2 p).pow_abs]
    rw[heq]
    apply sum_le_sum_of_subset_of_nonneg (subset_univ T)
    intro i _ _
    exact å (â i) (ἥ (ᾝ _) _)
 let q:ℕ:=2*p
 by_cases F0:(2:ℝ)^q≤È ν (f+1) q
 ·refine ⟨q,by dsimp[q]; omega,T2 p, ?_, ?_⟩
  ·dsimp[q,ῌ]
   exact Q4 _ (ix qu)
  ·exact(ἤ (by positivity) (by linarith) q).trans F0
 ·have ø:È ν (f+1) q<(2:ℝ)^q:=ᾙ F0
  have hq:1≤q:=by dsimp[q]; omega
  have Og:È ν f q≤(2:ℝ)^(2*q):=by
   calc
    È ν f q ≤
      (2:ℝ)^(q-1)*(È ν (f+1) q+1):=by
     unfold È
     calc
      (∑ x:X,ν x* |f x| ^q) ≤
        ∑ x:X,ν x *
         ((2:ℝ)^(q-1)*(|f x+1| ^q+1^q)):=by
       apply sum_le_sum
       intro i _
       apply Å _ (â i)
       calc
        |f i| ^q≤(|f i+1| +1)^q:=by
         apply ἤ (ᾝ _) _ q
         calc
          |f i| = |(f i+1)-1|:=by ring_nf
          _≤ |f i+1| + |(1:ℝ)|:=abs_sub _ _
          _= |f i+1| +1:=by norm_num
        _≤(2:ℝ)^(q-1)*(|f i+1| ^q+1^q):=
         oI (ᾝ _) (by norm_num) hq
      _=(2:ℝ)^(q-1) *
        (∑ x:X,ν x* |(f+1) x| ^q+1):=by
       simp only[RM,Rt,one_pow]
       calc
        (∑ x:X,ν x*(2^(q-1)*(|f x+1| ^q+1))) =
          2^(q-1)*(∑ x:X,ν x* |f x+1| ^q) +
           2^(q-1)* ∑ x:X,ν x:=by
         simp_rw[Tc]
         rw[sum_add_distrib]
         congr 1
         ·rw[mul_sum]
          apply sum_congr rfl
          intro i _
          ring
         ·rw[mul_sum]
          apply sum_congr rfl
          intro i _
          ring
        _=2^(q-1)*((∑ x:X,ν x* |f x+1| ^q)+1):=by
         rw[ob]
         ring
    _≤(2:ℝ)^(q-1)*((2:ℝ)^q+1):=by
     gcongr
    _≤(2:ℝ)^(q-1)*(2:ℝ)^(q+1):=by
     gcongr
     calc
      (2:ℝ)^q+1≤(2:ℝ)^q+(2:ℝ)^q:=by
       gcongr
       exact RH (by norm_num:(1:ℝ)≤2)
      _=(2:ℝ)^(q+1):=by rw[ᾬ]; ring
    _=(2:ℝ)^(2*q):=by rw[←ᾫ]; congr 1; omega
  have Ja:(ε/8)^(2*p)≤ ∑ i∈T,ν i:=by
   have M6:È ν f (2*p)≤(2:ℝ)^(4*p):=by
    convert Og using 1; simp[q]; omega
   have M7 :
     ((4:ℝ)⁻¹ *ε^p)^2 ≤
      (∑ i∈T,ν i)*(2:ℝ)^(4*p):=
    I9.trans (Å M6 (sum_nonneg λ i _↦â i))
   have si:(16:ℝ)*(2:ℝ)^(4*p)≤(8:ℝ)^(2*p):=by
    have Oh:(16:ℝ)≤4^p:=by
     calc
      (16:ℝ)=4^2:=by norm_num
      _≤4^p:=Se (by norm_num:(1:ℝ)≤4) (by omega)
    rw[show(2:ℝ)^(4*p)=16^p by rw[Ἂ]; norm_num,
     show(8:ℝ)^(2*p)=64^p by rw[Ἂ]; norm_num]
    calc
     (16:ℝ)*16^p≤4^p*16^p:=
      ἂ Oh (ἥ (by norm_num) p)
     _=64^p:=by rw[←Ἀ]; norm_num
   rw[TY]
   apply(ἲ (ᾅ (by norm_num:(0:ℝ)<8) (2*p))).2
   have pO:=Å M7 (by norm_num:(0:ℝ)≤16)
   calc
    ε^(2*p)=16*((4:ℝ)⁻¹ *ε^p)^2:=by
     rw[show 2*p=p+p by omega,ᾫ,TI]
     ring
    _≤16*((∑ i∈T,ν i)*(2:ℝ)^(4*p)):=pO
    _=(∑ i∈T,ν i)*(16*(2:ℝ)^(4*p)):=by ring
    _≤(∑ i∈T,ν i)*(8:ℝ)^(2*p):=
     Å si (sum_nonneg λ i _↦â i)
  let m:ℕ:=ᾩ ε
  have G7:0< m:=ix qu
  have Ht:60/ε^2≤(m:ℝ):=by
   simpa[m] using q0 qu
  have ἕ :
    1+ε/6≤(1+3*ε/4)/(1+ε/2):=by
   apply(ἇ (by positivity:0<1+ε/2)).2
   nlinarith
  have x4 :
    8/ε≤((1+3*ε/4)/(1+ε/2))^m:=by
   calc
    8/ε≤1+(m:ℝ)*(ε/6):=by
     have:=ἂ Ht (by positivity:0≤ε/6)
     field_simp at this ⊢
     nlinarith[SY qu]
    _≤(1+ε/6)^m:=UM (by linarith) m
    _≤((1+3*ε/4)/(1+ε/2))^m:=
     ἤ (by positivity) ἕ m
  have CM :
    (1+ε/2)^m≤(ε/8)*(1+3*ε/4)^m:=by
   have Hu:0<(1+ε/2)^m:=ᾅ (by positivity) m
   rw[TY] at x4
   have Jb:=(ἇ Hu).1 x4
   calc
    (1+ε/2)^m =
      (ε/8)*((8/ε)*(1+ε/2)^m):=by field_simp
    _≤(ε/8)*(1+3*ε/4)^m:=
     Å Jb (by positivity)
  have Ar :
    (1+ε/2)^(2*p*m) ≤
     (ε/8)^(2*p)*(1+3*ε/4)^(2*p*m):=by
   calc
    (1+ε/2)^(2*p*m)=((1+ε/2)^m)^(2*p):=by
     rw[←Ἂ,R8 m (2*p)]
    _≤((ε/8)*(1+3*ε/4)^m)^(2*p):=
     ἤ (by positivity) CM (2*p)
    _=(ε/8)^(2*p)*(1+3*ε/4)^(2*p*m):=by
     rw[Ἀ, ←Ἂ,R8 m (2*p)]
  have mx:Even (2*p*m):=by
   simp[SZ]
  refine ⟨2*p*m,by positivity,mx, ?_, ?_⟩
  ·simp[ῌ,m]
  ·calc
    (1+ε/2)^(2*p*m) ≤
      (ε/8)^(2*p)*(1+3*ε/4)^(2*p*m):=Ar
    _≤(∑ i∈T,ν i)*(1+3*ε/4)^(2*p*m):=
     ἂ Ja (ἥ (by positivity) _)
    _= ∑ i∈T,ν i*(1+3*ε/4)^(2*p*m):=by
     rw[←sum_mul]
    _≤ ∑ i∈T,ν i* |(f+1) i| ^(2*p*m):=by
     apply sum_le_sum
     intro i hi
     apply Å _ (â i)
     apply ἤ (by positivity) _ _
     have G5:3/4*ε≤f i:=by simpa[T] using hi
     have Jc:0≤(f+1) i:=by
      simp only[RM,Rt]
      nlinarith
     rw[ἳ Jc]
     simp only[RM,Rt]
     nlinarith
    _≤È ν (f+1) (2*p*m):=by
     unfold È
     apply sum_le_sum_of_subset_of_nonneg (subset_univ T)
     intro i _ _
     exact å (â i) (ἥ (ᾝ _) _)
end Moments
section vy
open Fintype MeasureTheory RCLike Real
open scoped ComplexConjugate ComplexOrder ENNReal
variable {G:Type*} [Δ G] [Β G] [Γ G]
 [MeasurableSpace G] [Α G]
omit [Α G] [MeasurableSpace G] in
lemma rC {ν:G→ℝ≥0} {f:G→ℝ} {g h:G→ℂ}
  (hf:(al g g)=(↑) ∘ f) (â:(al h h)=(↑) ∘ ν) (k:ℕ) :
  (0:ℝ)≤⟪(↑) ∘ ν,f^k⟫_[ℝ]:=
 xm hf â k
end vy
end ay
end
section
open Finset
open scoped BigOperators
namespace ay
namespace an
variable {X:Type*} [Δ X] [Β X]
structure cw (ν:X→ℝ):Prop where
 nonneg: ∀ x,0≤ν x
 sum_eq_one: ∑ x,ν x=1
noncomputable def aM (ν f:X→ℝ) (p:ℕ):ℝ:=
 if p=0 then 0 else
  (È ν f p)^(1/(p:ℝ))
omit [Β X] in
lemma dG (ν f:X→ℝ) {p:ℕ} (hp:0<p) :
  aM ν f p =
   (È ν f p)^(1/(p:ℝ)):=by
 simp[aM,hp.ne']
omit [Β X] in
lemma j3 {ν:X→ℝ} (â:cw ν)
  (f:X→ℝ) (p:ℕ) :
  0≤aM ν f p:=by
 classical
 unfold aM
 split
 ·exact SF
 ·exact Tn (dx â.nonneg p) _
omit [Β X] in
lemma jr {ν f:X→ℝ} (â:cw ν)
  {p:ℕ} (hp:0<p) :
  aM ν f p^p=È ν f p:=by
 classical
 rw[dG _ _ hp, ←RN,
  ←S0 (dx â.nonneg p)]
 have Ec:(p:ℝ)≠0:=by exact_mod_cast hp.ne'
 field_simp
 simp
private lemma xo {x:ℝ} {p q:ℕ} (hp:0<p) :
  (|x| ^p)^((q:ℝ)/(p:ℝ))= |x| ^q:=by
 rw[←RN]
 rw[←S0 (ᾝ x)]
 rw[←RN]
 congr 1
 have Ec:(p:ℝ)≠0:=by exact_mod_cast hp.ne'
 field_simp
omit [Β X] in
lemma gG
  {ν f:X→ℝ} (â:cw ν)
  {p q:ℕ} (hp:0<p) (hpq:p≤q) :
  aM ν f p≤aM ν f q:=by
 classical
 have hq:0<q:=hp.trans_le hpq
 have Ec:(0:ℝ)<p:=by exact_mod_cast hp
 have Jd:(0:ℝ)<q:=by exact_mod_cast hq
 have M8:(p:ℝ)≤q:=by exact_mod_cast hpq
 have ἕ:(1:ℝ)≤(q:ℝ)/(p:ℝ):=by
  exact(ἇ Ec).2 (by simpa using M8)
 have As:0≤È ν f p:=
  dx â.nonneg p
 have M9:0≤È ν f q:=
  dx â.nonneg q
 have Hv :
   (È ν f p)^((q:ℝ)/(p:ℝ)) ≤
    È ν f q:=by
  have h:=Real.rpow_arith_mean_le_arith_mean_rpow
   (Finset.univ:Finset X) ν (λ x↦ |f x| ^p)
   (λ x _↦â.nonneg x) (by simpa using â.sum_eq_one)
   (λ x _↦ἥ (ᾝ _) _) ἕ
  simpa only[È,mem_univ,xo hp] using h
 rw[dG _ _ hp,dG _ _ hq]
 have Ὢ :
   0≤(È ν f p)^((q:ℝ)/(p:ℝ)):=
  Tn As _
 have wJ:=Sf Ὢ Hv
  (RS Us Jd.le)
 calc
  (È ν f p)^(1/(p:ℝ)) =
    ((È ν f p)^((q:ℝ)/(p:ℝ))) ^
     (1/(q:ℝ)):=by
   rw[←S0 As]
   congr 1
   field_simp
  _≤(È ν f q)^(1/(q:ℝ)):=wJ
omit [Β X] in
lemma lv
  {μ ν f g:X→ℝ} (Je:cw μ) (â:cw ν)
  {p:ℕ} (hp:0<p)
  (yW:È μ f p≤2*È ν g p) :
  aM μ f p≤2*aM ν g p:=by
 classical
 have Ec:(0:ℝ)<p:=by exact_mod_cast hp
 have ha:0≤(1/(p:ℝ)):=by positivity
 have K6:(1/(p:ℝ))≤1:=by
  rw[ᾜ Ec]
  exact_mod_cast hp
 have Ed:0≤È μ f p:=
  dx Je.nonneg p
 have zj:0≤È ν g p:=
  dx â.nonneg p
 rw[dG _ _ hp,dG _ _ hp]
 calc
  (È μ f p)^(1/(p:ℝ)) ≤
    (2*È ν g p)^(1/(p:ℝ)):=
   Sf Ed yW ha
  _=(2:ℝ)^(1/(p:ℝ)) *
    (È ν g p)^(1/(p:ℝ)):=by
   rw[Real.mul_rpow (by norm_num:(0:ℝ)≤2) zj]
  _≤2*(È ν g p)^(1/(p:ℝ)):=by
   apply ἂ _ (Tn zj _)
   simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num:(1:ℝ)≤2) K6
def bS (p:ℕ):ℕ:=2*p
lemma sX (p:ℕ):Even (bS p):=
       ⟨p,by simp[bS,ΐ]⟩
lemma t3 {p:ℕ} (hp:0<p) :
  p≤bS p:=by
 simp only[bS]
 omega
def cF (p:ℕ):ℕ:=
 2*bS p+3
lemma pP (p:ℕ) :
  Odd (cF p):=by
 simp[cF,bS,Nat.odd_iff]
lemma fK {p:ℕ} (hp:0<p) :
  5≤cF p:=by
 simp only[cF,bS]
 omega
lemma je (p:ℕ) :
  bS p≤cF p:=by
 simp only[cF]
 omega
omit [Β X] in
lemma js
  {ν f:X→ℝ} (â:cw ν) {p:ℕ} (hp:0<p) :
  aM ν f (bS p) ≤
   aM ν f (cF p):=by
 classical
 apply gG â
 ·exact Ὑ (by norm_num) hp
 ·exact je p
noncomputable def cz (ε:ℝ) (p:ℕ):ℕ:=
 ῌ (ε/2) (cF p)
lemma t4 (ε:ℝ) (p:ℕ) :
  Even (cz ε p):=
       sh _ _
lemma uQ {ε:ℝ} {p:ℕ}
  (hε:0<ε) (hp:0<p) :
  0<cz ε p:=by
 apply sW (p:=cF p)
 ·positivity
 ·have Pw:=fK hp
  omega
lemma pF (ε:ℝ) (p:ℕ) :
  cz ε p =
   (8*p+6)*ᾩ (ε/2):=by
 unfold cz ῌ cF
  bS
 ring
lemma po {ε:ℝ} {p:ℕ} (hp:0<p) :
  cz ε p ≤
   14*ᾩ (ε/2)*p:=by
 rw[pF]
 have Cd:8*p+6≤14*p:=by omega
 have h:=QQ (ᾩ (ε/2)) Cd
 simpa[à,ä,Ῐ] using h
omit [Β X] in
lemma pQ
  {ν:X→ℝ} (â:cw ν)
  {f Ή:X→ℝ} {η bo:ℝ}
  (Jf:0<η) (Jg:η≤1) (Ἆ:0<bo)
  {p:ℕ} (hp:5≤p) (CL:Odd p)
  (Ao: ∀ k:ℕ,0≤ iP ν f k)
  (Ὤ:η^p≤È ν f p)
  (Ý: ∀ x,Ή x=bo*(1+f x)) :
  ∃ r:ℕ,0<r∧Even r∧r≤ῌ η p ∧
   (1+η/2)*bo≤aM ν Ή r:=by
 classical
 obtain ⟨r,hr,At,yX,tv⟩:=
  mV â.nonneg â.sum_eq_one Ao
   Jf Jg hp CL Ὤ
 refine ⟨r,hr,At,yX, ?_⟩
 have Au :
   È ν Ή r =
    bo^r*È ν (f+1) r:=by
  unfold È
  rw[á]
  apply sum_congr rfl
  intro x _
  rw[Ý x,SU,RT Ἆ,Ἀ]
  simp only[RM,Rt]
  ring_nf
 have Ar :
   ((1+η/2)*bo)^r ≤
    È ν Ή r:=by
  rw[Au,Ἀ]
  simpa[ä] using
   (ἂ tv (ἥ Ἆ.le r))
 rw[dG _ _ hr]
 have dc:0≤(1+η/2)*bo:=by positivity
 have wJ:=Sf (ἥ dc r) Ar
  (by positivity:0≤(r:ℝ)⁻¹)
 rw[Sc dc hr.ne'] at wJ
 simpa[ῆ] using wJ
omit [Β X] in
lemma nP
  {μ ν:X→ℝ} (Je:cw μ) (â:cw ν)
  {balanced Ἁ Ή:X→ℝ}
  {ε bo:ℝ} (hε:0<ε) (Ἆ:0<bo)
  {p:ℕ} (hp:0<p)
  (lh :
   aM μ balanced (bS p) ≤
    2*aM ν Ἁ (bS p))
  (CN :
   ε*bo/2<aM ν Ἁ (bS p) →
    ∃ r:ℕ,0<r∧r≤cz ε p ∧
     (1+ε/8)*bo≤aM ν Ή r)
  (qv :
   aM ν Ή (cz ε p) <
    (1+ε/8)*bo) :
  aM μ balanced p≤ε*bo:=by
 classical
 have Hw:0<ε*bo:=Ἃ hε Ἆ
 by_contra hbound
 have K7:ε*bo<aM μ balanced p:=ᾙ hbound
 have xp :
   aM μ balanced p ≤
    aM μ balanced (bS p):=
  gG Je hp (t3 hp)
 have CO :
   ε*bo/2<aM ν Ἁ (bS p):=by
  nlinarith[Hw,K7.trans_le xp,lh,
   j3 â Ἁ (bS p)]
 obtain ⟨r,hr,Jh,tv⟩:=CN CO
 have xq :
   aM ν Ή r ≤
    aM ν Ή (cz ε p):=
  gG â hr Jh
 exact(ῑ (tv.trans xq)) qv
end an
end ay
end
section
open Finset Function
namespace ay
section Av
variable {α:Type*} [AddCommMonoid α] [Β α]
def Ὧ (A:Finset α):ℕ:=
 #(((A ×ˢ A) ×ˢ A).filter λ x↦x.1.1+x.2=x.1.2+x.1.2)
variable [IsCancelAdd α]
lemma uR {A:Finset α} (ξ:ThreeAPFree (A:Set α)) :
  Ὧ A= #A:=by
 classical
 let D:Finset ((α × α) × α):=A.image λ a↦((a,a),a)
 have Ἠ :
   (((A ×ˢ A) ×ˢ A).filter λ x↦x.1.1+x.2=x.1.2+x.1.2)=D:=by
  ext x
  rcases x with ⟨⟨a,b⟩,c⟩
  simp only[mem_filter,mem_product,D,mem_image]
  constructor
  ·rintro ⟨⟨⟨ha,hb⟩,hc⟩,ᾊ⟩
   have hab:a=b:=ξ ha hb hc ᾊ
   have Oi:b=c:=ξ.eq_right ha hb hc ᾊ
   exact ⟨b,hb,by simp[hab,Oi]⟩
  ·rintro ⟨d,hd,CP⟩
   have PZ:d=a:=è (λ x↦x.1.1) CP
   have Oj:d=b:=è (λ x↦x.1.2) CP
   have P1:d=c:=è (λ x↦x.2) CP
   subst a
   subst b
   subst c
   simp[hd]
 change #(((A ×ˢ A) ×ˢ A).filter λ x↦x.1.1+x.2=x.1.2+x.1.2)= #A
 rw[Ἠ]
 change #(A.image λ a↦((a,a),a))= #A
 rw[card_image_of_injective]
 intro a b hab
 exact è (λ x↦x.1.1) hab
end Av
section x5
abbrev Â (N:ℕ):ℕ:=2*N+1
abbrev ὁ (N:ℕ) (a:ℕ):ZMod (Â N):=a
lemma gA (N:ℕ) :
  Set.InjOn (ὁ N) (Set.Iic N):=by
 intro a ha b hb hab
 change a≤N at ha
 change b≤N at hb
 have K8:a<Â N:=by
  change a<2*N+1
  omega
 have K9:b<Â N:=by
  change b<2*N+1
  omega
 have yY:=
  (TB a b (Â N)).mp hab
 rwa[Sl K8,Sl K9] at yY
lemma iV {N a b c d:ℕ}
  (ha:a≤N) (hb:b≤N) (hc:c≤N) (hd:d≤N) :
  ὁ N a+ὁ N c =
    ὁ N b+ὁ N d ↔
   a+c=b+d:=by
 constructor
 ·intro h
  have hcast:((a+c:ℕ):ZMod (Â N)) =
    ((b+d:ℕ):ZMod (Â N)):=by
   simpa only[T3] using h
  have Ji:a+c<Â N:=by
   change a+c<2*N+1
   omega
  have Jj:b+d<Â N:=by
   change b+d<2*N+1
   omega
  have yY:=
   (TB (a+c) (b+d) (Â N)).mp hcast
  rwa[Sl Ji,Sl Jj] at yY
 ·intro h
  simpa only[T3] using
   è (λ n:ℕ↦(n:ZMod (Â N))) h
def ὂ (N:ℕ) (A:Finset ℕ):Finset (ZMod (Â N)):=
 A.image (ὁ N)
@[simp] lemma fi {N:ℕ} {A:Finset ℕ} {x:ZMod (Â N)} :
  x∈ὂ N A↔ ∃ a∈A,ὁ N a=x:=by
 simp[ὂ]
lemma vR {N:ℕ} {A:Finset ℕ}
  (ξ: ∀ a∈A,a≤N): #(ὂ N A)= #A:=by
 rw[ὂ,card_image_iff]
 exact λ a ha b hb h↦gA N (ξ a ha) (ξ b hb) h
lemma q1 {N:ℕ} {A:Finset ℕ}
  (ξ: ∀ a∈A,a≤N) :
  Ὧ (ὂ N A)=Ὧ A:=by
 classical
 let f:((ℕ × ℕ) × ℕ)→((ZMod (Â N) × ZMod (Â N)) ×
   ZMod (Â N)):=λ x ↦
  ((ὁ N x.1.1,ὁ N x.1.2),ὁ N x.2)
 let T:Finset ((ℕ × ℕ) × ℕ):=
  ((A ×ˢ A) ×ˢ A).filter λ x↦x.1.1+x.2=x.1.2+x.1.2
 let U:Finset ((ZMod (Â N) × ZMod (Â N)) ×
   ZMod (Â N)):=
  (((ὂ N A ×ˢ ὂ N A) ×ˢ ὂ N A).filter λ x ↦
   x.1.1+x.2=x.1.2+x.1.2)
 have Ol:U=T.image f:=by
  ext x
  rcases x with ⟨⟨x,y⟩,z⟩
  constructor
  ·intro F1
   have La :
     x∈ὂ N A∧y∈ὂ N A∧z∈ὂ N A ∧
      x+z=y+y:=by
    simpa[U,Tm] using F1
   rcases La with ⟨hx,hy,hz,ΰ⟩
   obtain ⟨a,ha,rfl⟩:=fi.mp hx
   obtain ⟨b,hb,rfl⟩:=fi.mp hy
   obtain ⟨c,hc,rfl⟩:=fi.mp hz
   refine mem_image.mpr ⟨((a,b),c), ?_,rfl⟩
   have ᾊ:a+c=b+b:=
    (iV (ξ a ha) (ξ b hb) (ξ c hc) (ξ b hb)).1 ΰ
   simp[T,ha,hb,hc,ᾊ]
  ·intro F1
   obtain ⟨⟨⟨a,b⟩,c⟩,xr,Hx⟩:=mem_image.mp F1
   have CQ:a∈A∧b∈A∧c∈A∧a+c=b+b:=by
    simpa[T,Tm] using xr
   rcases CQ with ⟨ha,hb,hc,ᾊ⟩
   have hx:ὁ N a∈ὂ N A:=
    fi.mpr ⟨a,ha,rfl⟩
   have hy:ὁ N b∈ὂ N A:=
    fi.mpr ⟨b,hb,rfl⟩
   have hz:ὁ N c∈ὂ N A:=
    fi.mpr ⟨c,hc,rfl⟩
   have ΰ:ὁ N a+ὁ N c =
     ὁ N b+ὁ N b:=
    (iV (ξ a ha) (ξ b hb) (ξ c hc) (ξ b hb)).2 ᾊ
   rw[←Hx]
   simp[U,f,hx,hy,hz,ΰ]
 have hf:Set.InjOn f T:=by
  rintro ⟨⟨a,b⟩,c⟩ ᾊ ⟨⟨a',b'⟩,c'⟩ CQ heq
  have xr:a∈A∧b∈A∧c∈A∧a+c=b+b:=by
   simpa[T,Tm] using ᾊ
  have Ee:a'∈A∧b'∈A∧c'∈A∧a'+c'=b'+b':=by
   simpa[T,Tm] using CQ
  rcases xr with ⟨ha,hb,hc, -⟩
  rcases Ee with ⟨ἠ,Om,hc', -⟩
  have On:a=a':=gA N (ξ a ha) (ξ a' ἠ)<|
   è (λ x↦x.1.1) heq
  have Oo:b=b':=gA N (ξ b hb) (ξ b' Om)<|
   è (λ x↦x.1.2) heq
  have Oq:c=c':=gA N (ξ c hc) (ξ c' hc')<|
   è (λ x↦x.2) heq
  simp[On,Oo,Oq]
 change #U= #T
 rw[Ol,card_image_of_injOn hf]
end x5
end ay
end
section
open Finset Function
open scoped BigOperators translate
namespace ay
noncomputable section
section BE
variable {G:Type*} [Γ G] [Δ G] [Β G]
def af (A:Finset G) (x:G):ℝ:=
 if x∈A then (#A:ℝ)⁻¹ else 0
def ao (f g:G→ℝ) (x:G):ℝ:=
 ∑ y:G,f y*g (x-y)
def ἆ (f g:G→ℝ) (x:G):ℝ:=
 ∑ y:G,f y*g (y-x)
def qj (f g:G→ℝ):ℝ:=
 ∑ x:G,f x*g x
omit [Γ G] [Δ G] in
@[simp] lemma dj {A:Finset G} {x:G} (hx:x∈A) :
  af A x=(#A:ℝ)⁻¹:=by
 simp[af,hx]
omit [Γ G] [Δ G] in
@[simp] lemma dO {A:Finset G} {x:G} (hx:x∉A) :
  af A x=0:=by
 simp[af,hx]
omit [Γ G] [Δ G] in
lemma ὡ (A:Finset G) (x:G) :
  0≤af A x:=by
 unfold af
 split_ifs
 ·exact inv_nonneg.mpr (Q5 _)
 ·exact SF
omit [Γ G] [Δ G] in
lemma qw {A:Finset G} (ξ:A.Nonempty) (x:G) :
  0<af A x↔x∈A:=by
 unfold af
 split_ifs with hx
 ·simp only[hx,iff_true]
  exact inv_pos.mpr (Nat.cast_pos.mpr ξ.card_pos)
 ·simp[hx]
omit [Γ G] [Δ G] in
lemma d6 {A:Finset G} (ξ:A.Nonempty) (x:G) :
  af A x≠0↔x∈A:=by
 unfold af
 split_ifs with hx
 ·simp[hx,ξ.card_ne_zero]
 ·simp[hx]
omit [Γ G] in
lemma ᾁ {A:Finset G} (ξ:A.Nonempty) :
  ∑ x:G,af A x=1:=by
 change(∑ x∈(univ:Finset G),if x∈A then (#A:ℝ)⁻¹ else 0)=1
 rw[←ᾛ]
 have Ἠ:univ.filter (λ x:G↦x∈A)=A:=by ext; simp
 rw[Ἠ]
 simp[ξ.card_ne_zero]
omit [Β G] in
lemma fa {f g:G→ℝ}
  (hf: ∀ x,0≤f x) (hg: ∀ x,0≤g x) (z:G) :
  0≤ao f g z:=
       sum_nonneg λ x _↦å (hf x) (hg (z-x))
omit [Β G] in
lemma gB {f g:G→ℝ}
  (hf: ∀ x,0≤f x) (hg: ∀ x,0≤g x) (z:G) :
  0≤ἆ f g z:=
       sum_nonneg λ x _↦å (hf x) (hg (x-z))
lemma kC (A B:Finset G) (x:G) :
  ao (af A) (af B) x =
   (#(A.filter λ y↦x-y∈B):ℝ)*(#A:ℝ)⁻¹ *(#B:ℝ)⁻¹:=by
 have Ἠ:(univ.filter λ y:G↦x-y∈B)∩A =
   A.filter λ y↦x-y∈B:=by
  ext y
  simp[and_comm]
 simp[ao,af, ←ᾛ,
  à,Ῐ,Ἠ]
omit [Δ G] in
lemma lT (A B:Finset G) (x:G) :
  #(A.filter λ y↦x-y∈B)=A.addConvolution B x:=by
 unfold Finset.addConvolution
 refine Finset.card_nbij' (λ y↦(y,x-y)) (λ ab↦ab.1) ?_ ?_ ?_ ?_
 ·intro y hy
  change y∈A.filter (λ y↦x-y∈B) at hy
  change(y,x-y)∈(A ×ˢ B).filter (λ ab↦ab.1+ab.2=x)
  rw[mem_filter] at hy ⊢
  exact ⟨mem_product.mpr hy,by simp⟩
 ·rintro ⟨a,b⟩ hab
  change(a,b)∈(A ×ˢ B).filter (λ ab↦ab.1+ab.2=x) at hab
  change a∈A.filter (λ y↦x-y∈B)
  simp only[mem_filter,mem_product] at hab ⊢
  rcases hab with ⟨⟨ha,hb⟩,hsum⟩
  refine ⟨ha, ?_⟩
  have Ef:x-a=b:=by
   rw[←hsum]
   simp
  simpa[Ef] using hb
 ·intro y _
  rfl
 ·rintro ⟨a,b⟩ hab
  change(a,b)∈(A ×ˢ B).filter (λ ab↦ab.1+ab.2=x) at hab
  simp only[mem_filter,mem_product] at hab
  rcases hab with ⟨-,hsum⟩
  have Ef:x-a=b:=by
   rw[←hsum]
   simp
  simp[Ef]
lemma iy (A B:Finset G) (x:G) :
  ao (af A) (af B) x =
   (A.addConvolution B x:ℝ)*(#A:ℝ)⁻¹ *(#B:ℝ)⁻¹:=by
 rw[kC,lT]
end BE
section Algebra
variable {G:Type*} [Γ G] [Δ G] [Β G]
omit [Β G] in
lemma fG (f g:G→ℝ) :
  ao f g=ao g f:=by
 funext x
 rw[ao,ao]
 refine ἐ (Equiv.subLeft x) _ _ λ y↦ ?_
 simp[ä]
omit [Β G] in
lemma iz (f g:G→ℝ) :
  ∑ x:G,ao f g x=(∑ x:G,f x)* ∑ x:G,g x:=by
 simp_rw[ao,Ἕ]
 rw[ὶ]
 apply Ò rfl
 intro y _
 rw[←á]
 congr 1
 exact ἐ (Equiv.subRight y) _ _ λ x↦by simp
omit [Β G] in
lemma ho (f g:G→ℝ) :
  ∑ x:G,ἆ f g x =
   (∑ x:G,f x)* ∑ x:G,g x:=by
 simp_rw[ἆ,Ἕ]
 rw[ὶ]
 apply Ò rfl
 intro y _
 rw[←á]
 congr 1
 exact ἐ (Equiv.subLeft y) _ _ λ x↦by simp
end Algebra
section CR
variable {G:Type*} [Γ G] [Δ G] [Β G]
def ᾦ (A C:Finset G):ℕ:=
 #(((A ×ˢ A) ×ˢ C).filter λ x↦x.1.1+x.1.2=x.2+x.2)
omit [Δ G] in
lemma kZ (A C:Finset G) :
  ᾦ A C= ∑ c∈C,A.addConvolution A (c+c):=by
 unfold ᾦ Finset.addConvolution
 simp only[Finset.card_eq_sum_ones,ᾛ,Finset.sum_product]
 calc
  _ =
    ∑ a∈A, ∑ c∈C, ∑ b∈A,if a+b=c+c then 1 else 0:=by
   apply Ò rfl
   intro a _
   rw[ὶ]
  _= ∑ c∈C, ∑ a∈A, ∑ b∈A,if a+b=c+c then 1 else 0:=by
   rw[ὶ]
lemma jK {A C:Finset G}
  (Ἦ:Injective (λ x:G↦x+x)) :
  qj (ao (af A) (af A))
    (af (C.image λ x↦x+x)) =
   (ᾦ A C:ℝ)*(#A:ℝ)⁻¹ ^2*(#C:ℝ)⁻¹:=by
 let D := C.image λ x↦x+x
 have Jk: #D= #C:=by
  dsimp[D]
  exact card_image_of_injective _ Ἦ
 have vS (F:G→ℝ) :
   (∑ z:G,F z*af D z) =
    ∑ z∈D,F z*(#D:ℝ)⁻¹:=by
  change(∑ z:G,F z*(if z∈D then (#D:ℝ)⁻¹ else 0))=_
  simp only[Td,mul_zero]
  rw[←ᾛ]
  have Ἠ:univ.filter (λ z:G↦z∈D)=D:=by ext; simp
  rw[Ἠ]
 have yZ: ∑ z∈D,A.addConvolution A z=ᾦ A C:=by
  rw[kZ]
  dsimp[D]
  rw[Finset.sum_image]
  intro a _ b _ hab
  exact Ἦ hab
 have F2: ∑ z∈D,(A.addConvolution A z:ℝ)=(ᾦ A C:ℝ):=by
  exact_mod_cast yZ
 rw[qj,vS]
 simp_rw[iy]
 rw[Jk]
 have Ὄ (z:G) :
   ((A.addConvolution A z:ℝ)*(#A:ℝ)⁻¹ *(#A:ℝ)⁻¹)*(#C:ℝ)⁻¹ =
    (A.addConvolution A z:ℝ) *
     ((#A:ℝ)⁻¹ *(#A:ℝ)⁻¹ *(#C:ℝ)⁻¹):=by ac_rfl
 simp_rw[Ὄ]
 rw[←Ἕ,F2]
 simp only[TI]
 ac_rfl
omit [Δ G] in
lemma iA {A A' C:Finset G} (t:G)
  (ξ: ∀ x∈A',x-t∈A) (Ã: ∀ x∈C,x-t∈A) :
  ᾦ A' C≤Ὧ A:=by
 unfold ᾦ Ὧ
 let f:((G × G) × G)→((G × G) × G):=λ x ↦
  ((x.1.1-t,x.2-t),x.1.2-t)
 apply Finset.card_le_card_of_injOn f
 ·rintro ⟨⟨a,c⟩,b⟩ ᾊ
  change((a,c),b)∈(((A' ×ˢ A') ×ˢ C).filter λ x ↦
   x.1.1+x.1.2=x.2+x.2) at ᾊ
  change((a-t,b-t),c-t)∈(((A ×ˢ A) ×ˢ A).filter λ x ↦
   x.1.1+x.2=x.1.2+x.1.2)
  simp only[mem_filter,mem_product] at ᾊ ⊢
  rcases ᾊ with ⟨⟨⟨ha,hc⟩,hb⟩,ΰ⟩
  refine ⟨⟨⟨ξ a ha,Ã b hb⟩,ξ c hc⟩, ?_⟩
  calc
   _ =(a+c)-(t+t):=by
    simp only[Ἱ,neg_add_rev]
    ac_rfl
   _=(b+b)-(t+t):=è (λ x↦x-(t+t)) ΰ
   _=(b-t)+(b-t):=by
    simp only[Ἱ,neg_add_rev]
    ac_rfl
 ·rintro ⟨⟨a,c⟩,b⟩ _ ⟨⟨a',c'⟩,b'⟩ _ heq
  have Lb := è (λ x↦x.1.1) heq
  have Lc := è (λ x↦x.1.2) heq
  have Ld := è (λ x↦x.2) heq
  have ha:a=a':=calc
   a=(a-t)+t:=(Rs a t).symm
   _=(a'-t)+t:=è (λ x↦x+t) Lb
   _=a':=Rs a' t
  have hb:b=b':=calc
   b=(b-t)+t:=(Rs b t).symm
   _=(b'-t)+t:=è (λ x↦x+t) Lc
   _=b':=Rs b' t
  have hc:c=c':=calc
   c=(c-t)+t:=(Rs c t).symm
   _=(c'-t)+t:=è (λ x↦x+t) Ld
   _=c':=Rs c' t
  simp[ha,hb,hc]
end CR
end
end ay
end
section
open Finset
open scoped BigOperators NNReal symmDiff
namespace ay
namespace aj
variable {G:Type*} [Γ G] [Δ G] [Β G]
def vT (B:aj G) (Φ Ο:ℝ≥0):Prop:=
 0<Ο ∧
  ∀ Ρ:ℝ≥0,Ρ≤Ο →
   (B.ai (Φ-Ρ)).Η=(B.ai Φ).Η ∧
   (B.ai (Φ+Ρ)).Η=(B.ai Φ).Η
def pG (B:aj G) (Φ Ο:ℝ≥0):Prop:=
 0<Ο∧Ο≤Φ ∧
  (B.ai (Φ+Ο)).Η.card ≤
   2*(B.ai (Φ-Ο)).Η.card
def a1 (B:aj G):Prop:=
 let d:ℕ:=max B.Ι 1
 ∀ Ρ:ℝ≥0,
  Ρ≤1/(100*(d:ℝ≥0)) →
   (1-100*(d:ℝ)*(Ρ:ℝ))*(B.Η.card:ℝ) ≤
     ((B.ai (1-Ρ)).Η.card:ℝ) ∧
   ((B.ai (1+Ρ)).Η.card:ℝ) ≤
     (1+100*(d:ℝ)*(Ρ:ℝ))*(B.Η.card:ℝ)
omit [Β G] in
lemma sj (B:aj G) (Φ:ℝ≥0) :
  (B.ai Φ).a1 ↔
   let d := max B.Ι 1
   ∀ Ρ:ℝ≥0,
    Ρ≤1/(100*(d:ℝ≥0)) →
     (1-100*(d:ℝ)*(Ρ:ℝ)) *
        ((B.ai Φ).Η.card:ℝ) ≤
       ((B.ai ((1-Ρ)*Φ)).Η.card:ℝ) ∧
     ((B.ai ((1+Ρ)*Φ)).Η.card:ℝ) ≤
       (1+100*(d:ℝ)*(Ρ:ℝ)) *
        ((B.ai Φ).Η.card:ℝ):=by
 simp[a1,ä]
noncomputable def fp (A:Finset G) (t:G):Finset G:=
 A.map (Equiv.addRight t).toEmbedding
omit [Β G] [Δ G] in
@[simp] lemma lx {A:Finset G} {t x:G} :
  x∈fp A t↔x-t∈A:=by
 simp[fp,Ἱ]
lemma k0
  {B:aj G} {Φ Ο:ℝ≥0} (ò:Ο≤Φ) {t:G}
  (ht:t∈(B.ai Ο).Η) :
  (fp (B.ai Φ).Η t) ∆ (B.ai Φ).Η ⊆
   (B.ai (Φ+Ο)).Η \ (B.ai (Φ-Ο)).Η:=by
 intro x hx
 rw[UF] at hx
 rw[Finset.mem_sdiff]
 constructor
 ·rcases hx with hx | hx
  ·rw[lx] at hx
   have Aw:=e8 hx.1 ht
   simpa using Aw
  ·exact b5 (Ss (by positivity)) hx.1
 ·intro ῳ
  have zN :=
         b5 (T4) ῳ
  have Jl:x-t∈(B.ai Φ).Η:=by
   have ê := ec.mpr ht
   have xt:=e8 ῳ ê
   simpa[Ἱ,tsub_add_cancel_of_le ò] using xt
  have xu:x∈fp (B.ai Φ).Η t:=by
   rwa[lx]
  rcases hx with hx | hx
  ·exact hx.2 zN
  ·exact hx.2 xu
lemma kD
  {B:aj G} {Φ Ο:ℝ≥0} (ò:Ο≤Φ) {t:G}
  (ht:t∈(B.ai Ο).Η) :
  ((fp (B.ai Φ).Η t) ∆
    (B.ai Φ).Η).card ≤
   (B.ai (Φ+Ο)).Η.card -
    (B.ai (Φ-Ο)).Η.card:=by
 have sm :
   (B.ai (Φ-Ο)).Η ⊆
    (B.ai (Φ+Ο)).Η:=
  b5 ((T4).trans (Ss (by positivity)))
 calc
  ((fp (B.ai Φ).Η t) ∆
    (B.ai Φ).Η).card ≤
    ((B.ai (Φ+Ο)).Η \
     (B.ai (Φ-Ο)).Η).card:=
   ὣ (k0 ò ht)
  _=(B.ai (Φ+Ο)).Η.card -
    (B.ai (Φ-Ο)).Η.card:=
   Finset.card_sdiff_of_subset sm
lemma gY
  (A:Finset G) (t:G) :
  ∑ x:G, |af A (x-t)-af A x| =
   (((fp A t) ∆ A).card:ℝ)/(A.card:ℝ):=by
 have Ὄ (x:G) :
   |af A (x-t)-af A x| =
    if x∈(fp A t) ∆ A then (A.card:ℝ)⁻¹ else 0:=by
  by_cases Aw:x-t∈A<;>by_cases hx:x∈A <;>
   simp[af,UF,lx,
    Aw,hx,ἳ]
 simp_rw[Ὄ]
 rw[←ᾛ]
 simp[ἱ]
lemma jf
  {B:aj G} {Φ Ο:ℝ≥0} (ò:Ο≤Φ) {t:G}
  (ht:t∈(B.ai Ο).Η) :
  ∑ x:G,
    |af (B.ai Φ).Η (x-t) -
     af (B.ai Φ).Η x| ≤
   (((B.ai (Φ+Ο)).Η.card -
    (B.ai (Φ-Ο)).Η.card:ℕ):ℝ) /
     ((B.ai Φ).Η.card:ℝ):=by
 rw[gY]
 rw[ἱ,ἱ]
 gcongr
 exact_mod_cast kD ò ht
lemma cN
  {B:aj G} (Ô:B.a1) {Ρ:ℝ≥0}
  (dy:Ρ≤1/(100*(max B.Ι 1:ℕ):ℝ≥0))
  {t:G} (ht:t∈(B.ai Ρ).Η) :
  ∑ x:G,
    |af B.Η (x-t) -
     af B.Η x| ≤
   200*((max B.Ι 1:ℕ):ℝ)*(Ρ:ℝ):=by
 let d:ℕ:=max B.Ι 1
 have hd:0<d:=by simp[d]
 have Ce:Ρ≤1/(100*(d:ℝ≥0)):=by
  simpa[d] using dy
 have oK:Ρ≤1:=by
  apply Ce.trans
  rw[ᾜ]
  ·exact_mod_cast(show 1≤100*d by omega)
  ·positivity
 have Eg:=
  jf
   (B:=B) (Φ:=(1:ℝ≥0)) (Ο:=Ρ) oK ht
 simp only[oG] at Eg
 simp only[a1] at Ô
 have jt:=Ô Ρ (by simpa[d] using Ce)
 have sm :
   (B.ai (1-Ρ)).Η.card ≤
    (B.ai (1+Ρ)).Η.card:=
  ὣ
   (b5
    (tsub_le_self.trans (Ss (show 0≤Ρ by exact bot_le))))
 have BF:(0:ℝ)<B.Η.card:=by
  exact_mod_cast B.aE.card_pos
 apply Eg.trans
 rw[Nat.cast_sub sm]
 rw[ἲ BF]
 nlinarith[jt.1,jt.2]
end aj
end ay
end
section
open Finset
open scoped BigOperators NNReal
namespace ay
noncomputable section
variable {G:Type*} [Γ G] [Δ G] [Β G]
lemma g7
  {B:aj G} (Ô:B.a1) {κ:ℝ≥0}
  (qx:κ≤1/(100*(max B.Ι 1:ℕ):ℝ≥0))
  (ν:G→ℝ) (ks: ∀ t,0≤ν t)
  (pR: ∀ t,ν t≠0→t∈(B.ai κ).Η) :
  ∑ x:G,
    |ao (af B.Η) ν x -
     (∑ t:G,ν t)*af B.Η x| ≤
   200*((max B.Ι 1:ℕ):ℝ)*(κ:ℝ)* ∑ t:G,ν t:=by
 let E:ℝ:=200*((max B.Ι 1:ℕ):ℝ)*(κ:ℝ)
 have Ὄ (x:G) :
   |ao (af B.Η) ν x -
     (∑ t:G,ν t)*af B.Η x| ≤
    ∑ t:G,ν t *
     |af B.Η (x-t)-af B.Η x|:=by
  rw[fG]
  simp only[ao]
  rw[Ἕ, ←QJ]
  simp_rw[←UY]
  calc
   _
                                          ≤
     ∑ t:G, |ν t *
      (af B.Η (x-t)-af B.Η x)|:=
    abs_sum_le_sum_abs _ _
   _= ∑ t:G,ν t *
     |af B.Η (x-t)-af B.Η x|:=by
    apply Ò rfl
    intro t _
    rw[SU,ἳ (ks t)]
 calc
  _
                                 ≤
    ∑ x:G, ∑ t:G,ν t *
     |af B.Η (x-t)-af B.Η x|:=by
   exact ᾯ λ x _↦Ὄ x
  _= ∑ t:G,ν t* ∑ x:G,
     |af B.Η (x-t)-af B.Η x|:=by
   rw[ὶ]
   apply Ò rfl
   intro t _
   rw[á]
  _≤ ∑ t:G,ν t*E:=by
   apply ᾯ
   intro t _
   by_cases ht:ν t=0
   ·simp[ht]
   ·exact Å
     (aj.cN
      Ô qx (pR t ht)) (ks t)
  _=(∑ t:G,ν t)*E:=by rw[Ἕ]
  _=E* ∑ t:G,ν t:=by ring
  _=200*((max B.Ι 1:ℕ):ℝ)*(κ:ℝ)* ∑ t:G,ν t:=rfl
lemma f4
  {B:aj G} {Φ Ο:ℝ≥0}
  (Ô:B.pG Φ Ο)
  (ν:G→ℝ)
  (ks: ∀ t,0≤ν t)
  (ob: ∑ t:G,ν t=1)
  (pR: ∀ t,ν t≠0→t∈(B.ai Ο).Η)
  (x:G) :
  af (B.ai Φ).Η x ≤
   2*ao
    (af (B.ai (Φ+Ο)).Η) ν x:=by
 let Jm:=(B.ai (Φ-Ο)).Η
 let K:=(B.ai Φ).Η
 let my:=(B.ai (Φ+Ο)).Η
 have ῳ:Jm.card≤K.card:=by
  apply ὣ
  exact aj.b5 (T4:Φ-Ο≤Φ)
 have ch :=
  Ô.2.2.trans (ὄ 2 ῳ)
 have x6:(0:ℝ)<K.card:=by
  exact_mod_cast(B.ai Φ).aE.card_pos
 have Eh:(0:ℝ)< my.card:=by
  exact_mod_cast(B.ai (Φ+Ο)).aE.card_pos
 have x7 (hx:x∈K) :
   ao (af my) ν x =
    (my.card:ℝ)⁻¹:=by
  rw[fG]
  simp only[ao]
  calc
   _ =
     ∑ t:G,ν t*(my.card:ℝ)⁻¹:=by
    apply Ò rfl
    intro t _
    by_cases ht:ν t=0
    ·simp[ht]
    ·have Aw :=
      aj.j2 hx (pR t ht)
     rw[dj Aw]
   _=(∑ t:G,ν t)*(my.card:ℝ)⁻¹:=by
    rw[Ἕ]
   _=(my.card:ℝ)⁻¹:=by rw[ob,ἃ]
 by_cases hx:x∈K
 ·rw[show(B.ai Φ).Η=K by rfl,
   dj hx,x7 hx]
  calc
   _ =1/(K.card:ℝ):=by rw[ῆ]
   _≤2/(my.card:ℝ):=by
    rw[Sy x6 Eh]
    simpa only[ἃ] using(show(my.card:ℝ)≤2*K.card by
     exact_mod_cast ch)
   _=2*(my.card:ℝ)⁻¹:=by rw[ἱ]
 ·rw[show(B.ai Φ).Η=K by rfl,
   dO hx]
  exact å (by norm_num)
   (fa
    (ὡ my) ks x)
lemma gC
  {B:aj G} (Ô:B.a1) {κ:ℝ≥0} (Jn:0<κ)
  (qx:κ≤1/(400*(max B.Ι 1:ℕ):ℝ≥0))
  (ν:G→ℝ) (ks: ∀ t,0≤ν t)
  (ob: ∑ t:G,ν t=1)
  (pR: ∀ t,ν t≠0→t∈(B.ai κ).Η)
  (x:G) :
  af B.Η x ≤
   2*ao
    (af (B.ai (1+κ)).Η) ν x:=by
 let d := max B.Ι 1
 have hd:0<d:=by simp[d]
 have Jo:κ≤1/(400*(d:ℝ≥0)):=by simpa[d] using qx
 have Ei:κ≤1/(100*(d:ℝ≥0)):=by
  apply Jo.trans
  apply Rb (by positivity) (by positivity)
  exact ἂ (by norm_num:(100:ℝ≥0)≤400) (by positivity)
 have Jp:κ≤1:=by
  apply Ei.trans
  rw[ᾜ]
  ·exact_mod_cast(show 1≤100*d by omega)
  ·positivity
 have jt:=Ô κ (by simpa[d] using Ei)
 have Ax:(100:ℝ)*d*(κ:ℝ)≤1/4:=by
  have NN:(κ:ℝ)≤1/(400*(d:ℝ)):=by
   exact_mod_cast Jo
  have Os:(0:ℝ)<d:=by exact_mod_cast hd
  calc
   _ ≤100*d*(1/(400*(d:ℝ))):=by gcongr
   _=1/4:=by field_simp; ring
 have Ej :
   ((B.ai (1+κ)).Η.card:ℝ) ≤
    2*((B.ai (1-κ)).Η.card:ℝ):=by
  nlinarith[jt.1,jt.2,
   show(0:ℝ)<B.Η.card by exact_mod_cast B.aE.card_pos]
 have ch :
   (B.ai (1+κ)).Η.card ≤
    2*(B.ai (1-κ)).Η.card:=by
  exact_mod_cast Ej
 have Hy:B.pG 1 κ:=⟨Jn,Jp,ch⟩
 simpa only[aj.oG] using
  f4
   Hy ν ks ob pR x
def ý (A:Finset G) (x:G):ℝ:=
 if x∈A then 1 else 0
omit [Γ G] [Δ G] in
@[simp] lemma rD {A:Finset G} {x:G} (hx:x∈A) :
  ý A x=1:=by simp[ý,hx]
def ὒ (A K:Finset G):ℝ:=
 (A.card:ℝ)/K.card
def Ó (A C:Finset G) (x:G):ℝ:=
 ao (ý A) (af C) x
omit [Γ G] in
lemma jV
  {A K:Finset G} (ἒ:A⊆K) (_hK:K.Nonempty) :
  ∑ x:G,ý A x*af K x =
   ὒ A K:=by
 have hsum :
   ∑ x∈A,ý A x*af K x =
    ∑ x:G,ý A x*af K x:=by
  apply Ro (S7 A)
  intro x _ Ek
  simp[ý,Ek]
 rw[←hsum]
 calc
  ∑ x∈A,ý A x*af K x =
    ∑ _x∈A,(K.card:ℝ)⁻¹:=by
   apply Ò rfl
   intro x hx
   rw[rD hx,
    dj (ἒ hx),ἃ]
  _=ὒ A K:=by
   simp[ὒ,ἱ]
lemma dP
  {B:aj G} (Ô:B.a1) {κ:ℝ≥0}
  (qx:κ≤1/(100*(max B.Ι 1:ℕ):ℝ≥0))
  {A C:Finset G} (ἒ:A⊆B.Η) (Ã:C.Nonempty)
  (Ὅ:C⊆(B.ai κ).Η) :
  |(∑ x:G,af B.Η x*Ó A C x) -
    ὒ A B.Η| ≤
   200*((max B.Ι 1:ℕ):ℝ)*(κ:ℝ):=by
 let ν:G→ℝ:=λ t↦af C (-t)
 have ks: ∀ t,0≤ν t:=λ t↦ὡ C (-t)
 have ob: ∑ t:G,ν t=1:=by
  calc
   _ = ∑ t:G,af C t:=
          ἐ (Equiv.neg G) _ _ (λ _↦rfl)
   _=1:=ᾁ Ã
 have pR: ∀ t,ν t≠0→t∈(B.ai κ).Η:=by
  intro t ht
  have ê: -t∈C:=(d6 Ã (-t)).mp ht
  exact aj.ec.mp (Ὅ ê)
 have x7 :
   ∑ y:G,
     |ao (af B.Η) ν y -
      af B.Η y| ≤
    200*((max B.Ι 1:ℕ):ℝ)*(κ:ℝ):=by
  simpa[ob] using
   g7
    Ô qx ν ks pR
 have Ay :
   ∑ x:G,af B.Η x*Ó A C x =
    ∑ y:G,ý A y *
     ao (af B.Η) ν y:=by
  simp only[Ó,ao,á]
  rw[ὶ]
  apply Ò rfl
  intro y _
  apply Ò rfl
  intro x _
  dsimp[ν]
  rw[neg_sub]
  ring
 have dc  :=
  jV ἒ B.aE
 rw[Ay, ←dc, ←QJ]
 simp_rw[←UY]
 calc
  _
                      ≤
    ∑ y:G, |ý A y *
     (ao (af B.Η) ν y -
      af B.Η y)|:=abs_sum_le_sum_abs _ _
  _≤ ∑ y:G,
    |ao (af B.Η) ν y -
     af B.Η y|:=by
   apply ᾯ
   intro y _
   by_cases hy:y∈A<;>simp[ý,hy]
  _≤200*((max B.Ι 1:ℕ):ℝ)*(κ:ℝ):=x7
lemma kk
  {B:aj G} (Ô:B.a1) {κ:ℝ≥0}
  (qx:κ≤1/(100*(max B.Ι 1:ℕ):ℝ≥0))
  {A ᾠ ᾴ:Finset G}
  (ξ:A.Nonempty) (ἒ:A⊆B.Η)
  (Lf:ᾠ.Nonempty) (Lg:ᾴ.Nonempty)
  (CS:ᾠ⊆(B.ai κ).Η)
  (CT:ᾴ⊆(B.ai κ).Η)
  {ε:ℝ} (_hε:0<ε)
  (ø :
   400*((max B.Ι 1:ℕ):ℝ)*(κ:ℝ) ≤
    ε*ὒ A B.Η/4) :
  (∃ x∈B.Η,
    (1-ε)*ὒ A B.Η≤Ó A ᾠ x ∧
    (1-ε)*ὒ A B.Η≤Ó A ᾴ x) ∨
   (∃ x:G,
    (1+ε/2)*ὒ A B.Η≤Ó A ᾠ x) ∨
   (∃ x:G,
    (1+ε/2)*ὒ A B.Η≤Ó A ᾴ x):=by
 let K:=B.Η
 let α := ὒ A K
 let E:ℝ:=200*((max B.Ι 1:ℕ):ℝ)*(κ:ℝ)
 let y0 :=  ∑ x:G,af K x*Ó A ᾠ x
 let y1 :=  ∑ x:G,af K x*Ó A ᾴ x
 have æ := B.aE
 have P2:0<α:=by
  dsimp[α,K,ὒ]
  exact ὗ (by exact_mod_cast ξ.card_pos) (by exact_mod_cast æ.card_pos)
 have Hz: |y0-α| ≤E:=by
  simpa[y0,α,E,K] using
   dP
    Ô qx ἒ Lf CS
 have HA: |y1-α| ≤E:=by
  simpa[y1,α,E,K] using
   dP
    Ô qx ἒ Lg CT
 have z1:α-E≤y0:=by
  have:=(abs_le.mp Hz).1
  linarith
 have Px:α-E≤y1:=by
  have:=(abs_le.mp HA).1
  linarith
 have NO:2*E≤ε*α/4:=by
  calc
   _ =400*((max B.Ι 1:ℕ):ℝ)*(κ:ℝ):=by
    dsimp[E]
    ring
   _≤ε*ὒ A B.Η/4:=ø
   _=ε*α/4:=by rfl
 by_cases Ύ :
   ∃ x∈K,
    (1-ε)*α≤Ó A ᾠ x ∧
    (1-ε)*α≤Ó A ᾴ x
 ·exact Or.inl Ύ
 by_cases Cf: ∃ x:G,(1+ε/2)*α≤Ó A ᾠ x
 ·exact Or.inr (Or.inl Cf)
 by_cases Cg: ∃ x:G,(1+ε/2)*α≤Ó A ᾴ x
 ·exact Or.inr (Or.inr Cg)
 exfalso
 let T:ℝ:=2*α-ε*α/2
 have Ὄ: ∀ x∈K,
   Ó A ᾠ x+Ó A ᾴ x<T:=by
  intro x hx
  have Py :=
   ᾙ (λ h↦Cf ⟨x,h⟩)
  have Pz :=
   ᾙ (λ h↦Cg ⟨x,h⟩)
  have Ap :
    Ó A ᾠ x<(1-ε)*α ∨
     Ó A ᾴ x<(1-ε)*α:=by
   by_cases h₁:(1-ε)*α≤Ó A ᾠ x
   ·right
    exact ᾙ (λ h₂↦Ύ ⟨x,hx,h₁,h₂⟩)
   ·left
    exact ᾙ h₁
  rcases Ap with NQ | NR
  ·dsimp[T]
   nlinarith
  ·dsimp[T]
   nlinarith
 have qy :
   ∑ x:G,af K x *
     (Ó A ᾠ x+Ó A ᾴ x) <
    ∑ x:G,af K x*T:=by
  apply Finset.sum_lt_sum
  ·intro x _
   by_cases hx:x∈K
   ·exact Å (Ὄ x hx).le
     (ὡ K x)
   ·simp[dO hx]
  ·refine ⟨0,Sz 0, ?_⟩
   have hz := B.se
   exact T6 (Ὄ 0 hz)
    ((qw æ 0).2 hz)
 have CV:y0+y1<T:=by
  calc
   _ = ∑ x:G,af K x *
     (Ó A ᾠ x+Ó A ᾴ x):=by
    dsimp[y0,y1]
    rw[←T7]
    apply Ò rfl
    intro x _
    ring
   _< ∑ x:G,af K x*T:=qy
   _=(∑ x:G,af K x)*T:=by rw[Ἕ]
   _=T:=by rw[ᾁ æ,ἃ]
 dsimp[T] at CV
 nlinarith
end
end ay
end
section
open Finset Function Real
open Complex (re)
open scoped BigOperators ComplexConjugate
namespace ay
namespace c5
variable {G:Type*} [Δ G] [Γ G]
noncomputable def c6 (A:Finset G) (psi:Ε G ℂ):ℂ:=
 ∑ x∈A,psi x
noncomputable def cj (A:Finset G) (Ο:ℝ):Finset (Ε G ℂ):=
 Finset.univ.filter λ psi↦Ο*A.card≤ ‖c6 A psi‖
@[simp] lemma gm {A:Finset G} {Ο:ℝ} {psi:Ε G ℂ} :
  psi∈cj A Ο↔Ο*A.card≤ ‖c6 A psi‖:=by
 simp[cj]
end c5
end ay
end
section
open Finset
open scoped BigOperators NNReal
namespace ay
noncomputable section
variable {G:Type*} [Γ G] [Δ G] [Β G]
def ᾕ (f:G→ℝ):ℕ→G→ℝ
 | 0=>af {0}
 | n+1=>ao (ᾕ f n) f
@[simp] lemma Ch (f:G→ℝ) :
  ᾕ f 0=af {0}:=rfl
@[simp] lemma j4 (f:G→ℝ) (n:ℕ) :
  ᾕ f (n+1) =
   ao (ᾕ f n) f:=rfl
lemma sY {f:G→ℝ} (hf: ∀ x,0≤f x) :
  ∀ n x,0≤ᾕ f n x:=by
 intro n
 induction n with
 | zero =>
   exact ὡ {0}
 | succ n Az =>
   exact fa Az hf
lemma oL {f:G→ℝ} (hf: ∑ x:G,f x=1) :
  ∀ n, ∑ x:G,ᾕ f n x=1:=by
 intro n
 induction n with
 | zero =>
   exact ᾁ (singleton_nonempty 0)
 | succ n Az =>
   rw[j4,iz,Az,hf,ἃ]
lemma jL
  (B:aj G) (σ:ℝ≥0) :
  ∀ n x,ᾕ (af (B.ai σ).Η) n x≠0 →
   x∈(B.ai ((n:ℝ≥0)*σ)).Η:=by
 intro n
 induction n with
 | zero =>
   intro x hx
   have P3:x=0:=by
    simpa using
     (d6 (singleton_nonempty 0) x).mp hx
   subst x
   simp
 | succ n Az =>
   intro x hx
   rw[j4,ao] at hx
   obtain ⟨y, -,hy⟩:=Finset.exists_ne_zero_of_sum_ne_zero hx
   have Lh:ᾕ (af (B.ai σ).Η) n y≠0:=
    (mul_ne_zero_iff.mp hy).1
   have HB:af (B.ai σ).Η (x-y)≠0:=
    (mul_ne_zero_iff.mp hy).2
   have Jq:=Az y Lh
   have F3:x-y∈(B.ai σ).Η:=
    (d6
     (B.ai σ).aE (x-y)).mp HB
   have xt:=aj.e8 Jq F3
   have Li:y+(x-y)=x:=by simp
   rw[Li] at xt
   simpa[T3,Nat.cast_one,US] using xt
def ἅ (w:G→ℝ) (ψ:Ε G ℂ):ℂ:=
 ∑ x:G,(w x:ℂ)*ψ x
lemma jU (A:Finset G) (ψ:Ε G ℂ) :
  ἅ (af A) ψ =
   ((A.card:ℝ)⁻¹ :ℂ)*c5.c6 A ψ:=by
 calc
  _ =
    ∑ x∈A,((A.card:ℝ)⁻¹ :ℂ)*ψ x:=by
   rw[ἅ, ←Ro (s₁:=A) (s₂:=Finset.univ)]
   ·apply Ò rfl
    intro x hx
    simp[af,hx]
   ·simp
   ·intro x MH Ek
    simp[af,Ek]
  _=((A.card:ℝ)⁻¹ :ℂ)*c5.c6 A ψ:=by
   rw[c5.c6,á]
lemma fy
  (C:aj G) (ψ:Ε G ℂ)
  (Jr:ψ∉c5.cj C.Η (1/2)) :
  ‖ἅ (af C.Η) ψ‖ <1/2:=by
 have ch:(0:ℝ)<C.Η.card:=by
  exact_mod_cast C.aE.card_pos
 have El :
   ‖c5.c6 C.Η ψ‖ <(1/2:ℝ)*C.Η.card:=by
  apply ᾙ
  intro h
  exact Jr (c5.gm.mpr h)
 calc
  _ =
    (C.Η.card:ℝ)⁻¹ * ‖c5.c6 C.Η ψ‖:=by
   rw[jU,ἑ]
   simp[Up]
  _<(C.Η.card:ℝ)⁻¹ *
    ((1/2:ℝ)*C.Η.card):=
   T6 El (inv_pos.mpr ch)
  _=1/2:=by field_simp
omit [Β G] in
lemma jb (f g:G→ℝ) (ψ:Ε G ℂ) :
  ἅ (ao f g) ψ=ἅ f ψ*ἅ g ψ:=by
 unfold ἅ ao
 push_cast
 calc
  _ =
    ∑ x:G, ∑ y:G,(f y:ℂ)*(g (x-y):ℂ)*ψ x:=by
   apply Ò rfl
   intro x hx
   rw[Ἕ]
  _= ∑ y:G, ∑ x:G,(f y:ℂ)*(g (x-y):ℂ)*ψ x:=
   ὶ
  _ =
    ∑ y:G,((f y:ℂ)*ψ y) *
     ∑ z:G,(g z:ℂ)*ψ z:=by
   apply Ò rfl
   intro y hy
   rw[á]
   refine ἐ (Equiv.subRight y) _ _ λ z↦ ?_
   have Jr:ψ z=ψ y*ψ (z-y):=by
    calc
     _ =ψ (y+(z-y)):=è ψ (by simp)
     _=ψ y*ψ (z-y):=St ψ y (z-y)
   simp only[Ut]
   rw[Jr]
   ring
  _=(∑ y:G,(f y:ℂ)*ψ y) *
    ∑ z:G,(g z:ℂ)*ψ z:=by
   simpa using
    (Ἕ (univ:Finset G) (λ y↦(f y:ℂ)*ψ y)
     (∑ z:G,(g z:ℂ)*ψ z)).symm
lemma q3 (f:G→ℝ) (ψ:Ε G ℂ) :
  ∀ n,ἅ (ᾕ f n) ψ=ἅ f ψ^n:=by
 intro n
 induction n with
 | zero =>
   unfold ἅ
   rw[Fintype.sum_eq_single 0]
   ·simp[af]
   ·intro y hy
    simp[af,hy]
 | succ n Az =>
   rw[j4,jb,Az,ᾬ]
omit [Β G] in
lemma t5 {w:G→ℝ} (hw: ∀ x,0≤w x)
  (ψ:Ε G ℂ) :
  ‖ἅ w ψ‖ ≤ ∑ x:G,w x:=by
 unfold ἅ
 calc
  _ ≤
    ∑ x:G, ‖(w x:ℂ)*ψ x‖:=Rq _ _
  _= ∑ x:G,w x:=by
   apply Ò rfl
   intro x hx
   simp[hw x]
def ed (B:aj G) (σ:ℝ≥0) (n:ℕ):G→ℝ:=
 ao
  (af (B.ai (1+(n:ℝ≥0)*σ)).Η)
  (ᾕ (af (B.ai σ).Η) n)
lemma qz (B:aj G) (σ:ℝ≥0) (n:ℕ) (x:G) :
  0≤ed B σ n x:=
       fa
  (ὡ _)
  (sY (ὡ _) n) x
lemma sn (B:aj G) (σ:ℝ≥0) (n:ℕ) :
  ∑ x:G,ed B σ n x=1:=by
 rw[ed,iz,
  ᾁ (B.ai (1+(n:ℝ≥0)*σ)).aE,
  oL
   (ᾁ (B.ai σ).aE),ἃ]
lemma nh
  (B:aj G) (σ:ℝ≥0) (n:ℕ) {x:G} (hx:x∈B.Η) :
  ed B σ n x =
   (((B.ai (1+(n:ℝ≥0)*σ)).Η.card:ℝ)⁻¹):=by
 rw[ed,fG]
 simp only[ao]
 calc
  _
                                           =
    ∑ t:G,ᾕ (af (B.ai σ).Η) n t *
     (((B.ai (1+(n:ℝ≥0)*σ)).Η.card:ℝ)⁻¹):=by
   apply Ò rfl
   intro t ht
   by_cases Js :
     ᾕ (af (B.ai σ).Η) n t=0
   ·simp[Js]
   ·have Ot :=
     jL B σ n t Js
    have Aw :=
           aj.j2
      (B:=B) (s:=1) (t:=(n:ℝ≥0)*σ)
      (by simpa using hx) Ot
    rw[dj Aw]
  _=(∑ t:G,
     ᾕ (af (B.ai σ).Η) n t) *
    (((B.ai (1+(n:ℝ≥0)*σ)).Η.card:ℝ)⁻¹):=by
   rw[Ἕ]
  _=(((B.ai (1+(n:ℝ≥0)*σ)).Η.card:ℝ)⁻¹):=by
   rw[oL
    (ᾁ (B.ai σ).aE)]
   simp
omit [Β G] in
lemma oM
  {B:aj G} (Ô:B.a1) {σ:ℝ≥0} (n:ℕ)
  (ø:(n:ℝ≥0)*σ ≤
   1/(100*(max B.Ι 1:ℕ):ℝ≥0)) :
  (B.ai (1+(n:ℝ≥0)*σ)).Η.card ≤
   2*B.Η.card:=by
 let κ:ℝ≥0:=(n:ℝ≥0)*σ
 let d := max B.Ι 1
 have jt:=Ô κ (by simpa[κ,d] using ø)
 have oc:(1+100*(d:ℝ)*(κ:ℝ))≤2:=by
  have NS:(κ:ℝ)≤1/(100*(d:ℝ)):=by
   exact_mod_cast(show κ≤1/(100*(d:ℝ≥0)) by
    simpa[κ,d] using ø)
  have hd:(0:ℝ)<d:=by exact_mod_cast(show 0<d by simp[d])
  calc
   _ ≤
     1+100*(d:ℝ)*(1/(100*(d:ℝ))):=by gcongr
   _=2:=by field_simp; ring
 have Jt :
   ((B.ai (1+κ)).Η.card:ℝ) ≤
    2*(B.Η.card:ℝ):=by
  calc
   _ ≤
     (1+100*(d:ℝ)*(κ:ℝ))*(B.Η.card:ℝ):=by
    simpa[κ,d] using jt.2
   _≤2*(B.Η.card:ℝ):=by gcongr
 exact_mod_cast Jt
lemma ly
  (B:aj G) (σ:ℝ≥0) (n:ℕ) (ψ:Ε G ℂ) :
  ‖ἅ (ed B σ n) ψ‖ ≤
   ‖ἅ (af (B.ai σ).Η) ψ‖ ^n:=by
 rw[ed,jb,
  q3,ἑ,norm_pow]
 have ju :
   ‖ἅ (af
    (B.ai (1+(n:ℝ≥0)*σ)).Η) ψ‖ ≤1:=by
  simpa[ᾁ
   (B.ai (1+(n:ℝ≥0)*σ)).aE] using
   t5
    (w:=af
     (B.ai (1+(n:ℝ≥0)*σ)).Η)
    (ὡ _) ψ
 exact RQ (by positivity) ju
end
end ay
end
section
open Finset
open scoped BigOperators NNReal
namespace ay
noncomputable section
namespace aj
variable {G:Type*} [Γ G] [Δ G] [Β G]
def ï (z:AddCircle (1:ℝ)):ℝ:=
 (QuotientAddGroup.equivIcoMod (p:=(1:ℝ)) (by norm_num) (-1/2) z).1
lemma k1 (z:AddCircle (1:ℝ)) :
  ï z∈Set.Ico (-1/2:ℝ) (1/2):=by
 let e:=QuotientAddGroup.equivIcoMod (p:=(1:ℝ)) (by norm_num) (-1/2)
 change-1/2≤ï z∧ï z<1/2
 constructor
 ·exact(e z).2.1
 ·have hz:=(e z).2.2
  norm_num at hz ⊢
  exact hz
@[simp] lemma zO (z:AddCircle (1:ℝ)) :
  ((ï z:ℝ):AddCircle (1:ℝ))=z:=by
 let e:=QuotientAddGroup.equivIcoMod (p:=(1:ℝ)) (by norm_num) (-1/2)
 have h:=e.symm_apply_apply z
 change((ï z:ℝ):AddCircle (1:ℝ))=z
 simpa only[e,ï,QuotientAddGroup.equivIcoMod_symm_apply] using h
lemma t6 (z:AddCircle (1:ℝ)): |ï z| ≤1/2:=by
 have hz:=k1 z
 rw[Set.mem_Ico] at hz
 rw[abs_le]
 constructor<;>linarith
lemma hH (z:AddCircle (1:ℝ)): ‖z‖ = |ï z|:=by
 calc
  ‖z‖ = ‖((ï z:ℝ):AddCircle (1:ℝ))‖:=by rw[zO]
  _= |ï z|:=
   (Ts (1:ℝ) (by norm_num)).2
    (by simpa using t6 z)
lemma gu (z w:AddCircle (1:ℝ)) :
  ‖z-w‖ ≤ |ï z-ï w|:=by
 have tw :
   (((ï z-ï w:ℝ):ℝ):AddCircle (1:ℝ))=z-w:=by
  simp
 rw[←tw]
 simpa only[ᾮ] using
  (QuotientAddGroup.norm_mk_le_norm
   (S:=AddSubgroup.zmultiples (1:ℝ)) :
    ‖((ï z-ï w:ℝ):AddCircle (1:ℝ))‖ ≤
     ‖ï z-ï w‖)
def uT (w r:ℝ):Fin 4:=
 if r< -(w/2) then 0
 else if r<0 then 1
 else if r<w/2 then 2
 else 3
lemma oN {w r s:ℝ}
  (_hw:0≤w) (hr: |r| ≤w) (hs: |s| ≤w)
  (ό:uT w r=uT w s) :
  |r-s| ≤w/2:=by
 rw[abs_le] at hr hs ⊢
 unfold uT at ό
 split_ifs at ό
 all_goals try { omega }
 all_goals constructor<;>linarith
def gr (B:aj G) (x:↥(B.ai 1).Η) :
  B.í→Fin 4:=
 λ γ↦uT (B.Υ γ.1:ℝ) (ï (γ.1 x.1))
omit [Β G] in
private lemma nQ (B:aj G)
  {x y:↥(B.ai 1).Η}
  (ni:B.gr x=B.gr y) :
  x.1-y.1∈(B.ai (1/2)).Η:=by
 rw[mem_carrier]
 intro γ oa
 have hx:=(mem_carrier (B.ai 1) x.1).mp x.2 γ oa
 have hy:=(mem_carrier (B.ai 1) y.1).mp y.2 γ oa
 simp only[oF,ἃ,SK] at hx hy ⊢
 rw[map_sub]
 have CW: |ï (γ x.1)| ≤(B.Υ γ:ℝ):=by
  rwa[←hH]
 have CX: |ï (γ y.1)| ≤(B.Υ γ:ℝ):=by
  rwa[←hH]
 have vU:=Uu ni ⟨γ,oa⟩
 calc
  _ ≤ |ï (γ x.1)-ï (γ y.1)|:=
   gu _ _
  _≤(B.Υ γ:ℝ)/2:=
   oN (by positivity) CW CX vU
  _=((1/2:ℝ≥0):ℝ)*(B.Υ γ:ℝ):=by
   norm_num
   ring
omit [Β G] in
private lemma qA (B:aj G)
  (a:B.í→Fin 4) :
  Fintype.card {x:↥(B.ai 1).Η// B.gr x=a} ≤
   (B.ai (1/2)).Η.card:=by
 classical
 by_cases jv:Nonempty
   {x:↥(B.ai 1).Η// B.gr x=a}
 ·let x₀ :=
   Classical.choice jv
  let f:{x:↥(B.ai 1).Η// B.gr x=a} →
    ↥(B.ai (1/2)).Η:=
   λ x↦⟨x.1.1-x₀.1.1,nQ B
    (x.2.trans x₀.2.symm)⟩
  have hf:Injective f:=by
   intro x y ni
   apply RI
   apply RI
   have ᾟ:=congr_arg (λ z↦z.1) ni
   dsimp[f] at ᾟ
   exact S8 ᾟ
  calc
   _ ≤
     Fintype.card ↥(B.ai (1/2)).Η:=
    R1 f hf
   _=(B.ai (1/2)).Η.card:=Rx _
 ·simp only[To] at jv
  simp
omit [Β G] in
lemma de (B:aj G) :
  (B.ai 1).Η.card ≤
   4^B.Ι*(B.ai (1/2)).Η.card:=by
 classical
 let S:=B.í→Fin 4
 let q := B.gr
 have jv: ∀ a:S,
   Fintype.card {x:↥(B.ai 1).Η// q x=a} ≤
    (B.ai (1/2)).Η.card:=by
  intro a
  exact qA B a
 have AA:Fintype.card S=4^B.Ι:=by
  dsimp[S,Ι]
  rw[TC]
  simp
 rw[←Rx (B.ai 1).Η, ←AA]
 by_contra h
 have Ί :
   Fintype.card S*(B.ai (1/2)).Η.card <
    Fintype.card ↥(B.ai 1).Η:=by omega
 obtain ⟨a,ha⟩:=Rk (f:=q) Ί
 have Em: #{x | q x=a}≤(B.ai (1/2)).Η.card:=by
  rw[←SL]
  exact jv a
 exact(ῑ Em) ha
omit [Β G] in
lemma iW (B:aj G) :
  (B.ai 2).Η.card ≤
   4^(3*B.Ι)*(B.ai (1/4)).Η.card:=by
 classical
 have h₂:=de (B.ai 2)
 have h₁:=de B
 have ἵ:=de (B.ai (1/2))
 simp only[f6,vo] at h₂ ἵ
 norm_num at h₂ ἵ
 calc
  _ ≤4^B.Ι*B.Η.card:=h₂
  _≤4^B.Ι*(4^B.Ι*(B.ai (1/2)).Η.card):=by
   gcongr
   simpa using h₁
  _≤4^B.Ι *
    (4^B.Ι*(4^B.Ι*(B.ai (1/4)).Η.card)):=by
   gcongr
  _=4^(3*B.Ι)*(B.ai (1/4)).Η.card:=by
   rw[←à, ←ᾫ, ←à, ←ᾫ]
   congr 2
   omega
private lemma nR
  (f:ℝ→ℝ) (hf:Monotone f)
  (rW:f (5/4)-f (1/4)<5) :
  ∃ x∈Set.Icc (1/2:ℝ) 1,
   ∀ y∈Set.Icc (1/4:ℝ) (5/4),
    |f y-f x| ≤60* |y-x|:=by
 classical
 by_contra! xv
 let zk:Set (ℝ × ℝ):={p |
  1/4≤p.1∧p.1<p.2∧p.2≤5/4 ∧
   60*(p.2-p.1)<f p.2-f p.1}
 let center:(ℝ × ℝ)→ℝ:=λ p↦(p.1+p.2)/2
 let radius:(ℝ × ℝ)→ℝ:=λ p↦(p.2-p.1)/2
 have tx {p:ℝ × ℝ} (hp:p∈zk):0<radius p:=by
  dsimp[zk] at hp
  dsimp[radius]
  linarith
 have CY (p:ℝ × ℝ) (hp:p∈zk):radius p≤1/2:=by
  dsimp[zk] at hp
  dsimp[radius]
  linarith
 obtain ⟨u,x8,CZ,HC⟩:=
  Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
   zk center radius (1/2) CY 5 (by norm_num)
 have zP:Set.Icc (1/2:ℝ) 1 ⊆
   ⋃ b:↥u,Metric.ball (center b.1) (6*radius b.1):=by
  intro x hx
  obtain ⟨y,G8,ni⟩:=xv x hx
  let p:ℝ × ℝ:=(min x y,max x y)
  have Lj:p∈zk:=by
   dsimp[zk,p]
   have G9:x∈Set.Icc (1/4:ℝ) (5/4):=by
    constructor<;>linarith[hx.1,hx.2]
   rcases le_total x y with hle | hle
   ·simp only[min_eq_left hle,max_eq_right hle]
    have xw: |f y-f x| =f y-f x:=
     ἳ (sub_nonneg.mpr (hf hle))
    have C2: |y-x| =y-x:=ἳ (sub_nonneg.mpr hle)
    rw[xw,C2] at ni
    exact ⟨G9.1,ᾙ (λ heq↦by
     have:y=x:=SC heq hle
     subst y
     norm_num at ni),G8.2,ni⟩
   ·simp only[min_eq_right hle,max_eq_left hle]
    have xw: |f y-f x| =f x-f y:=by
     rw[Su]
     exact ἳ (sub_nonneg.mpr (hf hle))
    have C2: |y-x| =x-y:=by
     rw[Su]
     exact ἳ (sub_nonneg.mpr hle)
    rw[xw,C2] at ni
    exact ⟨G8.1,ᾙ (λ heq↦by
     have:x=y:=SC heq hle
     subst y
     norm_num at ni),G9.2,ni⟩
  obtain ⟨b,MI,Ὂ⟩:=HC p Lj
  have Ou:x∈Metric.closedBall (center p) (radius p):=by
   rw[T8]
   dsimp[center,radius,p]
   constructor<;>rcases le_total x y with hle | hle <;>
    simp[hle]<;>linarith
  have Ef:x∈Metric.closedBall (center b) (5*radius b):=Ὂ Ou
  rw[Metric.mem_closedBall] at Ef
  rw[Set.mem_iUnion]
  refine ⟨⟨b,MI⟩, ?_⟩
  rw[Metric.mem_ball]
  have P4:0<radius b:=tx (x8 MI)
  linarith
 obtain ⟨v,Ci⟩:=isCompact_Icc.elim_finite_subcover
  (λ b:↥u↦Metric.ball (center b.1) (6*radius b.1))
  (λ _↦Metric.isOpen_ball) zP
 have BG:v.Nonempty:=by
  by_contra hv
  rw[Finset.not_nonempty_iff_eq_empty] at hv
  simpa[hv] using Ci (show(1/2:ℝ)∈Set.Icc (1/2) 1 by norm_num)
 have NU:(1/2:ℝ)≤6* ∑ b∈v,(b.1.2-b.1.1):=by
  have hm:MeasureTheory.volume (Set.Icc (1/2:ℝ) 1) ≤
    MeasureTheory.volume (⋃ b∈v,
     Metric.ball (center b.1) (6*radius b.1)):=
   MeasureTheory.measure_mono Ci
  have ῲ:0≤6* ∑ b∈v,(b.1.2-b.1.1):=by
   apply å (by norm_num)
   apply UZ
   intro b hb
   have:=tx (x8 b.2)
   dsimp[radius] at this
   linarith
  rw[←ENNReal.ofReal_le_ofReal_iff ῲ]
  have ἵ:ENNReal.ofReal (1/2:ℝ) =
    MeasureTheory.volume (Set.Icc (1/2:ℝ) 1):=by
   rw[Real.volume_Icc]
   norm_num
  rw[ἵ]
  calc
   MeasureTheory.volume (Set.Icc (1/2:ℝ) 1) ≤
     MeasureTheory.volume (⋃ b∈v,
      Metric.ball (center b.1) (6*radius b.1)):=hm
   _≤ ∑ b∈v,MeasureTheory.volume
     (Metric.ball (center b.1) (6*radius b.1)):=
    MeasureTheory.measure_biUnion_finset_le v _
   _=ENNReal.ofReal (6* ∑ b∈v,(b.1.2-b.1.1)):=by
    simp only[Real.volume_ball]
    rw[←ENNReal.ofReal_sum_of_nonneg]
    ·congr 1
     simp only[radius]
     calc
      ∑ b∈v,2*(6*((b.1.2-b.1.1)/2)) =
        ∑ b∈v,6*(b.1.2-b.1.1):=by
       apply Ò rfl
       intro b hb
       ring
      _=6* ∑ b∈v,(b.1.2-b.1.1):=by
       rw[á]
    ·intro b hb
     have:=tx (x8 b.2)
     dsimp[radius] at this
     positivity
   _=ENNReal.ofReal (6* ∑ b∈v,(b.1.2-b.1.1)):=rfl
 let e:↥u ↪ (ℝ × ℝ):=⟨Subtype.val,Subtype.val_injective⟩
 let F:Finset (ℝ × ℝ):=v.map e
 have Ha (p:ℝ × ℝ) :
   Metric.closedBall (center p) (radius p)=Set.Icc p.1 p.2:=by
  rw[T8]
  dsimp[center,radius]
  congr<;>ring
 have En: ∀ ⦃z⦄,z∈F →
   (1/4:ℝ)≤z.1∧z.1≤z.2∧z.2≤5/4:=by
  intro z hz
  obtain ⟨b,hb,rfl⟩:=Finset.mem_map.mp hz
  have ὸ:=x8 b.2
  dsimp[zk] at ὸ
  exact ⟨ὸ.1,ὸ.2.1.le,ὸ.2.2.1⟩
 have BH:(SetLike.coe F).PairwiseDisjoint
   (λ z↦Set.Icc z.1 z.2):=by
  intro z hz w hw Ov
  obtain ⟨bz,P5,rfl⟩:=Finset.mem_map.mp hz
  obtain ⟨bw,P6,rfl⟩:=Finset.mem_map.mp hw
  have ᾱ:(bz:ℝ × ℝ)≠bw:=by
   simpa[e] using Ov
  have hd:=CZ bz.2 bw.2 ᾱ
  change Disjoint (Metric.closedBall (center bz) (radius bz))
   (Metric.closedBall (center bw) (radius bw)) at hd
  rw[Ha,Ha] at hd
  simpa[e] using hd
 have NV: ∑ z∈F,(f z.2-f z.1)≤f (5/4)-f (1/4):=by
  have Na:=F.sum_intervalGapsWithin_add_sum_eq_sub rfl
   (a:=(1/4:ℝ)) (b:=(5/4:ℝ)) f
  calc
   ∑ z∈F,(f z.2-f z.1)≤_:=by
    rw[le_add_iff_nonneg_left]
    apply UZ
    intro i hi
    apply sub_nonneg.mpr
    apply hf
    exact F.intervalGapsWithin_fst_le_snd rfl _ (by norm_num)
     En BH
   _=f (5/4)-f (1/4):=Na
 have Nb:60* ∑ b∈v,(b.1.2-b.1.1) <
   ∑ z∈F,(f z.2-f z.1):=by
  rw[Finset.sum_map]
  simp only[e,Function.Embedding.coeFn_mk]
  rw[á]
  exact Tt BG
   (λ b hb↦(x8 b.2).2.2.2)
 linarith
omit [Β G] in
private lemma nS (B:aj G) :
  log ((B.ai (5/4)).Η.card:ℝ) -
    log ((B.ai (1/4)).Η.card:ℝ) <
   5*(max B.Ι 1:ℕ):=by
 classical
 let d := max B.Ι 1
 have ch:(B.ai (5/4)).Η.card ≤
   4^(3*B.Ι)*(B.ai (1/4)).Η.card:=by
  calc
   _ ≤(B.ai 2).Η.card:=
    ὣ (b5
     (show(5/4:ℝ≥0)≤2 by
      rw[ἲ (by norm_num:(0:ℝ≥0)<4)]
      norm_num))
   _≤4^(3*B.Ι)*(B.ai (1/4)).Η.card:=
    iW B
 have C3:(0:ℝ)<(B.ai (1/4)).Η.card:=by
  exact_mod_cast(B.ai (1/4)).aE.card_pos
 have C4:(0:ℝ)<(B.ai (5/4)).Η.card:=by
  exact_mod_cast(B.ai (5/4)).aE.card_pos
 have ei:=ᾆ C4 (show
   ((B.ai (5/4)).Η.card:ℝ) ≤
    ((4^(3*B.Ι)*(B.ai (1/4)).Η.card:ℕ):ℝ) by
   exact_mod_cast ch)
 rw[Rm,Rv,ñ (by positivity) C3.ne',
  ἦ] at ei
 have z2:(0:ℝ)<d:=by
  exact_mod_cast(show 0<d by simp[d])
 have Nc:(B.Ι:ℝ)≤d:=by
  exact_mod_cast(Tu B.Ι 1)
 have PA:log (4:ℝ)<5/3:=by
  rw[Real.log_four_eq]
  linarith[Real.log_two_lt_d9]
 have Ἆ:(3*B.Ι:ℕ)*log (4:ℝ)<5*d:=by
  push_cast
  calc
   _ ≤3*d*log 4:=by
    gcongr
   _<3*d*(5/3):=by gcongr
   _=5*d:=by ring
 dsimp[d] at Ἆ ⊢
 linarith
private noncomputable def fj (B:aj G) (s:ℝ):ℝ:=
 log ((B.ai s.toNNReal).Η.card:ℝ) /
  (max B.Ι 1:ℕ)
omit [Β G] in
private lemma q5 (B:aj G) :
  Monotone B.fj:=by
 intro s t Ἳ
 dsimp[fj]
 apply ῖ _ (by positivity)
 apply ᾆ
 ·exact_mod_cast(B.ai s.toNNReal).aE.card_pos
 ·exact_mod_cast ὣ
   (b5 (B:=B) (Real.toNNReal_mono Ἳ))
omit [Β G] in
private lemma og (B:aj G) :
  B.fj (5/4)-B.fj (1/4)<5:=by
 classical
 have h:=nS B
 have hd:(0:ℝ)<(max B.Ι 1:ℕ):=by positivity
 have Ow:Real.toNNReal (5/4:ℝ)=(5/4:ℝ≥0):=by
  apply NNReal.eq
  rw[Tg _ (by norm_num)]
  norm_num
 have Ox:Real.toNNReal (1/4:ℝ)=(1/4:ℝ≥0):=by
  apply NNReal.eq
  rw[Tg _ (by norm_num)]
  norm_num
 dsimp[fj]
 rw[Ow,Ox]
 rw[div_sub_div_same]
 exact(Tv hd).2 (by simpa[ä] using h)
omit [Β G] in
lemma eP (B:aj G) :
  ∃ Φ:ℝ≥0,1/2≤Φ∧Φ≤1 ∧
   (B.ai Φ).a1:=by
 classical
 let d:ℕ:=max B.Ι 1
 obtain ⟨r,hr,Ju⟩:=nR
  B.fj (q5 B)
   (og B)
 let Φ:ℝ≥0:=r.toNNReal
 have ἧ:(Φ:ℝ)=r:=Tg r (by linarith[hr.1])
 have zl:(1/2:ℝ≥0)≤Φ:=by
  rw[←U0,ἧ]
  norm_num
  exact hr.1
 have AD:Φ≤1:=by
  rw[←U0,ἧ]
  norm_num
  exact hr.2
 refine ⟨Φ,zl,AD, ?_⟩
 rw[sj]
 dsimp only[f6]
 intro Ρ dy
 have Jv:0<d:=by simp[d]
 have z2:(0:ℝ)<d:=by exact_mod_cast Jv
 have oK:Ρ≤1:=by
  apply dy.trans
  rw[ᾜ]
  ·exact_mod_cast(show 1≤100*d by omega)
  ·positivity
 have BI:(Ρ:ℝ)≤1/(100*(d:ℝ)):=by
  exact_mod_cast dy
 let ᾎ:ℝ≥0:=(1-Ρ)*Φ
 let mz:ℝ≥0:=(1+Ρ)*Φ
 have Oy:(Ρ:ℝ)≤1/100:=by
  calc
   (Ρ:ℝ)≤1/(100*(d:ℝ)):=BI
   _≤1/100:=by
    apply Rb (by norm_num) (by norm_num)
    have Eo:(1:ℝ)≤d:=by
     exact_mod_cast(show 1≤d by simp[d])
    nlinarith
 have ta:(1/2:ℝ)≤Φ∧(Φ:ℝ)≤1:=by
  exact ⟨by exact_mod_cast zl,by exact_mod_cast AD⟩
 have BJ:(ᾎ:ℝ)∈Set.Icc (1/4:ℝ) (5/4):=by
  dsimp[ᾎ]
  rw[NNReal.coe_sub oK]
  simp only[TN]
  have F4:(99/100:ℝ)≤1-(Ρ:ℝ):=by
   nlinarith
  constructor
  ·calc
    (1/4:ℝ)≤(99/100)*(1/2):=by norm_num
    _≤(1-(Ρ:ℝ))*(Φ:ℝ):=by
     exact ὤ F4 ta.1 (by norm_num)
      (sub_nonneg.mpr (by exact_mod_cast oK))
  ·calc
    (1-(Ρ:ℝ))*(Φ:ℝ)≤1*Φ:=
     ἂ (sub_le_self 1 (by positivity)) (by positivity)
    _≤1*1:=Å ta.2 (by norm_num)
    _≤5/4:=by norm_num
 have C5:(mz:ℝ)∈Set.Icc (1/4:ℝ) (5/4):=by
  dsimp[mz]
  constructor<;>nlinarith
 have Lk: |(ᾎ:ℝ)-r| ≤(Ρ:ℝ):=by
  rw[←ἧ]
  dsimp[ᾎ]
  rw[NNReal.coe_sub oK]
  simp only[TN]
  have xx:(0:ℝ)≤Φ:=by positivity
  rw[show(1-(Ρ:ℝ))*(Φ:ℝ)-Φ= -(Ρ*Φ) by ring,
   abs_neg,ἳ (å (by positivity) xx)]
  nlinarith[ta.2]
 have MJ: |(mz:ℝ)-r| ≤(Ρ:ℝ):=by
  rw[←ἧ]
  dsimp[mz]
  have xx:(0:ℝ)≤Φ:=by positivity
  rw[show(1+(Ρ:ℝ))*(Φ:ℝ)-Φ=Ρ*Φ by ring,
   ἳ (å (by positivity) xx)]
  nlinarith[ta.2]
 have tb:=Ju (ᾎ:ℝ) BJ
 have uU:=Ju (mz:ℝ) C5
 simp only[fj,Real.toNNReal_coe,
  show r.toNNReal=Φ by rfl] at tb uU
 change
  |log ((B.ai ᾎ).Η.card:ℝ)/d -
   log ((B.ai Φ).Η.card:ℝ)/d| ≤
    60* |(ᾎ:ℝ)-r| at tb
 change
  |log ((B.ai mz).Η.card:ℝ)/d -
   log ((B.ai Φ).Η.card:ℝ)/d| ≤
    60* |(mz:ℝ)-r| at uU
 rw[div_sub_div_same,TE,RT z2] at tb uU
 have Ep :
   log ((B.ai Φ).Η.card:ℝ) -
     log ((B.ai ᾎ).Η.card:ℝ) ≤
    60*d*(Ρ:ℝ):=by
  have xw:=(ἲ z2).mp tb
  calc
   _≤ |log ((B.ai ᾎ).Η.card:ℝ) -
     log ((B.ai Φ).Η.card:ℝ)|:=by
    rw[Su]
    exact SG _
   _≤60* |(ᾎ:ℝ)-r| *d:=xw
   _≤60*(Ρ:ℝ)*d:=by gcongr
   _=60*d*(Ρ:ℝ):=by ring
 have F5 :
   log ((B.ai mz).Η.card:ℝ) -
     log ((B.ai Φ).Η.card:ℝ) ≤
    60*d*(Ρ:ℝ):=by
  have xw:=(ἲ z2).mp uU
  calc
   _≤ |log ((B.ai mz).Η.card:ℝ) -
     log ((B.ai Φ).Η.card:ℝ)|:=SG _
   _≤60* |(mz:ℝ)-r| *d:=xw
   _≤60*(Ρ:ℝ)*d:=by gcongr
   _=60*d*(Ρ:ℝ):=by ring
 let u:ℝ:=100*d*(Ρ:ℝ)
 have Jw:0≤u:=by dsimp[u]; positivity
 have Oz:u≤1:=by
  dsimp[u]
  calc
   100*(d:ℝ)*(Ρ:ℝ) ≤
     100*d*(1/(100*d)):=by gcongr
   _=1:=by field_simp
 have Er:60*d*(Ρ:ℝ)=(3/5:ℝ)*u:=by
  dsimp[u]
  ring
 constructor
 ·change(1-u)*((B.ai Φ).Η.card:ℝ) ≤
   ((B.ai ᾎ).Η.card:ℝ)
  by_cases hu:u=1
  ·rw[hu]
   norm_num
  ·have Ll:u<1:=SM Oz hu
   have Hb:0<1-u:=sub_pos.mpr Ll
   have t7:(0:ℝ)<(B.ai Φ).Η.card:=by
    exact_mod_cast(B.ai Φ).aE.card_pos
   have ῳ:(0:ℝ)<(B.ai ᾎ).Η.card:=by
    exact_mod_cast(B.ai ᾎ).aE.card_pos
   rw[←SW (Ἃ Hb t7) ῳ]
   rw[ñ (sub_ne_zero.mpr (Ne.symm hu)) t7.ne']
   have HG:=QX Hb
   rw[Er] at Ep
   nlinarith
 ·change((B.ai mz).Η.card:ℝ) ≤
   (1+u)*((B.ai Φ).Η.card:ℝ)
  have t7:(0:ℝ)<(B.ai Φ).Η.card:=by
   exact_mod_cast(B.ai Φ).aE.card_pos
  have ju:(0:ℝ)<(B.ai mz).Η.card:=by
   exact_mod_cast(B.ai mz).aE.card_pos
  rw[←SW ju (Ἃ (by linarith) t7)]
  rw[ñ (by linarith) t7.ne']
  have HG:=Real.le_log_one_add_of_nonneg Jw
  have PC:(3/5:ℝ)*u≤2*u/(u+2):=by
   rw[ἇ (by linarith)]
   nlinarith
  rw[Er] at F5
  linarith
end aj
end
end ay
end
section
noncomputable section
open AddChar Finset Fintype Function RCLike
open scoped BigOperators ComplexConjugate
namespace ay.dT
variable {G:Type*} [Γ G] [Δ G]
def ω (f:G→ℂ) (χ:Ε G ℂ):ℂ:=⟪(χ:G→ℂ),f⟫ₙ_[ℂ]
lemma inversion (f:G→ℂ) (a:G) :
  ∑ χ:Ε G ℂ,ω f χ*χ a=f a:=by
 classical
 simp_rw[ω,wInner_cWeight_eq_expect,inner_apply',expect_mul,
  ←expect_sum_comm,ᾭ _ (f _), ←sum_mul,
  ←Rz,TK, ←map_sub_eq_div,
  AddChar.sum_apply_eq_ite,sub_eq_zero,ite_mul,zero_mul,Fintype.expect_ite_eq]
 simp[NNRat.smul_def (K:=ℂ),SN]
def Ω (f g:G→ℂ) (x:G):ℂ:=
 𝔼 y:G,f y*g (x-y)
def a2 (f g:G→ℂ) (x:G):ℂ:=
 𝔼 y:G,f (x+y)*conj (g y)
lemma mW (f g:G→ℂ) (χ:Ε G ℂ) :
  ω (Ω f g) χ=ω f χ*ω g χ:=by
 classical
 simp_rw[ω,wInner_cWeight_eq_expect,inner_apply,Ω,
  mul_expect,expect_mul, ←expect_product',univ_product_univ]
 refine RW ((Equiv.prodComm _ _).trans<|
  ((Equiv.refl _).prodShear Equiv.subRight).trans<| Equiv.prodComm _ _) _ _ λ (a,b)↦ ?_
 simp[Q7, ←ᾪ, ←map_add_eq_mul]
lemma zQ (f:G→ℂ) (χ:Ε G ℂ) :
  ω (λ x↦conj (f (-x))) χ=conj (ω f χ):=by
 classical
 simp only[ω,wInner_cWeight_eq_expect,inner_apply,map_expect,ᾪ,
  Tl]
 refine RW (Equiv.neg _) _ _ λ i↦ ?_
 simp only[Equiv.neg_apply, ←inv_apply_eq_conj, ←inv_apply',inv_apply]
lemma l6 (f g:G→ℂ) :
  a2 f g=Ω f (λ x↦conj (g (-x))):=by
 funext x
 simp only[a2,Ω]
 refine RW (Equiv.addLeft x) _ _ λ y↦ ?_
 simp
lemma kt (f g:G→ℂ) (χ:Ε G ℂ) :
  ω (a2 f g) χ=ω f χ*conj (ω g χ):=by
 rw[l6,mW,zQ]
lemma t8 (f:G→ℂ) (χ:Ε G ℂ) :
  ω (a2 f f) χ=(Complex.normSq (ω f χ):ℂ):=by
 rw[kt]
 exact Complex.mul_conj _
end ay.dT
end
end
section
noncomputable section
open AddChar Finset Fintype Function RCLike
open scoped BigOperators ComplexConjugate
namespace ay.jw
open dT
variable {G:Type*} [Γ G] [Δ G]
def È (nu:G→ℝ) (f:G→ℂ) (p:ℕ):ℝ:=
 𝔼 x:G,nu x* ‖f x‖ ^p
def ᾔ (nu:G→ℝ) (ß:Ε G ℂ):ℂ:=
 𝔼 x:G,(nu x:ℂ)*ß x
def fO (nu:G→ℝ):Prop:=
 ∀ ß:Ε G ℂ,
  0≤(ᾔ nu ß).re∧(ᾔ nu ß).im=0
lemma k2 (a b:G→ℝ) (x:G) :
  (ay.ao a b x:ℂ) =
   (Fintype.card G:ℂ) *
    dT.Ω ((↑) ∘ a) ((↑) ∘ b) x:=by
 unfold ay.ao dT.Ω
 rw[Rj]
 push_cast
 field_simp
 simp[Rh]
lemma ga (a:G→ℝ) (x:G) :
  (ay.ἆ a a x:ℂ) =
   (Fintype.card G:ℂ) *
    a2 ((↑) ∘ a) ((↑) ∘ a) x:=by
 unfold ay.ἆ dT.a2
 rw[Rj]
 push_cast
 field_simp
 refine ἐ (Equiv.subRight x) _ _ λ y↦ ?_
 simp
lemma k3 {nu:G→ℝ}
  (rq:fO nu) (ß:Ε G ℂ) :
  ᾔ nu ß=((ᾔ nu ß).re:ℂ):=by
 apply Complex.ext
 ·simp
 ·simpa using(rq ß).2
lemma q6 (nu:G→ℝ) (ß:Ε G ℂ) (t:G) :
  (𝔼 x:G,(nu (x-t):ℂ)*ß x)=ß t*ᾔ nu ß:=by
 unfold ᾔ
 rw[mul_expect]
 refine RW (M:=ℂ) (Equiv.subRight t:G ≃ G) _ _ λ y↦ ?_
 simp only[Ut,Ἱ]
 have hc:ß y=ß t*ß (y+ -t):=by
  rw[←map_add_eq_mul]
  congr 1
  abel
 rw[hc]
 ring
lemma oh {nu:G→ℝ}
  (rq:fO nu) (ß:Ε G ℂ) (t:G) :
  ‖𝔼 x:G,(nu (x-t):ℂ)*ß x‖ =(ᾔ nu ß).re:=by
 rw[q6,ἑ,Q0,
  ἃ,k3 rq]
 simp[ἳ (rq ß).1]
lemma gv
  (a b:G→ℝ) :
  fO
   (ay.ao
    (ay.ἆ a a)
    (ay.ἆ b b)):=by
 let ac:G→ℂ:=(↑) ∘ a
 let bc:G→ℂ:=(↑) ∘ b
 let da := a2 ac ac
 let db := a2 bc bc
 let h := dT.Ω da db
 have t9 (x:G) :
   (ay.ao
     (ay.ἆ a a)
     (ay.ἆ b b) x:ℂ) =
    (Fintype.card G:ℂ)^3*h x:=by
  rw[k2]
  have OA:((↑) ∘ ay.ἆ a a) =
    λ y↦(Fintype.card G:ℂ)*da y:=by
   funext y
   exact ga a y
  have OB:((↑) ∘ ay.ἆ b b) =
    λ y↦(Fintype.card G:ℂ)*db y:=by
   funext y
   exact ga b y
  rw[OA,OB]
  simp only[h,da,db,dT.Ω,
   Rj]
  have ch:(Fintype.card G:ℂ)≠0:=by
   exact_mod_cast SN
  field_simp
  rw[á]
  apply Ò rfl
  intro x hx
  ring
 intro ß
 have Ay :
   ᾔ
     (ay.ao
      (ay.ἆ a a)
      (ay.ἆ b b)) ß =
    (Fintype.card G:ℂ)^3*ω h (-ß):=by
  unfold ᾔ
  simp_rw[t9]
  calc
   _ =
     (Fintype.card G:ℂ)^3*(𝔼 x:G,h x*ß x):=by
    calc
     _=𝔼 x:G,(Fintype.card G:ℂ)^3*(h x*ß x):=by
      congr 1 with x
      ring
     _=_:=by rw[←mul_expect]
   _=_:=by
    congr 1
    simp[ω,wInner_cWeight_eq_expect,inner_apply,map_neg_eq_conj]
 have uO :
   ᾔ
     (ay.ao
      (ay.ἆ a a)
      (ay.ἆ b b)) ß =
    (((Fintype.card G:ℝ)^3*Complex.normSq (ω ac (-ß)) *
     Complex.normSq (ω bc (-ß)):ℝ):ℂ):=by
  rw[Ay]
  simp only[h,mW,da,db,t8]
  push_cast
  ring
 rw[uO]
 constructor
 ·simpa only[Complex.ofReal_re] using
   (å
   (å (by positivity) (Uk _))
   (Uk _))
 ·exact Complex.ofReal_im _
omit [Γ G] in
lemma iG {I:Type*} {k:ℕ} (_hk:k≠0)
  (nu:G→ℝ) (s:Finset I) (u:I→G→ℂ) :
  (È nu (∑ i∈s,u i) (2*k):ℂ) =
   ∑ x∈(piFinset λ _:Fin k↦s), ∑ y∈(piFinset λ _:Fin k↦s),
    𝔼 a:G,(nu a:ℂ) *
     ((∏ i,conj (u (x i) a))* ∏ i,u (y i) a):=by
 rw[È]
 push_cast
 simp_rw[Si]
 calc
  _ =
    𝔼 a:G,(nu a:ℂ) *
     ((∑ i∈s,conj (u i a))^k*(∑ j∈s,u j a)^k):=by
   congr 1 with a
   simp_rw[Ἂ, ←UX,Ἀ,ᾘ]
  _=_:=by
   simp_rw[sum_pow',Finset.sum_mul_sum,mul_sum,expect_sum_comm]
omit [Γ G] in
lemma dx {nu:G→ℝ} (rq: ∀ x,0≤nu x)
  (f:G→ℂ) (p:ℕ):0≤È nu f p:=
       expect_nonneg λ x _↦å (rq x) (ἥ (Re _) _)
lemma gw
  {p:ℕ} (hp:p≠0) (mx:Even p)
  (nu:G→ℝ) (rq: ∀ x,0≤nu x)
  (z3:fO nu) (t:G) (f:G→ℂ) :
  È (λ x↦nu (x-t)) (Ω f f) p ≤
   È nu (a2 f f) p:=by
 obtain ⟨k,rfl⟩:=mx.two_dvd
 simp only[ne_eq,mul_eq_zero,OfNat.ofNat_ne_zero,false_or] at hp
 let term:(Fin k→ Ε G ℂ) × (Fin k→ Ε G ℂ)→ℂ:=
  λ psi ↦
   conj (∏ i,ω f (psi.1 i)^2) *
    (∏ i,ω f (psi.2 i)^2) *
     (𝔼 x:G,(nu (x-t):ℂ) *
      ((∑ i,psi.2 i- ∑ i,psi.1 i) x))
 refine Complex.le_of_eq_sum_of_eq_sum_norm term univ
  (dx (λ x↦rq (x-t)) _ _) ?_ ?_
 ·have hinv:Ω f f =
    ∑ ß:Ε G ℂ,λ x↦ω (Ω f f) ß*ß x:=by
   funext x
   simpa only[Si] using(inversion (Ω f f) x).symm
  rw[hinv]
  have hm:=iG (G:=G) hp
   (λ x↦nu (x-t)) (univ:Finset (Ε G ℂ))
   (λ ß x↦ω (Ω f f) ß*ß x)
  rw[hm]
  simp only[term]
  simp_rw[mW, ←sq,Ul,mul_expect,
   RO]
  simp[Q7,ä,map_neg_eq_conj,prod_mul_distrib]
  ring_nf
 ·have hinv:a2 f f =
    ∑ ß:Ε G ℂ,
     λ x↦ω (a2 f f) ß*ß x:=by
   funext x
   simpa only[Si] using
    (inversion (a2 f f) x).symm
  rw[hinv]
  have hm:=iG (G:=G) hp nu
   (univ:Finset (Ε G ℂ))
   (λ ß x↦ω (a2 f f) ß*ß x)
  rw[hm]
  simp only[term]
  simp_rw[kt,Complex.mul_conj',
   Ul,mul_expect]
  congr 1 with psi
  congr 1 with Æ
  simp only[ᾪ,map_pow,prod_mul_distrib,Q7,
   map_prod,RO,AddChar.coe_sum,
   Finset.prod_apply,
   Complex.conj_ofReal]
  have Jx :
    (𝔼 x:G,(nu x:ℂ) *
      ((∏ i,conj (psi i x))* ∏ i,Æ i x)) =
     ᾔ nu (∑ i,Æ i- ∑ i,psi i):=by
   simp[ᾔ,map_neg_eq_conj,ä,
    RO]
  let a:ℂ:=
   (∏ i,(‖ω f (psi i)‖ ^2:ℂ)) *
    ∏ i,(‖ω f (Æ i)‖ ^2:ℂ)
  let c :=
   conj (∏ i,ω f (psi i)^2)* ∏ i,ω f (Æ i)^2
  let Ο :=  ∑ i,Æ i- ∑ i,psi i
  have Ὢ :
    (𝔼 x:G,(nu x:ℂ) *
      (a*((∏ i,conj (psi i x))* ∏ i,Æ i x))) =
     a*ᾔ nu Ο:=by
   calc
    _=𝔼 x:G,a*((nu x:ℂ) *
       ((∏ i,conj (psi i x))* ∏ i,Æ i x)):=by
      congr 1 with x
      ring
    _=a*(𝔼 x:G,(nu x:ℂ) *
       ((∏ i,conj (psi i x))* ∏ i,Æ i x)):=by
      rw[←mul_expect]
    _=_:=by simpa only[Ο] using è (a*·) Jx
  have y2 :
    (𝔼 x:G,c*(nu (x-t):ℂ) *
      ((∏ i,Æ i x)* ∏ i,psi i (-x))) =
     c*(𝔼 x:G,(nu (x-t):ℂ)*Ο x):=by
   calc
    _=𝔼 x:G,c*((nu (x-t):ℂ)*Ο x):=by
     congr 1 with x
     dsimp only[Ο]
     simp[map_neg_eq_conj,RO,ä,Ῐ]
     ring
    _=_:=by rw[←mul_expect]
  have Lm :
    (𝔼 x:G,(nu x:ℂ) *
      (a*((∏ i,conj (psi i x))* ∏ i,Æ i x))) =
     (‖𝔼 x:G,c*(nu (x-t):ℂ) *
      ((∏ i,Æ i x)* ∏ i,psi i (-x))‖ :ℂ):=by
   rw[Ὢ,y2,ἑ,
    oh z3 Ο t]
   rw[k3 z3]
   dsimp only[a,c]
   push_cast
   simp[norm_prod]
  simpa[a,c,TI,prod_mul_distrib,à,ä,Ῐ] using Lm
lemma jN
  {p:ℕ} (hp:p≠0) (mx:Even p)
  (nu:G→ℝ) (rq: ∀ x,0≤nu x)
  (z3:fO nu) (t:G) (f:G→ℂ) :
  ∑ x:G,nu (x-t)* ‖Ω f f x‖ ^p ≤
   ∑ x:G,nu x* ‖a2 f f x‖ ^p:=by
 have h:=gw
  hp mx nu rq z3 t f
 simp only[È,Rj] at h
 exact(R9
  (by positivity:(0:ℝ)<Fintype.card G)).mp h
end ay.jw
end
end
section
open Finset Fintype Function
open scoped BigOperators NNReal
namespace ay
namespace hJ
noncomputable section
open dT
variable {G:Type*} [Γ G] [Δ G] [Β G]
def c4 (C D:Finset G):G→ℝ:=
 ao
  (ἆ (af C) (af C))
  (ἆ (af D) (af D))
lemma mT (C D:Finset G) (x:G) :
  0≤c4 C D x:=by
 apply fa
 ·exact gB
   (ὡ C) (ὡ C)
 ·exact gB
   (ὡ D) (ὡ D)
lemma uV {C D:Finset G}
  (Ã:C.Nonempty) (Ð:D.Nonempty) :
  ∑ x:G,c4 C D x=1:=by
 rw[c4,iz,
  ho,ho,
  ᾁ Ã,ᾁ Ð]
 norm_num
lemma hO
  {B:aj G} {Ο:ℝ≥0} {C:Finset G}
  (Ã:C.Nonempty) (Ὅ:C⊆(B.ai Ο).Η)
  {x:G}
  (hx:ἆ
   (af C) (af C) x≠0) :
  x∈(B.ai (2*Ο)).Η:=by
 by_contra C6
 apply hx
 rw[ἆ]
 apply UN
 intro y _
 by_cases hy:af C y=0
 ·simp[hy]
 have OC:y∈C:=(d6 Ã y).mp hy
 by_cases Es:af C (y-x)=0
 ·simp[Es]
 have Nd:y-x∈C:=
  (d6 Ã (y-x)).mp Es
 have AF:=aj.j2 (Ὅ OC) (Ὅ Nd)
 have heq:y-(y-x)=x:=by abel
 rw[heq] at AF
 exact(C6 (by simpa[ΐ] using AF)).elim
lemma nj
  {B:aj G} {Ο:ℝ≥0} {C D:Finset G}
  (Ã:C.Nonempty) (Ð:D.Nonempty)
  (Ὅ:C⊆(B.ai Ο).Η)
  (gn:D⊆(B.ai Ο).Η)
  {x:G} (hx:c4 C D x≠0) :
  x∈(B.ai (4*Ο)).Η:=by
 by_contra C6
 apply hx
 rw[c4,ao]
 apply UN
 intro y _
 let Hc:=ἆ
  (af C) (af C)
 let Hd:=ἆ
  (af D) (af D)
 by_cases hy:Hc y=0
 ·exact mul_eq_zero.mpr (Or.inl (by simpa[Hc] using hy))
 by_cases ni:Hd (x-y)=0
 ·exact mul_eq_zero.mpr (Or.inr (by simpa[Hd] using ni))
 have Jq :=
  hO Ã Ὅ hy
 have F3 :=
  hO Ð gn ni
 have AF:=aj.e8 Jq F3
 have heq:y+(x-y)=x:=by abel
 rw[heq] at AF
 exact(C6 (by
  simpa[show(2:ℝ≥0)*Ο+2*Ο=4*Ο by ring] using AF)).elim
omit [Β G] in
lemma lU
  (mu Ψ nu h:G→ℝ) (R:ℝ)
  (zR: ∀ x,0≤Ψ x)
  (BK: ∑ x:G,Ψ x=1)
  (hh: ∀ x,0≤h x)
  (Jy: ∀ x,mu x≤2*ao Ψ nu x)
  (kE: ∀ t:G, ∑ x:G,nu (x-t)*h x≤R) :
  ∑ x:G,mu x*h x≤2*R:=by
 calc
  _ ≤
    ∑ x:G,(2*ao Ψ nu x)*h x:=by
   apply ᾯ
   intro x _
   exact ἂ (Jy x) (hh x)
  _=2* ∑ x:G,ao Ψ nu x*h x:=by
   rw[á]
   apply Ò rfl
   intro x _
   ring
  _=2* ∑ t:G,Ψ t* ∑ x:G,nu (x-t)*h x:=by
   apply è (λ z:ℝ↦2*z)
   simp only[ao]
   calc
    _ =
      ∑ x:G, ∑ y:G,(Ψ y*nu (x-y))*h x:=by
     apply Ò rfl
     intro x _
     rw[Ἕ]
    _= ∑ t:G, ∑ x:G,(Ψ t*nu (x-t))*h x:=
     ὶ
    _= ∑ t:G,Ψ t* ∑ x:G,nu (x-t)*h x:=by
     apply Ò rfl
     intro t _
     rw[á]
     apply Ò rfl
     intro x _
     ring
  _≤2* ∑ t:G,Ψ t*R:=by
   apply Å
   ·apply ᾯ
    intro t _
    exact Å (kE t) (zR t)
   ·norm_num
  _=2*R:=by rw[←Ἕ,BK,ἃ]
lemma gI
  {B:aj G} {Ο:ℝ≥0} {C D:Finset G}
  (Ô:B.a1) (ò:0<Ο)
  (ῴ:4*Ο ≤
   1/(400*(max B.Ι 1:ℕ):ℝ≥0))
  (Ã:C.Nonempty) (Ð:D.Nonempty)
  (Ὅ:C⊆(B.ai Ο).Η)
  (gn:D⊆(B.ai Ο).Η)
  (p:ℕ) (f:G→ℂ)
  (Ᾰ: ∀ t:G,
   ∑ x:G,c4 C D (x-t)* ‖Ω f f x‖ ^p ≤
    ∑ x:G,c4 C D x* ‖a2 f f x‖ ^p) :
  ∑ x:G,af B.Η x* ‖Ω f f x‖ ^p ≤
   2* ∑ x:G,c4 C D x *
    ‖a2 f f x‖ ^p:=by
 let nu:=c4 C D
 let Ψ:=af (B.ai (1+4*Ο)).Η
 apply lU
   (af B.Η) Ψ nu
   (λ x↦ ‖Ω f f x‖ ^p)
   (∑ x:G,c4 C D x* ‖a2 f f x‖ ^p)
 ·exact ὡ _
 ·exact ᾁ (B.ai (1+4*Ο)).aE
 ·intro x
  positivity
 ·intro x
  exact gC
   Ô (by positivity:0<(4:ℝ≥0)*Ο) ῴ nu
   (mT C D) (uV Ã Ð)
   (λ t ht↦nj Ã Ð Ὅ gn ht) x
 ·exact Ᾰ
lemma kF
  {B:aj G} {Ο:ℝ≥0} {C D:Finset G}
  (Ô:B.a1) (ò:0<Ο)
  (ῴ:4*Ο ≤
   1/(400*(max B.Ι 1:ℕ):ℝ≥0))
  (Ã:C.Nonempty) (Ð:D.Nonempty)
  (Ὅ:C⊆(B.ai Ο).Η)
  (gn:D⊆(B.ai Ο).Η)
  {p:ℕ} (hp:p≠0) (mx:Even p) (f:G→ℂ) :
  ∑ x:G,af B.Η x* ‖Ω f f x‖ ^p ≤
   2* ∑ x:G,c4 C D x *
    ‖a2 f f x‖ ^p:=by
 apply gI
  Ô ò ῴ Ã Ð Ὅ gn p f
 intro t
 apply jw.jN hp mx
   (c4 C D) (mT C D)
 ·simpa only[c4] using
   jw.gv
    (af C) (af D)
end
end hJ
end ay
end
section
namespace ay
open Finset
open scoped BigOperators Pointwise translate ENNReal NNReal
noncomputable def ᾨ (q:ℕ) (ε:ℝ):ℕ:=
 ⌈(64:ℝ)*q/(ε/2)^2⌉₊
lemma vz
  {G:Type*} [Δ G] [Β G] [Γ G]
  [MeasurableSpace G] [Α G]
  {A S:Finset G} (ξ:A.Nonempty) (Ø:S.Nonempty)
  (q:ℕ) (hq:1≤q) (ε:ℝ) (hε:0<ε) (f:G→ℂ) :
  let k:=ᾨ q ε
  ∃ T:Finset G,
   T⊆S ∧
   T.Nonempty ∧
   (((#A:ℝ)^k/2* #S)/(#(A+S):ℝ)^k≤ #T) ∧
   ∀ s∈T, ∀ t∈T,
    (aJ (2*q) (τ (t-s) ((Χ (mu A) f))-(Χ (mu A) f))) ≤
     ε*(aJ (2*q) f):=by
 classical
 let k:=ᾨ q ε
 let L:=gl.l k q (ε/2) f A
 have Cj:(64:ℝ)*q/(ε/2)^2≤k:=by
  change(64:ℝ)*q/(ε/2)^2 ≤
   (↑⌈(64:ℝ)*q/(ε/2)^2⌉₊:ℝ)
  exact Rr _
 have Ln:0<k:=by
  rw[← @Nat.cast_pos ℝ]
  exact Cj.trans_lt'
   (ὗ (Ἃ (by norm_num) (by positivity)) (ᾅ (half_pos hε) 2))
 have Jz:(#A:ℝ)^k/2≤ #L:=
  gl.Ho (half_pos hε) hq Cj
 have Nf:L.Nonempty:=by
  rw[←card_pos, ← @Nat.cast_pos ℝ]
  exact Jz.trans_lt' (by positivity)
 let P:Finset ((Fin k→G) × G):=L ×ˢ S
 let X:Finset (Fin k→G):=(piFinset λ _:Fin k↦((A+S)))
 let φ:((Fin k→G) × G)→(Fin k→G):=λ z↦z.1+λ _↦z.2
 have ᾉ:X.Nonempty:=(ξ.add Ø).piFinset_const
 have AG: ∀ z∈P,φ z∈X:=by
  rintro ⟨l,s⟩ JA
  simp only[P,mem_product] at JA
  simp only[X,RX,φ,RM]
  have AH:l∈L:=JA.1
  change l∈gl.l k q (ε/2) f A at AH
  rw[gl.l,mem_filter] at AH
  have hl:l∈(piFinset λ _:Fin k↦A):=AH.1
  intro i
  exact Finset.add_mem_add (Fintype.mem_piFinset.1 hl i) JA.2
 have Et: #X= #(A+S)^k:=by simp[X]
 have HI:(#X:ℝ)=(#(A+S):ℝ)^k:=by
  rw[Et]
  norm_cast
 have F6:(#X:ℝ)≠0:=by exact_mod_cast ᾉ.card_ne_zero
 have HJ :
   ∃ x∈X,((#L:ℝ)* #S)/ #X ≤
    ∑ z∈P with φ z=x,(1:ℝ):=by
  refine Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum AG ᾉ ?_
  simp only[ᾚ,sum_const,P,card_product,Rm]
  rw[ä (#X:ℝ),Tz _ F6,Ἣ]
 obtain ⟨x,He,hx⟩:=HJ
 let Q:Finset ((Fin k→G) × G):={z∈P | φ z=x}
 let T:Finset G:=Q.image Prod.snd
 have Eu:(#Q:ℝ)= ∑ z∈P with φ z=x,(1:ℝ):=by simp[Q]
 have HK:Set.InjOn Prod.snd (Q:Set ((Fin k→G) × G)):=by
  rintro ⟨JC,s₁⟩ Lo ⟨JE,s₂⟩ Lq hs
  have JF:(JC,s₁)∈Q:=Lo
  have JG:(JE,s₂)∈Q:=Lq
  have OD:JC+(λ _↦s₁)=JE+λ _↦s₂:=
   (mem_filter.1 JF).2.trans (mem_filter.1 JG).2.symm
  cases hs
  apply Prod.ext
  ·funext i
   exact add_right_cancel (SR OD i)
  ·rfl
 have nk: #T= #Q:=card_image_iff.mpr HK
 have Lr:(0:ℝ)< #Q:=by
  have Ev:0<((#L:ℝ)* #S)/ #X:=
   ὗ (Ἃ (by exact_mod_cast Nf.card_pos) (by exact_mod_cast Ø.card_pos))
    (by exact_mod_cast ᾉ.card_pos)
  exact Ev.trans_le (by simpa[Eu] using hx)
 have ῢ:T.Nonempty:=by
  rw[←card_pos, ← @Nat.cast_pos ℝ,nk]
  exact Lr
 refine ⟨T, ?_,ῢ, ?_, ?_⟩
 ·intro s JH
  obtain ⟨z,OE,rfl⟩:=mem_image.1 JH
  exact(mem_product.1 (mem_filter.1 OE).1).2
 ·calc
   (((#A:ℝ)^k/2* #S)/(#(A+S):ℝ)^k)
     = (((#A:ℝ)^k/2* #S)/ #X):=by rw[HI]
   _≤((#L:ℝ)* #S)/ #X:=by gcongr
   _≤ #Q:=by simpa[Eu] using hx
   _= #T:=by exact_mod_cast nk.symm
 ·intro s JH t OF
  obtain ⟨⟨a,s'⟩,JI,OG⟩:=mem_image.1 JH
  obtain ⟨⟨b,t'⟩,JJ,OH⟩:=mem_image.1 OF
  simp only at OG OH
  subst s'
  subst t'
  have OI:a∈L:=(mem_product.1 (mem_filter.1 JI).1).1
  have OJ:b∈L:=(mem_product.1 (mem_filter.1 JJ).1).1
  have OK:a+(λ _↦s)=x:=(mem_filter.1 JI).2
  have OL:b+(λ _↦t)=x:=(mem_filter.1 JJ).2
  have hab:a+(λ _↦s-t)=b:=by
   funext i
   have ha:=SR OK i
   have hb:=SR OL i
   simp only[RM] at ha hb ⊢
   calc
    a i+(s-t)=(a i+s)-t:=by abel
    _=x i-t:=by rw[ha]
    _=b i:=by rw[←hb]; abel
  have HL:a+(λ _↦s-t)∈L:=by rw[hab]; exact OJ
  have JK:=gl.pN
   (A:=A) (f:=f) (m:=q) (k:=k) (t:=s-t) OI HL Ln hq
  simpa[neg_sub,mul_div_cancel₀ _ (two_ne_zero' ℝ)] using JK
private lemma ua
  {G:Type*} (B C:Finset G) (É:B.Nonempty) (Ã:C.Nonempty)
  (q:ℕ) (hq:q=⌈1+log (min 1 ((#C:ℝ)/ #B))⁻¹⌉₊) :
  ((#C:ℝ)/ #B)^(-((2*q:ℕ):ℝ)⁻¹)≤exp 1:=by
 let r:ℝ:=min 1 ((#C:ℝ)/ #B)
 have tc:0<r:=by
  dsimp[r]
  exact lt_min U1 (ὗ (by exact_mod_cast Ã.card_pos) (by exact_mod_cast É.card_pos))
 have xA:r≤1:=Uv _ _
 have si:0<1+log r⁻¹:=by
  have Ck:0≤log r⁻¹:=
   Ἲ ((Uw tc).2 xA)
  linarith
 have x9:1≤q:=by
  rw[hq,Nat.one_le_ceil_iff]
  have Ck:0≤log r⁻¹:=
   Ἲ ((Uw tc).2 xA)
  dsimp[r] at Ck ⊢
  linarith
 calc
  ((#C:ℝ)/ #B)^(-((2*q:ℕ):ℝ)⁻¹)
    ≤ r^(-((2*q:ℕ):ℝ)⁻¹):=
   Real.rpow_le_rpow_of_nonpos (by positivity) inf_le_right<| neg_nonpos.2<| by positivity
  _≤r^(-(1+log r⁻¹)⁻¹):=
   Th (by positivity) xA<| TO<| inv_anti₀
    si<| (Rr _).trans<| by
     rw[←hq]
     exact_mod_cast T9 q (by norm_num:0<2)
  _≤r^(-(0+log r⁻¹)⁻¹):=by
   obtain hr | hr:r=1∨r<1:=xA.eq_or_lt
   ·simp[hr]
   have:0<log r⁻¹:=Sv<| (one_lt_inv₀ tc).2 hr
   exact Th (by positivity) xA
    (by gcongr; exact Us)
  _=r^(log r)⁻¹:=by simp[inv_neg]
  _≤exp 1:=Real.rpow_inv_log_le_exp_one
private lemma sZ
  {G:Type*} [Δ G] [Β G] [Γ G]
  [MeasurableSpace G] [Α G]
  {A:Finset G} (B C:Finset G) (u x:G) (q:ℕ) (x9:1≤q) :
  ‖(τ u ((Χ (((Χ (mu A) (((indicator B λ _↦(1:_)):G→ℂ))))) (mu C))) -
   (Χ (((Χ (mu A) ((indicator B λ _↦(1:_)))))) (mu C)):G→ℂ) x‖ ≤
    (aJ (2*q) (τ u ((Χ (mu A) (((indicator B λ _↦(1:_)):G→ℂ))))-(Χ (mu A) ((indicator B λ _↦(1:_)))))) *
     (aJ (NNReal.conjExponent (2*q)) ((@mu (ℂ) _ _) (x+ᵥ -C))):=by
 let M:ℕ:=2*q
 have z1:1<(M:ℝ≥0):=by
  norm_cast
  dsimp[M]
  omega
 have ἄ:(M:ℝ≥0).HolderConjugate _:=S2 z1
 have P7:(M:ℝ≥0∞).HolderConjugate _:=ἄ.coe_ennreal
 set F:G→ℂ:=τ u ((Χ (mu A) ((indicator B λ _↦(1:_)))))-(Χ (mu A) ((indicator B λ _↦(1:_))))
 have x7 :
   (τ u ((Χ (((Χ (mu A) ((indicator B λ _↦(1:_)))))) (mu C)))-(Χ (((Χ (mu A) ((indicator B λ _↦(1:_)))))) (mu C)):G→ℂ) x =
    ((Χ F (mu C))) x:=by simp[CA,F]
 have hsum:((Χ F (mu C))) x= ∑ y,F y*mu (x+ᵥ -C) y:=by
  rw[ᾂ]
  congr with y
  simp[neg_add_eq_sub]
 calc
  ‖(τ u ((Χ (((Χ (mu A) ((indicator B λ _↦(1:_)))))) (mu C))) -
    (Χ (((Χ (mu A) ((indicator B λ _↦(1:_)))))) (mu C)):G→ℂ) x‖
    = ‖∑ y,F y*mu (x+ᵥ -C) y‖:=by rw[x7,hsum]
  _≤ ∑ y, ‖F y*mu (x+ᵥ -C) y‖:=Rq _ _
  _=(aJ 1 (F*mu (x+ᵥ -C))):=by
   rw[ek]
   rfl
  _≤(aJ M F)*(aJ (NNReal.conjExponent M) ((@mu (ℂ) _ _) (x+ᵥ -C))):=
   yR _ _
  _=_:=by simp[F,M]
private lemma vA
  {G:Type*} [Δ G] [Β G] [Γ G]
  [MeasurableSpace G] [Α G]
  {A:Finset G} {ε:ℝ} (B C:Finset G)
  (Ã:C.Nonempty) (u x:G) (q:ℕ) (x9:1≤q)
  (C7 :
   (aJ (2*q) (τ u ((Χ (mu A) (((indicator B λ _↦(1:_)):G→ℂ))))-(Χ (mu A) ((indicator B λ _↦(1:_)))))) ≤
    ε/exp 1*(aJ (2*q) (((indicator B λ _↦(1:_)):G→ℂ)))) :
  ‖(τ u ((Χ (((Χ (mu A) ((indicator B λ _↦(1:_)))))) (mu C))) -
   (Χ (((Χ (mu A) ((indicator B λ _↦(1:_)))))) (mu C)):G→ℂ) x‖ ≤
    ε*(((#C:ℝ)/ #B)^(-((2*q:ℕ):ℝ)⁻¹)/exp 1):=by
 let M:ℕ:=2*q
 have Lu:(M:ℝ≥0)≠0:=by positivity
 have z1:1<(M:ℝ≥0):=by
  norm_cast
  dsimp[M]
  omega
 have ἄ := S2 z1
 calc
  _
    ≤ (aJ M (τ u ((Χ (mu A) (((indicator B λ _↦(1:_)):G→ℂ))))-(Χ (mu A) ((indicator B λ _↦(1:_)))))) *
      (aJ (NNReal.conjExponent M) ((@mu (ℂ) _ _) (x+ᵥ -C))):=by
     simpa[M] using sZ B C u x q x9
  _≤ε/exp 1* #B^(M:ℝ)⁻¹ *
     (aJ (NNReal.conjExponent M) ((@mu (ℂ) _ _) (x+ᵥ -C))):=by
   gcongr
   ·exact ᾧ
   have Lv :
     (aJ M (τ u ((Χ (mu A) (((indicator B λ _↦(1:_)):G→ℂ))))-(Χ (mu A) ((indicator B λ _↦(1:_)))))) ≤
      ε/exp 1*(aJ M (((indicator B λ _↦(1:_)):G→ℂ))):=by
    simpa only[M,Rm,Nat.cast_ofNat] using C7
   have F7:(aJ M (((indicator B λ _↦(1:_)):G→ℂ)))=(#B:ℝ)^(M:ℝ)⁻¹:=by
    rw[show(M:ℝ≥0∞)=((M:ℝ≥0):ℝ≥0∞) by norm_num,
     n8 Lu]
    norm_num
   rw[←F7]
   exact Lv
  _=ε*(((#C:ℝ)/ #B)^(-(M:ℝ)⁻¹)/exp 1):=by
   rw[←mul_comm_div,rB ἄ.symm.lt.le Ã.neg.vadd_finset,
    card_vadd_finset,card_neg,ἄ.symm.coe.inv_sub_one,Real.div_rpow,à]
   any_goals positivity
   push_cast
   rw[TS,TS, ←ἱ,inv_div_inv]
   all_goals positivity
  _=ε*(((#C:ℝ)/ #B)^(-((2*q:ℕ):ℝ)⁻¹)/exp 1):=by
   simp[M]
private lemma ss
  {G:Type*} [Δ G] [Β G] [Γ G]
  [MeasurableSpace G] [Α G]
  {A:Finset G} {ε:ℝ} (hε:0<ε) (B C:Finset G)
  (Ã:C.Nonempty) (u:G) (q:ℕ) (x9:1≤q)
  (ἕ:((#C:ℝ)/ #B)^(-((2*q:ℕ):ℝ)⁻¹)≤exp 1)
  (C7 :
   (aJ (2*q) (τ u ((Χ (mu A) (((indicator B λ _↦(1:_)):G→ℂ))))-(Χ (mu A) ((indicator B λ _↦(1:_)))))) ≤
    ε/exp 1*(aJ (2*q) (((indicator B λ _↦(1:_)):G→ℂ)))) :
  (aJ (∞) ((τ u ((Χ (((Χ (mu A) ((indicator B λ _↦(1:_)))))) (mu C))) -
   (Χ (((Χ (mu A) ((indicator B λ _↦(1:_)))))) (mu C)):G→ℂ)))≤ε:=by
 rw[dw]
 refine ciSup_le λ x↦(vA B C Ã u x q x9 C7).trans ?_
 refine Sq hε.le ((ᾜ (by positivity)).2 ?_)
 exact ἕ
lemma q7
  {G:Type*} [Δ G] [Β G] [Γ G]
  [MeasurableSpace G] [Α G]
  {A S:Finset G} (ξ:A.Nonempty) (Ø:S.Nonempty)
  (ε:ℝ) (hε:0<ε) (B C:Finset G) (É:B.Nonempty) (Ã:C.Nonempty) :
  let q:=⌈1+log (min 1 ((#C:ℝ)/ #B))⁻¹⌉₊
  let k:=ᾨ q (ε/exp 1)
  ∃ T:Finset G,
   T⊆S∧T.Nonempty ∧
   (((#A:ℝ)^k/2* #S)/(#(A+S):ℝ)^k≤ #T) ∧
   ∀ s∈T, ∀ t∈T,
    (aJ (∞) ((τ (t-s) ((Χ (((Χ (mu A) ((indicator B λ _↦(1:_)))))) (mu C))) -
     (Χ (((Χ (mu A) ((indicator B λ _↦(1:_)))))) (mu C)):G→ℂ)))≤ε:=by
 let r:ℝ:=min 1 ((#C:ℝ)/ #B)
 let m:ℝ:=1+log r⁻¹
 have tc:0<r:=by
  dsimp[r]
  exact lt_min U1 (ὗ (by exact_mod_cast Ã.card_pos) (by exact_mod_cast É.card_pos))
 have xA:r≤1:=Uv _ _
 have PE:0< m:=by
  have:0≤log r⁻¹:=Ἲ ((Uw tc).2 xA)
  positivity
 have Hf:1≤⌈m⌉₊:=Nat.one_le_iff_ne_zero.2 (by positivity)
 obtain ⟨T,Ew,ῢ,ch,ἓ⟩:=
  vz ξ Ø ⌈m⌉₊ Hf (ε/exp 1) (by positivity)
   ((indicator B λ _↦(1:_)):G→ℂ)
 refine ⟨T,Ew,ῢ, ?_, ?_⟩
 ·simpa[r,m] using ch
 ·intro s hs t ht
  apply ss hε B C Ã (t-s) ⌈m⌉₊ Hf
   (ua B C É Ã ⌈m⌉₊ (by simp[r,m]))
  simpa[r,m] using ἓ s hs t ht
lemma mX
  {G:Type*} [Δ G] [Β G] [Γ G]
  [MeasurableSpace G] [Α G]
  {A S:Finset G} (ξ:A.Nonempty) (Ø:S.Nonempty)
  (ε:ℝ) (hε:0<ε) (m:ℕ) (hm:m≠0)
  (B C:Finset G) (É:B.Nonempty) (Ã:C.Nonempty) :
  let q:=⌈1+log (min 1 ((#C:ℝ)/ #B))⁻¹⌉₊
  let k:=ᾨ q ((ε/m)/exp 1)
  ∃ (T:Finset G) (z:G),
   T⊆S∧z∈T ∧
   (-z+ᵥ T).Nonempty∧(-z+ᵥ T)⊆S-S ∧
   (((#A:ℝ)^k/2* #S)/(#(A+S):ℝ)^k≤ #T) ∧
   (aJ (∞) (((Χ ((ἶ (mu (-z+ᵥ T)) m)) (((Χ (((Χ (mu A) ((indicator B λ _↦(1:_)))))) (mu C))))) -
    (Χ (((Χ (mu A) ((indicator B λ _↦(1:_)))))) (mu C)):G→ℂ)))≤ε:=by
 have G7:(0:ℝ)< m:=by exact_mod_cast(Nat.pos_iff_ne_zero.2 hm)
 have Cc := ὗ hε G7
 obtain ⟨T,Ew,ῢ,ch,jl⟩:=
  q7 ξ Ø (ε/(m:ℝ)) Cc B C É Ã
 obtain ⟨z,hz⟩:=ῢ
 let X := -z+ᵥ T
 have ᾉ:X.Nonempty:=by
  refine ⟨0, ?_⟩
  change 0∈ -z+ᵥ T
  rw[mem_vadd_finset]
  exact ⟨z,hz,by simp⟩
 have F8: ∀ x∈X,
   (aJ (∞) ((τ x ((Χ (((Χ (mu A) ((indicator B λ _↦(1:_)))))) (mu C))) -
    (Χ (((Χ (mu A) ((indicator B λ _↦(1:_)))))) (mu C)):G→ℂ)))≤ε/(m:ℝ):=by
  intro x hx
  change x∈ -z+ᵥ T at hx
  rw[mem_vadd_finset] at hx
  obtain ⟨t,ht,rfl⟩:=hx
  have hp:=jl z hz t ht
  simpa[Ἱ,ῒ] using hp
 have Lw: -z+ᵥ T⊆S-S:=by
  intro x hx
  rw[mem_vadd_finset] at hx
  obtain ⟨t,ht,rfl⟩:=hx
  simpa[Ἱ,ῒ] using sub_mem_sub (Ew ht) (Ew hz)
 set F:G→ℂ:=(Χ (((Χ (mu A) ((indicator B λ _↦(1:_)))))) (mu C))
 refine ⟨T,z,Ew,hz, ?_,Lw, ?_, ?_⟩
 ·simpa[X] using ᾉ
 ·simpa using ch
 ·change(aJ (∞) ((Χ ((ἶ (mu X) m)) F)-F))≤ε
  calc
   _
     = (aJ (∞) (𝔼 a∈(piFinset λ _:Fin m↦X),(τ (∑ i,a i) F-F))):=by
      rw[vJ,expect_sub_distrib,expect_const ᾉ.piFinset_const]
   _≤𝔼 a∈(piFinset λ _:Fin m↦X),(aJ (∞) (τ (∑ i,a i) F-F)):=
    wU le_top
   _≤𝔼 _a∈(piFinset λ _:Fin m↦X),ε:=by
    refine expect_le_expect λ a ha↦ ?_
    calc
     _
       ≤ ∑ i,(aJ (∞) (τ (a i) F-F)):=
        pM le_top _ _ _
     _≤ ∑ _i,ε/(m:ℝ):=by
      gcongr
      simpa[F] using F8 (a _) (Fintype.mem_piFinset.1 ha _)
     _=ε:=by
      simp only[sum_const,card_fin,ᾚ]
      rw[mul_div_cancel₀]
      exact_mod_cast hm
   _=ε:=by rw[expect_const ᾉ.piFinset_const]
end ay
end
section
open AddChar Finset
open scoped BigOperators NNReal
namespace ay
noncomputable section
variable {G:Type*} [Γ G] [Δ G] [Β G]
private lemma ub (A:Finset G) (psi:Ε G ℂ) :
  (∑ x:G,(af A x:ℂ)*psi x) =
   ((A.card:ℂ)⁻¹)*c5.c6 A psi:=by
 classical
 rw[c5.c6,á]
 calc
  _ =
    ∑ x:G,if x∈A then ((A.card:ℂ)⁻¹)*psi x else 0:=by
   apply Ò rfl
   intro x _
   by_cases hx:x∈A<;>simp[af,hx]
  _= ∑ x∈A,((A.card:ℂ)⁻¹)*psi x:=by
   rw[←ᾛ]
   have Ἠ :
     (Finset.univ.filter λ x:G↦x∈A)=A:=by
    ext x
    simp
   rw[Ἠ]
private lemma pU (A:Finset G)
  (psi:Ε G ℂ) (t:G) :
  (1-psi t)*(∑ x:G,(af A x:ℂ)*psi x) =
   ∑ x:G,
    ((af A x-af A (x-t):ℝ):ℂ) *
     psi x:=by
 classical
 have kE :
   (∑ x:G,(af A (x-t):ℂ)*psi x) =
    psi t* ∑ x:G,(af A x:ℂ)*psi x:=by
  rw[←(Equiv.addRight t).sum_comp]
  ·change
    (∑ x:G,(af A ((x+t)-t):ℂ)*psi (x+t)) =
     psi t* ∑ x:G,(af A x:ℂ)*psi x
   simp_rw[add_sub_cancel_right,map_add_eq_mul]
   rw[á]
   apply Ò rfl
   intro x _
   ring
  ·simp
 push_cast
 simp_rw[sub_mul]
 rw[QJ,kE]
 ring
omit [Β G] in
lemma l8
  {C:aj G} (Ô:C.a1) {Ο:ℝ} (ò:0<Ο)
  {sigma:ℝ≥0}
  (Ὣ:sigma≤1/(100*(max C.Ι 1:ℕ):ℝ≥0))
  {psi:Ε G ℂ} (Ê:psi∈c5.cj C.Η Ο)
  {t:G} (ht:t∈(C.ai sigma).Η) :
  ‖1-psi t‖ ≤
   200*((max C.Ι 1:ℕ):ℝ)*(sigma:ℝ)/Ο:=by
 classical
 let F :=  ∑ x:G,(af C.Η x:ℂ)*psi x
 have ch:(0:ℝ)<C.Η.card:=by
  exact_mod_cast C.aE.card_pos
 have JL: ‖F‖ = ‖c5.c6 C.Η psi‖ /C.Η.card:=by
  dsimp[F]
  rw[ub,ἑ]
  simp[Ri]
 have Ὤ:Ο≤ ‖F‖:=by
  rw[JL,ἇ ch]
  exact c5.gm.mp Ê
 have Ᾰ :
   ‖1-psi t‖ * ‖F‖ ≤
    ∑ x:G,
     |af C.Η (x-t) -
      af C.Η x|:=by
  rw[←ἑ,pU C.Η psi t]
  calc
   _
                                       ≤
     ∑ x:G,
      ‖((af C.Η x -
        af C.Η (x-t):ℝ):ℂ)*psi x‖:=
    Rq _ _
   _= ∑ x:G,
     |af C.Η (x-t) -
      af C.Η x|:=by
    apply Ò rfl
    intro x _
    rw[ἑ]
    rw[Rf,ᾮ,Su]
    simp
 have AI:=
  aj.cN
   Ô Ὣ ht
 have hmul :
   ‖1-psi t‖ *Ο ≤
    200*((max C.Ι 1:ℕ):ℝ)*(sigma:ℝ):=by
  calc
   _ ≤ ‖1-psi t‖ * ‖F‖:=
    Å Ὤ (Re _)
   _≤ ∑ x:G,
     |af C.Η (x-t) -
      af C.Η x|:=Ᾰ
   _≤200*((max C.Ι 1:ℕ):ℝ)*(sigma:ℝ):=AI
 exact(ἇ ò).2 hmul
omit [Β G] in
lemma kl
  {C:aj G} (Ô:C.a1) {sigma:ℝ≥0}
  (Ὣ:sigma≤1/(100*(max C.Ι 1:ℕ):ℝ≥0))
  {psi:Ε G ℂ} (Ê:psi∈c5.cj C.Η (1/2))
  {t:G} (ht:t∈(C.ai sigma).Η) :
  ‖1-psi t‖ ≤400*((max C.Ι 1:ℕ):ℝ)*(sigma:ℝ):=by
 classical
 have h:=l8 Ô (Ο:=(1/2:ℝ))
  (by norm_num) Ὣ Ê ht
 convert h using 1
 ring
end
end ay
end
section
noncomputable section
open Finset Function Real
open scoped BigOperators ComplexConjugate NNReal
namespace ay.aI
variable {G:Type*} [Δ G] [Γ G]
def eV (mu:G→ℝ) (K:ℝ)
  (Κ:Finset (Ε G ℂ)):Prop:=
 ∀ u:Ε G ℂ→ℂ,
  (∀ psi∈Κ, ‖u psi‖ ≤1) →
   ∑ x:G,mu x *
    ∏ psi∈Κ,(1+(u psi*psi x).re)≤exp K
def fP (mu f:G→ℝ) (Ο:ℝ) :
  Finset (Ε G ℂ):=
  Finset.univ.filter λ psi ↦
  Ο*(∑ x:G,f x*mu x) ≤
   ‖∑ x:G,(f x*mu x:ℝ)*psi x‖
@[simp] lemma lQ {mu f:G→ℝ} {Ο:ℝ}
  {psi:Ε G ℂ} :
  psi∈fP mu f Ο ↔
   Ο*(∑ x:G,f x*mu x) ≤
    ‖∑ x:G,(f x*mu x:ℝ)*psi x‖:=by
 simp[fP]
end ay.aI
end
end
section
noncomputable section
open Finset Real
open scoped BigOperators ComplexConjugate
namespace ay.aI
variable {G:Type*} [Δ G] [Γ G]
def ὑ (S Κ:Finset (Ε G ℂ)):Prop:=
 ∀ t u:Finset (Ε G ℂ),t⊆Κ→u⊆Κ →
  Disjoint t u→(t∪u).Nonempty →
   (∑ psi∈t,psi)- ∑ psi∈u,psi∉S
omit [Δ G] in
lemma s0 (S:Finset (Ε G ℂ)) :
  ὑ S ∅:=by
 intro t u ht hu ῠ ᾱ
 simp only[Finset.subset_empty] at ht hu
 subst t
 subst u
 simp at ᾱ
omit [Δ G] in
lemma ὑ.mono {S:Finset (Ε G ℂ)}
  {Κ Gamma:Finset (Ε G ℂ)}
  (h:ὑ S Κ) (Ὂ:Gamma⊆Κ) :
  ὑ S Gamma:=by
 intro t u ht hu
 exact h t u (ht.trans Ὂ) (hu.trans Ὂ)
omit [Δ G] in
lemma nT [Finite G]
  (S T:Finset (Ε G ℂ))
  (hzero:0∈S)
  (Ø: ∀ s,s∈S→ -s∈S) :
  ∃ Κ:Finset (Ε G ℂ),
   Κ⊆T∧ὑ S Κ ∧
    ∀ psi∈T, ∃ z∈Κ.addSpan, ∃ s∈S,psi=z+s:=by
 let:=Fintype.ofFinite G
 classical
 let candidates:=T.powerset.filter (ὑ S)
 have BL:candidates.Nonempty:=by
  refine ⟨∅, ?_⟩
  simp[candidates,s0]
 obtain ⟨Κ,C8,C9⟩:=candidates.exists_maximal BL
 have ó:=Finset.mem_filter.mp C8
 refine ⟨Κ,Finset.mem_powerset.mp ó.1,ó.2, ?_⟩
 intro psi Lx
 by_cases zm:psi∈Κ
 ·exact ⟨psi,Finset.subset_addSpan zm,0,hzero,by simp⟩
 ·have y3 :=
   Finset.insert_subset Lx (Finset.mem_powerset.mp ó.1)
  have hnot: ¬ ὑ S (insert psi Κ):=by
   intro Ng
   have BM:insert psi Κ∈candidates:=by
    simp[candidates,y3,Ng]
   have Ὂ:=C9 BM (Finset.subset_insert psi Κ)
   exact zm (Ὂ (Finset.mem_insert_self psi Κ))
  rw[ὑ] at hnot
  push Not at hnot
  obtain ⟨t,u,ht,hu,ῠ,ᾱ,Da⟩:=hnot
  have Cl:psi∈t∪u:=by
   by_contra Ê
   have rX:t⊆Κ:=by
    intro a ha
    have ἠ:=ht ha
    rw[Rp] at ἠ
    exact ἠ.resolve_left (λ h↦Ê (h▸Um u ha))
   have y4:u⊆Κ:=by
    intro a ha
    have ἠ:=hu ha
    rw[Rp] at ἠ
    exact ἠ.resolve_left (λ h↦Ê (h▸Ua t ha))
   exact ó.2 t u rX y4 ῠ ᾱ Da
  rw[Finset.mem_union] at Cl
  rcases Cl with Ex | Ey
  ·have Db:psi∉u:=λ h↦Finset.disjoint_left.mp ῠ Ex h
   have HM:t.erase psi⊆Κ:=by
    intro a ha
    have ἠ:=ht (Sm ha)
    rw[Rp] at ἠ
    exact ἠ.resolve_left (Sw ha)
   have y4:u⊆Κ:=by
    intro a ha
    have ἠ:=hu ha
    rw[Rp] at ἠ
    exact ἠ.resolve_left (λ h↦Db (h▸ha))
   let z:=(∑ a∈u,a)- ∑ a∈t.erase psi,a
   have hz :=
          Tp y4 HM
   refine ⟨z,hz,(∑ a∈t,a)- ∑ a∈u,a,Da, ?_⟩
   dsimp[z]
   rw[←SO _ _ Ex]
   abel
  ·have Dc:psi∉t:=λ h↦Finset.disjoint_left.mp ῠ h Ey
   have HN:u.erase psi⊆Κ:=by
    intro a ha
    have ἠ:=hu (Sm ha)
    rw[Rp] at ἠ
    exact ἠ.resolve_left (Sw ha)
   have rX:t⊆Κ:=by
    intro a ha
    have ἠ:=ht ha
    rw[Rp] at ἠ
    exact ἠ.resolve_left (λ h↦Dc (h▸ha))
   let z:=(∑ a∈t,a)- ∑ a∈u.erase psi,a
   have hz :=
          Tp rX HN
   let s:=-((∑ a∈t,a)- ∑ a∈u,a)
   have hs := Ø _ Da
   refine ⟨z,hz,s,hs, ?_⟩
   dsimp[z,s]
   rw[←SO _ _ Ey]
   abel
private def fq (t u:Finset (Ε G ℂ)):Ε G ℂ:=
 (∑ psi∈u,psi)- ∑ psi∈t \ u,psi
private def ῼ (v:Ε G ℂ→ℂ)
  (t u:Finset (Ε G ℂ)):ℂ:=
 ((∏ psi∈u,v psi)* ∏ psi∈t \ u,conj (v psi)) /
  (2:ℂ)^t.card
omit [Δ G] in
private lemma oi [Finite G]
  (Κ:Finset (Ε G ℂ)) (v:Ε G ℂ→ℂ) (x:G) :
  ∏ psi∈Κ,((1+(v psi*psi x).re:ℝ):ℂ) =
   ∑ t∈Κ.powerset, ∑ u∈t.powerset,
    ῼ v t u*fq t u x:=by
 let:=Fintype.ofFinite G
 calc
  ∏ psi∈Κ,((1+(v psi*psi x).re:ℝ):ℂ) =
    ∏ psi∈Κ,
     (((v psi*psi x)+conj (v psi*psi x))/2+1):=by
   apply Finset.prod_congr rfl
   intro psi Ê
   rw[ῒ, ←Complex.re_eq_add_conj]
   push_cast
   rfl
  _= ∑ t∈Κ.powerset,
    ∏ psi∈t,((v psi*psi x)+conj (v psi*psi x))/2:=by
   rw[Finset.prod_add]
   simp
  _= ∑ t∈Κ.powerset, ∑ u∈t.powerset,
    ῼ v t u*fq t u x:=by
   apply Ò rfl
   intro t ht
   rw[Finset.prod_div_distrib]
   rw[Finset.prod_add]
   rw[TP]
   apply Ò rfl
   intro u hu
   rw[ῼ,fq]
   simp only[AddChar.sum_apply,RO,
    TV]
   simp only[Finset.prod_const]
   simp_rw[ᾪ,TW]
   rw[map_prod]
   ring
private lemma nU
  (w:G→ℝ) (Κ:Finset (Ε G ℂ))
  (v:Ε G ℂ→ℂ) :
  ((∑ x:G,w x *
    ∏ psi∈Κ,(1+(v psi*psi x).re)):ℂ) =
   ∑ t∈Κ.powerset, ∑ u∈t.powerset,
    ῼ v t u *
     ay.ἅ w (fq t u):=by
 simp_rw[Complex.ofReal_prod]
 simp_rw[oi]
 simp_rw[á]
 rw[ὶ]
 apply Ò rfl
 intro t ht
 rw[ὶ]
 apply Ò rfl
 intro u hu
 rw[ay.ἅ,á]
 apply Ò rfl
 intro x hx
 ring
omit [Δ G] in
private lemma s3
  {S Κ t u:Finset (Ε G ℂ)}
  (ó:ὑ S Κ)
  (ht:t⊆Κ) (JM:t.Nonempty) (hu:u⊆t) :
  fq t u∉S:=by
 apply ó u (t \ u)
 ·exact hu.trans ht
 ·exact Finset.sdiff_subset.trans ht
 ·rw[Finset.disjoint_left]
  intro psi Ly JN
  exact(Finset.mem_sdiff.mp JN).2 Ly
 ·simpa[Finset.union_sdiff_of_subset hu] using JM
omit [Δ G] in
private lemma rF
  {v:Ε G ℂ→ℂ} {t u:Finset (Ε G ℂ)}
  (hu:u⊆t) (hv: ∀ psi∈t, ‖v psi‖ ≤1) :
  ‖ῼ v t u‖ ≤((2:ℝ)^t.card)⁻¹:=by
 have OM: ‖∏ psi∈u,v psi‖ ≤1:=by
  rw[norm_prod]
  exact UO (λ psi Ê↦Re _)
   (λ psi Ê↦hv psi (hu Ê))
 have Nh: ‖∏ psi∈t \ u,conj (v psi)‖ ≤1:=by
  rw[norm_prod]
  exact UO (λ psi Ê↦Re _)
   (λ psi Ê↦by
    rw[RCLike.norm_conj]
    exact hv psi (Finset.sdiff_subset Ê))
 have ἴ :
   ‖(∏ psi∈u,v psi)* ∏ psi∈t \ u,conj (v psi)‖ ≤1:=by
  rw[ἑ]
  calc
   _≤1*1:=ὤ OM Nh (Re _) (by norm_num)
   _=1:=by norm_num
 rw[ῼ,norm_div]
 calc
  _≤1/ ‖(2:ℂ)^t.card‖:=
   ῖ ἴ (Re _)
  _=((2:ℝ)^t.card)⁻¹:=by
   rw[norm_pow]
   norm_num
lemma ὑ.oj
  {S Κ:Finset (Ε G ℂ)} {w:G→ℝ} {q:ℝ}
  (ó:ὑ S Κ)
  (_hw0: ∀ x,0≤w x) (AJ: ∑ x:G,w x=1)
  (Ῑ:0≤q)
  (hq: ∀ psi,psi∉S→ ‖ay.ἅ w psi‖ ≤q)
  (v:Ε G ℂ→ℂ) (hv: ∀ psi∈Κ, ‖v psi‖ ≤1) :
  ∑ x:G,w x* ∏ psi∈Κ,(1+(v psi*psi x).re) ≤
   1+q*(2:ℝ)^Κ.card:=by
 classical
 let F:Finset (Ε G ℂ)→ℂ:=λ t ↦
  ∑ u∈t.powerset,ῼ v t u *
   ay.ἅ w (fq t u)
 let E :=  ∑ t∈Κ.powerset.erase ∅,F t
 have su:(∅:Finset (Ε G ℂ))∈Κ.powerset:=by simp
 have Ni: ∑ x:G,(w x:ℂ)=1:=by exact_mod_cast AJ
 have HO:F ∅=1:=by
  simp[F,ῼ,fq,ay.ἅ,Ni]
 have Ὁ :
   ((∑ x:G,w x *
     ∏ psi∈Κ,(1+(v psi*psi x).re)):ℂ)=1+E:=by
  rw[nU]
  rw[←SO _ _ su]
  simp only[HO,E,F]
  ring
 have ῳ (t:Finset (Ε G ℂ))
   (ht:t∈Κ.powerset.erase ∅): ‖F t‖ ≤q:=by
  have rX := Finset.mem_powerset.mp (Sm ht)
  have JM := Finset.nonempty_iff_ne_empty.mpr (Sw ht)
  calc
   _ ≤ ∑ u∈t.powerset,
     ‖ῼ v t u *
      ay.ἅ w (fq t u)‖:=by
    exact Rq _ _
   _≤ ∑ _u∈t.powerset,((2:ℝ)^t.card)⁻¹ *q:=by
    apply ᾯ
    intro u hu
    rw[ἑ]
    apply ὤ
    ·exact rF (Finset.mem_powerset.mp hu)
      (λ psi Ê↦hv psi (rX Ê))
    ·exact hq _ (s3 ó rX JM
      (Finset.mem_powerset.mp hu))
    ·exact Re _
    ·exact inv_nonneg.mpr (ἥ (by norm_num) _)
   _=q:=by
    rw[Tq,Ux]
    simp[ᾚ]
 have JO: ‖E‖ ≤q*(2:ℝ)^Κ.card:=by
  calc
   _ ≤ ∑ t∈Κ.powerset.erase ∅, ‖F t‖:=Rq _ _
   _≤ ∑ _t∈Κ.powerset.erase ∅,q:=
          ᾯ λ t ht↦ῳ t ht
   _≤ ∑ _t∈Κ.powerset,q:=
          Ry (Finset.erase_subset _ _)
     (λ _ _ _↦Ῑ)
   _=q*(2:ℝ)^Κ.card:=by
    simp[Ux]
    ring
 let R :=
  ∑ x:G,w x* ∏ psi∈Κ,(1+(v psi*psi x).re)
 have Lz:(R:ℂ)=1+E:=by
  calc
   _ = ∑ x:G,(w x:ℂ) *
     (↑(∏ psi∈Κ,(1+(v psi*psi x).re)):ℂ):=by
    dsimp[R]
    push_cast
    rfl
   _=1+E:=Ὁ
 have JP:R=1+E.re:=by
  have:=è Complex.re Lz
  simpa using this
 change R≤1+q*(2:ℝ)^Κ.card
 calc
  R=1+E.re:=JP
  _≤1+ ‖E‖:=Sr (le_refl 1) (Complex.re_le_norm E)
  _≤1+q*(2:ℝ)^Κ.card:=Sr (le_refl 1) JO
lemma ὑ.uc
  {S Κ:Finset (Ε G ℂ)} {w:G→ℝ} {q:ℝ} {k:ℕ}
  (ó:ὑ S Κ)
  (vq: ∀ x,0≤w x) (AJ: ∑ x:G,w x=1)
  (Ῑ:0≤q)
  (hq: ∀ psi,psi∉S→ ‖ay.ἅ w psi‖ ≤q)
  (ch:Κ.card≤k) (ON:q*(2:ℝ)^k≤1) :
  eV w 1 Κ:=by
 intro v hv
 have HP:2^Κ.card≤2^k:=
  QR (by norm_num) ch
 have hpow:(2:ℝ)^Κ.card≤(2:ℝ)^k:=by
  exact_mod_cast HP
 have uX:q*(2:ℝ)^Κ.card≤1:=
  (Å hpow Ῑ).trans ON
 calc
  ∑ x:G,w x* ∏ psi∈Κ,(1+(v psi*psi x).re) ≤
    1+q*(2:ℝ)^Κ.card:=
   ó.oj vq AJ Ῑ hq v hv
  _≤2:=by linarith
  _≤exp 1:=Real.exp_one_gt_two.le
lemma ὑ.k4
  {S Κ:Finset (Ε G ℂ)} {w:G→ℝ} {q:ℝ} {k:ℕ}
  (ó:ὑ S Κ)
  (vq: ∀ x,0≤w x) (AJ: ∑ x:G,w x=1)
  (Ῑ:0≤q)
  (hq: ∀ psi,psi∉S→ ‖ay.ἅ w psi‖ ≤q)
  (ch:Κ.card≤k) (Dd:q≤(1/4:ℝ)^k) :
  eV w 1 Κ:=by
 apply ó.uc vq AJ Ῑ hq ch
 calc
  _ ≤(1/4:ℝ)^k*(2:ℝ)^k:=
   ἂ Dd (ἥ (by norm_num) _)
  _=(1/2:ℝ)^k:=by rw[←Ἀ]; congr 1; norm_num
  _≤1:=Uy (by norm_num) (by norm_num)
lemma nm (A:Finset G) :
  (0:Ε G ℂ)∈ay.c5.cj A (1/2:ℝ):=by
 rw[ay.c5.gm]
 simp[ay.c5.c6]
 have ch:(0:ℝ)≤A.card:=by exact_mod_cast Nat.zero_le A.card
 nlinarith
lemma ku {A:Finset G} {Ο:ℝ}
  {psi:Ε G ℂ}
  (Ê:psi∈ay.c5.cj A Ο) :
  -psi∈ay.c5.cj A Ο:=by
 rw[ay.c5.gm] at Ê ⊢
 have hsum:ay.c5.c6 A (-psi) =
   conj (ay.c5.c6 A psi):=by
  unfold ay.c5.c6
  rw[ᾘ]
  apply Ò rfl
  intro x hx
  rw[U2,TV]
 rw[hsum,RCLike.norm_conj]
 exact Ê
end ay.aI
end
end
section
open Finset
open scoped BigOperators
namespace ay.jO
variable {G:Type*} [Δ G] [Γ G] [Β G]
omit [Γ G] in
lemma f2
  {B X:Finset G} (ud:X⊆B) {w:G→ℝ} {c:ℝ}
  (hw: ∀ x∈B,w x=c) :
  ∑ x:G,ý X x*w x=c*X.card:=by
 classical
 calc
  _ = ∑ x∈X,c:=by
   rw[←Ro (s₁:=X) (s₂:=Finset.univ)]
   ·apply Ò rfl
    intro x hx
    simp[ý,hx,hw x (ud hx)]
   ·simp
   ·intro x MH He
    simp[ý,He]
  _=c*X.card:=by simp[ä]
lemma jg
  {B X:Finset G} (ud:X⊆B) {w:G→ℝ} {c:ℝ}
  (hw: ∀ x∈B,w x=c) (psi:Ε G ℂ) :
  ∑ x:G,((ý X x*w x:ℝ):ℂ)*psi x =
   (c:ℂ)*c5.c6 X psi:=by
 classical
 calc
  _ =
    ∑ x∈X,(c:ℂ)*psi x:=by
   rw[←Ro (s₁:=X) (s₂:=Finset.univ)]
   ·apply Ò rfl
    intro x hx
    simp[ý,hx,hw x (ud hx)]
   ·simp
   ·intro x MH He
    simp[ý,He]
  _=(c:ℂ)*c5.c6 X psi:=by
   rw[c5.c6,á]
lemma km
  {B X:Finset G} (ud:X⊆B) {w:G→ℝ} {c:ℝ}
  (hw: ∀ x∈B,w x=c) (hc:0<c)
  (Ο:ℝ) (psi:Ε G ℂ) :
  psi∈aI.fP w (ý X) Ο ↔
   psi∈c5.cj X Ο:=by
 classical
 rw[aI.lQ,c5.gm]
 rw[f2 ud hw]
 rw[jg ud hw]
 rw[ἑ,Rf,ᾮ,RT hc]
 constructor
 ·intro h
  have hh:c*(Ο*(X.card:ℝ)) ≤
    c* ‖c5.c6 X psi‖:=by
   calc
    _ =Ο*(c*(X.card:ℝ)):=by ring
    _≤c* ‖c5.c6 X psi‖:=h
  nlinarith
 ·intro h
  calc
   _ =c*(Ο*(X.card:ℝ)):=by ring
   _≤c* ‖c5.c6 X psi‖:=
    Å h hc.le
end ay.jO
end
section
noncomputable section
open Finset Function Real
open scoped BigOperators ComplexConjugate NNReal
namespace ay.aI
variable {G:Type*} [Δ G] [Γ G]
omit [Γ G] in
lemma j6
  (w:G→ℝ) (hw: ∀ x,0≤w x) (AK: ∑ x:G,w x=1)
  (f:G→ℝ) :
  exp (∑ x:G,w x*f x)≤ ∑ x:G,w x*exp (f x):=by
 have h:=convexOn_exp.map_sum_le (t:=(Finset.univ:Finset G))
  (p:=f) (λ x _↦hw x) (by simpa using AK)
  (λ x _↦Set.mem_univ (f x))
 simpa using h
lemma s4
  (mu:G→ℝ) (K:ℝ) (Κ:Finset (Ε G ℂ))
  (AL: ∀ x,0≤ mu x)
  (ó:eV mu K Κ)
  (c:Ε G ℂ→ℂ) :
  ∑ x:G,mu x*exp ((∑ psi∈Κ,c psi*psi x).re) ≤
   exp (K+(∑ psi∈Κ, ‖c psi‖ ^2)/2):=by
 have Ὁ (z:ℂ) :
   exp z.re≤cosh ‖z‖ +(z/ ‖z‖).re*sinh ‖z‖:=by
  calc
   _=exp ((z/ ‖z‖).re* ‖z‖):=by
    obtain rfl | hz:=Tf z 0<;>simp[*]
   _≤_:=exp_mul_le_cosh_add_mul_sinh
    (by simpa using z.abs_re_div_norm_le_one) _
 choose u hu OO using λ psi↦Complex.exists_norm_mul_eq_self (c psi)
 have Jw (psi:Ε G ℂ):u psi≠0:=λ h↦by
  simpa[h] using hu psi
 have Ὄ (x:G) :
   exp ((∑ psi∈Κ,c psi*psi x).re) ≤
    ∏ psi∈Κ,
     (cosh ‖c psi‖ +(u psi*sinh ‖c psi‖ *psi x).re):=by
  calc
   exp ((∑ psi∈Κ,c psi*psi x).re) =
     ∏ psi∈Κ,exp ((c psi*psi x).re):=by
      simp_rw[←exp_sum, ←Complex.re_sum]
   _≤ ∏ psi∈Κ,
     (cosh ‖c psi*psi x‖ +
      ((c psi*psi x)/ ‖c psi*psi x‖).re *
       sinh ‖c psi*psi x‖):=by
    gcongr with psi Ê
    exact Ὁ _
   _= ∏ psi∈Κ,
     (cosh ‖c psi‖ +
      (u psi*(c psi*psi x)/(u psi* ↑‖c psi‖)).re *
       sinh ‖c psi‖):=by
    apply prod_congr rfl
    intro psi Ê
    rw[ἑ,Q0,Ἣ,
     mul_div_mul_left _ _ (Jw psi)]
   _= ∏ psi∈Κ,
     (cosh ‖c psi‖ +(u psi*sinh ‖c psi‖ *psi x).re):=by
    apply prod_congr rfl
    intro psi Ê
    obtain hc | hc:=Tf (c psi) 0
    ·simp[hc]
    simp only[OO,Ῐ (u psi),SH _ hc,
     ←Complex.re_mul_ofReal,ᾭ]
 let q:Ε G ℂ→ℝ:=λ psi↦sinh ‖c psi‖ /cosh ‖c psi‖
 let v:Ε G ℂ→ℂ:=λ psi↦(q psi:ℂ)*u psi
 have oc (x:G) :
   (∏ psi∈Κ,
     (cosh ‖c psi‖ +(u psi*sinh ‖c psi‖ *psi x).re)) =
    (∏ psi∈Κ,cosh ‖c psi‖) *
     (∏ psi∈Κ,
      (1+(v psi*psi x).re)):=by
  rw[←TW]
  apply prod_congr rfl
  intro psi Ê
  have PF:cosh ‖c psi‖ ≠0:=Uq (cosh_pos _)
  have F9 :
    (u psi*(sinh ‖c psi‖ :ℂ)*psi x).re =
     sinh ‖c psi‖ *(u psi*psi x).re:=by
   rw[show u psi*(sinh ‖c psi‖ :ℂ)*psi x =
     (sinh ‖c psi‖ :ℂ)*(u psi*psi x) by ring]
   exact Un _ _
  have LA:(v psi*psi x).re=q psi*(u psi*psi x).re:=by
   rw[show v psi*psi x=(q psi:ℂ)*(u psi*psi x) by
    simp[v]; ring]
   exact Un _ _
  rw[F9,LA]
  dsimp[q]
  field_simp
 calc
  ∑ x:G,mu x*exp ((∑ psi∈Κ,c psi*psi x).re) ≤
    ∑ x:G,mu x* ∏ psi∈Κ,
     (cosh ‖c psi‖ +(u psi*sinh ‖c psi‖ *psi x).re):=by
   apply sum_le_sum
   intro x hx
   exact Å (Ὄ x) (AL x)
  _=(∏ psi∈Κ,cosh ‖c psi‖) *
    (∑ x:G,mu x *
     ∏ psi∈Κ,
      (1+(v psi*psi x).re)):=by
   rw[á]
   apply sum_congr rfl
   intro x hx
   rw[oc]
   ring
  _≤(∏ psi∈Κ,cosh ‖c psi‖)*exp K:=by
   gcongr
   apply ó v
   intro psi Ê
   have hq: |q psi| ≤1:=by
    simpa[q,Real.tanh_eq_sinh_div_cosh] using(Real.abs_tanh_lt_one ‖c psi‖).le
   simpa[v,ἑ,hu psi,Rf,ᾮ] using hq
  _≤exp ((∑ psi∈Κ, ‖c psi‖ ^2)/2)*exp K:=by
   apply ἂ _ (exp_pos _).le
   calc
    ∏ psi∈Κ,cosh ‖c psi‖ ≤
      ∏ psi∈Κ,exp (‖c psi‖ ^2/2):=by
     gcongr with psi Ê
     exact cosh_le_exp_half_sq _
    _=exp ((∑ psi∈Κ, ‖c psi‖ ^2)/2):=by
     simp_rw[←exp_sum, ←sum_div]
  _=exp (K+(∑ psi∈Κ, ‖c psi‖ ^2)/2):=by
   rw[←exp_add]
   congr 1
   ring
lemma iQ
  (mu f:G→ℝ) (K Ο:ℝ) (Κ:Finset (Ε G ℂ))
  (AL: ∀ x,0≤ mu x) (OP: ∀ x,0≤f x)
  (Jc: ∀ x,f x≤1)
  (ò:0<Ο)
  (ó:eV mu K Κ)
  (Ὂ:Κ⊆fP mu f Ο)
  (ft:0< ∑ x:G,f x*mu x) :
  (Κ.card:ℝ) ≤
   2*(K+log ((∑ x:G,f x*mu x)⁻¹))/Ο^2:=by
 let a :=  ∑ x:G,f x*mu x
 have ha:0<a:=by simpa[a] using ft
 let spec:Ε G ℂ→ℂ:=λ psi ↦
  ∑ x:G,(f x*mu x:ℝ)*psi x
 choose u hu JQ using λ psi:Ε G ℂ ↦
  Complex.exists_norm_eq_mul_self (spec psi)
 let c:Ε G ℂ→ℂ:=λ psi↦(Ο:ℂ)*u psi
 let P:G→ℝ:=λ x↦(∑ psi∈Κ,c psi*psi x).re
 have HQ (psi:Ε G ℂ): ‖c psi‖ ^2=Ο^2:=by
  simp[c,hu,RT ò]
 have LB: ∑ psi∈Κ, ‖c psi‖ ^2=Ο^2*Κ.card:=by
  simp_rw[HQ]
  simp
  ring
 have Ga :
   ∑ x:G,((f x*mu x:ℝ):ℂ) *
     (∑ psi∈Κ,c psi*psi x) =
    (Ο:ℂ)* ∑ psi∈Κ,(‖spec psi‖ :ℂ):=by
  calc
   _
                               =
     ∑ psi∈Κ,
      c psi* ∑ x:G,((f x*mu x:ℝ):ℂ)*psi x:=by
    simp_rw[á]
    rw[ὶ]
    apply sum_congr rfl
    intro psi Ê
    apply sum_congr rfl
    intro x hx
    ring
   _= ∑ psi∈Κ,(Ο:ℂ)*(‖spec psi‖ :ℂ):=by
    apply sum_congr rfl
    intro psi Ê
    dsimp[c,spec]
    rw[à, ←JQ]
   _=(Ο:ℂ)* ∑ psi∈Κ,(‖spec psi‖ :ℂ):=by
    rw[á]
 have JR :
   ∑ x:G,f x*mu x*P x =
    Ο* ∑ psi∈Κ, ‖spec psi‖:=by
  have JP:=è Complex.re Ga
  calc
   _ =
     (∑ x:G,((f x*mu x:ℝ):ℂ) *
      (∑ psi∈Κ,c psi*psi x)).re:=by
    simp[P,Complex.re_sum,Complex.mul_re]
   _=((Ο:ℂ) *
     ∑ psi∈Κ,(‖spec psi‖ :ℂ)).re:=JP
   _=Ο* ∑ psi∈Κ, ‖spec psi‖:=by simp
 have BN :
   Ο^2*a*Κ.card≤ ∑ x:G,f x*mu x*P x:=by
  rw[JR]
  calc
   _ =
     ∑ psi∈Κ,Ο*(Ο*a):=by
    simp
    ring
   _≤ ∑ psi∈Κ,Ο* ‖spec psi‖:=by
    gcongr with psi Ê
    have hs:=lQ.mp (Ὂ Ê)
    simpa[a,spec] using hs
   _=Ο* ∑ psi∈Κ, ‖spec psi‖:=by
    rw[á]
 let w:G→ℝ:=λ x↦f x*mu x/a
 have vq: ∀ x,0≤w x:=by
  intro x
  exact RS (å (OP x) (AL x)) ha.le
 have AK: ∑ x:G,w x=1:=by
  dsimp[w]
  rw[←TP]
  dsimp[a]
  exact div_self ha.ne'
 have HR:Ο^2*Κ.card≤ ∑ x:G,w x*P x:=by
  calc
   _ ≤
     (∑ x:G,f x*mu x*P x)/a:=by
    rw[ἇ ha]
    calc
     _ =
       Ο^2*a*(Κ.card:ℝ):=by ring
     _≤_:=BN
   _= ∑ x:G,w x*P x:=by
    dsimp[w]
    rw[TP]
    apply sum_congr rfl
    intro x hx
    ring
 have HS :
   exp (Ο^2*Κ.card) ≤
    ∑ x:G,w x*exp (P x):=by
  calc
   _ ≤exp (∑ x:G,w x*P x):=
          Real.exp_le_exp.mpr HR
   _≤_:=j6 w vq AK P
 have AM :
   ∑ x:G,w x*exp (P x) ≤
    a⁻¹ * ∑ x:G,mu x*exp (P x):=by
  dsimp[w]
  rw[á]
  apply sum_le_sum
  intro x hx
  rw[Ri]
  calc
   _ ≤
     a⁻¹ *(1*mu x)*exp (P x):=by
    apply ἂ _ (exp_pos _).le
    apply Å _ (inv_nonneg.mpr ha.le)
    exact ἂ (Jc x) (AL x)
   _=a⁻¹ *(mu x*exp (P x)):=by ring
 have JS :
   ∑ x:G,mu x*exp (P x) ≤
    exp (K+Ο^2*Κ.card/2):=by
  have hr:=s4 mu K Κ AL ó c
  simpa[P,LB] using hr
 have ue  :=
  HS.trans (AM.trans
   (Å JS (inv_nonneg.mpr ha.le)))
 have hmul :
   a*exp (Ο^2*Κ.card) ≤
    exp (K+Ο^2*Κ.card/2):=by
  calc
   _ ≤
     a*(a⁻¹ *exp (K+Ο^2*Κ.card/2)):=by
    gcongr
   _=exp (K+Ο^2*Κ.card/2):=by
    field_simp
 have Cd :
   log a+Ο^2*Κ.card ≤
    K+Ο^2*Κ.card/2:=by
  rw[←exp_log ha, ←exp_add] at hmul
  exact Real.exp_le_exp.mp hmul
 have HT := SY ò
 rw[ἇ HT]
 rw[log_inv]
 nlinarith
lemma jW
  (B X:Finset G) (ud:X⊆B) (Ἵ:X.Nonempty)
  (w:G→ℝ) (c R Ο:ℝ)
  (vq: ∀ x,0≤w x) (hw: ∀ x∈B,w x=c)
  (hc:0<c) (Ὥ:(c*X.card)⁻¹ ≤R)
  (ò:0<Ο) (Κ:Finset (Ε G ℂ))
  (ó:eV w 1 Κ)
  (Ὂ:Κ⊆c5.cj X Ο) :
  (Κ.card:ℝ)≤2*(1+log R)/Ο^2:=by
 classical
 have AN  :=
  jO.f2 ud hw
 have ft:0< ∑ x:G,ý X x*w x:=by
  rw[AN]
  have Et:(0:ℝ)<X.card:=by exact_mod_cast Ἵ.card_pos
  positivity
 have LD:Κ ⊆
   fP w (ý X) Ο:=by
  intro psi Ê
  exact(jO.km
   ud hw hc Ο psi).2 (Ὂ Ê)
 have ί:=iQ
  w (ý X) 1 Ο Κ vq
  (by intro x; unfold ý; split<;>norm_num)
  (by intro x; unfold ý; split<;>norm_num)
  ò ó LD ft
 have Gb :
   ((∑ x:G,ý X x*w x)⁻¹)≤R:=by
  simpa[AN] using Ὥ
 have ei  :=
  ᾆ (inv_pos.mpr ft) Gb
 calc
  _ ≤
    2*(1+log ((∑ x:G,ý X x*w x)⁻¹)) /
     Ο^2:=by simpa using ί
  _≤2*(1+log R)/Ο^2:=by
   gcongr
omit [Δ G] in
lemma om [Finite G]
  (S T:Finset (Ε G ℂ)) (hzero:0∈S)
  (ê: ∀ s∈S, -s∈S) (D:ℝ) (k:ℕ)
  (JT:D<k)
  (ί: ∀ Gamma,Gamma⊆T→ὑ S Gamma →
   Gamma.card≤k→(Gamma.card:ℝ)≤D) :
  ∃ Κ:Finset (Ε G ℂ),
   Κ⊆T∧(Κ.card:ℝ)≤D ∧
    ∀ psi∈T, ∃ z∈Κ.addSpan, ∃ s∈S,psi=z+s:=by
 let:=Fintype.ofFinite G
 classical
 obtain ⟨Κ,uf,zn,ᾍ⟩:=
  nT S T hzero ê
 have ᾤ:Κ.card≤k:=by
  by_contra hnot
  have HU := Nat.le_of_not_ge hnot
  obtain ⟨Gamma,w6,rG⟩:=
   Finset.exists_subset_card_eq HU
  have zo:= ί Gamma (w6.trans uf)
   (zn.mono w6) (by simp[rG])
  rw[rG] at zo
  exact(not_le_of_gt JT) zo
 exact ⟨Κ,uf,ί Κ uf zn ᾤ,ᾍ⟩
def bf (B:aj G) (X:Finset G) (Ο:ℝ):ℝ:=
 2*(1+log (2*(B.Η.card:ℝ)/X.card))/Ο^2
def dg (B:aj G) (X:Finset G) (Ο:ℝ):ℕ:=
 ⌈bf B X Ο⌉₊+1
def cJ (B:aj G) (X:Finset G)
  (Ο:ℝ):ℝ≥0:=
 (100*((max B.Ι 1:ℕ):ℝ≥0) *
  (((2*dg B X Ο+1:ℕ):ℝ≥0)))⁻¹
lemma mY
  (B:aj G) (Ὺ:B.a1)
  (X:Finset G) (Ἵ:X.Nonempty) (ud:X⊆B.Η)
  (Ο:ℝ) (ò:0<Ο) :
  ∃ Φ:ℝ≥0, ∃ C:aj G,
   ∃ Κ:Finset (Ε G ℂ),
    1/2≤Φ∧Φ≤1 ∧
    C=B.ai (Φ*cJ B X Ο) ∧
    C.a1 ∧
    (Κ.card:ℝ)≤bf B X Ο ∧
    Κ⊆c5.cj X Ο ∧
    ∀ psi∈c5.cj X Ο,
     ∃ z∈Κ.addSpan,
      ∃ s∈c5.cj C.Η (1/2),psi=z+s:=by
 classical
 let D := bf B X Ο
 let k := dg B X Ο
 let d := max B.Ι 1
 let a := cJ B X Ο
 obtain ⟨Φ,ᾐ,lj,xv⟩:=
  (B.ai a).eP
 let tau := Φ*a
 let C := B.ai tau
 have td:C.a1:=by
  simpa[C,tau] using xv
 have hd:0<d:=by simp[d]
 have hk:0<k:=by simp[k,dg]
 have ha:a =
   (100*(d:ℝ≥0)*(((2*k+1:ℕ):ℝ≥0)))⁻¹:=by
  simp[a,cJ,d,k]
 have ø:(((2*k:ℕ):ℝ≥0)*tau) ≤
   1/(100*(d:ℝ≥0)):=by
  have LF:(0:ℝ≥0)<(((2*k+1:ℕ):ℝ≥0)):=by positivity
  have Oj:(0:ℝ≥0)<100*(d:ℝ≥0):=by positivity
  calc
   _ =
     ((2*k:ℕ):ℝ≥0)*(Φ*a):=rfl
   _≤((2*k:ℕ):ℝ≥0)*(1*a):=by gcongr
   _=(((2*k:ℕ):ℝ≥0) /
     (((2*k+1:ℕ):ℝ≥0))) /
      (100*(d:ℝ≥0)):=by rw[ha]; field_simp
   _≤1/(100*(d:ℝ≥0)):=by
    gcongr
    exact(ᾜ LF).2 (by
     exact_mod_cast Nat.le_add_right (2*k) 1)
 let T := c5.cj X Ο
 let S :=
  c5.cj C.Η (1/2)
 let w := ay.ed B tau (2*k)
 let Ψ:Finset G:=
  (B.ai (1+(((2*k:ℕ):ℝ≥0)*tau))).Η
 let c:ℝ:=(Ψ.card:ℝ)⁻¹
 let R:ℝ:=2*(B.Η.card:ℝ)/X.card
 have vq: ∀ x,0≤w x:=by
  intro x
  exact ay.qz B tau (2*k) x
 have AJ :=
        ay.sn B tau (2*k)
 have HV: ∀ x∈B.Η,w x=c:=by
  intro x hx
  simpa[w,c,Ψ] using
   (ay.nh B tau (2*k) hx)
 have De:Ψ.card≤2*B.Η.card:=by
  simpa[Ψ,d] using
   (ay.oM Ὺ (2*k) ø)
 have Ez :=
        Ψ.card_pos.mpr (by
   simpa[Ψ] using
    (B.ai (1+(((2*k:ℕ):ℝ≥0)*tau))).aE)
 have hc:0<c:=by
  dsimp[c]
  positivity
 have Ὥ:(c*X.card)⁻¹ ≤R:=by
  have hOr:(0:ℝ)<Ψ.card:=by exact_mod_cast Ez
  have OQ:(0:ℝ)<X.card:=by exact_mod_cast Ἵ.card_pos
  have Nj:(Ψ.card:ℝ)≤2*B.Η.card:=by
   exact_mod_cast De
  calc
   _ =(Ψ.card:ℝ)/X.card:=by
    dsimp[c]
    field_simp
   _≤(2*B.Η.card:ℝ)/X.card:=
    (R9 OQ).2 Nj
   _=R:=by simp[R]
 have hzero :=
        nm C.Η
 have ê: ∀ s∈S, -s∈S:=by
  intro s hs
  exact ku hs
 have JT:D<(k:ℝ):=by
  calc
   D≤(⌈D⌉₊:ℝ):=Rr D
   _<((⌈D⌉₊+1:ℕ):ℝ):=by
    exact_mod_cast Tr ⌈D⌉₊
   _=(k:ℝ):=by simp[k,dg,D]
 have ί: ∀ Gamma,Gamma⊆T→ὑ S Gamma →
   Gamma.card≤k→(Gamma.card:ℝ)≤D:=by
  intro Gamma HW EA rG
  have hq: ∀ psi,psi∉S →
    ‖ay.ἅ w psi‖ ≤(1/2:ℝ)^(2*k):=by
   intro psi Ê
   calc
    _ ≤
      ‖ay.ἅ
       (af (B.ai tau).Η) psi‖ ^(2*k):=
           ay.ly
      B tau (2*k) psi
    _≤(1/2:ℝ)^(2*k):=by
     gcongr
     exact(ay.fy
      (B.ai tau) psi (by simpa[S,C] using Ê)).le
  have qy:eV w 1 Gamma:=by
   apply EA.k4
    vq AJ (by positivity) hq rG
   rw[Ἂ]
   norm_num
  have ch:=jW
   B.Η X ud Ἵ w c R Ο vq HV hc Ὥ ò Gamma
    qy (by simpa[T] using HW)
  simpa[D,bf,R] using ch
 obtain ⟨Κ,uf,ᾤ,ᾍ⟩:=
  om S T hzero ê D k JT ί
 refine ⟨Φ,C,Κ,ᾐ,lj, ?_,td, ?_, ?_, ?_⟩
 ·simp[C,tau,a]
 ·simpa[D] using ᾤ
 ·simpa[T] using uf
 ·simpa[T,S] using ᾍ
end ay.aI
end
end
section
open Finset Function Real
open scoped BigOperators NNReal
namespace ay.jm
variable {G:Type*} [Δ G] [Γ G] [Β G]
noncomputable def Í (psi:Ε G ℂ):ρ G:=by
  let e:=AddCircle.homeomorphCircle (by norm_num:(1:ℝ)≠0)
  exact
    { toFun:=λ x↦e.symm ((AddChar.circleEquivComplex.symm psi) x)
      map_zero':=by
        apply e.injective
        simp[e,QY]
      map_add':=by
        intro x y
        apply e.injective
        rw[e.apply_symm_apply]
        rw[show e (e.symm ((AddChar.circleEquivComplex.symm psi) x) +
              e.symm ((AddChar.circleEquivComplex.symm psi) y)) =
            AddCircle.toCircle (e.symm ((AddChar.circleEquivComplex.symm psi) x) +
              e.symm ((AddChar.circleEquivComplex.symm psi) y)) by
              exact QY _ _]
        rw[Ub]
        rw[←QY (by norm_num:(1:ℝ)≠0),
          e.apply_symm_apply]
        rw[←QY (by norm_num:(1:ℝ)≠0),
          e.apply_symm_apply]
        exact St _ _ _ }
omit [Β G] in
lemma qB (psi:Ε G ℂ) (x:G) :
  AddCircle.toCircle (Í psi x) =
   (AddChar.circleEquivComplex.symm psi) x:=by
 rw[←QY (by norm_num:(1:ℝ)≠0)]
 simp[Í]
omit [Β G] in
lemma eE (psi:Ε G ℂ) (x:G) :
  (AddCircle.toCircle (Í psi x):ℂ)=psi x:=by
 classical
 rw[qB]
 exact S6 (AddChar.circleEquivComplex.apply_symm_apply psi) x
omit [Β G] in
lemma pV :
  Injective (Í (G:=G)):=by
 intro psi ß h
 ext x
 have hx:=S6 h x
 have hh:=è (λ z:AddCircle (1:ℝ)↦(AddCircle.toCircle z:ℂ)) hx
 simpa only[eE] using hh
noncomputable def ῷ :
  Ε G ℂ→+ ρ G where
 toFun:=Í
 map_zero':=by
  ext x
  apply TD (by norm_num:(1:ℝ)≠0)
  apply RI
  simp[eE]
 map_add' psi ß:=by
  ext x
  apply TD (by norm_num:(1:ℝ)≠0)
  apply RI
  simp[eE,Ub,
   U3]
noncomputable def nL (Κ:Finset (Ε G ℂ)) (r:ℝ≥0) :
  aj G where
 í:=Κ.image Í
 Υ:=λ _↦r
omit [Β G] in
@[simp] lemma pH (Κ:Finset (Ε G ℂ)) (r:ℝ≥0)
  (gamma:ρ G) :
  (nL Κ r).Υ gamma=r:=rfl
omit [Β G] in
lemma iC
  {Κ:Finset (Ε G ℂ)} {r:ℝ≥0} {psi:Ε G ℂ} {x:G}
  (hx:x∈(nL Κ r).Η)
  (Ê:psi∈Κ.addSpan) :
  ‖Í psi x‖ ≤(Κ.card:ℝ)*(r:ℝ):=by
 classical
 rw[Finset.mem_addSpan] at Ê
 obtain ⟨Μ,Ἷ,hsum⟩:=Ê
 have HX :
   ∑ gamma∈Κ,Μ gamma•Í gamma =
    Í psi:=by
  change ∑ gamma∈Κ,Μ gamma•ῷ gamma=ῷ psi
  calc
   ∑ gamma∈Κ,Μ gamma•ῷ gamma =
     ∑ gamma∈Κ,ῷ (Μ gamma•gamma):=by
      apply sum_congr rfl
      intro gamma ᾣ
      exact(map_zsmul ῷ (Μ gamma) gamma).symm
   _=ῷ (∑ gamma∈Κ,Μ gamma•gamma):=by
    exact(ᾘ ῷ (λ gamma↦Μ gamma•gamma) Κ).symm
   _=ῷ psi:=è ῷ hsum
 have EB :
   (∑ gamma∈Κ,Μ gamma•Í gamma) x =
    ∑ gamma∈Κ,(Μ gamma•Í gamma) x:=by
  induction Κ using Finset.induction_on with
  | empty=>simp
  | @insert gamma Κ ᾣ ih=>simp[ᾣ]
 rw[←HX,EB]
 calc
  ‖∑ gamma∈Κ,(Μ gamma•Í gamma) x‖ ≤
    ∑ gamma∈Κ, ‖(Μ gamma•Í gamma) x‖:=
   Rq _ _
  _≤ ∑ _gamma∈Κ,(r:ℝ):=by
   apply sum_le_sum
   intro gamma ᾣ
   have CK:Í gamma∈(nL Κ r).í:=by
    exact Finset.mem_image.mpr ⟨gamma,ᾣ,rfl⟩
   have ú:=(aj.mem_carrier _ _).mp hx
    (Í gamma) CK
   have hw: ‖Í gamma x‖ ≤(r:ℝ):=by
    simpa only[pH] using ú
   rcases Ἷ gamma with ê | hzero | JU
   ·simpa[ê] using hw
   ·simp[hzero]
   ·simpa[JU] using hw
  _=(Κ.card:ℝ)*(r:ℝ):=by simp
noncomputable def cD (B:aj G)
    (Κ:Finset (Ε G ℂ)) (Ρ r:ℝ≥0):aj G:=by
  classical
  let Cm:=Κ.image Í
  exact
    { í:=B.í∪Cm
      Υ:=λ gamma ↦
        if gamma∈B.í then
          if gamma∈Cm then min (Ρ*B.Υ gamma) r
          else Ρ*B.Υ gamma
        else r }
omit [Β G] in
lemma vB (B:aj G)
  (Κ:Finset (Ε G ℂ)) (Ρ r:ℝ≥0) :
  (cD B Κ Ρ r).Ι≤B.Ι+Κ.card:=by
 classical
 rw[aj.Ι,aj.Ι,cD]
 exact(Finset.card_union_le _ _).trans_eq (by
  rw[Finset.card_image_iff.mpr pV.injOn])
omit [Β G] in
lemma fD (B:aj G)
    (Κ:Finset (Ε G ℂ)) (Ρ r:ℝ≥0) :
    (cD B Κ Ρ r).Η⊆(B.ai Ρ).Η:=by
  classical
  intro x hx
  rw[aj.mem_carrier] at hx ⊢
  intro gamma ᾣ
  have y5:gamma∈B.í:=by simpa using ᾣ
  have AO:gamma∈B.í∪Κ.image Í:=
    Um _ y5
  have hbound:=hx gamma (by simpa[cD] using AO)
  by_cases AQ:gamma∈Κ.image Í
  · change ‖gamma x‖ ≤
      (((if gamma∈B.í then
          if gamma∈Κ.image Í then
            min (Ρ*B.Υ gamma) r else Ρ*B.Υ gamma
        else r):ℝ≥0):ℝ) at hbound
    rw[ή y5,ή AQ] at hbound
    simpa only[aj.oF,SK] using
      hbound.trans (by exact_mod_cast(Uv (Ρ*B.Υ gamma) r))
  · change ‖gamma x‖ ≤
      (((if gamma∈B.í then
          if gamma∈Κ.image Í then
            min (Ρ*B.Υ gamma) r else Ρ*B.Υ gamma
        else r):ℝ≥0):ℝ) at hbound
    rw[ή y5,if_neg AQ] at hbound
    simpa only[aj.oF,SK] using hbound
omit [Β G] in
lemma gd (B:aj G)
  (Κ:Finset (Ε G ℂ)) (Ρ r:ℝ≥0) :
  (cD B Κ Ρ r).Η⊆(nL Κ r).Η:=by
 classical
 intro x hx
 rw[aj.mem_carrier] at hx ⊢
 intro gamma ᾣ
 rw[pH]
 obtain ⟨psi,Ê,rfl⟩:=Finset.mem_image.mp ᾣ
 have AQ:Í psi∈Κ.image Í:=
  Finset.mem_image.mpr ⟨psi,Ê,rfl⟩
 have AO:Í psi∈B.í∪Κ.image Í:=
  Ua _ AQ
 have hbound:=hx (Í psi) (by simpa[cD] using AO)
 by_cases hold:Í psi∈B.í
 ·change ‖Í psi x‖ ≤
   (((if Í psi∈B.í then
     if Í psi∈Κ.image Í then
      min (Ρ*B.Υ (Í psi)) r
     else Ρ*B.Υ (Í psi)
    else r):ℝ≥0):ℝ) at hbound
  rw[ή hold,ή AQ] at hbound
  exact hbound.trans (by
   exact_mod_cast(min_le_right (Ρ*B.Υ (Í psi)) r))
 ·change ‖Í psi x‖ ≤
   (((if Í psi∈B.í then
     if Í psi∈Κ.image Í then
      min (Ρ*B.Υ (Í psi)) r
     else Ρ*B.Υ (Í psi)
    else r):ℝ≥0):ℝ) at hbound
  rw[if_neg hold] at hbound
  exact hbound
omit [Β G] in
lemma gZ
  (B:aj G) {Κ:Finset (Ε G ℂ)} {Ρ r:ℝ≥0}
  {psi:Ε G ℂ} {x:G}
  (hx:x∈(cD B Κ Ρ r).Η)
  (Ê:psi∈Κ.addSpan) :
  ‖Í psi x‖ ≤(Κ.card:ℝ)*(r:ℝ):=
 iC
  (gd B Κ Ρ r hx) Ê
omit [Β G] in
lemma lV
  (psi:Ε G ℂ) (x:G)
  (JV: ‖Í psi x‖ ≤(2*pi)⁻¹) :
  ‖1-psi x‖ ≤4*pi* ‖Í psi x‖:=by
 classical
 let a:ℝ:=AddCircle.equivIoc (1:ℝ) (-1/2) (Í psi x)
 have EC:a∈Set.Ioc (-1/2) (-1/2+1):=
  (AddCircle.equivIoc (1:ℝ) (-1/2) (Í psi x)).property
 have JW: |a| ≤1/2:=by
  rw[abs_le]
  constructor<;>linarith[EC.1,EC.2]
 have tw:(a:AddCircle (1:ℝ))=Í psi x:=by
  exact AddCircle.coe_equivIoc
 have Cn: ‖Í psi x‖ = |a|:=by
  rw[←tw]
  exact(Ts (1:ℝ) (by norm_num)).2 (by simpa using JW)
 have vV: ‖(2*pi*a:ℂ)‖ =2*pi* |a|:=by
  simp[ᾮ,ἳ Real.pi_nonneg]
 have ῡ: ‖(2*pi*a:ℂ)*Complex.I‖ ≤1:=by
  rw[ἑ,Complex.norm_I,Ἣ,vV, ←Cn]
  have Af:0<2*pi:=by positivity
  calc
   2*pi* ‖Í psi x‖ ≤
     2*pi*(2*pi)⁻¹:=
    Å JV Af.le
   _=1:=by field_simp
 have Ὁ:=Complex.norm_exp_sub_one_le ῡ
 have heval:psi x=Complex.exp ((2*pi*a:ℂ)*Complex.I):=by
  rw[←eE psi x, ←tw]
  simp only[AddCircle.toCircle_apply_mk,Circle.coe_exp]
  congr 1
  push_cast
  field_simp
 rw[heval,norm_sub_rev]
 calc
  ‖Complex.exp ((2*pi*a:ℂ)*Complex.I)-1‖
    ≤ 2* ‖(2*pi*a:ℂ)*Complex.I‖:=Ὁ
  _=4*pi* ‖Í psi x‖:=by
   rw[ἑ,Complex.norm_I,Ἣ,vV,Cn]
   ring
omit [Β G] in
lemma jP
  (B:aj G) {Κ:Finset (Ε G ℂ)} {Ρ r:ℝ≥0}
  {psi:Ε G ℂ} {x:G}
  (ø:(Κ.card:ℝ)*(r:ℝ)≤(2*pi)⁻¹)
  (hx:x∈(cD B Κ Ρ r).Η)
  (Ê:psi∈Κ.addSpan) :
  ‖1-psi x‖ ≤4*pi*((Κ.card:ℝ)*(r:ℝ)):=by
 classical
 have JX:=gZ
  B hx Ê
 calc
  _ ≤4*pi* ‖Í psi x‖:=
   lV psi x (JX.trans ø)
  _≤4*pi*((Κ.card:ℝ)*(r:ℝ)):=
   Å JX (by positivity)
omit [Β G] in
lemma jh
  (B:aj G) {Κ Q S:Finset (Ε G ℂ)} {Ρ r:ℝ≥0}
  {beta:ℝ} {x:G}
  (ø:(Κ.card:ℝ)*(r:ℝ)≤(2*pi)⁻¹)
  (hx:x∈(cD B Κ Ρ r).Η)
  (ᾍ: ∀ psi∈Q, ∃ z∈Κ.addSpan, ∃ s∈S,psi=z+s)
  (ED: ∀ s∈S, ‖1-s x‖ ≤beta) :
  ∀ psi∈Q,
   ‖1-psi x‖ ≤4*pi*((Κ.card:ℝ)*(r:ℝ))+beta:=by
 classical
 intro psi Ê
 obtain ⟨z,hz,s,hs,rfl⟩:=ᾍ psi Ê
 have HY  :=
  jP B ø hx hz
 calc
  _ = ‖(1-z x)+z x*(1-s x)‖:=by
   rw[U3]
   congr 1
   ring
  _≤ ‖1-z x‖ + ‖z x*(1-s x)‖:=norm_add_le _ _
  _= ‖1-z x‖ + ‖1-s x‖:=by
   rw[ἑ,Q0,ἃ]
  _≤4*pi*((Κ.card:ℝ)*(r:ℝ))+beta:=
   Sr HY (ED s hs)
omit [Β G] in
lemma iY
  (C:aj G) (Ô:C.a1)
  {Κ Q:Finset (Ε G ℂ)} {sigma r:ℝ≥0}
  (Ὣ:sigma ≤
   1/(100*(max C.Ι 1:ℕ):ℝ≥0))
  (ø:(Κ.card:ℝ)*(r:ℝ)≤(2*pi)⁻¹)
  (ᾍ: ∀ psi∈Q, ∃ z∈Κ.addSpan,
   ∃ s∈c5.cj C.Η (1/2),psi=z+s) :
  ∀ x∈(cD C Κ sigma r).Η, ∀ psi∈Q,
   ‖1-psi x‖ ≤
    4*pi*((Κ.card:ℝ)*(r:ℝ)) +
     400*((max C.Ι 1:ℕ):ℝ)*(sigma:ℝ):=by
 classical
 intro x hx
 apply jh
  C ø hx ᾍ
 intro s hs
 exact ay.kl
  Ô Ὣ hs (fD C Κ sigma r hx)
end ay.jm
end
section
open Finset
open scoped BigOperators NNReal
namespace ay.qC
noncomputable section
variable {G:Type*} [Γ G] [Δ G] [Β G]
open aj jm
def rI (m:ℕ) (hm:0< m) (z:AddCircle (1:ℝ)):Fin m:=by
 have ug:0≤(ï z+1/2)*(m:ℝ):=by
  have hz:=(k1 z).1
  have Ὀ:(0:ℝ)≤ m:=by positivity
  exact å (by linarith) Ὀ
 refine ⟨⌊(ï z+1/2)*m⌋₊,(Uc ug).2 ?_⟩
 have hz:ï z+1/2<1:=by
  linarith[(k1 z).2]
 have Ὀ:(0:ℝ)< m:=by exact_mod_cast hm
 exact(Sk hz Ὀ).trans_eq (ἃ (m:ℝ))
lemma nV
  {m:ℕ} (hm:0< m) {z w:AddCircle (1:ℝ)}
  (ό:rI m hm z=rI m hm w) :
  ‖z-w‖ ≤1/(m:ℝ):=by
 let rz:=ï z
 let rw:=ï w
 let uz:=(rz+1/2)*(m:ℝ)
 let uw:=(rw+1/2)*(m:ℝ)
 have P8:0≤rz+1/2:=by
  dsimp[rz]
  linarith[(k1 z).1]
 have P9:0≤rw+1/2:=by
  dsimp[rw]
  linarith[(k1 w).1]
 have Ὀ:(0:ℝ)< m:=by exact_mod_cast hm
 have OR:0≤uz:=by dsimp[uz]; positivity
 have OS:0≤uw:=by dsimp[uw]; positivity
 have vW:⌊uz⌋₊=⌊uw⌋₊:=by
  have ᾟ:=è Fin.val ό
  simpa only[rI,uz,uw,rz,rw] using ᾟ
 have uZ := Ti OR
 have u0 := RY uz
 have AR := Ti OS
 have AS := RY uw
 have Df:(rz-rw)*(m:ℝ)<1:=by
  dsimp[uz,uw] at uZ u0 AR AS
  rw[vW] at uZ u0
  nlinarith
 have Dg: -(1/(m:ℝ))<rz-rw:=by
  have hmul:(-1:ℝ)<(rz-rw)*(m:ℝ):=by
   dsimp[uz,uw] at uZ u0 AR AS
   rw[vW] at uZ u0
   nlinarith
  have hdiv:(-1:ℝ)/(m:ℝ)<rz-rw:=
   (Tv Ὀ).2 hmul
  simpa only[neg_div,ῆ] using hdiv
 have BO:rz-rw<1/(m:ℝ):=
  (SP Ὀ).2 Df
 calc
  _ ≤ |rz-rw|:=gu z w
  _≤1/(m:ℝ):=(abs_lt.2 ⟨Dg,BO⟩).le
def signature (Κ:Finset (Ε G ℂ))
  (m:ℕ) (hm:0< m) (x:G):Κ→Fin m:=
 λ psi↦rI m hm (Í psi.1 x)
omit [Β G] in
lemma qE
  (B:aj G) (Κ:Finset (Ε G ℂ))
  (Ρ r:ℝ≥0) (x:G) :
  x∈(cD B Κ Ρ r).Η ↔
   x∈(B.ai Ρ).Η ∧
    ∀ psi∈Κ, ‖Í psi x‖ ≤(r:ℝ):=by
 classical
 constructor
 ·intro hx
  refine ⟨fD B Κ Ρ r hx, ?_⟩
  intro psi Ê
  have JY:=gd B Κ Ρ r hx
  exact(aj.mem_carrier _ _).mp JY (Í psi)
   (Finset.mem_image.mpr ⟨psi,Ê,rfl⟩)
 ·rintro ⟨É,ó⟩
  rw[aj.mem_carrier] at É ⊢
  intro gamma ᾣ
  change gamma∈B.í∪Κ.image Í at ᾣ
  rw[Finset.mem_union] at ᾣ
  change ‖gamma x‖ ≤
   (((if gamma∈B.í then
     if gamma∈Κ.image Í then
      min (Ρ*B.Υ gamma) r
     else Ρ*B.Υ gamma
    else r):ℝ≥0):ℝ)
  rcases ᾣ with vX | JZ
  ·by_cases Dh:gamma∈Κ.image Í
   ·obtain ⟨psi,Ê,EE⟩:=Finset.mem_image.mp Dh
    subst gamma
    rw[ή vX,ή Dh]
    exact le_min (É _ vX) (ó psi Ê)
   ·rw[ή vX,if_neg Dh]
    exact É gamma vX
  ·obtain ⟨psi,Ê,EE⟩:=Finset.mem_image.mp JZ
   subst gamma
   by_cases vX:Í psi∈B.í
   ·rw[ή vX,ή JZ]
    exact le_min (É _ vX) (ó psi Ê)
   ·rw[if_neg vX]
    exact ó psi Ê
omit [Β G] in
private lemma mB
  (B:aj G) (Κ:Finset (Ε G ℂ))
  (Ρ:ℝ≥0) {m:ℕ} (hm:0< m)
  (S:Finset G) (Ø:S⊆(B.ai Ρ).Η)
  {x y:↥S} (ni:signature Κ m hm x.1=signature Κ m hm y.1) :
  x.1-y.1 ∈
   (cD B Κ (Ρ+Ρ) (m:ℝ≥0)⁻¹).Η:=by
 classical
 rw[qE]
 constructor
 ·exact aj.j2 (Ø x.2) (Ø y.2)
 ·intro psi Ê
  rw[map_sub]
  have vU:=Uu ni ⟨psi,Ê⟩
  have hbound:=nV hm vU
  simpa only[SE,S9,ῆ] using hbound
omit [Β G] in
private lemma s5
  (B:aj G) (Κ:Finset (Ε G ℂ))
  (Ρ:ℝ≥0) {m:ℕ} (hm:0< m)
  (S:Finset G) (Ø:S⊆(B.ai Ρ).Η)
  (a:Κ→Fin m) :
  Fintype.card {x:↥S// signature Κ m hm x.1=a} ≤
   (cD B Κ (Ρ+Ρ) (m:ℝ≥0)⁻¹).Η.card:=by
 classical
 by_cases jv:Nonempty {x:↥S// signature Κ m hm x.1=a}
 ·let x₀ := Classical.choice jv
  let f:{x:↥S// signature Κ m hm x.1=a} →
    ↥(cD B Κ (Ρ+Ρ) (m:ℝ≥0)⁻¹).Η:=
   λ x↦⟨x.1.1-x₀.1.1,mB
    B Κ Ρ hm S Ø (x.2.trans x₀.2.symm)⟩
  have hf:Injective f:=by
   intro x y ni
   apply RI
   apply RI
   have ᾟ:=è Subtype.val ni
   dsimp[f] at ᾟ
   exact S8 ᾟ
  calc
   _ ≤
     Fintype.card ↥(cD B Κ (Ρ+Ρ)
      (m:ℝ≥0)⁻¹).Η:=R1 f hf
   _=(cD B Κ (Ρ+Ρ)
      (m:ℝ≥0)⁻¹).Η.card:=Rx _
 ·simp only[To] at jv
  simp
omit [Β G] in
lemma nW
  (B:aj G) (Κ:Finset (Ε G ℂ))
  (Ρ:ℝ≥0) {m:ℕ} (hm:0< m)
  (S:Finset G) (Ø:S⊆(B.ai Ρ).Η) :
  S.card≤ m^Κ.card *
   (cD B Κ (Ρ+Ρ) (m:ℝ≥0)⁻¹).Η.card:=by
 classical
 let Sigma:=Κ→Fin m
 let q:↥S→ Sigma:=λ x↦signature Κ m hm x.1
 have jv: ∀ a:Sigma,
   Fintype.card {x:↥S// q x=a} ≤
    (cD B Κ (Ρ+Ρ) (m:ℝ≥0)⁻¹).Η.card:=by
  intro a
  exact s5 B Κ Ρ hm S Ø a
 have Di:Fintype.card Sigma=m^Κ.card:=by
  dsimp[Sigma]
  rw[TC]
  simp
 rw[←Rx S, ←Di]
 by_contra h
 have Ί:Fintype.card Sigma *
   (cD B Κ (Ρ+Ρ) (m:ℝ≥0)⁻¹).Η.card <
    Fintype.card ↥S:=by omega
 obtain ⟨a,ha⟩:=Rk (f:=q) Ί
 have Em: #{x | q x=a} ≤
   (cD B Κ (Ρ+Ρ) (m:ℝ≥0)⁻¹).Η.card:=by
  rw[←SL]
  exact jv a
 exact(ῑ Em) ha
omit [Β G] in
lemma tz
  (B:aj G) (Κ:Finset (Ε G ℂ))
  (Ρ:ℝ≥0) {m:ℕ} (hm:0< m)
  (S:Finset G) (Ø:S⊆(B.ai Ρ).Η) :
  (cD B Κ (Ρ+Ρ) (m:ℝ≥0)⁻¹).Ι ≤
    B.Ι+Κ.card ∧
   (cD B Κ (Ρ+Ρ) (m:ℝ≥0)⁻¹).Η ⊆
    (B.ai (Ρ+Ρ)).Η ∧
   S.card≤ m^Κ.card *
    (cD B Κ (Ρ+Ρ)
     (m:ℝ≥0)⁻¹).Η.card:=by
 classical
 exact ⟨vB B Κ _ _,
  fD B Κ _ _,
  nW B Κ Ρ hm S Ø⟩
end
end ay.qC
end
section
open scoped BigOperators ENNReal NNReal Pointwise translate
open Finset Function MeasureTheory RCLike
namespace ay.ag
variable {G:Type*} [Δ G] [Γ G] [Β G]
omit [Β G] [Δ G] in
lemma q8 [Finite G] (psi:Ε G ℂ) (t:G) :
  ‖psi (-t)-1‖ = ‖1-psi t‖:=by
 rw[psi.map_neg_eq_inv]
 have ᾱ:psi t≠0:=by
  intro h
  have:=Q0 psi t
  simp[h] at this
 calc
  _ = ‖(psi t)⁻¹ *(1-psi t)‖:=by
   congr 1
   field_simp
  _= ‖1-psi t‖:=by
   rw[ἑ,Up,Q0,inv_one,ἃ]
lemma oR
  [MeasurableSpace G] [Α G]
  (X:Finset G) (Ἵ:X.Nonempty) (m:ℕ) (F:G→ℂ)
  (Ο ς:ℝ) (ò:0≤Ο) (OT:0≤ς)
  (t:G)
  (Ᾰ: ∀ psi:Ε G ℂ,
   Ο≤ ‖π ((@mu (ℂ) _ _) X) psi‖ → ‖1-psi t‖ ≤ς) :
  (aJ (∞) (τ t ((Χ ((ἶ (mu X) m)) F))-((Χ ((ἶ (mu X) m)) F)))) ≤
   (ς+2*Ο^m)*(ð 1 (π F)):=by
 rw[dw]
 refine ciSup_le λ x↦ ?_
 let P:G→ℂ:=(Χ ((ἶ (mu X) m)) F)
 have Ὄ :
   (τ t P-P) x =
    𝔼 psi:Ε G ℂ,
     π P psi*(psi (x-t)-psi x):=by
  simp only[Rw,ῗ]
  rw[←vn P (x-t), ←vn P x,
   ←Finset.expect_sub_distrib]
  apply Finset.expect_congr rfl
  intro psi _
  ring
 rw[Ὄ]
 calc
  ‖𝔼 psi:Ε G ℂ,
    π P psi*(psi (x-t)-psi x)‖
    ≤ 𝔼 psi:Ε G ℂ,
      ‖π P psi*(psi (x-t)-psi x)‖:=
     RCLike.norm_expect_le (K:=ℝ)
  _≤𝔼 psi:Ε G ℂ,
     (ς+2*Ο^m)* ‖π F psi‖:=by
   refine expect_le_expect λ psi _↦ ?_
   rw[ἑ]
   have oc :
     ‖psi (x-t)-psi x‖ = ‖1-psi t‖:=by
    have AG:psi (x-t)=psi x*psi (-t):=by
     rw[Ἱ,psi.map_add_eq_mul]
    rw[AG]
    calc
     ‖psi x*psi (-t)-psi x‖ = ‖psi x*(psi (-t)-1)‖:=by ring_nf
     _= ‖psi (-t)-1‖:=by rw[ἑ,Q0,ἃ]
     _= ‖1-psi t‖:=q8 psi t
   rw[oc]
   simp only[P,sb,vP,ἑ,norm_pow]
   have AL: ‖π ((@mu (ℂ) _ _) X) psi‖ ≤1:=by
    calc
     ‖π ((@mu (ℂ) _ _) X) psi‖ ≤(aJ 1 (((@mu (ℂ) _ _) X))):=pD _ _
     _=1:=uN Ἵ
   by_cases Ὤ:Ο≤ ‖π ((@mu (ℂ) _ _) X) psi‖
   ·have hpow: ‖π ((@mu (ℂ) _ _) X) psi‖ ^m≤1:=
     Uy (Re _) AL
    have hp:=Ᾰ psi Ὤ
    calc
     ‖π ((@mu (ℂ) _ _) X) psi‖ ^m* ‖π F psi‖ * ‖1-psi t‖ ≤
       1* ‖π F psi‖ *ς:=by gcongr
     _≤(ς+2*Ο^m)* ‖π F psi‖:=by
      have LG:0≤Ο^m:=ἥ ò m
      have hF:0≤ ‖π F psi‖:=Re _
      nlinarith
   ·have uX: ‖π ((@mu (ℂ) _ _) X) psi‖ ^m≤Ο^m:=by
     exact ἤ (Re _) (le_of_not_ge Ὤ) m
    have OU: ‖1-psi t‖ ≤2:=by
     calc
      ‖1-psi t‖ ≤ ‖(1:ℂ)‖ + ‖psi t‖:=norm_sub_le _ _
      _=2:=by norm_num
    calc
     ‖π ((@mu (ℂ) _ _) X) psi‖ ^m* ‖π F psi‖ * ‖1-psi t‖ ≤
       Ο^m* ‖π F psi‖ *2:=by gcongr
     _≤(ς+2*Ο^m)* ‖π F psi‖:=by
      have LG:0≤Ο^m:=ἥ ò m
      have hF:0≤ ‖π F psi‖:=Re _
      nlinarith
  _=(ς+2*Ο^m)*(ð 1 (π F)):=by
   rw[tq,Finset.mul_expect]
lemma sv
  [MeasurableSpace G] [Α G]
  (A B C:Finset G) (ξ:A.Nonempty) (Ã:C.Nonempty) :
  (ð 1 (π ((Χ (((Χ ((@mu (ℂ) _ _) A) (((indicator B λ _↦(1:_)):G→ℂ))))) (mu C))))) ≤
   Real.sqrt ((B.card:ℝ)/C.card):=by
 calc
  _
    = (ð 1 (π ((@mu (ℂ) _ _) A) *
      (π ((indicator B λ _↦(1:_)):G→ℂ)*π ((@mu (ℂ) _ _) C)))):=by
     rw[x2,x2]
     congr 1
     funext psi
     ring_nf
  _≤(ð 1 (π ((indicator B λ _↦(1:_)):G→ℂ)*π ((@mu (ℂ) _ _) C))):=by
   calc
    _≤(ð 1 (π ((indicator B λ _↦(1:_)):G→ℂ)*π ((@mu (ℂ) _ _) C))) *
       (ð (∞) (π ((@mu (ℂ) _ _) A))):=by
      simpa[ä] using
       (tY (f:=π ((indicator B λ _↦(1:_)):G→ℂ)*π ((@mu (ℂ) _ _) C))
        (g:=π ((@mu (ℂ) _ _) A)) 1 ∞)
    _≤(ð 1 (π ((indicator B λ _↦(1:_)):G→ℂ)*π ((@mu (ℂ) _ _) C)))*1:=by
      gcongr
      ·exact yM
      exact(qY _).trans_eq (uN ξ)
    _=_:=Ἣ _
  _≤(ð 2 (π ((indicator B λ _↦(1:_)):G→ℂ)))*(ð 2 (π ((@mu (ℂ) _ _) C))):=
   tY 2 2
  _=Real.sqrt (B.card:ℝ)*(C.card:ℝ)^(-2⁻¹ :ℝ):=by
   rw[w5,tU,w5,CD Ã]
  _=Real.sqrt ((B.card:ℝ)/C.card):=by
   rw[Real.sqrt_div (by positivity),U4,
    U4,ἱ]
   congr 1
   rw[←TS (by positivity)]
   congr 1
   norm_num
lemma s6 (X:Finset G) (psi:Ε G ℂ) :
  π ((@mu (ℂ) _ _) X) psi =
   ay.ἅ (ay.af X) (-psi):=by
 classical
 rw[Ú,wInner_one_eq_sum]
 simp only[inner_apply',ay.ἅ,
  U2]
 apply Ò rfl
 intro x _
 unfold mu ay.af
 by_cases hx:x∈X
 ·simp[hx,ᾞ, ←Rz,
   ←Ud,ä]
 ·simp[hx,ᾞ]
omit [Β G] in
lemma vY (f:G→ℂ) (a:G) (psi:Ε G ℂ) :
  ‖π (τ a f) psi‖ = ‖π f psi‖:=by
 rw[Ú,Ú,wInner_one_eq_sum,wInner_one_eq_sum]
 simp only[inner_apply',ῗ]
 have hsum :
   (∑ x:G,starRingEnd ℂ (psi x)*f (x-a)) =
    starRingEnd ℂ (psi a)* ∑ x:G,starRingEnd ℂ (psi x)*f x:=by
  rw[á]
  refine ἐ (Equiv.addRight (-a)) _ _ (λ x↦ ?_)
  simp only[Equiv.coe_addRight,Ἱ,St,
   Ud,ᾪ,map_inv₀]
  have ᾱ:starRingEnd ℂ (psi a)≠0:=by
   have Ê:psi a≠0:=by
    intro h
    have ᾷ:=Q0 psi a
    rw[h,norm_zero] at ᾷ
    norm_num at ᾷ
   simpa using Ê
  field_simp
 rw[hsum,ἑ]
 simp
lemma tA (T:Finset G) (a:G) (psi:Ε G ℂ) :
  ‖π ((@mu (ℂ) _ _) (a+ᵥ T)) psi‖ = ‖π ((@mu (ℂ) _ _) T) psi‖:=by
 rw[←vI (K:=ℂ)]
 exact vY ((@mu (ℂ) _ _) T) a psi
omit [Β G] in
lemma kH
  (X:Finset G) (Ἵ:X.Nonempty) (psi:Ε G ℂ)
  (Ê:(1/2:ℝ)≤ ‖π ((@mu (ℂ) _ _) X) psi‖) :
  psi∈ay.c5.cj X (1/2):=by
 classical
 by_contra hnot
 have ê: -psi∉ay.c5.cj X (1/2):=by
  intro hn
  have:=ay.aI.ku hn
  exact hnot (by simpa only[neg_neg] using this)
 have NW  :=
        ᾙ λ h↦ê (ay.c5.gm.mpr h)
 have ch:(0:ℝ)<X.card:=by exact_mod_cast Ἵ.card_pos
 have Ί :
   ‖ay.ἅ (ay.af X) (-psi)‖ <1/2:=by
  rw[ay.jU,ἑ,Up,
   Rf,ᾮ,RT ch]
  calc
   _ <
     (X.card:ℝ)⁻¹ *((1/2:ℝ)*X.card):=by gcongr
   _=1/2:=by field_simp
 rw[s6] at Ê
 linarith
lemma ib
  (T:Finset G) (ἓ:T.Nonempty) (a:G) (psi:Ε G ℂ)
  (Ê:(1/2:ℝ)≤ ‖π ((@mu (ℂ) _ _) (a+ᵥ T)) psi‖) :
  psi∈ay.c5.cj T (1/2):=by
 apply kH T ἓ psi
 rw[←tA T a psi]
 exact Ê
noncomputable def a6 (D:ℝ):ℕ:=
 ⌈2*pi*max D 0⌉₊+1
lemma gf (D:ℝ):0<a6 D:=by
 simp[a6]
lemma jc (D:ℝ) :
  D*((((a6 D:ℕ):ℝ≥0)⁻¹ :ℝ)) ≤
   (2*pi)⁻¹:=by
 let n:=a6 D
 have LH:0<n:=gf D
 have hn:(0:ℝ)<n:=by exact_mod_cast LH
 have Af:(0:ℝ)<2*pi:=by positivity
 have Ῡ:2*pi*max D 0 ≤
   (Nat.ceil (2*pi*max D 0):ℝ):=Rr _
 have Ἆ:2*pi*D≤(n:ℝ):=by
  calc
   2*pi*D≤2*pi*max D 0:=by
    gcongr
    exact Tu _ _
   _≤(Nat.ceil (2*pi*max D 0):ℝ):=Ῡ
   _≤(n:ℝ):=by
    dsimp[n,a6]
    exact_mod_cast Nat.le_succ _
 have tw:((((n:ℕ):ℝ≥0)⁻¹ :ℝ))=(n:ℝ)⁻¹:=by
  norm_cast
 rw[tw]
 rw[←ἱ,ἲ hn]
 calc
  D≤(n:ℝ)/(2*pi):=
   (ἇ Af).2 (by nlinarith[Ἆ])
  _=(2*pi)⁻¹ *(n:ℝ):=by
   field_simp
lemma sw (D:ℝ) (d q:ℕ)
  (hd:(d:ℝ)≤D) (hq:0<q) :
  4*pi*(d:ℝ) *
    (((((q*a6 D:ℕ):ℝ≥0)⁻¹ :ℝ))) ≤
   2/(q:ℝ):=by
 have hs := gf D
 have Qa:(0:ℝ)<a6 D:=by exact_mod_cast hs
 have Jd:(0:ℝ)<q:=by exact_mod_cast hq
 have dc:D*((a6 D:ℝ)⁻¹) ≤
   (2*pi)⁻¹:=by
  have h:=jc D
  have tw:((((a6 D:ℕ):ℝ≥0)⁻¹ :ℝ)) =
    (a6 D:ℝ)⁻¹:=by norm_cast
  simpa[tw] using h
 have NX:(d:ℝ)*((a6 D:ℝ)⁻¹) ≤
   (2*pi)⁻¹:=by
  calc
   _ ≤
     D*((a6 D:ℝ)⁻¹):=by gcongr
   _≤_:=dc
 have tw:(((((q*a6 D:ℕ):ℝ≥0)⁻¹ :ℝ))) =
   ((q:ℝ)*(a6 D:ℝ))⁻¹:=by
  norm_cast
 rw[tw,mul_inv]
 calc
  _
                          =
    (q:ℝ)⁻¹ *
     (4*pi*((d:ℝ)*(a6 D:ℝ)⁻¹)):=by ring
  _≤(q:ℝ)⁻¹ *(4*pi*(2*pi)⁻¹):=by gcongr
  _=2/(q:ℝ):=by
   field_simp
   ring
omit [Β G] [Δ G] in
lemma pW [Finite G]
  [MeasurableSpace G] [Α G]
  (F P:G→ℂ) (t:G) {delta E:ℝ}
  (cu:(aJ (∞) (P-F))≤delta)
  (jl:(aJ (∞) (τ t P-P))≤E) :
  (aJ (∞) (τ t F-F))≤2*delta+E:=by
 have jx :
   (aJ (∞) (τ t F-F))≤(aJ (∞) (τ t F-τ t P))+(aJ (∞) (τ t P-F)):=
  er le_top
 have uh :
   (aJ (∞) (τ t P-F))≤(aJ (∞) (τ t P-P))+(aJ (∞) (P-F)):=
  er le_top
 calc
  (aJ (∞) (τ t F-F))≤(aJ (∞) (τ t F-τ t P))+(aJ (∞) (τ t P-F)):=jx
  _≤(aJ (∞) (τ t F-τ t P)) +
     ((aJ (∞) (τ t P-P))+(aJ (∞) (P-F))):=by gcongr
  _=(aJ (∞) (F-P))+((aJ (∞) (τ t P-P))+(aJ (∞) (P-F))):=by
   have J0:τ t F-τ t P=τ t (F-P):=by rfl
   rw[J0,jY]
  _≤delta+(E+delta):=by
   gcongr
   simpa[r6] using cu
  _=2*delta+E:=by ring
omit [Β G] in
lemma kn
  (C:ay.aj G) (td:C.a1)
  (Q Κ:Finset (Ε G ℂ)) (Ρ:ℝ≥0)
  (m:ℕ) (hm:0< m) (X:Finset G)
  (Ἵ:X⊆(C.ai Ρ).Η)
  (Ὣ:Ρ+Ρ ≤
   1/(100*(max C.Ι 1:ℕ):ℝ≥0))
  (ø:(Κ.card:ℝ)*((m:ℝ≥0)⁻¹ :ℝ) ≤
   (2*pi)⁻¹)
  (ᾍ: ∀ psi∈Q, ∃ z∈Κ.addSpan,
   ∃ s∈ay.c5.cj C.Η (1/2),psi=z+s) :
  let D:=ay.jm.cD C Κ
   (Ρ+Ρ) (m:ℝ≥0)⁻¹
  D.Ι≤C.Ι+Κ.card ∧
   D.Η⊆(C.ai (Ρ+Ρ)).Η ∧
   X.card≤ m^Κ.card*D.Η.card ∧
   ∀ t∈D.Η, ∀ psi∈Q,
    ‖1-psi t‖ ≤
     4*pi*((Κ.card:ℝ)*((m:ℝ≥0)⁻¹ :ℝ)) +
      400*((max C.Ι 1:ℕ):ℝ)*(Ρ+Ρ:ℝ≥0):=by
 classical
 let D:=ay.jm.cD C Κ
  (Ρ+Ρ) (m:ℝ≥0)⁻¹
 have tB:=ay.qC.tz
  C Κ Ρ hm X Ἵ
 refine ⟨tB.1,tB.2.1,tB.2.2, ?_⟩
 intro t ht psi Ê
 simpa only[D,SE,S9] using
  (ay.jm.iY
   C td Ὣ ø ᾍ t ht psi Ê)
omit [Β G] in
lemma kv (D:ay.aj G) :
  ∃ R:ay.aj G,
   R.a1∧R.Ι=D.Ι∧R.Η⊆D.Η ∧
    D.Η.card≤4^D.Ι*R.Η.card:=by
 classical
 obtain ⟨Φ,ᾐ,lj,Ô⟩:=D.eP
 refine ⟨D.ai Φ,Ô,by simp, ?_, ?_⟩
 ·simpa only[ay.aj.oG] using
   (ay.aj.b5 (B:=D) lj)
 ·have dc:=ay.aj.de D
  have ἵ:(D.ai (1/2)).Η.card ≤
    (D.ai Φ).Η.card:=
   ὣ (ay.aj.b5 ᾐ)
  calc
   D.Η.card=(D.ai 1).Η.card:=by simp
   _≤4^D.Ι*(D.ai (1/2)).Η.card:=dc
   _≤4^D.Ι*(D.ai Φ).Η.card:=
    ὄ _ ἵ
omit [Β G] in
lemma gK
  (C:ay.aj G) (td:C.a1)
  (Q Κ:Finset (Ε G ℂ)) (Ρ:ℝ≥0)
  (m:ℕ) (hm:0< m) (X:Finset G)
  (Ἵ:X⊆(C.ai Ρ).Η)
  (Ὣ:Ρ+Ρ ≤
   1/(100*(max C.Ι 1:ℕ):ℝ≥0))
  (ø:(Κ.card:ℝ)*((m:ℝ≥0)⁻¹ :ℝ) ≤
   (2*pi)⁻¹)
  (ᾍ: ∀ psi∈Q, ∃ z∈Κ.addSpan,
   ∃ s∈ay.c5.cj C.Η (1/2),psi=z+s) :
  ∃ R:ay.aj G,
   R.a1∧R.Ι≤C.Ι+Κ.card ∧
   R.Η⊆(C.ai (Ρ+Ρ)).Η ∧
   X.card≤ m^Κ.card*(4^(C.Ι+Κ.card)*R.Η.card) ∧
   ∀ t∈R.Η, ∀ psi∈Q,
    ‖1-psi t‖ ≤
     4*pi*((Κ.card:ℝ)*((m:ℝ≥0)⁻¹ :ℝ)) +
      400*((max C.Ι 1:ℕ):ℝ)*(Ρ+Ρ:ℝ≥0):=by
 classical
 let D:=ay.jm.cD C Κ
  (Ρ+Ρ) (m:ℝ≥0)⁻¹
 have Ð:=kn
  C td Q Κ Ρ m hm X Ἵ Ὣ ø ᾍ
 obtain ⟨R,qk,Ῥ,Hg,ya⟩:=kv D
 refine ⟨R,qk,Ῥ.le.trans Ð.1,Hg.trans Ð.2.1, ?_, ?_⟩
 ·calc
   X.card≤ m^Κ.card*D.Η.card:=Ð.2.2.1
   _≤ m^Κ.card*(4^D.Ι*R.Η.card):=
    ὄ _ ya
   _≤ m^Κ.card*(4^(C.Ι+Κ.card)*R.Η.card):=by
    have hpow:4^D.Ι≤4^(C.Ι+Κ.card):=
     QR (by omega) Ð.1
    exact ὄ _ (QQ _ hpow)
 ·intro t ht psi Ê
  exact Ð.2.2.2 t (Hg ht) psi Ê
omit [Β G] in
lemma iD
  (B:ay.aj G) (Ὺ:B.a1)
  (X:Finset G) (Ἵ:X.Nonempty) (ud:X⊆B.Η)
  (Ο:ℝ) (ò:0<Ο) (Ρ:ℝ≥0) (m:ℕ) (hm:0< m)
  (Ὣ:Ρ+Ρ ≤
   1/(100*(max B.Ι 1:ℕ):ℝ≥0))
  (ø :
   ay.aI.bf B X Ο *
     (((m:ℝ≥0)⁻¹ :ℝ))≤(2*pi)⁻¹) :
  ∃ Φ:ℝ≥0, ∃ C:ay.aj G,
   ∃ Κ:Finset (Ε G ℂ), ∃ R:ay.aj G,
    1/2≤Φ∧Φ≤1 ∧
    C=B.ai (Φ *
     ay.aI.cJ B X Ο) ∧
    C.a1 ∧
    (Κ.card:ℝ) ≤
     ay.aI.bf B X Ο ∧
    Κ⊆ay.c5.cj X Ο ∧
    R.a1∧R.Ι≤B.Ι+Κ.card ∧
    R.Η⊆(C.ai (Ρ+Ρ)).Η ∧
    (C.ai Ρ).Η.card ≤
     m^Κ.card*(4^(B.Ι+Κ.card)*R.Η.card) ∧
    ∀ t∈R.Η,
     ∀ psi∈ay.c5.cj X Ο,
      ‖1-psi t‖ ≤
       4*pi *
         (Κ.card:ℝ)*(((m:ℝ≥0)⁻¹ :ℝ)) +
        400*((max B.Ι 1:ℕ):ℝ) *
         (Ρ+Ρ:ℝ≥0):=by
 classical
 obtain ⟨Φ,C,Κ,ᾐ,lj,Ã,td,
   ᾤ,u1,ᾍ⟩:=
  ay.aI.mY
   B Ὺ X Ἵ ud Ο ò
 have yb:C.Ι=B.Ι:=by simp[Ã]
 have HZ:Ρ+Ρ ≤
   1/(100*(max C.Ι 1:ℕ):ℝ≥0):=by
  simpa[yb] using Ὣ
 have hinv:0≤(((m:ℝ≥0)⁻¹ :ℝ)):=by positivity
 have BP :
   (Κ.card:ℝ)*(((m:ℝ≥0)⁻¹ :ℝ)) ≤
    (2*pi)⁻¹:=
  (ἂ ᾤ hinv).trans ø
 obtain ⟨R,qk,Ῥ,yc,vZ,Ᾰ⟩:=
  gK
   C td (ay.c5.cj X Ο) Κ Ρ m hm
    (C.ai Ρ).Η (λ _ hx↦hx) HZ BP ᾍ
 refine ⟨Φ,C,Κ,R,ᾐ,lj,Ã,td,
  ᾤ,u1,qk, ?_,yc, ?_, ?_⟩
 ·simpa[yb] using Ῥ
 ·simpa[yb] using vZ
 ·intro t ht psi Ê
  simpa only[yb,à] using Ᾰ t ht psi Ê
lemma fk
  [MeasurableSpace G] [Α G]
  {A:Finset G} (ξ:A.Nonempty)
  (delta:ℝ) (cu:0<delta) (m:ℕ) (hm:m≠0)
  (M L:Finset G) (ἄ:M.Nonempty) (hL:L.Nonempty)
  (bl:ay.aj G) (sx:bl.a1)
  (Ρ:ℝ≥0)
  (dy:Ρ+Ρ ≤
   1/(100*(max bl.Ι 1:ℕ):ℝ≥0))
  (ç:ℕ) (pX:0<ç) :
  let q:=⌈1+log (min 1 ((L.card:ℝ)/M.card))⁻¹⌉₊
  let wK:=ay.ᾨ q
   ((delta/m)/exp 1)
  ∃ (T X:Finset G) (z:G) (Φ:ℝ≥0),
   ∃ (fl:ay.aj G)
    (Κ:Finset (Ε G ℂ)) (R:ay.aj G),
   T⊆bl.Η∧z∈T∧X= -z+ᵥ T∧X.Nonempty ∧
   (((A.card:ℝ)^wK/2*bl.Η.card) /
     ((A+bl.Η).card:ℝ)^wK≤T.card) ∧
   1/2≤Φ∧Φ≤1 ∧
   fl=bl.ai (Φ *
    ay.aI.cJ bl T (1/2)) ∧
   fl.a1 ∧
   (Κ.card:ℝ) ≤
    ay.aI.bf bl T (1/2) ∧
   Κ⊆ay.c5.cj T (1/2) ∧
   R.a1∧R.Ι≤bl.Ι+Κ.card ∧
   R.Η⊆(fl.ai (Ρ+Ρ)).Η ∧
   (fl.ai Ρ).Η.card ≤
    (ç*a6
       (ay.aI.bf bl T (1/2))) ^
      Κ.card *
     (4^(bl.Ι+Κ.card)*R.Η.card) ∧
   ∀ t∈R.Η,
    (aJ (∞) (τ t ((Χ (((Χ ((@mu (ℂ) _ _) A) (((indicator M λ _↦(1:_)):G→ℂ))))) (mu L))) -
      ((Χ (((Χ ((@mu (ℂ) _ _) A) (((indicator M λ _↦(1:_)):G→ℂ))))) (mu L))))) ≤
     2*delta +
      (4*pi *
         (Κ.card:ℝ) *
          ((((ç*a6
           (ay.aI.bf
            bl T (1/2)):ℕ):ℝ≥0)⁻¹ :ℝ)) +
        400*((max bl.Ι 1:ℕ):ℝ) *
         (Ρ+Ρ:ℝ≥0) +
        2*(1/2:ℝ)^m) *
       Real.sqrt ((M.card:ℝ)/L.card):=by
 classical
 let q:=⌈1+log (min 1 ((L.card:ℝ)/M.card))⁻¹⌉₊
 let wK:=ay.ᾨ q
  ((delta/m)/exp 1)
 obtain ⟨T,z,ui,ML,ᾉ,_hXdiff,nk,Ᾱ⟩:=
  ay.mX
   ξ bl.aE delta cu m hm M L ἄ hL
 let X := -z+ᵥ T
 have ῢ:T.Nonempty:=⟨z,ML⟩
 let dim:=ay.aI.bf bl T (1/2)
 let n:=ç*a6 dim
 have hn := Ὑ pX (gf dim)
 have ø:dim*(((n:ℝ≥0)⁻¹ :ℝ))≤(2*pi)⁻¹:=by
  have ί:0≤dim:=by
   have nk:(0:ℝ)<T.card:=by exact_mod_cast ῢ.card_pos
   have ch:(T.card:ℝ)≤bl.Η.card:=by
    exact_mod_cast ὣ ui
   have ἕ:(1:ℝ)≤2*(bl.Η.card:ℝ)/T.card:=by
    rw[ἇ nk]
    nlinarith
   have ei :=
    Ἲ ἕ
   dsimp[dim,ay.aI.bf]
   positivity
  have dc :=
   jc dim
  have Dj:a6 dim≤n:=by
   dsimp[n]
   exact T9 _ pX
  have hinv:(((n:ℝ≥0)⁻¹ :ℝ)) ≤
    ((((a6 dim:ℕ):ℝ≥0)⁻¹ :ℝ)):=by
   have EG:(0:ℝ≥0) <
     (a6 dim:ℕ):=by
    exact_mod_cast gf dim
   have J1:(0:ℝ≥0)<n:=by exact_mod_cast hn
   have BQ:(a6 dim:ℝ≥0)≤n:=by
    exact_mod_cast Dj
   exact_mod_cast(RJ J1 EG).2 BQ
  exact(Å hinv ί).trans dc
 obtain ⟨Φ,fl,Κ,R,ᾐ,lj,ᾶ,AT,
   ᾤ,u1,qk,Ῥ,yc,vZ,Ᾰ⟩:=
  iD
   bl sx T ῢ ui (1/2) (by norm_num)
    Ρ n hn dy (by simpa[dim] using ø)
 let F:G→ℂ:=(Χ (((Χ (mu A) ((indicator M λ _↦(1:_)))))) (mu L))
 let P:G→ℂ:=(Χ ((ἶ (mu X) m)) F)
 let phase:ℝ:=
  4*pi*(Κ.card:ℝ)*(((n:ℝ≥0)⁻¹ :ℝ)) +
   400*((max bl.Ι 1:ℕ):ℝ)*(Ρ+Ρ:ℝ≥0)
 have H3:0≤phase:=by
  dsimp[phase]
  positivity
 have MM:(ð 1 (π F))≤Real.sqrt ((M.card:ℝ)/L.card):=by
  simpa[F] using sv A M L ξ hL
 have Gc:(aJ (∞) (P-F))≤delta:=by
  simpa[P,F,X] using Ᾱ
 have jl: ∀ t∈R.Η,
   (aJ (∞) (τ t F-F)) ≤
    2*delta+(phase+2*(1/2:ℝ)^m) *
     Real.sqrt ((M.card:ℝ)/L.card):=by
  intro t ht
  have ὼ:= oR X (by simpa[X] using ᾉ) m F
   (1/2) phase (by norm_num) H3 t (λ psi Ê ↦
    Ᾰ t ht psi
     (ib
      T ῢ (-z) psi (by simpa[X] using Ê)))
  have OV:(aJ (∞) (τ t P-P)) ≤
    (phase+2*(1/2:ℝ)^m) *
     Real.sqrt ((M.card:ℝ)/L.card):=by
   calc
    _ ≤
      (phase+2*(1/2:ℝ)^m)*(ð 1 (π F)):=by
       simpa[P] using ὼ
    _≤(phase+2*(1/2:ℝ)^m) *
      Real.sqrt ((M.card:ℝ)/L.card):=by
       gcongr
  exact pW F P t Gc OV
 refine ⟨T,X,z,Φ,fl,Κ,R,ui,ML,rfl,
  by simpa[X] using ᾉ, ?_,ᾐ,lj, ?_,AT,
  ?_,u1,qk,Ῥ,yc, ?_, ?_⟩
 ·simpa[q,wK] using nk
 ·simpa using ᾶ
 ·simpa[dim] using ᾤ
 ·simpa[n,dim] using vZ
 ·intro t ht
  simpa[F,phase,n,dim,à] using jl t ht
noncomputable def aS (A:Finset G) (x:G):ℝ:=
 if x∈A then (A.card:ℝ)⁻¹ else 0
noncomputable def d9 (f g:G→ℝ) (x:G):ℝ:=
 ∑ y:G,f y*g (x-y)
noncomputable def a2 (f g:G→ℝ) (x:G):ℝ:=
 ∑ y:G,f y*g (y-x)
noncomputable def bC (f g:G→ℝ):ℝ:=
 ∑ x:G,f x*g x
noncomputable def bJ (A:Finset G) (x:G):ℝ:=
 if x∈A then 1 else 0
noncomputable def bW
  (aX a3 S:Finset G) (t:G):ℝ:=
 ∑ a₁:G, ∑ a₂:G,
  bJ aX a₁*bJ a3 a₂*bJ S (t+a₁-a₂)
lemma d7
  {aX a3:Finset G} (ἔ:aX.Nonempty) (Ἥ:a3.Nonempty)
  (S:Finset G) (t:G) :
  bC
    (λ x↦a2 (aS aX)
     (aS a3) (x-t))
    (bJ S) =
   bW aX a3 S t/(aX.card*a3.card:ℝ):=by
 classical
 simp only[bC,a2,aS,
  bW]
 simp_rw[Ἕ]
 rw[sum_comm]
 calc
  _
    = ((#aX:ℝ)⁻¹ *(#a3:ℝ)⁻¹) *
      ∑ y:G, ∑ x:G,
       bJ aX y*bJ a3 (y-(x-t)) *
        bJ S x:=by
     rw[á]
     apply sum_congr rfl
     intro y _
     rw[á]
     apply sum_congr rfl
     intro x _
     simp only[bJ]
     split_ifs<;>ring
  _=((#aX:ℝ)⁻¹ *(#a3:ℝ)⁻¹) *
      ∑ a₁:G, ∑ a₂:G,
       bJ aX a₁*bJ a3 a₂ *
        bJ S (t+a₁-a₂):=by
     congr 1
     apply sum_congr rfl
     intro a₁ _
     refine(ἐ (Equiv.subLeft (t+a₁)) _ _ λ a₂↦ ?_).symm
     simp only[SX]
     congr 2; abel_nf
  _=(∑ a₁:G, ∑ a₂:G,
      bJ aX a₁*bJ a3 a₂ *
       bJ S (t+a₁-a₂)) /
     (aX.card*a3.card:ℝ):=by
     rw[Ri]
     field_simp[ἔ.card_ne_zero,Ἥ.card_ne_zero]
lemma ja
  {D:Finset G} (_hD:D.Nonempty) (f:G→ℝ) (x:G) :
  d9 (aS D) f x =
   (∑ t∈D,f (x-t))/D.card:=by
 classical
 simp only[d9,aS]
 rw[←sum_subset (s₁:=D) (s₂:=univ)]
 ·rw[Ri,á]
  apply sum_congr rfl
  intro t ht
  rw[ή ht]
 ·simp
 ·intro t _ ht
  simp[ht]
lemma mZ
  {D:Finset G} (Ð:D.Nonempty)
  (f h:G→ℝ) {eps:ℝ}
  (jl: ∀ t∈D,
   |bC (λ x↦f (x-t)) h-bC f h| ≤eps) :
  |bC (d9 (aS D) f) h -
    bC f h| ≤eps:=by
 classical
 have ch:(0:ℝ)<D.card:=by exact_mod_cast Ð.card_pos
 have Ᾱ :
   bC (d9 (aS D) f) h =
    (∑ t∈D,bC (λ x↦f (x-t)) h)/D.card:=by
  simp only[bC]
  simp_rw[ja Ð]
  simp_rw[div_mul_eq_mul_div,sum_div,Ἕ]
  rw[sum_comm]
  simp_rw[←sum_div]
 rw[Ᾱ]
 have sy :
   (∑ t∈D,bC (λ x↦f (x-t)) h)/D.card-bC f h =
    (∑ t∈D,
     (bC (λ x↦f (x-t)) h-bC f h))/D.card:=by
  rw[QJ,Tq,ᾚ]
  field_simp[ch.ne']
 rw[sy,TE,RT ch]
 apply(ἲ ch).2
 calc
  |∑ t∈D,(bC (λ x↦f (x-t)) h-bC f h)|
    ≤ ∑ t∈D,
      |bC (λ x↦f (x-t)) h-bC f h|:=
     abs_sum_le_sum_abs (λ t ↦
      bC (λ x↦f (x-t)) h-bC f h) D
  _≤ ∑ _t∈D,eps:=sum_le_sum λ t ht↦jl t ht
  _=eps*D.card:=by simp[ä]
lemma ji
  {D:aj G} {aX a3 S:Finset G} {eps:ℝ}
  (ἔ:aX.Nonempty) (Ἥ:a3.Nonempty)
  (uj: ∀ t∈D.Η,
   |bW aX a3 S t-bW aX a3 S 0| ≤
    eps*(aX.card:ℝ)*a3.card) :
  |bC
     (d9 (aS D.Η)
      (a2
       (aS aX) (aS a3)))
     (bJ S) -
    bC
     (a2
      (aS aX) (aS a3))
     (bJ S)| ≤eps:=by
 classical
 apply mZ D.aE
 intro t ht
 have hzero:=d7 ἔ Ἥ S (0:G)
 simp only[sub_zero] at hzero
 rw[d7 ἔ Ἥ,hzero]
 rw[←UT,TE]
 have ch:(0:ℝ)<(aX.card:ℝ)*a3.card:=
  Ἃ (by exact_mod_cast ἔ.card_pos) (by exact_mod_cast Ἥ.card_pos)
 rw[RT ch]
 apply(ἲ ch).2
 simpa[à] using uj t ht
end ay.ag
end
section
open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ComplexOrder ENNReal NNReal Pointwise
namespace ay
namespace aN
noncomputable section
variable {G:Type*} [Δ G] [Β G] [Γ G]
 [MeasurableSpace G] [Α G]
def dU (D E:Finset G):G→ℝ≥0:=
 (Χ ((@mu (ℝ≥0) _ _) D) (mu E))
def bh (D E:Finset G):G→ℝ≥0:=
 (al (dU D E) (dU D E))
omit [Α G] [MeasurableSpace G] in
lemma wY {D E:Finset G} (Ð:D.Nonempty) (Þ:E.Nonempty) :
  ∑ x:G,dU D E x=1:=by
 simp[dU,uM,Ð,Þ]
omit [Α G] [MeasurableSpace G] in
lemma i7 {D E:Finset G} (Ð:D.Nonempty) (Þ:E.Nonempty) :
  ∑ x:G,bh D E x=1:=by
 simp[bh,jJ,wY Ð Þ]
omit [Α G] [MeasurableSpace G] in
lemma gS (D E:Finset G) :
  0≤bh D E:=by
 simp[bh]
omit [Α G] [MeasurableSpace G] in
lemma oo (D E:Finset G) :
  (al (((↑) ∘ dU D E:G→ℂ)) (((↑) ∘ dU D E))) =
   (↑) ∘ bh D E:=by
 let b:=dU D E
 calc
  (al (((↑) ∘ b:G→ℂ)) (((↑) ∘ b))) =
    (↑) ∘ ((al (((↑) ∘ b:G→ℝ)) (((↑) ∘ b)))):=by
     exact(Complex.pB ((↑) ∘ b) ((↑) ∘ b)).symm
  _=(↑) ∘ ((al b b)):=by
   rw[←NNReal.gF]
   rfl
  _=(↑) ∘ bh D E:=by
   funext x
   rfl
omit [Γ G] [Β G] in
lemma dN (w:G→ℝ≥0) (f:G→ℝ)
  {p:ℕ} (hp:0<p) :
  an.aM ((↑) ∘ w) f p=(b0 p w f):=by
 rw[an.dG _ _ hp]
 rw[lu (by exact_mod_cast hp.ne') (by simp)]
 congr 1
 ·apply Ò rfl
  intro x _
  simp only[RG,ᾞ,norm_eq_abs,
   Rh,Ue]
  rw[RN]
 ·simp[ῆ]
omit [Γ G] [Β G] in
lemma gx
  (w:G→ℝ≥0) (f:G→ℝ) (c:ℝ) (hc:0≤c)
  {p:ℕ} (hp:0<p) :
  an.aM ((↑) ∘ w) (c•f) p =
   c*an.aM ((↑) ∘ w) f p:=by
 classical
 rw[dN w _ hp,dN w _ hp,
  Ah]
 simp[ᾮ,ἳ hc]
omit [Γ G] [Β G] in
lemma pY
  (w:G→ℝ≥0) (f g:G→ℝ) {p:ℕ} (hp:1≤p) :
  an.aM ((↑) ∘ w) f p ≤
   an.aM ((↑) ∘ w) (f+g) p +
    an.aM ((↑) ∘ w) g p:=by
 classical
 simp_rw[dN w _ (U5 hp)]
 exact qX (by exact_mod_cast hp) w f g
omit [Γ G] [Β G] in
lemma qF
  {w:G→ℝ≥0} (hw: ∑ x:G,w x=1)
  {f:G→ℝ} {C:ℝ} (Ã:0≤C) {p:ℕ} (hp:0<p)
  (hf: ∀ x, |f x| ≤C) :
  an.aM ((↑) ∘ w) f p≤C:=by
 classical
 rw[dN w f hp]
 calc
  _ ≤(b0 p w ((λ _:G↦C))):=by
   apply lpNorm_mono_real .of_discrete
   simpa[ἳ Ã] using hf
  _=C:=by
   rw[lu (by exact_mod_cast hp.ne') (by simp)]
   simp only[Ue]
   have hsum: ∑ x:G,(w x:ℝ)=1:=by exact_mod_cast hw
   have heq: ∑ x:G,(w x:ℝ)* ‖C‖ ^(p:ℝ)=C^p:=by
    rw[norm_eq_abs,ἳ Ã,RN, ←Ἕ,
     hsum,ἃ]
   rw[show(∑ x:G,w x• ‖C‖ ^(p:ℝ))=C^p by
    simpa[RG] using heq]
   exact Sc Ã hp.ne'
omit [Γ G] [Β G] in
lemma lz
  {w:G→ℝ≥0} (hw: ∑ x:G,w x=1)
  {f:G→ℝ} {C:ℝ} (Ã:0≤C) {p:ℕ} (hp:0<p)
  (hf: ∀ x,w x≠0→ |f x| ≤C) :
  an.aM ((↑) ∘ w) f p≤C:=by
 classical
 let g:G→ℝ:=λ x↦if w x=0 then 0 else f x
 have ᾷ:an.aM ((↑) ∘ w) f p =
   an.aM ((↑) ∘ w) g p:=by
  rw[an.dG _ _ hp,
   an.dG _ _ hp]
  apply è (λ z:ℝ↦z^(1/(p:ℝ)))
  unfold È
  apply Ò rfl
  intro x _
  by_cases hx:w x=0<;>simp[g,hx]
 rw[ᾷ]
 apply qF hw Ã hp
 intro x
 by_cases hx:w x=0
 ·simp[g,hx,Ã]
 ·simpa[g,hx] using hf x hx
omit [Γ G] [Α G] [Δ G] [MeasurableSpace G] in
lemma eQ (S:Finset G) :
  (@mu (ℝ) _ _) S=af S:=by
 funext x
 by_cases hx:x∈S<;>simp[υ,af,hx]
omit [Α G] [MeasurableSpace G] in
lemma eZ
  {B:aj G} (Ô:B.a1)
  {A:Finset G} (ξ:A.Nonempty) (zq:A⊆B.Η)
  {Ρ:ℝ≥0}
  (dy:Ρ≤1/(100*(max B.Ι 1:ℕ):ℝ≥0))
  {t:G} (ht:t∈(B.ai Ρ).Η) :
  |((al ((@mu (ℝ) _ _) A) (mu B.Η))) t-(B.Η.card:ℝ)⁻¹| ≤
   (A.card:ℝ)⁻¹ *
    (200*((max B.Ι 1:ℕ):ℝ)*(Ρ:ℝ)):=by
 have É := B.aE
 have dc :
   ∑ x:G,(@mu (ℝ) _ _) A x*mu B.Η x =
    (B.Η.card:ℝ)⁻¹:=by
  calc
   _ =
     ∑ x:G,(@mu (ℝ) _ _) A x*(B.Η.card:ℝ)⁻¹:=by
    apply Ò rfl
    intro x _
    by_cases hx:x∈A
    ·rw[υ,υ]
     simp[hx,zq hx]
    ·simp[υ,hx]
   _=(B.Η.card:ℝ)⁻¹:=by
    rw[←Ἕ,ᾢ ℝ ξ,ἃ]
 have kE :
   ∑ x:G, |(@mu (ℝ) _ _) B.Η (x-t)-mu B.Η x| ≤
    200*((max B.Ι 1:ℕ):ℝ)*(Ρ:ℝ):=by
  simpa only[eQ] using
   B.cN Ô dy ht
 rw[eL]
 simp only[Rc,star_trivial]
 rw[←dc]
 rw[←QJ]
 have Dk :
   (∑ x:G,((@mu (ℝ) _ _) A x*mu B.Η (x-t) -
    mu A x*mu B.Η x)) =
   ∑ x:G,(@mu (ℝ) _ _) A x *
    (mu B.Η (x-t)-mu B.Η x):=by
  apply Ò rfl
  intro x _
  ring
 rw[Dk]
 calc
  _
                                         ≤
    ∑ x:G, |(@mu (ℝ) _ _) A x *
     (mu B.Η (x-t)-mu B.Η x)|:=
   TQ _ _
  _= ∑ x:G,(@mu (ℝ) _ _) A x *
     |mu B.Η (x-t)-mu B.Η x|:=by
   apply Ò rfl
   intro x _
   have LI:0≤(@mu (ℝ) _ _) A x:=by
    rw[υ]
    positivity
   rw[SU,ἳ LI]
  _≤ ∑ x:G,(A.card:ℝ)⁻¹ *
     |(@mu (ℝ) _ _) B.Η (x-t)-mu B.Η x|:=by
   apply ᾯ
   intro x _
   apply ἂ _ (ᾝ _)
   rw[υ]
   split_ifs<;>simp
  _=(A.card:ℝ)⁻¹ *
     ∑ x:G, |(@mu (ℝ) _ _) B.Η (x-t)-mu B.Η x|:=by
   rw[á]
  _≤(A.card:ℝ)⁻¹ *
     (200*((max B.Ι 1:ℕ):ℝ)*(Ρ:ℝ)):=
   Å kE (by positivity)
omit [Α G] [MeasurableSpace G] in
lemma ko
  {B:aj G} (Ô:B.a1)
  {A:Finset G} (ξ:A.Nonempty) (zq:A⊆B.Η)
  {Ρ:ℝ≥0}
  (dy:Ρ≤1/(100*(max B.Ι 1:ℕ):ℝ≥0))
  {t:G} (ht:t∈(B.ai Ρ).Η) :
  |((al ((@mu (ℝ) _ _) A) (mu A))) t -
    ((B.Η.card:ℝ)⁻¹ +
     ((al (((@mu (ℝ) _ _) A-mu B.Η)) ((mu A-mu B.Η)))) t)| ≤
   2*((A.card:ℝ)⁻¹ *
     (200*((max B.Ι 1:ℕ):ℝ)*(Ρ:ℝ))) +
    (B.Η.card:ℝ)⁻¹ *
     (200*((max B.Ι 1:ℕ):ℝ)*(Ρ:ℝ)):=by
 let m:ℝ:=(B.Η.card:ℝ)⁻¹
 let eA:ℝ:=(A.card:ℝ)⁻¹ *
  (200*((max B.Ι 1:ℕ):ℝ)*(Ρ:ℝ))
 let eB:ℝ:=(B.Η.card:ℝ)⁻¹ *
  (200*((max B.Ι 1:ℕ):ℝ)*(Ρ:ℝ))
 have PU:=eZ Ô ξ zq dy ht
 have H4:=eZ Ô ξ zq dy
  (aj.ec.mpr ht)
 have Nk :
   |((al ((@mu (ℝ) _ _) B.Η) (mu A))) t-m| ≤eA:=by
  have Nl:((al ((@mu (ℝ) _ _) B.Η) (mu A))) t =
    ((al (mu A) (mu B.Η))) (-t):=by
   have h:=wT ((@mu (ℝ) _ _) A) ((@mu (ℝ) _ _) B.Η) t
   simpa using h.symm
  simpa[m,eA,Nl] using H4
 have PG:=eZ Ô
  B.aE (λ _ h↦h) dy ht
 have hsum :
   |(((al ((@mu (ℝ) _ _) A) (mu B.Η))) t-m) +
    (((al (mu B.Η) (mu A))) t-m) -
    (((al (mu B.Η) (mu B.Η))) t-m)| ≤
     2*eA+eB:=by
  calc
   _
                                                 ≤
     |((al ((@mu (ℝ) _ _) A) (mu B.Η))) t-m| +
     |((al (mu B.Η) (mu A))) t-m| +
     |((al (mu B.Η) (mu B.Η))) t-m|:=by
      have Ὂ:=abs_sub
       ((((al ((@mu (ℝ) _ _) A) (mu B.Η))) t-m) +
        (((al (mu B.Η) (mu A))) t-m))
       (((al (mu B.Η) (mu B.Η))) t-m)
      have xt:=UP
       (((al ((@mu (ℝ) _ _) A) (mu B.Η))) t-m)
       (((al (mu B.Η) (mu A))) t-m)
      linarith
   _≤eA+eA+eB:=by gcongr
   _=2*eA+eB:=by ring
 have H5 :
   ((al ((@mu (ℝ) _ _) A) (mu A))) t -
     (m+((al ((mu A-mu B.Η)) ((mu A-mu B.Η)))) t) =
    (((al (mu A) (mu B.Η))) t-m) +
    (((al (mu B.Η) (mu A))) t-m) -
    (((al (mu B.Η) (mu B.Η))) t-m):=by
  simp only[BB,BA,Rw]
  ring
 simpa[m,eA,eB,H5] using hsum
omit [Α G] [MeasurableSpace G] in
lemma oq
  (A K:Finset G) :
  (al (((Real.sqrt (K.card:ℝ):ℂ) •
     ((↑) ∘ ((@mu (ℝ) _ _) A-mu K):G→ℂ))) (((Real.sqrt (K.card:ℝ):ℂ) •
     ((↑) ∘ ((@mu (ℝ) _ _) A-mu K):G→ℂ)))) =
   (↑) ∘ ((K.card:ℝ) •
    ((al (((@mu (ℝ) _ _) A-mu K)) ((mu A-mu K))))):=by
 rw[oB,oC]
 rw[←Complex.pB]
 funext x
 simp only[RD,Rh,ᾞ]
 rw[show star (↑(Real.sqrt (K.card:ℝ)):ℂ) =
   ↑(Real.sqrt (K.card:ℝ)) by simp]
 rw[←à]
 norm_cast
 rw[←TI,Uf (by positivity:(0:ℝ)≤K.card)]
lemma uk
  {B:aj G} (Ô:B.a1)
  {A:Finset G} (ξ:A.Nonempty) (zq:A⊆B.Η)
  {D E:Finset G} (Ð:D.Nonempty) (Þ:E.Nonempty)
  {Ρ:ℝ≥0}
  (dy:Ρ≤1/(100*(max B.Ι 1:ℕ):ℝ≥0))
  (ῶ: ∀ t,bh D E t≠0 →
   t∈(B.ai Ρ).Η)
  {Μ:ℝ} (Ἷ:0<Μ) (oV:Μ≤1)
  (ú :
   2*((A.card:ℝ)⁻¹ *
     (200*((max B.Ι 1:ℕ):ℝ)*(Ρ:ℝ))) +
    (B.Η.card:ℝ)⁻¹ *
     (200*((max B.Ι 1:ℕ):ℝ)*(Ρ:ℝ)) ≤
    Μ/8*(B.Η.card:ℝ)⁻¹)
  {p:ℕ} (hp:0<p)
  (Ὤ :
   Μ*(B.Η.card:ℝ)⁻¹ /2 <
    an.aM
     ((↑) ∘ bh D E)
     ((al (((@mu (ℝ) _ _) A-mu B.Η)) ((mu A-mu B.Η))))
     (an.bS p)) :
  ∃ r:ℕ,0<r∧Even r ∧
   r≤an.cz Μ p ∧
   (1+Μ/8)*(B.Η.card:ℝ)⁻¹ ≤
    an.aM
     ((↑) ∘ bh D E) ((al ((@mu (ℝ) _ _) A) (mu A))) r:=by
 let K:=B.Η
 let nu:=bh D E
 let balanced:G→ℝ:=(@mu (ℝ) _ _) A-mu K
 let Ἁ:G→ℝ:=(al balanced balanced)
 let positive:G→ℝ:=(al ((@mu (ℝ) _ _) A) (mu A))
 let main:ℝ:=(K.card:ℝ)⁻¹
 let f:G→ℝ:=(K.card:ℝ)•Ἁ
 let Ά := main•(f+1)
 have æ := B.aE
 have yd:(0:ℝ)<K.card:=by exact_mod_cast æ.card_pos
 have Ἆ:0< main:=by simp[main,yd]
 have ft := i7 Ð Þ
 have wL:an.cw ((↑) ∘ nu):=
  ⟨λ x↦by exact_mod_cast(show 0≤nu x by exact gS D E x),
   by simpa using è (λ z:ℝ≥0↦(z:ℝ)) ft⟩
 have LJ :
   (al (((Real.sqrt (K.card:ℝ):ℂ)•((↑) ∘ balanced:G→ℂ))) (((Real.sqrt (K.card:ℝ):ℂ)•((↑) ∘ balanced:G→ℂ)))) =
    (↑) ∘ f:=by
  simpa[K,balanced,Ἁ,f] using oq A K
 have J2 :
   (al (((↑) ∘ dU D E:G→ℂ)) (((↑) ∘ dU D E)))=(↑) ∘ nu:=by
  simpa[nu] using oo D E
 have Ao: ∀ k:ℕ,0≤ iP ((↑) ∘ nu) f k:=by
  intro k
  have h:=rC LJ J2 k
  simpa[iP,wInner_one_eq_sum,Sb,ä] using h
 have MN:(K.card:ℝ)*main=1:=by
  simp[main,Uq yd]
 have H6:Μ/2 <
   an.aM ((↑) ∘ nu) f
    (an.bS p):=by
  rw[show f=(K.card:ℝ)•Ἁ by rfl,
   gx nu Ἁ (K.card:ℝ) (by positivity)
    (by simp[an.bS,hp])]
  have NY:Μ*main/2 <
    an.aM ((↑) ∘ nu) Ἁ
     (an.bS p):=by
   simpa[K,nu,balanced,Ἁ,main] using Ὤ
  nlinarith
 let ῦ:=an.cF p
 have LK:0<ῦ:=by
  have:=an.fK hp
  omega
 have Gd:=an.js
  wL hp (f:=f)
 have EH :=
        H6.trans_le (by simpa[ῦ] using Gd)
 have AU:(Μ/2)^ῦ ≤
   È ((↑) ∘ nu) f ῦ:=by
  calc
   _ ≤
     an.aM ((↑) ∘ nu) f ῦ^ῦ:=
    ἤ (by positivity) EH.le ῦ
   _=È ((↑) ∘ nu) f ῦ:=
    an.jr wL LK
 have Ý: ∀ x,Ά x=main*(1+f x):=by
  intro x
  simp[Ά,ᾞ,ῒ]
  ring
 obtain ⟨r,hr,At,yX,Dl⟩:=
  an.pQ wL
   (f:=f) (Ή:=Ά) (η:=Μ/2)
   (bo:=main) (by positivity) (by linarith) Ἆ
   (an.fK hp)
   (an.pP p) Ao AU Ý
 have J3:r≤an.cz Μ p:=by
  simpa[an.cz,ῦ] using yX
 have BR: ∀ x,nu x≠0→ |positive x-Ά x| ≤Μ/8*main:=by
  intro x hx
  have hb:=ko Ô ξ zq dy
   (ῶ x hx)
  have ye:Ά x=main+Ἁ x:=by
   simp only[smul_add,RM,RD,ᾞ,Rt,
    Ἣ,Ά,f]
   rw[←à,show main*(K.card:ℝ)=1 by nlinarith,ἃ]
   ring
  simpa[K,balanced,Ἁ,positive,main,ye] using hb.trans ú
 have EI :
   an.aM ((↑) ∘ nu) (positive-Ά) r ≤
    Μ/8*main:=by
  apply lz ft
   (å (by positivity) Ἆ.le) hr
  intro x hx
  simpa[Rw] using BR x hx
 have zr:=pY nu Ά (positive-Ά)
  (Nat.succ_le_iff.mpr hr)
 have xt:Ά+(positive-Ά)=positive:=by ext x; simp
 rw[xt] at zr
 refine ⟨r,hr,At,J3, ?_⟩
 simpa[K,nu,positive,main] using(by nlinarith[Dl,zr,EI])
end
end aN
end ay
end
section
open scoped BigOperators
open Finset
namespace ay
namespace cA
variable {G:Type*} [Δ G] [Γ G] [Β G]
noncomputable section
def cS (A B:Finset G) {p:ℕ} (s:Fin p→G):Finset G:=
 B.filter λ b↦ ∀ i,b-s i∈A
omit [Δ G] in
lemma kJ (A B:Finset G) {p:ℕ} (s:Fin p→G) :
  cS A B s⊆B:=by
 intro b hb
 exact(mem_filter.mp hb).1
omit [Δ G] in
@[simp] lemma jn {A B:Finset G} {p:ℕ} {s:Fin p→G} {b:G} :
  b∈cS A B s↔b∈B∧ ∀ i,b-s i∈A:=by
 simp[cS]
def wM (aX a3:Finset G) (F:G→ℝ):ℝ:=
 ∑ a₁∈aX, ∑ a₂∈a3,F (a₁-a₂)
def ef (A:Finset G) (x:G):ℕ:=
 #(Finset.univ.filter λ t:G↦x-t∈A∧ -t∈A)
private lemma sB (A:Finset G) (ey b₂:G) :
  (∑ s:G,if ey-s∈A∧b₂-s∈A then (1:ℝ) else 0) =
   ef A (ey-b₂):=by
 rw[ef]
 let e := Equiv.subRight b₂
 rw[show((#(Finset.univ.filter λ t:G↦ey-b₂-t∈A∧ -t∈A):ℕ):ℝ) =
   ∑ t:G,if ey-b₂-t∈A∧ -t∈A then (1:ℝ) else 0 by
  simp]
 refine ἐ e
  (λ s:G↦if ey-s∈A∧b₂-s∈A then (1:ℝ) else 0)
  (λ t:G↦if ey-b₂-t∈A∧ -t∈A then (1:ℝ) else 0)
  (λ t↦ ?_)
 change(if ey-t∈A∧b₂-t∈A then (1:ℝ) else 0) =
  if ey-b₂-(t-b₂)∈A∧ -(t-b₂)∈A then 1 else 0
 have h₁:ey-b₂-(t-b₂)=ey-t:=by abel
 have h₂: -(t-b₂)=b₂-t:=by abel
 rw[h₁,h₂]
private lemma pq (A:Finset G) (ey b₂:G) (p:ℕ) :
  (∑ s:Fin p→G,
    if ∀ i,ey-s i∈A∧b₂-s i∈A then (1:ℝ) else 0) =
   (ef A (ey-b₂):ℝ)^p:=by
 let D := Finset.univ.filter λ t:G↦ey-t∈A∧b₂-t∈A
 have LL :
   Finset.univ.filter
     (λ s:Fin p→G↦ ∀ i,ey-s i∈A∧b₂-s i∈A) =
    piFinset (λ _:Fin p↦D):=by
  ext s
  simp[D,RX]
 calc
  _
                                                =
    ((Finset.univ.filter
     (λ s:Fin p→G↦ ∀ i,ey-s i∈A∧b₂-s i∈A)).card:ℝ):=by
   simp
  _=((piFinset λ _:Fin p↦D).card:ℝ):=by rw[LL]
  _=(D.card:ℝ)^p:=by simp[Fintype.card_piFinset]
  _=(ef A (ey-b₂):ℝ)^p:=by
   congr 1
   have hsum:=sB A ey b₂
   simpa[D] using hsum
lemma v3 (A Τ ζ:Finset G) (p:ℕ) (F:G→ℝ) :
  (∑ s:Fin p→G,wM (cS A Τ s) (cS A ζ s) F) =
   ∑ ey∈Τ, ∑ b₂∈ζ,
    (ef A (ey-b₂):ℝ)^p*F (ey-b₂):=by
 classical
 simp only[wM,cS,sum_filter]
 rw[ὶ]
 apply sum_congr rfl
 intro ey PH
 have LN: ∀ s:Fin p→G,
   (if ∀ i,ey-s i∈A then
     ∑ a∈ζ,if ∀ i,a-s i∈A then F (ey-a) else 0
    else 0) =
    ∑ a∈ζ,if ∀ i,ey-s i∈A then
     if ∀ i,a-s i∈A then F (ey-a) else 0 else 0:=by
  intro s
  by_cases h: ∀ i,ey-s i∈A<;>simp[h]
 simp_rw[LN]
 rw[ὶ]
 apply sum_congr rfl
 intro b₂ PI
 calc
  _
           =
    (∑ s:Fin p→G,
     (if ∀ i,ey-s i∈A∧b₂-s i∈A then (1:ℝ) else 0)) *
      F (ey-b₂):=by
       rw[Ἕ]
       apply sum_congr rfl
       intro s hs
       split_ifs<;>simp_all
  _=(ef A (ey-b₂):ℝ)^p*F (ey-b₂):=by
   rw[pq]
section v5
open Function MeasureTheory Real
open scoped ENNReal NNReal Pointwise
variable [MeasurableSpace G] [Α G]
lemma v7 {A:Finset G} {p:ℕ} {ε δ:ℝ}
  (Τ ζ:Finset G) (hε:0<ε) (Ak:ε≤1) (Cc:0<δ)
  (hp:Even p) (hp₂:2≤p) (FW:ε⁻¹ *log (2/δ)≤p)
  (É:(Τ∩ζ).Nonempty) (ξ:A.Nonempty)
  (hf: ∃ x,x∈Τ-ζ∧x∈A-A∧x∉s p ε Τ ζ A) :
  ∃ aX,aX⊆Τ∧ ∃ a3,a3⊆ζ ∧
   1-δ≤ ∑ x∈s p ε Τ ζ A,((al (mu aX) (mu a3))) x ∧
   (4:ℝ)⁻¹ *(b0 p ((al (mu Τ) (mu ζ))) ((al ((indicator A λ _↦(1:(ℝ)))) ((indicator A λ _↦(1:_))))))^(2*p)/ #A^(2*p) ≤
    #aX/ #Τ ∧
   (4:ℝ)⁻¹ *(b0 p ((al (mu Τ) (mu ζ))) ((al ((indicator A λ _↦(1:(ℝ)))) ((indicator A λ _↦(1:_))))))^(2*p)/ #A^(2*p) ≤
    #a3/ #ζ:=
       Hq Τ ζ hε Ak Cc hp hp₂ FW É ξ hf
end v5
end
end cA
end ay
end
section
open Finset
open scoped BigOperators NNReal translate
namespace ay.ah
noncomputable section
variable {G:Type*} [Γ G] [Δ G] [Β G]
open br
structure aA (Λ:Finset G) where
 Θ:aY G
 Î:G
 eR :
  ∀ x∈Θ.set,x-Î∈Λ
namespace aA
def e9 {Λ:Finset G} (s:aA Λ):Finset G:=
 s.Θ.e9
def Ξ {Λ:Finset G} (s:aA Λ):ℝ:=
 s.Θ.Ξ
def Ι {Λ:Finset G} (s:aA Λ):ℕ:=
 s.Θ.Ι
def card {Λ:Finset G} (s:aA Λ):ℕ:=
 s.Θ.card
lemma ὰ {Λ:Finset G} (s:aA Λ) :
  0<s.Ξ:=s.Θ.ὰ
lemma Ö {Λ:Finset G} (s:aA Λ) :
  s.Ξ≤1:=s.Θ.Ö
end aA
inductive cU {Λ:Finset G}
  (q:ℝ) (aq:ℕ) (Á:ℝ) :
  ℕ→aA Λ→aA Λ→Prop
 | nil (s:aA Λ) :
   cU q aq Á 0 s s
 | cons {n:ℕ} {s t u:aA Λ}
   (Ἳ:dk q aq Á
    s.Θ t.Θ)
   (ῠ:cU q aq Á n t u) :
   cU q aq Á (n+1) s u
namespace cU
lemma forget {Λ:Finset G} {q:ℝ} {aq:ℕ}
  {Á:ℝ} {n:ℕ} {s t:aA Λ}
  (h:cU q aq Á n s t) :
  eu q aq Á n s.Θ t.Θ:=by
 induction h with
 | nil s=>exact eu.nil s.Θ
 | cons Ἳ _ ih=>exact eu.cons Ἳ ih
lemma qZ {Λ:Finset G} {q:ℝ} {aq:ℕ}
  {Á:ℝ} (hq:0≤q) {n:ℕ}
  {s t:aA Λ}
  (h:cU q aq Á n s t) :
  q^n*s.Ξ≤t.Ξ:=
 h.forget.qZ hq
lemma card_bound {Λ:Finset G} {q:ℝ} {aq:ℕ}
  {Á:ℝ} {n:ℕ} {s t:aA Λ}
  (h:cU q aq Á n s t) :
  exp (-(n:ℝ)*Á)*(s.card:ℝ)≤(t.card:ℝ):=
 h.forget.card_bound
end cU
def dn (A C:Finset G) (x:G):Finset G:=
 (C.filter λ c=>x-c∈A).image λ c=>-c
omit [Δ G] in
@[simp] lemma e4 {A C:Finset G} {x z:G} :
  z∈dn A C x↔ -z∈C∧x+z∈A:=by
 classical
 simp only[dn,mem_image,mem_filter]
 constructor
 ·rintro ⟨c,⟨hc,OW⟩,rfl⟩
  exact ⟨by simpa,by simpa[Ἱ] using OW⟩
 ·rintro ⟨OX,Nm⟩
  refine ⟨-z, ?_,by simp⟩
  exact ⟨OX,by simpa[Ἱ] using Nm⟩
omit [Δ G] in
lemma wZ (A C:Finset G) (x:G) :
  (dn A C x).card=(C.filter λ c=>x-c∈A).card:=by
 classical
 unfold dn
 rw[Finset.card_image_of_injective]
 intro a b h
 exact neg_injective h
lemma dz
  {B:aj G} {Φ:ℝ≥0} {A C:Finset G} {x:G}
  (Ã:C⊆(B.ai Φ).Η) :
  dn A C x⊆(B.ai Φ).Η:=by
 intro z hz
 have OY:=(e4.mp hz).1
 exact aj.ec.mp (Ã OY)
lemma bk
  {A C:Finset G} (_hC:C.Nonempty) (x:G) :
  Ó A C x=(dn A C x).card/(C.card:ℝ):=by
 classical
 rw[Ó,ao]
 let e := Equiv.subLeft x
 rw[ἐ e
  (λ y:G=>ý A y*af C (x-y))
  (λ c:G=>ý A (x-c)*af C c)
  (λ c=>by simp[e])]
 rw[wZ]
 simp only[ý,af,ἱ]
 have Ὄ (c:G) :
   (if x-c∈A then (1:ℝ) else 0) *
     (if c∈C then (C.card:ℝ)⁻¹ else 0) =
    if c∈C∧x-c∈A then (C.card:ℝ)⁻¹ else 0:=by
  by_cases hc:c∈C<;>by_cases ha:x-c∈A<;>simp[hc,ha]
 simp_rw[Ὄ]
 rw[←ᾛ]
 have Ἠ :
   (Finset.univ.filter λ c:G=>c∈C∧x-c∈A) =
    C.filter λ c=>x-c∈A:=by
  ext c
  simp
 rw[Ἠ]
 simp
open Function MeasureTheory
open scoped ENNReal Pointwise
omit [Γ G] [Δ G] in
lemma hZ (A:Finset G) :
  ag.aS A=(@mu ℝ _ _) A:=by
 funext x
 simp[ag.aS,υ]
lemma eg (aX a3:Finset G) :
  ag.a2
    (ag.aS aX)
    (ag.aS a3) =
   (al ((@mu ℝ _ _) aX) (mu a3)):=by
 funext x
 rw[hZ,hZ,
  ag.a2,eL]
 simp
lemma os
  (aX a3 S:Finset G) (t:G) :
  ((Χ (((Χ ((@mu (ℂ) _ _) (-aX)) (((indicator S λ _↦(1:_)):G→ℂ))))) (mu a3))) t =
   Complex.ofReal
    (ag.bC
     (λ x↦ag.a2
      (ag.aS aX)
      (ag.aS a3) (x-t))
     (ag.bJ S)):=by
 classical
 let a:G→ℝ:=(@mu ℝ _ _) aX
 let b:G→ℝ:=(@mu ℝ _ _) a3
 let Ὃ:G→ℝ:=(indicator S λ _↦(1:_))
 have qG :
   ag.bC
     (λ x↦ag.a2
      (ag.aS aX)
      (ag.aS a3) (x-t))
     (ag.bJ S) =
    ⟪τ t ((al a b)),Ὃ⟫_[ℝ]:=by
  rw[eg]
  unfold ag.bC
   ag.bJ
  simp only[Sg,SV,
   R3,ῗ,a,b,Ὃ,ὅ,
   mem_coe]
 have uO :
   ((Χ (((Χ ((@mu ℝ _ _) (-aX)) Ὃ))) b)) t =
    ag.bC
     (λ x↦ag.a2
      (ag.aS aX)
      (ag.aS a3) (x-t))
     (ag.bJ S):=by
  calc
   _ =
     ((Χ (((Χ Ὃ b))) ((@mu ℝ _ _) (-aX)))) t:=by
      apply Uu
      calc
       _ =
         (Χ Ὃ (((Χ ((@mu ℝ _ _) (-aX)) b)))):=by
          rw[ᾼ ((@mu ℝ _ _) (-aX)) Ὃ,
           iS]
       _=(Χ Ὃ (((Χ b ((@mu ℝ _ _) (-aX)))))):=by
          rw[ᾼ ((@mu ℝ _ _) (-aX)) b]
       _=(Χ (((Χ Ὃ b))) ((@mu ℝ _ _) (-aX))):=by
          rw[iS]
   _=((al (((Χ Ὃ b))) a)) t:=by
    rw[←CB (K:=ℝ) aX,iM]
   _=⟪τ t a,(Χ Ὃ b)⟫_[ℝ]:=by
    rw[tV]
    exact RCLike.conj_wInner_symm (𝕜:=ℝ)
     (1:G→ℝ) ((Χ Ὃ b)) (τ t a)
   _=⟪(al (τ t a) b),Ὃ⟫_[ℝ]:=
         (kY
     (τ t a) b Ὃ).symm
   _=⟪τ t ((al a b)),Ὃ⟫_[ℝ]:=by rw[rl]
   _=_:=qG.symm
 have LO:((↑) ∘ Ὃ:G→ ℂ)=((indicator S λ _↦(1:_)):G→ ℂ):=by
  ext x
  by_cases hx:x∈S<;>simp[Ὃ,hx]
 rw[←uO]
 change((Χ (((Χ ((@mu ℂ _ _) (-aX)) (((indicator S λ _↦(1:_)):G→ ℂ))))) (mu a3))) t =
  (Complex.ofReal ∘ ((Χ (((Χ ((@mu ℝ _ _) (-aX)) Ὃ))) b))) t
 rw[Complex.qo,Complex.qo]
 simp only[Complex.yL,b]
 rw[LO]
lemma ca
  (aX a3 S:Finset G) :
  ag.bC
    (ag.a2
     (ag.aS aX)
     (ag.aS a3))
    (ag.bJ S) =
   ∑ x∈S,((al ((@mu ℝ _ _) aX) (mu a3))) x:=by
 classical
 rw[eg]
 unfold ag.bC
  ag.bJ
 simp only[Td,Ἣ,mul_zero]
 rw[←ᾛ]
 have Ἠ:Finset.univ.filter (λ x:G=>x∈S)=S:=by ext; simp
 rw[Ἠ]
lemma nn
  {D:aj G} {aX a3 S:Finset G} {Μ delta:ℝ}
  (ἔ:aX.Nonempty) (Ἥ:a3.Nonempty)
  (ft:1-delta≤ ∑ x∈S,((al ((@mu ℝ _ _) aX) (mu a3))) x)
  (uj: ∀ t∈D.Η,
   |ag.bW aX a3 S t -
     ag.bW aX a3 S 0| ≤
    Μ*(aX.card:ℝ)*a3.card) :
  1-delta-Μ ≤
   ag.bC
    (ag.d9
     (ag.aS D.Η)
     (ag.a2
      (ag.aS aX)
      (ag.aS a3)))
    (ag.bJ S):=by
 have Nn:=
  ag.ji
   ἔ Ἥ uj
 have dc :
   1-delta ≤
    ag.bC
     (ag.a2
      (ag.aS aX)
      (ag.aS a3))
     (ag.bJ S):=by
  rwa[ca]
 have ic:=(abs_le.mp Nn).1
 linarith
section zS
variable [MeasurableSpace G] [Α G]
def bj (A Τ ζ:Finset G) (p:ℕ):ℝ:=
 (4:ℝ)⁻¹ *
   (b0 p ((al (mu Τ) (mu ζ))) ((al ((indicator A λ _↦(1:(ℝ)))) ((indicator A λ _↦(1:_))))))^(2*p) /
  (A.card:ℝ)^(2*p)
omit [Α G] [MeasurableSpace G] in
lemma kL
  (A:Finset G) (x:G) :
  (cA.ef A x:ℝ) =
   ((al ((indicator A λ _↦(1:ℝ))) ((indicator A λ _↦(1:_))))) x:=by
 classical
 rw[cA.ef,eL]
 have qG :
   ((#(Finset.univ.filter λ t:G↦x-t∈A∧ -t∈A):ℕ):ℝ) =
    ∑ t:G,if x-t∈A∧ -t∈A then (1:ℝ) else 0:=by
  simp
 rw[qG]
 refine ἐ (Equiv.subLeft x) _ _ (λ y↦ ?_)
 simp only[SX,ὅ]
 have ê:x-y-x= -y:=by abel
 rw[ê]
 split_ifs<;>simp_all
lemma gQ
  (A Τ ζ:Finset G) (p:ℕ) (hp:p≠0)
  (Ῠ:Τ.Nonempty) (u2:ζ.Nonempty) :
  (∑ u:Fin p→G,
    ((cA.cS A Τ u).card:ℝ) *
     (cA.cS A ζ u).card) =
   (Τ.card:ℝ)*ζ.card *
    (b0 p ((al (mu Τ) (mu ζ))) ((al ((indicator A λ _↦(1:ℝ))) ((indicator A λ _↦(1:_))))))^p:=by
 classical
 let Ἁ:G→ℝ:=(al ((indicator A λ _↦(1:ℝ))) ((indicator A λ _↦(1:_))))
 have ῧ: ∀ x,0≤Ἁ x:=λ x ↦
  dM Set.cY Set.cY x
 have ὧ:=cA.v3 A Τ ζ p (λ _↦(1:ℝ))
 have Ὢ :
   (∑ u:Fin p→G,
     cA.wM (cA.cS A Τ u)
      (cA.cS A ζ u) (λ _↦(1:ℝ))) =
    ∑ u:Fin p→G,
     ((cA.cS A Τ u).card:ℝ) *
      (cA.cS A ζ u).card:=by
  apply Ò rfl
  intro u _
  simp[cA.wM]
 have ῲ :
   (∑ ey∈Τ, ∑ b₂∈ζ,
     (cA.ef A (ey-b₂):ℝ)^p) =
    ∑ x:G,((al ((indicator Τ λ _↦(1:ℝ))) ((indicator ζ λ _↦(1:_))))) x*Ἁ x^p:=by
  rw[lM]
  simp[ὅ,Ἁ,kL]
 have t9 :
   ((al ((indicator Τ λ _↦(1:ℝ))) ((indicator ζ λ _↦(1:_))))) =
    λ x↦(Τ.card:ℝ)*ζ.card *
     ((al ((@mu ℝ _ _) Τ) (mu ζ))) x:=by
  ext x
  simp only[eL,ὅ,υ]
  rw[á]
  apply Ò rfl
  intro y _
  by_cases hy:y∈Τ<;>by_cases Es:y-x∈ζ
  ·simp only[mem_coe,ή hy,ή Es,Rc,
    star_trivial,Ἣ]
   have yf:(Τ.card:ℝ)≠0:=by
    exact_mod_cast Ῠ.card_ne_zero
   have yg:(ζ.card:ℝ)≠0:=by
    exact_mod_cast u2.card_ne_zero
   field_simp
  ·simp[hy,Es]
  ·simp[hy]
  ·simp[hy]
 have ᾷ:=jd hp
  ((al ((@mu ℝ≥0 _ _) Τ) (mu ζ))) Ἁ
 rw[Ὢ] at ὧ
 simp only[Ἣ] at ὧ
 calc
  _
                          =
    ∑ ey∈Τ, ∑ b₂∈ζ,
     (cA.ef A (ey-b₂):ℝ)^p:=by
   simpa using ὧ
  _ =
    ∑ x:G,((al ((indicator Τ λ _↦(1:ℝ))) ((indicator ζ λ _↦(1:_))))) x*Ἁ x^p:=
         ῲ
  _=(Τ.card:ℝ)*ζ.card *
     ∑ x:G,((al ((@mu ℝ _ _) Τ) (mu ζ))) x*Ἁ x^p:=by
   rw[t9]
   rw[á]
   apply Ò rfl
   intro x _
   ring
  _=(Τ.card:ℝ)*ζ.card *
    (b0 p ((al (mu Τ) (mu ζ))) ((al ((indicator A λ _↦(1:ℝ))) ((indicator A λ _↦(1:_))))))^p:=by
   congr 1
   rw[ᾷ]
   apply Ò rfl
   intro x _
   simp only[RG,ᾞ,ᾮ,
    ἳ (ῧ x),NNReal.lg,
    NNReal.iF,Ἁ]
omit [Α G] [MeasurableSpace G] in
theorem qH (A B : Finset G) (p : ℕ) :
    (∑ u : Fin p → G, ((cA.cS A B u).card : ℝ)) =
      (A.card : ℝ) ^ p * B.card:= by
  classical
  have ᾳ :
      ∑ u : Fin p → G, (cA.cS A B u).card =
        A.card ^ p * B.card:= by
    simp only [lN, cA.cS,
      Set.indicator_apply, mem_coe, mem_filter,
      mul_sum, sum_mul, @sum_comm G, Fintype.piFinset_univ,
      sum_pow']
    congr with b
    refine Fintype.sum_equiv (Equiv.subLeft λ _ : Fin p ↦ b) _ _ (λ u ↦ ?_)
    simp only [Equiv.subLeft_apply]
    by_cases hb : b ∈ B
    · simp only [hb, true_and, if_pos, mul_one]
      rw [Fintype.prod_boole]
      simp only [Pi.sub_apply]
      by_cases h : ∀ i : Fin p, b - u i ∈ A <;> simp [h]
    · simp [hb]
  exact_mod_cast ᾳ
lemma pZ
  (A Τ ζ:Finset G) (p:ℕ) (u3:2≤p)
  (É:(Τ∩ζ).Nonempty) (ξ:A.Nonempty) :
  ∃ u:Fin p→G,
   (cA.cS A Τ u).Nonempty ∧
   (cA.cS A ζ u).Nonempty ∧
   bj A Τ ζ p ≤
    ((cA.cS A Τ u).card:ℝ)/Τ.card ∧
   bj A Τ ζ p ≤
    ((cA.cS A ζ u).card:ℝ)/ζ.card:=by
 classical
 have hp:p≠0:=by omega
 have Ῠ:Τ.Nonempty:=É.mono inter_subset_left
 have u2:ζ.Nonempty:=É.mono inter_subset_right
 have ῥ:A.Nonempty:=ξ
 let aX:(Fin p→G)→Finset G:=λ u↦cA.cS A Τ u
 let a3:(Fin p→G)→Finset G:=λ u↦cA.cS A ζ u
 let N:ℝ:=(b0 p ((al (mu Τ) (mu ζ))) ((al ((indicator A λ _↦(1:ℝ))) ((indicator A λ _↦(1:_))))))
 let g:(Fin p→G)→ℝ:=λ u↦(aX u).card*(a3 u).card
 have hg: ∀ u,0≤g u:=λ u↦by dsimp[g]; positivity
 have Aj: ∑ u,g u=(Τ.card:ℝ)*ζ.card*N^p:=by
  simpa[g,aX,a3,N] using
   gQ A Τ ζ p hp Ῠ u2
 obtain ⟨b,hb⟩:=É
 obtain ⟨a,ha⟩:=ξ
 let ᾲ:Fin p→G:=λ _↦b-a
 have v8:b∈aX ᾲ:=by
  simp only[aX,cA.jn,ᾲ]
  refine ⟨(inter_subset_left hb), ?_⟩
  intro i
  have:b-(b-a)=a:=by abel
  rwa[this]
 have v9:b∈a3 ᾲ:=by
  simp only[a3,cA.jn,ᾲ]
  refine ⟨(inter_subset_right hb), ?_⟩
  intro i
  have:b-(b-a)=a:=by abel
  rwa[this]
 have rY:0< ∑ u,g u:=by
  exact Finset.sum_pos' (λ u _↦hg u) ⟨ᾲ,Sz _,by
   dsimp only[g]
   exact Ἃ (by exact_mod_cast(Finset.card_pos.mpr ⟨b,v8⟩))
    (by exact_mod_cast(Finset.card_pos.mpr ⟨b,v9⟩))⟩
 have Hh:0<N^p:=by
  have jt:0<(Τ.card:ℝ)*ζ.card:=by positivity
  rw[Aj] at rY
  rcases mul_pos_iff.mp rY with gy | ê
  ·exact gy.2
  ·exact(ῑ jt.le ê.1).elim
 let M:ℝ:=
  2⁻¹ *N^p*(Real.sqrt Τ.card*Real.sqrt ζ.card) /
   (A.card:ℝ)^p
 have ἄ:0<M:=by
  dsimp[M]
  have J4:(0:ℝ)<A.card:=by exact_mod_cast ῥ.card_pos
  have yf:(0:ℝ)<Τ.card:=by exact_mod_cast Ῠ.card_pos
  have yg:(0:ℝ)<ζ.card:=by exact_mod_cast u2.card_pos
  exact ὗ (Ἃ (Ἃ (by norm_num) Hh)
   (Ἃ (Real.sqrt_pos.2 yf) (Real.sqrt_pos.2 yg)))
   (ᾅ J4 p)
 have H7: ∑ u,((aX u).card:ℝ)=(A.card:ℝ)^p*Τ.card:=by
  simpa[aX] using qH A Τ p
 have H8: ∑ u,((a3 u).card:ℝ)=(A.card:ℝ)^p*ζ.card:=by
  simpa[a3] using qH A ζ p
 have ᾌ: ∃ u,M^2≤g u:=by
  by_cases h: ∀ u,g u≠0→M^2≤g u
  ·have ᾱ: ∃ u,g u≠0:=by
    by_contra hn
    push Not at hn
    have: ∑ u,g u=0:=by simp[hn]
    linarith
   obtain ⟨u,hu⟩:=ᾱ
   exact ⟨u,h u hu⟩
  ·push Not at h
   obtain ⟨u₁,H9,Ge⟩:=h
   have Ap:(2:ℝ)* ∑ u with g u<M^2,g u< ∑ u,g u:=by
    rw[←lt_div_iff₀' (by norm_num:(0:ℝ)<2),Ri]
    calc
     ∑ u with g u<M^2,g u =
       ∑ u with g u<M^2∧g u≠0,
        Real.sqrt (g u)*Real.sqrt (g u):=by
      simp_rw[Ta (hg _), ←Finset.filter_filter,
       Finset.sum_filter_ne_zero]
     _< ∑ u with g u<M^2∧g u≠0,
        M*Real.sqrt (g u):=by
      apply Tt
      ·exact ⟨u₁,Finset.mem_filter.mpr ⟨Sz _,Ge,H9⟩⟩
      ·intro u hu
       have OZ:=(Finset.mem_filter.mp hu).2.1
       have No:=(Finset.mem_filter.mp hu).2.2
       exact Sk ((Real.sqrt_lt' ἄ).2 OZ)
        (Real.sqrt_pos.2 ((hg u).lt_of_ne' No))
     _≤ ∑ u,M*Real.sqrt (g u):=
      Tj λ u↦by positivity
     _=M*(∑ u,Real.sqrt ((aX u).card) *
        Real.sqrt ((a3 u).card)):=by
      rw[á]
      apply Ò rfl
      intro u _
      dsimp only[g]
      rw[Real.sqrt_mul (by positivity:(0:ℝ)≤(aX u).card)]
     _≤M*(Real.sqrt (∑ u,((aX u).card:ℝ)) *
        Real.sqrt (∑ u,((a3 u).card:ℝ))):=by
      gcongr
      exact Real.sum_sqrt_mul_sqrt_le _ (λ _↦by positivity)
       (λ _↦by positivity)
     _=(2:ℝ)⁻¹ * ∑ u,g u:=by
      dsimp only[M]
      rw[H7,H8,Real.sqrt_mul' _ (by positivity),
       Real.sqrt_mul' _ (by positivity),
       Q7 (Real.sqrt _),Ta,
       ←à,Tz, ←Real.sqrt_mul,
       à,Ta,Aj,ᾭ,à]
      all_goals positivity
   by_contra z4
   push Not at z4
   have Dn: ∑ u,g u= ∑ u with g u<M^2,g u:=by
    congr 1
    symm
    exact Finset.filter_eq_self.mpr (λ u _↦z4 u)
   rw[Dn] at Ap
   linarith
 obtain ⟨u,hu⟩:=ᾌ
 have te:bj A Τ ζ p ≤
   (((aX u).card:ℝ)/Τ.card) *
    (((a3 u).card:ℝ)/ζ.card):=by
  dsimp[bj,M,N,g] at hu ⊢
  have J4:(A.card:ℝ)≠0:=by exact_mod_cast ῥ.card_ne_zero
  have yf:(Τ.card:ℝ)≠0:=by exact_mod_cast Ῠ.card_ne_zero
  have yg:(ζ.card:ℝ)≠0:=by exact_mod_cast u2.card_ne_zero
  rw[div_mul_div_comm,ἇ (by positivity)]
  simpa[Ἀ,TY,pow_mul',show(2:ℝ)^2=4 by norm_num,
   Uf (show 0≤(Τ.card:ℝ) by positivity),
   Uf (show 0≤(ζ.card:ℝ) by positivity),
   J4,yf,yg,S5] using hu
 have J5:0<g u:=(SY ἄ).trans_le hu
 have EJ:0<((aX u).card:ℝ)*(a3 u).card:=by
  simpa only[g] using J5
 have EK:0<((aX u).card:ℝ)∧0<((a3 u).card:ℝ):=by
  rcases mul_pos_iff.mp EJ with gy | ê
  ·exact gy
  ·exact(ῑ (Q5 _) ê.1).elim
 have xB:0<((aX u).card:ℝ):=EK.1
 have Gf:0<((a3 u).card:ℝ):=EK.2
 refine ⟨u,Finset.card_pos.mp (by exact_mod_cast xB),
  Finset.card_pos.mp (by exact_mod_cast Gf), ?_, ?_⟩
 ·have sa:((a3 u).card:ℝ)≤ζ.card:=by
   exact_mod_cast ὣ (cA.kJ A ζ u)
  exact te.trans (Sq (by positivity)
   ((ᾜ (by positivity:(0:ℝ)<ζ.card)).2 sa))
 ·have r9:((aX u).card:ℝ)≤Τ.card:=by
   exact_mod_cast ὣ (cA.kJ A Τ u)
  exact te.trans (RQ (by positivity)
   ((ᾜ (by positivity:(0:ℝ)<Τ.card)).2 r9))
structure aW (A Τ ζ:Finset G)
  (p:ℕ) (Μ delta:ℝ) where
 aX:Finset G
 a3:Finset G
 u5:aX⊆Τ
 rM:a3⊆ζ
 oW:1-delta ≤
  ag.bC
   (ag.a2
    (ag.aS aX)
    (ag.aS a3))
   (ag.bJ (s p Μ Τ ζ A))
 tC:bj A Τ ζ p ≤
  (aX.card:ℝ)/Τ.card
 tD:bj A Τ ζ p ≤
  (a3.card:ℝ)/ζ.card
namespace aW
def bg
  (A Τ ζ:Finset G) (p:ℕ) (Μ:ℝ):Finset G:=
 s p Μ Τ ζ A∩(Τ-ζ)
omit [Α G] in
lemma oX
  (A Τ ζ:Finset G) (p:ℕ) (Μ:ℝ) :
  bg A Τ ζ p Μ⊆Τ-ζ:=
 Sd
omit [Α G] in
lemma lR
  {A Τ ζ:Finset G} {p:ℕ} {Μ delta:ℝ}
  (data:aW A Τ ζ p Μ delta)
  (cu:delta<1):data.aX.Nonempty∧data.a3.Nonempty:=by
 have ft:1-delta ≤
   ∑ x∈s p Μ Τ ζ A,((al ((@mu ℝ _ _) data.aX) (mu data.a3))) x:=by
  simpa only[ca] using
   data.oW
 constructor
 ·by_contra wa
  have su := not_nonempty_iff_eq_empty.mp wa
  rw[su] at ft
  simp at ft
  linarith
 ·by_contra wa
  have su := not_nonempty_iff_eq_empty.mp wa
  rw[su] at ft
  simp at ft
  linarith
omit [Α G] in
lemma np
  {A Τ ζ:Finset G} {p:ℕ} {Μ delta:ℝ}
  (data:aW A Τ ζ p Μ delta) :
  1-delta ≤
   ag.bC
    (ag.a2
     (ag.aS data.aX)
     (ag.aS data.a3))
    (ag.bJ
     (bg A Τ ζ p Μ)):=by
 have Ia:1-delta ≤
   ∑ x∈s p Μ Τ ζ A,
    ((al ((@mu ℝ _ _) data.aX) (mu data.a3))) x:=by
  simpa only[ca] using
   data.oW
 have hsum :
   ∑ x∈bg A Τ ζ p Μ,
     ((al ((@mu ℝ _ _) data.aX) (mu data.a3))) x =
    ∑ x∈s p Μ Τ ζ A,
     ((al ((@mu ℝ _ _) data.aX) (mu data.a3))) x:=by
  apply Ro Sh
  intro x xC LP
  rw[←UQ]
  intro Np
  apply LP
  have EL :
    x∈Function.support ((al ((@mu ℝ _ _) data.aX) (mu data.a3))):=Np
  have J6:x∈data.aX-data.a3:=by
   simpa only[f8 õ õ,jo,
    ←coe_sub,mem_coe] using EL
  obtain ⟨a₁,z5,a₂,z6,Hi⟩:=Finset.mem_sub.mp J6
  exact Finset.mem_inter.mpr ⟨xC,
   Finset.mem_sub.mpr ⟨a₁,data.u5 z5,a₂,
    data.rM z6,Hi⟩⟩
 rw[ca,hsum]
 exact Ia
omit [Α G] in
lemma gL
  {A Τ ζ:Finset G} {p:ℕ} {Μ delta:ℝ}
  (data:aW A Τ ζ p Μ delta)
  (cu:delta<1) :
  (bg A Τ ζ p Μ).Nonempty:=by
 by_contra z4
 have su :=
  not_nonempty_iff_eq_empty.mp z4
 have ft:=data.np
 rw[su] at ft
 simp[ag.bC,
  ag.bJ] at ft
 linarith
end aW
lemma q9
  {A:Finset G} {p:ℕ} {Μ delta:ℝ}
  (Τ ζ:Finset G) (Ἷ:0<Μ) (tE:Μ≤1)
  (cu:0<delta) (hp:Even p) (u3:2≤p)
  (wb:Μ⁻¹ *log (2/delta)≤p)
  (É:(Τ∩ζ).Nonempty) (ξ:A.Nonempty)
  (ὸ: ∃ x,x∈Τ-ζ∧x∈A-A ∧
   x∉s p Μ Τ ζ A) :
  Nonempty (aW A Τ ζ p Μ delta):=by
 obtain ⟨aX,ἔ,a3,Ἥ,ft,y6,y7⟩:=
  cA.v7 Τ ζ Ἷ tE cu hp u3
   wb É ξ ὸ
 refine ⟨{
  aX:=aX
  a3:=a3
  u5:=ἔ
  rM:=Ἥ
  oW:= ?_
  tC:= ?_
  tD:= ?_ }⟩
 ·rwa[ca]
 ·simpa only[bj] using y6
 ·simpa only[bj] using y7
lemma ma
  {A:Finset G} {p:ℕ} {Μ delta:ℝ}
  (Τ ζ:Finset G) (cu:0<delta) (u3:2≤p)
  (É:(Τ∩ζ).Nonempty) (ξ:A.Nonempty)
  (ῶ: ∀ x,x∈Τ-ζ→x∈A-A →
   x∈s p Μ Τ ζ A) :
  Nonempty (aW A Τ ζ p Μ delta):=by
 classical
 obtain ⟨u,ἔ,Ἥ,y6,y7⟩:=
  pZ A Τ ζ p u3 É ξ
 let aX:=cA.cS A Τ u
 let a3:=cA.cS A ζ u
 have Co:aX⊆Τ:=cA.kJ A Τ u
 have Cp:a3⊆ζ:=cA.kJ A ζ u
 have hp:0<p:=by omega
 let i:Fin p:=⟨0,hp⟩
 have LQ:aX-a3⊆s p Μ Τ ζ A:=by
  intro x hx
  obtain ⟨a₁,z5,a₂,z6,Hi⟩:=Finset.mem_sub.mp hx
  apply ῶ x
  ·exact Finset.mem_sub.mpr ⟨a₁,Co z5,a₂,Cp z6,Hi⟩
  ·have J7:=(cA.jn.mp z5).2 i
   have J8:=(cA.jn.mp z6).2 i
   refine Finset.mem_sub.mpr ⟨a₁-u i,J7,a₂-u i,J8, ?_⟩
   rw[←Hi]
   abel
 have hsum :
   ∑ x∈s p Μ Τ ζ A,((al ((@mu ℝ _ _) aX) (mu a3))) x=1:=by
  calc
   ∑ x∈s p Μ Τ ζ A,((al ((@mu ℝ _ _) aX) (mu a3))) x =
     ∑ x:G,((al ((@mu ℝ _ _) aX) (mu a3))) x:=by
    apply Ro (S7 _)
    intro x _ LS
    rw[←UQ]
    intro Nq
    apply LS
    apply LQ
    have LU:x∈Function.support ((al ((@mu ℝ _ _) aX) (mu a3))):=Nq
    simpa only[f8 õ õ,jo,
     ←coe_sub,mem_coe] using LU
   _=1:=by
    rw[jJ]
    simp only[Rc,star_trivial]
    rw[ᾢ _ (by simpa[aX] using ἔ),
     ᾢ _ (by simpa[a3] using Ἥ),ἃ]
 refine ⟨{
  aX:=aX
  a3:=a3
  u5:=Co
  rM:=Cp
  oW:= ?_
  tC:=by simpa[aX] using y6
  tD:=by simpa[a3] using y7 }⟩
 rw[ca,hsum]
 linarith
lemma kM
  {A:Finset G} {p:ℕ} {Μ delta:ℝ}
  (Τ ζ:Finset G) (Ἷ:0<Μ) (tE:Μ≤1)
  (cu:0<delta) (hp:Even p) (u3:2≤p)
  (wb:Μ⁻¹ *log (2/delta)≤p)
  (É:(Τ∩ζ).Nonempty) (ξ:A.Nonempty) :
  Nonempty (aW A Τ ζ p Μ delta):=by
 classical
 by_cases ὸ: ∃ x,x∈Τ-ζ∧x∈A-A ∧
   x∉s p Μ Τ ζ A
 ·exact q9 Τ ζ Ἷ tE
   cu hp u3 wb É ξ ὸ
 ·apply ma Τ ζ cu u3 É ξ
  intro x O0 Ek
  by_contra O1
  exact ὸ ⟨x,O0,Ek,O1⟩
structure cb
  {A Τ ζ:Finset G} {p:ℕ} {Μ delta:ℝ}
  (data:aW A Τ ζ p Μ delta)
  (parent:aj G) (ὐ:ℝ≥0)
  (source:Finset G) (aq bq:ℕ)
  (bm:ℝ) where
 child:aj G
 k6:child.a1
 rN:child.Ι≤parent.Ι+aq
 tF:child.Η⊆(parent.ai ὐ).Η
 nM:source.card≤bq*child.Η.card
 oY: ∀ t∈child.Η,
  |ag.bW
    data.aX data.a3
     (aW.bg A Τ ζ p Μ) t -
   ag.bW
    data.aX data.a3
     (aW.bg A Τ ζ p Μ) 0| ≤
   bm*(data.aX.card:ℝ)*data.a3.card
def cb.mono
  {A Τ ζ:Finset G} {p:ℕ} {Μ delta:ℝ}
  {data:aW A Τ ζ p Μ delta}
  {parent:aj G} {ὐ:ℝ≥0} {source:Finset G}
  {aq bq zs tf:ℕ}
  {bm lA:ℝ}
  (P:cb data parent ὐ source
   aq bq bm)
  (Ñ:aq≤zs)
  (ch:bq≤tf)
  (EI:bm≤lA) :
  cb data parent ὐ source
   zs tf lA where
 child:=P.child
 k6:=P.k6
 rN:=P.rN.trans (Nat.add_le_add_left Ñ _)
 tF:=P.tF
 nM:=P.nM.trans
  (QQ P.child.Η.card ch)
 oY:=by
  intro t ht
  calc
   _
     ≤ bm*(data.aX.card:ℝ)*data.a3.card:=
    P.oY t ht
   _≤lA*(data.aX.card:ℝ)*data.a3.card:=by
    gcongr
omit [Α G] [MeasurableSpace G] in
lemma kN
  (D aX a3:Finset G) :
  ag.d9
    (ag.aS D)
    (ag.a2
     (ag.aS aX)
     (ag.aS a3)) =
   (Χ ((@mu ℝ _ _) D) (((al (mu aX) (mu a3))))):=by
 funext x
 rw[hZ,
  eg,
  ag.d9,ᾂ]
omit [Α G] [MeasurableSpace G] in
lemma j9
  (D aX a3 S:Finset G) :
  ag.bC
    (ag.d9
     (ag.aS D)
     (ag.a2
      (ag.aS aX)
      (ag.aS a3)))
    (ag.bJ S) =
   ∑ x∈S,((Χ ((@mu ℝ _ _) D) (((al (mu aX) (mu a3)))))) x:=by
 classical
 rw[kN]
 unfold ag.bC
  ag.bJ
 simp only[Td,Ἣ,mul_zero]
 rw[←ᾛ]
 have Ἠ:Finset.univ.filter (λ x:G↦x∈S)=S:=by ext; simp
 rw[Ἠ]
omit [Α G] [MeasurableSpace G] in
lemma lW
  {D aX a3 S:Finset G} {Ἁ:G→ℝ}
  {mass threshold:ℝ}
  (oZ:0≤threshold)
  (ῧ: ∀ x,0≤Ἁ x)
  (sE: ∀ x∈S,threshold≤Ἁ x)
  (ft:mass ≤
   ag.bC
    (ag.d9
     (ag.aS D)
     (ag.a2
      (ag.aS aX)
      (ag.aS a3)))
    (ag.bJ S)) :
  threshold*mass ≤
   ∑ x:G,((Χ ((@mu ℝ _ _) D) (((al (mu aX) (mu a3)))))) x*Ἁ x:=by
 classical
 rw[j9] at ft
 have zt: ∀ x:G,
   0≤((Χ ((@mu ℝ _ _) D) (((al (mu aX) (mu a3)))))) x:=by
  intro x
  exact pC õ
   (λ y↦dM õ õ y) x
 calc
  _ ≤
    threshold* ∑ x∈S,
     ((Χ ((@mu ℝ _ _) D) (((al (mu aX) (mu a3)))))) x:=
   Å ft oZ
  _= ∑ x∈S,
    threshold*((Χ ((@mu ℝ _ _) D) (((al (mu aX) (mu a3)))))) x:=by
   rw[á]
  _≤ ∑ x∈S,
    ((Χ ((@mu ℝ _ _) D) (((al (mu aX) (mu a3)))))) x*Ἁ x:=by
   apply ᾯ
   intro x hx
   rw[ä threshold]
   exact Å (sE x hx) (zt x)
  _≤ ∑ x:G,
    ((Χ ((@mu ℝ _ _) D) (((al (mu aX) (mu a3)))))) x*Ἁ x:=
         Tj λ x ↦
    å (zt x) (ῧ x)
omit [Β G] [Α G] [MeasurableSpace G] in
lemma mD
  {w f:G→ℝ} (hw: ∀ x,0≤w x)
  (u6: ∑ x:G,w x=1) {lower:ℝ}
  (ic:lower≤ ∑ x:G,w x*f x) :
  ∃ x:G,lower≤f x:=by
 classical
 obtain ⟨x,_hx,Dp⟩:=
  TX Finset.univ f (Finset.univ_nonempty :
   (Finset.univ:Finset G).Nonempty)
 refine ⟨x,ic.trans ?_⟩
 calc
  _ ≤ ∑ y:G,w y*f x:=by
   apply ᾯ
   intro y _
   exact Å (Dp y (by simp)) (hw y)
  _=f x:=by rw[←Ἕ,u6,ἃ]
omit [Γ G] [Β G] [Α G] [MeasurableSpace G] in
lemma lB
  {w f:G→ℝ} {T:Finset G} (ἓ:T.Nonempty)
  (hw: ∀ x,0≤w x) (wc: ∀ x,x∉T→w x=0)
  (u6: ∑ x:G,w x=1) {lower:ℝ}
  (ic:lower≤ ∑ x:G,w x*f x) :
  ∃ x∈T,lower≤f x:=by
 classical
 obtain ⟨x,O2,Dp⟩:=TX T f ἓ
 refine ⟨x,O2,ic.trans ?_⟩
 calc
  _ ≤ ∑ y:G,w y*f x:=by
   apply ᾯ
   intro y _
   by_cases hy:y∈T
   ·exact Å (Dp y hy) (hw y)
   ·rw[wc y hy,zero_mul,zero_mul]
  _=f x:=by rw[←Ἕ,u6,ἃ]
omit [Α G] [MeasurableSpace G] in
lemma lC
  (D E:Finset G) :
  ((↑) ∘ aN.bh D E:G→ℝ) =
   (Χ (((al ((@mu ℝ _ _) D) (mu E)))) (((al (mu E) (mu D))))):=by
 unfold aN.bh
  aN.dU
 simp only[NNReal.gF,NNReal.oD,
  NNReal.iF]
 symm
 rw[kr,ᾼ ((@mu ℝ _ _) E) (mu D)]
omit [Α G] [MeasurableSpace G] in
lemma kp
  (D E:Finset G) (f:G→ℝ) (p:ℕ) :
  È
    ((↑) ∘ aN.bh D E) f p =
   ∑ z:G,((al ((@mu ℝ _ _) D) (mu E))) z *
    È
     (λ x↦((al ((@mu ℝ _ _) E) (mu D))) (x-z)) f p:=by
 rw[lC]
 unfold È
 simp_rw[ᾂ,Ἕ]
 rw[ὶ]
 apply Ò rfl
 intro z _
 rw[á]
 apply Ò rfl
 intro x _
 ring
omit [Α G] [MeasurableSpace G] in
lemma lD
  {D E:Finset G} (Ð:D.Nonempty) (Þ:E.Nonempty)
  (f:G→ℝ) (p:ℕ) {lower:ℝ}
  (ic:lower≤È
   ((↑) ∘ aN.bh D E) f p) :
  ∃ z∈D-E,
   ((z+ᵥ E)∩D).Nonempty ∧
   lower≤È ((al ((@mu ℝ _ _) (z+ᵥ E)) (mu D))) f p:=by
 let w:G→ℝ:=(al ((@mu ℝ _ _) D) (mu E))
 let F:G→ℝ:=λ z ↦
  È (λ x↦((al ((@mu ℝ _ _) E) (mu D))) (x-z)) f p
 have O3:(D-E).Nonempty:=by
  obtain ⟨d,hd⟩:=Ð
  obtain ⟨e,he⟩:=Þ
  refine ⟨d-e, ?_⟩
  exact Finset.mem_sub.mpr ⟨d,hd,e,he,rfl⟩
 have hw: ∀ z,0≤w z:=by
  intro z
  exact dM õ õ z
 have wc: ∀ z,z∉D-E→w z=0:=by
  intro z hz
  rw[←UQ]
  intro O4
  apply hz
  have EM:z∈Function.support w:= O4
  simpa only[w,f8 õ õ,
   jo, ←coe_sub,mem_coe] using EM
 have u6: ∑ z:G,w z=1:=by
  dsimp only[w]
  rw[jJ]
  simp only[Rc,star_trivial]
  rw[ᾢ _ Ð,ᾢ _ Þ,ἃ]
 have Gg:lower≤ ∑ z:G,w z*F z:=by
  rw[←kp]
  exact ic
 obtain ⟨z,hz,y8⟩:=
  lB O3 hw wc u6 Gg
 obtain ⟨d,hd,e,he,O5⟩:=Finset.mem_sub.mp hz
 refine ⟨z,hz, ?_, ?_⟩
 ·refine ⟨d,Finset.mem_inter.mpr ⟨?_,hd⟩⟩
  rw[Ug]
  refine ⟨e,he, ?_⟩
  rw[←O5]
  simp only[Uz]
  exact Rs d e
 ·dsimp only[F] at y8
  have t9 :
    (λ x↦((al ((@mu ℝ _ _) E) (mu D))) (x-z)) =
     (al ((@mu ℝ _ _) (z+ᵥ E)) (mu D)):=by
   rw[←vI,rl]
   rfl
  rw[t9] at y8
  exact y8
lemma lE
  {D E A:Finset G} (Ð:D.Nonempty) (Þ:E.Nonempty)
  (_hA:A.Nonempty) {p:ℕ} (hp:0<p) {lower:ℝ}
  (AV:0≤lower)
  (ic:lower ≤
   an.aM
    ((↑) ∘ aN.bh D E)
    ((al ((@mu ℝ _ _) A) (mu A))) p) :
  ∃ z∈D-E,
   ((z+ᵥ E)∩D).Nonempty ∧
   lower≤(b0 p ((al (mu (z+ᵥ E)) (mu D))) ((al ((@mu ℝ _ _) A) (mu A)))):=by
 let nu:=aN.bh D E
 have rq:an.cw
   ((↑) ∘ nu:G→ℝ):=by
  refine ⟨?_, ?_⟩
  ·intro x
   exact_mod_cast(aN.gS D E x)
  ·simpa using è (λ r:ℝ≥0↦(r:ℝ))
    (aN.i7 Ð Þ)
 have yW:lower^p ≤
   È ((↑) ∘ nu:G→ℝ)
    ((al ((@mu ℝ _ _) A) (mu A))) p:=by
  calc
   lower^p ≤
     an.aM
       ((↑) ∘ nu:G→ℝ) ((al ((@mu ℝ _ _) A) (mu A))) p^p:=
    ἤ AV ic p
   _=È ((↑) ∘ nu:G→ℝ)
     ((al ((@mu ℝ _ _) A) (mu A))) p:=
    an.jr rq hp
 obtain ⟨z,hz,um,EN⟩:=
  lD Ð Þ
   ((al ((@mu ℝ _ _) A) (mu A))) p (by simpa[nu] using yW)
 let ῤ:G→ℝ≥0:=(al ((@mu ℝ≥0 _ _) (z+ᵥ E)) (mu D))
 have Ῠ:(z+ᵥ E).Nonempty:=by
  obtain ⟨e,he⟩:=Þ
  refine ⟨z+e, ?_⟩
  rw[Ug]
  exact ⟨e,he,rfl⟩
 have Hj:an.cw
   ((↑) ∘ ῤ:G→ℝ):=by
  refine ⟨?_, ?_⟩
  ·intro x
   exact_mod_cast(dM õ õ x:0≤ῤ x)
  ·dsimp only[ῤ]
   simp only[NNReal.gF,NNReal.iF]
   rw[jJ]
   simp only[Rc,star_trivial]
   rw[ᾢ _ Ῠ,ᾢ _ Ð,ἃ]
 have Dq:lower^p ≤
   È ((↑) ∘ ῤ:G→ℝ)
    ((al ((@mu ℝ _ _) A) (mu A))) p:=by
  simpa only[ῤ,NNReal.gF,NNReal.iF] using EN
 have EO:lower^p ≤
   an.aM
     ((↑) ∘ ῤ:G→ℝ) ((al ((@mu ℝ _ _) A) (mu A))) p^p:=by
  rw[an.jr Hj hp]
  exact Dq
 have AW:0 ≤
   an.aM
    ((↑) ∘ ῤ:G→ℝ) ((al ((@mu ℝ _ _) A) (mu A))) p:=
  an.j3 Hj _ _
 have yh:lower ≤
   an.aM
    ((↑) ∘ ῤ:G→ℝ) ((al ((@mu ℝ _ _) A) (mu A))) p:=by
  by_contra hnot
  have Ί:=ᾙ hnot
  have LV:=pow_lt_pow_left₀ Ί AW hp.ne'
  exact(ῑ EO) LV
 refine ⟨z,hz,um, ?_⟩
 rw[aN.dN ῤ
  ((al ((@mu ℝ _ _) A) (mu A))) hp] at yh
 exact yh
omit [Α G] [MeasurableSpace G] in
lemma m0
  {A D:Finset G} (ξ:A.Nonempty) (x:G) :
  (A.card:ℝ)*((Χ ((@mu ℝ _ _) D) (mu A))) x=Ó A D x:=by
 classical
 rw[ᾂ,Ó,ao,á]
 let e := Equiv.subLeft x
 rw[ἐ e
  (λ z:G↦(A.card:ℝ)*((@mu ℝ _ _) D z*mu A (x-z)))
  (λ y:G↦(A.card:ℝ)*((@mu ℝ _ _) D (x-y)*mu A y))]
 ·apply Ò rfl
  intro y _
  simp only[υ,ý,af]
  have sF:(A.card:ℝ)≠0:=by exact_mod_cast ξ.card_ne_zero
  by_cases J9:y∈A
  ·by_cases Ka:x-y∈D
   ·simp only[ή J9,ή Ka,Ἣ]
    calc
     _ =
       (D.card:ℝ)⁻¹ *((A.card:ℝ)*(A.card:ℝ)⁻¹):=by ring
     _=(D.card:ℝ)⁻¹:=by rw[Tw sF,Ἣ]
     _=1*(D.card:ℝ)⁻¹:=by rw[ἃ]
   ·simp[J9,Ka]
  ·simp[J9]
 ·intro y
  simp[e]
omit [Α G] [MeasurableSpace G] in
lemma p0
  (d a₁ a₂ a:G→ℝ) :
  ⟪(Χ d (((al a₁ a₂)))),(al a a)⟫_[ℝ] =
   ⟪(Χ d a),(Χ (((al a₂ a₁))) a)⟫_[ℝ]:=by
 rw[ro,ro]
 congr 1
 change(al (((al a a))) (((al a₁ a₂))))=(al (((Χ (((al a₂ a₁))) a))) a)
 simp_rw[←iM,pL,conjneg_conjneg]
 calc
  _ =
    (Χ (((Χ a (conjneg a₁)))) (((Χ (conjneg a) a₂)))):=
   ir _ _ _ _
  _=(Χ (((Χ (conjneg a₁) a))) (((Χ a₂ (conjneg a))))):=by
   rw[ᾼ a,ᾼ (conjneg a) a₂]
  _=(Χ (((Χ (conjneg a₁) a₂))) (((Χ a (conjneg a))))):=
   ir _ _ _ _
  _=(Χ (((Χ (((Χ a₂ (conjneg a₁)))) a))) (conjneg a)):=by
   rw[ᾼ (conjneg a₁) a₂]
   exact(iS _ _ _).symm
omit [Α G] [MeasurableSpace G] in
lemma jy
  {D aX a3 A S:Finset G}
  (_hD:D.Nonempty) (ἔ:aX.Nonempty)
  (Ἥ:a3.Nonempty) (ξ:A.Nonempty)
  {threshold mass lower:ℝ} (oZ:0≤threshold)
  (ῧ: ∀ x,0≤((al ((@mu ℝ _ _) A) (mu A))) x)
  (sE: ∀ x∈S,threshold≤((al ((@mu ℝ _ _) A) (mu A))) x)
  (ft:mass ≤
   ag.bC
    (ag.d9
     (ag.aS D)
     (ag.a2
      (ag.aS aX)
      (ag.aS a3)))
    (ag.bJ S))
  (ic:lower≤threshold*mass) :
  ∃ x:G,(A.card:ℝ)*lower≤Ó A D x:=by
 have EP:=lW oZ ῧ
  sE ft
 have xD:=p0
  ((@mu ℝ _ _) D) (mu aX) (mu a3) (mu A)
 rw[Sg,Sg] at xD
 simp only[SV,R3] at xD
 let w:G→ℝ:=(Χ (((al ((@mu ℝ _ _) a3) (mu aX)))) (mu A))
 let f:G→ℝ:=(Χ ((@mu ℝ _ _) D) (mu A))
 have hw: ∀ x,0≤w x:=by
  intro x
  exact pC
   (λ y↦dM õ õ y) õ x
 have u6: ∑ x:G,w x=1:=by
  dsimp only[w]
  rw[uM,jJ]
  simp only[Rc,star_trivial]
  rw[ᾢ _ Ἥ,ᾢ _ ἔ,ἃ,
   ᾢ _ ξ,Ἣ]
 have Ay:lower≤ ∑ x:G,w x*f x:=by
  calc
   _ ≤threshold*mass:=ic
   _≤ ∑ x:G,
     ((Χ ((@mu ℝ _ _) D) (((al (mu aX) (mu a3)))))) x*((al (mu A) (mu A))) x:=
    EP
   _= ∑ x:G,w x*f x:=by
    rw[xD]
    apply Ò rfl
    intro x _
    rw[ä]
 obtain ⟨x,hx⟩:=mD hw u6 Ay
 refine ⟨x, ?_⟩
 rw[←m0 ξ]
 exact Å hx (Q5 _)
end zS
lemma bK
  {A C:Finset G} (Ã:C.Nonempty) {x:G}
  (hx:0<Ó A C x) :
  (dn A C x).Nonempty:=by
 by_contra h
 have Gh: ¬ 0<(dn A C x).card:=by
  intro ch
  exact h (Finset.card_pos.mp ch)
 have ch := Nat.eq_zero_of_not_pos Gh
 rw[bk Ã,ch] at hx
 norm_num at hx
structure bt where
 ba:aj G
 Ψ:ℝ≥0
 Ï:ℝ≥0
 é:0< Ï∧Ï≤Ψ ∧
  (ba.ai (Ψ+Ï)).Η.card ≤
   2*(ba.ai (Ψ-Ï)).Η.card
namespace bt
def Η (c:bt (G:=G)):Finset G:=
 (c.ba.ai c.Ψ).Η
omit [Β G] in
lemma aE (c:bt (G:=G)):c.Η.Nonempty:=
 (c.ba.ai c.Ψ).aE
def eo (c:bt (G:=G))
  (A:Finset G) (ξ:A.Nonempty) (ER:A⊆c.Η) :
  aY G where
 ba:=c.ba
 Ψ:=c.Ψ
 Ï:=c.Ï
 é:=c.é
 set:=A
 nonempty:=ξ
 mw:=ER
omit [Β G] in
lemma od (B:aj G) (Ô:B.a1) :
    ∃ c:bt (G:=G),
      c.ba=B∧c.Ψ=1∧c.Η=B.Η:=by
  let d:ℕ:=max B.Ι 1
  let Ρ:ℝ≥0:=1/(400*(d:ℝ≥0))
  have hd:0<d:=by simp[d]
  have ES:0<Ρ:=by
    dsimp[Ρ]
    positivity
  have zu:Ρ≤1/(100*(d:ℝ≥0)):=by
    dsimp[Ρ]
    apply Rb (by positivity) (by positivity)
    exact ἂ (by norm_num:(100:ℝ≥0)≤400)
      (by positivity)
  have ET:Ρ≤1:=by
    apply zu.trans
    rw[ᾜ]
    · exact_mod_cast(show 1≤100*d by omega)
    · positivity
  have jt:=Ô Ρ (by simpa[d] using zu)
  have Ax:(100:ℝ)*d*(Ρ:ℝ)≤1/4:=by
    have LW:(Ρ:ℝ)≤1/(400*(d:ℝ)):=by
      exact_mod_cast(show Ρ≤1/(400*(d:ℝ≥0)) by rfl)
    have O6:(0:ℝ)<d:=by exact_mod_cast hd
    calc
      (100:ℝ)*d*(Ρ:ℝ) ≤
          100*d*(1/(400*(d:ℝ))):=by gcongr
      _=1/4:=by field_simp; ring
  have EU :
      ((B.ai (1+Ρ)).Η.card:ℝ) ≤
        2*((B.ai (1-Ρ)).Η.card:ℝ):=by
    nlinarith[jt.1,jt.2,Ax,
      show(0:ℝ)<B.Η.card by
        exact_mod_cast B.aE.card_pos]
  have ch :
      (B.ai (1+Ρ)).Η.card ≤
        2*(B.ai (1-Ρ)).Η.card:=by
    exact_mod_cast EU
  let c:bt (G:=G):=
    { ba:=B
      Ψ:=1
      Ï:=Ρ
      é:=⟨ES,ET,ch⟩ }
  refine ⟨c,rfl,rfl, ?_⟩
  simp only[Η,c,aj.oG]
end bt
def di {Λ:Finset G} (s:aA Λ)
  (child:bt (G:=G)) (x:G)
  (gy:0<Ó s.Θ.set child.Η x) :
  aA Λ where
 Θ:=child.eo
  (dn s.Θ.set child.Η x)
  (bK child.aE gy)
  (dz (B:=child.ba) (Φ:=child.Ψ)
   (A:=s.Θ.set) (C:=child.Η) (x:=x) λ _ h=>h)
 Î:=s.Î-x
 eR:=by
  intro z hz
  have O7:=(e4.mp hz).2
  have Ὦ:=s.eR (x+z) O7
  have heq:z-(s.Î-x)=(x+z)-s.Î:=by abel
  rwa[heq]
@[simp] lemma hQ {Λ:Finset G}
  (s:aA Λ) (child:bt (G:=G)) (x:G)
  (gy:0<Ó s.Θ.set child.Η x) :
  (di s child x gy).Ξ =
   Ó s.Θ.set child.Η x:=by
 change((dn s.Θ.set child.Η x).card:ℝ) /
   child.Η.card=Ó s.Θ.set child.Η x
 exact(bk child.aE x).symm
lemma fb
  {Λ:Finset G} (s:aA Λ)
  (child:bt (G:=G)) (x:G)
  {q Á:ℝ} {aq:ℕ}
  (gy:0<Ó s.Θ.set child.Η x)
  (û:q*s.Ξ ≤
   Ó s.Θ.set child.Η x)
  (Ñ:child.ba.Ι≤ s.Ι+aq)
  (ch:exp (-Á)*(s.card:ℝ)≤child.Η.card) :
  dk q aq Á s.Θ
   (di s child x gy).Θ:=by
 refine ⟨?_,Ñ, ?_⟩
 ·change q*s.Ξ ≤
   ((dn s.Θ.set child.Η x).card:ℝ) /
    child.Η.card
  rw[←bk child.aE]
  exact û
 ·change exp (-Á)*(s.Θ.card:ℝ) ≤
   child.Η.card
  exact ch
section sG
variable [MeasurableSpace G] [Α G]
lemma nq
  {D:aj G} {aX a3 S:Finset G} {error:ℝ}
  (ἔ:aX.Nonempty) (Ἥ:a3.Nonempty)
  (jl: ∀ t∈D.Η,
   (aJ (∞) (τ t ((Χ (((Χ ((@mu ℂ _ _) (-aX)) (((indicator S λ _↦(1:_)):G→ ℂ))))) (mu a3))) -
     ((Χ (((Χ ((@mu ℂ _ _) (-aX)) (((indicator S λ _↦(1:_)):G→ ℂ))))) (mu a3))))) ≤
    error) :
  ∀ t∈D.Η,
   |ag.bW aX a3 S t -
     ag.bW aX a3 S 0| ≤
    error*(aX.card:ℝ)*a3.card:=by
 classical
 let F:G→ ℂ:=
  (Χ (((Χ ((@mu ℂ _ _) (-aX)) (((indicator S λ _↦(1:_)):G→ ℂ))))) (mu a3))
 have hF (u:G) :
   F u=Complex.ofReal
    (ag.bW aX a3 S u /
     (aX.card*a3.card:ℝ)):=by
  dsimp only[F]
  rw[os]
  congr 1
  exact ag.d7
   ἔ Ἥ S u
 intro t ht
 have ê: -t∈D.Η:=aj.ec.mpr ht
 have Ὄ :
   ‖(τ (-t) F-F) 0‖ ≤error:=by
  calc
   ‖(τ (-t) F-F) 0‖ ≤(aJ (∞) (τ (-t) F-F)):=
    vw
   _≤error:=by simpa only[F] using jl (-t) ê
 have Hk :
   |(ag.bW aX a3 S t -
     ag.bW aX a3 S 0) /
     (aX.card*a3.card:ℝ)| ≤error:=by
  rw[Rw,ῗ,sub_neg_eq_add,zero_add,
   hF t,hF 0, ←Complex.ofReal_sub,Rf,ᾮ,
   ←UT] at Ὄ
  exact Ὄ
 have ch:(0:ℝ)<(aX.card:ℝ)*a3.card:=
  Ἃ (by exact_mod_cast ἔ.card_pos) (by exact_mod_cast Ἥ.card_pos)
 rw[TE,RT ch] at Hk
 have pO:=(ἲ ch).mp Hk
 nlinarith
omit [Α G] [MeasurableSpace G] in
lemma hU
  (aX a3 S:Finset G) (t:G) :
  ag.bW a3 aX (-S) t =
   ag.bW aX a3 S (-t):=by
 classical
 unfold ag.bW
 rw[ὶ]
 apply Ò rfl
 intro a₁ _
 apply Ò rfl
 intro a₂ _
 have F7 (u:G) :
   ag.bJ (-S) u =
    ag.bJ S (-u):=by
  by_cases hu:u∈ -S
  ·have ê: -u∈S:=by simpa using hu
   simp[ag.bJ,hu,ê]
  ·have ê: -u∉S:=by
    intro h
    apply hu
    simpa using h
   simp[ag.bJ,hu,ê]
 rw[F7]
 have ῡ: -(t+a₂-a₁)= -t+a₁-a₂:=by abel
 rw[ῡ]
 ring
lemma h4
  {D:aj G} {aX a3 S:Finset G} {error:ℝ}
  (ἔ:aX.Nonempty) (Ἥ:a3.Nonempty)
  (jl: ∀ t∈D.Η,
   (aJ (∞) (τ t ((Χ (((Χ ((@mu ℂ _ _) (-a3)) (((indicator ((-S:Finset G)) λ _↦(1:_)):G→ ℂ))))) (mu aX))) -
     ((Χ (((Χ ((@mu ℂ _ _) (-a3)) (((indicator ((-S:Finset G)) λ _↦(1:_)):G→ ℂ))))) (mu aX))))) ≤
    error) :
  ∀ t∈D.Η,
   |ag.bW aX a3 S t -
     ag.bW aX a3 S 0| ≤
    error*(aX.card:ℝ)*a3.card:=by
 classical
 have dc:=nq
  (D:=D) (aX:=a3) (a3:=aX) (S:=-S) (error:=error)
  Ἥ ἔ jl
 intro t ht
 have ê := aj.ec.mpr ht
 have h:=dc (-t) ê
 rw[hU aX a3 S (-t),
  hU aX a3 S 0] at h
 simpa[ä,Ῐ,à] using h
noncomputable def mb (M L:Finset G):ℕ:=
 ⌈1+log (min 1 ((L.card:ℝ)/M.card))⁻¹⌉₊
noncomputable def cm
  (M L:Finset G) (dv:ℝ) (m:ℕ):ℕ:=
 ᾨ (mb M L)
  ((dv/m)/exp 1)
lemma ej
    {A Τ ζ:Finset G} {p:ℕ} {sigma delta:ℝ}
    (data:aW A Τ ζ p sigma delta)
    (cu:delta<1)
    (dv:ℝ) (sH:0<dv)
    (m:ℕ) (hm:m≠0)
    (bl:aj G) (sx:bl.a1)
    (Ρ:ℝ≥0)
    (dy:Ρ+Ρ ≤
      1/(100*(max bl.Ι 1:ℕ):ℝ≥0))
    (ç:ℕ) (pX:0<ç)
    (bm:ℝ)
    (ø: ∀ (T:Finset G) (Κ:Finset (Ε G ℂ)),
      (Κ.card:ℝ) ≤
        aI.bf bl T (1/2) →
      2*dv +
          (2/(ç:ℝ) +
            400*((max bl.Ι 1:ℕ):ℝ) *
              (Ρ+Ρ:ℝ≥0) +
            2*(1/2:ℝ)^m) *
          Real.sqrt
            (((aW.bg A Τ ζ p sigma).card:ℝ) /
              data.aX.card)≤bm) :
    ∃ (T X:Finset G) (Φ:ℝ≥0) (fl:aj G)
      (Κ:Finset (Ε G ℂ)),
      ((((-data.a3).card:ℝ) ^
            cm
              (-(aW.bg A Τ ζ p sigma))
              data.aX dv m/2*bl.Η.card) /
          ((-data.a3+bl.Η).card:ℝ) ^
            cm
              (-(aW.bg A Τ ζ p sigma))
              data.aX dv m≤T.card) ∧
      T⊆bl.Η∧X.Nonempty ∧
      (Κ.card:ℝ) ≤
        aI.bf bl T (1/2) ∧
      1/2≤Φ∧Φ≤1 ∧
      fl=bl.ai (Φ *
        aI.cJ bl T (1/2)) ∧
      Nonempty
        (cb data fl (Ρ+Ρ)
          (fl.ai Ρ).Η Κ.card
          ((ç*ag.a6
              (aI.bf bl T (1/2))) ^
              Κ.card *
            4^(bl.Ι+Κ.card))
          bm):=by
  classical
  let S :=
    aW.bg A Τ ζ p sigma
  have ᾏ:=data.lR cu
  have Gi:(-data.a3).Nonempty:=by
    obtain ⟨a,ha⟩:=ᾏ.2
    exact ⟨-a,by simpa using ha⟩
  have Ø:S.Nonempty:=by
    simpa[S] using data.gL cu
  have LX:(-S).Nonempty:=by
    obtain ⟨s,hs⟩:=Ø
    exact ⟨-s,by simpa using hs⟩
  obtain ⟨T,X,z,Φ,fl,Κ,R,ui,_hzT,_hX,
      ᾉ,nk,ᾐ,lj,ᾶ,AT,
      ᾤ,_hDeltaSpec,qk,Ῥ,yc,vZ,
      jl⟩:=
    ag.fk
      (A:=-data.a3) Gi dv sH m hm
      (-S) data.aX LX ᾏ.1 bl sx Ρ dy
      ç pX
  let n :=
    ç*ag.a6
      (aI.bf bl T (1/2))
  let p3:ℝ:=
    2*dv +
      (4*pi*(Κ.card:ℝ) *
          ((((n:ℕ):ℝ≥0)⁻¹ :ℝ)) +
        400*((max bl.Ι 1:ℕ):ℝ) *
          (Ρ+Ρ:ℝ≥0) +
        2*(1/2:ℝ)^m) *
      Real.sqrt ((S.card:ℝ)/data.aX.card)
  have Ᾰ :
      4*pi*(Κ.card:ℝ) *
          ((((n:ℕ):ℝ≥0)⁻¹ :ℝ))≤2/(ç:ℝ):=by
    simpa[n] using
      (ag.sw
        (aI.bf bl T (1/2))
        Κ.card ç ᾤ pX)
  have ὧ:p3≤bm:=by
    calc
      _ ≤
          2*dv +
            (2/(ç:ℝ) +
              400*((max bl.Ι 1:ℕ):ℝ) *
                (Ρ+Ρ:ℝ≥0) +
              2*(1/2:ℝ)^m) *
            Real.sqrt ((S.card:ℝ)/data.aX.card):=by
        dsimp only[p3]
        gcongr
      _≤bm:=by simpa[S] using ø T Κ ᾤ
  refine ⟨T,X,Φ,fl,Κ, ?_,ui,ᾉ,ᾤ,
    ᾐ,lj,ᾶ,⟨?_⟩⟩
  · simpa[S,cm,mb] using nk
  refine
    { child:=R
      k6:=qk
      rN:= ?_
      tF:=yc
      nM:= ?_
      oY:= ?_ }
  · simpa[ᾶ] using Ῥ
  · simpa[n,SZ] using vZ
  · have uj:=h4
      ᾏ.1 ᾏ.2 (D:=R) (error:=p3) (by
        intro t ht
        simpa[S,n,p3,à] using jl t ht)
    intro t ht
    calc
      _
          ≤ p3*(data.aX.card:ℝ)*data.a3.card:=by
            simpa[S] using uj t ht
      _≤bm*(data.aX.card:ℝ)*data.a3.card:=by
        gcongr
end sG
def þ {Λ:Finset G} (s:aA Λ)
  (ak aB:bt (G:=G)) (Μ:ℝ):Prop:=
 ∃ x∈s.e9,
  (1-Μ)*s.Ξ ≤
   Ó s.Θ.set ak.Η x ∧
  (1-Μ)*s.Ξ ≤
   Ó s.Θ.set aB.Η x
end
end ay.ah
end
section
open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ComplexOrder ENNReal NNReal Pointwise
namespace ay.fu
noncomputable section
variable {G:Type*} [Δ G] [Β G] [Γ G]
lemma ot (f g:G→ℝ) :
  ao f g=(Χ f g):=by
 funext x
 rw[ao,ᾂ]
lemma es (f g:G→ℝ) :
  ἆ f g=(al f g):=by
 funext x
 rw[ἆ,eL]
 simp
lemma k7 (D E:Finset G) :
  ((↑) ∘ aN.bh D E:G→ℝ) =
   hJ.c4 D E:=by
 rw[hJ.c4,
  ot,
  es,
  es]
 simp only[aN.bh,
  aN.dU,NNReal.gF,
  NNReal.oD,NNReal.iF,
  aN.eQ]
 exact(kr
  (af D) (af D)
  (af E) (af E)).symm
omit [Β G] in
private lemma pr
  (a:G→ℝ) (p:ℕ) (x:G) :
  |ao a a x| ^p =
   (Fintype.card G:ℝ)^p *
    ‖dT.Ω ((↑) ∘ a) ((↑) ∘ a) x‖ ^p:=by
 have h:=è norm
  (jw.k2 a a x)
 simp only[Rf,ἑ,UA] at h
 have h': |ao a a x| =
   (Fintype.card G:ℝ) *
    ‖dT.Ω ((↑) ∘ a) ((↑) ∘ a) x‖:=by
  simpa only[ᾮ] using h
 rw[h',Ἀ]
omit [Β G] in
private lemma k8
  (a:G→ℝ) (p:ℕ) (x:G) :
  |ἆ a a x| ^p =
   (Fintype.card G:ℝ)^p *
    ‖dT.a2 ((↑) ∘ a) ((↑) ∘ a) x‖ ^p:=by
 have h:=è norm
  (jw.ga a x)
 simp only[Rf,ἑ,UA] at h
 have h': |ἆ a a x| =
   (Fintype.card G:ℝ) *
    ‖dT.a2 ((↑) ∘ a) ((↑) ∘ a) x‖:=by
  simpa only[ᾮ] using h
 rw[h',Ἀ]
omit [Β G] in
private lemma ka
  (w a:G→ℝ) (p:ℕ) :
  È w (ao a a) p =
   (Fintype.card G:ℝ)^p *
    ∑ x:G,w x *
     ‖dT.Ω ((↑) ∘ a) ((↑) ∘ a) x‖ ^p:=by
 classical
 unfold È
 rw[á]
 apply Ò rfl
 intro x _
 rw[pr]
 ring
omit [Β G] in
private lemma h5
  (w a:G→ℝ) (p:ℕ) :
  È w (ἆ a a) p =
   (Fintype.card G:ℝ)^p *
    ∑ x:G,w x *
     ‖dT.a2 ((↑) ∘ a) ((↑) ∘ a) x‖ ^p:=by
 classical
 unfold È
 rw[á]
 apply Ò rfl
 intro x _
 rw[k8]
 ring
lemma ra
  {B:aj G} {Ο:ℝ≥0} {D E:Finset G}
  (Ô:B.a1) (ò:0<Ο)
  (ῴ:4*Ο ≤
   1/(400*(max B.Ι 1:ℕ):ℝ≥0))
  (Ð:D.Nonempty) (Þ:E.Nonempty)
  (gn:D⊆(B.ai Ο).Η)
  (lk:E⊆(B.ai Ο).Η)
  {p:ℕ} (hp:p≠0) (mx:Even p) (a:G→ℝ) :
  È (af B.Η)
    (ao a a) p ≤
   2*È
    ((↑) ∘ aN.bh D E)
    (ἆ a a) p:=by
 have h:=hJ.kF
  Ô ò ῴ Ð Þ gn lk hp mx ((↑) ∘ a)
 rw[←k7 D E] at h
 have Ý:0≤(Fintype.card G:ℝ)^p:=by positivity
 have hmul:=Å h Ý
 rw[ka,
  h5]
 nlinarith
lemma tG
  {B:aj G} {Ο:ℝ≥0} {D E:Finset G}
  (Ô:B.a1) (ò:0<Ο)
  (ῴ:4*Ο ≤
   1/(400*(max B.Ι 1:ℕ):ℝ≥0))
  (Ð:D.Nonempty) (Þ:E.Nonempty)
  (gn:D⊆(B.ai Ο).Η)
  (lk:E⊆(B.ai Ο).Η)
  {p:ℕ} (hp:0<p) (mx:Even p) (a:G→ℝ) :
  an.aM (af B.Η)
    (ao a a) p ≤
   2*an.aM
    ((↑) ∘ aN.bh D E)
    (ἆ a a) p:=by
 have ju:an.cw
   (af B.Η):=
  ⟨ὡ B.Η,
   ᾁ B.aE⟩
 have rq:an.cw
   ((↑) ∘ aN.bh D E):=
  ⟨λ x↦by
   exact_mod_cast(show 0≤aN.bh D E x by
    exact aN.gS D E x),
   by
    simpa using è (λ z:ℝ≥0↦(z:ℝ))
     (aN.i7 Ð Þ)⟩
 apply an.lv
  ju rq hp
 exact ra Ô ò ῴ Ð Þ gn lk
  hp.ne' mx a
variable [MeasurableSpace G] [Α G]
lemma nr
  {B:aj G} (Ô:B.a1)
  {A:Finset G} (ξ:A.Nonempty) (zq:A⊆B.Η)
  {D E:Finset G} (Ð:D.Nonempty) (Þ:E.Nonempty)
  {Ρ:ℝ≥0}
  (dy:Ρ≤1/(100*(max B.Ι 1:ℕ):ℝ≥0))
  (ῶ: ∀ t,aN.bh D E t≠0 →
   t∈(B.ai Ρ).Η)
  {Μ:ℝ} (Ἷ:0<Μ) (oV:Μ≤1)
  (ú :
   2*((A.card:ℝ)⁻¹ *
     (200*((max B.Ι 1:ℕ):ℝ)*(Ρ:ℝ))) +
    (B.Η.card:ℝ)⁻¹ *
     (200*((max B.Ι 1:ℕ):ℝ)*(Ρ:ℝ)) ≤
    Μ/8*(B.Η.card:ℝ)⁻¹)
  {p:ℕ} (hp:0<p)
  {tH pI:G→ℝ}
  (ju:an.cw tH)
  (lh :
   an.aM tH pI
     (an.bS p) ≤
    2*an.aM
     ((↑) ∘ aN.bh D E)
     ((al (((@mu (ℝ) _ _) A-mu B.Η)) ((mu A-mu B.Η))))
     (an.bS p))
  (qv :
   an.aM
     ((↑) ∘ aN.bh D E)
     ((al ((@mu (ℝ) _ _) A) (mu A))) (an.cz Μ p) <
    (1+Μ/8)*(B.Η.card:ℝ)⁻¹) :
  an.aM tH pI p ≤
   Μ*(B.Η.card:ℝ)⁻¹:=by
 let nu:=aN.bh D E
 have ft :=
  aN.i7 Ð Þ
 have rq:an.cw ((↑) ∘ nu):=
  ⟨λ x↦by
   exact_mod_cast(show 0≤nu x by
    exact aN.gS D E x),
   by simpa using è (λ z:ℝ≥0↦(z:ℝ)) ft⟩
 have ch:(0:ℝ)<B.Η.card:=by
  exact_mod_cast B.aE.card_pos
 have Ἆ := inv_pos.mpr ch
 apply an.nP
   ju rq Ἷ Ἆ hp (by simpa[nu] using lh) _
   (by simpa[nu] using qv)
 intro Ὤ
 obtain ⟨r,hr,_hreven,Jh,Ib⟩:=
  aN.uk Ô ξ zq Ð Þ dy
   ῶ Ἷ oV ú hp (by simpa[nu] using Ὤ)
 exact ⟨r,hr,Jh,by simpa[nu] using Ib⟩
end
end ay.fu
end
section
open Finset
open scoped BigOperators NNReal
namespace ay
noncomputable section
namespace aj
variable {G:Type*} [Γ G] [Δ G] [Β G]
def rO (m:ℕ) (w r:ℝ):Fin (2*m+1):=
 ⟨min ⌊((r+w)*(m:ℝ))/w⌋₊ (2*m),
  Nat.lt_succ_iff.mpr (Nat.min_le_right _ _)⟩
lemma ou
  {m:ℕ} (hm:0< m) {w r s:ℝ}
  (hw:0≤w) (hr: |r| ≤w) (hs: |s| ≤w)
  (ό:rO m w r=rO m w s) :
  |r-s| ≤w/(m:ℝ):=by
 by_cases vq:w=0
 ·subst w
  have O8:r=0:=by
   apply abs_eq_zero.mp
   exact SC hr (ᾝ r)
  have O9:s=0:=by
   apply abs_eq_zero.mp
   exact SC hs (ᾝ s)
  simp[O8,O9]
 have z7 := SM hw (Ne.symm vq)
 have Ὀ:(0:ℝ)< m:=by exact_mod_cast hm
 let ur:ℝ:=((r+w)*(m:ℝ))/w
 let us:ℝ:=((s+w)*(m:ℝ))/w
 have MO: -w≤r∧r≤w:=(abs_le.mp hr)
 have MP: -w≤ s∧s≤w:=(abs_le.mp hs)
 have Kb:0≤ur:=by
  dsimp[ur]
  exact RS (å (by linarith) Ὀ.le) hw
 have Kc:0≤us:=by
  dsimp[us]
  exact RS (å (by linarith) Ὀ.le) hw
 have Kd:ur≤(2*m:ℕ):=by
  dsimp[ur]
  apply(ἲ z7).2
  push_cast
  nlinarith
 have Ke:us≤(2*m:ℕ):=by
  dsimp[us]
  apply(ἲ z7).2
  push_cast
  nlinarith
 have KT:⌊ur⌋₊<2*m+1:=by
  apply(Uc Kb).2
  exact lt_of_le_of_lt Kd (by exact_mod_cast(Tr (2*m)))
 have KU:⌊us⌋₊<2*m+1:=by
  apply(Uc Kc).2
  exact lt_of_le_of_lt Ke (by exact_mod_cast(Tr (2*m)))
 have BS:⌊ur⌋₊≤2*m:=by omega
 have BT:⌊us⌋₊≤2*m:=by omega
 have vW:⌊ur⌋₊=⌊us⌋₊:=by
  have ᾟ:=è Fin.val ό
  simpa only[rO,ur,us,Nat.min_eq_left BS,
   Nat.min_eq_left BT] using ᾟ
 have MQ := Ti Kb
 have EV := RY ur
 have MR := Ti Kc
 have EW := RY us
 have IZ:ur<us+1:=by
  calc
   ur<((⌊ur⌋₊:ℕ):ℝ)+1:=EV
   _=((⌊us⌋₊:ℕ):ℝ)+1:=by rw[vW]
   _≤us+1:=by gcongr
 have I0:us<ur+1:=by
  calc
   us<((⌊us⌋₊:ℕ):ℝ)+1:=EW
   _=((⌊ur⌋₊:ℕ):ℝ)+1:=by rw[←vW]
   _≤ur+1:=by gcongr
 have yi :
   ur-us=((r-s)*(m:ℝ))/w:=by
  dsimp[ur,us]
  field_simp
  ring
 have BU:((r-s)*(m:ℝ))/w<1:=by
  rw[←yi]
  linarith
 have BV:(-1:ℝ)<((r-s)*(m:ℝ))/w:=by
  rw[←yi]
  linarith
 have Dr:(r-s)*(m:ℝ)<w:=by
  have h:=(Tv z7).mp BU
  simpa only[ἃ] using h
 have Ds: -w<(r-s)*(m:ℝ):=by
  have h:=(SP z7).mp BV
  simpa only[neg_one_mul] using h
 have Kf:r-s<w/(m:ℝ):=
  (SP Ὀ).2 Dr
 have ic: -(w/(m:ℝ))<r-s:=by
  have h:=(Tv Ὀ).2 Ds
  simpa only[neg_div] using h
 exact(abs_lt.2 ⟨ic,Kf⟩).le
def fv (B:aj G) (Φ:ℝ≥0) (m:ℕ)
  (x:↥(B.ai Φ).Η):B.í→Fin (2*m+1):=
 λ γ ↦
  rO m ((Φ:ℝ)*(B.Υ γ.1:ℝ))
   (ï (γ.1 x.1))
omit [Β G] in
private lemma kP
  (B:aj G) (Φ:ℝ≥0) {m:ℕ} (hm:0< m)
  {x y:↥(B.ai Φ).Η}
  (ni:B.fv Φ m x=B.fv Φ m y) :
  x.1-y.1∈(B.ai (Φ/(m:ℝ≥0))).Η:=by
 rw[mem_carrier]
 intro γ oa
 have hx:=(mem_carrier (B.ai Φ) x.1).mp x.2 γ oa
 have hy:=(mem_carrier (B.ai Φ) y.1).mp y.2 γ oa
 simp only[oF,SK] at hx hy ⊢
 rw[map_sub]
 have CW :
   |ï (γ x.1)| ≤(Φ:ℝ)*(B.Υ γ:ℝ):=by
  rwa[←hH]
 have CX :
   |ï (γ y.1)| ≤(Φ:ℝ)*(B.Υ γ:ℝ):=by
  rwa[←hH]
 have vU:=Uu ni ⟨γ,oa⟩
 have hdiv:= ou hm
  (å (by positivity) (by positivity)) CW CX vU
 calc
  _ ≤
    |ï (γ x.1)-ï (γ y.1)|:=
   gu _ _
  _≤((Φ:ℝ)*(B.Υ γ:ℝ))/(m:ℝ):=hdiv
  _=((Φ/(m:ℝ≥0):ℝ≥0):ℝ) *
    (B.Υ γ:ℝ):=by
   push_cast
   field_simp
omit [Β G] in
private lemma ps
  (B:aj G) (Φ:ℝ≥0) {m:ℕ} (hm:0< m)
  (a:B.í→Fin (2*m+1)) :
  Fintype.card
    {x:↥(B.ai Φ).Η// B.fv Φ m x=a} ≤
   (B.ai (Φ/(m:ℝ≥0))).Η.card:=by
 classical
 by_cases jv:Nonempty
   {x:↥(B.ai Φ).Η// B.fv Φ m x=a}
 ·let x₀  :=
   Classical.choice jv
  let f :
    {x:↥(B.ai Φ).Η// B.fv Φ m x=a} →
     ↥(B.ai (Φ/(m:ℝ≥0))).Η:=
   λ x ↦
    ⟨x.1.1-x₀.1.1,
     kP B Φ hm
      (x.2.trans x₀.2.symm)⟩
  have hf:Injective f:=by
   intro x y ni
   apply RI
   apply RI
   have ᾟ:=è Subtype.val ni
   dsimp[f] at ᾟ
   exact S8 ᾟ
  calc
   _
                                            ≤
     Fintype.card ↥(B.ai (Φ/(m:ℝ≥0))).Η:=
    R1 f hf
   _=(B.ai (Φ/(m:ℝ≥0))).Η.card:=
    Rx _
 ·simp only[To] at jv
  simp
omit [Β G] in
lemma h6
  (B:aj G) (Φ:ℝ≥0) {m:ℕ} (hm:0< m) :
  (B.ai Φ).Η.card ≤
   (2*m+1)^B.Ι *
    (B.ai (Φ/(m:ℝ≥0))).Η.card:=by
 classical
 let S:=B.í→Fin (2*m+1)
 let q := B.fv Φ m
 have jv: ∀ a:S,
   Fintype.card {x:↥(B.ai Φ).Η// q x=a} ≤
    (B.ai (Φ/(m:ℝ≥0))).Η.card:=by
  intro a
  exact ps B Φ hm a
 have AA:Fintype.card S=(2*m+1)^B.Ι:=by
  dsimp[S,Ι]
  rw[TC]
  simp
 rw[←Rx (B.ai Φ).Η, ←AA]
 by_contra h
 have Ί :
   Fintype.card S*(B.ai (Φ/(m:ℝ≥0))).Η.card <
    Fintype.card ↥(B.ai Φ).Η:=by omega
 obtain ⟨a,ha⟩:=
  Rk (f:=q) Ί
 have Em: #{x | q x=a} ≤
   (B.ai (Φ/(m:ℝ≥0))).Η.card:=by
  rw[←SL]
  exact jv a
 exact(ῑ Em) ha
omit [Β G] in
lemma cM
  (B:aj G) (Φ:ℝ≥0) {m:ℕ} (hm:0< m) :
  (B.ai Φ).Η.card ≤
   (3*m)^B.Ι *
    (B.ai (Φ/(m:ℝ≥0))).Η.card:=by
 classical
 calc
  _ ≤
    (2*m+1)^B.Ι *
     (B.ai (Φ/(m:ℝ≥0))).Η.card:=
   h6 B Φ hm
  _≤(3*m)^B.Ι *
     (B.ai (Φ/(m:ℝ≥0))).Η.card:=by
   apply QQ
   apply R4
   omega
end aj
end
end ay
end
section
open Finset
open scoped NNReal Pointwise
namespace ay
noncomputable section
lemma lX
  {G:Type*} [Γ G] [Δ G]
  (B:aj G) (X:Finset G) {beta Ο:ℝ}
  (Ἤ:0<beta) (ò:0<Ο)
  (Ἵ:X.Nonempty)
  (ch:beta*(B.Η.card:ℝ)≤(X.card:ℝ)) :
  aI.bf B X Ο ≤
   2*(1+log (2/beta))/Ο^2:=by
 have wN:(0:ℝ)<B.Η.card:=by
  exact_mod_cast B.aE.card_pos
 have LY:(0:ℝ)<X.card:=by
  exact_mod_cast Ἵ.card_pos
 have ἕ :
   2*(B.Η.card:ℝ)/X.card≤2/beta:=by
  rw[Sy LY Ἤ]
  nlinarith
 have Ic:0<2*(B.Η.card:ℝ)/X.card:=by
  positivity
 have ei  :=
  ᾆ Ic ἕ
 have Kg := SY ò
 rw[aI.bf]
 apply(R9 Kg).2
 nlinarith
lemma fQ
  {G:Type*} [Γ G] [Δ G]
  (B:aj G) (X:Finset G) {beta:ℝ}
  (Ἤ:0<beta) (Ἵ:X.Nonempty)
  (ch:beta*(B.Η.card:ℝ)≤(X.card:ℝ)) :
  aI.bf B X (1/2) ≤
   8*(1+log (2/beta)):=by
 have h:=
  lX B X Ἤ
   (by norm_num:(0:ℝ)<1/2) Ἵ ch
 convert h using 1
 ring
lemma ov
  {α:Type*} (S:Finset α) {D:ℝ}
  (ch:(S.card:ℝ)≤D) :
  S.card≤⌈D⌉₊:=by
 exact_mod_cast ch.trans (Rr D)
end
end ay
end
section
open Finset
open scoped NNReal
namespace ay.ar
noncomputable section
def ax (d aq:ℕ):ℕ:=
 1024*(d+1)*aq
def bn (d aq:ℕ):ℕ:=
 819200*ax d aq*2^d
def bd (d aq:ℕ):ℕ:=
 76800*ax d aq*2^(d+1)
lemma iH {d aq:ℕ} (ô:0<aq) :
  0<ax d aq:=by
 unfold ax
 positivity
lemma y9 {d aq:ℕ} (ô:0<aq) :
  1≤ax d aq:=
 Nat.one_le_iff_ne_zero.mpr (iH ô).ne'
lemma i8 {d aq r:ℕ}
  (ô:0<aq)
  (Ñ:r≤ax d aq) :
  max r 1≤ax d aq:=
       max_le Ñ (y9 ô)
lemma mc {d aq:ℕ} (ô:0<aq) :
  0<bn d aq:=by
 unfold bn
 exact Ὑ
  (Ὑ (by norm_num) (iH ô))
  (ᾅ (by norm_num) _)
lemma md {d aq:ℕ} (ô:0<aq) :
  0<bd d aq:=by
 unfold bd
 exact Ὑ
  (Ὑ (by norm_num) (iH ô))
  (ᾅ (by norm_num) _)
lemma p6 {d aq r:ℕ}
  (ô:0<aq)
  (Ñ:r≤ax d aq) :
  100*max r 1≤bn d aq:=by
 have Ἴ:=i8 ô Ñ
 unfold bn
 calc
  _ ≤100*ax d aq:=
   ὄ 100 Ἴ
  _≤819200*ax d aq*2^d:=by
   have qI:100≤819200:=by omega
   calc
    _ ≤819200*ax d aq:=
     QQ _ qI
    _≤819200*ax d aq*2^d:=
     Q4 _ (ᾅ (by norm_num) _)
lemma tI {d aq r:ℕ}
  (ô:0<aq)
  (Ñ:r≤ax d aq) :
  ((bn d aq:ℝ≥0)⁻¹) ≤
   1/(100*(max r 1:ℕ):ℝ≥0):=by
 rw[ῆ]
 have Ὢ:(0:ℝ≥0)<bn d aq:=by
  exact_mod_cast mc ô
 have ῲ:(0:ℝ≥0)<100*(max r 1:ℕ):=by
  positivity
 apply(RJ Ὢ ῲ).2
 exact_mod_cast p6 ô Ñ
lemma wd {d aq r:ℕ}
  (ô:0<aq)
  (Ñ:r≤ax d aq)
  {Ξ:ℝ}
  (û:1/(2:ℝ)^d≤Ξ) :
  400*((max r 1:ℕ):ℝ) *
    ((((bn d aq:ℕ):ℝ≥0)⁻¹ :ℝ≥0):ℝ) ≤
   (1/512:ℝ)*Ξ/4:=by
 change 400*((max r 1:ℕ):ℝ) *
   (bn d aq:ℝ)⁻¹ ≤(1/512:ℝ)*Ξ/4
 have Ἴ:=i8 ô Ñ
 have EX :
   819200*max r 1*2^d≤bn d aq:=by
  unfold bn
  exact QQ (2^d)
   (ὄ 819200 Ἴ)
 have hbound :
   (819200:ℝ)*(max r 1:ℕ)*(2:ℝ)^d ≤
    (bn d aq:ℝ):=by
  exact_mod_cast EX
 have Hl:(0:ℝ)<bn d aq:=by
  exact_mod_cast mc ô
 have xE :
   (0:ℝ)<(819200:ℝ)*(max r 1:ℕ)*(2:ℝ)^d:=by
  positivity
 have hinv :
   (bn d aq:ℝ)⁻¹ ≤
    ((819200:ℝ)*(max r 1:ℕ)*(2:ℝ)^d)⁻¹:=
  (RJ Hl xE).2 hbound
 calc
  _ ≤
    400*((max r 1:ℕ):ℝ) *
     ((819200:ℝ)*(max r 1:ℕ)*(2:ℝ)^d)⁻¹:=by
   gcongr
  _=(1/2048:ℝ)*(1/(2:ℝ)^d):=by
   have tc:(0:ℝ)<(max r 1:ℕ):=by positivity
   have Ie:(0:ℝ)<(2:ℝ)^d:=by positivity
   field_simp
   ring
  _≤(1/2048:ℝ)*Ξ:=by
   gcongr
  _=(1/512:ℝ)*Ξ/4:=by ring
lemma nZ {d aq r:ℕ}
  (ô:0<aq)
  (Ñ:r≤ax d aq) :
  200*max r 1≤bd d aq:=by
 have Ἴ:=i8 ô Ñ
 unfold bd
 calc
  _ ≤200*ax d aq:=
   ὄ 200 Ἴ
  _≤76800*ax d aq*2^(d+1):=by
   have qI:200≤76800:=by omega
   calc
    _ ≤76800*ax d aq:=
     QQ _ qI
    _≤76800*ax d aq*2^(d+1):=
     Q4 _ (ᾅ (by norm_num) _)
lemma rb {d aq r:ℕ}
  (ô:0<aq)
  (Ñ:r≤ax d aq) :
  (bd d aq:ℝ≥0)⁻¹ +(bd d aq:ℝ≥0)⁻¹ ≤
   1/(100*(max r 1:ℕ):ℝ≥0):=by
 have si:=nZ ô Ñ
 have Ὢ:(0:ℝ≥0)<bd d aq:=by
  exact_mod_cast md ô
 have ῲ:(0:ℝ≥0)<200*(max r 1:ℕ):=by
  positivity
 have hinv :
   (bd d aq:ℝ≥0)⁻¹ ≤
    (200*(max r 1:ℕ):ℝ≥0)⁻¹:=by
  apply(RJ Ὢ ῲ).2
  exact_mod_cast si
 calc
  _ ≤
    (200*(max r 1:ℕ):ℝ≥0)⁻¹ +
     (200*(max r 1:ℕ):ℝ≥0)⁻¹:=
   Sr hinv hinv
  _=1/(100*(max r 1:ℕ):ℝ≥0):=by
   have tc:(0:ℝ≥0)<(max r 1:ℕ):=by positivity
   field_simp
   norm_num
end
end ay.ar
end
section
open Filter Finset
open scoped Topology
namespace ay
noncomputable def ü (N:ℕ):ℕ:=
 addRothNumber (Finset.Icc 1 N)
lemma vC (N:ℕ):ü N=rothNumberNat N:=by
 rw[ü, ←Finset.Ico_add_one_right_eq_Icc,addRothNumber_Ico]
 simp
lemma nt
  {c beta:ℝ} (hc:0<c) (Ἤ:0<beta) (C:ℝ) :
  Tendsto
   (λ N:ℕ =>
    (log (N:ℝ))^C *
     exp (-c*(log (N:ℝ))^beta))
   atTop (nhds 0):=by
 have ei:Tendsto (λ N:ℕ=>log (N:ℝ)) atTop atTop:=
  Real.tendsto_log_atTop.comp Sa
 have hpow:Tendsto (λ N:ℕ=>(log (N:ℝ))^beta) atTop atTop:=
  (UR Ἤ).comp ei
 have h:=
  (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (C/beta) c hc).comp hpow
 refine h.congr' ?_
 filter_upwards[eventually_gt_atTop 1] with N î
 have ql:0≤log (N:ℝ):=
  Ἲ (by exact_mod_cast î.le)
 change
  ((log (N:ℝ))^beta)^(C/beta) *
    exp (-c*(log (N:ℝ))^beta) =
   (log (N:ℝ))^C *
    exp (-c*(log (N:ℝ))^beta)
 congr 1
 rw[←S0 ql]
 congr 1
 field_simp[Ἤ.ne']
lemma m1
  {K c beta:ℝ} (æ:0≤K) (hc:0<c) (Ἤ:0<beta)
  (AX: ∀ᶠ N:ℕ in atTop,
   (ü N:ℝ) ≤
    K*(N:ℝ)*exp (-c*(log (N:ℝ))^beta))
  (C:ℝ) :
  (λ N:ℕ=>(ü N:ℝ))=O[atTop]
   (λ N:ℕ=>(N:ℝ)/(log (N:ℝ))^C):=by
 have we:=
  nt hc Ἤ C
 have ø: ∀ᶠ N:ℕ in atTop,
   (log (N:ℝ))^C *
     exp (-c*(log (N:ℝ))^beta)≤1:=
  we.eventually (Iic_mem_nhds (by norm_num:(0:ℝ)<1))
 refine Asymptotics.IsBigO.of_bound K ?_
 filter_upwards[AX,ø,eventually_gt_atTop 1] with N hbound Ig î
 have zv:0≤(N:ℝ):=by positivity
 have Gj:0<log (N:ℝ):=
  Sv (by exact_mod_cast î)
 have w7:0<(log (N:ℝ))^C:=
  SQ Gj C
 rw[RA (Q5 (ü N))]
 rw[RA (RS zv w7.le)]
 apply hbound.trans
 have Ih :
   exp (-c*(log (N:ℝ))^beta) ≤
    1/(log (N:ℝ))^C:=by
  rw[ἇ w7]
  simpa[ä] using Ig
 calc
  K*(N:ℝ)*exp (-c*(log (N:ℝ))^beta) ≤
    K*(N:ℝ)*(1/(log (N:ℝ))^C):=
   Å Ih (å æ zv)
  _=K*((N:ℝ)/(log (N:ℝ))^C):=by ring
end ay
end
section
open scoped BigOperators
open Finset
namespace ay
namespace aw
variable {G:Type*} [Δ G] [Γ G]
noncomputable def uo (f:G→ℝ):ℝ:=
 (∑ x,f x)/Fintype.card G
noncomputable def indicator (C:Finset G) (x:G):ℝ:=
 open scoped Classical in
 if x∈C then 1 else 0
noncomputable def af (C:Finset G) (x:G):ℝ:=
 (Fintype.card G:ℝ)/C.card*indicator C x
noncomputable def Ç (B:Finset G) (f:G→ℝ):ℝ:=
 (∑ x∈B,f x)/B.card
noncomputable def Ἔ (C B:Finset G):ℝ:=
 C.card/B.card
noncomputable def ἡ (B:Finset G) (p:ℕ) (f:G→ℝ):ℝ:=
 Ç B λ x↦ |f x| ^p
noncomputable def θ (f:G→ℝ) (C:Finset G):ℝ:=
 uo λ x↦f x*af C x
lemma mU {C:Finset G} (Ã:C.Nonempty) (f:G→ℝ) :
  θ f C=Ç C f:=by
 classical
 unfold θ Ç uo af indicator
 rw[show(∑ x:G,f x *
   ((Fintype.card G:ℝ)/(C.card:ℝ)*if x∈C then 1 else 0)) =
   (Fintype.card G:ℝ)/(C.card:ℝ)* ∑ x∈C,f x by
  simp_rw[Td,Ἣ,mul_zero]
  simp only[←ᾛ]
  simp only[subset_univ,filter_mem_eq_of_subset]
  rw[←Ἕ]
  exact ä _ _]
 have Pa:(C.card:ℝ)≠0:=by exact_mod_cast Ã.card_ne_zero
 have yj:(Fintype.card G:ℝ)≠0:=by
  exact_mod_cast(SN:Fintype.card G≠0)
 field_simp
omit [Γ G] [Δ G] in
lemma g1 {C:Finset G} (f:G→ℝ) :
  |Ç C f| ≤Ç C λ x↦ |f x|:=by
 unfold Ç
 calc
  _ =
    |(∑ x∈C,f x)| /(C.card:ℝ):=by
   rw[TE]
   congr 1
   exact ἳ (Q5 C.card)
  _≤(∑ x∈C, |f x|)/(C.card:ℝ):=
   ῖ (TQ f C) (by positivity)
omit [Γ G] [Δ G] in
lemma mH {C:Finset G} (Ã:C.Nonempty)
  (p:ℕ) (f:G→ℝ) :
  (Ç C λ x↦ |f x|)^p≤ἡ C p f:=by
 let w:G→ℝ:=λ _↦(C.card:ℝ)⁻¹
 have hw: ∀ x∈C,0≤w x:=by
  intro x hx
  exact inv_nonneg.mpr (by positivity)
 have Pb: ∑ x∈C,w x=1:=by
  simp[w,Ã.card_ne_zero]
 have hz: ∀ x∈C,0≤ |f x|:=by
  intro x hx
  positivity
 have h:=Real.pow_arith_mean_le_arith_mean_pow C w (λ x↦ |f x|)
  hw Pb hz p
 simpa[Ç,ἡ,w,Ri,á] using h
lemma s7 {B C:Finset G} (Ã:C.Nonempty)
  (ῇ:C⊆B) (p:ℕ) (f:G→ℝ) :
  Ἔ C B* |θ f C| ^p≤ἡ B p f:=by
 have É := Ã.mono ῇ
 have ᾡ: |θ f C| ^p≤ἡ C p f:=by
  rw[mU Ã]
  calc
   _
     ≤ (Ç C λ x↦ |f x|)^p:=
      ἤ (ᾝ _) (g1 f) p
   _≤ἡ C p f:=mH Ã p f
 have ΰ:0≤Ἔ C B:=by
  unfold Ἔ
  positivity
 calc
  _
    ≤ Ἔ C B*ἡ C p f:=Å ᾡ ΰ
  _=(∑ x∈C, |f x| ^p)/B.card:=by
   unfold Ἔ ἡ Ç
   field_simp[Ã.card_ne_zero,É.card_ne_zero]
  _≤(∑ x∈B, |f x| ^p)/B.card:=by
   apply ῖ _ (by positivity)
   exact Ry ῇ λ _ _ _↦by positivity
  _=ἡ B p f:=rfl
lemma rd {B C:Finset G} (Ã:C.Nonempty)
  (ῇ:C⊆B) (p:ℕ) (_hp:0<p) (f:G→ℝ)
  (Ὗ bo ε:ℝ) (Ἆ:0≤bo) (hε:0≤ε)
  (û:(2/3:ℝ)^p≤Ἔ C B)
  (ew: |(Ὗ-bo)-θ f C| ≤ε*bo/4) :
  |Ὗ-bo| ≤ε*bo ∨
   (ε*bo/2)^p≤ἡ B p f:=by
 by_cases Ύ: |Ὗ-bo| ≤ε*bo
 ·exact Or.inl Ύ
 right
 have JK: |Ὗ-bo| ≤
   |(Ὗ-bo)-θ f C| + |θ f C|:=by
  calc
   _ =
     |((Ὗ-bo)-θ f C)+θ f C|:=by ring_nf
   _≤ |(Ὗ-bo)-θ f C| + |θ f C|:=UP _ _
 have ᾡ:3*(ε*bo)/4< |θ f C|:=by
  have Ὤ := ᾙ Ύ
  nlinarith
 have ΰ:0≤Ἔ C B:=by
  unfold Ἔ
  positivity
 have Gk :=
  ἤ (by positivity) ᾡ.le p
 have AY  :=
        ὤ û Gk (by positivity) ΰ
 calc
  _ =
    (2/3:ℝ)^p*(3*(ε*bo)/4)^p:=by
   rw[←Ἀ]
   congr 1
   ring
  _≤Ἔ C B* |θ f C| ^p:=AY
  _≤ἡ B p f:=s7 Ã ῇ p f
lemma n0 {B C:Finset G} (Ã:C.Nonempty)
  (ῇ:C⊆B) (p:ℕ) (hp:0<p) (f:G→ℝ)
  (Ὗ bo:ℝ) (Ἆ:0<bo)
  (û:(2/3:ℝ)^p≤Ἔ C B)
  (ew: |(Ὗ-bo)-θ f C| ≤bo/8) :
  bo/2≤Ὗ ∨
   (bo/4)^p≤ἡ B p f:=by
 have An: |(Ὗ-bo)-θ f C| ≤
   (1/2:ℝ)*bo/4:=by
  convert ew using 1; ring
 have LZ:=rd Ã ῇ p hp f Ὗ bo
  (1/2:ℝ) Ἆ.le (by norm_num) û An
 rcases LZ with Ύ | ὸ
 ·left
  have ic:=(abs_le.mp Ύ).1
  linarith
 ·right
  convert ὸ using 1; ring
lemma nv {B C:Finset G} (Ã:C.Nonempty)
  (ῇ:C⊆B) (p:ℕ) (hp:0<p) (f:G→ℝ)
  (Ὗ bo:ℝ) (Ἆ:0<bo)
  (û:(2/3:ℝ)^p≤Ἔ C B)
  (ew: |(Ὗ-bo)-θ f C| ≤bo/8)
  (ee:ἡ B p f≤(bo/8)^p) :
  bo/2≤Ὗ:=by
 rcases n0 Ã ῇ p hp f Ὗ bo Ἆ
  û ew with Ύ | ὸ
 ·exact Ύ
 ·have Nr := Nat.ne_of_gt hp
  have Ii:(bo/8)^p<(bo/4)^p:=by
   apply pow_lt_pow_left₀
   ·nlinarith
   ·positivity
   ·exact Nr
  have:(bo/4)^p≤(bo/8)^p:= ὸ.trans ee
  exact(ῑ this Ii).elim
end aw
end ay
end
section
open Finset
namespace ay
namespace aO
noncomputable section
variable {G:Type*} [Γ G] [Δ G] [Β G]
def Û (S:Finset G):Finset G:=
 S.image λ x↦x+x
omit [Δ G] in
@[simp] lemma m2 {S:Finset G} {x:G} :
  x∈Û S↔ ∃ y∈S,y+y=x:=by
 simp[Û]
omit [Δ G] in
lemma eJ {S:Finset G} (Ø:S.Nonempty) :
  (Û S).Nonempty:=
       Ø.image _
omit [Δ G] in
lemma qJ {S T:Finset G} (Pc:S⊆T) :
  Û S⊆Û T:=by
 intro x hx
 obtain ⟨y,hy,rfl⟩:=m2.mp hx
 exact m2.mpr ⟨y,Pc hy,rfl⟩
omit [Δ G] in
lemma qK (S:Finset G)
  (Ἦ:Injective (λ x:G↦x+x)) :
  #(Û S)= #S:=
       card_image_of_injective _ Ἦ
omit [Δ G] in
lemma pv (S T:Finset G)
  (Ἦ:Injective (λ x:G↦x+x)) :
  aw.Ἔ (Û S) (Û T) =
   aw.Ἔ S T:=by
 simp only[aw.Ἔ,qK S Ἦ,
  qK T Ἦ]
omit [Β G] in
lemma sI
  {H:Type*} [Γ H] [Δ H] [Β H]
  (B:aj G) (e:G ≃+ H) :
  B.Η.image e=(B.map e).Η:=by
 ext x
 constructor
 ·intro hx
  obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
  exact(aj.oH B e y).2 hy
 ·intro hx
  refine Finset.mem_image.mpr ⟨e.symm x, ?_,by simp⟩
  have AG:=(aj.oH B e (e.symm x)).1
  exact AG (by simpa using hx)
def hY (M:ℕ) (ἄ:Odd M) (B:aj (ZMod M)) :
  aj (ZMod M):=
 B.map (aj.eK M ἄ)
lemma jQ
  {M:ℕ} [NeZero M] (ἄ:Odd M) (B:aj (ZMod M)) :
  Û B.Η=(hY M ἄ B).Η:=by
 rw[Û,hY, ←sI]
 apply Finset.image_congr
 intro x _
 exact aj.sV M ἄ x
@[simp] lemma u8
  (M:ℕ) (ἄ:Odd M) (B:aj (ZMod M)) :
  (hY M ἄ B).Ι=B.Ι:=
       aj.Am B (aj.eK M ἄ)
@[simp] lemma p7
  (M:ℕ) [NeZero M] (ἄ:Odd M) (B:aj (ZMod M)) :
  (hY M ἄ B).Η.card=B.Η.card:=
       aj.tZ M ἄ B
def bb (A' À:Finset G):ℝ:=
 (Fintype.card G:ℝ) *
  qj
   (ao (af A') (af A'))
   (af (Û À))
lemma pw
  (Ἦ:Injective (λ x:G↦x+x))
  (A' À:Finset G) :
  bb A' À =
   (Fintype.card G:ℝ)*(ᾦ A' À:ℝ) *
    (#A':ℝ)⁻¹ ^2*(#À:ℝ)⁻¹:=by
 rw[bb,
  Û,
  jK Ἦ]
 ring
lemma nw
  (Ἦ:Injective (λ x:G↦x+x))
  {A' À:Finset G} (ᾈ:A'.Nonempty) (Ἑ:À.Nonempty) :
  bb A' À =
   (Fintype.card G:ℝ)*(ᾦ A' À:ℝ) /
    ((#A':ℝ)^2*(#À:ℝ)):=by
 rw[pw Ἦ]
 have N0:(#A':ℝ)≠0:=by exact_mod_cast ᾈ.card_ne_zero
 have Ns:(#À:ℝ)≠0:=by exact_mod_cast Ἑ.card_ne_zero
 field_simp
lemma kb
  {A' À:Finset G} (Ἑ:À.Nonempty) :
  bb A' À =
   aw.Ç (Û À) (λ x ↦
    (Fintype.card G:ℝ) *
     ao (af A') (af A') x):=by
 let D:=Û À
 let F:=ao (af A') (af A')
 have Ð := eJ Ἑ
 have ya:(#D:ℝ)≠0:=by exact_mod_cast Ð.card_ne_zero
 unfold bb aw.Ç qj
 change(Fintype.card G:ℝ) *
   ∑ x:G,F x*af D x =
  (∑ x∈D,(Fintype.card G:ℝ)*F x)/(#D:ℝ)
 have vS :
   (∑ x:G,F x*af D x) =
    (∑ x∈D,F x)*(#D:ℝ)⁻¹:=by
  change(∑ x:G,F x*(if x∈D then (#D:ℝ)⁻¹ else 0))=_
  simp only[Td,mul_zero]
  rw[←ᾛ]
  have Ἠ:univ.filter (λ x:G↦x∈D)=D:=by ext; simp
  rw[Ἠ,Ἕ]
 rw[vS]
 rw[show(∑ x∈D,(Fintype.card G:ℝ)*F x) =
   (Fintype.card G:ℝ)* ∑ x∈D,F x by
  rw[á]]
 field_simp
omit [Γ G] in
lemma k9 {S:Finset G} (Ø:S.Nonempty) :
  an.cw (af S):=by
 refine ⟨ὡ S, ?_⟩
 exact ᾁ Ø
omit [Γ G] in
lemma h7
  {S:Finset G} (Ø:S.Nonempty) (p:ℕ) (f:G→ℝ) :
  È (af S) f p =
   aw.ἡ S p f:=by
 have EY:(#S:ℝ)≠0:=by exact_mod_cast Ø.card_ne_zero
 unfold È aw.ἡ aw.Ç
  af
 change(∑ x:G,(if x∈S then (#S:ℝ)⁻¹ else 0)* |f x| ^p) =
  (∑ x∈S, |f x| ^p)/(#S:ℝ)
 simp only[ite_mul,zero_mul]
 rw[←ᾛ]
 have Ἠ:univ.filter (λ x:G↦x∈S)=S:=by ext; simp
 rw[Ἠ]
 rw[←á,ἱ]
 ring
omit [Γ G] in
lemma fc
  {S:Finset G} (Ø:S.Nonempty) {p:ℕ} (hp:0<p)
  (f:G→ℝ) {C:ℝ} (_hC:0≤C)
  (ee :
   an.aM (af S) f p≤C) :
  aw.ἡ S p f≤C^p:=by
 have wL:=k9 Ø
 rw[←h7 Ø p f,
  ←an.jr wL hp]
 exact ἤ
  (an.j3 wL f p) ee p
structure eh (Λ:Finset G) where
 A':Finset G
 À:Finset G
 B:Finset G
 B':Finset G
 translate:G
 Ν:ℝ
 p:ℕ
 f:G→ℝ
 jR:A'.Nonempty
 iZ:À.Nonempty
 kQ:B.Nonempty
 h8:À⊆B'
 fL: ∀ x∈A',x-translate∈Λ
 fm: ∀ x∈À,x-translate∈Λ
 i0:0≤Ν
 kR:Ν*(#B:ℝ)≤(#A':ℝ)
 jS:Ν*(#B':ℝ)≤(#À:ℝ)
 Ἐ:0<p
 gg :
  (2/3:ℝ)^p≤aw.Ἔ À B'
 e7 :
  |(bb A' À -
    (Fintype.card G:ℝ)/(#B:ℝ)) -
    aw.θ f (Û À)| ≤
   ((Fintype.card G:ℝ)/(#B:ℝ))/8
 gh :
  aw.ἡ (Û B') p f ≤
   (((Fintype.card G:ℝ)/(#B:ℝ))/8)^p
noncomputable def cr {Λ:Finset G}
  {s:ah.aA Λ}
  {ak aB:ah.bt (G:=G)} {Μ:ℝ}
  (h:ah.þ s ak aB Μ):G:=
 Classical.choose h
lemma c0 {Λ:Finset G}
  {s:ah.aA Λ}
  {ak aB:ah.bt (G:=G)} {Μ:ℝ}
  (h:ah.þ s ak aB Μ) :
  (1-Μ)*s.Ξ ≤
   Ó s.Θ.set ak.Η (cr h):=
 (Uo h).2.1
lemma ea {Λ:Finset G}
  {s:ah.aA Λ}
  {ak aB:ah.bt (G:=G)} {Μ:ℝ}
  (h:ah.þ s ak aB Μ) :
  (1-Μ)*s.Ξ ≤
   Ó s.Θ.set aB.Η (cr h):=
 (Uo h).2.2
def ì {Λ:Finset G}
  (s:ah.aA Λ) (Μ:ℝ):ℝ:=
 (1-Μ)*s.Ξ
lemma lY
  (Ἦ:Injective (λ x:G↦x+x))
  {A' À:Finset G} (ᾈ:A'.Nonempty) (Ἑ:À.Nonempty)
  {bo:ℝ}
  (ἵ:bo/2≤bb A' À) :
  bo*(#A':ℝ)^2*(#À:ℝ) /
    (2*(Fintype.card G:ℝ)) ≤
   (ᾦ A' À:ℝ):=by
 have hG:(0:ℝ)<Fintype.card G:=by
  exact_mod_cast(Fintype.card_pos:0<Fintype.card G)
 have Kh:(0:ℝ)<(#A':ℝ)^2*(#À:ℝ):=by
  positivity
 rw[nw Ἦ ᾈ Ἑ] at ἵ
 have hmul :
   bo/2*((#A':ℝ)^2*(#À:ℝ)) ≤
    (Fintype.card G:ℝ)*(ᾦ A' À:ℝ):=
  (ἇ Kh).mp ἵ
 rw[ἲ (Ἃ (by norm_num) hG)]
 nlinarith
lemma m3
  (Ἦ:Injective (λ x:G↦x+x))
  {A A' À B':Finset G} (ᾈ:A'.Nonempty) (Ἑ:À.Nonempty)
  (kc:À⊆B') (t:G)
  (Ὸ: ∀ x∈A',x-t∈A)
  (Ὼ: ∀ x∈À,x-t∈A)
  {p:ℕ} (hp:0<p) (f:G→ℝ) {bo:ℝ}
  (Ἆ:0<bo)
  (û:(2/3:ℝ)^p≤aw.Ἔ À B')
  (ew :
   |(bb A' À-bo) -
     aw.θ f (Û À)| ≤bo/8)
  (ee :
   aw.ἡ (Û B') p f≤(bo/8)^p) :
  bo*(#A':ℝ)^2*(#À:ℝ) /
    (2*(Fintype.card G:ℝ))≤(Ὧ A:ℝ):=by
 have Ã := eJ Ἑ
 have ῇ := qJ kc
 have EZ :
   (2/3:ℝ)^p ≤
    aw.Ἔ (Û À) (Û B'):=by
  rwa[pv À B' Ἦ]
 have ἵ  :=
  aw.nv Ã ῇ p hp f
   (bb A' À) bo Ἆ EZ ew ee
 have Ki:=
  lY Ἦ ᾈ Ἑ ἵ
 have E0 :=
  iA t Ὸ Ὼ
 have Dt :
   (ᾦ A' À:ℝ)≤(Ὧ A:ℝ):=by
  exact_mod_cast E0
 exact Ki.trans Dt
lemma kd
  (Ἦ:Injective (λ x:G↦x+x))
  {A A' À B B':Finset G}
  (ᾈ:A'.Nonempty) (Ἑ:À.Nonempty) (É:B.Nonempty)
  (kc:À⊆B') (t:G)
  (Ὸ: ∀ x∈A',x-t∈A)
  (Ὼ: ∀ x∈À,x-t∈A)
  {Ν:ℝ} (Õ:0≤Ν)
  (o2:Ν*(#B:ℝ)≤(#A':ℝ))
  (nA:Ν*(#B':ℝ)≤(#À:ℝ))
  {p:ℕ} (hp:0<p) (f:G→ℝ)
  (û:(2/3:ℝ)^p≤aw.Ἔ À B')
  (ew :
   |(bb A' À -
     (Fintype.card G:ℝ)/(#B:ℝ)) -
     aw.θ f (Û À)| ≤
    ((Fintype.card G:ℝ)/(#B:ℝ))/8)
  (ee :
   aw.ἡ (Û B') p f ≤
    (((Fintype.card G:ℝ)/(#B:ℝ))/8)^p) :
  Ν^3*(#B:ℝ)*(#B':ℝ)/2 ≤
   (Ὧ A:ℝ):=by
 have hG:(0:ℝ)<Fintype.card G:=by
  exact_mod_cast(Fintype.card_pos:0<Fintype.card G)
 have yk:(0:ℝ)< #B:=by exact_mod_cast É.card_pos
 have Ἆ :=
  ὗ hG yk
 have ic:=m3 Ἦ ᾈ Ἑ kc t
  Ὸ Ὼ hp f Ἆ û ew ee
 have Ij  :=
  ἤ (å Õ yk.le) o2 2
 have Kj :
   Ν^3*(#B:ℝ)^2*(#B':ℝ) ≤
    (#A':ℝ)^2*(#À:ℝ):=by
  have hmul:=ὤ Ij nA
   (å Õ (Q5 _)) (sq_nonneg (#A':ℝ))
  nlinarith only[hmul]
 have Ὢ :
   Ν^3*(#B:ℝ)*(#B':ℝ)/2 =
    (Ν^3*(#B:ℝ)^2*(#B':ℝ)) /
     (2*(#B:ℝ)):=by
  field_simp
 have ῲ :
   ((Fintype.card G:ℝ)/(#B:ℝ))*(#A':ℝ)^2 *
     (#À:ℝ)/(2*(Fintype.card G:ℝ)) =
    ((#A':ℝ)^2*(#À:ℝ))/(2*(#B:ℝ)):=by
  field_simp
 rw[ῲ] at ic
 rw[Ὢ]
 exact(ῖ Kj (by positivity)).trans ic
lemma me
  (Ἦ:Injective (λ x:G↦x+x))
  {A A' À B B':Finset G}
  (ᾈ:A'.Nonempty) (Ἑ:À.Nonempty) (É:B.Nonempty)
  (kc:À⊆B') (t:G)
  (Ὸ: ∀ x∈A',x-t∈A)
  (Ὼ: ∀ x∈À,x-t∈A)
  {Ν K:ℝ} {d p:ℕ} (Õ:0≤Ν)
  (o2:Ν*(#B:ℝ)≤(#A':ℝ))
  (nA:Ν*(#B':ℝ)≤(#À:ℝ))
  (hp:0<p) (f:G→ℝ)
  (û:(2/3:ℝ)^p≤aw.Ἔ À B')
  (ew :
   |(bb A' À -
     (Fintype.card G:ℝ)/(#B:ℝ)) -
     aw.θ f (Û À)| ≤
    ((Fintype.card G:ℝ)/(#B:ℝ))/8)
  (ee :
   aw.ἡ (Û B') p f ≤
    (((Fintype.card G:ℝ)/(#B:ℝ))/8)^p)
  (AZ:exp (-K*(d:ℝ)^12)*(Fintype.card G:ℝ)^2 ≤
   Ν^3*(#B:ℝ)*(#B':ℝ)/2) :
  exp (-K*(d:ℝ)^12)*(Fintype.card G:ℝ)^2 ≤
   (Ὧ A:ℝ):=
       AZ.trans<|
  kd Ἦ ᾈ Ἑ É kc t
   Ὸ Ὼ Õ o2 nA hp f û ew ee
lemma kq
  {M:ℕ} [NeZero M] (ἄ:Odd M)
  {A A' À B B':Finset (ZMod M)}
  (ᾈ:A'.Nonempty) (Ἑ:À.Nonempty) (É:B.Nonempty)
  (kc:À⊆B') (t:ZMod M)
  (Ὸ: ∀ x∈A',x-t∈A)
  (Ὼ: ∀ x∈À,x-t∈A)
  {Ν K:ℝ} {d p:ℕ} (Õ:0≤Ν)
  (o2:Ν*(#B:ℝ)≤(#A':ℝ))
  (nA:Ν*(#B':ℝ)≤(#À:ℝ))
  (hp:0<p) (f:ZMod M→ℝ)
  (û:(2/3:ℝ)^p≤aw.Ἔ À B')
  (ew :
   |(bb A' À -
     (Fintype.card (ZMod M):ℝ)/(#B:ℝ)) -
     aw.θ f (Û À)| ≤
    ((Fintype.card (ZMod M):ℝ)/(#B:ℝ))/8)
  (ee :
   aw.ἡ (Û B') p f ≤
    (((Fintype.card (ZMod M):ℝ)/(#B:ℝ))/8)^p)
  (AZ:exp (-K*(d:ℝ)^12) *
    (Fintype.card (ZMod M):ℝ)^2 ≤
   Ν^3*(#B:ℝ)*(#B':ℝ)/2) :
  exp (-K*(d:ℝ)^12) *
    (Fintype.card (ZMod M):ℝ)^2≤(Ὧ A:ℝ):=by
 apply me
  (aj.eK M ἄ).injective ᾈ Ἑ É kc t
  Ὸ Ὼ Õ o2 nA hp f û ew ee
  AZ
end
end aO
end ay
end
section
open Filter Finset
open scoped Topology
namespace ay
def dX (K:ℝ) (Ὠ:ℕ):Prop:=
 0<K ∧
  ∀ (N:ℕ),Ὠ≤N →
   ∀ (A:Finset ℕ),A⊆Finset.Icc 1 N→ A.Nonempty →
    ∀ d:ℕ,
     1≤d →
     log ((N:ℝ)/(#A:ℝ))≤(d:ℝ)*log 2 →
      exp (-K*(d:ℝ)^12)*(N:ℝ)^2 ≤
       (Ὧ A:ℝ)
lemma jA
  {K:ℝ} {Ὠ:ℕ} (AX:dX K Ὠ) :
  ∀ᶠ N:ℕ in atTop,
   (ü N:ℝ) ≤
    (N:ℝ)*exp
     (-(log 2/(2*K^(1/12:ℝ))) *
      (log (N:ℝ))^(1/12:ℝ)):=by
 have æ:0<K:=AX.1
 have ei:Tendsto (λ N:ℕ=>log (N:ℝ)) atTop atTop:=
  Real.tendsto_log_atTop.comp Sa
 have Gl:Tendsto (λ N:ℕ=>log (N:ℝ)/K) atTop atTop:=
  Tendsto.atTop_div_const æ ei
 have wJ :
   Tendsto
    (λ N:ℕ=>(log (N:ℝ)/K)^(1/12:ℝ))
    atTop atTop:=
  (UR (by norm_num:(0:ℝ)<1/12)).comp Gl
 filter_upwards[eventually_ge_atTop Ὠ,eventually_gt_atTop 3,
   wJ.eventually_ge_atTop 2] with N Kk î KV
 obtain ⟨A,z8,sF,E1⟩:=UG (Finset.Icc 1 N)
 have wO: #A=ü N:=by simpa[ü] using sF
 have yl:ü N≤N:=by
  rw[vC]
  exact rothNumberNat_le N
 have Cq:0<ü N:=by
  have Du:({1}:Finset ℕ)⊆Finset.Icc 1 N:=by
   simpa using(show 1≤N by omega)
  have ym:=addRothNumber.mono Du
  have Pd:1≤addRothNumber (Finset.Icc 1 N):=by simpa using ym
  have:0<addRothNumber (Finset.Icc 1 N):=by omega
  simpa[ü] using this
 have ῥ:A.Nonempty:=by
  apply Finset.card_pos.mp
  simpa[wO] using Cq
 have yo:(0:ℝ)<N:=by exact_mod_cast(U5 î)
 have o3:(0:ℝ)<ü N:=by exact_mod_cast Cq
 have w9:(ü N:ℝ)≤N:=by exact_mod_cast yl
 have Dv:(1:ℝ)≤(N:ℝ)/(ü N:ℝ):=by
  rw[one_le_div o3]
  exact w9
 have Dw:(0:ℝ)<(N:ℝ)/(ü N:ℝ):=
  ὗ yo o3
 let q:ℝ:=log ((N:ℝ)/(ü N:ℝ))/log 2
 let d:ℕ:=Nat.ceil q
 have sJ:0<log 2:=Sv (by norm_num)
 have E3:0≤q:=by
  exact RS (Ἲ Dv) sJ.le
 have A0 :
   log ((N:ℝ)/(#A:ℝ))≤(d:ℝ)*log 2:=by
  rw[wO]
  rw[←ἲ sJ]
  simpa[q,d] using Rr q
 have Dx:ü N<N:=by
  apply SM yl
  intro heq
  have E4: #(Finset.Icc 1 N)=N:=by
   rw[Nat.card_Icc]
   omega
  have Nt:A=Finset.Icc 1 N:=by
   apply Finset.eq_of_subset_of_card_le z8
   rw[E4,wO,heq]
  have E5:ThreeAPFree (Finset.Icc 1 N:Set ℕ):=by
   simpa[Nt] using E1
  have ὸ:=E5 (a:=1) (b:=2) (c:=3)
   (by simp[show 1≤N by omega]) (by simp[show 2≤N by omega])
   (by simp[show 3≤N by omega]) (by norm_num)
  omega
 have Kl:0<q:=by
  have E9:(1:ℝ)<(N:ℝ)/(ü N:ℝ):=by
   rw[SP o3]
   norm_num
   exact_mod_cast Dx
  exact ὗ (Sv E9) sJ
 have Eo:1≤d:=by
  exact(Nat.ceil_pos.mpr Kl)
 have qG:=AX.2 N Kk A z8 ῥ d Eo A0
 rw[uR E1,wO] at qG
 have Ik :
   exp (-K*(d:ℝ)^12)*(N:ℝ)^2≤(N:ℝ):=
  qG.trans w9
 have A1 :
   exp (-K*(d:ℝ)^12)*(N:ℝ)≤1:=by
  have pO :
    (exp (-K*(d:ℝ)^12)*(N:ℝ))*(N:ℝ) ≤
     1*(N:ℝ):=by
   simpa[TI,à] using Ik
  exact(TZ pO yo)
 have Dy:log (N:ℝ)≤K*(d:ℝ)^12:=by
  have Fa:=
   ᾆ
    (Ἃ (ᾰ _) yo)
    A1
  rw[ñ (Real.exp_ne_zero _) yo.ne',Real.log_exp,
   Real.log_one] at Fa
  linarith
 have ql:0≤log (N:ℝ):=
  Ἲ (by exact_mod_cast(show 1≤N by omega))
 have BW:0≤log (N:ℝ)/K:=
  RS ql æ.le
 have BX:log (N:ℝ)/K≤(d:ℝ)^12:=by
  rw[ἲ æ]
  simpa[ä] using Dy
 have L0 :
   (log (N:ℝ)/K)^(1/12:ℝ)≤(d:ℝ):=by
  calc
   (log (N:ℝ)/K)^(1/12:ℝ) ≤
     ((d:ℝ)^12)^(1/12:ℝ):=
    Sf BW BX (by norm_num)
   _=(d:ℝ):=by
    convert Sc (show(0:ℝ)≤d by positivity)
     (by norm_num:(12:ℕ)≠0) using 1
    all_goals norm_num
 have KW:(d:ℝ)<q+1:=by
  simpa[d] using Nat.ceil_lt_add_one E3
 have yp :
   (log (N:ℝ)/K)^(1/12:ℝ)/2≤q:=by
  linarith
 have xF :
   (log 2/2) *
     (log (N:ℝ)/K)^(1/12:ℝ) ≤
    log ((N:ℝ)/(ü N:ℝ)):=by
  calc
   (log 2/2) *
     (log (N:ℝ)/K)^(1/12:ℝ) =
     ((log (N:ℝ)/K)^(1/12:ℝ)/2)*log 2:=by ring
   _≤q*log 2:=
    ἂ yp sJ.le
   _=log ((N:ℝ)/(ü N:ℝ)):=by
    simp[q,sJ.ne']
 have Dz:0<K^(1/12:ℝ):=
  SQ æ _
 have A2 :
   (log 2/(2*K^(1/12:ℝ))) *
     (log (N:ℝ))^(1/12:ℝ) =
    (log 2/2) *
     (log (N:ℝ)/K)^(1/12:ℝ):=by
  rw[Real.div_rpow ql æ.le]
  field_simp[Dz.ne']
 have zT :
   exp
     ((log 2/(2*K^(1/12:ℝ))) *
      (log (N:ℝ))^(1/12:ℝ)) ≤
    (N:ℝ)/(ü N:ℝ):=by
  rw[←Real.le_log_iff_exp_le Dw]
  rw[A2]
  exact xF
 have BY :
   (ü N:ℝ) *
     exp
      ((log 2/(2*K^(1/12:ℝ))) *
       (log (N:ℝ))^(1/12:ℝ)) ≤
    (N:ℝ):=by
  have:=(ἇ o3).mp zT
  simpa[ä] using this
 calc
  (ü N:ℝ) ≤
    (N:ℝ) /
     exp
      ((log 2/(2*K^(1/12:ℝ))) *
       (log (N:ℝ))^(1/12:ℝ)):=
   (ἇ (ᾰ _)).2 BY
  _=(N:ℝ) *
    exp
     (-((log 2/(2*K^(1/12:ℝ))) *
      (log (N:ℝ))^(1/12:ℝ))):=by
   rw[Uh,ἱ]
  _=(N:ℝ)*exp
    (-(log 2/(2*K^(1/12:ℝ))) *
     (log (N:ℝ))^(1/12:ℝ)):=by
   congr 2
   ring
lemma m4
  {K:ℝ} {Ὠ:ℕ} (AX:dX K Ὠ)
  (C:ℝ) :
  (λ N:ℕ=>(ü N:ℝ))=O[atTop]
   (λ N:ℕ=>(N:ℝ)/(log (N:ℝ))^C):=by
 have hc:0<log 2/(2*K^(1/12:ℝ)):=by
  exact ὗ (Sv (by norm_num))
   (Ἃ two_pos (SQ AX.1 _))
 apply m1
   (K:=1) (c:=log 2/(2*K^(1/12:ℝ)))
   (beta:=(1/12:ℝ)) Us hc (by norm_num) _ C
 simpa using jA AX
end ay
end
section
open Finset
open scoped NNReal
namespace ay
def f1 (K:ℝ):Prop:=
 0<K ∧
  ∀ (N:ℕ),1≤N →
   ∀ (A:Finset (ZMod (Â N))),A.Nonempty →
    ∀ d:ℕ,1≤d →
     log (((Â N:ℕ):ℝ)/(#A:ℝ)) ≤
       (d:ℝ)*log 2 →
      exp (-K*(d:ℝ)^12) *
        ((Â N:ℕ):ℝ)^2 ≤
       (Ὧ A:ℝ)
noncomputable def gp (G:Type*) [Γ G]:aj G where
 í:=∅
 Υ:=λ _↦0
@[simp] lemma tJ (G:Type*) [Γ G] :
  aj.Ι (gp G)=0:=by
 change(∅:Finset (ρ G)).card=0
 simp
@[simp] lemma fZ (G:Type*) [Γ G] [Δ G]
  (Φ:ℝ≥0) :
  ((gp G).ai Φ).Η=(Finset.univ:Finset G):=by
 classical
 ext x
 simp[aj.mem_carrier,gp]
@[simp] lemma o4
  (G:Type*) [Γ G] [Δ G] :
  (gp G).Η=(Finset.univ:Finset G):=by
 simpa using fZ G 1
noncomputable def dA (N:ℕ)
  (A:Finset (ZMod (Â N))) (ξ:A.Nonempty) :
  br.aY (ZMod (Â N)) where
 ba:=gp (ZMod (Â N))
 Ψ:=1
 Ï:=1
 é:=by
  refine ⟨by norm_num,by norm_num, ?_⟩
  simp only[fZ]
  omega
 set:=A
 nonempty:=ξ
 mw:=by
  intro x hx
  rw[fZ]
  simp
@[simp] lemma n1 (N:ℕ)
  (A:Finset (ZMod (Â N))) (ξ:A.Nonempty) :
  (dA N A ξ).Ξ =
   (#A:ℝ)/(Â N:ℕ):=by
 simp[br.aY.Ξ,
  br.aY.e9,dA]
@[simp] lemma px (N:ℕ)
  (A:Finset (ZMod (Â N))) (ξ:A.Nonempty) :
  (dA N A ξ).Ι=0:=by
 simp[br.aY.Ι,dA]
@[simp] lemma py (N:ℕ)
  (A:Finset (ZMod (Â N))) (ξ:A.Nonempty) :
  (dA N A ξ).card=Â N:=by
 simp[br.aY.card,
  br.aY.e9,dA]
noncomputable def Ἰ (N:ℕ)
  (A:Finset (ZMod (Â N))) (ξ:A.Nonempty) :
  ah.aA A where
 Θ:=dA N A ξ
 Î:=0
 eR:=by
  intro x hx
  simpa[dA] using hx
@[simp] lemma p8 (N:ℕ)
  (A:Finset (ZMod (Â N))) (ξ:A.Nonempty) :
  (Ἰ N A ξ).Ξ =
   (#A:ℝ)/(Â N:ℕ):=
       n1 N A ξ
@[simp] lemma rP (N:ℕ)
  (A:Finset (ZMod (Â N))) (ξ:A.Nonempty) :
  (Ἰ N A ξ).Ι=0:=
       px N A ξ
@[simp] lemma rQ (N:ℕ)
  (A:Finset (ZMod (Â N))) (ξ:A.Nonempty) :
  (Ἰ N A ξ).card=Â N:=
       py N A ξ
lemma mf
  {G:Type*} [Γ G] [Δ G] [Β G]
  {Λ:Finset G} {d:ℕ}
  (s:ah.aA Λ)
  (Ý:br.nK d s.Ξ) :
  1<(1025/1024:ℝ)^(1024*(d+1))*s.Ξ:=by
 have dc:(2:ℝ)≤(1025/1024:ℝ)^1024:=by
  have h:=UM (a:=(1/1024:ℝ)) (by norm_num) 1024
  norm_num at h
  exact h
 have hpow:(2:ℝ)^(d+1) ≤
   (1025/1024:ℝ)^(1024*(d+1)):=by
  calc
   _ ≤((1025/1024:ℝ)^1024)^(d+1):=
    ἤ (by positivity) dc (d+1)
   _=(1025/1024:ℝ)^(1024*(d+1)):=by rw[←Ἂ]
 change 1/(2:ℝ)^d≤ s.Ξ at Ý
 have hmul:=ὤ hpow Ý (by positivity) (by positivity)
 have Ὢ:(2:ℝ)^(d+1)*(1/(2:ℝ)^d)=2:=by
  rw[ᾬ]
  field_simp
 rw[Ὢ] at hmul
 exact SI (by norm_num:(1:ℝ)<2) hmul
structure dm (N:ℕ)
  (A:Finset (ZMod (Â N))) (K:ℝ) (d:ℕ) where
 A':Finset (ZMod (Â N))
 À:Finset (ZMod (Â N))
 B:Finset (ZMod (Â N))
 B':Finset (ZMod (Â N))
 translate:ZMod (Â N)
 Ν:ℝ
 p:ℕ
 f:ZMod (Â N)→ℝ
 jR:A'.Nonempty
 iZ:À.Nonempty
 kQ:B.Nonempty
 h8:À⊆B'
 fL: ∀ x∈A',x-translate∈A
 fm: ∀ x∈À,x-translate∈A
 i0:0≤Ν
 kR:Ν*(#B:ℝ)≤(#A':ℝ)
 jS:Ν*(#B':ℝ)≤(#À:ℝ)
 Ἐ:0<p
 gg :
  (2/3:ℝ)^p≤aw.Ἔ À B'
 e7 :
  |(aO.bb A' À -
    (Fintype.card (ZMod (Â N)):ℝ)/(#B:ℝ)) -
    aw.θ f (aO.Û À)| ≤
   ((Fintype.card (ZMod (Â N)):ℝ)/(#B:ℝ))/8
 gh :
  aw.ἡ (aO.Û B') p f ≤
   (((Fintype.card (ZMod (Â N)):ℝ)/(#B:ℝ))/8)^p
 rr :
  exp (-K*(d:ℝ)^12) *
    (Fintype.card (ZMod (Â N)):ℝ)^2 ≤
   Ν^3*(#B:ℝ)*(#B':ℝ)/2
structure dr
  {G:Type*} [Γ G] [Δ G] [Β G]
  {Λ:Finset G} (t:ah.aA Λ)
  (K:ℝ) (d:ℕ) where
 ll:aO.eh Λ
 tK:(3/4:ℝ)*t.Ξ≤ll.Ν
 A3:exp (-(K*((d+1:ℕ):ℝ)^11)) *
   (t.card:ℝ)≤(#ll.B:ℝ)
 za:exp (-(K*((d+1:ℕ):ℝ)^11)) *
   (t.card:ℝ)≤(#ll.B':ℝ)
namespace dm
private lemma vD:exp (-1)≤(1/2:ℝ):=by
 have he := Real.exp_one_gt_two.le
 have hm:=ἂ he (ᾰ (-1)).le
 have te:exp 1*exp (-1)=1:=by
  rw[←R7]
  norm_num
 rw[te] at hm
 exact(ἇ (by norm_num:(0:ℝ)<2)).2
  (by simpa[ä] using hm)
lemma p9
  {d:ℕ} (hd:1≤d) {Ν:ℝ}
  (Õ:(3/4:ℝ)*(1/(2:ℝ)^d)≤Ν) :
  exp (-(8:ℝ)*(d:ℝ)^12)≤Ν^3/2:=by
 let m:ℕ:=8*d^12
 have Ὁ:exp (-(8:ℝ)*(d:ℝ)^12) =
   exp (-1)^m:=by
  rw[show-(8:ℝ)*(d:ℝ)^12=(m:ℝ)*(-1) by
   simp[m],Real.exp_nat_mul]
 have ἵ:exp (-1)^m≤(1/2:ℝ)^m:=
  ἤ (ᾰ _).le vD m
 have PJ:d≤d^12:=Nat.le_pow (by norm_num)
 have hm:3*d+3≤ m:=by
  dsimp[m]
  omega
 have we:(1/2:ℝ)^m≤(1/2:ℝ)^(3*d+3):=
  SJ (by norm_num) (by norm_num) hm
 have qI:(1/2:ℝ)^(3*d+3) ≤
   ((3/4:ℝ)*(1/(2:ℝ)^d))^3/2:=by
  rw[ᾫ,Ἂ]
  ring_nf
  rw[show(1/8:ℝ)=(1/2:ℝ)^3 by norm_num, ←Ἂ]
  gcongr
  all_goals norm_num[R8]
 calc
  exp (-(8:ℝ)*(d:ℝ)^12)=exp (-1)^m:=Ὁ
  _≤(1/2:ℝ)^m:=ἵ
  _≤(1/2:ℝ)^(3*d+3):=we
  _≤((3/4:ℝ)*(1/(2:ℝ)^d))^3/2:=qI
  _≤Ν^3/2:=by gcongr
def sK {N:ℕ}
  {A:Finset (ZMod (Â N))} {K:ℝ} {d:ℕ}
  (c:aO.eh A)
  (DA:exp (-K*(d:ℝ)^12) *
    (Fintype.card (ZMod (Â N)):ℝ)^2 ≤
   c.Ν^3*(#c.B:ℝ)*(#c.B':ℝ)/2) :
  dm N A K d where
 A':=c.A'
 À:=c.À
 B:=c.B
 B':=c.B'
 translate:=c.translate
 Ν:=c.Ν
 p:=c.p
 f:=c.f
 jR:=c.jR
 iZ:=c.iZ
 kQ:=c.kQ
 h8:=c.h8
 fL:=c.fL
 fm:=c.fm
 i0:=c.i0
 kR:=c.kR
 jS:=c.jS
 Ἐ:=c.Ἐ
 gg:=c.gg
 e7:=c.e7
 gh:=c.gh
 rr:=DA
lemma nB
  {G:Type*} [Δ G] {zb zc:ℝ} {d:ℕ} {B B':Finset G}
  (É:exp (-zb*(d:ℝ)^12)*(Fintype.card G:ℝ) ≤
   (#B:ℝ))
  (Km:exp (-zc*(d:ℝ)^12)*(Fintype.card G:ℝ) ≤
   (#B':ℝ)) :
  exp (-(zb+zc)*(d:ℝ)^12) *
    (Fintype.card G:ℝ)^2≤(#B:ℝ)*(#B':ℝ):=by
 calc
  _
                          =
    (exp (-zb*(d:ℝ)^12)*(Fintype.card G:ℝ)) *
     (exp (-zc*(d:ℝ)^12)*(Fintype.card G:ℝ)):=by
   rw[show-(zb+zc)*(d:ℝ)^12 =
     -zb*(d:ℝ)^12+ -zc*(d:ℝ)^12 by ring,
    R7]
   ring
  _≤(#B:ℝ)*(#B':ℝ):=
         ὤ É Km (by positivity) (by positivity)
lemma lZ
  {G:Type*} [Δ G] {Ν n2 wP:ℝ} {d:ℕ}
  {B B':Finset G}
  (û:exp (-n2*(d:ℝ)^12)≤Ν^3/2)
  (DB:exp (-wP*(d:ℝ)^12) *
    (Fintype.card G:ℝ)^2≤(#B:ℝ)*(#B':ℝ)) :
  exp (-(n2+wP)*(d:ℝ)^12) *
    (Fintype.card G:ℝ)^2 ≤
   Ν^3*(#B:ℝ)*(#B':ℝ)/2:=by
 have Gm:0≤(#B:ℝ)*(#B':ℝ):=by positivity
 calc
  _
                          =
    exp (-n2*(d:ℝ)^12) *
     (exp (-wP*(d:ℝ)^12) *
      (Fintype.card G:ℝ)^2):=by
   rw[show-(n2+wP)*(d:ℝ)^12 =
     -n2*(d:ℝ)^12+ -wP*(d:ℝ)^12 by ring,
    R7]
   ring
  _≤exp (-n2*(d:ℝ)^12) *
     ((#B:ℝ)*(#B':ℝ)):=
   Å DB (ᾰ _).le
  _≤(Ν^3/2)*((#B:ℝ)*(#B':ℝ)):=
   ἂ û Gm
  _=Ν^3*(#B:ℝ)*(#B':ℝ)/2:=by ring
lemma BZ {N:ℕ} {A:Finset (ZMod (Â N))}
  {K:ℝ} {d:ℕ} (c:dm N A K d) :
  exp (-K*(d:ℝ)^12) *
    ((Â N:ℕ):ℝ)^2≤(Ὧ A:ℝ):=by
 let:NeZero (Â N):=⟨by simp[Â]⟩
 have A4:Odd (Â N):=
        ⟨N,by simp[Â,ΐ]⟩
 simpa using aO.kq A4
  c.jR c.iZ c.kQ c.h8 c.translate
  c.fL c.fm c.i0 c.kR
  c.jS c.Ἐ c.f c.gg c.e7
  c.gh c.rr
end dm
def eT (K:ℝ):Prop:=
 0<K ∧
  ∀ (N:ℕ),1≤N →
   ∀ (A:Finset (ZMod (Â N))),A.Nonempty →
    ∀ d:ℕ,1≤d →
     log (((Â N:ℕ):ℝ)/(#A:ℝ)) ≤
       (d:ℝ)*log 2 →
      Nonempty (dm N A K d)
lemma nC
  {K:ℝ} (h:eT K) :
  f1 K:=by
 refine ⟨h.1, ?_⟩
 intro N î A ξ d hd ei
 exact(Classical.choice (h.2 N î A ξ d hd ei)).BZ
private lemma uu {d:ℕ} (hd:1≤d) :
  ((d+1:ℕ):ℝ)^12≤(2:ℝ)^12*(d:ℝ)^12:=by
 have Pe:(1:ℝ)≤d:=by exact_mod_cast hd
 have dc:((d+1:ℕ):ℝ)≤2*(d:ℝ):=by
  push_cast
  linarith
 calc
  _ ≤(2*(d:ℝ))^12:=
   ἤ (by positivity) dc 12
  _=(2:ℝ)^12*(d:ℝ)^12:=by rw[Ἀ]
namespace dm
lemma iJ
  {G:Type*} [Δ G] {K:ℝ} (æ:0≤K)
  {d n mg:ℕ} (hd:1≤d) (hn:n≤1024*(d+1))
  {B:Finset G}
  (ue:exp (-(n:ℝ) *
     (K*((d+1:ℕ):ℝ)^11))*(Fintype.card G:ℝ) ≤
    (mg:ℝ))
  (A5:exp (-(K*((d+1:ℕ):ℝ)^11)) *
    (mg:ℝ)≤(#B:ℝ)) :
  exp (-(1025*(2:ℝ)^12*K)*(d:ℝ)^12) *
    (Fintype.card G:ℝ)≤(#B:ℝ):=by
 let step := K*((d+1:ℕ):ℝ)^11
 have Kn:n+1≤1025*(d+1):=by omega
 have Ko:(n:ℝ)+1≤1025*((d+1:ℕ):ℝ):=by
  exact_mod_cast Kn
 have yq:0≤ step:=by
  dsimp[step]
  positivity
 have Gn:((n:ℝ)+1)*step ≤
   1025*K*((d+1:ℕ):ℝ)^12:=by
  calc
   _ ≤
     (1025*((d+1:ℕ):ℝ))*step:=
    ἂ Ko yq
   _=1025*K*((d+1:ℕ):ℝ)^12:=by
    simp only[step]
    ring
 have hpow:=uu hd
 have yr:((n:ℝ)+1)*step ≤
   (1025*(2:ℝ)^12*K)*(d:ℝ)^12:=by
  calc
   _ ≤
     1025*K*((d+1:ℕ):ℝ)^12:=Gn
   _≤1025*K*((2:ℝ)^12*(d:ℝ)^12):=
    Å hpow (å (by norm_num) æ)
   _=(1025*(2:ℝ)^12*K)*(d:ℝ)^12:=by ring
 have Fb:exp (-((n:ℝ)+1)*step) *
   (Fintype.card G:ℝ)≤(#B:ℝ):=by
  calc
   _ =
     exp (-step) *
      (exp (-(n:ℝ)*step)*(Fintype.card G:ℝ)):=by
    rw[show-((n:ℝ)+1)*step =
      -step+(-(n:ℝ)*step) by ring,R7]
    ring
   _≤exp (-step)*(mg:ℝ):=
    Å (by simpa[step] using ue)
     (ᾰ _).le
   _≤(#B:ℝ):=by simpa[step] using A5
 have Ὁ:exp (-(1025*(2:ℝ)^12*K)*(d:ℝ)^12) ≤
   exp (-((n:ℝ)+1)*step):=by
  apply Real.exp_le_exp.mpr
  nlinarith
 exact(ἂ Ὁ (by positivity)).trans Fb
noncomputable def tL
  {N d n:ℕ} (hd:1≤d)
  {A:Finset (ZMod (Â N))} (ξ:A.Nonempty)
  {K:ℝ} (æ:0≤K)
  {t:ah.aA A}
  (hn:n≤1024*(d+1))
  (uv:br.nK d
   (Ἰ N A ξ).Ξ)
  (û:(1025/1024:ℝ)^n *
    (Ἰ N A ξ).Ξ≤t.Ξ)
  (ch:exp (-(n:ℝ) *
     (K*((d+1:ℕ):ℝ)^11)) *
    ((Ἰ N A ξ).card:ℝ)≤(t.card:ℝ))
  (terminal:dr t K d) :
  dm N A
   (8+2050*(2:ℝ)^12*K) d:=by
 letI:NeZero (Â N):=⟨by simp[Â]⟩
 let c:=terminal.ll
 have B0:0≤(Ἰ N A ξ).Ξ:=
  (Ἰ N A ξ).ὰ.le
 have uP:(1:ℝ)≤(1025/1024:ℝ)^n:=
  RH (by norm_num)
 have Go:(Ἰ N A ξ).Ξ≤t.Ξ:=by
  calc
   (Ἰ N A ξ).Ξ =
     1*(Ἰ N A ξ).Ξ:=by ring
   _≤(1025/1024:ℝ)^n*(Ἰ N A ξ).Ξ:=
    ἂ uP B0
   _≤t.Ξ:=û
 have Ý:(1/(2:ℝ)^d) ≤
   (Ἰ N A ξ).Ξ:=uv
 have Õ:(3/4:ℝ)*(1/(2:ℝ)^d)≤c.Ν:=by
  calc
   (3/4:ℝ)*(1/(2:ℝ)^d) ≤
     (3/4:ℝ)*(Ἰ N A ξ).Ξ:=
    Å Ý (by norm_num)
   _≤(3/4:ℝ)*t.Ξ:=
    Å Go (by norm_num)
   _≤c.Ν:=terminal.tK
 have A6:exp (-(8:ℝ)*(d:ℝ)^12) ≤
   c.Ν^3/2:=p9 hd Õ
 have ys:exp (-(n:ℝ) *
    (K*((d+1:ℕ):ℝ)^11)) *
   (Fintype.card (ZMod (Â N)):ℝ)≤(t.card:ℝ):=by
  simpa only[rQ,ZMod.card] using ch
 have É:exp (-(1025*(2:ℝ)^12*K)*(d:ℝ)^12) *
   (Fintype.card (ZMod (Â N)):ℝ)≤(#c.B:ℝ):=by
  exact iJ
   (G:=ZMod (Â N)) (K:=K) æ
   (d:=d) (n:=n) (mg:=t.card) hd hn ys terminal.A3
 have Km:exp (-(1025*(2:ℝ)^12*K)*(d:ℝ)^12) *
   (Fintype.card (ZMod (Â N)):ℝ)≤(#c.B':ℝ):=by
  exact iJ
   (G:=ZMod (Â N)) (K:=K) æ
   (d:=d) (n:=n) (mg:=t.card) hd hn ys terminal.za
 have DB:=nB É Km
 have DA:=lZ A6 DB
 exact sK c (by
  convert DA using 1; ring_nf)
end dm
private lemma n3 {N:ℕ} (î:1≤N) :
  (((Â N:ℕ):ℝ))≤4*(N:ℝ):=by
 push_cast
 have Qb:(1:ℝ)≤N:=by exact_mod_cast î
 linarith
private lemma ow
  {N d:ℕ} {A:Finset ℕ} (î:1≤N) (ξ:A.Nonempty)
  (ei:log ((N:ℝ)/(#A:ℝ))≤(d:ℝ)*log 2) :
  log (((Â N:ℕ):ℝ)/(#A:ℝ)) ≤
   ((d+2:ℕ):ℝ)*log 2:=by
 have Kp:(0:ℝ)<N:=by exact_mod_cast î
 have Fc:(0:ℝ)< #A:=by exact_mod_cast ξ.card_pos
 have Il := ὗ Kp Fc
 have wh :
   (((Â N:ℕ):ℝ)/(#A:ℝ)) ≤
    4*((N:ℝ)/(#A:ℝ)):=by
  calc
   _ ≤
     (4*(N:ℝ))/(#A:ℝ):=
    ῖ (n3 î) Fc.le
   _=4*((N:ℝ)/(#A:ℝ)):=by ring
 calc
  _ ≤
    log (4*((N:ℝ)/(#A:ℝ))):=
   ᾆ (by positivity) wh
  _=2*log 2+log ((N:ℝ)/(#A:ℝ)):=by
   rw[ñ (by norm_num:(4:ℝ)≠0) Il.ne',
    show(4:ℝ)=2*2 by norm_num,
    ñ (by norm_num:(2:ℝ)≠0) (by norm_num:(2:ℝ)≠0)]
   ring
  _≤2*log 2+(d:ℝ)*log 2:=by linarith
  _=((d+2:ℕ):ℝ)*log 2:=by
   push_cast
   ring
private lemma ux {d:ℕ} (hd:1≤d) :
  ((d+2:ℕ):ℝ)^12≤(3:ℝ)^12*(d:ℝ)^12:=by
 have Pe:(1:ℝ)≤d:=by exact_mod_cast hd
 have dc:((d+2:ℕ):ℝ)≤3*(d:ℝ):=by
  push_cast
  linarith
 calc
  _ ≤(3*(d:ℝ))^12:=
   ἤ (by positivity) dc 12
  _=(3:ℝ)^12*(d:ℝ)^12:=by rw[Ἀ]
lemma tM
  {K:ℝ} (zd:f1 K) :
  dX ((3:ℝ)^12*K) 1:=by
 refine ⟨Ἃ (ᾅ (by norm_num) _) zd.1, ?_⟩
 intro N î A z8 ξ d hd ei
 have Kq: ∀ a∈A,a≤N:=by
  intro a ha
  exact(Finset.mem_Icc.mp (z8 ha)).2
 have ze:(ὂ N A).Nonempty:=by
  obtain ⟨a,ha⟩:=ξ
  exact ⟨ὁ N a,fi.mpr ⟨a,ha,rfl⟩⟩
 have DC := vR Kq
 have Fd :
   log (((Â N:ℕ):ℝ) /
     (#(ὂ N A):ℝ)) ≤
    ((d+2:ℕ):ℝ)*log 2:=by
  rw[DC]
  exact ow î ξ ei
 have Kr:=zd.2 N î (ὂ N A) ze
  (d+2) (by omega) Fd
 have hpow:=ux hd
 have Ὁ :
   exp (-((3:ℝ)^12*K)*(d:ℝ)^12) ≤
    exp (-K*((d+2:ℕ):ℝ)^12):=by
  apply Real.exp_le_exp.mpr
  have æ:=zd.1.le
  nlinarith[Å hpow æ]
 have Ks:(N:ℝ)^2≤(((Â N:ℕ):ℝ))^2:=by
  apply ἤ (by positivity) _ 2
  push_cast
  have MS:(0:ℝ)≤N:=by positivity
  linarith
 calc
  _ ≤
    exp (-K*((d+2:ℕ):ℝ)^12) *
     (((Â N:ℕ):ℝ))^2:=
   ὤ Ὁ Ks (sq_nonneg _) (ᾰ _).le
  _≤(Ὧ (ὂ N A):ℝ):=Kr
  _=(Ὧ A:ℝ):=by rw[q1 Kq]
lemma mh
  (h: ∃ K:ℝ,f1 K) :
  ∃ K:ℝ, ∃ Ὠ:ℕ,dX K Ὠ:=by
 obtain ⟨K,æ⟩:=h
 exact ⟨(3:ℝ)^12*K,1,tM æ⟩
lemma i2
  (h: ∃ K:ℝ,eT K) :
  ∃ K:ℝ, ∃ Ὠ:ℕ,dX K Ὠ:=by
 obtain ⟨K,æ⟩:=h
 exact mh
  ⟨K,nC æ⟩
end ay
end
section
open Finset Fintype Function
open scoped BigOperators NNReal
namespace ay.bu
noncomputable section
variable {G:Type*} [Δ G] [Β G] [Γ G]
 [MeasurableSpace G] [Α G]
def et (K:aj G) (A:Finset G):G→ℝ:=
 (Fintype.card G:ℝ) •
  ao ((@mu (ℝ) _ _) A-mu K.Η) (mu A-mu K.Η)
lemma l0
  {K W:aj G} (L3:K.a1)
  (u9:W.a1)
  {A:Finset G} (ξ:A.Nonempty) (ἒ:A⊆K.Η)
  {Ο:ℝ≥0} (ò:0<Ο)
  (ῴ:4*Ο ≤
   1/(400*(max W.Ι 1:ℕ):ℝ≥0))
  {D E:Finset G} (Ð:D.Nonempty) (Þ:E.Nonempty)
  (gn:D⊆(W.ai Ο).Η)
  (lk:E⊆(W.ai Ο).Η)
  {Ρ:ℝ≥0}
  (dy:Ρ≤1/(100*(max K.Ι 1:ℕ):ℝ≥0))
  (ῶ: ∀ t,aN.bh D E t≠0 →
   t∈(K.ai Ρ).Η)
  {Μ:ℝ} (Ἷ:0<Μ) (oV:Μ≤1)
  (ú :
   2*((A.card:ℝ)⁻¹ *
     (200*((max K.Ι 1:ℕ):ℝ)*(Ρ:ℝ))) +
    (K.Η.card:ℝ)⁻¹ *
     (200*((max K.Ι 1:ℕ):ℝ)*(Ρ:ℝ)) ≤
    Μ/8*(K.Η.card:ℝ)⁻¹)
  {p:ℕ} (hp:0<p)
  (qv :
   an.aM
     ((↑) ∘ aN.bh D E)
     ((al ((@mu (ℝ) _ _) A) (mu A))) (an.cz Μ p) <
    (1+Μ/8)*(K.Η.card:ℝ)⁻¹) :
  an.aM (af W.Η)
    (ao
     ((@mu (ℝ) _ _) A-mu K.Η) (mu A-mu K.Η)) p ≤
   Μ*(K.Η.card:ℝ)⁻¹:=by
 let a:G→ℝ:=(@mu (ℝ) _ _) A-mu K.Η
 have hq:0<an.bS p:=
  Ὑ (by norm_num) hp
 have lh:=
  fu.tG u9 ò ῴ
   Ð Þ gn lk hq
   (an.sX p) a
 rw[fu.es]
  at lh
 apply fu.nr
   L3 ξ ἒ Ð Þ dy ῶ Ἷ oV ú hp
   ⟨ὡ W.Η,
    ᾁ W.aE⟩
 ·simpa[a] using lh
 ·exact qv
structure aG (Λ:Finset G) where
 aV:ah.aA Λ
 ᾒ:aV.Θ.Ψ=1
 iK:aV.Θ.ba.a1
namespace aG
def Ξ {Λ:Finset G} (s:aG Λ) :
  ℝ:=s.aV.Ξ
def Ι {Λ:Finset G} (s:aG Λ) :
  ℕ:=s.aV.Ι
def card {Λ:Finset G} (s:aG Λ) :
  ℕ:=s.aV.card
omit [Α G] [MeasurableSpace G] in
lemma ὰ {Λ:Finset G} (s:aG Λ) :
  0<s.Ξ:=s.aV.ὰ
omit [Α G] [MeasurableSpace G] in
lemma density_nonneg {Λ:Finset G} (s:aG Λ) :
  0≤ s.Ξ:=s.ὰ.le
end aG
structure dB
  {Λ:Finset G} (s:aG Λ)
  (Μ Á:ℝ) (aq:ℕ) where
 Ρ:ℝ≥0
 xb :
  Ρ ≤
   1/(100*(max s.aV.Θ.ba.Ι 1:ℕ):ℝ≥0)
 ak:ah.bt (G:=G)
 aB:ah.bt (G:=G)
 fT:ak.Ψ=1
 g3:aB.Ψ=1
 ez:ak.ba.a1
 fe:aB.ba.a1
 nY:ak.Η ⊆
  (s.aV.Θ.ba.ai Ρ).Η
 p4:aB.Η ⊆
  (s.aV.Θ.ba.ai Ρ).Η
 tg :
  400*((max s.aV.Θ.ba.Ι 1:ℕ):ℝ)*(Ρ:ℝ) ≤
   Μ *
    ὒ s.aV.Θ.set
     s.aV.Θ.ba.Η/4
 Ì:ak.ba.Ι≤ s.Ι+aq
 p5:aB.ba.Ι≤ s.Ι+aq
 mE:exp (-Á)*(s.card:ℝ)≤ak.Η.card
 mF:exp (-Á)*(s.card:ℝ)≤aB.Η.card
omit [Α G] [MeasurableSpace G] in
lemma m5
  {Λ:Finset G} (s:aG Λ)
  {Μ Á:ℝ} {aq:ℕ}
  (Ἷ:0<Μ)
  (P:dB s Μ Á aq) :
  ah.þ s.aV P.ak P.aB Μ ∨
   ∃ t:aG Λ,
    br.dk (1+Μ/2) aq Á
     s.aV.Θ t.aV.Θ:=by
 have ξ:=s.aV.Θ.nonempty
 have ἒ :
   s.aV.Θ.set⊆s.aV.Θ.ba.Η:=by
  simpa[br.aY.e9,s.ᾒ] using
   s.aV.Θ.mw
 have o5 :
   ὒ s.aV.Θ.set
     s.aV.Θ.ba.Η=s.aV.Ξ:=by
  unfold ah.aA.Ξ br.aY.Ξ
   ὒ br.aY.e9
  simp[s.ᾒ]
 rcases kk
   s.iK P.xb ξ ἒ
   P.ak.aE P.aB.aE
   P.nY P.p4 Ἷ P.tg with
  ο | Im | In
 ·left
  rw[o5] at ο
  simpa[ah.þ,ah.aA.e9,
   ah.aA.Ξ,
   br.aY.Ξ,
   br.aY.e9,s.ᾒ] using ο
 ·right
  obtain ⟨x,hx⟩:=Im
  rw[o5] at hx
  have gy:0<Ó s.aV.Θ.set
    P.ak.Η x:=by
   have hs := s.aV.ὰ
   have hq:0<(1+Μ/2:ℝ):=by nlinarith
   exact(Ἃ hq hs).trans_le (by simpa using hx)
  let u:=ah.di s.aV P.ak x gy
  refine ⟨{ aV:=u,ᾒ:= ?_,iK:= ?_ }, ?_⟩
  ·simpa[u,ah.di,ah.bt.eo]
    using P.fT
  ·simpa[u,ah.di,ah.bt.eo]
    using P.ez
  ·apply ah.fb
    s.aV P.ak x gy
   ·simpa[ah.aA.Ξ,
     br.aY.Ξ,
     br.aY.e9] using hx
   ·exact P.Ì
   ·exact P.mE
 ·right
  obtain ⟨x,hx⟩:=In
  rw[o5] at hx
  have gy:0<Ó s.aV.Θ.set
    P.aB.Η x:=by
   have hs := s.aV.ὰ
   have hq:0<(1+Μ/2:ℝ):=by nlinarith
   exact(Ἃ hq hs).trans_le (by simpa using hx)
  let u:=ah.di s.aV P.aB x gy
  refine ⟨{ aV:=u,ᾒ:= ?_,iK:= ?_ }, ?_⟩
  ·simpa[u,ah.di,ah.bt.eo]
    using P.g3
  ·simpa[u,ah.di,ah.bt.eo]
    using P.fe
  ·apply ah.fb
    s.aV P.aB x gy
   ·simpa[ah.aA.Ξ,
     br.aY.Ξ,
     br.aY.e9] using hx
   ·exact P.p5
   ·exact P.mF
def ö
  {Λ:Finset G} {s:ah.aA Λ}
  {ak aB:ah.bt (G:=G)} {Μ:ℝ}
  (h:ah.þ s ak aB Μ):Finset G:=
 ah.dn s.Θ.set ak.Η
  (aO.cr h)
def d3
  {Λ:Finset G} {s:ah.aA Λ}
  {ak aB:ah.bt (G:=G)} {Μ:ℝ}
  (h:ah.þ s ak aB Μ):Finset G:=
 ah.dn s.Θ.set aB.Η
  (aO.cr h)
noncomputable def mi
    {Λ:Finset G} (s:ah.aA Λ)
    {ak aB:ah.bt (G:=G)} {Μ:ℝ}
    (ο:ah.þ s ak aB Μ)
    (_hepsilon_nonneg:0≤Μ) (ὃ:Μ<1)
    {p:ℕ} (hp:0<p) (f:G→ℝ)
    (jz:(2/3:ℝ)^p≤aO.ì s Μ)
    (ew :
      |(aO.bb
            (ö ο) (d3 ο) -
          (Fintype.card G:ℝ)/(#ak.Η:ℝ)) -
          aw.θ f
            (aO.Û (d3 ο))| ≤
        ((Fintype.card G:ℝ)/(#ak.Η:ℝ))/8)
    (ee :
      an.aM
          (af (aO.Û aB.Η)) f p ≤
        ((Fintype.card G:ℝ)/(#ak.Η:ℝ))/8) :
    aO.eh Λ:=by
  let x := aO.cr ο
  let A' := ö ο
  let À := d3 ο
  let B := ak.Η
  let B' := aB.Η
  let Ν := aO.ì s Μ
  have Έ:Ν≤Ó s.Θ.set B x:=by
    simpa[Ν,x,B,aO.ì] using
      aO.c0 ο
  have o0:Ν≤Ó s.Θ.set B' x:=by
    simpa[Ν,x,B',aO.ì] using
      aO.ea ο
  have Õ :=
    Ἃ (sub_pos.mpr ὃ) s.ὰ
  have ᾈ:A'.Nonempty:=by
    apply ah.bK ak.aE
    exact Õ.trans_le Έ
  have Ἑ:À.Nonempty:=by
    apply ah.bK aB.aE
    exact Õ.trans_le o0
  have kc :=
          ah.dz
      (B:=aB.ba) (Φ:=aB.Ψ)
      (A:=s.Θ.set) (C:=aB.Η)
      (x:=x) (λ _ hz↦hz)
  have Ὸ: ∀ z∈A',z-(s.Î-x)∈Λ:=by
    intro z hz
    have i1:x+z∈s.Θ.set:=
      (ah.e4.mp hz).2
    have hs:=s.eR (x+z) i1
    have heq:z-(s.Î-x)=(x+z)-s.Î:=by abel
    rwa[heq]
  have Ὼ: ∀ z∈À,z-(s.Î-x)∈Λ:=by
    intro z hz
    have i1:x+z∈s.Θ.set:=
      (ah.e4.mp hz).2
    have hs:=s.eR (x+z) i1
    have heq:z-(s.Î-x)=(x+z)-s.Î:=by abel
    rwa[heq]
  have nx:Ν*(#B:ℝ)≤(#A':ℝ):=by
    have wN:(0:ℝ)< #B:=by exact_mod_cast ak.aE.card_pos
    rw[ah.bk
      ak.aE x] at Έ
    exact(ἇ wN).mp Έ
  have ny:Ν*(#B':ℝ)≤(#À:ℝ):=by
    have wg:(0:ℝ)< #B':=by exact_mod_cast aB.aE.card_pos
    rw[ah.bk
      aB.aE x] at o0
    exact(ἇ wg).mp o0
  have qM :
      (2/3:ℝ)^p≤aw.Ἔ À B':=by
    calc
      _ ≤Ν:=jz
      _≤Ó s.Θ.set B' x:= o0
      _=aw.Ἔ À B':=by
        rw[ah.bk
          aB.aE x]
        rfl
  have o1 :=
    aO.eJ aB.aE
  have uq :
      aw.ἡ (aO.Û B') p f ≤
        (((Fintype.card G:ℝ)/(#B:ℝ))/8)^p:=by
    apply aO.fc o1 hp f (by positivity)
    simpa[B,B'] using ee
  exact
    { A':=A'
      À:=À
      B:=B
      B':=B'
      translate:=s.Î-x
      Ν:=Ν
      p:=p
      f:=f
      jR:=ᾈ
      iZ:=Ἑ
      kQ:=ak.aE
      h8:=kc
      fL:=Ὸ
      fm:=Ὼ
      i0:=Õ.le
      kR:=nx
      jS:=ny
      Ἐ:=hp
      gg:=qM
      e7:=by simpa[A',À,B] using ew
      gh:=uq }
structure eS
  {Λ:Finset G} (s:aG Λ)
  {Μ Á:ℝ} {aq p:ℕ}
  (P:dB s Μ Á aq)
  (ο:ah.þ s.aV P.ak P.aB Μ) where
 base:aj G
 weight:aj G
 wj:base.a1
 uy:weight.a1
 wk:base.Η=P.ak.Η
 uA :
  weight.Η=aO.Û P.aB.Η
 rt:(ö ο).Nonempty
 th:ö ο⊆base.Η
 Ο:ℝ≥0
 uB:0<Ο
 mI:4*Ο ≤
  1/(400*(max weight.Ι 1:ℕ):ℝ≥0)
 D:Finset G
 E:Finset G
 yt:D.Nonempty
 yu:E.Nonempty
 rZ:D⊆(weight.ai Ο).Η
 r0:E⊆(weight.ai Ο).Η
 Ρ:ℝ≥0
 yv:Ρ≤1/(100*(max base.Ι 1:ℕ):ℝ≥0)
 ru :
  ∀ t,aN.bh D E t≠0 →
   t∈(base.ai Ρ).Η
 uC :
  2*(((ö ο).card:ℝ)⁻¹ *
    (200*((max base.Ι 1:ℕ):ℝ)*(Ρ:ℝ))) +
   (base.Η.card:ℝ)⁻¹ *
    (200*((max base.Ι 1:ℕ):ℝ)*(Ρ:ℝ)) ≤
   (1/8:ℝ)/8*(base.Η.card:ℝ)⁻¹
 vr :
  (2/3:ℝ)^p≤aO.ì s.aV Μ
 e7 :
  |(aO.bb
     (ö ο) (d3 ο) -
    (Fintype.card G:ℝ)/(#P.ak.Η:ℝ)) -
    aw.θ
     (et base (ö ο))
     (aO.Û (d3 ο))| ≤
   ((Fintype.card G:ℝ)/(#P.ak.Η:ℝ))/8
 qN :
  (1+(1/8:ℝ)/8)*(base.Η.card:ℝ)⁻¹ ≤
    an.aM
     ((↑) ∘ aN.bh D E)
     ((al ((@mu (ℝ) _ _) (ö ο)) (mu (ö ο))))
     (an.cz (1/8:ℝ) p) →
   ∃ t:aG Λ,
    (257/256:ℝ) *
      aO.ì s.aV Μ≤t.Ξ ∧
    t.Ι≤ s.Ι+aq ∧
    exp (-Á)*(s.card:ℝ)≤(t.card:ℝ)
noncomputable def ox
    {Λ:Finset G} (s:aG Λ)
    {K:ℝ} {d aq p:ℕ}
    (P:dB s (1/512:ℝ)
      (K*((d+1:ℕ):ℝ)^11) aq)
    (ο:ah.þ s.aV P.ak P.aB
      (1/512:ℝ))
    (hp:0<p)
    (Q:eS (p:=p) s P ο)
    (ὧ :
      an.aM (af Q.weight.Η)
          (ao
            ((@mu (ℝ) _ _) (ö ο)-mu Q.base.Η)
            (mu (ö ο)-mu Q.base.Η)) p ≤
        (1/8:ℝ)*(Q.base.Η.card:ℝ)⁻¹) :
    dr s.aV K d:=by
  let c:=mi s.aV ο
    (by norm_num) (by norm_num) hp
    (et Q.base (ö ο))
    Q.vr Q.e7 (by
      let w:G→ℝ≥0:=mu Q.weight.Η
      have Ý:=
        aN.gx w
          (ao
            ((@mu (ℝ) _ _) (ö ο)-mu Q.base.Η)
            (mu (ö ο)-mu Q.base.Η))
          (Fintype.card G:ℝ) (by positivity) hp
      have uD :
          an.aM
              (af Q.weight.Η)
              (et Q.base (ö ο)) p =
            (Fintype.card G:ℝ) *
              an.aM
                (af Q.weight.Η)
                (ao
                  ((@mu (ℝ) _ _) (ö ο)-mu Q.base.Η)
                  (mu (ö ο)-mu Q.base.Η)) p:=by
        simpa only[w,NNReal.iF,
          aN.eQ,
          et] using Ý
      have pO :
          an.aM
              (af Q.weight.Η)
              (et Q.base (ö ο)) p ≤
            (Fintype.card G:ℝ) *
              ((1/8:ℝ)*(Q.base.Η.card:ℝ)⁻¹):=by
        rw[uD]
        exact Å ὧ (by positivity)
      rw[Q.uA] at pO
      simpa[Q.wk,ἱ,à,Ῐ,
        ä] using pO)
  refine
    { ll:=c
      tK:= ?_
      A3:= ?_
      za:= ?_ }
  · change(3/4:ℝ)*s.aV.Ξ ≤
      aO.ì s.aV (1/512:ℝ)
    simp only[aO.ì]
    nlinarith[s.aV.ὰ.le]
  · change exp (-(K*((d+1:ℕ):ℝ)^11)) *
        (s.card:ℝ)≤(#P.ak.Η:ℝ)
    exact P.mE
  · change exp (-(K*((d+1:ℕ):ℝ)^11)) *
        (s.card:ℝ)≤(#P.aB.Η:ℝ)
    exact P.mF
lemma l1
  {Λ:Finset G} (s:aG Λ)
  {K:ℝ} {d aq p:ℕ}
  (P:dB s (1/512:ℝ)
   (K*((d+1:ℕ):ℝ)^11) aq)
  (hp:0<p)
  (mj :
   ∀ ο:ah.þ s.aV P.ak P.aB
     (1/512:ℝ),
    Nonempty (eS (p:=p) s P ο)) :
  Nonempty (dr s.aV K d) ∨
   ∃ t:aG Λ,
    br.dk (1025/1024:ℝ) aq
     (K*((d+1:ℕ):ℝ)^11)
     s.aV.Θ t.aV.Θ:=by
 rcases m5 s
   (by norm_num:(0:ℝ)<1/512) P with ᾡ | DD
 ·obtain ⟨Q⟩:=mj ᾡ
  by_cases ᾌ :
    (1+(1/8:ℝ)/8)*(Q.base.Η.card:ℝ)⁻¹ ≤
     an.aM
      ((↑) ∘ aN.bh Q.D Q.E)
      ((al ((@mu (ℝ) _ _) (ö ᾡ)) (mu (ö ᾡ))))
      (an.cz (1/8:ℝ) p)
  ·right
   obtain ⟨u,û,Kt,Ku⟩:=Q.qN ᾌ
   refine ⟨u, ?_,Kt,Ku⟩
   calc
    (1025/1024:ℝ)*s.aV.Ξ ≤
      (257/256:ℝ) *
       aO.ì s.aV (1/512:ℝ):=by
     simp only[aO.ì]
     nlinarith[s.aV.ὰ.le]
    _≤u.Ξ:=û
  ·left
   have L4 :
     an.aM
       ((↑) ∘ aN.bh Q.D Q.E)
       ((al ((@mu (ℝ) _ _) (ö ᾡ)) (mu (ö ᾡ))))
       (an.cz (1/8:ℝ) p) <
      (1+(1/8:ℝ)/8)*(Q.base.Η.card:ℝ)⁻¹:=
    ᾙ ᾌ
   have ὧ:=l0 Q.wj
    Q.uy Q.rt Q.th Q.uB
    Q.mI Q.yt Q.yu Q.rZ Q.r0
    Q.yv Q.ru (by norm_num) (by norm_num)
    Q.uC hp L4
   exact ⟨ox s P ᾡ hp Q ὧ⟩
 ·right
  obtain ⟨u,hu⟩:=DD
  refine ⟨u, ?_⟩
  simpa only[show(1+(1/512:ℝ)/2) =
    (1025/1024:ℝ) by norm_num] using hu
inductive c1 {Λ:Finset G}
  (q:ℝ) (aq:ℕ) (Á:ℝ) :
  ℕ→aG Λ →
   aG Λ→Prop
 | nil (s:aG Λ) :
   c1 q aq Á 0 s s
 | cons {n:ℕ} {s t u:aG Λ}
   (Ἳ:br.dk q aq Á
    s.aV.Θ t.aV.Θ)
   (ῠ:c1 q aq Á n t u) :
   c1 q aq Á (n+1) s u
namespace c1
omit [Α G] [MeasurableSpace G] in
lemma forget {Λ:Finset G} {q Á:ℝ} {aq n:ℕ}
  {s t:aG Λ}
  (h:c1 q aq Á n s t) :
  ah.cU q aq Á n s.aV t.aV:=by
 induction h with
 | nil s=>exact ah.cU.nil s.aV
 | cons Ἳ _ ih=>exact ah.cU.cons Ἳ ih
end c1
lemma pz
  (G:Type*) [Γ G] [Δ G] :
  (gp G).a1:=by
 intro Ρ _hkappa
 simp only[tJ,show max 0 1=1 by omega,
  Nat.cast_one]
 rw[o4]
 simp only[fZ]
 have ch:(0:ℝ)≤Fintype.card G:=by positivity
 constructor<;>nlinarith[show(0:ℝ)≤Ρ by positivity]
noncomputable def eF (N:ℕ)
  (A:Finset (ZMod (Â N))) (ξ:A.Nonempty) :
  aG A where
 aV:=Ἰ N A ξ
 ᾒ:=rfl
 iK:=pz (ZMod (Â N))
@[simp] lemma la (N:ℕ)
  (A:Finset (ZMod (Â N))) (ξ:A.Nonempty) :
  (eF N A ξ).Ξ =
   (#A:ℝ)/(Â N:ℕ):=
       p8 N A ξ
@[simp] lemma wm (N:ℕ)
  (A:Finset (ZMod (Â N))) (ξ:A.Nonempty) :
  (eF N A ξ).Ι=0:=
       rP N A ξ
omit [Α G] [MeasurableSpace G] in
lemma jB
  {Λ:Finset G}
  {Terminal:aG Λ→Prop}
  {q lower Á:ℝ} {aq total used remaining:ℕ}
  (hq:1≤q)
  (oe:used+remaining≤total)
  (yq: ∀ n<total, ∀ s:aG Λ,
   lower≤ s.Ξ →
   s.Ι≤n*aq →
   Terminal s∨ ∃ t:aG Λ,
    br.dk q aq Á
     s.aV.Θ t.aV.Θ)
  (initial:aG Λ)
  (Ý:lower≤ initial.Ξ)
  (Ñ:initial.Ι≤used*aq)
  (rW:1<q^remaining*initial.Ξ) :
  ∃ n≤remaining, ∃ t:aG Λ,
   c1 q aq Á n initial t ∧
   Terminal t:=by
 induction remaining generalizing initial used with
 | zero =>
   have hs:=initial.aV.Ö
   simp only[pow_zero,ἃ] at rW
   exact(ῑ hs rW).elim
 | succ remaining ih =>
   have L5:used<total:=by omega
   rcases yq used L5 initial Ý Ñ with wq | ⟨t,Ἳ⟩
   ·exact ⟨0,by omega,initial,
     c1.nil initial,wq⟩
   ·have L6:initial.Ξ≤t.Ξ:=by
     calc
      initial.Ξ=1*initial.Ξ:=by ring
      _≤q*initial.Ξ:=
       ἂ hq initial.density_nonneg
      _≤t.Ξ:=Ἳ.1
    have uD:lower≤t.Ξ:=Ý.trans L6
    have A7:t.Ι≤(used+1)*aq:=by
     calc
      t.Ι≤ initial.Ι+aq:=Ἳ.2.1
      _≤used*aq+aq:=
       RZ Ñ aq
      _=(used+1)*aq:=by
       rw[Nat.add_mul]
       simp
    have xG:used+1+remaining≤total:=by omega
    have uP:0≤q^remaining:=ἥ (zero_le_one.trans hq) _
    have Gp:1<q^remaining*t.Ξ:=by
     calc
      1<q^(remaining+1)*initial.Ξ:=by simpa using rW
      _=q^remaining*(q*initial.Ξ):=by
       rw[ᾬ]
       ring
      _≤q^remaining*t.Ξ:=
       Å Ἳ.1 uP
    obtain ⟨n,hn,u,ue,hu⟩:=
     ih xG t uD A7 Gp
    exact ⟨n+1,by omega,u,
     c1.cons Ἳ ue,hu⟩
lemma lH
  {N d:ℕ} (_hN:1≤N)
  {A:Finset (ZMod (Â N))} (ξ:A.Nonempty)
  (ei:log (((Â N:ℕ):ℝ)/(#A:ℝ)) ≤
   (d:ℝ)*log 2) :
  br.nK d
   (eF N A ξ).Ξ:=by
 have Ip:0<Â N:=by simp[Â]
 have yY:(0:ℝ)<Â N:=by exact_mod_cast Ip
 have ch:(0:ℝ)< #A:=by exact_mod_cast ξ.card_pos
 have ἕ:(0:ℝ) <
   ((Â N:ℕ):ℝ)/(#A:ℝ):=ὗ yY ch
 have hpow:(0:ℝ)<(2:ℝ)^d:=ᾅ (by norm_num) _
 have L7 :
   log (((Â N:ℕ):ℝ)/(#A:ℝ)) ≤
    log ((2:ℝ)^d):=by
  simpa[ἦ] using ei
 have wh :
   (((Â N:ℕ):ℝ)/(#A:ℝ))≤(2:ℝ)^d:=
  (SW ἕ hpow).mp L7
 have hmul:(((Â N:ℕ):ℝ)) ≤
   (2:ℝ)^d*(#A:ℝ):=(ἲ ch).mp wh
 rw[br.nK]
 simp only[la]
 apply(Sy hpow yY).2
 simpa[ä] using hmul
def jZ (K:ℝ):Prop:=
 ∀ (N:ℕ),
  ∀ (A:Finset (ZMod (Â N))),A.Nonempty →
   ∀ d:ℕ,1≤d →
    ∃ aq p:ℕ,0<p ∧
     ∀ n<1024*(d+1),
      ∀ s:aG A,
       (1/(2:ℝ)^d)≤ s.Ξ →
       s.Ι≤n*aq →
       ∃ P:dB s (1/512:ℝ)
        (K*((d+1:ℕ):ℝ)^11) aq,
        ∀ ο:ah.þ s.aV
          P.ak P.aB (1/512:ℝ),
         Nonempty (eS (p:=p) s P ο)
lemma lb
  {K:ℝ} (æ:0<K) (Iq:jZ K) :
  eT
   (8+2050*(2:ℝ)^12*K):=by
 refine ⟨by positivity, ?_⟩
 intro N î A ξ d hd ei
 obtain ⟨aq,p,hp,yh⟩:=Iq N A ξ d hd
 let fuel:ℕ:=1024*(d+1)
 let initial:=eF N A ξ
 let Terminal:aG A→Prop:=
  λ s=>Nonempty (dr s.aV K d)
 have yq: ∀ n<fuel, ∀ s:aG A,
   (1/(2:ℝ)^d)≤ s.Ξ →
   s.Ι≤n*aq →
   Terminal s∨ ∃ t:aG A,
    br.dk (1025/1024:ℝ) aq
     (K*((d+1:ℕ):ℝ)^11)
     s.aV.Θ t.aV.Θ:=by
  intro n hn s Ý Ñ
  obtain ⟨P,mj⟩:=yh n (by simpa[fuel] using hn) s Ý Ñ
  exact l1 s P hp mj
 have uv:=lH î ξ ei
 have zU :
   (1/(2:ℝ)^d)≤ initial.Ξ:=by
  change(1/(2:ℝ)^d)≤(Ἰ N A ξ).Ξ
  exact uv
 have rW :
   1<(1025/1024:ℝ)^fuel*initial.Ξ:=by
  simpa[fuel,initial] using
   mf
    (Ἰ N A ξ) uv
 obtain ⟨n,hn,t,ue,wq⟩:=
  jB
   (Terminal:=Terminal) (q:=(1025/1024:ℝ))
   (lower:=1/(2:ℝ)^d)
   (Á:=K*((d+1:ℕ):ℝ)^11)
   (aq:=aq) (total:=fuel) (used:=0)
   (remaining:=fuel) (by norm_num) (by omega) yq initial
   zU (by simp[initial]) rW
 let data:=Classical.choice wq
 have Cr:=ue.forget
 have zw:=
  Cr.qZ (by norm_num)
 change(1025/1024:ℝ)^n *
   (Ἰ N A ξ).Ξ≤t.aV.Ξ at zw
 have û  :=
        zw
 have Fe:=Cr.card_bound
 change exp (-(n:ℝ)*(K*((d+1:ℕ):ℝ)^11)) *
   ((Ἰ N A ξ).card:ℝ)≤t.aV.card at Fe
 have ch  :=
        Fe
 exact ⟨dm.tL hd ξ æ.le hn
  uv û ch data⟩
end
end ay.bu
end
section
open Finset Fintype Function
open scoped BigOperators NNReal
namespace ay.pJ
noncomputable section
variable {G:Type*} [Δ G] [Β G] [Γ G]
private lemma rf (K:aj G) (x:G) :
  af K.Η (-x)=af K.Η x:=by
 by_cases hx:x∈K.Η
 ·have Kv := aj.ec.mpr hx
  simp[dj hx,dj Kv]
 ·have Kv: -x∉K.Η:=by
   intro h
   exact hx (aj.ec.mp h)
  simp[dO hx,
   dO Kv]
lemma ie
  {K:aj G} (Ô:K.a1) {κ:ℝ≥0}
  (qx:κ≤1/(100*(max K.Ι 1:ℕ):ℝ≥0))
  {A:Finset G} (ξ:A.Nonempty) (ἒ:A⊆K.Η)
  {t:G} (ht:t∈(K.ai κ).Η) :
  |ao (af A)
    (af K.Η) t-(K.Η.card:ℝ)⁻¹| ≤
   (A.card:ℝ)⁻¹ *
    (200*((max K.Ι 1:ℕ):ℝ)*(κ:ℝ)):=by
 let E:ℝ:=200*((max K.Ι 1:ℕ):ℝ)*(κ:ℝ)
 have sF:(A.card:ℝ)≠0:=by exact_mod_cast ξ.card_ne_zero
 have L8 :=
  ᾁ ξ
 have dc :
   ∑ x:G,af A x*(K.Η.card:ℝ)⁻¹ =
    (K.Η.card:ℝ)⁻¹:=by
  rw[←Ἕ,L8,ἃ]
 have Gq :
   ∑ x:G,
     |af K.Η (t-x) -
      af K.Η (-x)| ≤E:=by
  have ê :=
   aj.ec.mpr ht
  have kE:=
   aj.cN
    Ô qx ê
  calc
   _
                         =
     ∑ x:G,
      |af K.Η (x- -t) -
       af K.Η x|:=by
    refine ἐ (Equiv.neg G) _ _ ?_
    intro x
    simp only[Equiv.neg_apply]
    congr 2; abel_nf
   _≤E:=kE
 have qy :
   ∑ x:G,af A x *
     |af K.Η (t-x) -
      af K.Η (-x)| ≤
    (A.card:ℝ)⁻¹ *E:=by
  calc
   _
                         =
     (A.card:ℝ)⁻¹ * ∑ x∈A,
      |af K.Η (t-x) -
       af K.Η (-x)|:=by
    change(∑ x:G,(if x∈A then (A.card:ℝ)⁻¹ else 0) *
      |af K.Η (t-x) -
       af K.Η (-x)|)=_
    simp only[ite_mul,zero_mul]
    rw[←ᾛ]
    have Ἠ:(Finset.univ:Finset G).filter (λ x↦x∈A)=A:=by
     ext x
     simp
    rw[Ἠ,á]
   _≤(A.card:ℝ)⁻¹ * ∑ x:G,
      |af K.Η (t-x) -
       af K.Η (-x)|:=by
    apply Å
    ·exact Ry (S7 A)
      (λ _ _ _↦ᾝ _)
    ·positivity
   _≤(A.card:ℝ)⁻¹ *E:=
    Å Gq (by positivity)
 rw[ao, ←dc, ←QJ]
 simp_rw[←UY]
 calc
  _
                            =
    |∑ x:G,af A x *
     (af K.Η (t-x) -
      af K.Η (-x))|:=by
   apply è abs
   apply Ò rfl
   intro x _
   by_cases hx:x∈A
   ·rw[rf K x,
     dj (ἒ hx)]
   ·simp[dO hx]
  _≤ ∑ x:G, |af A x *
     (af K.Η (t-x) -
      af K.Η (-x))|:=
   abs_sum_le_sum_abs _ _
  _= ∑ x:G,af A x *
     |af K.Η (t-x) -
      af K.Η (-x)|:=by
   apply Ò rfl
   intro x _
   rw[SU,ἳ (ὡ A x)]
  _≤(A.card:ℝ)⁻¹ *E:=qy
omit [Γ G] [Β G] [Δ G] in
private lemma tN
  {C:Finset G} (Ã:C.Nonempty) (f:G→ℝ) (c:ℝ) :
  aw.Ç C f-c =
   aw.Ç C (λ x↦f x-c):=by
 unfold aw.Ç
 rw[QJ]
 simp only[Tq,ᾚ]
 have Pf:(C.card:ℝ)≠0:=by exact_mod_cast Ã.card_ne_zero
 field_simp
omit [Γ G] [Β G] [Δ G] in
private lemma wt
  {C:Finset G} (Ã:C.Nonempty) (c:ℝ) :
  aw.Ç C (λ _↦c)=c:=by
 unfold aw.Ç
 simp[Ã.card_ne_zero]
lemma dY
  {K:aj G} (Ô:K.a1) {κ:ℝ≥0}
  (qx:κ≤1/(100*(max K.Ι 1:ℕ):ℝ≥0))
  {A C:Finset G} (ξ:A.Nonempty) (ἒ:A⊆K.Η)
  (Ã:C.Nonempty) (Ὅ:C⊆(K.ai κ).Η) :
  |aw.Ç C
    (ao (af A)
     (af K.Η))-(K.Η.card:ℝ)⁻¹| ≤
   (A.card:ℝ)⁻¹ *
    (200*((max K.Ι 1:ℕ):ℝ)*(κ:ℝ)):=by
 let M:ℝ:=(A.card:ℝ)⁻¹ *
  (200*((max K.Ι 1:ℕ):ℝ)*(κ:ℝ))
 rw[tN Ã]
 calc
  _
                                             ≤
   aw.Ç C (λ x ↦
    |ao (af A)
     (af K.Η) x-(K.Η.card:ℝ)⁻¹|):=
   aw.g1 _
  _≤aw.Ç C (λ _↦M):=by
   unfold aw.Ç
   apply ῖ
   ·apply ᾯ
    intro x hx
    exact ie
     Ô qx ξ ἒ (Ὅ hx)
   ·positivity
  _=M:=wt Ã M
omit [Β G] in
private lemma mJ
  (a k:G→ℝ) (x:G) :
  ao (a-k) (a-k) x =
   ao a a x-ao a k x -
    ao k a x+ao k k x:=by
 unfold ao
 simp only[Rw,UY,sub_mul,QJ]
 ring
omit [Γ G] [Β G] [Δ G] in
private lemma xH
  {C:Finset G} (f g:G→ℝ) :
  aw.Ç C (λ x↦f x+g x) =
   aw.Ç C f+aw.Ç C g:=by
 unfold aw.Ç
 rw[T7,add_div]
omit [Γ G] [Β G] [Δ G] in
private lemma sL
  {C:Finset G} (f g:G→ℝ) :
  aw.Ç C (λ x↦f x-g x) =
   aw.Ç C f-aw.Ç C g:=by
 unfold aw.Ç
 rw[QJ,UT]
omit [Γ G] [Β G] [Δ G] in
private lemma kx
  {C:Finset G} (c:ℝ) (f:G→ℝ) :
  aw.Ç C (λ x↦c*f x) =
   c*aw.Ç C f:=by
 unfold aw.Ç
 rw[←á]
 ring
lemma gT
  {K:aj G} (Ô:K.a1) {κ:ℝ≥0}
  (qx:κ≤1/(100*(max K.Ι 1:ℕ):ℝ≥0))
  {A À:Finset G} (ξ:A.Nonempty) (ἒ:A⊆K.Η)
  (Ἑ:À.Nonempty)
  (Ὅ:aO.Û À⊆(K.ai κ).Η)
  (ú :
   2*((A.card:ℝ)⁻¹ *
     (200*((max K.Ι 1:ℕ):ℝ)*(κ:ℝ))) +
    (K.Η.card:ℝ)⁻¹ *
     (200*((max K.Ι 1:ℕ):ℝ)*(κ:ℝ)) ≤
    ((K.Η.card:ℝ)⁻¹)/8) :
  |(aO.bb A À -
    (Fintype.card G:ℝ)/(#K.Η:ℝ)) -
    aw.θ
     ((Fintype.card G:ℝ) •
      ao
       (af A-af K.Η)
       (af A-af K.Η))
     (aO.Û À)| ≤
   ((Fintype.card G:ℝ)/(#K.Η:ℝ))/8:=by
 let C:=aO.Û À
 let yw:=ao (af A) (af A)
 let ὦ:=ao (af A) (af K.Η)
 let rv:=ao (af K.Η) (af A)
 let ᾇ:=ao (af K.Η) (af K.Η)
 let ë:ℝ:=(K.Η.card:ℝ)⁻¹
 let E:ℝ:=200*((max K.Ι 1:ℕ):ℝ)*(κ:ℝ)
 have Ã := aO.eJ Ἑ
 have Kw: |aw.Ç C ὦ-ë| ≤
   (A.card:ℝ)⁻¹ *E:=by
  simpa[C,ὦ,ë,E] using
   dY
    Ô qx ξ ἒ Ã Ὅ
 have Pg: |aw.Ç C rv-ë| ≤
   (A.card:ℝ)⁻¹ *E:=by
  rw[show rv=ὦ by
   dsimp[rv,ὦ]
   exact fG _ _]
  exact Kw
 have Ph: |aw.Ç C ᾇ-ë| ≤ë*E:=by
  simpa[C,ᾇ,ë,E] using
   dY
    Ô qx K.aE (Finset.Subset.rfl) Ã Ὅ
 have hsum :
   |(aw.Ç C ὦ-ë) +
     (aw.Ç C rv-ë) -
     (aw.Ç C ᾇ-ë)| ≤
    2*((A.card:ℝ)⁻¹ *E)+ë*E:=by
  calc
   _
                      ≤
    |aw.Ç C ὦ-ë| +
     |aw.Ç C rv-ë| +
     |aw.Ç C ᾇ-ë|:=by
    calc
     _ ≤ |(aw.Ç C ὦ-ë) +
       (aw.Ç C rv-ë)| +
       |aw.Ç C ᾇ-ë|:=by
      simpa[Su] using(abs_sub_le
       ((aw.Ç C ὦ-ë) +
        (aw.Ç C rv-ë))
       (0:ℝ) (aw.Ç C ᾇ-ë))
     _≤(|aw.Ç C ὦ-ë| +
       |aw.Ç C rv-ë|) +
       |aw.Ç C ᾇ-ë|:=by
      gcongr
      exact UP _ _
   _≤2*((A.card:ℝ)⁻¹ *E)+ë*E:=by
    nlinarith
 have Ἆ:(Fintype.card G:ℝ)/(#K.Η:ℝ) =
   (Fintype.card G:ℝ)*ë:=by
  simp[ë,ἱ]
 have L9:aO.bb A À =
   (Fintype.card G:ℝ)*aw.Ç C yw:=by
  rw[aO.kb Ἑ]
  change aw.Ç C
    (λ x↦(Fintype.card G:ℝ)*yw x)=_
  rw[kx]
 have ᾡ :
   aw.θ
     ((Fintype.card G:ℝ) •
      ao
       (af A-af K.Η)
       (af A-af K.Η)) C =
    (Fintype.card G:ℝ) *
     (aw.Ç C yw-aw.Ç C ὦ -
      aw.Ç C rv+aw.Ç C ᾇ):=by
  rw[aw.mU Ã]
  change aw.Ç C (λ x↦(Fintype.card G:ℝ) *
   ao
    (af A-af K.Η)
    (af A-af K.Η) x)=_
  rw[kx]
  congr 1
  rw[show ao
    (af A-af K.Η)
    (af A-af K.Η) =
    (λ x↦yw x-ὦ x-rv x+ᾇ x) by
   funext x
   simpa[yw,ὦ,rv,ᾇ] using
    mJ (af A)
     (af K.Η) x]
  rw[xH,sL,sL]
 rw[L9,Ἆ,ᾡ]
 have yj:0≤(Fintype.card G:ℝ):=by positivity
 calc
  _
                              =
   (Fintype.card G:ℝ) *
    |(aw.Ç C ὦ-ë) +
     (aw.Ç C rv-ë) -
     (aw.Ç C ᾇ-ë)|:=by
   have heq :
     (Fintype.card G:ℝ)*aw.Ç C yw -
       (Fintype.card G:ℝ)*ë -
       (Fintype.card G:ℝ) *
        (aw.Ç C yw-aw.Ç C ὦ -
         aw.Ç C rv+aw.Ç C ᾇ) =
      (Fintype.card G:ℝ) *
       ((aw.Ç C ὦ-ë) +
        (aw.Ç C rv-ë) -
        (aw.Ç C ᾇ-ë)):=by ring
   rw[heq,SU,ἳ yj]
  _≤(Fintype.card G:ℝ) *
    (2*((A.card:ℝ)⁻¹ *E)+ë*E):=
   Å hsum yj
  _≤(Fintype.card G:ℝ)*(ë/8):=by
   apply Å
   ·simpa[E,ë] using ú
   ·exact yj
  _=((Fintype.card G:ℝ)/(#K.Η:ℝ))/8:=by
   rw[Ἆ]
   ring
lemma e5
  {K:aj G} (Ô:K.a1) {κ:ℝ≥0}
  (qx:κ≤1/(100*(max K.Ι 1:ℕ):ℝ≥0))
  {A À:Finset G} (ξ:A.Nonempty) (ἒ:A⊆K.Η)
  (Ἑ:À.Nonempty)
  (Ὅ:aO.Û À⊆(K.ai κ).Η)
  (ú :
   2*((A.card:ℝ)⁻¹ *
     (200*((max K.Ι 1:ℕ):ℝ)*(κ:ℝ))) +
    (K.Η.card:ℝ)⁻¹ *
     (200*((max K.Ι 1:ℕ):ℝ)*(κ:ℝ)) ≤
    (1/8:ℝ)/8*(K.Η.card:ℝ)⁻¹) :
  |(aO.bb A À -
    (Fintype.card G:ℝ)/(#K.Η:ℝ)) -
    aw.θ
     ((Fintype.card G:ℝ) •
      ao
       ((@mu (ℝ) _ _) A-mu K.Η)
       (mu A-mu K.Η))
     (aO.Û À)| ≤
   ((Fintype.card G:ℝ)/(#K.Η:ℝ))/8:=by
 have Ma:0≤(K.Η.card:ℝ)⁻¹:=by positivity
 have Cs :
   2*((A.card:ℝ)⁻¹ *
     (200*((max K.Ι 1:ℕ):ℝ)*(κ:ℝ))) +
    (K.Η.card:ℝ)⁻¹ *
     (200*((max K.Ι 1:ℕ):ℝ)*(κ:ℝ)) ≤
    ((K.Η.card:ℝ)⁻¹)/8:=by
  apply ú.trans
  nlinarith
 have Nu :=
  aN.eQ A
 have Nv :=
  aN.eQ K.Η
 simpa only[Nu,Nv] using
  gT Ô qx ξ ἒ
   Ἑ Ὅ Cs
end
end ay.pJ
end
section
open Finset
open scoped NNReal
namespace ay.aa
noncomputable section
def ὴ:ℝ:=1/8192
def ç (Ν:ℝ):ℕ:=⌈8192/Ν⌉₊
def Ὕ (Ν:ℝ):ℕ:=Nat.clog 2 (ç Ν)
def g4 (Ν:ℝ):ℕ:=
 ⌈1+log (2/Ν)⌉₊
def fE (Ν:ℝ):ℕ:=
 ay.ᾨ (g4 Ν)
  ((ὴ/Ὕ Ν)/exp 1)
def gs (Ν:ℝ) (k:ℕ):ℝ:=
 (Ν/2)^k/2
def rg (Ν:ℝ) (k:ℕ):ℕ:=
 ⌈8*(1+log (2/gs Ν k))⌉₊
def dt (d:ℕ):ℕ:=4*(d+1)
def Ἅ (d:ℕ):ℕ:=
 an.cz (1/8:ℝ) (dt d)
def av (d:ℕ):ℕ:=
 2+2*d*Ἅ d
def Ù (d:ℕ):ℝ:=
 1/(2:ℝ)^av d
def au (d:ℕ):ℕ:=
 max 1 (rg (Ù d)
  (fE (Ù d)))
def ã (d:ℕ):ℕ:=ç (Ù d)
def ἰ (d:ℕ):ℕ:=
 Ὕ (Ù d)
def ι (d:ℕ):ℕ:=
 fE (Ù d)
def nD (d:ℕ):ℕ:=
 2^38*(av d+13)^3
def o6 (d:ℕ):ℕ:=
 2^42*(av d+13)^4
def Ü:ℕ:=
 2^42*1720335^4
lemma nE:0<ὴ:=by
 norm_num[ὴ]
lemma ml (d:ℕ):0<dt d:=by
 unfold dt
 positivity
lemma fU (d:ℕ):0<Ἅ d:=by
 unfold Ἅ
 exact an.uQ (by norm_num) (ml d)
lemma nF (d:ℕ):Even (Ἅ d):=by
 unfold Ἅ
 exact an.t4 _ _
lemma va (d:ℕ) :
  Ἅ d≤860160*(d+1):=by
 have h:=
  an.po
   (ε:=(1/8:ℝ)) (p:=dt d) (ml d)
 norm_num[Ἅ,dt,ᾩ] at h ⊢
 omega
lemma gU (d:ℕ) :
  av d≤1720322*(d+1)^2:=by
 unfold av
 have h:=va d
 nlinarith[show d≤d+1 by omega]
lemma Ἧ (d:ℕ):0<Ù d:=by
 unfold Ù
 positivity
lemma dZ (d:ℕ):Ù d≤1:=by
 unfold Ù
 have hpow:(1:ℝ)≤(2:ℝ)^av d:=by
  exact RH (by norm_num)
 exact(ἲ (by positivity)).2
  (by simpa only[av,ἃ] using hpow)
lemma i3 (d:ℕ):Ù d≤2:=
 (dZ d).trans (by norm_num)
lemma ἢ (d:ℕ):0<au d:=by
 unfold au
 exact SI (by norm_num) (Tu _ _)
lemma ti (d:ℕ) :
  ã d=8192*2^av d:=by
 unfold ã ç Ù
 have hpow:(0:ℝ)<(2:ℝ)^av d:=by positivity
 rw[show(8192:ℝ)/(1/(2:ℝ)^av d) =
   ((8192*2^av d:ℕ):ℝ) by
    push_cast
    field_simp]
 exact Nat.ceil_natCast _
lemma uE (d:ℕ) :
  ἰ d=13+av d:=by
 unfold ἰ Ὕ
 change Nat.clog 2 (ã d)=13+av d
 rw[ti]
 rw[show(8192:ℕ)=2^13 by norm_num, ←ᾫ,
  Nat.clog_pow 2 (13+av d) (by norm_num)]
lemma tO (d:ℕ) :
  g4 (Ù d)≤av d+2:=by
 unfold g4 Ù
 apply Nat.ceil_le.mpr
 have hpow:(0:ℝ)<(2:ℝ)^av d:=by positivity
 have ῡ :
   2/(1/(2:ℝ)^av d) =
    (2:ℝ)^(av d+1):=by
  field_simp
  rw[ᾬ]
  ring
 rw[ῡ,ἦ]
 have ei:log (2:ℝ)≤1:=by
  convert QX (show(0:ℝ)<2 by norm_num) using 1
  norm_num
 push_cast
 nlinarith[Å ei
  (show(0:ℝ)≤av d+1 by positivity)]
lemma n4 (d:ℕ) :
  ι d≤nD d:=by
 unfold ι fE nD
 unfold ay.ᾨ
 apply Nat.ceil_le.mpr
 have hq:=tO d
 have uX:=uE d
 have Jd:(g4 (Ù d):ℝ) ≤
   av d+2:=by exact_mod_cast hq
 have Kx:(Ὕ (Ù d):ℝ) =
   av d+13:=by
  change(ἰ d:ℝ) =
   av d+13
  exact_mod_cast(by simpa[Nat.add_comm] using uX)
 have Ὁ:exp 1≤3:=Real.exp_one_lt_three.le
 have Þ:(0:ℝ)≤av d:=by positivity
 rw[Kx]
 unfold ὴ
 have si :
   (0:ℝ) <
    (((1/8192:ℝ)/(av d+13)) /
     exp 1/2)^2:=by positivity
 apply(ἲ si).2
 have Gr:(0:ℝ)<av d+13:=by positivity
 have PK:(g4 (Ù d):ℝ) ≤
   av d+13:=by linarith
 have PL:exp 1^2≤(9:ℝ):=by
  nlinarith[ᾰ (1:ℝ)]
 field_simp
 push_cast
 calc
  64*(g4 (Ù d):ℝ)*8192^2 *
    (av d+13)^2*exp 1^2*2^2 ≤
   64*(av d+13)*8192^2 *
    (av d+13)^2*9*2^2:=by
     gcongr
  _=(64*8192^2*9*2^2:ℝ) *
    (av d+13)^3:=by ring
  _≤(2^38:ℝ)*(av d+13)^3:=by
   gcongr
   norm_num
  _=(274877906944:ℝ) *
    (av d+13)^3:=by norm_num
lemma Ὴ {Ν:ℝ} (Õ:0<Ν) :
  0<ç Ν:=by
 unfold ç
 apply Nat.ceil_pos.2
 positivity
lemma m6 {Ν:ℝ} (_halpha:0<Ν) :
  8192/Ν≤(ç Ν:ℝ):=
       Rr _
lemma s8 {Ν ratio:ℝ}
  (Õ:0<Ν) (yx:Ν≤2)
  (ἕ:Ν/2≤ratio) :
  ⌈1+log (min 1 ratio)⁻¹⌉₊≤g4 Ν:=by
 have yy:0<Ν/2:=by positivity
 have Gs:Ν/2≤(1:ℝ):=by linarith
 have Ky := le_min Gs ἕ
 have Ir := yy.trans_le Ky
 have hinv:(min 1 ratio)⁻¹ ≤(Ν/2)⁻¹:=
  (RJ Ir yy).2 Ky
 have ei:log (min 1 ratio)⁻¹ ≤log (2/Ν):=by
  have sy:(Ν/2)⁻¹ =2/Ν:=by
   field_simp
  rw[←sy]
  exact ᾆ (by positivity) hinv
 unfold g4
 apply S3
 linarith
lemma qa {q Q:ℕ} {Μ:ℝ}
  (hq:q≤Q) (Ἷ:0<Μ) :
  ay.ᾨ q Μ ≤
   ay.ᾨ Q Μ:=by
 unfold ay.ᾨ
 apply S3
 have si:0<(Μ/2)^2:=by positivity
 exact ῖ
  (by exact_mod_cast ὄ 64 hq) si.le
lemma ig
  {G:Type*} [Γ G]
  (M L:Finset G) {Ν:ℝ}
  (Õ:0<Ν) (yx:Ν≤2)
  (ἕ:Ν/2≤(L.card:ℝ)/M.card)
  (hm:0<Ὕ Ν) :
  ah.cm M L ὴ
    (Ὕ Ν)≤fE Ν:=by
 classical
 unfold ah.cm fE
 apply qa
 ·unfold ah.mb
  exact s8 Õ yx ἕ
 ·have uX:(0:ℝ)<Ὕ Ν:=by exact_mod_cast hm
  exact ὗ (ὗ nE uX) (ᾰ _)
lemma sN {Ν:ℝ} (Õ:0<Ν)
  (o7:Ν≤1) :
  0<Ὕ Ν:=by
 unfold Ὕ
 have hq:1<ç Ν:=by
  have Ὤ:(1:ℝ)<8192/Ν:=by
   have:Ν<8192:=by
    nlinarith
   exact(SP Õ).2 (by nlinarith)
  have Ῡ := m6 Õ
  exact_mod_cast Ὤ.trans_le Ῡ
 exact Nat.clog_pos (by norm_num) hq
lemma o8 {Ν:ℝ} (_halpha:0<Ν) :
  ç Ν≤2^Ὕ Ν:=by
 unfold Ὕ
 exact Nat.le_pow_clog (by norm_num) _
lemma qP {Ν:ℝ} (Õ:0<Ν) :
  (1/2:ℝ)^Ὕ Ν≤Ν/8192:=by
 have hq:(0:ℝ)<ç Ν:=by
  exact_mod_cast Ὴ Õ
 have hpow:(0:ℝ)<(2:ℝ)^Ὕ Ν:=by positivity
 have uP:(ç Ν:ℝ)≤(2:ℝ)^Ὕ Ν:=by
  exact_mod_cast o8 Õ
 have Ῡ :=
  m6 Õ
 calc
  _ =
    ((2:ℝ)^Ὕ Ν)⁻¹:=by
     rw[ῆ,Te]
  _≤(ç Ν:ℝ)⁻¹:=
   (RJ hpow hq).2 uP
  _≤(8192/Ν)⁻¹:=by
   have dc:(0:ℝ)<8192/Ν:=by positivity
   exact(RJ hq dc).2 Ῡ
  _=Ν/8192:=by
   field_simp
lemma jj {Ν:ℝ}
  (Õ:0<Ν) (o7:Ν≤1) :
  Real.sqrt (2/Ν)≤2/Ν:=by
 have JU:(1:ℝ)≤2/Ν:=by
  apply(ἇ Õ).2
  nlinarith
 have ug:0≤2/Ν:=by positivity
 rw[Real.sqrt_le_iff]
 constructor
 ·exact ug
 ·nlinarith
lemma qQ
  {Ν:ℝ} (Õ:0<Ν) (o7:Ν≤1) :
  (2/(ç Ν:ℝ))*Real.sqrt (2/Ν)≤1/2048:=by
 have hq:(0:ℝ)<ç Ν:=by
  exact_mod_cast Ὴ Õ
 have Ῡ:=m6 Õ
 have DE:=jj Õ o7
 calc
  (2/(ç Ν:ℝ))*Real.sqrt (2/Ν) ≤
    (2/(ç Ν:ℝ))*(2/Ν):=by
   gcongr
  _≤(2/(8192/Ν))*(2/Ν):=by
   have dc:(0:ℝ)<8192/Ν:=by positivity
   have hdiv:2/(ç Ν:ℝ)≤2/(8192/Ν):=by
    exact Rb (by norm_num) dc Ῡ
   exact ἂ hdiv (by positivity)
  _=1/2048:=by
   field_simp
   norm_num
lemma s9
  {Ν:ℝ} (Õ:0<Ν) (o7:Ν≤1) :
  (2*(1/2:ℝ)^Ὕ Ν) *
    Real.sqrt (2/Ν)≤1/2048:=by
 have uX:=qP Õ
 have DE:=jj Õ o7
 calc
  _
                        ≤
   (2*(Ν/8192))*(2/Ν):=by
    gcongr
  _=1/2048:=by
   field_simp
   norm_num
lemma zV {Ν:ℝ} {k:ℕ} (Õ:0<Ν) :
  0<gs Ν k:=by
 unfold gs
 positivity
lemma sO
  {Ν:ℝ} {k:ℕ} (Õ:0<Ν) :
  log (2/gs Ν k) =
   log 4+(k:ℝ)*log (2/Ν):=by
 have ἵ:(0:ℝ)<Ν/2:=by positivity
 have ῡ :
   2/gs Ν k=4/(Ν/2)^k:=by
  unfold gs
  field_simp
  ring
 rw[ῡ,Ui (by norm_num) (ῄ _ ἵ.ne'),
  ἦ,Ui (by norm_num) Õ.ne',
  Ui Õ.ne' (by norm_num)]
 ring
lemma ke (d:ℕ) :
  au d≤o6 d:=by
 unfold au o6
 apply max_le
 ·have gy:0<2^42*(av d+13)^4:=by
   positivity
  omega
 ·unfold rg
  apply Nat.ceil_le.mpr
  rw[sO (Ἧ d)]
  have hk:=n4 d
  have MT:(fE (Ù d):ℝ) ≤
    (2^38*(av d+13)^3:ℕ):=by
   exact_mod_cast hk
  have Ct:log (2:ℝ)≤1:=by
   convert QX (show(0:ℝ)<2 by norm_num) using 1
   norm_num
  have A8:log (4:ℝ)≤2:=by
   rw[show(4:ℝ)=2^2 by norm_num,ἦ]
   have hmul:=Å Ct
    (show(0:ℝ)≤2 by norm_num)
   norm_num at hmul ⊢
   exact hmul
  have Ff :
    log (2/Ù d) ≤
     (av d+1:ℝ):=by
   unfold Ù
   have ῡ :
     2/(1/(2:ℝ)^av d) =
      (2:ℝ)^(av d+1):=by
    field_simp
    rw[ᾬ]
    ring
   rw[ῡ,ἦ]
   push_cast
   nlinarith[Å Ct
    (show(0:ℝ)≤(av d+1:ℕ) by positivity)]
  have Pj :
    (av d+1:ℝ) ≤
     av d+13:=by norm_num
  have F0 :
    (1:ℝ)≤(av d+13)^4:=by
   have Pk:(0:ℝ)≤av d:=by positivity
   have:(1:ℝ)≤av d+13:=by nlinarith
   exact RH this
  have DF :
    0≤log (2/Ù d):=by
   apply Ἲ
   apply(ἇ (Ἧ d)).2
   nlinarith[i3 d]
  have Nw :
    (fE (Ù d):ℝ) ≤
     (2^38:ℝ)*(av d+13)^3:=by
   norm_num at MT ⊢
   exact MT
  have DG  :=
              Ff.trans Pj
  have hmul  :=
         ὤ Nw DG DF (by positivity)
  push_cast at ⊢
  calc
   _
                          ≤
    8*(1+(2 +
     (2^38*(av d+13)^3:ℝ) *
      (av d+13))):=by
       have ῳ :
         log 4 +
           (fE (Ù d):ℝ) *
            log (2/Ù d) ≤
          2+(2^38:ℝ) *
           (av d+13)^3 *
            (av d+13):=by
        linarith
       nlinarith
   _=8*(3 +
     (2^38:ℝ)*(av d+13)^4):=by ring
   _≤(2^42:ℝ)*(av d+13)^4:=by
    norm_num at ⊢
    nlinarith
   _=(4398046511104:ℝ) *
     (av d+13)^4:=by norm_num
lemma jC (d:ℕ) :
  au d ≤
   Ü*(d+1)^8:=by
 have Þ:=gU d
 have MU:1≤(d+1)^2:=by
  exact RH (by omega)
 have Gr :
   av d+13≤1720335*(d+1)^2:=by
  nlinarith
 calc
  au d ≤
    2^42*(av d+13)^4:=
   ke d
  _≤2^42*(1720335*(d+1)^2)^4:=by
   gcongr
  _=Ü*(d+1)^8:=by
   unfold Ü
   ring
lemma ff (d:ℕ) :
  ar.ax d (au d) ≤
   (1024*Ü)*(d+1)^9:=by
 unfold ar.ax
 calc
  _ ≤
    1024*(d+1) *
     (Ü*(d+1)^8):=by
   gcongr
   exact jC d
  _=(1024*Ü)*(d+1)^9:=by
   ring
lemma Ό:log (2:ℝ)≤1:=by
 have h:=
  QX (show(0:ℝ)<2 by norm_num)
 norm_num at h ⊢
 exact h
lemma ῃ {n:ℕ} (hn:0<n) :
  log (n:ℝ)≤n:=by
 have h:=QX
  (show(0:ℝ)<n by exact_mod_cast hn)
 nlinarith
lemma qb (d:ℕ) :
  log (ã d:ℝ) ≤
   (av d+13:ℝ):=by
 rw[ti]
 push_cast
 rw[show(8192:ℝ)=2^13 by norm_num, ←ᾫ,
  ἦ]
 push_cast
 have ug:(0:ℝ)≤13+av d:=by positivity
 nlinarith[Å Ό ug]
lemma o9 (d:ℕ) :
  log (ã d:ℝ) ≤
   1720335*((d+1:ℕ):ℝ)^2:=by
 have Þ:=gU d
 have MU:1≤(d+1)^2:=by
  exact RH (by omega)
 have Gr :
   av d+13≤1720335*(d+1)^2:=by
  nlinarith
 calc
  log (ã d:ℝ) ≤
    (av d+13:ℝ):=
   qb d
  _≤1720335*((d+1:ℕ):ℝ)^2:=by
   exact_mod_cast Gr
lemma pa (d:ℕ) :
  log (au d:ℝ) ≤
   42+4*(av d+13:ℝ):=by
 have yr:=ke d
 have Kz :
   (au d:ℝ) ≤
    ((2^42*(av d+13)^4:ℕ):ℝ):=by
  exact_mod_cast yr
 have wu:(0:ℝ)<au d:=by
  exact_mod_cast ἢ d
 have ei  :=
  ᾆ wu Kz
 have Gt :
   log ((2^42*(av d+13)^4:ℕ):ℝ) =
    42*log 2 +
     4*log ((av d+13:ℕ):ℝ):=by
  push_cast
  rw[show(4398046511104:ℝ)=(2:ℝ)^42 by norm_num]
  rw[ñ (ῄ _ (by norm_num))
   (ῄ _ (by positivity)),
   ἦ,ἦ]
  push_cast
  ring
 have It:0<av d+13:=by positivity
 have Iu  :=
  ῃ It
 rw[Gt] at ei
 have MV:42*log (2:ℝ)≤42:=by
  nlinarith[Å Ό
   (show(0:ℝ)≤42 by norm_num)]
 have Gu:=Å Iu
  (show(0:ℝ)≤4 by norm_num)
 push_cast at ei Gu
 nlinarith
lemma fM (d:ℕ) :
  log (au d:ℝ) ≤
   6881382*((d+1:ℕ):ℝ)^2:=by
 have Þ:=gU d
 have MU:1≤(d+1)^2:=by
  exact RH (by omega)
 have Iv :
   42+4*(av d+13) ≤
    6881382*(d+1)^2:=by
  nlinarith
 calc
  log (au d:ℝ) ≤
    42+4*(av d+13:ℝ):=
   pa d
  _≤6881382*((d+1:ℕ):ℝ)^2:=by
   exact_mod_cast Iv
lemma qc
  {R:ℕ} (Ὥ:0<R) :
  log ((8*R+1:ℕ):ℝ) ≤
   9+log (R:ℝ):=by
 have Mb:1≤R:=Nat.one_le_iff_ne_zero.mpr Ὥ.ne'
 have ᾳ:8*R+1≤9*R:=by omega
 have zf:(0:ℝ)<((8*R+1:ℕ):ℝ):=by
  exact_mod_cast(show 0<8*R+1 by positivity)
 have Ὡ:(0:ℝ)<R:=by exact_mod_cast Ὥ
 have ei :
   log ((8*R+1:ℕ):ℝ) ≤
    log ((9*R:ℕ):ℝ):=
  ᾆ zf (by exact_mod_cast ᾳ)
 have te :
   log ((9*R:ℕ):ℝ) =
    log 9+log (R:ℝ):=by
  push_cast
  rw[ñ (by norm_num) Ὡ.ne']
 rw[te] at ei
 have h9:log (9:ℝ)≤9:=
  ῃ (by norm_num)
 nlinarith
lemma m7 (d:ℕ) :
  log
    ((ã d*(8*au d+1:ℕ):ℕ):ℝ) ≤
   8601726*((d+1:ℕ):ℝ)^2:=by
 have Hm:0<ã d:=by
  unfold ã
  exact Ὴ (Ἧ d)
 have Ὡ:=ἢ d
 have KA:(0:ℝ)<ã d:=by exact_mod_cast Hm
 have Fh:(0:ℝ)<8*au d+1:=by positivity
 have Mc:= o9 d
 have Gv:=qc Ὡ
 have wR:=fM d
 have pb:(1:ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have tj:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 push_cast
 rw[ñ KA.ne' Fh.ne']
 push_cast at Mc wR pb Gv
 nlinarith
lemma eG (d:ℕ) :
  log
    (ar.ax d (au d):ℝ) ≤
   6881393*((d+1:ℕ):ℝ)^2:=by
 have Gw:=ἢ d
 have wu:(0:ℝ)<au d:=by
  exact_mod_cast Gw
 have hdPos:0<d+1:=by omega
 have Fi:(0:ℝ)<d+1:=by exact_mod_cast hdPos
 have Md :=
  ῃ hdPos
 have Gx:=fM d
 have Nx:((d+1:ℕ):ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have tj:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 unfold ar.ax
 push_cast
 rw[ñ
   (ῐ (by norm_num) Fi.ne') wu.ne',
  ñ (by norm_num) Fi.ne']
 have Ny:log (1024:ℝ)≤10:=by
  rw[show(1024:ℝ)=2^10 by norm_num,ἦ]
  push_cast
  nlinarith[Å Ό
   (show(0:ℝ)≤10 by norm_num)]
 push_cast at Md Gx Nx ⊢
 have pb:(1:ℝ)≤(↑d+1)^2:=by
  nlinarith
 nlinarith
lemma qd (d:ℕ) :
  log
    (ar.bn d (au d):ℝ) ≤
   7700594*((d+1:ℕ):ℝ)^2:=by
 have Ὥ:=eG d
 have hconst:log (819200:ℝ)≤819200:=
  ῃ (by norm_num)
 have hpow:(d:ℝ)*log 2≤d:=by
  nlinarith[Å Ό
   (show(0:ℝ)≤d by positivity)]
 have pb:(1:ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have tj:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 have Gy:(d:ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have hd:(d:ℝ)≤d+1:=by norm_num
  push_cast at pb ⊢
  nlinarith
 have Ὡ:0<ar.ax d (au d):=
  ar.iH (ἢ d)
 have wv:(0:ℝ) <
   ar.ax d (au d):=by
  exact_mod_cast Ὡ
 unfold ar.bn
 push_cast
 rw[ñ (ῐ (by norm_num) wv.ne')
   (ῄ _ (by norm_num)),
  ñ (by norm_num) wv.ne',ἦ]
 push_cast at Ὥ hpow Gy ⊢
 nlinarith
lemma qe (d:ℕ) :
  log
    (ar.bd d (au d):ℝ) ≤
   6958194*((d+1:ℕ):ℝ)^2:=by
 have Ὥ:=eG d
 have hconst:log (76800:ℝ)≤76800:=
  ῃ (by norm_num)
 have hpow:((d+1:ℕ):ℝ)*log 2≤d+1:=by
  have hmul:=Å Ό
   (show(0:ℝ)≤((d+1:ℕ):ℝ) by positivity)
  norm_num at hmul ⊢
  exact hmul
 have pb:(1:ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have tj:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 have Gy:((d+1:ℕ):ℝ) ≤
   ((d+1:ℕ):ℝ)^2:=by
  have tj:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 have Ὡ:0<ar.ax d (au d):=
  ar.iH (ἢ d)
 have wv:(0:ℝ) <
   ar.ax d (au d):=by
  exact_mod_cast Ὡ
 unfold ar.bd
 push_cast
 rw[ñ (ῐ (by norm_num) wv.ne')
   (ῄ _ (by norm_num)),
  ñ (by norm_num) wv.ne',ἦ]
 push_cast at Ὥ hpow Gy ⊢
 nlinarith
lemma kU
  (d ax:ℕ) (vb:0<ax) {LR:ℝ}
  (KY:log (ax:ℝ)≤LR) :
  log
    ((8388608*max ax 1 *
     2^av d:ℕ):ℝ) ≤
   23+LR+av d:=by
 have Ἴ :=
  max_eq_left (Nat.one_le_iff_ne_zero.mpr vb.ne')
 rw[Ἴ]
 have zx:(0:ℝ)<ax:=by exact_mod_cast vb
 have MW:log (8388608:ℝ)≤23:=by
  rw[show(8388608:ℝ)=2^23 by norm_num,ἦ]
  push_cast
  nlinarith[Å Ό
   (show(0:ℝ)≤23 by norm_num)]
 have N1 :
   (av d:ℝ)*log 2 ≤
    av d:=by
  nlinarith[Å Ό
   (show(0:ℝ)≤av d by positivity)]
 push_cast
 rw[ñ
   (ῐ (by norm_num) zx.ne')
   (ῄ _ (by norm_num)),
  ñ (by norm_num) zx.ne',ἦ]
 nlinarith
lemma m8 (d:ℕ) :
  (2/(ã d:ℝ)) *
    Real.sqrt (2/Ù d)≤1/2048:=by
 unfold ã
 exact qQ
  (Ἧ d) (dZ d)
lemma pA (d:ℕ) :
  (2*(1/2:ℝ)^ἰ d) *
    Real.sqrt (2/Ù d)≤1/2048:=by
 unfold ἰ
 exact s9
  (Ἧ d) (dZ d)
def ᾀ (Ι delta n:ℕ):ℕ:=
 n^delta*4^(Ι+delta)
def ᾖ (d:ℕ):ℕ:=
 ᾀ
  (ar.ax d (au d))
  (au d)
  (ã d*(8*au d+1))
def eW:ℕ:=
 Ü*8601726 +
  2*(1024*Ü +
   Ü)
def ἣ (Ι m:ℕ):ℕ:=
 (3*m)^Ι*4^Ι
def ὕ (Ι bn bd:ℕ):ℕ:=
 ἣ Ι bn*ἣ Ι bd
def ᾄ (Ι:ℕ):ℕ:=
 ἣ Ι (1600*max Ι 1) *
  ἣ Ι (200*max Ι 1) *
   ἣ Ι (200*max Ι 1)
def cd (d ax:ℕ):ℕ:=
 8388608*max ax 1*2^av d
lemma vE
  {Ι delta n R D N:ℕ}
  (hn:0<n) (Hn:n≤N)
  (Ñ:Ι≤R) (cu:delta≤D) :
  ᾀ Ι delta n≤ᾀ R D N:=by
 unfold ᾀ
 have î := hn.trans_le Hn
 have jx:n^delta≤N^D:=by
  calc
   _ ≤N^delta:=R4 Hn _
   _≤N^D:=QR î cu
 have uh:4^(Ι+delta)≤4^(R+D):=by
  apply QR (by norm_num)
  exact Nat.add_le_add Ñ cu
 exact Ra jx uh
lemma pc (R:ℕ) :
  ⌈8*(R:ℝ)⌉₊+1=8*R+1:=by
 rw[show 8*(R:ℝ)=((8*R:ℕ):ℝ) by
  push_cast
  ring]
 rw[Nat.ceil_natCast]
def ἀ (Ι Ë m:ℕ):ℕ:=
 200*max Ι 1*(2*Ë+1)*m
lemma kg {Ι Ë m:ℕ} (hm:0< m) :
  0<ἀ Ι Ë m:=by
 unfold ἀ
 positivity
lemma uF {Ι Ë m:ℕ} (hm:0< m) :
  log (ἀ Ι Ë m:ℝ) =
   log 200+log ((max Ι 1:ℕ):ℝ) +
    log ((2*Ë+1:ℕ):ℝ)+log (m:ℝ):=by
 have Ὀ:(0:ℝ)< m:=by exact_mod_cast hm
 unfold ἀ
 push_cast
 rw[ñ (by positivity) Ὀ.ne',
  ñ (by positivity) (by positivity),
  ñ (by norm_num) (by positivity)]
lemma m9
  {Ι Ë m:ℕ} {LR LC LM:ℝ} (hm:0< m)
  (PM:log ((max Ι 1:ℕ):ℝ)≤LR)
  (PV:log ((2*Ë+1:ℕ):ℝ)≤LC)
  (ἄ:log (m:ℝ)≤LM) :
  log (ἀ Ι Ë m:ℝ) ≤
   200+LR+LC+LM:=by
 rw[uF hm]
 have DH:log (200:ℝ)≤200:=
  ῃ (by norm_num)
 nlinarith
lemma ky
  {Ι ax:ℕ} (vb:0<ax) (Ñ:Ι≤ax) :
  log ((max Ι 1:ℕ):ℝ)≤log (ax:ℝ):=by
 have Ἴ :=
  max_le Ñ (Nat.one_le_iff_ne_zero.mpr vb.ne')
 have wS:(0:ℝ)< max Ι 1:=by positivity
 exact ᾆ wS (by exact_mod_cast Ἴ)
lemma kh
  {Ë R:ℕ} (Ὥ:0<R) (pd:Ë≤8*R) :
  log ((2*Ë+1:ℕ):ℝ) ≤
   17+log (R:ℝ):=by
 have Mb:1≤R:=Nat.one_le_iff_ne_zero.mpr Ὥ.ne'
 have ᾳ:2*Ë+1≤17*R:=by
  nlinarith
 have zf:(0:ℝ)<((2*Ë+1:ℕ):ℝ):=by
  exact_mod_cast(show 0<2*Ë+1 by positivity)
 have Ὡ:(0:ℝ)<R:=by exact_mod_cast Ὥ
 have ei :
   log ((2*Ë+1:ℕ):ℝ) ≤
    log ((17*R:ℕ):ℝ):=
  ᾆ zf (by exact_mod_cast ᾳ)
 have te :
   log ((17*R:ℕ):ℝ) =
    log 17+log (R:ℝ):=by
  push_cast
  rw[ñ (by norm_num) Ὡ.ne']
 rw[te] at ei
 have Qc:log (17:ℝ)≤17:=
  ῃ (by norm_num)
 nlinarith
lemma iR
  (d Ι Ë:ℕ)
  (Ñ:Ι ≤
   ar.ax d (au d))
  (pd:Ë≤8*au d) :
  log
    (ἀ Ι Ë
     (8388608 *
      max (ar.ax d (au d)) 1 *
       2^av d):ℝ) ≤
   22364730*((d+1:ℕ):ℝ)^2:=by
 let R:=ar.ax d (au d)
 let m:=8388608*max R 1*2^av d
 have Ὡ:0<R:=by
  unfold R
  exact ar.iH (ἢ d)
 have hm:0< m:=by
  unfold m
  positivity
 have wR:log (R:ℝ) ≤
   6881393*((d+1:ℕ):ℝ)^2:=by
  simpa[R] using eG d
 have Gz:log ((max Ι 1:ℕ):ℝ) ≤
   6881393*((d+1:ℕ):ℝ)^2:=
  (ky Ὡ (by simpa[R] using Ñ)).trans wR
 have Iw:log ((2*Ë+1:ℕ):ℝ) ≤
   17+6881382*((d+1:ℕ):ℝ)^2:=by
  calc
   _ ≤
     17+log (au d:ℝ):=
    kh
     (ἢ d) pd
   _≤17+6881382*((d+1:ℕ):ℝ)^2:=by
    gcongr
    exact fM d
 have Me:log (m:ℝ) ≤
   23+8601715*((d+1:ℕ):ℝ)^2:=by
  have ὧ:=kU d R Ὡ wR
  have Þ:=gU d
  have Qd:(av d:ℝ) ≤
    1720322*((d+1:ℕ):ℝ)^2:=by
   exact_mod_cast Þ
  unfold m
  nlinarith
 have Ὦ:=m9
  (Ι:=Ι) (Ë:=Ë) (m:=m) hm Gz Iw Me
 have pb:(1:ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have tj:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 simpa[m,R] using(by nlinarith :
  log (ἀ Ι Ë m:ℝ) ≤
   22364730*((d+1:ℕ):ℝ)^2)
lemma jT
  (d Ι Ë:ℕ)
  (Ñ:Ι ≤
   ar.ax d (au d))
  (pd:Ë≤8*au d) :
  log
    (((3*ἀ Ι Ë
     (cd d
      (ar.ax d (au d))))^Ι:ℕ):ℝ) ≤
   (1024*Ü*22364733:ℕ) *
    ((d+1:ℕ):ℝ)^11:=by
 let R:=ar.ax d (au d)
 let m:=cd d R
 let P:=ἀ Ι Ë m
 have hm:0< m:=by
  unfold m cd
  positivity
 have ὼ:0<P:=by
  unfold P
  exact kg hm
 have PN:log (P:ℝ) ≤
   22364730*((d+1:ℕ):ℝ)^2:=by
  simpa[P,m,R,cd] using
   iR d Ι Ë Ñ pd
 have Pl:log ((3*P:ℕ):ℝ) ≤
   3+22364730*((d+1:ℕ):ℝ)^2:=by
  have Pm:(0:ℝ)<P:=by exact_mod_cast ὼ
  have ώ:log (3:ℝ)≤3:=
   ῃ (by norm_num)
  rw[show((3*P:ℕ):ℝ)=(3:ℝ)*(P:ℝ) by norm_num]
  rw[ñ (by norm_num) Pm.ne']
  nlinarith
 have pb:(1:ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have tj:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 have oc:log ((3*P:ℕ):ℝ) ≤
   22364733*((d+1:ℕ):ℝ)^2:=by
  nlinarith
 have sP:(Ι:ℝ) ≤
   (1024*Ü:ℕ) *
    ((d+1:ℕ):ℝ)^9:=by
  calc
   (Ι:ℝ)≤(R:ℝ):=by exact_mod_cast(by simpa[R] using Ñ)
   _≤(1024*Ü:ℕ) *
     ((d+1:ℕ):ℝ)^9:=by
    simpa[R] using(show
     (ar.ax d (au d):ℝ) ≤
      (1024*Ü:ℕ) *
       ((d+1:ℕ):ℝ)^9 by
     exact_mod_cast ff d)
 have zW:0≤log ((3*P:ℕ):ℝ):=by
  apply Ἲ
  exact_mod_cast(show 1≤3*P by omega)
 have hmul:=ὤ sP oc zW (by positivity)
 push_cast
 rw[ἦ]
 push_cast at hmul ⊢
 nlinarith
lemma i4
  {G:Type*} [Γ G] [Δ G]
  (B:aj G) (T:Finset G) (Ο:ℝ) (m:ℕ)
  (hm:0< m) (Φ:ℝ≥0) (ἧ:1/2≤Φ) :
  ((ἀ B.Ι
    (aI.dg B T Ο) m:ℝ≥0)⁻¹) ≤
   Φ*aI.cJ B T Ο *
    (m:ℝ≥0)⁻¹:=by
 classical
 unfold ἀ aI.cJ
 have Ñ:(0:ℝ≥0)< max B.Ι 1:=by positivity
 have pd:(0:ℝ≥0) <
   (2*aI.dg B T Ο+1:ℕ):=by
  positivity
 have Ὲ:(0:ℝ≥0)< m:=by exact_mod_cast hm
 have hmul :
   (200*(max B.Ι 1:ℝ≥0) *
     (2*aI.dg B T Ο+1:ℕ) *
     (m:ℝ≥0))*(1/2) ≤
    (200*(max B.Ι 1:ℝ≥0) *
     (2*aI.dg B T Ο+1:ℕ) *
     (m:ℝ≥0))*Φ:=by
  exact Å ἧ (by positivity)
 field_simp
 norm_num at hmul ⊢
 convert hmul using 1; ring
lemma f5
  {G:Type*} [Γ G] [Δ G]
  (B:aj G) (P:ℕ) (ὼ:0<P) {Φ:ℝ≥0}
  (ἧ:((P:ℝ≥0)⁻¹)≤Φ) :
  B.Η.card ≤
   (3*P)^B.Ι*(B.ai Φ).Η.card:=by
 classical
 have dc:=
  aj.cM B 1 ὼ
 have ym :
   (B.ai ((P:ℝ≥0)⁻¹)).Η.card ≤
    (B.ai Φ).Η.card:=
  ὣ (aj.b5 ἧ)
 calc
  B.Η.card=(B.ai 1).Η.card:=by simp
  _≤(3*P)^B.Ι *
    (B.ai ((P:ℝ≥0)⁻¹)).Η.card:=by
     simpa[ἱ] using dc
  _≤(3*P)^B.Ι*(B.ai Φ).Η.card:=
   ὄ _ ym
lemma wx
  {Ι delta n:ℕ} (hn:0<n) :
  log (ᾀ Ι delta n:ℝ) =
   (delta:ℝ)*log (n:ℝ) +
    (Ι+delta:ℝ)*log 4:=by
 have Ko:(0:ℝ)<n:=by exact_mod_cast hn
 unfold ᾀ
 push_cast
 rw[ñ (ῄ _ Ko.ne') (ῄ _ (by norm_num)),
  ἦ,ἦ]
 push_cast
 ring
lemma ck {Ι m:ℕ} (hm:0< m) :
  0<ἣ Ι m:=by
 unfold ἣ
 positivity
lemma f0 {Ι m:ℕ} (hm:0< m) :
  log (ἣ Ι m:ℝ) =
   (Ι:ℝ) *
    (log ((3*m:ℕ):ℝ)+log 4):=by
 have Ὀ:(0:ℝ)< m:=by exact_mod_cast hm
 unfold ἣ
 push_cast
 rw[ñ (ῄ _ (ῐ (by norm_num) Ὀ.ne'))
   (ῄ _ (by norm_num)),ἦ,ἦ]
 ring
lemma qf {Ι bn bd:ℕ}
  (ù:0<bn) (fw:0<bd) :
  log (ὕ Ι bn bd:ℝ) =
   (Ι:ℝ) *
    (log ((3*bn:ℕ):ℝ)+log 4) +
   (Ι:ℝ) *
    (log ((3*bd:ℕ):ℝ)+log 4):=by
 unfold ὕ
 push_cast
 rw[ñ
   (by exact_mod_cast(ck ù).ne')
   (by exact_mod_cast(ck fw).ne'),
  f0 ù,f0 fw]
 push_cast
 ring
lemma nG (Ι:ℕ) :
  log (ᾄ Ι:ℝ) =
   (Ι:ℝ) *
     (log ((3*(1600*max Ι 1):ℕ):ℝ) +
      log 4) +
    (Ι:ℝ) *
     (log ((3*(200*max Ι 1):ℕ):ℝ) +
      log 4) +
    (Ι:ℝ) *
     (log ((3*(200*max Ι 1):ℕ):ℝ) +
      log 4):=by
 have Ἴ:0< max Ι 1:=by positivity
 have DI:0<1600*max Ι 1:=by positivity
 have DH:0<200*max Ι 1:=by positivity
 have ῥ :
   ((ἣ Ι (1600*max Ι 1):ℕ):ℝ)≠0:=by
  exact_mod_cast(ck DI).ne'
 have GA :
   ((ἣ Ι (200*max Ι 1):ℕ):ℝ)≠0:=by
  exact_mod_cast(ck DH).ne'
 unfold ᾄ
 push_cast
 rw[ñ
   (ῐ ῥ GA) GA,
  ñ ῥ GA,
  f0 DI,
  f0 DH]
 push_cast
 ring
lemma fI
  {m:ℕ} {L:ℝ} (hm:0< m)
  (ei:log (m:ℝ)≤L) :
  log ((3*m:ℕ):ℝ)≤3+L:=by
 have Ὀ:(0:ℝ)< m:=by exact_mod_cast hm
 have ώ:log (3:ℝ)≤3:=
  ῃ (by norm_num)
 push_cast
 rw[ñ (by norm_num) Ὀ.ne']
 nlinarith
lemma lS:log (4:ℝ)≤2:=by
 rw[show(4:ℝ)=2^2 by norm_num,ἦ]
 have hmul:=Å Ό
  (show(0:ℝ)≤2 by norm_num)
 norm_num at hmul ⊢
 exact hmul
lemma ia
  (d Ι:ℕ)
  (Ñ:Ι ≤
   ar.ax d (au d)) :
  log
    (ὕ Ι
     (ar.bn d (au d))
     (ar.bd d (au d)):ℝ) ≤
   (1024*Ü*14658798:ℕ) *
    ((d+1:ℕ):ℝ)^11:=by
 let bn:=ar.bn d (au d)
 let bd:=ar.bd d (au d)
 have ù:0<bn:=by
  unfold bn
  exact ar.mc (ἢ d)
 have fw:0<bd:=by
  unfold bd
  exact ar.md (ἢ d)
 have GB:log (bn:ℝ) ≤
   7700594*((d+1:ℕ):ℝ)^2:=by
  simpa[bn] using qd d
 have GC:log (bd:ℝ) ≤
   6958194*((d+1:ℕ):ℝ)^2:=by
  simpa[bd] using qe d
 have Nz:=fI ù GB
 have NA:=fI fw GC
 have pb:(1:ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have tj:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 have DJ :
   log ((3*bn:ℕ):ℝ)+log 4 ≤
    7700599*((d+1:ℕ):ℝ)^2:=by
  nlinarith[lS]
 have DK :
   log ((3*bd:ℕ):ℝ)+log 4 ≤
    6958199*((d+1:ℕ):ℝ)^2:=by
  nlinarith[lS]
 have sP:(Ι:ℝ) ≤
   (1024*Ü:ℕ) *
    ((d+1:ℕ):ℝ)^9:=by
  calc
   _ ≤
     (ar.ax d (au d):ℝ):=by
    exact_mod_cast Ñ
   _≤(1024*Ü:ℕ) *
     ((d+1:ℕ):ℝ)^9:=by
    exact_mod_cast ff d
 have xI :
   0≤log ((3*bn:ℕ):ℝ)+log 4:=by
  have ώ:(1:ℝ)≤(3*bn:ℕ):=by
   exact_mod_cast(show 1≤3*bn by omega)
  nlinarith[Ἲ ώ,Ἲ (show(1:ℝ)≤4 by norm_num)]
 have xJ :
   0≤log ((3*bd:ℕ):ℝ)+log 4:=by
  have ώ:(1:ℝ)≤(3*bd:ℕ):=by
   exact_mod_cast(show 1≤3*bd by omega)
  nlinarith[Ἲ ώ,Ἲ (show(1:ℝ)≤4 by norm_num)]
 rw[qf ù fw]
 have GD:=ὤ sP DJ xI (by positivity)
 have GF:=ὤ sP DK xJ (by positivity)
 push_cast at GD GF ⊢
 nlinarith
lemma gD
  (d Ι:ℕ)
  (Ñ:Ι ≤
   ar.ax d (au d)) :
  log (ᾄ Ι:ℝ) ≤
   (1024*Ü*20646194:ℕ) *
    ((d+1:ℕ):ℝ)^11:=by
 let R:=ar.ax d (au d)
 have Ὡ:0<R:=by
  unfold R
  exact ar.iH (ἢ d)
 have wR:log (R:ℝ) ≤
   6881393*((d+1:ℕ):ℝ)^2:=by
  simpa[R] using eG d
 have N2:log ((max Ι 1:ℕ):ℝ) ≤
   6881393*((d+1:ℕ):ℝ)^2:=
  (ky Ὡ (by simpa[R] using Ñ)).trans wR
 have wS:0< max Ι 1:=by positivity
 have A9:(0:ℝ)< max Ι 1:=by exact_mod_cast wS
 have pb:(1:ℝ)≤((d+1:ℕ):ℝ)^2:=by
  have tj:(1:ℝ)≤(d+1:ℕ):=by
   exact_mod_cast(show 1≤d+1 by omega)
  nlinarith
 have Ix :
   log ((1600*max Ι 1:ℕ):ℝ) ≤
    1600+6881393*((d+1:ℕ):ℝ)^2:=by
  rw[show((1600*max Ι 1:ℕ):ℝ) =
    (1600:ℝ)*((max Ι 1:ℕ):ℝ) by norm_num]
  rw[ñ (by norm_num) A9.ne']
  have DI:log (1600:ℝ)≤1600:=
   ῃ (by norm_num)
  nlinarith
 have Fj :
   log ((200*max Ι 1:ℕ):ℝ) ≤
    200+6881393*((d+1:ℕ):ℝ)^2:=by
  rw[show((200*max Ι 1:ℕ):ℝ) =
    (200:ℝ)*((max Ι 1:ℕ):ℝ) by norm_num]
  rw[ñ (by norm_num) A9.ne']
  have DH:log (200:ℝ)≤200:=
   ῃ (by norm_num)
  nlinarith
 have Iy:0<1600*max Ι 1:=by positivity
 have Fk:0<200*max Ι 1:=by positivity
 have NB:=fI Iy Ix
 have Mf:=fI Fk Fj
 have DL :
   log ((3*(1600*max Ι 1):ℕ):ℝ)+log 4 ≤
    6882998*((d+1:ℕ):ℝ)^2:=by
  nlinarith[lS]
 have Ba :
   log ((3*(200*max Ι 1):ℕ):ℝ)+log 4 ≤
    6881598*((d+1:ℕ):ℝ)^2:=by
  nlinarith[lS]
 have sP:(Ι:ℝ) ≤
   (1024*Ü:ℕ) *
    ((d+1:ℕ):ℝ)^9:=by
  calc
   (Ι:ℝ)≤(R:ℝ):=by exact_mod_cast(by simpa[R] using Ñ)
   _≤(1024*Ü:ℕ) *
     ((d+1:ℕ):ℝ)^9:=by
    simpa[R] using(show
     (ar.ax d (au d):ℝ) ≤
      (1024*Ü:ℕ) *
       ((d+1:ℕ):ℝ)^9 by
     exact_mod_cast ff d)
 have xK :
   0≤log ((3*(1600*max Ι 1):ℕ):ℝ)+log 4:=by
  have ώ:(1:ℝ)≤(3*(1600*max Ι 1):ℕ):=by
   exact_mod_cast(show 1≤3*(1600*max Ι 1) by omega)
  nlinarith[Ἲ ώ,Ἲ (show(1:ℝ)≤4 by norm_num)]
 have wy :
   0≤log ((3*(200*max Ι 1):ℕ):ℝ)+log 4:=by
  have ώ:(1:ℝ)≤(3*(200*max Ι 1):ℕ):=by
   exact_mod_cast(show 1≤3*(200*max Ι 1) by omega)
  nlinarith[Ἲ ώ,Ἲ (show(1:ℝ)≤4 by norm_num)]
 rw[nG]
 have GG:=ὤ sP DL xK (by positivity)
 have DM:=ὤ sP Ba wy (by positivity)
 push_cast at GG DM ⊢
 nlinarith
def cv (d Ι Ë:ℕ):ℕ:=
 ὕ Ι
   (ar.bn d (au d))
   (ar.bd d (au d)) *
  ᾄ Ι *
   (3*ἀ Ι Ë
    (cd d
     (ar.ax d (au d))))^Ι *
    ᾖ d
def ῂ:ℕ:=
 1024*Ü*57669725 +
  eW
lemma lI (d:ℕ) :
  log (ᾖ d:ℝ) ≤
   (eW:ℝ) *
    ((d+1:ℕ):ℝ)^10:=by
 let R:=ar.ax d (au d)
 let delta:=au d
 let n:=ã d*(8*au d+1)
 have Hm:0<ã d:=by
  unfold ã
  exact Ὴ (Ἧ d)
 have MX:0<delta:=by
  simpa[delta] using ἢ d
 have hn:0<n:=by
  unfold n
  positivity
 have Mg:log (n:ℝ) ≤
   8601726*((d+1:ℕ):ℝ)^2:=by
  simpa[n] using m7 d
 have B1:0≤log (n:ℝ):=by
  apply Ἲ
  exact_mod_cast(show 1≤n by exact Nat.one_le_iff_ne_zero.mpr hn.ne')
 have cu:(delta:ℝ) ≤
   (Ü:ℝ) *
    ((d+1:ℕ):ℝ)^8:=by
  unfold delta
  exact_mod_cast jC d
 have Ὥ:(R:ℝ) ≤
   (1024*Ü:ℕ) *
    ((d+1:ℕ):ℝ)^9:=by
  unfold R
  exact_mod_cast ff d
 have hx:(1:ℝ)≤((d+1:ℕ):ℝ):=by
  exact_mod_cast(show 1≤d+1 by omega)
 have PO:((d+1:ℕ):ℝ)^8 ≤
   ((d+1:ℕ):ℝ)^10:=
  Se hx (by omega)
 have PQ:((d+1:ℕ):ℝ)^9 ≤
   ((d+1:ℕ):ℝ)^10:=
  Se hx (by omega)
 have jx :
   (delta:ℝ)*log (n:ℝ) ≤
    ((Ü:ℝ)*8601726) *
     ((d+1:ℕ):ℝ)^10:=by
  calc
   (delta:ℝ)*log (n:ℝ) ≤
     ((Ü:ℝ) *
      ((d+1:ℕ):ℝ)^8) *
      (8601726*((d+1:ℕ):ℝ)^2):=
    ὤ cu Mg B1 (by positivity)
   _=((Ü:ℝ)*8601726) *
     ((d+1:ℕ):ℝ)^10:=by ring
 have KB:(R+delta:ℝ) ≤
   (1024*Ü +
    Ü:ℕ) *
     ((d+1:ℕ):ℝ)^10:=by
  calc
   (R:ℝ)+delta ≤
     ((1024*Ü:ℕ):ℝ) *
       ((d+1:ℕ):ℝ)^9 +
      Ü *
       ((d+1:ℕ):ℝ)^8:=Sr Ὥ cu
   _≤((1024*Ü:ℕ):ℝ) *
       ((d+1:ℕ):ℝ)^10 +
      Ü *
       ((d+1:ℕ):ℝ)^10:=by
    gcongr
   _=((1024*Ü +
      Ü:ℕ):ℝ) *
     ((d+1:ℕ):ℝ)^10:=by
    push_cast
    ring
 have A8:log (4:ℝ)≤2:=by
  rw[show(4:ℝ)=2^2 by norm_num,ἦ]
  have hmul:=Å Ό
   (show(0:ℝ)≤2 by norm_num)
  norm_num at hmul ⊢
  exact hmul
 have zg:0≤log (4:ℝ):=
  Ἲ (by norm_num)
 have uh :
   (R+delta:ℝ)*log 4 ≤
    (2:ℝ) *
     (1024*Ü +
      Ü) *
     ((d+1:ℕ):ℝ)^10:=by
  calc
   (R+delta:ℝ)*log 4 ≤
     ((1024*Ü +
      Ü:ℕ):ℝ) *
      ((d+1:ℕ):ℝ)^10*2:=
    ὤ KB A8 zg (by positivity)
   _=(2:ℝ) *
     (1024*Ü +
      Ü) *
     ((d+1:ℕ):ℝ)^10:=by
    push_cast
    ring
 unfold ᾖ
 change log (ᾀ R delta n:ℝ)≤_
 rw[wx hn]
 unfold eW
 push_cast at jx uh ⊢
 nlinarith
lemma jX
  (d Ι Ë:ℕ)
  (Ñ:Ι ≤
   ar.ax d (au d))
  (pd:Ë≤8*au d) :
  log (cv d Ι Ë:ℝ) ≤
   (ῂ:ℝ) *
    ((d+1:ℕ):ℝ)^11:=by
 let two:=ὕ Ι
  (ar.bn d (au d))
  (ar.bd d (au d))
 let smooth:=ᾄ Ι
 let source:=
  (3*ἀ Ι Ë
   (cd d
    (ar.ax d (au d))))^Ι
 let cell:=ᾖ d
 have vc:log (two:ℝ) ≤
   (1024*Ü*14658798:ℕ) *
    ((d+1:ℕ):ℝ)^11:=by
  simpa[two] using
   ia d Ι Ñ
 have Ᾱ:log (smooth:ℝ) ≤
   (1024*Ü*20646194:ℕ) *
    ((d+1:ℕ):ℝ)^11:=by
  simpa[smooth] using
   gD d Ι Ñ
 have Ὦ:log (source:ℝ) ≤
   (1024*Ü*22364733:ℕ) *
    ((d+1:ℕ):ℝ)^11:=by
  simpa[source] using
   jT d Ι Ë Ñ pd
 have ό:log (cell:ℝ) ≤
   (eW:ℝ) *
    ((d+1:ℕ):ℝ)^10:=by
  simpa[cell] using lI d
 have hx:(1:ℝ)≤((d+1:ℕ):ℝ):=by
  exact_mod_cast(show 1≤d+1 by omega)
 have KC:((d+1:ℕ):ℝ)^10 ≤
   ((d+1:ℕ):ℝ)^11:=
  Se hx (by omega)
 have Iz:log (cell:ℝ) ≤
   (eW:ℝ) *
    ((d+1:ℕ):ℝ)^11:=
  ό.trans (Å KC (by positivity))
 have uG:(0:ℝ)<two:=by
  have ù:=ar.mc (d:=d)
   (aq:=au d) (ἢ d)
  have fw:=ar.md (d:=d)
   (aq:=au d) (ἢ d)
  unfold two ὕ
  exact_mod_cast Ὑ
   (ck ù) (ck fw)
 have vd:(0:ℝ)<smooth:=by
  unfold smooth ᾄ ἣ
  positivity
 have yA:(0:ℝ)<source:=by
  unfold source ἀ cd
  positivity
 have GH:(0:ℝ)<cell:=by
  have hq:0<ã d:=by
   unfold ã
   exact Ὴ (Ἧ d)
  unfold cell ᾖ ᾀ
  positivity
 change log ((two*smooth*source*cell:ℕ):ℝ)≤_
 push_cast
 rw[ñ
   (ῐ
    (ῐ uG.ne' vd.ne') yA.ne')
   GH.ne',
  ñ (ῐ uG.ne' vd.ne') yA.ne',
  ñ uG.ne' vd.ne']
 unfold ῂ
 push_cast at vc Ᾱ Ὦ Iz ⊢
 nlinarith
end
end ay.aa
end
section
open Finset Fintype Function
open scoped BigOperators NNReal Pointwise translate
namespace ay.uH
noncomputable section
variable {G:Type*} [Γ G] [Δ G] [Β G]
omit [Β G] [Δ G] in
lemma vs
    {H:Type*} [Γ H]
    (B:aj G) (e:G ≃+ H) (Φ:ℝ≥0) :
    (B.map e).ai Φ=(B.ai Φ).map e:=by
  classical
  rfl
omit [Β G] in
lemma w0
  {H:Type*} [Γ H] [Δ H]
  (B:aj G) (e:G ≃+ H) (É:B.a1) :
  (B.map e).a1:=by
 classical
 unfold aj.a1 at É ⊢
 simp only[aj.Am]
 intro Ρ dy
 have h:=É Ρ dy
 rw[vs,vs,
  aj.kA,aj.kA,
  aj.kA]
 exact h
lemma qR
  {M:ℕ} [NeZero M] (ἄ:Odd M) (B:aj (ZMod M))
  (É:B.a1) :
  (aO.hY M ἄ B).a1:=
       w0 B (aj.eK M ἄ) É
omit [Β G] in
lemma fW
  (B:aj G) (m:ℕ) (hm:0< m) :
  ∃ c:ah.bt (G:=G),
   c.ba.a1 ∧
   c.ba.Ι=B.Ι ∧
   c.Ψ=1 ∧
   c.Η=c.ba.Η ∧
   c.Η⊆(B.ai ((m:ℝ≥0)⁻¹)).Η ∧
   B.Η.card ≤
    ((3*m)^B.Ι*4^B.Ι)*c.Η.card:=by
 classical
 let D:=B.ai ((m:ℝ≥0)⁻¹)
 obtain ⟨R,qk,Ῥ,Hg,ya⟩:=
  ag.kv D
 obtain ⟨c,Bb,_hcouter,wz⟩:=
  ah.bt.od R qk
 refine ⟨c, ?_, ?_, ?_, ?_, ?_, ?_⟩
 ·simpa[Bb] using qk
 ·simpa[Bb,D] using Ῥ
 ·exact _hcouter
 ·simpa[Bb] using wz
 ·simpa[wz,D] using Hg
 ·have Ý:=
   aj.cM
    B 1 hm
  have uD :
    B.Η.card ≤
     (3*m)^B.Ι *
      (B.ai ((m:ℝ≥0)⁻¹)).Η.card:=by
   simpa[ἱ] using Ý
  calc
   _ ≤
     (3*m)^B.Ι *
      (B.ai ((m:ℝ≥0)⁻¹)).Η.card:=uD
   _≤(3*m)^B.Ι*(4^B.Ι*R.Η.card):=
          ὄ _ (by simpa[D] using ya)
   _=((3*m)^B.Ι*4^B.Ι)*c.Η.card:=by
    rw[wz]
    ring
def Ἇ (B:aj G) (m:ℕ):ℕ:=
 (3*m)^B.Ι*4^B.Ι
def Ἄ (B:aj G) (bn bd:ℕ):ℕ:=
 Ἇ B bn*Ἇ B bd
structure ᾗ (B:aj G) (bn bd:ℕ) where
 ak:ah.bt (G:=G)
 aB:ah.bt (G:=G)
 ez:ak.ba.a1
 fe:aB.ba.a1
 Ì:ak.ba.Ι=B.Ι
 p5:aB.ba.Ι=B.Ι
 fT:ak.Ψ=1
 g3:aB.Ψ=1
 eD:ak.Η=ak.ba.Η
 n5:aB.Η=aB.ba.Η
 nY:ak.Η⊆(B.ai ((bn:ℝ≥0)⁻¹)).Η
 p4:aB.Η⊆(B.ai ((bn:ℝ≥0)⁻¹)).Η
 Bc :
  aB.Η ⊆
   (ak.ba.ai ((bd:ℝ≥0)⁻¹)).Η
 kV :
  aO.Û aB.Η ⊆
   (ak.ba.ai
    ((bd:ℝ≥0)⁻¹ +(bd:ℝ≥0)⁻¹)).Η
 mE :
  B.Η.card ≤
   Ἇ B bn*ak.Η.card
 mF :
  B.Η.card ≤
   Ἄ B bn bd*aB.Η.card
lemma rR (B:aj G)
  (bn bd:ℕ) (ù:0<bn) (fw:0<bd)
  (xL:((bd:ℝ≥0)⁻¹)≤1) :
  Nonempty (ᾗ B bn bd):=by
 obtain ⟨Bd,IA,xM,Fl,tP,zy,ve⟩:=
  fW B bn ù
 obtain ⟨xN,IB,Fm,Fn,B2,r2,B3⟩:=
  fW Bd.ba bd fw
 have Fo:xN.Η ⊆
   (B.ai ((bn:ℝ≥0)⁻¹)).Η:=by
  intro x hx
  apply zy
  rw[tP]
  simpa using aj.b5 xL (r2 hx)
 have GI :
   aO.Û xN.Η ⊆
    (Bd.ba.ai
     ((bd:ℝ≥0)⁻¹ +(bd:ℝ≥0)⁻¹)).Η:=by
  intro x hx
  obtain ⟨y,hy,rfl⟩:=aO.m2.mp hx
  exact aj.e8 (r2 hy) (r2 hy)
 have GJ := Fm.trans xM
 have xO :
   B.Η.card ≤
    Ἄ B bn bd*xN.Η.card:=by
  calc
   _ ≤
     Ἇ B bn*Bd.Η.card:=
    ve
   _≤Ἇ B bn *
     (Ἇ Bd.ba bd *
      xN.Η.card):=
    ὄ _
     (by simpa[tP,Ἇ] using B3)
   _=Ἄ B bn bd*xN.Η.card:=by
    simp[Ἇ,Ἄ,xM]
    ring
 exact ⟨{
  ak:=Bd
  aB:=xN
  ez:=IA
  fe:=IB
  Ì:=xM
  p5:=GJ
  fT:=Fl
  g3:=Fn
  eD:=tP
  n5:=B2
  nY:=zy
  p4:=Fo
  Bc:=r2
  kV:=GI
  mE:=ve
  mF:=xO }⟩
structure gj {Λ:Finset G}
  (s:ah.aA Λ) (bn bd:ℕ)
  (Μ Á:ℝ) where
 Be:s.Θ.Ψ=1
 iK:s.Θ.ba.a1
 yB :
  ((bn:ℝ≥0)⁻¹) ≤
   1/(100*(max s.Θ.ba.Ι 1:ℕ):ℝ≥0)
 vt :
  400*((max s.Θ.ba.Ι 1:ℕ):ℝ) *
    (((bn:ℝ≥0)⁻¹ :ℝ≥0):ℝ)≤Μ*s.Ξ/4
 tk :
  exp (-Á)*(s.card:ℝ) ≤
   ((Ἇ s.Θ.ba bn:ℕ):ℝ)⁻¹ *
    (s.Θ.ba.Η.card:ℝ)
 tl :
  exp (-Á)*(s.card:ℝ) ≤
   ((Ἄ s.Θ.ba bn bd:ℕ):ℝ)⁻¹ *
    (s.Θ.ba.Η.card:ℝ)
lemma mm
  {Λ:Finset G} (s:ah.aA Λ)
  {Ἒ:ℕ} {Á:ℝ} {child:Finset G}
  (ᾋ:(0:ℝ)<(Ἒ:ℝ))
  (oe :
   exp (-Á)*(s.card:ℝ) ≤
    (Ἒ:ℝ)⁻¹ *(s.Θ.ba.Η.card:ℝ))
  (GK :
   (s.Θ.ba.Η.card:ℝ) ≤
    (Ἒ:ℝ)*(child.card:ℝ)) :
  exp (-Á)*(s.card:ℝ)≤child.card:=by
 calc
  _ ≤
    (Ἒ:ℝ)⁻¹ *(s.Θ.ba.Η.card:ℝ):= oe
  _≤(Ἒ:ℝ)⁻¹ *((Ἒ:ℝ)*(child.card:ℝ)):=
         Å GK (by positivity)
  _=child.card:=by
   field_simp
lemma jk
  {Λ:Finset G} (s:ah.aA Λ)
  (ju:s.Θ.Ψ=1)
  {Ἒ:ℕ} {Á:ℝ}
  (ᾋ:(0:ℝ)<(Ἒ:ℝ))
  (ei:log (Ἒ:ℝ)≤Á) :
  exp (-Á)*(s.card:ℝ) ≤
   (Ἒ:ℝ)⁻¹ *(s.Θ.ba.Η.card:ℝ):=by
 have Ὁ :
   exp (-Á)≤(Ἒ:ℝ)⁻¹:=by
  have ê := TO ei
  have h:=Real.exp_le_exp.mpr ê
  calc
   _ ≤exp (-log (Ἒ:ℝ)):=h
   _=(Ἒ:ℝ)⁻¹:=by
    rw[Uh,Real.exp_log ᾋ]
 have ch :
   (s.card:ℝ)=(s.Θ.ba.Η.card:ℝ):=by
  unfold ah.aA.card br.aY.card
   br.aY.e9
  simp[ju]
 rw[ch]
 exact ἂ Ὁ (by positivity)
lemma oy
  {Ἒ:ℕ} {Á:ℝ} (ᾋ:0<Ἒ)
  (ei:log (Ἒ:ℝ)≤Á) :
  exp (-Á)*(Ἒ:ℝ)≤1:=by
 have Ὁ:exp (-Á)≤(Ἒ:ℝ)⁻¹:=by
  have ê := TO ei
  calc
   _ ≤exp (-log (Ἒ:ℝ)):=
    Real.exp_le_exp.mpr ê
   _=(Ἒ:ℝ)⁻¹:=by
    rw[Uh,Real.exp_log (by exact_mod_cast ᾋ)]
 calc
  _ ≤(Ἒ:ℝ)⁻¹ *Ἒ:=by gcongr
  _=1:=by
   have Pn:(0:ℝ)<Ἒ:=by exact_mod_cast ᾋ
   field_simp
omit [Δ G] in
lemma lJ
  {A S T D:Finset G} (k:ℕ) {Ν C:ℝ}
  (Õ:0≤Ν) (Ã:0<C)
  (ξ:A.Nonempty) (Ø:S.Nonempty)
  (Cu:Ν*(D.card:ℝ)≤(A.card:ℝ))
  (hsum:((A+S).card:ℝ)≤C*(D.card:ℝ))
  (ἓ :
   (((A.card:ℝ)^k/2*S.card) /
     ((A+S).card:ℝ)^k≤(T.card:ℝ))) :
  (((Ν/C)^k/2)*(S.card:ℝ))≤(T.card:ℝ):=by
 have rY:(0:ℝ)<(A+S).card:=by
  exact_mod_cast(ξ.add Ø).card_pos
 have IC:(0:ℝ)<((A+S).card:ℝ)^k:=by
  positivity
 apply Sj ?_ ἓ
 apply(ἇ IC).2
 calc
  _
                     ≤
   ((Ν/C)^k/2)*(S.card:ℝ) *
    (C*(D.card:ℝ))^k:=by
     gcongr
  _=(Ν*(D.card:ℝ))^k/2*S.card:=by
     have PW := Ã.ne'
     rw[Ἀ]
     field_simp
     have ID:Ν/C*C=Ν:=by field_simp
     rw[←Ἀ (Ν/C) C,ID, ←Ἀ]
  _≤(A.card:ℝ)^k/2*S.card:=by
     gcongr
lemma nH
  (B:aj G) (A S:Finset G) {Φ:ℝ≥0}
  (ξ:A⊆B.Η)
  (Ø:S⊆(B.ai Φ).Η) :
  (-A)+S⊆(B.ai (1+Φ)).Η:=by
 intro x hx
 obtain ⟨u,hu,v,hv,rfl⟩:=Finset.mem_add.mp hx
 obtain ⟨a,ha,rfl⟩:=Finset.mem_neg.mp hu
 exact aj.e8
  (by simpa using(aj.ec.mpr (ξ ha))) (Ø hv)
lemma ij
  (B:aj G) (Ὺ:B.a1)
  (A S:Finset G) {Φ:ℝ≥0}
  (ξ:A⊆B.Η)
  (Ø:S⊆(B.ai Φ).Η)
  (ἧ :
   Φ≤1/(100*(max B.Ι 1:ℕ):ℝ≥0)) :
  (-A+S).card≤2*B.Η.card:=by
 have Ὂ:=nH B A S ξ Ø
 have ch :
   ((B.ai (1+Φ)).Η.card:ℝ) ≤
    (1+100*((max B.Ι 1:ℕ):ℝ)*(Φ:ℝ)) *
     (B.Η.card:ℝ):=
  (Ὺ Φ ἧ).2
 have qI :
   1+100*((max B.Ι 1:ℕ):ℝ)*(Φ:ℝ)≤2:=by
  have NC :
    (Φ:ℝ) ≤
     1/(100*((max B.Ι 1:ℕ):ℝ)):=by
   exact_mod_cast ἧ
  have ND:(0:ℝ)<(max B.Ι 1:ℕ):=by positivity
  have hmul :
    100*((max B.Ι 1:ℕ):ℝ)*(Φ:ℝ)≤1:=by
   calc
    _ ≤
      100*((max B.Ι 1:ℕ):ℝ) *
       (1/(100*((max B.Ι 1:ℕ):ℝ))):=by
        gcongr
    _=1:=by field_simp
  nlinarith
 have KD :
   ((B.ai (1+Φ)).Η.card:ℝ) ≤
    2*(B.Η.card:ℝ):=by
  calc
   _ ≤
     (1+100*((max B.Ι 1:ℕ):ℝ)*(Φ:ℝ)) *
      (B.Η.card:ℝ):=ch
   _≤2*(B.Η.card:ℝ):=by
    gcongr
 have GM :
   ((-A+S).card:ℝ) ≤
    ((B.ai (1+Φ)).Η.card:ℝ):=by
  exact_mod_cast ὣ Ὂ
 exact_mod_cast GM.trans KD
lemma pe
  (B:aj G) (Ὺ:B.a1)
  (S:Finset G) {Φ:ℝ≥0}
  (Ø:S⊆(B.ai Φ).Η)
  (ἧ :
   Φ≤1/(100*(max B.Ι 1:ℕ):ℝ≥0)) :
  (B.Η-S).card≤2*B.Η.card:=by
 have h:=
  ij B Ὺ B.Η S
   (λ _ hx↦hx) Ø ἧ
 have ê :
   (B.Η-S).card=(-B.Η+S).card:=by
  rw[←Finset.card_neg]
  simp[Ἱ,ῒ]
 rw[ê]
 exact h
lemma mL
  (B:aj G) (Ὺ:B.a1)
  (S:Finset G) {Φ:ℝ≥0}
  (Ø:S⊆(B.ai Φ).Η)
  (ἧ :
   Φ≤1/(100*(max B.Ι 1:ℕ):ℝ≥0))
  (z:G) :
  ((z+ᵥ B.Η)-S).card≤2*B.Η.card:=by
 have dc:=pe B Ὺ S Ø ἧ
 have heq :
   (z+ᵥ B.Η)-S=z+ᵥ (B.Η-S):=by
  ext x
  constructor
  ·intro hx
   obtain ⟨u,hu,v,hv,rfl⟩:=Finset.mem_sub.mp hx
   obtain ⟨b,hb,rfl⟩:=Finset.mem_vadd_finset.mp hu
   apply Finset.mem_vadd_finset.mpr
   exact ⟨b-v,Finset.mem_sub.mpr ⟨b,hb,v,hv,rfl⟩,by
    simp only[Uz]
    abel⟩
  ·intro hx
   obtain ⟨u,hu,rfl⟩:=Finset.mem_vadd_finset.mp hx
   obtain ⟨b,hb,v,hv,rfl⟩:=Finset.mem_sub.mp hu
   apply Finset.mem_sub.mpr
   exact ⟨z+b,Finset.mem_vadd_finset.mpr ⟨b,hb,rfl⟩,
    v,hv,by
     simp only[Uz]
     abel⟩
 rw[heq,Finset.card_vadd_finset]
 exact dc
structure Ἓ (W:aj G) where
 Ο:ℝ≥0
 Ä:aj G
 vf:ℝ≥0
 ς:ℝ≥0
 bx:aj G
 vg:ℝ≥0
 Æ:ℝ≥0
 bl:aj G
 pg:ℝ≥0
 Fp:Ο=1/(1600*(max W.Ι 1:ℕ):ℝ≥0)
 uB:0<Ο
 mI :
  4*Ο≤1/(400*(max W.Ι 1:ℕ):ℝ≥0)
 GN:Ä=(W.ai Ο).ai vf
 zz:1/2≤vf
 GO:vf≤1
 zA:Ä.a1
 Bf:ς=1/(200*(max Ä.Ι 1:ℕ):ℝ≥0)
 ὥ:0<ς
 xc :
  ς≤1/(100*(max Ä.Ι 1:ℕ):ℝ≥0)
 GQ:bx=(Ä.ai ς).ai vg
 zB:1/2≤vg
 GR:vg≤1
 zC:bx.a1
 Fq:Æ=1/(200*(max bx.Ι 1:ℕ):ℝ≥0)
 IE:0<Æ
 zD :
  Æ≤1/(100*(max bx.Ι 1:ℕ):ℝ≥0)
 zh:bl=(bx.ai Æ).ai pg
 xd:1/2≤pg
 DN:pg≤1
 wA:bl.a1
 rZ:Ä.Η⊆(W.ai Ο).Η
 r0:bx.Η⊆(W.ai Ο).Η
 xe:bx.Η⊆(Ä.ai ς).Η
 DO:bl.Η⊆(W.ai Ο).Η
 wB:bl.Η⊆(bx.ai Æ).Η
omit [Β G] in
lemma rS (W:aj G) :
  Nonempty (Ἓ W):=by
 classical
 let dW := max W.Ι 1
 let Ο:ℝ≥0:=1/(1600*(dW:ℝ≥0))
 have Qe:0<dW:=by simp[dW]
 have IF:0<Ο:=by
  dsimp[Ο]
  positivity
 have vh :
   4*Ο≤1/(400*(max W.Ι 1:ℕ):ℝ≥0):=by
  dsimp[Ο,dW]
  have hd:(0:ℝ≥0)<(max W.Ι 1:ℕ):=by positivity
  field_simp
  norm_num
 obtain ⟨vf,Fr,Bg,Mh⟩:=
  (W.ai Ο).eP
 let Ä:aj G:=(W.ai Ο).ai vf
 let dD := max Ä.Ι 1
 let ς:ℝ≥0:=1/(200*(dD:ℝ≥0))
 have Qf:0<dD:=by simp[dD]
 have Fs:0<ς:=by
  dsimp[ς]
  positivity
 have xf :
   ς≤1/(100*(max Ä.Ι 1:ℕ):ℝ≥0):=by
  dsimp[ς,dD]
  have hd:(0:ℝ≥0)<(max Ä.Ι 1:ℕ):=by positivity
  field_simp
  norm_num
 obtain ⟨vg,Ft,Bh,Mi⟩:=
  (Ä.ai ς).eP
 let bx:aj G:=(Ä.ai ς).ai vg
 let dE := max bx.Ι 1
 let Æ:ℝ≥0:=1/(200*(dE:ℝ≥0))
 have Qg:0<dE:=by simp[dE]
 have IG:0<Æ:=by
  dsimp[Æ]
  positivity
 have zE :
   Æ≤1/(100*(max bx.Ι 1:ℕ):ℝ≥0):=by
  dsimp[Æ,dE]
  have hd:(0:ℝ≥0)<(max bx.Ι 1:ℕ):=by positivity
  field_simp
  norm_num
 obtain ⟨pg,B4,yC,sx⟩:=
  (bx.ai Æ).eP
 let bl:aj G:=(bx.ai Æ).ai pg
 have gn:Ä.Η⊆(W.ai Ο).Η:=by
  dsimp[Ä]
  simpa using
   (aj.b5 Bg :
    ((W.ai Ο).ai vf).Η ⊆
     ((W.ai Ο).ai 1).Η)
 have Cv :
   bx.Η⊆(Ä.ai ς).Η:=by
  dsimp[bx]
  simpa using
   (aj.b5 Bh :
    ((Ä.ai ς).ai vg).Η ⊆
     ((Ä.ai ς).ai 1).Η)
 have Fu:ς≤1:=by
  calc
   _ ≤1/(100*(max Ä.Ι 1:ℕ):ℝ≥0):=
    xf
   _≤1:=by
    rw[ᾜ]
    ·exact_mod_cast(show 1≤100*max Ä.Ι 1 by omega)
    ·positivity
 have lk:bx.Η⊆(W.ai Ο).Η:=by
  apply Cv.trans
  apply(aj.b5 Fu).trans
  simpa using gn
 have Bi :
   bl.Η⊆(bx.ai Æ).Η:=by
  dsimp[bl]
  simpa using
   (aj.b5 yC :
    ((bx.ai Æ).ai pg).Η ⊆
     ((bx.ai Æ).ai 1).Η)
 have IH:Æ≤1:=by
  calc
   _ ≤1/(100*(max bx.Ι 1:ℕ):ℝ≥0):=
    zE
   _≤1:=by
    rw[ᾜ]
    ·exact_mod_cast(show 1≤100*max bx.Ι 1 by omega)
    ·positivity
 have DP:bl.Η⊆(W.ai Ο).Η:=by
  apply Bi.trans
  apply(aj.b5 IH).trans
  simpa using lk
 exact ⟨{
  Ο:=Ο
  Ä:=Ä
  vf:=vf
  ς:=ς
  bx:=bx
  vg:=vg
  Æ:=Æ
  bl:=bl
  pg:=pg
  Fp:=rfl
  uB:=IF
  mI:=vh
  GN:=rfl
  zz:=Fr
  GO:=Bg
  zA:=by simpa[Ä] using Mh
  Bf:=rfl
  ὥ:=Fs
  xc:=xf
  GQ:=rfl
  zB:=Ft
  GR:=Bh
  zC:=by simpa[bx] using Mi
  Fq:=rfl
  IE:=IG
  zD:=zE
  zh:=rfl
  xd:=B4
  DN:=yC
  wA:=by simpa[bl] using sx
  rZ:=gn
  r0:=lk
  xe:=Cv
  DO:=DP
  wB:=Bi }⟩
omit [Β G] in
lemma d0
  (B:aj G) (Φ:ℝ≥0) (ἧ:1/2≤Φ) :
  B.Η.card≤4^B.Ι*(B.ai Φ).Η.card:=by
 classical
 have ἵ:=B.de
 have ym :
   (B.ai (1/2)).Η.card≤(B.ai Φ).Η.card:=
  ὣ (aj.b5 ἧ)
 calc
  B.Η.card≤4^B.Ι*(B.ai (1/2)).Η.card:=
   by simpa using ἵ
  _≤4^B.Ι*(B.ai Φ).Η.card:=
   ὄ _ ym
omit [Β G] in
lemma mn (W:aj G) (H:Ἓ W) :
  H.Ä.Ι=W.Ι∧H.bx.Ι=W.Ι∧H.bl.Ι=W.Ι:=by
 have Ð:H.Ä.Ι=W.Ι:=by
  rw[H.GN,aj.f6,aj.f6]
 have Þ:H.bx.Ι=W.Ι:=by
  rw[H.GQ,aj.f6,aj.f6]
  exact Ð
 have É:H.bl.Ι=W.Ι:=by
  rw[H.zh,aj.f6,aj.f6]
  exact Þ
 constructor
 ·exact Ð
 constructor
 ·exact Þ
 ·exact É
def ὢ (W:aj G):ℕ:=
 ((3*(1600*max W.Ι 1))^W.Ι*4^W.Ι) *
  ((3*(200*max W.Ι 1))^W.Ι*4^W.Ι) *
  ((3*(200*max W.Ι 1))^W.Ι*4^W.Ι)
omit [Β G] in
lemma qg
  (W:aj G) (H:Ἓ W) :
  W.Η.card≤ὢ W*H.bl.Η.card:=by
 classical
 let qh:ℕ:=1600*max W.Ι 1
 let ύ:ℕ:=200*max W.Ι 1
 have Mj:0<qh:=by dsimp[qh]; positivity
 have Cw:0<ύ:=by dsimp[ύ]; positivity
 have uI:=mn W H
 have Mk :
   W.Η.card≤(3*qh)^W.Ι *
    (W.ai H.Ο).Η.card:=by
  have Ý:=
   aj.cM W 1 Mj
  rw[H.Fp]
  simpa[qh,ἱ] using Ý
 have Ml :
   (W.ai H.Ο).Η.card≤4^W.Ι*H.Ä.Η.card:=by
  rw[H.GN]
  simpa only[aj.f6] using
   d0
    (W.ai H.Ο) H.vf H.zz
 have IJ :
   H.Ä.Η.card≤(3*ύ)^W.Ι *
    (H.Ä.ai H.ς).Η.card:=by
  have Ý:=
   aj.cM H.Ä 1 Cw
  rw[H.Bf]
  simpa[ύ,uI.1,ἱ] using Ý
 have Po :
   (H.Ä.ai H.ς).Η.card ≤
    4^W.Ι*H.bx.Η.card:=by
  rw[H.GQ]
  simpa[uI.1] using
   d0
    (H.Ä.ai H.ς) H.vg H.zB
 have IK :
   H.bx.Η.card≤(3*ύ)^W.Ι *
    (H.bx.ai H.Æ).Η.card:=by
  have Ý:=
   aj.cM H.bx 1 Cw
  rw[H.Fq]
  simpa[ύ,uI.2.1,ἱ] using Ý
 have Pp :
   (H.bx.ai H.Æ).Η.card ≤
    4^W.Ι*H.bl.Η.card:=by
  rw[H.zh]
  simpa[uI.2.1] using
   d0
    (H.bx.ai H.Æ) H.pg H.xd
 unfold ὢ
 calc
  _ ≤(3*qh)^W.Ι *
    (W.ai H.Ο).Η.card:=Mk
  _≤(3*qh)^W.Ι*(4^W.Ι*H.Ä.Η.card):=
   ὄ _ Ml
  _≤((3*qh)^W.Ι*4^W.Ι) *
    ((3*ύ)^W.Ι *
     (H.Ä.ai H.ς).Η.card):=by
   have h:=ὄ
    ((3*qh)^W.Ι*4^W.Ι) IJ
   simpa[SZ,R8,U6] using h
  _≤((3*qh)^W.Ι*4^W.Ι) *
    ((3*ύ)^W.Ι*(4^W.Ι*H.bx.Η.card)):=by
   gcongr
  _≤((3*qh)^W.Ι*4^W.Ι) *
    (((3*ύ)^W.Ι*4^W.Ι) *
     ((3*ύ)^W.Ι *
      (H.bx.ai H.Æ).Η.card)):=by
   have h:=ὄ
    (((3*qh)^W.Ι*4^W.Ι) *
     ((3*ύ)^W.Ι*4^W.Ι)) IK
   simpa[SZ,R8,U6] using h
  _≤((3*qh)^W.Ι*4^W.Ι) *
    (((3*ύ)^W.Ι*4^W.Ι) *
     ((3*ύ)^W.Ι*(4^W.Ι*H.bl.Η.card))):=by
   gcongr
  _=(((3*(1600*max W.Ι 1))^W.Ι*4^W.Ι) *
    ((3*(200*max W.Ι 1))^W.Ι*4^W.Ι) *
    ((3*(200*max W.Ι 1))^W.Ι*4^W.Ι)) *
    H.bl.Η.card:=by
   simp[qh,ύ]
   ring
lemma ki
  (W:aj G) {D E:Finset G} {Ο:ℝ≥0}
  (Ð:D⊆(W.ai Ο).Η)
  (Þ:E⊆(W.ai Ο).Η) :
  ∀ t,aN.bh D E t≠0 →
   t∈(W.ai (4*Ο)).Η:=by
 intro t ht
 have zF :
   t∈Function.support (aN.bh D E):=ht
 have qm :
   0≤aN.dU D E:=by
  simp[aN.dU]
 have KE:t∈(D+E)-(D+E):=by
  rw[aN.bh,
   f8 qm qm,
   aN.dU,
   tW õ õ,
   jo,jo] at zF
  simpa only[←coe_add, ←coe_sub,mem_coe] using zF
 obtain ⟨u,hu,v,hv,rfl⟩:=Finset.mem_sub.mp KE
 obtain ⟨d₁,Mm,KF,Mn,rfl⟩:=Finset.mem_add.mp hu
 obtain ⟨d₂,Mo,KG,Mp,rfl⟩:=Finset.mem_add.mp hv
 have Pq :
   d₁+KF∈(W.ai (Ο+Ο)).Η:=
  aj.e8 (Ð Mm) (Þ Mn)
 have Pr :
   d₂+KG∈(W.ai (Ο+Ο)).Η:=
  aj.e8 (Ð Mo) (Þ Mp)
 have Ὂ :
   (d₁+KF)-(d₂+KG) ∈
    (W.ai ((Ο+Ο)+(Ο+Ο))).Η:=
  aj.j2 Pq Pr
 simpa[show(Ο+Ο)+(Ο+Ο)=4*Ο by ring] using Ὂ
lemma ld
  {Λ:Finset G} (s:ah.aA Λ)
  {bn bd:ℕ}
  (C:ᾗ s.Θ.ba bn bd)
  (W:aj G) (H:Ἓ W)
  (kz:W.Η=aO.Û C.aB.Η) :
  ∀ t,
   aN.bh H.bx.Η H.Ä.Η t≠0 →
   t∈(C.ak.ba.ai
    ((bd:ℝ≥0)⁻¹ +(bd:ℝ≥0)⁻¹)).Η:=by
 intro t ht
 have KH  :=
  ki W H.r0 H.rZ t ht
 have GS:4*H.Ο≤(1:ℝ≥0):=by
  calc
   _ ≤
     1/(400*(max W.Ι 1:ℕ):ℝ≥0):=H.mI
   _≤1:=by
    rw[ᾜ]
    ·exact_mod_cast(show 1≤400*max W.Ι 1 by omega)
    ·positivity
 have MY:t∈W.Η:=by
  simpa only[aj.oG] using
   (aj.b5 GS KH)
 rw[kz] at MY
 exact C.kV MY
def gk
  (W:aj G) (H:Ἓ W) (a3:Finset G):Finset G:=
 (-a3)+H.bl.Η
def έ
  (W:aj G) (H:Ἓ W) (a3:Finset G):ℝ:=
 (gk W H a3).card
def ὠ
  (W:aj G) (H:Ἓ W):ℝ:=
 H.bl.Η.card
def ᾓ (a3:Finset G):ℝ:=
 (-a3).card
section wC
variable [MeasurableSpace G] [Α G]
def ἁ
  {A Τ:Finset G} {p:ℕ} {sigma delta:ℝ}
  (W:aj G) (H:Ἓ W)
  (_data:ah.aW A Τ H.bx.Η p sigma delta)
  (k:ℕ):ℝ:=
 ((ah.bj A Τ H.bx.Η p/2)^k)/2
omit [Α G] in
lemma mo
  {A Τ:Finset G} {p:ℕ} {sigma delta:ℝ}
  (W:aj G) (H:Ἓ W)
  (data:ah.aW A Τ H.bx.Η p sigma delta)
  (cu:delta<1)
  (k:ℕ) (T:Finset G)
  (ἓ :
   ((ᾓ data.a3^k/2 *
     ὠ W H) /
     έ W H data.a3^k≤(T.card:ℝ))) :
  ((((ah.bj A Τ H.bx.Η p/2)^k) /
    2)*ὠ W H)≤(T.card:ℝ):=by
 have ᾏ:=data.lR cu
 have Fv:(0:ℝ)<H.bx.Η.card:=by
  exact_mod_cast H.bx.aE.card_pos
 have Cu :
   ah.bj A Τ H.bx.Η p *
     (H.bx.Η.card:ℝ)≤(data.a3.card:ℝ):=
       (ἇ Fv).mp data.tD
 have DQ :
   ah.bj A Τ H.bx.Η p *
     (H.bx.Η.card:ℝ)≤((-data.a3).card:ℝ):=by
  simpa using Cu
 have yZ :
   (gk W H data.a3).card ≤
    2*H.bx.Η.card:=by
  unfold gk
  apply ij H.bx H.zC
   data.a3 (H.bl).Η data.rM H.wB H.zD
 have hsum :
   έ W H data.a3 ≤
    2*(H.bx.Η.card:ℝ):=by
  unfold έ
  exact_mod_cast yZ
 have Õ :
   0≤ah.bj A Τ H.bx.Η p:=by
  unfold ah.bj
  exact RS (å (by norm_num) (ἥ tX _))
   (by positivity)
 have Mq:(-data.a3).Nonempty:=by
  obtain ⟨a,ha⟩:=ᾏ.2
  exact ⟨-a,by simpa using ha⟩
 simpa only[ᾓ,ὠ,έ,
  gk,show(2:ℝ)=2 by rfl] using
  (lJ
   (A:=-data.a3) (S:=(H.bl).Η) (T:=T)
   (D:=H.bx.Η) k Õ (by norm_num:(0:ℝ)<2)
   Mq (H.bl).aE DQ hsum ἓ)
omit [Α G] in
lemma i5
  {A Τ:Finset G} {p:ℕ} {sigma delta:ℝ}
  (W:aj G) (H:Ἓ W)
  (data:ah.aW A Τ H.bx.Η p sigma delta)
  (cu:delta<1)
  (k:ℕ) (T:Finset G) (Κ:Finset (Ε G ℂ))
  (Ἤ:0 <
   ἁ (A:=A) (Τ:=Τ) (p:=p) (sigma:=sigma)
    (delta:=delta) W H data k)
  (ἓ :
   ((ᾓ data.a3^k/2 *
     ὠ W H) /
     έ W H data.a3^k≤(T.card:ℝ)))
  (ó:(Κ.card:ℝ) ≤
   aI.bf H.bl T (1/2)) :
  Κ.card ≤
   ⌈8*(1+log (2 /
    ἁ (A:=A) (Τ:=Τ) (p:=p) (sigma:=sigma)
     (delta:=delta) W H data k))⌉₊:=by
 have wD :
   ἁ (A:=A) (Τ:=Τ) (p:=p) (sigma:=sigma)
     (delta:=delta) W H data k*(H.bl.Η.card:ℝ) ≤
    (T.card:ℝ):=by
  simpa[ἁ,ὠ] using
   mo W H data cu k T ἓ
 have ί :
   aI.bf H.bl T (1/2) ≤
    8*(1+log (2 /
     ἁ (A:=A) (Τ:=Τ) (p:=p) (sigma:=sigma)
      (delta:=delta) W H data k)):=
  fQ H.bl T Ἤ
   (by
    have gy:(0:ℝ) <
      ἁ (A:=A) (Τ:=Τ) (p:=p) (sigma:=sigma)
       (delta:=delta) W H data k *
      (H.bl.Η.card:ℝ):=
     Ἃ Ἤ (by exact_mod_cast H.bl.aE.card_pos)
    have DR:(0:ℝ)<T.card:=gy.trans_le wD
    exact Finset.card_pos.mp (by exact_mod_cast DR))
   wD
 exact ov Κ (ó.trans ί)
omit [Α G] in
lemma oz
  {A Τ:Finset G} {p:ℕ} {sigma delta:ℝ}
  (W:aj G) (H:Ἓ W)
  (data:ah.aW A Τ H.bx.Η p sigma delta)
  (cu:delta<1)
  (k:ℕ) (T:Finset G)
  (Ἤ:0 <
   ἁ (A:=A) (Τ:=Τ) (p:=p) (sigma:=sigma)
    (delta:=delta) W H data k)
  (ἓ :
   ((ᾓ data.a3^k/2 *
     ὠ W H) /
     έ W H data.a3^k≤(T.card:ℝ))) :
  aI.bf H.bl T (1/2) ≤
   8*(1+log (2 /
    ἁ (A:=A) (Τ:=Τ) (p:=p) (sigma:=sigma)
     (delta:=delta) W H data k)):=by
 have wD :
   ἁ (A:=A) (Τ:=Τ) (p:=p) (sigma:=sigma)
     (delta:=delta) W H data k*(H.bl.Η.card:ℝ) ≤
    (T.card:ℝ):=by
  simpa[ἁ,ὠ] using
   mo W H data cu k T ἓ
 apply fQ H.bl T Ἤ
 ·have gy:(0:ℝ) <
    ἁ (A:=A) (Τ:=Τ) (p:=p) (sigma:=sigma)
      (delta:=delta) W H data k *
     (H.bl.Η.card:ℝ):=
   Ἃ Ἤ (by exact_mod_cast H.bl.aE.card_pos)
  have DR:(0:ℝ)<T.card:=gy.trans_le wD
  exact Finset.card_pos.mp (by exact_mod_cast DR)
 ·exact wD
end wC
lemma n6
  {Λ:Finset G} (s:ah.aA Λ)
  {d:ℕ}
  (Ý:(1/(2:ℝ)^d)≤ s.Ξ) :
  (2/3:ℝ)^(4*(d+1)) ≤
   (1-(1/512:ℝ))*s.Ξ:=by
 have dc:(2/3:ℝ)^4≤1/2:=by norm_num
 have hpow :
   (2/3:ℝ)^(4*(d+1))≤(1/2:ℝ)^(d+1):=by
  calc
   _ =
     ((2/3:ℝ)^4)^(d+1):=by rw[Ἂ]
   _≤(1/2:ℝ)^(d+1):=
    ἤ (by positivity) dc (d+1)
 have we :
   (1/2:ℝ)^(d+1) ≤
    (511/512:ℝ)*(1/(2:ℝ)^d):=by
  have DS:0≤(1/2:ℝ)^d:=by positivity
  rw[ᾬ]
  calc
   _ ≤
     (1/2:ℝ)^d*(511/512):=
    Å (by norm_num) DS
   _=(511/512:ℝ)*(1/(2:ℝ)^d):=by
    simp[ῆ,Te,ä]
 calc
  _ ≤(1/2:ℝ)^(d+1):=hpow
  _≤(511/512:ℝ)*(1/(2:ℝ)^d):=we
  _≤(511/512:ℝ)*s.Ξ:=
   Å Ý (by norm_num)
  _=(1-(1/512:ℝ))*s.Ξ:=by ring
noncomputable def bF
    {Λ:Finset G}
    (s:bu.aG Λ)
    {bn bd:ℕ} (ù:0<bn) (fw:0<bd)
    (C:ᾗ s.aV.Θ.ba bn bd)
    {Μ Á:ℝ} {aq:ℕ}
    (ἴ:gj s.aV bn bd Μ Á) :
    bu.dB s Μ Á aq:=by
  have zX :
      (0:ℝ)<(Ἇ s.aV.Θ.ba bn:ℝ):=by
    unfold Ἇ
    positivity
  have zY :
      (0:ℝ) <
        (Ἄ s.aV.Θ.ba bn bd:ℝ):=by
    unfold Ἄ Ἇ
    positivity
  have IL :
      (s.aV.Θ.ba.Η.card:ℝ) ≤
        (Ἇ s.aV.Θ.ba bn:ℝ) *
          (C.ak.Η.card:ℝ):=by
    exact_mod_cast C.mE
  have IM :
      (s.aV.Θ.ba.Η.card:ℝ) ≤
        (Ἄ s.aV.Θ.ba bn bd:ℝ) *
          (C.aB.Η.card:ℝ):=by
    exact_mod_cast C.mF
  have ve :
      exp (-Á)*(s.card:ℝ)≤C.ak.Η.card:=by
    simpa[bu.aG.card] using
      mm s.aV zX ἴ.tk IL
  have xO :
      exp (-Á)*(s.card:ℝ)≤C.aB.Η.card:=by
    simpa[bu.aG.card] using
      mm s.aV zY ἴ.tl IM
  have o5 :
      ὒ s.aV.Θ.set
          s.aV.Θ.ba.Η=s.aV.Ξ:=by
    unfold ah.aA.Ξ
      br.aY.Ξ ὒ
      br.aY.e9
    simp[s.ᾒ]
  refine
    { Ρ:=(bn:ℝ≥0)⁻¹
      xb:=ἴ.yB
      ak:=C.ak
      aB:=C.aB
      fT:=C.fT
      g3:=C.g3
      ez:=C.ez
      fe:=C.fe
      nY:=C.nY
      p4:=C.p4
      tg:= ?_
      Ì:= ?_
      p5:= ?_
      mE:=ve
      mF:=xO }
  · simpa only[o5] using ἴ.vt
  · rw[C.Ì]
    simp[bu.aG.Ι,
      ah.aA.Ι,br.aY.Ι]
  · rw[C.p5]
    simp[bu.aG.Ι,
      ah.aA.Ι,br.aY.Ι]
def Ἢ {Λ:Finset G}
  (s:ah.aA Λ)
  (ak aB:ah.bt (G:=G)) {Μ:ℝ}
  (ο:ah.þ s ak aB Μ):Finset G:=
 ah.dn s.Θ.set ak.Η
  (aO.cr ο)
def jE {Λ:Finset G}
  (s:ah.aA Λ)
  (ak aB:ah.bt (G:=G)) {Μ:ℝ}
  (ο:ah.þ s ak aB Μ):Finset G:=
 ah.dn s.Θ.set aB.Η
  (aO.cr ο)
def ì {Λ:Finset G}
  (s:ah.aA Λ) (Μ:ℝ):ℝ:=
 (1-Μ)*s.Ξ
lemma ph
  {Λ:Finset G} (s:ah.aA Λ)
  (ak aB:ah.bt (G:=G)) {Μ:ℝ}
  (ο:ah.þ s ak aB Μ)
  (ὃ:Μ<1) :
  (Ἢ s ak aB ο).Nonempty:=by
 let Ν:=ì s Μ
 have Õ :=
  Ἃ (sub_pos.mpr ὃ) s.ὰ
 have Έ:Ν ≤
   Ó s.Θ.set ak.Η
    (aO.cr ο):=by
  simpa[Ν,ì] using
   aO.c0 ο
 apply ah.bK
  ak.aE
 exact Õ.trans_le Έ
lemma qS
  {Λ:Finset G} (s:ah.aA Λ)
  (ak aB:ah.bt (G:=G)) {Μ:ℝ}
  (ο:ah.þ s ak aB Μ) :
  Ἢ s ak aB ο⊆ak.Η:=
       ah.dz
  (B:=ak.ba) (Φ:=ak.Ψ)
  (A:=s.Θ.set) (C:=ak.Η)
  (x:=aO.cr ο) (λ _ hz↦hz)
noncomputable def ÿ
  {Λ:Finset G} (s:ah.aA Λ)
  (ak aB:ah.bt (G:=G)) {Μ:ℝ}
  (ο:ah.þ s ak aB Μ)
  (ὃ:Μ<1) :
  ah.aA Λ:=by
 let x:=aO.cr ο
 have oc :=
  Ἃ (sub_pos.mpr ὃ) s.ὰ
 have hx:ì s Μ ≤
   Ó s.Θ.set ak.Η x:=by
  simpa[x,ì] using
   aO.c0 ο
 exact ah.di s ak x (oc.trans_le hx)
@[simp] lemma D1
  {Λ:Finset G} (s:ah.aA Λ)
  (ak aB:ah.bt (G:=G)) {Μ:ℝ}
  (ο:ah.þ s ak aB Μ)
  (ὃ:Μ<1) :
  (ÿ s ak aB ο ὃ).Θ.set =
   Ἢ s ak aB ο:=by
 rfl
lemma na
  {Λ:Finset G} (s:ah.aA Λ)
  {bn bd:ℕ} (ù:0<bn)
  (C:ᾗ s.Θ.ba bn bd)
  {Μ:ℝ}
  (ο:ah.þ s C.ak C.aB Μ)
  (ὃ:Μ<1)
  (ju:s.Θ.Ψ=1) :
  (ÿ s C.ak C.aB ο ὃ).card≤ s.card:=by
 have GU:((bn:ℝ≥0)⁻¹)≤1:=by
  apply(inv_le_one₀ (by exact_mod_cast ù)).2
  exact_mod_cast(show 1≤bn by omega)
 have A5:C.ak.Η.card≤ s.Θ.ba.Η.card:=by
  calc
   _ ≤
     (s.Θ.ba.ai ((bn:ℝ≥0)⁻¹)).Η.card:=
    ὣ C.nY
   _≤(s.Θ.ba.ai 1).Η.card:=
    ὣ (aj.b5 GU)
   _=s.Θ.ba.Η.card:=by simp
 calc
  _ =
    C.ak.Η.card:=by
   simp[ÿ,ah.di,
    ah.bt.eo,
    ah.aA.card,br.aY.card,
    br.aY.e9,C.fT,
    C.eD]
  _≤ s.Θ.ba.Η.card:=A5
  _=s.card:=by
   unfold ah.aA.card br.aY.card
    br.aY.e9
   simp[ju]
lemma mq
  {Λ:Finset G} (s:ah.aA Λ)
  {bn bd:ℕ} (ù:0<bn)
  (C:ᾗ s.Θ.ba bn bd)
  {Μ:ℝ}
  (ο:ah.þ s C.ak C.aB Μ)
  (ὃ:Μ<1)
  (ju:s.Θ.Ψ=1)
  (W:aj G) (H:Ἓ W)
  (wE:W.Η.card=C.aB.Η.card) :
  ((ÿ s C.ak C.aB ο ὃ).card:ℝ) ≤
   ((Ἄ s.Θ.ba bn bd *
     ὢ W:ℕ):ℝ)*(H.bl.Η.card:ℝ):=by
 have mj  :=
  na s ù C ο ὃ ju
 have KI :
   s.card≤Ἄ s.Θ.ba bn bd*W.Η.card:=by
  have Ã:=C.mF
  unfold ah.aA.card br.aY.card
   br.aY.e9
  rw[wE]
  simpa[ju] using Ã
 have Mr:=qg W H
 have ᾳ :
   (ÿ s C.ak C.aB ο ὃ).card ≤
    (Ἄ s.Θ.ba bn bd *
     ὢ W)*H.bl.Η.card:=by
  calc
   _ ≤
     s.card:=mj
   _≤Ἄ s.Θ.ba bn bd*W.Η.card:=KI
   _≤Ἄ s.Θ.ba bn bd *
     (ὢ W*H.bl.Η.card):=
    ὄ _ Mr
   _=(Ἄ s.Θ.ba bn bd *
     ὢ W)*H.bl.Η.card:=by ring
 exact_mod_cast ᾳ
section xP
variable [MeasurableSpace G] [Α G]
lemma mM
  (A Τ ζ:Finset G) {p:ℕ} (hp:0<p) :
  ah.bj A Τ ζ p =
   (4:ℝ)⁻¹ *
    ((A.card:ℝ) *
     an.aM
      (λ x:G=>(((al ((@mu (ℝ≥0) _ _) Τ) (mu ζ))) x:ℝ))
      ((al ((@mu (ℝ) _ _) A) (mu A))) p)^(2*p):=by
 let w:G→ℝ≥0:=(al (mu Τ) (mu ζ))
 have ῧ :
   ((al ((indicator A λ _↦(1:ℝ))) ((indicator A λ _↦(1:_))))) =
    ((A.card:ℝ)^2)•((al ((@mu (ℝ) _ _) A) (mu A))):=by
  rw[←l5 ℝ A,oB,oC]
  funext x
  simp[RD,ᾞ,TI]
  ring
 have Ý:=
  aN.gx w
   ((al ((@mu (ℝ) _ _) A) (mu A))) ((A.card:ℝ)^2) (by positivity) hp
 have ᾷ :
   (b0 p ((al (mu Τ) (mu ζ))) ((al ((indicator A λ _↦(1:ℝ))) ((indicator A λ _↦(1:_)))))) =
    (A.card:ℝ)^2 *
     an.aM
      ((↑) ∘ w)
      ((al ((@mu (ℝ) _ _) A) (mu A))) p:=by
  rw[ῧ]
  simpa only[aN.dN w
   ((A.card:ℝ)^2•((al ((@mu (ℝ) _ _) A) (mu A)))) hp] using Ý
 dsimp[w,Function.comp_def] at ᾷ
 rw[ah.bj,ᾷ]
 by_cases MZ:(A.card:ℝ)=0
 ·have vc:2*p≠0:=by omega
  simp[MZ,vc]
 have hpow:(A.card:ℝ)^(2*p)≠0:=ῄ _ MZ
 field_simp[hpow]
 ring
lemma mN
  (A Τ ζ:Finset G) {p:ℕ} (hp:0<p)
  (É:(Τ∩ζ).Nonempty) (ξ:A.Nonempty) :
  0<ah.bj A Τ ζ p:=by
 classical
 have Ὶ := hp.ne'
 have Ῠ := É.mono Sh
 have u2 := É.mono Sd
 let N:ℝ:=(b0 p ((al (mu Τ) (mu ζ))) ((al ((indicator A λ _↦(1:(ℝ)))) ((indicator A λ _↦(1:_))))))
 have KJ:=
  ah.gQ A Τ ζ p Ὶ Ῠ u2
 obtain ⟨b,hb⟩:=É
 obtain ⟨a,ha⟩:=ξ
 let ᾲ:Fin p→G:=λ _↦b-a
 have v8:b∈cA.cS A Τ ᾲ:=by
  simp only[cA.jn,ᾲ]
  refine ⟨Sh hb, ?_⟩
  intro i
  have:b-(b-a)=a:=by abel
  rwa[this]
 have v9:b∈cA.cS A ζ ᾲ:=by
  simp only[cA.jn,ᾲ]
  refine ⟨Sd hb, ?_⟩
  intro i
  have:b-(b-a)=a:=by abel
  rwa[this]
 have rY :
   0< ∑ u:Fin p→G,
    ((cA.cS A Τ u).card:ℝ) *
     (cA.cS A ζ u).card:=by
  apply Finset.sum_pos'
  ·intro u hu
   positivity
  ·refine ⟨ᾲ,Sz _, ?_⟩
   exact Ἃ
    (by exact_mod_cast(Finset.card_pos.mpr ⟨b,v8⟩))
    (by exact_mod_cast(Finset.card_pos.mpr ⟨b,v9⟩))
 have Hh:0<N^p:=by
  rw[KJ] at rY
  have jt:0<(Τ.card:ℝ)*ζ.card:=by positivity
  rcases mul_pos_iff.mp rY with gy | ê
  ·simpa[N] using gy.2
  ·exact(ῑ jt.le ê.1).elim
 have GV:0≤N:=by
  dsimp[N]
  exact tX
 have NH:N≠0:=by
  intro MS
  rw[MS] at Hh
  simp[Ὶ] at Hh
 have Ms := SM GV (Ne.symm NH)
 unfold ah.bj
 have sF:(0:ℝ)<A.card:=by
  exact_mod_cast(Finset.card_pos.mpr ⟨a,ha⟩)
 dsimp[N] at Ms
 positivity
omit [Α G] in
lemma ik
  (H:Ἓ W)
  {A:Finset G} {p:ℕ} {sigma delta Ν:ℝ} (z:G)
  (data:ah.aW A
   (z+ᵥ H.Ä.Η) H.bx.Η p sigma delta)
  (cu:delta<1)
  (Õ:0≤Ν)
  (Ἡ :
   Ν≤ah.bj A
    (z+ᵥ H.Ä.Η) H.bx.Η p) :
  Ν/2 ≤
   (data.aX.card:ℝ) /
    (ah.aW.bg A
     (z+ᵥ H.Ä.Η) H.bx.Η p sigma).card:=by
 let S :=
  ah.aW.bg A
   (z+ᵥ H.Ä.Η) H.bx.Η p sigma
 have vi:S.Nonempty:=by
  simpa[S] using data.gL cu
 have DT:(0:ℝ)<S.card:=by exact_mod_cast vi.card_pos
 have yk :
   ((z+ᵥ H.Ä.Η).card:ℝ) =
    (H.Ä.Η.card:ℝ):=by
  simp
 have Mt :
   Ν*(H.Ä.Η.card:ℝ)≤(data.aX.card:ℝ):=by
  have ο  :=
   Ἡ.trans data.tC
  rw[yk] at ο
  have Mu:(0:ℝ)<H.Ä.Η.card:=by
   exact_mod_cast H.Ä.aE.card_pos
  exact(ἇ Mu).mp ο
 have Fw :
   S.card≤2*H.Ä.Η.card:=by
  calc
   _ ≤((z+ᵥ H.Ä.Η)-H.bx.Η).card:=
          ὣ
     (ah.aW.oX
      A (z+ᵥ H.Ä.Η) H.bx.Η p sigma)
   _≤2*H.Ä.Η.card:=
    mL H.Ä H.zA
     H.bx.Η H.xe H.xc z
 have EY:(S.card:ℝ)≤2*(H.Ä.Η.card:ℝ):=by
  exact_mod_cast Fw
 apply(ἇ DT).2
 calc
  _ ≤
    Ν/2*(2*(H.Ä.Η.card:ℝ)):=
         Å EY (by positivity)
  _=Ν*(H.Ä.Η.card:ℝ):=by ring
  _≤(data.aX.card:ℝ):=Mt
omit [Γ G] [Β G] [Α G] [Δ G] [MeasurableSpace G] in
lemma oA
  {aX S:Finset G} {Ν:ℝ}
  (Õ:0<Ν) (ἔ:aX.Nonempty) (Ø:S.Nonempty)
  (ἕ:Ν/2≤(aX.card:ℝ)/S.card) :
  Real.sqrt ((S.card:ℝ)/aX.card)≤Real.sqrt (2/Ν):=by
 have xB:(0:ℝ)<aX.card:=by exact_mod_cast ἔ.card_pos
 have DT:(0:ℝ)<S.card:=by exact_mod_cast Ø.card_pos
 have hmul:Ν/2*(S.card:ℝ)≤(aX.card:ℝ):=
  (ἇ DT).mp ἕ
 have hdiv:(S.card:ℝ)/aX.card≤2/Ν:=by
  apply(Sy xB Õ).2
  nlinarith
 exact Real.sqrt_le_sqrt hdiv
omit [Γ G] [Β G] [Α G] [Δ G] [MeasurableSpace G] in
lemma tQ
  (d:ℕ) {Ι:ℕ} {Ρ:ℝ≥0}
  {aX S:Finset G}
  (ἔ:aX.Nonempty) (Ø:S.Nonempty)
  (ἕ :
   aa.Ù d/2 ≤
    (aX.card:ℝ)/S.card)
  (ú :
   (400*((max Ι 1:ℕ):ℝ) *
     (Ρ+Ρ:ℝ≥0)) *
    Real.sqrt (2/aa.Ù d) ≤
    1/2048) :
  2*aa.ὴ +
    (2/(aa.ã d:ℝ) +
     400*((max Ι 1:ℕ):ℝ) *
      (Ρ+Ρ:ℝ≥0) +
     2*(1/2:ℝ)^aa.ἰ d) *
    Real.sqrt ((S.card:ℝ)/aX.card)≤(1/512:ℝ):=by
 classical
 have ᾑ:=aa.Ἧ d
 have DE  :=
  oA ᾑ ἔ Ø ἕ
 have Ᾰ :
   (2/(aa.ã d:ℝ)) *
     Real.sqrt ((S.card:ℝ)/aX.card)≤1/2048:=by
  calc
   _
                                    ≤
    (2/(aa.ã d:ℝ)) *
     Real.sqrt (2/aa.Ù d):=by
      gcongr
   _≤1/2048:=aa.m8 d
 have Cs :
   (400*((max Ι 1:ℕ):ℝ) *
     (Ρ+Ρ:ℝ≥0)) *
    Real.sqrt ((S.card:ℝ)/aX.card)≤1/2048:=by
  calc
   _
                                   ≤
    (400*((max Ι 1:ℕ):ℝ) *
     (Ρ+Ρ:ℝ≥0)) *
    Real.sqrt (2/aa.Ù d):=by
     gcongr
   _≤1/2048:=ú
 have uX :
   (2*(1/2:ℝ)^aa.ἰ d) *
     Real.sqrt ((S.card:ℝ)/aX.card)≤1/2048:=by
  calc
   _
                                    ≤
    (2*(1/2:ℝ)^aa.ἰ d) *
     Real.sqrt (2/aa.Ù d):=by
      gcongr
   _≤1/2048:=aa.pA d
 unfold aa.ὴ
 nlinarith
def ὖ (d ax:ℕ):ℕ:=
 8388608*max ax 1 *
  2^(2+2*d*aa.Ἅ d)
def ὲ (d ax:ℕ):ℝ≥0:=
 ((ὖ d ax:ℕ):ℝ≥0)⁻¹
lemma jF (d ax:ℕ) :
  0<ὖ d ax:=by
 unfold ὖ
 positivity
lemma rh
  (d ax Ι:ℕ) (Ñ:Ι≤ax) :
  (400*((max Ι 1:ℕ):ℝ) *
    (ὲ d ax +
     ὲ d ax:ℝ≥0)) *
   Real.sqrt (2/aa.Ù d) ≤
   1/2048:=by
 let e:ℕ:=2+2*d*aa.Ἅ d
 let P := ὖ d ax
 have Mv:(0:ℝ)<P:=by
  dsimp[P,ὖ,e]
  positivity
 have Ἴ :=
  Sn 1 Ñ
 have DE  :=
  aa.jj
   (aa.Ἧ d)
   (aa.dZ d)
 have hbound :
   (400*((max Ι 1:ℕ):ℝ) *
     (ὲ d ax +
      ὲ d ax:ℝ≥0)) *
    Real.sqrt (2/aa.Ù d) ≤
   (400*((max Ι 1:ℕ):ℝ) *
     (ὲ d ax +
      ὲ d ax:ℝ≥0)) *
    (2/aa.Ù d):=by
  gcongr
 apply hbound.trans
 unfold ὲ ὖ
  aa.Ù
 change
  (400*((max Ι 1:ℕ):ℝ) *
    (((P:ℕ):ℝ)⁻¹ +((P:ℕ):ℝ)⁻¹)) *
   (2/(1/(2:ℝ)^e))≤1/2048
 have NI:((max Ι 1:ℕ):ℝ)≤ max ax 1:=by
  exact_mod_cast Ἴ
 have Ie:(0:ℝ)<(2:ℝ)^e:=by positivity
 have Mw :
   (400*((max Ι 1:ℕ):ℝ) *
     (((P:ℕ):ℝ)⁻¹ +((P:ℕ):ℝ)⁻¹)) *
    (2/(1/(2:ℝ)^e)) =
   1600*((max Ι 1:ℕ):ℝ)*(2:ℝ)^e/P:=by
  field_simp
  ring
 rw[Mw]
 have ὼ :
   (8388608:ℝ)*(max ax 1:ℕ)*(2:ℝ)^e =
    (P:ℝ):=by
  dsimp[P,ὖ]
  norm_cast
 rw[←ὼ]
 have si:(0:ℝ) <
   (8388608:ℝ)*(max ax 1:ℕ)*(2:ℝ)^e:=by
  positivity
 apply(ἲ si).2
 calc
  _ ≤
    1600*((max ax 1:ℕ):ℝ)*(2:ℝ)^e:=by
   gcongr
  _≤(1/2048:ℝ) *
    ((8388608:ℝ)*(max ax 1:ℕ)*(2:ℝ)^e):=by
   have wS:(0:ℝ)<(max ax 1:ℕ):=by positivity
   nlinarith
lemma lK
  (d ax Ι:ℕ) (Ñ:Ι≤ax) :
  ὲ d ax+ὲ d ax ≤
   1/(100*(max Ι 1:ℕ):ℝ≥0):=by
 let e:ℕ:=2+2*d*aa.Ἅ d
 let P:ℕ:=ὖ d ax
 have Mv:(0:ℝ)<P:=by
  dsimp[P,ὖ,e]
  positivity
 have tc:(0:ℝ)<100*(max Ι 1:ℕ):=by positivity
 have Ἴ:max Ι 1≤ max ax 1:=
  Sn 1 Ñ
 have ᾳ:2*(100*max Ι 1)≤P:=by
  dsimp[P,ὖ]
  have hpow:1≤2^e:=Nat.one_le_pow _ _ (by omega)
  calc
   2*(100*max Ι 1)≤200*max ax 1:=by
    omega
   _≤8388608*max ax 1*2^e:=by
    have qI:200≤8388608:=by norm_num
    calc
     200*max ax 1≤8388608*max ax 1:=
      QQ _ qI
     _≤8388608*max ax 1*2^e:=
      Q4 _ (by positivity)
 have uO :
   (2:ℝ)*(P:ℝ)⁻¹ ≤
    1/(100*(max Ι 1:ℕ):ℝ):=by
  have NJ:(2:ℝ)*(100*(max Ι 1:ℕ))≤P:=by
   exact_mod_cast ᾳ
  field_simp
  linarith
 unfold ὲ
 change
  ((P:ℕ):ℝ≥0)⁻¹ +((P:ℕ):ℝ≥0)⁻¹ ≤
   1/(100*(max Ι 1:ℕ):ℝ≥0)
 have Ps :
   (2:ℝ≥0)*((P:ℕ):ℝ≥0)⁻¹ ≤
    1/(100*(max Ι 1:ℕ):ℝ≥0):=by
  exact_mod_cast uO
 simpa[ΐ] using Ps
omit [Α G] in
lemma e6
  (W:aj G) (H:Ἓ W)
  {A Τ:Finset G} {p:ℕ} {sigma delta:ℝ}
  (data:ah.aW A Τ H.bx.Η p sigma delta)
  (d k:ℕ)
  (Ἡ :
   aa.Ù d ≤
    ah.bj A Τ H.bx.Η p)
  (hk:k≤aa.ι d) :
  ⌈8*(1+log (2 /
   ἁ W H data k))⌉₊ ≤
   aa.au d:=by
 let Ν:=aa.Ù d
 let K:=aa.ι d
 let DU:=ah.bj A Τ H.bx.Η p
 have ᾑ:0<Ν:=by
  simpa[Ν] using aa.Ἧ d
 have wF:Ν≤1:=by
  simpa[Ν] using aa.dZ d
 have xQ:0<DU:=ᾑ.trans_le (by simpa[DU,Ν] using Ἡ)
 have qm:0≤Ν/2:=by positivity
 have xR:Ν/2≤1:=by linarith
 have IN:(Ν/2)^K≤(Ν/2)^k:=by
  have æ:k+(K-k)=K:=Nat.add_sub_of_le hk
  calc
   (Ν/2)^K=(Ν/2)^(k+(K-k)):=by rw[æ]
   _=(Ν/2)^k*(Ν/2)^(K-k):=by rw[ᾫ]
   _≤(Ν/2)^k*1:=by
    exact Å
     (Uy qm xR) (by positivity)
   _=(Ν/2)^k:=by ring
 have GW:(Ν/2)^k≤(DU/2)^k:=by
  apply ἤ
  ·positivity
  ·simpa[DU,Ν] using(ῖ Ἡ (by norm_num))
 have DV :
   aa.gs Ν K≤ἁ W H data k:=by
  unfold aa.gs ἁ
  exact ῖ (IN.trans GW) (by norm_num)
 have NK:0<ἁ W H data k:=by
  unfold ἁ
  positivity
 have Fx:0<aa.gs Ν K:=
  aa.zV ᾑ
 have hdiv :
   2/ἁ W H data k ≤
    2/aa.gs Ν K:=by
  exact Rb (by norm_num) Fx DV
 have ei :
   log (2/ἁ W H data k) ≤
    log (2/aa.gs Ν K):=
  ᾆ (by positivity) hdiv
 have y2 :
   8*(1+log (2/ἁ W H data k)) ≤
    8*(1+log (2/aa.gs Ν K)):=by
  nlinarith
 apply Sj (S3 y2)
 unfold aa.au aa.rg
 exact le_max_right _ _
omit [Α G] in
lemma gR
  (W:aj G) (H:Ἓ W)
  {A Τ:Finset G} {p:ℕ} {sigma delta:ℝ}
  (data:ah.aW A Τ H.bx.Η p sigma delta)
  (cu:delta<1)
  (d k:ℕ)
  (Ἡ :
   aa.Ù d ≤
    ah.bj A Τ H.bx.Η p)
  (hk:k≤aa.ι d)
  (T:Finset G)
  (ἓ :
   ((ᾓ data.a3^k/2 *
     ὠ W H) /
     έ W H data.a3^k≤(T.card:ℝ))) :
  aI.bf H.bl T (1/2) ≤
   aa.au d:=by
 have xQ :
   0<ah.bj A Τ H.bx.Η p:=
  (aa.Ἧ d).trans_le Ἡ
 have Ἤ:0<ἁ W H data k:=by
  unfold ἁ
  positivity
 have ί:= oz W H data cu k T Ἤ ἓ
 have Ῡ :
   8*(1+log (2/ἁ W H data k)) ≤
    (⌈8*(1+log (2/ἁ W H data k))⌉₊:ℝ):=
  Rr _
 have Ñ:=e6 W H data d k Ἡ hk
 have Fy :
   (⌈8*(1+log (2/ἁ W H data k))⌉₊:ℝ) ≤
    aa.au d:=by
  exact_mod_cast Ñ
 exact ί.trans (Ῡ.trans Fy)
omit [Α G] in
lemma nb
  (W:aj G) (H:Ἓ W)
  {A Τ:Finset G} {p:ℕ} {sigma delta:ℝ}
  (data:ah.aW A Τ H.bx.Η p sigma delta)
  (cu:delta<1)
  (d k ax:ℕ)
  (Ἡ :
   aa.Ù d ≤
    ah.bj A Τ H.bx.Η p)
  (hk:k≤aa.ι d)
  (Ὰ:H.bl.Ι≤ax)
  (T:Finset G) (Κ:Finset (Ε G ℂ))
  (ἓ :
   ((ᾓ data.a3^k/2 *
     ὠ W H) /
     έ W H data.a3^k≤(T.card:ℝ)))
  (ó:(Κ.card:ℝ) ≤
   aI.bf H.bl T (1/2)) :
  (aa.ã d *
    ag.a6
     (aI.bf H.bl T (1/2))) ^
    Κ.card*4^(H.bl.Ι+Κ.card) ≤
   aa.ᾀ ax
    (aa.au d)
    (aa.ã d *
     (⌈8*(aa.au d:ℝ)⌉₊+1)):=by
 let dim:=aI.bf H.bl T (1/2)
 have ί:dim≤aa.au d:=by
  simpa[dim] using gR W H data cu d k
   Ἡ hk T ἓ
 have Fz :
   ag.a6 dim ≤
    ⌈8*(aa.au d:ℝ)⌉₊+1:=by
  unfold ag.a6
  apply RZ
  apply S3
  have Ἴ:max dim 0≤(aa.au d:ℝ):=
   max_le ί (by positivity)
  have Af:2*pi≤(8:ℝ):=by
   nlinarith[Real.pi_lt_four]
  calc
   2*pi*max dim 0 ≤
     2*pi*aa.au d:=by
    gcongr
   _≤8*(aa.au d:ℝ):=by
    gcongr
 have hq:0<aa.ã d:=by
  unfold aa.ã
  exact aa.Ὴ (aa.Ἧ d)
 have GX :
   0<ag.a6 dim:=by
  unfold ag.a6
  positivity
 have hn :
   0<aa.ã d *
    ag.a6 dim:=
  Ὑ hq GX
 have Hn :
   aa.ã d *
     ag.a6 dim ≤
    aa.ã d *
     (⌈8*(aa.au d:ℝ)⌉₊+1):=
  ὄ _ Fz
 have xQ :
   0<ah.bj A Τ H.bx.Η p:=
  (aa.Ἧ d).trans_le Ἡ
 have Ἤ:0<ἁ W H data k:=by
  unfold ἁ
  positivity
 have DW:Κ.card≤aa.au d:=by
  apply(i5 W H data cu k T Κ
   Ἤ ἓ ó).trans
  exact e6 W H data d k Ἡ hk
 simpa[aa.ᾀ,dim] using
  aa.vE hn Hn Ὰ DW
lemma i6
  (A Τ ζ K:Finset G) (d:ℕ)
  (æ:K.Nonempty)
  (û:1/(2:ℝ)^d≤(A.card:ℝ)/K.card)
  (ᾷ :
   (65/64:ℝ)*(K.card:ℝ)⁻¹ ≤
    an.aM
     (λ x:G=>(((al ((@mu (ℝ≥0) _ _) Τ) (mu ζ))) x:ℝ))
     ((al ((@mu (ℝ) _ _) A) (mu A)))
     (aa.Ἅ d)) :
  aa.Ù d ≤
   ah.bj A Τ ζ
    (aa.Ἅ d):=by
 let r:=aa.Ἅ d
 have hr:0<r:=by
  simpa[r] using aa.fU d
 have x6:(0:ℝ)<K.card:=by exact_mod_cast æ.card_pos
 have Bj:(0:ℝ)≤A.card:=by positivity
 have KK:0≤(A.card:ℝ)/K.card:=by positivity
 have AY :
   1/(2:ℝ)^d ≤
    (A.card:ℝ) *
     an.aM
      (λ x:G=>(((al ((@mu (ℝ≥0) _ _) Τ) (mu ζ))) x:ℝ))
      ((al ((@mu (ℝ) _ _) A) (mu A))) r:=by
  calc
   _ ≤(A.card:ℝ)/K.card:=û
   _≤(65/64:ℝ)*((A.card:ℝ)/K.card):=by
    nlinarith
   _=(A.card:ℝ)*((65/64:ℝ)*(K.card:ℝ)⁻¹):=by
    field_simp
   _≤(A.card:ℝ) *
     an.aM
      (λ x:G=>(((al ((@mu (ℝ≥0) _ _) Τ) (mu ζ))) x:ℝ))
      ((al ((@mu (ℝ) _ _) A) (mu A))) r:=
    Å (by simpa[r] using ᾷ) Bj
 have sy :
   aa.Ù d =
    (4:ℝ)⁻¹ *(1/(2:ℝ)^d)^(2*r):=by
  unfold aa.Ù
  unfold aa.av
  dsimp[r]
  simp only[ῆ, ←Te,ᾫ,Ἂ]
  field_simp
  have hpow :
    (1/2:ℝ) ^
      (d*aa.Ἅ d*2) *
     (4:ℝ)^(d*aa.Ἅ d)=1:=by
   rw[show d*aa.Ἅ d*2 =
     2*(d*aa.Ἅ d) by omega]
   rw[show(4:ℝ)=(2:ℝ)^2 by norm_num, ←Ἂ]
   rw[ῆ,Te]
   field_simp
  norm_num[Ἂ,ᾫ] at hpow ⊢
  have Mx :
    (((1/2:ℝ)^d)^aa.Ἅ d)^2 =
     (((1/2:ℝ)^d)^2) ^
      aa.Ἅ d:=by
   conv_lhs =>
    rw[←Ἂ, ←Ἂ]
   conv_rhs =>
    rw[←Ἂ, ←Ἂ]
   congr 1
   simp[R8]
  rw[Mx] at hpow
  nlinarith
 rw[sy,mM A Τ ζ hr]
 gcongr
lemma qT (d:ℕ) :
  ((1/8192:ℝ)⁻¹)*log (2/(1/8192:ℝ)) ≤
   aa.Ἅ d:=by
 have My:log (2:ℝ)≤1:=by
  convert QX (show(0:ℝ)<2 by norm_num) using 1
  norm_num
 have ei:log (2/(1/8192:ℝ))≤14:=by
  rw[show(2/(1/8192:ℝ))=(2:ℝ)^14 by norm_num,
   ἦ]
  norm_num at My ⊢
  nlinarith
 have Ὢ :
   ((1/8192:ℝ)⁻¹)*log (2/(1/8192:ℝ)) ≤
    (114688:ℝ):=by
  norm_num
  nlinarith
 apply Ὢ.trans
 unfold aa.Ἅ aa.dt
 rw[an.pF]
 norm_num[ᾩ]
 have hd:1≤d+1:=by omega
 norm_num at hd ⊢
 nlinarith
lemma sQ :
  (1+(1/8:ℝ)/32) ≤
   (65/64:ℝ)*(1-1/8192) *
    (1-1/8192-1/512):=by
 norm_num
omit [Α G] [MeasurableSpace G] in
lemma rT
  {Λ:Finset G} (s:ah.aA Λ)
  {bn bd:ℕ} (C:ᾗ s.Θ.ba bn bd)
  {ά:ℝ}
  (ο:ah.þ s C.ak C.aB ά)
  (ἷ:ά<1) :
  (1+(1/8:ℝ)/32) *
    (ÿ s C.ak C.aB ο
     ἷ).Ξ ≤
   ((ÿ s C.ak C.aB ο
     ἷ).Θ.set.card:ℝ) *
    (((1-(1/8192:ℝ)) *
      ((65/64:ℝ)*(C.ak.ba.Η.card:ℝ)⁻¹)) *
     (1-(1/8192:ℝ)-(1/512:ℝ))):=by
 let u:=ÿ s C.ak C.aB ο ἷ
 have x6:(0:ℝ)<C.ak.ba.Η.card:=by
  exact_mod_cast C.ak.ba.aE.card_pos
 have û :
   u.Ξ=(u.Θ.set.card:ℝ) /
    C.ak.ba.Η.card:=by
  simp only[u,ÿ,ah.hQ]
  rw[ah.bk
   C.ak.aE]
  simp[ah.di,ah.bt.eo,
   C.eD]
 rw[show(ÿ s C.ak C.aB ο
   ἷ).Ξ=u.Ξ by rfl,
  show(ÿ s C.ak C.aB ο
   ἷ).Θ.set=u.Θ.set by rfl,
  û]
 have ἴ:=sQ
 have ξ:(0:ℝ)≤u.Θ.set.card:=by positivity
 calc
  _
                                                      ≤
   ((65/64:ℝ)*(1-1/8192) *
    (1-1/8192-1/512)) *
     ((u.Θ.set.card:ℝ)/C.ak.ba.Η.card):=by
   gcongr
  _=(u.Θ.set.card:ℝ) *
    (((1-(1/8192:ℝ)) *
      ((65/64:ℝ)*(C.ak.ba.Η.card:ℝ)⁻¹)) *
     (1-(1/8192:ℝ)-(1/512:ℝ))):=by
   field_simp
omit [Α G] [MeasurableSpace G] in
lemma nc
  {Λ:Finset G} (s:ah.aA Λ)
  {bn bd:ℕ} (C:ᾗ s.Θ.ba bn bd)
  {ά:ℝ}
  (ο:ah.þ s C.ak C.aB ά)
  (zZ:ά=(1/512:ℝ))
  (ἷ:ά<1)
  {d:ℕ} (Ý:1/(2:ℝ)^d≤ s.Ξ) :
  1/(2:ℝ)^(d+1) ≤
   (ÿ s C.ak C.aB ο
    ἷ).Ξ:=by
 let u:=ÿ s C.ak C.aB ο ἷ
 have wG:ì s ά≤u.Ξ:=by
  let x:=aO.cr ο
  have hx:ì s ά ≤
    Ó s.Θ.set C.ak.Η x:=by
   simpa[x,ì] using
    aO.c0 ο
  simpa[u,ÿ,ah.hQ] using hx
 have ἵ :
   1/(2:ℝ)^(d+1) ≤
    (1-(1/512:ℝ))*(1/(2:ℝ)^d):=by
  rw[ᾬ]
  have hpow:(0:ℝ)≤(2:ℝ)^d:=by positivity
  field_simp
  nlinarith
 calc
  _ ≤
    (1-(1/512:ℝ))*(1/(2:ℝ)^d):=ἵ
  _≤(1-(1/512:ℝ))*s.Ξ:=by gcongr
  _=ì s ά:=by simp[ì,zZ]
  _≤u.Ξ:=wG
omit [Α G] [MeasurableSpace G] in
lemma l2
  {Λ:Finset G} (s:ah.aA Λ)
  {d:ℕ} (Ý:1/(2:ℝ)^d≤ s.Ξ) :
  (2/3:ℝ)^aa.dt (d+1) ≤
   ì s (1/512:ℝ):=by
 have dc:0≤(2/3:ℝ):=by norm_num
 have xR:(2/3:ℝ)≤1:=by norm_num
 have Ὁ:aa.dt d ≤
   aa.dt (d+1):=by
  unfold aa.dt
  omega
 calc
  _ ≤
    (2/3:ℝ)^aa.dt d:=
         SJ dc xR Ὁ
  _≤(1-(1/512:ℝ))*s.Ξ:=by
   simpa[aa.dt] using
    n6 s Ý
  _=ì s (1/512:ℝ):=by
   simp[ì]
lemma nd
  {vj Ὓ Ν Υ:ℝ}
  (sF:0<vj) (yd:0< Ὓ)
  (Õ:0<Ν) (wF:Ν≤1)
  (ἒ:Ν*Ὓ≤vj)
  (ú:Υ≤Ν/384) (wH:0≤Υ) :
  2*(vj⁻¹ *Υ)+Ὓ⁻¹ *Υ ≤
   (1/64:ℝ)*Ὓ⁻¹:=by
 have IP := Ἃ Õ yd
 have PR:vj⁻¹ ≤(Ν*Ὓ)⁻¹:=
  (RJ sF IP).2 ἒ
 have jx:vj⁻¹ *Υ≤ Ὓ⁻¹ /384:=by
  calc
   _ ≤(Ν*Ὓ)⁻¹ *Υ:=by gcongr
   _≤(Ν*Ὓ)⁻¹ *(Ν/384):=by gcongr
   _=Ὓ⁻¹ /384:=by
    field_simp
 have FA:Υ≤1/384:=by
  calc
   _ ≤Ν/384:=ú
   _≤1/384:=by gcongr
 have uh:Ὓ⁻¹ *Υ≤ Ὓ⁻¹ /384:=by
  simpa[ἱ] using
   Å FA (by positivity:0≤ Ὓ⁻¹)
 calc
  _ ≤
    2*(Ὓ⁻¹ /384)+Ὓ⁻¹ /384:=by gcongr
  _≤(1/64:ℝ)*Ὓ⁻¹:=by
   have Ma:0≤ Ὓ⁻¹:=by positivity
   nlinarith
omit [Α G] [MeasurableSpace G] in
lemma uJ
  {Λ:Finset G} (s:ah.aA Λ)
  {d aq bn:ℕ}
  (C:ᾗ s.Θ.ba bn
   (ar.bd (d+1) aq))
  (ο:ah.þ s C.ak C.aB (1/512:ℝ))
  (Ý:1/(2:ℝ)^d≤ s.Ξ)
  (Ñ:s.Ι≤ar.ax (d+1) aq)
  (ô:0<aq) :
  2*(((Ἢ s C.ak C.aB ο).card:ℝ)⁻¹ *
    (200*((max C.ak.ba.Ι 1:ℕ):ℝ) *
     (((ar.bd (d+1) aq:ℝ≥0)⁻¹ +
      (ar.bd (d+1) aq:ℝ≥0)⁻¹ :ℝ≥0):ℝ))) +
   (C.ak.ba.Η.card:ℝ)⁻¹ *
    (200*((max C.ak.ba.Ι 1:ℕ):ℝ) *
     (((ar.bd (d+1) aq:ℝ≥0)⁻¹ +
      (ar.bd (d+1) aq:ℝ≥0)⁻¹ :ℝ≥0):ℝ)) ≤
   (1/8:ℝ)/8*(C.ak.ba.Η.card:ℝ)⁻¹:=by
 let Ν:ℝ:=(1-(1/512:ℝ))*(1/(2:ℝ)^d)
 let Υ:ℝ:=
  200*((max C.ak.ba.Ι 1:ℕ):ℝ) *
   (((ar.bd (d+1) aq:ℝ≥0)⁻¹ +
    (ar.bd (d+1) aq:ℝ≥0)⁻¹ :ℝ≥0):ℝ)
 have ῥ:(Ἢ s C.ak C.aB ο).Nonempty:=
  ph s C.ak C.aB ο (by norm_num)
 have Mz:(0:ℝ)<(Ἢ s C.ak C.aB ο).card:=by
  exact_mod_cast ῥ.card_pos
 have x6:(0:ℝ)<C.ak.ba.Η.card:=by
  exact_mod_cast C.ak.ba.aE.card_pos
 have ᾑ:0<Ν:=by unfold Ν; positivity
 have wF:Ν≤1:=by
  unfold Ν
  have û:1/(2:ℝ)^d≤1:=by
   have hpow:(1:ℝ)≤(2:ℝ)^d:=RH (by norm_num)
   exact(ἲ (by positivity)).2 (by simpa using hpow)
  nlinarith
 have Έ:Ν ≤
   Ó s.Θ.set C.ak.Η
    (aO.cr ο):=by
  calc
   Ν≤(1-(1/512:ℝ))*s.Ξ:=by
    unfold Ν
    gcongr
   _=ì s (1/512:ℝ):=by simp[ì]
   _≤Ó s.Θ.set C.ak.Η
     (aO.cr ο):=by
    simpa[ì] using aO.c0 ο
 have ἒ:Ν*(C.ak.ba.Η.card:ℝ) ≤
   (Ἢ s C.ak C.aB ο).card:=by
  rw[ah.bk
   C.ak.aE] at Έ
  have MA:(0:ℝ)<C.ak.Η.card:=by
   exact_mod_cast C.ak.aE.card_pos
  simpa[Ἢ,C.eD] using
   (ἇ MA).mp Έ
 have wH:0≤Υ:=by unfold Υ; positivity
 have ú:Υ≤Ν/384:=by
  have Ἴ:max C.ak.ba.Ι 1 ≤
    ar.ax (d+1) aq:=by
   rw[C.Ì]
   exact ar.i8 ô Ñ
  have Hl:(0:ℝ)<ar.bd (d+1) aq:=by
   exact_mod_cast ar.md ô
  have Ὡ:(0:ℝ)<ar.ax (d+1) aq:=by
   exact_mod_cast ar.iH ô
  have MB:((max C.ak.ba.Ι 1:ℕ):ℝ) ≤
    ar.ax (d+1) aq:=by exact_mod_cast Ἴ
  have Pt:max (C.ak.ba.Ι:ℝ) 1 ≤
    ar.ax (d+1) aq:=by
   simpa[Nat.cast_max] using MB
  unfold Υ Ν ar.bd
  simp only[NNReal.coe_add,SE,S9]
  push_cast
  change 200*max (C.ak.ba.Ι:ℝ) 1 *
    ((76800*ar.ax (d+1) aq *
     2^(d+1+1):ℝ)⁻¹ +
     (76800*ar.ax (d+1) aq *
     2^(d+1+1):ℝ)⁻¹) ≤
   ((1-1/512)*(1/(2:ℝ)^d))/384
  field_simp
  have hpow:(0:ℝ)<(2:ℝ)^d:=by positivity
  have MC:(2:ℝ)^(d+1+1)=4*(2:ℝ)^d:=by
   rw[show d+1+1=d+2 by omega,ᾫ]
   norm_num
   ring
  rw[MC]
  nlinarith
 convert nd Mz x6 ᾑ wF
   ἒ ú wH using 1
 norm_num
open ah in
lemma lL
  {Λ:Finset G} (s:ah.aA Λ)
  (W:aj G) (H:Ἓ W)
  {Τ:Finset G} {p:ℕ} {sigma delta:ℝ}
  (data:ah.aW s.Θ.set Τ
   H.bx.Η p sigma delta)
  (hp:0<p)
  (É:(Τ∩H.bx.Η).Nonempty)
  (cu:delta<1)
  (dv:ℝ) (sH:0<dv)
  (m:ℕ) (hm:m≠0)
  (Ρ:ℝ≥0)
  (dy:Ρ+Ρ ≤
   1/(100*(max H.bl.Ι 1:ℕ):ℝ≥0))
  (ç:ℕ) (pX:0<ç)
  (bm Á:ℝ)
  (ø: ∀ (T:Finset G) (Κ:Finset (Ε G ℂ)),
   (Κ.card:ℝ) ≤
    aI.bf H.bl T (1/2) →
   2*dv +
     (2/(ç:ℝ) +
      400*((max H.bl.Ι 1:ℕ):ℝ) *
       (Ρ+Ρ:ℝ≥0) +
      2*(1/2:ℝ)^m) *
     Real.sqrt
      (((ah.aW.bg
        s.Θ.set Τ H.bx.Η p sigma).card:ℝ) /
       data.aX.card)≤bm)
  {aq bq:ℕ}
  (Ὰ:H.bl.Ι≤ s.Ι)
  (B5 :
   ⌈8*(1+log (2 /
    ἁ W H data
     (ah.cm
      (-(ah.aW.bg
       s.Θ.set Τ H.bx.Η p sigma))
      data.aX dv m)))⌉₊≤aq)
  (DX: ∀ (T:Finset G) (Κ:Finset (Ε G ℂ)),
   ((ᾓ data.a3 ^
     (ah.cm
      (-(ah.aW.bg
       s.Θ.set Τ H.bx.Η p sigma))
      data.aX dv m)/2 *
     ὠ W H) /
     έ W H data.a3 ^
      (ah.cm
       (-(ah.aW.bg
        s.Θ.set Τ H.bx.Η p sigma))
       data.aX dv m)≤(T.card:ℝ)) →
   (Κ.card:ℝ) ≤
    aI.bf H.bl T (1/2) →
   (ç*ag.a6
     (aI.bf H.bl T (1/2))) ^
     Κ.card *
    4^(H.bl.Ι+Κ.card)≤bq)
  (pj:0<bq)
  (Ὦ: ∀ (T:Finset G) (Φ:ℝ≥0) (fl:aj G)
    (_Delta:Finset (Ε G ℂ)),
   ((ᾓ data.a3 ^
     (ah.cm
      (-(ah.aW.bg
       s.Θ.set Τ H.bx.Η p sigma))
      data.aX dv m)/2 *
     ὠ W H) /
     έ W H data.a3 ^
      (ah.cm
       (-(ah.aW.bg
        s.Θ.set Τ H.bx.Η p sigma))
       data.aX dv m)≤(T.card:ℝ)) →
   1/2≤Φ →
   fl=H.bl.ai (Φ *
    aI.cJ H.bl T (1/2)) →
   exp (-Á)*(s.card:ℝ)*(bq:ℝ) ≤
    ((fl.ai Ρ).Η.card:ℝ)) :
  ∃ (parent:aj G) (ὐ:ℝ≥0)
   (source:Finset G) (pk:ℕ),
   ∃ P:ah.cb data parent
    ὐ source aq pk bm,
    P.child.Ι≤ s.Ι+aq ∧
    exp (-Á)*(s.card:ℝ)≤P.child.Η.card:=by
 obtain ⟨T,X,Φ,fl,Κ,nk,ui,ᾉ,ó,
   ᾐ,lj,ᾶ,GY⟩:=
  ej
   data cu dv sH m hm H.bl H.wA
   Ρ dy ç pX bm ø
 obtain ⟨GY⟩:=GY
 let vu:ℕ:=
  (ç*ag.a6
    (aI.bf H.bl T (1/2))) ^
    Κ.card *
   4^(H.bl.Ι+Κ.card)
 let k :=
  ah.cm
   (-(ah.aW.bg
    s.Θ.set Τ H.bx.Η p sigma))
   data.aX dv m
 have zi :
   ((ᾓ data.a3^k/2 *
     ὠ W H) /
     έ W H data.a3^k≤(T.card:ℝ)):=by
  simpa[k,ᾓ,ὠ,
   έ,gk] using nk
 have xQ  :=
  mN s.Θ.set Τ
   H.bx.Η hp É s.Θ.nonempty
 have Ἤ :
   0<ἁ W H data k:=by
  unfold ἁ
  positivity
 have A7:Κ.card≤aq:=by
  apply(i5 W H data cu k T Κ
   Ἤ zi ó).trans
  simpa[k] using B5
 have KL:vu≤bq:=by
  simpa[vu] using DX T Κ zi ó
 let P:=GY.mono A7 KL (le_refl bm)
 have Bk:P.child.Ι≤ s.Ι+aq:=by
  have ὧ:=P.rN
  calc
   _ ≤H.bl.Ι+aq:=by
    simpa[P,ᾶ,aj.f6] using ὧ
   _≤ s.Ι+aq:=RZ Ὰ aq
 have GZ  :=
  Ὦ T Φ fl Κ zi ᾐ ᾶ
 have FB :
   ((fl.ai Ρ).Η.card:ℝ) ≤
    (bq:ℝ)*(P.child.Η.card:ℝ):=by
  have ᾳ  :=
         P.nM
  exact_mod_cast ᾳ
 have FC :
   (bq:ℝ) *
     (exp (-Á)*(s.card:ℝ)) ≤
    (bq:ℝ)*(P.child.Η.card:ℝ):=by
  calc
   _
                                 =
     exp (-Á)*(s.card:ℝ)*bq:=by ring
   _≤((fl.ai Ρ).Η.card:ℝ):=GZ
   _≤(bq:ℝ)*(P.child.Η.card:ℝ):=FB
 have G0:(0:ℝ)<bq:=by exact_mod_cast pj
 have Bl  :=
  Uj FC G0
 exact ⟨fl,Ρ+Ρ,(fl.ai Ρ).Η,
  bq,P,Bk,Bl⟩
lemma jG
  {Λ:Finset G} (s:ah.aA Λ)
  (W:aj G) (H:Ἓ W)
  {d:ℕ} (z:G)
  {p:ℕ} {sigma delta:ℝ}
  (data:ah.aW s.Θ.set
   (z+ᵥ H.Ä.Η) H.bx.Η p sigma delta)
  (hp:0<p)
  (É:((z+ᵥ H.Ä.Η)∩H.bx.Η).Nonempty)
  (cu:delta<1)
  (Ἡ :
   aa.Ù d ≤
    ah.bj s.Θ.set
     (z+ᵥ H.Ä.Η) H.bx.Η p)
  (Ρ:ℝ≥0)
  (dy:Ρ+Ρ ≤
   1/(100*(max H.bl.Ι 1:ℕ):ℝ≥0))
  (bm Á:ℝ)
  (vF:(1/512:ℝ)≤bm)
  (ú :
   (400*((max H.bl.Ι 1:ℕ):ℝ) *
     (Ρ+Ρ:ℝ≥0)) *
    Real.sqrt (2/aa.Ù d) ≤
     1/2048)
  {bq:ℕ}
  (Ὰ:H.bl.Ι≤ s.Ι)
  (DX: ∀ (T:Finset G) (Κ:Finset (Ε G ℂ)),
   ((ᾓ data.a3 ^
     (ah.cm
      (-(ah.aW.bg
       s.Θ.set (z+ᵥ H.Ä.Η)
        H.bx.Η p sigma))
      data.aX aa.ὴ
       (aa.ἰ d))/2 *
     ὠ W H) /
     έ W H data.a3 ^
      (ah.cm
       (-(ah.aW.bg
        s.Θ.set (z+ᵥ H.Ä.Η)
         H.bx.Η p sigma))
       data.aX aa.ὴ
        (aa.ἰ d))≤(T.card:ℝ)) →
   (Κ.card:ℝ) ≤
    aI.bf H.bl T (1/2) →
   (aa.ã d *
     ag.a6
      (aI.bf H.bl T (1/2))) ^
     Κ.card *
    4^(H.bl.Ι+Κ.card)≤bq)
  (pj:0<bq)
  (Ὦ: ∀ (T:Finset G) (Φ:ℝ≥0) (fl:aj G)
    (_Delta:Finset (Ε G ℂ)),
   ((ᾓ data.a3 ^
     (ah.cm
      (-(ah.aW.bg
       s.Θ.set (z+ᵥ H.Ä.Η)
        H.bx.Η p sigma))
      data.aX aa.ὴ
       (aa.ἰ d))/2 *
     ὠ W H) /
     έ W H data.a3 ^
      (ah.cm
       (-(ah.aW.bg
        s.Θ.set (z+ᵥ H.Ä.Η)
         H.bx.Η p sigma))
       data.aX aa.ὴ
        (aa.ἰ d))≤(T.card:ℝ)) →
   1/2≤Φ →
   fl=H.bl.ai (Φ *
    aI.cJ H.bl T (1/2)) →
   exp (-Á)*(s.card:ℝ)*(bq:ℝ) ≤
    ((fl.ai Ρ).Η.card:ℝ)) :
  ∃ (parent:aj G) (ὐ:ℝ≥0)
   (source:Finset G) (pk:ℕ),
   ∃ P:ah.cb data parent
    ὐ source (aa.au d)
     pk bm,
    P.child.Ι≤ s.Ι+aa.au d ∧
    exp (-Á)*(s.card:ℝ)≤P.child.Η.card:=by
 let S :=
  ah.aW.bg s.Θ.set
   (z+ᵥ H.Ä.Η) H.bx.Η p sigma
 let k :=
  ah.cm (-S) data.aX
   aa.ὴ
   (aa.ἰ d)
 have ᾑ:=aa.Ἧ d
 have ἕ :
   aa.Ù d/2 ≤
    (data.aX.card:ℝ)/(-S).card:=by
  simpa[S] using
   ik H z data cu
    (aa.Ἧ d).le Ἡ
 have vk :
   0<aa.ἰ d:=by
  unfold aa.ἰ
  exact aa.sN
   (aa.Ἧ d)
   (aa.dZ d)
 have hk :
   k≤aa.ι d:=by
  dsimp[k]
  unfold aa.ι
  exact aa.ig
   (-S) data.aX ᾑ
   (aa.i3 d) ἕ vk
 have ø :
   ∀ (T:Finset G) (Κ:Finset (Ε G ℂ)),
   (Κ.card:ℝ) ≤
    aI.bf H.bl T (1/2) →
   2*aa.ὴ +
     (2/(aa.ã d:ℝ) +
      400*((max H.bl.Ι 1:ℕ):ℝ) *
       (Ρ+Ρ:ℝ≥0) +
      2*(1/2:ℝ)^aa.ἰ d) *
     Real.sqrt
      (((ah.aW.bg
        s.Θ.set (z+ᵥ H.Ä.Η)
        H.bx.Η p sigma).card:ℝ) /
       data.aX.card)≤bm:=by
  intro T Κ ó
  have ᾏ:=data.lR cu
  have vi:S.Nonempty:=by
   simpa[S] using data.gL cu
  apply(tQ d ᾏ.1 vi
   (by simpa[S] using ἕ) ú).trans
  exact vF
 apply lL s W H data hp É cu
  aa.ὴ
  aa.nE
  (aa.ἰ d) vk.ne'
  Ρ dy (aa.ã d)
  (by
   unfold aa.ã
   exact aa.Ὴ ᾑ)
  bm Á ø Ὰ
 ·simpa[k,S] using
   e6 W H data d k Ἡ hk
 ·exact DX
 ·exact pj
 ·exact Ὦ
omit [Β G] [Α G] [MeasurableSpace G] in
lemma mO
  (B:aj G) (source:Finset G) {Φ:ℝ≥0}
  (P:ℕ) (ὼ:0<P)
  (ἧ:((P:ℝ≥0)⁻¹)≤Φ)
  {mr ὀ Á:ℝ} {bq:ℕ}
  (nI:0≤ὀ)
  (dc:mr≤ὀ*(B.Η.card:ℝ))
  (Ὦ:source=(B.ai Φ).Η)
  (oe :
   exp (-Á)*ὀ *
     (((3*P)^B.Ι:ℕ):ℝ)*(bq:ℝ)≤1) :
  exp (-Á)*mr*(bq:ℝ) ≤
   (source.card:ℝ):=by
 classical
 have B6 :
   B.Η.card≤(3*P)^B.Ι*source.card:=by
  rw[Ὦ]
  exact aa.f5
   B P ὼ ἧ
 have G1 :
   (B.Η.card:ℝ) ≤
    (((3*P)^B.Ι:ℕ):ℝ)*(source.card:ℝ):=by
  exact_mod_cast B6
 have KZ :
   mr≤ὀ *
     (((3*P)^B.Ι:ℕ):ℝ)*(source.card:ℝ):=by
  calc
   mr≤ὀ*(B.Η.card:ℝ):=dc
   _≤ὀ *
     ((((3*P)^B.Ι:ℕ):ℝ)*(source.card:ℝ)):=
    Å G1 nI
   _=ὀ*(((3*P)^B.Ι:ℕ):ℝ) *
     (source.card:ℝ):=by ring
 calc
  _ ≤
    exp (-Á) *
     (ὀ*(((3*P)^B.Ι:ℕ):ℝ) *
      (source.card:ℝ))*(bq:ℝ):=by
       gcongr
  _=(exp (-Á)*ὀ *
     (((3*P)^B.Ι:ℕ):ℝ)*(bq:ℝ)) *
     (source.card:ℝ):=by ring
  _≤1*(source.card:ℝ):=
   ἂ oe (by positivity)
  _=(source.card:ℝ):=by ring
omit [Β G] [Α G] [MeasurableSpace G] in
lemma mP
  (H:Ἓ W) (d ax:ℕ)
  (T:Finset G) (Φ:ℝ≥0) (fl:aj G)
  (ἧ:1/2≤Φ)
  (ᾶ:fl=H.bl.ai (Φ *
   aI.cJ H.bl T (1/2)))
  {mr ὀ Á:ℝ} {bq:ℕ}
  (nI:0≤ὀ)
  (dc:mr≤ὀ*(H.bl.Η.card:ℝ))
  (oe :
   exp (-Á)*ὀ *
     (((3*aa.ἀ H.bl.Ι
       (aI.dg H.bl T (1/2))
       (ὖ d ax))^H.bl.Ι:ℕ):ℝ) *
      (bq:ℝ)≤1) :
  exp (-Á)*mr*(bq:ℝ) ≤
   ((fl.ai (ὲ d ax)).Η.card:ℝ):=by
 classical
 let m:=ὖ d ax
 let P:=aa.ἀ H.bl.Ι
  (aI.dg H.bl T (1/2)) m
 have hm:0< m:=by
  simpa[m] using jF d ax
 have ὼ:0<P:=by
  exact aa.kg hm
 have Ý :
   ((P:ℝ≥0)⁻¹) ≤
    Φ*aI.cJ H.bl T (1/2) *
     (m:ℝ≥0)⁻¹:=by
  simpa[P] using
   aa.i4
    H.bl T (1/2) m hm Φ ἧ
 have G3 :
   (fl.ai (ὲ d ax)).Η =
    (H.bl.ai
     (Φ*aI.cJ H.bl T (1/2) *
      (m:ℝ≥0)⁻¹)).Η:=by
  rw[ᾶ]
  simp[ὲ,m,aj.vo,
   ä,Ῐ]
 apply mO
  (Φ:=Φ*aI.cJ H.bl T (1/2) *
  (m:ℝ≥0)⁻¹)
  H.bl (fl.ai (ὲ d ax)).Η P ὼ
 ·exact Ý
 ·exact nI
 ·exact dc
 ·exact G3
 ·simpa[P,m] using oe
def jH (d:ℕ):ℕ:=
 aa.ã d *
  (⌈8*(aa.au d:ℝ)⌉₊+1)
def ᾃ (d ax:ℕ):ℕ:=
 aa.ᾀ ax
  (aa.au d) (jH d)
def ὔ (d ax:ℕ):ℕ:=
 aa.ἀ ax
  (aa.au d+1)
  (ὖ d ax)
lemma vG (d:ℕ):0<jH d:=by
 unfold jH
 have hq:0<aa.ã d:=by
  unfold aa.ã
  exact aa.Ὴ (aa.Ἧ d)
 positivity
lemma sR (d ax:ℕ) :
  0<ᾃ d ax:=by
 unfold ᾃ aa.ᾀ
 have hn:=vG d
 positivity
omit [Α G] in
lemma nJ
  (W:aj G) (H:Ἓ W)
  {A Τ:Finset G} {p:ℕ} {sigma delta:ℝ}
  (data:ah.aW A Τ H.bx.Η p sigma delta)
  (cu:delta<1)
  (d k:ℕ)
  (Ἡ :
   aa.Ù d ≤
    ah.bj A Τ H.bx.Η p)
  (hk:k≤aa.ι d)
  (T:Finset G)
  (ἓ :
   ((ᾓ data.a3^k/2 *
     ὠ W H) /
     έ W H data.a3^k≤(T.card:ℝ))) :
  aI.dg H.bl T (1/2) ≤
   aa.au d+1:=by
 unfold aI.dg
 apply RZ
 apply Nat.ceil_le.mpr
 exact gR W H data cu d k
  Ἡ hk T ἓ
lemma il
  {Λ:Finset G} (s:ah.aA Λ)
  (W:aj G) (H:Ἓ W)
  {d:ℕ} (z:G)
  {p:ℕ} {sigma delta:ℝ}
  (data:ah.aW s.Θ.set
   (z+ᵥ H.Ä.Η) H.bx.Η p sigma delta)
  (hp:0<p)
  (É:((z+ᵥ H.Ä.Η)∩H.bx.Η).Nonempty)
  (cu:delta<1)
  (Ἡ :
   aa.Ù d ≤
    ah.bj s.Θ.set
     (z+ᵥ H.Ä.Η) H.bx.Η p)
  (ax:ℕ)
  (B7:H.bl.Ι≤ s.Ι)
  (Ὰ:H.bl.Ι≤ax)
  {ὀ ὓ:ℝ}
  (nI:0≤ὀ)
  (dc:(s.card:ℝ)≤ὀ*(H.bl.Η.card:ℝ))
  (oe :
   exp (-ὓ)*ὀ *
     (((3*ὔ d ax)^ax:ℕ):ℝ) *
      (ᾃ d ax:ℝ)≤1) :
  ∃ (parent:aj G) (ὐ:ℝ≥0)
   (source:Finset G) (pk:ℕ),
   ∃ P:ah.cb data parent
    ὐ source (aa.au d)
     pk (1/512:ℝ),
    P.child.Ι≤ s.Ι+aa.au d ∧
    exp (-ὓ)*(s.card:ℝ)≤P.child.Η.card:=by
 let S :=
  ah.aW.bg s.Θ.set
   (z+ᵥ H.Ä.Η) H.bx.Η p sigma
 let k := ah.cm (-S) data.aX
  aa.ὴ (aa.ἰ d)
 have ᾑ:=aa.Ἧ d
 have ἕ :
   aa.Ù d/2 ≤
    (data.aX.card:ℝ)/(-S).card:=by
  simpa[S] using ik H z data cu
   ᾑ.le Ἡ
 have vk:0<aa.ἰ d:=by
  unfold aa.ἰ
  exact aa.sN ᾑ
   (aa.dZ d)
 have hk:k≤aa.ι d:=by
  dsimp[k]
  unfold aa.ι
  exact aa.ig
   (-S) data.aX ᾑ (aa.i3 d)
   ἕ vk
 apply jG s W H z data hp É cu
  Ἡ (ὲ d ax)
  (lK d ax H.bl.Ι Ὰ)
  (1/512:ℝ) ὓ (SF)
  (rh d ax H.bl.Ι Ὰ)
  B7
 ·intro T Κ ἓ ó
  simpa[ᾃ,jH,k,S] using
   nb W H data cu d k ax
    Ἡ hk Ὰ T Κ (by simpa[k,S] using ἓ) ó
 ·exact sR d ax
 ·intro T Φ fl Κ ἓ ᾐ ᾶ
  have pd  :=
   nJ W H data cu d k Ἡ hk T
    (by simpa[k,S] using ἓ)
  have ὼ :
    aa.ἀ H.bl.Ι
      (aI.dg H.bl T (1/2))
      (ὖ d ax) ≤
     ὔ d ax:=by
   unfold ὔ aa.ἀ
   have Ἴ :=
    Sn 1 Ὰ
   gcongr
  have hpow :
    (3*aa.ἀ H.bl.Ι
      (aI.dg H.bl T (1/2))
      (ὖ d ax))^H.bl.Ι ≤
     (3*ὔ d ax)^ax:=by
   calc
    _
                           ≤
     (3*ὔ d ax)^H.bl.Ι:=by
      apply R4
      gcongr
    _≤(3*ὔ d ax)^ax:=by
     apply QR
     ·have IQ:0<ὔ d ax:=by
       unfold ὔ
       exact aa.kg
        (jF d ax)
      exact Ὑ (by norm_num) IQ
     ·exact Ὰ
  have xG :
    exp (-ὓ)*ὀ *
     (((3*aa.ἀ H.bl.Ι
       (aI.dg H.bl T (1/2))
       (ὖ d ax))^H.bl.Ι:ℕ):ℝ) *
      (ᾃ d ax:ℝ)≤1:=by
   apply Sj ?_ oe
   gcongr
  exact mP H d ax T Φ fl
   ᾐ ᾶ nI dc xG
theorem gW
    {Λ : Finset G} (s : ah.aA Λ)
    {D E : Finset G}
    (Ð : D.Nonempty) (Þ : E.Nonempty)
    {Μ sigma delta bm fx Á : ℝ}
    {aq r : ℕ}
    (Ἷ : 0 < Μ)
    (Ὣ : 0 < sigma) (qU : sigma ≤ 1)
    (cu : 0 < delta) (wI : delta < 1)
    (hr : 0 < r) (Bm : Even r) (DY : 2 ≤ r)
    (Bn : sigma⁻¹ * log (2 / delta) ≤ r)
    (rU : 0 ≤ fx)
    (ᾌ : fx ≤
      an.aM
        ((↑) ∘ aN.bh D E)
        ((_root_.al ((@_root_.mu (ℝ) _ _) s.Θ.set) (_root_.mu s.Θ.set))) r)
    (DZ :
      (1 + Μ / 32) * s.Ξ ≤
        (s.Θ.set.card : ℝ) *
          (((1 - sigma) * fx) *
            (1 - delta - bm)))
    (pl :
      ∀ (z : G), z ∈ D - E → ((z +ᵥ E) ∩ D).Nonempty →
        fx ≤
          (_root_.b0 r ((_root_.al (_root_.mu (z +ᵥ E)) (_root_.mu D))) ((_root_.al ((@_root_.mu (ℝ) _ _) s.Θ.set) (_root_.mu s.Θ.set)))) →
        ∀ data : ah.aW s.Θ.set
            (z +ᵥ E) D r sigma delta,
          ∃ (parent : aj G) (ὐ : ℝ≥0)
            (source : Finset G) (bq : ℕ),
            ∃ P : ah.cb data parent
              ὐ source aq bq bm,
              P.child.Ι ≤ s.Ι + aq ∧
              exp (-Á) * (s.card : ℝ) ≤ P.child.Η.card) :
    ∃ t : bu.aG Λ,
      br.dk (1 + Μ / 32) aq Á
        s.Θ t.aV.Θ:= by
  obtain ⟨z, hz, um, rV⟩:=
    ah.lE Ð Þ
      s.Θ.nonempty hr rU ᾌ
  let Τ  :=  z +ᵥ E
  let ζ  :=  D
  have É : (Τ ∩ ζ).Nonempty:= by
    simpa [Τ, ζ] using um
  obtain ⟨data⟩:=
    ah.kM
      (A:= s.Θ.set) (p:= r) (Μ:= sigma) (delta:= delta)
      Τ ζ Ὣ qU cu Bm DY Bn É
      s.Θ.nonempty
  obtain ⟨parent, ὐ, source, bq, P, Bk, Bl⟩:=
    pl z hz (by simpa [Τ, ζ] using um)
      (by simpa [Τ, ζ] using rV)
      (by simpa [Τ, ζ] using data)
  have ᾏ:= data.lR wI
  let S  :=
    ah.aW.bg
      s.Θ.set Τ ζ r sigma
  have ft  :=
          ah.nn ᾏ.1 ᾏ.2
      (by
        simpa only [ah.ca]
          using data.np)
      (by simpa [S] using P.oY)
  have oZ  :=
    mul_nonneg (sub_nonneg.mpr qU) rU
  have sE : ∀ x ∈ S,
      (1 - sigma) * fx ≤
        ((_root_.al ((@_root_.mu (ℝ) _ _) s.Θ.set) (_root_.mu s.Θ.set))) x:= by
    intro x hx
    have xC : x ∈ _root_.s r sigma Τ ζ s.Θ.set:= by
      have FD:= hx
      change x ∈ _root_.s r sigma Τ ζ s.Θ.set ∩ (Τ - ζ) at FD
      exact (Finset.mem_inter.mp FD).1
    have FE :
        (1 - sigma) *
            (_root_.b0 r ((_root_.al (_root_.mu Τ) (_root_.mu ζ))) ((_root_.al ((@_root_.mu (ℝ) _ _) s.Θ.set) (_root_.mu s.Θ.set)))) <
          ((_root_.al ((@_root_.mu (ℝ) _ _) s.Θ.set) (_root_.mu s.Θ.set))) x:=
      (I6.mp xC)
    exact (mul_le_mul_of_nonneg_left rV
      (sub_nonneg.mpr qU)).trans FE.le
  have ῧ : ∀ x, 0 ≤
      ((_root_.al ((@_root_.mu (ℝ) _ _) s.Θ.set) (_root_.mu s.Θ.set))) x:= by
    intro x
    exact dM õ õ x
  obtain ⟨x, hx⟩:=
    ah.jy
      P.child.aE ᾏ.1 ᾏ.2 s.Θ.nonempty
      oZ ῧ sE ft
      (show ((1 - sigma) * fx) * (1 - delta - bm) ≤
          ((1 - sigma) * fx) * (1 - delta - bm) from le_rfl)
  obtain ⟨child, yD, B8, vv⟩:=
    ah.bt.od P.child P.k6
  have FD :
      (1 + Μ / 32) * s.Ξ ≤
        Ó s.Θ.set child.Η x:= by
    rw [vv]
    exact DZ.trans hx
  have gy : 0 < Ó s.Θ.set child.Η x:=
    (mul_pos (by nlinarith [Ἷ]) s.ὰ).trans_le FD
  let t:= ah.di s child x gy
  refine ⟨{ aV:= t, ᾒ:= ?_, iK:= ?_ }, ?_⟩
  · simpa [t, ah.di, ah.bt.eo]
      using B8
  · simpa [t, ah.di, ah.bt.eo,
      yD] using P.k6
  · apply ah.fb s child x gy FD
    · simpa [yD] using Bk
    · simpa [vv] using Bl
lemma gq
  {Λ:Finset G} (s:ah.aA Λ)
  {bn bd:ℕ} (C:ᾗ s.Θ.ba bn bd)
  {ά:ℝ}
  (ο:ah.þ s C.ak C.aB ά)
  (ἷ:ά<1)
  {D E:Finset G} (Ð:D.Nonempty) (Þ:E.Nonempty)
  {Μ sigma delta bm fx eb
   ὓ:ℝ} {aq r:ℕ}
  (Ἷ:0<Μ)
  (Ὣ:0<sigma) (qU:sigma≤1)
  (cu:0<delta) (wI:delta<1)
  (hr:0<r) (Bm:Even r) (DY:2≤r)
  (Bn:sigma⁻¹ *log (2/delta)≤r)
  (rU:0≤fx)
  (jx :
   exp (-eb)*(s.card:ℝ)≤C.ak.Η.card)
  (ᾌ:fx ≤
   an.aM
    ((↑) ∘ aN.bh D E)
    ((al ((@mu ℝ _ _)
     (ÿ s C.ak C.aB ο ἷ).Θ.set) (mu (ÿ s C.ak C.aB ο ἷ).Θ.set)))
    r)
  (DZ :
   (1+Μ/32) *
     (ÿ s C.ak C.aB ο
      ἷ).Ξ ≤
    ((ÿ s C.ak C.aB ο
      ἷ).Θ.set.card:ℝ) *
     (((1-sigma)*fx) *
      (1-delta-bm)))
  (pl :
   ∀ (z:G),z∈D-E→((z+ᵥ E)∩D).Nonempty →
    fx ≤
     (b0 r ((al (mu (z+ᵥ E)) (mu D))) ((al ((@mu (ℝ) _ _)
       (ÿ s C.ak C.aB ο
        ἷ).Θ.set) (mu (ÿ s C.ak C.aB ο
        ἷ).Θ.set)))) →
    ∀ data:ah.aW
      (ÿ s C.ak C.aB ο
       ἷ).Θ.set
      (z+ᵥ E) D r sigma delta,
     ∃ (parent:aj G) (ὐ:ℝ≥0)
      (source:Finset G) (bq:ℕ),
      ∃ P:ah.cb data parent
       ὐ source aq bq bm,
       P.child.Ι ≤
        (ÿ s C.ak C.aB ο
         ἷ).Ι+aq ∧
       exp (-ὓ) *
         ((ÿ s C.ak C.aB ο
          ἷ).card:ℝ)≤P.child.Η.card) :
  ∃ t:bu.aG Λ,
   (1+Μ/32)*ì s ά≤t.Ξ ∧
   t.Ι≤ s.Ι+aq ∧
   exp (-(eb+ὓ))*(s.card:ℝ) ≤
    (t.card:ℝ):=by
 let u:=ÿ s C.ak C.aB ο ἷ
 obtain ⟨t,ht⟩:=
  gW u Ð Þ Ἷ
   Ὣ qU cu wI hr Bm DY Bn rU
   (by simpa[u] using ᾌ) (by simpa[u] using DZ)
   (by simpa[u] using pl)
 have wG:ì s ά≤u.Ξ:=by
  let x:=aO.cr ο
  have hx:ì s ά ≤
    Ó s.Θ.set C.ak.Η x:=by
   simpa[x,ì] using
    aO.c0 ο
  simpa[u,ÿ,ah.hQ] using hx
 have IS :
   exp (-eb)*(s.card:ℝ)≤(u.card:ℝ):=by
  change exp (-eb)*(s.card:ℝ) ≤
   (C.ak.Η.card:ℝ)
  exact jx
 refine ⟨t, ?_, ?_, ?_⟩
 ·exact(Å wG (by nlinarith)).trans ht.1
 ·have Bo:u.Ι=s.Ι:=by
   simpa[u,ÿ,ah.aA.Ι,
    br.aY.Ι,
    ah.di,ah.bt.eo]
    using C.Ì
  rw[←Bo]
  exact ht.2.1
 ·calc
   _ =
     exp (-ὓ) *
      (exp (-eb)*(s.card:ℝ)):=by
    rw[show-(eb+ὓ) =
      -ὓ+ -eb by ring,R7]
    ring
   _≤exp (-ὓ)*(u.card:ℝ):=
    Å IS (ᾰ _).le
   _≤(t.card:ℝ):=ht.2.2
end xP
section IT
def et (K:aj G) (A:Finset G):G→ℝ:=
 (Fintype.card G:ℝ) •
  ao ((@mu (ℝ) _ _) A-mu K.Η) (mu A-mu K.Η)
lemma nf
  {Λ:Finset G} (s:ah.aA Λ)
  {bn bd:ℕ} (C:ᾗ s.Θ.ba bn bd)
  {Μ:ℝ}
  (ο:ah.þ s C.ak C.aB Μ)
  (ὃ:Μ<1)
  (dy :
   (bd:ℝ≥0)⁻¹ +(bd:ℝ≥0)⁻¹ ≤
    1/(100*(max C.ak.ba.Ι 1:ℕ):ℝ≥0))
  (ú :
   2*(((Ἢ s C.ak C.aB ο).card:ℝ)⁻¹ *
     (200*((max C.ak.ba.Ι 1:ℕ):ℝ) *
      (((bd:ℝ≥0)⁻¹ +(bd:ℝ≥0)⁻¹ :ℝ≥0):ℝ))) +
    (C.ak.ba.Η.card:ℝ)⁻¹ *
     (200*((max C.ak.ba.Ι 1:ℕ):ℝ) *
      (((bd:ℝ≥0)⁻¹ +(bd:ℝ≥0)⁻¹ :ℝ≥0):ℝ)) ≤
    (1/8:ℝ)/8*(C.ak.ba.Η.card:ℝ)⁻¹) :
  |(aO.bb
     (Ἢ s C.ak C.aB ο)
     (jE s C.ak C.aB ο) -
    (Fintype.card G:ℝ)/(#C.ak.Η:ℝ)) -
    aw.θ
     (et C.ak.ba
      (Ἢ s C.ak C.aB ο))
     (aO.Û
      (jE s C.ak C.aB ο))| ≤
   ((Fintype.card G:ℝ)/(#C.ak.Η:ℝ))/8:=by
 let Ν:=ì s Μ
 have Õ :=
  Ἃ (sub_pos.mpr ὃ) s.ὰ
 have Έ:Ν ≤
   Ó s.Θ.set C.ak.Η
    (aO.cr ο):=by
  simpa[Ν,ì] using
   aO.c0 ο
 have o0:Ν ≤
   Ó s.Θ.set C.aB.Η
    (aO.cr ο):=by
  simpa[Ν,ì] using
   aO.ea ο
 have ξ :
   (Ἢ s C.ak C.aB ο).Nonempty:=by
  apply ah.bK
   C.ak.aE
  exact Õ.trans_le Έ
 have Ἑ :
   (jE s C.ak C.aB ο).Nonempty:=by
  apply ah.bK
   C.aB.aE
  exact Õ.trans_le o0
 have ἒ :
   Ἢ s C.ak C.aB ο ⊆
    C.ak.ba.Η:=by
  rw[←C.eD]
  exact ah.dz
   (B:=C.ak.ba) (Φ:=C.ak.Ψ)
   (A:=s.Θ.set) (C:=C.ak.Η)
   (x:=aO.cr ο) (λ _ hz↦hz)
 have r2  :=
        ah.dz
   (B:=C.aB.ba) (Φ:=C.aB.Ψ)
   (A:=s.Θ.set) (C:=C.aB.Η)
   (x:=aO.cr ο) (λ _ hz↦hz)
 have ø :
   aO.Û
     (jE s C.ak C.aB ο) ⊆
    (C.ak.ba.ai
     ((bd:ℝ≥0)⁻¹ +(bd:ℝ≥0)⁻¹)).Η:=
  (aO.qJ r2).trans C.kV
 have h:=
  pJ.e5
   C.ez dy ξ ἒ Ἑ ø ú
 simpa[et,C.eD] using h
lemma kj
    {Λ:Finset G}
    (s:bu.aG Λ)
    {bn bd:ℕ} (ù:0<bn) (fw:0<bd)
    (C:ᾗ s.aV.Θ.ba bn bd)
    {Μ Á:ℝ} {aq p:ℕ}
    (ἴ:gj s.aV bn bd Μ Á)
    (ο:ah.þ s.aV
      (bF
        (aq:=aq) s ù fw C ἴ).ak
      (bF
        (aq:=aq) s ù fw C ἴ).aB Μ)
    (ὃ:Μ<1)
    (W:aj G) (u9:W.a1)
    (kz :
      W.Η=aO.Û C.aB.Η)
    {Ο:ℝ≥0} (ò:0<Ο)
    (vh :
      4*Ο≤1/(400*(max W.Ι 1:ℕ):ℝ≥0))
    {D E:Finset G} (Ð:D.Nonempty) (Þ:E.Nonempty)
    (gn:D⊆(W.ai Ο).Η)
    (lk:E⊆(W.ai Ο).Η)
    {Ρ:ℝ≥0}
    (Bp :
      Ρ=(bd:ℝ≥0)⁻¹ +(bd:ℝ≥0)⁻¹)
    (dy :
      Ρ ≤
        1/(100*(max C.ak.ba.Ι 1:ℕ):ℝ≥0))
    (ῶ :
      ∀ t,aN.bh D E t≠0 →
        t∈(C.ak.ba.ai Ρ).Η)
    (ú :
      2*(((Ἢ s.aV C.ak C.aB ο).card:ℝ)⁻¹ *
          (200*((max C.ak.ba.Ι 1:ℕ):ℝ) *
            (Ρ:ℝ))) +
        (C.ak.ba.Η.card:ℝ)⁻¹ *
          (200*((max C.ak.ba.Ι 1:ℕ):ℝ) *
            (Ρ:ℝ)) ≤
        (1/8:ℝ)/8*(C.ak.ba.Η.card:ℝ)⁻¹)
    (jz :
      (2/3:ℝ)^p ≤
        aO.ì s.aV Μ)
    (ᾌ :
      (1+(1/8:ℝ)/8) *
          (C.ak.ba.Η.card:ℝ)⁻¹ ≤
          an.aM
            ((↑) ∘ aN.bh D E)
            ((al ((@mu (ℝ) _ _) (bu.ö ο)) (mu (bu.ö ο))))
            (an.cz (1/8:ℝ) p) →
        ∃ t:bu.aG Λ,
          (257/256:ℝ) *
              aO.ì s.aV Μ≤t.Ξ ∧
          t.Ι≤ s.Ι+aq ∧
          exp (-Á)*(s.card:ℝ)≤(t.card:ℝ)) :
    Nonempty
      (bu.eS (p:=p) s
        (bF
          (aq:=aq) s ù fw C ἴ) ο):=by
  let P:=bF
    (aq:=aq) s ù fw C ἴ
  change ah.þ s.aV C.ak C.aB Μ at ο
  have mj :
      (bu.ö ο).Nonempty:=by
    simpa[bu.ö,Ἢ] using
      ph s.aV C.ak C.aB ο ὃ
  have IU :
      bu.ö ο⊆C.ak.ba.Η:=by
    rw[←C.eD]
    simpa[bu.ö,Ἢ] using
      qS s.aV C.ak C.aB ο
  have ew :
      |(aO.bb
            (bu.ö ο)
            (bu.d3 ο) -
          (Fintype.card G:ℝ)/(#C.ak.Η:ℝ)) -
          aw.θ
            (bu.et C.ak.ba
              (bu.ö ο))
            (aO.Û
              (bu.d3 ο))| ≤
        ((Fintype.card G:ℝ)/(#C.ak.Η:ℝ))/8:=by
    have IV :
        (bd:ℝ≥0)⁻¹ +(bd:ℝ≥0)⁻¹ ≤
          1/(100*(max C.ak.ba.Ι 1:ℕ):ℝ≥0):=by
      simpa[Bp] using dy
    have Bq :
        2*(((Ἢ s.aV C.ak C.aB ο).card:ℝ)⁻¹ *
            (200*((max C.ak.ba.Ι 1:ℕ):ℝ) *
              (((bd:ℝ≥0)⁻¹ +(bd:ℝ≥0)⁻¹ :ℝ≥0):ℝ))) +
          (C.ak.ba.Η.card:ℝ)⁻¹ *
            (200*((max C.ak.ba.Ι 1:ℕ):ℝ) *
              (((bd:ℝ≥0)⁻¹ +(bd:ℝ≥0)⁻¹ :ℝ≥0):ℝ)) ≤
          (1/8:ℝ)/8*(C.ak.ba.Η.card:ℝ)⁻¹:=by
      simpa[Bp] using ú
    simpa[bu.ö,
      bu.d3,Ἢ,jE,
      bu.et,et] using
      nf s.aV C ο ὃ
        IV Bq
  exact ⟨{
    base:=C.ak.ba
    weight:=W
    wj:=C.ez
    uy:=u9
    wk:=by
      change C.ak.ba.Η=C.ak.Η
      exact C.eD.symm
    uA:=kz
    rt:=mj
    th:=IU
    Ο:=Ο
    uB:=ò
    mI:=vh
    D:=D
    E:=E
    yt:=Ð
    yu:=Þ
    rZ:=gn
    r0:=lk
    Ρ:=Ρ
    yv:=dy
    ru:=ῶ
    uC:=ú
    vr:=jz
    e7:=ew
    qN:=ᾌ }⟩
variable [MeasurableSpace G] [Α G]
lemma iE
    {Λ:Finset G}
    (s:bu.aG Λ)
    {d ax bn bd:ℕ}
    (ù:0<bn) (fw:0<bd)
    (C:ᾗ s.aV.Θ.ba bn bd)
    {eb ὓ:ℝ}
    (ἴ:gj s.aV bn bd (1/512:ℝ)
      (eb+ὓ))
    (jx :
      exp (-eb)*(s.card:ℝ)≤C.ak.Η.card)
    (ο:ah.þ s.aV
      (bF
        (aq:=aa.au (d+1))
        s ù fw C ἴ).ak
      (bF
        (aq:=aa.au (d+1))
        s ù fw C ἴ).aB (1/512:ℝ))
    (Ý:1/(2:ℝ)^d≤ s.Ξ)
    (W:aj G) (u9:W.a1)
    (kz:W.Η=aO.Û C.aB.Η)
    (wE:W.Η.card=C.aB.Η.card)
    (yE:W.Ι=s.Ι)
    (H:Ἓ W)
    (ὺ:s.Ι≤ax)
    (dy :
      (bd:ℝ≥0)⁻¹ +(bd:ℝ≥0)⁻¹ ≤
        1/(100*(max C.ak.ba.Ι 1:ℕ):ℝ≥0))
    (ú :
      2*(((Ἢ s.aV C.ak C.aB ο).card:ℝ)⁻¹ *
          (200*((max C.ak.ba.Ι 1:ℕ):ℝ) *
            (((bd:ℝ≥0)⁻¹ +(bd:ℝ≥0)⁻¹ :ℝ≥0):ℝ))) +
        (C.ak.ba.Η.card:ℝ)⁻¹ *
          (200*((max C.ak.ba.Ι 1:ℕ):ℝ) *
            (((bd:ℝ≥0)⁻¹ +(bd:ℝ≥0)⁻¹ :ℝ≥0):ℝ)) ≤
        (1/8:ℝ)/8*(C.ak.ba.Η.card:ℝ)⁻¹)
    (sS :
      exp (-ὓ) *
          ((Ἄ s.aV.Θ.ba bn bd *
            ὢ W:ℕ):ℝ) *
          (((3*ὔ (d+1) ax)^ax:ℕ):ℝ) *
            (ᾃ (d+1) ax:ℝ)≤1) :
    Nonempty (bu.eS
      (p:=aa.dt (d+1)) s
      (bF
        (aq:=aa.au (d+1))
        s ù fw C ἴ) ο):=by
  change ah.þ s.aV C.ak C.aB
    (1/512:ℝ) at ο
  let u:=ÿ s.aV C.ak C.aB ο (by norm_num)
  have uI:=mn W H
  have xg := uI.2.2.trans yE
  have Br:H.bl.Ι≤ax:=by rw[xg]; exact ὺ
  have Bo:u.Ι=s.Ι:=by
    simpa[u,ÿ,ah.aA.Ι,
      bu.aG.Ι,
      br.aY.Ι,
      ah.di,ah.bt.eo]
      using C.Ì
  have D0:H.bl.Ι≤u.Ι:=by
    rw[xg,Bo]
  have N3:1/(2:ℝ)^(d+1)≤u.Ξ:=by
    simpa[u] using nc s.aV C ο rfl
      (by norm_num) Ý
  have dc:(u.card:ℝ) ≤
      ((Ἄ s.aV.Θ.ba bn bd *
          ὢ W:ℕ):ℝ)*(H.bl.Η.card:ℝ):=by
    simpa[u] using mq s.aV ù C ο
      (by norm_num) s.ᾒ W H wE
  have pl :
      ∀ (z:G),z∈H.bx.Η-H.Ä.Η →
        ((z+ᵥ H.Ä.Η)∩H.bx.Η).Nonempty →
        (65/64:ℝ)*(C.ak.ba.Η.card:ℝ)⁻¹ ≤
          (b0 (aa.Ἅ (d+1)) ((al (mu (z+ᵥ H.Ä.Η)) (mu H.bx.Η))) ((al ((@mu (ℝ) _ _) u.Θ.set) (mu u.Θ.set)))) →
        ∀ data:ah.aW u.Θ.set
            (z+ᵥ H.Ä.Η) H.bx.Η
            (aa.Ἅ (d+1))
            (1/8192:ℝ) (1/8192:ℝ),
          ∃ (parent:aj G) (ὐ:ℝ≥0)
            (source:Finset G) (bq:ℕ),
            ∃ P:ah.cb data parent
              ὐ source (aa.au (d+1))
              bq (1/512:ℝ),
              P.child.Ι≤u.Ι+aa.au (d+1) ∧
              exp (-ὓ)*(u.card:ℝ)≤P.child.Η.card:=by
    intro z hz um rV data
    have B9 :
        (65/64:ℝ)*(C.ak.ba.Η.card:ℝ)⁻¹ ≤
          an.aM
            ((NNReal.toReal ∘ ((al (mu (z+ᵥ H.Ä.Η)) (mu H.bx.Η)))):G→ℝ)
            ((al ((@mu (ℝ) _ _) u.Θ.set) (mu u.Θ.set)))
            (aa.Ἅ (d+1)):=by
      rw[aN.dN
        ((al (mu (z+ᵥ H.Ä.Η)) (mu H.bx.Η)))
        ((al ((@mu (ℝ) _ _) u.Θ.set) (mu u.Θ.set)))
        (aa.fU (d+1))]
      exact rV
    have Õ  :=
      i6
        u.Θ.set (z+ᵥ H.Ä.Η) H.bx.Η
        C.ak.ba.Η (d+1)
        C.ak.ba.aE
        (by
          have û :
              u.Ξ=(u.Θ.set.card:ℝ) /
                C.ak.ba.Η.card:=by
            simp only[u,ÿ,ah.hQ]
            rw[ah.bk
              C.ak.aE]
            simp[ah.di,ah.bt.eo,
              C.eD]
          rwa[←û]) B9
    exact il u W H z data
      (aa.fU (d+1)) um (by norm_num)
      Õ ax D0 Br (by positivity) dc sS
  apply kj s ù fw C ἴ ο
    (by norm_num) W u9 kz H.uB H.mI
    H.bx.aE H.Ä.aE H.r0 H.rZ
    (show(bd:ℝ≥0)⁻¹ +(bd:ℝ≥0)⁻¹ =
      (bd:ℝ≥0)⁻¹ +(bd:ℝ≥0)⁻¹ from rfl)
    dy
    (ld s.aV C W H kz)
    ú (l2 s.aV Ý)
  intro ᾌ
  obtain ⟨t,zG,KM,KN⟩:=
    gq
      s.aV C ο (by norm_num) H.bx.aE
      H.Ä.aE (Μ:=(1/8:ℝ))
      (sigma:=(1/8192:ℝ)) (delta:=(1/8192:ℝ))
      (bm:=(1/512:ℝ))
      (fx:=(65/64:ℝ) *
        (C.ak.ba.Η.card:ℝ)⁻¹)
      (eb:=eb) (ὓ:=ὓ)
      (aq:=aa.au (d+1))
      (r:=aa.Ἅ (d+1))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (aa.fU (d+1))
      (aa.nF (d+1))
      (by
        have gy:=aa.fU (d+1)
        have mx:=aa.nF (d+1)
        rcases mx with ⟨k,hk⟩
        omega)
      (qT (d+1)) (by positivity) jx
      (by
        norm_num at ᾌ ⊢
        simpa[u,aa.Ἅ,
          bu.ö,Ἢ,
          bF] using ᾌ)
      (rT s.aV C ο (by norm_num))
      (by simpa[u] using pl)
  exact ⟨t,by norm_num at zG ⊢; exact zG,KM,by
    simpa[bu.aG.card,
      ῒ,add_left_comm,add_assoc] using KN⟩
def fo:ℝ:=
 4096*(aa.ῂ:ℝ)
lemma iL
  (d Ι Ë:ℕ)
  (Ñ:Ι≤ar.ax (d+1)
   (aa.au (d+1)))
  (pd:Ë≤8*aa.au (d+1)) :
  log (aa.cv (d+1) Ι Ë:ℝ) ≤
   2048*(aa.ῂ:ℝ) *
    ((d+1:ℕ):ℝ)^11:=by
 have ei:=aa.jX
  (d+1) Ι Ë Ñ pd
 have dc:((d+1+1:ℕ):ℝ)≤2*((d+1:ℕ):ℝ):=by
  push_cast
  nlinarith
 have hpow:((d+1+1:ℕ):ℝ)^11 ≤
   (2:ℝ)^11*((d+1:ℕ):ℝ)^11:=by
  calc
   _ ≤
     (2*((d+1:ℕ):ℝ))^11:=
    ἤ (by positivity) dc 11
   _=(2:ℝ)^11*((d+1:ℕ):ℝ)^11:=by rw[Ἀ]
 calc
  _ ≤
    (aa.ῂ:ℝ) *
     ((d+1+1:ℕ):ℝ)^11:=by simpa using ei
  _≤(aa.ῂ:ℝ) *
    ((2:ℝ)^11*((d+1:ℕ):ℝ)^11):=by gcongr
  _=2048*(aa.ῂ:ℝ) *
    ((d+1:ℕ):ℝ)^11:=by norm_num; ring
lemma f3
  (d Ι:ℕ)
  (Ñ:Ι≤ar.ax (d+1)
   (aa.au (d+1))) :
  log (aa.ὕ Ι
   (ar.bn (d+1) (aa.au (d+1)))
   (ar.bd (d+1) (aa.au (d+1))):ℝ) ≤
   2048*(aa.ῂ:ℝ) *
    ((d+1:ℕ):ℝ)^11:=by
 let Ë:=aa.au (d+1)+1
 have pd:Ë≤8*aa.au (d+1):=by
  dsimp[Ë]
  have gy:=aa.ἢ (d+1)
  omega
 have KO:=iL d Ι Ë Ñ pd
 have uG:(0:ℝ)<aa.ὕ Ι
   (ar.bn (d+1) (aa.au (d+1)))
   (ar.bd (d+1) (aa.au (d+1))):=by
  exact_mod_cast Ὑ
   (aa.ck
    (ar.mc (aa.ἢ (d+1))))
   (aa.ck
    (ar.md (aa.ἢ (d+1))))
 have hle:aa.ὕ Ι
   (ar.bn (d+1) (aa.au (d+1)))
   (ar.bd (d+1) (aa.au (d+1))) ≤
   aa.cv (d+1) Ι Ë:=by
  unfold aa.cv
  rw[show
   aa.ὕ Ι
     (ar.bn (d+1) (aa.au (d+1)))
     (ar.bd (d+1) (aa.au (d+1))) *
     aa.ᾄ Ι *
     (3*aa.ἀ Ι Ë
      (aa.cd (d+1)
       (ar.ax (d+1)
        (aa.au (d+1)))))^Ι *
     aa.ᾖ (d+1) =
    aa.ὕ Ι
     (ar.bn (d+1) (aa.au (d+1)))
     (ar.bd (d+1) (aa.au (d+1))) *
     (aa.ᾄ Ι *
     (3*aa.ἀ Ι Ë
      (aa.cd (d+1)
       (ar.ax (d+1)
        (aa.au (d+1)))))^Ι *
     aa.ᾖ (d+1)) by ring]
  apply Q4
  have Ᾱ:0<aa.ᾄ Ι:=by
   unfold aa.ᾄ
    aa.ἣ
   positivity
  have Ὦ:0 <
    (3*aa.ἀ Ι Ë
     (aa.cd (d+1)
      (ar.ax (d+1)
       (aa.au (d+1)))))^Ι:=by
   unfold aa.ἀ aa.cd
   positivity
  have ό:0<aa.ᾖ (d+1):=by
   unfold aa.ᾖ aa.ᾀ
   have hq:0<aa.ã (d+1):=by
    unfold aa.ã
    exact aa.Ὴ
     (aa.Ἧ (d+1))
   positivity
  exact Ὑ (Ὑ Ᾱ Ὦ) ό
 exact(ᾆ uG (by exact_mod_cast hle)).trans KO
lemma gE
  (d Ι:ℕ)
  (Ñ:Ι≤ar.ax (d+1)
   (aa.au (d+1))) :
  log (aa.ἣ Ι
   (ar.bn (d+1) (aa.au (d+1))):ℝ) ≤
   2048*(aa.ῂ:ℝ) *
    ((d+1:ℕ):ℝ)^11:=by
 have vc:=f3 d Ι Ñ
 have IW:(0:ℝ)<aa.ἣ Ι
   (ar.bn (d+1) (aa.au (d+1))):=by
  exact_mod_cast aa.ck
   (ar.mc (aa.ἢ (d+1)))
 have hle:aa.ἣ Ι
   (ar.bn (d+1) (aa.au (d+1))) ≤
   aa.ὕ Ι
    (ar.bn (d+1) (aa.au (d+1)))
    (ar.bd (d+1) (aa.au (d+1))):=by
  unfold aa.ὕ
  apply Q4
  exact aa.ck
   (ar.md (aa.ἢ (d+1)))
 exact(ᾆ IW (by exact_mod_cast hle)).trans vc
lemma sT :
    ∃ K:ℝ,0<K∧bu.jZ K:=by
  refine ⟨fo, ?_, ?_⟩
  · unfold fo
    unfold aa.ῂ
      aa.Ü
      aa.eW
    positivity
  · intro N A ξ d hd
    let e:ℕ:=d+1
    let aq:ℕ:=aa.au e
    let p:ℕ:=aa.dt e
    refine ⟨aq,p, ?_, ?_⟩
    · dsimp[p]
      exact aa.ml e
    · intro n hn s Ý Ñ
      let ax:ℕ:=ar.ax e aq
      let bn:ℕ:=ar.bn e aq
      let bd:ℕ:=ar.bd e aq
      let Ἶ:ℝ:=
        2048*(aa.ῂ:ℝ) *
          ((d+1:ℕ):ℝ)^11
      have ô:0<aq:=by
        dsimp[aq]
        exact aa.ἢ e
      have ὺ:s.Ι≤ax:=by
        dsimp[ax,e,aq]
        unfold ar.ax
        have Kn:n≤1024*(d+1+1):=by omega
        exact Sj Ñ (QQ _ Kn)
      have ù:0<bn:=by
        dsimp[bn]
        exact ar.mc ô
      have fw:0<bd:=by
        dsimp[bd]
        exact ar.md ô
      have IX:1/(2:ℝ)^e≤ s.Ξ:=by
        calc
          1/(2:ℝ)^e≤1/(2:ℝ)^d:=by
            dsimp[e]
            rw[ᾬ]
            have hpow:(0:ℝ)<(2:ℝ)^d:=by positivity
            field_simp
            nlinarith
          _≤ s.Ξ:=Ý
      have ἴ:gj s.aV bn bd (1/512:ℝ)
          (fo*((d+1:ℕ):ℝ)^11):=by
        refine
          { Be:=s.ᾒ
            iK:=s.iK
            yB:= ?_
            vt:= ?_
            tk:= ?_
            tl:= ?_ }
        · dsimp[bn]
          exact ar.tI ô ὺ
        · dsimp[bn]
          exact ar.wd ô ὺ IX
        · have ᾋ :
              (0:ℝ) <
                (Ἇ s.aV.Θ.ba bn:ℕ):=by
            unfold Ἇ
            positivity
          apply jk s.aV s.ᾒ ᾋ
          have ei:=gE d s.Ι ὺ
          apply ei.trans
          unfold fo
          gcongr
          norm_num
        · have ᾋ :
              (0:ℝ) <
                (Ἄ s.aV.Θ.ba bn bd:ℕ):=by
            unfold Ἄ Ἇ
            positivity
          apply jk s.aV s.ᾒ ᾋ
          have ei:=f3 d s.Ι ὺ
          apply ei.trans
          unfold fo
          gcongr
          norm_num
      have xL:((bd:ℝ≥0)⁻¹)≤1:=by
        apply(inv_le_one₀ (by exact_mod_cast fw)).2
        exact_mod_cast(show 1≤bd by omega)
      let C:ᾗ s.aV.Θ.ba bn bd:=
        Classical.choice (rR s.aV.Θ.ba
          bn bd ù fw xL)
      have yr :
          Ἶ+Ἶ =
            fo*((d+1:ℕ):ℝ)^11:=by
        dsimp[Ἶ,fo]
        ring
      have Bs :
          gj s.aV bn bd (1/512:ℝ)
            (Ἶ+Ἶ):=by
        rw[yr]
        exact ἴ
      rw[←yr]
      let P:bu.dB s (1/512:ℝ)
          (Ἶ+Ἶ) aq:=
        bF
          (aq:=aq) s ù fw C Bs
      refine ⟨P, ?_⟩
      intro ο
      have Bt :
          exp (-Ἶ)*(s.aV.card:ℝ) ≤
            ((Ἇ s.aV.Θ.ba bn:ℕ):ℝ)⁻¹ *
              (s.aV.Θ.ba.Η.card:ℝ):=by
        have ᾋ :
            (0:ℝ) <
              (Ἇ s.aV.Θ.ba bn:ℕ):=by
          unfold Ἇ
          positivity
        apply jk s.aV s.ᾒ ᾋ
        simpa[Ἶ,Ἇ,
          aa.ἣ,bn,e,aq,
          bu.aG.Ι,
          ah.aA.Ι,
          br.aY.Ι] using
          (gE d s.Ι ὺ)
      have jx :
          exp (-Ἶ)*(s.card:ℝ)≤C.ak.Η.card:=by
        have ᾋ :
            (0:ℝ) <
              (Ἇ s.aV.Θ.ba bn:ℕ):=by
          unfold Ἇ
          positivity
        have GK :
            (s.aV.Θ.ba.Η.card:ℝ) ≤
              (Ἇ s.aV.Θ.ba bn:ℝ) *
                (C.ak.Η.card:ℝ):=by
          exact_mod_cast C.mE
        simpa[bu.aG.card] using
          mm s.aV ᾋ Bt GK
      let:NeZero (Â N):=⟨by simp[Â]⟩
      have A4:Odd (Â N):=by
        exact ⟨N,by simp[Â,ΐ]⟩
      let W:aj (ZMod (Â N)):=
        aO.hY (Â N) A4 C.aB.ba
      have u9:W.a1:=by
        dsimp[W]
        exact qR A4 C.aB.ba
          C.fe
      have kz :
          W.Η=aO.Û C.aB.Η:=by
        rw[C.n5]
        dsimp[W]
        exact
          (aO.jQ
            A4 C.aB.ba).symm
      have wE:W.Η.card=C.aB.Η.card:=by
        dsimp[W]
        rw[aO.p7]
        exact è Finset.card C.n5.symm
      have yE:W.Ι=s.Ι:=by
        dsimp[W]
        rw[aO.u8,C.p5]
        rfl
      let H:Ἓ W:=
        Classical.choice (rS W)
      have dy :
          (bd:ℝ≥0)⁻¹ +(bd:ℝ≥0)⁻¹ ≤
            1/(100*(max C.ak.ba.Ι 1:ℕ):ℝ≥0):=by
        rw[C.Ì]
        simpa[bd,e,aq,
          bu.aG.Ι,
          ah.aA.Ι,
          br.aY.Ι] using
          (ar.rb ô ὺ)
      have ú :
          2*(((Ἢ s.aV C.ak C.aB ο).card:ℝ)⁻¹ *
              (200*((max C.ak.ba.Ι 1:ℕ):ℝ) *
                (((bd:ℝ≥0)⁻¹ +(bd:ℝ≥0)⁻¹ :ℝ≥0):ℝ))) +
            (C.ak.ba.Η.card:ℝ)⁻¹ *
              (200*((max C.ak.ba.Ι 1:ℕ):ℝ) *
                (((bd:ℝ≥0)⁻¹ +(bd:ℝ≥0)⁻¹ :ℝ≥0):ℝ)) ≤
            (1/8:ℝ)/8*(C.ak.ba.Η.card:ℝ)⁻¹:=by
        simpa[bd,e,aq] using
          (uJ s.aV C ο Ý ὺ ô)
      let Ë:ℕ:=aq+1
      have pd:Ë≤8*aa.au e:=by
        dsimp[Ë,aq]
        have gy:=aa.ἢ e
        omega
      have FF :
          0<aa.cv e ax Ë:=by
        have KP:0<ar.bn e
            (aa.au e):=
          ar.mc (aa.ἢ e)
        have KQ:0<ar.bd e
            (aa.au e):=
          ar.md (aa.ἢ e)
        have hq:0<aa.ã e:=by
          unfold aa.ã
          exact aa.Ὴ
            (aa.Ἧ e)
        have vc:0<aa.ὕ ax
            (ar.bn e (aa.au e))
            (ar.bd e (aa.au e)):=by
          unfold aa.ὕ
          exact Ὑ
            (aa.ck KP)
            (aa.ck KQ)
        have Ᾱ :
            0<aa.ᾄ ax:=by
          unfold aa.ᾄ
            aa.ἣ
          positivity
        have Ὦ :
            0<(3*aa.ἀ ax Ë
              (aa.cd e
                (ar.ax e
                  (aa.au e))))^ax:=by
          unfold aa.ἀ
            aa.cd
          positivity
        have ό:0<aa.ᾖ e:=by
          unfold aa.ᾖ
            aa.ᾀ
          positivity
        unfold aa.cv
        exact Ὑ (Ὑ (Ὑ vc Ᾱ) Ὦ) ό
      have Bu :
          exp (-Ἶ) *
              (aa.cv e ax Ë:ℝ) ≤
            1:=by
        apply oy FF
        simpa[Ἶ,e] using
          (iL d ax Ë (SF) pd)
      have FH :
          (Ἄ s.aV.Θ.ba bn bd *
              ὢ W) *
              (3*ὔ e ax)^ax *
              ᾃ e ax ≤
            aa.cv e ax Ë:=by
        have zH :
            s.aV.Θ.ba.Ι≤ax:=by
          simpa[bu.aG.Ι,
            ah.aA.Ι,
            br.aY.Ι] using ὺ
        have xh {m:ℕ} (hm:0< m) :
            Ἇ s.aV.Θ.ba m ≤
              aa.ἣ ax m:=by
          unfold Ἇ aa.ἣ
          exact Ra
            (QR (by omega) zH)
            (QR (by norm_num) zH)
        have vc :
            Ἄ s.aV.Θ.ba bn bd ≤
              aa.ὕ ax bn bd:=by
          unfold Ἄ aa.ὕ
          exact Ra (xh ù) (xh fw)
        have Ἴ:max s.Ι 1≤ max ax 1:=
          Sn 1 ὺ
        have ri (c:ℕ) (hc:0<c) :
            (3*(c*max s.Ι 1))^s.Ι*4^s.Ι ≤
              aa.ἣ ax
                (c*max ax 1):=by
          unfold aa.ἣ
          have dc :
              3*(c*max s.Ι 1)≤3*(c*max ax 1):=by
            gcongr
          have xE:0<3*(c*max ax 1):=by positivity
          have jx :
              (3*(c*max s.Ι 1))^s.Ι ≤
                (3*(c*max ax 1))^ax:=by
            calc
              (3*(c*max s.Ι 1))^s.Ι ≤
                  (3*(c*max ax 1))^s.Ι:=
                R4 dc _
              _≤(3*(c*max ax 1))^ax:=
                QR xE ὺ
          exact Ra jx
            (QR (by norm_num) ὺ)
        have Ᾱ :
            ὢ W ≤
              aa.ᾄ ax:=by
          unfold ὢ
            aa.ᾄ
          rw[yE]
          exact Ra
            (Ra (ri 1600 (by norm_num))
              (ri 200 (by norm_num)))
            (ri 200 (by norm_num))
        have Ὦ :
            (3*ὔ e ax)^ax =
              (3*aa.ἀ ax Ë
                (aa.cd e
                  (ar.ax e
                    (aa.au e))))^ax:=by
          unfold ὔ ὖ
            aa.ἀ
            aa.cd
            aa.av
          dsimp[ax,aq,Ë]
        have ό :
            ᾃ e ax =
              aa.ᾖ e:=by
          unfold ᾃ jH
            aa.ᾖ
          rw[aa.pc]
        unfold aa.cv
        rw[←Ὦ, ←ό]
        dsimp[bn,bd,aq]
        exact Ra
          (Ra (Ra vc Ᾱ) (SF))
          (SF)
      have sS :
          exp (-Ἶ) *
              ((Ἄ s.aV.Θ.ba bn bd *
                ὢ W:ℕ):ℝ) *
              (((3*ὔ e ax)^ax:ℕ):ℝ) *
                (ᾃ e ax:ℝ)≤1:=by
        calc
          exp (-Ἶ) *
              ((Ἄ s.aV.Θ.ba bn bd *
                ὢ W:ℕ):ℝ) *
              (((3*ὔ e ax)^ax:ℕ):ℝ) *
                (ᾃ e ax:ℝ) ≤
              exp (-Ἶ) *
                (aa.cv e ax Ë:ℝ):=by
                  have yF :
                      ((Ἄ s.aV.Θ.ba bn bd *
                        ὢ W) *
                        (3*ὔ e ax)^ax *
                        ᾃ e ax:ℝ) ≤
                        (aa.cv
                          e ax Ë:ℝ):=by
                    exact_mod_cast FH
                  push_cast at yF ⊢
                  calc
                    exp (-Ἶ) *
                        ((Ἄ s.aV.Θ.ba bn bd:ℝ) *
                          ὢ W) *
                        (3*ὔ e ax:ℝ)^ax *
                          ᾃ e ax =
                        exp (-Ἶ) *
                          (((Ἄ s.aV.Θ.ba bn bd:ℝ) *
                            ὢ W) *
                            (3*ὔ e ax:ℝ)^ax *
                              ᾃ e ax):=by ring
                    _≤exp (-Ἶ) *
                        (aa.cv e ax Ë:ℝ):=
                      Å yF (ᾰ _).le
          _≤1:=Bu
      simpa[p,e] using
        (iE
          (d:=d) (ax:=ax) (bn:=bn) (bd:=bd)
          s ù fw C Bs jx ο Ý W u9
          kz wE yE H ὺ dy ú sS)
end IT
end
end ay.uH
end
section
open Filter
open scoped Topology
namespace ay
lemma lf
  {K:ℝ} (æ:0<K) (ὧ:bu.jZ K)
  (C:ℝ) :
  (λ N:ℕ=>(ü N:ℝ))=O[atTop]
   (λ N:ℕ=>(N:ℝ)/(log (N:ℝ))^C):=by
 obtain ⟨K',Ὠ,qG⟩:=
  i2
   ⟨8+2050*(2:ℝ)^12*K,
    bu.lb æ ὧ⟩
 exact m4 qG C
lemma l3
  (ὧ: ∃ K:ℝ,0<K∧bu.jZ K)
  (C:ℝ) (_hC:0<C) :
  (λ N:ℕ=>(ü N:ℝ))=O[atTop]
   (λ N:ℕ=>(N:ℝ)/(log (N:ℝ))^C):=by
 obtain ⟨K,æ,MD⟩:=ὧ
 exact lf æ MD C
lemma FI (C:ℝ) (Ã:0<C) :
  (λ N:ℕ=>(ü N:ℝ))=O[atTop]
   (λ N:ℕ=>(N:ℝ)/(log (N:ℝ))^C):=
       l3
  uH.sT C Ã
end ay
end
section
open Filter Real Asymptotics
namespace Erdos142KM
lemma z0 (N:ℕ):Erdos142.r 3 N=ay.ü N:=
 w1.r4 N
lemma logSquare : ∀ᶠ N:ℕ in atTop,
  (Erdos142.r 3 N:ℝ)≤(N:ℝ)/log (N:ℝ)^((1:ℝ)+1):=by
 obtain ⟨K,æ⟩:=(ay.FI 3 (by norm_num)).bound
 have ei:Tendsto (λ N:ℕ=>log (N:ℝ)) atTop atTop:=
  tendsto_log_atTop.comp Sa
 filter_upwards[æ,ei.eventually (eventually_ge_atTop (max K 1))] with N î hL
 have Pu:(1:ℝ)≤log (N:ℝ):=Sj (le_max_right _ _) hL
 have Pv:K≤log (N:ℝ):=Sj (Tu _ _) hL
 have ME:0<log (N:ℝ):=SI U1 Pu
 have PX:(0:ℝ)≤N:=Q5 N
 have hq:0≤(N:ℝ)/log (N:ℝ)^(3:ℝ):=by positivity
 rw[RA (Q5 _),RA hq] at î
 rw[z0]
 have e3:log (N:ℝ)^(3:ℝ)=log (N:ℝ)^((1:ℝ)+1)*log (N:ℝ):=by
  rw[←Real.rpow_add_one ME.ne']
  norm_num
 calc (ay.ü N:ℝ)≤K*((N:ℝ)/log (N:ℝ)^(3:ℝ)):=î
  _≤log (N:ℝ)*((N:ℝ)/log (N:ℝ)^(3:ℝ)):=
    ἂ Pv hq
  _=(N:ℝ)/log (N:ℝ)^((1:ℝ)+1):=by
    rw[e3]
    have:0<log (N:ℝ)^((1:ℝ)+1):=by positivity
    field_simp
end Erdos142KM
end
open Erdos142 Filter Real
open OMA.R_Erdos142_erdos_142_variants_lower_R3
namespace WindowEstimate
lemma reciprocal_window_le {k n : ℕ} (hk : 1 < k) (S : Finset ℕ)
    (hw : ∀ x ∈ S, ∃ j ∈ Finset.Ico n (2*n), 4*4^j < x ∧ x ≤ 5*4^j)
    (hf : ¬ ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i*d ∈ S) :
    ∑ x ∈ S, (x : ℝ)⁻¹ ≤ n * ((r k (4^n) : ℝ) / (4:ℝ)^n) / 4 := by
  let B (j : ℕ) := (Finset.Icc 1 (4^j)).filter (λ b => 4*4^j+b ∈ S)
  have sub j : B j ⊆ Finset.Icc 1 (4^j) := Finset.filter_subset _ _
  let block j := (B j).map (addLeftEmbedding (4*4^j))
  have cover : S ⊆ (Finset.Ico n (2*n)).biUnion block := by
    intro x hx
    obtain ⟨j, hj, hl, hu⟩ := hw x hx
    refine Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_map.mpr ⟨x-4*4^j, ?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by simpa [Nat.add_sub_of_le hl.le] using hx⟩
    · change 4*4^j+(x-4*4^j) = x
      omega
  have size j : (B j).card ≤ r k (4^j) := by
    apply card_le_r (sub j) ((apFree_iff hk).mpr ?_)
    rintro ⟨a, d, hd, h⟩
    exact hf ⟨4*4^j+a, d, hd, λ i hi => by simpa [Nat.add_assoc] using (Finset.mem_filter.mp (h i hi)).2⟩
  calc
    _ ≤ ∑ x ∈ (Finset.Ico n (2*n)).biUnion block, (x : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg cover (by intros; positivity)
    _ = _ := Finset.sum_biUnion (shiftBlocks_pairwiseDisjoint _ B sub)
    _ ≤ ∑ _j ∈ Finset.Ico n (2*n), ((r k (4^n) : ℝ) / (4:ℝ)^n) / 4 := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        _ ≤ ∑ _x ∈ block j, (4 * (4:ℝ)^j)⁻¹ := by
          apply Finset.sum_le_sum
          intro x hx
          apply inv_anti₀ (by positivity)
          exact_mod_cast (mem_shiftBlock_bounds (sub j) hx).1.le
        _ = (B j).card / (4:ℝ)^j / 4 := by simp [block, div_eq_mul_inv]; ring
        _ ≤ (r k (4^j) : ℝ) / (4:ℝ)^j / 4 := by gcongr; exact_mod_cast size j
        _ ≤ _ := div_le_div_of_nonneg_right (blockDensity_antitone hk (Finset.mem_Ico.mp hj).1) (by norm_num)
    _ = _ := by simp [show 2 * n - n = n by omega, mul_div_assoc]
end WindowEstimate
open Erdos142 Filter Real WindowEstimate
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R3.H1 := by
  intro ε hε
  have L : 0 < log 4 := log_pos (by norm_num)
  have tend : Tendsto (λ n : ℕ => (4:ℕ)^n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  filter_upwards [tend.eventually Erdos142KM.logSquare,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (1/(4*ε*(log 4)^2))),
    eventually_gt_atTop (0:ℕ)] with n î hn hn0 S hw hf
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn0
  have bound := reciprocal_window_le (by decide : 1 < 3) S hw hf
  apply bound.trans
  push_cast at î
  rw [Real.log_pow] at î
  norm_num at î
  have hp : 0 < (4:ℝ)^n := by positivity
  calc
    _ ≤ n * (((4:ℝ)^n / ((n:ℝ)*log 4)^2) / (4:ℝ)^n) / 4 := by gcongr
    _ = 1/(4*(n:ℝ)*(log 4)^2) := by field_simp
    _ ≤ ε := by
      apply (div_le_iff₀ (by positivity)).mpr
      have hh := (div_le_iff₀ (by positivity : 0 < 4*ε*(log 4)^2)).mp hn
      linarith only [show (n:ℝ) * (4 * ε * (log 4)^2) = ε * (4 * n * (log 4)^2) by ring, hh]
