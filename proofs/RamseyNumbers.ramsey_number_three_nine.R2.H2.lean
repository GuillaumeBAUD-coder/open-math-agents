import OMAReductions.R_RamseyNumbers_ramsey_number_three_nine_R2
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Dist
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
A triangle-free graph on twenty-one vertices with 51 edges and no independent seven-set
has a degree-five vertex whose exterior on fifteen vertices has at most 26 edges.
We enumerate all eight possible exteriors and certify the five contact rows by weighted
independent-set inequalities. The compatible five-tuples produce the four codes in R2.H2.

The sparse-graph recursion and graph relabelings build on Deldor14 (#6274), the smaller
density bounds on dasante78 (#12460), and the neighborhood counts on physbuzz (#9042).
The four target codes are those of the parent reduction (#13293), based on the Ramsey
graphs catalogued by Brendan McKay. The order-fifteen classification and all extension
and relabeling certificates are verified below by Lean.
-/

namespace RamseyFourProof
/- The 27-vertex edge bound forces regularity in a 35-vertex Ramsey graph. -/
open SimpleGraph RamseyNumbers
namespace OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1

-- With no triangle and no independent k-set, each vertex has fewer than k neighbours.
lemma degree_lt {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hc : Gᶜ.CliqueFree k) (v : Fin n) : G.degree v < k := by
  by_contra! h
  apply hc.mono h (G.neighborFinset v)
  refine ⟨?_, rfl⟩
  rw [G.coe_neighborFinset, G.isClique_compl]
  exact G.isIndepSet_neighborSet_of_triangleFree hG v

-- An independent k-set among non-neighbours extends to an independent (k+1)-set.
lemma nonneighbors_lt {n k m : ℕ} (hr : IsGraphRamsey m 3 k)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (hc : Gᶜ.CliqueFree (k + 1)) (v : Fin n) : Gᶜ.degree v < m := by
  classical
  by_contra! h
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin m) (s := Gᶜ.neighborFinset v) (by simpa using h)
  have hv (i : Fin m) : Gᶜ.Adj v (f i) :=
    (Gᶜ.mem_neighborFinset v (f i)).mp (hf ⟨i, rfl⟩)
  let H := G.comap f
  let e : H ↪g G := SimpleGraph.Embedding.comap f G
  let ec : Hᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv e
  apply hr H
  refine ⟨CliqueFree.comap e.isContained hG, ?_⟩
  intro t ht
  have hs : Gᶜ.IsNClique k (t.map f) := by
    refine ⟨?_, (Finset.card_map _).trans ht.card_eq⟩
    intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
    exact ec.map_adj_iff.mpr (ht.isClique hi hj (fun he => hxy (congrArg f he)))
  apply hc _ (hs.insert (a := v) ?_)
  intro w hw
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hw
  exact hv i
end OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1


section
namespace GlueSeed
-- Recursive independent-set encoding from merged OMA reduction
-- RamseyNumbers.ramsey_number_three_seven.R1.H2.R1.H2.R1.
def ind0 (p : Nat × Nat) : Nat × Nat := (2*p.1,p.2)
def ind1 (p : Nat × Nat) : Nat × Nat := (2*p.1+1,p.2+1)
def inds : List Nat → List (Nat × Nat)
  | [] => [(0,0)]
  | m::rows =>
    let t := inds rows
    t.map ind0 ++ (t.filter fun p => m &&& p.1 == 0).map ind1

def member : List Nat → Nat → Nat → Bool
  | [], mask, size => mask==0 && size==0
  | a::as, mask, size =>
      if mask%2=0 then member as (mask/2) size else
        decide (0< size) && (a&&&(mask/2)==0) && member as (mask/2) (size-1)

theorem member_ok {as : List Nat} {r k : Nat} (h : member as r k=true) : (r,k)∈inds as := by
  induction as generalizing r k with
  | nil =>
    simpa [member,inds] using h
  | cons a as ih =>
    simp only [member] at h
    by_cases even : r%2=0
    · rw [if_pos even] at h
      exact List.mem_append_left _ (List.mem_map.mpr ⟨_,ih h,by unfold ind0; congr 1; omega⟩)
    · simp only [if_neg even,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at h
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨ih h.2,by simpa using h.1.2⟩,by unfold ind1; congr 1 <;> omega⟩

abbrev Test := Nat × Nat

def missed : List Test → Nat → Nat
  | [], _ => 0
  | (s,w)::tests, row => (if row &&& s == 0 then w else 0) + missed tests row

/-- Integral weighted bound on unseen independent six-sets for all row sizes
in the indicated interval. Values a and b certify score(row)+b·size ≥ a. -/
def verify (adj : List Nat) (tests : List Test) (lo hi a b : Nat) : Bool :=
  tests.all (fun t => member adj t.1 6) &&
  (inds adj).all (fun v => if lo≤ v.2 ∧ v.2≤ hi then decide (a≤ missed tests v.1+b*v.2) else true)

end GlueSeed
end

section
/- The graph encoding and independent-set enumeration proof are reused from
the merged R(3,7) finite reduction, `RamseyNumbers.ramsey_number_three_seven.R1.H2.R1.H2.R1`. -/
namespace GlueSeed
open SimpleGraph Finset

def bits : List Bool → Nat
  | [] => 0
  | b::bs => 2 * bits bs + b.toNat

def encode {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] : List V → List Nat
  | [] => []
  | v::vs => bits (vs.map fun x => decide (G.Adj v x)) :: encode G vs
end GlueSeed
end

section
namespace GlueSeed

def adj (g : Fin 4) : List Nat :=
  match g.val with
  | 0 => [0x380a8,0x140a8,0x3081,0x4480,0x4190,0x8c4,0x10a8,0x2a8,0x444,0x91,0x4,0x11,0x4,0x1,0x3,0x0,0x8,0x4,0x2,0x1,0x0]
  | 1 => [0x380a8,0x100a8,0xb081,0x2480,0x4190,0x4c4,0x10a8,0x1a8,0x444,0x51,0x44,0x1,0x4,0x1,0x1,0x2,0x8,0x4,0x2,0x1,0x0]
  | 2 => [0x380a8,0xc0a8,0x3081,0x2480,0x4190,0x10c4,0x10a8,0x4a8,0x444,0x111,0x44,0x11,0x4,0x1,0x1,0x0,0x8,0x4,0x2,0x1,0x0]
  | _ => [0x380a8,0x40a8,0x7081,0x4480,0x4190,0x8c4,0x10a8,0x2a8,0x444,0x11,0x84,0x1,0x4,0x5,0x1,0x4,0x8,0x4,0x2,0x1,0x0]
end GlueSeed
end

section
namespace FiveIso
open SimpleGraph Finset

/-- Pull a 21-element graph back to Fin 21 and transport the verified vertex ordering. -/
theorem arbitrary_of_fin (fin : ∀ J : SimpleGraph (Fin 21), ∀ [DecidableRel J.Adj],
    J.CliqueFree 3 → Jᶜ.CliqueFree 7 → J.edgeFinset.card=51 →
    ∃ (i : Fin 4) (xs : List (Fin 21)), xs.Nodup ∧ xs.toFinset=univ ∧ GlueSeed.encode J xs=GlueSeed.adj i)
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (sz : Fintype.card V=21) (tri : G.CliqueFree 3) (ind : Gᶜ.CliqueFree 7) (ec : G.edgeFinset.card=51) :
    ∃ (i : Fin 4) (xs : List V), xs.Nodup ∧ (∀ x, x∈xs) ∧ GlueSeed.encode G xs=GlueSeed.adj i := by
  classical
  let e := (Fintype.equivFinOfCardEq sz).symm
  let J := G.comap e
  let f : J ≃g G := SimpleGraph.Iso.comap e G
  have tj := CliqueFree.comap f.toEmbedding.isContained tri
  have ij := CliqueFree.comap (SimpleGraph.Embedding.complEquiv f.toEmbedding).isContained ind
  obtain ⟨i,zs,nd,allv,h⟩ := fin J tj ij (f.card_edgeFinset_eq.trans ec)
  refine ⟨i,zs.map e,nd.map e.injective,?_,?_⟩
  · intro x
    obtain ⟨y,rfl⟩ := e.surjective x
    exact List.mem_map.mpr ⟨y,List.mem_toFinset.mp (allv ▸ mem_univ y),rfl⟩
  · suffices agree : ∀ ws : List (Fin 21), GlueSeed.encode G (ws.map e) = GlueSeed.encode J ws by
      exact (agree zs).trans h
    intro ws
    induction ws with
    | nil => rfl
    | cons a ws ih =>
      simp only [List.map_cons,GlueSeed.encode,List.map_map,ih]
      rfl

theorem encoded_fold {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) :
    (vs.foldr (fun v (pair : List V × List ℕ) =>
      (v::pair.1, ((pair.1.map fun x => decide (G.Adj v x)).foldr
        (fun b k => 2*k+b.toNat) 0)::pair.2)) ([],[])) = (vs,GlueSeed.encode G vs) := by
  have bits_eq (xs : List Bool) : xs.foldr (fun b k => 2*k+b.toNat) 0 = GlueSeed.bits xs := by
    induction xs with
    | nil => rfl
    | cons b xs ih => simp only [List.foldr_cons,GlueSeed.bits,ih]
  induction vs with
  | nil => rfl
  | cons a vs ih =>
    rw [List.foldr_cons,ih]
    simp only [bits_eq,GlueSeed.encode]

end FiveIso
end

section
/- Transfer of the four finite graph codes to the exact public Ramsey reduction. -/
namespace FiveIso
open SimpleGraph Finset

theorem public_H2_of_fin (fin : ∀ J : SimpleGraph (Fin 21), ∀ [DecidableRel J.Adj],
    J.CliqueFree 3 → Jᶜ.CliqueFree 7 → J.edgeFinset.card=51 →
    ∃ (i : Fin 4) (xs : List (Fin 21)), xs.Nodup ∧ xs.toFinset=univ ∧
      GlueSeed.encode J xs=GlueSeed.adj i) :
    OMA.R_RamseyNumbers_ramsey_number_three_nine_R2.H2 := by
  intro V _ _ G _ sz tri ind edges
  obtain ⟨i,vs,nd,allv,code⟩ := arbitrary_of_fin fin G sz tri ind edges
  refine ⟨vs,nd,allv,?_⟩
  dsimp only
  rw [encoded_fold]
  change GlueSeed.encode G vs ∈ _
  rw [code]
  fin_cases i <;> decide

end FiveIso
end

section
namespace SparseFifteen
def adj (i : Fin 8) : List Nat :=
  match i.val with
  | 0 => [3, 2, 14, 7, 24, 130, 145, 3, 2, 6, 3, 2, 2, 1, 0]
  | 1 => [3, 12, 1025, 7, 24, 130, 145, 3, 2, 6, 3, 2, 2, 1, 0]
  | 2 => [3, 24, 17, 7, 24, 130, 145, 3, 2, 6, 3, 2, 2, 1, 0]
  | 3 => [7, 24, 18, 49, 3, 128, 144, 3, 2, 6, 3, 2, 2, 1, 0]
  | 4 => [7, 24, 18, 561, 3, 128, 144, 3, 2, 6, 3, 2, 2, 1, 0]
  | 5 => [7, 24, 98, 73, 3, 128, 144, 3, 2, 6, 3, 2, 2, 1, 0]
  | 6 => [7, 24, 98, 265, 3, 128, 144, 3, 2, 6, 3, 2, 2, 1, 0]
  | _ => [7, 24, 98, 1033, 3, 128, 144, 3, 2, 6, 3, 2, 2, 1, 0]
end SparseFifteen
end

section
namespace FiveLP
def pool (i : Fin 8) : List Nat :=
  match i.val with
  | 0 => [321, 322, 518, 521, 801, 802, 833, 834, 1030, 1033, 1158, 1161, 1168, 1169, 1170, 1542, 1545, 2054, 2057, 2310, 2313, 4102, 4105, 4129, 4130, 4161, 4162, 4178, 4358, 4361, 4385, 4386, 4417, 4418, 6150, 6153, 6177, 6178, 6404, 6406, 6408, 6409, 6412, 8337, 8338, 8449, 8450, 8454, 8457, 8460, 8513, 8514, 8705, 8706, 8710, 8713, 8769, 8770, 8961, 8962, 9025, 9026, 9222, 9225, 9228, 9345, 9346, 9348, 9350, 9352, 9353, 9360, 9361, 9362, 9729, 9730, 9734, 9737, 9740, 12294, 12297, 12304, 12305, 12306, 12353, 12354, 12368, 12370, 12432, 12545, 12546, 12550, 12553, 12609, 12610, 16529, 16530, 16641, 16642, 16646, 16649, 16673, 16674, 16902, 16905, 17153, 17154, 17186, 17409, 17410, 17414, 17417, 17425, 17426, 17441, 17442, 17457, 17458, 17537, 17538, 17552, 17553, 17554, 17921, 17922, 17926, 17929, 17932, 18465, 18466, 18480, 18481, 18482, 18689, 18690, 18721, 18722]
  | 1 => [521, 582, 777, 1030, 1033, 1089, 1094, 1108, 1121, 1124, 1158, 1169, 1172, 1542, 1572, 2054, 2182, 2196, 2310, 2337, 4102, 4106, 4166, 4177, 4193, 4230, 4233, 4356, 4358, 4361, 4362, 4385, 4417, 6150, 6402, 6404, 6406, 8513, 8961, 9360, 9361, 12290, 12353, 12354, 12368, 12545, 12546, 12609, 16529, 16641, 16644, 16646, 16673, 16902, 16905, 17153, 17184, 17414, 17417, 17418, 17425, 17441, 17537, 17553, 17922, 17924, 17926, 18442, 18449, 18689]
  | 2 => [777, 778, 1030, 1033, 1046, 1169, 1170, 1542, 2310, 4102, 4118, 4129, 4145, 4177, 4180, 4358, 4362, 4385, 4417, 6150, 6196, 6401, 6404, 6406, 6436, 8209, 8214, 8273, 8276, 8337, 8338, 8449, 8457, 8458, 8513, 8961, 8969, 9222, 9225, 9233, 9238, 9345, 9361, 9738, 12294, 12305, 12310, 12353, 12356, 12369, 12545, 12609, 16401, 16433, 16436, 16529, 16641, 16646, 16649, 16673, 16902, 17153, 17161, 17414, 17417, 17425, 17444, 17537, 17553, 17921, 17922, 17926, 17930, 18449, 18465, 18468, 18481, 18689, 18721]
  | 3 => []
  | 4 => []
  | 5 => []
  | 6 => []
  | _ => []
def weights (i : Fin 8) : List ((Nat × Nat) × Nat) :=
  match i.val with
  | 0 => [((864,4),24),((865,5),4),((866,5),4),((1136,4),14),((1137,5),12),((1138,5),12),((1632,4),2),((4209,5),4),((4210,5),4),((4449,5),4),((4450,5),4),((6278,5),20),((6281,5),20),((6284,5),4),((6289,5),4),((6290,5),4),((6406,5),20),((6409,5),20),((6412,5),4),((9025,5),4),((9026,5),4),((9350,5),7),((9353,5),5),((9356,5),18),((9361,5),1),((9362,5),1),((9737,5),2),((9740,5),6),((9792,4),1),((9793,5),19),((9794,5),19),((12369,5),28),((12370,5),28),((12428,5),4),((12556,5),24),((17164,5),22),((17542,5),2),((17545,5),4),((17548,5),6),((17926,5),22),((17929,5),20),((17932,5),8),((18481,5),24),((18482,5),24),((18566,5),6),((18569,5),2),((18572,5),14),((18577,5),6),((18578,5),2),((18700,5),6)]
  | 1 => [((838,5),29),((865,5),880),((868,5),410),((1137,5),320),((1140,5),301),((1606,5),1623),((1633,5),13),((1636,5),75),((4209,5),313),((4212,5),1230),((4422,5),435),((6193,5),1202),((6196,5),393),((6278,5),1051),((6281,5),13),((6282,5),351),((6292,5),205),((6406,5),721),((6409,5),702),((6410,5),681),((6433,5),418),((6436,5),172),((8273,4),113),((8968,4),568),((8969,5),552),((8970,5),7),((9026,5),828),((9297,5),674),((9354,5),976),((9360,4),965),((9361,5),41),((9737,5),1107),((9738,5),59),((9794,5),243),((12368,4),377),((12369,5),317),((12424,4),226),((12425,5),350),((12426,5),372),((12433,5),418),((12610,5),597),((17162,5),276),((17188,5),710),((17456,4),113),((17546,5),506),((17556,5),596),((17926,5),288),((17929,5),800),((17930,5),217),((17953,5),302),((17956,5),1027),((18481,5),1006),((18484,5),726),((18566,5),315),((18568,4),485),((18569,5),508),((18580,5),175),((18694,5),75),((18698,5),939)]
  | 2 => [((865,5),69),((868,5),70),((1137,5),58),((1140,5),70),((1633,5),27),((1636,5),10),((4209,5),34),((4212,5),5),((4449,5),28),((4452,5),5),((6166,5),34),((6281,5),34),((6282,5),9),((6289,5),37),((6290,5),37),((6406,5),75),((6433,5),23),((8966,5),2),((8970,5),37),((9025,5),16),((9028,5),7),((9353,5),27),((9362,5),43),((9734,5),36),((9738,5),5),((9793,5),42),((9796,5),34),((12372,5),41),((12425,5),51),((12426,5),71),((12609,5),18),((12612,5),34),((17162,5),39),((17545,5),21),((17546,5),5),((17553,5),13),((17554,5),36),((17926,5),74),((17929,5),33),((17953,5),4),((18454,5),3),((18481,5),14),((18484,5),38),((18569,5),71),((18570,5),71),((18578,5),3),((18724,5),41)]
  | 3 => [((865,5),4),((868,5),4),((1132,5),2),((1249,5),2),((1256,5),2),((1633,5),2),((4204,5),2),((4321,5),2),((4449,5),1),((6158,5),2),((6282,5),2),((6289,5),4),((6312,5),2),((6406,5),2),((6417,5),4),((6418,5),2),((6433,5),1),((6436,5),2),((8966,5),2),((8977,5),2),((8978,5),2),((9028,5),2),((9230,5),2),((9354,5),1),((9361,5),2),((9362,5),1),((9416,5),4),((9746,5),4),((9793,5),2),((9796,5),2),((12302,5),2),((12364,5),2),((12433,5),1),((12434,5),2),((12481,5),1),((12488,5),4),((12562,5),2),((12609,5),2),((12612,5),2),((17158,5),2),((17169,5),2),((17188,5),1),((17422,5),1),((17546,5),2),((17553,5),2),((17576,5),2),((17926,5),1),((17937,5),2),((17938,5),4),((17953,5),2),((17956,5),2),((18446,5),4),((18476,5),4),((18577,5),2),((18578,5),2),((18593,5),2),((18600,5),2),((18706,5),2),((18721,5),2),((18724,5),1)]
  | 4 => [((865,5),5),((868,5),8),((1224,4),1),((1256,5),8),((1633,5),3),((4172,4),2),((4204,5),2),((4328,5),5),((6158,5),7),((6282,5),3),((6289,5),6),((6312,5),2),((6417,5),3),((6418,5),1),((6433,5),4),((8966,5),4),((8977,5),5),((8978,5),4),((9361,5),3),((9362,5),8),((9409,5),3),((9745,5),1),((9746,5),1),((9796,5),9),((12434,5),5),((12480,4),1),((12481,5),5),((12561,5),1),((12562,5),2),((12612,5),7),((17169,5),3),((17188,5),1),((17422,5),1),((17546,5),4),((17576,5),2),((17926,5),3),((17937,5),4),((17938,5),5),((17953,5),4),((18446,5),4),((18476,5),7),((18577,5),6),((18578,5),1),((18600,5),3),((18705,5),1),((18706,5),5),((18724,5),2)]
  | 5 => [((108,4),1),((865,5),2),((872,5),3),((1249,5),2),((1252,5),3),((1633,5),4),((4321,5),1),((4449,5),2),((6158,5),2),((6278,5),1),((6289,5),2),((6290,5),1),((6308,5),2),((6410,5),1),((6417,5),2),((6440,5),2),((8970,5),3),((8977,5),2),((9032,5),3),((9350,5),3),((9361,5),2),((9412,5),3),((9746,5),4),((9792,4),1),((12364,5),4),((12434,5),2),((12481,5),2),((12484,5),2),((12562,5),2),((12609,5),1),((12616,5),2),((17162,5),2),((17169,5),1),((17192,5),3),((17542,5),2),((17553,5),1),((17572,5),3),((17937,5),2),((17938,5),4),((18446,5),4),((18476,5),4),((18578,5),2),((18593,5),2),((18705,5),1),((18706,5),2),((18721,5),2)]
  | 6 => [((108,4),2),((865,5),4),((872,5),7),((1132,5),3),((1249,5),3),((1252,5),4),((1633,5),4),((2062,4),4),((4321,5),1),((4449,5),5),((6180,4),2),((6278,5),5),((6289,5),4),((6308,5),5),((6417,5),7),((6418,5),7),((6433,5),1),((8970,5),5),((8977,5),1),((9032,5),6),((9230,5),2),((9292,5),2),((9361,5),2),((9362,5),6),((9412,5),1),((9745,5),1),((9746,5),5),((9793,5),3),((9800,5),5),((12356,4),4),((12422,5),3),((12433,5),1),((12481,5),2),((12484,5),4),((12562,5),5),((12609,5),2),((17169,5),4),((17170,5),3),((17185,5),1),((17553,5),1),((17554,5),3),((17572,5),4),((17930,5),4),((17937,5),4),((17938,5),3),((17953,5),2),((17960,5),3),((18446,5),6),((18476,5),5),((18577,5),3),((18578,5),1),((18593,5),4),((18596,5),1),((18698,5),3),((18728,5),4)]
  | _ => [((778,4),1),((865,5),1),((872,5),4),((1132,5),3),((1249,5),1),((1252,5),1),((1633,5),1),((1640,5),1),((2062,4),2),((2092,4),1),((4204,5),1),((4321,5),2),((4324,5),1),((4449,5),2),((6158,5),2),((6188,5),2),((6289,5),2),((6410,5),1),((6417,5),4),((6418,5),1),((6440,5),1),((8970,5),2),((8977,5),2),((8978,5),1),((9032,5),1),((9230,5),2),((9362,5),2),((9412,5),4),((9738,5),1),((9746,5),1),((9793,5),2),((9800,5),2),((12302,5),1),((12364,5),2),((12433,5),1),((12434,5),2),((12481,5),1),((12484,5),2),((12562,5),1),((12616,5),3),((17169,5),2),((17170,5),1),((17185,5),1),((17542,5),1),((17553,5),3),((17572,5),1),((17937,5),1),((17938,5),4),((17952,4),1),((17953,5),2),((18438,4),1),((18468,4),2),((18566,5),2),((18577,5),2),((18578,5),1),((18593,5),1),((18596,5),2),((18706,5),3),((18721,5),2)]
def scale (i : Fin 8) : Nat :=
  match i.val with
  | 0 => 32
  | 1 => 2000
  | 2 => 85
  | 3 => 8
  | 4 => 10
  | 5 => 6
  | 6 => 12
  | _ => 6
def floor (i : Fin 8) : Nat :=
  match i.val with
  | 0 => 240
  | 1 => 14447
  | 2 => 650
  | 3 => 60
  | 4 => 76
  | 5 => 45
  | 6 => 88
  | _ => 46
def budget (i : Fin 8) : Nat :=
  match i.val with
  | 0 => 20
  | 1 => 20
  | 2 => 20
  | 3 => 21
  | 4 => 20
  | 5 => 20
  | 6 => 20
  | _ => 20
end FiveLP
end

section
namespace Generated35
def ind0 (p : Nat × Nat) : Nat × Nat := (2*p.1,p.2)
def ind1 (p : Nat × Nat) : Nat × Nat := (2*p.1+1,p.2+1)
def inds : List Nat → List (Nat × Nat)
  | [] => [(0,0)]
  | m::rows =>
    let t := inds rows
    t.map ind0 ++ (t.filter fun p => m &&& p.1 == 0).map ind1
def usable (k d : Nat) (base : List Nat) : List Nat :=
  ((inds base).filter fun p => d ≤ p.2+1 && p.2+1 < k).map Prod.fst
def countBits : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,x => (x%2) + countBits n (x/2)
end Generated35
end

section
namespace FiveLP
open Generated35
def value (w : List ((Nat × Nat) × Nat)) (x : Nat) : Nat :=
  ((w.filter fun t => x &&& t.1.1 == 0).map Prod.snd).sum
def cap (w : List ((Nat × Nat) × Nat)) : Nat := (w.map fun t => (6-t.1.2)*t.2).sum
def rowOK (i : Fin 8) (x : Nat) : Bool :=
  let b := SparseFifteen.adj i
  let total := countBits b.length x * scale i + value (weights i) x
  decide (floor i ≤ total ∧
    (4*floor i + total ≤ (budget i)*(scale i) + cap (weights i) → x∈pool i))
def witnesses (i : Fin 8) := (weights i).all (fun t => decide (t.1∈inds (SparseFifteen.adj i)))
def rowsOK (i : Fin 8) := (usable 7 3 (SparseFifteen.adj i)).all (rowOK i)
end FiveLP
end

section
/- The 17-vertex extremal Ramsey edge bound e(3,6;17) ≥ 40.

The Ramsey bounds, rooted-graph generation, and the 13- and 12-vertex
classification certificates are adapted from merged OMA proof #12460.
The final 14 integer-weight certificates treat the two possible minimum degrees. -/
namespace OMA.Ramsey37Density

open RamseyNumbers SimpleGraph Finset
open OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1 (degree_lt nonneighbors_lt)

lemma three_works : IsGraphRamsey 3 3 2 := by
  classical
  rintro G ⟨hG, hc⟩
  apply hG Finset.univ
  refine ⟨?_, by simp⟩
  intro u _ v _ hne
  by_contra h
  apply hc {u, v}
  refine ⟨?_, Finset.card_pair hne⟩
  intro a ha b hb hab
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  refine ⟨hab, ?_⟩
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (hab rfl).elim
  · exact h
  · exact fun h' => h h'.symm
  · exact (hab rfl).elim

lemma six_works : IsGraphRamsey 6 3 3 := by
  classical
  rintro G ⟨hG, hc⟩
  have hd := degree_lt G hG hc 0
  have hdc := degree_lt Gᶜ hc (by simpa using hG : Gᶜᶜ.CliqueFree 3) 0
  rw [G.degree_compl, Fintype.card_fin] at hdc
  omega

lemma nine_works : IsGraphRamsey 9 3 4 := by
  classical
  rintro G ⟨hG, hc⟩
  have hdegree (v : Fin 9) : G.degree v = 3 := by
    have hd := degree_lt G hG hc v
    have hdc := nonneighbors_lt six_works G hG hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    omega
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp [hdegree] at hsum
  omega

lemma fourteen_works : IsGraphRamsey 14 3 5 := by
  classical
  rintro G ⟨hG, hc⟩
  have hd := degree_lt G hG hc 0
  have hdc := nonneighbors_lt nine_works G hG hc 0
  rw [G.degree_compl, Fintype.card_fin] at hdc
  omega

end OMA.Ramsey37Density

section RamseyFiniteSection
open SimpleGraph
namespace OMA.RamseyFinite

def bits : List Bool → Nat
  | [] => 0
  | b::bs => 2 * bits bs + b.toNat

theorem bits_lt (b : List Bool) : bits b < 2 ^ b.length := by
  induction b with
  | nil => decide
  | cons a l ih => cases a <;> simp [bits, pow_succ] <;> omega

theorem bits_append (a b : List Bool) : bits (a ++ b) = bits a + 2 ^ a.length * bits b := by
  induction a with
  | nil => simp [bits]
  | cons c a ih => simp [bits, ih, pow_succ]; ring

theorem bits_replicate_false (n : Nat) : bits (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, bits, ih]

theorem bits_replicate_true (n : Nat) : bits (List.replicate n true) + 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, bits, pow_succ]; omega

def encode {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] : List V → List Nat
  | [] => []
  | v::vs => bits (vs.map fun x => decide (G.Adj v x)) :: encode G vs

def shifted : List Nat → List Nat
  | [] => []
  | s::ss => 2 ^ ss.length * s :: shifted ss

def attach (blocks base : List Nat) : List Nat :=
  (2 ^ blocks.length - 1) :: (shifted blocks ++ base)

theorem contacts {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (front base : List V) (hi : ∀ x ∈ front, ∀ y ∈ front, ¬ G.Adj x y) :
    encode G (front ++ base) =
      shifted (front.map fun x => bits (base.map fun y => decide (G.Adj x y))) ++ encode G base := by
  induction front with
  | nil => rfl
  | cons a as ih =>
    have nh (x) (hx : x∈as) := hi a (by simp) x (by simp [hx])
    have nils : as.map (fun x => decide (G.Adj a x)) = List.replicate as.length false := by
      apply List.eq_replicate_iff.mpr
      exact ⟨by simp, fun x hx => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx; simp [nh b hb]⟩
    simp [encode, shifted, bits_append, nils, bits_replicate_false,
      ih (fun x hx y hy => hi x (by simp [hx]) y (by simp [hy]))]

theorem root_encoding {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (front base : List V) (hfront : ∀ x∈front, G.Adj r x)
    (hbase : ∀ x∈base, ¬ G.Adj r x) (ht : G.CliqueFree 3) :
    encode G (r::front++base) = attach
      (front.map fun x => bits (base.map fun y => decide (G.Adj x y))) (encode G base) := by
  have hf : front.map (fun x => decide (G.Adj r x)) = List.replicate front.length true := by
    apply List.eq_replicate_iff.mpr
    exact ⟨by simp, fun x hx => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx; simp [hfront b hb]⟩
  have hb : base.map (fun x => decide (G.Adj r x)) = List.replicate base.length false := by
    apply List.eq_replicate_iff.mpr
    exact ⟨by simp, fun x hx => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx; simp [hbase b hb]⟩
  have hi (x) (hx : x ∈ front) (y) (hy : y ∈ front) (h : G.Adj x y) : False :=
    G.isIndepSet_neighborSet_of_triangleFree ht r (hfront x hx) (hfront y hy) h.ne h
  simp [encode, attach, bits_append, hf, hb, bits_replicate_false, contacts G front base hi]
  have := bits_replicate_true front.length
  omega

def mark {V : Type*} [DecidableEq V] (vs : List V) (s : Finset V) : Nat :=
  bits (vs.map fun x => decide (x ∈ s))

theorem bit_form (b : Bool) (n : Nat) : Nat.bit b n = 2 * n + b.toNat := by
  cases b <;> simp [Nat.bit, Nat.two_mul]

theorem and_mask {V : Type*} (vs : List V) (f g : V → Bool) :
    bits (vs.map f) &&& bits (vs.map g) = 0 ↔ ∀ x ∈ vs, f x = true → g x = false := by
  induction vs with
  | nil => simp [bits]
  | cons a l ih =>
    simp only [List.map_cons, bits, ← bit_form, Nat.land_bit, List.forall_mem_cons]
    rw [bit_form]
    cases f a <;> cases g a <;> simp [ih]

def ind0 (p : Nat × Nat) : Nat × Nat := (2*p.1,p.2)
def ind1 (p : Nat × Nat) : Nat × Nat := (2*p.1+1,p.2+1)

def inds : List Nat → List (Nat × Nat)
  | [] => [(0,0)]
  | m::rows =>
    let t := inds rows
    t.map ind0 ++ (t.filter fun p => m &&& p.1 == 0).map ind1

theorem mark_congr {V : Type*} [DecidableEq V] (vs : List V) (s t : Finset V)
    (h : ∀ x∈vs, x∈s ↔ x∈t) : mark vs s = mark vs t := by
  unfold mark
  congr 1
  exact List.map_congr_left (fun x hx => by simp only [h x hx])

theorem inds_sound {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (vs : List V) (hn : vs.Nodup) {p : Nat × Nat} (hp : p ∈ inds (encode G vs)) :
    ∃ S : Finset V, S ⊆ vs.toFinset ∧ Gᶜ.IsClique (S : Set V) ∧ p = (mark vs S,S.card) := by
  induction vs generalizing p with
  | nil =>
    simp [encode,inds] at hp
    exact ⟨∅,by simp,by simp,by simp [hp,mark,bits]⟩
  | cons a l ih =>
    have hn' := List.nodup_cons.mp hn
    simp only [encode,inds,List.mem_append,List.mem_map,List.mem_filter] at hp
    rcases hp with ⟨q,hq,rfl⟩ | ⟨q,⟨hq,hd⟩,rfl⟩
    · obtain ⟨S,hS,hI,rfl⟩ := ih hn'.2 hq
      have ha : a ∉ S := fun h => hn'.1 (List.mem_toFinset.mp (hS h))
      exact ⟨S,by simpa using hS.trans (Finset.subset_insert a _),hI,by simp [ind0,mark,bits,ha]⟩
    · obtain ⟨S,hS,hI,rfl⟩ := ih hn'.2 hq
      have ha : a ∉ S := fun h => hn'.1 (List.mem_toFinset.mp (hS h))
      have hz := (and_mask l (fun x => decide (G.Adj a x)) (fun x => decide (x∈S))).mp (beq_iff_eq.mp hd)
      have hi : Gᶜ.IsClique (insert a S : Finset V) := by
        rw [Finset.coe_insert, SimpleGraph.isClique_insert_of_notMem ha]
        refine ⟨hI,fun x hx => ⟨?_,?_⟩⟩
        · exact fun e => ha (e ▸ hx)
        · intro adj
          have := hz x (List.mem_toFinset.mp (hS hx)) (by simpa using adj)
          exact (of_decide_eq_false this) hx
      have hm := mark_congr l (insert a S) S (by intro x hx; simp [show x ≠ a from fun e => hn'.1 (e ▸ hx)])
      refine ⟨insert a S, by simpa using Finset.insert_subset_insert a hS, hi, ?_⟩
      simp [ind1,mark,bits,Finset.card_insert_of_notMem ha] at hm ⊢
      omega

theorem inds_complete {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (vs : List V) (hn : vs.Nodup) (S : Finset V) (hS : S ⊆ vs.toFinset) (hI : Gᶜ.IsClique (S : Set V)) :
    (mark vs S,S.card) ∈ inds (encode G vs) := by
  induction vs generalizing S with
  | nil =>
    have e : S=∅ := Finset.subset_empty.mp (by simpa using hS)
    simp [e,encode,inds,mark,bits]
  | cons a l ih =>
    have hn' := List.nodup_cons.mp hn
    simp only [encode,inds,List.mem_append,List.mem_map,List.mem_filter]
    by_cases ha : a ∈ S
    · let T := S.erase a
      have hT : T ⊆ l.toFinset := by
        intro x hx
        have m := Finset.mem_erase.mp hx
        have h := List.mem_cons.mp (List.mem_toFinset.mp (hS m.2))
        exact List.mem_toFinset.mpr (h.resolve_left m.1)
      have hI' := hI.subset (show (T : Set V) ⊆ (S : Set V) from Finset.erase_subset ..)
      have hmark := mark_congr l S T (by intro x hx; simp [T,show x≠a from fun e => hn'.1 (e ▸ hx)])
      have hcard : T.card + 1 = S.card := Finset.card_erase_add_one ha
      right
      refine ⟨(mark l T,T.card),⟨ih hn'.2 T hT hI', ?_⟩,?_⟩
      · apply beq_iff_eq.mpr
        apply (and_mask l (fun x => decide (G.Adj a x)) (fun x => decide (x∈T))).mpr
        intro x _ hx
        apply decide_eq_false
        intro hm
        have hmem := Finset.mem_erase.mp hm
        exact (hI ha hmem.2 hmem.1.symm).2 (of_decide_eq_true hx)
      · simp [ind1,mark,bits,ha,hcard] at hmark ⊢
        omega
    · have hT : S ⊆ l.toFinset := by
        intro x hx
        have h := List.mem_cons.mp (List.mem_toFinset.mp (hS hx))
        exact List.mem_toFinset.mpr (h.resolve_left (fun e => ha (e ▸ hx)))
      exact Or.inl ⟨_,ih hn'.2 S hT hI,by simp [ind0,mark,bits,ha]⟩


def countBits : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,x => (x%2) + countBits n (x/2)

def bump (m : Nat) : List Nat → List Nat
  | [] => []
  | x::xs => (x+m%2)::bump (m/2) xs

def degrees : List Nat → List Nat
  | [] => []
  | m::ms => countBits ms.length m :: bump m (degrees ms)

def sizeAt {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) (x : V) :=
  (vs.filter fun y => decide (G.Adj x y)).length

theorem half_step (x : Nat) : (2*x+1)/2=x := by omega

theorem count_map {V : Type*} (vs : List V) (f : V → Bool) :
    countBits vs.length (bits (vs.map f)) = (vs.filter f).length := by
  induction vs with
  | nil => rfl
  | cons a l ih =>
    cases ha : f a <;> simp [countBits,bits,ha,ih,half_step]
    omega

theorem bump_map {V : Type*} (vs : List V) (f : V → Bool) (d : V → Nat) :
    bump (bits (vs.map f)) (vs.map d) = vs.map (fun x => d x + (f x).toNat) := by
  induction vs with
  | nil => rfl
  | cons a l ih => cases ha : f a <;> simp [bump,bits,ha,ih,half_step]

theorem encode_length {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) :
    (encode G vs).length=vs.length := by induction vs with | nil => rfl | cons a as ih => simp [encode,ih]

theorem degrees_encode {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) :
    degrees (encode G vs) = vs.map (sizeAt G vs) := by
  induction vs with
  | nil => rfl
  | cons a l ih =>
    simp only [encode,degrees,encode_length,count_map,ih,bump_map,List.map_cons,List.cons.injEq]
    refine ⟨by simp [sizeAt], List.map_congr_left ?_⟩
    intro x _
    by_cases h : G.Adj a x <;> simp [sizeAt,h,G.adj_comm x a]

theorem sizeAt_finset {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {vs : List V} (hn : vs.Nodup) (x : V) :
    sizeAt G vs x = (vs.toFinset.filter (G.Adj x)).card := by
  have h := List.toFinset_filter vs (fun y => decide (G.Adj x y))
  simp only [decide_eq_true_eq] at h
  rw [← h, List.toFinset_card_of_nodup (hn.filter _)]
  rfl


def Small {V : Type*} (G : SimpleGraph V) (A : Finset V) (k : Nat) :=
  ∀ I ⊆ A, Gᶜ.IsClique (I : Set V) → I.card < k

theorem row_mark {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (base : List V) (x : V) :
    bits (base.map fun y => decide (G.Adj x y)) = mark base (base.toFinset.filter (G.Adj x)) := by
  unfold mark
  congr 1
  exact List.map_congr_left (fun y hy => by simp [hy])

theorem neighbors_small {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (A : Finset V) (x : V) :
    Gᶜ.IsClique ((A.filter (G.Adj x) : Finset V) : Set V) := by
  rw [G.isClique_compl]
  intro y hy z hz hn
  exact G.isIndepSet_neighborSet_of_triangleFree ht x (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2 hn

theorem degrees_bound {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (A : Finset V) (k : Nat) (hs : Small G A k)
    (l : List V) (hn : l.Nodup) (hsub : l.toFinset ⊆ A) :
    (degrees (encode G l)).all (· < k) = true := by
  rw [degrees_encode, List.all_eq_true]
  intro y hy
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hy
  simp only [decide_eq_true_eq, sizeAt_finset G hn]
  exact hs _ ((Finset.filter_subset _ _).trans hsub) (neighbors_small G ht _ x)

def okContacts (k : Nat) (isets : List (Nat × Nat)) (cs : List Nat) : Bool :=
  isets.all fun p => p.2 + (cs.filter fun v => v &&& p.1 == 0).length < k

theorem ok_contacts {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : Nat) (hs : Small G A k) (front base : List V)
    (hn : (front++base).Nodup) (hsub : (front++base).toFinset ⊆ A)
    (hi : Gᶜ.IsClique (front.toFinset : Set V)) :
    okContacts k (inds (encode G base)) (front.map fun x => bits (base.map fun y => decide (G.Adj x y))) := by
  rw [okContacts,List.all_eq_true]
  intro q hq
  obtain ⟨hh,hb,hd⟩ := List.nodup_append.mp hn
  obtain ⟨S,hS,hI,rfl⟩ := inds_sound G base hb hq
  let pred (v : V) : Bool := bits (base.map fun y => decide (G.Adj v y)) &&& mark base S == 0
  let F := front.filter pred
  have hF (x) (hx : x∈F) : x∈front := (List.mem_filter.mp hx).1
  have sep (x) (hx : x∈F) (y) (hy : y∈S) : Gᶜ.Adj x y := by
    have hx' := List.mem_filter.mp hx
    have hy' := List.mem_toFinset.mp (hS hy)
    have neq : x ≠ y := hd x hx'.1 y hy'
    exact ⟨neq,fun ha => by
      have e := (and_mask base (fun z => decide (G.Adj x z)) (fun z => decide (z ∈ S))).mp
        (beq_iff_eq.mp hx'.2) y hy' (by simpa using ha)
      exact of_decide_eq_false e hy⟩
  have sub : F.toFinset ∪ S ⊆ A := by
    apply Finset.union_subset
    · exact fun x hx => hsub (by simp [hF x (List.mem_toFinset.mp hx)])
    · exact fun x hx => hsub (by simp [List.mem_toFinset.mp (hS hx)])
  have together : Gᶜ.IsClique ((F.toFinset ∪ S : Finset V) : Set V) := by
    rw [Finset.coe_union, SimpleGraph.IsClique, Set.pairwise_union]
    refine ⟨hi.subset ?_,hI,?_⟩
    · exact fun x hx => List.mem_toFinset.mpr (hF x (List.mem_toFinset.mp hx))
    · intro x hx y hy _
      exact ⟨sep x (List.mem_toFinset.mp hx) y hy,(sep x (List.mem_toFinset.mp hx) y hy).symm⟩
  have dis : Disjoint F.toFinset S := Finset.disjoint_left.mpr fun x hx hy =>
    (sep x (List.mem_toFinset.mp hx) x hy).ne rfl
  have w := hs _ sub together
  rw [Finset.card_union_of_disjoint dis,List.toFinset_card_of_nodup (hh.filter _)] at w
  simp only [decide_eq_true_eq,List.filter_map,List.length_map]
  change S.card + F.length < k
  simpa only [F, Nat.add_comm S.card] using w


theorem bit_and {α : Type*} (l : List α) (f g : α → Bool) :
    bits (l.map f) &&& bits (l.map g) = bits (l.map fun x => f x && g x) := by
  induction l with
  | nil => simp [bits]
  | cons a l ih => simp only [List.map_cons,bits,← bit_form,Nat.land_bit,ih]

theorem bit_or {α : Type*} (l : List α) (f g : α → Bool) :
    bits (l.map f) ||| bits (l.map g) = bits (l.map fun x => f x || g x) := by
  induction l with
  | nil => simp [bits]
  | cons a l ih => simp only [List.map_cons,bits,← bit_form,Nat.lor_bit,ih]

def compat (I : List (Nat × Nat)) (a : Nat) := bits (I.map fun p => a &&& p.1 == 0)
def universal (I : List (Nat × Nat)) := bits (I.map fun _=> true)
def threshold (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) (j : Nat) :=
  bits (I.map fun p => decide (k≤ p.2 + (acc.filter fun a => a &&& p.1 == 0).length+j))

theorem saturated (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) (j : Nat) (h : k≤ j) :
    threshold k I acc j=universal I := by
  unfold threshold universal
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [decide_eq_true_eq]; omega

theorem threshold_cons (k : Nat) (I : List (Nat × Nat)) (a : Nat) (acc : List Nat) (j : Nat) :
    threshold k I (a::acc) j = threshold k I acc j ||| (compat I a &&& threshold k I acc (j+1)) := by
  unfold threshold compat
  rw [bit_and,bit_or]
  congr 1
  apply List.map_congr_left
  intro p _
  apply Bool.eq_iff_iff.mpr
  by_cases e : a &&& p.1=0 <;> simp [e]; omega

def cells (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,j => threshold k I acc j :: cells k I acc n (j+1)

def tick (u m : Nat) : List Nat → List Nat
  | [] => []
  | a::as => (a ||| (m &&& as.headD u)) :: tick u m as

theorem tick_cells (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) (a n j : Nat) (h : k ≤ j+n) :
    tick (universal I) (compat I a) (cells k I acc n j) = cells k I (a::acc) n j := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    simp only [cells,tick,List.cons.injEq]
    refine ⟨?_,ih (j+1) (by omega)⟩
    rw [threshold_cons]
    cases n with
    | zero => simp [cells,saturated k I acc (j+1) (by omega)]
    | succ n => rfl

theorem can_add (k : Nat) (I : List (Nat × Nat)) (acc : List Nat) (a : Nat)
    (h : okContacts k I (a::acc)) : compat I a &&& threshold k I acc 1=0 := by
  apply (and_mask I _ _).mpr
  intro p hp e
  have b := List.all_eq_true.mp h p hp
  simp only [List.filter_cons,e,if_true,List.length_cons,decide_eq_true_eq] at b
  apply decide_eq_false
  omega

def traverse (opts : List (Nat × Nat)) (u : Nat) (ending : List (Nat × Nat) → Bool) :
    Nat → Nat → List (Nat × Nat) → List Nat → List (List (Nat × Nat))
  | 0,_,acc,_ => if ending acc then [acc] else []
  | fuel+1,lo,acc,st => opts.flatMap fun a =>
    if lo ≤ a.1 && a.2 &&& st.headD u == 0 then
      traverse opts u ending fuel a.1 (a::acc) (tick u a.2 st) else []

theorem traverse_complete (opts : List (Nat × Nat)) (I : List (Nat × Nat)) (k : Nat) (hk : 0< k)
    (ending : List (Nat × Nat) → Bool) (next acc : List (Nat × Nat)) (lo : Nat)
    (hc : ∀ a∈next,a∈opts) (vals : ∀ a∈next,a.2=compat I a.1)
    (hl : ∀ a∈next,lo≤ a.1) (hs : next.Pairwise (fun a b => a.1 ≤ b.1))
    (hg : ∀ u w,next=u++w → okContacts k I ((u.reverse++acc).map Prod.fst)) (hf : ending (next.reverse++acc)) :
    next.reverse++acc ∈ traverse opts (universal I) ending next.length lo acc (cells k I (acc.map Prod.fst) k 1) := by
  induction next generalizing acc lo with
  | nil => simpa [traverse,hf] using hf
  | cons a rest ih =>
    simp only [List.length_cons,traverse,List.mem_flatMap]
    refine ⟨a,hc a (by simp),?_⟩
    have hd : (cells k I (acc.map Prod.fst) k 1).headD (universal I)=threshold k I (acc.map Prod.fst) 1 := by
      cases k with | zero => omega | succ k => rfl
    have an := vals a (by simp)
    have allow := can_add k I (acc.map Prod.fst) a.1 (by simpa using hg [a] rest rfl)
    simp only [hl a (by simp),decide_true,Bool.true_and,an,hd,allow,beq_self_eq_true,if_true,tick_cells k I (acc.map Prod.fst) a.1 k 1 (by omega)]
    simpa [List.append_assoc] using ih (a::acc) a.1 (fun x hx => hc x (by simp [hx]))
      (fun x hx => vals x (by simp [hx])) (List.pairwise_cons.mp hs).1 (List.pairwise_cons.mp hs).2
      (by intro u w h; simpa [List.append_assoc] using hg (a::u) w (by simp [h]))
      (by simpa [List.append_assoc] using hf)


def contactsOf {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (base front : List V) :=
  front.map fun x => bits (base.map fun y => decide (G.Adj x y))

def usable (k d : Nat) (base : List Nat) : List Nat :=
  ((inds base).filter fun p => d ≤ p.2+1 && p.2+1 < k).map Prod.fst

def guardRows (k : Nat) (base : List Nat) (isets : List (Nat × Nat)) (cs : List Nat) :=
  okContacts k isets cs && (degrees (shifted cs ++ base)).all (·< k)

def tagged (k d : Nat) (base : List Nat) :=
  (usable k d base).map fun x => (x,compat (inds base) x)

def assemble (_k d : Nat) (base : List Nat) (opts : List (Nat × Nat)) (bits0 : Nat) (lims : List Nat) :=
  let ending := fun cs : List (Nat × Nat) => (degrees (attach (cs.reverse.map Prod.fst) base)).all (d≤·)
  (traverse opts bits0 ending d 0 [] lims).map (fun cs => attach (cs.reverse.map Prod.fst) base)

def grow (k d : Nat) (base : List Nat) : List (List Nat) :=
  assemble k d base (tagged k d base) (universal (inds base)) (cells k (inds base) [] k 1)

theorem grow_complete {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k d : Nat) (ht : G.CliqueFree 3) (hs : Small G A k)
    (r : V) (front base : List V) (hn : (r::front++base).Nodup)
    (hall : (r::front++base).toFinset=A) (hd : front.length=d)
    (ha : ∀ x∈front,G.Adj r x) (hb : ∀ x∈base,¬G.Adj r x)
    (hcount : ∀ x∈front,d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k)
    (hmin : ∀ x∈A,d≤(A.filter (G.Adj x)).card)
    (horder : (contactsOf G base front).Pairwise (·≤·)) :
    encode G (r::front++base) ∈ grow k d (encode G base) := by
  let cs := contactsOf G base front
  have split := root_encoding G r front base ha hb ht
  change encode G (r::front++base) = attach cs (encode G base) at split
  have hbnd := (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.1
  have hc (s) (mem : s ∈ cs) : s ∈ usable k d (encode G base) := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp mem
    let S := base.toFinset.filter (G.Adj x)
    have row := inds_complete G base hbnd S (Finset.filter_subset ..) (neighbors_small G ht _ x)
    have m := hcount x hx
    rw [sizeAt_finset G hbnd] at m
    change bits (base.map fun y => decide (G.Adj x y)) ∈ _
    rw [row_mark]
    exact List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨row,by simpa [S] using m⟩,rfl⟩
  have guard_ (u w : List Nat) (h : cs=u++w) : guardRows k (encode G base) (inds (encode G base)) u := by
    let sl := front.take u.length
    have hu : contactsOf G base sl = u := by
      change (front.take u.length).map _=u
      rw [List.map_take, show front.map _=u++w from h, List.take_left]
    have ssub := (List.take_sublist u.length front).append (List.Sublist.refl base)
    have nodup : (sl++base).Nodup := (List.nodup_cons.mp hn).2.sublist ssub
    have sub : (sl++base).toFinset ⊆ A := by
      intro x hx
      rw [← hall]
      exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (ssub.subset (List.mem_toFinset.mp hx)))
    have ha' (x) (hx : x∈sl) := ha x ((List.take_sublist u.length front).subset hx)
    have indep : Gᶜ.IsClique (sl.toFinset : Set V) := by
      rw [G.isClique_compl]
      intro x hx y hy hxy
      exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x (List.mem_toFinset.mp hx)) (ha' y (List.mem_toFinset.mp hy)) hxy
    have em := contacts G sl base (by intro x hx y hy adj; exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x hx) (ha' y hy) adj.ne adj)
    change encode G (sl++base)=shifted (contactsOf G base sl)++encode G base at em
    rw [← hu]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨ok_contacts G A k hs sl base nodup sub indep,?_⟩
    rw [← em]
    exact degrees_bound G ht A k hs _ nodup sub
  have final_ : (degrees (attach cs (encode G base))).all (d≤·) = true := by
    rw [← split,degrees_encode,List.all_eq_true]
    intro n hh
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hh
    simpa only [decide_eq_true_eq,sizeAt_finset G hn,hall] using hmin x (hall ▸ List.mem_toFinset.mpr hx)
  have csl : cs.length=d := by simp [cs,contactsOf,hd]
  let base' := encode G base
  let tag (x : Nat) := (x,compat (inds base') x)
  let ts := cs.map tag
  have ret (ss : List Nat) : (ss.map tag).map Prod.fst = ss := by simp [tag,Function.comp_def]
  have tg (a) (ma : a∈ts) : a ∈ tagged k d base' := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ma
    exact List.mem_map.mpr ⟨x,hc x hx,rfl⟩
  have gg (u w : List (Nat × Nat)) (h : ts=u++w) : okContacts k (inds base') (u.reverse.map Prod.fst) := by
    let sl := cs.take u.length
    have split_ : cs=sl++cs.drop u.length := (List.take_append_drop u.length cs).symm
    have hu : sl.map tag=u := by
      change (cs.take u.length).map tag=u
      rw [List.map_take,show cs.map tag=u++w from h,List.take_left]
    have gh := Bool.and_eq_true_iff.mp (guard_ sl (cs.drop u.length) split_)
    rw [← hu,List.map_reverse,ret]
    simpa [okContacts] using gh.1
  have tslen : ts.length=d := by simp [ts,csl]
  have tsord : ts.Pairwise (fun a b => a.1 ≤ b.1) := List.pairwise_map.mpr horder
  rw [split]
  apply List.mem_map.mpr
  refine ⟨ts.reverse,?_,by simp [ts,ret]⟩
  have hk : 0< k := hs ∅ (by simp) (by simp)
  simpa only [List.append_nil,tslen,List.map_nil] using traverse_complete (tagged k d base') (inds base') k hk
    (fun u => (degrees (attach (u.reverse.map Prod.fst) base')).all (d≤·)) ts [] 0 tg
    (by intro a ha; obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha; rfl) (by simp) tsord
    (by simpa using gg) (by simpa only [List.append_nil,List.reverse_reverse,ts,ret,base'] using final_)

def levels (norm : List Nat → List Nat) : Nat → Nat → Nat → List (List Nat)
  | 0,_,_ => []
  | k+1,n,cap => if n=0 then [[]] else
    ((List.range (min cap (min k (n-1)) + 1)).flatMap fun d =>
      (levels norm k (n-1-d) (k-1)).flatMap fun base => (grow (k+1) d base).map norm).eraseDups

theorem sorted_neigh {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : Finset V) (base : List V) :
    ∃ l : List V, l.Nodup ∧ l.toFinset=N ∧ (contactsOf G base l).Pairwise (·≤·) := by
  let key (x : V) := bits (base.map fun y => decide (G.Adj x y))
  let ord (a b : V) := decide (key a ≤ key b)
  let l := N.toList.mergeSort ord
  have h := List.mergeSort_perm N.toList ord
  refine ⟨l,h.nodup_iff.mpr N.nodup_toList,?_,?_⟩
  · ext x
    simp [l]
  · have htr (a b c) : ord a b → ord b c → ord a c := by simp only [ord,decide_eq_true_eq]; omega
    have htot (a b) : ord a b || ord b a := by simp [ord,le_total]
    have sort_ := List.pairwise_mergeSort htr htot N.toList
    apply List.pairwise_map.mpr
    simpa only [ord,decide_eq_true_eq] using sort_

theorem levels_complete {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (norm : List Nat → List Nat)
    (hnorm : ∀ l : List V, ∃ l' : List V, l'.Perm l ∧ encode G l'=norm (encode G l))
    (k : Nat) (A : Finset V) (cap : Nat) (hs : Small G A k)
    (hu : A.Nonempty → ∃ x∈A,(A.filter (G.Adj x)).card ≤ cap) :
    ∃ vs : List V, vs.Nodup ∧ vs.toFinset=A ∧ encode G vs ∈ levels norm k A.card cap := by
  induction k generalizing A cap with
  | zero => have h := hs ∅ (by simp) (by simp); simp at h
  | succ k ih =>
    by_cases empty : A=∅
    · subst A; exact ⟨[],by simp,by simp,by simp [encode,levels]⟩
    have non := Finset.nonempty_iff_ne_empty.mpr empty
    obtain ⟨r,hr,hmin⟩ := A.exists_min_image (fun x => (A.filter (G.Adj x)).card) non
    let N := A.filter (G.Adj r)
    let B := A \ insert r N
    let d := N.card
    have hNr : r∉N := by simp [N]
    have hNA : N⊆A := Finset.filter_subset ..
    have hBA : B⊆A := Finset.sdiff_subset
    have hu' : d≤ cap := by obtain ⟨x,hx,hh⟩ := hu non; exact (hmin x hx).trans hh
    have hdk : d≤ k := Nat.le_of_lt_succ (hs N hNA (neighbors_small G ht A r))
    have hBcard : B.card + d + 1 = A.card := by
      have hh := Finset.card_sdiff_add_card_eq_card (Finset.insert_subset hr hNA)
      rw [Finset.card_insert_of_notMem hNr] at hh
      omega
    have rB : r∉B := by simp [B]
    have hbase (x) (hx : x∈B) : ¬G.Adj r x := by
      have h := Finset.mem_sdiff.mp hx
      exact fun ha => h.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h.1,ha⟩))
    have noK : Small G B k := by
      intro S hS hI
      have rn : r∉S := fun h => rB (hS h)
      have indep : Gᶜ.IsClique (insert r S : Finset V) := by
        rw [Finset.coe_insert,SimpleGraph.isClique_insert_of_notMem rn]
        exact ⟨hI,fun x hx => ⟨fun e => rn (e ▸ hx),hbase x (hS hx)⟩⟩
      have hh := hs (insert r S) (Finset.insert_subset hr (hS.trans hBA)) indep
      rw [Finset.card_insert_of_notMem rn] at hh
      omega
    obtain ⟨base,hbn,hb,cls⟩ := ih B (k-1) noK (by
      rintro ⟨x,hx⟩
      have mm := noK (B.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht B x)
      exact ⟨x,hx,by omega⟩)
    obtain ⟨front,hfn,hf,sorted_⟩ := sorted_neigh G N base
    have ha (x) (hx : x∈front) : G.Adj r x := (Finset.mem_filter.mp (hf ▸ List.mem_toFinset.mpr hx)).2
    have hnot (x) (hx : x∈base) := hbase x (hb ▸ List.mem_toFinset.mpr hx)
    have dl : front.length=d := by rw [← List.toFinset_card_of_nodup hfn,hf]
    have nodup : (r::front++base).Nodup := by
      apply List.nodup_cons.mpr
      constructor
      · change r ∉ front++base
        rw [List.mem_append,not_or]
        exact ⟨fun h => hNr (hf ▸ List.mem_toFinset.mpr h), fun h => rB (hb ▸ List.mem_toFinset.mpr h)⟩
      · exact List.nodup_append.mpr ⟨hfn,hbn,fun x hx y hy e => hnot y hy (e ▸ ha x hx)⟩
    have cover : (r::front++base).toFinset=A := by
      ext x
      simp only [List.toFinset_cons,List.toFinset_append,hf,hb,B,Finset.mem_insert,Finset.mem_union,Finset.mem_sdiff]
      have h1 : x=r → x∈A := fun h => h ▸ hr
      have h2 : x∈N → x∈A := fun h => hNA h
      grind
    have hcount (x) (hx : x∈front) : d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k+1 := by
      have xN : x∈N := hf ▸ List.mem_toFinset.mpr hx
      have adj := ha x hx
      have eq : A.filter (G.Adj x)=insert r (B.filter (G.Adj x)) := by
        ext y
        simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_sdiff,B]
        constructor
        · rintro ⟨yA,xy⟩
          by_cases yr : y=r
          · exact Or.inl yr
          · exact Or.inr ⟨⟨yA,not_or.mpr ⟨yr,fun yN => G.isIndepSet_neighborSet_of_triangleFree ht r adj (Finset.mem_filter.mp yN).2 xy.ne xy⟩⟩,xy⟩
        · rintro (rfl|⟨⟨yA,_⟩,xy⟩)
          · exact ⟨hr,adj.symm⟩
          · exact ⟨yA,xy⟩
      have mm := hmin x (hNA xN)
      have mx := hs (A.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht A x)
      have rn : r∉B.filter (G.Adj x) := fun h => rB (Finset.mem_filter.mp h).1
      rw [eq,Finset.card_insert_of_notMem rn] at mm mx
      rw [sizeAt_finset G hbn,hb]
      exact ⟨mm,mx⟩
    have grown := grow_complete G A (k+1) d ht hs r front base nodup cover dl ha hnot hcount hmin sorted_
    obtain ⟨l,hperm,heq⟩ := hnorm (r::front++base)
    refine ⟨l,hperm.nodup_iff.mpr nodup,?_,?_⟩
    · rw [← cover]
      ext x
      exact List.mem_toFinset.trans (hperm.mem_iff.trans List.mem_toFinset.symm)
    · rw [heq,levels,if_neg (Finset.card_ne_zero.mpr non)]
      apply List.mem_eraseDups.mpr
      apply List.mem_flatMap.mpr
      refine ⟨d,List.mem_range.mpr (by omega),List.mem_flatMap.mpr ⟨encode G base,?_,List.mem_map.mpr ⟨_,grown,rfl⟩⟩⟩
      simpa only [show A.card-1-d=B.card by omega] using cls


def swapAt {α : Type*} : Nat → List α → List α
  | 0,x::y::xs => y::x::xs
  | i+1,x::xs => x::swapAt i xs
  | _,l => l

theorem swap_perm {α : Type*} (i : Nat) (l : List α) : (swapAt i l).Perm l := by
  induction i generalizing l with
  | zero => cases l with | nil => rfl | cons a l => cases l with | nil => rfl | cons b l => exact List.Perm.swap a b l
  | succ i ih => cases l with | nil => rfl | cons a l => exact List.Perm.cons a (ih l)

def exchange : Nat → Nat → Nat
  | 0,x => 4*(x/4)+2*(x%2)+((x/2)%2)
  | i+1,x => 2*exchange i (x/2)+x%2

theorem bits_swap (i : Nat) (l : List Bool) (h : i+2≤ l.length) :
    bits (swapAt i l)=exchange i (bits l) := by
  induction i generalizing l with
  | zero =>
    obtain ⟨a,b,l,rfl⟩ : ∃ a b t,l=a::b::t := by cases l with | nil => simp at h | cons a l => cases l with | nil => simp at h | cons b t => exact ⟨_,_,_,rfl⟩
    cases a <;> cases b <;> simp [swapAt,bits,exchange] <;> omega
  | succ i ih =>
    cases l with
    | nil => simp at h
    | cons a t =>
      have e := ih t (by simp at h; omega)
      cases a <;> simp [swapAt,bits,exchange,half_step,e]

theorem swap_map {α β : Type*} (f : α→β) (i : Nat) (l : List α) :
    (swapAt i l).map f=swapAt i (l.map f) := by
  induction i generalizing l with
  | zero => cases l with | nil => rfl | cons a l => cases l <;> rfl
  | succ i ih => cases l with | nil => rfl | cons a l => simp [swapAt,ih]

def swapCode : Nat → List Nat → List Nat
  | 0,p::q::rs => (p%2+2*q)::(p/2)::rs
  | i+1,p::rs => exchange i p :: swapCode i rs
  | _,l => l

theorem swap_encode {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : Nat) (l : List V) (h : i+2≤ l.length) : encode G (swapAt i l) = swapCode i (encode G l) := by
  induction i generalizing l with
  | zero =>
    obtain ⟨a,b,t,rfl⟩ : ∃ a b t,l=a::b::t := by cases l with | nil => simp at h | cons a l => cases l with | nil => simp at h | cons b t => exact ⟨_,_,_,rfl⟩
    by_cases adj : G.Adj a b <;> simp [swapAt,swapCode,encode,bits,adj,G.adj_comm b a,Nat.add_comm]
    omega
  | succ i ih =>
    cases l with
    | nil => simp at h
    | cons a t =>
      have hi : i+2≤ t.length := by simp at h; omega
      simp only [swapAt,encode,swap_map,swapCode,List.cons.injEq]
      exact ⟨bits_swap i _ (by simpa using hi),ih t hi⟩

def relabel (swaps rows : List Nat) :=
  swaps.foldl (fun l i => if i+2≤ l.length then swapCode i l else l) rows

theorem relabel_real {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (swaps : List Nat) (l : List V) : ∃ l', l'.Perm l ∧ encode G l'=relabel swaps (encode G l) := by
  induction swaps generalizing l with
  | nil => exact ⟨l,.refl _,rfl⟩
  | cons i is ih =>
    by_cases hi : i+2≤ l.length
    · obtain ⟨t,ht,he⟩ := ih (swapAt i l)
      exact ⟨t,ht.trans (swap_perm ..),by simpa [relabel,encode_length,hi,swap_encode G i l hi] using he⟩
    · simpa [relabel,encode_length,hi] using ih l


def renumber : List Nat → List Nat
  | [1,2,1,0] => [2]
  | [1,2,3,2,2,1,0] => [2,4]
  | [1,4,3,2,2,1,0] => [3,2,5,4]
  | [1,8,3,2,2,1,0] => [4,3,2,3,5,4]
  | [1,9,3,2,2,1,0] => [2,4]
  | [1,12,3,2,2,1,0] => [5,4,3,2,4,3,5,4]
  | [1,16,3,2,2,1,0] => [5,4,3,2,4,3,5,4]
  | [1,17,3,2,2,1,0] => [3,2,5,4]
  | [1,18,3,2,2,1,0] => [4,3,2,3,5,4]
  | [3,2,2,3,2,1,0] => [5,4,3,2,1,0,5,4,3,2,1,5,4,3,2,5,4,3,4]
  | [3,2,4,3,2,1,0] => [5,4,3,2,1,0,4,3,2,1,5,4,3,2,5,4,3,4]
  | [3,2,6,3,2,1,0] => [5,4,3,2,1,0,4,3,2,1,5,4,3,2,4,3]
  | [3,2,10,1,1,1,0] => [4,3,2,1,0,5,4,3,2,1,5,4,3,2,4,3]
  | [3,4,8,3,2,1,0] => [4,3,2,1,0,3,2,1,5,4,3,2,5,4,3,4]
  | [3,4,9,1,1,1,0] => [2,1,0,2,1,3,2,5]
  | [3,4,9,3,2,1,0] => [4,3,2,1,0,3,2,1,5,4,3,2,4,3]
  | [3,4,9,3,2,2,1,0] => [3,5]
  | [3,8,8,3,2,1,0] => [3,2,1,0,3,2,1,5,4,3,2,5,4,3,4]
  | [3,8,9,1,1,1,0] => [5,4,3,2,1,0,2,1,5,4,3,2]
  | [3,8,9,3,2,1,0] => [3,2,1,0,3,2,1,5,4,3,2,4,3]
  | [3,8,17,3,2,2,1,0] => [4,3,6,5]
  | [3,10,8,1,1,1,0] => [3,2,1,0,3,2,1,4,3,2,3]
  | [3,10,10,1,1,1,0] => [2,1,0,3,2,1,2,4,3,5,4,5]
  | [3,12,8,3,2,1,0] => [2,1,0,3,2,1,4,3,2,3]
  | [3,12,9,1,0,1,0] => [1,5]
  | [3,12,17,3,2,2,1,0] => [4,6]
  | [3,16,9,1,1,1,0] => [0,5,4,3,2]
  | [3,16,18,3,2,2,1,0] => [5,4,3,4,6,5]
  | [3,18,10,1,1,1,0] => [1,5,4,3,5,4,5]
  | [3,18,18,3,2,2,1,0] => [3,5,4,6]
  | [3,24,16,3,2,2,1,0] => [1,6,5,4,3,5,4,6,5]
  | [3,24,17,3,2,2,1,0] => [6,5,4,3,5,4,6,5]
  | [3,24,18,3,2,2,1,0] => [6,5,4,3,6,5,4,6,5,6]
  | [7,24,66,137,3,12,9,3,2,2,1,0] => [0,4,3,2,5,4,3,5,4,8,7,10,9]
  | [7,24,130,145,3,12,9,3,2,2,1,0] => [0,5,4,3,2,5,4,3,5,4,9,8,7,8,10,9]
  | [7,24,146,145,3,12,9,3,2,2,1,0] => [5,7,9]
  | [7,24,194,129,3,2,6,3,2,2,1,0] => [2,8,10]
  | [7,24,194,129,3,12,9,3,2,2,1,0] => [0,5,4,3,2,5,4,3,5,4,5,10,9,8,7,9,8,10,9]
  | [7,24,194,137,3,2,6,3,2,2,1,0] => [2,8,10]
  | [7,24,194,137,3,12,9,3,2,2,1,0] => [7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,7,6,5,4,3,9,8,7,6,5,4,10,9,8,7,6,5,7,6,8,7,9,8,10]
  | [7,24,194,145,3,12,9,3,2,2,1,0] => [6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,8,7,6,5,4,3,9,8,7,6,5,4,10,9,8,7,6,5,7,6,8,7,9,8,10]
  | [7,36,132,146,3,2,6,3,2,2,1,0] => [4,6]
  | [7,36,140,146,3,2,6,3,2,2,1,0] => [4,6]
  | [7,36,196,130,3,2,6,3,2,2,1,0] => [2,4,6,8,10]
  | [7,36,196,134,3,2,6,3,2,2,1,0] => [2,4,6,8,10]
  | [7,36,196,146,3,2,6,3,2,2,1,0] => [4,6]
  | [7,260,140,144,3,2,6,3,2,2,1,0] => [2,1,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,260,140,145,3,2,6,3,2,2,1,0] => [4,3,2,1,0,6,5,4,3,2,1,3,2,5,4,3,6,5,4,8,7,6,5,8,7,6,10,9,8,7,9,8,10,9]
  | [7,260,140,146,3,2,6,3,2,2,1,0] => [3,2,1,0,1,4,3,2,5,4,3,4,9,8,7,6,8,10,9]
  | [7,260,268,145,3,2,6,3,2,2,1,0] => [9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,6,8,10]
  | [7,260,268,145,3,12,9,3,2,2,1,0] => [5,7,9]
  | [7,264,146,144,3,2,6,3,2,2,1,0] => [2,1,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,264,146,145,3,2,6,3,2,2,1,0] => [4,3,2,1,0,1,4,3,2,6,5,4,3,4,9,8,7,6,8,10,9]
  | [7,264,146,146,3,2,6,3,2,2,1,0] => [3,2,1,0,5,4,3,2,1,3,2,5,4,3,6,5,4,8,7,6,5,8,7,6,10,9,8,7,9,8,10,9]
  | [7,264,274,146,3,2,6,3,2,2,1,0] => [9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,7,6,9,8,10]
  | [7,280,146,144,3,2,6,3,2,2,1,0] => [2,1,2,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,280,146,146,3,2,6,3,2,2,1,0] => [1,4,6]
  | [7,280,194,129,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,3,2,1,0,3,2,1,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,5,4,6,8,10]
  | [7,280,194,144,3,2,6,3,2,2,1,0] => [2,1,2,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,280,194,145,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,3,2,1,0,3,2,1,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,5,4,6,8,10]
  | [7,280,194,146,3,2,6,3,2,2,1,0] => [2,1,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,280,274,146,3,2,6,3,2,2,1,0] => [1,2,4,6,8,10]
  | [7,292,196,130,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,3,2,1,0,3,2,1,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,5,4,7,6,9,8,10]
  | [7,292,196,134,3,2,6,3,2,2,1,0] => [4,6]
  | [7,292,196,144,3,2,6,3,2,2,1,0] => [2,1,2,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,292,196,145,3,2,6,3,2,2,1,0] => [2,1,9,8,7,6,5,4,10,9,8,7,6,5,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,292,196,146,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,3,2,1,0,3,2,1,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,5,4,7,6,9,8,10]
  | [7,292,268,145,3,2,6,3,2,2,1,0] => [1,2,8,10]
  | [7,292,268,145,3,12,9,3,2,2,1,0] => [5,7,9]
  | [7,384,258,134,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,384,258,134,3,12,9,3,2,2,1,0] => [0,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,8]
  | [7,384,260,137,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,384,260,145,3,12,9,3,2,2,1,0] => [0,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,7,10,9,8,10]
  | [7,384,264,137,3,12,9,3,2,2,1,0] => [0,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,8,7,9,8,10]
  | [7,384,268,137,3,2,6,3,2,2,1,0] => [2,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,384,268,137,3,12,9,3,2,2,1,0] => [7,6,5,4,3,2,1,0,5,4,3,2,1,7,6,5,4,3,2,9,8,7,6,5,4,3,8,7,6,5,4,8,7,6,5,7,6,8,7,10,9,8,10]
  | [7,384,268,145,3,2,6,3,2,2,1,0] => [2,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,384,268,145,3,12,9,3,2,2,1,0] => [6,5,4,3,2,1,0,6,5,4,3,2,1,7,6,5,4,3,2,8,7,6,5,4,3,8,7,6,5,4,8,7,6,5,7,6,8,7,10,9,8,10]
  | [7,384,274,146,3,2,6,3,2,2,1,0] => [2,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,384,274,148,3,12,9,3,2,2,1,0] => [2,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,9,8,7,10,9,8,10,9,10]
  | [7,384,276,145,3,12,9,3,2,2,1,0] => [10,9,8,7,6,5,4,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,9,10]
  | [7,388,258,134,3,2,6,3,2,2,1,0] => [4,3,2,1,0,6,5,4,3,2,1,4,3,2,5,4,3,6,5,4,7,6,5,8,7,6,9,8,7,8,10,9]
  | [7,388,260,137,3,2,6,3,2,2,1,0] => [4,3,2,1,0,2,1,4,3,2,6,5,4,3,5,4,10,9,8,7,6,9,8,10,9]
  | [7,388,260,145,3,12,9,3,2,2,1,0] => [1,10,9,8,7,6,5,4,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,9,10]
  | [7,388,264,137,3,12,9,3,2,2,1,0] => [1,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,9,8,7,10,9,8,10,9,10]
  | [7,388,268,137,3,2,6,3,2,2,1,0] => [1,2,8,10]
  | [7,388,268,145,3,2,6,3,2,2,1,0] => [9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,6,8,10]
  | [7,388,268,145,3,12,9,3,2,2,1,0] => [5,7,9]
  | [7,388,274,146,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,9,8,10,9]
  | [7,388,274,148,3,12,9,3,2,2,1,0] => [2,1,10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,9,8,7,10,9,8,10,9,10]
  | [7,388,276,145,3,12,9,3,2,2,1,0] => [1,10,9,8,7,6,5,4,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,9,10]
  | [7,392,258,134,3,2,6,3,2,2,1,0] => [3,2,1,0,2,1,4,3,2,5,4,3,5,4,10,9,8,7,6,9,8,10,9]
  | [7,392,260,137,3,2,6,3,2,2,1,0] => [3,2,1,0,5,4,3,2,1,4,3,2,5,4,3,6,5,4,7,6,5,8,7,6,9,8,7,8,10,9]
  | [7,392,268,137,3,2,6,3,2,2,1,0] => [2,1,2,4,6,8,10]
  | [7,392,268,145,3,2,6,3,2,2,1,0] => [10,9,8,7,6,5,4,10,9,8,7,6,5,10,9,8,7,6,10,9,8,7,10,9,8,10,9,10]
  | [7,392,274,146,3,2,6,3,2,2,1,0] => [9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,7,6,9,8,10]
  | [15,304,164,162,82,3,2,9,1,1,1,0] => [2,1,0,10,9,8,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,6,5,4,3,6,5,7,6,8,7,9,10]
  | [15,304,196,138,73,1,6,3,2,2,1,0] => [2,1,3,2,8,10]
  | [15,584,392,268,145,3,2,6,3,2,2,1,0] => [5,7]
  | _ => []

def normalized (g : List Nat) := relabel (renumber g) g

def roots0 : List (List Nat) := []
def roots1 : List (List Nat) := []
def roots2 : List (List Nat) := []
def roots3 : List (List Nat) := [[15,560,388,274,146,3,2,6,3,2,2,1,0]]
def roots4 : List (List Nat) := [[7,24,130,145,3,2,6,3,2,2,1,0],
  [7,24,146,145,3,2,6,3,2,2,1,0],
  [7,24,194,145,3,2,6,3,2,2,1,0],
  [7,280,146,145,3,2,6,3,2,2,1,0],
  [7,280,194,137,3,2,6,3,2,2,1,0],
  [7,24,98,137,3,12,9,3,2,2,1,0],
  [7,132,268,137,3,12,9,3,2,2,1,0],
  [7,196,268,137,3,12,9,3,2,2,1,0],
  [7,388,258,134,3,12,9,3,2,2,1,0],
  [7,388,268,137,3,12,9,3,2,2,1,0],
  [15,296,196,140,73,1,6,3,2,2,1,0],
  [15,352,196,146,82,3,10,10,1,0,1,0]]

theorem degrees_length (g : List Nat) : (degrees g).length=g.length := by
  have step (xs : List Nat) (m : Nat) : (bump m xs).length=xs.length := by
    induction xs generalizing m with | nil => rfl | cons a xs ih => simp [bump,ih]
  induction g with | nil => rfl | cons a g ih => simp [degrees,step,ih]

theorem bump_sum (xs : List Nat) (m : Nat) : (bump m xs).sum=xs.sum+countBits xs.length m := by
  induction xs generalizing m with | nil => rfl | cons a xs ih => simp [bump,countBits,ih]; omega

def edges_ : List Nat → Nat
  | [] => 0
  | m::t => countBits t.length m + edges_ t

theorem energy (rows : List Nat) : (degrees rows).sum=2*edges_ rows := by
  induction rows with
  | nil => rfl
  | cons m t ih => simp [degrees,edges_,bump_sum,degrees_length,ih]; omega

theorem count_shift (n a j : Nat) : countBits (j+n) (2^j*a)=countBits n a := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : 2^(j+1)*a=2*(2^j*a) := by rw [pow_succ]; ring
    rw [Nat.succ_add,countBits,e]
    simp [ih]

theorem count_full (d n : Nat) : countBits (d+n) (2^d-1)=d := by
  induction d with
  | zero =>
    have h (t : Nat) : countBits t 0=0 := by induction t with | zero => rfl | succ k ih => simp [countBits,ih]
    simp [h]
  | succ d ih =>
    have hp : 0 < 2^d := Nat.two_pow_pos _
    have split : 2^(d+1)-1=2*(2^d-1)+1 := by rw [pow_succ]; omega
    rw [Nat.succ_add,countBits,split,half_step,ih]
    omega

theorem shifted_length (xs : List Nat) : (shifted xs).length=xs.length := by
  induction xs with | nil => rfl | cons a xs ih => simp [shifted,ih]

theorem edges_attached (xs b : List Nat) : edges_ (attach xs b) =
    xs.length + (xs.map (countBits b.length)).sum + edges_ b := by
  have h (ls : List Nat) : edges_ (shifted ls++b)=(ls.map (countBits b.length)).sum+edges_ b := by
    induction ls with
    | nil => simp [shifted]
    | cons a ls ih => simp [shifted,edges_,shifted_length,count_shift,ih,Nat.add_assoc]
  simp [attach,edges_,shifted_length,count_full,h,Nat.add_assoc]

def Extension (k d : Nat) (b cs : List Nat) : Prop :=
  cs.length = d ∧ (∀ x ∈ cs, x ∈ usable k d b) ∧ okContacts k (inds b) cs = true
theorem graphExtension {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k d : Nat) (ht : G.CliqueFree 3) (hs : Small G A k)
    (r : V) (front base : List V) (hn : (r::front++base).Nodup)
    (hall : (r::front++base).toFinset=A) (hd : front.length=d)
    (ha : ∀ x∈front,G.Adj r x) (hb : ∀ x∈base,¬G.Adj r x)
    (hcount : ∀ x∈front,d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k)
    (_hmin : ∀ x∈A,d≤(A.filter (G.Adj x)).card)
    (_horder : (contactsOf G base front).Pairwise (·≤·)) :
    ∃ cs, Extension k d (encode G base) cs ∧ encode G (r::front++base) = attach cs (encode G base) := by
  let cs := contactsOf G base front
  have split := root_encoding G r front base ha hb ht
  change encode G (r::front++base) = attach cs (encode G base) at split
  have hbnd := (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.1
  have hc (s) (mem : s ∈ cs) : s ∈ usable k d (encode G base) := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp mem
    let S := base.toFinset.filter (G.Adj x)
    have row := inds_complete G base hbnd S (Finset.filter_subset ..) (neighbors_small G ht _ x)
    have m := hcount x hx
    rw [sizeAt_finset G hbnd] at m
    change bits (base.map fun y => decide (G.Adj x y)) ∈ _
    rw [row_mark]
    exact List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨row,by simpa [S] using m⟩,rfl⟩
  have guard_ (u w : List Nat) (h : cs=u++w) : guardRows k (encode G base) (inds (encode G base)) u := by
    let sl := front.take u.length
    have hu : contactsOf G base sl = u := by
      change (front.take u.length).map _=u
      rw [List.map_take, show front.map _=u++w from h, List.take_left]
    have ssub := (List.take_sublist u.length front).append (List.Sublist.refl base)
    have nodup : (sl++base).Nodup := (List.nodup_cons.mp hn).2.sublist ssub
    have sub : (sl++base).toFinset ⊆ A := by
      intro x hx
      rw [← hall]
      exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (ssub.subset (List.mem_toFinset.mp hx)))
    have ha' (x) (hx : x∈sl) := ha x ((List.take_sublist u.length front).subset hx)
    have indep : Gᶜ.IsClique (sl.toFinset : Set V) := by
      rw [G.isClique_compl]
      intro x hx y hy hxy
      exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x (List.mem_toFinset.mp hx)) (ha' y (List.mem_toFinset.mp hy)) hxy
    have em := contacts G sl base (by intro x hx y hy adj; exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x hx) (ha' y hy) adj.ne adj)
    change encode G (sl++base)=shifted (contactsOf G base sl)++encode G base at em
    rw [← hu]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨ok_contacts G A k hs sl base nodup sub indep,?_⟩
    rw [← em]
    exact degrees_bound G ht A k hs _ nodup sub
  exact ⟨cs, ⟨by simp [cs,contactsOf,hd], hc,
    (Bool.and_eq_true_iff.mp (guard_ cs [] (by simp))).1⟩, split⟩

theorem rootSplitting {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (norm : List Nat → List Nat)
    (hnorm : ∀ l : List V, ∃ l' : List V, l'.Perm l ∧ encode G l'=norm (encode G l))
    (k : Nat) (A : Finset V) (non : A.Nonempty) (cap : Nat) (hs : Small G A (k+1))
    (hu : A.Nonempty → ∃ x∈A,(A.filter (G.Adj x)).card ≤ cap) :
    ∃ (vs : List V) (d : Nat) (b cs : List Nat), vs.Nodup ∧ vs.toFinset=A ∧ d≤ cap ∧
      b∈levels norm k (A.card-1-d) (k-1) ∧ Extension (k+1) d b cs ∧ encode G vs=attach cs b ∧ ∃ r ∈ A, (A.filter (G.Adj r)).card = d := by
    obtain ⟨r,hr,hmin⟩ := A.exists_min_image (fun x => (A.filter (G.Adj x)).card) non
    let N := A.filter (G.Adj r)
    let B := A \ insert r N
    let d := N.card
    have hNr : r∉N := by simp [N]
    have hNA : N⊆A := Finset.filter_subset ..
    have hBA : B⊆A := Finset.sdiff_subset
    have hu' : d≤ cap := by obtain ⟨x,hx,hh⟩ := hu non; exact (hmin x hx).trans hh
    have hdk : d≤ k := Nat.le_of_lt_succ (hs N hNA (neighbors_small G ht A r))
    have hBcard : B.card + d + 1 = A.card := by
      have hh := Finset.card_sdiff_add_card_eq_card (Finset.insert_subset hr hNA)
      rw [Finset.card_insert_of_notMem hNr] at hh
      omega
    have rB : r∉B := by simp [B]
    have hbase (x) (hx : x∈B) : ¬G.Adj r x := by
      have h := Finset.mem_sdiff.mp hx
      exact fun ha => h.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h.1,ha⟩))
    have noK : Small G B k := by
      intro S hS hI
      have rn : r∉S := fun h => rB (hS h)
      have indep : Gᶜ.IsClique (insert r S : Finset V) := by
        rw [Finset.coe_insert,SimpleGraph.isClique_insert_of_notMem rn]
        exact ⟨hI,fun x hx => ⟨fun e => rn (e ▸ hx),hbase x (hS hx)⟩⟩
      have hh := hs (insert r S) (Finset.insert_subset hr (hS.trans hBA)) indep
      rw [Finset.card_insert_of_notMem rn] at hh
      omega
    obtain ⟨base,hbn,hb,cls⟩ := levels_complete G ht norm hnorm k B (k-1) noK (by
      rintro ⟨x,hx⟩
      have mm := noK (B.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht B x)
      exact ⟨x,hx,by omega⟩)
    obtain ⟨front,hfn,hf,sorted_⟩ := sorted_neigh G N base
    have ha (x) (hx : x∈front) : G.Adj r x := (Finset.mem_filter.mp (hf ▸ List.mem_toFinset.mpr hx)).2
    have hnot (x) (hx : x∈base) := hbase x (hb ▸ List.mem_toFinset.mpr hx)
    have dl : front.length=d := by rw [← List.toFinset_card_of_nodup hfn,hf]
    have nodup : (r::front++base).Nodup := by
      apply List.nodup_cons.mpr
      constructor
      · change r ∉ front++base
        rw [List.mem_append,not_or]
        exact ⟨fun h => hNr (hf ▸ List.mem_toFinset.mpr h), fun h => rB (hb ▸ List.mem_toFinset.mpr h)⟩
      · exact List.nodup_append.mpr ⟨hfn,hbn,fun x hx y hy e => hnot y hy (e ▸ ha x hx)⟩
    have cover : (r::front++base).toFinset=A := by
      ext x
      simp only [List.toFinset_cons,List.toFinset_append,hf,hb,B,Finset.mem_insert,Finset.mem_union,Finset.mem_sdiff]
      have h1 : x=r → x∈A := fun h => h ▸ hr
      have h2 : x∈N → x∈A := fun h => hNA h
      grind
    have hcount (x) (hx : x∈front) : d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k+1 := by
      have xN : x∈N := hf ▸ List.mem_toFinset.mpr hx
      have adj := ha x hx
      have eq : A.filter (G.Adj x)=insert r (B.filter (G.Adj x)) := by
        ext y
        simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_sdiff,B]
        constructor
        · rintro ⟨yA,xy⟩
          by_cases yr : y=r
          · exact Or.inl yr
          · exact Or.inr ⟨⟨yA,not_or.mpr ⟨yr,fun yN => G.isIndepSet_neighborSet_of_triangleFree ht r adj (Finset.mem_filter.mp yN).2 xy.ne xy⟩⟩,xy⟩
        · rintro (rfl|⟨⟨yA,_⟩,xy⟩)
          · exact ⟨hr,adj.symm⟩
          · exact ⟨yA,xy⟩
      have mm := hmin x (hNA xN)
      have mx := hs (A.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht A x)
      have rn : r∉B.filter (G.Adj x) := fun h => rB (Finset.mem_filter.mp h).1
      rw [eq,Finset.card_insert_of_notMem rn] at mm mx
      rw [sizeAt_finset G hbn,hb]
      exact ⟨mm,mx⟩
    obtain ⟨cs,hcs,enc⟩ := graphExtension G A (k+1) d ht hs r front base nodup cover dl ha hnot hcount hmin sorted_
    exact ⟨r::front++base, d, encode G base, cs, nodup, cover, hu', by simpa only [show A.card-1-d=B.card by omega] using cls, hcs, enc, ⟨r, hr, rfl⟩⟩


abbrev WeightedRow := (Nat × Nat) × Nat

def rowScore (W : List WeightedRow) (x : Nat) : Nat :=
  ((W.filter (fun w => x &&& w.1.1 == 0)).map Prod.snd).sum

def rowCapacity (W : List WeightedRow) : Nat :=
  (W.map fun w => (5-w.1.2)*w.2).sum

def penalty (f : Nat → Bool) (x : Nat) := (f x).toNat

theorem rowScore_cons (w : WeightedRow) (W : List WeightedRow) (cs : List Nat) :
    (cs.map (rowScore (w::W))).sum =
    (cs.filter (fun x => x &&& w.1.1 == 0)).length*w.2 + (cs.map (rowScore W)).sum := by
  induction cs with
  | nil => simp
  | cons x cs ih =>
    by_cases e : x &&& w.1.1 = 0
    · simp [rowScore,e,Nat.succ_mul] at ih ⊢
      omega
    · simp [rowScore,e] at ih ⊢
      omega

theorem rowScore_le (b cs : List Nat) (W : List WeightedRow)
    (valid : ∀ w∈W,w.1∈inds b) (good : okContacts 6 (inds b) cs=true) :
    (cs.map (rowScore W)).sum ≤ rowCapacity W := by
  induction W with
  | nil =>
    have h : rowScore [] = fun _ => 0 := rfl
    simp [h,rowCapacity]
  | cons w W ih =>
    have sub := ih (fun t ht => valid t (.tail _ ht))
    have hm := of_decide_eq_true (List.all_eq_true.mp good w.1 (valid w (.head _)))
    have lecap : (cs.filter (fun x => x &&& w.1.1 == 0)).length ≤ 5-w.1.2 := by omega
    have lh := Nat.mul_le_mul_right w.2 lecap
    rw [rowScore_cons]
    change _ ≤ (5-w.1.2)*w.2 + rowCapacity W
    omega

theorem rowScore_ge (b : List Nat) (f : Nat → Bool) (edgeWeight extraWeight low : Nat) (W : List WeightedRow)
    (cs : List Nat) (h : ∀ x∈cs, low ≤ countBits b.length x * edgeWeight + penalty f x * extraWeight + rowScore W x) :
    cs.length*low ≤ (cs.map (countBits b.length)).sum * edgeWeight +
      (cs.map (penalty f)).sum * extraWeight + (cs.map (rowScore W)).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hh := ih (fun x hx => h x (.tail _ hx))
    have hc := h c (.head _)
    simp only [List.length_cons,Nat.succ_mul,List.map_cons,List.sum_cons,Nat.add_mul]
    omega


def dualCheckSimple (limit : Nat) (b : List Nat) (d edgeWeight low : Nat)
    (W : List WeightedRow) : Bool :=
  W.all (fun w => decide (w.1 ∈ inds b)) &&
  (usable 6 d b).all (fun x => decide (low ≤ countBits b.length x * edgeWeight + rowScore W x)) &&
  decide ((limit - edges_ b - d) * edgeWeight + rowCapacity W < d * low)

abbrev b3_0 : List Nat := [15,560,388,274,146,3,2,6,3,2,2,1,0]
abbrev b4_0 : List Nat := [7,24,130,145,3,2,6,3,2,2,1,0]
abbrev b4_1 : List Nat := [7,24,146,145,3,2,6,3,2,2,1,0]
abbrev b4_2 : List Nat := [7,24,194,145,3,2,6,3,2,2,1,0]
abbrev b4_3 : List Nat := [7,280,146,145,3,2,6,3,2,2,1,0]
abbrev b4_4 : List Nat := [7,280,194,137,3,2,6,3,2,2,1,0]
abbrev b4_5 : List Nat := [7,24,98,137,3,12,9,3,2,2,1,0]
abbrev b4_6 : List Nat := [7,132,268,137,3,12,9,3,2,2,1,0]
abbrev b4_7 : List Nat := [7,196,268,137,3,12,9,3,2,2,1,0]
abbrev b4_8 : List Nat := [7,388,258,134,3,12,9,3,2,2,1,0]
abbrev b4_9 : List Nat := [7,388,268,137,3,12,9,3,2,2,1,0]
abbrev b4_10 : List Nat := [15,296,196,140,73,1,6,3,2,2,1,0]
abbrev b4_11 : List Nat := [15,352,196,146,82,3,10,10,1,0,1,0]


set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
theorem smaller3 : (levels normalized 5 13 4).all (fun b => decide (b ∈ roots3)) = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 30000000 in
theorem smaller4 : (levels normalized 5 12 4).all (fun b => decide (b ∈ roots4)) = true := by
  decide +kernel


theorem viaDual40 (b cs : List Nat) (d edgeWeight low : Nat) (W : List WeightedRow)
    (ext : Extension 6 d b cs)
    (check : dualCheckSimple 39 b d edgeWeight low W = true) :
    40 ≤ edges_ (attach cs b) := by
  by_contra! small
  obtain ⟨len, mem, good⟩ := ext
  obtain ⟨both, last⟩ := Bool.and_eq_true_iff.mp check
  obtain ⟨valid, opts⟩ := Bool.and_eq_true_iff.mp both
  have upper := rowScore_le b cs W (fun w hw => of_decide_eq_true (List.all_eq_true.mp valid w hw)) good
  have lower := rowScore_ge b (fun _ => false) edgeWeight 0 low W cs (fun x hx => by
    have hx' := of_decide_eq_true (List.all_eq_true.mp opts x (mem x hx))
    simp only [Nat.mul_zero, Nat.add_zero]
    exact hx')
  simp only [Nat.mul_zero, Nat.add_zero] at lower
  rw [edges_attached, len] at small
  have e : (cs.map (countBits b.length)).sum ≤ 39 - edges_ b - d := by omega
  have he := Nat.mul_le_mul_right edgeWeight e
  have hl := of_decide_eq_true last
  rw [len] at lower
  omega


/-- Each row has score at least floor. A distinguished row can produce the
specified additional score, contradicting the sum of the witness capacities. -/
abbrev Featured40 := Nat × Nat × List WeightedRow

def featured40 (b : List Nat) (d : Nat) (c : Featured40) : Bool :=
  let (floor,extra,W) := c
  W.all (fun w => decide (w.1 ∈ inds b)) &&
    (usable 6 d b).all (fun x => decide (floor≤ rowScore W x)) &&
    decide (rowCapacity W < d*floor+extra)

def heavy40 (x : Nat) (c : Featured40) : Bool :=
  decide (c.1+c.2.1≤ rowScore c.2.2 x)

theorem featured40_sound {b cs : List Nat} {d : Nat} {c : Featured40}
    (ext : Extension 6 d b cs) (checked : featured40 b d c=true) {x : Nat}
    (hx : x∈cs) (enough : heavy40 x c=true) : False := by
  rcases c with ⟨floor,extra,W⟩
  obtain ⟨len, mem, good⟩ := ext
  obtain ⟨both, last⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨valid, opts⟩ := Bool.and_eq_true_iff.mp both
  have upper := rowScore_le b cs W (fun w hw => of_decide_eq_true (List.all_eq_true.mp valid w hw)) good
  obtain ⟨pre,post,eq⟩ := List.append_of_mem hx
  have run (xs : List Nat) (base : ∀ y∈xs,floor≤ rowScore W y) :
      xs.length*floor≤(xs.map (rowScore W)).sum := by
    induction xs with
    | nil => simp
    | cons y ys ih =>
      have a := base y (.head _)
      have tail := ih fun z hz => base z (.tail _ hz)
      simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.succ_mul]
      omega
  have each (y) (hy : y∈cs) := of_decide_eq_true (List.all_eq_true.mp opts y (mem y hy))
  have left := run pre fun y hy => each y (by rw [eq]; simp [hy])
  have right := run post fun y hy => each y (by rw [eq]; simp [hy])
  have plus := of_decide_eq_true enough
  change floor+extra≤ rowScore W x at plus
  have bad := of_decide_eq_true last
  rw [←len,eq] at bad
  rw [eq] at upper
  simp only [List.map_append,List.sum_append,List.map_cons,List.sum_cons] at upper
  simp only [List.length_append,List.length_cons,Nat.add_mul,Nat.succ_mul] at bad
  omega

theorem all_featured40 {b cs : List Nat} {d : Nat} (C : List Featured40)
    (ext : Extension 6 d b cs) (check : C.all (featured40 b d)=true)
    (coverage : (usable 6 d b).all (fun x => decide (4≤ countBits b.length x) ||
      C.any (heavy40 x))=true) (dense : 40 ≤ d+4*d+edges_ b) :
    40≤ edges_ (attach cs b) := by
  by_cases h : ∃ x∈cs, countBits b.length x<4
  · obtain ⟨x,hx,tiny⟩ := h
    have c := List.all_eq_true.mp coverage x (ext.2.1 x hx)
    simp only [Bool.or_eq_true,decide_eq_true_eq] at c
    obtain ⟨c,hc,eq⟩ := List.any_eq_true.mp (c.resolve_left (by omega))
    exact False.elim (featured40_sound ext (List.all_eq_true.mp check c hc) hx eq)
  · have bound (xs : List Nat) (hb : ∀ x∈xs, 4≤ countBits b.length x) :
        4*xs.length ≤ (xs.map (countBits b.length)).sum := by
      induction xs with
      | nil => simp
      | cons x xs ih =>
        have hd := hb x (.head _)
        have tl := ih (fun y hy => hb y (.tail _ hy))
        simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.mul_succ]
        omega
    have hsum := bound cs (by intro x hx; by_contra! small; exact h ⟨x,hx,small⟩)
    rw [edges_attached,←ext.1] at *
    omega
def b3_0_w40 : List WeightedRow := [((30,4),1),((204,4),1),((306,4),1),((1570,4),1),((1608,4),1),((2241,4),1),((2448,4),1),((3096,4),1),((3105,4),1),((4385,4),1),((4484,4),1),((4614,4),1),((4673,4),1)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem b3_0_cert40 : dualCheckSimple 39 b3_0 3 1 8 b3_0_w40 = true := by
  decide +kernel

theorem b3_0_bound40 (cs : List Nat) (ext : Extension 6 3 b3_0 cs) : 40 ≤ edges_ (attach cs b3_0) :=
  viaDual40 _ _ _ _ _ _ ext b3_0_cert40

def b4_1_w40 : List WeightedRow := [((14,3),5),((76,3),18),((108,4),35),((144,2),15),((200,3),18),((260,2),15),((272,2),19),((526,4),37),((556,4),4),((785,4),15),((786,4),26),((801,4),23),((804,4),23),((1121,4),34),((1128,4),8),((1162,4),32),((1169,4),23),((1170,4),14),((1217,4),4),((1224,4),35),((1546,4),15),((1553,4),23),((1554,4),12),((1576,4),34),((2145,4),15),((2148,4),32),((2194,4),46),((2240,3),7),((2241,4),35),((2310,4),46),((2321,4),26),((2322,4),1),((2337,4),12),((2340,4),14)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem b4_1_cert40 : dualCheckSimple 39 b4_1 4 61 434 b4_1_w40 = true := by
  decide +kernel

theorem b4_1_bound40 (cs : List Nat) (ext : Extension 6 4 b4_1 cs) : 40 ≤ edges_ (attach cs b4_1) :=
  viaDual40 _ _ _ _ _ _ ext b4_1_cert40

def b4_2_w40 : List WeightedRow := [((108,4),4),((142,4),4),((204,4),1),((785,4),1),((786,4),4),((800,3),1),((801,4),3),((1121,4),2),((1169,4),2),((1170,4),2),((1224,4),3),((1546,4),5),((1553,4),3),((1576,4),5),((2145,4),2),((2194,4),2),((2241,4),2),((2244,4),3),((2310,4),5),((2321,4),3),((2340,4),5)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem b4_2_cert40 : dualCheckSimple 39 b4_2 4 4 31 b4_2_w40 = true := by
  decide +kernel

theorem b4_2_bound40 (cs : List Nat) (ext : Extension 6 4 b4_2 cs) : 40 ≤ edges_ (attach cs b4_2) :=
  viaDual40 _ _ _ _ _ _ ext b4_2_cert40

def b4_3_w40 : List WeightedRow := [((76,3),1),((108,4),2),((138,3),4),((526,4),4),((786,4),4),((804,4),3),((1121,4),5),((1168,3),1),((1169,4),2),((1224,4),3),((1553,4),3),((1576,4),3),((2148,4),3),((2194,4),4),((2241,4),3),((2310,4),4),((2321,4),3)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem b4_3_cert40 : dualCheckSimple 39 b4_3 4 4 29 b4_3_w40 = true := by
  decide +kernel

theorem b4_3_bound40 (cs : List Nat) (ext : Extension 6 4 b4_3 cs) : 40 ≤ edges_ (attach cs b4_3) :=
  viaDual40 _ _ _ _ _ _ ext b4_3_cert40

def b4_4_w40 : List WeightedRow := [((14,3),1),((108,4),1),((146,3),1),((786,4),1),((808,4),1),((1121,4),1),((1216,3),1),((1544,3),1),((1553,4),1),((2193,4),1),((2244,4),1),((2310,4),1),((2337,4),1)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem b4_4_cert40 : dualCheckSimple 39 b4_4 4 1 8 b4_4_w40 = true := by
  decide +kernel

theorem b4_4_bound40 (cs : List Nat) (ext : Extension 6 4 b4_4 cs) : 40 ≤ edges_ (attach cs b4_4) :=
  viaDual40 _ _ _ _ _ _ ext b4_4_cert40

def b4_5_w40 : List WeightedRow := [((108,4),13),((144,2),6),((164,3),2),((778,4),2),((784,3),4),((785,4),6),((786,4),6),((833,4),2),((840,4),13),((1038,4),5),((1068,4),3),((1158,4),1),((1185,4),6),((1188,4),7),((1546,4),6),((1553,4),6),((1554,4),1),((2145,4),5),((2148,4),3),((2182,4),6),((2209,4),1),((2212,4),7),((2321,4),1),((2322,4),6),((2369,4),6)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem b4_5_cert40 : dualCheckSimple 39 b4_5 4 12 79 b4_5_w40 = true := by
  decide +kernel

theorem b4_5_bound40 (cs : List Nat) (ext : Extension 6 4 b4_5 cs) : 40 ≤ edges_ (attach cs b4_5) :=
  viaDual40 _ _ _ _ _ _ ext b4_5_cert40

def b4_6_w40 : List WeightedRow := [((104,3),1),((106,4),1),((148,3),1),((270,4),2),((584,3),1),((788,4),2),((833,4),1),((840,4),1),((1066,4),1),((1158,4),2),((1172,4),1),((1185,4),2),((1548,4),2),((1553,4),2),((2145,4),2),((2192,3),1),((2193,4),1),((2210,4),2),((2321,4),2),((2370,4),2)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem b4_6_cert40 : dualCheckSimple 39 b4_6 4 3 19 b4_6_w40 = true := by
  decide +kernel

theorem b4_6_bound40 (cs : List Nat) (ext : Extension 6 4 b4_6 cs) : 40 ≤ edges_ (attach cs b4_6) :=
  viaDual40 _ _ _ _ _ _ ext b4_6_cert40

def b4_7_w40 : List WeightedRow := [((14,3),3),((106,4),19),((134,3),8),((148,3),6),((780,4),7),((785,4),12),((788,4),16),((833,4),6),((840,4),16),((1038,4),7),((1066,4),4),((1172,4),5),((1185,4),8),((1186,4),13),((1548,4),9),((1553,4),8),((2145,4),14),((2146,4),5),((2192,3),2),((2193,4),6),((2210,4),15),((2320,3),8),((2368,3),5),((2369,4),2)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem b4_7_cert40 : dualCheckSimple 39 b4_7 4 16 119 b4_7_w40 = true := by
  decide +kernel

theorem b4_7_bound40 (cs : List Nat) (ext : Extension 6 4 b4_7 cs) : 40 ≤ edges_ (attach cs b4_7) :=
  viaDual40 _ _ _ _ _ _ ext b4_7_cert40

def b4_8_w40 : List WeightedRow := [((102,4),1),((142,4),1),((270,4),1),((792,4),1),((833,4),1),((836,4),1),((1176,4),1),((1185,4),1),((1188,4),1),((1548,4),1),((1553,4),1),((2145,4),1),((2193,4),1),((2210,4),1),((2321,4),1),((2370,4),1)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem b4_8_cert40 : dualCheckSimple 39 b4_8 4 1 8 b4_8_w40 = true := by
  decide +kernel

theorem b4_8_bound40 (cs : List Nat) (ext : Extension 6 4 b4_8 cs) : 40 ≤ edges_ (attach cs b4_8) :=
  viaDual40 _ _ _ _ _ _ ext b4_8_cert40

def b4_9_w40 : List WeightedRow := [((106,4),1),((134,3),1),((270,4),1),((788,4),1),((840,4),1),((1064,3),1),((1172,4),1),((1185,4),1),((1548,4),1),((1553,4),1),((2145,4),1),((2193,4),1),((2210,4),1),((2321,4),1),((2370,4),1)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem b4_9_cert40 : dualCheckSimple 39 b4_9 4 1 8 b4_9_w40 = true := by
  decide +kernel

theorem b4_9_bound40 (cs : List Nat) (ext : Extension 6 4 b4_9 cs) : 40 ≤ edges_ (attach cs b4_9) :=
  viaDual40 _ _ _ _ _ _ ext b4_9_cert40

def b4_10_w40 : List WeightedRow := [((30,4),1),((86,4),1),((778,4),1),((808,4),1),((1185,4),1),((1232,4),1),((1560,4),1),((1569,4),1),((2241,4),1),((2244,4),1),((2310,4),1),((2337,4),1)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem b4_10_cert40 : dualCheckSimple 39 b4_10 4 0 4 b4_10_w40 = true := by
  decide +kernel

theorem b4_10_bound40 (cs : List Nat) (ext : Extension 6 4 b4_10 cs) : 40 ≤ edges_ (attach cs b4_10) :=
  viaDual40 _ _ _ _ _ _ ext b4_10_cert40

def b4_11_w40 : List WeightedRow := []

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem b4_11_cert40 : dualCheckSimple 39 b4_11 4 1 3 b4_11_w40 = true := by
  decide +kernel

theorem b4_11_bound40 (cs : List Nat) (ext : Extension 6 4 b4_11 cs) : 40 ≤ edges_ (attach cs b4_11) :=
  viaDual40 _ _ _ _ _ _ ext b4_11_cert40

def feature0 : Featured40 := (48,15,[((108,4),5),((142,4),11),((526,4),8),((556,4),10),((774,4),2),((785,4),10),((786,4),5),((801,4),9),((804,4),2),((1121,4),11),((1162,4),8),((1169,4),4),((1170,4),4),((1217,4),8),((1224,4),7),((1546,4),10),((1553,4),7),((1576,4),11),((2145,4),8),((2148,4),10),((2194,4),7),((2241,4),10),((2244,4),11),((2310,4),9),((2321,4),5),((2322,4),10),((2337,4),2),((2340,4),2)])

def feature1 : Featured40 := (8,5,[((108,4),1),((204,4),4),((774,4),3),((786,4),1),((801,4),2),((804,4),1),((1128,4),4),((1169,4),1),((1170,4),1),((1224,4),1),((1553,4),2),((1554,4),3),((2145,4),3),((2193,4),3),((2194,4),2),((2310,4),2),((2321,4),1),((2340,4),1)])

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem b4_0_bound40 (cs : List Nat) (ext : Extension 6 4 b4_0 cs) : 40≤ edges_ (attach cs b4_0) :=
  all_featured40 [feature0,feature1] ext (by decide +kernel) (by decide +kernel) (by decide +kernel)
open SimpleGraph Finset RamseyNumbers

/-- Lift the finite contact checks on the 13- and 12-vertex antineighborhoods
to the density bound for all 17-vertex graphs. -/
theorem density17_of_checks
    (check : ∀ (d : ℕ) (b cs : List ℕ), 3≤ d → d≤4 →
      b∈levels normalized 5 (16-d) 4 → Extension 6 d b cs → 40≤ edges_ (attach cs b))
    (G : SimpleGraph (Fin 17)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 6) : 40 ≤ G.edgeFinset.card := by
  have hmin (v : Fin 17) : 3≤ G.degree v := by
    have h := OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1.nonneighbors_lt
      OMA.Ramsey37Density.fourteen_works G ht hi v
    rw [G.degree_compl,Fintype.card_fin] at h
    omega
  classical
  by_contra! hsmall
  let U : Finset (Fin 17) := Finset.univ
  have bounded : Small G U 6 := by
    intro I _ hI
    by_contra! hc
    exact (hi.mono hc) I ⟨hI, rfl⟩
  have low : U.Nonempty → ∃ x ∈ U, (U.filter (G.Adj x)).card ≤ 4 := by
    intro _
    by_contra! hn
    have h5 (x : Fin 17) : 5 ≤ G.degree x := by
      have hh := hn x (Finset.mem_univ _)
      simp only [U, ← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree] at hh
      omega
    have w := Finset.sum_le_sum (s := U) (f := fun _ => 5) (g := fun x => G.degree x) (fun x _ => h5 x)
    have tot := G.sum_degrees_eq_twice_card_edges
    simp [U] at w
    omega
  have hn (l : List (Fin 17)) := relabel_real G (renumber (encode G l)) l
  obtain ⟨vs, d, b, cs, hv, cover, hd, hb, hcs, enc, ⟨r, _, hr⟩⟩ :=
    rootSplitting G ht normalized hn 5 U (by simp [U]) 4 bounded low
  have hdlb : 3 ≤ d := by
    have hmr := hmin r
    simp only [U, ← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree] at hr
    omega
  have h40 := check d b cs hdlb hd (by simpa [U] using hb) hcs
  rw [← enc] at h40
  have dg : degrees (encode G vs) = vs.map (fun x => G.degree x) := by
    rw [degrees_encode]
    apply List.map_congr_left
    intro x _
    rw [sizeAt_finset G hv, cover]
    simp only [U, ← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree]
  have w := List.sum_toFinset (fun x => G.degree x) hv
  rw [cover] at w
  have tot := G.sum_degrees_eq_twice_card_edges
  have hh : 80 ≤ (degrees (encode G vs)).sum := by rw [energy]; omega
  rw [dg, ← w] at hh
  exact (by change 80 ≤ ∑ i, G.degree i at hh; omega : False)

theorem all_contacts40 (d : Nat) (b cs : List Nat) (minimum : 3≤ d) (maximum : d≤4)
    (covered : b∈levels normalized 5 (16-d) 4) (ext : Extension 6 d b cs) :
    40≤ edges_ (attach cs b) := by
  interval_cases d
  · have ok := of_decide_eq_true (List.all_eq_true.mp smaller3 b covered)
    simp only [roots3,List.mem_cons,List.not_mem_nil,or_false] at ok
    subst ok
    exact b3_0_bound40 cs ext
  · have ok := of_decide_eq_true (List.all_eq_true.mp smaller4 b covered)
    simp only [roots4,List.mem_cons,List.not_mem_nil,or_false] at ok
    rcases ok with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact b4_0_bound40 cs ext
    · exact b4_1_bound40 cs ext
    · exact b4_2_bound40 cs ext
    · exact b4_3_bound40 cs ext
    · exact b4_4_bound40 cs ext
    · exact b4_5_bound40 cs ext
    · exact b4_6_bound40 cs ext
    · exact b4_7_bound40 cs ext
    · exact b4_8_bound40 cs ext
    · exact b4_9_bound40 cs ext
    · exact b4_10_bound40 cs ext
    · exact b4_11_bound40 cs ext

/-- The extremal Ramsey edge lower bound e(3,6;17) ≥ 40. -/
theorem density17_40 (G : SimpleGraph (Fin 17)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 6) : 40 ≤ G.edgeFinset.card :=
  density17_of_checks all_contacts40 G ht hi
end OMA.RamseyFinite
end RamseyFiniteSection
end

section
namespace FiveLP
open OMA.RamseyFinite

/-- An independent set of size k can be missed by at most 6-k of the five contacts. -/
theorem score_upper (b cs : List Nat) (W : List WeightedRow)
    (valid : ∀ t∈W,t.1∈inds b) (good : okContacts 7 (inds b) cs=true) :
    (cs.map (rowScore W)).sum ≤ cap W := by
  induction W with
  | nil =>
    have h : rowScore [] = fun _ => 0 := rfl
    simp [h,cap]
  | cons t W ih =>
    have h := ih (fun a ha => valid a (.tail _ ha))
    have hm := of_decide_eq_true (List.all_eq_true.mp good t.1 (valid t (.head _)))
    have cnt : (cs.filter (fun x => x &&& t.1.1 == 0)).length ≤ 6-t.1.2 := by omega
    have weighted := Nat.mul_le_mul_right t.2 cnt
    rw [rowScore_cons]
    change _ ≤ (6-t.1.2)*t.2 + cap W
    omega

private theorem all_floor (f : Nat → Nat) (lo : Nat) (l : List Nat)
    (h : ∀ x∈l,lo≤ f x) : l.length*lo≤(l.map f).sum := by
  induction l with
  | nil => simp
  | cons y l ih =>
    have a := h y (.head _)
    have b := ih (fun x hx => h x (.tail _ hx))
    simp only [List.length_cons,Nat.succ_mul,List.map_cons,List.sum_cons]
    omega

private theorem exceptional_score (f : Nat→Nat) (lo : Nat) (l : List Nat) (x : Nat)
    (low : ∀ y∈l, lo≤ f y) (mem : x∈l) : (l.length-1)*lo + f x ≤ (l.map f).sum := by
  obtain ⟨u,v,rfl⟩ := List.mem_iff_append.mp mem
  have l₁ := all_floor f lo u (fun y hy => low y (List.mem_append_left _ hy))
  have l₂ := all_floor f lo v (fun y hy => low y (List.mem_append_right _ (.tail _ hy)))
  simp only [List.length_append,List.length_cons,List.map_append,List.map_cons,List.sum_append,
    List.sum_cons,Nat.add_succ,Nat.succ_sub_one,Nat.add_mul]
  omega

theorem from_checks (b cs pool : List Nat) (W : List WeightedRow) (factor low budget : Nat)
    (valid : ∀ t∈W,t.1∈inds b)
    (enough : ∀ x∈usable 7 3 b,
      let score := countBits b.length x*factor + rowScore W x
      low≤ score ∧ (4*low+score≤ budget*factor+cap W → x∈pool))
    (rows : ∀ x∈cs,x∈usable 7 3 b) (len : cs.length=5) (good : okContacts 7 (inds b) cs=true)
    (cost : (cs.map (countBits b.length)).sum ≤ budget) : ∀ x∈cs,x∈pool := by
  let f (x : Nat) := countBits b.length x*factor+rowScore W x
  have sum_rule (l : List Nat) :
      (l.map f).sum=(l.map (countBits b.length)).sum*factor+(l.map (rowScore W)).sum := by
    induction l with
    | nil => simp
    | cons y l ih => simp only [List.map_cons,List.sum_cons,Nat.add_mul,ih,f]; omega
  have bounded := score_upper b cs W valid good
  have bounded' := Nat.mul_le_mul_right factor cost
  intro x hx
  apply (enough x (rows x hx)).2
  have ceil := exceptional_score f low cs x (fun y hy => (enough y (rows y hy)).1) hx
  rw [len,sum_rule] at ceil
  change 4*low+(countBits b.length x*factor+rowScore W x)≤_ at ceil
  omega
end FiveLP
end

section
namespace FiveLP
open OMA.RamseyFinite
theorem enum_eq (b : List Nat) : Generated35.inds b=inds b := by
  induction b with
  | nil => rfl
  | cons x xs ih => simp only [Generated35.inds,inds,ih]; rfl
theorem options_eq (b : List Nat) : Generated35.usable 7 3 b=usable 7 3 b := by
  simp only [Generated35.usable,usable,enum_eq]
theorem weight_eq (n x : Nat) : Generated35.countBits n x=countBits n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [Generated35.countBits,countBits,ih]

theorem pool_of_check (i : Fin 8) (ok : (witnesses i && rowsOK i)=true) (cs : List Nat)
    (mem : ∀ x∈cs,x∈usable 7 3 (SparseFifteen.adj i))
    (len : cs.length=5) (test : okContacts 7 (inds (SparseFifteen.adj i)) cs=true)
    (cost : (cs.map (countBits (SparseFifteen.adj i).length)).sum≤ budget i) :
    ∀x∈cs,x∈pool i := by
  obtain ⟨val,opts⟩ := Bool.and_eq_true_iff.mp ok
  apply from_checks (SparseFifteen.adj i) cs (pool i) (weights i) (scale i) (floor i) (budget i) _ _ mem len test cost
  · intro t ht
    rw [←enum_eq]
    exact of_decide_eq_true (List.all_eq_true.mp val t ht)
  · intro x hx
    rw [←options_eq] at hx
    have rule := of_decide_eq_true (List.all_eq_true.mp opts x hx)
    simpa only [rowOK,weight_eq, value,rowScore] using rule
end FiveLP
end

section
namespace FiveLP
set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem ok0 : (witnesses 0 && rowsOK 0) = true := by decide +kernel
end FiveLP
end

section
namespace FiveLP
set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem ok1 : (witnesses 1 && rowsOK 1) = true := by decide +kernel
end FiveLP
end

section
namespace FiveLP
set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem ok2 : (witnesses 2 && rowsOK 2) = true := by decide +kernel
end FiveLP
end

section
namespace FiveLP
set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem ok3 : (witnesses 3 && rowsOK 3) = true := by decide +kernel
end FiveLP
end

section
namespace FiveLP
set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem ok4 : (witnesses 4 && rowsOK 4) = true := by decide +kernel
end FiveLP
end

section
namespace FiveLP
set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem ok5 : (witnesses 5 && rowsOK 5) = true := by decide +kernel
end FiveLP
end

section
namespace FiveLP
set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem ok6 : (witnesses 6 && rowsOK 6) = true := by decide +kernel
end FiveLP
end

section
namespace FiveLP
set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
theorem ok7 : (witnesses 7 && rowsOK 7) = true := by decide +kernel
end FiveLP
end

section
namespace FiveLP
theorem checked (i : Fin 8) : (witnesses i && rowsOK i)=true := by
  fin_cases i
  · exact ok0
  · exact ok1
  · exact ok2
  · exact ok3
  · exact ok4
  · exact ok5
  · exact ok6
  · exact ok7
end FiveLP
end

section
namespace FP32
def bits : List Bool → Nat
  | [] => 0
  | b::bs => 2 * bits bs + b.toNat
def ind0 (p : Nat × Nat) : Nat × Nat := (2*p.1,p.2)
def ind1 (p : Nat × Nat) : Nat × Nat := (2*p.1+1,p.2+1)
def inds : List Nat → List (Nat × Nat)
  | [] => [(0,0)]
  | m::rows =>
    let t := inds rows
    t.map ind0 ++ (t.filter fun p => m &&& p.1 == 0).map ind1
def countBits : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,x => (x%2) + countBits n (x/2)
def edges_ : List Nat → Nat
  | [] => 0
  | m::t => countBits t.length m + edges_ t
def usable (k d : Nat) (base : List Nat) : List Nat :=
  ((inds base).filter fun p => d ≤ p.2+1 && p.2+1 < k).map Prod.fst
def shifted : List Nat → List Nat
  | [] => []
  | s::ss => 2 ^ ss.length * s :: shifted ss
def attach (blocks base : List Nat) : List Nat :=
  (2 ^ blocks.length - 1) :: (shifted blocks ++ base)
abbrev WeightedRow := (Nat × Nat) × Nat
def rowScore (W : List WeightedRow) (x : Nat) : Nat :=
  ((W.filter (fun w => x &&& w.1.1 == 0)).map Prod.snd).sum
def rowCapacity (W : List WeightedRow) : Nat :=
  (W.map fun w => (5-w.1.2)*w.2).sum
def dualCheckSimple (limit : Nat) (b : List Nat) (d edgeWeight low : Nat)
    (W : List WeightedRow) : Bool :=
  W.all (fun w => decide (w.1 ∈ inds b)) &&
  (usable 6 d b).all (fun x => decide (low ≤ countBits b.length x * edgeWeight + rowScore W x)) &&
  decide ((limit - edges_ b - d) * edgeWeight + rowCapacity W < d * low)
def swapAt {α : Type _} : Nat → List α → List α
  | 0,x::y::xs => y::x::xs
  | i+1,x::xs => x::swapAt i xs
  | _,l => l
def exchange : Nat → Nat → Nat
  | 0,x => 4*(x/4)+2*(x%2)+((x/2)%2)
  | i+1,x => 2*exchange i (x/2)+x%2
def swapCode : Nat → List Nat → List Nat
  | 0,p::q::rs => (p%2+2*q)::(p/2)::rs
  | i+1,p::rs => exchange i p :: swapCode i rs
  | _,l => l
def relabel (swaps rows : List Nat) :=
  swaps.foldl (fun l i => if i+2≤ l.length then swapCode i l else l) rows
structure TrioAtom where
  mask : Nat
  cost : Nat
  miss4 : Nat
  miss3 : Nat
  later : Nat
deriving Inhabited
structure TriFeature where
  subset : Nat
  blocked : Nat
deriving Inhabited
def tableBits {α : Type _} (xs : List α) (pred : α → Bool) := bits (xs.map pred)
def missWord (sets : List Nat) (x : Nat) := tableBits sets (fun s=> x &&& s == 0)
def allowedPair (a b : TrioAtom) := decide (a.mask≤ b.mask) && (a.miss4 &&& b.miss4 == 0)
def fitMask (xs : List TrioAtom) (k : Nat) := tableBits xs (fun a=> decide (a.cost≤ k))
def removeHits (fs : Array TriFeature) : Nat → Nat → Nat → Nat
  | 0,_,pool => pool
  | t+1,sel,pool => if sel=0 || pool=0 then pool else
    let i := sel.log2
    let bad := (fs[i]?.getD default).blocked
    removeHits fs t (sel % (2^i)) (pool ^^^ (pool &&& bad))
def eachBit (fn : Nat → Bool) : Nat → Nat → Bool
  | 0,_ => true
  | s+1,pool => if pool=0 then true else
    let i := pool.log2
    fn i && eachBit fn s (pool % (2^i))
def trioTest (as_ : List TrioAtom) (fs : Array TriFeature) (costs : Array Nat) (budget : Nat)
    (done_ : Nat → Nat → Nat → Bool) :=
  as_.all fun x => as_.all fun y =>
    if allowedPair x y && (x.cost+y.cost≤ budget) then
      let pool := x.later &&& y.later &&& costs[budget-x.cost-y.cost]?.getD 0
      let live := removeHits fs fs.size (x.miss3 &&& y.miss3) pool
      eachBit (fun k=> done_ x.mask y.mask (as_[k]?.getD default).mask) as_.length live
    else true
def trioValidated (b : List Nat) (as_ : List TrioAtom) (quads : List Nat) (fs : Array TriFeature)
    (costs : Array Nat) (budget : Nat) :=
  (quads.all (fun s=> decide ((s,4)∈inds b))) &&
  (fs.toList.all (fun f=> decide ((f.subset,3)∈inds b) && (f.blocked == tableBits as_ (fun z=> z.mask &&& f.subset == 0)))) &&
  (as_.all (fun a=> a.cost == countBits b.length a.mask && a.miss4 == missWord quads a.mask &&
    a.miss3 == missWord (fs.toList.map TriFeature.subset) a.mask && a.later == tableBits as_ (allowedPair a))) &&
  ((List.range (budget+1)).all (fun k=> decide (costs[k]?=some (fitMask as_ k)))) &&
  ((usable 6 3 b).all (fun x=> decide (x∈as_.map TrioAtom.mask)))
def compactAtoms (n : Nat) (masks quads threes : List Nat) : List TrioAtom :=
  let first := masks.map fun m =>
    (⟨m, countBits n m, missWord quads m, missWord threes m, 0⟩ : TrioAtom)
  first.map fun a => { a with later := tableBits first (allowedPair a) }
def compactFeatures (masks threes : List Nat) : Array TriFeature :=
  (threes.map fun s => (⟨s,tableBits masks (fun z => z &&& s == 0)⟩ : TriFeature)).toArray
def compactCosts (atoms : List TrioAtom) (budget : Nat) : Array Nat :=
  ((List.range (budget+1)).map (fitMask atoms)).toArray
def pairCheck (b : List Nat) :=
  let q := ((inds b).filter fun p => p.2 == 4).map Prod.fst
  let rows := (usable 6 2 b).map fun x => (x,countBits b.length x,missWord q x)
  rows.all fun x => rows.all fun y =>
    decide (x.2.1 + y.2.1 ≤ 32 - edges_ b - 2 → x.2.2 &&& y.2.2 ≠ 0)
end FP32
end

section
namespace FiveIso
def target (i : Fin 4) : List Nat :=
  match i.val with
  | 0 => [229544,82088,12417,17536,16784,2244,4264,680,1092,145,4,17,4,1,3,0,8,4,2,1,0]
  | 1 => [229544,65704,45185,9344,16784,1220,4264,424,1092,81,68,1,4,1,1,2,8,4,2,1,0]
  | 2 => [229544,49320,12417,9344,16784,4292,4264,1192,1092,273,68,17,4,1,1,0,8,4,2,1,0]
  | _ => [229544,16552,28801,17536,16784,2244,4264,680,1092,17,132,1,4,5,1,4,8,4,2,1,0]

def outputs (i : Fin 8) : List (List Nat) :=
  match i.val with
  | 0 => [[1030,6406,8337,8961,18465],[1030,6406,12353,16529,17153],[1033,6409,8338,8962,18466],[1033,6409,12354,16530,17154],[1169,1542,6150,8449,18721],[1169,1542,6150,8513,18689],[1169,1542,6150,12545,16673],[1169,1542,6150,12609,16641],[1169,4102,8449,17926,18721],[1169,4102,8513,17926,18689],[1170,1545,6153,8450,18722],[1170,1545,6153,8514,18690],[1170,1545,6153,12546,16674],[1170,1545,6153,12610,16642],[1170,4105,8450,17929,18722],[1170,4105,8514,17929,18690],[1542,6150,8337,8961,18465],[1542,6150,8449,9361,18465],[1542,6150,12353,16529,17153],[1542,6150,12353,16641,17553],[1545,6153,8338,8962,18466],[1545,6153,8450,9362,18466],[1545,6153,12354,16530,17154],[1545,6153,12354,16642,17554],[4102,8337,8961,17926,18465],[4102,8449,9361,17926,18465],[4105,8338,8962,17929,18466],[4105,8450,9362,17929,18466],[4358,8337,8961,17414,18465],[4361,8338,8962,17417,18466]]
  | 1 => [[1030,6406,12353,16529,17153],[1169,1542,6150,8513,18689],[1169,1542,6150,12609,16641],[1169,4102,8513,17926,18689],[1542,6150,12353,16529,17153],[1542,6150,12353,16641,17553]]
  | 2 => [[777,1030,6406,8209,18481],[777,1030,6406,8273,18449],[777,1030,6406,12305,16433],[777,1030,6406,12369,16401],[777,1542,6150,8209,18481],[777,1542,6150,8273,18449],[777,1542,6150,12305,16433],[777,1542,6150,12369,16401],[777,4102,8209,17926,18481],[777,4102,8273,17926,18449],[777,4358,8209,17414,18481],[777,4358,8273,17414,18449],[1030,6406,8209,8969,18465],[1030,6406,8337,8961,18465],[1030,6406,12353,16401,17161],[1030,6406,12353,16529,17153],[1169,1542,6150,8449,18721],[1169,1542,6150,8513,18689],[1169,1542,6150,12545,16673],[1169,1542,6150,12609,16641],[1169,4102,8449,17926,18721],[1169,4102,8513,17926,18689],[1542,6150,8209,8969,18465],[1542,6150,8337,8961,18465],[1542,6150,8449,9361,18465],[1542,6150,8457,9233,18465],[1542,6150,12353,16401,17161],[1542,6150,12353,16529,17153],[1542,6150,12353,16641,17553],[1542,6150,12353,16649,17425],[4102,8209,8969,17926,18465],[4102,8337,8961,17926,18465],[4102,8449,9361,17926,18465],[4102,8457,9233,17926,18465],[4358,8209,8969,17414,18465],[4358,8337,8961,17414,18465]]
  | _ => []

structure Move where
  base : Fin 8
  contacts : List Nat
  rep : Fin 4
  steps : List Nat

def valid (m : Move) : Bool :=
  FP32.relabel m.steps (FP32.attach m.contacts (SparseFifteen.adj m.base)) == target m.rep

def key (m : Move) : Nat × List Nat := (m.base.val,m.contacts)

end FiveIso
end

section
namespace FP32
theorem bit_form (b : Bool) (n : Nat) : Nat.bit b n = 2 * n + b.toNat := by
  cases b <;> simp [Nat.bit, Nat.two_mul]
theorem and_mask {V : Type*} (vs : List V) (f g : V → Bool) :
    bits (vs.map f) &&& bits (vs.map g) = 0 ↔ ∀ x ∈ vs, f x = true → g x = false := by
  induction vs with
  | nil => simp [bits]
  | cons a l ih =>
    simp only [List.map_cons, bits, ← bit_form, Nat.land_bit, List.forall_mem_cons]
    rw [bit_form]
    cases f a <;> cases g a <;> simp [ih]
theorem half_step (x : Nat) : (2*x+1)/2=x := by omega
def okContacts (k : Nat) (isets : List (Nat × Nat)) (cs : List Nat) : Bool :=
  isets.all fun p => p.2 + (cs.filter fun v => v &&& p.1 == 0).length < k
theorem count_shift (n a j : Nat) : countBits (j+n) (2^j*a)=countBits n a := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : 2^(j+1)*a=2*(2^j*a) := by rw [pow_succ]; ring
    rw [Nat.succ_add,countBits,e]
    simp [ih]
theorem count_full (d n : Nat) : countBits (d+n) (2^d-1)=d := by
  induction d with
  | zero =>
    have h (t : Nat) : countBits t 0=0 := by induction t with | zero => rfl | succ k ih => simp [countBits,ih]
    simp [h]
  | succ d ih =>
    have hp : 0 < 2^d := Nat.two_pow_pos _
    have split : 2^(d+1)-1=2*(2^d-1)+1 := by rw [pow_succ]; omega
    rw [Nat.succ_add,countBits,split,half_step,ih]
    omega
theorem shifted_length (xs : List Nat) : (shifted xs).length=xs.length := by
  induction xs with | nil => rfl | cons a xs ih => simp [shifted,ih]
theorem edges_attached (xs b : List Nat) : edges_ (attach xs b) =
    xs.length + (xs.map (countBits b.length)).sum + edges_ b := by
  have h (ls : List Nat) : edges_ (shifted ls++b)=(ls.map (countBits b.length)).sum+edges_ b := by
    induction ls with
    | nil => simp [shifted]
    | cons a ls ih => simp [shifted,edges_,shifted_length,count_shift,ih,Nat.add_assoc]
  simp [attach,edges_,shifted_length,count_full,h,Nat.add_assoc]
def Extension (k d : Nat) (b cs : List Nat) : Prop :=
  cs.length = d ∧ (∀ x ∈ cs, x ∈ usable k d b) ∧ okContacts k (inds b) cs = true
def penalty (f : Nat → Bool) (x : Nat) := (f x).toNat
theorem rowScore_cons (w : WeightedRow) (W : List WeightedRow) (cs : List Nat) :
    (cs.map (rowScore (w::W))).sum =
    (cs.filter (fun x => x &&& w.1.1 == 0)).length*w.2 + (cs.map (rowScore W)).sum := by
  induction cs with
  | nil => simp
  | cons x cs ih =>
    by_cases e : x &&& w.1.1 = 0
    · simp [rowScore,e,Nat.succ_mul] at ih ⊢
      omega
    · simp [rowScore,e] at ih ⊢
      omega
theorem rowScore_le (b cs : List Nat) (W : List WeightedRow)
    (valid : ∀ w∈W,w.1∈inds b) (good : okContacts 6 (inds b) cs=true) :
    (cs.map (rowScore W)).sum ≤ rowCapacity W := by
  induction W with
  | nil =>
    have h : rowScore [] = fun _ => 0 := rfl
    simp [h,rowCapacity]
  | cons w W ih =>
    have sub := ih (fun t ht => valid t (.tail _ ht))
    have hm := of_decide_eq_true (List.all_eq_true.mp good w.1 (valid w (.head _)))
    have lecap : (cs.filter (fun x => x &&& w.1.1 == 0)).length ≤ 5-w.1.2 := by omega
    have lh := Nat.mul_le_mul_right w.2 lecap
    rw [rowScore_cons]
    change _ ≤ (5-w.1.2)*w.2 + rowCapacity W
    omega
theorem rowScore_ge (b : List Nat) (f : Nat → Bool) (edgeWeight extraWeight low : Nat) (W : List WeightedRow)
    (cs : List Nat) (h : ∀ x∈cs, low ≤ countBits b.length x * edgeWeight + penalty f x * extraWeight + rowScore W x) :
    cs.length*low ≤ (cs.map (countBits b.length)).sum * edgeWeight +
      (cs.map (penalty f)).sum * extraWeight + (cs.map (rowScore W)).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hh := ih (fun x hx => h x (.tail _ hx))
    have hc := h c (.head _)
    simp only [List.length_cons,Nat.succ_mul,List.map_cons,List.sum_cons,Nat.add_mul]
    omega
theorem viaDual33 (b cs : List Nat) (d edgeWeight low : Nat) (W : List WeightedRow)
    (ext : Extension 6 d b cs)
    (check : dualCheckSimple 32 b d edgeWeight low W = true) :
    33 ≤ edges_ (attach cs b) := by
  by_contra! small
  obtain ⟨len, mem, good⟩ := ext
  obtain ⟨both, last⟩ := Bool.and_eq_true_iff.mp check
  obtain ⟨valid, opts⟩ := Bool.and_eq_true_iff.mp both
  have upper := rowScore_le b cs W (fun w hw => of_decide_eq_true (List.all_eq_true.mp valid w hw)) good
  have lower := rowScore_ge b (fun _ => false) edgeWeight 0 low W cs (fun x hx => by
    have hx' := of_decide_eq_true (List.all_eq_true.mp opts x (mem x hx))
    simp only [Nat.mul_zero, Nat.add_zero]
    exact hx')
  simp only [Nat.mul_zero, Nat.add_zero] at lower
  rw [edges_attached, len] at small
  have e : (cs.map (countBits b.length)).sum ≤ 32 - edges_ b - d := by omega
  have he := Nat.mul_le_mul_right edgeWeight e
  have hl := of_decide_eq_true last
  rw [len] at lower
  omega
end FP32
end

section
namespace FP32
theorem bits_lt (b : List Bool) : bits b < 2 ^ b.length := by
  induction b with
  | nil => decide
  | cons a l ih => cases a <;> simp [bits, pow_succ] <;> omega
theorem testbit_of_get {α : Type*} (xs : List α) (fn : α→Bool) (i : Nat) {a : α}
    (h : xs[i]?=some a) : (tableBits xs fn).testBit i=fn a := by
  induction xs generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simp at h; subst a; cases e : fn x <;> simp [tableBits,bits,e,Nat.testBit]
    | succ i =>
      have he := ih i (by simpa using h)
      change (2*bits (xs.map fn)+(fn x).toNat).testBit (i+1)=fn a
      rw [Nat.testBit_add_one]
      cases hh : fn x <;> simpa [hh,half_step,tableBits] using he
theorem visit_hits (fn : Nat → Bool) (n pool i : Nat) (hi : pool.testBit i=true)
    (sz : pool<2^n) (h : eachBit fn n pool=true) : fn i=true := by
  induction n generalizing pool with
  | zero =>
    have e : pool=0 := by simpa using sz
    simp [e] at hi
  | succ n ih =>
    have nz : pool≠0 := by intro e; simp [e] at hi
    simp only [eachBit,nz,if_false,Bool.and_eq_true_iff] at h
    by_cases e : i=pool.log2
    · simpa [e] using h.1
    have upper : i≤ pool.log2 := by
      by_contra! hn
      have lt : pool<2^i := (Nat.lt_log2_self (n:=pool)).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
      simp [Nat.testBit_lt_two_pow lt] at hi
    have logle : pool.log2≤ n := by
      by_contra! hn
      have lp := Nat.log2_self_le nz
      have mono := Nat.pow_le_pow_right (n:=2) (by decide) (show n+1≤ pool.log2 by omega)
      omega
    apply ih (pool % 2^pool.log2)
    · simp [Nat.testBit_mod_two_pow,show i< pool.log2 by omega,hi]
    · exact (Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le (Nat.pow_le_pow_right (by decide) logle)
    · exact h.2
theorem remove_keeps (fs : Array TriFeature) (fuel sel pool j : Nat)
    (bit : pool.testBit j=true)
    (safe : ∀ i,sel.testBit i=true → ((fs[i]?.getD default).blocked).testBit j=false) :
    (removeHits fs fuel sel pool).testBit j=true := by
  induction fuel generalizing sel pool with
  | zero => exact bit
  | succ fuel ih =>
    simp only [removeHits]
    split
    · exact bit
    next h =>
      have nz : sel≠0 := by intro e; simp [e] at h
      have v := safe sel.log2 (Nat.testBit_log2 nz)
      apply ih
      · simp [Nat.testBit_xor,Nat.testBit_and,bit,v]
      · intro i hi
        apply safe i
        simp only [Nat.testBit_mod_two_pow,Bool.and_eq_true_iff] at hi
        exact hi.2
theorem pair_lim (I : List (Nat × Nat)) (Q cs : List Nat)
    (qok : ∀ s∈Q,(s,4)∈I) (ok : okContacts 6 I cs=true) :
    cs.Pairwise (fun x y=> missWord Q x &&& missWord Q y = 0) := by
  rw [List.pairwise_iff_forall_sublist]
  intro x y sub
  apply (and_mask Q _ _).mpr
  intro m hm hx
  by_contra! hy
  have yhit : (y &&& m == 0)=true := by simpa using hy
  have a := of_decide_eq_true (List.all_eq_true.mp ok (m,4) (qok m hm))
  have b := (sub.filter (p:=fun z=> z &&& m == 0)).length_le
  simp [hx,yhit] at b
  change 4+(cs.filter (fun z=> z &&& m == 0)).length < 6 at a
  omega
theorem trioTest_sound (b : List Nat) (as_ : List TrioAtom) (Q : List Nat) (fs : Array TriFeature)
    (costs : Array Nat) (budget : Nat) (done_ : Nat→Nat→Nat→Bool)
    (verified : trioValidated b as_ Q fs costs budget=true)
    (passed : trioTest as_ fs costs budget done_=true)
    (x y z : Nat) (inc : ∀ t∈[x,y,z],t∈usable 6 3 b)
    (ord : [x,y,z].Pairwise (·≤·)) (ok : okContacts 6 (inds b) [x,y,z]=true)
    (small : countBits b.length x+countBits b.length y+countBits b.length z≤ budget) : done_ x y z=true := by
  obtain ⟨vleft,cover⟩ := Bool.and_eq_true_iff.mp verified
  obtain ⟨vhead,costOK⟩ := Bool.and_eq_true_iff.mp vleft
  obtain ⟨vf,atomsOK⟩ := Bool.and_eq_true_iff.mp vhead
  obtain ⟨quadsOK,triOK⟩ := Bool.and_eq_true_iff.mp vf
  have get_ (t) (ht : t∈[x,y,z]) : ∃ a∈as_,a.mask=t := List.mem_map.mp (of_decide_eq_true (List.all_eq_true.mp cover t (inc t ht)))
  obtain ⟨a,ha,rfl⟩ := get_ x (by simp)
  obtain ⟨c,hc,rfl⟩ := get_ y (by simp)
  obtain ⟨e,he,rfl⟩ := get_ z (by simp)
  obtain ⟨j,hj⟩ : ∃ j,as_[j]?=some e := List.mem_iff_getElem?.mp he
  have rec_ (w) (hw : w∈as_) := List.all_eq_true.mp atomsOK w hw
  have A := rec_ a ha
  have C := rec_ c hc
  have E := rec_ e he
  simp only [Bool.and_eq_true_iff,beq_iff_eq] at A C E
  have pairs := pair_lim (inds b) Q [a.mask,c.mask,e.mask] (fun s hs=> of_decide_eq_true (List.all_eq_true.mp quadsOK s hs)) ok
  simp [List.pairwise_cons] at pairs ord
  have ac : allowedPair a c=true := by simp [allowedPair,ord,pairs,A.1.1.2,C.1.1.2]
  have ae : allowedPair a e=true := by simp [allowedPair,ord,pairs,A.1.1.2,E.1.1.2]
  have ce : allowedPair c e=true := by simp [allowedPair,ord,pairs,C.1.1.2,E.1.1.2]
  have enough : a.cost+c.cost+e.cost≤ budget := by simpa [A.1.1.1,C.1.1.1,E.1.1.1] using small
  have hk : budget-a.cost-c.cost ∈ List.range (budget+1) := List.mem_range.mpr (by omega)
  have costeq := of_decide_eq_true (List.all_eq_true.mp costOK _ hk)
  have inner := List.all_eq_true.mp (List.all_eq_true.mp passed a ha) c hc
  simp only [ac,Bool.true_and,show a.cost+c.cost≤ budget by omega,decide_true,if_true,costeq,Option.getD_some] at inner
  have inpool : (a.later &&& c.later &&& fitMask as_ (budget-a.cost-c.cost)).testBit j=true := by
    rw [A.2,C.2]
    simp only [Nat.testBit_and,Bool.and_eq_true_iff]
    exact ⟨⟨(testbit_of_get _ _ _ hj).trans ae,(testbit_of_get _ _ _ hj).trans ce⟩,
      (testbit_of_get _ _ _ hj).trans (decide_eq_true (by omega))⟩
  have alive := remove_keeps fs fs.size (a.miss3 &&& c.miss3) _ j inpool (by
    intro i hi
    cases hh : fs[i]? with
    | none => change (0:Nat).testBit j=false; simp
    | some f =>
      have fl : fs.toList[i]?=some f := by simpa using hh
      have hmem : f∈fs.toList := List.mem_iff_getElem?.mpr ⟨i,fl⟩
      obtain ⟨fi,mask⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp triOK _ hmem)
      simp only [A.1.2,C.1.2,Nat.testBit_and,Bool.and_eq_true_iff] at hi
      have si : (fs.toList.map TriFeature.subset)[i]?=some f.subset := by simp [List.getElem?_map,fl]
      have ax := (testbit_of_get _ _ _ si).symm.trans hi.1
      have cx := (testbit_of_get _ _ _ si).symm.trans hi.2
      simp only [Option.getD_some,beq_iff_eq.mp mask,testbit_of_get _ _ _ hj]
      apply Bool.eq_false_iff.mpr
      intro ex
      have h := of_decide_eq_true (List.all_eq_true.mp ok (f.subset,3) (of_decide_eq_true fi))
      simp [show (a.mask &&& f.subset == 0)=true from ax,show (c.mask &&& f.subset == 0)=true from cx,ex] at h)
  have cnt : (removeHits fs fs.size (a.miss3 &&& c.miss3) (a.later &&& c.later &&& fitMask as_ (budget-a.cost-c.cost))) < 2^as_.length := by
    have bound (fs : Array TriFeature) (n s p : Nat) : removeHits fs n s p≤ p := by
      induction n generalizing s p with
      | zero => rfl
      | succ n ih =>
        simp only [removeHits]
        split
        · rfl
        · apply le_trans (ih _ _)
          apply Nat.le_of_testBit
          intro i hi
          by_contra! hh
          simp [Nat.testBit_xor,Nat.testBit_and,hh] at hi
    apply (bound ..).trans_lt
    apply Nat.lt_of_le_of_lt Nat.and_le_right
    simpa [fitMask,tableBits] using bits_lt (as_.map fun o=> decide (o.cost≤ budget-a.cost-c.cost))
  have answer := visit_hits _ _ _ _ alive cnt inner
  simpa [hj] using answer
theorem triple_in (b : List Nat) (as_ : List FP32.TrioAtom) (Q : List Nat) (fs : Array FP32.TriFeature)
    (costs : Array Nat) (budget : Nat) (known : List (List Nat))
    (bound : 32-edges_ b-3 = budget)
    (valid : trioValidated b as_ Q fs costs budget=true)
    (run : trioTest as_ fs costs budget (fun x y z=> decide ([x,y,z]∈known))=true)
    {cs : List Nat} (ex : Extension 6 3 b cs) (sorted : cs.Pairwise (·≤·))
    (he : edges_ (attach cs b)≤32) : cs∈known := by
  obtain ⟨x,y,z,rfl⟩ : ∃ x y z,cs=[x,y,z] := ⟨_,_,_,List.eq_getElem_of_length_eq_three cs ex.1⟩
  have en := edges_attached [x,y,z] b
  simp only [List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at en
  have cost : countBits b.length x+countBits b.length y+countBits b.length z≤ budget := by omega
  exact of_decide_eq_true (trioTest_sound b as_ Q fs costs budget _ valid run x y z ex.2.1 sorted ex.2.2 cost)
end FP32
end

section
namespace FiveSearch
open FP32

structure Vertex where
  mask : Nat
  cost : Nat
  misses : Nat
deriving Inhabited

def relation (a b : Vertex) := decide (a.mask≤ b.mask) && (a.misses &&& b.misses == 0)
def quints (b : List Nat) := ((inds b).filter fun p=> p.2==5).map Prod.fst

def dataOK (b pool Q : List Nat) (rows : List Vertex) :=
  Q == quints b && rows.map Vertex.mask == pool &&
    rows.all (fun a=> a.cost == countBits b.length a.mask && a.misses == missWord Q a.mask)

theorem splitTest {α : Type u} {l : List α} {f : α → Bool} (k : Nat)
    (h₁ : (l.take k).all f = true) (h₂ : (l.drop k).all f = true) : l.all f = true := by
  rw [←List.take_append_drop k l,List.all_append,h₁,h₂]
  rfl
end FiveSearch
namespace FiveSearch
def listDfs (out : List (List Nat)) : Nat → List Vertex → Nat → List Nat → Bool
  | 0,_,_,pref => decide (pref.reverse∈out)
  | k+1,avail,bud,pref =>
    avail.all fun a =>
      if a.cost+3*k≤ bud && bud≤ a.cost+5*k then
        listDfs out k (avail.filter (relation a)) (bud-a.cost) (a.mask::pref)
      else true
end FiveSearch
namespace FiveSearch
open FP32

def guard (near out : List (List Nat)) (weights : List (Nat×Nat)) :=
  near.all fun cs=> decide (cs∈out) || weights.any fun p =>
    decide (7 ≤ p.2 + (cs.filter fun x=> x&&&p.1==0).length)
end FiveSearch

namespace FiveSearch
open FP32

theorem quint_pairs (b Q masks : List Nat) (qv : Q=quints b)
    (ok : okContacts 7 (inds b) masks=true) :
    masks.Pairwise (fun x y=> missWord Q x &&& missWord Q y=0) := by
  rw [List.pairwise_iff_forall_sublist]
  intro x y sub
  apply (and_mask Q _ _).mpr
  intro s hs hx
  by_contra! hy
  have q : (s,5)∈inds b := by
    rw [qv] at hs
    obtain ⟨⟨a,t⟩,hm,rfl⟩ := List.mem_map.mp hs
    obtain ⟨hi,ht⟩ := List.mem_filter.mp hm
    have h : t=5 := beq_iff_eq.mp ht
    simpa [h] using hi
  have a := of_decide_eq_true (List.all_eq_true.mp ok (s,5) q)
  have h := (sub.filter (p:=fun z=> z&&&s==0)).length_le
  have hy' : (y&&&s==0)=true := by simpa using hy
  simp [hx,hy'] at h
  change 5+(masks.filter (fun z=> z&&&s==0)).length<7 at a
  omega

theorem select_path (rows : List Vertex) (cs : List Nat)
    (inc : ∀x∈cs,x∈rows.map Vertex.mask) :
    ∃ vs : List Vertex, vs.map Vertex.mask=cs ∧ ∀ v∈vs,v∈rows := by
  induction cs with
  | nil => exact ⟨[],rfl,by simp⟩
  | cons x l ih =>
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp (inc x (.head _))
    obtain ⟨vs,rfl,allv⟩ := ih (fun y hy=> inc y (.tail _ hy))
    exact ⟨v::vs,rfl,by simpa using And.intro hv allv⟩

end FiveSearch
namespace FiveSearch
open FP32

theorem sum_bounds (vs : List Vertex) (costs : ∀ a∈vs,3≤ a.cost ∧ a.cost≤5) :
    3*vs.length ≤ (vs.map Vertex.cost).sum ∧ (vs.map Vertex.cost).sum ≤ 5*vs.length := by
  induction vs with
  | nil => simp
  | cons a l ih =>
    have first := costs a (.head _)
    have tail := ih (fun b hb=> costs b (.tail _ hb))
    simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.mul_succ]
    omega

theorem list_complete (out : List (List Nat)) (vs : List Vertex)
    (pw : vs.Pairwise (fun a c=> relation a c=true)) (costs : ∀ a∈vs,3≤ a.cost ∧ a.cost≤5)
    (avail : List Vertex) (rem : Nat) (pref : List Nat) (mem : ∀a∈vs,a∈avail)
    (sum : (vs.map Vertex.cost).sum=rem)
    (check : listDfs out vs.length avail rem pref=true) :
    pref.reverse ++ vs.map Vertex.mask ∈ out := by
  induction vs generalizing avail rem pref with
  | nil => simpa [listDfs] using check
  | cons a l ih =>
    obtain ⟨rel,pw'⟩ := List.pairwise_cons.mp pw
    have cb := fun c (hc : c∈l) => costs c (.tail _ hc)
    have bounds := sum_bounds l cb
    simp only [List.map_cons,List.sum_cons] at sum
    have choice := List.all_eq_true.mp check a (mem a (.head _))
    simp only [show a.cost+3*l.length ≤ rem by omega, show rem ≤ a.cost+5*l.length by omega,
      decide_true,Bool.true_and,ite_true] at choice
    have got := ih pw' cb (avail.filter (relation a)) (rem-a.cost) (a.mask::pref)
      (fun c hc=> List.mem_filter.mpr ⟨mem c (.tail _ hc),rel c hc⟩) (by omega) choice
    simpa using got

theorem recover_from_checks (b pool Q : List Nat) (rows : List Vertex) (bud : Nat)
    (near out : List (List Nat)) (W : List (Nat×Nat)) (good : dataOK b pool Q rows=true)
    (bound : rows.all (fun a=> decide (3≤ a.cost ∧ a.cost≤5))=true)
    (check : rows.all (fun a=> listDfs near 4 (rows.filter (relation a)) (bud-a.cost) [a.mask])=true)
    (wgood : W.all (fun p=> decide (p∈inds b))=true) (reject : guard near out W=true)
    {cs : List Nat} (len : cs.length=5) (inc : ∀x∈cs,x∈pool) (ord : cs.Pairwise (·≤·))
    (ok : okContacts 7 (inds b) cs=true) (ub : (cs.map (countBits b.length)).sum=bud) :
    cs∈out := by
  obtain ⟨⟨qv,rm⟩,va⟩ := (by simpa only [dataOK,Bool.and_eq_true_iff,beq_iff_eq] using good :
    (Q=quints b ∧ rows.map Vertex.mask=pool) ∧ _)
  have dat (a) (ha : a∈rows) := List.all_eq_true.mp va a ha
  simp only [Bool.and_eq_true_iff,beq_iff_eq] at dat
  obtain ⟨vs,hvs,allv⟩ := select_path rows cs (by simpa [rm] using inc)
  have inside : cs∈near := by
    rw [←hvs] at len ord ok ub ⊢
    have quad := List.pairwise_map.mp (quint_pairs b Q _ qv ok)
    have sort_ := List.pairwise_map.mp ord
    have pw : vs.Pairwise (fun a c=> relation a c=true) := by
      rw [List.pairwise_iff_forall_sublist] at quad sort_ ⊢
      intro a c sub
      have hac := (dat a (allv _ (sub.subset (by simp)))).2
      have hcc := (dat c (allv _ (sub.subset (by simp)))).2
      simp [relation,hac,hcc,quad sub,sort_ sub]
    have costs : (vs.map Vertex.cost).sum=bud := by
      rw [←ub,List.map_map]
      congr 1
      exact List.map_congr_left (fun x hx=>(dat x (allv x hx)).1)
    cases vs with
    | nil => simp at len
    | cons a l =>
      have la : l.length=4 := by simpa using len
      obtain ⟨first,rest⟩ := List.pairwise_cons.mp pw
      have test := List.all_eq_true.mp check a (allv _ (.head _))
      rw [←la] at test
      have done_ := list_complete near l rest
        (fun c hc=> of_decide_eq_true (List.all_eq_true.mp bound c (allv c (.tail _ hc))))
        _ _ _ (fun c hc=> List.mem_filter.mpr ⟨allv c (.tail _ hc),first c hc⟩)
        (by simp only [List.map_cons,List.sum_cons] at costs;omega) test
      simpa using done_
  rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp reject cs inside) with yes|no
  · exact of_decide_eq_true yes
  · obtain ⟨p,hp,hg⟩ := List.any_eq_true.mp no
    have hi := of_decide_eq_true (List.all_eq_true.mp wgood p hp)
    have le := of_decide_eq_true (List.all_eq_true.mp ok p hi)
    exact False.elim ((Nat.not_lt_of_ge (of_decide_eq_true hg)) le)
end FiveSearch
namespace FiveSearch.FiveData0
open FP32
def Q : List Nat := [17932,9740,12556,18700,6412,17164,8972,12428,18572,6284,17548,9356,9794,12610,9026,17954,18722,6434,17186,1634,4450,866,12434,18578,6290,17554,9362,12370,9298,18482,6194,17458,4210,1138,17926,9734,12550,18694,6406,17158,8966,12422,18566,6278,17542,9350,9793,12609,9025,17953,18721,6433,17185,1633,4449,865,12433,18577,6289,17553,9361,12369,9297,18481,6193,17457,4209,1137,17929,9737,12553,18697,6409,17161,8969,12425,18569,6281,17545,9353]
def R : List Vertex := [⟨321,3,68225148686211⟩,⟨322,3,1172099129419833184096131⟩,⟨518,3,1179706126477114925383680⟩,⟨521,3,68667934187520⟩,⟨801,4,68170253602688⟩,⟨802,4,1171156039066114829848448⟩,⟨833,4,68173609045888⟩,⟨834,4,1171213685141345172197248⟩,⟨1030,3,301155192968220105506816⟩,⟨1033,3,17529539354624⟩,⟨1158,4,36702165524361708044288⟩,⟨1161,4,2136347205632⟩,⟨1168,3,36598402591077399224444⟩,⟨1169,4,2130307407996⟩,⟨1170,4,36598402588947091816572⟩,⟨1542,4,272820953257130611179520⟩,⟨1545,4,15880269537280⟩,⟨2054,3,975140572802838480027648⟩,⟨2057,3,56760651804672⟩,⟨2310,4,945625723315895576559616⟩,⟨2313,4,55042661453824⟩,⟨4102,3,1014033281867603802849280⟩,⟨4105,3,59024505425920⟩,⟨4129,3,59013228158315⟩,⟨4130,3,1013839539826384091221355⟩,⟨4161,3,59015644417387⟩,⟨4162,3,1013881050841155704458603⟩,⟨4178,4,1013833060483526444453227⟩,⟨4358,4,983337857789179579072512⟩,⟨4361,4,57237796589568⟩,⟨4385,4,57226521746691⟩,⟨4386,4,983144157406256420621571⟩,⟨4417,4,57228937694467⟩,⟨4418,4,983185663073003476356355⟩,⟨6150,4,936104866287129819348992⟩,⟨6153,4,54488474636288⟩,⟨6177,4,54477734304867⟩,⟨6178,4,935920348743846869339235⟩,⟨6404,4,907770626576051432099840⟩,⟨6406,5,907770626576040325021696⟩,⟨6408,4,190818202369590333440⟩,⟨6409,5,52839204818944⟩,⟨6412,5,190818149541492592640⟩,⟨8337,4,979256705081⟩,⟨8338,4,16823502089867195580473⟩,⟨8449,3,30820207724289⟩,⟨8450,3,529487136896187853965057⟩,⟨8454,4,529487136896187853963264⟩,⟨8457,4,30820207722496⟩,⟨8460,4,286942909624939479040⟩,⟨8513,4,30807322298113⟩,⟨8514,4,529265766960104084604673⟩,⟨8705,3,31215345403672⟩,⟨8706,3,536275550537261990807320⟩,⟨8710,4,536275550537261990805504⟩,⟨8713,4,31215345401856⟩,⟨8769,4,31202459453208⟩,⟨8770,4,536054171593978966705944⟩,⟨8961,4,30803027298048⟩,⟨8962,4,529191979420859292976896⟩,⟨9025,5,30790142396160⟩,⟨9026,5,528970618491974778357504⟩,⟨9222,4,243303825230251234951168⟩,⟨9225,4,14162146557952⟩,⟨9228,4,101951362470440796160⟩,⟨9345,4,967981858872⟩,⟨9346,4,16629801706944037126200⟩,⟨9348,4,16629801706949946310656⟩,⟨9350,5,16629801706944037126144⟩,⟨9352,4,101519017868260737024⟩,⟨9353,5,967981858816⟩,⟨9360,4,16528344615500710871096⟩,⟨9361,5,962076278840⟩,⟨9362,5,16528344614538634592312⟩,⟨9729,4,13612388385560⟩,⟨9730,4,233859051732115298190104⟩,⟨9734,5,233859051732115298189312⟩,⟨9737,5,13612388384768⟩,⟨9740,5,101910830073792102400⟩,⟨12294,4,390084845359085173866496⟩,⟨12297,4,22705926406144⟩,⟨12304,3,389890433993065454470441⟩,⟨12305,4,22694610175273⟩,⟨12306,4,389890433970370844296489⟩,⟨12353,4,22697333851433⟩,⟨12354,4,389937226370499223749929⟩,⟨12368,4,389890388957069178144041⟩,⟨12370,5,389890388934374570591529⟩,⟨12432,4,12101115341503604817961⟩,⟨12545,4,22018729215233⟩,⟨12546,4,378278887493614507656449⟩,⟨12550,5,378278887493614507655168⟩,⟨12553,5,22018729213952⟩,⟨12609,5,22010138756353⟩,⟨12610,5,378131304533825576502529⟩,⟨16529,4,1477472579670⟩,⟨16530,4,25382785640200149139542⟩,⟨16641,3,46228298013314⟩,⟨16642,3,794196112421487762213506⟩,⟨16646,4,794196112421487762210816⟩,⟨16649,4,46228298010624⟩,⟨16673,4,46214338845314⟩,⟨16674,4,793956295741330283301506⟩,⟨16902,4,799508786044083925680128⟩,⟨16905,4,46537536315392⟩,⟨17153,4,46193937746560⟩,⟨17154,4,793605807533561057643136⟩,⟨17186,5,793365999860602833472128⟩,⟨17409,3,12443752489684⟩,⟨17410,3,213782039918407204209364⟩,⟨17414,4,213782039918407204208640⟩,⟨17417,4,12443752488960⟩,⟨17425,4,12438228591316⟩,⟨17426,4,213687140067059253117652⟩,⟨17441,4,12438380503764⟩,⟨17442,4,213689749903043314320084⟩,⟨17457,5,12438225314516⟩,⟨17458,5,213687083772063910986452⟩,⟨17537,4,1448615239764⟩,⟨17538,4,24887020315651206021204⟩,⟨17552,4,24792480753716556882004⟩,⟨17553,5,1443112312916⟩,⟨17554,5,24792480752273444569172⟩,⟨17921,4,11344238748308⟩,⟨17922,4,194892537676656627679892⟩,⟨17926,5,194892537676656627679232⟩,⟨17929,5,11344238747648⟩,⟨17932,5,94920258289287700480⟩,⟨18465,4,38586460174534⟩,⟨18466,4,662910338033533941975238⟩,⟨18480,4,662902195563993642334406⟩,⟨18481,5,38585986218182⟩,⟨18482,5,662902195525407656118470⟩,⟨18689,4,37431114471554⟩,⟨18690,4,643061649995209254111362⟩,⟨18721,5,37418229045378⟩,⟨18722,5,642840280059125484750978⟩]
def near : List (List Nat) := [[1030,1169,6406,8449,18721],[1030,1169,6406,8513,18689],[1030,1169,6406,12545,16673],[1030,1169,6406,12609,16641],[1030,6406,8337,8961,18465],[1030,6406,8449,9361,18465],[1030,6406,12353,16529,17153],[1030,6406,12353,16641,17553],[1033,1170,6409,8450,18722],[1033,1170,6409,8514,18690],[1033,1170,6409,12546,16674],[1033,1170,6409,12610,16642],[1033,6409,8338,8962,18466],[1033,6409,8450,9362,18466],[1033,6409,12354,16530,17154],[1033,6409,12354,16642,17554],[1169,1542,6150,8449,18721],[1169,1542,6150,8513,18689],[1169,1542,6150,12545,16673],[1169,1542,6150,12609,16641],[1169,4102,8449,17926,18721],[1169,4102,8513,17926,18689],[1169,4102,12545,16673,17926],[1169,4102,12609,16641,17926],[1169,4358,8449,17414,18721],[1169,4358,8513,17414,18689],[1169,4358,12545,16673,17414],[1169,4358,12609,16641,17414],[1170,1545,6153,8450,18722],[1170,1545,6153,8514,18690],[1170,1545,6153,12546,16674],[1170,1545,6153,12610,16642],[1170,4105,8450,17929,18722],[1170,4105,8514,17929,18690],[1170,4105,12546,16674,17929],[1170,4105,12610,16642,17929],[1170,4361,8450,17417,18722],[1170,4361,8514,17417,18690],[1170,4361,12546,16674,17417],[1170,4361,12610,16642,17417],[1542,6150,8337,8961,18465],[1542,6150,8449,9361,18465],[1542,6150,12353,16529,17153],[1542,6150,12353,16641,17553],[1545,6153,8338,8962,18466],[1545,6153,8450,9362,18466],[1545,6153,12354,16530,17154],[1545,6153,12354,16642,17554],[4102,8337,8961,17926,18465],[4102,8449,9361,17926,18465],[4102,12353,16529,17153,17926],[4102,12353,16641,17553,17926],[4105,8338,8962,17929,18466],[4105,8450,9362,17929,18466],[4105,12354,16530,17154,17929],[4105,12354,16642,17554,17929],[4358,8337,8961,17414,18465],[4358,8449,9361,17414,18465],[4358,12353,16529,17153,17414],[4358,12353,16641,17414,17553],[4361,8338,8962,17417,18466],[4361,8450,9362,17417,18466],[4361,12354,16530,17154,17417],[4361,12354,16642,17417,17554]]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem validRows : dataOK (SparseFifteen.adj 0) (FiveLP.pool 0) Q R=true := by decide +kernel
def test : Vertex → Bool := (fun a=> listDfs near 4 (R.filter (relation a)) (FiveLP.budget 0-a.cost) [a.mask])
end FiveSearch.FiveData0
namespace FiveSearch.FiveData0
open FP32
def W : List (Nat × Nat) := [(576,2),(8768,3),(2192,3),(2080,2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem covered : guard near (FiveIso.outputs 0) W=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem wgood : W.all (fun x => decide (x∈inds (SparseFifteen.adj 0)))=true := by decide +kernel
end FiveSearch.FiveData0
namespace FiveSearch.FiveData0
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block0 : ((R.drop 0).take 4).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block1 : ((R.drop 4).take 4).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block2 : ((R.drop 8).take 1).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block3 : ((R.drop 9).take 1).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block4 : ((R.drop 10).take 1).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block5 : ((R.drop 11).take 1).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block6 : ((R.drop 12).take 1).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block7 : ((R.drop 13).take 1).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block8 : ((R.drop 14).take 1).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block9 : ((R.drop 15).take 1).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block10 : ((R.drop 16).take 1).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block11 : ((R.drop 17).take 2).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block12 : ((R.drop 19).take 2).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block13 : ((R.drop 21).take 5).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block14 : ((R.drop 26).take 3).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block15 : ((R.drop 29).take 1).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block16 : ((R.drop 30).take 3).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block17 : ((R.drop 33).take 2).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block18 : ((R.drop 35).take 4).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block19 : ((R.drop 39).take 1).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block20 : ((R.drop 40).take 1).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block21 : ((R.drop 41).take 1).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block22 : ((R.drop 42).take 5).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block23 : ((R.drop 47).take 3).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block24 : ((R.drop 50).take 6).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block25 : ((R.drop 56).take 7).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block26 : ((R.drop 63).take 8).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block27 : ((R.drop 71).take 8).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block28 : ((R.drop 79).take 4).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block29 : ((R.drop 83).take 3).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block30 : ((R.drop 86).take 5).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block31 : ((R.drop 91).take 25).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block32 : ((R.drop 116).take 21).all test = true := by decide +kernel

set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem checked : R.all test = true := by
  apply splitTest 4
  · exact block0
  apply splitTest 4
  · exact block1
  apply splitTest 1
  · exact block2
  apply splitTest 1
  · exact block3
  apply splitTest 1
  · exact block4
  apply splitTest 1
  · exact block5
  apply splitTest 1
  · exact block6
  apply splitTest 1
  · exact block7
  apply splitTest 1
  · exact block8
  apply splitTest 1
  · exact block9
  apply splitTest 1
  · exact block10
  apply splitTest 2
  · exact block11
  apply splitTest 2
  · exact block12
  apply splitTest 5
  · exact block13
  apply splitTest 3
  · exact block14
  apply splitTest 1
  · exact block15
  apply splitTest 3
  · exact block16
  apply splitTest 2
  · exact block17
  apply splitTest 4
  · exact block18
  apply splitTest 1
  · exact block19
  apply splitTest 1
  · exact block20
  apply splitTest 1
  · exact block21
  apply splitTest 5
  · exact block22
  apply splitTest 3
  · exact block23
  apply splitTest 6
  · exact block24
  apply splitTest 7
  · exact block25
  apply splitTest 8
  · exact block26
  apply splitTest 8
  · exact block27
  apply splitTest 4
  · exact block28
  apply splitTest 3
  · exact block29
  apply splitTest 5
  · exact block30
  apply splitTest 25
  · exact block31
  exact block32
end FiveSearch.FiveData0
namespace FiveSearch.FiveData1
open FP32
def Q : List Nat := [17956,18724,6436,17188,1636,4452,868,18580,6292,17556,18484,6196,17460,4212,1140,9794,12610,9026,17930,9738,12554,18698,6410,17162,8970,12426,18570,6282,17546,9354,17926,18694,6406,17158,18566,6278,17542,1606,4422,838,9793,12609,9025,17953,18721,6433,17185,1633,4449,865,12433,18577,6289,17553,9361,12369,9297,18481,6193,17457,4209,1137,17929,9737,12553,18697,6409,17161,8969,12425,18569,6281,17545,9353]
def R : List Vertex := [⟨521,3,401579540390⟩,⟨582,4,18429341091626043310080⟩,⟨777,4,120259116928⟩,⟨1030,3,4705549890128439148544⟩,⟨1033,3,891205922286⟩,⟨1089,3,66839383438⟩,⟨1094,4,4704360088804813438976⟩,⟨1108,4,4703919861941505359872⟩,⟨1121,4,66839380352⟩,⟨1124,4,4703927620095550947328⟩,⟨1158,4,573471336318151688192⟩,⟨1169,4,839698808942⟩,⟨1172,4,571850040452331012096⟩,⟨1542,4,4262827394642665799680⟩,⟨1572,4,4261241793322538827776⟩,⟨2054,3,15236571450044351250432⟩,⟨2182,4,479148043579038892032⟩,⟨2196,4,475004731921885265920⟩,⟨2310,4,14775401926810868383744⟩,⟨2337,4,208071852544⟩,⟨4102,3,15844270029181309419520⟩,⟨4106,3,3128555883231991515⟩,⟨4166,4,15841891419393057882112⟩,⟨4177,4,98610970635⟩,⟨4193,4,98610971264⟩,⟨4230,4,496549686457384566784⟩,⟨4233,4,699006112859⟩,⟨4356,3,15364654027956804157440⟩,⟨4358,4,15364654027955930923008⟩,⟨4361,4,224412096145⟩,⟨4362,4,3127900574301836945⟩,⟨4385,4,225285276288⟩,⟨4417,4,87846295169⟩,⟨6150,4,14626638535736403427328⟩,⟨6402,4,14183916040250630099473⟩,⟨6404,4,14183916040251436204032⟩,⟨6406,5,14183916040250630078464⟩,⟨8513,4,121802858369⟩,⟨8961,4,120728878976⟩,⟨9360,4,258255385441846952046⟩,⟨9361,5,839680786542⟩,⟨12290,3,6095075708735705863899⟩,⟨12353,4,98056803979⟩,⟨12354,4,6092769162039050376843⟩,⟨12368,4,6092037327197659463691⟩,⟨12545,4,224747869841⟩,⟨12546,4,5910607617087726704273⟩,⟨12609,5,87308899969⟩,⟨16529,4,966390415476⟩,⟨16641,3,172503918864⟩,⟨16644,3,12409314256586451484672⟩,⟨16646,4,12409314256585746284544⟩,⟨16673,4,172503892224⟩,⟨16902,4,12492324781938811338752⟩,⟨16905,4,313532705060⟩,⟨17153,4,35064408320⟩,⟨17184,4,12396343747856983654656⟩,⟨17414,4,3340344373725112565760⟩,⟨17417,4,863288633700⟩,⟨17418,4,1483696383683733860⟩,⟨17425,4,863478415460⟩,⟨17441,4,863478415616⟩,⟨17537,4,828950915172⟩,⟨17553,5,828950904932⟩,⟨17922,4,3045195901197759818020⟩,⟨17924,4,3045195901197932888064⟩,⟨17926,5,3045195901197759807488⟩,⟨18442,4,3586984062293663856⟩,⟨18449,4,962661679216⟩,⟨18689,4,138009960464⟩]
def near : List (List Nat) := [[1030,1169,6406,8513,18689],[1030,1169,6406,12609,16641],[1030,6406,12353,16529,17153],[1030,6406,12353,16641,17553],[1030,6406,12353,16673,17537],[1169,1542,6150,8513,18689],[1169,1542,6150,12609,16641],[1169,4102,8513,17926,18689],[1169,4102,12609,16641,17926],[1169,4358,8513,17414,18689],[1169,4358,12609,16641,17414],[1542,6150,12353,16529,17153],[1542,6150,12353,16641,17553],[1542,6150,12353,16673,17537],[4102,12353,16529,17153,17926],[4102,12353,16641,17553,17926],[4102,12353,16673,17537,17926],[4358,12353,16529,17153,17414],[4358,12353,16641,17414,17553],[4358,12353,16673,17414,17537]]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem validRows : dataOK (SparseFifteen.adj 1) (FiveLP.pool 1) Q R=true := by decide +kernel
def test : Vertex → Bool := (fun a=> listDfs near 4 (R.filter (relation a)) (FiveLP.budget 1-a.cost) [a.mask])
end FiveSearch.FiveData1
namespace FiveSearch.FiveData1
open FP32
def W : List (Nat × Nat) := [(8768,3),(2080,2),(8272,3),(2336,3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem covered : guard near (FiveIso.outputs 1) W=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem wgood : W.all (fun x => decide (x∈inds (SparseFifteen.adj 1)))=true := by decide +kernel
end FiveSearch.FiveData1
namespace FiveSearch.FiveData1
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block0 : ((R.drop 0).take 11).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block1 : ((R.drop 11).take 13).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block2 : ((R.drop 24).take 25).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block3 : ((R.drop 49).take 21).all test = true := by decide +kernel

set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem checked : R.all test = true := by
  apply splitTest 11
  · exact block0
  apply splitTest 13
  · exact block1
  apply splitTest 25
  · exact block2
  exact block3
end FiveSearch.FiveData1
namespace FiveSearch.FiveData2
open FP32
def Q : List Nat := [9796,12612,9028,17956,18724,6436,17188,1636,4452,868,12372,9300,18484,6196,17460,4212,1140,12434,18578,6290,17554,9362,17930,9738,12554,18698,6410,17162,8970,12426,18570,6282,17546,9354,17926,9734,12550,18694,6406,17158,8966,12310,18454,6166,17430,9238,9793,12609,9025,17953,18721,6433,17185,1633,4449,865,12433,18577,6289,17553,9361,12369,9297,18481,6193,17457,4209,1137,17929,9737,12553,18697,6409,17161,8969,12425,18569,6281,17545,9353]
def R : List Vertex := [⟨777,4,68169725115392⟩,⟨778,4,295075847585315027968⟩,⟨1030,3,301155192968220105506816⟩,⟨1033,3,17523467532150⟩,⟨1046,4,301050925629647223783424⟩,⟨1169,4,2130823873398⟩,⟨1170,4,36598402588947091817334⟩,⟨1542,4,272820953257130611179520⟩,⟨2310,4,945625723315895576559616⟩,⟨4102,3,1014033281867603802849280⟩,⟨4118,4,1013833105871366439043072⟩,⟨4129,3,59027261491205⟩,⟨4145,4,1852653436933⟩,⟨4177,4,1852653437016⟩,⟨4180,4,1013833060483540851884032⟩,⟨4358,4,983337857789179579072512⟩,⟨4362,4,200185636755316234377⟩,⟨4385,4,57240118888449⟩,⟨4417,4,57240118906888⟩,⟨6150,4,936104866287129819348992⟩,⟨6196,5,935914007675584831815680⟩,⟨6401,4,52840998455433⟩,⟨6404,4,907770626576053225652224⟩,⟨6406,5,907770626576040325021696⟩,⟨6436,5,907586149565166921973760⟩,⟨8209,3,987007812600⟩,⟨8214,4,545728548171267459514368⟩,⟨8273,4,987007811704⟩,⟨8276,4,545728485120880431595520⟩,⟨8337,4,979491619832⟩,⟨8338,4,16823502089867195581432⟩,⟨8449,3,30811027796104⟩,⟨8457,4,30803507409032⟩,⟨8458,4,286942909608237330568⟩,⟨8513,4,30811027697672⟩,⟨8961,4,30793843732480⟩,⟨8969,5,30786327539712⟩,⟨9222,4,243303825230251234951168⟩,⟨9225,4,14156213039984⟩,⟨9233,4,965528781680⟩,⟨9238,5,243201935792281604849664⟩,⟨9345,4,14156447134576⟩,⟨9361,5,962307556208⟩,⟨9738,5,101910830067860156720⟩,⟨12294,4,390084845359085173866496⟩,⟨12305,4,709915312856⟩,⟨12310,5,389890433970370844295168⟩,⟨12353,4,22700149198936⟩,⟨12356,4,389937226370504765734912⟩,⟨12369,5,709915312216⟩,⟨12545,4,22012786725000⟩,⟨12609,5,22012786659336⟩,⟨16401,3,1489103750055⟩,⟨16433,4,1489103749127⟩,⟨16436,4,818740289460117583167488⟩,⟨16529,4,1477829460903⟩,⟨16641,3,46225133644929⟩,⟨16646,4,794196112421487762210816⟩,⟨16649,4,46213850967169⟩,⟨16673,4,46225133538305⟩,⟨16902,4,799508786044083925680128⟩,⟨17153,4,46190765517824⟩,⟨17161,5,46179491228672⟩,⟨17414,4,213782039918407204208640⟩,⟨17417,4,12438225987366⟩,⟨17425,4,1446145688358⟩,⟨17444,4,213689749903046351650816⟩,⟨17537,4,12438577653542⟩,⟨17553,5,1443461333798⟩,⟨17921,4,11341482599714⟩,⟨17922,4,194892537676656627721506⟩,⟨17926,5,194892537676656627679232⟩,⟨17930,5,94920258283762656546⟩,⟨18449,4,1212011250567⟩,⟨18465,4,38595408825351⟩,⟨18468,4,662910338033543364608000⟩,⟨18481,5,1212011249671⟩,⟨18689,4,37426892606593⟩,⟨18721,5,37426892508161⟩]
def near : List (List Nat) := [[777,1030,6406,8209,18481],[777,1030,6406,8273,18449],[777,1030,6406,12305,16433],[777,1030,6406,12369,16401],[777,1542,6150,8209,18481],[777,1542,6150,8273,18449],[777,1542,6150,12305,16433],[777,1542,6150,12369,16401],[777,4102,8209,17926,18481],[777,4102,8273,17926,18449],[777,4102,12305,16433,17926],[777,4102,12369,16401,17926],[777,4358,8209,17414,18481],[777,4358,8273,17414,18449],[777,4358,12305,16433,17414],[777,4358,12369,16401,17414],[1030,1169,6406,8449,18721],[1030,1169,6406,8513,18689],[1030,1169,6406,12545,16673],[1030,1169,6406,12609,16641],[1030,6406,8209,8969,18465],[1030,6406,8337,8961,18465],[1030,6406,8449,9361,18465],[1030,6406,8457,9233,18465],[1030,6406,12353,16401,17161],[1030,6406,12353,16529,17153],[1030,6406,12353,16641,17553],[1030,6406,12353,16649,17425],[1169,1542,6150,8449,18721],[1169,1542,6150,8513,18689],[1169,1542,6150,12545,16673],[1169,1542,6150,12609,16641],[1169,4102,8449,17926,18721],[1169,4102,8513,17926,18689],[1169,4102,12545,16673,17926],[1169,4102,12609,16641,17926],[1169,4358,8449,17414,18721],[1169,4358,8513,17414,18689],[1169,4358,12545,16673,17414],[1169,4358,12609,16641,17414],[1542,6150,8209,8969,18465],[1542,6150,8337,8961,18465],[1542,6150,8449,9361,18465],[1542,6150,8457,9233,18465],[1542,6150,12353,16401,17161],[1542,6150,12353,16529,17153],[1542,6150,12353,16641,17553],[1542,6150,12353,16649,17425],[4102,8209,8969,17926,18465],[4102,8337,8961,17926,18465],[4102,8449,9361,17926,18465],[4102,8457,9233,17926,18465],[4102,12353,16401,17161,17926],[4102,12353,16529,17153,17926],[4102,12353,16641,17553,17926],[4102,12353,16649,17425,17926],[4358,8209,8969,17414,18465],[4358,8337,8961,17414,18465],[4358,8449,9361,17414,18465],[4358,8457,9233,17414,18465],[4358,12353,16401,17161,17414],[4358,12353,16529,17153,17414],[4358,12353,16641,17414,17553],[4358,12353,16649,17414,17425]]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem validRows : dataOK (SparseFifteen.adj 2) (FiveLP.pool 2) Q R=true := by decide +kernel
def test : Vertex → Bool := (fun a=> listDfs near 4 (R.filter (relation a)) (FiveLP.budget 2-a.cost) [a.mask])
end FiveSearch.FiveData2
namespace FiveSearch.FiveData2
open FP32
def W : List (Nat × Nat) := [(2176,2),(576,2),(8768,3),(2192,3),(2080,2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem covered : guard near (FiveIso.outputs 2) W=true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem wgood : W.all (fun x => decide (x∈inds (SparseFifteen.adj 2)))=true := by decide +kernel
end FiveSearch.FiveData2
namespace FiveSearch.FiveData2
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block0 : ((R.drop 0).take 2).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block1 : ((R.drop 2).take 3).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block2 : ((R.drop 5).take 2).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block3 : ((R.drop 7).take 2).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block4 : ((R.drop 9).take 6).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block5 : ((R.drop 15).take 8).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block6 : ((R.drop 23).take 10).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block7 : ((R.drop 33).take 13).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block8 : ((R.drop 46).take 25).all test = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem block9 : ((R.drop 71).take 8).all test = true := by decide +kernel

set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem checked : R.all test = true := by
  apply splitTest 2
  · exact block0
  apply splitTest 3
  · exact block1
  apply splitTest 2
  · exact block2
  apply splitTest 2
  · exact block3
  apply splitTest 6
  · exact block4
  apply splitTest 8
  · exact block5
  apply splitTest 10
  · exact block6
  apply splitTest 13
  · exact block7
  apply splitTest 25
  · exact block8
  exact block9
end FiveSearch.FiveData2
namespace FiveSearch
open FP32
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem recover (i : Fin 8) {cs : List Nat} (len : cs.length=5)
    (inc : ∀x∈cs,x∈FiveLP.pool i) (ord : cs.Pairwise (·≤·))
    (ok : okContacts 7 (inds (SparseFifteen.adj i)) cs=true)
    (sum : (cs.map (countBits (SparseFifteen.adj i).length)).sum=FiveLP.budget i) :
    cs∈FiveIso.outputs i := by
  rcases i with ⟨j,hj⟩
  rcases (show j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 by omega) with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact recover_from_checks _ _ FiveData0.Q FiveData0.R _ FiveData0.near _ FiveData0.W FiveData0.validRows
      (by decide +kernel) FiveData0.checked FiveData0.wgood FiveData0.covered len inc ord ok sum
  · exact recover_from_checks _ _ FiveData1.Q FiveData1.R _ FiveData1.near _ FiveData1.W FiveData1.validRows
      (by decide +kernel) FiveData1.checked FiveData1.wgood FiveData1.covered len inc ord ok sum
  · exact recover_from_checks _ _ FiveData2.Q FiveData2.R _ FiveData2.near _ FiveData2.W FiveData2.validRows
      (by decide +kernel) FiveData2.checked FiveData2.wgood FiveData2.covered len inc ord ok sum
  all_goals
    cases cs with
    | nil => simp at len
    | cons x xs => exact False.elim (List.not_mem_nil (inc x (.head _)))
end FiveSearch
end

section
namespace OMA.RamseyFinite
open SimpleGraph Finset RamseyNumbers
theorem sorted_graphExtension {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k d : Nat) (ht : G.CliqueFree 3) (hs : Small G A k)
    (r : V) (front base : List V) (hn : (r::front++base).Nodup)
    (hall : (r::front++base).toFinset=A) (hd : front.length=d)
    (ha : ∀ x∈front,G.Adj r x) (hb : ∀ x∈base,¬G.Adj r x)
    (hcount : ∀ x∈front,d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k)
    (_hmin : ∀ x∈A,d≤(A.filter (G.Adj x)).card)
    (_horder : (contactsOf G base front).Pairwise (·≤·)) :
    ∃ cs, Extension k d (encode G base) cs ∧ cs.Pairwise (·≤·) ∧ encode G (r::front++base) = attach cs (encode G base) := by
  let cs := contactsOf G base front
  have split := root_encoding G r front base ha hb ht
  change encode G (r::front++base) = attach cs (encode G base) at split
  have hbnd := (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.1
  have hc (s) (mem : s ∈ cs) : s ∈ usable k d (encode G base) := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp mem
    let S := base.toFinset.filter (G.Adj x)
    have row := inds_complete G base hbnd S (Finset.filter_subset ..) (neighbors_small G ht _ x)
    have m := hcount x hx
    rw [sizeAt_finset G hbnd] at m
    change bits (base.map fun y => decide (G.Adj x y)) ∈ _
    rw [row_mark]
    exact List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨row,by simpa [S] using m⟩,rfl⟩
  have guard_ (u w : List Nat) (h : cs=u++w) : guardRows k (encode G base) (inds (encode G base)) u := by
    let sl := front.take u.length
    have hu : contactsOf G base sl = u := by
      change (front.take u.length).map _=u
      rw [List.map_take, show front.map _=u++w from h, List.take_left]
    have ssub := (List.take_sublist u.length front).append (List.Sublist.refl base)
    have nodup : (sl++base).Nodup := (List.nodup_cons.mp hn).2.sublist ssub
    have sub : (sl++base).toFinset ⊆ A := by
      intro x hx
      rw [← hall]
      exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (ssub.subset (List.mem_toFinset.mp hx)))
    have ha' (x) (hx : x∈sl) := ha x ((List.take_sublist u.length front).subset hx)
    have indep : Gᶜ.IsClique (sl.toFinset : Set V) := by
      rw [G.isClique_compl]
      intro x hx y hy hxy
      exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x (List.mem_toFinset.mp hx)) (ha' y (List.mem_toFinset.mp hy)) hxy
    have em := contacts G sl base (by intro x hx y hy adj; exact G.isIndepSet_neighborSet_of_triangleFree ht r (ha' x hx) (ha' y hy) adj.ne adj)
    change encode G (sl++base)=shifted (contactsOf G base sl)++encode G base at em
    rw [← hu]
    apply Bool.and_eq_true_iff.mpr
    refine ⟨ok_contacts G A k hs sl base nodup sub indep,?_⟩
    rw [← em]
    exact degrees_bound G ht A k hs _ nodup sub
  exact ⟨cs, ⟨by simp [cs,contactsOf,hd], hc,
    (Bool.and_eq_true_iff.mp (guard_ cs [] (by simp))).1⟩, _horder, split⟩
end OMA.RamseyFinite
end

section
namespace Sparse32
open SimpleGraph OMA.RamseyFinite

theorem bits_glue (xs : List Bool) : bits xs=GlueSeed.bits xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [bits,GlueSeed.bits,ih]
theorem encode_glue {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (vs : List V) :
    encode G vs=GlueSeed.encode G vs := by
  induction vs with
  | nil => rfl
  | cons x xs ih => simp only [encode,GlueSeed.encode,bits_glue,ih]
end Sparse32
end

section
namespace Sparse32
open OMA.RamseyFinite SimpleGraph Finset

theorem edge_card {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (vs : List V) (nd : vs.Nodup) (allv : vs.toFinset=univ) :
    edges_ (encode G vs)=G.edgeFinset.card := by
  have h : degrees (encode G vs)=vs.map (fun x => G.degree x) := by
    rw [degrees_encode]
    apply List.map_congr_left
    intro x _
    rw [sizeAt_finset G nd,allv,← SimpleGraph.neighborFinset_eq_filter,
       SimpleGraph.card_neighborFinset_eq_degree]
  have h' := congrArg List.sum h
  rw [energy,← List.sum_toFinset _ nd,allv,G.sum_degrees_eq_twice_card_edges] at h'
  omega
end Sparse32
end

section
namespace Sparse32
open OMA.RamseyFinite SimpleGraph Finset

theorem toPure_inds (b : List Nat) : inds b = FP32.inds b := by
  induction b with
  | nil => rfl
  | cons m b ih => simp only [inds,FP32.inds,ih]; rfl

theorem toPure_count (n x : Nat) : countBits n x = FP32.countBits n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [countBits,FP32.countBits,ih]

theorem toPure_edges (b : List Nat) : edges_ b = FP32.edges_ b := by
  induction b with
  | nil => rfl
  | cons m b ih => simp only [edges_,FP32.edges_,toPure_count,ih]

theorem toPure_shifted (cs : List Nat) : shifted cs = FP32.shifted cs := by
  induction cs with
  | nil => rfl
  | cons m cs ih => simp only [shifted,FP32.shifted,ih]

theorem toPure_attach (cs b : List Nat) : attach cs b = FP32.attach cs b := by
  simp only [OMA.RamseyFinite.attach,FP32.attach,toPure_shifted]

theorem toPure_ext {k d : Nat} {b cs : List Nat} (h : Extension k d b cs) :
    FP32.Extension k d b cs := by
  simpa only [Extension,FP32.Extension,usable,FP32.usable,toPure_inds,okContacts,FP32.okContacts] using h

theorem toPure_exchange (i x : Nat) : exchange i x = FP32.exchange i x := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih => simp only [exchange,FP32.exchange,ih]

theorem toPure_swap (i : Nat) (b : List Nat) : swapCode i b = FP32.swapCode i b := by
  induction i generalizing b with
  | zero =>
    cases b with
    | nil => rfl
    | cons b bs => cases bs <;> rfl
  | succ i ih =>
    cases b with
    | nil => rfl
    | cons b bs => simp only [swapCode,FP32.swapCode,toPure_exchange,ih]

theorem toPure_relabel (s b : List Nat) : relabel s b = FP32.relabel s b := by
  simp only [relabel,FP32.relabel,toPure_swap]
end Sparse32
end

section
namespace SparseFifteen
structure RowCase where
  base : List Nat
  outputs : List (List Nat)
def pair0 : RowCase := ⟨[7,24,130,145,3,2,6,3,2,2,1,0],[[1,14],[2,97],[4,1041],[6,1025],[12,17],[18,96],[32,146],[33,130],[128,800],[192,768],[512,2240],[544,2176],[1024,2308],[1032,2304],[1536,2052],[1544,2048]]⟩
def pair1 : RowCase := ⟨[7,24,146,145,3,2,6,3,2,2,1,0],[]⟩
def pair2 : RowCase := ⟨[7,24,194,145,3,2,6,3,2,2,1,0],[]⟩
def pair3 : RowCase := ⟨[7,280,146,145,3,2,6,3,2,2,1,0],[]⟩
def pair4 : RowCase := ⟨[7,280,194,137,3,2,6,3,2,2,1,0],[]⟩
def pair5 : RowCase := ⟨[7,24,98,137,3,12,9,3,2,2,1,0],[]⟩
def pair6 : RowCase := ⟨[7,132,268,137,3,12,9,3,2,2,1,0],[]⟩
def pair7 : RowCase := ⟨[7,388,258,134,3,12,9,3,2,2,1,0],[]⟩
def pairs : List RowCase := [pair0,pair1,pair2,pair3,pair4,pair5,pair6,pair7]
def triple0 : RowCase := ⟨[3,128,144,3,2,6,3,2,2,1,0],[[6,9,49],[6,9,561],[6,9,1073],[6,17,73],[6,17,585],[6,17,1097],[6,33,393],[6,49,73],[6,49,137],[6,49,265],[6,49,521],[6,49,1033],[6,65,401],[6,73,145],[6,73,273],[6,73,529],[6,73,1041],[6,97,385],[6,257,1121],[6,265,1057],[6,273,1089],[9,14,48],[9,14,49],[9,14,50],[9,14,52],[9,14,560],[9,14,1072],[9,22,49],[9,38,49],[9,48,78],[9,48,270],[9,49,70],[9,49,262],[10,48,521],[10,48,585],[10,48,777],[10,49,521],[10,50,513],[10,50,521],[10,50,529],[10,50,545],[10,50,577],[10,50,769],[10,52,521],[10,54,513],[10,513,1074],[10,521,560],[10,521,1072],[12,48,1161],[12,52,1153],[14,17,73],[14,48,73],[14,48,137],[14,48,265],[14,48,521],[14,48,1033],[14,50,513],[17,22,72],[17,22,73],[17,22,74],[17,22,76],[17,22,584],[17,22,1096],[17,38,73],[17,54,72],[17,70,73],[17,72,278],[17,73,262],[18,72,529],[18,72,561],[18,72,785],[18,73,529],[18,74,513],[18,74,521],[18,74,529],[18,74,545],[18,74,577],[18,74,769],[18,76,529],[18,78,513],[18,513,1098],[18,529,584],[18,529,1096],[20,72,1169],[20,76,1153],[22,49,72],[22,72,145],[22,72,273],[22,72,529],[22,72,1041],[22,74,513],[33,38,392],[34,392,545],[34,394,513],[48,74,521],[48,138,521],[48,266,521],[48,268,1033],[48,520,1162],[48,521,1034],[48,524,1160],[48,776,1034],[48,780,1032],[50,72,529],[50,74,513],[50,138,513],[50,266,513],[50,513,1034],[65,70,400],[66,400,577],[66,402,513],[72,146,529],[72,274,529],[72,276,1041],[72,528,1170],[72,529,1042],[72,532,1168],[72,784,1042],[72,788,1040],[74,146,513],[74,274,513],[74,513,1042],[98,386,513],[257,262,1120],[258,513,1122],[258,769,1120],[266,513,1058],[274,513,1090],[520,560,1154],[528,584,1154],[772,1032,1072],[772,1040,1096]]⟩
def triple1 : RowCase := ⟨[3,128,146,3,2,6,3,2,2,1,0],[[6,9,49],[6,17,73],[9,14,48],[10,48,521],[10,50,513],[18,72,529],[18,74,513]]⟩
def triple2 : RowCase := ⟨[3,64,140,3,2,6,3,2,2,1,0],[[6,9,49],[6,17,73],[6,513,1153],[9,14,48],[10,48,265],[10,50,257],[17,22,72],[18,72,273],[18,74,257],[48,520,1160],[72,528,1168],[257,514,1154],[513,518,1152],[514,769,1152],[520,560,1152],[528,584,1152]]⟩
def triple3 : RowCase := ⟨[3,192,144,3,2,6,3,2,2,1,0],[[6,9,49],[6,17,73],[9,14,48],[10,48,521],[10,50,513],[12,48,1033],[12,52,1025],[17,22,72],[18,72,529],[18,74,513],[20,72,1041],[20,76,1025]]⟩
def triple4 : RowCase := ⟨[3,192,140,3,2,6,3,2,2,1,0],[]⟩
def triple5 : RowCase := ⟨[3,192,130,3,2,6,3,2,2,1,0],[[6,9,49],[6,17,73],[9,14,48],[12,48,1033]]⟩
def triple6 : RowCase := ⟨[3,192,146,3,2,6,3,2,2,1,0],[]⟩
def triple7 : RowCase := ⟨[3,192,134,3,2,6,3,2,2,1,0],[]⟩
def triple8 : RowCase := ⟨[3,96,140,3,2,6,3,2,2,1,0],[]⟩
def triple9 : RowCase := ⟨[3,144,146,3,2,6,3,2,2,1,0],[]⟩
def triple10 : RowCase := ⟨[3,144,145,3,2,6,3,2,2,1,0],[]⟩
def triple11 : RowCase := ⟨[3,132,129,3,2,6,3,2,2,1,0],[]⟩
def triple12 : RowCase := ⟨[3,132,145,3,2,6,3,2,2,1,0],[]⟩
def triple13 : RowCase := ⟨[3,68,136,3,2,6,3,2,2,1,0],[[6,9,49],[6,513,1153],[9,14,48],[48,520,1160],[513,518,1152],[520,560,1152]]⟩
def triple14 : RowCase := ⟨[3,68,140,3,2,6,3,2,2,1,0],[]⟩
def triple15 : RowCase := ⟨[3,128,145,3,12,9,3,2,2,1,0],[]⟩
def triple16 : RowCase := ⟨[3,192,144,3,12,9,3,2,2,1,0],[]⟩
def triple17 : RowCase := ⟨[3,192,129,3,12,9,3,2,2,1,0],[]⟩
def triple18 : RowCase := ⟨[3,32,137,3,12,9,3,2,2,1,0],[]⟩
def triple19 : RowCase := ⟨[3,96,136,3,12,9,3,2,2,1,0],[]⟩
def triple20 : RowCase := ⟨[3,2,134,3,12,9,3,2,2,1,0],[]⟩
def triple21 : RowCase := ⟨[3,130,144,3,12,9,3,2,2,1,0],[]⟩
def triple22 : RowCase := ⟨[3,130,132,3,12,9,3,2,2,1,0],[]⟩
def triple23 : RowCase := ⟨[3,34,136,3,12,9,3,2,2,1,0],[]⟩
def triple24 : RowCase := ⟨[7,72,66,73,1,1,3,2,2,1,0],[]⟩
def triple25 : RowCase := ⟨[7,68,68,73,1,1,3,2,2,1,0],[]⟩
def triples : List RowCase := [triple0,triple1,triple2,triple3,triple4,triple5,triple6,triple7,triple8,triple9,triple10,triple11,triple12,triple13,triple14,triple15,triple16,triple17,triple18,triple19,triple20,triple21,triple22,triple23,triple24,triple25]
end SparseFifteen
end

section
namespace SparseFifteen
structure FinalMove where
  source : List Nat
  steps : List Nat
  index : Fin 8
def isFinal (m : FinalMove) := FP32.relabel m.steps m.source == adj m.index
end SparseFifteen
end

section
namespace SparseFifteen
def moves0 : List FinalMove := [
⟨[3,2,14,7,24,130,145,3,2,6,3,2,2,1,0],[],0⟩,
⟨[3,4,97,7,24,130,145,3,2,6,3,2,2,1,0],[3,7,6,5,8,7,6,8,7,12,11,10,11,13,12],0⟩,
⟨[3,8,1041,7,24,130,145,3,2,6,3,2,2,1,0],[4,3,12,11,10,9,8,7,6,5,4,7,6,7,13,12,11,10,9,8,12,11,10,9,13,12,11,10,12,11,13,12],0⟩,
⟨[3,12,1025,7,24,130,145,3,2,6,3,2,2,1,0],[],1⟩,
⟨[3,24,17,7,24,130,145,3,2,6,3,2,2,1,0],[],2⟩,
⟨[3,36,96,7,24,130,145,3,2,6,3,2,2,1,0],[7,6,5,4,3,9,8,7,6,5,4,5,8,7,6,9,8,7,11,10,9,8,11,10,9,13,12,11,10,12,11,13,12],2⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound0 : moves0.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves1 : List FinalMove := [
⟨[3,64,146,7,24,130,145,3,2,6,3,2,2,1,0],[7,6,5,4,3,9,8,7,6,5,4,5,8,7,6,9,8,7,11,10,9,8,11,10,9,13,12,11,10,12,11,13,12],0⟩,
⟨[3,66,130,7,24,130,145,3,2,6,3,2,2,1,0],[3,7,6,5,8,7,6,8,7,12,11,10,11,13,12],1⟩,
⟨[3,256,800,7,24,130,145,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,11,10,9,8,7,8,11,10,9,11,13],0⟩,
⟨[3,384,768,7,24,130,145,3,2,6,3,2,2,1,0],[11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,12,11,10,9,8,7,13,12,11,10,9,8,11,10,9,11,10,12,11,13],2⟩,
⟨[3,1024,2240,7,24,130,145,3,2,6,3,2,2,1,0],[11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,12,11,10,9,8,7,13,12,11,10,9,8,11,10,9,11,10,12,11,13],0⟩,
⟨[3,1088,2176,7,24,130,145,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,11,10,9,8,7,8,11,10,9,11,13],1⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound1 : moves1.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves2 : List FinalMove := [
⟨[3,2048,2308,7,24,130,145,3,2,6,3,2,2,1,0],[12,11,10,9,8,7,6,5,4,3,5,4,13,12,11,10,9,8,7,6,5,12,11,10,9,8,7,6,8,7,9,11,13],0⟩,
⟨[3,2064,2304,7,24,130,145,3,2,6,3,2,2,1,0],[13,12,11,10,9,8,7,6,5,4,3,12,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,8,7,6,13,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,13,12,11,12,13],2⟩,
⟨[3,3072,2052,7,24,130,145,3,2,6,3,2,2,1,0],[1,12,11,10,9,8,7,6,5,4,3,5,4,13,12,11,10,9,8,7,6,5,12,11,10,9,8,7,6,8,7,9,11,13],1⟩,
⟨[3,3088,2048,7,24,130,145,3,2,6,3,2,2,1,0],[1,13,12,11,10,9,8,7,6,5,4,3,12,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,8,7,6,13,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,13,12,11,12,13],0⟩,
⟨[7,24,18,49,3,128,144,3,2,6,3,2,2,1,0],[],3⟩,
⟨[7,24,18,561,3,128,144,3,2,6,3,2,2,1,0],[],4⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound2 : moves2.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves3 : List FinalMove := [
⟨[7,24,18,1073,3,128,144,3,2,6,3,2,2,1,0],[7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,5,4,3,9,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,8,7,9,11,13],4⟩,
⟨[7,24,34,73,3,128,144,3,2,6,3,2,2,1,0],[7,9],3⟩,
⟨[7,24,34,585,3,128,144,3,2,6,3,2,2,1,0],[7,9],4⟩,
⟨[7,24,34,1097,3,128,144,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,5,4,3,9,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,8,7,9,11,13],4⟩,
⟨[7,24,66,393,3,128,144,3,2,6,3,2,2,1,0],[7,6,5,4,3,2,1,0,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,11,10,9,8,7,6,5,8,7,6,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,13,12,11,12,13],2⟩,
⟨[7,24,98,73,3,128,144,3,2,6,3,2,2,1,0],[],5⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound3 : moves3.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves4 : List FinalMove := [
⟨[7,24,98,137,3,128,144,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,11,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,11,10,9,8,7,6,5,7,6,13,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,13,12,11,12,13],4⟩,
⟨[7,24,98,265,3,128,144,3,2,6,3,2,2,1,0],[],6⟩,
⟨[7,24,98,521,3,128,144,3,2,6,3,2,2,1,0],[13,12,11,10,9,8,7,6,5,4,3,2,1,0,12,11,10,9,8,7,6,5,4,3,2,1,7,6,5,4,3,2,13,12,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,13,12,11,10,9,8,7,6,11,10,9,8,7,8,11,10,9,13],6⟩,
⟨[7,24,98,1033,3,128,144,3,2,6,3,2,2,1,0],[],7⟩,
⟨[7,24,130,401,3,128,144,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,7,6,5,4,3,2,1,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,11,10,9,8,7,6,5,8,7,6,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,13,12,11,12,13],2⟩,
⟨[7,24,146,145,3,128,144,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,2,1,0,7,6,5,4,3,2,1,11,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,11,10,9,8,7,6,5,7,6,13,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,13,12,11,12,13],4⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound4 : moves4.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves5 : List FinalMove := [
⟨[7,24,146,273,3,128,144,3,2,6,3,2,2,1,0],[7,9],6⟩,
⟨[7,24,146,529,3,128,144,3,2,6,3,2,2,1,0],[13,12,11,10,9,8,7,6,5,4,3,2,1,0,12,11,10,9,8,7,6,5,4,3,2,1,7,6,5,4,3,2,13,12,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,12,11,10,9,8,7,6,5,13,12,11,10,9,8,7,6,11,10,9,8,7,8,11,10,9],6⟩,
⟨[7,24,146,1041,3,128,144,3,2,6,3,2,2,1,0],[7,9],7⟩,
⟨[7,24,194,385,3,128,144,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,7,6,5,4,3,2,1,8,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,8,7,9,11,13],0⟩,
⟨[7,24,514,1121,3,128,144,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,7,6,5,4,3,2,1,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,11,10,9,8,7,6,5,8,7,6,13,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,13,12,11,12,13],0⟩,
⟨[7,24,530,1057,3,128,144,3,2,6,3,2,2,1,0],[7,6,5,4,3,2,1,0,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,5,4,10,9,8,7,6,5,13,12,11,10,9,8,7,6,8,7,9,11],1⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound5 : moves5.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves6 : List FinalMove := [
⟨[7,24,546,1089,3,128,144,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,7,6,5,4,3,2,1,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,5,4,10,9,8,7,6,5,13,12,11,10,9,8,7,6,8,7,9,11],1⟩,
⟨[7,36,28,48,3,128,144,3,2,6,3,2,2,1,0],[2,1,6,5,4,7,6,5,8,7,6,12,11,10,11,13,12],3⟩,
⟨[7,36,28,49,3,128,144,3,2,6,3,2,2,1,0],[4,3,2,1,0,12,11,10,9,8,7,6,5,4,3,2,1,3,2,5,4,3,6,5,4,13,12,11,10,9,8,7,6,5,12,11,10,9,8,7,6,7,9,11,13],5⟩,
⟨[7,36,28,50,3,128,144,3,2,6,3,2,2,1,0],[7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,5,4,3,9,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,11,13],6⟩,
⟨[7,36,28,52,3,128,144,3,2,6,3,2,2,1,0],[3,2,1,0,1,4,3,2,5,4,3,4,6,12,11,10,9,8,7,13,12,11,10,9,8,12,11,10,9,13,12,11,10,12,11,13,12],4⟩,
⟨[7,36,28,560,3,128,144,3,2,6,3,2,2,1,0],[7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,5,4,3,9,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,11,13],7⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound6 : moves6.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves7 : List FinalMove := [
⟨[7,36,28,1072,3,128,144,3,2,6,3,2,2,1,0],[12,11,10,9,8,7,6,5,4,3,2,1,0,5,4,3,2,1,11,10,9,8,7,6,5,4,3,2,13,12,11,10,9,8,7,6,5,4,3,8,7,6,5,4,8,7,6,5,7,6,13,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,13,12,11,13,12,13],6⟩,
⟨[7,36,44,49,3,128,144,3,2,6,3,2,2,1,0],[4,3,2,1,0,12,11,10,9,8,7,6,5,4,3,2,1,5,4,3,2,4,3,6,5,4,13,12,11,10,9,8,7,6,5,12,11,10,9,8,7,6,11,13],6⟩,
⟨[7,36,76,49,3,128,144,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,1,7,6,5,4,3,2,8,7,6,5,4,3,5,4,6,9,8,7,11,10,9,8,11,10,9,13,12,11,10,12,11,13,12],4⟩,
⟨[7,36,96,78,3,128,144,3,2,6,3,2,2,1,0],[1,6,5,4,7,6,5,8,7,6,12,11,10,11,13,12],4⟩,
⟨[7,36,96,270,3,128,144,3,2,6,3,2,2,1,0],[4,3,2,1,0,12,11,10,9,8,7,6,5,4,3,2,1,5,4,3,2,5,4,3,6,5,4,13,12,11,10,9,8,7,6,5,12,11,10,9,8,7,6,7,9,11,13],4⟩,
⟨[7,36,98,70,3,128,144,3,2,6,3,2,2,1,0],[4,3,2,1,0,12,11,10,9,8,7,6,5,4,3,2,1,5,4,3,2,5,4,3,6,5,4,13,12,11,10,9,8,7,6,5,12,11,10,9,8,7,6,11,13],7⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound7 : moves7.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves8 : List FinalMove := [
⟨[7,36,98,262,3,128,144,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,11,10,9,8,7,6,5,7,6,13,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,13,12,11,13,12,13],6⟩,
⟨[7,40,96,521,3,128,144,3,2,6,3,2,2,1,0],[1,6,5,4,7,6,5,8,7,6,7,12,11,10,9,11,13,12],3⟩,
⟨[7,40,96,585,3,128,144,3,2,6,3,2,2,1,0],[1,6,5,4,7,6,5,8,7,6,7,12,11,10,9,11,13,12],4⟩,
⟨[7,40,96,777,3,128,144,3,2,6,3,2,2,1,0],[3,2,1,0,5,4,3,2,1,5,4,3,2,5,4,3,12,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,12,11,10,9,8,7,6,7,9,11,13],4⟩,
⟨[7,40,98,521,3,128,144,3,2,6,3,2,2,1,0],[7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,4,3,9,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,10,12,11,13],6⟩,
⟨[7,40,100,513,3,128,144,3,2,6,3,2,2,1,0],[2,1,4,12,11,10,9,8,7,6,7,8,9,10,11,12],3⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound8 : moves8.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves9 : List FinalMove := [
⟨[7,40,100,521,3,128,144,3,2,6,3,2,2,1,0],[7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,3,2,8,7,6,5,4,3,9,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,7,10,9,12,11,13],5⟩,
⟨[7,40,100,529,3,128,144,3,2,6,3,2,2,1,0],[3,2,1,0,5,4,3,2,1,5,4,3,2,5,4,3,12,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,12,11,10,9,8,7,6,11,13],6⟩,
⟨[7,40,100,545,3,128,144,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,1,7,6,5,4,3,2,8,7,6,5,4,3,4,7,6,9,8,7,11,10,9,8,11,10,9,13,12,11,10,13,12,11,13,12],4⟩,
⟨[7,40,100,577,3,128,144,3,2,6,3,2,2,1,0],[3,2,1,0,5,4,3,2,1,5,4,3,2,5,4,3,12,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,12,11,10,9,8,7,6,11,13],7⟩,
⟨[7,40,100,769,3,128,144,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,11,10,9,8,7,6,5,7,6,13,12,11,10,9,8,7,12,11,10,9,8,13,12,11,10,9,12,11,10,13,12,11,13,12,13],6⟩,
⟨[7,40,104,521,3,128,144,3,2,6,3,2,2,1,0],[7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,4,3,9,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,10,12,11,13],7⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound9 : moves9.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves10 : List FinalMove := [
⟨[7,40,108,513,3,128,144,3,2,6,3,2,2,1,0],[2,1,4,12,11,10,9,8,7,6,7,8,9,10,11,12],4⟩,
⟨[7,40,1026,1074,3,128,144,3,2,6,3,2,2,1,0],[7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,5,4,3,9,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,7,10,9,12,11,13],4⟩,
⟨[7,40,1042,560,3,128,144,3,2,6,3,2,2,1,0],[4,3,2,1,0,1,4,3,2,12,11,10,9,8,7,6,5,4,3,4,7,6,7,13,12,11,10,9,8,12,11,10,9,13,12,11,10,12,11,13,12],4⟩,
⟨[7,40,1042,1072,3,128,144,3,2,6,3,2,2,1,0],[5,4,3,2,1,0,4,3,2,1,10,9,8,7,6,5,4,3,2,13,12,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,8,7,6,5,7,6,13,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,13,12,11,13,12,13],6⟩,
⟨[7,48,96,1161,3,128,144,3,2,6,3,2,2,1,0],[4,3,2,1,0,4,3,2,1,12,11,10,9,8,7,6,5,4,3,2,13,12,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,8,7,6,5,8,7,6,13,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,13,12,11,13,12,13],2⟩,
⟨[7,48,104,1153,3,128,144,3,2,6,3,2,2,1,0],[4,3,2,1,0,4,3,2,1,12,11,10,9,8,7,6,5,4,3,2,13,12,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,7,6,5,8,7,6,13,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,12,11,13,12],2⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound10 : moves10.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves11 : List FinalMove := [
⟨[7,56,34,73,3,128,144,3,2,6,3,2,2,1,0],[4,3,2,1,0,12,11,10,9,8,7,6,5,4,3,2,1,5,4,3,2,3,6,5,4,13,12,11,10,9,8,7,6,5,12,11,10,9,8,7,6,10,12,11,13],6⟩,
⟨[7,56,96,73,3,128,144,3,2,6,3,2,2,1,0],[11,10,9,8,7,6,5,4,3,2,1,0,13,12,11,10,9,8,7,6,5,4,3,2,1,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,12,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,11,10,9,8,7,6,13,12,11,10,9,8,7,9,8,13,12,11,10,9,13],6⟩,
⟨[7,56,96,137,3,128,144,3,2,6,3,2,2,1,0],[12,11,10,9,8,7,6,5,4,3,2,1,0,5,4,3,2,1,13,12,11,10,9,8,7,6,5,4,3,2,12,11,10,9,8,7,6,5,4,3,8,7,6,5,4,8,7,6,5,6,13,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,13,12,11,12,13],4⟩,
⟨[7,56,96,265,3,128,144,3,2,6,3,2,2,1,0],[1,6,5,4,7,6,5,8,7,6,12,11,10,11,13,12],7⟩,
⟨[7,56,96,521,3,128,144,3,2,6,3,2,2,1,0],[1,6,5,4,7,6,5,8,7,6,12,11,10,11,13,12],5⟩,
⟨[7,56,96,1033,3,128,144,3,2,6,3,2,2,1,0],[1,6,5,4,7,6,5,8,7,6,12,11,10,11,13,12],6⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound11 : moves11.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves12 : List FinalMove := [
⟨[7,56,100,513,3,128,144,3,2,6,3,2,2,1,0],[13,12,11,10,9,8,7,6,5,4,3,2,1,0,12,11,10,9,8,7,6,5,4,3,2,1,13,12,11,10,9,8,7,6,5,4,3,2,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,13,12,11,10,9,8,7,6,10,9,8,7,10,9,8,11,10,9,11,13],6⟩,
⟨[7,68,44,72,3,128,144,3,2,6,3,2,2,1,0],[2,1,7,6,5,4,7,6,5,9,8,7,6,12,11,10,11,13,12],3⟩,
⟨[7,68,44,73,3,128,144,3,2,6,3,2,2,1,0],[4,3,2,1,0,12,11,10,9,8,7,6,5,4,3,2,1,3,2,5,4,3,6,5,4,13,12,11,10,9,8,7,6,5,12,11,10,9,8,7,6,7,10,9,12,11,13],5⟩,
⟨[7,68,44,74,3,128,144,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,5,4,3,9,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,11,13],6⟩,
⟨[7,68,44,76,3,128,144,3,2,6,3,2,2,1,0],[3,2,1,0,1,4,3,2,5,4,3,4,7,6,12,11,10,9,8,7,13,12,11,10,9,8,12,11,10,9,13,12,11,10,13,12,11,13,12],4⟩,
⟨[7,68,44,584,3,128,144,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,5,4,3,9,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,11,13],7⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound12 : moves12.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves13 : List FinalMove := [
⟨[7,68,44,1096,3,128,144,3,2,6,3,2,2,1,0],[12,11,10,9,8,7,6,5,4,3,2,1,0,5,4,3,2,1,11,10,9,8,7,6,5,4,3,2,13,12,11,10,9,8,7,6,5,4,3,8,7,6,5,4,8,7,6,5,7,6,13,12,11,10,9,8,7,12,11,10,9,8,13,12,11,10,9,12,11,10,13,12,11,13,12,13],6⟩,
⟨[7,68,76,73,3,128,144,3,2,6,3,2,2,1,0],[4,3,2,1,0,12,11,10,9,8,7,6,5,4,3,2,1,5,4,3,2,4,3,6,5,4,13,12,11,10,9,8,7,6,5,12,11,10,9,8,7,6,10,12,11,13],7⟩,
⟨[7,68,108,72,3,128,144,3,2,6,3,2,2,1,0],[2,1,7,6,5,4,7,6,5,9,8,7,6,12,11,10,11,13,12],4⟩,
⟨[7,68,140,73,3,128,144,3,2,6,3,2,2,1,0],[7,6,5,4,3,2,1,0,1,7,6,5,4,3,2,9,8,7,6,5,4,3,5,4,6,9,8,7,11,10,9,8,11,10,9,13,12,11,10,12,11,13,12],4⟩,
⟨[7,68,144,278,3,128,144,3,2,6,3,2,2,1,0],[4,3,2,1,0,12,11,10,9,8,7,6,5,4,3,2,1,5,4,3,2,5,4,3,6,5,4,13,12,11,10,9,8,7,6,5,12,11,10,9,8,7,6,7,10,9,12,11,13],4⟩,
⟨[7,68,146,262,3,128,144,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,2,1,0,7,6,5,4,3,2,1,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,11,10,9,8,7,6,5,7,6,13,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,13,12,11,13,12,13],6⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound13 : moves13.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves14 : List FinalMove := [
⟨[7,72,144,529,3,128,144,3,2,6,3,2,2,1,0],[1,7,6,5,4,7,6,5,9,8,7,6,7,12,11,10,9,11,13,12],3⟩,
⟨[7,72,144,561,3,128,144,3,2,6,3,2,2,1,0],[1,7,6,5,4,7,6,5,9,8,7,6,7,12,11,10,9,11,13,12],4⟩,
⟨[7,72,144,785,3,128,144,3,2,6,3,2,2,1,0],[3,2,1,0,5,4,3,2,1,5,4,3,2,5,4,3,12,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,12,11,10,9,8,7,6,7,10,9,12,11,13],4⟩,
⟨[7,72,146,529,3,128,144,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,4,3,9,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,10,12,11,13],6⟩,
⟨[7,72,148,513,3,128,144,3,2,6,3,2,2,1,0],[2,1,4,12,11,10,9,8,7,6,8,7,8,10,9,10,11,12],3⟩,
⟨[7,72,148,521,3,128,144,3,2,6,3,2,2,1,0],[3,2,1,0,5,4,3,2,1,5,4,3,2,5,4,3,12,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,12,11,10,9,8,7,6,10,12,11,13],6⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound14 : moves14.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves15 : List FinalMove := [
⟨[7,72,148,529,3,128,144,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,3,2,8,7,6,5,4,3,9,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,7,10,9,12,11,13],5⟩,
⟨[7,72,148,545,3,128,144,3,2,6,3,2,2,1,0],[3,2,1,0,5,4,3,2,1,5,4,3,2,5,4,3,12,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,12,11,10,9,8,7,6,10,12,11,13],7⟩,
⟨[7,72,148,577,3,128,144,3,2,6,3,2,2,1,0],[7,6,5,4,3,2,1,0,1,7,6,5,4,3,2,9,8,7,6,5,4,3,4,7,6,9,8,7,11,10,9,8,11,10,9,13,12,11,10,13,12,11,13,12],4⟩,
⟨[7,72,148,769,3,128,144,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,2,1,0,7,6,5,4,3,2,1,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,11,10,9,8,7,6,5,7,6,13,12,11,10,9,8,7,12,11,10,9,8,13,12,11,10,9,12,11,10,13,12,11,13,12,13],6⟩,
⟨[7,72,152,529,3,128,144,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,4,3,9,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,10,12,11,13],7⟩,
⟨[7,72,156,513,3,128,144,3,2,6,3,2,2,1,0],[2,1,4,12,11,10,9,8,7,6,8,7,8,10,9,10,11,12],4⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound15 : moves15.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves16 : List FinalMove := [
⟨[7,72,1026,1098,3,128,144,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,5,4,3,9,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,7,10,9,12,11,13],4⟩,
⟨[7,72,1058,584,3,128,144,3,2,6,3,2,2,1,0],[4,3,2,1,0,1,4,3,2,12,11,10,9,8,7,6,5,4,3,4,8,7,6,7,13,12,11,10,9,8,12,11,10,9,13,12,11,10,13,12,11,13,12],4⟩,
⟨[7,72,1058,1096,3,128,144,3,2,6,3,2,2,1,0],[5,4,3,2,1,0,4,3,2,1,10,9,8,7,6,5,4,3,2,13,12,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,8,7,6,5,7,6,13,12,11,10,9,8,7,12,11,10,9,8,13,12,11,10,9,12,11,10,13,12,11,13,12,13],6⟩,
⟨[7,80,144,1169,3,128,144,3,2,6,3,2,2,1,0],[4,3,2,1,0,4,3,2,1,12,11,10,9,8,7,6,5,4,3,2,13,12,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,8,7,6,5,8,7,6,13,12,11,10,9,8,7,12,11,10,9,8,13,12,11,10,9,12,11,10,13,12,11,13,12,13],2⟩,
⟨[7,80,152,1153,3,128,144,3,2,6,3,2,2,1,0],[4,3,2,1,0,4,3,2,1,12,11,10,9,8,7,6,5,4,3,2,13,12,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,7,6,5,8,7,6,13,12,11,10,9,8,7,12,11,10,9,8,13,12,11,10,9,12,11,10,12,11,13,12],2⟩,
⟨[7,88,98,72,3,128,144,3,2,6,3,2,2,1,0],[11,10,9,8,7,6,5,4,3,2,1,0,13,12,11,10,9,8,7,6,5,4,3,2,1,11,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,12,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,11,10,9,8,7,6,12,11,10,9,8,7,10,9,8,13,12,11,10,9,13],6⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound16 : moves16.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves17 : List FinalMove := [
⟨[7,88,144,145,3,128,144,3,2,6,3,2,2,1,0],[12,11,10,9,8,7,6,5,4,3,2,1,0,5,4,3,2,1,13,12,11,10,9,8,7,6,5,4,3,2,12,11,10,9,8,7,6,5,4,3,8,7,6,5,4,8,7,6,5,6,13,12,11,10,9,8,7,12,11,10,9,8,13,12,11,10,9,12,11,10,13,12,11,12,13],4⟩,
⟨[7,88,144,273,3,128,144,3,2,6,3,2,2,1,0],[1,7,6,5,4,7,6,5,9,8,7,6,12,11,10,11,13,12],7⟩,
⟨[7,88,144,529,3,128,144,3,2,6,3,2,2,1,0],[1,7,6,5,4,7,6,5,9,8,7,6,12,11,10,11,13,12],5⟩,
⟨[7,88,144,1041,3,128,144,3,2,6,3,2,2,1,0],[1,7,6,5,4,7,6,5,9,8,7,6,12,11,10,11,13,12],6⟩,
⟨[7,88,148,513,3,128,144,3,2,6,3,2,2,1,0],[13,12,11,10,9,8,7,6,5,4,3,2,1,0,12,11,10,9,8,7,6,5,4,3,2,1,13,12,11,10,9,8,7,6,5,4,3,2,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,12,11,10,9,8,7,6,5,13,12,11,10,9,8,7,6,10,9,8,7,10,9,8,11,10,9,11],6⟩,
⟨[7,132,76,392,3,128,144,3,2,6,3,2,2,1,0],[7,6,5,4,3,2,1,0,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,7,6,5,11,10,9,8,7,6,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,12,11,13,12],2⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound17 : moves17.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves18 : List FinalMove := [
⟨[7,136,784,545,3,128,144,3,2,6,3,2,2,1,0],[7,6,5,4,3,2,1,0,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,6,5,11,10,9,8,7,6,12,11,10,9,8,7,12,11,10,9,8,13,12,11,10,9,12,11,10,12,11,13,12],2⟩,
⟨[7,136,788,513,3,128,144,3,2,6,3,2,2,1,0],[7,6,5,4,3,2,1,0,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,11,10,9,8,7,6,5,7,6,12,11,10,9,8,7,12,11,10,9,8,13,12,11,10,9,12,11,10,13,12,11,13,12,13],2⟩,
⟨[7,192,148,521,3,128,144,3,2,6,3,2,2,1,0],[11,10,9,8,7,6,5,4,3,2,1,0,13,12,11,10,9,8,7,6,5,4,3,2,1,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,12,11,10,9,8,7,6,5,4,10,9,8,7,6,5,13,12,11,10,9,8,7,6,13,12,11,10,9,8,7,8,13,12,11,10,9,11],6⟩,
⟨[7,192,276,521,3,128,144,3,2,6,3,2,2,1,0],[5,4,3,2,1,0,4,3,2,1,13,12,11,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,8,7,6,5,8,7,6,13,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,13,12,11,12,13],4⟩,
⟨[7,192,532,521,3,128,144,3,2,6,3,2,2,1,0],[2,6,5,4,7,6,5,8,7,6,7,12,11,10,9,11,13,12],7⟩,
⟨[7,192,536,1033,3,128,144,3,2,6,3,2,2,1,0],[4,3,2,1,0,4,3,2,1,12,11,10,9,8,7,6,5,4,3,2,13,12,11,10,9,8,7,6,5,4,3,6,5,4,7,6,5,13,12,11,10,9,8,7,6,8,7,9,11,13],1⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound18 : moves18.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves19 : List FinalMove := [
⟨[7,192,1040,1162,3,128,144,3,2,6,3,2,2,1,0],[3,2,1,0,4,3,2,1,5,4,3,2,13,12,11,10,9,8,7,6,5,4,3,12,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,8,7,6,13,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,13,12,11,12,13],2⟩,
⟨[7,192,1042,1034,3,128,144,3,2,6,3,2,2,1,0],[6,5,4,7,6,5,8,7,6,7,12,11,10,9,11,13,12],6⟩,
⟨[7,192,1048,1160,3,128,144,3,2,6,3,2,2,1,0],[3,2,1,0,4,3,2,1,5,4,3,2,12,11,10,9,8,7,6,5,4,3,5,4,13,12,11,10,9,8,7,6,5,12,11,10,9,8,7,6,8,7,9,11,13],0⟩,
⟨[7,192,1552,1034,3,128,144,3,2,6,3,2,2,1,0],[3,2,1,0,4,3,2,1,5,4,3,2,13,12,11,10,9,8,7,6,5,4,3,6,5,4,13,12,11,10,9,8,7,6,5,13,12,11,10,9,8,7,6,8,7,9,11,13],1⟩,
⟨[7,192,1560,1032,3,128,144,3,2,6,3,2,2,1,0],[3,2,1,0,4,3,2,1,5,4,3,2,12,11,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,7,6,13,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,13,12,11,12,13],0⟩,
⟨[7,200,144,529,3,128,144,3,2,6,3,2,2,1,0],[11,10,9,8,7,6,5,4,3,2,1,0,13,12,11,10,9,8,7,6,5,4,3,2,1,11,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,12,11,10,9,8,7,6,5,4,10,9,8,7,6,5,13,12,11,10,9,8,7,6,12,11,10,9,8,7,9,8,13,12,11,10,9,11],6⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound19 : moves19.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves20 : List FinalMove := [
⟨[7,200,148,513,3,128,144,3,2,6,3,2,2,1,0],[2,1,4,12,11,10,9,8,7,6,7,8,9,10,11,12],5⟩,
⟨[7,200,276,513,3,128,144,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,11,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,11,10,9,8,7,6,5,6,13,12,11,10,9,8,7,12,11,10,9,8,13,12,11,10,9,12,11,10,13,12,11,13,12,13],4⟩,
⟨[7,200,532,513,3,128,144,3,2,6,3,2,2,1,0],[2,1,4,12,11,10,9,8,7,6,7,8,9,10,11,12],6⟩,
⟨[7,200,1026,1034,3,128,144,3,2,6,3,2,2,1,0],[1,4,12,11,10,9,8,7,6,7,8,9,10,11,12],7⟩,
⟨[7,260,140,400,3,128,144,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,7,6,5,4,3,2,1,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,7,6,5,11,10,9,8,7,6,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,12,11,13,12],2⟩,
⟨[7,264,800,577,3,128,144,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,7,6,5,4,3,2,1,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,6,5,11,10,9,8,7,6,12,11,10,9,8,7,12,11,10,9,8,13,12,11,10,9,12,11,10,12,11,13,12],2⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound20 : moves20.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves21 : List FinalMove := [
⟨[7,264,804,513,3,128,144,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,7,6,5,4,3,2,1,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,11,10,9,8,7,6,5,7,6,12,11,10,9,8,7,12,11,10,9,8,13,12,11,10,9,12,11,10,13,12,11,13,12,13],2⟩,
⟨[7,288,292,529,3,128,144,3,2,6,3,2,2,1,0],[5,4,3,2,1,0,4,3,2,1,13,12,11,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,8,7,6,5,8,7,6,13,12,11,10,9,8,7,12,11,10,9,8,13,12,11,10,9,12,11,10,13,12,11,12,13],4⟩,
⟨[7,288,548,529,3,128,144,3,2,6,3,2,2,1,0],[2,7,6,5,4,7,6,5,9,8,7,6,7,12,11,10,9,11,13,12],7⟩,
⟨[7,288,552,1041,3,128,144,3,2,6,3,2,2,1,0],[4,3,2,1,0,4,3,2,1,12,11,10,9,8,7,6,5,4,3,2,13,12,11,10,9,8,7,6,5,4,3,6,5,4,7,6,5,13,12,11,10,9,8,7,6,8,7,10,9,12,11,13],1⟩,
⟨[7,288,1056,1170,3,128,144,3,2,6,3,2,2,1,0],[3,2,1,0,4,3,2,1,5,4,3,2,13,12,11,10,9,8,7,6,5,4,3,12,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,8,7,6,13,12,11,10,9,8,7,12,11,10,9,8,13,12,11,10,9,12,11,10,13,12,11,12,13],2⟩,
⟨[7,288,1058,1042,3,128,144,3,2,6,3,2,2,1,0],[7,6,5,4,7,6,5,9,8,7,6,7,12,11,10,9,11,13,12],6⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound21 : moves21.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves22 : List FinalMove := [
⟨[7,288,1064,1168,3,128,144,3,2,6,3,2,2,1,0],[3,2,1,0,4,3,2,1,5,4,3,2,12,11,10,9,8,7,6,5,4,3,5,4,13,12,11,10,9,8,7,6,5,12,11,10,9,8,7,6,8,7,10,9,12,11,13],0⟩,
⟨[7,288,1568,1042,3,128,144,3,2,6,3,2,2,1,0],[3,2,1,0,4,3,2,1,5,4,3,2,13,12,11,10,9,8,7,6,5,4,3,6,5,4,13,12,11,10,9,8,7,6,5,13,12,11,10,9,8,7,6,8,7,10,9,12,11,13],1⟩,
⟨[7,288,1576,1040,3,128,144,3,2,6,3,2,2,1,0],[3,2,1,0,4,3,2,1,5,4,3,2,12,11,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,7,6,13,12,11,10,9,8,7,12,11,10,9,8,13,12,11,10,9,12,11,10,13,12,11,12,13],0⟩,
⟨[7,296,292,513,3,128,144,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,2,1,0,7,6,5,4,3,2,1,11,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,11,10,9,8,7,6,5,6,13,12,11,10,9,8,7,12,11,10,9,8,13,12,11,10,9,12,11,10,13,12,11,13,12,13],4⟩,
⟨[7,296,548,513,3,128,144,3,2,6,3,2,2,1,0],[2,1,4,12,11,10,9,8,7,6,8,7,8,10,9,10,11,12],6⟩,
⟨[7,296,1026,1042,3,128,144,3,2,6,3,2,2,1,0],[1,4,12,11,10,9,8,7,6,8,7,8,10,9,10,11,12],7⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound22 : moves22.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves23 : List FinalMove := [
⟨[7,392,772,513,3,128,144,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,7,6,5,4,3,2,1,8,7,6,5,4,3,2,9,8,7,6,5,4,3,4,11,10,9,8,7,6,5,11,10,9,8,7,6,7,10,9,12,11,13],0⟩,
⟨[7,1028,524,1120,3,128,144,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,7,6,5,4,3,2,1,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,7,6,5,11,10,9,8,7,6,13,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,12,11,13,12],0⟩,
⟨[7,1032,1026,1122,3,128,144,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,7,6,5,4,3,2,1,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,11,10,9,8,7,6,5,8,7,6,13,12,11,10,9,8,7,12,11,10,9,8,13,12,11,10,9,12,11,10,13,12,11,13,12,13],0⟩,
⟨[7,1032,1538,1120,3,128,144,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,7,6,5,4,3,2,1,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,7,6,5,11,10,9,8,7,6,13,12,11,10,9,8,7,12,11,10,9,8,13,12,11,10,9,12,11,10,12,11,13,12],0⟩,
⟨[7,1064,1026,1058,3,128,144,3,2,6,3,2,2,1,0],[7,6,5,4,3,2,1,0,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,4,10,9,8,7,6,5,13,12,11,10,9,8,7,6,8,7,10,9,13,12,11,13],1⟩,
⟨[7,1096,1026,1090,3,128,144,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,7,6,5,4,3,2,1,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,4,10,9,8,7,6,5,13,12,11,10,9,8,7,6,8,7,10,9,13,12,11,13],1⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound23 : moves23.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves24 : List FinalMove := [
⟨[7,2080,1120,1154,3,128,144,3,2,6,3,2,2,1,0],[3,2,1,0,5,4,3,2,1,5,4,3,2,5,4,3,13,12,11,10,9,8,7,6,5,11,10,9,8,7,6,13,12,11,10,9,8,7,11,13],2⟩,
⟨[7,2112,1168,1154,3,128,144,3,2,6,3,2,2,1,0],[3,2,1,0,5,4,3,2,1,5,4,3,2,5,4,3,13,12,11,10,9,8,7,6,5,11,10,9,8,7,6,13,12,11,10,9,8,7,10,12,11,13],2⟩,
⟨[7,3088,2064,1072,3,128,144,3,2,6,3,2,2,1,0],[3,2,1,0,4,3,2,1,5,4,3,2,12,11,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,5,13,12,11,10,9,8,7,6,13,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,12,11,13,12],0⟩,
⟨[7,3088,2080,1096,3,128,144,3,2,6,3,2,2,1,0],[3,2,1,0,4,3,2,1,5,4,3,2,12,11,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,5,13,12,11,10,9,8,7,6,13,12,11,10,9,8,7,12,11,10,9,8,13,12,11,10,9,12,11,10,12,11,13,12],0⟩,
⟨[7,24,18,49,3,128,146,3,2,6,3,2,2,1,0],[13,12,11,10,9,8,7,6,5,4,3,2,1,0,12,11,10,9,8,7,6,5,4,3,2,1,13,12,11,10,9,8,7,6,5,4,3,2,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,13,12,11,10,9,8,7,6,11,10,9,8,7,8,11,10,9,11,13],4⟩,
⟨[7,24,34,73,3,128,146,3,2,6,3,2,2,1,0],[0,4,3,2,5,4,3,5,4,12,11,10,9,8,7,13,12,11,10,9,8,12,11,10,9,13,12,11,10,13,12,11,13,12,13],4⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound24 : moves24.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves25 : List FinalMove := [
⟨[7,36,28,48,3,128,146,3,2,6,3,2,2,1,0],[13,12,11,10,9,8,7,6,5,4,3,2,1,0,12,11,10,9,8,7,6,5,4,3,2,1,13,12,11,10,9,8,7,6,5,4,3,2,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,13,12,11,10,9,8,7,6,11,10,9,8,7,11,10,9,8,10,9,10,12,11,13],4⟩,
⟨[7,40,96,521,3,128,146,3,2,6,3,2,2,1,0],[1,0,8,7,6,5,4,3,2,8,7,6,5,4,3,8,7,6,5,4,9,8,7,11,10,9,8,11,10,9,13,12,11,10,13,12,11,13,12,13],6⟩,
⟨[7,40,100,513,3,128,146,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,1,8,7,6,5,4,3,2,8,7,6,5,4,3,4,7,6,9,8,7,11,10,9,8,11,10,9,13,12,11,10,13,12,11,13,12],6⟩,
⟨[7,72,144,529,3,128,146,3,2,6,3,2,2,1,0],[0,4,3,2,1,7,6,5,4,3,4,5,12,11,10,9,8,7,6,8,10,9,10,11,12],4⟩,
⟨[7,72,148,513,3,128,146,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,3,2,8,7,6,5,4,3,9,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,7,10,9,12,11,13],7⟩,
⟨[7,24,18,49,3,64,140,3,2,6,3,2,2,1,0],[12,11,10,9,8,7,6,5,4,3,2,1,0,13,12,11,10,9,8,7,6,5,4,3,2,1,12,11,10,9,8,7,6,5,4,3,2,12,11,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,11,10,9,8,7,6,13,12,11,10,9,8,7,13,12,11,10,9,8,11,10,9,11,10,12,11,13],2⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound25 : moves25.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves26 : List FinalMove := [
⟨[7,24,34,73,3,64,140,3,2,6,3,2,2,1,0],[12,11,10,9,8,7,6,5,4,3,2,1,0,13,12,11,10,9,8,7,6,5,4,3,2,1,12,11,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,11,10,9,8,7,6,13,12,11,10,9,8,7,13,12,11,10,9,8,11,10,9,11,10,12,11,13],2⟩,
⟨[7,24,1026,1153,3,64,140,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,7,6,5,4,3,2,1,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,13,12,11,10,9,8,7,13,12,11,10,9,8,11,10,9,11,10,12,11,13],0⟩,
⟨[7,36,28,48,3,64,140,3,2,6,3,2,2,1,0],[12,11,10,9,8,7,6,5,4,3,2,1,0,13,12,11,10,9,8,7,6,5,4,3,2,1,12,11,10,9,8,7,6,5,4,3,2,12,11,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,11,10,9,8,7,6,13,12,11,10,9,8,7,10,9,8,13,12,11,10,9,11,13],2⟩,
⟨[7,40,96,265,3,64,140,3,2,6,3,2,2,1,0],[12,11,10,9,8,7,6,5,4,3,2,1,0,11,10,9,8,7,6,5,4,3,2,1,13,12,11,10,9,8,7,6,5,4,3,2,8,7,6,5,4,3,7,6,5,4,12,11,10,9,8,7,6,5,12,11,10,9,8,7,6,13,12,11,10,9,8,7,11,10,9,8,11,10,9,10,12,11,13],2⟩,
⟨[7,40,100,257,3,64,140,3,2,6,3,2,2,1,0],[12,11,10,9,8,7,6,5,4,3,2,1,0,11,10,9,8,7,6,5,4,3,2,1,13,12,11,10,9,8,7,6,5,4,3,2,8,7,6,5,4,3,7,6,5,4,12,11,10,9,8,7,6,5,12,11,10,9,8,7,6,13,12,11,10,9,8,7,10,9,8,11,10,9,11,13],2⟩,
⟨[7,68,44,72,3,64,140,3,2,6,3,2,2,1,0],[12,11,10,9,8,7,6,5,4,3,2,1,0,13,12,11,10,9,8,7,6,5,4,3,2,1,12,11,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,11,10,9,8,7,6,13,12,11,10,9,8,7,10,9,8,13,12,11,10,9,11,13],2⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound26 : moves26.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves27 : List FinalMove := [
⟨[7,72,144,273,3,64,140,3,2,6,3,2,2,1,0],[12,11,10,9,8,7,6,5,4,3,2,1,0,11,10,9,8,7,6,5,4,3,2,1,13,12,11,10,9,8,7,6,5,4,3,2,8,7,6,5,4,3,7,6,5,4,11,10,9,8,7,6,5,12,11,10,9,8,7,6,13,12,11,10,9,8,7,11,10,9,8,11,10,9,10,13,12,11,13],2⟩,
⟨[7,72,148,257,3,64,140,3,2,6,3,2,2,1,0],[12,11,10,9,8,7,6,5,4,3,2,1,0,11,10,9,8,7,6,5,4,3,2,1,13,12,11,10,9,8,7,6,5,4,3,2,8,7,6,5,4,3,7,6,5,4,11,10,9,8,7,6,5,12,11,10,9,8,7,6,13,12,11,10,9,8,7,10,9,8,11,10,9,11],2⟩,
⟨[7,192,1040,1160,3,64,140,3,2,6,3,2,2,1,0],[3,2,1,0,4,3,2,1,5,4,3,2,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,12,11,10,9,8,7,13,12,11,10,9,8,11,10,9,11,10,12,11,13],0⟩,
⟨[7,288,1056,1168,3,64,140,3,2,6,3,2,2,1,0],[3,2,1,0,4,3,2,1,5,4,3,2,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,10,9,8,7,6,5,11,10,9,8,7,6,12,11,10,9,8,7,13,12,11,10,9,8,11,10,9,11,10,13,12,11,13],0⟩,
⟨[7,1028,1028,1154,3,64,140,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,7,6,5,4,3,2,1,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,10,9,8,7,6,5,11,10,9,8,7,6,13,12,11,10,9,8,7,13,12,11,10,9,8,11,10,9,11,10,13,12,11,13],0⟩,
⟨[7,2052,1036,1152,3,64,140,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,7,6,5,4,3,2,1,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,13,12,11,10,9,8,7,10,9,8,13,12,11,10,9,11,13],0⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound27 : moves27.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves28 : List FinalMove := [
⟨[7,2056,1538,1152,3,64,140,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,7,6,5,4,3,2,1,8,7,6,5,4,3,2,9,8,7,6,5,4,3,10,9,8,7,6,5,4,10,9,8,7,6,5,11,10,9,8,7,6,13,12,11,10,9,8,7,10,9,8,13,12,11,10,9,11],0⟩,
⟨[7,2080,1120,1152,3,64,140,3,2,6,3,2,2,1,0],[3,2,1,0,4,3,2,1,5,4,3,2,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,12,11,10,9,8,7,10,9,8,13,12,11,10,9,11,13],0⟩,
⟨[7,2112,1168,1152,3,64,140,3,2,6,3,2,2,1,0],[3,2,1,0,4,3,2,1,5,4,3,2,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,10,9,8,7,6,5,11,10,9,8,7,6,12,11,10,9,8,7,10,9,8,13,12,11,10,9,11],0⟩,
⟨[7,24,18,49,3,192,144,3,2,6,3,2,2,1,0],[0,4,3,2,5,4,3,5,4,13,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,12,11,13,12],5⟩,
⟨[7,24,34,73,3,192,144,3,2,6,3,2,2,1,0],[0,4,3,2,5,4,3,5,4,13,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,13,12,11,13,12,13],5⟩,
⟨[7,36,28,48,3,192,144,3,2,6,3,2,2,1,0],[3,2,1,0,1,4,3,2,5,4,3,4,6,13,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,12,11,13,12],5⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound28 : moves28.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves29 : List FinalMove := [
⟨[7,40,96,521,3,192,144,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,6,5,11,10,9,8,7,6,13,12,11,10,9,8,7,12,11,10,9,8,13,12,11,10,9,12,11,10,12,11,13,12],6⟩,
⟨[7,40,100,513,3,192,144,3,2,6,3,2,2,1,0],[3,2,1,0,5,4,3,2,1,4,3,2,5,4,3,12,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,12,11,10,9,8,7,6,11,13],4⟩,
⟨[7,48,96,1033,3,192,144,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,11,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,6,5,11,10,9,8,7,6,12,11,10,9,8,7,11,10,9,8,13,12,11,10,9,12,11,10,12,11,13,12],6⟩,
⟨[7,48,104,1025,3,192,144,3,2,6,3,2,2,1,0],[3,2,1,0,4,3,2,1,4,3,2,5,4,3,13,12,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,13,12,11,10,9,8,7,6,11,13],4⟩,
⟨[7,68,44,72,3,192,144,3,2,6,3,2,2,1,0],[3,2,1,0,1,4,3,2,5,4,3,4,7,6,13,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,13,12,11,13,12],5⟩,
⟨[7,72,144,529,3,192,144,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,2,1,0,7,6,5,4,3,2,1,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,6,5,11,10,9,8,7,6,13,12,11,10,9,8,7,12,11,10,9,8,13,12,11,10,9,12,11,10,12,11,13,12],6⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound29 : moves29.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves30 : List FinalMove := [
⟨[7,72,148,513,3,192,144,3,2,6,3,2,2,1,0],[3,2,1,0,5,4,3,2,1,4,3,2,5,4,3,12,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,12,11,10,9,8,7,6,10,12,11,13],4⟩,
⟨[7,80,144,1041,3,192,144,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,2,1,0,7,6,5,4,3,2,1,11,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,6,5,11,10,9,8,7,6,12,11,10,9,8,7,11,10,9,8,13,12,11,10,9,12,11,10,12,11,13,12],6⟩,
⟨[7,80,152,1025,3,192,144,3,2,6,3,2,2,1,0],[3,2,1,0,4,3,2,1,4,3,2,5,4,3,13,12,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,13,12,11,10,9,8,7,6,10,12,11,13],4⟩,
⟨[7,24,18,49,3,192,130,3,2,6,3,2,2,1,0],[0,4,3,2,5,4,3,5,4,13,12,11,10,9,8,7,13,12,11,10,9,8,13,12,11,10,9,13,12,11,10,12,11,13,12],7⟩,
⟨[7,24,34,73,3,192,130,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,4,3,2,8,7,6,5,4,3,9,8,7,6,5,4,10,9,8,7,6,5,11,10,9,8,7,6,8,7,9],6⟩,
⟨[7,36,28,48,3,192,130,3,2,6,3,2,2,1,0],[2,1,0,8,7,6,5,4,3,2,8,7,6,5,4,3,8,7,6,5,4,9,8,7,10,9,8,11,10,9,12,11,10,11,13,12],7⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound30 : moves30.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves31 : List FinalMove := [
⟨[7,48,96,1033,3,192,130,3,2,6,3,2,2,1,0],[3,2,1,0,4,3,2,1,4,3,2,5,4,3,13,12,11,10,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,13,12,11,10,9,8,7,6,7,9,11,13],6⟩,
⟨[7,24,18,49,3,68,136,3,2,6,3,2,2,1,0],[12,11,10,9,8,7,6,5,4,3,2,1,0,13,12,11,10,9,8,7,6,5,4,3,2,1,12,11,10,9,8,7,6,5,4,3,2,12,11,10,9,8,7,6,5,4,3,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,12,11,10,9,8,7,6,11,10,9,8,7,8,11,10,9,11,13],1⟩,
⟨[7,24,1026,1153,3,68,136,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,7,6,5,4,3,2,1,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,8,7,6,5,4,10,9,8,7,6,5,13,12,11,10,9,8,7,6,11,10,9,8,7,8,11,10,9,11],1⟩,
⟨[7,36,28,48,3,68,136,3,2,6,3,2,2,1,0],[12,11,10,9,8,7,6,5,4,3,2,1,0,13,12,11,10,9,8,7,6,5,4,3,2,1,12,11,10,9,8,7,6,5,4,3,2,12,11,10,9,8,7,6,5,4,3,9,8,7,6,5,4,13,12,11,10,9,8,7,6,5,12,11,10,9,8,7,6,11,10,9,8,7,11,10,9,8,10,9,10,12,11,13],1⟩,
⟨[7,192,1040,1160,3,68,136,3,2,6,3,2,2,1,0],[3,2,1,0,4,3,2,1,5,4,3,2,9,8,7,6,5,4,3,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,11,10,9,8,7,8,11,10,9,11,13],1⟩,
⟨[7,2052,1036,1152,3,68,136,3,2,6,3,2,2,1,0],[6,5,4,3,2,1,0,7,6,5,4,3,2,1,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,8,7,6,5,4,10,9,8,7,6,5,13,12,11,10,9,8,7,6,11,10,9,8,7,11,10,9,8,10,9,10,13,12,11,13],1⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound31 : moves31.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves32 : List FinalMove := [
⟨[7,2080,1120,1152,3,68,136,3,2,6,3,2,2,1,0],[3,2,1,0,4,3,2,1,5,4,3,2,9,8,7,6,5,4,3,8,7,6,5,4,11,10,9,8,7,6,5,11,10,9,8,7,6,11,10,9,8,7,11,10,9,8,10,9,10,12,11,13],1⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem sound32 : moves32.all isFinal = true := by decide +kernel
end SparseFifteen
end

section
namespace SparseFifteen
def moves := moves0 ++ moves1 ++ moves2 ++ moves3 ++ moves4 ++ moves5 ++ moves6 ++ moves7 ++ moves8 ++ moves9 ++ moves10 ++ moves11 ++ moves12 ++ moves13 ++ moves14 ++ moves15 ++ moves16 ++ moves17 ++ moves18 ++ moves19 ++ moves20 ++ moves21 ++ moves22 ++ moves23 ++ moves24 ++ moves25 ++ moves26 ++ moves27 ++ moves28 ++ moves29 ++ moves30 ++ moves31 ++ moves32
private theorem combine {a b : List FinalMove} (ha : a.all isFinal=true) (hb : b.all isFinal=true) :
    (a++b).all isFinal=true := by rw [List.all_append,ha,hb]; rfl

set_option maxHeartbeats 4000000 in
theorem moves_sound : moves.all isFinal=true := (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine sound0 sound1) sound2) sound3) sound4) sound5) sound6) sound7) sound8) sound9) sound10) sound11) sound12) sound13) sound14) sound15) sound16) sound17) sound18) sound19) sound20) sound21) sound22) sound23) sound24) sound25) sound26) sound27) sound28) sound29) sound30) sound31) sound32)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 6000000 in
theorem source_list : (pairs++triples).flatMap (fun r => r.outputs.map (fun cs => FP32.attach cs r.base)) =
    moves.map FinalMove.source := by decide +kernel

theorem moves_total : (pairs++triples).all (fun r => r.outputs.all
    (fun cs => decide (FP32.attach cs r.base ∈ moves.map FinalMove.source)))=true := by
  apply List.all_eq_true.mpr
  intro r hr
  apply List.all_eq_true.mpr
  intro cs hc
  apply decide_eq_true
  rw [←source_list]
  exact List.mem_flatMap.mpr ⟨r,hr,List.mem_map.mpr ⟨cs,hc,rfl⟩⟩

end SparseFifteen
end

section
/- Turn the rooted contact tables into a labeled-graph classification.
The graph relabeling uses adjacent swaps from the accepted OMA Ramsey
enumeration. All terminal contacts and all permutations are checked. -/

namespace SparseFifteen
open SimpleGraph Finset

theorem presentation_of_rowcase {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (vs : List V) (nd : vs.Nodup) (allv : vs.toFinset=univ)
    (r : RowCase) (cs : List ℕ) (which : r∈pairs++triples) (allowed : cs∈r.outputs)
    (code : OMA.RamseyFinite.encode G vs=OMA.RamseyFinite.attach cs r.base) :
    ∃ (i : Fin 8) (ws : List V), ws.Nodup ∧ ws.toFinset=univ ∧ GlueSeed.encode G ws=adj i := by
  have selected := List.all_eq_true.mp (List.all_eq_true.mp moves_total r which) cs allowed
  obtain ⟨m,hm,present⟩ := List.mem_map.mp (of_decide_eq_true selected)
  have yes := List.all_eq_true.mp moves_sound m hm
  obtain ⟨ws,perm,relabel⟩ := OMA.RamseyFinite.relabel_real G m.steps vs
  refine ⟨m.index,ws,perm.nodup_iff.mpr nd,?_,?_⟩
  · rw [←allv]
    ext v
    exact List.mem_toFinset.trans (perm.mem_iff.trans List.mem_toFinset.symm)
  · rw [←Sparse32.encode_glue,relabel,code,Sparse32.toPure_relabel,Sparse32.toPure_attach,←present]
    exact beq_iff_eq.mp yes

end SparseFifteen
end

section
namespace SparseFifteen
open FP32

structure Contact where
  mask : Nat
  cost : Nat
  q : Nat
  t : Nat
deriving DecidableEq

def contacts (b : List Nat) (d cap : Nat) (quads threes : List Nat) : List Contact :=
  (((usable 6 d b).filter fun x => decide (countBits b.length x ≤ cap)).map
    fun x => ⟨x,countBits b.length x,missWord quads x,missWord threes x⟩)

def setsOfSize (b : List Nat) (k : Nat) :=
  ((inds b).filter fun p => p.2 == k).map Prod.fst

def pairTest (rs : List Contact) (budget : Nat) (outs : List (List Nat)) :=
  rs.all fun a => rs.all fun c =>
    if a.cost+c.cost ≤ budget && a.mask ≤ c.mask && (a.q &&& c.q == 0) then
      decide ([a.mask,c.mask] ∈ outs)
    else true

end SparseFifteen
namespace SparseFifteen
def laterOK (budget : Nat) (a e : Contact) : Bool :=
  a.cost+e.cost+2 ≤ budget && a.mask ≤ e.mask && (a.q &&& e.q == 0)

def threeFast (rs : List Contact) (budget : Nat) (outs : List (List Nat)) :=
  rs.all fun a =>
    let ys := rs.filter (laterOK budget a)
    ys.all fun c => ys.all fun e =>
      if a.cost+c.cost+e.cost ≤ budget && c.mask ≤ e.mask &&
          (c.q &&& e.q == 0) && (a.t &&& c.t &&& e.t == 0) then
        decide ([a.mask,c.mask,e.mask] ∈ outs)
      else true
end SparseFifteen
namespace SparseFifteen
open FP32

def pairBatch (r : RowCase) :=
  let b:=r.base
  let budget:=26-edges_ b-2
  let Q:=setsOfSize b 4
  let rs:=contacts b 2 (budget-1) Q []
  (usable 6 2 b).all (fun x=> decide (1≤ countBits b.length x)) && pairTest rs budget r.outputs

def tripleBatch (r : RowCase) :=
  let b:=r.base
  let budget:=26-edges_ b-3
  let Q:=setsOfSize b 4
  let T:=setsOfSize b 3
  let rs:=contacts b 3 (budget-4) Q T
  (usable 6 3 b).all (fun x=> decide (2≤ countBits b.length x)) && threeFast rs budget r.outputs
end SparseFifteen

namespace SparseFifteen
open FP32

theorem setValid {b : List Nat} {k s : Nat} (h : s ∈ setsOfSize b k) : (s,k) ∈ inds b := by
  obtain ⟨⟨m,t⟩,hf,rfl⟩ := List.mem_map.mp h
  obtain ⟨hm,ht⟩ := List.mem_filter.mp hf
  have he : t = k := beq_iff_eq.mp ht
  simpa [he] using hm

theorem bits_and {α : Type*} (l : List α) (f g : α → Bool) :
    bits (l.map f) &&& bits (l.map g) = bits (l.map (fun x => f x && g x)) := by
  induction l with
  | nil => simp [bits]
  | cons x xs ih => simp only [List.map_cons,bits,←bit_form,Nat.land_bit,ih]

theorem triple_limit {b T : List Nat} {x y z : Nat}
    (valid : ∀ s∈T,(s,3)∈inds b) (ok : okContacts 6 (inds b) [x,y,z]=true) :
    missWord T x &&& missWord T y &&& missWord T z = 0 := by
  unfold missWord tableBits
  rw [bits_and,and_mask]
  intro s hs hit
  obtain ⟨hx,hy⟩ := Bool.and_eq_true_iff.mp hit
  apply Bool.eq_false_iff.mpr
  intro hz
  have h := of_decide_eq_true (List.all_eq_true.mp ok (s,3) (valid s hs))
  simp [hx,hy,hz] at h

theorem batch (b : List Nat) (d cap : Nat) (Q T : List Nat)
    {x : Nat} (hx : x ∈ usable 6 d b) (hc : countBits b.length x ≤ cap) :
    (⟨x,countBits b.length x,missWord Q x,missWord T x⟩ : Contact) ∈ contacts b d cap Q T := by
  exact List.mem_map.mpr ⟨x,List.mem_filter.mpr ⟨hx,decide_eq_true hc⟩,rfl⟩

theorem recoverPair (b Q : List Nat) (rs : List Contact) (budget cap : Nat) (outs : List (List Nat))
    (quads : Q = setsOfSize b 4)
    (rows : contacts b 2 cap Q [] = rs)
    (low : (usable 6 2 b).all (fun x => decide (1 ≤ countBits b.length x)) = true)
    (hb : 26-edges_ b-2 = budget) (hc : budget-1 = cap)
    (test : pairTest rs budget outs = true)
    {cs : List Nat} (ex : Extension 6 2 b cs) (ord : cs.Pairwise (·≤·))
    (small : edges_ (attach cs b) ≤ 26) : cs ∈ outs := by
  obtain ⟨x,y,rfl⟩ : ∃ x y, cs=[x,y] := ⟨_,_,List.eq_getElem_of_length_eq_two cs ex.1⟩
  have ix := ex.2.1 x (by simp)
  have iy := ex.2.1 y (by simp)
  have lx := of_decide_eq_true (List.all_eq_true.mp low x ix)
  have ly := of_decide_eq_true (List.all_eq_true.mp low y iy)
  rw [edges_attached] at small
  simp only [List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at small
  have hxy : countBits b.length x + countBits b.length y ≤ budget := by omega
  have ax := batch b 2 cap Q [] ix (by omega)
  have ay := batch b 2 cap Q [] iy (by omega)
  rw [rows] at ax ay
  have h := List.all_eq_true.mp (List.all_eq_true.mp test _ ax) _ ay
  have hp := pair_lim (inds b) Q [x,y] (fun s hs=> setValid (quads ▸ hs)) ex.2.2
  simp [List.pairwise_cons] at hp ord
  exact of_decide_eq_true (by simpa [hxy,hp,ord] using h)

end SparseFifteen
namespace SparseFifteen
open FP32
theorem recoverTripleFast (b Q T : List Nat) (rs : List Contact) (budget cap : Nat) (outs : List (List Nat))
    (quads : Q = setsOfSize b 4) (threes : T = setsOfSize b 3)
    (rows : contacts b 3 cap Q T = rs)
    (low : (usable 6 3 b).all (fun x => decide (2 ≤ countBits b.length x)) = true)
    (hb : 26-edges_ b-3 = budget) (hc : budget-4 = cap)
    (test : threeFast rs budget outs = true)
    {cs : List Nat} (ex : Extension 6 3 b cs) (ord : cs.Pairwise (·≤·))
    (small : edges_ (attach cs b) ≤ 26) : cs ∈ outs := by
  obtain ⟨x,y,z,rfl⟩ : ∃ x y z, cs=[x,y,z] := ⟨_,_,_,List.eq_getElem_of_length_eq_three cs ex.1⟩
  have ix := ex.2.1 x (by simp)
  have iy := ex.2.1 y (by simp)
  have iz := ex.2.1 z (by simp)
  have lx := of_decide_eq_true (List.all_eq_true.mp low x ix)
  have ly := of_decide_eq_true (List.all_eq_true.mp low y iy)
  have lz := of_decide_eq_true (List.all_eq_true.mp low z iz)
  rw [edges_attached] at small
  simp only [List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at small
  have hxyz : countBits b.length x + countBits b.length y + countBits b.length z ≤ budget := by omega
  have hxy : countBits b.length x + countBits b.length y + 2 ≤ budget := by omega
  have ax := batch b 3 cap Q T ix (by omega)
  have ay := batch b 3 cap Q T iy (by omega)
  have az := batch b 3 cap Q T iz (by omega)
  rw [rows] at ax ay az
  have hp := pair_lim (inds b) Q [x,y,z] (fun s hs=> setValid (quads ▸ hs)) ex.2.2
  have ht := triple_limit (fun s hs=> setValid (threes ▸ hs)) ex.2.2
  simp [List.pairwise_cons] at hp ord
  have hxz : countBits b.length x + countBits b.length z + 2 ≤ budget := by omega
  have memy : _ := (List.mem_filter (p := laterOK budget ⟨x,countBits b.length x,missWord Q x,missWord T x⟩)).mpr ⟨ay,by simp [laterOK,hxy,ord,hp]⟩
  have memz : _ := (List.mem_filter (p := laterOK budget ⟨x,countBits b.length x,missWord Q x,missWord T x⟩)).mpr ⟨az,by simp [laterOK,hxz,ord,hp]⟩
  have he := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp test _ ax) _ memy) _ memz
  exact of_decide_eq_true (by simpa [hxyz,ord,hp,ht] using he)
end SparseFifteen
namespace SparseFifteen
namespace CheckFifteenTriple0
open FP32
def Q : List Nat := [612,788,564,780,588,1122,1170,402,1074,1162,394,1098,102,278,54,270,78,1121,609,785,1169,401,1073,561,777,1161,393,1097,585]
def T : List Nat := [1120,608,784,1168,400,1072,560,776,1160,392,1096,584,772,580,548,100,532,276,52,524,268,76,1154,386,1090,1058,98,1042,274,146,50,1034,266,138,74,262,70,38,22,14,769,1153,385,1089,577,1057,545,97,1041,529,273,145,49,1033,521,265,137,73]
def R : List Contact := [⟨768,2,173235040,232404833341310249⟩,⟨1152,2,294514719,204581719062345926⟩,⟨384,2,415717685,176758540729183331⟩,⟨1088,2,94954638,134621916376814292⟩,⟨576,2,108062656,125299159603741496⟩,⟨1056,2,355050650,274180675655645844⟩,⟨544,2,238137024,264884307144869656⟩,⟨96,2,121153226,139338685032895388⟩,⟨1120,3,86549642,130047809492292244⟩,⟨608,3,103851712,120760237057770264⟩,⟨1040,2,352687129,270450994036931202⟩,⟨528,2,235118112,261400916030162689⟩,⟨272,2,436673073,243470041740799235⟩,⟨784,3,167975456,225367682300544257⟩,⟨144,2,419928121,207440175271836803⟩,⟨1168,3,285577241,198388993354168450⟩,⟨400,3,403118129,171410240085486595⟩,⟨48,2,520195608,279257946837761920⟩,⟨1072,3,352420888,270239750298286720⟩,⟨560,3,234982912,261224856630068992⟩,⟨1032,2,11300999,8678962629177430⟩,⟨520,2,7500256,8354606887632953⟩,⟨264,2,14045541,7875185181319275⟩,⟨776,3,5394784,7224274297585705⟩,⟨136,2,13529383,6748219850092647⟩,⟨1160,3,9203719,6422764223721542⟩,⟨392,3,12996901,5621185803313251⟩,⟨72,2,16277958,8839422712172668⟩,⟨1096,3,11034758,8520564168151124⟩,⟨584,3,7365056,8205004502859832⟩,⟨516,2,242356192,269562902090876729⟩,⟨260,2,450235232,251069111939894635⟩,⟨772,3,173149024,232403802546767145⟩,⟨68,2,133695424,143946979888595964⟩,⟨580,3,108005312,125298163169887032⟩,⟨36,2,523767488,283479419589234588⟩,⟨548,3,238030528,264883379428656920⟩,⟨100,3,121112256,139337826037662620⟩,⟨612,4,103810752,120759378063131416⟩,⟨20,2,520490528,279503584704335747⟩,⟨532,3,235015712,261400125753001729⟩,⟨276,3,436603424,243469285823876355⟩,⟨788,4,167905824,225366926384170241⟩,⟨52,3,520097280,279257293999050624⟩,⟨564,4,234884608,261224203791894272⟩,⟨12,2,16646624,9006101886402687⟩,⟨524,3,7471584,8354091491131449⟩,⟨268,3,14025056,7874704144597099⟩,⟨780,4,5374304,7223793260953641⟩,⟨76,3,16253376,8838976035094652⟩,⟨588,4,7340480,8204557825867832⟩,⟨1026,2,363593759,278894422924458710⟩,⟨258,2,450232341,251069082159148395⟩,⟨130,2,432930847,213913285722897639⟩,⟨1154,3,294387743,204580631026333894⟩,⟨386,3,415629333,176757489284279395⟩,⟨66,2,133693454,143946962798859260⟩,⟨1090,3,94896142,134620905172062932⟩,⟨34,2,523763738,283479386411974556⟩,⟨1058,3,354943002,274179717064243860⟩,⟨98,3,121110538,139337810054943644⟩,⟨1122,4,86507530,130046936800236180⟩,⟨18,2,520486937,279503552365789059⟩,⟨1042,3,352583705,270450173622680194⟩,⟨274,3,436600849,243469257787632899⟩,⟨146,3,419823641,207439361258093699⟩,⟨1170,4,285474841,198388181538240642⟩,⟨402,4,403046417,171409464726449155⟩,⟨50,3,520093720,279257261761118080⟩,⟨1074,4,352321560,270239067390098048⟩,⟨10,2,16646151,9006099743633535⟩,⟨1034,3,11272199,8678445278556246⟩,⟨266,3,14024709,7874702278516843⟩,⟨138,3,13500423,6747702860181607⟩,⟨1162,4,9175047,6422247418359878⟩,⟨394,4,12976133,5620703441576035⟩,⟨74,3,16252934,8838973976170620⟩,⟨1098,4,11010054,8520115604115540⟩,⟨6,2,536739840,288229276640088063⟩,⟨262,3,450232320,251069082156141931⟩,⟨70,3,133693440,143946962796807164⟩,⟨38,3,523763712,283479386408095644⟩,⟨102,4,121110528,139337810053170076⟩,⟨22,3,520486912,279503552362057603⟩,⟨278,4,436600832,243469257784954115⟩,⟨54,4,520093696,279257261757435776⟩,⟨14,3,16646144,9006099743113343⟩,⟨270,4,14024704,7874702278131819⟩,⟨78,4,16252928,8838973975691388⟩,⟨1025,2,128159,1097175399126⟩,⟨513,2,131040,1099511007033⟩,⟨257,2,88949,1060578913643⟩,⟨769,3,88928,1060578297129⟩,⟨129,2,129343,1090372238567⟩,⟨1153,3,127007,1088040204486⟩,⟨385,3,88373,1051447913571⟩,⟨65,2,59342,1013526254588⟩,⟨1089,3,58510,1011206804180⟩,⟨577,3,59328,1013525644088⟩,⟨33,2,110298,960897957788⟩,⟨1057,3,107674,958595283604⟩,⟨545,3,110272,960897353496⟩,⟨97,3,42698,874979726236⟩,⟨1121,4,42122,872693830292⟩,⟨609,4,42688,874979132184⟩,⟨17,2,106041,822619996035⟩,⟨1041,3,103449,820417985154⟩,⟨529,3,106016,822619440897⟩,⟨273,3,72241,783955848451⟩,⟨785,4,72224,783955297537⟩,⟨145,3,104505,814017477763⟩,⟨1169,4,102425,811819661442⟩,⟨401,4,71729,775361719299⟩,⟨49,3,101912,685080330112⟩,⟨1073,4,99352,682911873664⟩,⟨561,4,101888,685079791360⟩,⟨9,2,29159,517539885183⟩,⟨1033,3,28807,517351141462⟩,⟨521,3,29152,517539790905⟩,⟨265,3,20837,482903187563⟩,⟨777,4,20832,482903097385⟩,⟨137,3,28967,516990431335⟩,⟨1161,4,28679,516805881926⟩,⟨393,4,20773,482362122339⟩,⟨73,3,25030,448736481404⟩,⟨1097,4,24710,448564514900⟩,⟨585,4,25024,448736395320⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 60000000 in
theorem quadOK : Q = setsOfSize triple0.base 4 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 60000000 in
theorem threeOK : T = setsOfSize triple0.base 3 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 60000000 in
theorem rowsOK : contacts triple0.base 3 4 Q T = R := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 60000000 in
theorem lowOK : (usable 6 3 triple0.base).all (fun x => decide (2 ≤ countBits triple0.base.length x)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 60000000 in
theorem edgeOK : 26-edges_ triple0.base-3 = 8 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 60000000 in
theorem testOK : threeFast R 8 triple0.outputs = true := by decide +kernel
end CheckFifteenTriple0
end SparseFifteen
namespace SparseFifteen
set_option maxRecDepth 100000 in
set_option maxHeartbeats 60000000 in
theorem resultT0 : tripleBatch triple0=true := by
  dsimp only [tripleBatch]
  rw [←CheckFifteenTriple0.quadOK,←CheckFifteenTriple0.threeOK,CheckFifteenTriple0.edgeOK,CheckFifteenTriple0.lowOK]
  change (true && threeFast (contacts triple0.base 3 4 CheckFifteenTriple0.Q CheckFifteenTriple0.T) 8 triple0.outputs)=true
  simp only [CheckFifteenTriple0.rowsOK,CheckFifteenTriple0.testOK,Bool.true_and]
end SparseFifteen
namespace SparseFifteen
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultP0 : pairBatch pair0 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultP1 : pairBatch pair1 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultP2 : pairBatch pair2 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultP3 : pairBatch pair3 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultP4 : pairBatch pair4 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultP5 : pairBatch pair5 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultP6 : pairBatch pair6 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultP7 : pairBatch pair7 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT1 : tripleBatch triple1 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT2 : tripleBatch triple2 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT3 : tripleBatch triple3 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT4 : tripleBatch triple4 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT5 : tripleBatch triple5 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT6 : tripleBatch triple6 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT7 : tripleBatch triple7 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT8 : tripleBatch triple8 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT9 : tripleBatch triple9 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT10 : tripleBatch triple10 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT11 : tripleBatch triple11 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT12 : tripleBatch triple12 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT13 : tripleBatch triple13 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT14 : tripleBatch triple14 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT15 : tripleBatch triple15 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT16 : tripleBatch triple16 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT17 : tripleBatch triple17 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT18 : tripleBatch triple18 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT19 : tripleBatch triple19 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT20 : tripleBatch triple20 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT21 : tripleBatch triple21 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT22 : tripleBatch triple22 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT23 : tripleBatch triple23 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT24 : tripleBatch triple24 = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem resultT25 : tripleBatch triple25 = true := by decide +kernel
end SparseFifteen
namespace SparseFifteen
open FP32
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem allP : pairs.all pairBatch=true := by
  simp only [pairs,List.all_cons,List.all_nil,Bool.and_self,resultP0,resultP1,resultP2,resultP3,resultP4,resultP5,resultP6,resultP7]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem recover_pairs {r : RowCase} (hr : r∈pairs) {cs : List Nat}
    (ext : Extension 6 2 r.base cs) (sort : cs.Pairwise (·≤·))
    (small : edges_ (attach cs r.base)≤26) : cs∈r.outputs := by
  obtain ⟨low,test⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp allP r hr)
  exact recoverPair r.base (setsOfSize r.base 4) _ _ _ r.outputs rfl rfl low rfl rfl test ext sort small
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem allT : triples.all tripleBatch=true := by
  simp only [triples,List.all_cons,List.all_nil,Bool.and_self,resultT0,resultT1,resultT2,resultT3,resultT4,resultT5,resultT6,resultT7,resultT8,resultT9,resultT10,resultT11,resultT12,resultT13,resultT14,resultT15,resultT16,resultT17,resultT18,resultT19,resultT20,resultT21,resultT22,resultT23,resultT24,resultT25]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 80000000 in
theorem recover_triples {r : RowCase} (hr : r∈triples) {cs : List Nat}
    (ext : Extension 6 3 r.base cs) (sort : cs.Pairwise (·≤·))
    (small : edges_ (attach cs r.base)≤26) : cs∈r.outputs := by
  obtain ⟨low,test⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp allT r hr)
  exact recoverTripleFast r.base (setsOfSize r.base 4) (setsOfSize r.base 3) _ _ _ r.outputs rfl rfl rfl low rfl rfl test ext sort small
end SparseFifteen
end

section
namespace SparseFifteen
open SimpleGraph Finset

/-- For order fifteen, the sparse triangle-free graphs with independence
number at most five have exactly eight possible forward adjacency codes. -/
theorem classification_of_ground {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V)
    [DecidableRel K.Adj] (cap : K.edgeFinset.card≤26)
    (grounded : ∃ (vs : List V) (d : Nat) (r : RowCase) (cs : List Nat), vs.Nodup ∧ vs.toFinset=univ ∧
      ((d=2 ∧ r∈pairs) ∨ (d=3 ∧ r∈triples)) ∧ OMA.RamseyFinite.Extension 6 d r.base cs ∧ cs.Pairwise (·≤·) ∧
      OMA.RamseyFinite.encode K vs=OMA.RamseyFinite.attach cs r.base) :
    ∃ (i : Fin 8) (vs : List V), vs.Nodup ∧ vs.toFinset=univ ∧ GlueSeed.encode K vs=adj i := by
  obtain ⟨vs,d,r,cs,nd,allv,which,ext,sorted,code⟩ := grounded
  have small : OMA.RamseyFinite.edges_ (OMA.RamseyFinite.attach cs r.base) ≤ 26 := by
    rw [←code,Sparse32.edge_card K vs nd allv]
    exact cap
  rw [Sparse32.toPure_edges,Sparse32.toPure_attach] at small
  have extension := Sparse32.toPure_ext ext
  rcases which with ⟨rfl,pair⟩|⟨rfl,triple⟩
  · exact presentation_of_rowcase K vs nd allv r cs (List.mem_append_left _ pair)
      (recover_pairs pair extension sorted small) code
  · exact presentation_of_rowcase K vs nd allv r cs (List.mem_append_right _ triple)
      (recover_triples triple extension sorted small) code

end SparseFifteen
end

section
namespace SparseFifteen
open OMA.RamseyFinite SimpleGraph Finset
theorem root_with_swaps {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (norm : List Nat → List Nat)
    (hnorm : ∀ l : List V, ∃ l' : List V, l'.Perm l ∧ encode G l'=norm (encode G l))
    (swaps : List Nat → List Nat) (k : Nat) (A : Finset V) (non : A.Nonempty) (cap : Nat) (hs : Small G A (k+1))
    (hu : A.Nonempty → ∃ x∈A,(A.filter (G.Adj x)).card ≤ cap) :
    ∃ (vs : List V) (d : Nat) (b cs : List Nat), vs.Nodup ∧ vs.toFinset=A ∧ d≤ cap ∧
      b∈levels norm k (A.card-1-d) (k-1) ∧ Extension (k+1) d (relabel (swaps b) b) cs ∧ cs.Pairwise (·≤·) ∧ encode G vs=attach cs (relabel (swaps b) b) ∧ ∃ r ∈ A, (A.filter (G.Adj r)).card = d := by
    obtain ⟨r,hr,hmin⟩ := A.exists_min_image (fun x => (A.filter (G.Adj x)).card) non
    let N := A.filter (G.Adj r)
    let B := A \ insert r N
    let d := N.card
    have hNr : r∉N := by simp [N]
    have hNA : N⊆A := Finset.filter_subset ..
    have hBA : B⊆A := Finset.sdiff_subset
    have hu' : d≤ cap := by obtain ⟨x,hx,hh⟩ := hu non; exact (hmin x hx).trans hh
    have hdk : d≤ k := Nat.le_of_lt_succ (hs N hNA (neighbors_small G ht A r))
    have hBcard : B.card + d + 1 = A.card := by
      have hh := Finset.card_sdiff_add_card_eq_card (Finset.insert_subset hr hNA)
      rw [Finset.card_insert_of_notMem hNr] at hh
      omega
    have rB : r∉B := by simp [B]
    have hbase (x) (hx : x∈B) : ¬G.Adj r x := by
      have h := Finset.mem_sdiff.mp hx
      exact fun ha => h.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h.1,ha⟩))
    have noK : Small G B k := by
      intro S hS hI
      have rn : r∉S := fun h => rB (hS h)
      have indep : Gᶜ.IsClique (insert r S : Finset V) := by
        rw [Finset.coe_insert,SimpleGraph.isClique_insert_of_notMem rn]
        exact ⟨hI,fun x hx => ⟨fun e => rn (e ▸ hx),hbase x (hS hx)⟩⟩
      have hh := hs (insert r S) (Finset.insert_subset hr (hS.trans hBA)) indep
      rw [Finset.card_insert_of_notMem rn] at hh
      omega
    obtain ⟨before,nd0,mem0,cls⟩ := levels_complete G ht norm hnorm k B (k-1) noK (by
      rintro ⟨x,hx⟩
      have mm := noK (B.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht B x)
      exact ⟨x,hx,by omega⟩)
    obtain ⟨base,perm,encBase⟩ := relabel_real G (swaps (encode G before)) before
    have hbn := perm.nodup_iff.mpr nd0
    have hb : base.toFinset=B := by
      rw [←mem0]
      ext x
      simpa only [List.mem_toFinset] using perm.mem_iff (a:=x)
    obtain ⟨front,hfn,hf,sorted_⟩ := sorted_neigh G N base
    have ha (x) (hx : x∈front) : G.Adj r x := (Finset.mem_filter.mp (hf ▸ List.mem_toFinset.mpr hx)).2
    have hnot (x) (hx : x∈base) := hbase x (hb ▸ List.mem_toFinset.mpr hx)
    have dl : front.length=d := by rw [← List.toFinset_card_of_nodup hfn,hf]
    have nodup : (r::front++base).Nodup := by
      apply List.nodup_cons.mpr
      constructor
      · change r ∉ front++base
        rw [List.mem_append,not_or]
        exact ⟨fun h => hNr (hf ▸ List.mem_toFinset.mpr h), fun h => rB (hb ▸ List.mem_toFinset.mpr h)⟩
      · exact List.nodup_append.mpr ⟨hfn,hbn,fun x hx y hy e => hnot y hy (e ▸ ha x hx)⟩
    have cover : (r::front++base).toFinset=A := by
      ext x
      simp only [List.toFinset_cons,List.toFinset_append,hf,hb,B,Finset.mem_insert,Finset.mem_union,Finset.mem_sdiff]
      have h1 : x=r → x∈A := fun h => h ▸ hr
      have h2 : x∈N → x∈A := fun h => hNA h
      grind
    have hcount (x) (hx : x∈front) : d≤ sizeAt G base x+1 ∧ sizeAt G base x+1 < k+1 := by
      have xN : x∈N := hf ▸ List.mem_toFinset.mpr hx
      have adj := ha x hx
      have eq : A.filter (G.Adj x)=insert r (B.filter (G.Adj x)) := by
        ext y
        simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_sdiff,B]
        constructor
        · rintro ⟨yA,xy⟩
          by_cases yr : y=r
          · exact Or.inl yr
          · exact Or.inr ⟨⟨yA,not_or.mpr ⟨yr,fun yN => G.isIndepSet_neighborSet_of_triangleFree ht r adj (Finset.mem_filter.mp yN).2 xy.ne xy⟩⟩,xy⟩
        · rintro (rfl|⟨⟨yA,_⟩,xy⟩)
          · exact ⟨hr,adj.symm⟩
          · exact ⟨yA,xy⟩
      have mm := hmin x (hNA xN)
      have mx := hs (A.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G ht A x)
      have rn : r∉B.filter (G.Adj x) := fun h => rB (Finset.mem_filter.mp h).1
      rw [eq,Finset.card_insert_of_notMem rn] at mm mx
      rw [sizeAt_finset G hbn,hb]
      exact ⟨mm,mx⟩
    obtain ⟨cs,hcs,sort,enc⟩ := sorted_graphExtension G A (k+1) d ht hs r front base nodup cover dl ha hnot hcount hmin sorted_
    rw [encBase] at hcs enc
    exact ⟨r::front++base, d, encode G before, cs, nodup, cover, hu', by simpa only [show A.card-1-d=B.card by omega] using cls, hcs, sort, enc, ⟨r, hr, rfl⟩⟩

theorem min_one {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (sz : Fintype.card V = 15) (tri : G.CliqueFree 3) (ind : Gᶜ.CliqueFree 6) (v : V) :
    1 ≤ G.degree v := by
  classical
  by_contra! low
  let B := Gᶜ.neighborFinset v
  have enough : 14≤ B.card := by
    change 14≤ Gᶜ.degree v
    rw [G.degree_compl,sz]
    omega
  obtain ⟨f,inside⟩ := Function.Embedding.exists_of_card_le_finset (α:=Fin 14) (s:=B) (by simpa using enough)
  let K := G.comap f
  let g := SimpleGraph.Embedding.comap f G
  have yes : ¬Kᶜ.CliqueFree 5 := fun no => OMA.Ramsey37Density.fourteen_works K ⟨CliqueFree.comap g.isContained tri,no⟩
  obtain ⟨s,five⟩ := not_forall_not.mp yes
  have clique : Gᶜ.IsNClique 5 (s.map f) := by
    refine ⟨?_,(card_map _).trans five.card_eq⟩
    intro x hx y hy ne
    obtain ⟨i,hi,rfl⟩ := mem_map.mp hx
    obtain ⟨j,hj,rfl⟩ := mem_map.mp hy
    exact (SimpleGraph.Embedding.complEquiv g).map_adj_iff.mpr (five.isClique hi hj (fun h => ne (congrArg f h)))
  apply ind _ (clique.insert (a:=v) ?_)
  intro x hx
  obtain ⟨i,_,rfl⟩ := mem_map.mp hx
  exact (Gᶜ.mem_neighborFinset ..).mp (inside ⟨i,rfl⟩)

/-- The cardinality component of each independent-set entry counts its encoded vertices. -/
theorem independent_weight (b : List Nat) {p : Nat × Nat} (h : p∈inds b) :
    countBits b.length p.1 = p.2 := by
  induction b generalizing p with
  | nil =>
    simp [inds] at h
    subst p
    rfl
  | cons m b ih =>
    rcases List.mem_append.mp h with left|right
    · obtain ⟨⟨x,k⟩,hx,rfl⟩ := List.mem_map.mp left
      simpa [ind0,countBits] using ih hx
    · obtain ⟨⟨x,k⟩,hx,rfl⟩ := List.mem_map.mp right
      have eq := ih (List.mem_filter.mp hx).1
      change countBits b.length x = k at eq
      change (2*x+1)%2 + countBits b.length ((2*x+1)/2) = k+1
      rw [half_step,eq]
      omega

theorem extension_floor {d : Nat} {b cs : List Nat} (ex : Extension 6 d b cs) :
    d*(d-1) ≤ (cs.map (countBits b.length)).sum := by
  have each (x) (hx : x∈cs) : d-1 ≤ countBits b.length x := by
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (ex.2.1 x hx)
    obtain ⟨inside,low⟩ := List.mem_filter.mp hp
    have hl := of_decide_eq_true (Bool.and_eq_true_iff.mp low).1
    rw [independent_weight b inside]
    omega
  have bound (l : List Nat) (h : ∀ x∈l,d-1 ≤ countBits b.length x) :
      l.length*(d-1) ≤ (l.map (countBits b.length)).sum := by
    induction l with
    | nil => simp
    | cons x l ih =>
      have first := h x (.head _)
      have rest := ih (fun y hy=> h y (.tail _ hy))
      simp only [List.length_cons,Nat.succ_mul,List.map_cons,List.sum_cons]
      omega
  simpa only [ex.1] using bound cs each

theorem ground_from_members (swaps : List Nat → List Nat)
    (one : ∀ {b}, b ∈ levels normalized 5 13 4 → edges_ (relabel (swaps b) b) ≤ 25 → False)
    (two : ∀ {b}, b ∈ levels normalized 5 12 4 → edges_ (relabel (swaps b) b) ≤ 22 →
      relabel (swaps b) b ∈ pairs.map RowCase.base)
    (three : ∀ {b}, b ∈ levels normalized 5 11 4 → edges_ (relabel (swaps b) b) ≤ 17 →
      relabel (swaps b) b ∈ triples.map RowCase.base)
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (sz : Fintype.card V = 15) (tri : G.CliqueFree 3) (ind : Gᶜ.CliqueFree 6)
    (few : G.edgeFinset.card ≤ 26) :
    ∃ (vs : List V) (d : Nat) (r : RowCase) (cs : List Nat), vs.Nodup ∧ vs.toFinset=univ ∧
      ((d=2 ∧ r∈pairs) ∨ (d=3 ∧ r∈triples)) ∧ Extension 6 d r.base cs ∧ cs.Pairwise (·≤·) ∧
      encode G vs=attach cs r.base := by
  classical
  let U := (univ : Finset V)
  have cu : U.card = 15 := card_univ.trans sz
  have small : Small G U 6 := by
    intro S _ h
    by_contra! big
    exact ind.mono big S ⟨h,rfl⟩
  have low : ∃ x, G.degree x≤3 := by
    by_contra! high
    have total := Finset.sum_le_sum (s:=U) (f:=fun _=>4) (fun x _=> high x)
    rw [Finset.sum_const,cu,nsmul_eq_mul,G.sum_degrees_eq_twice_card_edges] at total
    omega
  have upper : U.Nonempty → ∃ x∈U,(U.filter (G.Adj x)).card≤3 := by
    obtain ⟨x,hx⟩ := low
    exact fun _ => ⟨x,mem_univ _,by simpa only [U,←SimpleGraph.neighborFinset_eq_filter,
      SimpleGraph.card_neighborFinset_eq_degree] using hx⟩
  obtain ⟨vs,d,b,cs,nd,allv,hd,level,ext,sort,code,v,_,deg⟩ :=
    root_with_swaps G tri normalized (fun l=> relabel_real G (renumber (encode G l)) l)
      swaps 5 U (card_pos.mp (by omega)) 3 small upper
  rw [cu] at level
  have lb := min_one G sz tri ind v
  simp only [U,←SimpleGraph.neighborFinset_eq_filter,SimpleGraph.card_neighborFinset_eq_degree] at deg
  have eb := Sparse32.edge_card G vs nd allv
  rw [code,edges_attached,ext.1] at eb
  have counts := extension_floor ext
  rcases (show d=1 ∨ d=2 ∨ d=3 by omega) with rfl|rfl|rfl
  · exact False.elim (one level (by omega))
  · obtain ⟨r,hr,eq⟩ := List.mem_map.mp (two level (by omega))
    rw [←eq] at ext code
    exact ⟨vs,2,r,cs,nd,allv,Or.inl ⟨rfl,hr⟩,ext,sort,code⟩
  · obtain ⟨r,hr,eq⟩ := List.mem_map.mp (three level (by omega))
    rw [←eq] at ext code
    exact ⟨vs,3,r,cs,nd,allv,Or.inr ⟨rfl,hr⟩,ext,sort,code⟩
end SparseFifteen
end

section
namespace SparseFifteen
def rawBaseSwaps (b : List Nat) := (([([3,128,145,3,2,6,3,2,2,1,0],[3,5]),
([3,192,128,3,2,6,3,2,2,1,0],[1,7,9]),
([3,192,136,3,2,6,3,2,2,1,0],[3,2,1,0,3,2,1,5,4,3,2,4,9,8,7,6,8,7,9,8]),
([3,192,132,3,2,6,3,2,2,1,0],[2,1,0,3,2,1,4,3,2,4,9,8,7,6,8,7,9,8]),
([3,192,129,3,2,6,3,2,2,1,0],[3,5]),
([3,192,145,3,2,6,3,2,2,1,0],[3,5]),
([3,192,137,3,2,6,3,2,2,1,0],[3,5]),
([3,32,76,3,2,6,3,2,2,1,0],[7,9]),
([3,96,76,3,2,6,3,2,2,1,0],[7,9]),
([3,16,50,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,9,8,7,6,8,7,9,8]),
([3,144,144,3,2,6,3,2,2,1,0],[3,2,1,0,3,2,1,5,4,3,2,8,7,6,7,9,8]),
([3,8,49,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,9,8,7,6,9,8,7,9,8,9]),
([3,136,144,3,2,6,3,2,2,1,0],[2,1,0,3,2,1,4,3,2,8,7,6,7,9,8]),
([3,136,146,3,2,6,3,2,2,1,0],[3,5]),
([3,136,145,3,2,6,3,2,2,1,0],[3,5]),
([3,24,48,3,2,6,3,2,2,1,0],[2,1,0,3,2,1,4,3,2,8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,9,8,7,6,8,7,9,8]),
([3,24,50,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,9,8,7,6,8,7,9,8]),
([3,24,49,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,9,8,7,6,9,8,7,9,8,9]),
([3,152,144,3,2,6,3,2,2,1,0],[1,7,9]),
([3,4,9,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,9,8,7,6,9,8,7,9,8,9]),
([3,4,137,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,9,8,7,6,9,8,7,9,8,9]),
([3,4,73,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,9,8,7,6,5,4,9,8,7,6,5,9,8,7,6,9,8,7,9,8,9]),
([3,260,137,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,2,1,0,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,6,8]),
([3,132,144,3,2,6,3,2,2,1,0],[1,7,9]),
([3,132,146,3,2,6,3,2,2,1,0],[2,1,0,4,3,2,1,4,3,2,8,7,6,9,8,7,8,9]),
([3,132,137,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,9,8,7,6,5,4,9,8,7,6,5,9,8,7,6,9,8,7,9,8,9]),
([3,132,73,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,6,8]),
([3,68,137,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,9,8,7,6,9,8,7,9,8,9]),
([3,68,73,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,9,8,7,6,9,8,7,9,8,9]),
([3,196,128,3,2,6,3,2,2,1,0],[1,7,9]),
([3,196,144,3,2,6,3,2,2,1,0],[1,7,9]),
([3,196,136,3,2,6,3,2,2,1,0],[1,7,9]),
([3,196,132,3,2,6,3,2,2,1,0],[1,3,5,7,9]),
([3,196,130,3,2,6,3,2,2,1,0],[2,1,0,4,3,2,1,4,3,2,4,9,8,7,6,9,8,7,9,8,9]),
([3,196,129,3,2,6,3,2,2,1,0],[1,3,5,7,9]),
([3,36,72,3,2,6,3,2,2,1,0],[7,9]),
([3,36,76,3,2,6,3,2,2,1,0],[7,9]),
([3,36,137,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,9,8,7,6,5,4,9,8,7,6,5,9,8,7,6,9,8,7,9,8,9]),
([3,36,73,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,9,8,7,6,5,4,9,8,7,6,5,9,8,7,6,9,8,7,9,8,9]),
([3,100,136,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,4,8,7,6,7,9,8]),
([3,100,72,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,4,8,7,6,7,9,8]),
([3,12,129,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,9,8,7,6,9,8,7,9,8,9]),
([3,12,65,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,9,8,7,6,5,4,9,8,7,6,5,9,8,7,6,9,8,7,9,8,9]),
([3,12,33,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,4,7,9]),
([3,12,97,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,9,8,7,6,5,4,9,8,7,6,5,9,8,7,6,9,8,7,9,8,9]),
([3,12,17,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,4,7,9]),
([3,12,145,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,9,8,7,6,9,8,7,9,8,9]),
([3,12,49,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,9,8,7,6,9,8,7,9,8,9]),
([3,12,9,3,2,6,3,2,2,1,0],[1,8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,9,8,7,6,8,7,9,8]),
([3,12,137,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,9,8,7,6,9,8,7,9,8,9]),
([3,12,73,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,9,8,7,6,5,4,9,8,7,6,5,9,8,7,6,9,8,7,9,8,9]),
([3,140,144,3,2,6,3,2,2,1,0],[1,7,9]),
([3,140,129,3,2,6,3,2,2,1,0],[1,8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,9,8,7,6,8,7,9,8]),
([3,2,6,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,9,8,7,6,8,7,9,8]),
([3,2,134,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,9,8,7,6,8,7,9,8]),
([3,2,70,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,9,8,7,6,5,4,9,8,7,6,5,9,8,7,6,8,7,9,8]),
([3,258,134,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,2,1,0,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2]),
([3,130,144,3,2,6,3,2,2,1,0],[1,3,5,7,9]),
([3,130,130,3,2,6,3,2,2,1,0],[1,7,9]),
([3,130,146,3,2,6,3,2,2,1,0],[3,5]),
([3,130,134,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,9,8,7,6,5,4,9,8,7,6,5,9,8,7,6,8,7,9,8]),
([3,130,70,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2]),
([3,130,145,3,2,6,3,2,2,1,0],[3,2,1,0,5,4,3,2,1,4,3,2,8,7,6,9,8,7,8,9]),
([3,66,132,3,2,6,3,2,2,1,0],[3,5]),
([3,66,140,3,2,6,3,2,2,1,0],[3,5]),
([3,66,134,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,9,8,7,6,8,7,9,8]),
([3,66,70,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,9,8,7,6,8,7,9,8]),
([3,194,128,3,2,6,3,2,2,1,0],[1,3,5,7,9]),
([3,194,144,3,2,6,3,2,2,1,0],[1,3,5,7,9]),
([3,194,136,3,2,6,3,2,2,1,0],[1,7,9]),
([3,194,132,3,2,6,3,2,2,1,0],[1,3,5,7,9]),
([3,194,130,3,2,6,3,2,2,1,0],[1,7,9]),
([3,194,129,3,2,6,3,2,2,1,0],[3,2,1,0,5,4,3,2,1,4,3,2,4,9,8,7,6,9,8,7,9,8,9]),
([3,34,68,3,2,6,3,2,2,1,0],[3,5,7,9]),
([3,34,76,3,2,6,3,2,2,1,0],[3,5,7,9]),
([3,34,134,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,9,8,7,6,5,4,9,8,7,6,5,9,8,7,6,8,7,9,8]),
([3,34,70,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,9,8,7,6,5,4,9,8,7,6,5,9,8,7,6,8,7,9,8]),
([3,98,132,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,4,7,6,9,8]),
([3,98,68,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,4,7,6,9,8]),
([3,18,130,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,9,8,7,6,8,7,9,8]),
([3,18,66,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,9,8,7,6,5,4,9,8,7,6,5,9,8,7,6,8,7,9,8]),
([3,18,34,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,4,6,8,7,9]),
([3,18,98,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,9,8,7,6,5,4,9,8,7,6,5,9,8,7,6,8,7,9,8]),
([3,18,18,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,4,6,8,7,9]),
([3,18,146,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,9,8,7,6,8,7,9,8]),
([3,18,50,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,9,8,7,6,8,7,9,8]),
([3,18,134,3,2,6,3,2,2,1,0],[8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,9,8,7,6,8,7,9,8]),
([3,18,70,3,2,6,3,2,2,1,0],[9,8,7,6,5,4,3,9,8,7,6,5,4,9,8,7,6,5,9,8,7,6,8,7,9,8]),
([3,146,144,3,2,6,3,2,2,1,0],[1,3,5,7,9]),
([3,146,130,3,2,6,3,2,2,1,0],[1,8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,9,8,7,6,9,8,7,9,8,9]),
([3,128,144,3,12,9,3,2,2,1,0],[0,8,7,6,5,4,3,2,3,5,4,5,6,7,8]),
([3,128,148,3,12,9,3,2,2,1,0],[2,1,0,3,2,1,4,3,2,8,7,6,9,8,7,8,9]),
([3,64,136,3,12,9,3,2,2,1,0],[0,7,6,5,4,3,2,3,4,5,7,6,7,8]),
([3,64,138,3,12,9,3,2,2,1,0],[2,1,0,4,3,2,1,4,3,2,7,6,9,8,7,9]),
([3,64,137,3,12,9,3,2,2,1,0],[4,6,8]),
([3,192,128,3,12,9,3,2,2,1,0],[2,1,0,4,3,2,1,4,3,2,4,9,8,7,6,8,7,9,8]),
([3,192,136,3,12,9,3,2,2,1,0],[4,6,8]),
([3,192,132,3,12,9,3,2,2,1,0],[2,1,0,3,2,1,4,3,2,4,9,8,7,6,9,8,7,9,8,9]),
([3,192,130,3,12,9,3,2,2,1,0],[2,1,0,4,3,2,1,4,3,2,4,9,8,7,6,8,7,9,8]),
([3,32,74,3,12,9,3,2,2,1,0],[2,1,0,4,3,2,1,4,3,2,6,8,7,9]),
([3,16,52,3,12,9,3,2,2,1,0],[2,1,0,3,2,1,4,3,2,7,9]),
([3,16,145,3,12,9,3,2,2,1,0],[4,6,8]),
([3,144,144,3,12,9,3,2,2,1,0],[4,6,8]),
([3,8,9,3,12,9,3,2,2,1,0],[0,4,3,2,9,8,7,6,5,4,3,9,8,7,6,5,4,9,8,7,6,5,9,8,7,6,9,8,7,9,8]),
([3,8,137,3,12,9,3,2,2,1,0],[0,4,3,2,8,7,6,5,4,3,7,6,5,4,9,8,7,6,5,9,8,7,6,9,8,7,9,8]),
([3,8,73,3,12,9,3,2,2,1,0],[9,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,7,6,8]),
([3,72,136,3,12,9,3,2,2,1,0],[2,1,0,3,2,1,4,3,2,7,6,9,8]),
([3,40,72,3,12,9,3,2,2,1,0],[2,1,0,3,2,1,4,3,2,9,8,7,6,5,4,3,8,7,6,5,4,9,8,7,6,5,8,7,6,8,7,9,8]),
([3,4,17,3,12,9,3,2,2,1,0],[0,3,2,9,8,7,6,5,4,3,8,7,6,5,4,9,8,7,6,5,8,7,6,9,8,7,9,8]),
([3,4,145,3,12,9,3,2,2,1,0],[0,3,2,7,6,5,4,3,6,5,4,9,8,7,6,5,9,8,7,6,9,8,7,9,8]),
([3,4,49,3,12,9,3,2,2,1,0],[9,8,7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,6,9,8]),
([3,132,144,3,12,9,3,2,2,1,0],[2,1,0,4,3,2,1,4,3,2,8,7,6,7,9,8]),
([3,20,48,3,12,9,3,2,2,1,0],[9,8,7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,5,4,3,7,6,5,4,7,6,5,8,7,6,7,9,8]),
([3,20,17,3,12,9,3,2,2,1,0],[9,8,7,6,5,4,3,8,7,6,5,4,9,8,7,6,5,9,8,7,6,9,8,7,8,9]),
([3,12,129,3,12,9,3,2,2,1,0],[9,8,7,6,5,4,3,9,8,7,6,5,4,9,8,7,6,5,8,7,6,9,8,7,9,8,9]),
([3,12,65,3,12,9,3,2,2,1,0],[9,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,4,7]),
([3,12,33,3,12,9,3,2,2,1,0],[9,8,7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,4,9]),
([3,12,17,3,12,9,3,2,2,1,0],[9,8,7,6,5,4,3,9,8,7,6,5,4,9,8,7,6,5,8,7,6,9,8,7,9,8,9]),
([3,12,9,3,12,9,3,2,2,1,0],[9,8,7,6,5,4,3,8,7,6,5,4,9,8,7,6,5,9,8,7,6,9,8,7,8,9]),
([3,2,6,3,12,9,3,2,2,1,0],[9,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,7]),
([3,66,136,3,12,9,3,2,2,1,0],[4,6,8]),
([3,66,130,3,12,9,3,2,2,1,0],[4,6,8]),
([3,194,128,3,12,9,3,2,2,1,0],[1,9,8,7,6,5,4,3,8,7,6,5,4,9,8,7,6,5,9,8,7,6,9,8,7,8,9]),
([3,34,130,3,12,9,3,2,2,1,0],[1,9,8,7,6,5,4,3,9,8,7,6,5,4,9,8,7,6,5,8,7,6,9,8,7,9,8,9]),
([3,34,66,3,12,9,3,2,2,1,0],[9,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,4,6,9,8,7,9]),
([3,18,144,3,12,9,3,2,2,1,0],[4,6,8]),
([3,18,132,3,12,9,3,2,2,1,0],[1,9,8,7,6,5,4,3,8,7,6,5,4,9,8,7,6,5,9,8,7,6,9,8,7,8,9]),
([3,18,36,3,12,9,3,2,2,1,0],[9,8,7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,4,7,6,8,7,9]),
([3,18,20,3,12,9,3,2,2,1,0],[1,9,8,7,6,5,4,3,9,8,7,6,5,4,9,8,7,6,5,8,7,6,9,8,7,9,8,9]),
([3,128,130,7,20,18,10,1,1,1,0],[0,8,7,6,5,4,3,2,9,8,7,6,5,4,5]),
([3,32,36,7,20,18,10,1,1,1,0],[0,6,5,4,3,2,5,4,7,6,5,7,6,9,8,7,9]),
([3,16,33,7,20,18,10,1,1,1,0],[0,5,4,3,2,7,6,5,7,6]),
([3,48,32,7,20,18,10,1,1,1,0],[1,0,7,6,5,4,3,2,7,6,5,4,7,6,5,7,9]),
([3,8,144,7,20,18,10,1,1,1,0],[0,4,3,2,6,5,4,9,8,7,6,5,9,8,7,6,9,8,7,8,9]),
([3,136,128,7,20,18,10,1,1,1,0],[1,0,9,8,7,6,5,4,3,2,5,4,9,8,7,6,5,6,8,7,9]),
([3,4,65,7,20,18,10,1,1,1,0],[0,3,2,8,7,6,5,9,8,7,6,7,9]),
([3,2,10,7,20,18,10,1,1,1,0],[0,2,5,7,6,8,7,8,9]),
([7,40,98,65,1,1,3,2,2,1,0],[2,7,9]),
([7,36,98,66,1,1,3,2,2,1,0],[2,7,9]),
([7,100,68,65,1,1,3,2,2,1,0],[3,2,1,0,3,2,1,4,3,2,3,8,7,6,7,9,8]),
([7,100,66,66,1,1,3,2,2,1,0],[3,2,1,0,2,1,4,3,2,3,9,8,7,6,8,7,9,8]),
([7,20,96,65,1,6,3,2,2,1,0],[1,0,8,7,6,5,4,3,2,8,7,6,5,4,3,9,8,7,6,5,4,5,6,7,9]),
([7,20,66,72,1,6,3,2,2,1,0],[2,1,0,9,8,7,6,5,4,3,2,7,6,5,4,3,9,8,7,6,5,4,5,6,7,9]),
([7,48,96,65,3,10,10,1,0,1,0],[0,6,5,4,3,2,1,6,5,4,3,7,6,5,4,8,7,6,9,8,7,9,8]),
([7,72,66,72,3,10,10,1,0,1,0],[0,7,6,5,4,3,2,1,5,4,3,7,6,5,4,5,9,8,7,6,9,8,7,9,8]),
([7,68,72,72,3,10,10,1,0,1,0],[1,0,8,7,6,5,4,3,2,1,6,5,4,3,9,8,7,6,5,4,5,8,7,6,9,8,7,9,8]),
([7,36,96,66,3,10,10,1,0,1,0],[2,1,0,9,8,7,6,5,4,3,2,1,5,4,3,9,8,7,6,5,4,5,9,8,7,6,9,8,7,9,8]),
([7,132,68,80,3,2,9,1,1,1,0],[0,3,2,1,8,7,6,5,4,3,5,7,6,8,7,8]),
([7,68,80,66,3,2,9,1,1,1,0],[7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,2,8,7,6,5,4,3,4,7,9,8]),
([7,68,72,66,3,2,9,1,1,1,0],[9,8,7,6,5,4,3,2,1,0,9,8,7,6,5,4,3,2,1,4,3,2,7,6,5,4,3,5,4,9,8]),
([7,68,68,66,3,2,9,1,1,1,0],[3,2,1,0,5,4,3,2,1,2,5,4,3,6,5,4,7,6,5,8,7,6,7,9,8]),
([7,68,66,66,3,2,9,1,1,1,0],[4,3,2,1,0,6,5,4,3,2,1,4,3,2,5,4,3,6,5,4,9,8,7,6,5,9,8,7,6,8,7,9,8])] : List (List Nat × List Nat)).lookup b).getD []
def sub0 : List (List Nat) := []
def sub1 : List (List Nat) := []
def s2_0 : List Nat := [3,2,6,3,2,2,1,0]
def s2_1 : List Nat := [3,12,9,3,2,2,1,0]
def s2_2 : List Nat := [7,20,18,10,1,1,1,0]
def sub2 : List (List Nat) := [s2_0,s2_1,s2_2]
def s3_0 : List Nat := [1,0,3,2,2,1,0]
def s3_1 : List Nat := [1,1,3,2,2,1,0]
def s3_2 : List Nat := [1,6,3,2,2,1,0]
def s3_3 : List Nat := [3,10,10,1,0,1,0]
def s3_4 : List Nat := [3,2,9,1,1,1,0]
def s3_5 : List Nat := [3,2,8,1,1,1,0]
def s3_6 : List Nat := [3,10,9,1,1,1,0]
def s3_7 : List Nat := [3,18,9,1,1,1,0]
def s3_8 : List Nat := [3,12,9,3,2,1,0]
def sub3 : List (List Nat) := [s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8]
def s4_0 : List Nat := [0,3,2,2,1,0]
def s4_1 : List Nat := [1,0,1,0,1,0]
def s4_2 : List Nat := [1,8,1,0,1,0]
def s4_3 : List Nat := [1,4,1,0,1,0]
def s4_4 : List Nat := [1,2,1,0,1,0]
def s4_5 : List Nat := [1,10,1,0,1,0]
def s4_6 : List Nat := [1,6,1,0,1,0]
def s4_7 : List Nat := [1,1,1,0,1,0]
def s4_8 : List Nat := [1,9,1,0,1,0]
def s4_9 : List Nat := [1,5,1,0,1,0]
def s4_10 : List Nat := [1,0,1,1,1,0]
def s4_11 : List Nat := [1,8,1,1,1,0]
def s4_12 : List Nat := [1,4,1,1,1,0]
def s4_13 : List Nat := [1,2,1,1,1,0]
def s4_14 : List Nat := [1,10,1,1,1,0]
def s4_15 : List Nat := [1,1,1,1,1,0]
def s4_16 : List Nat := [1,9,1,1,1,0]
def s4_17 : List Nat := [1,5,1,1,1,0]
def s4_18 : List Nat := [1,0,3,2,1,0]
def s4_19 : List Nat := [1,8,3,2,1,0]
def s4_20 : List Nat := [1,4,3,2,1,0]
def s4_21 : List Nat := [1,2,3,2,1,0]
def s4_22 : List Nat := [1,6,3,2,1,0]
def s4_23 : List Nat := [1,1,3,2,1,0]
def s4_24 : List Nat := [1,9,3,2,1,0]
def s4_25 : List Nat := [3,6,5,0,1,0]
def s4_26 : List Nat := [3,8,5,1,1,0]
def s4_27 : List Nat := [3,4,5,1,1,0]
def s4_28 : List Nat := [3,2,4,1,1,0]
def s4_29 : List Nat := [3,2,5,1,1,0]
def s4_30 : List Nat := [3,10,5,1,1,0]
def s4_31 : List Nat := [7,12,6,3,0,0]
def sub4 : List (List Nat) := [s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15,s4_16,s4_17,s4_18,s4_19,s4_20,s4_21,s4_22,s4_23,s4_24,s4_25,s4_26,s4_27,s4_28,s4_29,s4_30,s4_31]
end SparseFifteen
end

section
namespace SparseFifteen
open OMA.RamseyFinite
def baseSwaps (b : List Nat) := if edges_ b≤17 then rawBaseSwaps b else []
def post (b : List Nat) := relabel (baseSwaps b) b
theorem base_limit {b : List Nat} (h : edges_ (post b)≤17) : edges_ b≤17 := by
  by_contra! hi
  exact (Nat.not_le.mpr hi) (by simpa only [post,baseSwaps,if_neg (Nat.not_le.mpr hi),relabel,List.foldl_nil] using h)
theorem base1_of {b : List Nat} (hb : b ∈ levels normalized 5 13 4) (cap : edges_ (post b) ≤25) : False := by
  have h := of_decide_eq_true (List.all_eq_true.mp smaller3 b hb)
  obtain rfl := List.mem_singleton.mp h
  change edges_ (post b3_0) ≤ 25 at cap
  exact (by decide : ¬ (edges_ (post b3_0) ≤ 25)) cap
theorem base2_of {b : List Nat} (hb : b ∈ levels normalized 5 12 4) (cap : edges_ (post b) ≤22) :
    post b∈pairs.map RowCase.base := by
  have h := of_decide_eq_true (List.all_eq_true.mp smaller4 b hb)
  exact (of_decide_eq_true (List.all_eq_true.mp
    (show roots4.all (fun v => decide (edges_ (post v)≤22 → post v∈pairs.map RowCase.base))=true by decide +kernel) b h)) cap
end SparseFifteen
end

section
namespace SparseFifteen
open OMA.RamseyFinite
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
theorem smallSub0 : (levels normalized 4 10 3).all (fun z => decide (z∈sub0))=true := by decide +kernel
theorem covered0 {z t : List Nat} (hz : z∈levels normalized 4 10 3) (_ht : t∈grow 5 0 z)
    (_small : edges_ (normalized t)≤17) : post (normalized t)∈triples.map RowCase.base := by
  have mem := of_decide_eq_true (List.all_eq_true.mp smallSub0 z hz)
  simp [sub0] at mem
end SparseFifteen
end

section
namespace SparseFifteen
open OMA.RamseyFinite
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
theorem smallSub1 : (levels normalized 4 9 3).all (fun z => decide (z∈sub1))=true := by decide +kernel
theorem covered1 {z t : List Nat} (hz : z∈levels normalized 4 9 3) (_ht : t∈grow 5 1 z)
    (_small : edges_ (normalized t)≤17) : post (normalized t)∈triples.map RowCase.base := by
  have mem := of_decide_eq_true (List.all_eq_true.mp smallSub1 z hz)
  simp [sub1] at mem
end SparseFifteen
end

section
namespace SparseFifteen
open OMA.RamseyFinite
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
theorem smallSub2 : (levels normalized 4 8 3).all (fun z => decide (z∈sub2))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child2_0 : (grow 5 2 s2_0).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child2_1 : (grow 5 2 s2_1).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child2_2 : (grow 5 2 s2_2).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
theorem covered2 {z t : List Nat} (hz : z∈levels normalized 4 8 3) (ht : t∈grow 5 2 z)
    (small : edges_ (normalized t)≤17) : post (normalized t)∈triples.map RowCase.base := by
  have mem := of_decide_eq_true (List.all_eq_true.mp smallSub2 z hz)
  simp only [sub2,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl
  · exact (of_decide_eq_true (List.all_eq_true.mp child2_0 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child2_1 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child2_2 t ht)) small
end SparseFifteen
end

section
namespace SparseFifteen
open OMA.RamseyFinite
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
theorem smallSub3 : (levels normalized 4 7 3).all (fun z => decide (z∈sub3))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child3_0 : (grow 5 3 s3_0).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child3_1 : (grow 5 3 s3_1).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child3_2 : (grow 5 3 s3_2).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child3_3 : (grow 5 3 s3_3).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child3_4 : (grow 5 3 s3_4).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child3_5 : (grow 5 3 s3_5).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child3_6 : (grow 5 3 s3_6).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child3_7 : (grow 5 3 s3_7).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child3_8 : (grow 5 3 s3_8).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
theorem covered3 {z t : List Nat} (hz : z∈levels normalized 4 7 3) (ht : t∈grow 5 3 z)
    (small : edges_ (normalized t)≤17) : post (normalized t)∈triples.map RowCase.base := by
  have mem := of_decide_eq_true (List.all_eq_true.mp smallSub3 z hz)
  simp only [sub3,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact (of_decide_eq_true (List.all_eq_true.mp child3_0 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child3_1 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child3_2 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child3_3 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child3_4 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child3_5 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child3_6 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child3_7 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child3_8 t ht)) small
end SparseFifteen
end

section
namespace SparseFifteen
open OMA.RamseyFinite
set_option maxRecDepth 30000 in
set_option maxHeartbeats 12000000 in
theorem smallSub4 : (levels normalized 4 6 3).all (fun z => decide (z∈sub4))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_0 : (grow 5 4 s4_0).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_1 : (grow 5 4 s4_1).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_2 : (grow 5 4 s4_2).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_3 : (grow 5 4 s4_3).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_4 : (grow 5 4 s4_4).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_5 : (grow 5 4 s4_5).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_6 : (grow 5 4 s4_6).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_7 : (grow 5 4 s4_7).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_8 : (grow 5 4 s4_8).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_9 : (grow 5 4 s4_9).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_10 : (grow 5 4 s4_10).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_11 : (grow 5 4 s4_11).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_12 : (grow 5 4 s4_12).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_13 : (grow 5 4 s4_13).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_14 : (grow 5 4 s4_14).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_15 : (grow 5 4 s4_15).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_16 : (grow 5 4 s4_16).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_17 : (grow 5 4 s4_17).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_18 : (grow 5 4 s4_18).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_19 : (grow 5 4 s4_19).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_20 : (grow 5 4 s4_20).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_21 : (grow 5 4 s4_21).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_22 : (grow 5 4 s4_22).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_23 : (grow 5 4 s4_23).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_24 : (grow 5 4 s4_24).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_25 : (grow 5 4 s4_25).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_26 : (grow 5 4 s4_26).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_27 : (grow 5 4 s4_27).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_28 : (grow 5 4 s4_28).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_29 : (grow 5 4 s4_29).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_30 : (grow 5 4 s4_30).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 32000000 in
theorem child4_31 : (grow 5 4 s4_31).all
    (fun t => decide (edges_ (normalized t)≤17 → post (normalized t)∈triples.map RowCase.base))=true := by decide +kernel
theorem covered4 {z t : List Nat} (hz : z∈levels normalized 4 6 3) (ht : t∈grow 5 4 z)
    (small : edges_ (normalized t)≤17) : post (normalized t)∈triples.map RowCase.base := by
  have mem := of_decide_eq_true (List.all_eq_true.mp smallSub4 z hz)
  simp only [sub4,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_0 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_1 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_2 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_3 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_4 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_5 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_6 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_7 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_8 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_9 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_10 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_11 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_12 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_13 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_14 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_15 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_16 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_17 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_18 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_19 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_20 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_21 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_22 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_23 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_24 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_25 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_26 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_27 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_28 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_29 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_30 t ht)) small
  · exact (of_decide_eq_true (List.all_eq_true.mp child4_31 t ht)) small
end SparseFifteen
end

section
namespace SparseFifteen
open OMA.RamseyFinite
theorem base3_of {b : List Nat} (hb : b∈levels normalized 5 11 4) (cap : edges_ (post b)≤17) :
    post b ∈ triples.map RowCase.base := by
  have orig := base_limit cap
  rw [levels,if_neg (by decide : 11≠0)] at hb
  simp only [List.mem_eraseDups,List.mem_flatMap,List.mem_range,List.mem_map] at hb
  obtain ⟨q,hq,z,hz,t,ht,rfl⟩ := hb
  change q<5 at hq
  interval_cases q
  · exact covered0 hz ht orig
  · exact covered1 hz ht orig
  · exact covered2 hz ht orig
  · exact covered3 hz ht orig
  · exact covered4 hz ht orig
end SparseFifteen
end

section
namespace SparseFifteen
open OMA.RamseyFinite SimpleGraph Finset

theorem ground {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (sz : Fintype.card V = 15) (tri : G.CliqueFree 3) (ind : Gᶜ.CliqueFree 6)
    (few : G.edgeFinset.card ≤ 26) :
    ∃ (vs : List V) (d : Nat) (r : RowCase) (cs : List Nat), vs.Nodup ∧ vs.toFinset=univ ∧
      ((d=2 ∧ r∈pairs) ∨ (d=3 ∧ r∈triples)) ∧ Extension 6 d r.base cs ∧ cs.Pairwise (·≤·) ∧
      encode G vs=attach cs r.base :=
  ground_from_members baseSwaps (fun hb cap => base1_of hb cap) (fun hb cap => base2_of hb cap)
    (fun hb cap => base3_of hb cap) G sz tri ind few

end SparseFifteen
end

section
namespace SparseFifteen
open SimpleGraph Finset

/-- For order fifteen, the sparse triangle-free graphs with independence
number at most five have exactly eight possible forward adjacency codes. -/
theorem classification {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V)
    [DecidableRel K.Adj] (sz : Fintype.card V=15) (tri : K.CliqueFree 3)
    (ind : Kᶜ.CliqueFree 6) (cap : K.edgeFinset.card≤26) :
    ∃ (i : Fin 8) (vs : List V), vs.Nodup ∧ vs.toFinset=univ ∧ GlueSeed.encode K vs=adj i :=
  classification_of_ground K cap (ground K sz tri ind cap)

end SparseFifteen
end

section
namespace FiveIso
def moves0 : List Move := [
  ⟨0,[1030,6406,8337,8961,18465],0,[7,6,5,4,3,2,1,0,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,16,15,14,13,12,11,10,9,8,7,6,5,4,3,12,11,10,9,8,7,6,5,4,6,5,13,12,11,10,9,8,7,6,8,7,13,12,11,10,9,8,10,9,19,18,17,16,15,14,13,12,11,10,16,15,14,13,12,11,16,15,14,13,12,19,18,17,16,15,14,13,19,18,17,16,15,14,19,18,17,16,15,16,17,19]⟩,
  ⟨0,[1030,6406,12353,16529,17153],0,[1,0,5,4,3,2,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,17,16,15,14,13,12,11,10,9,8,7,6,5,4,8,7,6,5,17,16,15,14,13,12,11,10,9,8,7,6,9,8,7,15,14,13,12,11,10,9,8,10,9,18,17,16,15,14,13,12,11,10,14,13,12,11,17,16,15,14,13,12,19,18,17,16,15,14,13,17,16,15,14,18,17,16,15,18,17,16,18,19]⟩,
  ⟨0,[1033,6409,8338,8962,18466],0,[8,7,6,5,4,3,2,1,0,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,16,15,14,13,12,11,10,9,8,7,6,5,4,3,12,11,10,9,8,7,6,5,4,6,5,13,12,11,10,9,8,7,6,8,7,13,12,11,10,9,8,10,9,19,18,17,16,15,14,13,12,11,10,16,15,14,13,12,11,16,15,14,13,12,19,18,17,16,15,14,13,19,18,17,16,15,14,19,18,17,16,15,16,18,17,19]⟩,
  ⟨0,[1033,6409,12354,16530,17154],0,[1,0,6,5,4,3,2,1,10,9,8,7,6,5,4,3,2,8,7,6,5,4,3,17,16,15,14,13,12,11,10,9,8,7,6,5,4,8,7,6,5,17,16,15,14,13,12,11,10,9,8,7,6,9,8,7,15,14,13,12,11,10,9,8,10,9,18,17,16,15,14,13,12,11,10,14,13,12,11,17,16,15,14,13,12,19,18,17,16,15,14,13,17,16,15,14,18,17,16,15,18,17,16,18,19]⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem check0 : moves0.all valid=true := by decide +kernel
end FiveIso
end

section
namespace FiveIso
def moves1 : List Move := [
  ⟨0,[1169,1542,6150,8449,18721],1,[16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,4,3,2,1,11,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,16,15,14,13,12,11,10,9,8,7,6,5,4,16,15,14,13,12,11,10,9,8,7,6,10,9,8,7,9,8,16,15,14,13,12,11,10,9,16,15,14,13,12,11,10,13,12,11,12,15,14,15,18]⟩,
  ⟨0,[1169,1542,6150,8513,18689],0,[7,6,5,4,3,2,1,0,12,11,10,9,8,7,6,5,4,3,2,1,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,5,4,5,6,15,14,13,12,11,10,9,8,7,10,9,8,16,15,14,13,12,11,10,9,19,18,17,16,15,14,13,12,11,10,11,18,17,16,15,14,13,19,18,17,16,15,14,19,18,17,16,18,17,19,18]⟩,
  ⟨0,[1169,1542,6150,12545,16673],2,[7,6,5,4,3,2,1,0,12,11,10,9,8,7,6,5,4,3,2,1,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,5,4,5,6,15,14,13,12,11,10,9,8,7,10,9,8,16,15,14,13,12,11,10,9,18,17,16,15,14,13,12,11,10,12,11,18,17,16,15,14,13,19,18,17,16,15,14,18,17,16,19,18,17,19,18]⟩,
  ⟨0,[1169,1542,6150,12609,16641],0,[3,2,1,0,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,16,15,14,13,12,11,10,9,8,7,6,5,9,8,7,6,16,15,14,13,12,11,10,9,8,7,16,15,14,13,12,11,10,9,8,10,9,12,11,10,16,15,14,13,12,11,14,15,16,17,18]⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem check1 : moves1.all valid=true := by decide +kernel
end FiveIso
end

section
namespace FiveIso
def moves2 : List Move := [
  ⟨0,[1169,4102,8449,17926,18721],1,[3,2,1,0,8,7,6,5,4,3,2,1,6,5,4,3,2,5,4,3,14,13,12,11,10,9,8,7,6,5,4,12,11,10,9,8,7,6,5,15,14,13,12,11,10,9,8,7,6,13,12,11,10,9,8,7,19,18,17,16,15,14,13,12,11,10,9,8,14,13,12,11,10,9,10,19,18,17,16,15,14,13,12,11,18,17,16,15,14,13,12,17,16,15,14,13,18,17,16,15,14,16,15,18,17,16,18,19]⟩,
  ⟨0,[1169,4102,8513,17926,18689],0,[11,10,9,8,7,6,5,4,3,2,1,0,10,9,8,7,6,5,4,3,2,1,3,2,8,7,6,5,4,3,16,15,14,13,12,11,10,9,8,7,6,5,4,14,13,12,11,10,9,8,7,6,5,19,18,17,16,15,14,13,12,11,10,9,8,7,6,7,8,16,15,14,13,12,11,10,9,18,17,16,15,14,13,12,11,10,13,12,11,13,12,18,17,16,15,14,13,14,18,17,19]⟩,
  ⟨0,[1170,1545,6153,8450,18722],1,[16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,4,3,2,1,11,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,16,15,14,13,12,11,10,9,8,7,6,5,4,16,15,14,13,12,11,10,9,8,7,6,11,10,9,8,7,9,8,16,15,14,13,12,11,10,9,16,15,14,13,12,11,10,13,12,11,12,15,14,15,18]⟩,
  ⟨0,[1170,1545,6153,8514,18690],0,[8,7,6,5,4,3,2,1,0,12,11,10,9,8,7,6,5,4,3,2,1,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,5,4,5,6,15,14,13,12,11,10,9,8,7,11,10,9,8,16,15,14,13,12,11,10,9,19,18,17,16,15,14,13,12,11,10,11,18,17,16,15,14,13,19,18,17,16,15,14,19,18,17,16,18,17,19,18]⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem check2 : moves2.all valid=true := by decide +kernel
end FiveIso
end

section
namespace FiveIso
def moves3 : List Move := [
  ⟨0,[1170,1545,6153,12546,16674],2,[8,7,6,5,4,3,2,1,0,12,11,10,9,8,7,6,5,4,3,2,1,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,5,4,5,6,15,14,13,12,11,10,9,8,7,11,10,9,8,16,15,14,13,12,11,10,9,18,17,16,15,14,13,12,11,10,12,11,18,17,16,15,14,13,19,18,17,16,15,14,18,17,16,19,18,17,19,18]⟩,
  ⟨0,[1170,1545,6153,12610,16642],0,[3,2,1,0,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,16,15,14,13,12,11,10,9,8,7,6,5,10,9,8,7,6,16,15,14,13,12,11,10,9,8,7,16,15,14,13,12,11,10,9,8,10,9,12,11,10,16,15,14,13,12,11,14,15,16,17,18]⟩,
  ⟨0,[1170,4105,8450,17929,18722],1,[3,2,1,0,7,6,5,4,3,2,1,7,6,5,4,3,2,5,4,3,14,13,12,11,10,9,8,7,6,5,4,12,11,10,9,8,7,6,5,15,14,13,12,11,10,9,8,7,6,13,12,11,10,9,8,7,19,18,17,16,15,14,13,12,11,10,9,8,14,13,12,11,10,9,10,19,18,17,16,15,14,13,12,11,18,17,16,15,14,13,12,17,16,15,14,13,18,17,16,15,14,16,15,18,17,16,18,19]⟩,
  ⟨0,[1170,4105,8514,17929,18690],0,[11,10,9,8,7,6,5,4,3,2,1,0,10,9,8,7,6,5,4,3,2,1,3,2,7,6,5,4,3,16,15,14,13,12,11,10,9,8,7,6,5,4,14,13,12,11,10,9,8,7,6,5,19,18,17,16,15,14,13,12,11,10,9,8,7,6,7,8,16,15,14,13,12,11,10,9,18,17,16,15,14,13,12,11,10,13,12,11,13,12,18,17,16,15,14,13,14,16,18,17,19]⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem check3 : moves3.all valid=true := by decide +kernel
end FiveIso
end

section
namespace FiveIso
def moves4 : List Move := [
  ⟨0,[1542,6150,8337,8961,18465],1,[16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,14,13,12,11,10,9,8,7,6,5,4,3,2,1,2,8,7,6,5,4,3,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,15,14,13,12,11,10,9,8,7,6,5,9,8,7,6,13,12,11,10,9,8,7,15,14,13,12,11,10,9,8,11,10,9,14,13,12,11,15,14,13,12,13,14,15,16,19]⟩,
  ⟨0,[1542,6150,8449,9361,18465],3,[7,6,5,4,3,2,1,0,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,4,3,12,11,10,9,8,7,6,5,4,15,14,13,12,11,10,9,8,7,6,5,13,12,11,10,9,8,7,6,16,15,14,13,12,11,10,9,8,7,14,13,12,11,10,9,8,19,18,17,16,15,14,13,12,11,10,9,12,11,10,17,16,15,14,13,12,11,17,16,15,14,13,12,18,17,16,15,14,13,19,18,17,16,15,14,16,15,16,19]⟩,
  ⟨0,[1542,6150,12353,16529,17153],1,[11,10,9,8,7,6,5,4,3,2,1,0,7,6,5,4,3,2,1,10,9,8,7,6,5,4,3,2,13,12,11,10,9,8,7,6,5,4,3,6,5,4,6,5,19,18,17,16,15,14,13,12,11,10,9,8,7,6,7,17,16,15,14,13,12,11,10,9,8,11,10,9,10,17,16,15,14,13,12,11,18,17,16,15,14,13,12,18,17,16,15,18,17,19]⟩,
  ⟨0,[1542,6150,12353,16641,17553],1,[7,6,5,4,3,2,1,0,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,13,12,11,10,9,8,7,6,5,4,3,2,14,13,12,11,10,9,8,7,6,5,4,3,5,4,6,5,6,19,18,17,16,15,14,13,12,11,10,9,8,7,10,9,8,18,17,16,15,14,13,12,11,10,9,17,16,15,14,13,12,11,10,11,19,18,17,16,15,14,13,19,18,17,16,15,14,19,18,17,16,18,17,19,18]⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem check4 : moves4.all valid=true := by decide +kernel
end FiveIso
end

section
namespace FiveIso
def moves5 : List Move := [
  ⟨0,[1545,6153,8338,8962,18466],1,[16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,14,13,12,11,10,9,8,7,6,5,4,3,2,1,2,7,6,5,4,3,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,15,14,13,12,11,10,9,8,7,6,5,9,8,7,6,13,12,11,10,9,8,7,15,14,13,12,11,10,9,8,11,10,9,13,12,11,15,14,13,12,13,14,15,16,19]⟩,
  ⟨0,[1545,6153,8450,9362,18466],3,[8,7,6,5,4,3,2,1,0,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,4,3,12,11,10,9,8,7,6,5,4,15,14,13,12,11,10,9,8,7,6,5,13,12,11,10,9,8,7,6,16,15,14,13,12,11,10,9,8,7,14,13,12,11,10,9,8,19,18,17,16,15,14,13,12,11,10,9,12,11,10,17,16,15,14,13,12,11,17,16,15,14,13,12,18,17,16,15,14,13,19,18,17,16,15,14,16,15,16,18,19]⟩,
  ⟨0,[1545,6153,12354,16530,17154],1,[11,10,9,8,7,6,5,4,3,2,1,0,6,5,4,3,2,1,10,9,8,7,6,5,4,3,2,13,12,11,10,9,8,7,6,5,4,3,6,5,4,6,5,19,18,17,16,15,14,13,12,11,10,9,8,7,6,7,17,16,15,14,13,12,11,10,9,8,11,10,9,10,17,16,15,14,13,12,11,18,17,16,15,14,13,12,18,17,16,15,16,18,17,19]⟩,
  ⟨0,[1545,6153,12354,16642,17554],1,[8,7,6,5,4,3,2,1,0,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,13,12,11,10,9,8,7,6,5,4,3,2,14,13,12,11,10,9,8,7,6,5,4,3,5,4,6,5,6,19,18,17,16,15,14,13,12,11,10,9,8,7,11,10,9,8,18,17,16,15,14,13,12,11,10,9,17,16,15,14,13,12,11,10,11,19,18,17,16,15,14,13,19,18,17,16,15,14,19,18,17,16,18,17,19,18]⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem check5 : moves5.all valid=true := by decide +kernel
end FiveIso
end

section
namespace FiveIso
def moves6 : List Move := [
  ⟨0,[4102,8337,8961,17926,18465],0,[14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,3,14,13,12,11,10,9,8,7,6,5,4,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,13,12,11,10,9,8,7,6,10,9,8,7,9,8,15,14,13,12,11,10,9,14,13,12,11,10,15,14,13,15,14,15,18,17,19,18]⟩,
  ⟨0,[4102,8449,9361,17926,18465],1,[7,6,5,4,3,2,1,0,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,3,12,11,10,9,8,7,6,5,4,15,14,13,12,11,10,9,8,7,6,5,13,12,11,10,9,8,7,6,16,15,14,13,12,11,10,9,8,7,14,13,12,11,10,9,8,19,18,17,16,15,14,13,12,11,10,9,12,11,10,17,16,15,14,13,12,11,17,16,15,14,13,12,18,17,16,15,14,13,19,18,17,16,15,14,15,16,17,19]⟩,
  ⟨0,[4105,8338,8962,17929,18466],0,[14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,7,6,5,4,3,2,3,14,13,12,11,10,9,8,7,6,5,4,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,13,12,11,10,9,8,7,6,10,9,8,7,9,8,15,14,13,12,11,10,9,13,12,11,10,15,14,13,15,14,15,18,17,19,18]⟩,
  ⟨0,[4105,8450,9362,17929,18466],1,[8,7,6,5,4,3,2,1,0,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,3,12,11,10,9,8,7,6,5,4,15,14,13,12,11,10,9,8,7,6,5,13,12,11,10,9,8,7,6,16,15,14,13,12,11,10,9,8,7,14,13,12,11,10,9,8,19,18,17,16,15,14,13,12,11,10,9,12,11,10,17,16,15,14,13,12,11,17,16,15,14,13,12,18,17,16,15,14,13,19,18,17,16,15,14,15,16,18,17,19]⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem check6 : moves6.all valid=true := by decide +kernel
end FiveIso
end

section
namespace FiveIso
def moves7 : List Move := [
  ⟨0,[4358,8337,8961,17414,18465],2,[7,6,5,4,3,2,1,0,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,16,15,14,13,12,11,10,9,8,7,6,5,4,3,12,11,10,9,8,7,6,5,4,5,13,12,11,10,9,8,7,6,7,13,12,11,10,9,8,10,9,19,18,17,16,15,14,13,12,11,10,16,15,14,13,12,11,16,15,14,13,12,19,18,17,16,15,14,13,19,18,17,16,15,14,19,18,17,16,15,19]⟩,
  ⟨0,[4361,8338,8962,17417,18466],2,[8,7,6,5,4,3,2,1,0,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,16,15,14,13,12,11,10,9,8,7,6,5,4,3,12,11,10,9,8,7,6,5,4,5,13,12,11,10,9,8,7,6,7,13,12,11,10,9,8,10,9,19,18,17,16,15,14,13,12,11,10,16,15,14,13,12,11,16,15,14,13,12,19,18,17,16,15,14,13,19,18,17,16,15,14,19,18,17,16,15,18,19]⟩,
  ⟨1,[1030,6406,12353,16529,17153],2,[1,0,5,4,3,2,1,10,9,8,7,6,5,4,3,2,9,8,7,6,5,4,3,17,16,15,14,13,12,11,10,9,8,7,6,5,4,8,7,6,5,17,16,15,14,13,12,11,10,9,8,7,6,9,8,7,15,14,13,12,11,10,9,8,10,9,18,17,16,15,14,13,12,11,10,14,13,12,11,17,16,15,14,13,12,19,18,17,16,15,14,13,17,16,15,14,18,17,16,15,17,16,18,17,19]⟩,
  ⟨1,[1169,1542,6150,8513,18689],2,[16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,4,3,2,1,11,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,16,15,14,13,12,11,10,9,8,7,6,5,4,16,15,14,13,12,11,10,9,8,7,6,10,9,8,7,9,8,16,15,14,13,12,11,10,9,16,15,14,13,12,11,10,14,13,12,11,12,15,14,15,18,17,16,17]⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem check7 : moves7.all valid=true := by decide +kernel
end FiveIso
end

section
namespace FiveIso
def moves8 : List Move := [
  ⟨1,[1169,1542,6150,12609,16641],2,[3,2,1,0,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,16,15,14,13,12,11,10,9,8,7,6,5,9,8,7,6,16,15,14,13,12,11,10,9,8,7,16,15,14,13,12,11,10,9,8,10,9,13,12,11,10,16,15,14,13,12,11,14,15,16,18,17,18]⟩,
  ⟨1,[1169,4102,8513,17926,18689],2,[3,2,1,0,5,4,3,2,1,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,15,14,13,12,11,10,9,8,7,6,5,4,8,7,6,5,15,14,13,12,11,10,9,8,7,6,9,8,7,19,18,17,16,15,14,13,12,11,10,9,8,9,13,12,11,10,19,18,17,16,15,14,13,12,11,18,17,16,15,14,13,12,18,17,16,15,14,13,18,17,16,15,14,18,17,16,15,18,17,16,18,17,19]⟩,
  ⟨1,[1542,6150,12353,16529,17153],2,[14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,4,3,2,1,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,17,16,15,14,13,12,11,10,9,8,7,6,5,4,17,16,15,14,13,12,11,10,9,8,7,6,10,9,8,7,19,18,17,16,15,14,13,12,11,10,9,15,14,13,12,11,10,13,12,11,19,18,17,16,15,14,15,16,17,19]⟩,
  ⟨1,[1542,6150,12353,16641,17553],2,[4,3,2,1,0,14,13,12,11,10,9,8,7,6,5,4,3,2,1,11,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,17,16,15,14,13,12,11,10,9,8,7,6,5,9,8,7,6,17,16,15,14,13,12,11,10,9,8,7,19,18,17,16,15,14,13,12,11,10,9,8,12,11,10,15,14,13,12,11,12,14,19,18,17,16,15,17,16,17,19,18]⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem check8 : moves8.all valid=true := by decide +kernel
end FiveIso
end

section
namespace FiveIso
def moves9 : List Move := [
  ⟨2,[777,1030,6406,8209,18481],0,[4,3,2,1,0,11,10,9,8,7,6,5,4,3,2,1,15,14,13,12,11,10,9,8,7,6,5,4,3,2,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,8,7,6,5,4,11,10,9,8,7,6,5,14,13,12,11,10,9,8,7,13,12,11,10,9,8,12,11,10,9,10,16,15,14,13,12,11,14,13,16,15,17,16,17,19,18]⟩,
  ⟨2,[777,1030,6406,8273,18449],0,[2,1,0,14,13,12,11,10,9,8,7,6,5,4,3,2,1,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,10,9,8,7,6,5,4,5,10,9,8,7,6,12,11,10,9,8,7,15,14,13,12,11,10,9,14,13,12,11,10,12,11,13,12,14,13,15,14,15,18,17,16,17,19,18]⟩,
  ⟨2,[777,1030,6406,12305,16433],2,[2,1,0,14,13,12,11,10,9,8,7,6,5,4,3,2,1,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,10,9,8,7,6,5,4,5,10,9,8,7,6,12,11,10,9,8,7,15,14,13,12,11,10,9,15,14,13,12,11,10,11,13,12,14,13,15,14,15,19,18,17,16,19,18,17,18]⟩,
  ⟨2,[777,1030,6406,12369,16401],1,[11,10,9,8,7,6,5,4,3,2,1,0,5,4,3,2,1,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,16,15,14,13,12,11,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,9,8,7,6,5,14,13,12,11,10,9,8,7,6,11,10,9,8,13,12,11,10,9,16,15,14,13,12,11,10,11,14,13,12,16,15,14,17,19,18]⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem check9 : moves9.all valid=true := by decide +kernel
end FiveIso
end

section
namespace FiveIso
def moves10 : List Move := [
  ⟨2,[777,1542,6150,8209,18481],0,[14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,3,2,1,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,4,10,9,8,7,6,5,12,11,10,9,8,7,6,11,10,9,8,7,15,14,13,12,11,10,9,8,10,15,14,13,12,11,14,13,12,14,13,14,15,18,17,16,19,18]⟩,
  ⟨2,[777,1542,6150,8273,18449],0,[11,10,9,8,7,6,5,4,3,2,1,0,5,4,3,2,1,15,14,13,12,11,10,9,8,7,6,5,4,3,2,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,9,8,7,6,5,14,13,12,11,10,9,8,7,6,11,10,9,8,13,12,11,10,9,15,14,13,12,11,10,12,11,14,13,12,16,15,14,17,16,19,18]⟩,
  ⟨2,[777,1542,6150,12305,16433],2,[14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,3,2,1,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,4,10,9,8,7,6,5,12,11,10,9,8,7,6,11,10,9,8,7,15,14,13,12,11,10,9,8,10,15,14,13,12,11,14,13,12,14,13,14,15,18,17,16,19,18,17]⟩,
  ⟨2,[777,1542,6150,12369,16401],1,[3,2,1,0,10,9,8,7,6,5,4,3,2,1,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,16,15,14,13,12,11,10,9,8,7,6,5,4,3,8,7,6,5,4,11,10,9,8,7,6,5,14,13,12,11,10,9,8,7,13,12,11,10,9,8,12,11,10,9,11,10,15,14,13,12,11,14,13,16,15,16,17,18]⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem check10 : moves10.all valid=true := by decide +kernel
end FiveIso
end

section
namespace FiveIso
def moves11 : List Move := [
  ⟨2,[777,4102,8209,17926,18481],1,[3,2,1,0,13,12,11,10,9,8,7,6,5,4,3,2,1,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,10,9,8,7,6,5,4,5,10,9,8,7,6,12,11,10,9,8,7,15,14,13,12,11,10,9,15,14,13,12,11,10,11,13,12,14,13,15,14,15,16,19,18,17,18]⟩,
  ⟨2,[777,4102,8273,17926,18449],1,[14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,2,1,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,4,10,9,8,7,6,5,12,11,10,9,8,7,6,11,10,9,8,7,15,14,13,12,11,10,9,8,11,10,14,13,12,11,14,13,12,14,13,15,18,17,19,18]⟩,
  ⟨2,[777,4358,8209,17414,18481],2,[4,3,2,1,0,11,10,9,8,7,6,5,4,3,2,1,15,14,13,12,11,10,9,8,7,6,5,4,3,2,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,8,7,6,5,4,11,10,9,8,7,6,5,14,13,12,11,10,9,8,7,13,12,11,10,9,8,12,11,10,9,12,11,10,16,15,14,13,12,11,14,13,16,15,17,16,19,18,17,18]⟩,
  ⟨2,[777,4358,8273,17414,18449],2,[11,10,9,8,7,6,5,4,3,2,1,0,5,4,3,2,1,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,16,15,14,13,12,11,10,9,8,7,6,5,4,3,11,10,9,8,7,6,5,4,9,8,7,6,5,14,13,12,11,10,9,8,7,6,11,10,9,8,13,12,11,10,9,16,15,14,13,12,11,10,13,12,11,14,13,12,16,15,14,19,18,17,16,18,17]⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem check11 : moves11.all valid=true := by decide +kernel
end FiveIso
end

section
namespace FiveIso
def moves12 : List Move := [
  ⟨2,[1030,6406,8209,8969,18465],1,[1,0,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,15,14,13,12,11,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,10,9,8,7,6,19,18,17,16,15,14,13,12,11,10,9,8,7,14,13,12,11,10,9,15,14,13,12,11,10,11,13,12,15,14,13,15,14,15,18,17,16,17,19,18]⟩,
  ⟨2,[1030,6406,8337,8961,18465],1,[16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,1,14,13,12,11,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,7,6,5,4,9,8,7,6,5,18,17,16,15,14,13,12,11,10,9,8,7,6,11,10,9,8,7,14,13,12,11,10,9,8,11,10,13,12,11,14,13,12,14,13,14,15,19]⟩,
  ⟨2,[1030,6406,12353,16401,17161],3,[4,3,2,1,0,1,3,2,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,14,13,12,11,10,9,8,7,6,5,4,9,8,7,6,5,15,14,13,12,11,10,9,8,7,6,10,9,8,7,11,10,9,8,16,15,14,13,12,11,10,9,18,17,16,15,14,13,12,11,10,15,14,13,12,11,17,16,15,14,13,12,13,18,17,16,15,14,18,17,16,15,17,19,18,19]⟩,
  ⟨2,[1030,6406,12353,16529,17153],1,[11,10,9,8,7,6,5,4,3,2,1,0,10,9,8,7,6,5,4,3,2,1,9,8,7,6,5,4,3,2,3,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,15,14,13,12,11,10,9,8,7,6,5,7,6,15,14,13,12,11,10,9,8,7,17,16,15,14,13,12,11,10,9,8,10,9,12,11,10,17,16,15,14,13,12,11,18,17,16,15,14,13,12,14,13,18,17,16,19]⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem check12 : moves12.all valid=true := by decide +kernel
end FiveIso
end

section
namespace FiveIso
def moves13 : List Move := [
  ⟨2,[1169,1542,6150,8449,18721],1,[4,3,2,1,0,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,12,11,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,16,15,14,13,12,11,10,9,8,7,6,5,9,8,7,6,16,15,14,13,12,11,10,9,8,7,16,15,14,13,12,11,10,9,8,10,9,12,11,10,14,13,12,11,14,16,15,17,16,17,19,18]⟩,
  ⟨2,[1169,1542,6150,8513,18689],0,[16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,4,3,2,1,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,16,15,14,13,12,11,10,9,8,7,6,5,4,16,15,14,13,12,11,10,9,8,7,6,10,9,8,7,9,8,16,15,14,13,12,11,10,9,14,13,12,11,10,13,12,11,12,16,15,14,15,16,18]⟩,
  ⟨2,[1169,1542,6150,12545,16673],2,[12,11,10,9,8,7,6,5,4,3,2,1,0,7,6,5,4,3,2,1,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,4,5,15,14,13,12,11,10,9,8,7,6,7,16,15,14,13,12,11,10,9,8,11,10,9,11,10,18,17,16,15,14,13,12,11,18,17,16,15,14,13,12,19,18,17,16,15,19,18,17,16,19,18,17,19]⟩,
  ⟨2,[1169,1542,6150,12609,16641],0,[12,11,10,9,8,7,6,5,4,3,2,1,0,7,6,5,4,3,2,1,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,4,5,15,14,13,12,11,10,9,8,7,6,7,16,15,14,13,12,11,10,9,8,11,10,9,11,10,18,17,16,15,14,13,12,11,18,17,16,15,14,13,12,19,18,17,16,15,19,18,17,16,19,18,19]⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem check13 : moves13.all valid=true := by decide +kernel
end FiveIso
end

section
namespace FiveIso
def moves14 : List Move := [
  ⟨2,[1169,4102,8449,17926,18721],3,[4,3,2,1,0,2,1,2,9,8,7,6,5,4,3,19,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,8,7,6,5,17,16,15,14,13,12,11,10,9,8,7,6,10,9,8,7,12,11,10,9,8,18,17,16,15,14,13,12,11,10,9,18,17,16,15,14,13,12,11,10,14,13,12,11,15,14,13,12,14,13,18,17,16,15,14,17,16,15,17,18,19]⟩,
  ⟨2,[1169,4102,8513,17926,18689],1,[12,11,10,9,8,7,6,5,4,3,2,1,0,18,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,8,7,6,5,4,3,2,4,3,14,13,12,11,10,9,8,7,6,5,4,17,16,15,14,13,12,11,10,9,8,7,6,5,6,19,18,17,16,15,14,13,12,11,10,9,8,7,17,16,15,14,13,12,11,10,9,8,9,12,11,10,19,18,17,16,15,14,13,12,11,19,18,17,16,15,14,13,12,14,13,19,18,17,16,19,18,19]⟩,
  ⟨2,[1542,6150,8209,8969,18465],0,[16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,14,13,12,11,10,9,8,7,6,5,4,3,7,6,5,4,9,8,7,6,5,18,17,16,15,14,13,12,11,10,9,8,7,6,11,10,9,8,7,14,13,12,11,10,9,8,10,15,14,13,12,11,15,14,13,12,14,13,14,15,16,19]⟩,
  ⟨2,[1542,6150,8337,8961,18465],0,[12,11,10,9,8,7,6,5,4,3,2,1,0,4,3,2,1,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,16,15,14,13,12,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,9,8,7,6,5,14,13,12,11,10,9,8,7,6,12,11,10,9,8,18,17,16,15,14,13,12,11,10,9,19,18,17,16,15,14,13,12,11,10,14,13,12,14,13,19,18,17,16,15,14,19,18,17,16,19,18]⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem check14 : moves14.all valid=true := by decide +kernel
end FiveIso
end

section
namespace FiveIso
def moves15 : List Move := [
  ⟨2,[1542,6150,8449,9361,18465],1,[3,2,1,0,8,7,6,5,4,3,2,1,14,13,12,11,10,9,8,7,6,5,4,3,2,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,8,7,6,5,4,12,11,10,9,8,7,6,5,13,12,11,10,9,8,7,18,17,16,15,14,13,12,11,10,9,8,13,12,11,10,9,19,18,17,16,15,14,13,12,11,13,12,14,13,19,18,17,16,15,17,16,19,18,17,18]⟩,
  ⟨2,[1542,6150,8457,9233,18465],2,[16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,1,10,9,8,7,6,5,4,3,2,14,13,12,11,10,9,8,7,6,5,4,3,7,6,5,4,9,8,7,6,5,18,17,16,15,14,13,12,11,10,9,8,7,6,11,10,9,8,7,14,13,12,11,10,9,8,11,10,15,14,13,12,11,15,14,13,12,14,13,14,15,16,17,19]⟩,
  ⟨2,[1542,6150,12353,16401,17161],1,[4,3,2,1,0,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,13,12,11,10,9,8,7,6,5,4,3,2,12,11,10,9,8,7,6,5,4,3,17,16,15,14,13,12,11,10,9,8,7,6,5,9,8,7,6,17,16,15,14,13,12,11,10,9,8,7,19,18,17,16,15,14,13,12,11,10,9,8,13,12,11,10,19,18,17,16,15,14,13,12,11,12,14,17,16,15,19,18,17,16,17,19,18]⟩,
  ⟨2,[1542,6150,12353,16529,17153],0,[14,13,12,11,10,9,8,7,6,5,4,3,2,1,0,4,3,2,1,11,10,9,8,7,6,5,4,3,2,10,9,8,7,6,5,4,3,17,16,15,14,13,12,11,10,9,8,7,6,5,4,17,16,15,14,13,12,11,10,9,8,7,6,10,9,8,7,19,18,17,16,15,14,13,12,11,10,9,19,18,17,16,15,14,13,12,11,10,14,13,12,11,16,15,14,15,17,16,19]⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem check15 : moves15.all valid=true := by decide +kernel
end FiveIso
end

section
namespace FiveIso
def moves16 : List Move := [
  ⟨2,[1542,6150,12353,16641,17553],0,[11,10,9,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,13,12,11,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,6,5,4,6,5,19,18,17,16,15,14,13,12,11,10,9,8,7,6,7,17,16,15,14,13,12,11,10,9,8,11,10,9,10,16,15,14,13,12,11,18,17,16,15,14,13,12,18,17,16,15,18,17,16,19]⟩,
  ⟨2,[1542,6150,12353,16649,17425],2,[11,10,9,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,2,1,13,12,11,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,6,5,4,6,5,19,18,17,16,15,14,13,12,11,10,9,8,7,6,7,17,16,15,14,13,12,11,10,9,8,11,10,9,10,16,15,14,13,12,11,18,17,16,15,14,13,12,18,17,16,15,18,17,16,17,19]⟩,
  ⟨2,[4102,8209,8969,17926,18465],0,[2,1,0,12,11,10,9,8,7,6,5,4,3,2,1,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,16,15,14,13,12,11,10,9,8,7,6,5,4,3,8,7,6,5,4,13,12,11,10,9,8,7,6,5,14,13,12,11,10,9,8,7,18,17,16,15,14,13,12,11,10,9,8,13,12,11,10,9,18,17,16,15,14,13,12,11,13,12,14,13,14,19,18,17,16,15,19,18,17,16,17,19,18]⟩,
  ⟨2,[4102,8337,8961,17926,18465],0,[3,2,1,0,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,10,9,8,7,6,5,4,3,2,14,13,12,11,10,9,8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,10,9,8,7,6,18,17,16,15,14,13,12,11,10,9,8,7,14,13,12,11,10,9,13,12,11,10,12,11,13,12,14,13,15,14,15,16,19,18,17,18]⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem check16 : moves16.all valid=true := by decide +kernel
end FiveIso
end

section
namespace FiveIso
def moves17 : List Move := [
  ⟨2,[4102,8449,9361,17926,18465],1,[12,11,10,9,8,7,6,5,4,3,2,1,0,2,1,15,14,13,12,11,10,9,8,7,6,5,4,3,2,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,9,8,7,6,5,14,13,12,11,10,9,8,7,6,12,11,10,9,8,18,17,16,15,14,13,12,11,10,9,18,17,16,15,14,13,12,11,10,14,13,12,14,13,19,18,17,16,15,14,15,19,18,17,19,18]⟩,
  ⟨2,[4102,8457,9233,17926,18465],2,[3,2,1,0,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,14,13,12,11,10,9,8,7,6,5,4,3,2,11,10,9,8,7,6,5,4,3,9,8,7,6,5,4,8,7,6,5,10,9,8,7,6,18,17,16,15,14,13,12,11,10,9,8,7,14,13,12,11,10,9,15,14,13,12,11,10,12,11,13,12,15,14,13,15,14,15,17,16,17,19,18]⟩,
  ⟨2,[4358,8209,8969,17414,18465],2,[2,1,0,12,11,10,9,8,7,6,5,4,3,2,1,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,2,16,15,14,13,12,11,10,9,8,7,6,5,4,3,8,7,6,5,4,13,12,11,10,9,8,7,6,5,14,13,12,11,10,9,8,7,18,17,16,15,14,13,12,11,10,9,8,13,12,11,10,9,18,17,16,15,14,13,12,11,13,12,14,13,14,19,18,17,16,15,19,18,17,16,19,18,17,18]⟩,
  ⟨2,[4358,8337,8961,17414,18465],2,[12,11,10,9,8,7,6,5,4,3,2,1,0,3,2,1,15,14,13,12,11,10,9,8,7,6,5,4,3,2,17,16,15,14,13,12,11,10,9,8,7,6,5,4,3,13,12,11,10,9,8,7,6,5,4,9,8,7,6,5,14,13,12,11,10,9,8,7,6,12,11,10,9,8,18,17,16,15,14,13,12,11,10,9,18,17,16,15,14,13,12,11,10,14,13,12,14,13,19,18,17,16,15,14,15,18,17,16,19,18,17]⟩]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem check17 : moves17.all valid=true := by decide +kernel
end FiveIso
end

section
namespace FiveIso
def moves := moves0 ++ moves1 ++ moves2 ++ moves3 ++ moves4 ++ moves5 ++ moves6 ++ moves7 ++ moves8 ++ moves9 ++ moves10 ++ moves11 ++ moves12 ++ moves13 ++ moves14 ++ moves15 ++ moves16 ++ moves17
private theorem combine {a b : List Move} (ha : a.all valid=true) (hb : b.all valid=true) :
    (a++b).all valid=true := by rw [List.all_append,ha,hb]; rfl

theorem checks : moves.all valid=true := (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine (combine check0 check1) check2) check3) check4) check5) check6) check7) check8) check9) check10) check11) check12) check13) check14) check15) check16) check17)

set_option maxRecDepth 30000 in
theorem complete : ∀ i : Fin 8, (outputs i).all (fun cs => decide ((i.val,cs)∈moves.map key))=true := by
  decide +kernel

theorem relabel_output (i : Fin 8) (cs : List Nat) (hc : cs∈outputs i) :
    ∃ (j : Fin 4) (steps : List Nat), FP32.relabel steps (FP32.attach cs (SparseFifteen.adj i))=target j := by
  have covered := of_decide_eq_true (List.all_eq_true.mp (complete i) cs hc)
  obtain ⟨m,hm,eq⟩ := List.mem_map.mp covered
  have left : m.base=i := Fin.ext (congrArg Prod.fst eq)
  have right : m.contacts=cs := congrArg Prod.snd eq
  have yes := beq_iff_eq.mp (List.all_eq_true.mp checks m hm)
  change FP32.relabel m.steps (FP32.attach m.contacts (SparseFifteen.adj m.base))=target m.rep at yes
  exact ⟨m.rep,m.steps,by simpa only [left,right] using yes⟩
end FiveIso
end

section
/- Relabeling certificates for the five-neighbour extensions of sparse
fifteen-vertex Ramsey graphs attaining 51 edges on 21 vertices. -/
namespace FiveIso
open SimpleGraph Finset

theorem target_public (j : Fin 4) : target j=GlueSeed.adj j := by
  fin_cases j <;> rfl

theorem terminal (i : Fin 8) (cs : List ℕ) (hc : cs∈outputs i)
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (vs : List V) (nd : vs.Nodup) (allv : vs.toFinset=univ)
    (code : OMA.RamseyFinite.encode G vs = OMA.RamseyFinite.attach cs (SparseFifteen.adj i)) :
    ∃ (j : Fin 4) (ws : List V), ws.Nodup ∧ ws.toFinset=univ ∧ GlueSeed.encode G ws = GlueSeed.adj j := by
  obtain ⟨j,steps,classified⟩ := relabel_output i cs hc
  obtain ⟨ws,perm,eq⟩ := OMA.RamseyFinite.relabel_real G steps vs
  refine ⟨j,ws,perm.nodup_iff.mpr nd,?_,?_⟩
  · rw [←allv]
    ext v
    exact List.mem_toFinset.trans (perm.mem_iff.trans List.mem_toFinset.symm)
  · rw [←Sparse32.encode_glue,eq,code,Sparse32.toPure_relabel,Sparse32.toPure_attach,classified,target_public]
end FiveIso
end

section
/- Non-neighborhood deficiency for triangle-free Ramsey graphs. -/
open SimpleGraph Finset
namespace OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1_H2_R1

lemma lift_card {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (hi : Gᶜ.CliqueFree 8) (S : Finset (Gᶜ.neighborFinset v))
    (cl : ((G.induce ((Gᶜ.neighborFinset v : Finset V) : Set V))ᶜ).IsClique S) :
    S.card ≤ 6 := by
  classical
  let B := Gᶜ.neighborFinset v
  let f : B ↪ V := Function.Embedding.subtype _
  have free : Gᶜ.IsClique (S.map f) := by
    intro x hx y hy hxy
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
    exact ⟨hxy,(cl ha hb (fun h => hxy (congrArg f h))).2⟩
  have hv : v ∉ S.map f := by
    intro hm
    obtain ⟨b,_,eq⟩ := mem_map.mp hm
    exact ((Gᶜ.mem_neighborFinset _ _).mp b.2).ne eq.symm
  have ext : Gᶜ.IsClique (insert v (S.map f)) := free.insert (by
    intro b hb _
    obtain ⟨i,_,rfl⟩ := mem_map.mp hb
    exact (Gᶜ.mem_neighborFinset _ _).mp i.2)
  have lim : (insert v (S.map f)).card < 8 := lt_of_not_ge (fun h =>
    hi.mono h _ ⟨by simpa only [Finset.coe_insert] using ext,rfl⟩)
  rw [card_insert_of_notMem hv,card_map] at lim
  omega

theorem neighborhood_data {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 8) :
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    let D := G.induce (B : Set V)
    let A (i : N) := (univ : Finset B).filter fun x => G.Adj i.val x.val
    D.CliqueFree 3 ∧ Dᶜ.CliqueFree 7 ∧
      (∀ i, Dᶜ.IsClique (A i)) ∧
      (∀ (J : Finset N) (S : Finset B), Dᶜ.IsClique S → (∀ a ∈ J, Disjoint (A a) S) → J.card+S.card≤7) ∧
      N.card + (∑ a, (A a).card) ≤ ∑ a ∈ N, G.degree a := by
  classical
  let N := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  let D := G.induce (B : Set V)
  let A (i : N) := (univ : Finset B).filter fun x => G.Adj i.val x.val
  let f : B ↪ V := Function.Embedding.subtype _
  let g : N ↪ V := Function.Embedding.subtype _
  let em : D ↪g G := SimpleGraph.Embedding.comap f G
  have nd (a : N) := (G.mem_neighborFinset v a.val).mp a.2
  have bd (a : B) := (Gᶜ.mem_neighborFinset v a.val).mp a.2
  have split (a : N) (b : B) : a.val≠b.val := fun eq => (bd b).2 (eq ▸ nd a)
  have nr (a b : N) : ¬G.Adj a.val b.val := by
    intro h
    exact G.isIndepSet_neighborSet_of_triangleFree ht v (nd a) (nd b) h.ne h
  change D.CliqueFree 3 ∧ Dᶜ.CliqueFree 7 ∧ (∀ i, Dᶜ.IsClique (A i)) ∧ _ ∧ _
  refine ⟨CliqueFree.comap em.isContained ht,?_,?_,?_,?_⟩
  · intro S hS
    have h := lift_card G v hi S hS.isClique
    have eq := hS.card_eq
    omega
  · intro i a ha b hb hne
    refine ⟨hne,?_⟩
    intro h
    exact G.isIndepSet_neighborSet_of_triangleFree ht i.val (mem_filter.mp ha).2 (mem_filter.mp hb).2
      (Subtype.val_injective.ne hne) h
  · intro J S cl dis
    let X := J.map g
    let Y := S.map f
    have apart : Disjoint X Y := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨a,_,rfl⟩ := mem_map.mp hx
      obtain ⟨b,_,eq⟩ := mem_map.mp hy
      exact split a b eq.symm
    have sx : Gᶜ.IsClique X := by
      intro u hu w hw hne
      obtain ⟨a,_,rfl⟩ := mem_map.mp hu
      obtain ⟨b,_,rfl⟩ := mem_map.mp hw
      exact ⟨hne,nr a b⟩
    have sy : Gᶜ.IsClique Y := by
      intro u hu w hw hne
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hu
      obtain ⟨b,hb,rfl⟩ := mem_map.mp hw
      exact ⟨hne,(cl ha hb (fun h => hne (congrArg f h))).2⟩
    have cross (u : V) (hu : u∈X) (w : V) (hw : w∈Y) : Gᶜ.Adj u w := by
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hu
      obtain ⟨b,hb,rfl⟩ := mem_map.mp hw
      exact ⟨split a b,fun h => Finset.disjoint_left.mp (dis a ha) (mem_filter.mpr ⟨mem_univ _,h⟩) hb⟩
    have full : Gᶜ.IsClique (X ∪ Y) := by
      intro u hu w hw hne
      rcases hu with hu|hu <;> rcases hw with hw|hw
      · exact sx hu hw hne
      · exact cross _ hu _ hw
      · exact (cross _ hw _ hu).symm
      · exact sy hu hw hne
    have lim : (X ∪ Y).card < 8 := lt_of_not_ge (fun h =>
      hi.mono h _ ⟨by simpa only [Finset.coe_union] using full,rfl⟩)
    rw [card_union_of_disjoint apart,card_map,card_map] at lim
    omega
  · have each (a : N) : 1 + (A a).card ≤ G.degree a.val := by
      let Y := (A a).map f
      have nv : v ∉ Y := by
        rintro mem
        obtain ⟨b,_,eq⟩ := mem_map.mp mem
        exact (bd b).1 eq.symm
      have sub : insert v Y ⊆ G.neighborFinset a.val := by
        intro w hw
        rcases mem_insert.mp hw with rfl|mem
        · exact (G.mem_neighborFinset _ _).mpr (nd a).symm
        · obtain ⟨b,hb,rfl⟩ := mem_map.mp mem
          exact (G.mem_neighborFinset _ _).mpr (mem_filter.mp hb).2
      have le := card_le_card sub
      rw [card_insert_of_notMem nv,card_map,G.card_neighborFinset_eq_degree] at le
      omega
    have total := Finset.sum_le_sum (s := (univ : Finset N)) (fun a _ => each a)
    change N.card + (∑ a : N,(A a).card) ≤ ∑ a ∈ N,G.degree a
    rw [← Finset.sum_coe_sort N (fun i => G.degree i)]
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.mul_one,
      Fintype.card_coe,Nat.cast_id] using total


theorem removed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ht : G.CliqueFree 3) (v : Fin n) :
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    let D := G.induce (B : Set (Fin n))
    D.edgeFinset.card+(∑ i ∈ N, G.degree i) ≤ G.edgeFinset.card := by
  let N := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  let D := G.induce (B : Set (Fin n))
  let U : Finset (Fin n) := univ
  let W (X Y : Finset (Fin n)) := ∑ i ∈ X, ∑ j ∈ Y, (if G.Adj i j then 1 else 0 : ℕ)
  have flip (X Y) : W X Y = W Y X := by
    unfold W
    rw [Finset.sum_comm]
    simp only [G.adj_comm]
  have partition (X Y) : W X Y + W Xᶜ Y = W U Y := Finset.sum_add_sum_compl X _
  have total (X) : W X U=∑ i ∈ X, G.degree i := by
    simp [W,U,SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter]
  have vanish : W N N=0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    have un : ¬G.Adj a b := fun adj => G.isIndepSet_neighborSet_of_triangleFree ht v
      ((G.mem_neighborFinset _ _).mp ha) ((G.mem_neighborFinset _ _).mp hb) adj.ne adj
    simp [un]
  have inside : B ⊆ Nᶜ := fun i hi => Finset.mem_compl.mpr fun h =>
    ((Gᶜ.mem_neighborFinset _ _).mp hi).2 ((G.mem_neighborFinset _ _).mp h)
  have inc (X Y Z : Finset (Fin n)) (sub : X ⊆ Y) : W X Z ≤ W Y Z :=
    Finset.sum_le_sum_of_subset_of_nonneg sub (by intros; omega)
  have le : W B B ≤ W Nᶜ Nᶜ :=
    (inc B Nᶜ B inside).trans ((flip Nᶜ B) ▸ inc B Nᶜ Nᶜ inside)
  have db : W B B = 2*D.edgeFinset.card := by
    calc
      W B B = ∑ i : B, ∑ j ∈ B, (if G.Adj i.val j then 1 else 0 : ℕ) :=
        (Finset.sum_coe_sort B _).symm
      _ = ∑ i : B, ∑ j : B, (if D.Adj i j then 1 else 0 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (Finset.sum_coe_sort B (fun j => if G.Adj i.val j then 1 else 0)).symm
      _ = ∑ i : B, D.degree i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter]
        exact Finset.sum_boole (R:=ℕ) (D.Adj i) univ
      _ = _ := D.sum_degrees_eq_twice_card_edges
  have p1 := partition N U
  have p2 := partition N N
  have p3 := partition N Nᶜ
  have f1 := flip Nᶜ U
  have f2 := flip N U
  have f3 := flip Nᶜ N
  have a := total N
  have b := total U
  have all : (∑ i ∈ U,G.degree i) = 2*G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  change D.edgeFinset.card+(∑ i ∈ N,G.degree i)≤ G.edgeFinset.card
  omega

theorem sum_neighbor_degrees {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∑ v, ∑ w ∈ G.neighborFinset v, G.degree w) = ∑ v, G.degree v ^ 2 := by
  simp only [SimpleGraph.neighborFinset_eq_filter,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  calc
    (∑ v, if G.Adj v w then G.degree w else 0) =
        ∑ v ∈ univ.filter (G.Adj w), G.degree w := by
          rw [Finset.sum_filter]
          simp only [G.adj_comm]
    _ = G.degree w^2 := by
      rw [← G.neighborFinset_eq_filter,Finset.sum_const,G.card_neighborFinset_eq_degree,nsmul_eq_mul,pow_two]
      norm_cast


/-- The smaller 22-vertex (3,7) density estimate, weakened by one edge. -/
def H1 : Prop := ∀ (G : SimpleGraph (Fin 22)) [DecidableRel G.Adj],
  G.CliqueFree 3 → Gᶜ.CliqueFree 7 → 59 ≤ G.edgeFinset.card


end OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1_H2_R1
end

section
/-
# The 22-vertex extremal edge bound e(3,7;22) >= 59

We prove that every triangle-free graph on 22 vertices without an independent set of size 7
has at least 59 edges, establishing `OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1_H2_R1.H1`.

The proof consists of three parts:
1. Small Ramsey numbers R(3,2) = 3, R(3,3) = 6, R(3,4) = 9, R(3,5) = 14, and R(3,6) = 18.
   The 5-regular case of R(3,6) adapts the canonical neighborhood proof of
   `RamseyNumbers.ramsey_number_three_six.R1.H2` by @MrSeizy and @michielkosters; the
   degree-4 case is excluded by a single uniform dual packing certificate on the unique
   (3,5)-graph on 13 vertices.
2. The 16-vertex extremal bound e(3,6;16) >= 32, proved by adapting the finite graph
   enumeration and dual packing framework of `RamseyNumbers.ramsey_number_three_seven.R1.H2.R1.H1`
   to orders 12 and 13 with 13 zero-branching dual certificates.
3. The Graver--Yackel averaging ladder from e(3,3;3..5) through e(3,4;4..8),
   e(3,5;9..13), e(3,6;15..17), and finally e(3,7;22) >= 59.
-/

namespace RamseySmallImported.Ramsey37Density

open RamseyNumbers SimpleGraph Finset
open OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1 (degree_lt nonneighbors_lt)

lemma three_works : IsGraphRamsey 3 3 2 := by
  classical
  rintro G ⟨hG, hc⟩
  apply hG Finset.univ
  refine ⟨?_, by simp⟩
  intro u _ v _ hne
  by_contra h
  apply hc {u, v}
  refine ⟨?_, Finset.card_pair hne⟩
  intro a ha b hb hab
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  refine ⟨hab, ?_⟩
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (hab rfl).elim
  · exact h
  · exact fun h' => h h'.symm
  · exact (hab rfl).elim

lemma six_works : IsGraphRamsey 6 3 3 := by
  classical
  rintro G ⟨hG, hc⟩
  have hd := degree_lt G hG hc 0
  have hdc := degree_lt Gᶜ hc (by simpa using hG : Gᶜᶜ.CliqueFree 3) 0
  rw [G.degree_compl, Fintype.card_fin] at hdc
  omega

lemma nine_works : IsGraphRamsey 9 3 4 := by
  classical
  rintro G ⟨hG, hc⟩
  have hdegree (v : Fin 9) : G.degree v = 3 := by
    have hd := degree_lt G hG hc v
    have hdc := nonneighbors_lt six_works G hG hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    omega
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp [hdegree] at hsum
  omega

lemma fourteen_works : IsGraphRamsey 14 3 5 := by
  classical
  rintro G ⟨hG, hc⟩
  have hd := degree_lt G hG hc 0
  have hdc := nonneighbors_lt nine_works G hG hc 0
  rw [G.degree_compl, Fintype.card_fin] at hdc
  omega

end RamseySmallImported.Ramsey37Density

section Ramsey36Regular
open SimpleGraph Finset

namespace RamseySmallImported.RamseyRegular

def mask : Fin 18 → Finset (Fin 18) :=
  ![∅, ∅, ∅, ∅, ∅, ∅, {1}, {2}, {3}, {4}, {1, 3}, {1, 4}, {1, 5},
    {2, 3}, {2, 4}, {2, 5}, {3, 5}, {4, 5}]

private def blocked (i j : Fin 18) : Bool :=
  decide ((1 ≤ i.val ∧ i.val < 6 ∧ 1 ≤ j.val ∧ j.val < 6) ∨
    (1 ≤ i.val ∧ i.val < 6 ∧ 6 ≤ j.val ∧ i ∉ mask j) ∨
    (∃ k : Fin 18, 1 ≤ k.val ∧ k.val < 6 ∧ k ∈ mask i ∧ k ∈ mask j ∧ 6 ≤ i.val ∧ 6 ≤ j.val))

private theorem edge_in_six {V : Type*} (G : SimpleGraph V) (hc : Gᶜ.CliqueFree 6)
    (f : Fin 18 ↪ V) (s : Finset (Fin 18)) (hs : s.card = 6) :
    ∃ i ∈ s, ∃ j ∈ s, i < j ∧ G.Adj (f i) (f j) := by
  classical
  by_contra! hn
  apply hc (s.map f)
  refine ⟨?_, (card_map ..).trans hs⟩
  intro x hx y hy hne
  obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
  obtain ⟨j, hj, rfl⟩ := mem_map.mp hy
  refine ⟨hne, ?_⟩
  rcases lt_or_gt_of_ne (fun h => hne (congrArg f h)) with h | h
  · exact hn i hi j hj h
  · exact fun ha => hn j hj i hi h ha.symm

theorem canonical_impossible {V : Type*} (G : SimpleGraph V)
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6) (f : Fin 18 ↪ V)
    (ha : ∀ i j : Fin 18, 1 ≤ i.val → i.val < 6 → 1 ≤ j.val → j.val < 6 →
      ¬ G.Adj (f i) (f j))
    (hab : ∀ i j : Fin 18, 1 ≤ i.val → i.val < 6 → 6 ≤ j.val →
      (G.Adj (f i) (f j) ↔ i ∈ mask j)) : False := by
  classical
  have impossible (i j : Fin 18) (h : blocked i j) : ¬ G.Adj (f i) (f j) := by
    simp only [blocked, decide_eq_true_eq] at h
    rcases h with ⟨hi, hi', hj, hj'⟩ | ⟨hi, hi', hj, hm⟩ | ⟨k, hk, hk', hki, hkj, hi, hj⟩
    · exact ha i j hi hi' hj hj'
    · exact fun hadj => hm ((hab i j hi hi' hj).mp hadj)
    · intro hadj
      exact (G.isIndepSet_neighborSet_of_triangleFree ht (f k))
        ((hab k i hk hk' hi).mpr hki) ((hab k j hk hk' hj).mpr hkj) hadj.ne hadj
  have forced (s : Finset (Fin 18)) (a b : Fin 18) (hs : s.card = 6)
      (only : ∀ i ∈ s, ∀ j ∈ s, i < j → blocked i j ∨ (i = a ∧ j = b)) :
      G.Adj (f a) (f b) := by
    obtain ⟨i, hi, j, hj, hij, he⟩ := edge_in_six G hc f s hs
    rcases only i hi j hj hij with hn | ⟨rfl, rfl⟩
    · exact (impossible i j hn he).elim
    · exact he
  have e78 := forced {1,4,5,7,8,13} 7 8 (by decide +kernel) (by decide +kernel)
  have e79 := forced {1,3,5,7,9,14} 7 9 (by decide +kernel) (by decide +kernel)
  have e716 := forced {1,4,7,13,15,16} 7 16 (by decide +kernel) (by decide +kernel)
  have e717 := forced {1,3,7,14,15,17} 7 17 (by decide +kernel) (by decide +kernel)
  let neighbors : Finset (Fin 18) := {8,9,16,17}
  have adjacent (i : Fin 18) (hi : i ∈ neighbors) : G.Adj (f 7) (f i) := by
    simp only [neighbors, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> assumption
  let six : Finset (Fin 18) := {1,2,8,9,16,17}
  have cases : ∀ i ∈ six, ∀ j ∈ six, i < j → blocked i j ∨
      (i ∈ neighbors ∧ j ∈ neighbors) := by decide +kernel
  obtain ⟨i, hi, j, hj, hij, he⟩ := edge_in_six G hc f six (by decide +kernel)
  rcases cases i hi j hj hij with hn | ⟨hni, hnj⟩
  · exact impossible i j hn he
  · exact (G.isIndepSet_neighborSet_of_triangleFree ht (f 7))
      (adjacent i hni) (adjacent j hnj) he.ne he

end RamseySmallImported.RamseyRegular

namespace RamseySmallImported.RamseyRegular

def shape : Fin 15 → Finset (Fin 5) :=
  ![{0}, {1}, {2}, {3}, {4}, {0, 1}, {0, 2}, {0, 3}, {0, 4}, {1, 2}, {1, 3}, {1, 4}, {2, 3}, {2, 4}, {3, 4}]

def template : Fin 12 → Finset (Fin 5) :=
  ![{0}, {1}, {2}, {3}, {0, 2}, {0, 3}, {0, 4}, {1, 2}, {1, 3}, {1, 4}, {2, 4}, {3, 4}]

def permRow : Fin 15 → Fin 5 → Fin 5 :=
  ![![1, 2, 3, 4, 0],
    ![1, 3, 2, 4, 0],
    ![1, 4, 2, 3, 0],
    ![0, 2, 3, 4, 1],
    ![0, 3, 2, 4, 1],
    ![0, 4, 2, 3, 1],
    ![0, 1, 3, 4, 2],
    ![0, 3, 1, 4, 2],
    ![0, 4, 1, 3, 2],
    ![0, 1, 2, 4, 3],
    ![0, 2, 1, 4, 3],
    ![0, 4, 1, 2, 3],
    ![0, 1, 2, 3, 4],
    ![0, 2, 1, 3, 4],
    ![0, 3, 1, 2, 4]]

def imageIndex : Fin 15 → Fin 12 → Fin 15 :=
  ![![1, 2, 3, 4, 10, 11, 5, 12, 13, 6, 7, 8],
    ![1, 3, 2, 4, 9, 11, 5, 12, 14, 7, 6, 8],
    ![1, 4, 2, 3, 9, 10, 5, 13, 14, 8, 6, 7],
    ![0, 2, 3, 4, 7, 8, 5, 12, 13, 9, 10, 11],
    ![0, 3, 2, 4, 6, 8, 5, 12, 14, 10, 9, 11],
    ![0, 4, 2, 3, 6, 7, 5, 13, 14, 11, 9, 10],
    ![0, 1, 3, 4, 7, 8, 6, 10, 11, 9, 12, 13],
    ![0, 3, 1, 4, 5, 8, 6, 10, 14, 12, 9, 13],
    ![0, 4, 1, 3, 5, 7, 6, 11, 14, 13, 9, 12],
    ![0, 1, 2, 4, 6, 8, 7, 9, 11, 10, 12, 14],
    ![0, 2, 1, 4, 5, 8, 7, 9, 13, 12, 10, 14],
    ![0, 4, 1, 2, 5, 6, 7, 11, 13, 14, 10, 12],
    ![0, 1, 2, 3, 6, 7, 8, 9, 10, 11, 13, 14],
    ![0, 2, 1, 3, 5, 7, 8, 9, 12, 13, 11, 14],
    ![0, 3, 1, 2, 5, 6, 8, 10, 12, 14, 11, 13]]

private theorem row_injective (r : Fin 15) : Function.Injective (permRow r) := by
  exact (show ∀ d i j, permRow d i = permRow d j → i = j by decide +kernel) r

def patternPerm (r : Fin 15) : Fin 5 ↪ Fin 5 :=
  ⟨permRow r, row_injective r⟩

private theorem image_correct : ∀ (r : Fin 15) (j : Fin 12),
    shape (imageIndex r j) = (template j).map (patternPerm r) := by decide +kernel

private def Covers (a b c : Fin 15) : Prop :=
  let T := ({a,b,c} : Finset (Fin 15))ᶜ
  (∀ x : Fin 5, (T.filter (fun i => x ∈ shape i)).card = 4) →
  ∃ r : Fin 15, ∀ t : Fin 12, imageIndex r t ∈ T

private instance (a b c : Fin 15) : Decidable (Covers a b c) := by
  unfold Covers
  infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem cover : ∀ a b c, Covers a b c := by
  intro a
  fin_cases a <;> decide +kernel

theorem normalize_masks (S : Finset (Fin 15)) (hS : S.card = 12)
    (hrow : ∀ x : Fin 5, (S.filter (fun i => x ∈ shape i)).card = 4) :
    ∃ p : Fin 5 ↪ Fin 5, ∀ j : Fin 12, ∃ k ∈ S, shape k = (template j).map p := by
  have hthree : Sᶜ.card = 3 := by rw [Finset.card_compl, Fintype.card_fin, hS]
  obtain ⟨a,b,c, _, _, _, h⟩ := Finset.card_eq_three.mp hthree
  have hS' : S = ({a,b,c} : Finset (Fin 15))ᶜ := by
    simpa using congrArg (fun s : Finset (Fin 15) => sᶜ) h
  subst S
  obtain ⟨r, hr⟩ := cover a b c hrow
  exact ⟨patternPerm r, fun j => ⟨imageIndex r j, hr j, image_correct r j⟩⟩

end RamseySmallImported.RamseyRegular

namespace RamseySmallImported.Ramsey36Canonical


open SimpleGraph

private lemma nonneighbors_five_regular
    (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6)
    (x : Fin 18) (hx : G.degree x = 5)
    (y : Fin 18) (hy : y ∈ Gᶜ.neighborFinset x) :
    (Gᶜ.neighborFinset x ∩ G.neighborFinset y).card ∈ ({3,4} : Finset ℕ) := by
  classical
  have hcard : (Gᶜ.neighborFinset x).card = 12 := by
    rw [Gᶜ.card_neighborFinset_eq_degree, G.degree_compl, Fintype.card_fin, hx]
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 12) (s := Gᶜ.neighborFinset x) (by simp [hcard])
  have hsub_map : Finset.univ.map f ⊆ Gᶜ.neighborFinset x := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hz
    exact hf ⟨i, rfl⟩
  have hmap : Finset.univ.map f = Gᶜ.neighborFinset x :=
    Finset.eq_of_subset_of_card_le hsub_map (by simp [hcard])
  let H := G.comap f
  let e : H ↪g G := SimpleGraph.Embedding.comap f G
  let ec : Hᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv e
  have hH : H.CliqueFree 3 := CliqueFree.comap e.isContained hG
  have hHc : Hᶜ.CliqueFree 5 := by
    intro t ht
    have hs : Gᶜ.IsNClique 5 (t.map f) := by
      refine ⟨?_, (Finset.card_map _).trans ht.card_eq⟩
      intro u hu v hv huv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hv
      exact ec.map_adj_iff.mpr (ht.isClique hi hj (fun he => huv (congrArg f he)))
    apply hc _ (hs.insert (a := x) ?_)
    intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hw
    exact (Gᶜ.mem_neighborFinset x (f i)).mp (hf ⟨i, rfl⟩)
  have hdeg_all : ∀ i : Fin 12, H.degree i ∈ ({3,4} : Finset ℕ) := by
    intro i
    have hlt := OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1.degree_lt H hH hHc i
    have hnl := OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1.nonneighbors_lt
      RamseySmallImported.Ramsey37Density.nine_works H hH hHc i
    rw [H.degree_compl, Fintype.card_fin] at hnl
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp (hmap ▸ hy)
  have hinter : Gᶜ.neighborFinset x ∩ G.neighborFinset (f i) = (H.neighborFinset i).map f := by
    ext w
    simp only [← hmap, Finset.mem_inter, Finset.mem_map, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨⟨j, rfl⟩, hadj⟩
      exact ⟨j, hadj, rfl⟩
    · rintro ⟨j, hadj, rfl⟩
      exact ⟨⟨j, rfl⟩, hadj⟩
  rw [hinter, Finset.card_map, H.card_neighborFinset_eq_degree]
  exact hdeg_all i

theorem mask_arity (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6) (hdeg : ∀ x, G.degree x = 5)
    (v u : Fin 18) (hu : u ∈ Gᶜ.neighborFinset v) :
    (G.neighborFinset v ∩ G.neighborFinset u).card ∈ ({1,2} : Finset ℕ) := by
  have hv := hdeg v
  let A := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  have hAB_disj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro w hwA hwB
    rw [G.mem_neighborFinset] at hwA
    rw [Gᶜ.mem_neighborFinset] at hwB
    exact hwB.2 hwA
  have hA_deg_u : ∀ u ∈ B, (A ∩ G.neighborFinset u).card ∈ ({1,2} : Finset ℕ) := by
    intro u hu
    have hB_reg := nonneighbors_five_regular G hG hc v hv u hu
    have hsub : G.neighborFinset u ⊆ A ∪ B := by
      intro w hw
      rw [G.mem_neighborFinset] at hw
      have hvw : v ≠ w := by
        rintro rfl
        exact ((Gᶜ.mem_neighborFinset v u).mp hu).2 hw.symm
      by_cases hvw_adj : G.Adj v w
      · exact Finset.mem_union_left _ ((G.mem_neighborFinset v w).mpr hvw_adj)
      · exact Finset.mem_union_right _ ((Gᶜ.mem_neighborFinset v w).mpr ⟨hvw, hvw_adj⟩)
    have hsplit : G.neighborFinset u = (A ∩ G.neighborFinset u) ∪ (B ∩ G.neighborFinset u) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · intro hw
        rcases Finset.mem_union.mp (hsub hw) with hA | hB
        · exact Or.inl ⟨hA, hw⟩
        · exact Or.inr ⟨hB, hw⟩
      · rintro (⟨_, hw⟩ | ⟨_, hw⟩) <;> exact hw
    have hdisj_u : Disjoint (A ∩ G.neighborFinset u) (B ∩ G.neighborFinset u) :=
      hAB_disj.mono Finset.inter_subset_left Finset.inter_subset_left
    have hdeg_u : G.degree u = (A ∩ G.neighborFinset u).card + (B ∩ G.neighborFinset u).card := by
      conv_lhs => rw [← G.card_neighborFinset_eq_degree, hsplit, Finset.card_union_of_disjoint hdisj_u]
    change (B ∩ G.neighborFinset u).card ∈ ({3,4} : Finset ℕ) at hB_reg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hB_reg ⊢
    have := hdeg u
    omega
  exact hA_deg_u u hu

private theorem shared_neighbor_forbids (G : SimpleGraph (Fin 18))
    (hG : G.CliqueFree 3) {a x y : Fin 18} (hx : G.Adj a x) (hy : G.Adj a y) :
    ¬ G.Adj x y := fun h =>
  G.isIndepSet_neighborSet_of_triangleFree hG a hx hy (G.ne_of_adj h) h

theorem row_degree (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hdeg : ∀ x, G.degree x = 5)
    {v a : Fin 18} (ha : a ∈ G.neighborFinset v) :
    (Gᶜ.neighborFinset v ∩ G.neighborFinset a).card = 4 := by
  have hva := (G.mem_neighborFinset v a).mp ha
  have hv_mem : v ∈ G.neighborFinset a := (G.mem_neighborFinset _ _).mpr hva.symm
  have heq : Gᶜ.neighborFinset v ∩ G.neighborFinset a = (G.neighborFinset a).erase v := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_erase, Gᶜ.mem_neighborFinset, G.mem_neighborFinset]
    constructor
    · rintro ⟨⟨hvw, _⟩, haw⟩
      exact ⟨hvw.symm, haw⟩
    · rintro ⟨hwv, haw⟩
      exact ⟨⟨hwv.symm, shared_neighbor_forbids G hG hva.symm haw⟩, haw⟩
  rw [heq, Finset.card_erase_of_mem hv_mem, G.card_neighborFinset_eq_degree, hdeg]

theorem distinct_masks (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6) (hdeg : ∀ x, G.degree x = 5)
    (v : Fin 18) :
    Set.InjOn (fun u => G.neighborFinset v ∩ G.neighborFinset u) (Gᶜ.neighborFinset v) := by
  intro x hx y hy heq
  by_contra hxy
  let A := G.neighborFinset v
  let mask := fun u => A ∩ G.neighborFinset u
  change mask x = mask y at heq
  have hx' := (Gᶜ.mem_neighborFinset v x).mp hx
  have hy' := (Gᶜ.mem_neighborFinset v y).mp hy
  have hadj {u z : Fin 18} (h : z ∈ mask u) : G.Adj u z :=
    (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp h).2
  have hA {u z : Fin 18} (h : z ∈ mask u) : G.Adj v z :=
    (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp h).1
  have hcard := mask_arity G hG hc hdeg v x hx
  change (mask x).card ∈ ({1,2} : Finset ℕ) at hcard
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcard
  rcases hcard with h1 | h2
  · obtain ⟨a, hmask⟩ := Finset.card_eq_one.mp h1
    have ham : a ∈ mask x := by simp [hmask]
    have hya : a ∈ mask y := heq ▸ ham
    have hsub : Gᶜ.IsNClique 4 (A.erase a) := by
      refine ⟨?_, ?_⟩
      · intro i hi j hj hij
        exact ⟨hij, shared_neighbor_forbids G hG
          ((G.mem_neighborFinset _ _).mp (Finset.mem_of_mem_erase hi))
          ((G.mem_neighborFinset _ _).mp (Finset.mem_of_mem_erase hj))⟩
      · have ha : a ∈ A := Finset.mem_inter.mp ham |>.1
        rw [Finset.card_erase_of_mem ha]
        change (G.neighborFinset v).card - 1 = 4
        rw [G.card_neighborFinset_eq_degree, hdeg]
    have join {u : Fin 18} (hu : u ∈ Gᶜ.neighborFinset v) (hm : mask u = {a}) :
        ∀ w ∈ A.erase a, Gᶜ.Adj u w := by
      intro w hw
      have hwA := Finset.mem_of_mem_erase hw
      have hnot := ((Gᶜ.mem_neighborFinset v u).mp hu).2
      refine ⟨?_, ?_⟩
      · intro he
        exact hnot (he ▸ (G.mem_neighborFinset v w).mp hwA)
      · intro huw
        have hwM : w ∈ mask u := Finset.mem_inter.mpr ⟨hwA,(G.mem_neighborFinset _ _).mpr huw⟩
        exact (Finset.ne_of_mem_erase hw) (Finset.mem_singleton.mp (hm ▸ hwM))
    have hxjoin := hsub.insert (join hx hmask)
    apply hc _ (hxjoin.insert (a := y) ?_)
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact ⟨fun h => hxy h.symm, shared_neighbor_forbids G hG (hadj hya).symm (hadj ham).symm⟩
    · exact join hy (heq.symm.trans hmask) w hw
  · obtain ⟨a,b,hab,hm⟩ := Finset.card_eq_two.mp h2
    have hax : a ∈ mask x := by simp [hm]
    have hbx : b ∈ mask x := by simp [hm]
    have hay : a ∈ mask y := heq ▸ hax
    have hby : b ∈ mask y := heq ▸ hbx
    have hcompl : b ∈ Gᶜ.neighborFinset a :=
      (Gᶜ.mem_neighborFinset _ _).mpr ⟨hab, shared_neighbor_forbids G hG (hA hax) (hA hbx)⟩
    have htwo := mask_arity G hG hc hdeg a b hcompl
    simp only [Finset.mem_insert,Finset.mem_singleton] at htwo
    have hmem {z : Fin 18} (haz : G.Adj z a) (hbz : G.Adj z b) :
        z ∈ G.neighborFinset a ∩ G.neighborFinset b :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr haz.symm,
        (G.mem_neighborFinset _ _).mpr hbz.symm⟩
    have hsub : ({v,x,y} : Finset (Fin 18)) ⊆ G.neighborFinset a ∩ G.neighborFinset b := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hmem (hA hax) (hA hbx)
      · exact hmem (hadj hax) (hadj hbx)
      · exact hmem (hadj hay) (hadj hby)
    have hle := Finset.card_le_card hsub
    rw [Finset.card_triple_eq_three_iff.mpr ⟨hx'.1,hy'.1,hxy⟩] at hle
    omega

private theorem enumerateVertices {n : ℕ} (s : Finset (Fin 18)) (hn : s.card = n) :
    ∃ e : Fin n ↪ Fin 18, (∀ i, e i ∈ s) ∧ (∀ z ∈ s, ∃ i, e i = z) := by
  classical
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin n) (s := s) (by simp [hn])
  have hin (i) : e i ∈ s := he ⟨i,rfl⟩
  have hsub : Finset.univ.map e ⊆ s := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hz
    exact hin i
  have hmap := Finset.eq_of_subset_of_card_le hsub (by simp [hn])
  refine ⟨e, hin, fun z hz => ?_⟩
  obtain ⟨i,_,hi⟩ := Finset.mem_map.mp (hmap ▸ hz)
  exact ⟨i,hi⟩

theorem canonical_parts
    (shape : Fin 15 → Finset (Fin 5)) (template : Fin 12 → Finset (Fin 5))
    (shape_full : ∀ t : Finset (Fin 5), t.card ∈ ({1,2} : Finset ℕ) → ∃ k, shape k = t)
    (template_inj : Function.Injective template)
    (normalize : ∀ S : Finset (Fin 15), S.card = 12 →
      (∀ a : Fin 5, (S.filter (fun i => a ∈ shape i)).card = 4) →
      ∃ p : Fin 5 ↪ Fin 5, ∀ j : Fin 12, ∃ k ∈ S, shape k = (template j).map p)
    (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj] (hG : G.CliqueFree 3)
    (hc : Gᶜ.CliqueFree 6) (hdeg : ∀ x, G.degree x = 5) (v : Fin 18) :
    ∃ r : Fin 5 ↪ Fin 18, ∃ s : Fin 12 ↪ Fin 18,
      (∀ i, r i ∈ G.neighborFinset v) ∧ (∀ j, s j ∈ Gᶜ.neighborFinset v) ∧
      (∀ i j, G.Adj (r i) (s j) ↔ i ∈ template j) := by
  classical
  let A := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  have hAc : A.card = 5 := (G.card_neighborFinset_eq_degree v).trans (hdeg v)
  have hBc : B.card = 12 := by
    rw [Gᶜ.card_neighborFinset_eq_degree, G.degree_compl, Fintype.card_fin, hdeg]
  obtain ⟨f,hf,fcover⟩ := enumerateVertices A hAc
  obtain ⟨g,hg,gcover⟩ := enumerateVertices B hBc
  let m (j : Fin 12) := Finset.univ.filter fun i => G.Adj (f i) (g j)
  have mem_m (i : Fin 5) (j : Fin 12) : i ∈ m j ↔ G.Adj (f i) (g j) := by simp [m]
  have map_m (j : Fin 12) : (m j).map f = A ∩ G.neighborFinset (g j) := by
    ext z
    constructor
    · intro hz
      obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hz
      exact Finset.mem_inter.mpr ⟨hf a,(G.mem_neighborFinset _ _).mpr ((mem_m _ _).mp ha).symm⟩
    · intro hz
      obtain ⟨ha,hadj⟩ := Finset.mem_inter.mp hz
      obtain ⟨a,rfl⟩ := fcover _ ha
      exact Finset.mem_map.mpr ⟨a,(mem_m _ _).mpr ((G.mem_neighborFinset _ _).mp hadj).symm,rfl⟩
  have size_m (j : Fin 12) : (m j).card ∈ ({1,2} : Finset ℕ) := by
    have h := mask_arity G hG hc hdeg v (g j) (hg j)
    change (A ∩ G.neighborFinset (g j)).card ∈ ({1,2} : Finset ℕ) at h
    rwa [← map_m, Finset.card_map] at h
  choose code code_spec using fun j => shape_full (m j) (size_m j)
  have cinj : Function.Injective code := by
    intro i j hij
    have hm : m i = m j := (code_spec i).symm.trans ((congrArg shape hij).trans (code_spec j))
    apply g.injective
    apply distinct_masks G hG hc hdeg v (hg i) (hg j)
    change A ∩ G.neighborFinset (g i) = A ∩ G.neighborFinset (g j)
    rw [← map_m, ← map_m, hm]
  let S := Finset.univ.image code
  have size_S : S.card = 12 := by simp [S, Finset.card_image_of_injective _ cinj]
  have rows (a : Fin 5) : (S.filter (fun i => a ∈ shape i)).card = 4 := by
    let T := Finset.univ.filter fun j => G.Adj (f a) (g j)
    have hinT (j : Fin 12) : j ∈ T ↔ G.Adj (f a) (g j) := by simp [T]
    have hfilter : S.filter (fun i => a ∈ shape i) = T.image code := by
      ext z
      constructor
      · intro hz
        obtain ⟨hz,ha⟩ := Finset.mem_filter.mp hz
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hz
        rw [code_spec] at ha
        exact Finset.mem_image.mpr ⟨j,(hinT j).mpr ((mem_m _ _).mp ha),rfl⟩
      · intro hz
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
        refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,?_⟩
        rw [code_spec]
        exact (mem_m _ _).mpr ((hinT _).mp hj)
    have Tmap : T.map g = B ∩ G.neighborFinset (f a) := by
      ext z
      constructor
      · intro hz
        obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hz
        exact Finset.mem_inter.mpr ⟨hg j,(G.mem_neighborFinset _ _).mpr ((hinT _).mp hj)⟩
      · intro hz
        obtain ⟨hz,hz'⟩ := Finset.mem_inter.mp hz
        obtain ⟨j,rfl⟩ := gcover _ hz
        exact Finset.mem_map.mpr ⟨j,(hinT _).mpr ((G.mem_neighborFinset _ _).mp hz'),rfl⟩
    rw [hfilter, Finset.card_image_of_injective _ cinj, ← Finset.card_map g, Tmap]
    exact row_degree G hG hdeg (hf a)
  obtain ⟨p,hp⟩ := normalize S size_S rows
  have realize (i : Fin 12) : ∃ j, m j = (template i).map p := by
    obtain ⟨k,hk,hshape⟩ := hp i
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hk
    exact ⟨j,(code_spec j).symm.trans hshape⟩
  choose sel hsel using realize
  have sel_inj : Function.Injective sel := by
    intro i j heq
    apply template_inj
    apply Finset.map_injective p
    rw [← hsel, ← hsel, heq]
  let e : Fin 12 ↪ Fin 12 := ⟨sel,sel_inj⟩
  refine ⟨p.trans f,e.trans g,fun i => hf (p i),fun j => hg (sel j),?_⟩
  intro i j
  change G.Adj (f (p i)) (g (sel j)) ↔ i ∈ template j
  rw [← mem_m, hsel]
  exact Finset.mem_map' p


private def joinVertices {V : Type*} (v : V) (r : Fin 5 ↪ V) (s : Fin 12 ↪ V)
    (i : Fin 18) : V :=
  if i.val = 0 then v else if h : i.val < 6 then r ⟨i.val-1, by omega⟩
  else s ⟨i.val-6, by omega⟩

private theorem join_injective {V : Type*} (v : V) (r : Fin 5 ↪ V) (s : Fin 12 ↪ V)
    (hvr : ∀ i, v ≠ r i) (hvs : ∀ j, v ≠ s j) (hrs : ∀ i j, r i ≠ s j) :
    Function.Injective (joinVertices v r s) := by
  intro i j hh
  apply Fin.ext
  unfold joinVertices at hh
  split_ifs at hh
  all_goals first
    | omega
    | exact False.elim (hvr _ hh)
    | exact False.elim (hvr _ hh.symm)
    | exact False.elim (hvs _ hh)
    | exact False.elim (hvs _ hh.symm)
    | exact False.elim (hrs _ _ hh)
    | exact False.elim (hrs _ _ hh.symm)
    | have e := congrArg Fin.val (r.injective hh); dsimp at e; omega
    | have e := congrArg Fin.val (s.injective hh); dsimp at e; omega

private def rowTag (i : Fin 5) : Fin 18 := ⟨i.val+1, by omega⟩
private def colTag (j : Fin 12) : Fin 18 := ⟨j.val+6, by omega⟩
open RamseySmallImported.RamseyRegular

private theorem template_agrees : ∀ (i : Fin 5) (j : Fin 12),
    i ∈ template j ↔ rowTag i ∈ mask (colTag j) := by decide +kernel

private theorem shapes_complete : ∀ t : Finset (Fin 5),
    t.card ∈ ({1,2} : Finset ℕ) → ∃ k, shape k = t := by decide +kernel

private theorem template_injective : Function.Injective template := by
  intro i j
  exact (show ∀ i j : Fin 12, template i = template j → i = j by decide +kernel) i j

theorem regular_impossible (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hdeg : ∀ x, G.degree x = 5) (hc : Gᶜ.CliqueFree 6) : False := by
  classical
  let v : Fin 18 := 0
  obtain ⟨r,s,hr,hs,hadj⟩ := canonical_parts shape template shapes_complete template_injective normalize_masks G hG hc hdeg v
  have ra (i : Fin 5) : G.Adj v (r i) := (G.mem_neighborFinset _ _).mp (hr i)
  have sb (j : Fin 12) : Gᶜ.Adj v (s j) := (Gᶜ.mem_neighborFinset _ _).mp (hs j)
  have sep (i : Fin 5) (j : Fin 12) : r i ≠ s j := by
    intro he
    exact (sb j).2 (he ▸ ra i)
  let f : Fin 18 ↪ Fin 18 :=
    ⟨joinVertices v r s, join_injective v r s (fun i => (ra i).ne) (fun j => (sb j).1) sep⟩
  have row (i : Fin 18) (hl : 1 ≤ i.val) (hu : i.val < 6) :
      f i = r ⟨i.val-1, by omega⟩ := by
    have h0 : i.val ≠ 0 := by omega
    simp [f, joinVertices, h0, hu]
  have col (j : Fin 18) (hl : 6 ≤ j.val) :
      f j = s ⟨j.val-6, by omega⟩ := by
    have h0 : j.val ≠ 0 := by omega
    have h1 : ¬j.val < 6 := by omega
    simp [f, joinVertices, h0, h1]
  apply canonical_impossible G hG hc f
  · intro i j hil hiu hjl hju
    rw [row i hil hiu, row j hjl hju]
    exact shared_neighbor_forbids G hG (ra _) (ra _)
  · intro i j hil hiu hj
    let a : Fin 5 := ⟨i.val-1,by omega⟩
    let b : Fin 12 := ⟨j.val-6,by omega⟩
    have ai : rowTag a = i := Fin.ext (by dsimp [rowTag,a]; omega)
    have bj : colTag b = j := Fin.ext (by dsimp [colTag,b]; omega)
    rw [row i hil hiu, col j hj]
    exact (hadj a b).trans (by simpa only [ai,bj] using template_agrees a b)


end RamseySmallImported.Ramsey36Canonical
end Ramsey36Regular

section RamseyFiniteSection
open SimpleGraph
namespace RamseySmallImported.RamseyFinite

open OMA.RamseyFinite
private theorem viaDualImpossible (b cs : List Nat) (d low : Nat) (W : List WeightedRow)
    (ext : Extension 6 d b cs)
    (check : dualCheckSimple 0 b d 0 low W = true) : False := by
  obtain ⟨len, mem, good⟩ := ext
  obtain ⟨both, last⟩ := Bool.and_eq_true_iff.mp check
  obtain ⟨valid, opts⟩ := Bool.and_eq_true_iff.mp both
  have upper := rowScore_le b cs W (fun w hw => of_decide_eq_true (List.all_eq_true.mp valid w hw)) good
  have lower := rowScore_ge b (fun _ => false) 0 0 low W cs (fun x hx => by
    have hx' := of_decide_eq_true (List.all_eq_true.mp opts x (mem x hx))
    simp only [Nat.mul_zero, Nat.zero_add] at hx' ⊢
    exact hx')
  simp only [Nat.mul_zero, Nat.zero_add] at lower
  have hl := of_decide_eq_true last
  simp only [Nat.mul_zero, Nat.zero_add] at hl
  rw [len] at lower
  omega

private theorem viaDual32 (b cs : List Nat) (d edgeWeight low : Nat) (W : List WeightedRow)
    (ext : Extension 6 d b cs)
    (check : dualCheckSimple 31 b d edgeWeight low W = true) :
    32 ≤ edges_ (attach cs b) := by
  by_contra! small
  obtain ⟨len, mem, good⟩ := ext
  obtain ⟨both, last⟩ := Bool.and_eq_true_iff.mp check
  obtain ⟨valid, opts⟩ := Bool.and_eq_true_iff.mp both
  have upper := rowScore_le b cs W (fun w hw => of_decide_eq_true (List.all_eq_true.mp valid w hw)) good
  have lower := rowScore_ge b (fun _ => false) edgeWeight 0 low W cs (fun x hx => by
    have hx' := of_decide_eq_true (List.all_eq_true.mp opts x (mem x hx))
    simp only [Nat.mul_zero, Nat.add_zero]
    exact hx')
  simp only [Nat.mul_zero, Nat.add_zero] at lower
  rw [edges_attached, len] at small
  have e : (cs.map (countBits b.length)).sum ≤ 31 - edges_ b - d := by omega
  have he := Nat.mul_le_mul_right edgeWeight e
  have hl := of_decide_eq_true last
  rw [len] at lower
  omega

private def allInd4 (b : List Nat) : List WeightedRow :=
  ((inds b).filter (fun p => p.2 == 4)).map (fun p => (p, 1))

/- Degree-4 case of R(3,6) = 18: b3_0 has no d=4 extension. -/

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b3_0_deg4_cert : dualCheckSimple 0 b3_0 4 0 11 (allInd4 b3_0) = true := by
  decide +kernel

theorem no_deg4_18 (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 6)
    (hmin : ∀ v, 4 ≤ G.degree v) (h4 : ∃ v, G.degree v = 4) : False := by
  classical
  let U : Finset (Fin 18) := Finset.univ
  have bounded : Small G U 6 := by
    intro I _ hI
    by_contra! hc
    exact (hi.mono hc) I ⟨hI, rfl⟩
  have low : U.Nonempty → ∃ x ∈ U, (U.filter (G.Adj x)).card ≤ 4 := by
    intro _
    obtain ⟨v, hv⟩ := h4
    refine ⟨v, Finset.mem_univ v, ?_⟩
    simp only [U, ← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree]
    omega
  have hn (l : List (Fin 18)) := relabel_real G (renumber (encode G l)) l
  obtain ⟨vs, d, b, cs, _, _, hd, hb, hcs, _, ⟨r, _, hr⟩⟩ :=
    rootSplitting G ht normalized hn 5 U (by simp [U]) 4 bounded low
  have hdlb : 4 ≤ d := by
    have hmr := hmin r
    simp only [U, ← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree] at hr
    omega
  have hdeq : d = 4 := by omega
  subst hdeq
  have hb' : b ∈ levels normalized 5 13 4 := by simpa [U] using hb
  have ok := of_decide_eq_true (List.all_eq_true.mp smaller3 b hb')
  simp only [roots3, List.mem_cons, List.not_mem_nil, or_false] at ok
  subst ok
  exact viaDualImpossible b3_0 cs 4 11 (allInd4 b3_0) hcs b3_0_deg4_cert

/- Zero-branching dual certificates for e(3,6;16) >= 32. -/

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b3_0_32_cert : dualCheckSimple 31 b3_0 2 4 26 (allInd4 b3_0) = true := by
  decide +kernel

private def b4_0_32_w : List WeightedRow :=
  [((1224,4),3),((1576,4),2),((1128,4),1),((2244,4),2),((2340,4),2),((804,4),2),((204,4),1),
   ((108,4),3),((2322,4),1),((786,4),3),((2194,4),2),((1170,4),2),((1546,4),2),((2310,4),2),
   ((526,4),2),((142,4),2),((2241,4),2),((801,4),2),((2145,4),2),((1121,4),2),((1553,4),2),
   ((2321,4),3),((785,4),1),((1169,4),2)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_0_32_cert : dualCheckSimple 31 b4_0 3 5 30 b4_0_32_w = true := by
  decide +kernel

private def b4_1_32_w : List WeightedRow :=
  [((1224,4),2),((2340,4),1),((804,4),1),((108,4),2),((786,4),1),((2194,4),1),((1170,4),1),
   ((2310,4),1),((526,4),1),((2241,4),1),((2321,4),1),((785,4),1),((1169,4),1)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_1_32_cert : dualCheckSimple 31 b4_1 3 2 10 b4_1_32_w = true := by
  decide +kernel

private def b4_2_32_w : List WeightedRow :=
  [((1224,4),2),((1576,4),2),((2244,4),2),((2340,4),3),((204,4),1),((108,4),4),((786,4),4),
   ((2194,4),1),((1170,4),1),((1546,4),2),((2310,4),2),((142,4),2),((2241,4),1),((801,4),1),
   ((2145,4),1),((1121,4),1),((1553,4),3),((2321,4),3),((785,4),1),((1169,4),1)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_2_32_cert : dualCheckSimple 31 b4_2 3 5 25 b4_2_32_w = true := by
  decide +kernel

private def b4_3_32_w : List WeightedRow :=
  [((1224,4),2),((804,4),1),((108,4),2),((2322,4),1),((786,4),1),((2194,4),1),((2310,4),1),
   ((526,4),1),((1121,4),1),((2321,4),1),((1169,4),2)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_3_32_cert : dualCheckSimple 31 b4_3 3 3 11 b4_3_32_w = true := by
  decide +kernel

private def b4_4_32_w : List WeightedRow :=
  [((1576,4),1),((2244,4),1),((108,4),1),((786,4),1),((2194,4),1),((270,4),1),((1217,4),1),
   ((1553,4),1)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_4_32_cert : dualCheckSimple 31 b4_4 3 2 7 b4_4_32_w = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_5_32_cert : dualCheckSimple 31 b4_5 3 3 15 (allInd4 b4_5) = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_6_32_cert : dualCheckSimple 31 b4_6 3 3 15 (allInd4 b4_6) = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_7_32_cert : dualCheckSimple 31 b4_7 3 1 2 [] = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_8_32_cert : dualCheckSimple 31 b4_8 3 2 13 (allInd4 b4_8) = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_9_32_cert : dualCheckSimple 31 b4_9 3 1 2 [] = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_10_32_cert : dualCheckSimple 31 b4_10 3 1 2 [] = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
private theorem b4_11_32_cert : dualCheckSimple 31 b4_11 3 1 2 [] = true := by
  decide +kernel

theorem density16_of_min_deg (G : SimpleGraph (Fin 16)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 6)
    (hmin : ∀ v, 2 ≤ G.degree v) : 32 ≤ G.edgeFinset.card := by
  classical
  by_contra! hsmall
  let U : Finset (Fin 16) := Finset.univ
  have bounded : Small G U 6 := by
    intro I _ hI
    by_contra! hc
    exact (hi.mono hc) I ⟨hI, rfl⟩
  have low : U.Nonempty → ∃ x ∈ U, (U.filter (G.Adj x)).card ≤ 3 := by
    intro _
    by_contra! hn
    have h4 (x : Fin 16) : 4 ≤ G.degree x := by
      have hh := hn x (Finset.mem_univ _)
      simp only [U, ← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree] at hh
      omega
    have w := Finset.sum_le_sum (s := U) (f := fun _ => 4) (g := fun x => G.degree x) (fun x _ => h4 x)
    have tot := G.sum_degrees_eq_twice_card_edges
    simp [U] at w
    omega
  have hn (l : List (Fin 16)) := relabel_real G (renumber (encode G l)) l
  obtain ⟨vs, d, b, cs, hv, cover, hd, hb, hcs, enc, ⟨r, _, hr⟩⟩ :=
    rootSplitting G ht normalized hn 5 U (by simp [U]) 3 bounded low
  have hdlb : 2 ≤ d := by
    have hmr := hmin r
    simp only [U, ← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree] at hr
    omega
  have h32 : 32 ≤ edges_ (attach cs b) := by
    have hb' : b ∈ levels normalized 5 (15 - d) 4 := by simpa [U] using hb
    interval_cases d
    · have ok := of_decide_eq_true (List.all_eq_true.mp smaller3 b hb')
      simp only [roots3, List.mem_cons, List.not_mem_nil, or_false] at ok
      subst ok
      exact viaDual32 b3_0 cs 2 4 26 (allInd4 b3_0) hcs b3_0_32_cert
    · have ok := of_decide_eq_true (List.all_eq_true.mp smaller4 b hb')
      simp only [roots4, List.mem_cons, List.not_mem_nil, or_false] at ok
      rcases ok with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact viaDual32 b4_0 cs 3 5 30 b4_0_32_w hcs b4_0_32_cert
      · exact viaDual32 b4_1 cs 3 2 10 b4_1_32_w hcs b4_1_32_cert
      · exact viaDual32 b4_2 cs 3 5 25 b4_2_32_w hcs b4_2_32_cert
      · exact viaDual32 b4_3 cs 3 3 11 b4_3_32_w hcs b4_3_32_cert
      · exact viaDual32 b4_4 cs 3 2 7 b4_4_32_w hcs b4_4_32_cert
      · exact viaDual32 b4_5 cs 3 3 15 (allInd4 b4_5) hcs b4_5_32_cert
      · exact viaDual32 b4_6 cs 3 3 15 (allInd4 b4_6) hcs b4_6_32_cert
      · exact viaDual32 b4_7 cs 3 1 2 [] hcs b4_7_32_cert
      · exact viaDual32 b4_8 cs 3 2 13 (allInd4 b4_8) hcs b4_8_32_cert
      · exact viaDual32 b4_9 cs 3 1 2 [] hcs b4_9_32_cert
      · exact viaDual32 b4_10 cs 3 1 2 [] hcs b4_10_32_cert
      · exact viaDual32 b4_11 cs 3 1 2 [] hcs b4_11_32_cert
  rw [← enc] at h32
  have dg : degrees (encode G vs) = vs.map (fun x => G.degree x) := by
    rw [degrees_encode]
    apply List.map_congr_left
    intro x _
    rw [sizeAt_finset G hv, cover]
    simp only [U, ← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree]
  have w := List.sum_toFinset (fun x => G.degree x) hv
  rw [cover] at w
  have tot := G.sum_degrees_eq_twice_card_edges
  have hh : 64 ≤ (degrees (encode G vs)).sum := by rw [energy]; omega
  rw [dg, ← w] at hh
  exact (by change 64 ≤ ∑ i, G.degree i at hh; omega : False)

end RamseySmallImported.RamseyFinite
end RamseyFiniteSection

namespace RamseySmallImported.Ramsey37Density

open RamseyNumbers SimpleGraph Finset
open OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1 (degree_lt nonneighbors_lt)
open OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1_H2_R1 (removed sum_neighbor_degrees)

lemma eighteen_works : IsGraphRamsey 18 3 6 := by
  classical
  rintro G ⟨hG, hc⟩
  have hdeg (v : Fin 18) : G.degree v = 4 ∨ G.degree v = 5 := by
    have hd := degree_lt G hG hc v
    have hdc := nonneighbors_lt fourteen_works G hG hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    omega
  by_cases h4 : ∃ v, G.degree v = 4
  · exact RamseySmallImported.RamseyFinite.no_deg4_18 G hG hc (fun v => by rcases hdeg v with h | h <;> omega) h4
  · push Not at h4
    have hreg : ∀ v, G.degree v = 5 := fun v => by
      rcases hdeg v with h | h
      · exact (h4 v h).elim
      · exact h
    exact RamseySmallImported.Ramsey36Canonical.regular_impossible G hG hreg hc

lemma card_edgeFinset_ge_sub {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hc : Gᶜ.CliqueFree k) : n + 1 - k ≤ G.edgeFinset.card := by
  classical
  let S : Finset (Fin n) := G.edgeFinset.image (fun e => e.out.1)
  have hS : S.card ≤ G.edgeFinset.card := Finset.card_image_le
  have hindep : Gᶜ.IsClique ((Sᶜ : Finset (Fin n)) : Set (Fin n)) := by
    intro u hu v hv hne
    refine ⟨hne, fun hadj => ?_⟩
    let e : Sym2 (Fin n) := s(u, v)
    have hmem : e ∈ G.edgeFinset := G.mem_edgeFinset.mpr hadj
    have hpt : e.out.1 ∈ e := by
      have hq : s(e.out.1, e.out.2) = e := Quot.out_eq e
      exact Eq.mp (congrArg (fun x => e.out.1 ∈ x) hq) (by simp)
    have hinS : e.out.1 ∈ S := Finset.mem_image.mpr ⟨e, hmem, rfl⟩
    rcases Sym2.mem_iff.mp hpt with heq | heq
    · rw [heq] at hinS
      exact (Finset.mem_compl.mp (Finset.mem_coe.mp hu)) hinS
    · rw [heq] at hinS
      exact (Finset.mem_compl.mp (Finset.mem_coe.mp hv)) hinS
  have hlt : Sᶜ.card < k := by
    by_contra! hge
    exact hc.mono hge Sᶜ ⟨hindep, rfl⟩
  have hcompl := Finset.card_compl_add_card S
  rw [Fintype.card_fin] at hcompl
  omega

lemma gy_step {n k m : ℕ} (hr : IsGraphRamsey m 3 k) (lb : ℕ → ℕ)
    (hlb : ∀ d, n - 1 - d < m → ∀ (H : SimpleGraph (Fin (n - 1 - d))) [DecidableRel H.Adj],
      H.CliqueFree 3 → Hᶜ.CliqueFree k → lb (n - 1 - d) ≤ H.edgeFinset.card)
    (a b : ℕ)
    (hstep : ∀ d, d ≤ k → n - 1 - d < m → a + b * d ≤ d ^ 2 + lb (n - 1 - d))
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree (k + 1)) :
    n * a + 2 * b * G.edgeFinset.card ≤ n * G.edgeFinset.card := by
  have hlocal (v : Fin n) :
      lb (n - 1 - G.degree v) + ∑ w ∈ G.neighborFinset v, G.degree w ≤ G.edgeFinset.card := by
    have hdc := nonneighbors_lt hr G ht hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    let B := Gᶜ.neighborFinset v
    let D := G.induce (B : Set (Fin n))
    have hBcard : Fintype.card B = n - 1 - G.degree v := by
      rw [Fintype.card_coe, SimpleGraph.card_neighborFinset_eq_degree, G.degree_compl, Fintype.card_fin]
    let eB : Fin (n - 1 - G.degree v) ≃ B := (Fintype.equivFinOfCardEq hBcard).symm
    let f : Fin (n - 1 - G.degree v) ↪ Fin n := eB.toEmbedding.trans (Function.Embedding.subtype _)
    let H := G.comap f
    let emb : H ↪g G := SimpleGraph.Embedding.comap f G
    let ec : Hᶜ ↪g Gᶜ := SimpleGraph.Embedding.complEquiv emb
    have hH3 : H.CliqueFree 3 := CliqueFree.comap emb.isContained ht
    have hHk : Hᶜ.CliqueFree k := by
      intro t ht'
      have hs : Gᶜ.IsNClique k (t.map f) := by
        refine ⟨?_, (Finset.card_map _).trans ht'.card_eq⟩
        intro x hx y hy hxy
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hy
        exact ec.map_adj_iff.mpr (ht'.isClique hi hj (fun he => hxy (congrArg f he)))
      apply hc _ (hs.insert (a := v) ?_)
      intro w hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hw
      exact (Gᶜ.mem_neighborFinset v (f i)).mp (eB i).2
    have hHlb : lb (n - 1 - G.degree v) ≤ H.edgeFinset.card := hlb (G.degree v) hdc H hH3 hHk
    let iso : H ≃g D := { toEquiv := eB, map_rel_iff' := Iff.rfl }
    have hdeg_sum : ∑ i, H.degree i = ∑ x, D.degree x := by
      calc ∑ i, H.degree i = ∑ i, D.degree (eB i) :=
            Finset.sum_congr rfl (fun i _ => (iso.degree_eq i).symm)
        _ = ∑ x, D.degree x := Equiv.sum_comp eB (fun x => D.degree x)
    have hcard_eq : H.edgeFinset.card = D.edgeFinset.card := by
      have h1 := H.sum_degrees_eq_twice_card_edges
      have h2 := D.sum_degrees_eq_twice_card_edges
      omega
    have hrem := removed G ht v
    dsimp only at hrem
    change D.edgeFinset.card + ∑ i ∈ G.neighborFinset v, G.degree i ≤ G.edgeFinset.card at hrem
    omega
  have hsum_local := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun v _ => hlocal v)
  rw [Finset.sum_add_distrib, sum_neighbor_degrees, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hsum_local
  have hpoint (v : Fin n) : a + b * G.degree v ≤ G.degree v ^ 2 + lb (n - 1 - G.degree v) := by
    have hd := degree_lt G ht hc v
    have hdc := nonneighbors_lt hr G ht hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    exact hstep (G.degree v) (by omega) hdc
  have hsum_pt := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun v _ => hpoint v)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum, G.sum_degrees_eq_twice_card_edges] at hsum_pt
  have hcomm : b * (2 * G.edgeFinset.card) = 2 * b * G.edgeFinset.card := by ring
  omega

/- Extremal edge bounds ladder. -/

lemma e33_3 (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj]
    (_ : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 3) : 1 ≤ G.edgeFinset.card :=
  card_edgeFinset_ge_sub G hc

lemma e33_4 (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj]
    (_ : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 3) : 2 ≤ G.edgeFinset.card :=
  card_edgeFinset_ge_sub G hc

lemma e33_5 (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 3) : 5 ≤ G.edgeFinset.card := by
  have hdeg (v : Fin 5) : 2 ≤ G.degree v := by
    have hdc := nonneighbors_lt three_works G ht hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    omega
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 5))) (fun v _ => hdeg v)
  have htot := G.sum_degrees_eq_twice_card_edges
  simp at hsum
  omega

private def lb33 : ℕ → ℕ
  | 3 => 1
  | 4 => 2
  | 5 => 5
  | _ => 0

private lemma lb33_ok : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj],
    H.CliqueFree 3 → Hᶜ.CliqueFree 3 → lb33 m ≤ H.edgeFinset.card
  | 3, H, _, ht, hc => e33_3 H ht hc
  | 4, H, _, ht, hc => e33_4 H ht hc
  | 5, H, _, ht, hc => e33_5 H ht hc
  | 0, _, _, _, _ | 1, _, _, _, _ | 2, _, _, _, _ | _ + 6, _, _, _, _ => Nat.zero_le _

lemma e34_4 (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj]
    (_ : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 4) : 1 ≤ G.edgeFinset.card :=
  card_edgeFinset_ge_sub G hc

lemma e34_5 (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj]
    (_ : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 4) : 2 ≤ G.edgeFinset.card :=
  card_edgeFinset_ge_sub G hc

lemma e34_6 (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (_ : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 4) : 3 ≤ G.edgeFinset.card :=
  card_edgeFinset_ge_sub G hc

lemma e34_7 (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 4) : 6 ≤ G.edgeFinset.card := by
  have h := gy_step six_works lb33 (fun _ _ => lb33_ok _) 6 0
    (fun d hd hlt => by interval_cases d <;> simp [lb33] at hlt ⊢) G ht hc
  omega

lemma e34_8 (G : SimpleGraph (Fin 8)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 4) : 10 ≤ G.edgeFinset.card := by
  have h := gy_step six_works lb33 (fun _ _ => lb33_ok _) 7 1
    (fun d hd hlt => by interval_cases d <;> simp [lb33] at hlt ⊢) G ht hc
  omega

private def lb34 : ℕ → ℕ
  | 4 => 1
  | 5 => 2
  | 6 => 3
  | 7 => 6
  | 8 => 10
  | _ => 0

private lemma lb34_ok : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj],
    H.CliqueFree 3 → Hᶜ.CliqueFree 4 → lb34 m ≤ H.edgeFinset.card
  | 4, H, _, ht, hc => e34_4 H ht hc
  | 5, H, _, ht, hc => e34_5 H ht hc
  | 6, H, _, ht, hc => e34_6 H ht hc
  | 7, H, _, ht, hc => e34_7 H ht hc
  | 8, H, _, ht, hc => e34_8 H ht hc
  | 0, _, _, _, _ | 1, _, _, _, _ | 2, _, _, _, _ | 3, _, _, _, _ | _ + 9, _, _, _, _ => Nat.zero_le _

lemma e35_9 (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 5) : 7 ≤ G.edgeFinset.card := by
  have h := gy_step nine_works lb34 (fun _ _ => lb34_ok _) 7 0
    (fun d hd hlt => by interval_cases d <;> simp [lb34] at hlt ⊢) G ht hc
  omega

lemma e35_10 (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 5) : 10 ≤ G.edgeFinset.card := by
  have h := gy_step nine_works lb34 (fun _ _ => lb34_ok _) 10 0
    (fun d hd hlt => by interval_cases d <;> simp [lb34] at hlt ⊢) G ht hc
  omega

lemma e35_11 (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 5) : 15 ≤ G.edgeFinset.card := by
  have h := gy_step nine_works lb34 (fun _ _ => lb34_ok _) 12 1
    (fun d hd hlt => by interval_cases d <;> simp [lb34] at hlt ⊢) G ht hc
  omega

lemma e35_12 (G : SimpleGraph (Fin 12)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 5) : 20 ≤ G.edgeFinset.card := by
  have h := gy_step nine_works lb34 (fun _ _ => lb34_ok _) 16 1
    (fun d hd hlt => by interval_cases d <;> simp [lb34] at hlt ⊢) G ht hc
  omega

lemma e35_13 (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 5) : 26 ≤ G.edgeFinset.card := by
  have hdeg (v : Fin 13) : 4 ≤ G.degree v := by
    have hdc := nonneighbors_lt nine_works G ht hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    omega
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 13))) (fun v _ => hdeg v)
  have htot := G.sum_degrees_eq_twice_card_edges
  simp at hsum
  omega

private def lb35 : ℕ → ℕ
  | 9 => 7
  | 10 => 10
  | 11 => 15
  | 12 => 20
  | 13 => 26
  | _ => 0

private lemma lb35_ok : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj],
    H.CliqueFree 3 → Hᶜ.CliqueFree 5 → lb35 m ≤ H.edgeFinset.card
  | 9, H, _, ht, hc => e35_9 H ht hc
  | 10, H, _, ht, hc => e35_10 H ht hc
  | 11, H, _, ht, hc => e35_11 H ht hc
  | 12, H, _, ht, hc => e35_12 H ht hc
  | 13, H, _, ht, hc => e35_13 H ht hc
  | 0, _, _, _, _ | 1, _, _, _, _ | 2, _, _, _, _ | 3, _, _, _, _ | 4, _, _, _, _
  | 5, _, _, _, _ | 6, _, _, _, _ | 7, _, _, _, _ | 8, _, _, _, _ | _ + 14, _, _, _, _ => Nat.zero_le _

lemma e36_15 (G : SimpleGraph (Fin 15)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6) : 25 ≤ G.edgeFinset.card := by
  have h := gy_step fourteen_works lb35 (fun _ _ => lb35_ok _) 21 1
    (fun d hd hlt => by interval_cases d <;> simp [lb35] at hlt ⊢) G ht hc
  omega

lemma e36_16 (G : SimpleGraph (Fin 16)) [DecidableRel G.Adj]
    (ht : G.CliqueFree 3) (hc : Gᶜ.CliqueFree 6) : 32 ≤ G.edgeFinset.card := by
  have hmin (v : Fin 16) : 2 ≤ G.degree v := by
    have hdc := nonneighbors_lt fourteen_works G ht hc v
    rw [G.degree_compl, Fintype.card_fin] at hdc
    omega
  exact RamseySmallImported.RamseyFinite.density16_of_min_deg G ht hc hmin
end RamseySmallImported.Ramsey37Density
end

section
/- Verbatim previously merged counting lemmas from open-math-agents PR 9042. -/
open SimpleGraph Finset
namespace RamseyDeficiency
theorem removed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ht : G.CliqueFree 3) (v : Fin n) :
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    let D := G.induce (B : Set (Fin n))
    D.edgeFinset.card+(∑ i ∈ N, G.degree i) ≤ G.edgeFinset.card := by
  let N := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  let D := G.induce (B : Set (Fin n))
  let U : Finset (Fin n) := univ
  let W (X Y : Finset (Fin n)) := ∑ i ∈ X, ∑ j ∈ Y, (if G.Adj i j then 1 else 0 : ℕ)
  have flip (X Y) : W X Y = W Y X := by
    unfold W
    rw [Finset.sum_comm]
    simp only [G.adj_comm]
  have partition (X Y) : W X Y + W Xᶜ Y = W U Y := Finset.sum_add_sum_compl X _
  have total (X) : W X U=∑ i ∈ X, G.degree i := by
    simp [W,U,SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter]
  have vanish : W N N=0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    have un : ¬G.Adj a b := fun adj => G.isIndepSet_neighborSet_of_triangleFree ht v
      ((G.mem_neighborFinset _ _).mp ha) ((G.mem_neighborFinset _ _).mp hb) adj.ne adj
    simp [un]
  have inside : B ⊆ Nᶜ := fun i hi => Finset.mem_compl.mpr fun h =>
    ((Gᶜ.mem_neighborFinset _ _).mp hi).2 ((G.mem_neighborFinset _ _).mp h)
  have inc (X Y Z : Finset (Fin n)) (sub : X ⊆ Y) : W X Z ≤ W Y Z :=
    Finset.sum_le_sum_of_subset_of_nonneg sub (by intros; omega)
  have le : W B B ≤ W Nᶜ Nᶜ :=
    (inc B Nᶜ B inside).trans ((flip Nᶜ B) ▸ inc B Nᶜ Nᶜ inside)
  have db : W B B = 2*D.edgeFinset.card := by
    calc
      W B B = ∑ i : B, ∑ j ∈ B, (if G.Adj i.val j then 1 else 0 : ℕ) :=
        (Finset.sum_coe_sort B _).symm
      _ = ∑ i : B, ∑ j : B, (if D.Adj i j then 1 else 0 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (Finset.sum_coe_sort B (fun j => if G.Adj i.val j then 1 else 0)).symm
      _ = ∑ i : B, D.degree i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter]
        exact Finset.sum_boole (R:=ℕ) (D.Adj i) univ
      _ = _ := D.sum_degrees_eq_twice_card_edges
  have p1 := partition N U
  have p2 := partition N N
  have p3 := partition N Nᶜ
  have f1 := flip Nᶜ U
  have f2 := flip N U
  have f3 := flip Nᶜ N
  have a := total N
  have b := total U
  have all : (∑ i ∈ U,G.degree i) = 2*G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  change D.edgeFinset.card+(∑ i ∈ N,G.degree i)≤ G.edgeFinset.card
  omega

theorem sum_neighbor_degrees {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (∑ v, ∑ w ∈ G.neighborFinset v, G.degree w) = ∑ v, G.degree v ^ 2 := by
  simp only [SimpleGraph.neighborFinset_eq_filter,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  calc
    (∑ v, if G.Adj v w then G.degree w else 0) =
        ∑ v ∈ univ.filter (G.Adj w), G.degree w := by
          rw [Finset.sum_filter]
          simp only [G.adj_comm]
    _ = G.degree w^2 := by
      rw [← G.neighborFinset_eq_filter,Finset.sum_const,G.card_neighborFinset_eq_degree,nsmul_eq_mul,pow_two]
      norm_cast



end RamseyDeficiency
end

section
namespace RamseyDeficiency
open Finset SimpleGraph

/-- Restrict the anti-neighbourhood of v to any m of its vertices. An
independent k-set in the restriction would extend by v. -/
theorem extract_anti {n m k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (tri : G.CliqueFree 3) (ind : Gᶜ.CliqueFree (k+1)) (v : Fin n)
    (enough : m≤ Gᶜ.degree v) :
    let D := G.induce ((Gᶜ.neighborFinset v : Finset (Fin n)) : Set (Fin n))
    ∃ (K : SimpleGraph (Fin m)) (_ : DecidableRel K.Adj),
      K.CliqueFree 3 ∧ Kᶜ.CliqueFree k ∧ K.edgeFinset.card≤ D.edgeFinset.card := by
  classical
  let B := Gᶜ.neighborFinset v
  let D := G.induce (B : Set (Fin n))
  have card : m ≤ Fintype.card B := by rw [Fintype.card_coe]; exact enough
  obtain ⟨f,_⟩ := Function.Embedding.exists_of_card_le_finset (α:=Fin m) (s:=(univ : Finset B)) (by simpa using card)
  let K := D.comap f
  let e : K ↪g D := SimpleGraph.Embedding.comap f D
  let into : D ↪g G := SimpleGraph.Embedding.comap (Function.Embedding.subtype (· ∈ B)) G
  let all : K ↪g G := e.trans into
  have transport := Fintype.card_le_of_embedding e.toCopy.mapEdgeSet
  rw [K.card_edgeSet,D.card_edgeSet] at transport
  refine ⟨K,inferInstance,CliqueFree.comap all.isContained tri,?_,transport⟩
  intro S cl
  have mapped : Gᶜ.IsNClique k (S.map all.toEmbedding) := by
    refine ⟨?_,(card_map _).trans cl.card_eq⟩
    intro x hx y hy ne
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
    exact (SimpleGraph.Embedding.complEquiv all).map_adj_iff.mpr
      (cl.isClique ha hb (fun h => ne (congrArg all h)))
  apply ind _ (mapped.insert (a:=v) ?_)
  intro w hw
  obtain ⟨i,_,rfl⟩ := mem_map.mp hw
  exact (Gᶜ.mem_neighborFinset _ _).mp (f i).property

/-- In any hypothetical 36-vertex counterexample, some 27-vertex induced
subgraph is (3,8)-Ramsey and has at most 80 edges. -/
theorem sparse_anti (G : SimpleGraph (Fin 36)) [DecidableRel G.Adj]
    (tri : G.CliqueFree 3) (ind : Gᶜ.CliqueFree 9) :
    ∃ (K : SimpleGraph (Fin 27)) (_ : DecidableRel K.Adj),
       K.CliqueFree 3 ∧ Kᶜ.CliqueFree 8 ∧ K.edgeFinset.card≤80 := by
  classical
  have cap (v : Fin 36) : G.degree v ≤ 8 := by
    by_contra! bad
    apply ind.mono bad (G.neighborFinset v)
    refine ⟨?_,rfl⟩
    rw [G.coe_neighborFinset,G.isClique_compl]
    exact G.isIndepSet_neighborSet_of_triangleFree tri v
  let D (v : Fin 36) := G.induce ((Gᶜ.neighborFinset v : Finset (Fin 36)) : Set (Fin 36))
  have good : ∃ v, (D v).edgeFinset.card≤80 := by
    by_contra! none
    have point (v : Fin 36) : 81+(∑ w∈G.neighborFinset v,G.degree w) ≤ G.edgeFinset.card :=
      le_trans (Nat.add_le_add_right (none v) _) (removed G tri v)
    have total := Finset.sum_le_sum (s:=(univ : Finset (Fin 36))) (fun v _ => point v)
    rw [Finset.sum_add_distrib,sum_neighbor_degrees] at total
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at total
    have numerical (v : Fin 36) : 18*G.degree v ≤ 80+G.degree v^2 := by
      have gap : 0≤(8-(G.degree v : ℤ)) := by have hv := cap v; omega
      have product := mul_nonneg gap (show 0≤10-(G.degree v : ℤ) by omega)
      zify
      nlinarith
    have lower := Finset.sum_le_sum (s:=(univ : Finset (Fin 36))) (fun v _ => numerical v)
    rw [← Finset.mul_sum,G.sum_degrees_eq_twice_card_edges,Finset.sum_add_distrib] at lower
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at lower
    omega
  obtain ⟨v,edges⟩ := good
  have size : 27≤ Gᶜ.degree v := by rw [G.degree_compl,Fintype.card_fin]; have := cap v; omega
  obtain ⟨K,dec,triK,indK,le⟩ := extract_anti (k:=8) G tri ind v size
  exact ⟨K,dec,triK,indK,le.trans edges⟩

/-- The averaged 27-vertex density criterion for R(3,9) ≤ 36. -/
theorem upper_of_81
    (density : ∀ (K : SimpleGraph (Fin 27)) [DecidableRel K.Adj],
      K.CliqueFree 3 → Kᶜ.CliqueFree 8 → 81≤ K.edgeFinset.card) :
    ∀ G : SimpleGraph (Fin 36), ¬(G.CliqueFree 3 ∧ Gᶜ.CliqueFree 9) := by
  classical
  rintro G ⟨tr,ind⟩
  obtain ⟨K,dec,tk,ik,le⟩ := sparse_anti G tr ind
  have lower := @density K dec tk ik
  omega

end RamseyDeficiency
end

section
namespace RamseyDeficiency
open Finset SimpleGraph

/-- The neighbors of a neighbor of the root all lie in the antineighborhood,
apart from the root itself. -/
theorem row_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ht : G.CliqueFree 3) (v : Fin n) :
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    let A (i : N) := (univ : Finset B).filter (fun x => G.Adj i.val x.val)
    ∀ i : N, (A i).card+1=G.degree i.val := by
  intro N B A i
  let f : B ↪ Fin n := ⟨Subtype.val,Subtype.val_injective⟩
  have root := (G.mem_neighborFinset ..).mp i.property
  have eq : (A i).map f=(G.neighborFinset i.val).erase v := by
    ext y
    constructor
    · intro h
      obtain ⟨x,hx,rfl⟩ := mem_map.mp h
      exact mem_erase.mpr ⟨((Gᶜ.mem_neighborFinset ..).mp x.property).ne.symm,
        (G.mem_neighborFinset ..).mpr (mem_filter.mp hx).2⟩
    · intro h
      obtain ⟨ne,ha⟩ := mem_erase.mp h
      have adj := (G.mem_neighborFinset ..).mp ha
      have notAdj : ¬G.Adj v y := fun hit =>
        G.isIndepSet_neighborSet_of_triangleFree ht v root hit adj.ne adj
      exact mem_map.mpr ⟨⟨y,(Gᶜ.mem_neighborFinset ..).mpr ⟨ne.symm,notAdj⟩⟩,
        mem_filter.mpr ⟨mem_univ _,adj⟩,rfl⟩
  rw [←card_map (f:=f) (s:=A i),eq,card_erase_add_one ((G.mem_neighborFinset ..).mpr root.symm)]
  rfl

theorem removed_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ht : G.CliqueFree 3) (v : Fin n) :
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    let D := G.induce (B : Set (Fin n))
    D.edgeFinset.card+(∑ i ∈ N, G.degree i) = G.edgeFinset.card := by
  let N := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  let D := G.induce (B : Set (Fin n))
  let U : Finset (Fin n) := univ
  let W (X Y : Finset (Fin n)) := ∑ i ∈ X, ∑ j ∈ Y, (if G.Adj i j then 1 else 0 : ℕ)
  have flip (X Y) : W X Y = W Y X := by
    unfold W
    rw [Finset.sum_comm]
    simp only [G.adj_comm]
  have partition (X Y) : W X Y + W Xᶜ Y = W U Y := Finset.sum_add_sum_compl X _
  have total (X) : W X U=∑ i ∈ X, G.degree i := by
    simp [W,U,SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter]
  have vanish : W N N=0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    have un : ¬G.Adj a b := fun adj => G.isIndepSet_neighborSet_of_triangleFree ht v
      ((G.mem_neighborFinset _ _).mp ha) ((G.mem_neighborFinset _ _).mp hb) adj.ne adj
    simp [un]
  have complement : Nᶜ=insert v B := by
    ext x
    by_cases h : x=v
    · subst x
      simp [N]
    · simp only [N,B,mem_compl,mem_insert,G.mem_neighborFinset,Gᶜ.mem_neighborFinset,SimpleGraph.compl_adj]; tauto
  have absent : v∉B := by simp [B]
  have drop {Z : Finset (Fin n)} (isolated : ∀ j∈Z,¬G.Adj v j) : W Nᶜ Z=W B Z := by
    rw [complement]
    simp [W,sum_insert absent]
    exact fun x hx => isolated x hx
  have outside : ∀ j∈Nᶜ,¬G.Adj v j := fun j hj adj => (mem_compl.mp hj) ((G.mem_neighborFinset ..).mpr adj)
  have outB : ∀ j∈B,¬G.Adj v j := fun j hj => ((Gᶜ.mem_neighborFinset ..).mp hj).2
  have exactCut : W Nᶜ Nᶜ=W B B := (drop outside).trans ((flip B Nᶜ).trans (drop outB))
  have db : W B B = 2*D.edgeFinset.card := by
    calc
      W B B = ∑ i : B, ∑ j ∈ B, (if G.Adj i.val j then 1 else 0 : ℕ) :=
        (Finset.sum_coe_sort B _).symm
      _ = ∑ i : B, ∑ j : B, (if D.Adj i j then 1 else 0 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (Finset.sum_coe_sort B (fun j => if G.Adj i.val j then 1 else 0)).symm
      _ = ∑ i : B, D.degree i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter]
        exact Finset.sum_boole (R:=ℕ) (D.Adj i) univ
      _ = _ := D.sum_degrees_eq_twice_card_edges
  have p1 := partition N U
  have p2 := partition N N
  have p3 := partition N Nᶜ
  have f1 := flip Nᶜ U
  have f2 := flip N U
  have f3 := flip Nᶜ N
  have a := total N
  have b := total U
  have all : (∑ i ∈ U,G.degree i) = 2*G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  change D.edgeFinset.card+(∑ i ∈ N,G.degree i)=G.edgeFinset.card
  omega

end RamseyDeficiency
end

section
namespace Ramsey37Sparse
open SimpleGraph Finset

/-- The density bounds for (3,5)-graphs on nine through thirteen vertices
and the nine-vertex Ramsey theorem force twenty edges at order fourteen. -/
theorem density14 (nine : ∀ J : SimpleGraph (Fin 9), ¬(J.CliqueFree 3 ∧ Jᶜ.CliqueFree 4))
    (dens : ∀ (n : ℕ) (K : SimpleGraph (Fin n)) [DecidableRel K.Adj],
      K.CliqueFree 3 → Kᶜ.CliqueFree 5 →
      (if n=13 then 26 else if n=12 then 20 else if n=11 then 15 else if n=10 then 10
        else if n=9 then 7 else 0)≤ K.edgeFinset.card)
    (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj] (tri : G.CliqueFree 3)
    (ind : Gᶜ.CliqueFree 6) : 20≤ G.edgeFinset.card := by
  classical
  by_contra! few
  let low (n : ℕ) := if n=13 then 26 else if n=12 then 20 else if n=11 then 15
    else if n=10 then 10 else if n=9 then 7 else 0
  let cost (v : Fin 14) := low (13-G.degree v)+(G.degree v)^2
  have localBound (v : Fin 14) :
      low (13-G.degree v)+(∑ w∈G.neighborFinset v,G.degree w) ≤ G.edgeFinset.card := by
    have cc := G.degree_compl v
    rw [Fintype.card_fin] at cc
    obtain ⟨K,dc,ht,hi,hc⟩ := RamseyDeficiency.extract_anti G tri ind v (m:=Gᶜ.degree v) le_rfl
    let := dc
    have lo : low (Gᶜ.degree v) ≤ K.edgeFinset.card := dens _ K ht hi
    have rem := RamseyDeficiency.removed G tri v
    have same : low (Gᶜ.degree v)=low (13-G.degree v) := congrArg low cc
    omega
  have total := Finset.sum_le_sum (s:=univ) (fun v _ => localBound v)
  rw [Finset.sum_add_distrib,RamseyDeficiency.sum_neighbor_degrees,←Finset.sum_add_distrib] at total
  change (∑ v,cost v)≤_ at total
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at total
  have num (v : Fin 14) : 19≤ cost v ∧ (cost v≤19 → G.degree v=2 ∨ G.degree v=3) := by
    dsimp [cost,low]
    by_cases big : 5≤ G.degree v
    · have sq := Nat.mul_self_le_mul_self big
      simp only [Nat.pow_two]
      constructor <;> omega
    · generalize eq : G.degree v = d at *
      interval_cases d <;> decide
  have eqcost (v : Fin 14) : cost v≤19 := by
    by_contra! high
    have lt := Finset.sum_lt_sum (s:=univ) (f:=fun _ : Fin 14 => 19) (g:=cost)
      (fun w _ => (num w).1) ⟨v,mem_univ _,high⟩
    simp at lt
    omega
  have degree (v : Fin 14) := (num v).2 (eqcost v)
  have edge : G.edgeFinset.card=19 := by
    have le := Finset.sum_le_sum (s:=univ) (f:=fun _ : Fin 14 => 19) (g:=cost) (fun v _ => (num v).1)
    simp at le
    omega
  let D := univ.filter fun v : Fin 14 => G.degree v=2
  have split (v : Fin 14) : G.degree v + (if G.degree v=2 then 1 else 0)=3 := by
    rcases degree v with h|h <;> simp [h]
  have classes := Finset.sum_congr (s₁:=univ) (s₂:=univ) rfl (fun v _ => split v)
  rw [Finset.sum_add_distrib,G.sum_degrees_eq_twice_card_edges,←Finset.card_filter,edge] at classes
  have size : D.card=4 := by simp [D] at classes ⊢; omega
  have closed {v w : Fin 14} (hv : v∈D) (adj : G.Adj v w) : w∈D := by
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    have deg := (mem_filter.mp hv).2
    have l := localBound v
    simp [low,deg,edge] at l
    by_contra bad
    have high : 2 < G.degree w := by have := degree w; omega
    have lt := Finset.sum_lt_sum (s:=G.neighborFinset v) (f:=fun _ => 2) (g:=fun x => G.degree x)
      (fun x _ => by have := degree x; omega) ⟨w,(G.mem_neighborFinset ..).mpr adj,high⟩
    simp [deg] at lt
    omega
  have outside : 9≤ Dᶜ.card := by rw [Finset.card_compl,Fintype.card_fin,size]; decide
  obtain ⟨f,hf⟩ := Function.Embedding.exists_of_card_le_finset (α:=Fin 9) (s:=Dᶜ) (by simpa using outside)
  let K := G.comap f
  let emb : K ↪g G := SimpleGraph.Embedding.comap f G
  have triK := CliqueFree.comap emb.isContained tri
  have pick : ∃ t : Finset (Fin 9), Kᶜ.IsNClique 4 t := by
    by_contra! none
    exact nine K ⟨triK,none⟩
  obtain ⟨t,ht⟩ := pick
  let I := t.map f
  have independent : Gᶜ.IsNClique 4 I := by
    refine ⟨?_,(card_map _).trans ht.card_eq⟩
    intro a ha b hb ne
    obtain ⟨i,hi,rfl⟩ := mem_map.mp ha
    obtain ⟨j,hj,rfl⟩ := mem_map.mp hb
    exact (SimpleGraph.Embedding.complEquiv emb).map_adj_iff.mpr
      (ht.isClique hi hj (fun eq => ne (congrArg f eq)))
  have out {a : Fin 14} (ha : a∈I) : a∉D := by
    obtain ⟨i,_,rfl⟩ := mem_map.mp ha
    exact mem_compl.mp (hf ⟨i,rfl⟩)
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0< D.card by omega)
  have count : (G.neighborFinset v).card=2 := (G.card_neighborFinset_eq_degree v).trans (mem_filter.mp hv).2
  obtain ⟨x,y,ne,eq⟩ := Finset.card_eq_two.mp count
  have hx : G.Adj v x := (G.mem_neighborFinset ..).mp (by simp [eq])
  have hy : G.Adj v y := (G.mem_neighborFinset ..).mp (by simp [eq])
  have hxy : Gᶜ.Adj x y := ⟨ne,fun edge => G.isIndepSet_neighborSet_of_triangleFree tri v hx hy ne edge⟩
  have fromD {a b : Fin 14} (ha : a∈D) (hb : b∈I) : Gᶜ.Adj a b :=
    ⟨fun eq => out hb (eq ▸ ha), fun edge => out hb (closed ha edge)⟩
  have Iy := independent.insert (a:=y) (fun z hz => fromD (closed hv hy) hz)
  apply ind _ (Iy.insert (a:=x) ?_)
  intro z hz
  rcases mem_insert.mp hz with rfl | inI
  · exact hxy
  · exact fromD (closed hv hx) inI

end Ramsey37Sparse
end

section
namespace Ramsey37Sparse
open SimpleGraph
open RamseySmallImported.Ramsey37Density

theorem small_six : ∀ J : SimpleGraph (Fin 6), ¬ (J.CliqueFree 3 ∧ Jᶜ.CliqueFree 3) :=
  six_works

theorem small_eighteen : ∀ J : SimpleGraph (Fin 18), ¬ (J.CliqueFree 3 ∧ Jᶜ.CliqueFree 6) :=
  eighteen_works

theorem low_edges_for_five (n : ℕ) (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (t : K.CliqueFree 3) (i : Kᶜ.CliqueFree 5) :
    (if n=13 then 26 else if n=12 then 20 else if n=11 then 15 else if n=10 then 10
      else if n=9 then 7 else 0) ≤ K.edgeFinset.card := by
  split_ifs with h13 h12 h11 h10 h9
  · subst n; exact e35_13 K t i
  · subst n; exact e35_12 K t i
  · subst n; exact e35_11 K t i
  · subst n; exact e35_10 K t i
  · subst n; exact e35_9 K t i
  · exact Nat.zero_le _

theorem small_densities (n : ℕ) (lo : 14≤ n) (hi : n≤17)
    (J : SimpleGraph (Fin n)) [DecidableRel J.Adj] (t : J.CliqueFree 3) (i : Jᶜ.CliqueFree 6) :
    (if n=17 then 40 else if n=16 then 32 else if n=15 then 25 else 19) ≤ J.edgeFinset.card := by
  interval_cases n
  · exact (show 19≤20 by decide).trans (density14 nine_works low_edges_for_five J t i)
  · exact e36_15 J t i
  · exact e36_16 J t i
  · exact OMA.RamseyFinite.density17_40 J t i

end Ramsey37Sparse
end

section
/- Vertex-row restriction from the public Ramsey reduction in PR 9042. -/
namespace Ramsey37Sparse
open SimpleGraph Finset
lemma lift_card {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (hi : Gᶜ.CliqueFree 7) (S : Finset (Gᶜ.neighborFinset v))
    (cl : ((G.induce ((Gᶜ.neighborFinset v : Finset V) : Set V))ᶜ).IsClique S) :
    S.card ≤ 5 := by
  classical
  let B := Gᶜ.neighborFinset v
  let f : B ↪ V := Function.Embedding.subtype _
  have free : Gᶜ.IsClique (S.map f) := by
    intro x hx y hy hxy
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
    exact ⟨hxy,(cl ha hb (fun h => hxy (congrArg f h))).2⟩
  have hv : v ∉ S.map f := by
    intro hm
    obtain ⟨b,_,eq⟩ := mem_map.mp hm
    exact ((Gᶜ.mem_neighborFinset _ _).mp b.2).ne eq.symm
  have ext : Gᶜ.IsClique (insert v (S.map f)) := free.insert (by
    intro b hb _
    obtain ⟨i,_,rfl⟩ := mem_map.mp hb
    exact (Gᶜ.mem_neighborFinset _ _).mp i.2)
  have lim : (insert v (S.map f)).card < 7 := lt_of_not_ge (fun h =>
    hi.mono h _ ⟨by simpa only [Finset.coe_insert] using ext,rfl⟩)
  rw [card_insert_of_notMem hv,card_map] at lim
  omega

theorem neighborhood_data {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (ht : G.CliqueFree 3) (hi : Gᶜ.CliqueFree 7) :
    let N := G.neighborFinset v
    let B := Gᶜ.neighborFinset v
    let D := G.induce (B : Set V)
    let A (i : N) := (univ : Finset B).filter fun x => G.Adj i.val x.val
    D.CliqueFree 3 ∧ Dᶜ.CliqueFree 6 ∧
      (∀ i, Dᶜ.IsClique (A i)) ∧
      (∀ (J : Finset N) (S : Finset B), Dᶜ.IsClique S → (∀ a ∈ J, Disjoint (A a) S) → J.card+S.card≤6) ∧
      N.card + (∑ a, (A a).card) ≤ ∑ a ∈ N, G.degree a := by
  classical
  let N := G.neighborFinset v
  let B := Gᶜ.neighborFinset v
  let D := G.induce (B : Set V)
  let A (i : N) := (univ : Finset B).filter fun x => G.Adj i.val x.val
  let f : B ↪ V := Function.Embedding.subtype _
  let g : N ↪ V := Function.Embedding.subtype _
  let em : D ↪g G := SimpleGraph.Embedding.comap f G
  have nd (a : N) := (G.mem_neighborFinset v a.val).mp a.2
  have bd (a : B) := (Gᶜ.mem_neighborFinset v a.val).mp a.2
  have split (a : N) (b : B) : a.val≠b.val := fun eq => (bd b).2 (eq ▸ nd a)
  have nr (a b : N) : ¬G.Adj a.val b.val := by
    intro h
    exact G.isIndepSet_neighborSet_of_triangleFree ht v (nd a) (nd b) h.ne h
  change D.CliqueFree 3 ∧ Dᶜ.CliqueFree 6 ∧ (∀ i, Dᶜ.IsClique (A i)) ∧ _ ∧ _
  refine ⟨CliqueFree.comap em.isContained ht,?_,?_,?_,?_⟩
  · intro S hS
    have h := lift_card G v hi S hS.isClique
    have eq := hS.card_eq
    omega
  · intro i a ha b hb hne
    refine ⟨hne,?_⟩
    intro h
    exact G.isIndepSet_neighborSet_of_triangleFree ht i.val (mem_filter.mp ha).2 (mem_filter.mp hb).2
      (Subtype.val_injective.ne hne) h
  · intro J S cl dis
    let X := J.map g
    let Y := S.map f
    have apart : Disjoint X Y := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨a,_,rfl⟩ := mem_map.mp hx
      obtain ⟨b,_,eq⟩ := mem_map.mp hy
      exact split a b eq.symm
    have sx : Gᶜ.IsClique X := by
      intro u hu w hw hne
      obtain ⟨a,_,rfl⟩ := mem_map.mp hu
      obtain ⟨b,_,rfl⟩ := mem_map.mp hw
      exact ⟨hne,nr a b⟩
    have sy : Gᶜ.IsClique Y := by
      intro u hu w hw hne
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hu
      obtain ⟨b,hb,rfl⟩ := mem_map.mp hw
      exact ⟨hne,(cl ha hb (fun h => hne (congrArg f h))).2⟩
    have cross (u : V) (hu : u∈X) (w : V) (hw : w∈Y) : Gᶜ.Adj u w := by
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hu
      obtain ⟨b,hb,rfl⟩ := mem_map.mp hw
      exact ⟨split a b,fun h => Finset.disjoint_left.mp (dis a ha) (mem_filter.mpr ⟨mem_univ _,h⟩) hb⟩
    have full : Gᶜ.IsClique (X ∪ Y) := by
      intro u hu w hw hne
      rcases hu with hu|hu <;> rcases hw with hw|hw
      · exact sx hu hw hne
      · exact cross _ hu _ hw
      · exact (cross _ hw _ hu).symm
      · exact sy hu hw hne
    have lim : (X ∪ Y).card < 7 := lt_of_not_ge (fun h =>
      hi.mono h _ ⟨by simpa only [Finset.coe_union] using full,rfl⟩)
    rw [card_union_of_disjoint apart,card_map,card_map] at lim
    omega
  · have each (a : N) : 1 + (A a).card ≤ G.degree a.val := by
      let Y := (A a).map f
      have nv : v ∉ Y := by
        rintro mem
        obtain ⟨b,_,eq⟩ := mem_map.mp mem
        exact (bd b).1 eq.symm
      have sub : insert v Y ⊆ G.neighborFinset a.val := by
        intro w hw
        rcases mem_insert.mp hw with rfl|mem
        · exact (G.mem_neighborFinset _ _).mpr (nd a).symm
        · obtain ⟨b,hb,rfl⟩ := mem_map.mp mem
          exact (G.mem_neighborFinset _ _).mpr (mem_filter.mp hb).2
      have le := card_le_card sub
      rw [card_insert_of_notMem nv,card_map,G.card_neighborFinset_eq_degree] at le
      omega
    have total := Finset.sum_le_sum (s := (univ : Finset N)) (fun a _ => each a)
    change N.card + (∑ a : N,(A a).card) ≤ ∑ a ∈ N,G.degree a
    rw [← Finset.sum_coe_sort N (fun i => G.degree i)]
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.mul_one,
      Fintype.card_coe,Nat.cast_id] using total



end Ramsey37Sparse
end

section
/- A single affine inequality selects a five-neighbour root among the
twenty-one vertices of each triangle-free graph of size 51 with no
independent seven-set. -/
namespace Ramsey37Sparse
open SimpleGraph Finset
open RamseySmallImported.Ramsey37Density

set_option maxHeartbeats 1600000 in
theorem five_root51 (G : SimpleGraph (Fin 21)) [DecidableRel G.Adj] (tri : G.CliqueFree 3)
    (ind : Gᶜ.CliqueFree 7) (edges : G.edgeFinset.card=51) :
    ∃ r, let B := Gᶜ.neighborFinset r
      let K := G.induce (B : Set (Fin 21))
      G.degree r=5 ∧ Fintype.card B=15 ∧ K.CliqueFree 3 ∧ Kᶜ.CliqueFree 6 ∧ K.edgeFinset.card≤26 := by
  classical
  let child (v : Fin 21) := (G.induce ((Gᶜ.neighborFinset v : Finset _) : Set (Fin 21))).edgeFinset.card
  let mass (v : Fin 21) := ∑ w∈G.neighborFinset v, G.degree w
  obtain ⟨r,dr,ec⟩ : ∃ v : Fin 21, G.degree v=5 ∧ child v≤26 := by
    by_contra! no
    have point (v : Fin 21) : mass v + 4*G.degree v ≤ G.degree v*G.degree v + 19 := by
      have rem := RamseyDeficiency.removed G tri v
      change child v + mass v ≤ G.edgeFinset.card at rem
      have anti := OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1.nonneighbors_lt eighteen_works G tri ind v
      have high := OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1.degree_lt G tri ind v
      rw [G.degree_compl,Fintype.card_fin] at anti
      rcases (show G.degree v=3 ∨ G.degree v=4 ∨ G.degree v=5 ∨ G.degree v=6 by omega) with h|h|h|h
      · obtain ⟨J,dec,t,i,le⟩ := RamseyDeficiency.extract_anti G tri ind v (m:=17)
          (by rw [G.degree_compl,Fintype.card_fin,h])
        have lower := @OMA.RamseyFinite.density17_40 J dec t i
        change J.edgeFinset.card≤ child v at le
        rw [h]
        omega
      · obtain ⟨J,dec,t,i,le⟩ := RamseyDeficiency.extract_anti G tri ind v (m:=16)
          (by rw [G.degree_compl,Fintype.card_fin,h])
        have lower := @e36_16 J dec t i
        change J.edgeFinset.card≤ child v at le
        rw [h]
        omega
      · have upper := no v h
        rw [h]
        omega
      · obtain ⟨J,dec,t,i,le⟩ := RamseyDeficiency.extract_anti G tri ind v (m:=14)
          (by rw [G.degree_compl,Fintype.card_fin,h])
        have lower := @density14 nine_works low_edges_for_five J dec t i
        change J.edgeFinset.card≤ child v at le
        rw [h]
        omega
    have total := Finset.sum_le_sum (s:=univ) (fun v _ => point v)
    simp only [sum_add_distrib,←Finset.mul_sum,sum_const,card_univ,Fintype.card_fin,
      nsmul_eq_mul,G.sum_degrees_eq_twice_card_edges,edges] at total
    have same := RamseyDeficiency.sum_neighbor_degrees G
    simp only [pow_two] at same
    change (∑ v, mass v) = ∑ v, G.degree v*G.degree v at same
    omega
  obtain ⟨ct,ci,_⟩ := neighborhood_data G r tri ind
  refine ⟨r,dr,?_,ct,ci,ec⟩
  rw [Fintype.card_coe,card_neighborFinset_eq_degree,G.degree_compl,Fintype.card_fin,dr]

end Ramsey37Sparse
end

section
namespace FiveLP
open OMA.RamseyFinite SimpleGraph Finset

private theorem induce_encoding {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) (vs : List B) :
    encode G (vs.map Subtype.val)=encode (G.induce (B : Set V)) vs := by
  induction vs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,encode,List.map_map,ih]; rfl

/-- Sort the five neighbor contacts independently of the labeling of the antineighborhood.
The lower contact bound comes from minimum degree three, even at a degree-five root. -/
theorem graph_rows {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (tri : G.CliqueFree 3) (ind : Gᶜ.CliqueFree 7)
    (low : ∀ v,3≤ G.degree v) (edges : G.edgeFinset.card=51) (r : V) (deg : G.degree r=5)
    (i : Fin 8) (vs : List (Gᶜ.neighborFinset r)) (nd : vs.Nodup) (allv : vs.toFinset=univ)
    (code : GlueSeed.encode (G.induce ((Gᶜ.neighborFinset r : Finset V) : Set V)) vs=SparseFifteen.adj i) :
    ∃ l cs, l.Nodup ∧ l.toFinset=univ ∧ cs.length=5 ∧
      (∀ x∈cs,x∈usable 7 3 (SparseFifteen.adj i)) ∧
      okContacts 7 (inds (SparseFifteen.adj i)) cs=true ∧ cs.Pairwise (·≤·) ∧
      (cs.map (countBits (SparseFifteen.adj i).length)).sum=budget i ∧
      encode G l=attach cs (SparseFifteen.adj i) := by
  classical
  let N := G.neighborFinset r
  let B := Gᶜ.neighborFinset r
  let base : List V := vs.map Subtype.val
  have base_code : encode G base=SparseFifteen.adj i := by
    rw [induce_encoding,Sparse32.encode_glue]
    exact code
  have hbn : base.Nodup := nd.map Subtype.val_injective
  have hb : base.toFinset=B := by
    ext x
    constructor
    · intro h
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
      exact a.property
    · intro h
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨⟨x,h⟩,List.mem_toFinset.mp (allv ▸ mem_univ _),rfl⟩)
  obtain ⟨front,fn,hf,sorted_⟩ := sorted_neigh G N base
  have ha (x) (hx : x∈front) : G.Adj r x := (G.mem_neighborFinset r x).mp (show x∈N from hf ▸ List.mem_toFinset.mpr hx)
  have hB (x) (hx : x∈base) : Gᶜ.Adj r x := (Gᶜ.mem_neighborFinset r x).mp (show x∈B from hb ▸ List.mem_toFinset.mpr hx)
  have no (x) (hx : x∈base) : ¬G.Adj r x := (hB x hx).2
  have all_nd : (r::front++base).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,List.nodup_append.mpr ⟨fn,hbn,fun x hx y hy e => no y hy (e ▸ ha x hx)⟩⟩
    change r ∉ front++base
    rw [List.mem_append]
    exact not_or.mpr ⟨fun h => (ha r h).ne rfl,fun h => (hB r h).1 rfl⟩
  have all_front : (r::front++base).toFinset=univ := by
    ext x
    simp only [List.toFinset_cons,List.toFinset_append,hf,hb,Finset.mem_insert,Finset.mem_union,
      Finset.mem_univ,iff_true,N,B,SimpleGraph.mem_neighborFinset,SimpleGraph.compl_adj]
    by_cases h : r=x
    · exact Or.inl (Or.inl h.symm)
    · by_cases a : G.Adj r x
      · exact Or.inl (Or.inr a)
      · exact Or.inr ⟨h,a⟩
  let cs := contactsOf G base front
  have length : cs.length=5 := by
    change (front.map _).length=5
    rw [List.length_map,← List.toFinset_card_of_nodup fn,hf,G.card_neighborFinset_eq_degree,deg]
  have small : Small G univ 7 := by
    intro s _ hs
    by_contra! many
    exact ind.mono many s ⟨hs,rfl⟩
  have hcount (x) (hx : x∈front) : 3≤ sizeAt G base x+1 ∧ sizeAt G base x+1<7 := by
    have eq : G.neighborFinset x=insert r (B.filter (G.Adj x)) := by
      ext y
      simp only [Finset.mem_insert,Finset.mem_filter,B,SimpleGraph.mem_neighborFinset,SimpleGraph.compl_adj]
      constructor
      · intro xy
        by_cases yr : y=r
        · exact Or.inl yr
        · exact Or.inr ⟨⟨Ne.symm yr,fun ry => G.isIndepSet_neighborSet_of_triangleFree tri r (ha x hx) ry xy.ne xy⟩,xy⟩
      · rintro (rfl|⟨_,xy⟩)
        · exact (ha x hx).symm
        · exact xy
    have rn : r∉B.filter (G.Adj x) := fun h => (((Gᶜ.mem_neighborFinset r r).mp (Finset.mem_filter.mp h).1).ne rfl)
    have degree := congrArg Finset.card eq
    rw [G.card_neighborFinset_eq_degree,Finset.card_insert_of_notMem rn] at degree
    have upper := small (univ.filter (G.Adj x)) (Finset.filter_subset ..) (neighbors_small G tri univ x)
    rw [←G.neighborFinset_eq_filter,G.card_neighborFinset_eq_degree] at upper
    rw [sizeAt_finset G hbn,hb,←degree]
    exact ⟨low x,upper⟩
  have rows (s) (hs : s∈cs) : s∈usable 7 3 (encode G base) := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hs
    let S := base.toFinset.filter (G.Adj x)
    have row := inds_complete G base hbn S (Finset.filter_subset ..) (neighbors_small G tri _ x)
    have m := hcount x hx
    rw [sizeAt_finset G hbn] at m
    change bits (base.map fun y => decide (G.Adj x y)) ∈ _
    rw [row_mark]
    exact List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨row,by simpa [S] using m⟩,rfl⟩
  have hi : Gᶜ.IsClique (front.toFinset : Set V) := by
    rw [G.isClique_compl]
    intro x hx y hy xy
    exact G.isIndepSet_neighborSet_of_triangleFree tri r (ha x (List.mem_toFinset.mp hx)) (ha y (List.mem_toFinset.mp hy)) xy
  have ok : okContacts 7 (inds (encode G base)) cs=true := ok_contacts G univ 7 small front base (List.nodup_cons.mp all_nd).2 (subset_univ _) hi
  have enc := root_encoding G r front base ha no tri
  change encode G (r::front++base)=attach cs (encode G base) at enc
  rw [base_code] at rows ok enc
  have cnt := Sparse32.edge_card G (r::front++base) all_nd all_front
  rw [enc,edges_attached,length,edges] at cnt
  have bval : edges_ (SparseFifteen.adj i)+budget i=46 := by fin_cases i <;> decide
  exact ⟨_,cs,all_nd,all_front,length,rows,ok,sorted_,by omega,enc⟩
end FiveLP
end

section
namespace FiveLP
open SimpleGraph Finset OMA.RamseyFinite
theorem fin21_catalog (G : SimpleGraph (Fin 21)) [DecidableRel G.Adj] (tri : G.CliqueFree 3)
    (ind : Gᶜ.CliqueFree 7) (ed : G.edgeFinset.card=51) :
    ∃ (j : Fin 4) (vs : List (Fin 21)), vs.Nodup ∧ vs.toFinset=univ ∧ GlueSeed.encode G vs=GlueSeed.adj j := by
  classical
  obtain ⟨r,dr,cB,tr,ir,cap⟩ := Ramsey37Sparse.five_root51 G tri ind ed
  let B := Gᶜ.neighborFinset r
  let K := G.induce (B : Set (Fin 21))
  obtain ⟨i,vs,nd,allv,code⟩ := SparseFifteen.classification K cB tr ir cap
  have low (v : Fin 21) : 3≤ G.degree v := by
    have h := OMA.R_RamseyNumbers_ramsey_number_three_nine_R1_H2_R1.nonneighbors_lt
      RamseySmallImported.Ramsey37Density.eighteen_works G tri ind v
    rw [G.degree_compl,Fintype.card_fin] at h
    omega
  obtain ⟨l,cs,ln,lv,len,mem,ok,ord,sum,eq⟩ := graph_rows G tri ind low ed r dr i vs nd allv code
  have inside := pool_of_check i (checked i) cs mem len ok sum.le
  have counts (b : List Nat) : countBits b.length=FP32.countBits b.length :=
    funext (fun z=> Sparse32.toPure_count b.length z)
  rw [counts] at sum
  have good : FP32.okContacts 7 (FP32.inds (SparseFifteen.adj i)) cs=true := by
    simpa only [okContacts,FP32.okContacts,Sparse32.toPure_inds] using ok
  have lists := FiveSearch.recover i len inside ord good sum
  exact FiveIso.terminal i cs lists G l ln lv eq
end FiveLP
end

end RamseyFourProof

theorem OMA.solution : OMA.R_RamseyNumbers_ramsey_number_three_nine_R2.H2 :=
  RamseyFourProof.FiveIso.public_H2_of_fin RamseyFourProof.FiveLP.fin21_catalog
