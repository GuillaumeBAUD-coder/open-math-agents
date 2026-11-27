import FormalConjectures.ErdosProblems.«508»
import Mathlib
import Mathlib.Tactic.Sat.FromLRAT

/-!
A four-colouring would forbid monochromatic equilateral triangles of side √3.
The first certificate checks this on the 481-point graph of Jaan Parts
(2020), Table 3 of https://arxiv.org/abs/2010.12661. Each row of the
vertex array encodes the integer quadruple used there, with 32 added
to each signed coordinate before packing it into a six-bit block. The
four variables for vertex i have DIMACS indices 4i+1 through 4i+4.
The first certificate fixes the monochromatic triangle at indices
455, 117 and 112, and normalizes the colours on the unit triangle
455, 240 and 368. The second certificate
applies the triangle constraint to two radius-three hexagonal lattice
patches and proves that opposite points four units apart have the same
colour. The spindle argument of Aubrey de Grey (2018),
https://arxiv.org/abs/1804.02385, completes the contradiction.

The LRAT certificates were independently generated with CaDiCaL and
trimmed to their transitive proof dependencies. The numeric certificates
store the clauses and unit-propagation hints in 16-bit blocks. The
`rup_sound` theorem justifies each propagation, and `refute` inducts on
the derivation to obtain an empty clause. `valid_satisfies` checks each input clause
against the geometry or one of the fixed colours.
-/

namespace OMA.ColorPlane.Cert

def unpack (n : Nat) : List Nat :=
  ((List.range (if n = 0 then 0 else n.log2/16+1))).map (fun i => (n >>> (16*i)) % 65536)

def literal (x : Nat) : Sat.Literal :=
  if x%2 = 0 then .pos (x/2-1) else .neg (x/2-1)

inductive Table where
  | leaf (xs : List Nat)
  | node (l r : Table)

/-- The low bits choose a subtree; the remaining bits select an entry of a leaf. -/
def Table.get : Table → Nat → Nat
  | .leaf xs, i => xs[i]?.getD 0
  | .node l r, i => if i%2=0 then l.get (i/2) else r.get (i/2)

def context (n : Nat) (rows : Table) : Sat.Fmla :=
  (List.range n).map fun i => (unpack (rows.get i)).map literal

private def truth (v : Sat.Valuation) (x : Nat) : Prop :=
  if x%2 = 0 then v (x/2-1) else ¬ v (x/2-1)

private def opp (x : Nat) := if x%2 = 0 then x+1 else x-1

private theorem not_opp (v : Sat.Valuation) {x : Nat} (hx : truth v x) : ¬ truth v (opp x) := by
  by_cases t : x%2 = 0
  · have h1 : (x+1)%2 ≠ 0 := by omega
    have h2 : (x+1)/2 = x/2 := by omega
    simp_all [opp,truth]
  · have h1 : (x-1)%2 = 0 := by omega
    have h2 : (x-1)/2 = x/2 := by omega
    simp_all [opp,truth]

private def mark (s x : Nat) := s ||| (1 <<< x)
private def invariant (v : Sat.Valuation) (s : Nat) := ∀ i, s.testBit i → ¬ truth v i

private theorem mark_ok (v : Sat.Valuation) {s x : Nat} (hs : invariant v s)
    (hx : ¬ truth v x) : invariant v (mark s x) := by
  intro i hi
  simp only [mark, Nat.one_shiftLeft, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at hi
  exact hi.elim (hs i) (fun h => h ▸ hx)

private def initMask : List Nat → Nat
  | [] => 0
  | a::l => mark (initMask l) a

private theorem init_ok (v : Sat.Valuation) (xs : List Nat) (h : ∀ a ∈ xs, ¬truth v a) :
    invariant v (initMask xs) := by
  induction xs with
  | nil => simp [initMask,invariant]
  | cons a l ih => exact mark_ok v (ih (fun i hi => h i (by simp [hi]))) (h a (by simp))

private def holds (v : Sat.Valuation) (xs : List Nat) := ∃ i ∈ xs, truth v i

/-- Reverse unit propagation. Every reference is strictly earlier than the target clause. -/
def rup (db : Nat → List Nat) (cut : Nat) : List Nat → Nat → Bool
  | [], _ => false
  | h::hs, s => if 0 < h ∧ h ≤ cut then
      match (db (h-1)).filter (fun i => !s.testBit i) with
      | [] => true
      | [x] => rup db cut hs (mark s (opp x))
      | _ => false
    else false

private theorem rup_sound (db : Nat → List Nat) (cut : Nat) (v : Sat.Valuation)
    (hd : ∀ i < cut, holds v (db i)) (hs : List Nat) (s : Nat)
    (hi : invariant v s) (hc : rup db cut hs s) : False := by
  induction hs generalizing s with
  | nil => simp [rup] at hc
  | cons k ks ih =>
    rw [rup] at hc
    split at hc
    next hk =>
      obtain ⟨i,him,hit⟩ := hd (k-1) (by omega)
      have hmem : i ∈ (db (k-1)).filter (fun j => !s.testBit j) :=
        List.mem_filter.mpr ⟨him,by by_contra! h; exact hi i (by simpa using h) hit⟩
      split at hc
      next h => simp_all
      next x h =>
        have e : i = x := by simpa [h] using hmem
        subst i; exact ih _ (mark_ok v hi (not_opp _ hit)) hc
      next => contradiction
    next => contradiction

private theorem holds_of_sat (v : Sat.Valuation) (xs : List Nat)
    (h : v.satisfies (xs.map literal)) : holds v xs := by
  classical
  induction xs with
  | nil => exact False.elim h
  | cons a l ih =>
    by_cases ha : truth v a
    · exact ⟨a,by simp,ha⟩
    · have hnot : v.neg (literal a) := by by_cases t : a%2=0 <;> simp_all [literal,truth,Sat.Valuation.neg]
      obtain ⟨i,hi,hit⟩ := ih (h hnot)
      exact ⟨i,by simp [hi],hit⟩

/-- Input clauses are followed by the derived clauses in certificate order. -/
def verify (n k : Nat) (rows hints : Table) : Bool :=
  0 < k && rows.get (n + (k-1)) == 0 &&
    (List.range k).all fun i => rup (fun j => unpack (rows.get j)) (n+i)
      (unpack (hints.get i)) (initMask (unpack (rows.get (n+i))))

theorem refute (n k : Nat) (rows hints : Table) (h : verify n k rows hints) :
    (context n rows).proof [] := by
  intro v hv
  simp only [verify, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨hpos,hzero⟩,hcheck⟩ := h
  have allok (j : Nat) (hj : j < n+k) : holds v (unpack (rows.get j)) := by
    induction j using Nat.strong_induction_on with
    | h j ih =>
      by_cases ht : j < n
      · have hm : ((unpack (rows.get j)).map literal) ∈ context n rows :=
          List.mem_map.mpr ⟨j,List.mem_range.mpr ht,rfl⟩
        exact holds_of_sat _ _ (hv.prop _ hm)
      · let i := j-n
        have e : n+i=j := by dsimp [i];omega
        have hi : i<k := by omega
        by_contra hn
        exact rup_sound _ j v (fun a ha => ih a ha (by omega)) (unpack (hints.get i)) _
          (init_ok v _ (by simpa [holds] using hn)) (by simpa [e] using hcheck i hi)
  have last := allok (n+(k-1)) (by omega)
  rw [hzero] at last
  simp [holds,unpack] at last

/-- Sound range decomposition used to check a large certificate in bounded pieces. -/
def steps (n : Nat) (r h : Table) (a count : Nat) : Bool :=
  (List.range count).all fun d => rup (fun j => unpack (r.get j)) (n+(a+d))
    (unpack (h.get (a+d))) (initMask (unpack (r.get (n+(a+d)))))

theorem join_steps (n : Nat) (r h : Table) (a b : Nat)
    (ha : steps n r h 0 a) (hb : steps n r h a b) : steps n r h 0 (a+b) := by
  simp only [steps, List.all_eq_true, List.mem_range, Nat.zero_add] at ha hb ⊢
  intro i hi
  by_cases hlt : i<a
  · exact ha i hlt
  · have e : a+(i-a)=i := by omega
    simpa [e] using hb (i-a) (by omega)

theorem verify_from_steps (n k : Nat) (r h : Table) (hp : 0 < k)
    (hz : r.get (n+(k-1))=0) (hs : steps n r h 0 k) : verify n k r h := by
  simpa [verify,hp,hz,steps] using hs

end OMA.ColorPlane.Cert

namespace OMA.ColorPlane.Cert
set_option maxRecDepth 5000 in
private def rowsBasePart0 : Table := (.node (.node (.node (.leaf [0x8000600040002,0x31b00e3,0x4e10309,0x8c104f9,0xaef0757,0xbcd09f5,0x78064b06e1094402ae04bc0aec0569])
(.leaf [0x3e90019,0x4b101d9,0x62f03e7,0x6990631,0x8a10869,0xda30bdb,0x5b109bb08c101cb0563]))
(.node (.leaf [0x850084e084c084a,0x2e70167,0xa0d0375,0x7990581,0xb0307bb,0xe110b09,0x3e603e203e8])
(.leaf [0x6df008f,0x88d0255,0x6af0447,0xd0106d9,0x993094b,0xe9b0d93])))
(.node (.node (.leaf [0x428042604240422,0x273011b,0x6a10349,0x74f0557,0xabd0785,0xd090a79,0x54c031608be0aee034a0314031a09600af004f2082a0de201760bbe049808300e00031e034e0af20719])
(.leaf [0x1f10059,0x395020d,0x4490411,0x7fd0675,0xe3b08bb,0xd3f0cf7,0x6500d04064a]))
(.node (.leaf [0xc980c960c940c92,0x38301b3,0x73903a9,0x79105c1,0xb6507fd,0xe110b69,0x8860b64082e0c8604be0dfe04c004d80de80e000b460b7e083002f803400522088405240b420b7a0c840b3b])
(.leaf [0x75f00bf,0xa8b02bb,0x8d504ad,0xd410719,0xb5f0997,0xedb]))))
set_option maxRecDepth 5000 in
private def rowsBasePart64 : Table := (.node (.node (.node (.leaf [0x208020602040202,0x6cb00fb,0x4b3032b,0x5790539,0x9870777,0xd230a3b,0x5064b06dd0716])
(.leaf [0x1430033,0x51901f9,0xacd03f5,0xa75064d,0x903089b,0xe990c61,0x71401cb06dc06510d04]))
(.node (.leaf [0xa700a6e0a6c0a6a,0x78f017f,0x78b038b,0x78105a9,0xdd507e5,0xe150b45,0xd5c0d600d5a])
(.leaf [0x1c100b1,0x8bf0287,0x6d90471,0x8e906f1,0xd1b095b,0xee30e3b])))
(.node (.node (.leaf [0x640063e063c063a,0x83f0137,0x7590369,0x9470567,0xb1b0793,0xc7b0acb,0x507f503680714])
(.leaf [0x24d0075,0x8510229,0x647042f,0xa3906c1,0xb170917,0xe4d0d2d,0xc87]))
(.node (.leaf [0xee80ee60ee40ee2,0x54501c5,0x5b303c3,0x62b05f3,0xbf7082f,0xd410ba1,0x5af0650064c020804980528049609460b3e02e403e6031e034e04b606ce021803a805c004f808680ad009bc0192077a019605240b460e260c8202b00d98035008e008e80ef80c8807f3])
(.leaf [0x3ab00cb,0x33f02f7,0x80b04cb,0xabb073b,0xcb909b1,0xabd]))))
set_option maxRecDepth 5000 in
private def rowsBasePart32 : Table := (.node (.node (.node (.leaf [0x108010601040102,0x3bf00ef,0x6e10319,0x7290529,0xb490761,0xa8f0a1f,0x2d6038e03c607b60886098e0d3e0072064a0882019802d80320043005f0063007400ac00146019602f6033e044e0496004a00c20126031e03ce04be0a160af60dfe02e804c0049408640acc0c5c05a807480780000e00e601c6020602e6064e020404640462082a0b3a0b3c0c840dfc008d])
(.leaf [0x55002d,0x37f01e7,0x7fb03eb,0x82d0645,0xbf10879,0xe550c1d,0x65006dc064c0de403650d9803e30759]))
(.node (.leaf [0x958095609540952,0x1990179,0x3c90391,0x8ad0595,0x81f07d7,0xb610b41,0x95809560952])
(.leaf [0x17100a1,0x56b0273,0x7bb0453,0xde906e1,0xb670957,0xe3b0e1b])))
(.node (.node (.leaf [0x538053605340532,0x2990131,0x71f0357,0x8590561,0xb0f078f,0xc330abb,0x8a022a03a205ba094201b80cc00e98008e02e60abe031c04b406cc0dfc07d80d9808400a500a58068202e403f4043c0694094407c209da080808500692083a0a520b7c0e9c04080670068807d00b28079800fe026e022e0406066e03f2043a0a4a00e8021803a805c00dfa07cc09b409dc0d540e38042e062e02f2005000a800c8031e0cbc0212089a0b0200e609b80b8009b00ced])
(.leaf [0x5bb0063,0x4b50215,0xbf10419,0x9910699,0xe4908e1,0xd550d0d,0xa16]))
(.node (.leaf [0xdd00dce0dcc0dca,0x53f01bf,0x59903b9,0x9a905c9,0xa190821,0xdd50b7d,0x38e05140b680ba007d6081e03f2043a0a780bd00c180e78078c04d800d80bf00e74096007e2091a0e460e6607e40be0056c0bce0c1601be0bea09a80c9c084c00d4057007900e280b7a07d80820094a0b620d100e480e6805b80bdc0d07])
(.leaf [0x3a900c9,0x46902e9,0x6dd04bd,0xa350725,0xc5b09a3,0x35b]))))
set_option maxRecDepth 5000 in
private def rowsBasePart96 : Table := (.node (.node (.node (.leaf [0x318031603140312,0x28d010d,0x9a30333,0x9590549,0x9990781,0xcf50a55,0x5064b07b60365])
(.leaf [0x59d0045,0x38b0203,0x44f0407,0x7f50665,0xbe908b9,0xe790cc1,0x71406500717]))
(.node (.leaf [0xb800b7e0b7c0b7a,0x7b30193,0x3c703a7,0x98b05ab,0xa4d07f5,0xde10b61,0x50831])
(.leaf [0x1d700b7,0x45102a9,0x7030493,0x897070f,0xcfd096d,0xed70e9f])))
(.node (.node (.leaf [0x748074607440742,0x1830153,0x75d036d,0xd0b056b,0xba107b1,0xb230aeb,0x14036904d40724087408c40178049805c808780ad00b180136028e051603f4043c05f408200b640b9c0b7e03a805c0097807e20a32038a0552077a099a083a079007c809680ba80302026c0ace0b1601cc04500ae0020807e80a38020604d6072600e6042e062e01ca0462066204960b9603f2043a00e805e80134028c0018043006300ca00e100464094c077e099e09a609d60164032c0b580eb805e20c9c0e0c02e9])
(.leaf [0x6d70087,0x5fd0245,0xb110439,0xadd06cd,0x995093d,0xe450d55]))
(.node (.leaf [0x8f000f,0x4f301cb,0x71703cf,0x7f50605,0xb690841,0xe790bc1,0xd400a180717])
(.leaf [0x38b00d3,0x4cd02fd,0xb7d04d5,0x9290751,0xef509bd,0x650007807f208be0076064e010e06dd]))))
set_option maxRecDepth 5000 in
private def rowsBasePart16 : Table := (.node (.node (.node (.leaf [0x88008600840082,0x69b00e3,0x6d5030d,0x847050f,0x7910761,0xcff0a0f,0x140d3e007803e80a180172034a010c0364071408bc007209ba07f9])
(.leaf [0x3ed001d,0x22701df,0x43303eb,0xd85062d,0xe25086d,0xe3b0bfb,0x2d3]))
(.node (.leaf [0x8d008ce08cc08ca,0x1910171,0x3bb0383,0x8d90589,0xb1307c3,0xcdb0b23,0x5c805c405c6])
(.leaf [0x2d90099,0x3f90271,0x687044f,0x8c906e1,0xca10951,0xdfb0de3])))
(.node (.node (.leaf [0x4b004ae04ac04aa,0x3cd0125,0x5290351,0x9670557,0x967078f,0xd2d0a95,0x110055006e007400b400b3e07f408c0])
(.leaf [0x1f5005d,0x5a10211,0x6870417,0x84d0685,0xe4908d9,0xd3f0d07,0x65001d0036900d1]))
(.node (.leaf [0xd400d3e0d3c0d3a,0x1f901c1,0xb7d03a5,0xd4d05bd,0xa750805,0xba50b7d,0x5af08bd09900a180cf8071706e107f4035002ae03f6043e0606069609460c8600b000b800e800f001d0065802ac00e4021403a405bc0ba4004602d206920b460b7e0d4e042000d801d8022a060207e20a320179])
(.leaf [0x1f900c9,0x5ff02df,0x71904b9,0xa8f071f,0xb97099f,0x573]))))
set_option maxRecDepth 5000 in
private def rowsBasePart80 : Table := (.node (.node (.node (.leaf [0x290028e028c028a,0x6d50105,0xb03032b,0x94b053b,0x7ab077b,0xc170a4f,0x5064b07b601d1])
(.leaf [0x16f003f,0x4cf01ff,0x75d03fd,0x9710659,0xacd08a5,0xe010c89,0x1cd06dc08bd065107170d07]))
(.node (.leaf [0xb000afe0afc0afa,0x8dd0185,0x5670397,0xd3305a3,0xb5f07ef,0xd1b0b53,0x5036907240de40288049809180ad00b180bc0028604b60dfe043c06a40b640b9c0e540b7e0d4e037003a8038a03c2055205da07b2077a099a0b3a0db2079007c80ba80ace0b1601cc08e00e00020604960208072800e80db809980b980016056e057e078e07c609a6032e046600b000f001c801d00210065800d8077e])
(.leaf [0x5ff00af,0x5d10291,0xb470477,0xa410701,0xb7d0965,0xee10e59])))
(.node (.node (.leaf [0x6c806c606c406c2,0x4830143,0x55b036b,0x757056f,0x98907a9,0xb130adb,0x71406dc08c1])
(.leaf [0x1e10081,0x607022f,0xc03042b,0x70906d1,0x95f092f,0xe590d41,0x947]))
(.node (.leaf [0x990009,0x21901d1,0xa9703c7,0x7eb05fb,0xb870837,0xe590ba9,0x4f4017202f4033c06ee033a06ec02f607f3])
(.leaf [0x1e100d9,0x6c102f9,0x52704d7,0x9450745,0xd3509b5,0xb4f]))))
set_option maxRecDepth 5000 in
private def rowsBasePart48 : Table := (.node (.node (.node (.leaf [0x188018601840182,0x22d00fd,0x717031f,0x5510531,0xaf5076d,0xc070a37,0x7b6044a01260b260dfe05c40c24082e03d1])
(.leaf [0x3fb002b,0x4af01ef,0x64903f9,0x7f5064d,0xaf90889,0xdd90c39,0x71401d001cf]))
(.node (.leaf [0x9d809d609d409d2,0x4930173,0x6bd038d,0x7af059f,0x81f07e7,0xe250b3d,0xb4c0b4a0b50])
(.leaf [0x1b900a9,0x67b027b,0x7f90469,0xd0f06e7,0xb43095b,0xe550e35])))
(.node (.node (.leaf [0x5b805b605b405b2,0x2910139,0x52d0365,0x5bb0563,0x7c90799,0xb0b0ac3,0x58003a600b200b409900e000078010e0716038003a20a1803d00af80b2807d00e7e007206920dfa0e7a05e80db206940cde0540077805e2089a0cda08a00d98053a07720af20c9a098a064f])
(.leaf [0x5c5006d,0x4bd021d,0xaf7041f,0x9c506ad,0xc210901,0xe450d15,0x6e0]))
(.node (.leaf [0xe580e560e540e52,0x20f01c7,0x71f03bf,0x79305d3,0xa35082d,0xd230b8b,0x5af0368064d07f9082b])
(.leaf [0x1c700cf,0xabb02e3,0xc8504bd,0xa550735,0xee109a9,0x3e5]))))
set_option maxRecDepth 5000 in
private def rowsBasePart112 : Table := (.node (.node (.node (.leaf [0x3a0039e039c039a,0x7f90111,0x515033d,0x8c10551,0xb810781,0xbdf0a6f,0x5064b0365])
(.leaf [0x42d004d,0x5270207,0x7930403,0x803066b,0xad108c1,0xd390cf1,0xaa5]))
(.node (.leaf [0xc080c060c040c02,0x4b501ad,0x5bf03a7,0x89b05b3,0xde907f9,0xcf90b69,0x5af071406dd010e017807f509bc0a140aa408300650])
(.leaf [0x60700b7,0x56902b1,0x707049f,0x9050715,0xcad097d,0x8bb])))
(.node (.node (.leaf [0x7d007ce07cc07ca,0x8790159,0x56d0375,0x9570577,0xb8b07b3,0xdb30af3,0x1b001ac01ae])
(.leaf [0x2ab008b,0x6510251,0x7c3043b,0x86106d9,0xb3b0943,0xdb50d85]))
(.node (.leaf [0xa50015,0x20d01d5,0x7bf03d7,0x815061d,0xc13084b,0xc0d0bd5,0x65108be008e03160abe0ea003e807f50365034a064a008a0756094600b3])
(.leaf [0x1f500dd,0xad90301,0x83504ed,0x7850755,0xa1909e9,0x3f4043c082c094405c6078a094202040830020603f2043a0790077f]))))
set_option maxRecDepth 5000 in
private def rowsBasePart8 : Table := (.node (.node (.node (.leaf [0x48004600440042,0x3b700e7,0x9670307,0x7030503,0xd770757,0xa5b0a0b,0x5af00780230088802d2064b02e8036804c007280af0001000b800f001d004bc06de0b680d78078c0aea00d802ae066e021603a6083a0a520a340a9407f906ba07020da801ce022a0a320d7200d2008f0390])
(.leaf [0xaf001f,0x7ff01d7,0xabb03e3,0x9af062f,0xe1f0867,0xe730beb,0x5b101cb054f0563]))
(.node (.leaf [0x890088e088c088a,0x4d70167,0x5810381,0xbef057f,0xbb107c1,0xee50b15,0x55e055a0560])
(.leaf [0x1990099,0xa25025d,0x8230443,0x87506dd,0xb3f094f,0xead0da5])))
(.node (.node (.leaf [0x470046e046c046a,0x26f0127,0x4db034b,0x8c30553,0x7bf078f,0xbfd0a8d,0x5056303680d09])
(.leaf [0x5ab0053,0x3c90211,0xae90411,0xa3d0675,0xb2108d1,0xd370cff,0x650064f]))
(.node (.leaf [0xd000cfe0cfc0cfa,0x56901b9,0x79903a9,0x90105c1,0x83d0805,0xd3f0b6f,0x5af036808bd0b640b6c0b9c0cf407f40076082e09460c860208032806580250012603ce04be05a807480780011004c00de808e80d070e460830094209620c820b8005a2077a099a09a20d3602060b3e0948])
(.leaf [0x1b700c7,0x5ab02d3,0x50704b7,0x8cf071f,0xd490999,0x1db]))))
set_option maxRecDepth 5000 in
private def rowsBasePart72 : Table := (.node (.node (.node (.leaf [0x250024e024c024a,0x27f0107,0x723032b,0x9250535,0xac90779,0xd150a45,0x7f20874055008780bc00bf00e7604160412046601cd])
(.leaf [0x67003f,0x38d01fd,0x44703ff,0xd97064f,0xc13089b,0xdff0c7f,0x71400120202036a03a2046204f207f2095a06dd0650]))
(.node (.leaf [0xac00abe0abc0aba,0x3510189,0xa3d038d,0x91705a7,0x83907f1,0xb870b4f,0xe600e5e0e5c])
(.leaf [0x35d00ad,0x43b028b,0x4d50475,0xd1906f1,0x9af0967,0xef70e47])))
(.node (.node (.leaf [0x680067e067c067a,0x1730143,0x38b036b,0xd090569,0x7cd079d,0xeb10ad1,0x50714008c010c02e40314036404bc04d4087408bc0a740aec052e054e07560078012802880290041801ca0412046204f20602082a0a4a0e7203e70af00c880e1002e208820af20b020c320c5a0d92046409240944094c0b640cec0e2407780d09])
(.leaf [0x4bd0075,0x2710231,0x7bb042b,0x89306c3,0x9490929,0xe390d39,0xde4]))
(.node (.leaf [0x450005,0x95901c9,0x73103c9,0x96305f3,0xe010831,0xd510ba9,0x5af044201c4086a000e087001c2063c0300063804d0082804ca082205780910003e00be014e03ee02fa06320040044800c008b8090c00d1])
(.leaf [0xf100d9,0x4bf02f7,0xb7b04cb,0x7770747,0xb8109b9,0x4f7]))))
set_option maxRecDepth 5000 in
private def rowsBasePart40 : Table := (.node (.node (.node (.leaf [0x148014601440142,0x7bb00eb,0x493031b,0xba30523,0x9810769,0xc010a29,0x38e01ce090607280af00de8090401d006f007380bf608300bf40136028e0416038c041208e203a405bc05e4082e0134028c037003a805c008e80a5205e607f5])
(.leaf [0x15d002d,0x80f01e7,0x43103f9,0x695064d,0xbd3087b,0xe810c29,0x71401d001cf07f808c0]))
(.node (.leaf [0x998099609940992,0x33f0177,0x5a3038b,0xd270597,0xb6907d9,0xcf10b41,0xa160a140a18])
(.leaf [0x71d009d,0x4390281,0x4b50465,0xa3b06e3,0xe6b0953,0xe490e29])))
(.node (.node (.leaf [0x578057605740572,0x4590131,0x6d10361,0x9710561,0xda7078f,0xd930abb,0x64a07f503680aea09e80a7804120e7606dd])
(.leaf [0x1790071,0x9b30213,0x7b7041f,0x9b7069f,0xc8708e7,0xea70d0f,0xd92]))
(.node (.leaf [0xe100e0e0e0c0e0a,0x94f01bf,0x5a103c1,0x8c705cf,0xb7d0825,0xbaf0b87,0x3c603a60a520a5807e20a3203a207e40a340a9403c80b81])
(.leaf [0x77b00c3,0x65102e9,0x8e304bb,0xe0b0723,0xd2709a7,0x6d3]))))
set_option maxRecDepth 5000 in
private def rowsBasePart104 : Table := (.node (.node (.node (.leaf [0x358035603540352,0x3e90111,0x4bd033d,0x745054d,0xad90781,0xbd50a5d,0x5500bc008bd])
(.leaf [0xe5004d,0x3c70207,0x6690409,0x9c30663,0x90508bd,0xe7b0cdb,0x3cd]))
(.node (.leaf [0xbc80bc60bc40bc2,0x33f01a7,0x56b03a3,0xd3f05af,0xb8707f7,0xb990b69,0x5af071406dd010e01be075609e60b3e0179])
(.leaf [0x36500b5,0x41502ad,0x8bf0497,0xd37070f,0xb870977,0xf050ef5])))
(.node (.node (.leaf [0x790078e078c078a,0x4190159,0xb490371,0x75f0577,0x9a907b9,0xd770aef,0xe0010000c])
(.leaf [0x157008f,0x41f024f,0x667043f,0x70d06d5,0xd010941,0xd930d73]))
(.node (.leaf [0x2b10011,0x58101d1,0xaa703cf,0xd750605,0xc0b0843,0xd630bcb,0x1ce04f401cc068206880cba0551])
(.leaf [0x67300d3,0x6c90301,0x6ef04df,0xadb074b,0xd4909c9,0x94009605ae0251]))))
set_option maxRecDepth 5000 in
private def rowsBasePart24 : Table := (.node (.node (.node (.leaf [0xc800c600c400c2,0x21900f1,0x4f30313,0x9210519,0x975075d,0xbf70a17,0x14005601ee021e02d6038e0556056607b6098e0d3e0072022a041a064a0090017802d80350008c02e4031404bc08740a740d040126034e03ce04be0a160aa60b260288049804f8055008780c280018023004200628063000760286028e01b80390053005580b4007f8])
(.leaf [0xd10029,0x55f01df,0x63503ed,0xa5f0637,0x8df0877,0xe4d0c0d,0x883]))
(.node (.leaf [0x918091609140912,0x48b016b,0xa130383,0x99d058d,0xb2307cb,0xe010b29,0x770076e076c])
(.leaf [0x3510099,0x66b026b,0x82b044b,0xac106e1,0x9a10959,0xe930dfb])))
(.node (.node (.leaf [0x4f804f604f404f2,0x7150125,0x9bb034b,0x5a90561,0x9bd078d,0xdb50aa5,0x8a022a036a03a2053205ba08e209420390055807b800b801c000b601560536056e078e095e09660aee0d7604f808780c600cc00e980234028c008e031604be087604b404bc06cc0dfc0b660d9801d0084009f80a500a580de80e78015206820aea043c06a409440c84078a09620c82085008e6083a0a520b7c0e9c04080670068807d00b280318079807e20d7200fe022e0406066e0926043a0a4a021803a805c00dfa07cc09b40d380e380ed802f60c380ea00c5c01ce04b606ce0c360b3b])
(.leaf [0xef0067,0x3a30213,0x7f50415,0xcc10689,0xb2708df,0xe3b0d03,0x949]))
(.node (.leaf [0xd800d7e0d7c0d7a,0x38b01bb,0x5cb03ab,0x79105c9,0xb810811,0xd450b7d,0x914072803a405bc05a807800d5005a2077a072607ba03a805c00d4e05e9])
(.leaf [0x30100c9,0x32102e9,0x8dd04b5,0xd490721,0x9d909a9,0xa7b]))))
set_option maxRecDepth 5000 in
private def rowsBasePart88 : Table := (.node (.node (.node (.leaf [0x2d802d602d402d2,0x137010f,0x4c30333,0x7750545,0x947077f,0xe990a51,0x2aa02e2034a07f2094206dc01d00d3e05620365])
(.leaf [0xdb0043,0x82301fb,0xad703ff,0xc910659,0xad508b5,0xe0f0c9f,0x8bd0a18082c064b0717]))
(.node (.leaf [0xb400b3e0b3c0b3a,0x32f0197,0xb6f0397,0x7b705af,0x83107f9,0xb970b5f,0x5064c])
(.leaf [0xd700b7,0x5a70297,0x8b5048d,0xb130703,0x9b5096d,0xe7d0e75])))
(.node (.node (.leaf [0x708070607040702,0x2ff014f,0x6ed036d,0x8ab056b,0x99507ad,0xd670adf,0x507140368064c])
(.leaf [0x1710089,0x5750235,0x7ab0433,0x8a106d1,0x98f0937,0xed10d49]))
(.node (.leaf [0x2590009,0x3a501cd,0x5c103d1,0x64b0603,0xa55083d,0xc070bbf,0x5b107140650064c06dc])
(.leaf [0x2f300d3,0xacd02f5,0x72904d9,0xb470747,0xba509bd,0xde7]))))
set_option maxRecDepth 5000 in
private def rowsBasePart56 : Table := (.node (.node (.node (.leaf [0x1c801c601c401c2,0x35f00ff,0xaf90321,0x877052f,0x7af0777,0xbc50a3d,0x14064b06dd0719098c0b640b9c0cf4079007c8096809e00ba8007803e804200ac00db8019602d6031e005202d2038a03c2055205da098a02ae0524083a0a520db20b8001e6036e03a605be075608e60a3206040744077c0924099c0b3c00a800c801f002000dfe01be038e05560b3e02f208e20af40418095609ae0414082c083c09f40a54059400180070019802f804500312052206ea073207b9000e005600ae00e600ee01c60206020e02080218037003a809600330021d])
(.leaf [0x6d0035,0x99101f1,0x74903f9,0x947064f,0xac50895,0xefd0c55,0x1cb049405c409040acc0c240464082c0de40365064f03e80bf8077e0bf40300063809a809b80b800d200420008c0152056a078a096201820302012803d006d008a809080b660cf60e56008e0abe044e01560ad008a00ba4078c09640e480ec40948036e03a605be087e08960bd6075a07920c9202ac00c8020000fc026c0177]))
(.node (.leaf [0xa200a1e0a1c0a1a,0x19d017d,0x723038b,0xbff059f,0xa3907e9,0xb7f0b47,0xc280c240c26])
(.leaf [0xc300ab,0x54f0287,0xc350465,0x73506ed,0xc390961,0xecb0e33])))
(.node (.node (.leaf [0x5f805f605f405f2,0x3d70137,0x5590369,0x8810569,0x97f0797,0xb030acb,0x507f509610b700d40039603a600b203ea078a074009500b68098e0b960c9a0dfa010e04be0716072600b4038c0554073c0098032003d004c006d009080a180af80b280e00088808a00b080d980596077e09040af4020203a2043a06ce0528077a098a031c02d807d0007202d2052206920e7a0e7e0208070807b80e5805e80790083a0db20173])
(.leaf [0x1290079,0x8490221,0x7a90429,0x70706bf,0xcdb0903,0xeb50d1d,0x887]))
(.node (.leaf [0xea00e9e0e9c0e9a,0x38f01c7,0xa8f03bf,0x91105e1,0xa95082d,0xd330b93,0x5af06500714064c083007f4])
(.leaf [0x2e700cf,0x94f02ef,0x50b04cb,0x76f073f,0xb7f09af,0x74d]))))
set_option maxRecDepth 5000 in
private def rowsBasePart120 : Table := (.node (.node (.node (.leaf [0x3e803e603e403e2,0x38b0113,0x7090341,0xcf10551,0xe37077f,0xbed0a75,0x50563036806dd])
(.leaf [0xe30053,0x82b0203,0xadd0405,0xa35066d,0xc2708bf,0xe930ceb,0x24f]))
(.node (.leaf [0xc580c560c540c52,0x1ef01b7,0x6f903a9,0x9c305b3,0xa0b07fb,0xd3d0b65,0x566071406dc0a14010c0090007202aa02e20942007403cc0831])
(.leaf [0xd700bf,0x8e902b1,0x6d904b1,0xaa90719,0xb610991,0xd3b])))
(.node (.node (.leaf [0x810080e080c080a,0x77f015f,0x6d90379,0x5c7057f,0x9ab07bb,0xecb0afb,0x360035e035c])
(.leaf [0x313008b,0x3dd0255,0xb13043b,0xa1106d9,0xc870947,0xdc70d97]))
(.node (.leaf [0x1770017,0x37901d9,0x42103e9,0x8210629,0x8b90861,0xe390bd9,0x5b107f309bb08c1])
(.leaf [0x1fb00e3,0x3510309,0x6ed04f5,0x9610759,0xd7309e3,0x1403e8008a017206e101d00bbc031404f40494054c07f9]))))
set_option maxRecDepth 5000 in
private def rowsBasePart4 : Table := (.node (.node (.node (.leaf [0x28002600240022,0x34300e3,0x6cf0307,0xcc104f9,0xb410759,0xa770a07,0x505af0251064b06e100cf07f9])
(.leaf [0x43001b,0x55901d9,0x74103e9,0x81d062d,0xacd0865,0xe3b0be3,0x5b106e1]))
(.node (.leaf [0x870086e086c086a,0x3310169,0xb510379,0x8d10581,0xb9307bb,0xc870b17,0x4ec04ea04f0])
(.leaf [0x1790099,0x5690261,0x7970447,0x71906e1,0x9a7094f,0xef70d97])))
(.node (.node (.leaf [0x448044604440442,0x3b7011f,0x9b90349,0x77f0557,0xb5d0785,0xbe70a7f,0x5056303680d09094507f50719024b])
(.leaf [0x4330053,0x3a90211,0x7690411,0x97f0677,0xadd08c5,0xe330cf3,0x944064f0bf00c2804980550041808300e78049600b40414075801cf]))
(.node (.leaf [0xcc00cbe0cbc0cba,0x4bd01b5,0x78103a9,0x8a305bb,0xbc707ff,0xd050b6d,0x5af0368098c07f4064f0126031e06de03e60aba06e102ac0830017802e2])
(.leaf [0xe500c5,0x6b702c7,0xb6904b1,0x8b5071d,0xb970997,0xb]))))
set_option maxRecDepth 5000 in
private def rowsBasePart68 : Table := (.node (.node (.node (.leaf [0x228022602240222,0x12f0107,0x507032f,0x85b0533,0x9910779,0xbd30a43,0x4980ad00b180c600cc00b7e0758077e09a60552077c0e760e7e05580cba0790096804960ace0b1602060c5a0f000e7402080960038d])
(.leaf [0x4050035,0x82101f9,0xbcf03f7,0xc85064d,0xac108a1,0xddf0c77,0x71404f207f2008c010c02e4036408bc0a740d040650064a0569]))
(.node (.leaf [0xa900a8e0a8c0a8a,0x3070187,0xa35038d,0x8cb05a3,0x82707ef,0xe310b49,0xe040e020e08])
(.leaf [0x2dd00ad,0x2d5028d,0xb47046f,0xacf06ef,0xe790961,0xe610e49])))
(.node (.node (.leaf [0x660065e065c065a,0x7510141,0x9f10369,0xbd30563,0xb7b0793,0xc870acf,0x64a064c0a740a160d3e0d09])
(.leaf [0x2ad0075,0x24f022f,0x773042b,0xad106c1,0xb23091b,0xee70d2f,0x4bb]))
(.node (.leaf [0xf080f060f040f02,0x7eb01c3,0x70503c5,0x64f05f7,0xc290831,0xe4f0b9f,0x369007402210717])
(.leaf [0x65900d1,0x4b502f5,0x82904d1,0xb3d073d,0xee909b1,0xb5d]))))
set_option maxRecDepth 5000 in
private def rowsBasePart36 : Table := (.node (.node (.node (.leaf [0x128012601240122,0x6a300eb,0xaeb0313,0x8310529,0x7930763,0xcff0a1f,0x505af0177])
(.leaf [0xb90031,0x4cf01e7,0xac503ed,0x9b30643,0xe270877,0xda90c29,0x1d007f800140176010c03e804f40110]))
(.node (.leaf [0x978097609740972,0x2f30173,0x5590391,0x9a90599,0xa1907d9,0xb690b41,0x9a609a809a2])
(.leaf [0x325009d,0x3fb027b,0x4930463,0x8cb06e3,0xb710959,0xeb10e21])))
(.node (.node (.leaf [0x558055605540552,0x3c10131,0xb2b0353,0x93b055b,0xb67078f,0xc5f0abf,0x507f50b400b3e0d09])
(.leaf [0xd7006f,0x5a70217,0x76d041d,0xaa90699,0xaf108e9,0xe430d0b,0xd3f]))
(.node (.leaf [0xdf00dee0dec0dea,0x7e701bf,0x7b903b9,0xd5505c5,0xa270827,0xe350b7d,0x566031c0af40ba002aa06920a78078c096409dc00d801d8042001d003e8001800b8001602ae0e460e66041c069400d2031a01ce0b9a0af807560e480e6809da07c00d07])
(.leaf [0x63300c3,0x4a102e9,0x71704bf,0xb050725,0xcdb09a3,0x543]))))
set_option maxRecDepth 5000 in
private def rowsBasePart100 : Table := (.node (.node (.node (.leaf [0x338033603340332,0x367010f,0xb0d0335,0x5990551,0x9a10781,0xd610a59,0x71601240e000dfa082f])
(.leaf [0xc5004d,0x39d0205,0x6090409,0x8410669,0xc5908b9,0xe990cc1,0x95]))
(.node (.leaf [0xba80ba60ba40ba2,0x9050195,0x3d103a9,0x9c105b1,0xa5907f9,0xeff0b5f,0x5af00180b64083c0a54001407ce041c083a0a5207900ba8005400ae030e03f00ac800480b6207fa0dea00c4033803900678062c041e07ca0d580de0077207aa0c7209a200b000c80d0e0cfc0d0c00dc076205a000e0073007b00042001e04ae07fe063006d8076803e3])
(.leaf [0x31300b3,0x2d502ad,0x82d0495,0xa5f070f,0x9cd0975,0xef10eb9])))
(.node (.node (.leaf [0x768076607640762,0x3090159,0x9f5036d,0x5cd0575,0x99f07b7,0xcbd0aed,0x84036904d4072402880b180bc00126013602360286028e041603ce03f4043c0bf80e540a260b7e0d4e003001e8026003a80898097807e20a3203c2055207b2077a099a0db20198041e0220079007c80ba80b160ae0020607e60a360a4e0bf6006a04020412066a0682020804d8072800e80db8049007f0006e0196000e078e07c609a60134028c0168002e005e00b600e600ee01c6020e065606620a4a02180960042000c20294075c07940d1c0ada077e038f])
(.leaf [0x97008f,0x3e7024f,0x64d043d,0xcf706cf,0xc7b093b,0xedd0d55]))
(.node (.leaf [0xcf000f,0x54f01cf,0x7cd03cd,0x9730603,0xc07083f,0xe270bc7,0xcf04f403e807f3])
(.leaf [0x66b00d3,0x63502fd,0xc9d04d5,0x953074b,0xc9b09c3,0xa140a7407180d3e08be06e1]))))
set_option maxRecDepth 5000 in
private def rowsBasePart20 : Table := (.node (.node (.node (.leaf [0xa800a600a400a2,0x20b00eb,0x34b0313,0xb9f050f,0x7990761,0xbbd0a15,0x10c036405500bc003e7])
(.leaf [0x5590021,0x47501dd,0x5fb03eb,0x95f0637,0x8bf0877,0xe610c09,0x553]))
(.node (.leaf [0x8f808f608f408f2,0x40b016b,0x59b0383,0x893058b,0xb9b07c3,0xd970b27,0x71407180716])
(.leaf [0x3210099,0x5490271,0x785044d,0xa7506dd,0xea3094b,0xe110de9])))
(.node (.node (.leaf [0x4d004ce04cc04ca,0x41f0127,0x6510351,0xcf30553,0x9b3078b,0xd3d0aa5,0x95e01d001ce0cea0cee054d])
(.leaf [0x5b3005b,0x8390211,0x7590419,0xa4f0687,0xadd08dd,0xd510d09,0x650]))
(.node (.leaf [0xd600d5e0d5c0d5a,0x20901c1,0x3d303ab,0x5e705c7,0xb470807,0xd090b81,0xb6807720c7209620598077809640b6404cc082408920bd207ea0a440a4208aa07ec04ac0c7404b0071008b004ca08220bd807520b41])
(.leaf [0x20100c9,0x94102e1,0x7d904b9,0xb2f071f,0xd4f099f,0x6db]))))
set_option maxRecDepth 5000 in
private def rowsBasePart84 : Table := (.node (.node (.node (.leaf [0x2b002ae02ac02aa,0x125010d,0x4ab0333,0x59f0547,0x7b7077f,0xd550a4d,0x24c064b01d00d3e054e06e1012403e804f806080bc0008e022e03a60b7c022a07e20a1807e403d005c80b7a095a08bf])
(.leaf [0x575003d,0x5bb01fb,0x7810401,0xa1f0657,0x8ff08b7,0xce10ca1,0x71401d006dc]))
(.node (.leaf [0xb200b1e0b1c0b1a,0x7b7018f,0x5b10399,0x5df05af,0xbe907f1,0xe250b55,0x50714])
(.leaf [0xcf00b7,0xa590291,0x8690489,0x8890709,0xcf30963,0xeed0e5d])))
(.node (.node (.leaf [0x6e806e606e406e2,0x8630143,0x567036f,0x78f056f,0x98b07ab,0xb230adb,0x7802b006980830082a0b3a01260b3c02d202d80076069202ae0367])
(.leaf [0x4c3007b,0x28b0233,0x78b0433,0x86306cb,0x9710931,0xe3b0d43]))
(.node (.leaf [0x24f0007,0x37101d1,0xb9f03c7,0x9410601,0xbfd0835,0xbf50bbd,0x5b107140650064c0717])
(.leaf [0x21900d9,0x6f102f9,0x6e104d9,0xacd0745,0x9dd09bd,0xd17]))))
set_option maxRecDepth 5000 in
private def rowsBasePart52 : Table := (.node (.node (.node (.leaf [0x1a801a601a401a2,0x26d00fd,0x9910321,0x74b052b,0xb610771,0xd510a39,0xcf405520a52036e0a32055609f40a5403700cf20a38038d])
(.leaf [0x563002b,0x81501ed,0x65103f9,0x82f064f,0xc890889,0xe790c39,0x71403a206dc017803180350010c04140604082c0bec0de403650650064f0316075605a80748078003e609e60d8600c4057e09a609b60b460b7e0eb60b220bf00d980ef40d04]))
(.node (.leaf [0x9f809f609f409f2,0x4f90179,0x6e5038d,0x8b905a1,0x83107e9,0xb650b45,0xbac0bb00baa])
(.leaf [0x2f900a9,0xa43027b,0xb3b0463,0x72506ed,0xb7b095b,0xe9d0e35])))
(.node (.node (.leaf [0x5d805d605d405d2,0x38b0133,0x54f0367,0x7570567,0x9730793,0xc770ac7,0x507f503a600b2056a078a0962010e02e600b4038c032003d006d00af8060207e20a3202e8077e0864021203a20945041a0408067007b809c000720bde05700790083a0a52034e00e403c40142003600d6024e031e041e022003cf])
(.leaf [0x10f0077,0x5110221,0xbf7041f,0xa8f06af,0xbf30903,0xeb10d19,0xde9]))
(.node (.leaf [0xe780e760e740e72,0x36f01c7,0x7bf03bf,0x7b705df,0xa4d082d,0xe570b8f,0x5af07140a1606dc])
(.leaf [0x20700cf,0x4a902f1,0x71f04c7,0xb150735,0xb6b09ab,0x55d]))))
set_option maxRecDepth 5000 in
private def rowsBasePart116 : Table := (.node (.node (.node (.leaf [0x3c803c603c403c2,0x2470117,0x6b5033d,0xbbf054f,0xd890781,0xcfd0a6d,0x5025002e40de40b3e03e80b400a14064e02e607f5])
(.leaf [0x5a7004f,0x5990209,0x7e50405,0x8410671,0xbbd08bd,0xe330ceb,0x717]))
(.node (.leaf [0xc280c260c240c22,0x7d901b1,0x6cf03a7,0x92105b9,0x83307fb,0xd330b63,0x2e402e20651])
(.leaf [0x75300b3,0x65102b1,0x8cf04a7,0xa170717,0xd330983,0xbfb])))
(.node (.node (.leaf [0x7f007ee07ec07ea,0x4010161,0x5770377,0xbe90579,0xdb707b7,0xdfb0af3,0x1ee01f001ec])
(.leaf [0x2e3008b,0x8890251,0x81f043f,0x8b506d5,0xb5f0947,0xee90d89]))
(.node (.leaf [0xc50015,0x21f01d7,0x62103e1,0xc57061f,0xbcd0855,0xe2f0bd7,0x2b0000e01ce008c03140aec008a02ae08e60aee03a604f401cc03a40563])
(.leaf [0x33700df,0x3410309,0x52304f3,0x92f0757,0xbc109e9,0x5af06e103f4043c0694082c09440c26028605c608660ace0b16012403cc04b4051406cc07e20d720b440b7c0e24007003400b680ba00cf8078a07c209620ba20692083a0a520798036a03a205ba0752094200b604060d7600fc026c0134028c006c009c02b401620204089e042a004e00c601ce01d0083008400a5804b606ce028805a80780096000ae00e600ee01c60206020e065603080528010d]))))
set_option maxRecDepth 5000 in
private def rowsBasePart12 : Table := (.node (.node (.node (.leaf [0x68006600640062,0x3d100e9,0xae10309,0xb990509,0xe290759,0xa7f0a0f,0x1408bc0bc0055000120179])
(.leaf [0x14d001d,0x96701d7,0xbc103e9,0xa590631,0x8d5086d,0xe7b0bf3,0x5aa]))
(.node (.leaf [0x8b008ae08ac08aa,0x77f0167,0x7590381,0x5cd0585,0x9bb07c3,0xdf90b21,0x59405980596])
(.leaf [0x2510099,0x8a10269,0x66b044b,0x8bf06df,0xb67094f,0xe810db9])))
(.node (.node (.leaf [0x490048e048c048a,0x2890129,0x4f90351,0x9370557,0x7c7078f,0xd490a91,0x505630368])
(.leaf [0xeb005b,0x4ed020d,0x44f0417,0x8490681,0xc0d08d5,0xe210d01,0x65008c101cf]))
(.node (.leaf [0xd200d1e0d1c0d1a,0x94701b7,0xa5d03a5,0x9a105c1,0x84f0807,0xb9d0b7d,0x5af08bd09900a180b680ba007170af001cc0b3c03e60aea0b3a00b4038c073c073e0350064f04920b800b460b7e05a2077a0948032009280cc0078e0960077607ae05a80748078007c00cb4043000940179])
(.leaf [0x1bf00c7,0x69702d7,0x6cd04b5,0xa7d071d,0xb67099f,0x373]))))
set_option maxRecDepth 5000 in
private def rowsBasePart76 : Table := (.node (.node (.node (.leaf [0x270026e026c026a,0x3790109,0x99b032b,0x775053d,0xb630773,0xd310a49,0x6dc010c0367])
(.leaf [0xc10041,0x3bf01ff,0x65503fd,0x7ed0655,0xe35089d,0xde90c89,0x71401d006dc065007f3]))
(.node (.leaf [0xae00ade0adc0ada,0x4b90189,0xb65038d,0x9b305a3,0xa4907f1,0xd150b4d,0xee80ee40ee6])
(.leaf [0x5f300ab,0x555028d,0x6df0477,0xa5f06f7,0x9c10969,0xed50e55])))
(.node (.node (.leaf [0x6a806a606a406a2,0x2f50145,0x3a3036b,0x5c5056d,0xb2d079d,0xb210ad9,0x509480b480b700b800ea0008e022e02ae036e039603a60946010e02e604be04d607160726087608c60abe01bc038c052c0554032003d004b804c006d009080a180aa80af80b280e0002ac0aa40bec0c24007801380238029000c80200022a0a32087409040acc082a09f20a520bea024e041e042e062e052806f0008a0192044a052e05a60746077e019602d6031e02040214036c03a403f2064f])
(.leaf [0x64d0075,0x563022b,0x83f042f,0xad906c9,0xb3d0925,0xeef0d37,0x7f2]))
(.node (.leaf [0x870007,0x20901d1,0x7c303c3,0x63705ff,0xe810831,0xdfb0ba3,0x5af064c0717])
(.leaf [0x1d700d7,0x66d02f5,0xc9704cf,0x7810749,0xc7d09b5,0x96f]))))
set_option maxRecDepth 5000 in
private def rowsBasePart44 : Table := (.node (.node (.node (.leaf [0x168016601640162,0x6b700f7,0x695031d,0xcdf0527,0x7a5076d,0xa970a37,0x21e02d6038e03960556056607b6098e0d3e0072022a041a064a0090019802d80320011002300420043005f0063007f80ac0006a008a0192033a044a0492004e00c601ce0126031e03ce04be09060a160aa60af60b260dfe02e80318036804c00728087809e80a780af00d080de8064c0284049405c40874090409140acc0b140c2401d0052806f007380288053005a80780096009e60bf600cf])
(.leaf [0x1b90031,0x3b501ed,0x5f503f5,0x6a5064d,0xac10889,0xc610c39,0x71400d106dc0172034a0b26064f]))
(.node (.leaf [0x9b809b609b409b2,0x3e90179,0x5ab038b,0x77d059d,0xb4307db,0xcf90b41,0xabe0ac00aba])
(.leaf [0xc900a9,0x59d027d,0x6cf0467,0xac306e3,0x9a90961,0xe490e31])))
(.node (.node (.leaf [0x598059605940592,0x835012d,0x3830363,0xd010561,0xe490791,0xde90ac1,0x64a07f5071405800b800b700d50036e039603a605be00b200b4038c007804c0077e010e04be072603800212036a03a20a1803d004b806d00560075000fc007205e80a5205e2032c077a099a034a07940b6e039003980650])
(.leaf [0x2090071,0x3ab021b,0x82f041f,0x9a106a9,0xe4d08f5,0xd5b0d13,0xabb]))
(.node (.leaf [0xe300e2e0e2c0e2a,0x1ff01c7,0x5dd03bd,0x9af05cf,0xc1b0823,0xd5f0b87,0x5af0715064d083007f3])
(.leaf [0xe700cf,0x94302e3,0xb6b04bb,0xd590731,0xe7b09a3,0xa1b]))))
set_option maxRecDepth 5000 in
private def rowsBasePart108 : Table := (.node (.node (.node (.leaf [0x378037603740372,0x6dd010d,0x4d5033d,0x77f054f,0xb190781,0xd1d0a5d,0x5064b03670948])
(.leaf [0x1a5004d,0x4970207,0x6710409,0x6a3066b,0x91708bf,0xd230ceb,0x6dd]))
(.node (.leaf [0xbe80be60be40be2,0x91701a7,0x5b703a7,0x78505b5,0xbed07f5,0xba10b69,0x64c06500d980a17])
(.leaf [0x37f00b7,0x44f02af,0xc5b0493,0x8a90719,0xd090979,0x382])))
(.node (.node (.leaf [0x7b007ae07ac07aa,0x7570157,0x3ab0373,0x7910579,0xaf707b7,0xde90af1,0x12601280124])
(.leaf [0x1790091,0x5b10251,0x6a90441,0x71f06d7,0x99b0943,0xda90d79]))
(.node (.leaf [0x4d0015,0x95b01cb,0x5cd03d5,0x9510611,0xb7b084b,0xe190bd1,0x5b1065107260d50083c038c0554013800e4021403a400d6083a0a320406066e03f2043a040806700570079005b6078a079409cc00300036013400c4021203a2077e003800d80758079609ce0563])
(.leaf [0x78d00d5,0x95f02ff,0x8a904e1,0xb510751,0xba509dd,0x505af036803f4082c0bf60d960bee0c26028605c6086609060ace012403cc04b409040af40dfc0d720b440b7c0e240070015802f8034004500b68078a09620a5201e8036a03a205ba07520bd200b60d7604180156006c009c02040af60b0600c601ce01d008300a580bf00e7804b60bf40e74028805980748078009600028005800b000b800e801c802080210065801860b2602f6033e095209aa0ad00e000746077e07f0094009980d28010d]))))
set_option maxRecDepth 5000 in
private def rowsBasePart28 : Table := (.node (.node (.node (.leaf [0xe800e600e400e2,0x33100f1,0x6070317,0x8ff051f,0xad90761,0xd410a19,0x21e05660d3e022a041a064a0350071806dc03e8010e041e0abe0bbe008a044a04f201d0055007f80716])
(.leaf [0x1e10029,0x21d01e5,0x75903f1,0x965063d,0xadf0877,0xe350c15,0xc0b]))
(.node (.leaf [0x938093609340932,0x8b7016f,0x3c10391,0x7790599,0xba507cd,0xdd10b31,0x7f407f807f2])
(.leaf [0x7150095,0xa35026d,0xb27044f,0xd0506dd,0xb430953,0xe9b0e13])))
(.node (.node (.leaf [0x518051605140512,0x82f0127,0xb27034f,0x74b055b,0xacf078f,0xaf90ac1,0x36a03a205ba0bd201f00390055807b80c1000b801b800b6037e078e095e09660ac604f80ad00b1804b406cc08a40dfc0b6607d801d00a5803f40c84078a09620c820a520b440b7c0d4c04080670076007980a3208700e480406066e092603f2021803a805c00dfa09b40b900d380e380ee002f60c3800a800c801ce04b606ce0c360924094c0b640cec07760949])
(.leaf [0x1fd0065,0x3cd0215,0xaef0417,0x8310699,0xc7d08dd,0xd450d0d,0xc89]))
(.node (.leaf [0xda00d9e0d9c0d9a,0x4d301bb,0xa7303ab,0x8bd05c5,0xb690819,0xd4d0b7d,0x4f403e8017207f3])
(.leaf [0x34100c9,0x33102e9,0xb6904b9,0x8c90729,0xb7309a3,0x1ab]))))
set_option maxRecDepth 5000 in
private def rowsBasePart92 : Table := (.node (.node (.node (.leaf [0x2f802f602f402f2,0x2390111,0x6770337,0x8a50545,0x9510781,0xbdf0a57,0xd920d3f06e1])
(.leaf [0x1710049,0x99b01fb,0x43d0405,0x9790661,0xb0f08b7,0xcdd0cbd,0x4b609060908083a0e100136028e07900bf805580b6408e00ce0078e08da0cde0bf20138029007780e4805980b68038f]))
(.node (.leaf [0xb600b5e0b5c0b5a,0x41f0197,0x5b3039b,0x88905b1,0x9f307f3,0xd270b5f,0x71503680110017803d1])
(.leaf [0x1cf00b7,0x5af029f,0x6bb0493,0xd2d0705,0xb4b096b,0xf090e79])))
(.node (.node (.leaf [0x728072607240722,0x86b014b,0x745036d,0x9510571,0xb0f07af,0xcb30ae3,0x50369008c02e404bc0a74017805c80ad00b180c28007604160096034e03ce04be0a160b260d3e064d0d09])
(.leaf [0x55b0083,0x9f50235,0x8170437,0xa5306cb,0xcf70937,0xe5f0d4f]))
(.node (.leaf [0x410011,0x46501cd,0x5e503cd,0x66d0605,0xa710841,0xd890bc1,0x64d06dc08be0717])
(.leaf [0x33300d3,0x3390301,0x84b04d3,0x7810751,0xc8909c1,0x2e802e606de010e0abe064d]))))
set_option maxRecDepth 5000 in
private def rowsBasePart60 : Table := (.node (.node (.node (.leaf [0x1e801e601e401e2,0x3a700ff,0x9930323,0x5670537,0x93b0773,0xc110a41,0x5064b06dd07160d3e])
(.leaf [0xb90039,0x4c501f5,0x7d703f7,0x9c10651,0xc950895,0xe810c61,0x71401cb06dc064a0650]))
(.node (.leaf [0xa480a460a440a42,0x437017f,0x773038b,0xd3105a1,0xb8107e9,0xd010b49,0xd1c0d1a0d20])
(.leaf [0xcf00af,0x5c90289,0x4af046f,0x8e106f1,0xcc10961,0xe5b0e3b])))
(.node (.node (.leaf [0x620061e061c061a,0x42f0137,0x73d0365,0x8e30563,0x9c90799,0xb130acb,0x507f503680d04])
(.leaf [0x21d0075,0x4d50225,0xc010429,0x88506bd,0xc2b090b,0xe330d2b,0xaf2]))
(.node (.leaf [0xec80ec60ec40ec2,0x39901c9,0xb9903c1,0x90305e3,0xba5082d,0xe5d0b95,0xd3e06500714064c0a7403cc082b])
(.leaf [0x32700cf,0x32f02f7,0x6e904d1,0x777073f,0xba109b1,0x955]))))
set_option maxRecDepth 5000 in
private def rowsBasePart124 : Table := (.node (.node (.node (.leaf [0x408040604040402,0x3ed0115,0xb13033b,0x5ab0553,0x9550785,0xc270a77,0x5056306dc0367])
(.leaf [0x17b0053,0x9a30203,0xbdd0405,0xda5066d,0xc6108c1,0xd2d0cf5,0x22d]))
(.node (.leaf [0xc780c760c740c72,0x20101b9,0x71103a9,0xd4905b9,0xa610801,0xdf10b69,0x5af071406dc0d3d07f5064b])
(.leaf [0x2fd00bd,0x40b02b3,0x7ff04af,0xb270717,0xc75098d,0xe53])))
(.node (.node (.leaf [0x830082e082c082a,0x1970167,0x7670377,0x75f057f,0x9b907c1,0xdc50b05,0x3b803b403b6])
(.leaf [0x563008b,0x5610259,0xc190441,0xab506d5,0xd090949,0xe790d99]))
(.node (.leaf [0x1cf0017,0x3a901d9,0x5f103e9,0xc5d0625,0xe1d085d,0xc270bdf,0x5b109bb08c101cb03a4054f0563])
(.leaf [0x20300e3,0x4d70307,0x7f304f3,0xac30753,0xa3909f9,0x5af04200192064b06e1000e00e600ee01ce02060164032c094402ae031600700198045004f807f907d604b40af40dfc0e740b280bd00e800ea00ef8028605c60ace0b160c5e0cbe0e960b680ba0078c0ba40c840ef402020c5a0288059805a8074807800960005800d8051004b60b3e021603a60aec03e3082f]))))
set_option maxRecDepth 5000 in
private def rowsBasePart2 : Table := (.node (.node (.node (.leaf [0x18001600140012,0x31f00e7,0x5f70307,0xcbb04f3,0xb3b0753,0xd1909f9,0x4405af064b06e1000e00ae01c6020e030e065602ae034007f907d6081e04b406cc0bd00c180dc803080ace0b680cf807e20a32078c096407480960026c00d801d804b606ce0406066e03a605be0aec0bdc0da4027002c8083a0a520563069407e40a340a9403c809a80be00da8056c0bce0c160390])
(.leaf [0x54f0017,0x55501d5,0x73b03e3,0x7e90631,0x8bf0867,0xe1f0bdf,0x5b109bb08c1]))
(.node (.leaf [0x860085e085c085a,0x32b0163,0xa110379,0x8cd057d,0xb2b07bb,0xee10b11,0x42804260422])
(.leaf [0x1730093,0x427025f,0x7930443,0x71506dd,0x997094f,0xea10d99])))
(.node (.node (.leaf [0x438043604340432,0x3a5011d,0x70f0347,0x77b0553,0xafd0785,0xd990a79,0x505b1036507160ea002e6031608be0abe0aee034a031403e807f803500945031a0759])
(.leaf [0x21f0057,0x3a5020d,0x6790411,0x97b0673,0xe9708bf,0xe1d0cf5,0x6500d0406e1]))
(.node (.leaf [0xcb00cae0cac0caa,0x46f01b7,0x77d03a5,0x7bf05bf,0xb690801,0xe450b65,0x56607f402e803e60aba06e1017802e20b3e0949])
(.leaf [0xdf00c7,0x59d02c5,0xb6504ad,0xdff0717,0xb930993,0xefb]))))
set_option maxRecDepth 5000 in
private def rowsBasePart66 : Table := (.node (.node (.node (.leaf [0x218021602140212,0x7e90101,0x4b90331,0x7570537,0x98d0775,0xd270a3f,0x5064b06dd07b60569])
(.leaf [0x1bf0037,0x5b901f9,0xad103f9,0xa790651,0xabb089b,0xf010c61,0x71401d001cb06dc]))
(.node (.leaf [0xa800a7e0a7c0a7a,0x8d5017d,0x78f038f,0x7b705a7,0xdd907e9,0xe2d0b45,0xda00d9a0d9e])
(.leaf [0x1c900b1,0xa4b0283,0xb43046b,0xacb06eb,0xe73095b,0xf030e3b])))
(.node (.node (.leaf [0x650064e064c064a,0x2ed013d,0x9e70367,0x9730563,0xb1f0797,0xc7f0acf,0x507f50368])
(.leaf [0x2510079,0x24b022b,0x697042f,0xacd06bd,0xe5f0917,0xe910d31,0xc82]))
(.node (.leaf [0xef80ef60ef40ef2,0x57701c7,0x5b903c9,0x64b05f3,0xc25082d,0xd470b9f,0x5af06500714064c0717])
(.leaf [0x65100d1,0x47502f5,0x82504cd,0xac10741,0xd3109b1,0xafd]))))
set_option maxRecDepth 5000 in
private def rowsBasePart34 : Table := (.node (.node (.node (.leaf [0x118011601140112,0x3d500ed,0x9750315,0x82d0525,0xe2f075f,0xc010a21,0xd3e071808be06e1064d])
(.leaf [0xb5002d,0x3ab01e3,0x7ff03ef,0x93b0643,0xc390879,0xda50c25,0x71401cf07f808c0054c]))
(.node (.leaf [0x968096609640962,0x1a70177,0x555038d,0x8b10599,0xa1507d5,0xb650b3d,0x970096a096c])
(.leaf [0x2b3009b,0x5990279,0x8390459,0x71f06e7,0xb6b0953,0xead0e1d])))
(.node (.node (.leaf [0x548054605440542,0x3bd012d,0x9c50355,0x8db055b,0xb63078b,0xc390ac1,0x50563])
(.leaf [0xd3006b,0x4b90219,0x627041f,0x9e10699,0xaed08e5,0xe250d0d,0xc85]))
(.node (.leaf [0xde00dde0ddc0dda,0x56f01bf,0x71103b9,0xc2705c7,0xb9b081b,0xdd90b81,0x5af0368024a03f2043a060209420a780ac00bd00c180d680d780e780ea0078c07c409640ba400d803a605e6010004200a5207f9031600b80208091a0ada0aea0cba00160406041606860e460e660204041c049407e40a340be00da8056c05e40d540622068206260bce0c160cee0173])
(.leaf [0x62d00c5,0x49502e5,0x6e104c1,0xa390729,0xc6109a9,0x3b3]))))
set_option maxRecDepth 5000 in
private def rowsBasePart98 : Table := (.node (.node (.node (.leaf [0x328032603240322,0x2910111,0x9a90339,0x595054d,0x99d077d,0xcf90a59,0x94201b805620d09])
(.leaf [0x5a10049,0x38f0207,0x6050405,0x83d0665,0xbff08b7,0xe950cbd,0x7140650]))
(.node (.leaf [0xb980b960b940b92,0x7b90199,0x3cd03a5,0x99105b1,0xa5307f3,0xe010b61,0x56606dd0090064e0d96064c0251])
(.leaf [0x2eb00b3,0xa6d02a5,0x7090499,0x8ad070d,0x9bd0975,0xeff0e9f])))
(.node (.node (.leaf [0x758075607540752,0x1890159,0x7610371,0x5bf0577,0xe5107b1,0xb290af1,0x14036906dd037003a80538038a03c20552077a0b3a0790030201cc0af002060412020804d800e809980b9800160156056e078e015202e907f9])
(.leaf [0x93008b,0xa0b0243,0xc110439,0xcf306cb,0xb5f093f,0xe690d59]))
(.node (.leaf [0x9d000d,0x4f901d1,0x7b703cf,0x9270607,0xbb10841,0xd6f0bc7,0x1804f407f3001403e8])
(.leaf [0x38f00d7,0x4d10301,0xb8104d9,0x94f074f,0xb8709c7,0xd1034a00780a180d3e07f20aba044e08be06e000760416064e010e]))))
set_option maxRecDepth 5000 in
private def rowsBasePart18 : Table := (.node (.node (.node (.leaf [0x98009600940092,0x7b700e7,0x96b030b,0x8f5050d,0x795075d,0xd6b0a0b,0x1405af007803e8042008880a18008a0172031a034a008c010c02e40314036404bc071408bc0a740d04007202e20602094209ba0c820d9201cc046404f406040b3c00cf])
(.leaf [0x555001d,0x37701df,0x43703ef,0x8290639,0xe290871,0xdb50c05,0x393]))
(.node (.leaf [0x8e008de08dc08da,0x3010171,0x54b0383,0x773058b,0xb1707c7,0xce10b29,0x6d406d606d8])
(.leaf [0x31d0095,0x42d026d,0x6b3044b,0x9e706df,0xd0f094f,0xe010de9])))
(.node (.node (.leaf [0x4c004be04bc04ba,0x3d10129,0x64d034d,0xbc30553,0x96d078d,0xc270aa7,0x9720b4004160aee0b3e0e2604f8041403160d0607f3])
(.leaf [0x43d005d,0x833020b,0x7530413,0x95f0687,0x91708df,0xd4d0d05,0x65001d000d1]))
(.node (.leaf [0xd500d4e0d4c0d4a,0x20501bd,0xb8103a9,0xd5105c1,0xa790809,0xd050b7d,0x5af0368071409c00a180ef8071707f40350007603f6043e069606a6082e0c8600f0020802d206920b7e0e260a320bca0ef20744077c099c0c840162032a07aa03e609ba])
(.leaf [0x1fd00c5,0x6d902e1,0x7d504b5,0xaff071f,0xc9909a1,0x5c3]))))
set_option maxRecDepth 5000 in
private def rowsBasePart82 : Table := (.node (.node (.node (.leaf [0x2a0029e029c029a,0x7ed0105,0xb07032f,0x58d0545,0x7af077f,0xcef0a4f,0x24c064b0d3e06e103e8008e0b7c022a07e20a320a180ba0049603c20204049407e40a3403d009a805c80b7a0391])
(.leaf [0x40b003b,0x58f01ff,0x77d03fd,0x9990659,0xb0b08ab,0xcdd0c9d,0x1cd06dc06510368008c0090045000fc0406066e052005bc018e0446010008fc0b4402ae08060554059c0ad40a700212036e0b46020005c0006e056e078e04140760079808040666010c]))
(.node (.leaf [0xb100b0e0b0c0b0a,0x3390191,0x5ab0393,0xd3705a7,0xbe507ed,0xdeb0b53,0x5036906dd0096034e03ce04b604be051609060a160aa60b260d3e0dfe064d])
(.leaf [0x74b00ab,0x8c90291,0x4d10481,0x8850705,0xb810969,0xee70e5f])))
(.node (.node (.leaf [0x6d806d606d406d2,0x74f0147,0x5610371,0x78b056b,0xb0107a9,0xb170adf,0x507140368064f])
(.leaf [0x1f90081,0x9e3022b,0x6570437,0x71706cf,0x96b092b,0xef70d3f]))
(.node (.leaf [0xd10009,0x36d01cd,0xb9b03c3,0x93d05fd,0xb950835,0xe1d0bb5,0x5b101260af60dfe0b640b6c0b9c0cf40e54078a09620ba20606082e031404f4052400b800e801d002080d720e72008a0172004604500af00e00041c06dc06e103680494054c0acc0b140bbc0830059805a80748078003e6073e0b6e0b7e0e760ad00b180af203a205ba075202f4033c0744077c099c0b3c00d606ee07360aee049203cd])
(.leaf [0x21500d5,0x6ed02f5,0x6dd04d5,0x9490749,0xeeb09b3,0xba7]))))
set_option maxRecDepth 5000 in
private def rowsBasePart50 : Table := (.node (.node (.node (.leaf [0x198019601940192,0x2310101,0x98b031b,0x55f052f,0xaf90771,0xd4d0a35,0x505af])
(.leaf [0x3ff002f,0x5af01ef,0x64d03f5,0x82b064b,0xc850885,0xe750c35,0x3a2049405c40b140c24082c038c064f05a8074807800d8609b60b7e0eb60db20e9a008e03a605be007809480b800d500ea0010e02ac03d0008c044e00fc026c0496078a098e0e560ba406920b18078c075a075c02e3]))
(.node (.leaf [0x9e809e609e409e2,0x4990179,0x6c10391,0x8b5059d,0x82d07e5,0xe290b41,0xb600b5e])
(.leaf [0x2f500a5,0x8b7027f,0x8770467,0xdef06e7,0xb490961,0xe590e39])))
(.node (.node (.leaf [0x5c805c605c405c2,0x2d70137,0x5310369,0x5c10569,0x7cf0797,0xc6f0ac7,0x507f50368071401d005500688094809e80a780ea0094604120aea0496082e0dfe0aba0c820dfa06dd])
(.leaf [0x5c90071,0x4c10221,0xbf3041b,0x9d706af,0xe590901,0xe8d0d15,0x4c1]))
(.node (.leaf [0xe680e660e640e62,0x36b01c3,0x7a503bd,0x9b505d5,0xa390831,0xdf90b91,0x5af0368064d])
(.leaf [0x1cf00cf,0xac102e9,0xc8904c1,0xa590739,0x9df09af,0x425]))))
set_option maxRecDepth 5000 in
private def rowsBasePart114 : Table := (.node (.node (.node (.leaf [0x3b803b603b403b2,0x1310119,0x62d033d,0x9610551,0xd85077d,0xc250a6d,0x5064b])
(.leaf [0x4310051,0x5950205,0x7970407,0x83d066d,0xb1708bf,0xe170cef,0xd3d]))
(.node (.leaf [0xc180c160c140c12,0x55f01af,0x6cb03a3,0x8a105b9,0xe7507f5,0xcff0b67,0x5af071406dd010e052e054e075609e60b3e017807f5])
(.leaf [0x60d00b5,0x64d02ad,0xc63049b,0x9090719,0xd0f097f,0xbbb])))
(.node (.node (.leaf [0x7e007de07dc07da,0x3fd015d,0x5710379,0xbe50575,0xba307b3,0xdb70af7,0x1e001dc01de])
(.leaf [0x2af008f,0x885024d,0x7c90441,0x8af06d7,0xb3f0947,0xee50d85]))
(.node (.leaf [0xa90019,0x21101d9,0xbad03d5,0x957061f,0xabb0853,0xda10bd9,0x7f8083000180128010c08bf044e03cd])
(.leaf [0x33300db,0x33d0305,0x8b904f1,0x78f0757,0xbbd09e5,0x7b603f4082c0c2605c60ace0b16078a07c20ba2020408300206052803f207900da4077b]))))
set_option maxRecDepth 5000 in
private def rowsBasePart10 : Table := (.node (.node (.node (.leaf [0x58005600540052,0x3cd00e5,0xadd0305,0x9170507,0xd810759,0xa610a11,0x505af025106dc])
(.leaf [0xc3001b,0x96301d3,0xac103e9,0xa55062d,0x8b5086d,0xe770bef,0x5b101cb]))
(.node (.leaf [0x8a0089e089c089a,0x77b0163,0x6e90381,0xd1d057d,0xe5f07bf,0xee90b19,0x57405760578])
(.leaf [0x24d0095,0x5b70267,0xb1d0445,0x87906e1,0xb63094b,0xe7d0db5])))
(.node (.node (.leaf [0x480047e047c047a,0x2850125,0x4f3034b,0x8c90559,0x7c3078b,0xd450a8d,0x505630368064c])
(.leaf [0x5b10059,0x49f020f,0xbe90411,0xcab0673,0xb1d08d5,0xe1d0cfd,0x6500ac00c84022a03e80569]))
(.node (.leaf [0xd100d0e0d0c0d0a,0x7e101b9,0xa5703a7,0x99d05bd,0x8410809,0xcff0b77,0x5af03680714064c06500d3d])
(.leaf [0x1bb00c3,0x5b102d9,0x51904b9,0x90f071f,0xb63099b,0x21b]))))
set_option maxRecDepth 5000 in
private def rowsBasePart74 : Table := (.node (.node (.node (.leaf [0x260025e025c025a,0x3750105,0x727032f,0x5990541,0xb070777,0xd2d0a45,0x7580b3c0b400b64095e0b6609a9])
(.leaf [0xbb003b,0x3910201,0x60f03ff,0x6ab0653,0xc9f089f,0xde30c83,0x1d0001404f406dc08bd082a07f80076024e02ae082e0a760d040717]))
(.node (.leaf [0xad00ace0acc0aca,0x3f90189,0xa410391,0x98505a5,0xa4107f1,0xd0d0b4d,0xeb60eb80eb4])
(.leaf [0x37700af,0x4410291,0x4d90479,0x73106f9,0x9bb0963,0xecf0e4f])))
(.node (.node (.leaf [0x698069606940692,0x1790149,0x38f036f,0x5b7056f,0xaed079d,0xb0d0ad5,0x24c09480b480b80008e022e02ae036e03a60946010e0876038c052c032003d004b806d002ac0bec0c24007800c8022a08740a520bea024e062e008a044a052e05a60746077e02d6031e0214036c03a40076069600e8098e0b6602d2069205ab])
(.leaf [0x4c10079,0x3e7022f,0x7c10431,0xad306c3,0x9590929,0xe570d37,0x7f5]))
(.node (.leaf [0x490009,0x20501cd,0x7af03c7,0x96905f9,0xe7d082d,0xd550ba5,0x5af06500714])
(.leaf [0x1d300d3,0x5ed02f5,0xb7f04cf,0x77d0745,0xba509b5,0x7f7]))))
set_option maxRecDepth 5000 in
private def rowsBasePart42 : Table := (.node (.node (.node (.leaf [0x158015601540152,0x21d00f5,0x497031f,0xba90529,0xae90769,0xd070a27,0x630033a00c6073800cf0136028e00e403a40134028c037003a8062e0204036c0734038b])
(.leaf [0x1b5002d,0x97901e9,0x43f03f7,0x6990651,0xabb0883,0xc5d0c35,0x71401d001cf07f8]))
(.node (.leaf [0x9a809a609a409a2,0x3e30173,0x5a7038f,0x5df059f,0xbcd07d5,0xcf50b3d,0xa740a780a76])
(.leaf [0xc300a3,0x577027f,0x4b90469,0xa3f06e7,0x9a3095b,0xeb90e29])))
(.node (.node (.leaf [0x588058605840582,0x71f012f,0x7510361,0xbd10561,0xe45078d,0xd990ac1,0x5064c036809480d0706dd])
(.leaf [0x205006d,0x9b70217,0x82b041b,0x84106a9,0xb0108f9,0xd4d0d15,0xd09]))
(.node (.leaf [0xe200e1e0e1c0e1a,0x1fb01c3,0x5a703bf,0x90d05cd,0xb8d0825,0xd1f0b87,0x5af03680650064c])
(.leaf [0x77f00c7,0x6df02e7,0x8e704bf,0xb0f072f,0xd5309a3,0x76b]))))
set_option maxRecDepth 5000 in
private def rowsBasePart106 : Table := (.node (.node (.node (.leaf [0x368036603640362,0x417010f,0x4c10341,0x7490551,0xb15077d,0xc1d0a5d,0x5064b0563])
(.leaf [0xe90051,0x4930203,0x66d0405,0x9c90669,0x90908c1,0xe7f0cdf,0x4bd]))
(.node (.leaf [0xbd80bd60bd40bd2,0x7bb01a3,0x57103a9,0x5e705b7,0xbc107f9,0xb9d0b65,0x5af071406dd010e052e075609e60b3e017807f50d3d083103cf])
(.leaf [0x36900b9,0x41902b1,0xb5f0497,0x8a50715,0xc950975,0xe3a])))
(.node (.node (.leaf [0x7a0079e079c079a,0x4690159,0x3a70377,0x78d0575,0x9d907b9,0xde30aeb,0x10801060104])
(.leaf [0x173008b,0x5ab024b,0x6a5043d,0x71106d9,0x98d0945,0xd990d79]))
(.node (.leaf [0x3ab000b,0x7f501cd,0xba503cd,0x7fb060b,0xa77084f,0xd990bd1,0x5b1065103650b3c00e403a405bc00d6098e0b6608fc0b8c0c1c0edc0580079009a8078a075c07940030038004d000c4077e00d80758077807b0079209460b3a0563])
(.leaf [0x67900d9,0x6f90301,0x8a504dd,0xae10751,0xb9309d3,0x4405af06e103f4043c082c09440bf60d960bee0c26028605c6087609060ace0b16012403cc04b404bc051409040d720b440b6c0b7c0070015802f8034004500b680b700ba0078a07c209620ba2083a0a52036a03a205ba075209420d7604180156006c032a02040b0600c601ce01d0083008400a580bf00e7804b60bf40e74028805980780096001c80208018603060b260077]))))
set_option maxRecDepth 5000 in
private def rowsBasePart26 : Table := (.node (.node (.node (.leaf [0xd800d600d400d2,0x32d00ed,0x4f90319,0xb9f0517,0xad5075d,0xd3d0a15,0x21e041a064a010e041e044a07f8012403cc064e09bd])
(.leaf [0x1af0027,0x80701df,0x75303eb,0xd910639,0xadb0873,0xd990c19,0x98b]))
(.node (.leaf [0x928092609240922,0x4eb016b,0x3bd038d,0x7750595,0xb2907d1,0xef70b27,0x7b207b807b6])
(.leaf [0x5af0097,0x66f026f,0x8310451,0xaef06df,0x9af0957,0xe330e13])))
(.node (.node (.leaf [0x508050605040502,0x7190129,0x9c10351,0x5b7055f,0xacb078b,0xaf30abb,0x3a205ba0bd2039007b80c1000b800b6078e04f804b40b660a58078a0a520b440b7c04080670076007980e480406066e021803a805c00b900e380ee000c804b60b64078009a009520b8e0d26058009a80b480b800d220e3201cd])
(.leaf [0x1910069,0x3a70217,0xaeb0413,0x82d0695,0xbcb08db,0xe9f0d07,0xa19]))
(.node (.leaf [0xd900d8e0d8c0d8a,0x38f01bf,0x71b03ab,0x7c705c7,0xbd5080d,0xd490b81,0x5af06dc08bd0651071707f3])
(.leaf [0x33d00c5,0x32d02e5,0xb6304b3,0x8c50725,0xb6709a7,0x103]))))
set_option maxRecDepth 5000 in
private def rowsBasePart90 : Table := (.node (.node (.node (.leaf [0x2e802e602e402e2,0x235010d,0x50b0333,0x85d0545,0x94d077d,0xaa30a53,0x9420d9206dc0d3e05620369])
(.leaf [0xe10049,0x82701ff,0xbd503fd,0x7ff065f,0xad908b9,0xf050cb5,0x71406dc]))
(.node (.leaf [0xb500b4e0b4c0b4a,0x41b0193,0x55b039b,0x88305ab,0x83d07f5,0xcef0b5f,0x5036805b1])
(.leaf [0x1cb00b3,0xa5f0297,0xb610491,0xb190709,0x9c5096d,0xe810e79])))
(.node (.node (.leaf [0x718071607140712,0x757014f,0x6f10371,0x94b056b,0xb0b07ab,0xb1f0ae7,0x507140368])
(.leaf [0x2590089,0x5ed0235,0x7af0437,0x8a506cd,0xc650935,0xe450d4d]))
(.node (.leaf [0x3d000d,0x3a901d1,0x5c703cf,0x64f0607,0xa590841,0xd850bbd,0x5b10650064c0128035004c00b28010c02e4036404bc0a740d0405c60c2603cd])
(.leaf [0x2f700d7,0x33502fd,0x7e704d7,0x77b074b,0xc8309bb,0xf07]))))
set_option maxRecDepth 5000 in
private def rowsBasePart58 : Table := (.node (.node (.node (.leaf [0x1d801d601d401d2,0x3a300fb,0x6570327,0x92d052d,0x9330773,0xc0d0a3d,0x14064b06dd0719098c0b640b9c0cf40e540bf60220079007c8096809e00ba8007803e804200ac00db80e80019602d6031e005202d2038a03c2055205da098a02ae0524083a0a520db20b8001e6036e03a605be075608e60a3200fc026c06040744077c0924099c0b3c00a800c801f002000dfe010e01be038e052e05560b3e02f2033a08e206bc07040af4095609ae00180070019801a802f8034004500498031201ca052206ea073207b9])
(.leaf [0xb50035,0x3bd01f5,0x78f03f7,0x9bb064b,0xac90899,0xe7d0c5d,0x71401cb06dc0650064f]))
(.node (.leaf [0xa380a360a340a32,0x3490181,0x727038f,0xd2d059d,0xb7d07e5,0xcfd0b45,0xd040d080d06])
(.leaf [0xc700af,0x5c50285,0xc390469,0x8dd06ed,0xcbb095b,0xed90e39])))
(.node (.node (.leaf [0x608060606040602,0x42b0133,0x6df0367,0x8970567,0x9c30793,0xb070acf,0x507f503680d040714])
(.leaf [0x1b70077,0x9c10221,0x8390429,0x85306bb,0xe570907,0xedd0d25,0x888]))
(.node (.leaf [0xeb00eae0eac0eaa,0x39301c3,0xb9503bd,0x7bf05e7,0xb610831,0xd390b99,0x71403cc0129])
(.leaf [0x30f00cf,0xac502ed,0x6e304cb,0x773073b,0xb9b09ab,0x7b5]))))
set_option maxRecDepth 5000 in
private def rowsBasePart122 : Table := (.node (.node (.node (.leaf [0x3f803f603f403f2,0x38f0117,0x9ab033b,0x59f0557,0x7b50785,0xbf10a79,0xb3e0de80b4007f3])
(.leaf [0xe70057,0x82f0207,0xae10409,0xa390671,0xc5d08bd,0xeb50ced,0x24c]))
(.node (.leaf [0xc680c660c640c62,0x1fd01b5,0x70d03a5,0xc1905b9,0xa110801,0xd410b69,0x5af071406dc064c06500d3d07f500b4038c073c0179])
(.leaf [0x1e100c1,0xa7702af,0x70d04ad,0xaf70717,0xb8d098d,0xe1b])))
(.node (.node (.leaf [0x820081e081c081a,0x897015f,0x7510379,0x5d7057f,0x9b107c1,0xc670b07,0x37803760374])
(.leaf [0x317008f,0x4270257,0xb190441,0xa1f06d7,0xd050945,0xe730d93]))
(.node (.leaf [0x1cb0013,0x3a501d5,0x42f03e7,0xa4d0625,0xac7085f,0xc150bdd,0x5b107f3])
(.leaf [0x1ff00e7,0x4d30303,0x73304f3,0x9670757,0xbc709ef,0x505af0251064a06e1]))))
set_option maxRecDepth 5000 in
private def rowsBasePart6 : Table := (.node (.node (.node (.leaf [0x38003600340032,0x34700e7,0x9630303,0x90f04ff,0xb590759,0xbdb0a03,0x5af023002d2064b07280af0001000b800f001d00b680d78078c0aea00d802ae066e021603a6083a0a34060808400da801ce022a0a320d7200d203900563078a008f])
(.leaf [0x590021,0x7fb01d3,0x7f303e3,0x9390631,0xad10869,0xc270bef,0x5b107f5]))
(.node (.leaf [0x880087e087c087a,0x4410169,0x57d037d,0x9610581,0xb9907c1,0xc9b0b13,0x54805460544])
(.leaf [0x1950095,0x893025b,0x7b30443,0x72706df,0xb3b094b,0xec70d9f])))
(.node (.node (.leaf [0x458045604540452,0x7110121,0xb1f0347,0x86b0553,0xd9d0785,0xd490a81,0x64a0a16034a064c0715])
(.leaf [0x4370057,0x3c5020d,0x7eb040b,0x9a70677,0xae108c9,0xe370cf7,0x82e02080c2808c10830049602020c26]))
(.node (.leaf [0xcf00cee0cec0cea,0x4c101b9,0x79503a5,0x8fb05bb,0xdef07ff,0xd090b71,0x7b608bd082e01260b260dfe083003d1])
(.leaf [0xe900c9,0x44f02d7,0x50304b3,0x8b90721,0xc8f0997,0x10b]))))
set_option maxRecDepth 5000 in
private def rowsBasePart70 : Table := (.node (.node (.node (.leaf [0x238023602340232,0x2770107,0x6a7032f,0x85f0537,0xac50775,0xc0b0a43,0xcc00cba06820688095f])
(.leaf [0x56f0037,0x99901f9,0x4390401,0xc890651,0xb07089f,0xdfb0c7b,0x4f207f202e408bc064b0abe03e60717]))
(.node (.leaf [0xaa80aa60aa40aa2,0x34b0183,0xa390391,0x8d105a9,0x83307eb,0xb7d0b4d,0xe260e280e24])
(.leaf [0x30500ad,0x2d90291,0x4b30473,0xd1306eb,0xeb90961,0xec30e43])))
(.node (.node (.leaf [0x670066e066c066a,0x1650145,0xb3f0367,0xbd90569,0xb7f0797,0xda30acb,0x10c036404d4054e04180412082a0a4a03e70b800e46077a043c082c0b16033a0916043a06820158034001520524030205220ba80e4205a80780068801640c040d840b7a0550])
(.leaf [0x2b10079,0x26d022d,0x777042f,0x70b06c3,0x9430923,0xe350d35,0xde3]))
(.node (.leaf [0x170007,0x95301c3,0x70903c9,0x7e705f7,0xdfd082d,0xd4b0ba3,0x5af064d083003cc01280717])
(.leaf [0xeb00d3,0x4bb02f3,0x89504cd,0xb410741,0xb7d09b5,0xd9d]))))
set_option maxRecDepth 5000 in
private def rowsBasePart38 : Table := (.node (.node (.node (.leaf [0x138013601340132,0x6af00ef,0xaef0317,0x9070527,0x79d0765,0xd9f0a1f,0x21e02d605660d3e0072022a041a064a02d803200350071806dc01100230042004300628063007f80ac00bc0008a044a049201ce054e0716])
(.leaf [0xd10031,0x56701e7,0x42d03f5,0xa6b0643,0x8d7087f,0xe7d0c25,0x1cf05a4077c0cec0cbe04740a7404b80a180bf8082c0a4c03f2043a06820a4a09b20b420b7a0cba0cea0b620d0900c8098c0c7c0692082a0d92056007500bd00c180ef800e20852044a0ef20bf20e160e360b6605a807800e58069407d403a40a16]))
(.node (.leaf [0x988098609840982,0x2f90179,0x55f038f,0xbf70597,0xb6507d5,0xced0b3d,0x9bc09c009ba])
(.leaf [0x5b3009b,0x435027d,0x4970467,0x8d306e3,0xd130953,0xe450e25])))
(.node (.node (.leaf [0x568056605640562,0x4290131,0x53d035d,0x9410561,0xda3078b,0xc630abb,0x507f509600b40046603650d09])
(.leaf [0x173006b,0x83f0217,0x7710421,0xdb70697,0xb2908e9,0xe470d0f,0x34a]))
(.node (.leaf [0xe000dfe0dfc0dfa,0x94b01bb,0x59d03bd,0x79905d1,0xa8b0823,0xe390b81,0x5af071502aa0a780b280d780e78078c0ba408760450083a0a5207f90960018805280158015602ae04b60b3e041408e201be057007900e2808e60dfe05240a340a9401c0039003c809a80da8056c0d07])
(.leaf [0x63700c7,0x64d02e5,0x88304bb,0xd4d0725,0xce109a9,0x593]))))
set_option maxRecDepth 5000 in
private def rowsBasePart102 : Table := (.node (.node (.node (.leaf [0x348034603440342,0x3ab010b,0xb110339,0x5a7054f,0xad5077d,0xd890a59,0x5064b07b6])
(.leaf [0xc90051,0x3c30203,0x6650405,0x94d0665,0xcb908b9,0xf090cc1,0x31d]))
(.node (.leaf [0xbb80bb60bb40bb2,0x457019f,0x56703a7,0xc0f05af,0xb3d07f5,0xb930b63,0x5af008c02e4031404bc04d407240a740aec0d040de4010e01be07560b3e0078012803e8041800180090009802f803400450049804960c5e0320035004b804c0051806d00aa80b28064e0d96098c09bc0aa40b640b6c0b9c0ef401cc041404640604064c082c083c0a4c0a540b3c0e7401ca0312034a0522001405940cec0e7806820a4a022a060207e20a32025003cf])
(.leaf [0x31700b7,0x2d902b1,0x8310499,0xb1d070d,0xb550975,0xefd0ecd])))
(.node (.node (.leaf [0x778077607740772,0x4150155,0xb45036d,0x5d10579,0x9a307b3,0xcc10af1,0x5036906dd03ce03f4043c0bf80b640e540a260b7e0d4e003001e80260037003a805380898097807e20a320bf0038a03c2055207b20742077a099a0b3a083a0db20198041e0220079007c80ba80302026c0b1601cc0ae00af0020607e60a360a4e0bf6006a04020412066a0682020804d8072800e804300db8049007f009980b980cf00bec0016006e01560196000e056e057e078e07c609a601520134028c02e9])
(.leaf [0x153008b,0x41b024b,0x6510441,0xdd306cb,0xc7f093f,0xd990d69]))
(.node (.leaf [0x2ad000d,0x57d01cd,0x7d103d1,0x9790609,0xe110841,0xc130bcb,0x5b10651036500e403a405bc098e0b6608fc0b8c0c1c0edc0580079009a8078a075c07940030038004d007580b6800c409460b8e07760792077e077807b00563])
(.leaf [0x66f00d7,0x6390301,0xca104d9,0x9590751,0xca109c9,0x350034a09ba0a180d3e0717]))))
set_option maxRecDepth 5000 in
private def rowsBasePart22 : Table := (.node (.node (.node (.leaf [0xb800b600b400b2,0x21300eb,0x34f0317,0x7170517,0x9710761,0xbc10a19,0x1401ee02d6038e0556056607b6098e0d3e0072022a041a064a0090017802d80350008c02e4031404bc08740a740d040126034e03ce04be0a160aa60b260288049804f8055008780c280018023004200628063000760286028e01b80390053005580b4007f800cf])
(.leaf [0xad0025,0x47901e1,0x60103f1,0x9890639,0x8db0873,0xe470c0f,0x5db]))
(.node (.leaf [0x908090609040902,0x423016b,0x7130383,0x8990591,0xe6707c7,0xdfb0b23,0x74e0750074a])
(.leaf [0x34d0095,0x5bd026d,0x7cf044f,0xa7906e1,0x99b0953,0xe950de5])))
(.node (.node (.leaf [0x4e004de04dc04da,0x44f0127,0x717034f,0x5a3055b,0x9b7078f,0xd410aa9,0x8a022a036a03a2053205ba0390055807b800b801c000b601560536056e078e095e096604f808780c600cc00e980234028c008e0316087604b406cc0dfc0b660d9801d0084009f80a500a5801520682043c06a4078a09620850083a0a520b7c0e9c040806880b28031807e200fe022e04060926043a0a4a021803a805c00dfa09b40e380ed80c380ea00c5c01ce04b606ce0c3609220b620cea0e9406ec0949])
(.leaf [0xd70067,0x9af020f,0x7a10419,0xcbd0685,0xae108e1,0xe270d07,0x351]))
(.node (.leaf [0xd700d6e0d6c0d6a,0x36701bf,0x57b03ab,0x78d05c5,0xbcb0803,0xd0f0b7f,0x5af036808bd0126031e06de083006e107f4064f00e4069201e801780aba0943])
(.leaf [0x2fd00c5,0x31d02e5,0x84104b9,0xd45071d,0x9d309a3,0x79b]))))
set_option maxRecDepth 5000 in
private def rowsBasePart86 : Table := (.node (.node (.node (.leaf [0x2c002be02bc02ba,0x1290111,0x4af0337,0x7470547,0x943077b,0xe950a4d,0x5064b07b60d3e038e0367])
(.leaf [0xc30043,0x5bf01ff,0x8110401,0xa7f0657,0x90f08b7,0xde50c9d,0x1404f407f4010c03640551]))
(.node (.leaf [0xb300b2e0b2c0b2a,0x8fd018d,0xa490399,0x78505ad,0x82b07f3,0xb8f0b5f,0x50350064f])
(.leaf [0xd300b3,0x57d0295,0x6c7048f,0x89f0707,0xcf70967,0xefd0e6d])))
(.node (.node (.leaf [0x6f806f606f406f2,0x8690149,0x6c7036f,0x863056b,0x98f07af,0xb290ae1,0x56203680d080284049405c409040c24007802b002e803f804400698083009480d9800ee020e02e6082a0b3a06e10126031e04be09060b3c0bf402d2038a03920b7002d803200076041e09dc04200430028807800bf609e00946026c05bc05e4077e099e027006920a77])
(.leaf [0x13f0087,0x2910239,0x78f0437,0x89b06cb,0xb510931,0xe5f0d47]))
(.node (.leaf [0x2550005,0x39f01cf,0x5bd03cd,0xa110601,0xc310839,0xbf90bc1,0x5b107140650064c06dc03cd0830])
(.leaf [0x21f00d7,0x95702f7,0x72504d5,0xad10749,0xb8709bf,0xd57]))))
set_option maxRecDepth 5000 in
private def rowsBasePart54 : Table := (.node (.node (.node (.leaf [0x1b801b601b401b2,0x2710101,0xaf5031d,0x7510531,0x7ab0773,0xa8b0a3b,0x64b098c0b640cf407900552098a0a52036e03a60a32077c00c801f005560956082c09f40a54059406ea07b900e601c60206020e0208037003a801d4043800c206940b620cf206ec038d])
(.leaf [0x5b0033,0x98d01ed,0x74503f5,0x943064b,0x8f90899,0xca10c49,0x6dc08bd0178082c082e03e805500b220717]))
(.node (.leaf [0xa100a0e0a0c0a0a,0x8bf0177,0x6e90391,0x9b105a1,0xa3507e5,0xb7b0b43,0xbe80be40be6])
(.leaf [0x74300a3,0x43b0283,0xb3f0467,0x72906f1,0xb810961,0xea10e39])))
(.node (.node (.leaf [0x5e805e605e405e2,0x38f0137,0x5550365,0x7850565,0x9790799,0xea30ac3,0x507f502ae036e03a605be00b2056a078a0962074009280b680496082e098e09960c82010e02e6071600b4038c0554073c0098032003d006d009080a180aa80af8060207e20a3202ac0aa40c2402e801f00596077e044e049405c4086409040b140ba40c8402020212036a03a20d88017805280945])
(.leaf [0x1250075,0x5b10221,0x7850425,0x85106b9,0xbf70907,0xd550d1d,0xabe]))
(.node (.leaf [0xe900e8e0e8c0e8a,0x38b01c3,0xa8503bd,0x90b05db,0xa510831,0xd2d0b95,0x369071407f206dc])
(.leaf [0x20f00cf,0x6e702ef,0xc8f04c7,0xd610739,0xb7109b1,0x5ad]))))
set_option maxRecDepth 5000 in
private def rowsBasePart118 : Table := (.node (.node (.node (.leaf [0x3d803d603d403d2,0x37f0117,0x705033d,0xced054d,0xe33077b,0xaa70a77,0x505630a740b3e007807f80b400e280d07])
(.leaf [0xcf0057,0x5c70207,0x7e90409,0x957066f,0xbc108c1,0xe370cef,0x65007f30d04]))
(.node (.leaf [0xc380c360c340c32,0x94101b1,0x6f503a5,0x99705b7,0x8390801,0xd370b67,0x7140c880e000af2094406940c8406960dfe031c0948098b])
(.leaf [0x75900b9,0x8e502ad,0x6d504ad,0xaa50715,0xd390989,0xcfb])))
(.node (.node (.leaf [0x80007fe07fc07fa,0x4cf015f,0x6d50375,0xd190579,0xe5707b7,0xdff0af7,0x220021c021e])
(.leaf [0x2e7008f,0xa17024f,0x84f043f,0x8b906d9,0xc830943,0xdb70d97]))
(.node (.leaf [0xc90019,0x37501d5,0x41b03e3,0x7d90629,0x893085b,0xe330bd3,0x5b10714])
(.leaf [0x3c900e1,0x34d0305,0x52904f9,0x95b0753,0xd0709e7,0x7b603f4043c082c0c2605c60ace0b160d720e240b68078a07c209620ba20b5807520d76020400c6083005a8078001c602060656052802c80b6200c803fc077e037e07f00998011201c205a2078c002001d805a00870096803f2043a02c203780a6001d2083205740996082602480d000790]))))
set_option maxRecDepth 5000 in
private def rowsBasePart14 : Table := (.node (.node (.node (.leaf [0x78007600740072,0x69700e7,0x347030f,0x71f050f,0x78d075d,0xbe70a0f,0xd3e03e806500a18017208bc064a02e807f8008f])
(.leaf [0x1d7001f,0x21701df,0x42703ef,0xc690631,0xad90871,0xe7f0bf7,0x93]))
(.node (.leaf [0x8c008be08bc08ba,0x89f0167,0xb590381,0x7970587,0x9c107c9,0xcbf0b27,0x5ae05b005aa])
(.leaf [0x2d50095,0x3f5026d,0x6710451,0x8c506dd,0xc9d094d,0xdff0dd7])))
(.node (.node (.leaf [0x4a0049e049c049a,0x2c90129,0x525034d,0x9630553,0x963078b,0xc130a93,0x5056307f5])
(.leaf [0x163005b,0x59d020d,0x6830413,0x8050685,0xc7908d9,0xec90d01,0x65001d0010c]))
(.node (.leaf [0xd300d2e0d2c0d2a,0x1f501bd,0xa6103a9,0xc2105c1,0xa030803,0xba10b81,0x5af03680714064c065007f5])
(.leaf [0x1f500c5,0xaa302d3,0x71504b5,0xa810721,0xb93099b,0x3cb]))))
set_option maxRecDepth 5000 in
private def rowsBasePart78 : Table := (.node (.node (.node (.leaf [0x280027e027c027a,0x40f0107,0x99f032f,0x89d053d,0xb670777,0xbcd0a4d,0x6dc010c0369])
(.leaf [0xd7003f,0x4cb01fb,0x6590401,0x96b0653,0xe3908a1,0xdfd0c85,0x1cd08bd06510906099004d8072809b809e00b800d50094605bc05e4019603b6077e099e06920d070136038c03f2043a01ee01fe082d]))
(.node (.leaf [0xaf00aee0aec0aea,0x78f0187,0xb690391,0xc0305a3,0xb4d07ed,0xe210b51,0xf080f04])
(.leaf [0x5fb00ab,0x5590291,0x8590479,0xad706f7,0xb4d0965,0xedd0e55])))
(.node (.node (.leaf [0x6b806b606b406b2,0x4030143,0x3a7036f,0x5c90571,0xb87079f,0xd8b0ad3,0x5071403680d09])
(.leaf [0x6510079,0x5690231,0xb05042d,0x70306cb,0xb410929,0xe550d3d,0xb3e]))
(.node (.leaf [0x950005,0x21501cd,0x7c903c9,0x65305fb,0xa5d0835,0xe010ba9,0x5af0714])
(.leaf [0x1dd00d5,0x6bd02f5,0x51904d9,0x9410749,0xc8109b9,0x9bf]))))
set_option maxRecDepth 5000 in
private def rowsBasePart46 : Table := (.node (.node (.node (.leaf [0x178017601740172,0x12700ff,0x6990321,0x54d052d,0x7a90771,0xbcf0a37,0x84021e02d6038e03c6055607b608d608f6098e0c0e007202d8074007f8044a01ce012603ce04be0aa60b26036804c004d80728087808c809e80de8028405c408740c240cbc01d00cc002880530059805a80780096009e60e76003000b800e80208031003280658007602ae03f6043e06060696082e09460c860d9602ac0aa40bec0b7e0d4e0e260e9e0563])
(.leaf [0x1e7002f,0x3b901f1,0x64303f3,0x6a90651,0xaf50885,0xc810c39,0x650008c02e40a740d040a16008e0d3e064c064a]))
(.node (.leaf [0x9c809c609c409c2,0x44f0177,0x5b10391,0x78105a1,0xbd307db,0xde50b3d,0xafe0b000afa])
(.leaf [0x1b500a5,0x5a10281,0x7f30463,0xd0b06e3,0x9b7095f,0xec70e2f])))
(.node (.node (.leaf [0x5a805a605a405a2,0x28b0133,0x38f0367,0x5af0567,0x7c50795,0xe9f0abf,0x507f5071405800b8009780b700d50056700b2056a078a09620aea0d7200b401b4038c077e010e02e6031604be071607260aee03800212036a03a20a180bf80d88060207e20a3202e80318024e041e062608640b140c5c018403040ada0142043a062205600750034e040806700c5e0bde0e7e00fc0072041a0bf20e7a057005e8079007c80a5203c4003600d605e20abb])
(.leaf [0x44f006f,0x3cf021f,0xaf3041b,0x83306ab,0xb0f08ff,0xe310d19,0x6df]))
(.node (.leaf [0xe480e460e440e42,0x20b01c3,0x5e103c1,0xc2d05cd,0xc1f0827,0xe070b87,0x5af0368064d07f902020078028800e605c605e604160c2605e20173])
(.leaf [0xef00cf,0x94702e7,0xb7104c1,0x8e70737,0xe8109a9,0x16d]))))
set_option maxRecDepth 5000 in
private def rowsBasePart110 : Table := (.node (.node (.node (.leaf [0x390038e038c038a,0x6e10111,0x4d90341,0x8bd054d,0xb7d077d,0xd350a5d,0x5064b0367])
(.leaf [0x217004f,0x5230203,0x74f0407,0x6a90671,0xacd08bd,0xd330ceb,0x8bd]))
(.node (.leaf [0xbf80bf60bf40bf2,0x35f01af,0x5bb03a3,0x7bf05b7,0xde307f3,0xcf50b65,0x5af071408bc017807f50a140aa40830065003cf])
(.leaf [0x60300b3,0x56302ab,0xc5f0497,0x8bf0717,0x9c90981,0xb86])))
(.node (.node (.leaf [0x7c007be07bc07ba,0x8750155,0x5370377,0x8b70577,0xb1b07b3,0xc5f0af7,0x170016e016a])
(.leaf [0x22f008f,0x64d024d,0x77f043f,0x85d06d5,0x99f0947,0xe770d77]))
(.node (.leaf [0x510019,0x96101d1,0x72503d5,0xd7b060b,0xb7f084f,0xe450bcd,0x5b1071406dc03cd])
(.leaf [0x79100d9,0xad302fb,0x6f504ed,0xe1f074f,0xa1509e5,0x5af0694082c0944012403cc0070078a0ba20692036a03a2094200b6006c020400c601ce01d00830078000e602060656052801be00b807900391]))))
set_option maxRecDepth 5000 in
private def rowsBasePart30 : Table := (.node (.node (.node (.leaf [0xf800f600f400f2,0x35900f1,0x6dd0315,0x7250525,0xb45075d,0xd990a19,0x14021e05660d3e022a03e2041a064a009001780350071806dc03e8])
(.leaf [0x3f90029,0x22101e9,0x77503ed,0x7e90649,0xbed0875,0xe630c13,0x24e075208bd09e60de403660d7809e40aee03e9]))
(.node (.leaf [0x948094609440942,0x1930173,0x3c5038d,0x7af0597,0x81b07d3,0xe1d0b35,0x8b808b608b4])
(.leaf [0x7190099,0xa390271,0xc27044f,0xd0906e1,0xb490959,0xe370e1f])))
(.node (.node (.leaf [0x528052605240522,0x27d012d,0x6ab0353,0x785055d,0xb0b078b,0xb070abf,0x3a204b406cc08400a58083a0a520408067007980406066e021803a809b4062e02f200a800c8021209b809b007960c6200c400a40dd60b7b])
(.leaf [0x4450065,0x3d10219,0xbed0415,0x98d0695,0xe4508dd,0xd490d11,0xce]))
(.node (.leaf [0xdb80db60db40db2,0x4d701bf,0x59503b5,0x8c105c9,0xc0f0817,0xd510b81,0xd3e08be064d06e1])
(.leaf [0x3a500c5,0x46502e5,0xc7f04b7,0x8dd0725,0xb9f09a7,0x1eb]))))
set_option maxRecDepth 5000 in
private def rowsBasePart94 : Table := (.node (.node (.node (.leaf [0x308030603040302,0x287010f,0x72d0335,0x8a90549,0x995077d,0xc150a55,0x5064b07b601110563])
(.leaf [0x4270047,0x99f01ff,0x4410409,0xa23065b,0xbe508b5,0xe730cbb,0x7140717082a083a0b3a0bea0420052402ac0694082c09440c840b400c880e100136028e079007c809680ba80bf80390055807580522098c0aa40b64045008e00ce00d07]))
(.node (.leaf [0xb700b6e0b6c0b6a,0x5250195,0x3c303a3,0x8d705af,0x9f907f9,0xd2f0b5f,0x505b10177])
(.leaf [0x1d300b3,0x8d902a1,0x6bf0497,0x893070b,0xb87096f,0xeff0e7f])))
(.node (.node (.leaf [0x738073607340732,0x1770157,0x7490371,0x9810571,0xb9b07ab,0xddb0ae3,0x36904d407240b180136051603f4043c05f408200b9c0b7e03a805c0097807e20a320552077a099a083a07c809680302026c0b160ae007e80a3804d60726042e062e066203f2043a0134043006300ca00e10077e099e01640b580eb80c9c0e0c016800b609600ada07c6075c0794033e00c2066a038f])
(.leaf [0x5610089,0x2970247,0xb0d0435,0xa5906d1,0x987093f,0xed30d4b]))
(.node (.leaf [0x710011,0x46901d1,0x5e903d1,0x6710609,0xb65083d,0xe750bbd,0x5b1024c02ac02e4034c069407f4082c09440a140a74034a0ef2010c036408bc0aec0d040de40717])
(.leaf [0x33700d7,0x4c302fb,0x89d04d5,0x923074b,0xd4109c1,0xd106de0056021e010e01b801e80079]))))
set_option maxRecDepth 5000 in
private def rowsBasePart62 : Table := (.node (.node (.node (.leaf [0x1f801f601f401f2,0x40300fb,0xafb0323,0x5750535,0x93f0777,0xd0f0a3f,0x5064b06dd071607b600cf])
(.leaf [0xd50035,0x51501f5,0x80703f7,0xa17064f,0xe350895,0xe950c5d,0x1cb08bd01bc038c0554065100d800900370039803a805c0088008e80bd8007600c601fe04be0946075a07920b460b6e0b7e0d4e047804c004d8072802ac0b680b700ba00cf80e580717012603e60b3a0c9a0dfa008c06920a5200fc089e0c5e08e60b16078a09620cda0e4607cc0bc0]))
(.node (.leaf [0xa580a560a540a52,0x4ab017b,0x777038f,0x77d05a5,0xbdf07e7,0xd070b47,0xd440d460d48])
(.leaf [0x1bb00ab,0x6830283,0x4cf046f,0x8e506ed,0xcef095f,0xeb30e3b])))
(.node (.node (.leaf [0x630062e062c062a,0x7250135,0x7410369,0x8e90569,0xadd0795,0xb190ad1,0x507f50d05071406e1])
(.leaf [0x2210079,0x4d90229,0x62d042d,0x88906c1,0xe5f090f,0xe370d2f,0xdfe]))
(.node (.leaf [0xed80ed60ed40ed2,0x48b01c3,0x5af03c7,0x62b05eb,0xbf3082b,0xd3d0b9d,0x5af06500714064c0830])
(.leaf [0x34f00cf,0x33b02f3,0x71f04cf,0x933073b,0xc6909b1,0x9a5]))))
set_option maxRecDepth 5000 in
private def rowsBasePart126 : Table := (.node (.node (.node (.leaf [0x418041604140412,0x7ff0117,0xb190341,0x5b10559,0x9a50785,0xd050a75,0x3650abe0b400de403e3])
(.leaf [0x1ed0055,0x9a90209,0x443040b,0x6af0677,0xcbf08bf,0xd310cf9,0x885]))
(.node (.leaf [0xc880c860c840c82,0x36701b7,0x73503a5,0x78d05bd,0xb5507fd,0xe0d0b65,0x71406dc0a1407f4064b])
(.leaf [0x36d00bd,0x65902b9,0x81504ad,0xd3d0715,0xd3f098f,0xeab])))
(.node (.node (.leaf [0x840083e083c083a,0x2e30163,0xa050375,0x795057d,0x9df07bf,0xe0d0b05,0x3ce03d003cc])
(.leaf [0x5690091,0x6570257,0x6750445,0xcfd06d5,0xe9f0947,0xe7f0d97]))
(.node (.leaf [0x3e30013,0x4ad01d5,0x62903e9,0x695062d,0x89d0865,0xd750bdd,0x3e80018017800120014])
(.leaf [0x20700e7,0x4db0303,0x7f904f9,0xac90759,0xa5909f9,0x38e02aa06e1000e030e065602ae04180b680964096003a605be0aec039009a8056c05630791]))))
set_option maxRecDepth 5000 in
private def rowsBasePart1 : Table := (.node (.node (.node (.leaf [0x10000e000c000a,0x31d00e5,0x5f50305,0xb8704f7,0xaf10759,0xd1309f3,0x5af03e804200192064b06e1000e00e600ee01ce02060164032c094402ae031600700198045004f807f907d604b40af40dfc0e740b280bd00e800ea00ef8028605c60ace0b160c5e0cbe0e960b680ba0078c0ba40c840ef402020c5a0288059805a8074807800960005800d8051004b60b3e021603a60aec082f])
(.leaf [0x54d0015,0x55301d3,0x63103e9,0x7e5062d,0x8bd0865,0xda90be1,0x5b109bb08c101cb]))
(.node (.leaf [0x858085608540852,0x2e90169,0xa0f0377,0x8790581,0xb0707bf,0xc8d0b0d,0x40e040a0410])
(.leaf [0x6e10091,0x3ed025d,0x6b10449,0xddd06d5,0x995094d,0xe9f0d97])))
(.node (.node (.leaf [0x430042e042c042a,0x2bd011d,0x70d0345,0x7510559,0xae50785,0xd970a77,0x64a064c0351])
(.leaf [0x21d0055,0x3a3020b,0x673040b,0x7ff0677,0xe9508bd,0xd410cf9,0x34a064f]))
(.node (.leaf [0xca00c9e0c9c0c9a,0x46d01b5,0x77b03a3,0x7bb05bb,0xb6707ff,0xe430b63,0x5af036808bd098c09bc0aa40b640cf40e5407f40350007602ae034e06060696082e09460c86005800b000b800e801d002e80658025000160046031e03ce04b604be06ce0aa60af60dfe001805a80748078009600cf003e60e760aba0e720e9a06e108e80cc00e0002ac0b460b7e0d4e0e260e4608300179])
(.leaf [0xdb00c3,0x43f02c7,0xb6304ab,0xdfd0715,0xb610999,0xee3]))))
set_option maxRecDepth 5000 in
private def rowsBasePart65 : Table := (.node (.node (.node (.leaf [0x210020e020c020a,0x7e700ff,0x4b5032d,0x7530533,0x98b0773,0xd250a3d,0x5ae09ba0d3e0563])
(.leaf [0x1450035,0x5b701f7,0xacf03f7,0xa77064f,0x905089d,0xeff0c5f,0x1cb06f0002e020e097409dc0ba4003004da0b440b6c072804b606ce08a60b680b700cf808e00ae008de0ade0e380e4604b806d00e480b660cf6053209980b98057805c0076007c00b1007fc036e0726037403a409ae06ea08a201e604e00750015c03fc09940ad40e34054608b60bfe0569]))
(.node (.leaf [0xa780a760a740a72,0x7910181,0x78d038d,0x7b305a3,0xdd707e7,0xe190b49,0xd980d960d92])
(.leaf [0x1c300ab,0x8c10289,0x7df046f,0x9f706ef,0xd210961,0xefb0e3b])))
(.node (.node (.leaf [0x648064606440642,0x8410139,0x9e50365,0x9490569,0xb1d0795,0xc7d0acd,0xbbc054c08bf])
(.leaf [0x24f0077,0x9c50225,0x695042d,0xacb06bb,0xb190919,0xe4f0d2f,0xb60]))
(.node (.leaf [0xef00eee0eec0eea,0x57501c5,0x5b703c7,0x62f05f7,0xbf90831,0xd450b9d,0x5af02080498049609460d2e008c02e406ce021803a805c008680ad00b1800d401d40442099a09a20b1a0e260e9e0c82060202b00d9808e80ef80c8801cc04640604083c0a5401ca06ea0732046209420b620cf2008e014602f60206096602aa0e3808e207960764079809680b500d1003a603fe059e074e099e0b160e360216036c075c0b640cfc0e2c05ba0d120e420ec40ef406f0083a064f])
(.leaf [0x64f00cf,0x34102f9,0x82304cb,0xabf073f,0xd2b09ab,0xae5]))))
set_option maxRecDepth 5000 in
private def rowsBasePart33 : Table := (.node (.node (.node (.leaf [0x110010e010c010a,0x3c100f1,0x9730313,0x82b0523,0xe2b075b,0xbfd0a1d,0x2d6038e039603c60556056607b60886098e0d3e0072064a08820090019802d80320043005f00630074007f80ac0008e0146019602f6033e044e0496004a00a200c201ca0126031e03ce04be0a160af60b260dfe02e8036804c00728087809e80a780d080de8049404f4086408740acc0b140c5c09e601d0053005a80748078000cf])
(.leaf [0xb3002b,0x38101e9,0x7fd03ed,0x8310649,0xc330873,0xe590c21,0x71401cf07f8055108bd]))
(.node (.leaf [0x960095e095c095a,0x1a30173,0x553038b,0x8af0597,0x82107d9,0xb630b3b,0x960095a095e])
(.leaf [0x1a100a1,0x5950275,0x8350455,0x71d06e5,0xb690959,0xea50e1d])))
(.node (.node (.leaf [0x540053e053c053a,0x3ab012b,0x7210359,0x88b055b,0xb110791,0xc370abf,0xb660b4409b40d3809b80b48095809b00d320b640b7b])
(.leaf [0x5bf0067,0x4b70217,0x625041d,0x9df0697,0xaeb08e3,0xd590d11,0x34f]))
(.node (.leaf [0xdd80dd60dd40dd2,0x56b01bb,0x70f03b7,0xc2505c5,0xa83081b,0xdd70b7f,0x6cc043a0bd00c180d6803a601000a520a58078007e20ada040607e40be00bce0c16084c03a20e340bdc0376084e0a060e360b81])
(.leaf [0x62b00c3,0x49302e3,0x6df04bf,0xa370727,0xc5f09a7,0x363]))))
set_option maxRecDepth 5000 in
private def rowsBasePart97 : Table := (.node (.node (.node (.leaf [0x320031e031c031a,0x28f010f,0x9a70337,0xbb90549,0x99b077b,0xcf70a57,0x5064b07b60563])
(.leaf [0x59f0047,0x38d0205,0x4510409,0x7f90669,0xbfd08b5,0xe930cbb,0xcf065003e807f3]))
(.node (.leaf [0xb900b8e0b8c0b8a,0x7b70197,0x3c903a9,0x98f05af,0xa5107f9,0xdff0b5f,0x5])
(.leaf [0x1d900b9,0x8df02a7,0x7050495,0x8990711,0x9bb0973,0xefd0e9d])))
(.node (.node (.leaf [0x750074e074c074a,0x1850155,0x75f036f,0x5bd0575,0xe4b07ab,0xb270aef,0x5036902e404d40724087408c40de401780288049805c8087809080ad00b18012601360286028e03e603ce04b60516090603f4043c05f4069408200d980b640b9c0b7e0e26037003a805c0097807e20a3202d2038a055207b202e2077a099a0b3a0692083a019802d8041e079007c809680ba803020522026c0ace0b1601cc052404500ae00ce00831])
(.leaf [0x6d90089,0x6010249,0xc0d0435,0xae106d1,0x9990941,0xe490d59]))
(.node (.leaf [0x910011,0x4f501cd,0x71903d1,0x7f90609,0xbad083d,0xc010bc9,0x5b1071406dc03cd0d3e])
(.leaf [0x38d00d5,0x4cf02ff,0xb7f04d7,0x94b074b,0xef909c1,0x350034a0a1807f2044e0416010e0d98064d]))))
set_option maxRecDepth 5000 in
private def rowsBasePart17 : Table := (.node (.node (.node (.leaf [0x90008e008c008a,0x7b300e3,0x6d90311,0x8490511,0x793075b,0xd010a11,0x1407b6042000180af8077c041c00c40af400c8077e03e3])
(.leaf [0x3f10021,0x37501dd,0x43503ed,0x69d0635,0xe27086f,0xd830c03,0x38b]))
(.node (.leaf [0x8d808d608d408d2,0x2fb016b,0x5430383,0x9690589,0xb1507c5,0xcdf0b27,0x5cc05d005ce])
(.leaf [0x31b0093,0x42b026b,0x6890451,0x9e506dd,0xd0d094d,0xdfd0de5])))
(.node (.node (.leaf [0x4b804b604b404b2,0x3cf0127,0x64b034b,0x9690559,0x9690791,0xc250aa5,0x5056306dd])
(.leaf [0x2290061,0x5cf020f,0x6890419,0x8510689,0x91508dd,0xd410d09,0x65001d00369]))
(.node (.leaf [0xd480d460d440d42,0x20301bb,0xb7f03a7,0xd4f05bf,0xa770807,0xba90b81,0xd3e0a180717035007cc0ba404500b23])
(.leaf [0x1fb00c3,0x6d502dd,0x7d304b3,0xa910721,0xb9909a1,0x57b]))))
set_option maxRecDepth 5000 in
private def rowsBasePart81 : Table := (.node (.node (.node (.leaf [0x298029602940292,0x6d90109,0xb05032d,0x94d053d,0x7ad077d,0xced0a4d,0x24c064b0d3e06e103e8008e022a0a1804960204049403d005c8020809a7])
(.leaf [0x1c90041,0x4d10201,0x75f03ff,0x9930653,0xac908b1,0xdeb0c93,0x1cd065100fc0406066e052005bc018e0446010008fc0b4408060554059c0ad40a700212036e0b46020005c0078e076007980804066603650569]))
(.node (.leaf [0xb080b060b040b02,0x335018d,0x5690399,0xd3505a5,0xb6107f1,0xd210b59,0x5036906dd03ce04b604be0dfe007402ac03f4043c069406a40bf80b640b6c0b9c0e540a260b6e0b7e0d4e0030009001e8026002b0037003a805380898097807e20a320bf002d2038a03c2055205da07b202e20742077a099a0b3a0692083a0db2019802d8041e0220079007c80ba803020522026c0ace0b1601cc0524045008e00ae00af00e00082f])
(.leaf [0x60100b1,0x62b028b,0xc450475,0x8830703,0xb7f0967,0xee50e5d])))
(.node (.node (.leaf [0x6d006ce06cc06ca,0x74b0143,0x55f036f,0x7590571,0xafb07a3,0xb150add,0x5036806dc0d0804f405c40bbc0c240cbc064f0719])
(.leaf [0x1f5007d,0x6090231,0x6550435,0x71506cd,0x9610931,0xef50d3d,0x0]))
(.node (.leaf [0xcf0007,0x36b01cb,0xa9903c9,0x92d05fd,0xb930833,0xe0d0bad,0xb64078a0606031404f400b801d0008a017206e103680494054c0bbc075202f40b3c00d606ee0214021809580b680b3a078e06ec02f607f9])
(.leaf [0x21300d3,0x6eb02f3,0x52904d9,0x9470747,0xd3709b7,0xb57]))))
set_option maxRecDepth 5000 in
private def rowsBasePart49 : Table := (.node (.node (.node (.leaf [0x190018e018c018a,0x22f00ff,0x7190321,0x55b052b,0xaf7076f,0xc090a39,0x38e03c6055607b608d607f8049206ce0b260dfe04d80728087808c80de804940874053005a807800208021003f6043e082e0c860bec0b7e0d4e03a80134028c0136028e03f2043a01bc038c052c055407e20a3203a407cc0ba4083001d8051007ce0c820bf00206057e09a601cd])
(.leaf [0x3fd002d,0x4b101f1,0x64b03f3,0x7f90651,0xc830883,0xe730c33,0x71406dc0178010c0414082c0de4024e082e0c86075603e60b220aba0d040569]))
(.node (.leaf [0x9e009de09dc09da,0x4970177,0x6bf038f,0x7b105a1,0x82107e9,0xe270b3f,0xb580b520b54])
(.leaf [0x2f300a3,0x8b5027d,0x8730463,0xd1106e9,0xb47095f,0xe570e37])))
(.node (.node (.leaf [0x5c005be05bc05ba,0x2d50135,0x52f0367,0x5bf0567,0x7cb0793,0xb0d0ac5,0x507f503680d0407140d090b40])
(.leaf [0x5c7006f,0x4bf021f,0xaf90421,0x9c906b1,0xe5508fd,0xe490d19,0xb27]))
(.node (.leaf [0xe600e5e0e5c0e5a,0x21101c9,0x72103c1,0x8e105d9,0xa37082f,0xd290b91,0x5af0368064d0830])
(.leaf [0x1c900d1,0xabf02e7,0xc8704bf,0xa570737,0x9db09ab,0x40d]))))
set_option maxRecDepth 5000 in
private def rowsBasePart113 : Table := (.node (.node (.node (.leaf [0x3a803a603a403a2,0x12f0117,0x62b033b,0x95f054f,0xd83077b,0xbe10a71,0x2aa09420c8205a6077e00b801c0039007580b400b660b9e047604d60aee09440b440b7c066808400de807e20a3202b008500ad00b180cc00b2604b406cc0dfc021807d808200a88083a044e068207e40a3408e206860cee09b20b7a0dfa006e095809b007d4081c006c056c057c078c0c8404b606ce0b3e094a095a0b620b9a0cda0ce00567])
(.leaf [0x42f004f,0x5290209,0x7950405,0x805066d,0xb1508bd,0xe150ced,0xaf5]))
(.node (.leaf [0xc100c0e0c0c0c0a,0x4b901b1,0x5c103a9,0x89f05b7,0xe7307f3,0xcfd0b65,0x5af071406dd010e052e054e075609e60b3e017807f50d3d])
(.leaf [0x60900b9,0x64b02ab,0x8c904a1,0x9070717,0xd0b097b,0xb5b])))
(.node (.node (.leaf [0x7d807d607d407d2,0x2eb015b,0x56f0377,0x9590579,0xb9107b9,0xdb50af5,0x1b801b401b6])
(.leaf [0x2ad008d,0x883024b,0x7c5043d,0x8ad06d5,0xb3d0945,0xdb90d89]))
(.node (.leaf [0xa70017,0x20f01d7,0x7c103d9,0x953061b,0xc15084d,0xd7d0bd5,0x5b1071406dc])
(.leaf [0x1f900e1,0x33b0303,0x83904f1,0x78b0753,0xa3309e3,0x82c0830052805240203]))))
set_option maxRecDepth 5000 in
private def rowsBasePart9 : Table := (.node (.node (.node (.leaf [0x50004e004c004a,0x3b900e9,0x9690309,0x7070507,0xd790759,0xa5d0a0d,0x505af0251064b06e1])
(.leaf [0xb10021,0x80101d9,0xabf03e7,0x9b10631,0xe210869,0xe750bed,0x5b101cb054f]))
(.node (.leaf [0x898089608940892,0x4d90169,0x6e5037d,0xbf10581,0xdc907c1,0xee70b17,0x56205680566])
(.leaf [0x24b0093,0x42d0265,0x8250445,0x87706df,0xb410951,0xeb10da9])))
(.node (.node (.leaf [0x478047604740472,0x2710129,0x4dd034d,0x8c70557,0x7c10791,0xc010a91,0x505630368064c06df])
(.leaf [0x5af0057,0x49d020d,0xbe7040f,0xa410679,0x90b08d3,0xd390d01,0x65001760c5e06e1038e055607560b3e03e80b400960062201cf]))
(.node (.leaf [0xd080d060d040d02,0x7dd01b5,0xa5503a5,0x99b05bb,0x83f0807,0xd410b71,0xdfe0de80e000c85])
(.leaf [0x1b900c9,0x5af02d7,0x51504b5,0x90d071d,0xecb0993,0x1e3]))))
set_option maxRecDepth 5000 in
private def rowsBasePart73 : Table := (.node (.node (.node (.leaf [0x258025602540252,0x2810109,0x725032d,0x597053f,0xb050775,0xd190a49,0xad00b180b7e037003a80758077e09a6077c07900ace0b1602080206036e03a6095e038d])
(.leaf [0x690041,0x38f01ff,0x4490401,0xd990651,0xc15089d,0xe010c81,0x71401d001cb]))
(.node (.leaf [0xac80ac60ac40ac2,0x3f70187,0xa3f038f,0x91905a9,0xa3d07ed,0xd0b0b4b,0xeae0eac0eb0])
(.leaf [0x37500ad,0x43f028f,0x4d70477,0x72b06f3,0x9b10969,0xef90e49])))
(.node (.node (.leaf [0x688068606840682,0x1770147,0x38d036d,0x5b3056b,0x7d107a1,0xb0b0ad3,0x50714036806dd])
(.leaf [0x4bf0077,0x3e3022b,0x7bf042f,0x89506c5,0x9530923,0xe550d35,0x1b7]))
(.node (.leaf [0x470007,0x20301cb,0x7ad03c5,0x96705f7,0xe7b082b,0xd530ba3,0x5af02ac03f4043c0a74064807e80a3806620996094c0e2401780ad00b18047404d409e40d0404b6051606ce08a6028e04300630021807d007d8082000d403f2043a044205da0b6c0b9c02b007cc09b40b7c02f2033a0b6a07d4081c0dd2042e062e0ace0b160c160ae0004c00c401fc04d60790096807ba09aa01c403bc078c0a34070400c601f6053e07e6094e05b807080ba0028a074a086a0962044b])
(.leaf [0xf900d9,0x4c102f9,0xb7d04cd,0x77b0743,0xba309b3,0x79f]))))
set_option maxRecDepth 5000 in
private def rowsBasePart41 : Table := (.node (.node (.node (.leaf [0x150014e014c014a,0x7c100f1,0x495031d,0xba50525,0xae70767,0xd050a25,0x38e0320031e0b2602e80d0800e6020602e6094809c00d980b70038c0b6a00e405bc07cc0ba407ce05c00978094609de078e02040a77])
(.leaf [0x1610031,0x97501e5,0x43d03f5,0x697064f,0xe2d087d,0xc5b0c33,0x1cf0178008c02e4001403e607f3]))
(.node (.leaf [0x9a0099e099c099a,0x3410179,0x5a5038d,0x5dd059d,0xbcb07d3,0xcf30b3b,0xa200a1e0a1c])
(.leaf [0x72100a1,0x575027d,0x4b70467,0xa3d06e5,0xeaf0957,0xeb70e27])))
(.node (.node (.leaf [0x580057e057c057a,0x71d012d,0x74f035f,0xbcb055b,0xe43078b,0xd970abf,0x507f50368096007580aea0d09])
(.leaf [0x203006b,0x9b50215,0x7b90421,0x83f06a7,0xc8908e9,0xd4b0d13,0xb23]))
(.node (.leaf [0xe180e160e140e12,0x95101c1,0x5a503bd,0x8c905d1,0xb810829,0xd170b87,0x5af03680072024a02aa02e2034a03f2043a06020692082a09420c820a780ac00b280bd00c180d680d780e780e800ea0078c07c4096409dc0ba40c840ef4007800d801d803a605e601000288042004500830083a0a5207f9])
(.leaf [0x77d00c5,0x6dd02e5,0x8e504bd,0xb0d072d,0xd2909a9,0x713]))))
set_option maxRecDepth 5000 in
private def rowsBasePart105 : Table := (.node (.node (.node (.leaf [0x360035e035c035a,0x415010d,0x4bf033f,0x747054f,0xb13077b,0xbd70a5f,0x7b70aa60b660b6e0b9e01f003c808880c10078c09640b6c04be088601d60aa801b804c008400a58078e0966042a062a04940e480af804960db803320b620b9a073009ae01d403c40a54063007be05480708033803bc0e440947])
(.leaf [0xe7004f,0x3c90209,0x66b0403,0x9c50665,0x90708bf,0xe7d0cdd,0x4b5]))
(.node (.leaf [0xbd00bce0bcc0bca,0x42d01a5,0x56d03a5,0xd4105b1,0xbbd07f5,0xb9b0b63,0x3c60a540d3d0831054d0a5203f20d88042e062e020401d00bce07e20bd0005000c8089a0b020c6205a8078009a00b80036a0e3609220b620cea0cf20b7a0924099c095609ae0d84004c00c405600750093803a5])
(.leaf [0x36700b7,0x41702af,0x8c10499,0xd390711,0xc930973,0xf090ef9])))
(.node (.node (.leaf [0x798079607940792,0x4670157,0x3a50375,0x7610579,0x9d707b7,0xd790af1,0xd000ce])
(.leaf [0x1590091,0x4210251,0x6690441,0x70f06d7,0x98b0943,0xd970d77]))
(.node (.leaf [0x2b5000d,0x7f301cb,0xaa903d1,0xd770607,0xa75084d,0xd930bcb,0x5b1071406dc03cd09bb0177])
(.leaf [0x67700d7,0x6f702ff,0x72504dd,0xadf074f,0xd4b09cb,0x4405af06e103f4043c082c0bf60bee0c2605c6087609060ace0b1604b4051409040070015802f803400b680ba0078a07c20962083a0a5203a205ba04180156006c032a02040b0600c6083008400a580bf004b60bf405980780020801860306041402f2033a03f2043a03a605be05e6095609ae0570079009680bdc0da4044f]))))
set_option maxRecDepth 5000 in
private def rowsBasePart25 : Table := (.node (.node (.node (.leaf [0xd000ce00cc00ca,0x32b00eb,0x4f50315,0xb9b0513,0x9790761,0xbf90a19,0x14005601ee021e02d6038e0556056607b6098e0d3e0072022a03e2041a064a0090017802d80350071806dd])
(.leaf [0x1830023,0x56101e1,0x64103f1,0xc6b0633,0x8e10879,0xd930c13,0x8d3]))
(.node (.leaf [0x920091e091c091a,0x4910171,0xa1b0383,0x9a10591,0xb2707cf,0xef30b23,0x7a0079c])
(.leaf [0x5ab0093,0x66d026d,0x82f044f,0xaed06dd,0x9ab0953,0xe970dff])))
(.node (.node (.leaf [0x50004fe04fc04fa,0x7170127,0x9bd034d,0x5b3055b,0x9c10791,0xb010ab9,0x36a03a205ba01f000b801b800b6078e09660ad004b40b6607d801d003f4078a09620b440b7c03f2021803a805c009b40d3802f60c3800a801ce04b60c360b640ace0c80095b])
(.leaf [0x18d0065,0x3a50215,0x7f90419,0x82b0693,0xb2908e1,0xe9d0d05,0x9c1]))
(.node (.leaf [0xd880d860d840d82,0x38d01bd,0x6db03ab,0x7c505c5,0xbd3080b,0xd470b7f,0x8bd072803a405bc05e4057c05a8078009600b800d5005a2077a072607ba03a805c005e20d07])
(.leaf [0x33b00c3,0x32b02e3,0x8e104b9,0xe05071d,0xb6309a3,0x3]))))
set_option maxRecDepth 5000 in
private def rowsBasePart89 : Table := (.node (.node (.node (.leaf [0x2e002de02dc02da,0x1390111,0x4c70337,0x7770547,0x9490781,0xa970a57,0xd920d3e06df0d05])
(.leaf [0xdf0047,0x82501fd,0xad90401,0xd9b0653,0xad708b7,0xe8b0cb3,0x71406dc064b]))
(.node (.leaf [0xb480b460b440b42,0x3310199,0xb710399,0x7b905b1,0x83b07f3,0xb990b61,0x50d09])
(.leaf [0xd900b9,0x6370297,0xb5f048f,0xb150705,0x9c3096b,0xe7f0e77])))
(.node (.node (.leaf [0x710070e070c070a,0x3eb014b,0x6ef036f,0x8af056f,0x99907b1,0xdd70adf,0x6dc0d080a140719])
(.leaf [0x2470087,0x5770237,0x7ad0435,0x8a306cb,0x9910939,0xe430d4b]))
(.node (.leaf [0x3830003,0x3a701cf,0x5c503cd,0x64d0605,0xa57083f,0xc090bc1,0x650064c02e40a740d040076010e007201b602ac0948082b])
(.leaf [0x2f500d5,0xacf02f7,0x7e504d5,0xe130743,0xba909c1,0xe07]))))
set_option maxRecDepth 5000 in
private def rowsBasePart57 : Table := (.node (.node (.node (.leaf [0x1d001ce01cc01ca,0x3610101,0x6530323,0x8790531,0x7b10779,0xc0b0a3b,0x14064b06dd0719098c0b640b9c0cf40220079007c8096809e00ba8007803e804200ac00db8019602d6031e005202d2038a03c2055205da098a02ae0524083a0a520db20b8001e6036e03a605be075608e60a3200fc026c06040744077c0924099c0b3c00a800c801f002000dfe010e01be038e05560b3e02f2033a08e206bc0af4095609ae00180070019801a802f8034004500498031201ca052206ea073207b900cf])
(.leaf [0x6f0037,0x38301f3,0x78d03f5,0x9490651,0xac70897,0xe7b0c5b,0x1cb049405c409040acc0c240c5c01780464082c0de40365064f03e80bf80746077e0bf40300063809a809b80b800d20007802300420008c0152056a078a0962018203020974012803d006d008a809080b660cf60e56008e010e0abe044e07ce022a03f2015607cc0ad0074008a00c600ba4078c09640e480ec40d09]))
(.node (.leaf [0xa280a260a240a22,0x3110181,0x725038d,0xc0105a1,0xb3907e9,0xb810b49,0xd000cfe0cfc])
(.leaf [0xc500ad,0x5510289,0xc370467,0x8db06eb,0xc710961,0xed70e37])))
(.node (.node (.leaf [0x60005fe05fc05fa,0x3d90139,0x6dd0365,0x8930563,0x9810799,0xb050acd,0x507f503680d0407140d09])
(.leaf [0x1b50075,0x9bd021d,0x8330423,0x70906c1,0xe550905,0xe4b0d23,0xaf7]))
(.node (.leaf [0xea80ea60ea40ea2,0x39101c9,0xa9103c1,0x9dd05dd,0xb5f082f,0xd350b95,0x5af06500714064c083003cd])
(.leaf [0x2e900d1,0x95102f1,0x50d04cd,0x7710741,0xb8109b1,0x755]))))
set_option maxRecDepth 5000 in
private def rowsBasePart121 : Table := (.node (.node (.node (.leaf [0x3f003ee03ec03ea,0x38d0115,0x737033f,0x59d0555,0xe390781,0xbef0a77,0x505b106e10d3e])
(.leaf [0xe50055,0x82d0205,0xadf0407,0xa37066f,0xc2908c1,0xe950ced,0x251]))
(.node (.leaf [0xc600c5e0c5c0c5a,0x1f101b9,0x70b03a3,0x9c905b9,0xa0d07fd,0xd3f0b67,0x5af071406dc0d3d07f50179064b])
(.leaf [0x1dd00bd,0xa7502ad,0x70b04ab,0xaf50715,0xb8b098b,0xd43])))
(.node (.node (.leaf [0x818081608140812,0x7810161,0x74f0377,0x5c90581,0x9af07bf,0xecf0aff,0x36803660364])
(.leaf [0x315008d,0x4230253,0xb17043f,0xa1d06d5,0xc890949,0xdc90d99]))
(.node (.leaf [0x1790019,0x3a301d3,0x42b03e3,0x9a90629,0xac3085b,0xc130bdb,0x5b107f309bb])
(.leaf [0x1fd00e5,0x4870307,0x6f104f9,0x9630753,0xa1d09ed,0x1403e8011001d004f407f80179]))))
set_option maxRecDepth 5000 in
private def rowsBasePart5 : Table := (.node (.node (.node (.leaf [0x30002e002c002a,0x34500e5,0x6d10309,0x8390501,0xb530753,0xa790a09,0x505af0251064b06e100cf])
(.leaf [0x490021,0x58701d7,0x78503e5,0x933062b,0xacf0867,0xc250bed,0x5b101cf]))
(.node (.leaf [0x878087608740872,0x43f0167,0x3ab037b,0x95f057f,0xb9707bf,0xc890b19,0x4f804f404f2])
(.leaf [0x1930093,0x65b025b,0x7990449,0x72506dd,0x9a90951,0xef90d99])))
(.node (.node (.leaf [0x450044e044c044a,0x70b011b,0xb1d0345,0x7810559,0xd950785,0xd450a7d,0x5056303680d09094507f50719])
(.leaf [0x4350055,0x3c3020b,0x785040d,0x9a30673,0xadf08c7,0xe350cf5,0xd05064f046808300b4001c0039005580202036a03a204620b3a0569]))
(.node (.leaf [0xce00cde0cdc0cda,0x4bf01b7,0x79303a3,0x8a705bf,0xded07fd,0xd070b6f,0x5af036808bd0b6407f400760c860250012603ce04be011004c00de808e80d0709420b3e09480b3c0c84088803a60aca09580b68010e])
(.leaf [0xe700c7,0x44b02d3,0xc7704af,0x8b7071f,0xc8b0993,0xcb]))))
set_option maxRecDepth 5000 in
private def rowsBasePart69 : Table := (.node (.node (.node (.leaf [0x230022e022c022a,0x1310109,0x5090331,0x85d0535,0xac30773,0xbd70a47,0x9a60b3c0e7e0b400b640f000b660831])
(.leaf [0x56d0035,0x99501f5,0xbd103f9,0xc87064f,0xb05089d,0xdf30c73,0x71403a204f207f206dd0650064a]))
(.node (.leaf [0xa980a960a940a92,0x3090189,0xa37038f,0x8cd05a5,0x82907f1,0xb7b0b4b,0xe200e1e0e1c])
(.leaf [0x30300ab,0x2d7028f,0xb490471,0xad106f1,0xeb7095f,0xe630e43])))
(.node (.node (.leaf [0x668066606640662,0x85b013b,0xb3d0365,0xbd70567,0xb7d0795,0xc890ad1,0x507f5])
(.leaf [0x2af0077,0x2510231,0x775042d,0x6fb06c3,0xe65091d,0xe330d33,0x943]))
(.node (.leaf [0x150005,0x7ed01c5,0x70703c7,0x65105f9,0xdfb082b,0xe650b9d,0x5af0714007407f4082c083003cd])
(.leaf [0x78500cd,0x4b902f9,0x89304cb,0xb3f073f,0xb7b09b3,0xd95]))))
set_option maxRecDepth 5000 in
private def rowsBasePart37 : Table := (.node (.node (.node (.leaf [0x130012e012c012a,0x6ad00ed,0xaed0315,0x9030523,0x7970767,0xd010a21,0x21e02d60566022a041a064a02d8032002300420043006280630008a044a04920124031c03cc04b40aa40286049605c60c2606e10aa8064e07d6081e0d9602880462082a021403a4046409bd])
(.leaf [0xcf002f,0x4d101e9,0xbc303eb,0x9b70647,0xe290879,0xe3b0c23,0x1cf0cbe02e40b28034c04140464064c0b3c041806820b3e0753]))
(.node (.leaf [0x980097e097c097a,0x2f70177,0x55b038b,0xbf50595,0xb6307d3,0xceb0b3b,0x9b009ae09aa])
(.leaf [0x353009b,0x433027b,0x4950465,0x8d106e9,0xc530953,0xe3b0e23])))
(.node (.node (.leaf [0x560055e055c055a,0x427012f,0x383035b,0x93f055f,0xb690791,0xc610ac1,0x507f503680d040b400b3e])
(.leaf [0xd90071,0x83d0215,0x76f041f,0xdb50695,0xb2708e7,0xe450d0d,0xd97]))
(.node (.leaf [0xdf80df60df40df2,0x7e901c1,0xb8d03b5,0xd5905c9,0xa3f0827,0xe370b7f,0x5af0368024a02aa03f2043a06020692082a09420a780ac00b280bd00c180d680d780e780e800ea0078c07c4096409dc0ba40ef400d801d803a605e6010002880420045008300a5207f9034f])
(.leaf [0x63500c5,0x64b02e3,0x71904c1,0xd4b0723,0xcdf09a7,0x54b]))))
set_option maxRecDepth 5000 in
private def rowsBasePart101 : Table := (.node (.node (.node (.leaf [0x340033e033c033a,0x3690111,0xb0f0337,0x5a5054d,0xad3077b,0xd870a57,0x5064b07b60719])
(.leaf [0xc7004f,0x3a10209,0x6630403,0x94b0663,0xcb708b7,0xf050cbd,0x125]))
(.node (.leaf [0xbb00bae0bac0baa,0x9090199,0x56303a3,0xc0b05ab,0xb3b07f3,0xf010b61,0x5af008c02e404bc04d407240a740d040de401be07560b3e007803e8041800180090009802f8034004500c5e035004b804c0051806d00b280d96098c09bc0b640b6c0b9c01cc041404640604082c083c0a4c0a540b3c01ca034a0522001405940cec06820a4a022a060207e20a320250021603a605be07ce007400fc026c02c4041c083a0a52064b])
(.leaf [0x31500b5,0x2d702af,0x82f0497,0xb1b070b,0xb530973,0xf050ec5])))
(.node (.node (.leaf [0x770076e076c076a,0x4130153,0xb43036b,0x5cf0577,0x9a107b9,0xcbf0aef,0x84036904d4072402880b180bc00126013602360286028e041603ce03f4043c0bf80e540a260b7e0d4e003001e8026003a80898097807e20a32038a03c2055207b2077a099a0b3a0db20198041e0220079007c80ba80b160ae0020607e60a360a4e0bf6006a04020412066a0682020804d8072800e80db8049007f00cf0006e0196000e078e07c609a60134028c0168002e005e00b600e600ee01c6020e065606620a4a02180960042000c20294075c07940d1c0ada077e])
(.leaf [0x990091,0x3e90251,0x64f043f,0xcf906d1,0xc7d093d,0xee50d5d]))
(.node (.leaf [0xd10011,0x55101d1,0x7cf03cf,0x9750605,0xe0f083f,0xe290bc9,0x5b106510c5c0e940b480b8001cc0a4c00b4038c021403a400d601d60b660a4a03f205700580079009a80594078a075c0b54003200d20c6007580b680e920bca0551])
(.leaf [0x66d00d5,0x63702ff,0xc9f04d7,0x957074f,0xc9d09c5,0x2e8008e02e2008a0aba06e1]))))
set_option maxRecDepth 5000 in
private def rowsBasePart21 : Table := (.node (.node (.node (.leaf [0xb000ae00ac00aa,0x20d00ed,0x34d0315,0x7150515,0x96b075b,0xbbf0a17,0x1401ee02d6038e0556056607b6098e0d3e0072041a064a009002d80350008c02e404bc0a740d040126034e03ce04be0a160aa60b26028804f8001804200628063000760286028e01b80390055800cf0177])
(.leaf [0x4b0023,0x47701df,0x5ff03ef,0x9610639,0x8c10879,0xda10c11,0x563]))
(.node (.leaf [0x90008fe08fc08fa,0x4110171,0x6d30383,0x897058f,0xba107c9,0xd990b29,0x71c0720071e])
(.leaf [0x34b0093,0x5bb026b,0x7cb044b,0xa7706df,0xea90951,0xe930de3])))
(.node (.node (.leaf [0x4d804d604d404d2,0x4210129,0x715034d,0xcf90559,0x9b5078d,0xd3f0aa7,0x7b800b800b6095e04f80c600cc00e980d9801d008400a500682043c06a40850083a0b7c0e9c06880b28043a0a4a021809b40e380ed80ea00c5c01ce0cea0e9409490313])
(.leaf [0xd30063,0x9ab020b,0x79d0415,0xa510689,0xadf08df,0xe250d05,0xd1]))
(.node (.leaf [0xd680d660d640d62,0x36501bd,0x57303ab,0x5e905c9,0xb490809,0xd0d0b7d,0x5af03680714099009c00a180b680b700ef8071707f40350064f02d206920b6e0b7e0d4e0e260e9e0a3201780945])
(.leaf [0x2fb00c3,0x31b02e3,0x83f04b7,0xb310721,0xed5099d,0x71b]))))
set_option maxRecDepth 5000 in
private def rowsBasePart85 : Table := (.node (.node (.node (.leaf [0x2b802b602b402b2,0x127010f,0x4ad0335,0x5a10549,0x7b90781,0xd590a51,0x5064b07b60d3e038e03670567])
(.leaf [0x5790041,0x5bd01fd,0x7e10401,0xa7d0655,0x90108b9,0xde30c9b,0x1404f4054c07f4008c010c02e4036408bc0a740d040de406500717]))
(.node (.leaf [0xb280b260b240b22,0x8fb018b,0xa470397,0x5e105b1,0xe7107f1,0xe290b59,0x7150719])
(.leaf [0xd100b9,0x4430293,0xb4d0485,0x89b0703,0xcf50965,0xef70e67])))
(.node (.node (.leaf [0x6f006ee06ec06ea,0x8650145,0x5690371,0x7910571,0x98d07ad,0xb270adf,0x4940492082f])
(.leaf [0x657007f,0x28f0237,0x78d0435,0x86906d1,0xb4b092b,0xe5d0d45]))
(.node (.leaf [0x2510009,0x39d01cd,0xba103c9,0xa0b05fb,0xc010839,0xbf70bbf,0x5b10650064c03500a1804f40127083007f3])
(.leaf [0x21d00d5,0x95302f3,0x72304d3,0xacf0747,0x9e109c1,0xd1f]))))
set_option maxRecDepth 5000 in
private def rowsBasePart53 : Table := (.node (.node (.node (.leaf [0x1b001ae01ac01aa,0x26f00ff,0xaf3031b,0x74f052f,0x7a30773,0xda70a37,0x64b072408bf0b640cf4038a055202ae0524083a0a52036e08e60a32077c099c038e055602f208e2082c083c09f40a5402f80522073207b903700330032c0b0206940e100b620cf202d9])
(.leaf [0x5690031,0x81701ef,0x74303f3,0x8310651,0xb010891,0xc7f0c47,0x71401cb06dc0650064f0bc0]))
(.node (.leaf [0xa080a060a040a02,0x7850175,0x6e7038f,0x9af059f,0x9e307e3,0xb690b49,0xbc00bbc0bbe])
(.leaf [0x36b00a3,0x3f30283,0xb3d0465,0x72706ef,0xb7f095f,0xe9f0e37])))
(.node (.node (.leaf [0x5e005de05dc05da,0x38d0135,0x5510369,0x7590569,0x9750795,0xd7f0ac7,0x507f5036e03a605be00b2056a078a09620b68098e0996010e02e600b4038c05540098032003d006d00af8060207e20a3202e801f0077e08640b140212036a03a20d880945041a0692007002d80408067007b809c009e0007202d20bde057005e80790083a0a520250069801c6034e0b1600d801d8006c00e403c4074a095203b807b005e20173])
(.leaf [0x1110079,0x5af021f,0x6370427,0xdcf06af,0xbf50905,0xd530d1b,0xb28]))
(.node (.leaf [0xe800e7e0e7c0e7a,0x37101c9,0x7c103c1,0x7b905e1,0xa4f082f,0xe590b91,0x5af06500714064c083007f3])
(.leaf [0x20900d1,0x6e302eb,0xb7504c5,0xd5b0733,0xb6f09af,0x565]))))
set_option maxRecDepth 5000 in
private def rowsBasePart117 : Table := (.node (.node (.node (.leaf [0x3d003ce03cc03ca,0x37d0115,0x703033b,0xbc10551,0xd8f077f,0xaa50a75,0x5056302e40a740de40b3e03e807f80b400d3e0d09])
(.leaf [0x5a90051,0x5c50205,0x7e70407,0x953066b,0xbbf08bf,0xe350ced,0x650064a0d0406e1]))
(.node (.leaf [0xc300c2e0c2c0c2a,0x93d01ad,0x6d103a9,0x99305b3,0x83507fd,0xd350b65,0x5af008c010e06de0128041e0abe008a044a064d0831])
(.leaf [0x75700b7,0x8e302ab,0x50b04ab,0xa190719,0xd370987,0xc23])))
(.node (.node (.leaf [0x7f807f607f407f2,0x4cb015b,0x5790379,0xd150575,0xdb907b9,0xdfd0af5,0x1f401f601f8])
(.leaf [0x2e5008d,0xa15024d,0x8210441,0x8b706d7,0xb610949,0xdb30d93]))
(.node (.leaf [0xc70017,0x22101d9,0x74f03df,0x7d50625,0xe150855,0xe310bd9,0x18001403e80173])
(.leaf [0x3c500dd,0x34b0303,0x52504f5,0x9310759,0xd0509e5,0x38e082c00700158045004f8078a036a03a205ba04180156006c01ce01d00830018805280b280416038c03a605be06ec0203]))))
set_option maxRecDepth 5000 in
private def rowsBasePart13 : Table := (.node (.node (.node (.leaf [0x70006e006c006a,0x69500e5,0x343030b,0x71d050d,0x78b075b,0xbe50a0d,0x14056603e80650008a0172034a008c010c0364071408bc0a740aec0de4064a035007f9])
(.leaf [0x1d3001b,0x96901d9,0x42303eb,0xc65062d,0xad3086b,0xe7d0bf5,0x53]))
(.node (.leaf [0x8b808b608b408b2,0x7810169,0xb55037d,0x7930583,0x9bd07c5,0xcbb0b23,0x59e059c05a0])
(.leaf [0x2d30093,0x2c3026b,0x66f044f,0x8c106e1,0xb690951,0xdfb0dd3])))
(.node (.node (.leaf [0x498049604940492,0x2c50125,0x523034b,0x9390559,0x7c90791,0xdcb0a8b,0x5056307f50719])
(.leaf [0xed005d,0x4fb020b,0x4510419,0x9af067f,0xc7508d5,0xe3b0cfb,0x65001d001ca]))
(.node (.leaf [0xd280d260d240d22,0x94901b9,0xa5f03a7,0xc1b05bb,0x8510809,0xb9f0b7f,0x38e0728038c0b0607260b020779])
(.leaf [0x1c100c9,0x69902d9,0x6d104b9,0xa7f071f,0xb6909a1,0x37b]))))
set_option maxRecDepth 5000 in
private def rowsBasePart77 : Table := (.node (.node (.node (.leaf [0x278027602740272,0x3830103,0x99d032d,0x777053f,0xb650775,0xe8f0a47,0x5064b07b601d10d3e038e0365])
(.leaf [0xd3003b,0x3c10201,0x65703ff,0x8350655,0xe37089f,0xdfb0c83,0x71401d006dc0650]))
(.node (.leaf [0xae80ae60ae40ae2,0x78d0185,0xb67038f,0x9b505a5,0xb4b07eb,0xe1d0b4d,0xf000efe0efc])
(.leaf [0x5f500ad,0x557028f,0x6e10479,0xad306f3,0xb4b0963,0xed90e59])))
(.node (.node (.leaf [0x6b006ae06ac06aa,0x2f90149,0x3a5036d,0x5c7056f,0xb3107a1,0xc8b0ad3,0xc24044a082f])
(.leaf [0x64f0077,0x567022f,0x8410431,0xceb06c3,0xb3f0927,0xe3b0d3b,0xd04]))
(.node (.leaf [0x890009,0x21301cb,0x7c703c7,0x6390601,0xa430833,0xdfd0ba5,0x369071408c004f4017206dc])
(.leaf [0x1d900d9,0x67102f9,0x51304d3,0x93b0743,0xc7f09b7,0x977]))))
set_option maxRecDepth 5000 in
private def rowsBasePart45 : Table := (.node (.node (.node (.leaf [0x170016e016c016a,0x12500fd,0x697031f,0xce10529,0x7a7076f,0xa990a39,0x84038e03c6055607b608d608f6098e0c0e07f80b2604d80728087808c80de80874053005a8078000e8020803100328065803f6043e082e09460c860d960bec0b7e0d4e0e260e9e036a03a2053205ba094204180136028e0416068607ce03f2043a06820a4a01bc038c052c0554083001d80c820bf00e8007e20a3200e403a405bc07cc0ba40206056e057e078e09a60134028c099001cd])
(.leaf [0x1e5002d,0x3b701ef,0x5f903f9,0x6a7064f,0xaf30883,0xc7d0c35,0x714095e00d1011004f80bc00e7807f206dc]))
(.node (.leaf [0x9c009be09bc09ba,0x44b0173,0x5af038f,0x77f059f,0xb4507dd,0xde30b3b,0xae80ae60ae2])
(.leaf [0x1af00a7,0x59f027f,0x6d10469,0xac506e5,0x9b3095b,0xec30e2b])))
(.node (.node (.leaf [0x5a0059e059c059a,0x8390131,0x38d0365,0x5ab0563,0x7c30793,0xe9b0abb,0x3a6056a078a0962038c03a206d007e20a320864030401420750040806700bde00fc0570079003c4003600d6039003c800ae0406066e003800d801d80be0021d])
(.leaf [0x44b006b,0x3cd021d,0x8310421,0xdc506a5,0xb0b08fb,0xe2d0d15,0xef3]))
(.node (.leaf [0xe380e360e340e32,0x20101c9,0x5df03bf,0x9b105d1,0xc1d0825,0xde70b87,0x5c60c2608c1])
(.leaf [0xe900d1,0x94502e5,0xb6f04bf,0x8e50735,0xe7f09a7,0xcd]))))
set_option maxRecDepth 5000 in
private def rowsBasePart109 : Table := (.node (.node (.node (.leaf [0x380037e037c037a,0x6df010f,0x4d7033f,0x7810551,0xb7b077b,0xd210a61,0x24c0072024a03ce0074012407180d3e0a180716])
(.leaf [0x213004b,0x4990209,0x74b0403,0x6a5066d,0x91908c1,0xd250ced,0x8a5]))
(.node (.leaf [0xbf00bee0bec0bea,0x1f501ad,0x5b903a9,0x7bb05b3,0xbf107f9,0xcf30b63,0x5af071406dd010e052e054e075609e60b3e017807f50d3d0831])
(.leaf [0x38100b9,0x45102b1,0xc5d0495,0x8bd0715,0x9c5097d,0x784])))
(.node (.node (.leaf [0x7b807b607b407b2,0x8730153,0x5350375,0x8b50575,0xaf907b9,0xc5b0af3,0x12c0130012e])
(.leaf [0x22d008d,0x64b024b,0x77d043d,0x72106d9,0x99d0945,0xe750d75]))
(.node (.leaf [0x4f0017,0x95f01cf,0x5cf03d7,0x9eb060b,0xb7d084d,0xe430bcb,0x5b1071406dc03cd034d])
(.leaf [0x78f00d7,0x9610301,0x51d04ed,0xd710751,0xba909e1,0x505af025106e1064d00d1]))))
set_option maxRecDepth 5000 in
private def rowsBasePart29 : Table := (.node (.node (.node (.leaf [0xf000ee00ec00ea,0x35500ed,0x6090319,0xba90521,0xb43075b,0xd970a17,0x6dc010e05500717])
(.leaf [0x3f50025,0x21f01e7,0x77303eb,0x7e50645,0xbeb0873,0xe390c19,0x71400d10cba08bd03e60a1607f3]))
(.node (.leaf [0x940093e093c093a,0x8b90171,0x3c3038b,0x7ad0595,0xba907d1,0xdd30b33,0x83808340832])
(.leaf [0x7170097,0xa37026f,0xb290451,0xd0706df,0xb470957,0xe9f0e17])))
(.node (.node (.leaf [0x520051e051c051a,0x8310129,0xb290351,0x74f055f,0xad10791,0xb030abb,0x14008a022a036a03a2053205ba08e209420bd201f0039003c8055807b80c1000b801b801c007400b4000b60156037e0536056e078e095e09660ac60aee0b3e0d760178049804f808780ad00b180c600cc00e980234028c008e02e6031604be04d608760abe04b404bc06cc08a40af40dfc0b660b6e07d80d9801d00468084009f80a500a580de80e78015206820aea02e403f4043c06a409440c84078a09620c82085008e6083a0a520b440b6c0b7c0d4c0e9c04080670068807d00b2803180760079807e20a320d7208700e4800fe022e0406066e092603f2043a0a4a021803a805c004920dfa0e7a07cc09b40b900d380e380ed80ee003e3])
(.leaf [0x2010069,0x3cf0217,0xbeb0413,0x98b0693,0xc8108e1,0xd470d0f,0xd99]))
(.node (.leaf [0xda80da60da40da2,0x4d501bd,0xa7b03ab,0x8bf05c7,0xc0b0813,0xd4f0b7f,0x5af036807140651])
(.leaf [0x3a300c3,0x46302e3,0xc7b04b3,0x8db0723,0xb9b09a3,0x1b3]))))
set_option maxRecDepth 5000 in
private def rowsBasePart93 : Table := (.node (.node (.node (.leaf [0x30002fe02fc02fa,0x285010d,0x6ff0337,0x8a70547,0x993077b,0xbe10a59,0x5ae064b01d0008e02e60a760abe01110d09])
(.leaf [0x20b0043,0x99d01fd,0x43f0407,0x99d065d,0xb1108b9,0xcdf0cbf,0x7140717083a0b3a0420052406940b400e100136028e079007c80bf8039005580522098c0b6408e00ce00e2606920b1600e20492078e07c609a608da0831]))
(.node (.leaf [0xb680b660b640b62,0x4210199,0xa4f039f,0x8d305ab,0x9f507f5,0xd290b61,0x50368])
(.leaf [0x1d100b9,0x63b029b,0x6bd0495,0xd2f0707,0xb510971,0xefd0e7d])))
(.node (.node (.leaf [0x730072e072c072a,0x86d014d,0x747036f,0x97d056d,0xb1107b1,0xd9b0ae3,0x14036904d404980ad0043c0b64038a077a099a07900ace0208020604d600e6062e04960b96043a00e800180630094c077e099e09a609d60164032c01680330052a078e09d40173])
(.leaf [0x55f0087,0x2950245,0x8470437,0xa5706cf,0x985093d,0xe610d51]))
(.node (.leaf [0x6d000d,0x46701cf,0x5e703cf,0x66f0607,0xaa3083b,0xe3b0bbb,0x714064d06dc])
(.leaf [0x33500d5,0x34502fd,0x89b04d3,0x785074d,0xd3d09bd,0x72044a010e007602b1]))))
set_option maxRecDepth 5000 in
private def rowsBasePart61 : Table := (.node (.node (.node (.leaf [0x1f001ee01ec01ea,0x3a90101,0x9990329,0x5690539,0x93d0775,0xd0b0a3b,0x5ae09ba09780563])
(.leaf [0xd30033,0x4c901f9,0x80503f5,0xa15064d,0xe330893,0xe930c5b,0x1cb049405c40b140c240c5c05280464082c0b3c01bc038c0554065100d805220090037003a808800bd800c601fe0946075a0792047804d807280b680ba00cf8031e04b606ce0b3a0c9a008c0692045007d00ce0089e0c5e0b16078a0cda0e4607cc05510177]))
(.node (.leaf [0xa500a4e0a4c0a4a,0x4390181,0x775038d,0x77b05a3,0xbdd07e5,0xd050b45,0xd3e0d400d3c])
(.leaf [0xd100b1,0x6230283,0x4cb046b,0x8e306eb,0xceb095b,0xeab0e3b])))
(.node (.node (.leaf [0x628062606240622,0x7230133,0x73f0367,0x8e70567,0x9d10799,0xb150acd,0xd050d09])
(.leaf [0x21f0077,0x4d70227,0x62b042b,0x88706bf,0xe5d090d,0xe350d2d,0xdfb]))
(.node (.leaf [0xed00ece0ecc0eca,0x47f01c7,0x5ab03c3,0x9d505e5,0xba90831,0xe5f0b97,0x5af04bc03e603cc041c041e064b04c008840717])
(.leaf [0x32900d1,0x33102f9,0x71d04cd,0x7790741,0xc6709af,0x95d]))))
set_option maxRecDepth 5000 in
private def rowsBasePart125 : Table := (.node (.node (.node (.leaf [0x410040e040c040a,0x6e30113,0xb15033d,0x5af0557,0x95d0785,0xc290a79,0x5056303680d3e])
(.leaf [0x17d0055,0x9a70207,0xbdf0407,0x6ab0673,0xcbd08bd,0xd2f0cf7,0x64d]))
(.node (.leaf [0xc800c7e0c7c0c7a,0x36501b5,0x73303a3,0x78b05bb,0xb5307fb,0xe0b0b63,0x5af03680714064c06500d3d07f5])
(.leaf [0x30100c1,0x5b702b7,0x81304ab,0xb290719,0xd3d098d,0xe5b])))
(.node (.node (.leaf [0x838083608340832,0x1990169,0x7690379,0x7610581,0x9db07bb,0xdc70b07,0x3be03bc03c0])
(.leaf [0x567008f,0x6550255,0x6610449,0xae906d9,0xe9d0945,0xe7b0d93]))
(.node (.leaf [0x1d10019,0x4ab01d3,0x62703e7,0xc610629,0xe1f085f,0xc290be1,0x5b101e803a203a40567])
(.leaf [0x20500e5,0x4d90309,0x7f504f5,0xac70757,0xa5509f5,0x4405af064b04d800ae01c6020e034007f907d6081e04b406cc0c1803080ace0b680cf807e20a3209640748026c00d801d804b606ce03a605be0bdc0da4027002c80a5200c60262042a062a089e0b06069407e40a34039003c80be00da8056c0c160563078f]))))
set_option maxRecDepth 5000 in
private def rowsBasePart3 : Table := (.node (.node (.node (.leaf [0x20001e001c001a,0x32100e9,0x6cb0303,0xcbd04f5,0xb3f0757,0xa570a07,0x4405af0078023003e804200192034a064b06e1000e00ae00e600ee01c601ce0206020e030e034e06560164032c046404940944022e02ae03160070019803400450049804f807f90a17])
(.leaf [0x5510019,0x55701d7,0x73f03e7,0x81b062b,0x8c10869,0xc1f0be7,0x5b109bb]))
(.node (.leaf [0x868086608640862,0x32f0167,0xb4d0375,0x8cf057f,0xb2f07bf,0xc850b15,0x450044e044a])
(.leaf [0x1770097,0x567025f,0x7950445,0x71706df,0x9a3094b,0xef30d93])))
(.node (.node (.leaf [0x440043e043c043a,0x3a90121,0x9b70347,0x77d0555,0xb250785,0xbe50a7d,0x64a02e60abe0c82064c09450de9])
(.leaf [0x2210059,0x3a7020f,0x767040f,0x97d0675,0xe9908c1,0xe1f0cf7,0x6500d04]))
(.node (.leaf [0xcb80cb60cb40cb2,0x47101b9,0x77f03a7,0x7c105c1,0xbc507fd,0xe490b69,0x5af0368098c07f4007602ae0696082e094600d10126031e06de03e60aba06e102ac0830017802e2031c09440b3e])
(.leaf [0xe300c3,0x5a102c9,0xb6704af,0xe010719,0xb950995,0xf03]))))
set_option maxRecDepth 5000 in
private def rowsBasePart67 : Table := (.node (.node (.node (.leaf [0x220021e021c021a,0x11f0107,0x503032b,0x7590539,0x98f0777,0xd290a41,0xd920a740a160d3e0d09])
(.leaf [0x4030033,0x81d01f5,0xbcd03f5,0xc83064b,0xabf089f,0xdd50c65,0x4f207f2008c010c02e4036408bc0a740d040650064a05690717]))
(.node (.leaf [0xa880a860a840a82,0x3030183,0x7910391,0x7b905a9,0x82307eb,0xe2f0b47,0xde40de20de8])
(.leaf [0x2db00ab,0x2c3028b,0xb45046d,0xacd06ed,0xe77095f,0xe5d0e45])))
(.node (.node (.leaf [0x658065606540652,0x47d013d,0x9e90369,0x9790569,0xb210799,0xc850acd,0x507f508bf])
(.leaf [0x2ab0073,0x24d022d,0x6990431,0xacf06bf,0xe610919,0xee50d2d,0xb41]))
(.node (.leaf [0xf000efe0efc0efa,0x57901c9,0x70303c3,0x64d05f5,0xc27082f,0xd490ba1,0x5af06500714064c])
(.leaf [0x65700cf,0x47902f9,0x82704cf,0xb3b073b,0xee709af,0xb25]))))
set_option maxRecDepth 5000 in
private def rowsBasePart35 : Table := (.node (.node (.node (.leaf [0x120011e011c011a,0x3d700ef,0x9790319,0x82f0527,0xe310761,0xcfd0a1d,0x84038e0556056607b608860072022a0882019803200230074007f80ac00146019602f6033e044e0496004a00c20126031e03ce04b604be06ce08a60af60b260dfe02e8036804c004d80728049404f408640acc0b140c5c05a8074807800960001000b000b800e800f001c8007602e603f6043e06a6082e09460c860b7e0e26008d])
(.leaf [0xb7002f,0x4cd01e5,0xac303eb,0x93d0645,0xe250875,0xda70c27,0x1cf02840364052c05a40744077c02860496087609160ace0b160c5e010c02e404bc04d4087409e40a740d040de4032004b804c00a180aa80af80d4003e809e80d88031c088807f3]))
(.node (.leaf [0x970096e096c096a,0x1a90179,0x557038f,0x9a70597,0xa1707d7,0xb670b3f,0x97809740972])
(.leaf [0x2c100a1,0xa410279,0xc2f0457,0x86f06e7,0xb6f0957,0xeaf0e1f])))
(.node (.node (.leaf [0x550054e054c054a,0x3bf012f,0x9c90359,0x8df055f,0xb65078d,0xc5b0abb,0x64a07f50b400b3e0ea0094500cf])
(.leaf [0xd5006d,0x5a30213,0x6290421,0xaa30693,0xaef08e7,0xe270d0f,0xef5]))
(.node (.leaf [0xde80de60de40de2,0x7e501bd,0x7b703b7,0xc2905c9,0xc13081b,0xdf50b7d,0xc5e062206260c5a09a9])
(.leaf [0x62f00c7,0x49d02e5,0x71504bd,0xb030723,0xcb109a9,0x3bb]))))
set_option maxRecDepth 5000 in
private def rowsBasePart99 : Table := (.node (.node (.node (.leaf [0x330032e032c032a,0x365010d,0xb0b0333,0x597054f,0x99f077f,0xd5d0a55,0x64b07b6071607580b4001240414041808300de809440b260567])
(.leaf [0xc3004b,0x3910209,0x6070407,0x83f0667,0xc0108b9,0xe970cbf,0x714]))
(.node (.leaf [0xba00b9e0b9c0b9a,0x9030193,0x3cf03a7,0x9bb05ab,0xa5507f5,0xe3b0b5b,0x7240b640522094209480b48095609ae0926020e052409220b62020c03740b46057807c009a00722099a03d40b980831])
(.leaf [0x2ed00b5,0x2d302ab,0x82b0493,0x8af070f,0x9c10979,0xf010ea1])))
(.node (.node (.leaf [0x760075e075c075a,0x3050155,0x9f3036b,0x5c10579,0x99b07b3,0xcbb0aeb,0xb80b7e003001e803a8097803c202200ba80206006a020800e807f0006e000e002e00b600e601c6020e0218075c079400d601fe03be03c605a6040005a80b80044601fc07960b4a01e003cd])
(.leaf [0x95008d,0x3e3024b,0x64b043b,0xcf506cd,0xb610941,0xe930d53]))
(.node (.leaf [0x9f000f,0x54d01cd,0x7b903d1,0x9290609,0xc05083d,0xe250bc5,0x8bd010e036603e9])
(.leaf [0x39100d9,0x63302fb,0xc9b04d3,0x9510751,0xbab09c3,0xa7409e609e20d0806e1]))))
set_option maxRecDepth 5000 in
private def rowsBasePart19 : Table := (.node (.node (.node (.leaf [0xa0009e009c009a,0x7b900e9,0xae3030b,0xb9b050b,0x797075f,0xa890a19,0x505af0251])
(.leaf [0x557001f,0x3ab01db,0x43903f1,0x95b0633,0x8bd0875,0xe5f0c07,0x3c3]))
(.node (.leaf [0x8e808e608e408e2,0x337016f,0x5930383,0x777058f,0xb1907c9,0xd930b23,0x6e006dc06de])
(.leaf [0x31f0097,0x545026d,0x6b90451,0x9e906e1,0xd110951,0xe0b0de3])))
(.node (.node (.leaf [0x4c804c604c404c2,0x41d0125,0x64f034f,0xbc50555,0x9710791,0xc290aa9,0x5ae056304f80316034b])
(.leaf [0x4410061,0x835020d,0x7570417,0x9610689,0x91f08df,0xd4f0d07,0x65001d0]))
(.node (.leaf [0xd580d560d540d52,0x20701bf,0x3cb03ab,0x5e505c5,0xb430803,0xd070b7f,0x5af08bd0b680dfe083006e107f402ae082e01c801d00208021002ac03a405bc045001780e000e720744077c099c0b3c008a049207aa03e60c360c5e078a0094031409b805a2077a099a09a202060251])
(.leaf [0x1ff00c7,0x93f02df,0x7d704b7,0xb2d071d,0xd4d099d,0x5cb]))))
set_option maxRecDepth 5000 in
private def rowsBasePart83 : Table := (.node (.node (.node (.leaf [0x2a802a602a402a2,0x7ef0107,0xb090331,0x59d0545,0x7b3077b,0xcf10a51,0xb3e0b400cf80964095609ae09680b63])
(.leaf [0x40f003f,0x5910201,0x77f03ff,0xa1d0655,0x8fd08b5,0xcdf0c9f,0x1cd06dc08bd06510717]))
(.node (.leaf [0xb180b160b140b12,0x443018b,0x5af0397,0x5db05ab,0xbe707ef,0xdf10b59,0x5071406dd])
(.leaf [0x75100b1,0xa55028d,0xb4b047b,0x8870707,0xc790969,0xee90e61])))
(.node (.node (.leaf [0x6e006de06dc06da,0x7510149,0x563036b,0x78d056d,0xb9907a9,0xb190ae1,0xd080a7806df])
(.leaf [0x257007f,0x26b0233,0x6590439,0x71906d1,0x96d092d,0xef90d41]))
(.node (.leaf [0x24d0005,0x36f01cf,0xb9d03c5,0x93f05ff,0xb990839,0xe6f0bb7,0x5b10714071702e60606082e09460c86031404f4052400b800e801d0020802e80aba0b220d720e72008a01720046041c088406dc])
(.leaf [0x21700d7,0x6ef02f7,0x6df04d7,0xacb0743,0x9db09bb,0xbaf]))))
set_option maxRecDepth 5000 in
private def rowsBasePart51 : Table := (.node (.node (.node (.leaf [0x1a0019e019c019a,0x26b00fb,0x98d031d,0x5610531,0xb5f076f,0xd4f0a37,0x14064b0719098c0b64096809e00ba803e8031e038a055205da098a0b8003a60744077c099c00a800c802000dfe01be038e05560af409ae082c001807b900ae00e60206020e020803a8096001d404d0041f])
(.leaf [0x4010031,0x5b101f1,0x64f03f7,0x82d064d,0xc870887,0xe770c37,0x494064f078000c40b7e00c80b800320031c04960ba40692077a0831]))
(.node (.leaf [0x9f009ee09ec09ea,0x4f30173,0x6e3038b,0x8b7059f,0x82f07e7,0xb630b43,0xba80ba40ba2])
(.leaf [0x2f700a7,0x8b90281,0x8790469,0x72306eb,0xb790961,0xe9b0e33])))
(.node (.node (.leaf [0x5d005ce05cc05ca,0x2d90139,0x54d0365,0x7530563,0x7d10799,0xc750ac5,0x50a5403a6010e0078009803d0077e03a20d88077c069202d807b8007202d20a520db2064f])
(.leaf [0x10d0075,0x50d021d,0xbf5041d,0xa8b06ab,0xb030903,0xead0d15,0xac1]))
(.node (.leaf [0xe700e6e0e6c0e6a,0x36d01c5,0x7a903c1,0x7b305db,0xa4b082b,0xe550b8d,0x5af0368])
(.leaf [0x1d100d1,0x32702ef,0x6d504c5,0xb130733,0x9e109b1,0x44d]))))
set_option maxRecDepth 5000 in
private def rowsBasePart115 : Table := (.node (.node (.node (.leaf [0x3c003be03bc03ba,0x2450115,0x62f033f,0xbbd054d,0xd87077f,0xc290a71,0x64a0de40b3e0b400ea0064e0d960945])
(.leaf [0x5a5004d,0x5970207,0x7990409,0x83f066f,0xb1908c1,0xe190cf1,0xdfd]))
(.node (.leaf [0xc200c1e0c1c0c1a,0x7d501ad,0x6cd03a5,0x91f05b7,0xe7907f9,0xd010b69,0x2e402e2064f])
(.leaf [0x60f00b7,0x64f02af,0x70b04a3,0xa150715,0xc6d0985,0xbe3])))
(.node (.node (.leaf [0x7e807e607e407e2,0x3ff015f,0x5750375,0xbe70577,0xba907b9,0xdb90af9,0x1e801e601e4])
(.leaf [0x2b10091,0x887024f,0x81d043d,0x8b106d9,0xb410949,0xee70d87]))
(.node (.leaf [0xc30013,0x21d01d5,0x42303db,0xa45061d,0xabf0857,0xe2d0bd5,0x83000cf041c082c041a04f407f3])
(.leaf [0x33500dd,0x33f0307,0xb8704ef,0x7910759,0xbbf09e7,0x5af082c03cc0ba203a208300528039003a40203]))))
set_option maxRecDepth 5000 in
private def rowsBasePart11 : Table := (.node (.node (.node (.leaf [0x60005e005c005a,0x3cf00e7,0xadf0307,0x9190509,0xe270757,0xa7d0a0d,0x6500a18034a0714064a00cf])
(.leaf [0xc7001f,0x96501d5,0xbbf03e7,0xa57062f,0x8b7086f,0xe790bf1,0x5b1]))
(.node (.leaf [0x8a808a608a408a2,0x77d0165,0x757037f,0xd210581,0xe6107c1,0xcaf0b1f,0x57e0580057c])
(.leaf [0x24f0097,0x6630263,0xc1b0443,0x8bd06dd,0xb65094d,0xe7f0db7])))
(.node (.node (.leaf [0x488048604840482,0x2870127,0x4f5034d,0x9350555,0x7c5078d,0xd470a8f,0x24c0250007407f401240111])
(.leaf [0xcf005f,0x4eb020b,0x44b0413,0x80d067d,0xb2108d9,0xe1f0cff,0x65001d001ca08bf]))
(.node (.leaf [0xd180d160d140d12,0x94501b5,0xa5903a9,0x99f05bf,0x84b0803,0xb9b0b7b,0xd3e0c240a1807170830082c064b])
(.leaf [0x1bd00c5,0x69502d5,0x6cb04b3,0x9110721,0xb65099d,0x223]))))
set_option maxRecDepth 5000 in
private def rowsBasePart75 : Table := (.node (.node (.node (.leaf [0x268026602640262,0x3770107,0x7290331,0x73b053b,0xb090779,0xd2f0a47,0x5064b06dd])
(.leaf [0xbf003f,0x3bd01fd,0x6110401,0x6b10659,0xe33089b,0xde50c85,0x1cd06dc08bd07f30350034e082e020800960719]))
(.node (.leaf [0xad80ad60ad40ad2,0x4b30183,0xb63038b,0x98705a7,0xa4707ef,0xd110b51,0xede0ee00edc])
(.leaf [0x37900b1,0x553028b,0x6dd0475,0xa5d06f5,0x9bd0965,0xed10e51])))
(.node (.node (.leaf [0x6a0069e069c069a,0x2f30143,0x3910371,0x5b90571,0xaf107a1,0xb1b0ad3,0xea002e60abe032009080af80b280e0009040acc05280746077e031e02040c860d9600e8020802e80e5607b80c8205240ba40dfc00e407cc07d001640945])
(.leaf [0x64b0073,0x3e90231,0x83d042d,0xad506c5,0xb3b0923,0xe590d39,0xd07]))
(.node (.leaf [0x850005,0x20701cf,0x7b103c9,0x63305fb,0xe7f082f,0xd590ba9,0x5af0650])
(.leaf [0x1d500d5,0x66b02f3,0xb8104d1,0x77f0747,0xba909b9,0x837]))))
set_option maxRecDepth 5000 in
private def rowsBasePart43 : Table := (.node (.node (.node (.leaf [0x160015e015c015a,0x3c300f3,0x693031b,0xcdd0525,0xb4b0763,0xa870a37,0x2d6038e03960556056607b60072022a02d8032001100230043005f0063007f8033a044a0492004e00c601ce0126031e03ce04be09060aa60b2602e8036804c0072808780a780af00d080de80284049405c40874090409140acc0b140c2401d0052806f007380288053005a809600bf600cf007802b003f8060806980830094809c00c880d980bf4060207e20a320aa80b70008f])
(.leaf [0x1b7002f,0x38301eb,0x44103f9,0x6a3064b,0xabf0887,0xc5f0c37,0x71407f907f3]))
(.node (.leaf [0x9b009ae09ac09aa,0x3e70177,0x5a90391,0x5e105a1,0xa2907e1,0xcf70b3f,0xa7e0a800a7c])
(.leaf [0xc500a5,0x5790281,0x6cd0465,0xa4106e9,0x9a7095f,0xe430e2b])))
(.node (.node (.leaf [0x590058e058c058a,0x7210131,0xb37035f,0xcff055f,0xe47078f,0xde30abb,0x507f503680d0407140960])
(.leaf [0x207006f,0x9b90219,0x82d041d,0x99b06a3,0xc0b08f3,0xd510d19,0xef9]))
(.node (.leaf [0xe280e260e240e22,0x1fd01c5,0x5a903c1,0x91105d1,0xb910829,0xd570b87,0x960715064d03e20172032008bf])
(.leaf [0x78100c9,0x6e102e9,0x8e904c1,0xd53072b,0xd5909a9,0xa13]))))
set_option maxRecDepth 5000 in
private def rowsBasePart107 : Table := (.node (.node (.node (.leaf [0x370036e036c036a,0x4190111,0x4d3033b,0x77d054d,0xb17077f,0xd1b0a5b,0x942056201b609480d07])
(.leaf [0x1a3004b,0x4950205,0x66f0407,0xc9f0667,0x91508bd,0xe810ce1,0x6cd]))
(.node (.leaf [0xbe00bde0bdc0bda,0x7c101a9,0x5b303a3,0x5e905b9,0xbeb07f3,0xb9f0b67,0x5af07140a74064c09bc065003ce0d09])
(.leaf [0x37d00b5,0x44b02ab,0xb610499,0x8a70717,0xd050975,0x3aa])))
(.node (.node (.leaf [0x7a807a607a407a2,0x7530153,0x3a90379,0x78f0577,0xaf307b3,0xde50aed,0x110010e010c])
(.leaf [0x177008f,0x5af024f,0x6a7043f,0x71d06d5,0x9910949,0xda50d75]))
(.node (.leaf [0x4b0013,0x7f901d1,0xba903d1,0x94d060d,0xa790851,0xe150bcd,0x5b1071406dc03cd034d0b27])
(.leaf [0x78b00d3,0x95b02fb,0x8a704df,0xb4b074b,0xba309db,0x505af03f4082c0bf60bee0c2605c6086609060ace012403cc04b409040b440070015802f803400b68078a09620a5201e803a205ba0bd200b604180156006c009c02040b0600c608300a580bf004b60bf40598074807800028005800b000b800e802080658018602f6033e09520ad00746077e094009980d28041403f20150038003f00570079009680ac80bdc0da40bc6044f]))))
set_option maxRecDepth 5000 in
private def rowsBasePart27 : Table := (.node (.node (.node (.leaf [0xe000de00dc00da,0x32f00ef,0x6050315,0x72b051b,0xad7075f,0xd3f0a17,0x566022a06dc03e8010e0abe008a055002e8064d0b3a0de208bf])
(.leaf [0x1dd0025,0x96d01dd,0x75703ef,0x827063f,0xadd0875,0xe330c13,0x9bb]))
(.node (.leaf [0x930092e092c092a,0x785016d,0x3bf038f,0x7770597,0xba307cb,0xef90b29,0x7ba07c007be])
(.leaf [0x5b10099,0x8a90271,0xb23044b,0xaf106e1,0x9b10959,0xe370e17])))
(.node (.node (.leaf [0x510050e050c050a,0x82d0125,0xb23034b,0x5b90561,0xacd078d,0xaf70abf,0x3a205ba0390055807b80ac60b660b440d4c0408067007980a3208700406066e021803a805c009b40b900d380e380ee000c8094c0b640776078009a0074a0952093e0b8e0d2609a809b80b480d220d320e32021206e80b7b])
(.leaf [0x1fb0063,0x3a90219,0xaed0415,0x82f0697,0xbcd08dd,0xea10d09,0xa79]))
(.node (.leaf [0xd980d960d940d92,0x39101c1,0x79b03ab,0x7c905c9,0xa1f0817,0xd4b0b7b,0x5af0368071406510717])
(.leaf [0x33f00c7,0x32f02e7,0xb6504b5,0x8c70727,0xb6909a9,0x123]))))
set_option maxRecDepth 5000 in
private def rowsBasePart91 : Table := (.node (.node (.node (.leaf [0x2f002ee02ec02ea,0x237010f,0x6750335,0x8610549,0x94f077f,0xbdd0a55,0x5064b07b60d3e])
(.leaf [0x16b0043,0x8290201,0xbd90401,0x973065b,0xb0d08b5,0xcdb0cbb,0x7140717082a0524082c079009680ba80558075805220b7e0ace0b160c27]))
(.node (.leaf [0xb580b560b540b52,0x41d0195,0x56103a1,0x88705af,0x84107f9,0xcf10b61,0x505ab071603cf])
(.leaf [0x1cd00b5,0x445029d,0x5050495,0xd2b0703,0x9c90971,0xf050e75])))
(.node (.node (.leaf [0x720071e071c071a,0x7590151,0x743036b,0x94f056f,0xb0d07ad,0xb2f0ae7,0x50a740d040a160d3e02500650064c])
(.leaf [0x30f0087,0x9f30233,0x7b10439,0x8a906d1,0xcf30933,0xe5d0d4d]))
(.node (.leaf [0x3f000f,0x46301cb,0x5c903d1,0x6510609,0xa6f083f,0xd870bbf,0x5b107140650064c])
(.leaf [0x2f900d9,0x33702ff,0x7e904d9,0x77f074f,0xc8509bd,0x10e01260075]))))
set_option maxRecDepth 5000 in
private def rowsBasePart59 : Table := (.node (.node (.node (.leaf [0x1e001de01dc01da,0x3a500fd,0x71d0325,0x5630533,0x9370777,0xc0f0a3f,0x14064b06dd0719098c0b640b9c0cf40e540bf60220079007c8096809e00ba8007803e804200ac00db80e80008e019602d6031e005202d2038a03c2055205da07b2098a02ae04f40524083a0a520db20b8001e6036e03a605be075608e60a3200fc026c06040744077c0924099c0b3c00a800c801f002000dfe010e01be038e052e0556073e0b3e02f2033a08e206bc07040af4095609ae0179])
(.leaf [0xb70037,0x3c101f9,0x79103f9,0x9bd064d,0xbd50895,0xe7f0c5f,0x1d007f206dc010c0365064b]))
(.node (.leaf [0xa400a3e0a3c0a3a,0x435017d,0x7290391,0xd2f059f,0xb7f07e7,0xcff0b47,0xd180d120d14])
(.leaf [0xc900b1,0x5c70287,0x4ab046b,0x8df06ef,0xcbf095f,0xe530e3b])))
(.node (.node (.leaf [0x610060e060c060a,0x42d0135,0x6e10369,0x8990569,0x9c50795,0xb090ad1,0x64a07f507150d09])
(.leaf [0x1b90079,0x3ab0223,0xafb0423,0x88306bb,0xb1b090b,0xee10d29,0xaf9]))
(.node (.leaf [0xeb80eb60eb40eb2,0x39501c5,0xb9703bf,0x7c105e9,0xba3082b,0xe030b93,0x3cc0ba20dfa0b220717])
(.leaf [0x31100d1,0x32b02f3,0x6e504cd,0x775073d,0xb9f09af,0x7bd]))))
set_option maxRecDepth 5000 in
private def rowsBasePart123 : Table := (.node (.node (.node (.leaf [0x40003fe03fc03fa,0x3eb0113,0x9b10341,0x5a10559,0x7bd0785,0xc250a75,0x4403a205ba01f003900558038e055607900b66077e099e05a80780078a00c603a400d201d200d401d407b3])
(.leaf [0xe90059,0x8310209,0xbdb0403,0xda3066b,0xc5f08bf,0xd2b0cf3,0x75]))
(.node (.leaf [0xc700c6e0c6c0c6a,0x1ff01b7,0x70f03a7,0xd4705b7,0xa5f07ff,0xded0b65,0x566071406dc0d3d010c007202aa02e20942007403cc0831])
(.leaf [0x1e500bd,0xa7902b1,0x7fd04ad,0xaf90719,0xc73098b,0xe23])))
(.node (.node (.leaf [0x828082608240822,0x1950165,0x7650375,0x75d057d,0x9b707bf,0xc7d0b05,0x37c037e0380])
(.leaf [0x3190091,0x55b0253,0xc15043d,0xa2106d9,0xd070947,0xe770d97]))
(.node (.leaf [0x1cd0015,0x3a701d7,0x43103e9,0xa4f0627,0xbb3085b,0xc250bdd,0x5b1024c0007])
(.leaf [0x20100e9,0x4d50305,0x73904f9,0x9690759,0xa3709f7,0x505af025106dc064a]))))
set_option maxRecDepth 5000 in
private def rowsBasePart7 : Table := (.node (.node (.node (.leaf [0x40003e003c003a,0x3b500e5,0x9650305,0xb9504fd,0xd730753,0xd650a05,0x23003e8008a02e206e1022a008e])
(.leaf [0xad001d,0x7fd01d5,0x7f903e9,0x9ab062b,0xe1d0865,0xc290bf1,0x5b100b20602022f]))
(.node (.leaf [0x888088608840882,0x4d30163,0x57f037f,0xbed057d,0xbab07bb,0xd830b13,0x550054c054e])
(.leaf [0x1970097,0x8990261,0x7b70447,0x72906e1,0xb3d094d,0xdc30da3])))
(.node (.node (.leaf [0x468046604640462,0x26d0125,0xb210349,0x8710559,0x7bb078b,0xd9f0a7f,0x5056303680d090945])
(.leaf [0x4390059,0x3c7020f,0xae7040f,0x9a90679,0xb1308c3,0xd350cfd,0xd05064f04680b400462095a03ea078a0ac20b3a05be089600c401fc02700e7e078c07c409a601c403bc06bc07740a340a3c0b640ba800aa00c2094a07600b48070807c80ba0059e08da09120b020d4a030407e405bc08de06ce0c16042c082d]))
(.node (.leaf [0xcf80cf60cf40cf2,0x56701b7,0x79703a7,0x8ff05bf,0x83b0803,0xd3d0b6d,0xb640b6c0b9c0cf40b6e0b7e09620b8009a209a10b3b])
(.leaf [0x1b500c5,0x45102d9,0x50504b5,0x8cd071d,0xd470997,0x12b]))))
set_option maxRecDepth 5000 in
private def rowsBasePart71 : Table := (.node (.node (.node (.leaf [0x248024602440242,0x27d0105,0x6a90331,0x8610539,0xac70777,0xc0f0a47,0x64b02e404980ad00b180c600cc003e60b7e0e9e0758077e09a6038a0552077c0b3c0e9c0abe0e760e7e039005580b4001ca0cba079009680b64041604960ace0b160412068200cf])
(.leaf [0x5710039,0x38b01fb,0x44503fd,0xd93064b,0xb0908a1,0xdfd0c7d,0x71404f207f2010c02e4036408bc0a740d040650064b0569]))
(.node (.leaf [0xab80ab60ab40ab2,0x34f0187,0xa3b038b,0x91305a3,0x83507ed,0xb810b51,0xe540e580e56])
(.leaf [0x30700af,0x403028b,0x4d30473,0xd1506ed,0x9ab0963,0xef30e43])))
(.node (.node (.leaf [0x678067606740672,0x1690149,0xb410369,0xd070567,0xb810799,0xeaf0acf,0x5008c010c036404d40aec054e07560290041801ca0412046204f2082a0a4a0e7203e70af008820af20c320c5a04640cec07780b80008e02ae0e46077a098a0b280db80e780ef802ac034c043c0694082c09bc081e0bf608860b16009803500af8098c0ef4033a09160c5e0cbe02d206920db2041c043a0622068207b60179])
(.leaf [0x4bb0073,0x26f022f,0x7790431,0x88f06c7,0x9450925,0xe370d37,0x4be]))
(.node (.leaf [0x190009,0x95701c7,0x72b03c3,0x7e905f9,0xdff082f,0xd4d0ba5,0x5af0714064d0830])
(.leaf [0xed00d5,0x4bd02f5,0x89904d1,0x7730743,0xb7f09b7,0x4ef]))))
set_option maxRecDepth 5000 in
private def rowsBasePart39 : Table := (.node (.node (.node (.leaf [0x140013e013c013a,0x6b100f1,0xaf10319,0x9090529,0x7a10769,0xbc30a23,0x2d6038e056607b6007202d8011007f8044a0492004e00c601ce012603ce04be0aa6036804c007280af00de8049409140b1401d00528073805a800e60206007802b008300c880aa802ae010e])
(.leaf [0x15b002b,0x56901e9,0x42f03f7,0x693064b,0xae90881,0xe7f0c27,0x1cf05a4077c0cec0cbe04740a7404b806d00a180d400bf8082c083c0a4c0a5403f2043a06820a4a09b20b420b7a0cba0cea0b620cf20d0900c8098c0c7c0692082a0d92056007500bd00c180ef800e20852044a0ef2083a0a520bf20e160e360b6605a807800e58069407d403a4]))
(.node (.leaf [0x990098e098c098a,0x33b0173,0x5610391,0xd250595,0xb6707d7,0xcef0b3f,0x9c409c809c2])
(.leaf [0x5b7009f,0x437027f,0x4990469,0x8d506e5,0xd190959,0xe470e27])))
(.node (.node (.leaf [0x570056e056c056a,0x455012d,0x547035f,0x96b055b,0xda5078d,0xc670abf,0x507f503680d04071409600b40])
(.leaf [0x177006f,0x8410219,0x7b3041b,0xdb90699,0xc8508e5,0xe490d11,0xd40]))
(.node (.leaf [0xe080e060e040e02,0x94d01bd,0x59f03bf,0x7c705cf,0xb7b0823,0xba70b87,0xaf40420041c0af807b3])
(.leaf [0x63900c9,0x64f02e7,0x88504bd,0xd510729,0xd2309a3,0x59b]))))
set_option maxRecDepth 5000 in
private def rowsBasePart103 : Table := (.node (.node (.node (.leaf [0x350034e034c034a,0x3e7010f,0x4bb033b,0x5a90551,0xad7077f,0xbd30a5b,0x64b010e007602b00111])
(.leaf [0xe3004b,0x3c50205,0x6670407,0x94f0667,0xe3b08b3,0xe0d0cdd,0x34d]))
(.node (.leaf [0xbc00bbe0bbc0bba,0x7bb019b,0x56903a9,0xc1105b1,0xb4107f9,0xb950b65,0x5af06dd010e01be075609e60b3e00180090009802f803400450049804f808bf0320035003d004b804c0051806d00aa80b28064e0d96098c09bc0aa40b640b6c0b9c0ef407f5])
(.leaf [0x31900b9,0x41302ab,0x8bd0495,0xb210711,0xb590979,0xeff0ecf])))
(.node (.node (.leaf [0x780077e077c077a,0x4170157,0xb47036f,0x75d0575,0x9a707b7,0xd750aed,0x400080006])
(.leaf [0x155008d,0x41d024d,0x665043d,0xdd906d1,0xcff093f,0xd8d0d6d]))
(.node (.leaf [0x2af000f,0x57f01cf,0xaa503cd,0x9e30603,0xb9b0843,0xc150bcd,0x5b10651054c0c5c0e940b480b80036501cc0a4c00e4021403a405bc07cc00d601d6098e0b660a4a03f207d008fc0b8c0c1c0edc05700580079009a80594078a075c07940b540030038004d0003200d20c6007580b6800c409460b8e07760e920b27])
(.leaf [0x67100d9,0x6c502fd,0x6eb04db,0xab3074b,0xd4509c5,0xd3e07160a15]))))
set_option maxRecDepth 5000 in
private def rowsBasePart23 : Table := (.node (.node (.node (.leaf [0xc000be00bc00ba,0x21500ed,0x3510319,0x7190519,0x973075b,0xbf50a15,0x140056021e02d60566098e0d3e0072064a009002d80350008c02e404bc0a740d040126034e04be0a160aa60b26028804f805500018063000760286028e01b800d10177])
(.leaf [0xcf0027,0x4c901e1,0x63303eb,0xa5d0635,0x8dd0875,0xe490c11,0x7b3]))
(.node (.leaf [0x910090e090c090a,0x427016f,0x76b0383,0x99b058b,0x9cf07cf,0xdff0b27,0x75807560752])
(.leaf [0x34f0097,0x5bf026f,0x7d10451,0xabf06df,0x99f0957,0xe990de9])))
(.node (.node (.leaf [0x4f004ee04ec04ea,0x4510129,0x7190351,0x5a7055f,0x9bb078b,0xdb30aa3,0x4b406cc0408067007980406066e02f604b606ce0dd602f207960dd40b7b])
(.leaf [0xed0065,0x9b10211,0x7f30413,0xcbf0687,0xb2308db,0xe290d09,0x7f9]))
(.node (.leaf [0xd780d760d740d72,0x36901c1,0x5c303ab,0x78f05c7,0xa7f080f,0xd110b81,0x5af03680714064c0650])
(.leaf [0x2ff00c7,0x31f02e7,0x8db04b3,0xd47071f,0x9d709a7,0xa73]))))
set_option maxRecDepth 5000 in
private def rowsBasePart87 : Table := (.node (.node (.node (.leaf [0x2c802c602c402c2,0x135010d,0x4b10339,0x7490549,0x945077d,0xe970a4f,0x2aa02e2034a07f2094206dc01d00d3e03650567])
(.leaf [0xc70047,0x5c10201,0xad503fd,0xa810659,0x91108b9,0xde90ca1,0x71401d0]))
(.node (.leaf [0xb380b360b340b32,0x32d0195,0xb6d0395,0x7b305ab,0x82d07f5,0xb910b61,0x50651])
(.leaf [0xd500b5,0x5a30293,0x7ed048d,0x8a10709,0xcf90969,0xe7b0e73])))
(.node (.node (.leaf [0x70006fe06fc06fa,0x1710151,0x6c90371,0x867056f,0x99307ab,0xc9d0add,0x4940698031e03200692082f])
(.leaf [0x16b0083,0x3f90239,0x7910439,0x89d06cd,0x98d0935,0xecd0d45]))
(.node (.leaf [0x2570007,0x3a301cb,0x5bf03cf,0xd6f05ff,0xe090839,0xc050bbd,0x5b107140650064c06dc03cd])
(.leaf [0x22100d9,0xacb02f3,0x72704d7,0xb430743,0xba309bb,0xd5f]))))
set_option maxRecDepth 5000 in
private def rowsBasePart55 : Table := (.node (.node (.node (.leaf [0x1c001be01bc01ba,0x35d00fd,0xaf7031f,0x873052b,0x7ad0775,0xa8d0a3d,0x5c6079007c80b8003a605be09d800ee021803a8021605e605e20570078e05ba09d20b7e0d4808b807c60a8c00d3])
(.leaf [0x6b0033,0x98f01ef,0x74703f7,0x945064d,0x8fd0895,0xde30c43,0x1cb049405c40c24038c0554064f077e09b80b80056a078a0962044e0ba4078c09640948036e03a6075a006e049607ee0831]))
(.node (.leaf [0xa180a160a140a12,0x8c10179,0x6fd038d,0xbfd059d,0xa3707e7,0xb7d0b45,0xc000bfe0bfc])
(.leaf [0x74500a5,0x54d0285,0xb410469,0x73306eb,0xc33095b,0xea70e37])))
(.node (.node (.leaf [0x5f005ee05ec05ea,0x3910139,0x5570367,0x87f0567,0x97b0793,0xea90ac9,0x94008e02ae009802ac0178008c044b])
(.leaf [0x1270077,0x845021d,0x7a70427,0x9af06b7,0xbf90909,0xe2d0d1d,0xe01]))
(.node (.leaf [0xe980e960e940e92,0x38d01c5,0xa8d03bd,0x90d05dd,0xa93082b,0xd2f0b97,0x5af0650064c083004bc0076012605c80c280717024a044e03cd])
(.leaf [0x21100d1,0x6e902f1,0xc9104c9,0x76d073d,0xb7b09ab,0x5b5]))))
set_option maxRecDepth 5000 in
private def rowsBasePart119 : Table := (.node (.node (.node (.leaf [0x3e003de03dc03da,0x3810119,0x707033f,0xcef054f,0xe35077d,0xaa90a79,0x7460ace0b1607440acc0b1406bc07040e340e36089e06ba089c0781])
(.leaf [0xd10059,0x5c90209,0xadb0403,0x9590671,0xc2508bd,0xe390cf1,0x1ca03e204f20a74064f]))
(.node (.leaf [0xc480c460c440c42,0x1ed01b5,0x6f703a7,0x99905b9,0x84507fd,0xd390b69,0x5af0368071406dd])
(.leaf [0xd300bb,0x8e702af,0x6d704af,0xaa70717,0xb5f098f,0xd03])))
(.node (.node (.leaf [0x808080608040802,0x77d015d,0x6d70377,0x5c5057d,0xe5907b9,0xe010af9,0x22602280224])
(.leaf [0x2e90091,0xa190251,0x8510441,0xa0d06d5,0xc850945,0xdb90d99]))
(.node (.leaf [0x1730013,0x37701d7,0x41f03e7,0x81d0625,0x8b7085f,0xe370bd7,0x2e4008e02e60abe022a008a022e03e9])
(.leaf [0x7af00df,0x34f0307,0x6eb04f3,0x95f0757,0xd0909e9,0x505af025106e1064d]))))
set_option maxRecDepth 5000 in
private def rowsBasePart15 : Table := (.node (.node (.node (.leaf [0x80007e007c007a,0x69900e9,0x655030d,0x7210511,0x78f075f,0xcfd0a0d,0x1405af007803e806500a18008a017202d2034a008c010c02e4036404bc071408bc0a740aec0d040de4064a])
(.leaf [0x1d90021,0x21901e1,0x42903f1,0xd83062b,0xbc90871,0xd910c01,0x24b]))
(.node (.leaf [0x8c808c608c408c2,0x8a10169,0x3b30383,0x8d30583,0x9c307c3,0xcc10b29,0x5b805b605b2])
(.leaf [0x2d70097,0x3f7026f,0x683044b,0x8c706df,0xc9f094f,0xe010dd9])))
(.node (.node (.leaf [0x4a804a604a404a2,0x3830123,0x527034f,0x9650555,0x965078d,0xd2b0a93,0x110055007f408c006dd])
(.leaf [0x1690061,0x59f020f,0x6850415,0x8090689,0xe4508d5,0xd3d0d05,0x65001d0036900d10569]))
(.node (.leaf [0xd380d360d340d32,0x1f701bf,0xb7b03a3,0xd4b05bb,0xa6b0803,0xba30b7b,0x5af0a180717064b])
(.leaf [0x1f700c7,0x5fb02db,0x71704b7,0xa8d071d,0xb95099d,0x3d3]))))
set_option maxRecDepth 5000 in
private def rowsBasePart79 : Table := (.node (.node (.node (.leaf [0x288028602840282,0x4110109,0x9a10331,0x8a10541,0xb690779,0xbcf0a4f,0x5064b07b601d10d3e])
(.leaf [0x16b003b,0x4cd01fd,0x75b03fb,0x96d0655,0xacb08a3,0xdff0c87,0x1cd06dc08bd065107170d07010c]))
(.node (.leaf [0xaf80af60af40af2,0x7910189,0x5630393,0xc0905a9,0xb5107f1,0xb870b57,0x254036907240288049809180ad00b180bc0028604b6043c06a40b640b9c0e540b7e0d4e037003a8038a05da07b2077a099a0db2079007c80ace0b1608e0020604960208072800e80db8056e057e078e07c609a6032e00b000f0065800d8077e01cf])
(.leaf [0x5fd00ad,0x5cd028d,0xb430473,0xd1b06f3,0xb510969,0xedf0e57])))
(.node (.node (.leaf [0x6c006be06bc06ba,0x4050145,0x3a90371,0x753056b,0x98307a3,0xeb50ad5,0x71406dc08bf])
(.leaf [0x105007d,0x605022d,0xb07042f,0x70706cf,0x95b092b,0xe570d3f,0x945]))
(.node (.leaf [0x970007,0x21701cf,0xa9303c3,0x65705ff,0xa610839,0xe550ba5,0x5af])
(.leaf [0x1df00d7,0x6bf02f7,0x52504d5,0x9430743,0xd3309b3,0x9c7]))))
set_option maxRecDepth 5000 in
private def rowsBasePart47 : Table := (.node (.node (.node (.leaf [0x180017e017c017a,0x1290101,0x715031d,0x54f052f,0xab7076f,0xbd10a39,0x56021e0072012606de00d1007601b801e8010e])
(.leaf [0x1e90031,0x4ad01ed,0x64703f7,0x7f3064b,0xaf70887,0xdd50c35,0x2e80350024e02e40d040aba0c8201b80717064b]))
(.node (.leaf [0x9d009ce09cc09ca,0x4510179,0x6bb038b,0x7ad059d,0x81d07e5,0xde90b41,0xb260b280b22])
(.leaf [0x1b700a7,0x61b027b,0x7f50465,0xd0d06e5,0x9b90961,0xe4b0e33])))
(.node (.node (.leaf [0x5b005ae05ac05aa,0x28f0137,0x3910369,0x5b10569,0x7c70797,0xea10ac1,0x507f503a600b2056a078a096200b4038c07700078077e010e02e6021203a2032003d006d00af8060207e20a3202e8024e041e0864030401420750031e040806700bde00fc0072041a05700790083a0a5200e403c4003600d60af207b60945])
(.leaf [0x4510071,0x3d10221,0xaf5041d,0x83906b1,0xc1f08ff,0xe430d13,0xef6]))
(.node (.leaf [0xe500e4e0e4c0e4a,0x20d01c5,0x71d03bd,0xd5d05cd,0xdf70827,0xf070b87,0x5af0368064d07f9082b0129])
(.leaf [0xf100d1,0x94902e9,0xc8304bb,0x8e90739,0xedf09a7,0x175]))))
set_option maxRecDepth 5000 in
private def rowsBasePart111 : Table := (.node (.node (.node (.leaf [0x398039603940392,0x7f5010d,0x513033b,0x8bf054f,0xb7f077f,0xd370a5f,0x1407f206dc00e603b603ce09a6054c01d1])
(.leaf [0x42b004b,0x5250205,0x7510409,0x6b3066b,0xacf08bf,0xd370cef,0xa15]))
(.node (.leaf [0xc000bfe0bfc0bfa,0x38301ab,0x5bd03a5,0x7c105b9,0xde507f5,0xcf70b67,0xaec0de4041807f508300650094602b00b26044b])
(.leaf [0x60500b5,0x56702af,0xc610499,0x8c10719,0xb590981,0x8b3])))
(.node (.node (.leaf [0x7c807c607c407c2,0x8770157,0x5390379,0x8b90579,0xb1f07b7,0xc610af9,0x17801760172])
(.leaf [0x2310091,0x64f024f,0x7810441,0x85f06d7,0x9a10949,0xe790d79]))
(.node (.leaf [0xa30013,0x20b01d3,0x72903d9,0x7e10621,0xb810851,0xe470bcf,0x65101cc0664083c0a5403a600d40790077a083a0a520406066e078a04080670077e03f2043a03a400b9])
(.leaf [0x1ef00df,0xad502fd,0x72d04ed,0xe210751,0xa1709e7,0x5af04d803f4043c086604b4051406cc07e20b440b7c03400b680ba00cf8078a0962083a0a52079803a205ba00b6040600fc026c0134028c009c02b401620204089e042a004e00c601ce01d008400a5804b606ce05a8096000ae00e600ee01c60206020e06560308023403f2043a01be00b8057007900968086e0d0e0390021603a605be01000270077d]))))
set_option maxRecDepth 5000 in
private def rowsBasePart31 : Table := (.node (.node (.node (.leaf [0x10000fe00fc00fa,0x3bd00ed,0x6df0317,0x7270527,0xb47075f,0xa8d0a1d,0xd3e071806dc0ac008be0716])
(.leaf [0x53002b,0x37d01e5,0x77703ef,0x82b0643,0xbef0877,0xdcd0c1d,0x1cf05510b3c01b400a400c403a40757]))
(.node (.leaf [0x950094e094c094a,0x1970177,0x3c7038f,0x7b10599,0x81d07d5,0xb5f0b3f,0x8be08bc08c0])
(.leaf [0x16b009b,0x4350275,0xc290451,0xde506dd,0xb630953,0xe390e21])))
(.node (.node (.leaf [0x530052e052c052a,0x2810131,0x6af0357,0x857055f,0xb0d078d,0xb090ac1,0x8a022a03a205ba094201b8008e02e6031c04b406cc0dfc08400a5802e40944083a0a520b7c04080670079800fe026e022e0406066e00e8021803a805c00dfa09b4042e062e02f2005000a800c8031e021200e609b80b8009b007960abb])
(.leaf [0x4490069,0x4b30213,0xbef0417,0x98f0697,0xe4708df,0xd530d0b,0x9bc]))
(.node (.leaf [0xdc80dc60dc40dc2,0x4d901c1,0x59703b7,0x9a705c7,0xa17081f,0xdd30b7b,0x5af03680714])
(.leaf [0x3a700c7,0x46702e7,0xc8104b9,0x9130723,0xba109a9,0x1f3]))))
set_option maxRecDepth 5000 in
private def rowsBasePart95 : Table := (.node (.node (.node (.leaf [0x310030e030c030a,0x2890111,0x72f0337,0x9570547,0x997077f,0xc170a57,0x94201b409440567])
(.leaf [0x4290049,0x9a10201,0x44b0403,0x7f30663,0xbe708b7,0xe770cbf,0x7140650071707f3]))
(.node (.leaf [0xb780b760b740b72,0x5270197,0x3c503a5,0x8f705af,0xa4b07f3,0xd310b61,0x505b1])
(.leaf [0x1d500b5,0x40302a3,0x6c10499,0x895070d,0xc8d096d,0xed30e9b])))
(.node (.node (.leaf [0x740073e073c073a,0x1790159,0x75b036b,0xbdb056b,0xb9d07ad,0xec70ae7,0x14036904d4072408c4017804980ad00b180136028e051603f4043c05f408200b640b9c0b7e03a805c0097807e20a32038a0552077a099a083a079007c809680302026c0ace0b1604500ae0020807e80a38020604d6072600e6042e062e066204960b9603f2043a00e805e80134028c0018043006300ca00e10094c077e099e09a609d60164032c0b580eb805e20c9c0e0c0168033000b605800960052a0ada05c7])
(.leaf [0x6d50085,0x5610249,0xb0f0437,0xadb06cb,0x9890941,0xe430d53]))
(.node (.leaf [0x8d000d,0x4a501cd,0x71503cd,0x7f30603,0xb67083f,0xe770bbf,0x5b107140650])
(.leaf [0x33900d9,0x4cb02fb,0xb7b04d3,0x927074f,0xef309bb,0x2e80078010e02e606de0076064b]))))
set_option maxRecDepth 5000 in
private def rowsBasePart63 : Table := (.node (.node (.node (.leaf [0x20001fe01fc01fa,0x40500fd,0x49b032b,0x5770537,0x9830773,0xd110a41,0x5064b06dd071607b6])
(.leaf [0xd90039,0x51701f7,0xacb03f3,0xa190651,0xe390899,0xe970c5f,0x71401cb06dc06510d040569]))
(.node (.leaf [0xa600a5e0a5c0a5a,0x4b10181,0x7790391,0x77f05a7,0xbe107e9,0xd090b49,0xd520d580d54])
(.leaf [0x1bf00af,0x8bd0285,0x6d5046d,0x8e706ef,0xcf10961,0xedb0e3b])))
(.node (.node (.leaf [0x638063606340632,0x83d0135,0x7570367,0x9430563,0xadf0797,0xc450acd,0x507f5036807140173])
(.leaf [0x24b0073,0x5b70227,0x62f042f,0xa3706bf,0xb150915,0xe390d31,0xb5f]))
(.node (.leaf [0xee00ede0edc0eda,0x4e101c9,0x5b103c9,0x95705ef,0xbf5082d,0xd3f0b9f,0x36907140b3e0127])
(.leaf [0x35100d1,0x33d02f5,0x72104d1,0x9390741,0xcb709af,0x9ad]))))
set_option maxRecDepth 5000 in
private def rowsBasePart127 : Table := (.node (.node (.node (.leaf [0x420041e041c041a,0x8010119,0x4cb0343,0x74b0553,0x9ad0785,0xd070a77,0x64a03650ea002e608be0abe034a03e80945075907f5])
(.leaf [0x1ef0057,0x393020b,0x447040f,0x6b10679,0xcc108c1,0xd3d0cf5,0x65007f3]))
(.node (.leaf [0xc900c8e0c8c0c8a,0x36901b9,0x73703a7,0x78f05bf,0xb590801,0xe0f0b67,0x8bd07170831])
(.leaf [0x75b00bb,0x5b702bf,0x8d304ab,0xd3f0717,0xd410991,0xeb3])))
(.node (.node (.leaf [0x848084608440842,0x2e50165,0xa090379,0x797057f,0x9e107c1,0xe0f0b07,0x3d803d603d4])
(.leaf [0x6dd008d,0x6590259,0x6ab0443,0xcff06d7,0xea10949,0xe810d99]))
(.node (.leaf [0x3e70017,0x4af01d7,0x62b03e3,0x697062f,0x89f0867,0xd790be1,0x5b109bb08c101cb03a4])
(.leaf [0x20900e9,0x4df0307,0x8bd04f5,0xaeb0753,0xbcb09f3,0x5af07f90b680a320da4083a0a520a340a94039003c80da8078b]))))
def rowsBase : Table := (.node (.node (.node (.node (.node (.node (.node rowsBasePart0 rowsBasePart64) (.node rowsBasePart32 rowsBasePart96)) (.node (.node rowsBasePart16 rowsBasePart80) (.node rowsBasePart48 rowsBasePart112))) (.node (.node (.node rowsBasePart8 rowsBasePart72) (.node rowsBasePart40 rowsBasePart104)) (.node (.node rowsBasePart24 rowsBasePart88) (.node rowsBasePart56 rowsBasePart120)))) (.node (.node (.node (.node rowsBasePart4 rowsBasePart68) (.node rowsBasePart36 rowsBasePart100)) (.node (.node rowsBasePart20 rowsBasePart84) (.node rowsBasePart52 rowsBasePart116))) (.node (.node (.node rowsBasePart12 rowsBasePart76) (.node rowsBasePart44 rowsBasePart108)) (.node (.node rowsBasePart28 rowsBasePart92) (.node rowsBasePart60 rowsBasePart124))))) (.node (.node (.node (.node (.node rowsBasePart2 rowsBasePart66) (.node rowsBasePart34 rowsBasePart98)) (.node (.node rowsBasePart18 rowsBasePart82) (.node rowsBasePart50 rowsBasePart114))) (.node (.node (.node rowsBasePart10 rowsBasePart74) (.node rowsBasePart42 rowsBasePart106)) (.node (.node rowsBasePart26 rowsBasePart90) (.node rowsBasePart58 rowsBasePart122)))) (.node (.node (.node (.node rowsBasePart6 rowsBasePart70) (.node rowsBasePart38 rowsBasePart102)) (.node (.node rowsBasePart22 rowsBasePart86) (.node rowsBasePart54 rowsBasePart118))) (.node (.node (.node rowsBasePart14 rowsBasePart78) (.node rowsBasePart46 rowsBasePart110)) (.node (.node rowsBasePart30 rowsBasePart94) (.node rowsBasePart62 rowsBasePart126)))))) (.node (.node (.node (.node (.node (.node rowsBasePart1 rowsBasePart65) (.node rowsBasePart33 rowsBasePart97)) (.node (.node rowsBasePart17 rowsBasePart81) (.node rowsBasePart49 rowsBasePart113))) (.node (.node (.node rowsBasePart9 rowsBasePart73) (.node rowsBasePart41 rowsBasePart105)) (.node (.node rowsBasePart25 rowsBasePart89) (.node rowsBasePart57 rowsBasePart121)))) (.node (.node (.node (.node rowsBasePart5 rowsBasePart69) (.node rowsBasePart37 rowsBasePart101)) (.node (.node rowsBasePart21 rowsBasePart85) (.node rowsBasePart53 rowsBasePart117))) (.node (.node (.node rowsBasePart13 rowsBasePart77) (.node rowsBasePart45 rowsBasePart109)) (.node (.node rowsBasePart29 rowsBasePart93) (.node rowsBasePart61 rowsBasePart125))))) (.node (.node (.node (.node (.node rowsBasePart3 rowsBasePart67) (.node rowsBasePart35 rowsBasePart99)) (.node (.node rowsBasePart19 rowsBasePart83) (.node rowsBasePart51 rowsBasePart115))) (.node (.node (.node rowsBasePart11 rowsBasePart75) (.node rowsBasePart43 rowsBasePart107)) (.node (.node rowsBasePart27 rowsBasePart91) (.node rowsBasePart59 rowsBasePart123)))) (.node (.node (.node (.node rowsBasePart7 rowsBasePart71) (.node rowsBasePart39 rowsBasePart103)) (.node (.node rowsBasePart23 rowsBasePart87) (.node rowsBasePart55 rowsBasePart119))) (.node (.node (.node rowsBasePart15 rowsBasePart79) (.node rowsBasePart47 rowsBasePart111)) (.node (.node rowsBasePart31 rowsBasePart95) (.node rowsBasePart63 rowsBasePart127)))))))
set_option maxRecDepth 5000 in
private def hintsBasePart0 : Table := (.node (.node (.node (.leaf [0x1268176b,0x8870155006714cd053b0880014c003000950bbd0a590f6705390bba00d5007c00da0034009c0f3010c10322120e07250f65056706b5018b00ea00140105004f01400087004413140a720323120b073211cf0b220b21056803d60120007d0056010e00fe00ef001b0b7a053f0c141305069307480a4f077f0f860f230c0f04ae04a9042a03c900910164012b0042005100c400dc0026001e0b830c8809d4067f05b004b10e5209b004a30420015e00a50075004100390027012900740a77094c09340922091e066105b704b50647063c00f4006f003f0e541409044904450d77077e032805a4059a058f01390137002100b100380efc0ef90eee0b7904520ce10cdb0cca034100d300a80016090108f708f1044b034a006d09ab060005f800af003b142514110f0006a40417035f03570189004300170406153d05cf035c001d015a003a026b1331132b05ed168b000a012201ab02711539133610c70bcb0c1b0640120a00820161009d01040acd04c10be00bce11ff00ff0096010b11d9086d0510013f0066002d1684146207fd07f4050606d60188005f0084004706d413560808060c0cf0072c05c40a2c0a2906d8004d012300a9007b0b8b0442043610a5109110890cec0cd50a3b054103ee0092002000e90ee30ed70ed50b8c080404410d7f0ce2039a038b03840339026400d200b200190993098f097d09760972096e096208ec069c068505fd03a100721067105f105b0d3f0c840a530983050c03aa06b6092e09bf0c7e178b177017cc17bc17bf1796178817a417a017ad179b17b817a9178d177717be177b1791,0x1d040b040a03fd00760073004109e2099f067300db00ad181e0f6e0d250468010f012b007912770a0d132b01ff016801220003116a0c750c720c700c64020303b500f600a4001a05ef05ec05e605cd03b401fe178f17a317aa17a7177117bf17b1177317be17cb17a6178617ae,0x2f17b0,0x17f12f8164d12a9011f1944011412f60e440e3714eb12a20777193300c3014f005514e312a711ba0e350a9d076a193000fd007f0b1c0b190a8c076c0a990e311158,0x3e500c7001b0a6b03ee007d00e90a660a3a00c6007b0e650ae90a2b00ff008411da0aee013f00e8098c0985007205d8003a035e035a0a350ae703b318ea03c3,0xf741a64])
(.leaf [0x536176e,0xf17df17dc,0x18ae0a64145e00bb023d013f0ddc001711da0e7400c30355033d00ff02ce001a05f906a803d5000f03ae006d0044004317dc001d08f206af069e0492040c00a80076096a096308ea069a0072098509c0092f06b700e800b01054041206eb00ee00490aaa06ea00800aa500e610320150083700620796005b105807ae01d4183318730de10e31115b1164178617ae178d178b178f17b717bb17ab,0x15617c4,0xe90d9703ee1911001b0cfa03d8190c18f70d08061d016e18f416090ff4022f01b51918000613440ff80d06035802231922001705ed035b003a01fc000301ff19010a0a02a3192d000e07b101de05cc005b18e9004102f701e103b603560227001218ea02ee01d201c7004618e806c601d60049066c030a008e00130533030502a918f019af01e900550cb4076f02fd0235190a0cc4062b1924136c06d10371193b00bb1480147a0de806d3192b0dbd17e40f190f1707ac03020c730204011719141908126a0f0d0c700b69192019ae0b1f0a8d076d052f02af09de09db040c190418ff04980493048d02b9031b06b606ec0caf031d09e00f030f6e0f71169213f006ef077307a70dda0e411098136219270e3c13df05ec0a080de2116e11740c7415df06790b190b6412b8016f11bf15d51936116b141614191929141d193e0f7f0d690f7419a01962,0x12f8017f011f12340cc20108190a06f313dd122d0cc800491927192d193b06f8089a07b207af186317e70068005b0e37089207a608970f801a191a161a101a1c,0x1c31aa41aac1aae]))
(.node (.leaf [0x995176c,0x121132807d6018c005d13210f4807c5015e00d6009216aa153508db06a00193015a006c0043159f153a152208ce069a01610159007215c8159115200965069f0165015d00761335133111be11bb0f4006ae012200fd0114004413450b190bac07ca06b301b50086009316fb16941594153f078802c80b380b2b019c018a0059000f0088157b14831481079e0777076502c505ee05de05da05d405d001910142005b0055003a141b15e00e490e420e3507a8077402ce0bf805e113d80138016800c3009917e70f750ba50b9009e11173116a116711580e310bfe0b3005eb00db00f612770f700c010a07010f00790cbd096608d4076f0537052f052c052600a7002f02ff02f402ed0012180f03b4180e03c003ba001a180c06b6078a0caf0d6917bd17d517d3177217c5178f17be178b17b417c617781779179817ac177317c917aa17cb177117b117b617b0178617ae,0xa0700f60079116b0a0d01680c7400a412760c700468010f00220f0c046d17cb17b1177317a617711787,0xb117b8,0x1d218ea18e803c001d617e700490e3b089206ee06ec0d6906f619290f751962,0x6eb1a0d,0x1066014c00e80ecd107a00d101ae0ec7123f07e800da010a005e0f69125a0eeb0bc607e00190191f1913009515b90d160f850eec0bbe016300ac191613900d1908f80f9909b1012a18fb193f18fe13d10d8a0cf008f3159a0bcb06540652064e012d00b2190b00a80161004010970d800cec0cd50d1313b803980394133007ee00e900e71926001919221578138e10a61050087c039d101b0ce50d0613e8015e006600e41912190c19280b9b07f210bd10150da70d010e690e250092005f00ea00c600c20b8e08060a730a680ac100d2007d008216bf15b807fc0441043f0e630abf018f0096002000ff00bf1490113d0e1f0bdc0a77044311da0e0c06970692014600f4013f0042142d11380f5d0877098a09870983097b097008ea0683043c05af05ab013b00d9007200390ec109d209c708e208d708cf05b5059d038b00d00075006c00380fbd0931091f091b08ca05b8059a00e0006f15230fc50d970cf80ccd0669066305940159191100410e010ac410030ff20cd00da311b911b111330e21067a00cb19181a8700fd10430e9f037618650128001715631560155a1379057b03880a630370193318f200bb12f512ef1059058d06d10432011f00460cc20cbc0cb3096808d606cf12fb15930dd90e280e33035b05ca05d205d805ed0de20e621159115c11651168036b0580059808b008bf08c1137f157a0bd4147e0d9f06d3113613f201330f1313f608c411de145b014714781496185b0e3703b203b603b807f8006803c008920b2a0b2d0b370b5d0b610529082e09fa0a000a03101810b519240824006102f90820081a19060bff05e1136c0ebe0f540108122d14f50150149d083800620829008e0b270088079f05dc1a8e0b310b6a07a30315173401b914b0192d0a091901052c18f002eb001202e6001301d018e801d3030102f6005b03ba07ab07a6053819200f0d0a08191d04701a8f1a800f1817021942148318d4191408bc18be0e4800c31a89169a1a841a6a1a6c1a141a121a661a751a1b1a7d1a7e1a6d1a6f1a0f1a6519621a721a671a7f1a191a681a711a16])
(.leaf [0x13e3176f,0xf4113c11370161013b09910072098200e81058011f0cc1096700a7159512fd0cc90c86018a00a51690019109460924184e18420e370e3b05db08b70c6d13350f8100db181e0f6e0f1e0c7d113613f201330f1300d4046f0022046808c213f5113511b300fd11c401750da400b30da0012b10e900ee0d5800b006ed004906e500790a0d01ff0003020301c601fe01d406ee1833132b01220c7205ef0d9d1278010f127701680c75116a0c7000a408b4006b184f184d0470184c05e6115800f605ec0e300e3317b61778177917cb17a617a2177117731776179317be17bf17bb17b717b11795178717aa,0xf0500db00d40f6f0f0d17aa1795,0x85c006500c807dc0e82005e00f703970a220019007a033b0a17001600ba034a0a1806e118fb00c0004805530a0f044c0e1211790dd606e30032190318eb00cc0137055406fa02d00881140b0085004a0010006701400e800b020dd006ff02d60886075b075a06df00ce00c4015500520eb4140c0e5612bc128907df02d504a704a10446029f029a0145192c01180111009418ee000d0bb60f910f8e0f8b0f890bb504ab0db9063e02d3042702990160191600b618f6001e158b141109b809b009ad063b04a30420193a18fe1688146f146c064208f3064e029e0190193d191000a800400eb113d20ea908840d0b0d030757095d05a2033f0411040503f903841928012d190c00710038001d148d148713e90f991342133413300e160d0707ee0665059303fe193f1922004115c3139d132b066b01641925008e156d139c11830b5c015e009b0b9b0b870e4f03e903dd029600921923001b16d612be0b99109610930cd403ed1949011300e912c312930c0b11151110108b011900f012c011120425015400cd150816de084808460843019a0193006416cc16f11394084e065e0cad0ca90c9c095c06fd06e01948019f012a19090fa60f9e084910f710f510f010e50db50b08055504130d510d4d0d480d450c9707580aec00dd191b00af0084094e093b092b0927091c064a059b03e315dc1075106510560d410af003ac006f0737193600e8184a00500c740c6c0c660738190805ee05e505da05d705d4059808b008b608c1,0x316006800130896031d19cf01d118e803bf01d218ea089503c319cc031b1962,0x192f14f9149a0f9301be0148191616d809b2174c0efd0eec193f18fe01b0191313e908f916c1064c10e20f00192818fb018f004000ed193a0fe8111008f11768167c0660103a15c515c30f5e0cad08eb191700f000a8194e0188012a00e7016400d9190900720c3610bc108e0cd6175e1572156f138c104e0c8209d409ca09c508d108cd00a000ea00e901b6015e00a50075006c0c380d010ff20cd00fbb12ed13ad139e139a092709240920091c08cb0f5510300106190c191800e0011f1925006f0108191912200d9b0d980cf90cce152c152410040fc610d7104407ae067f066a0664122f103103f910b3016e1911187b0128197500410150001d00f1162916080da415661560152110350e9f0b6107a2066b083904040b161939193300cb18d618d818ce11cc11c411ba0e9c00fd1a4f057c05790737073618f2005008bd08b708b108ae057e045f045918fa18ec184d05cb05d305d905e707400b680d9d121412780e2b0e360e3a03ad03b51157116c1099110e04690a05073a08b60c31186906f4004906f61929141619360a0d19e505e2127506f108310f720f7b1380157b15c116820bd50f080f0b111b14f513cc13ee159215c912f9017f164e13dc0e47040b09d709dd09e5056209a4105510e510e8191b10f40ea4014709e818ff09ec193415cd01a7171219440f2119140f04116f191d0e3205eb151919300f7d089c0068089a03bf18ea03c308950f8313d909e1149719e10e400f78058908d609680cb61479192b14800e4310b519240cc4190a0cc8136319270e3d1a151a141a121a191a1b1a1c1a161a181a10,0x12fb1ace])))
(.node (.node (.leaf [0x173f176b,0x13f145a11d9014600ff142e11e009d0013b015e00751436094d091f019e006f10a710a30941092e09bf115c1165,0x79e0088005b0b3707a91874180c03c2001a16fc05df03b401b5003a134305ed01220f6e0c7205e5010f00a415e1141712770c7601680a0c0079187f11731170116a0b3005eb08b407ae0ff91005178617ae17be177117a6177317b1,0x771790,0x9dc191118ff0da30491193918ed11c5049e0d9d1278049a09e1,0x190a19fd19fe0cb0062b1924136c193b1481192b0f1619140f0e0f030e411691136205d81908020219ff01fb053801c818e819fc06ef0a08191d0e31188708990e3b141c193e0f7f19f70d6a19fb0c711962,0x1a78147f00c31a770e300bfd0a0705ea1a7e])
(.leaf [0x1080176e,0x576011e003612e50575017e00f212e90b9f0b940189009215720b4706a1015e008a004311e10b4f0b5105d000ff0102015a003a13cf06ac11e50ca00573133105ed012d017100a60122112a13c70d4f0c9706a4132c016a016100af012b1613154111f6168913d215e810700d4013ad019f01aa0190017300e801b6149811de171b16c6161c1077145114501648160f014701ae013e01a7016f1627149216781674167111b715cd159013ca12b50175018700fd0165011716080c34155b12e311ba173116ca15d012ba016e00a0015d01b1121e0c3814f3137910f810f410e910560d4401060150012800ee0ff90b34122f0d610d5800e30088010800b0165012341526152210030b3506f506ed017f015900491736171e164d153006e501b901a4007914ae14ac149b122b11f30a09014907b207a0005b03ba03b4001a183f01d406ee07a60e330e4407aa0b4c0f090f200b910f730f790f7c0f841215126a1279137f1496157a16d01123141815401595169c0a0d15d715da147a05e40c2f0c660c6c0c770b301158115b11611167116d00f6116b0e3014ab15eb161b16f81700019c1482014214810f150e480cb512eb12f812fe08b208c707430050046000220465006b05800037058c011f0cc112fd0e37058800a7183e136d0e3b18330cc9018a16910f1d08ba046d0741073800a40c76016814150138141c183d0f7612760c70010f0f7000db0f030f0c179d177717b517be17bf177617d3177217c5177d17bb17ba17b717d917b117c1178617ae177117aa17a6177317ac178717a2177817b6179e17c6179817cb,0xfc11a611a8013c0161065a1440159e0040018b01930948064816a516df006f01af01bf174a094316e116a1173b144203fb01c300e9019401ae018e001d13e1109916b61675166d03fe012e018d0187004115b211ac092f136216b9167b067e016200b0012501bc012b174d173115b410f10d580de71347134213a101b100ee00bb0122017a15d115c9159210f40de80c7214ef10ed057d0165013300a40150003711bc13f5020408360401058800fd01680003006200a70b1b0a0c0200031402ff0086007900130012052e052b030302eb01c601cf183318a30de11158116a136c13f615931693057e08ae08b403010f130469031f08320f7c127b16d016d301910f8116900ddb0e350b1f03ae03b617040d990da10da600b30da30d9d14a61736176101b914b01701169a16a41728172a14f615ce152913dd017f164f01a717110f841518015615140f7e0e46164b0ff20ff71557155b155d015d152102e8002b04ec04e804f10797005b07ad011f12f40e3912fb03ba07ab01fb05ca003a035d0017037500e310050159153201ac12260106121e0f0a121416961167152e01a414ad014914a9019c0e4914830f1811700a94007f0a9e016e160701751278010f0f7000db0f040f0d147e147b116d0a99046c0022046e0369006b184d0470035603b4001a03c200c30e4301420f1600d418bf0f1d147f18bd18730e3105eb17d717cf17d617b717ce178017bf177d17bb17be17d317a6179e177317b617b417b117ae17861798179517a217871776177117aa17ba17d917c117c6177c17c5177217c417931779,0x19417d7,0x18910f700470191518ec049a0456046608b608bc08bf08c8,0x1537015a016108e7106f006c00e808cb03ac1057006f0019011f0664038407ae0041001d1975040e067013371333040407a200cb009f192218d818d60e9c0c240c720c6d01f51a37190819ff0c760a0d1a3f10c9191a0a971749007f01c3165c0ffa0ff20a93170401851918194214e61001150512a914aa14a512440431145b0ea4014f017f192d00460147082602fa17111656164b152e14eb14ac06d30f780831046b04680456006119440133191518ec16d416d1168215c1158a157b14971476077a081d06d10f210f1c0f190f140f080f050bd50ba30b4e046f193e192b00bb19141694169115941586153f148013f710b510180de5058d0586057c038902bb18d4193b192418f20cc90cc70cc40cbf0cb90cb30968095208d606cf058902ff01fb05ca05d205ed0b680c6f127e0535081b0bf70c050a990de111581170057e059608ae08b708c20ddc0e2b0e3a0e430e470e4a03ad03b5136313dc13de13e101c818e801d2035a037700170355036918fa184d0470191d0bff19b705ea035b0815088e089c0068089a19270e3d03bf18ea03c3088d19060c00192018d118d005e11a121a1c1962,0x15621abf]))
(.node (.leaf [0x63a176d,0x14830142019c147f14a9018a0149141e0f1e0f180f16013800d41692141d0f0e0191010f0f7f0f6e00db17e8179817c6177817c117ac17951779177117aa,0x820acb0270071300ef000a004d0d83026f043400b20043002010f90970069a043c012c007213b909920161189f170f01a71563032f0385026906c90433015d0037001d004612f5058d040102ee011f0062001207b0079902f8005b14a707b117bc17c0177217c5179e,0x10f1771,0x148118da192b19150f160f041914199f0e410e3e1998199e18d019780d69,0x194716961533193b0159159412f10161011f153a106f1058015a00e80fd90fcc00e10337001508e708dd032d006c0019098208cd039e058d03890330007218f20cc90cc2096808d60589190a100c10040cb505d405da0c6b0c6e1331133519220c7305ee1a16,0x19271a1c1a9a])
(.leaf [0x46f00d4002207aa02b4005b000f07a602cc17951787,0x58e011f00370cc10588179e,0x753005101100752128800bf01540e02111200f400f01138108b0c8a013b00e900a5094509420923006f18df0b0d01f400860003052f052901f9002f18de0dbe0cff0cfc00b700aa0d9b0d980d950cf908b008b917b417b01792,0xd50017100af14310274013b000a0ad1071d02160082004d00050a290711021f021c007b18f314350a3f03d1019300f8001b159e0e7103e5016100c713c60d4d0e730acc012d00ff0d90071606ab06a7060f026f00b200430970069a00721337133005d805ce1922003a0c720c6703b30218190818ea15d80c7401ef03c01936000300680a0c09fb0200031819010013052b030301f818f0195f115c0a0805ec0e8f191d00ca11570a9100fd007f0b1b0b120b0f0a8e073f07361904005013cb049d0497048c0489193418ed09ec09d90965069f02b918ff000f035c035806af03d702be001718f70dde0371061d00bb18f411de0de7062b0ff70375076c076802c40147192419180055149613d8136208990cb50cb2096707700627193e1927190a0d6a0d650cb006b7031c01c601cf18a318c60499089609e00f770f7f02cd07730a330dda0e340e3c1959036b08b608c1045e046a184f077c1193147818d405380742127719200f0d0f6e136c159316930de813f2013313f6193b0f1e195a0f13191408bc0f03195508c4195e,0x97300d200720b8d098c0092013f0ee50b92096a11da0b96018800f200a800ff157111e111290cdb0acc0754015e0120008200510cd5104d0c9505aa04bb04af00e900e700a5003800270df6139b13050942093e0923059a04b600be1925006f0fbe073e09fe09fb067d0661059200e000501901004113080fc5048b04690463045a067b015918ed18ec00fd0dfe08c708be08b808af059702b802b51157017a18fa000f191d0b6e066c058002bc1171008e18f2194415210b6c057814ac14a40fc1193318f5192d13781044063807b20128005b12f112ea07ad011f0da10d990ccf073d0cc1096705881911190a0da2076f05311939005518f00ac40b200b1b076e053000cb1904078d0787074604b3005912fd145b11de0ea4078f193b014714801477077b192b030f14ab148300131942168015791495137e06e4030a02c015140b1c03ba03b6193e0049193018ea141e141c112406f7127c12790d9e0b6907410537089d0318180c1929192000680f7e0f790f760f700ed40b910898049b191519df0f200f1d0f1a0f0c08ba046d19de13e010980e3b089919270e410e3e0e3c0e380e340e310e29089307a7077306ef02cd19dc031c063406ed078b092f0c7f0cb00d630d650d6a,0x1b611cc13af00fd19250e9d067d00cb0041078d066c0059008e07670532005518f0082c082902f102eb0062001216270da0079902f8193919ae005b147d077002fe07ad16fe192b190a1863184414810cc9193b1a5f1513129a0b1e193015791495137e089c088e08c108b908b00580193e006818fa141a13df13da134d110f109a089b0465046204591929192718ec1715164d15300e450e3e0e3c0e380e340e2907730bf609f90469194400c319061901116f116c1166115a11570e300bfd0a0705cd05e303b503b903bf03c2030007aa0f150f1d0f2008310f750f7d0f80030f031303170013031e01d118e801d218ea03b405380b6a127a1815127719200f6f0f0c05e61a5808ba046d1a5b1a111a161a1c1a0f1962]))))
set_option maxRecDepth 5000 in
private def hintsBasePart8 : Table := (.node (.node (.node (.leaf [0x1699176b,0xa6b00c7007d0e780a5f012100840cf10a2b00a9007b0ced0a3c17f707190cad06e0004d00a60436065b0d770c9b0020004000b104410ce206560cca069305f000d200b200a80042098f09760972096e096b08ec06850748074400720051073707360c920c880c7c060502150960068705a304b1005000a50075003800270d970ccd073b092909260922091e064805b7059904b5047900b3006f0678066a06640595004117f6138211520621015d003d12f510590232022e011f000613230f3f058e057d038a022d015f01140037152209d809640bae0bab058601590076009308c608b708ae0596057e0493048f048a043002c8006b0025000f046b046504620459045602b5002217f5089e089107f90549006803c403bf03b703b503b103af03ad033d0226001a17ee0c730c6e0c68073a00a40c740b370b2d0b2a01680088116b11681165115c11590b3105ec01fd01f601ee00f600030a0709fa01ff007912440a0a0b26066c0149008e07b107a2079e04ff01ea01e301de005b000202f702e901e1074504b20012005906c7043102ee0779076b076701e9004600550dea0dde0a6406d103710cc00cbd0cb40cb1096608d4076f023500bb00a7136810b70de70cc4062b0125145b11de0ea413d81362134b110d10980147012e168215c1158a157b149713df0191053505330530052a04e002a901fa169615931585153e136c13f911360de806d30f7f0f770ed20c160ba40b8f09e00499002f018a17e400db1273127012030d9e0c700b69074105371480147d1477077b141613f00f7517e5014201380e410e3e0e3c0e380e340e310e290dda0ae50a33089307a7077302cd01c6078a092e09bf0c7e0caf0d590d6902c306c606e606f802e30303030e03160013030d01cf031b0302046f07ac08bc0ba30f050f170f190f1f17bd179117b517b81793177217c5178a179e178f17a2179c1787178617ae17a6177317cb17b117c1178517b617ce17cf177917b0177817aa179817ac,0xd90f580eb9010b00d0124c01ae0ec5014b0f590fd4015400e1107a106d0fcd,0x45178c,0xf7519291915141d0f81193e137e01280e3e1977137912f6082a193318d611c811ba0e9c00fd19760e450e340e2900c31975197412f2149b07b10531052e02eb0159192d18f01713164d153014ad0a0a09f8052c19441901116f116611570e300a07191d1973196904710469045718ec08c708c308c008bb08b508b20597046518fa0f2008ba07aa046d03000d620d69,0x2f8005b001207b102ee192d00460a0b06cc,0x190805e50c74003a193605e20a0c190619010c710c010a0b1920192d0f180f0d14a9191419420f17141f141703b4192b192918ea0e490e420e3f03c21a6f1a6d1a70])
(.leaf [0xd6d176e,0xeb4014500ce0f920eb100dc012f1110148c0f980f850eb30d7a00f00192010e013100b115990cef0dbe0ccb016100a900b700a80ce40d960990096c0969042800b200b30072001e108c0d970d7f0ceb0cd4069a041800e9004303ec03d203c7179617d0177a177017b817911793,0x2e30012001302f403040055002f076c052e17b0,0x1701775,0x199006f800c300490e3502c100fd000f11c302c80b191939009319040da306b3049802b9191118f718ed09da06ae049106b606ec0ba5,0x115500f5193705c51260114f0039191f193105b10d35135d0cf30cee0042190e1923190b06960d2d10170cea192600e800e413b909850c7b08e105b406870161007200a5006c007513c713591350134a096a0925092108cc0669012d012300a8006f00411097109110100cec0cd5094302ab105700e9000e011f0d990ccf02b307ae191119740da3159013ca07a202ae19391934008e190411c511be0b670b1b05ca05d205d80e3903b203b603b818ea03c21a151a141a12,0x15191ab6]))
(.node (.leaf [0x99d176c,0x51074b0752008400bf0aef087300e8006603ac039d001903850389001d00370e00040f07450c6c022b00cb005900a400060ea40ea1078605e5022f027902200737014701280086003a003d000b00501495137e0b1e05e20868061d0282048b0191015600990093004400251478141d12ea1057089c088b02cb02bf02b901420138011f0068000f14800e3e0e380e290ae5089302cd018a00c30cc90cc2062807af07a800a7005b02fd02f501fb01f400120003052f052902ec01f90227027803ae03b403ba03c3179e17a617b4178a177917c417c9178b179c179817ac177817b6,0x5d07c607cd009200c70b8c0a6a00d2007d0ee80a7201a200ea15a010c5,0xe317ba,0x171201a71944164e164b017f12fa011f199714a9198a199619421519151619301992199113f211360de806d30133061f05f603d804980496169b1697169415941586153f13f70ea4078f18f718ed01ca193b014709eb09e509d7096306ae069d0491040b18e8147f1476077a18ff03c503b403b003ae0356033e01d3192b198718ea0e490e460e420e390e350e2a0ddb0ae60a34077403c200c318821990198f13ef0f210f170f141929191419800f830f7d0f780f750f0409e10831049a191516d416921682158a157b1497141d13df13800f81193e198b06b60d590d69192018d118d019781962,0xd581a0d,0xe321a95])
(.leaf [0x15ad176f,0x6102f903680012001701e00816035b00020068003a01e903bf03b3035501e505eb0055001a00f60898077a03ba02f8047100db0142005b00220f7f0f160f04082007ab046e019100d4169214810f1f018a12fb07ae011f058e00370cc80cc10770058802fe03690464057e1785178617ae17cb17aa17981787177917951778179e,0x62082d082900cb18d60e9c,0x190f0d6a06eb193e0049141c06f719290e4006f101d418330f740f7f1955,0x1901052c06e418f0004906f0053506e800c31906008004690892088b0aaf18ec006801500464089a10ed14f6089d18fa1927191b01a7193019ce15cd13d810f315620b1c052e19341933190411be11bb0b1b0aae19d70497049518ed09eb049106ed0d5a0d65049b08980f7c0f7e0f84046e08bb19140f050c00192018d00f70191519d5,0xe32191d1a560bfd191519060f700c0119200c7019081a570f200f1d0f150f0c08ba07aa046d03001a5505eb05e405e201fc003a1a4a1a31])))
(.node (.node (.leaf [0x4a2176c,0x6cb0046007902ee0a09001217e6030207ac17b1,0x14f082510cc006100eb081b0a9c0a960099007f0bfd0a9800f618860a9400e318830833012812eb0cb40d6300b00cae137f169c07ab08200f180f1b082301250cc30469046c04710022046e0464006b187d18820c00010f0f7000db18870e4101420f1614810899183e136d1833141c18730f80187e0f0d00d40f1f1879179717ca17c917cb17ba1795177117aa179817a2178717ce17b7,0xa417a6,0x1231351134901611926158c13b70164015f135813a01323131a0188192519211570156c139b1321015e152a15221319138e,0x3760017191803700cb400bb190a06d106ce0cb00de2036b08c1195d0471191d1a0719fb053819200f0d19141a050f030f6e18ff06af18f706ba19271a040d6506b709e019f7,0xa140083007a0ae20a250172014a143c14b3013c017c114b13740a16161600f5012700ba194311510e1a123b12e00dd50e5a0dcf193300c0010a011e00c4156307e50726123f137612e111480e4e01a7005e004f01ae01900129191e12e71518143714880e570bc607e004ae03a703980733161e15b9138311d2017e19300145192c009518ee0019191f01730163129e129a0f900f8d0bbe04aa065203950d33072d0afc139005c5011319160040190e0084012a00391292035009bc09b909b1064d04a40c560a2c131805c813d10119001618fe1907007b1921012d12c10cf0072c0c5e034809b60714070f148d148713890f99131d133a13300e1607ee0154190b010c005f191c004d193f015a192211110af10ce80edc08060d8a0d850d8207160655159a153913360bcb1685130314fc10400e230a2f00f000e400d200b2016101880120015200e700c21097108d10100cec0ad70b9e0b8c0d93113d0e1f152b13080ad00aca0ac70ac100e90092019300f40159008215c2157815711569138e1322130e10a610500b9d14341138071e0b370b2a09fa0164015e013b00881901139e139a0f5a0ec1079f052c192500d900d0197418f013af159013ca0ac40b610b5d07a2053101b6193400cb008e11cb11bd0e9b0e210b65153e159316930a340ae60e2a07f6089c033e03b203c5157a15c01681161a16fe03050ea401471496193e141d14780a0b14a00b6a126e1274113613f201330f1313f613f10ebe0f54173601b914b01701169a14f5082b00620836015012300108122d149d192d14a91942141f19290e3f0e490f180315001301d018e801d318ea03c21018192408240061081a19060c0119200f0d088b08151a82082019140f17192b0e42147f136c1a1d1a741a6e1a6c1a6a1a6d1a6f1a671a0f1a6519621a721a701a7f1a191a711a73])
(.leaf [0xbf4176f,0x1522015e0159139c1004012b00e3132b0ff701221847094e006f18450a9205ef05cd007f003a11730a9905eb00f617640a0801b9007914ae14a40a09014907b3005b03b903b503b307a60e3017bf17ba17be17cb17b117c1,0x840af6074a00fb00510e04075200bf0abf0df8008200be0ac50e010ac40dfe00e700cb017a10440e9c162b012800fd0177137911c20b3b015d016f0088155b0d260d1b05de018700ad003a0c790c6505e618c70d24012b133e1335132b16f116130122019f1634134414f304fc01b501500033175c122f0ab3055b01c50108008016670e990ff910e910560d4406f506ea018500e300ee0049174814e410000d5806eb01c3014f00b0151b14e213da0d650156012e089c0899088e07f60745006800590767031803100308005500130c040bf605e202f102e702e3009900120535052a052104e002ed01cf01d4183306e509f809fb09fe0a01177217c517a717bf17be178417db17ba17bb17b717c417cf17c9,0x1b1177d,0x45518ed184f0492189018ff0f7009e2191519c719bb19c6046608b619b402cd0e310e34,0x19290f7617e819151a47046818ec14aa04661942196d18fa14830e38057f192b011f186c1691148012fc193b0cc90cc20e370e481a16,0x931a6b1ab31ac5]))
(.node (.leaf [0x915176d,0xdd0fa0093a0119006f12c20928015400a60fb408d10d490c9800df006c00af098008cf02740072000a0d42039e0264150500ee0019017f0c2004140387026b0bb0009f001d0093066f066103fd0fae05850388004101140037066e12a40cbf096808d605890776008e014f00a700550b2710000cb40765008800e300590b380c230a95078f015900fd007f0147164c152f14ec05dd05d305cb0b1a0a8d09e80963040b01a4003a00860076116f116611570b2f0a9805ea08c708c00498049302bb00f6006b0025000f0470046a0464045517dc002217b517bb179e17b617ba17d917b4178f17cb17a2179c1787,0x562003300ee055c10f4008001650aab111c00fd00f10b1a0b1709f900860079052e052b051f111b002f015601f9089c000317e701fb0e40003a00c310c905e6020406f006e900eb00a415ce0309030500490a970a8e0c7205ee01a7001317e9007f012217110f830f7d031e046b04680ff70a930d640d5806eb031a01a400db002200e300b00f210f05046f0cb60cb000d400a716910f1e0cc8018a18a7156311bb08ba08b4015d006b152010040b3708c718a601c601cf01d4183318a3047005eb0a991158117018820e31187317bb17d317b417b117b017c4179717ca17a617be17d917aa178717ba17b7179517b61778177217c517a2,0x12f17d0,0xab10150008010ec0aa8,0x973007200d2098c0b8d013f00920ee511da0b960b92018800ff00f2157111e11129015e16801579193e141c11241a2705da,0x193e1a731aa5])
(.leaf [0xf81019100db141b0f74177917aa,0x860a8c0b1b007f00fd076a049d0497005511580a9917dc02c500f6000f0471046c02b602cc07720e300e3317b417cb,0x1179a,0x11be193400fd13d80b191927190406bb049d049718f718ed09eb06ae049118ff1967196313f211360de806d30743073f0133005015e113f50c770c63073802020bf5088b081905e1193618c219061173116a116711641161115b11580e310de10bfe0b300a9905eb06b60caf030007aa081f0ba10bd30f060f120f150f1a0f1d0f2002b6045704600469046c18ec046d07410b691276127c,0x104e015e00e7094c093d006f094300e903ed001b035a0017037519180cb5190a19e70d200d1d190d0c6d0c64190819e615ea10b2194200f11515111a092f0cb00e4a035518ea03c3036908ae,0x8961a64]))))
set_option maxRecDepth 5000 in
private def hintsBasePart4 : Table := (.node (.node (.node (.leaf [0x1605176b,0x96400720076096209ec00750165091f0c2a006f17f206670661092e09bf178f17d3,0x14af014901b914ad170114a901a4019c152e0e4a015900c312fe12f20e3817c117d917c6,0x3d178a,0x3ba005b18ea07a803c2,0x800aad09f900fd19e51157,0xf821a64])
(.leaf [0xb15176e,0xa1600ba007a0dcc0a100a2200c0008100f70e130e150dd30ab811750aba00fc0122011e00ec00fe060a0bc2132b103d10360a1e0694003b0095012b00e70042060d035211a90bca0fcf11d410d4139b1182104f069101230016016100e10163015e00ae0c90033f134810700fcc138f138b09bb09b309a70ac600a50038012c00e8012a007400820d2b094f0925091d059c0e0a0982068205fa065f065b0651064d0337027300b6006f00bf007200400015000a0dba066203a603a3039f0393038c033a032c0265013200410019159013ec0ea20e000ac303fd03f9038402681045016500cb001d012815ce082d04021559137812e301f601f201ee01a70062015d000314f5083611bb0e9d0a0009fa01ff015000fd00790ab10aad09f80e280e3308320f7c0f8404140db6105610e610e917b317be17cc17bf17a817c017a417d3177217c517b1,0x30a0049001317e903100059078c00cb0ea8019f16f110f5019a00ee146610721054013f00e8098c0985007209630076049217dc000f0e2a06f002ce01cf01d4183317bb178f,0x16517d3,0x13031601d1006818e803bf01d218ea089503c319ab19b30896031d19a0031b1962,0x1903ab038400e8001d106f0403016100621590040e0829193400cb008e11be0e9d0b670e2a03ae18ea03c2,0xf191ab1]))
(.node (.leaf [0x999176c,0x537002f010f02ed0f70001200db02f717e7005b03c003ba001a181311670de10bfe0b3005eb00f618110e480e440e3b0e370e300dd907a602cc18100f200f1d0f1a0f150f0c0f030ba108ba081f07aa046d0300180b03160312030e030302e3001306f806f506f106ea06e6030d02c301c601cf031b0d6917b0177117aa178617ae17cb,0x610824081a183e00990899088b081517c9,0xd41795,0x11d30163191e1383069311d6012900421938130205b1126301200039191f130605c70d380d3319251921190e139b13210cf00d3212e2015e190b00ed011e10a40ceb09ca068705b412e600e90075006c017e09440ce3096208d013ce1097006f00b20072012d162f139213190d8d0fce0d4e092a152213071647066706610cb1096608d4132e0177012a00e100af015901a70041190a192216331064105c10530fcc0d400d2e162a15591520138112e311c7067a077105ee05da05d401b500e8017a193300fd0055003a15e00c730c6e0c6b0c6805e10b700b6c0b19076c01fc193618691906008e190417f91174116b11680bff0532052f191d18f00a0703031901001306e6030d031b092e09bf0caf0b680c000c6f1275127b,0x9be1a0d,0x3e700c7001b0b0d03cb1904003b0a8d060d007f01230a931348191819260377035a131c0017192103700e7b0e7305fb05c700bb013b00ff00720039081d0ec011e00c92060508d005b6006100d0015e00a5006c02f9139a0b5d094d0931092308ca05b803e200121925008e006f02f6067f066e0664005b004103b903b503b118ea1a9313b61324015f0b200ebf0bad11b10b65067a19390108009300fd160612340bb211ba016e017f1933160912fa12f601b5011f1344132c0cc1096708d502fe1922190a0c731a8b190811de13dc134c15df0c74014719271936158a157b149713df147a1477127912760b69193e192b192013f206d3185d0f190f170f0e0ba3082107ac030217e4191408c308c008bb08b808b508af036a18fa1a92081a19061174116e116b115c11590de20bff0a9a0a08191d0470046a04641a8f05ed05e105d805d205ca035b1a8e1a8012fb147f158518be1a8407a60dd90e330e370e440e4800c31a891a151a121a191a7f1a6b1a161a711a1c1a731a6f1a6d1a7e])
(.leaf [0x15a9176f,0x123135713480188012c152b131c01590121156e1522132017c017bd,0x147f018a01420f1e0f1617781798,0x192b14800e43193b18dc18c5195317e90f830f800f7d0f780f750f720c170ba50b9009e10897031e19150f7018900f1d0f1501cf1833187318c6046608b618db,0xfd049c11c618ed19bc19bb19d307a212a40faf0f4003d7005b011418f712f212ee10580fd107ae0baa086907c806b1011f00930cc00cbd0cb40cb10966122e0ba7150614c612fa190a010815e0017f159415860cc8122c0fc20a0a0c6e0c6b0c680c651936198a193b192d1980186912751272126f0c6f0b680f210f1f0f190ba319ce1920191418d106b70cb00d5d049a0ba50f040f6f0f7b0f831579158815bf1680169016cf1098134b13d813db192713de0d6514171929141b193e0f800d6a0f750b1e12a714e3151919300f7d,0x1f400190003039401f9004018f0065502eb00b200120cb202fe190a06490589038a006f18f20925058500a5009308b808af057f02c818fa000f046402b41a530ae90a3e0084007b0d010cfe07370736190c00500a9f0d980cf90cce073c02b20d8d06600fd90a3808de06a4016e1911012a00e100af160814740da4106710630fcb0d3f0d2d0c840aee03aa193900e8147d147a1192077b12ed10570fd0192b011f153e147f12fb193b1a5112b20430194818ed10f710e510550d430b08055509d70491191b18ff12f910f40c1e09ec0dde0a64017f193400bb164e15cd06d0043101a70046171206d31944013315190b1e0f210f140ba3030216d116921930191419e10f830f7d0f040ba509e1049a01fc05e707400d9d127802cf0a350ae70ddc0e3a0e430e470de0116c116f13d913dc0201052d06cc089c0068089a19270e3d03bf0895073a08b60c680c6b0c6e186913f413ef02c206c502e40013030c004906f61929141619360a0d19e505e2191d0e3205eb12750e4006f101d118e801d218ea03c31a161a121a151a181a0f19621a101a1c])))
(.node (.node (.leaf [0x1743176b,0x664180314511450013e074300500ccd073b00b3162515fe067f0678066a0175004111c311b911b511b111330e9b067a00fd180200a71801145b11de048f048a0147002516ec15ff14e809e909d80964069e0492019800760dea0dde0a640b370b2d0b2a06b506b005f603d8028400bb0088004406d006c70c730c6e0c6b0c680c65073a0b6d0b25066b13e113dc13d9134c109906ba004600a4008e012e13f913f2113606d3168215c1157b14971283127f127c1279127312700d9e0c700b690741089b07f901330191010f006817061703170016fa16eb161b15eb151615df13f30c740f820f7f0f7a0f770f6e0ed20ba40b8f09e008960499019c016800db141e141613f011a011240f7506b60caf0d690dd90e330e3b0e480f050f0e0f140b310de211591162116b1793177617b6179c178f178b17a617cf1779177117c6177317aa,0x7a900c3005b0e4607b1017f0149164d14ad07ae12f817c1,0x8617b4,0x1168191d0159115708c600fd18fa0e9b046500cb1830082c02c4006200550ea108350771062805890128190a12f112ea0cc0011f1983028a06b60caf0d6203ba,0x41b0064001e084303c90092001b06a0041703d20043069c03d6007218f705590964069e06b202a5003318ff0093000e055f049302c801de009f18ed000f18e90c24049d02c701e900fd00550bf50b2a096603060b19076c02ae19060088190a0013190405e205dd05d905cf0cc1030c02c20530052102a9003a011f004918f005ed130006e4052b192201b9190113440b1d14af0a0a0c7301b51930192d169a077b07ad079e079a1908170116fb151414a9193b192b005b15df0c74185d0f1f0f190f170ba307ac1936191412760f0d0c700537192003b91a03089e0891006803bf03b303af01e518ea01d318e819fc117411590bff0b310a0805ec191d0e410e380e340e3107a7077306ef02cd18870e3b0899031c06b706ed0cb0031d0499089609e00b8f0ba40f030f6e169114171929141c193e0f7f0d6a0f7419f719fb1962,0x45718ec18ed046402b818fa000f058002bc1863193b0f1e08bb046e19141a830e3702cc1a811a6d1a161a7c1a66])
(.leaf [0x1084176e,0x141f0138019c141b1482019101421692148117ac17c617791798,0x18a1863148007ad0142005b0e4307a9180c03b9001a088b03b4009917fa0535002f052b0079116b0a0d0f76016800db12760f6f053701c6187318a30bfe116a058007aa0f030f150f1d184f04680022046618c3047017781798178617ae17c917b017b1177317aa1787,0x1a417d9,0x196409ed131719120ce60f9e19210dae190b0113132419260ceb0b990de3015f121a13bb00e9009200bb0bad0106016413b90d840ce40cd308e806a006d20093088f121e156d1569138e1322016100b200a8006c0043004605860b2a03b70068016e015e09910970096a08ea08ce069a068302ef18f2008818ea0bf51299089d0aa1139f139b00720012058c05df05db05d505d103b419061930007f19250cb1096608d402fd011f06c417fa053502ed14e10a9b1335132b186315951587154012fd004918f0014f1922193b02c3052b14ed10010ff80ff30cd10da10d990ccf13401480147a000f19011944191819110187192b06d30dd9089206ee02cc0a0d152e1526152212f112cc10030b350da20c7702021483013300c3193601591939190815bf15881579196d13f00e3f116d116a11670de10bfe0b300a991279127612150c70053709db09d80964069e193e19291890192018ff0f810f7e0f760f700ba60b9109e2089817e8191519c3046b046802b50f200f1d0f1a0f150f120f0c0f090f060ba1030018ec184f0491045502b718ed19c0155b152012f5193311c511bb1159049e19bf06ec0d690466058008b608c108c408c819b4,0xcb078e0e9c005900fd030f0b190013190401d10ea40b1e18e80147193001d51495089c0049193e0068076606f813df089b00551929192702f10e3e0e3c0e340e29077306ef00121a2f052f02ec18f0052b190111590a08191d0bfe088c1815190612770c710c01053819200f7d0f780f750f6f0897031e02ff077116911478192b1480193b0cc91a111a0f19621a101a1c,0x15211ac2]))
(.node (.leaf [0x911176d,0xe4101b08e2014c006c14cf05b4019b003916e805be0197008b141304c4013700280b5302d7140e120f04c600950011016d0105010307e20ef902e21260120c11f8005e00d3010e0e1b07e707920d3300c0005a00ae0dd80dcd0791090208f80c5c0c5600ba006d00a30c460dd205f702dd0c5d00a1011c003b00a6010c0cf50cf00c4112d503cd0ca40bed00a90124001b011300970c8706d90dd50795135b101a035f03570f3a0be80e1407ec00a50047011e012f0125001700d6012208b70bea0bca0ce308a806d4135d12d60b5412e60e6b0de603700bfa0ff80ff50c430376006b00dd016100b2006a004d015b017e00c600bb009900e30465045c0bd610c510bb101209d7043804350b56034f034416470e600de00bfd0cc30cb40c3c17dc009600ea00760020008c001601a700f600a7000f0bdf0ba009930989096505fd043e080007fd07fa0348129a11c71158077102c7010b00920072005f015600fd00550eda0ed70b8c0973080404410b1c0b19076c00d20086129510bf0ee1080b0ddf0b0f014d00c70a7a0a730a6c0a68007d0ed60b550fee0fed0feb0a7008fb08ab04c5010400e204d504d204d104cf002907d307cd07c504cd005d03c80928092508cc03e407f507c20655064f05ab001e006f006600400e6d0425071106d8093003a6039f039b03970393033a00cd007b00d000190aeb0ae80a5d0a2a14c312060f450ec40267084b041c0084014b000a0064121114d10af90ead0d8d06600fd40fce0a3608dc092a027405100507050504c801ac0154012a00e100af002d153310051076106c106810640fdc0fcc0d400d2e0984050d015900e812f212ee10580fd1011f150614c612fa017f0bb0086807c7055804fc03fb0386026a0fc400930033001d00e012330ebd0ba810e410540d42056104120fb8010800ee00e614f8123110ee1033015014ee152012e31034017a015d14a512440fc20b700b6c0b670b60083704020149008e006207b107ad07a2079a079604ff005b06d106c8043201e80046000202f602f202ee01e0177417a9177017a8178d17a517b5179117cd17d017ce17be17a217a117d117c917ba178f17cb17b617c417b417b9177c17bb17ab177217c517c11785,0x7b10149005b14aa07a9187400c303c203b90e3114ad01a4152e01591167117007ae17c117d9,0x12517ce,0xdfd017a00be13a30dfa,0xfd113411bb00f419330bdc155900960163086e11070066191c087910fc00d9012d0c0913cf009b017e0c0c129d0eb90bdd0119011300d0010112c0087e12a10ec211ee12e50b9f0b89015401af014b0161011e0092150810ab109c1096093313b810f905760571019a00e9006f192618f116f11582156710a30b9b05a4059a13bd0575019f015e0038016400f214f313b6130e05aa0ca60ca4057311a3111f0a3b0150015f0120190900fb007b122f0bad086813900fe20fd70fcf0d4d0d480c970afb0af80af60a2c01080093012a191700e100af008412340bb21074107010640fdc0fcc0d400aef017f00e810e610560d44172812f712ed10570fd0191b1947011f0df80df6139f139b130510e816981595158712fd149800be1925193b01470c370c340dfe067d05921480147711eb00a0017a0041192b12170c380b6e0b620b5e0b5c066c16f8148315bf158814950106008e1942193e0b340b28141e141c11a01124109a00881929192708291531152313080b3611360e450e3e0e3c0e380e340ae50a3300620159013319a400c307af079808c708c308b208af0597073e073707361974005b18fa005014a914a4149b07b104660460192d18ec164d153014ad0a0a09fe046819441901116f116611570e300b2f0a0705cc05de03b603ba03c318ea03b31a121a191a181a1c,0x13e11aa0])
(.leaf [0x18a148013f6014201330f170f1417781798,0x4920076002509e4049800ee008610f30b1c09e00165015600db15cf15190f8401a7171101a4152f11c711bd015900fd1562152011ba0a8d015d007f12f610030a93011f00e30cc10cb50e330e37178f179c17bb17b417d317c417aa17d9177217c517ba,0x45300f500211145045005c500fc007e00390b090a7f025405b0044c008500080042006d0a48024d06820612007c00180072003c0a5203810378024e069b060f00e4001b004310150b06035801db06a400ea0017000200af090510b5101802310222068902a601df09aa015b012500060075000e0074154711a9062a037c022e066802ab065c064e05ae0161003d004100401590061e03fd03f901650044001d09eb096306ae069d040b179b17b2178d1789178517d117ce17a4178a17d3178b,0xb240176008712bd04a8011818ee125804450c07191f18eb009a0ef504510cef11d70c060b2304ae1913190b191e0f0008f9044d0daf0dab0ce50693068e193a18fb19120042153b08fa11d30c080dae0698015a1917016319261574131d0fe5110510f90b21015e1921191c138d12cb0fe109f109ee012a011b190012ee12c809f0011f00dd155912f50c201933009f11bb0c25,0x18fa08b60464186918ec0a0d0469,0x153019441874116f08c7011f191d18fa0cc10bfe0580190a19061863169c0cc9088b193b006814821480089a07ad07a6192b192719750e430e3d0e3a08951a630f200f1d0f1508ba07aa1a5b03c203bf18ea05ec05e303b41a581a161a1c]))))
set_option maxRecDepth 5000 in
private def hintsBasePart12 : Table := (.node (.node (.node (.leaf [0x1726176b,0x2d5009400100bb702d40180004a0e59070000c4063d02d2061802d113600e5006fc003f003c012400a605900612135a0c9e13860e520038006d012f00e20129059a05f910bc0fe40d7a0d780643006f003b00ea012000b10c990c800922060208eb10b00cdb0cca05a203d003cd00af00a5007200f000a8001b0d6b1305105f105b0d3f0c8409831094108e0cd603ef02a300b7012b00e800e9000e0dbd10e710540d420d9a0d970d940ccd02b1011700ee00b310b20c2709e409df09650da300f1009f00760175111d0c2a049216060ff30cd101650025016e00e305f403d615cf0b180498067f02ad0a9e08c108b908b00598004401a700860041007f006b06b3111a160b11c60c220b190679046a046403c403b50093015601b500fd0022001a02c8089e0891117411590a9a047117e3000f17e200f6076a02c60c6d0c67066c0a07005500a4008e00791562138111ba0cb40966076f15df0c740532052f052c02a8015d00a70168002f12f6105a10b70cc41277126b0d9f0c710b6a0538011f0125010f12ff07ad07a213d81362110d10980f820f710f6e0ba409e0049901b9005b012e00db14b007b313df0f8101490191170116fb151414a9169a1690136c019c018a14831481147e147b077c01420e410e3c0e380e340e3107a7077302cd00c3141e14160e3f013817e80f1e0f180f160f0d0f040ba208bb07ab046e00d417fb01d706b6092e0c7e0caf0d590d6902c306e606f106f8030303160013030d01cf031b17a0178917cd17b5178d17d017b917b817bf17bb1793178f177617d3179c17ba178b17b417a217c41787178617ae17cb17a617b1177217c517b6177317b017ce177117cf17aa17c1177917c61778179817ac1795,0x3e063003f00091001c0b7903f1025b00d3003f00090eed06420382025700dc00b100190f8508f7096e03a1010e006d00720cf008f6060005fc05f800a9003b0ce203ce0d6e0d34026200b2001b00ef00ae0b8210890d800cec03ee09b609b209a9063c015e00e90074094d0942091b006f138e0d8d09ab0922012a00af00a510630d3f0d2d0c8403aa00e810e410540d42179f17a917a0179617b81770178d179117bc17a817a4,0x6e178e,0x11f12fd07ae193b005b0f1e07ab191412f5030202f81933197911bb141b1690,0x30a0049001301d501d0031c06ed031d19f7,0x2c11a7b])
(.leaf [0x107c176e,0x1700abd12620081010e0aba0ab80f8700fe00ec00dc11d409b309b006940f980163007400420192103615ba0d390d3409a805f30d7d138f00e7019000ae003b00b1012a1577104f0d510c7a060309c215990d8d015e00af00a50075016100b20fbc0d2c094f092c09250921091d1336096f096c068205fa00e000b6006f01220072102f0fba0dba10450668066205ef05db00e6013201280041003a155910340ea20ea003b703b503b3015d00cb001a0a03139a132b067d11bb0e9d03ba0079012b00fd17e00a0a07b20aa5159013ec0da1067805f5049d02b801490080016500b30044002516cc0ea6149b0aaf09eb09da09d7096306ae049101b1019f0150007610f710f510ed10e810e50db50d430aa909e300ee183b0bfb0bf80bf505e102f900990012053505330530052a05270524052102ed02a901fa0e280e330300049b09e20f7c0d9e0f0d05eb11580c6600a40c760168116a00f604710022046d0e3012760c70010f0f700f0c177517b3177017cc179617a4177a17a817b817be17ab177217c5178617ae17b117bf17c117d31793178b179c177d178f17bb17c9177117a6177317cb1787,0x99088b0c011887010f141c0f0d019100d416920f1f0bfe0e310f030f6e0f7f17c9177117791795,0x18c17d5,0x15ce01a71934151909ec193018ff0f830f7d09e1,0x18f2058902bb190a18681860077c12fb18d4193b185e18ec0f180f1607ab046e03011914185d169118590e480e37089207a60772057e1a1619d0,0x12311abb]))
(.node (.leaf [0x490176d,0xcc0011f00a712f406cf01591808152f07b108c701a40149006b07af02f70f210f1908bc08b417dd00d400a40f0d0c700e3817b617d917c117a2179517a6,0x13c0f29094900d5006f11a60f2e0f24094600fc014a0105013b144411ab10490e79120b1435065c018e016200e700c7010e0193004016bb10f114b7103e0a6a0d350c8703921395065f0cef01c000ee01ba011e007d00ae00a50019012a00a913b010e813160ca517220a720d2d0c8403aa0d8b0ce20656012b012000a601ab00ea00e800b2139a138b130b104d094c0d360fe30c9e0c811738171f168d12e90cad09880984097103a0015e012c00e201ae018900721322131c0fe70cf216c71688069a012101900043153c131e13d206ab015a012d159c153713c613b811a810c5106e1770178117bb17a8179117bf17b5177b17c017b9177717bd,0xef17bc,0xe70fc9104e198e00e1015e14b90fd40b9b014b009214bf0f3611e00b8d015400d600ff00d20edf0fb40f3808dd06a806a30441013f00df006c00430020098b098008cf069b043d00720431096808d60046190a06d10cb400bb19180de80ff80fae0f3f01331922011413f40c730c6b0fbb0ba91936186900e00093150514c512a9149f0fc203770a0d0a0506cc02c9017f192d00171901000f08bd08ae0369164b14ac05ed05d805d205ce035b046802b518fa1944003a18ec184d11701164115b0de105eb0470191d199b145b11de0430014718ed09e80963069d049118ff06b018f712a713dc06ba0bfc0bfa05e3193019271906089c0899088b006803170013157b149706e406c3030a02c0193e0049141b13ef06f60f210f190f140f080ba3046f192919140f7d0f780f750f040ed30ba50b9009e1049a031b06b606ec092e0caf0d690c00126f12721275192018d118d0197802cf06f108950ddc0e320e3d0e400e47035503b303bf01d118e801d218ea03c31962,0xd641a0d,0xe431a95])
(.leaf [0x4570025002202b702b4179c1787,0x185708af006b185b185918421833077207a608920e300e370e3b0e48184c185117a2,0xb00cb006eb00a700490cc806f0018a00c318c501d41833187318a317b717b61778,0x15631933186511ba00fd15cd11bc193415d0194810f8049e191b18ed09e3049204990e340d5813da16d0193e13df19270d640e3c19590f7f1955,0x193b1691148117e8192b19290e420e3f00c30e3b192706ba18f706af18ff19db12790d9e19200f1d0f150f0c0ba108ba07aa046d19d90f7e0f760f700ba609e20898049b191519d506b70d65,0xdd0f9d0bd60110009612880c8a0be3015400a5016114be0c901591014b01231934109b108f15ca00e919400ffb0ff313ac1918192513350ff710e81922191b0c200bd10d0609e4067d009f190c18ff00410c250da50d970cf809da067600fd191111c40da305cd05e905ef03b518ea03b41a580bd30f060f0f09e10d9f1271127419200f6f0f0c1a5b1a151a18])))
(.node (.node (.leaf [0x6bc176c,0xdb0f750898013800680e3e089300c303c203bf17aa17ac,0x4906e502c00079000f0a0702b800f6002504710469045702b617b117cb179c,0xaa1792,0x19300b1c089e18ce17e700fd0e3b0e3308920f7d,0xbb081c06d10061004602fc02f0001206c402f619fc005b18e807b301c8192d19ff0a0906ca01ff02e3190100130dd907a6052c0304188718f0088b08190534190605e201fc003a1a0b0de20a0805ec191d1a071a060c01053819200f180f0d082007ab030119141a050e3c19271a0419fb141c193e0f7f0f6e0f03031d19f70d6a0d65031c1962,0x10a0d170f6000ac00da0bc60d180eea0095012a19130bbe10630eff191600e8193a09b20c530aef168a0f6a0653065118fe190700840190004009b50c610a5f13d105ab191c0f981921007d012d003908f908a810f9193f0fe50a6e0d510d4d13c90bcc05b6044018fb18f9192615c2132f191700af0161006c002008a9034a034913c30afc0164192208f20c9e0c9809900982097a08cd043b00d20016018f0173139e132b00a81909007208040395033c1490148f113c0a76044219250d7d0d700ccc0c9c096e005f0019014600f415771573139b138d191007f4039c142e1139015e095d095b0066013b185400710f5d08770ec013b613241451095e00d900d0015f013e0f550ebf0bad086811b911b511330108009300fd12340bb2155f11ba017f193312fa12f612f004330388011f004618600cc10cbb08d506ce190a1a8b0c920c8209d509d109c609c2096105a2038b033f00a50075003804e40ccd094d09450931092a0923091f091b064905b8059a002b1911006f0b2d04ea067f0678066a066606640595008800410b610b5d0b25066b02e7008e001207a302f6005b03b903b503b1033d18ea07f901d3006818e8031802e501d000130533052a04e0030518f019f605dd05d905d605d305cb01fc003a1a8a0743073e00500c730c6e0c68073a020419080c741936116b1168116211590b310a08191d13f2113606d30470045e17e413dc134c161b184d08c708c308c008b808af05971927194218fa168215c1158a157b13df14821859193e192b185d0f190f170ba308bc07ac03021914127c12760f0d0d9e0c700b69074105371a8012fb147f1585159318be1a84077207a608920ae40e330e370e440e4800c31a891a6c1a191a7f1a6b1a7d1a161a151a141a121a6819621a651a0f1a6d1a1c1a731a7e])
(.leaf [0x11d1176f,0x65085c055300c800320e8a05560e85029a013c01160126000d0f2a07dc125413720d8802a2029600d5005e010e018b00b2001b14370f260bbb07e00cf016a710ba136e0d7f03da01450111009500a901af00ea012f00e9005d0f910f890bbf08f4174410c007d81110108b07c400dc006d01b2014d014b00f0008a148d13e90f99154c09050b5015be14d214be11120b4a0192015b015a0163015400961599159615470bca08e709bb09b809b0150816150bd20161006c0074019a0171009f0990098608cd0652064e029e034b16f116130c24007200400016019f00fd0fec0fe90d4f0d450d34039f03970393033a170d11cd00e200af00ae001901b60fe60cf110750fdd0d410d2f03ac1627012100e8017515c3138f131710620d8a0d030cff0da30d9b059d033f03f9038402a60164012a00aa00b30038001d000e1584156d1569138e1322133713330d0707ee067a0676059303fe02ab015e0122004113ad139e139a132b0e860861067d012b184b0c7a00a5094e094a094309360924091c059b03e3006f0c66184a15dc15d901680c7400a405ee05e805e505da05d405cc003a184907a0005b03ba03b603b403ae033e001a18480b100a8c02ae008614d70b1e01561748151a12b31498150514c50532052f052602a801c301b10147017f002f046b16d216cf15bf1579149513e213dd134d110f109a0c030bf505e1053400220191012e009908c808b908b005980466141d089a088f088c006b17e70068057f057c0389031900370013170516ff16fc14aa12fe12f812f212ee1058058c0c7d092d031a019c10f710f510e810e510550d4305550413011f00b01483147b147818430cc20cb60cb30cb0096808d60589014200a7169b1594153f148012fc0cc8018a1844184206e51280127d127a12771274127112160d9f0c710c010b6a05380049010f17e90f800f7d0f780f750f6f0897031e18410f1d0f150f0c0f090bd30b4c08ba07aa046d01cf01d4183306ee07a608920e300e330e370e3b0e440e481770179117d01796178d177e177a17d117a417b917a817bd17761792179317be17bf177317a6178617ae17b417c4177d17b01787177917cf17c917a2179e17c617b7179817b617781771,0x12b40152011714bb12460c27014b010b009f124c0fd4050f066f01ae00e1002d0041107a0fcd050e03ff00e8001d10540412173100ee01b110ed15d10150016514f5111c01a700f117361518111a01b9015617011514019c14ab14a0124508370149006214c607b1079604ff017f005b12fe12f810580fd107ae17bb177d17d317c417c617c1,0x1c01781,0x1d618e8004901d2030a18ea001303c0031917e2076d076a187b00551520076f1933190a12f60cc2011f089907ad12ff1927005b01b90e3c07a7077306ef1701196d185a169a12fb077c14b014ad14ab07b3193b18d4192918201692141d13df0f1e0f0d0f0407ab046e193e191419560f7f0f740f03031d19cb031b06ec0caf0d6908bc08c819b41962,0x10e81925191b067d05630041003306710560009f0c23132d00fd1922133b0b1b0c72018519041908150f0b1d0204052e051f193019e3199d089c088e19e4006808bb046e03170307191400130f7e0f05031f01fc05cb05e4127e11570bf70c0519060bfd05e21a181a0f,0x186c1a991ac61a161aca]))
(.node (.leaf [0x919176d,0x1030c450ef100a100d30c430eec11fd00e300dc01ab0ff70f9911f80ef609b10c49172401220192010e0074011b01bb132f0d7c0d3309a712ca16b4012d00b100ae0121018c14c9159913c713cc06430cf00d360dc00e251403014b01610165003f00a9012c00b800c201350f470f43099010f3038f0ce30e080dbf0a3006dd06db00d6007200ee001900b200bf007b0047113d0e1f06d408da08cf0ff00fe70fe105900414038706980691065503920abf0a2706d700f4004d006c00e20038001d004200400082005113fc1138071e0c9a08d10c80059203fd05c205b005ac04bb04af013b00a600a5004100390027094709280925091d0664064b05ba059c04b8006f182b068005bb0c360c33007000a009580c38015f0106159415861220018a016e147f14790142182a0fae0f3f011414c512a9017f164c11b111330e2105d305cb01a400fd003a116f116c115d115705ea00f618290d980d950ea20e000ac300b300cb058d057c16080da4145b0ea40037017501470cc40cbf0cb60cb30c3e0968095208d60589078c074504b20b1f0b1a0b1709eb09e809e509dd09d70963040b00a70059008600760bb00bad0776076f0768076404980493048a00930055002508b708b108ae0596073602c902c502ba02b7006b0050000f046b04650462045f045c045902b518280de300bb06d006c7004602f302ef03ad03b103b503b703b917a917ba1796177b17be177a177017a4177f17b817a817bd17d517d317a0179117c017bb17b917b51778179817d917cb1793179e177617b617b4178f179c17a2,0x15014ee1033017a00e60b700ab00aa5008e00800b640aab00fd0e3609f900c3007906f006e90a03127b0b68004900e0010f17e914a50fc20f7b0f6f031e0468014900db002208bd0f190f0e0f05046f006b00d4184d18ab06eb00b00cb000a70f1e0cc8018a18aa14eb14ac11ba10340b6b01a4015d1530152112f410050fc718a801cf01d41833187318a304700e311158117017ab17b1177117c117aa178717a2179517b717b6177817d9177217c5,0x1431799,0x79817dd00620a0a046803121901001307ac052d0305191418f00f0d0537031d08300f03,0x192018d118d00f200c0019441906116f0bfd0bff1171,0x16d41aa8])
(.leaf [0x1b03d603e40044006f06b5094d009c015e0bba09340b820b76009500d500910bc107b8060000f9005c003b07b906290363035f0120003d001713060b7b0620036c012b00da006e13a804860477018e0024002314430482119b04800474013c0057016b00f70048143707810724146a117c07e3032402da0145004e0140005e001400110f640f910f230c0f0bbf04470444140906e30e1807e5032002d8010d00dc0021013700c0002e14391184142004d90ef40eee045202e20a5c0a570f2e07bb0dd70dce06e20ab6051801690139002a00d3007c014a00ba008115e2148a1423020d0901044b14110f000e550a4e0a260a240a210a150a0e04da047c0725054001700004006d018900c4007a004f003012620f850ef50260025d02060351034b0209153d0ad20a120727053c010e00090016015a00830d390d34072e02620217131e0285027d00ae00050121000b0d320adc021b0cf20cf0072c027a00ed003600a9001d10d80e520dd305760ce203a50396038403390257020b0129011e00b20019168b105f105b0d2d0a531048103f10390a20039b098f097d097208ec05fd048403a101ab00e800e700660072104c120a0fd80fce0fca0fc807bf098a05720152010400e1005d013f009214ba12050fd507d91603145d054c021a0d7707800328014b016c003100b114c7060c0ce00cdb0cd90cd70721054b0d6e019e012300a8007b00ef10a910a5109110890cec0cd50ad70a3b054103ee0dbc0d6c00e900b70d970d940ccd00b312b40dbd162515fe0da40d280d210d1e0d1b07220117017500ad12b8160604e209de09d80964067e067403ff016f016e002b0076004111bf0a9e04e6049302aa02a300fd007f0025000e0b1a0a8d049702af01c901cc028a06b6092e178b178a17bf178e1796179b17af17ad17a917b31775178d1777177017a817bd179d1791177b17b817bc1793177617a7178f179c,0x37058c0589011f00a712fc0cc8179e17b6,0x221787,0x18ff09e206ae191518f70f7506bb184419270e480e3b00c30e42192b148106b60d69,0x7f0005e014c07e01066009500e80bcd07ea0bca101d0d3f018100d7016100e400af16520f4c13931537101e027601a50140012a015a000a1187117c125a13181195021600f7191f192100f800050cee021e157c138c11810d350e760e71021d190b007b015e190e00c718f30cec0a2b146c0f50094c09290c7b03e603cf00e90084193d006f00a5001b108c0af20d0b092011e1118b0607060203cb05c905c400f0190c007500ff003b00391554118010c710b010140d000d8a09c108e706a7060f026f068f05f105b0193200ea00b21910006c004300421006098f0989098509790972096e08d0069c0685068005bb1918007200700cb50cb20967095108d5190a19eb0fc400e012f90fc3017f192d164f14a910b201a7194200f115181515111a092f095509c00c7f0cb00a350ae70e470e4a021803b103b70f840f18154015951191115b116708ae08b708bd040b069d096309d709e503d705f5137f157a11de014714961476192b0f160f790dde00bb0de10de8013313ef13f80f130ddc11c6073607370050046018ec04700740048c0b0f0b1812b215b41621174f194815d116d00cfa0d990d9c0da106680d6b00b70dbd01170c27009f06700c220c2b193411bc09eb0f7312690d9609dd1098110d13db101910b61367136b02300622062618f4062a19241362136d061e18f706ae06b70a0401ed01f50003020001f801c818e801d205ce05d205d80c670c6d035a036203770017035b036918fa19b703550d1d0d20190d0c6406730041067819110da319390b2012780d9d067903b507ee134219220c7219080c7619360a0c1901052b12750c6f05ed003a05e31906053403b305eb0958015f0bad009302c9000f02c00049030c0013030318f019ea1927089a0d65053019040b1900fd1158191d19e519e408bb046e0c00192018d00f7018ea03c30e320e36049d0497031c031706ed06f61929141c02b818ed0491049b02cf0ba20ba6158919e2158718d419140f05191519e10e400d6a0e4319e01962,0xed21a64]))))
set_option maxRecDepth 5000 in
private def hintsBasePart2 : Table := (.node (.node (.node (.leaf [0x1564176b,0xc2400fd009f0679066f,0xd5090b0f2b006e013c036c114b001700f5023c0f25045300070111002105c5143702450d47045200390145007d00af00d305b60f900f880a7a0d3e08f8044c006c00dc014d00e8006d0949093508ca05b809b909b114d2106b0612006f00740154003c059909b714bd061700380144014b008a0a660eff05c809b6059e142c14c00b5200c60189012100ef0096013b01780e631689148d0f9908e6131a10f90bdd11391636060f00ff01900192015a012c010100f4017e004311a211e616370be7166f159a153913b911ef113c13d113cd0d4e06aa0d04090800fb01a9018201870161012d00aa08f3024811210ee2166816531340133713300d070e91023800a800f200d20186012200ca000e15c213100e6805a9109710890cd509430b9e0b920b8c0b4706a0165e133c0b120a6202b00164012000e9009201850086164a171416561638158115781574156d1536130e10a60b9d150e14d50b1c14e501a701a4015e0156014f150514c515621151152f15271523130812a712a5017f015d0159011412fa12f6105a100310000ff20cd003750777011f00e300550cc10cbe0cb508d50770178e179b17a91796178d17a41789177717bd17bc177a17c0179217be17b417d917c4177217c517ba,0x37179e,0x18f005370303192000130f70031701d11915006818e80f75089903bf01d21929192718ea0e400e3d089503c31971196e1495141b13de031b0f0c1962,0x18ae03e304cf006f007d091e0a5d00750084145e09ce0a2b013f00f0007b11da108c0a3a00ff00e906a80fdd0cd50247004300e800a80cd005d805ce0983096a069a1918003a19f003770362035e035a023d001719f10737073600500c6d073919080c650cc10a94190d190a007f0b0f0a6206730668076f076802f11904004100550b19067907f702c600fd0068000f0d2415fd11c40b1f134b110d10980e3b089902c819251939192700930dde0a64145b11de10e710540da40da10d9c0d990ccf067806ba06b103d6042e00bb0147191b191118f717dc18ed13f211360de809e909e309db096406af069e0492013318ff08c219ef046c046018ec08ae03691164115b11580e610de10a9905eb047018fa191d19b719e519e41476077a169c13f8192b127812020d9d0c6f0c00074018d40f180f160f130ba208bb0820046e03011920191418d006b7092f09c00cb00d5a0d6502cf077508950a350ae70ddc0e320e360e43033d035503b303b503bf18ea03c3049b09e20ba60ed40f050f700f79191519e10e4019e00d6a,0xf7a1a64])
(.leaf [0xa86176e,0x1a6164611b0017d00fc0b861146009100f50b76150d0453009c015500210c15128e128b11a70b79044601640112014500d30026115113bb0d100f900eec0c0e04aa015d012c00ab00dc0b6c1354134a0d1208f8044c148d0f99008e0123006d01920b27080905ff05f7169e0088005f003b018b09b909b104a40b2e0806069705f216a81291007400d2004201af154a114e10c30d0f09aa0973068215ef015b00ea00af0072016a12a00ee1080b0d0d15a4159915961547135111a910c60d4009840a460113014d00b4016100e8007b129a0fed0feb08fb0caa16da10b212860da90be007fb0aee0a2a015600e200a6019300f101100096008415170c360c3315c9111e113d0fa70f9f0f9b0bd70751074b01a700a0016500f400dd00511651121b12170c3810f310ef0d42142f0fa20c8f0c890c830c80060209d4068705a5059f04be04af017f010600ee013b00a5007500380027164c122013a010e911c711b111330947092809250921091d059c04b801a4016e012b00fd006f116f116c0b2f0d01067d067906670661059200f600aa004105eb05e705dd05cb179b17a91788177217c517c01796178d177a17a417d1179417c417b917b517d317bb17d917bf17cb1792,0x66087f0569015400351508026d056c0afa019a000a00ef00841466027011080e110873026f0a5d013f0082016600bf0043007d11e311db0ace09f3075210890610024400ff0077005100e9003c000709f0061904c104b904b003ed03d303cf023f00dd00a60027001b0fa50acf0e070939092604b503e10152011d006f104b103c093f00e712d81043092f035a023d012800b000170ea00a6406eb035500cb00bb0049001a0e2b0ddc0ae706f103c300c318b112ea186018b010e8012b165614ee13a10fbf0fbb0c4c01a4017a00e014ad14ab14a614a012450fc3014918af12b912b412410dbd01170d1d0c4b0c2d0c2702a5023a00ad009f000e06730670066803fe02ab0041078c074504b21498145b11de0d9c0d990d960ccf06780059014700b311ca11c611bf0e9a0c220aab076402c40431162815fd14930da300fd0055004601750b6f0b66066d0b180b0f0a62078802b003180314031002f402f016080c370c34008e008600130012016e00a0073e07370531052e0528052204c9030302eb02a7121e121b0c3804e404e202e80050002f0106002b0aa00a8d04e8127b1272126912020d9d0b6807400a0109fe09fb09f806e5052c0bf7081b0b3407a104eb01fa01ef007f010f0079009900880003147c1476077a13f211360de806d30f7e0f7c0f790f730ed409e20832031f046c04630460045a15dd15d7141712770a0d05e105dc05d805d205ce05ca01fb187f0142013300db00220168003a090f0f1b0f180f160f130f0a0f070f040ba2082007ab046e0c750c700c6d0c640c30073905e5020302bc015c00d400a40037155512241563137911bb10350b6c08c208bd08ba08b408b108ae057e036901ac015d006b153215200fc60b3708c718a601c601cf01d418331873047005eb0a990b300bfe0de10e311158115b1164116a116d117005ef0c730d07132d13370f1f136d13f8148115871695169802fe058806ce07700967037504ec0a930cd00ff20ffa10001006100800e30cb500a70cc918a30ff918ac17bc17d41790178917b517b7178617ae17bf17d917c117a71793177617b417b0177117b117c9179817aa1787177317d2179517a6179e177c177217c517a217ba17b6,0x15c17d2,0x3a05de05ca008800410b26066c03b601fc18d618ea000307a2079e01d201c7005b18e807b201d6192d00490a0906e401ff19ac0f1907ac01fa082f191418f000cb0f0d05370ea41920014719ae052e09e909db190418ff0498049318ed11c40e9c0b1a067b049d00fd19b10b3105ec191d19ad031b06ec049909e00f030f6e0f771497193e0f7f19a00d6906ef07a70e290e310e341962,0x6e60049190106f3052b010818f01235052f017f1904198a0b1915190a8e00fd1930007f164b122c19800f830f7d046b1944192d191518ec0f210f190f05046f19140f1e0a93193b19180cc90cb6192018d118d01a101a19,0x151b1ab0]))
(.node (.leaf [0x997176c,0x105600ee00e810ec03a9015000190ab101f60080000309f701ff17bb,0x41d0064001e04290504041800ef002d004306ab10fa050a05ce012d012c0096003a13c613b80be0035c016100170bd1055804fc13b41100133713300365009f0033013201220061159113ed13cb0c2a055e0ea213430c22081d0165008000cb01b500fd00bb09ec069f09f7082f16ee11ba11740de205ec0076007900620198015d00f6049404910a0b082a13f90de812f6187b00250149008e0133011f16fc14aa14ed14ea0b1b049807b107a2079a04ff159413f712fc0ea4019c014f0086005b018a0147151414e10b1c03b903b303af148114780156001a0142089e089103c0077b006800550e380e340e290dda0893077302fc02f802f400c30012141f0e4006f006e90532052f052002ec01380049002f1495141b13d813d403160312030a030603030191184200130f800f7d0f780f7509e108970831031e045600db181500220f1d0f1a0f150f120f030bd308ba081f07aa046d030001cf01d4187302fd076f0cc0031c06ed0d6a00b00cae1833036b08c403760ff81001100905380b6a0f7012771891188f100400e308c10cb408c808bf08bc08b60466188d17bc17c017be17d3178f17b1177217c517cb179c17c117c617b4177817c4178617ae179817ac17b0177917aa178717ba17b7,0xb41794,0x111e00f119340b1713d8190417e711190b1c089c,0x92d1a0d,0x55077002f2190a001206cf02f0004602f906d1006100bb081803700068001703bf035518ea1a9106d3077c013318d40f1308200301191408c408bc036b13f618be1a84077208920dd900c31a89035b0de2081a19060bff191d04701a8f1a8005e11a8e1a161a7d1a681a6d1a7e])
(.leaf [0x1550176f,0x6c60049180806f702eb0138002f17e8053709e10533010f0076008e0d9d09da066b00b300410da0067e06ee07a60f0e17ac17b01771178f1793,0x92f00b0006f0d58066100ee0041041303ff0943001d00e9040110990062012e07971362040b005b0125007607ad0de710f40492011f00bb016500250ff213dd12fa0de911bd049c00e3017f019800fd14ea0ff9164e15cd05cb16ef0b1b0314014f012201a7003a01b50086001314e4133b1712164c14ec0a940d0605e815e1052e0303018501a4007f00aa0168002f1518150f14ad160a0d080a9f0d990cfa0c0505350a0c052c01560149016e00b30099007916e9151414a916070da30b1f1172116f116c11570de00bfd0a980a0705ea019c017500f61483147e147b0471046c046901420022147f136c12fb08ae0464018a006b0f1e0f1b0f1808bb046e00d40f840f7e0f0509e20832049b031f01cf183318c607a80ddb0e350e390e420e460e4903ae03b403b603ba001a03c217b717bb17cf17ce178f17d3179c17ba17be17b417d91792177317b017c417c1179317c917b117c6177617cb17981787177817a2179517ae1786,0x15f13b50baf1926009313bc02c80164000f156d02b9015e18ed139e139a04910d37094e192518ff190e006f10e909e40c7a0923191b00a510550d2e0c85195102a6000e01de18e903c503b803b403b203b0033e01e618ea07a0079c03b9005b18e7074504b202e7005900120da00d9b0d980cf90cce076601e8052004df02ec02a801f91911005518f016060da2155c155a138211520b5b0ea80ac404100c210bd206720b100b0d0a8c0a60076c052e02ae1939193300cb009f190411c411c111ba11b611b211340e9c0c240b660b1a067b08b008b9030007aa0ba10f060f20053807420b6a0d9f126e127112741277127a189018c608b602b50456045f18ec046d0466,0xc70ddd03e800bb001b0e7703ed036f07cc03d2192100e90017005d004313200ff4036907d505d0035d015e191818fa00d6003a1524100408c70bf805e101fc0159190617f911680de20bff0a08,0x8580065009108600b7d00de00f711790b3c0c1c11770f4b055201370089009e191e00d700320ef80b400f4e0c1d0bf10bf00bef0bee05541913014c01161905008514110f00125b12560bf30693068c02a0029b193a191f0042000d14750d34060805ff041602490141190e003b001e0008090308f911dc060509a903dd03cb03c7024e18fb00ff00a518fe001b0cee08f4025503e60e630924091c03e305b20252190b00c700c6006f0039101c0ce90a6d0a690ced0944064c05ac029d00e4007d00e9004011900e7110130b040a720d870d7e065502a106a8041903d5043f00f800ea00b200430020153d11960b4609880978097108eb069b05fc043d015a007210b508e608e008cd05b30583057c1924006c18f20cc4096808d6058905cf05d305d903af03b103b718ea03c30e60115a191d0e3205eb1099136319270e3d057e08ae1a151a121a1c,0x11f1ac61a991ad01ad1])))
(.node (.node (.leaf [0x1741176b,0x169a01b9018a14ae12ff12fc0149011f0a0a12f60079015d17fd11ba0e370f190f1f177817c117b1177217c5,0x3c200c3001a089503c0178617ae,0x7e17b2,0x16b146a123c0140010a0e18123700c001151409123a0dce0ab60a5c12ac0137014a00ba1903007c01720ef90a4d0a240a150a0e07250260161912ad191300c4007a004f000901b014100eff0ad30a130728072d026116c2193a0083190e018f12e80dd410e30adc0c560e5215b7011e00ed190701290163028503501047103e10380c590a1f130209bc000b001600e7012018fe027f090208f8034b0ac70fe40c60091d18f518fb008219171921006f062f161805f70abf0c80072c15671320130b094c18fd01af003b00bf00a5190b015e0fce09aa03390257173016bd09a616da060d0e0c0c960ceb0ad6153d131f0b9d00e100af001901ae016201930123013f018800e9015a0092106010530fdc0fcc0d400d2e0a5404090386173215b5159d13510fb10ee30d800ce308e706a000e8001d1948016100df00d200b2006c004310540d42041215d115c90993098f09810976097208ec08d0069c03a1191b1934007210ee09eb09d70963069d015018ff145b083704020faf06b005f601470062011418f70ea50e010ac4082f0baa06b113d8134b109800cb00931927078c02c813640059000f1924076702c70de6005500bb17270cc50cc30cbd0cba0cb1096608d4076f0fbe036f035f1947190a00e000171676100d0fff0ffc0ff40cb60a1d08bd08b708ae03690187191818fa152c152815241309100408c701591981173701b9137a10d510420e9e12fe12f810580fd10128011f1560155a15581382137912f612e4193314ee0b6b0b360b2c0b29017a008e0088162d07ad07a2079e017717e6133e1338133513310ff70e1402fb16330312030e02e305de05da05d405d0035d1922006101b50013003a133c088f08161174116811650de20b3106f3030b02c101fc01f501850068191d004900030c030bfb0bf5088b081905e10a070a030a0009fa06e401ff1906190105350533052d052a05270305028a031b063306b606ec078a092e0c7e0caf0d590d5c0d600d620d670b680c00127b127e08210ba30bd50f210fc214a214a514af192d0f19,0x6f092a093900af00dd027609460bd7000a013b0096071d02160fa811390bdc004d0005019300f40bdd0711021f021c159e113c0101007b18f30161118d0a3f0a7503d113c60d4d00f8007d001b012d0e710a6a03e513cb0d90071606ab060f026f048900c7193400b2004318ed0e910b0f0a6209ec09d9069f02b900ca190418ff000f0a910a8d06af03d702be007f18f7076c076802c4061d005518f40cb207700627190a1a0111890e7300ff11da013f098a0970069a1a00133713300e94073f0736192200500c720c6707391908020201ed19ff0358001705ed05ce035b01fb06b7092f0cb009e013d807730a330a080a9a115c116501c8021818ea01d318e819fc053807420c710bd40f07045e046a077c119311ec036b18fa046418ec046e188c02cd06ed06ef049908bb11de145b014714780f77149615931693062b1924136c1362113613f203710a640dde00bb0de8013313f6193b1481192b0f160e4116910f1319140f0e0f0313f119290f740de2191d0e3119fb0dda188708990e3b141c193e0f7f19f70d6a1962,0x3c0006818ea089403c21a68])
(.leaf [0x1082176e,0x13de0191012e0d6a136400b0183e0cae177917cf17b7,0xc76016800a412760c70177317a6,0x19c17c6,0x7c0a5b0a4a016b008514460b0b013d015515f307350725150c0a80128c1943004f01831902011214de07330e8b0a820b80192e191f00c800911371170714e00d35072f13a40e880e810b7c03ea012601bd190e192500f7001b1373168f102b10290a85060a0601144b0d3b139b11820b8403dc018b193a00e5003b018f015e005d117e154a168c08fd05f8172e167f11e104cc19321931194618fb01ad018800ff002915561356134f0ff008fb04d41023146211da04d619470123191700e4013f01041723172716a612900cee072a0c8f0c80060210b8102510120edd0ed503d2194a01af190b00a500ea00d2004316bd0ce316b516b216af144a0cf70fb3092313670987097408ea069a08e301ae00b2193c00df006f19240072006c14c8120617350d8b0f480f3907d30b2e06610cc50cc3096608d4014b01b9012a00d600880041190a174914bd130012f00faf0f4005de05d4066c02ff01c30154011f0114003a008e001217041701150414c412f80de7077703b407a202f51942017f00bb005518ea19740e490e460ddb077403c2092e0c7e0caf0d5f08b008b919b4,0x650860085800de00910c1c0b7d009e00f70bee085911790f4b19050094013700d7068c0bb40c1e0bb50b7a140a0f4c004219131934191600da014006810f0013ec0bb80f9a0f6a14680070193a0132018019450190016b15020faa08650959153d13b4138711d811d01177069516c815f80153015f015a19260129191e01ae12af0c1d1323131d131a15bc15b9138311d216850116192101630188123c12380f6013280fe61576157215680b830ee4010a193c1917015e00d211f716b00fe90b9b0b8c010301af014d009211d5140f110610ff0c5b129f12950b9919381937191c1907011312641261125611f90f870bf30d870d820c4714ce14ca0f4e04fb0c5f0f9e191f00b200a1014c002c010c00dd0cf60cf30cee0ce20c3f0a5a04f50beb0bea190b007c0097090308f91020101c0ce90a520be90231022818fb00e400d600061018098e097c0978097108eb08e108d9022e19240072006c18f40cc70cc40cbc0c3e0968095208d6062805d205d81a13,0x19331ac0]))
(.node (.leaf [0x8ad176d,0x14a14b20f2d14b8015300d501ba14b51315109f17220f2216a90f31017d012000e901ab00dc018b1646130c10a41209125d0f9916a801a6015e0104010e019201af154a135411b010de11e004d50d330d7c16da12a0015b012300fc00ed00ff002900ae00b10193011315a415991547135111a9156a10df12070cf009b10e750ff00fed04d4069106430fa70f9f01610164014b00a9007400c700e20042003f00dd099013bc13490acc14bd0d800ce305c207cd04cd09aa0c9a0e7a0c8f0c8009d40687059004be0072012c0082015400b20039005d00af00a6013b00a50075003800270680105c10530d2e09840e080abe087f087c0659065505ab033502750c360c33094709440937092809250921091d05ba059c04b8007000e800bf006600400015000a172716a300a0006f095803aa03a3039b0393038f032c026501ac08b708b108ae0596015f00191697169415941586006b0bad086807c7057c03890330018a0465045900930037147f17dc02c902ba15c9159215b311ac0142000f01650162077b02c610f310f10d42005500ee129a076504b2041403fc0387026b01560059001d0b1c0b0d078609d7040b00860076150514c50e000ac30c2004980493017f00cb009f0025137d137b10d612f7105711bd11b10e9b0c23049c1533130a12170c380128011f00fd0159010615c1158a157b138013f2155712f511ba0b370b33066f06670661059201910133015d00880041141b13ef0b6c0b28066e0138008e0e470e400e360e2b02cf0833082c0829040100c300620cc20cb3096809520771058907ae07a7079700a7005b02fd02f502f1001218211712164c152f0bf701a40099116f1166115a11570bfd0b2f00f605eb05dd05d905cb003a03c203b903b703b503b303b103ad01e5177b17961770177a17d117a817b8179117a417b917a017c017b5177c17a21778179e179817d317bb17c417b4178f179c1779177217c517ac17b617d917c917cb,0x15740189015e1688132001900121153c13d2131b015a012d012c153713c613b8177717bd17c0,0x12217be,0x14d0a7914d9007d01960a5f15e914080ee20084016a013600d20aef15e80afc14070441043f0ede090000e80173016c0020013f18fb107711f1113f0442098a098308ea043c01ae010100f4007215a711f0113d0993,0x18fe09a7091c190e006f0c7c064e064b00a500400d2e0c8503fa00e8001d03a903920384027b0019000b032d022100150006057c03890330022c033618f2006c08d60589098308ce190a1a200cb519181a2101f501f1000301ff19011a1f022214e60017018508c208b708ae057e036916fd16f0166118fa01b5184d1173117011670470191d1a1e15e0141613f40a0c193619de127e12750f0c01fd035d05d402270278035603ae03c301d518e801d318ea03b3020408b60c6e0c760ff7133b134319220c7305ee1a121a151a0e1a161962,0x3bf1a9f])
(.leaf [0x860b1e0a8c0156007f1514046a019c0022141e0a9a0471089d013800f600680e3e0e31089317b417c417c6178717ac17cb,0x41000cb001d082e04030062083207970e9b00db005b00fd09e0040b07b3049d00760149002509ec0a09031202b906af016500790013000f004410f3041206e5030c02c213d906ba00ee0049012e0d5a06ed06b7031c136400b0183e0cae01cf01d4183302cc06ee07a60e280e330e3b0f8007ab0f1802b404550a08115900f60470184f006b186108bb00d4185d185c0e48184c0e3017aa178f17c1179c17d317b1178b17bb17cf17b717cb179517a2,0x9206a10b9b0043015e06a4094e00af139c006f0d41012b184a00e813ad0c6c0c6601b600a416ff05ee05e505da05d405d0019c003a14a90b2b03b401490088001a07b207a003b9005b18e1166a16681653018612b90dbd0117172b15560565055804fc10ea10e810e510550d4301ac003300ee153113080b36171516580a0b0a0209fc0201074504b2055b09e409df069f040d07370736015901a400790059008000760050155915200b6b116f0e600b2f0a0705ea0e000ac3078d040f0c2d0c200bd10671056004940491048b015d00f600cb009f002511cd11bb11b3115911350e9d0c250aae067c049e01c618c608b008b608c108c817bf17a617c617c1178617ae177c17bb17d917b1178f177217c517cb179c,0x3205540557008501160afe125500c5191f0e5b0b5900f7008d0aff0b7c051e051a051100c8009118ef085d08570514006503f4001c025c025903f2000918f60206056e000418f1060705fe020e0577003b011e03eb03e003ce0e24056f001b00c218f90a3103e50ac103490208007b00c7008200160a3f039003830258020c0e5e05f8034b071a071305bf034200f80019012a18fb004d0039119408ab035403a90d8a0d8708f305b603d4043405bc015a191700e800b200a8006c0043002000700cdc103d131e0fe605c809830970096a08ea08ce069a043c095a012000e719210072015f15361322130e118310500b8512ca0fdf0fbd05d805d205ce0e8f0bad015e011b00e0003a00ca0093139a13040e86086112e30b5a1523130812cd0fc50360035c03580a9102cb1925193301590017007f000f13af12f612f012c9105a10030cd00375076802c401b60388011f19180055170b104318600cc10cb50cb20967095108d50770019f0128190a0ea80ea10ac406cf06c9043300cb0046163c082e02ee0b3705de017a00620012008814ee07ad079e079602f50b6e0b2601f70150005b008e0003149d07b3053201f9192d18f012b30de30dde03710a090a0309fa052b01ff194800bb190115d00de20b310a0805ec0b120b0f0a8e1934191d190411ca11bc11570e200b640b1900fd1961031502e6001306e506c5030c0049073f073614980ea406f800500147192910f510ed10e810e510550b080555049d0497048c0489042f02b816d01589157a1496141c137f0e5c191b18ed193e192409e409d90965069f049313df13da136418ff1927195c0d640d610d58095306eb031a190f19600de806d301331585153e13f6136c127d0b6a0742053814781193077c193b192018d40f1e0f180f130f0d0f040ba207ab0301046a045e1914184f08c808c408c108bf08bc036b195e195a0e3c0e380e340e290dda0a3307a7077302cd19590f7f0f7a0f770f740f6e0f030ba409e008300499195518c618a3183301d401cf01c901c6,0x144e01b7013d165a16b314490184193c1267132816ad191f1921194116c3144d13c011ce0cef13200db0018f1926191e190b015e1912167e0698069511d30ce415810da70ceb01880042016300b201a900ea00e9146514630686110510f90d8216bd1685150010b00da80a3b013f0075191c01ae015200f0007b146609cb09bd09b6124d12460af20a2a019a00ed18fe010b00841508139113180d8c0d3b0d330d3009a7068f050f05060154012a190e002d107a106d10650d2f050e04ff00e819750d2b09ae12ee1058079700b6011f00620dba12ea10d50833013201280ea20ea000cb16f10ea6019f14f30838171416680dbb0737073601501944018600b7005014f611701164139b04fc170d166c145b0d9c0d990d96073d066801a7191d1925003301b601471911004111c611570e9a0d250d20055e162814930da317f200fd190d00801939160e11c00d260ab405600400165b0b20016f009f001d194f1904150512f912b912b512b412410dbd0c2610ec10e710e410540db40aa805610412176a10b20b16017f0117191b01c300f1198a173212bb10f7151b15181512111a14ad14a012450c6d0c6419481930192d190815d113ee111e0c2b10b6088f16fe16f6151414a915dd15d70c761934192400681942193613e013db13d813d41362110d10980899141e141914161927192916d216cf1680157913de137e17e8193e09c00d560d5a0d630d6508950a350ae70e2b0e320e360e3a0e470e4a03ad03b503b703bf18ea03c308320f730f790f7c0f7e0f840f1807400c6f0d9d1269127212751278192018d00f70136d18d41476192b0f1619140f050e43040b09d709dd09e509eb048c04950497049d18ed0491049b191519e10e4019e00d6a,0x4906ef06e500c319010e300a0703c201d618e801d21a101962]))))
set_option maxRecDepth 5000 in
private def hintsBasePart10 : Table := (.node (.node (.node (.leaf [0x16d5176b,0x1ff0003007901fd0468003a002205eb047000f60bfd05e10099053501fa17b1178717cb17c9,0x6f000c300490e40030a0138182300130f750f6f031e00db141b0f7f019101cf01d41873031c06ed0d6a0f0517ac17aa1779,0x6b17a2,0x192510e7067f191b004109e402ab18ff000e0da009db02b219110da4066b02ae193918d618ce11c4067b00fd197906ae02bd18f706bb19270e3b0e370e3307a6077202cc06b60caf0d590b680d9d1278192018d118d013de141b0470115802a902ed,0x15211933187b12f512f3011f130007ad01b9005b14af07b2192d169a170114a9193b185d0f210f1f0f1907ac19140f0d192019f90e3807a7188708990f030f6e141c1691193e0f7f19f70d6a0e30,0x1d018e817e901d6196219d01a65])
(.leaf [0xff1176e,0x6908a008a500ce015704280eb108a30eaf0f9608a2001e012f00fe00dc11d4110403c713e406940f98016300ef001b01660042019209bb09b00420056b03da15d205f30d7d0d7a00740035005d01a9003b00b110cd0569064d056a07d015800fa9060309c200eb00660040008200d0015e00dd00a5007510ca1599138f138b039b039311e711e30ace07120b5d094f093c093309250921091d03e400f10161012a001900ff004d008e006f15590ac30c20111a1070106403ab0d8406a70437066c06680662015d00cb009f0156078c00e800b200430020004111bb0e9d0c250b1c0059111c09900982096f096c0699068205fa043b03fd03f9038400fd17de076701650072001d049d0489042f005509eb09e509d70963069d040b17dc02c50076000f06af05f503d702be00441839079d05ef05db05d505d105cd005b003a03b903b703b503b303b103af03ad033d027701e502cc077207a60e280e3307aa0f0609e20f7e0b69046c05eb0a991158115b115e11640c6300a40c760168116a00f604710022046d0e3012760c70010f0f700f0c0414105610e617d017cc179617bc17d4177a17a417b8179717ca177217c517c417d3178f178b177117a6177317cb1787,0xcb0e9f0e2b012800c30d63082e06f000b000620049031a0312030a001317e90304002f18b9149811de0d990d9615d110f40b63066e014700b30165008e162814930da311ca11bc0e9a0c220b64076402c4017500fd00550b200b1b0b180788076e008618b8079702f6005b12ea105707ad186018b70bf70b2d01fa0737009900880003005015dd05e105dc05d805d205ce05ca01fb164f15ce14f61272126912020d9d0b6807400a8d0168003a01a7010f007f0c750c6d0c64073905e50203057a14ab14a01245122d07b3147c1476077a13f211360de80f840f7e0f7c0f790f760f730f700ed40ba609e20832031f046c046000a4003701490142013300db002208c208bd08b708b408ae057e03690f180f160f130f0d0f070f040ba207ab046e006b00d4184d18b317111656164b14ac156215591381137811ba0b6b01a4015d153015251521130a12cf0fc70b3818b210000ffa0ff20cd00a930a1b037500e30cc10cb50cb20967095108d50770058802fe00a7169c16921587148113f812fd0f1f0cc901c601cf01d41833187318a3047005eb0a990b300bfe0e311158116a117005ef0c730e940ff918ac17b717b0179317d3177617b417c91773177117a6179e17c1179817aa178717a2179517d9177217c517ba17b6,0x1891777,0xe3500fd00c30b1906ee190419b8052f18f005341906127a0d9f0c01053819200f6f1915049b049818ed04910ba10f0c02b5045618ec046d19b719b6046619b40bfe115819b9,0xea10c710c201610155106f088800e800671066080f014c006007f007de0814005e192e0bc907e01228009501070f660bc00bcd122900da19160181016b122a0f69125a0f86123d123c0bc701ad0190191f010a172f14e00eec0ee9081115f91240039815b90d350d1501bd191301ae00190163190e00ac168f168a0f01124e0cee033a15590c540c53193a010b190b0016193319070cac13930d1a11070ed81024101d0cea0c58034d0b6c1747172c16850d140c5a1909012a191c00d200e400e100b9008e01af018800e70c9a0d8a0d82044108f80c7b08e10a370a2d080503480b6f15831572156f1568138c104e191000b2002018fb00a5006c007b005f017a015e0d6b09890985097d0972096e08ec043e040503840fd413580dcb08f1094f09400928092508cc054b054613a1139a00b70072001d014b012300a8006f0031192509dd09d70963040b10ac109d1091108910100cec0cd50943054f12410dbd173116ca10f010e810e5041318ff00e901171948191b0492042f0d990d960ccf12b715d110f417dc1911016f1934000f0da311bf111c0fbb02c404e404e2193900fd00f100e00055002b0b200b1b0b180a0402f402ea1904190100120531052e052b02eb18f01a3906c70431057d038a004618f2077a136a10b510180cc60cbb0cb80cb2096708d506ce0588192b1924190a1481136d12fd0cc905d205d8057e08ae08b708bd02ce07740a340dc50e350e42033e03ae03bc18ea03c21a151a121a181a16,0x149c1ab7]))
(.node (.leaf [0x1da176d,0xa08181908c808b908b308b00580006b04650462045f02b500220a0209ff09f906cc0469020100791815127a127712160c710c010b6a0742010f0f7d0f780f750f6f0ba509e10897049a00db0f1d0f150f0c0f090f030ba108ba081f07aa046d030017a2178717b1177117aa,0x3e0579063000370091032f0b78001500d30332032e0f01005d0036018907d908f705741688014b006d00f2019014c1060105f90a3d157511260b82017e003b007b015e13d213ce060c0a3c153c0b9d07c60572012d012300e9015a009213c913530d7f08e906a0016100b2006c00430992097108eb08cf069b05fc035f00720017162e05d905d305cf035c0177003a133813351331132e05ed179f179e17a9179d1777178d,0xeb17ca1797,0x106f00e801610984133500721922096c0d061910190c0d700cfa191c19110dbb0d950d6b00b71999169415940d9d126c,0xd5e1a0d,0xe3d1a95])
(.leaf [0x15af176f,0x141e0138019c141d1483019101421690147f0f1617e80f0417ac17c617791798,0x16900191018a141c0f1e013800d40f810f760f051779177817ac1795,0xf16192b191414810f1f0f0319550e411959,0x193b186c1481076f07ad192b005519740e42077400c317de0e330b19,0x13b0e79094611b300c7006f00fd03e803e411c4001b193902a50da4000e19110b0d02ae09db190418ff0a8d03d6049101de007f18f718ed18e90a9b02be02b801e9014f000f005514e80dde02c1053002a90770019800bb004918f0190a077a13f913f2081e046c02b606bb030c03040cc9192b0133006118ec1927001318d40f1b0f160f130820046e089a08160317191400680f0509e20898049b19151a5916eb148319420e480e33077202cc01e503bf01d101d618e801d20d9d127813f514170819088b04700a990de1115808ae08c216ef16fc0357036f0017036918fa19ce053408b5035518ea03b4035e14e70185166001b5134319220c7219080c6f05ef15e1186905e61173191d0bfd05ec0c0319060c0005e31a58127e192018d118d01a121a101a161a1c1a0f1962])))
(.node (.node (.leaf [0x623176c,0xbb2017f009314c60ba7014b010814c70ec30ebd019e00d014360ec0013b09470933180916ec01980dea00bb06d0004602ef180802a313f913f206d3000e013302b113f305cc00b30168004116250da4116b0de20b610b5d066b017500f6008e11c311b911b111580b65067a145b11de00fd0147049e09e90964069e002500760b1a0b0e076d049702af06b003d80086004414e10b1c13dc109906ba0533053002a90156012e002f16eb1516157b149713df127912700f0d0d9e0b690537089d019c0191010f0068141e141613f00f7f0f770f6e0ba409e008960499013800db17e817e703c003b603b403b0035601e6001a18060f1c0f140f0e0f080f050ba308bc07ac06b60d5c0d6902c306c606e606f506f802e30303030e03160013030d01cf031b07a60dd90e300e330e3b0e440e4817931773177617cb179c178f17b4178b17c417cf17b017c61779177117ac17aa178617ae,0xf02c502c000550049077406f002ce00c30e43077c02b6014200220f16046e01d41873076f06ed00b00cae18330464006b187d1879147f018a18891691187e17981787177817a217b7,0xa717b6,0x171101a71944164f164c,0xd90f530b6109c60108008e007512340b6b09cd017f193300f01651156310b101a700ea16490db1017e00b5129e0db2011305510f3c003100d6054b0f34007b00dd0bb00ba70a370bd7009300e100960baf0fd80bdd015f015a01011585153e11ec193b18d416950fa801930ed113940b9e0b98054c00d2012a009213b5108d0a3b054f0441138e0b9d192600e90020015e134a10920bdc044313cd0db311df012300f4012d00ff159e153913b9135211ef113c0ede0d8a08df08db06ab06a706a20161013f00b2006c00430ffa0ff20991098a09870970096008ce069a043c191800720cb50cb2096708d5190a1a0911360e910d000cfb013300ca190c13f31337133313300e940d07193619220c750c720c6a09c00cb00d5d0b8f0ba40ed20f82157a1589169113f114171929141c0f741099110e134c13dc06b2069f096509d9042f11de145b014709ea0f771496193e0f7f0d6a13ca159015c715cd10e50bd40f070f130b6a115c116508c1195d05380b6511330736073f0e95013e07430050045e18ec047104560742048c11b511620cf8139a192513ac19400da519110da3193911c300fd1159191d1a0719fb11bc049d18ed04930499127a09dc15ca10e8191b10f3193409ec18ff06af18f706ba06b709e013d919271a040d650d5a05ce05d205d805ed0bf9190605e10c0119200f0d19141a050f030f6e19f7,0x9ad00b618fe0d2b09a8190e0d370c7a192600a513bb0925091d0164006f156b094d015e13b61522015f139f139b01590bad1925152f00930db619a419440bb2191b09fe14ac14a4017f09e3190117e612fa18ff052b02eb011f195d18f00cc102fe0305190a00130cb601d0191818e8132b0ff701d3192218ea05ee03b312fb15851a8407a60e370e44046f07ac08bc0ba30f21157b158a15c113dc192713df193e185d0e4800c31a891a171a151a121a6b1a181a691a641a161a651a0f19621a1c1a731a7e])
(.leaf [0x10cf176f,0x14be0154014b106a109b00e800e910710ff3016100e313350ff701220991132d0072012b08cd067d006c0041094208ca066217ba17be17bf,0x6f801380049141e0e3e06eb019c18ab00b014830cc20cb0014200a714800cc8018a18c90fbe00e0153115271523130812f212cd0fc50b3614a914a414a1149e149b122b0fc107b1015901491715164d153014ed14ad0a0a06e501a400791172116f1166116011570de00bfd0b2f0a980a0705ea00f60471046c046904630460045702b6002208c708c008be08b508b20465006b0f200f1d0f1a0f150f0c0f090bd30ba108ba081f07aa046d030001d4183318a318c617ac17c617b7179817b6177817c117d917b117cb178717a2,0x1bb177f,0x140326032a0069191608a0083c0325032800ce006319100e4b083a029500c4000c03c403bd028c18ea19c90db800b60d350d2c190e0c5419070c5f08a8010c18f90eda08a700d200a20ed90c50037b010b18f3124a0e50061c02a0024a01731923000d0e53083e15fa0e1407ec135c0eb208a40426041e02980129016c19221928001e13010c5116020a1c04db03790297024f132f10bb04170120019e1918001b012d00ea00430fe408ab0e6a10a70ff203ec0e250dac0ce710bf12510f570e7d06160b8d06a1191700c600e900c21912014d014b00d900c7008a00920a7e0a6f0a680a3b0a300750026f14d114bd0f5907ce07c403dc0b8b007d007b0051000a0154005d009d14da135d0bde0b480b920afd0aea0a5f0a2c074b0294026c087e07c00659064f029c0646063f029101a21931009600f2008400350066004018f615a31548133711aa10c80be30bcc09b1064d042111210af5056a03a8039d0399039503910267016118fe00fb00820019158c0c1a134f0e1d05c710fd09b6056c042a0e040abe03a2016401231921191c00bf13bc1349131b10fa0dad0d3614360e7a1141113e0e1e0e020a751926013b00f4121313b7132513f211361947015f013316971594158613f7193b1481192b10b3077b01e805290526052300f1005518f00b160b0d0a60076c052e0d5508c108c419b4,0xbb0de5081d19240061136d0815081b193b0068190614801363089a0de10bfe03bf192b1927191d18ea0e430e3d0e320ddc089503c31a490f1d0f15081f1a4305ed05ea05e105dc05d805d205ca01fb1a1c,0x5861ac8]))
(.node (.leaf [0x917176d,0xd7e00b200e90d83094400ef006f10fb0661012c004113b210fe04000132001d13ee040101650062111c13d51099079700f1012e005b111b13b6136207ad0156015f0125011f15141585136c12fb019c018a1482148017bc17c017d317cf17c417ce17c61778,0x2f052b053501f90079009900030a0c05e101fb0168003a0c7605e60204046900a4002208b4046e006b00d4184d18a913440c7205ee01220ff70a9300e30cb500a7148113f80f1f0cc901c6187318a3047005eb0bfe116a17b017b117c9177317a6178717a2179517be17ba17b6,0x13917ad,0xf46014b00d614c70f48019e193c16ec132708da0bf80ec301981921006c190600d016ef131f08e905e205d314360ec001b5015a003a013b16ac1343133105ed11390193192200f4159e15391336113c016119a915c71590193410f4191b19a81324015f169315931585153e193b19a70ccd19111625067f0678066a066405951939004111c311b911b111330c23067a00fd11ba193312f6011f165012f912a9100d0ff40cd2017f1918123512310ebf08c00597010818fa0cb4096608d40bad0ba90ba7046a0464190a009318ec06cf02ca02b50b370b2a0046000f008802f302ef02e906f306e806c402c10b5d0b25066b00120049008e07ae07a3079f02f601d6053304e0005b18e818f003b903b503b301d2030302e318ea00130891054903c00319006819a613f913f2113606d30c730133190815df13f30c741936116b11650bff0b3105ec031b06ec09bf0caf0d590d5c031d08960ba40f7a158a13f0141605370b690c700d9e12151270127918200f751929141d0f7419560302046f07ac0ba30f14191418d41692193e0f7f0d690f0319a01962,0x2f50012197402e602ec00c3001318f006ef030b01f80049000306e6020119010e300a0701fd03c301d001d518e801d318ea03b31a0f1a101962,0x89c1aa7])
(.leaf [0x3de001b006503e4086403f5006f0153001c0922086310de03f600a5012b00ed00750c82139e10df09d300e201640fea0c1b014d009d12850bce125c01100096010e025b0f9c0bd80cf0000900dd00a90d340d310262038202570fa90ce200ae001901a900b20d2d086d039b084a11e6097203a1157f156b094d00e80066006400ff0072015e1288106a150107c107bd11d9098a0b8b0843080d13200fe501540152005d013f0092005f012114be14ba07d9145d0aef054c0544131c0d37014b016c00840031012c14c70c90111409cf0ce00a430a2c054b10f9019e012300f000a8007b00ef10a910a510a11091108d10890cec0cd50a3b03ee0dbc00e900b70d9a0d970d940ccd00b312b40dbd162515fe0da4121b0d1e01170175010600ad12b8160604ef04e404e2067e0674016f016e002b004111bf0a9e04e602aa02a300fd007f000e0b1a0a8d02af092e09bf0c7e0bd50f080f0b0f1117bf17b91770179117a817bd17c017bc1793177617a7,0xae1008301530adb0ae20faa00ed017200de0d321617119e0866086000ae01af00fa006509a809c810e010370b7f085600740075016400e7009109c60c590c54156d119d10500b850ac700d900a3015e008210aa109f0ad505fe11df0abf0acb09b600e9003b00ff00bf00ef1092060e0c6011da0e0c01230121013f1348131a10f9012c145b11de01471499019f14f1015013b71325122f0f53015f01080b610bad0ba706360631008e0093003e0b6c05850578015d003712f5058d10ed10f517a817a417a517bc17bd17c0179f177217c5179e,0x1a17ae1786,0x15214fb0acf017b008212db13bf0a291248011d1926007b010b0e0612dd131a0a440d7200bf01881921016a19100a3809c30e0d157112cb0caa0c9a027000e10075013f015e011b1909000a08df0667124d1466138d0fe00c980266006c004101ae019a012a191700af001905d405cc0e021077107210620fdb0fca0d3e03a9189500f400e81336113c107001610991096008ce15791680067c11350c660c690c6c16780187155b193311bb0c77,0x4d20029191704d004ce0c81007d005d00a50a6a07cc060200c7003b03e603da03cc001b0c370362035a00a000170c38035b0106003a122105ef016e19221609134301b50c720c3015e11908186919e916fc19421514150e193019e817160fbd155712f5194400e001f519331530152510050fc700030b700b6c187f0a0301ff02a30238008e1901000e0532052c052604ca02a801f90c7f0e4a035503b301c818e801d20f7e0f0a0f180b680c6f1214127b1282154015951479192b0f1605eb116111701173036908b108b708bd18fa19b7040b069d096309d709e503d705f5137f157a0a640dde00bb0de10de8013313ef1929141c13f80f130ddc0b6411b40736073f0050046018ec04700740048c02b00a620b0f0b120b18160712b215b41621174f194815d1193411bc09eb16d019e20ccf0cfa0d990da102ab06730041067819110da319390b2019040b19049712780d9d067900fd1158191d19e519e408bb046e0c00192018d00f700e320e36049d18ed0491049b03b518ea03c31098101910b6136702300622062618f4062a19241362136d18d419140f05191519e10e400d6a0e4319e0061e18f706ae06b71962,0xb8f1a64]))))
set_option maxRecDepth 5000 in
private def hintsBasePart6 : Table := (.node (.node (.node (.leaf [0x1626176b,0x310551054f04e1011300e9002b0f3d0ca30d7f129904e700d600a600b20156007f08da08d209720b1c0a8c0bf8006c0072008600990944092808cc05d905d302af0bf6006f003a000e17f2066105ca02aa17b517c417b417c9,0x7a900c3005b0e4507b1017f0149164d14ad0a0a01a40079116f0a0700f6187512f907af011f187414820e420142169c148112fd18730cc006ed13db1842141b01910d6a00b00cae183317c117d917b117cb179817b71779,0x3f17a0,0x76f190a005502ff02f4001202f717dd03ba18ea01d218e801d6004906e70080049418ed076d049719040b1b0aae06ec0caf06ef07731962,0x20019010003052b01f8,0xe3f192900c3141d0e41193e192b16911480193b0f1f0f171a701a73])
(.leaf [0xcb7176e,0x1540fb50afb14bd00df0084014b0aef0fb20aeb14bc07d900e8013f00cd0152005d14ff106211db0eab0853084707bd01a9012a00ff00641580138d11e00fa90849015e00dd094f093c006f18350c20009f11b30c250fb000fd01140e9c077700cb0055078e076707720ae40e280e2c0e3312701273105610e6,0xdc0f8c0eec011800d30db7125708f80b7900b6010e006d00910f980dba0b830cee08f405fe01920132015e00a9003b13890d3516d612be13b2063113210cf105c403cc012900ae01b2012c003e01210039001b10d90d30175313c4062d0fe7094c05b703e100ed01c1007300e2006f09cb16f3150b0db509a40c810c7b0924110c10fb0075019a015400ee00a500ef09c114661072106a105e10540c830d8205b400b1013f00e800b2006c0dbb0d6b098c09850972096e08ec08d005f500b70072004409dd09d7096306ae007618b510d501280ea20d630d560c7f09c0092f06b700cb00b0078c06eb0059004909f803140310030c02a5023a00790013000e052b04c9030302a701cf01d418331164046900220470105812eb179617a91770178d177a179117a8177e17c0179f17bd178217a317b917bb17bc17b8178b178f17b717b11787,0x1681773,0x9da18ff1911049309e10da318ed193919150456127a0f700d9f18ec1890046d19b511c31158049c00fd0e3f0e3500c311570e30046608b619b4,0x168c193a1946153d1720154e015a01ae19311546153710781350016100e801231685158f105c1091134c01880164012000e919271572156f156b130c10a413e21057015e01c3011f0ffa0ff2139e139a13041736168115c0157a151b152d1525130a12f41918192501b9193e1930187f1a210da10d9914b00f810f7e19011911192d191519e40da30f180f04046e19391914147e0f17192b169a16901593153e147f12fb1a3517691704170114a9194f1942175d16fd160c01b5165f150e01851346133c13361332132f132c0d0601f51922000315e015dc13f40a0c0c730c6e0c6b0c6802041936186901fb05d805ed19de0d9d12751278127e0535081b088d0c050a990de11158116d117011730e390e420e4901c718e801d3036703760017035618ea03c2036918fa184d0470191d0bff19060c00192018d118d005e119b705ea035b1a1c1962,0x19301aaa1ab2]))
(.node (.leaf [0x99b176c,0x840af5074b00fb00510e04074c00bf00a5087309230066006f039d066100190041038903fe03850037001d0e00057807450df8041200cb003e005900be00ee0ea40ea10639078605cd0aa309e4040d073e0737014701280086003a0080007600501495137e0b1e05e2086804940491048b01910156009900930025147812ea141d11a1089c088b02cb02b90142011f01380068000f148012fc0e3e0e380e290ae5089302cd018a00c30cc907b007a900a7005b02fd02f501fb01f400120003052f052902ec01f903ad03b303b503b903c2179e179f17bb17b4178f177917c417c9179c179817ac177817b6,0xeaa00ff00cd06a60aed004300840eac06ab0af7012a012d0101139613c611ed01bf0161173a15a601ae1760173401b9170210e5019c00ee151410e70156012b150f13a20185017a1662163e0e9101b800ca14580e95013e167614520187134013371330132d012205ed05ce003a0c04035c009900170819036512f0155b015d12f617c617bb17c417bf17be17c917c51772,0xdc1796,0x957013d0070114c095000f5190a11520cb61933191815201004187b199510061932118000f711781179010001370a5c11e911a70bbb0ef90ef40eeb0b79007c0172014500d51913140d0a58128e128d0b8111850ade0f900f220eec192c014c01120169008319161484140e115314ca1253128a1210120f073507260725148d14870f991937015301180105004f193f1260125d1257120c0ef6073315e415551211169e0f31191f1947018b14490cf50cf0072c172916a816181291154a114e15f7123e193c190b01af193101ae14030db90ce30dab12a015991596154711a90bca124d013500b600b2191201130161010b14010d330d2a072d16da0d900da90f470f3a0be00bde016a190e0193011000d600960a460fed10de0d320adc0fa70f9f0f9b0f350bd70751007b191700ed00dd00510510142f13fc10ab10a410a010900ceb0ad60a3a0c930c870c8009ca09b909b104be04af002d013b00e900a5007518fe0027109d0f4504fc0c200bd1094709440940093709250921091d04b8014b0033009f006f12880d8d0fd409aa055d066f066706610154012a00e100af008000411079106c1068106410530fdc0fcc0d400d2e0a54050d11b10aac067a0bfa095800e800fd19060736015f08b708ae0c6e0c6b0c680c65115d11570bfd074504b200500bad18fa1869191d00590462045f04590093184d0a0d0a080311030917dc02c902b419010013000f06e4030a02c00049199403ff001d10e710e410540db40d420aa805610412191b150614c615c9159213cc10f40c2b088f08160317017f1934006813db13d8134b109808991993173701b914a514a212440a0a192d137c10d5104207b107a2079a04ff02f50128197412fe12f812f212ee12eb10580fd107ae031b06ec078a092e095409bf0c7e0caf0d550d5f0d620d6707400c00126f127208970ba50ba30bd50f080f110f190f2106f619290f7502ce07740a340ae60e2a0e2e0e4603ae03b003b203b403b603b818ea03c2077a192b0e420f1719140f04040b096309d702b9048d049606b918f706ae06b6129a151915ea16fb170117041942151619301992049818ed049109eb09e518ff19870e350f83049a1980192018d118d019780d5909e10d690f7d0e49,0xcae1a0d,0x3c31a95])
(.leaf [0x15ab176f,0x319001317e7031e18201855132b012b139b015e18540c9200a5094d0923006f185313b61324015f0bad15900da40093016501750bb210f410e909e411c311b111330b65067a017f00ee00fd13dc13d9134c0d580c7d09be092d031a11ba0b6b0585012e00b0015d0037168215c1158a157b141d13df0d6a147d13f2113606d312fa12f6058e019101420133011f169015931585147f13f612fb018a0cc80cc1096706ce02fe01cf01d4183308920e330e370e3b0e441851057f08b508b808c308c704550ba30f050f140f170f190f1f00d408bb0a080bff0de211591168116b00f60470184d184c0e3017bf17d3177617bb17cf17b7177217c5179e17791798177817cb1795,0xb6c015d008e11ba0b66177217c5,0x49218ff18ed09e2049b049909e0,0x5600033009f051f088e199d006809f9055e031703070080001306e7030a01d0004918e806f601d3192918ea0c230aac0e3f089406f003c20bf700fd00c3190611570e300bfd031c06ed0495049d1962,0x1a2f1a3006ef03ba004918ea089b01d501d2192718e813de01c8193e0003141d06f8164b0a0901ff1929194419011415058011710a0802ec193618fa191d18f00c7508b502030bfd053418151908190612770c710c01053819200f800f750f6f1a101a1c1962])))
(.node (.node (.leaf [0x3c1176c,0x203000300a401ff08b40079006b05e60468046517fa00220bfe047000f6180501fa002f02ec001202f6005b03b901c606e602e303030013030d01cf031b07a60e300302046f07ac08bc17a617b117a2178717cb17b0,0x6f03e3094c001b015e03ed104e00e900e70d990d1d035a00b300ad001702a30da30c64035b000e017500a4003a067302ab0b2002b0020401fe00410086000303b50fbd052f02a801f9001a00e0002f03c30a0301ff030300c30079001306f006e5030c00491885067900fd0b67066e0533008e0d9d0b68010f0f7001c601cf01d4031c06ed092f036908ae08b408bd157a1098147c104203760ff305eb11580a8c007f0a99046c0a940fc3152507a20b6b11ba015d152105de0088079e005b07b3014914ac07ae0b300b380159152e01a4188413db117008c6100400e318830833012812eb0d63137f18820e4101420f1614811873047104690022046e0464082301250cc30899183e136d0f1b0f180f0d082007ab00d40f1f169c0f80187e006b187d187900b00cae18330cb4179317a7177617a617b4178617ae17b017b1177117ba17b717a2179517ce1787179817d917c117c51772,0x9917c9,0x7d500d6005d0f3907d600df07da19210bfb0bf8014b1321190614c6015e0bff017f1522191d0faf0f4012320159187b01140108100509810baa07c806f319180072009300490cbd0cb40966096302c802c0186c18ff000f08c0057f049302b918fa18ed0464045517dc18ec06ec0d5c0c00126f,0x66b008e00410b65067a00fd0532115918f0191d030304700013184f01d018fa18e808b403b601d3190818ea05e505cc03b3031c031d19fb049d18ed0493049911bc193409ec18ff06af18f706ba06b709e013d919271a040d6508bb05380b6a0c7119200f0d19141a050f030f6e19f71962,0x950bc60bbe010a19160d1609b100ac18fe0f9906540652064e193f0040123f159a0bcb03940d1901ae01610019012a16850d13107a107103ac1318018800e700e8192115c21571138e132210500983039f05c705ab0164015e00720039139e139a15900c8509d608cf05b5038b1925193400a50075006c003813af0c2b093e0923091f091b08ca064905b8059a01b6009f006f1628067e06710669066305940fbd1939004100e011cb11c311bd067a152b15230fc500fd01590b640b37008e008807a3079f0a031974190112ed105707ad06cb011f00460cc20cbc096808d606cf12fb15930e350e39088e03b203b6147e157a15c01681193e141d16fe0a0b0fc30b6a06d301330f1313f613f1173601b914b01701169a0bf619060c0119200f0d088b1a82082b00620836015012300108122d149d192d14a91942141f19290e3f0e490f1819140f17192b0e42147f0315001301d018e801d318ea03c21a151a141a121a7d1a671a0f1a6519621a721a6d1a701a7f1a191a6f1a73])
(.leaf [0x1086176e,0x12b13ad139c01b6015e175e152201c4015915651520015d11cd11bb17bf1783177217c5,0x4906f006eb00c300b00e430cb0014200a714800cc8018a18c517e90f800f75031e00db0f70010f18c40f1d0f150f0c0f03184f18c30e31047001cf01d41833187318a317b7179817b6177817aa1771,0x1ab177b,0x115700fd19b7049d189018ed0f70049b191519c518f706ae049106b6046608b619b4,0x1590016119bc0991096300721352096b012300a8089c10900cd4006800e908970d980cce19150ffa0ff20cd019ae0f701918189008c108b618fa17110465194418ec134d109a089b117104711927191d0e3c0e31089300c3147d0e42192b15951481193b0cc80cb50967190a1a450300046d07aa08ba0f0c0f150f1d0f201a1c1a16,0x12f71ac3]))
(.node (.leaf [0x913176d,0xbf0abf0e04008200fb07121122004d00f204360df80df60b92002000be00920431073e071706a30046005000b2004302ef073b0b2a096f0699043b17e600b30088007207960da40b280aa30cb3096800620175008e008000a70e000ac3082e11c30b650aac076f00cb00fd0055078c07650b1a076d005900860ea4078f0498048a04300147002514a909e909d80964069e0492019c00760e4a0e360e2b077506b000c300440e3c06ba07ac1793177617b617b4179c17c6178f178b,0x8c0006b00e308ba0cb600d400a70f1e0cc8018a18a50f2101a4152e1003015918a31167117017a217ba179517b6177817d9,0x12c17c0,0x19a208f2124e00a8010b0ce00ed9016c00d2161d15fb0bdf04410ede017300960020013f11f10bdd113f0bdb0442098a043c010100f40072096611f0113d0993140511eb190a0161192b0cd20cb61593147f1918193b0a930e91133619a5007f0a9000ca0e990dbc018500b7165d12410dbd018601170c2e0c28009f159013ec0c291934166b16e316e20ff810f410ee01b619401922191b13ad13ab139e132b10e7192519a4067e05cc00410b6d031202aa02a3008e0013000e0533030502a918f019a31453145114500dfc013e0743073f073e00500da50d940ccd073b02b11911162515fe0da4193911cb11c311b511b111330e9b0c230b650aac067a00fd175617490b1a0b110a8d0a61076d02af01c701c3190418e8151a1511150e14e114d512c50b1c03b6035601d3193018ea089d0890081703bf031b0caf0d59031d08300ed20f710f7a15c116d4053707410b690d9e126a1279127c127f0bd505ec0a080a9a1162116502040c6e0c7319080c740c7018200f7519561136013313f31936116b14160f14191418d416920f0313f01929141d193e0f7f0d690f7419a01962,0x68089d0892193000c3150e19740185079e0e97008800ca0b38133d0e940a9101591922007f10030ff70a9305de05ee03c003c318ea03b3,0x141e1aa1])
(.leaf [0x5b07b202f6014900120f19030217c1,0x2c3000f004902b8030c00250013049b031f01cf01d402cc06ee02b4031a00b00cb000a718641515019c14830142147f0f1612fb018a186305800e371691117111590a9a00f604700e30046a0455184f08c808c1006b186108bb00d4185d0e48184c0f80185c18621833179c17b717b6179517a217cb177817c61798,0xa40c780c6c018700e81527133e03ac01590122001910040ff8038d038500e30038001d0ff2059203fd00e9004109420662059a006f18e5059808b008b608c108c817a617be17ba,0xe9054109420030006f05430934011200d5128f0f32017d018b16450ce101a300a814df0cda192e010d053e14db1253109f0083015501530ade0b0b0fab0100008500de0c120a890a810f680f4a14b40f2e009c190200da00d7014a125e0c0f044f0f650f4d0b010a240a11191f191618eb014000ce007a0f020ef50ef20eec04510f33140911d00eb010480a20191301a50137191e00e714110f001186117a11760a220e7e0a820b800b7a053f07eb10380ada09b2193a00f700c80091005e00ed18fe157d157411830b850d230d1d0865085f085c085607db0d340d3109a8015e190d0065190e139b0e870d24086203f302611925001c000913a3039803830258017a001914a401f4192d00030a0a020019011965090308fe08f9044d18fb0e0a0609060005f8020f1926003b11e80c140696069305f0025e0164004209d609cc09c9068903f70075162b0784042c01770058001f163110c110250b0303f113120785042d01a200ea18f6012000cf153b15a2159710c70c1b064005aa0591038e034113100eb7015a0161009d00380182010113381331132b07ec0be40be00bdd0bce059d14d80e9119220096014d00ca137c10d51042133f114105a40bd814d60a910a7b0a740128018700f400dd1930007f007d15611379145614540e9611390c210bd20b1c0b160b130a8c0a601933013e013b009f190411ba11b611b20c240b1a0aad00fd19640c0d009b0c0a0e790a6b04260423042000d900c7001e087708750873084d0849084403eb03e803e403e003ce03ca03c900660064001b0719070e07c107bd03db004d005d044204360b8a0b88084207c5002000920ee70ee00ecf04410d8d0d840ce408e806a0041703d200d200b2006c004316580b3a0b2d0b2a0991098d097b097709740970096a096008ea08ce069a0683039f1944008800721553117e152e15261522130712cc0b35088f05db05d505d101cb193201590068003a18e8136710b6100710050fff0ff90cd20a1d03bf03bb03b703b303af033d01d20de30dde0a641924191818ea00bb13b613240cc30cb40cb1096608d407a1079d03ba06d206c90433015f190a005b004615951587154012fd0cc902f702ef0f55193b00120108148011eb06b806b405f4042b03d6028202e30bad0ba7086807c7192b18f70013009314ab148313da1364109a06bb06f306c4030b02ca194219270049000f0e480e3b0e370e3307a606ee02cc031b06b606ec092e09bf0caf0d5c0d5f0d621962,0x513005e18ef07f007df02d8014c009400110f4f085a05140bb402e0061802de00d70065191318f3190910660f4c0b79085808f8060f0cab00e80140009118fb0043016a1450106f101d146c0f50117c0b7d098f097908ec069c0a44092608f1013e016100e4193d00f70072007b006f00a814591537101e15521180096710100a3b0943060705fe024701b8015a1932190a00e9003b00071640153511810b83105510060cd00cb40d0b03ed03de03cf03cc023f017a015e191b1918190c001b13a1139a10e70861133613320ff80d0607ed0362035a023d1925192200170d2405ed05d805ce035b190d003a0c730c6e0c6505e6092f0cb00d5a0a35035503b301ce18e801d218ea03c31962,0x4991a64]))))
set_option maxRecDepth 5000 in
private def hintsBasePart14 : Table := (.node (.node (.node (.leaf [0x173d176b,0x4d9005e002a07e507dd04da00c00065007a0dcd0e1708550211020d00ba01270091000403f503520dd112de0dd313750b790206001c001600f5011e019000d3000903a5039603820339020b11540fce16890f00025e0600020f0019016d00e101890042003b039b125f0ef51041103f0fc90a200cad0ca703f605c605b003de03cc0066010e00e700a600750039001b16c9086c0d340262093d0926091e05b703e101ae009600ae006f124d0bdf0783157615720b83094d1150010b0058015e015b104c070d0fd507821126154d0152004c014b008400f2018c03f211010acf0ac6070a0a430a2c07fd0b950cf70cf50cf005c4003f00ef0082007b005f009200a911200af4064410fb0d370ac40a2d0802034e0b8c0ce20c9b070b06421402070e00fb012c00cb00b900d200b200b10135004d1687161c124911a40e090e000dc20ac0087409760972096e068503a113fc071e0188017300bf0072013b1461145f13fe0e0b098a113911320e030dc8013f00f4145d113f1355134e13480807060b0cca016c012300a8160114c70ffc0cd20a1d04dc019e00e310a910a5109110890ff30cec0cd50a3b03ee092e09bf0a320ae40dc30e28115f116509660cb10cb417a917741777177017b517a817d117d517a017bc179117c017b817ba,0xef10f90d70012c00b1134a0cca012300a810900cd400e90ffb0ff30cd100e3037700170dbb0d6b036500b700610d990d960ccf081b00b300990da305340175002f0dbd0b2005300117008612bb0b1601b100f115d1111e016513b609eb09e509dd015f00760bad04920093111a17dc02c90156000f1514076d02c603550304019c0055001a00130e4a077503c3030a02c000c300490e41077a0823141e0e3f06f7127812690d9d0c00014201250138010f15871481136d0f7e0f760f730f700ba609e202b6018a00db00220f1e0f160f0d0f040ba20820046e00d416cf16901588141b0f7f13d8134b1098187a0191184201cf01d41873076f0cb40cc3031c06ed0d6a00b00cae183303690464006b187d187917bc17c017b817ba179317c9177617b017b4177d17d3178f17c417c6178617ae179817ce17ac1771177817aa17871795177917a217b7,0x7417a4,0xfc0bc511a70095014511450bbb148d00f500d5193f11521438114a0f2a15991933013c0161065a06501520143f0f311546114e00400159018b1931039209b9152d16a3154d001918fe01881947193c0f470d7c03a1094b0937091d0c95172916b216a800d619100072006f00a501af0d7b0f3909c1095f091e0fed074f10ab017300df00751917005100e9146214600fb209cf0a6e07480a3c013f00f0007d007b14670f450afc0af20a5d0a2a019a014b008415080fb406600fd409aa05070154012a00e100af002d106c10640fdc0fcc0d400984050d04ff00e8197412ee10580fd10797011f006212ea083316e016a0144101281940018e0ea116e516bb074504fc00cb194c0059003316f10ea613b113aa145b078f0d9b0d980bfc0bfa0311030901f5019f192501471911190600130003170c0d290d2414940da40534030301f80625066801b6190d193918f018f40041160e0d2605600b1f0a61052f14f40839061f03ff03fb0386016f009f1904015018f7001d175011bf0e9a0c220b1910ec10e710e410540d4205610412096306ae040b194800fd191b18ff17f215d115cc159211be10f40c2b09ec062a088f031719341924006813d81362110d109808991927150614c613dd12fa017f164f15ce14f60737073601a700500de70a6517491711164b152e169715940462045f00bb01c31944193b18ec175b0de8151c15190b1e0f210f1f046f01b5013319301914170416fe16fb16f6161a151415e015dc15d613f40c6e0c6b0c680c65073a02040f830f7d0f7b0f780f0409e1083101c7194219361869191518e8141f141a141713f10f7603b603ae01d3192918ea0e490e460e3f0e390e350e2a0ddb0ae60a34089403c200c31882197d197b08c208bd08b708ae036918fa184d117311701167116411580de10470031b06b6078a092e09bf0c7e0d590d6207400c000d9d126f127212751278192018d118d01978137e13de141b14951680169016cf16d21962,0x6af18ff18f70965061d007218f40967062706b709e019f7,0x6ef1a7b])
(.leaf [0x107e176e,0x12e13630d65012500b00cc30cae17cf17ce17b7,0xf16014200d414810f1f0f1d147f17981795,0x1911779,0x19010a0909f9192d0080122d0aa814aa0108191b19420ba709e4141f009318ff19900ba509e10d590d5c0e48,0x172143d128d013c01120e89122700c801070e7f1229128c00ce016b015514480a831437089f15f810f0013d19020145006901ae191b14cc073505150f9108a1124f10e6014c004f18ef1916010b012a15f4122a125b0734051e148b0f9710c20d71084f01ad191f193f00ea19100064144b16af144a025402510d34072e13e910bd0eb20d7a08a407be018f193c0008190e1928005d0f5e0426041e0cf60cee072a0255107810670d2d13e60ed807c300d9001e190b00e8018200d2008a0f5b09ba09b204221023101c0ce90984096d0b4a172c16b01685167c15c313110b8c0b47015418fe00e40072009601af018801640120009211111110064c08490c7c09c508e108ce059d03d903c7024e01dd1583156f156b138c130c0b9c00f0004000dd00a50075006c0038001b18e9015e10ad108e10110ced0b2e0b2b0395094a093b09240920091c08cb059b03e302a401de139e139a13040e8600e900880019006f000e19250d9b0d98152c152413090b3703f903841654066a0664059502ad13a319110159001d01860041017a0da415601521040e0c2c0c1f0bd0067012ed105704040b6d0b611939193300cb009f011f18d818d611c411ba0e9c0c2410b307ae079b00fd00f119750b190b1602ae02f501f5190400120003052f052602ec02a801f901fb05ca05d205d805dc0e2b0e360e3a01e503ad03af03b51099110e19270e3d01c818e801d218ea03c30c6e132c19220c7305ed1a1d1a1a1a181a151a141a1219621a1c,0x14f51abd]))
(.node (.leaf [0x581176d,0x8b500a4006b0c6f0464010f00220f0e08bc046f00d40f6f0f0417a617a2177117871795,0x6f0599092000380075059e09c4009600d90be70ed10f5e018200d2018f131005a909420b8c16be13c20bdd0960012000e9009201ae012c01010072130e10a60b9d15a613b911ef0992015e01611653139a130418980186012b16301337166c13af0177012201b61632133e0e91175e01b5018700ca01c416ee1453165e0e9810b3164210e80198013e018500f1017a00ee14ea13b7166314571511150e111914ee10ec014f015f01b80156015016ff16fc12a30bad07c7171a170f151814f7019c0114009301a71734170112aa0bb3156615631560155c01b9017f015d12ff12f912f5011f189d171616560fbd01a400e0152f15271523130812cd0fc5015918990b3a0b2d0b2a05de0088079e0b6e0b620b2601f701f3005b008e000314b014a3149d07b30532052601f90149002f0a090a03052b01ff17c017bf17be178317bb17c417c6177217c517d917c117b0,0xfe17cc,0x4a718ee190304aa0aba06fb1916191e004a0f87069506fe191f004200c40d3311d306860e52190e01630075012909b109a804a405f115bb0cef0e510921130218fe003b0190190b1923006f01200d5209aa06021575156703cd0cf20ca8092606fc0cdb09af00af00a5015e001b1921190900a800b610610d410d2f0c86139b02a30fe60fe30c9e10930ceb0cd403ed0dba00e81925000e191700e9013216cb10540db40d4213a1066802ab0c370c340d990ccf0ea21948191b017a004100a0191100cb1559138112ca0fdf15d113ee10f414ef0d2506750c380da3078c02a81933011b19340150190d01061939005918f015251521130a12cf15ce14f60d2612210b2007880530015901a7016f016e190410040ff30cd1152e11c611bf0e9a06790a9e0a8c1918194400fd007f1880117011580a99191d199d01df05f603d818e918f701e006b118d60012009307a2122e02f002c8160b005b01080046000f01b512c8105807ae06f306c402c1175c011f0049194f12f9030e030a03030de306d1176a017f001300bb01c3198a03170de8046c151b151814ad14a6122d0c6d0c670c640c300de6076d076a02c60068013318ec1930192d19081924005513db13d813d4109808991479077a08c608c208b708b108ae0464170416fb151414a90e4815e115d70c760a0d0cc30cc00cb4076f06cd02fd1927192b18fa19421936190a16d216cf157913de0f180f160f0a0ba208bb046e0301141e1419141613f0169c13f8136d0cc9193e1914192918da0f840f810f7e0f7c0f050ba617e81915199c01d901d118e803c403bf03b903b703b501e501d218ea0e4a0e470e430e400e3d0e3a0e360e320e2b0ddc089507a9077506f103c302cf031b06b606ec078a092e09bf0c7e0caf0d550d590d5c0d690b680c000c6f0d9d121412751278127b192018d118d019781962,0x193415cd13da01a71927151911c711bd13de193000fd193e151419800f830f8019421915141f141d031f19290013150f06f6030b018500490e490e350c0506e600c31906190111570e300bfd0a0703c301d001d518e801d30c00127e19de0f0c1a1c1a0f1a101962,0xe4a1a95])
(.leaf [0x49717dc0086000f076e02c717b4,0x2f053502eb00990012052c05e101e00079003a00020a0903b301e50149001a07b303ba005b07ae02f401e9011f00550cc10770077a00a70142183e1481136d12fd0cc9077207a60e370e3b046905eb0bfe00f604710e3017b017c917b1178517c1178617ae17b6179817cb,0xd00eba0ec200d9014b08780c09109c09320066009b00e9006f086f084510a3059a00960064015e00380c0d050805030873130d05a90163002d00bf012013eb1390050603a20fe20131012a0084001900e2139c139903851065105d0fdd0af003ac0c36012b001d00e800a0067d059203fd0c6c0c2f004100a40b620b5e0b5c066c020301f6008e00030531052801f8059808b008b308b617b917bf17a6,0x195c18ff0f80195d03050013030c0049188c06f81929141c193e13df19270d6406eb031a190f195b01cf01d4183318c6049909e00f740f7f195502cd0e3c1959,0x192b0f161481191418da0f05191519dd18d00e3e0e41,0x12880154011011120f9d00f000dd108b0c8a04be00e900a500270942092304b6006f1a5d139c09a1192518fd1729067d09a4040819470041191b001d1531066c1045074704b40ab309e4040d0159008e01280059008018ff15200b6b0ea0078d0c2d0c2004940491193300cb009f18ed11bb0e9d0c25049e05cd03ad03b50f060f0f049a09e10b900f72030f0b6a126b127419200f6f0f0c1a5b06e90049030b0013031e01d101d618e801d218ea03b41a581a151a121a181a1b1a111a1019621a0f])))
(.node (.node (.leaf [0x906176c,0x19c14831514014201560e490e4214e300c3014f08931001006800e30f7d08970cb400db00a70f7002ff010f0012053702ec002f180d01ff08c108b60079006b14eb0468046501a400221171116b047117c6179817c417ba17aa17b6177117b017b117a217d91787,0x6610041006f066c0942008e00e907a20d8108cb005b00b2006c07a9097008ce03b500c30072001a07b206f0109805db05d505cd03b401490049012e17fa05330a0906e406ba002f00790044052e0a0d09d8096406af0086016800760b1d12760b69053704910156010f00250f7e0f7009e2049b01c601d4187308d409660cb106b706ed092f0d6500b00cae18330ff30bfe0e31116a07aa0f0c0456046800220466117114ad14e10a8e007f0a9b014f14ed01a4152e01591167100408c8117010010f1a184f04700a990a9400e308c1188d0cb4178617ae17c117cf17b017b1178b17b41773178f17c41771179c17ba17d9178717b7,0xae17a8,0xdd0fa509390152006f104c0940,0x2891a0d,0xda0b7b0f69009101900b7e166f00fa0187119c1527192a015914241003193a1918168c03761946001717250222194a0006170902330df1019e007c00bd16ed0df00a5607300725019800f3004f0de90a5107330b420b3d044800bb00e4191f008918eb0a6410150efc0ef70eeb0b4104a00446007d00ea191318ee151f0440058a0582022b10bc0f850eec04aa0158002018f219281916074808ac04390389170813e409b104a4005118f9001901a0193518fe04b10349033a110a110909b600270016191c04bd08f8044c034b10f9008218fb192614fd11e20acc061208f3087c015200ff18f300a800661500132a0df3118a061b0d6f0ccb07f2151e01a9192100f81910005f01a2166813e90f99131d112d101e0b4313d1118c0986097a096c043b08a9080606171143113a0a7704430186193f015a012d0101007200d2008a00f4165e15a2159a153913c813b911ef09920b8c0b47113815c20b49086d07fc018501610092013b016400960e970e910e8f159013ca1581157815741322119d0b9d0b850fa90fa404be0ec1074e09d609c3096205a2059d038b033f00ca1934015e00dd00d000a5007500380e950ac40c2e0c2b0c210bd2163013a5139e139a094d093a09310923091f091b059a013e00cb009f01771925006f11bd11b511b111330e9b0c230b3a0b370b2d0b2a082e067e06690663059400fd0088006200410ccd162411c40b5d0b250829066b191119ae008e0d000cfd0cf90ebe07a303b6033e0227190c0108005b18ea1340133713331330132d0e940d0714a314a0122d07b301f7089007f801d21922192d19ff006818e808c108b908b005980580036b0743073f163213430a0909fa01ff0319031501d118fa005001b51901001304640461045e045815df0532052c0529030418ec193618f0117411681162115c11590de20b310a0804710c780c750c7207390c030bf50534191d1908190605eb05e705e405e205dd05d905cb035c01fc003a1a8d13f913f21136013316fc16f916ea11de13f11942014719291483147811ec119315c0157a1496141c18d4185a0f180f130f070bd40b4d08bb07ab046e1914128012770f0e0d9f0c710c010b6a0742053819201a8c1a8013f6153e159318be1a8407a608920dd90e280e330e4800c31a891a6c1a6a1a151a141a121a671a191a7f1a6819621a651a0f1a711a701a6d1a6f1a7e])
(.leaf [0x1369176f,0x11bb015d00fd152011c40159017515220da4015e00b3139b0da0012b0fc710e9094f00e000ee006f15790fc10d58092d0191014900b00f8114ab06ed00db019c0049181e16fc12780f6e0d9d0a0a0a0406e5046801b5010f007915e112770a0d1343132b01ff0168012200030c750c720c70020300a408bd08b408ae01c601d4183306ee0e330e48184c01fe05e605ef11581167116a117300f605ec0e30177217c51776179317bf17bb177917c117b717aa17c6177117b1177317be17a617cb,0xb200175008611c40b1a177617b4,0x1c41783,0xa0d1869199d192019b718d008b6,0x18ed02b9045517e0184d046518fa07ac185919140f800f04049a19150898006803170013030c02c2004906f6197f0e3707a6077200c303c203bf03b918ea01d601d318e8030501c719ff000301ff19010a0c0204088b193618691906116b0bff0a0819b7191d1a4d01fc05e205eb003a1a4a1a3119de1275192018d118d01a161a0f1a101962,0x193b1aab1acc]))
(.node (.leaf [0x3c6176e,0x81000c400600e52080e0129006713020882012000da0cdb0b7400a800900cd407b500e9005c100e0f6507b400e401400063101b146d083f014c018d015114cf155112ab04c3019b015c0115002816e81180088812ac04c6019700f701550172010315e3118512ad128b0b75143b14131409117902dc02d70c460608120f016901b001120111013c0137001100a1003b0105161015e2140e174b14fa0f270f2507b614370e570ef90ef102e2090208ef05f815e4155512110170016d01be00d50145014300d3006d01ac12631260120c11f80ef6176717391730143f0f310f900f8d0f220eec083c08fc172916181291010e01c401ae018b00dc00e501af0d380d3309b909b11764175f161e0cf50cf00c4116d9169f148d14870f99154a102c10c3102615ef00ae007401b901b6017300a90192015b00ea016a10e310da0d320d4609aa170116fe161a12a00ce515a515991596154710c60a4600ed00af019c011300b40161007b10d510791076106810530d400d2e0fee0fed04c51516129a16da0da90be00ce30d7c0d770afc0a2a012800e800e2015601930110009600b200b1008412fe12eb10580c36111910b2145115c90fa70f9f0f9b0bd70caa0c9a02dd098f097d0972096e096b08ec113d0751074b011f00a000f1013e016500dd00a6007200f4005112fa12170c3810ca10280e9610f310ef0d42142f0fa20c930c890c870c830c80060209ca08e208d208cf05a905a5059f04be04af017f010600eb00ca00ee013b00a50075006c00380027164c12200a960a90130610e911cb11b511b11133094b094709440937092809250921091d08cc059c04b8040701a4016e007f012b00fd006f001d116f116c0a980d0c0d050d010cfe067d067906670661059203fd00f600aa004105eb05e705e005d305cb17d617c317d217751774179917a9178d177c17701783179617a817a41791177a17d117c6179417b917c417b817d317b5179717ca17bb17d917bf17cb1792,0x3460016005f03490805006a00d2034c043a0ed5006d00200104097408ea044204d7007200f40029080a096e113e08aa04d3012300b1016c00e21139109009c10cd80ccb0a7c0a6e043f013b00e9007500a8007d0e79094609430920060d05f802460245024200c7006f003b000703e503e103cb023e001b05f403d617a1178d17b817b9,0x14e17c2,0xda219391911127a0d9f,0x46418fa18ec08bb046e19140f05191508970068031717e9004906f6197f00c31a2d150f01851667194f175c117301b51343192215e00c03088b05340c73193619061869127e12750c00192019b719de18d118d003c003c301d001d518e801d319d01a101962,0x17041aa9])
(.leaf [0x7b800d5005c07b909340f2e07bb0120006f014a0f2305aa059c0fff14b100dc003800e301530eee034010a10ff3125c0f8500d3001600e9010e08f7034a0cf00ced0d34006d00a900ae05f80f000cf110de0d32003b0189012100ed060c153d131f104810390123015a00e7080a0fd815720ac6005f00e1015e0082105b10520d2d07f30338135711e00acd00e800660015018800ff03a9039a038b0339032b146111d902730019013f000a038502690fb208040d7f0ce208e8026e001d00df00d200b2006c004310d5104202790bfb09810976097208ec08d0069c05fd0128000b009900720637027f05e205d905d305cf003e003a152a152213070fbe057a038a03310363035f035b09d80964069e040c015900e000370017007608c608bd08ae0596057e03690493006b002504650456002217ed155e138212e41152015d12f510590fd2011f165114c612fa13b513230fae017f015f01140bb20bae0bab086a07c90586009302c8000f17eb089d07f80548006803c503c003b803b603b203ae0356033e0278021901c9028a0633092e0d6202c30316046f08bc0ba302cd08930a330ae50e340e380e451419141e147a147d07410d9e12031215126a12701273049909e00b8f0ba40c160ed20f710f7a0f8213f9153e15851593169602a904e00527052a053005351380157b158a15c116821098110d134b13d813db11de145b0147149714770f77062b08d409660cb10cb40cbd0cc00cc503710dea076b077902e901de01e3000201e101e90055076f00a70cc40caf0773077b079a066c0fc2149c149f09fa0a0301ee01f201f601fd000301ff01c601fa05ec1159115c11651168116e11740b2a0b2d0b3700880b31079e0b26008e07a20b690533002f0537030315d515df073a0c650c6b0c6e0c7300a40c740168116b00f60a0700790a0a014907b1005b02f7001202ee004606d100bb0de701251362012e13df01910f7f00db0f750e3c136c018a148001420f170dda0de806d317e413f00f1f06c602e30013030d01cf031b030207a707ac0f1906e60e311416013806f80c7017e50e410d690e3e0f05179617ba17a91770178d179117a8177717bd17c9179f179e178f17a2179c1787177217c517a617ac177317cb17b117c11778179817ce17cf177917aa17b017b61785,0x2b8000f002502c304930049007606f709e0013800db17e8179c178f17ac17aa,0x261788,0x193c16b20f4801af00d616da16aa08db17490193006c01c3159f08ce170401610072194217271335096608d414aa19471922190a192d100d0ff90cb60f4014ad19180114194412a2100007771711014f005501a7151c14e312a70a9d076a05ee05da05d415ce15c815911930007f003a19340b1c0a8c076c01fe10f319040003191b052f01f902020bf805e109e4096518f01908190618ff0a09052b01ff0c710c0104911901192018ed0a0c0f7d0f6f049a1936191514170f761929196d1483077c192b1697169415941480193b196c196b1562193311c911be11bb0e360b1b0caf0d590f0c0f150f1a0f1d0f2004570469046c18ec046d05eb0a990bfe0e31116a13de141b16d2,0xa0276021600af00050d3f0217021d00e8001618f30fdb0353092903cf1917006f001b0c9e092003cb034319090075003b00390c9a09c1060f026f05f105b01910004300420985096e069c0685068005bb0072007009670951190a19ed0c370c3400a00c3801061221016e160901b51660111810b3018500f1150e1119193019ec0958015f0bad009303770362035a023d0c6d0c670c3002c900171908000f05d805ce035b15e10c7601f501ed04b202c0003a19360003005900490c0505e30a0c02000310030c023a190619010013000e0534052b030302a701f818f019ea023018f4136510b6062a1924136210981927089a0317031c06ed078b092f095509c00cb00d6502cf0218033d035503b103b303b701c818e801d20ba60f7e0ba20f070f0a0c6f12141275127e136d15871695147905eb115b1173036908ae08b108b718fa19b7045a040b069d096309e502b803d705f5061e18f706ae06b7158906f6078f11de014714961476192b0f160f7913f20a640dde00bb0de10de8013313ef1929141c19e213f818d40e430f130ddc073607370050046018ec04700740048c02b005300a620b0f0b1816070ccf0d9902ab06680d6b00b70dbd01170c27009f067000410678067903b50c220c2b193411bc09eb0f7312690d9619110da319390b2019040b1900fd1158191d19e519e408bb046e19140f050c0018ea03c30e320e36049d049718ed0491049b12780d9d192018d00f70191519e10e4019e00d6a09dd1962,0xf6b1a64]))))
set_option maxRecDepth 5000 in
private def hintsBasePart1 : Table := (.node (.node (.node (.leaf [0x1281176b,0x678004100b306790d9700fd00e911ba0a3b015d007b12f60a2c011f008410590aef1793177217c5,0x2bb003718680589077c00a701421860147f12fb018a185e00220f180f1607ab046e030100d4185d16911859187008b4057e046401c61833077207a608920e300e370e48184c041309a409e310e81867186b179e17b61798177817871795,0x36179d,0x5502c6077217e100c30e49194215140765193000590b1e078819041970052f18f00a07052b078f190101470a0c0f7d0f780f6f1936191514170f761929196d14831478077c192b148012fc193b196c196f078a0f0c0f150f1a0f1d0f2002b60469046c18ec046d0e31116a,0x197507ad02f6011f0012188002fc19180061037503650e3a03b90816006803bf18ea03c30895,0xf771a64])
(.leaf [0xa06176e,0x1561519111901a700f111c60b1700fd008615ce111d11c50b200165017510f30da3049c00ee00b3002509ec09e709e409dc049317c417b417d3177617bb1793179c,0x165301860182166c13e701b6124b012f170b010b10bc019f0c4f00ea0d7914f300a20d0000b101500c4e00aa10b20d6b0989096e14f600e7090700f100b7007201a71043006e09e509dd09631518111a0128036d00760156137f00170492151417e80ea8035617dc019c013800cb001a000f0e490e3f0e2a03c202ce17d017b81792178e178f17c417c617ac178617ae,0x15b17d1,0x530195d190418ff0497049218ed19b00b19049909e019a00471,0x6f8192900490e3e06ef1a2f1a300f8019150f70192002ec1416127618f01936180d0c7402021908052b01ff08b60580190118fa164b14ac04680465194418ec0f200f1d0f150f0c08ba07aa046d03001a2e1a2c11741171116b0bff0a0804711a2b01d518e803c303c003ba01d318ea05ee05e503b31a101962,0x19141a6d1aaf]))
(.node (.leaf [0x996176c,0x1560b1c089e008617e70f7d052f00db002f049b0498180d002501ff08b602b70079006b000f04680465045602b50022116b047117c417b417aa17b0179c17b117a21787,0xfc100e001490fc50a0414ad01590079187b11660a0700f6116b0a0d1869010f0f180f0d00d4189017c117b117cb17711795,0xb31793,0x10a123c1237016b0115146a12ac0140017212ad0a5c0e18128d01b0007c00c001120ab6174b0a4d123a0dce16181291190301be00c4014a00ba01af128a072505171767138a0e520e55140911fa079016a70118004f18ef194e0129192a01370103005a018b12570733051d0db90260025d175f13020efc0ef90ef1079316d9169f191f00b6000901b601201913193f16ba0d330d2a072d026113af1306142414100eff0d7c018e190e1925193a1910166e0dd4079410e30d320d290d24168c11fe0ce10cdb0cca0c46035003450187011e00ed190d194600a800a100160dab16731047103e10380d1b16830fff090208f808f208ef034b191201aa00e70188191818fb0cf00ce70c41072c15ec0ac713570ffb05f7190b016a00820123003b10ab0ceb0cd414000abf080a03cd00e9013500bf005f001b120a0a460a3c142f13fc0da9087407f403c80104007b013b01100066001e12060a2a0fbe11390fa10f9b0871041c014b008400e000f400dd009d00640e0112880af90fda0fd40fce0a3605070fb81142163a16da0bd60bce1542153d0b8b0843027300cb015400e1002d191901a2017a01930096015a0092000a078c10d51042106c1060105c10530fcc0d2e0a54050d1566155e138212e410351631162d175915a1159d159915961351113b0be10ee70ee30ed508040d800ce308e708e506a00417039a0339026402570059012800e81933017701b5016100d200b2006c00430019076712eb10580fd10b6b0b390b2c0b291343133e1338133513310e14098f09760972096e096b08ec08d0069c03a10aa60055011f008e008819220072008014a514a20fc20cc50cba0cb10c3c096608d4076f07ad07a2079e079a04ff05ee05de05da05d405d00386026a055c055804fc192d190a1808003a150614c612fa001d00330a090a030a0009fa0cc40375035f035706c601fc01f501ed017f10e710540db40aa804120c200bd10560190119240017004917f9198a191b009f15e00a0c0c790c730c6e0c6b0c650de60370036702fb030a030602e315cf15c9159210f40c2b1936186900bb0061001319341174116b115f0de20b31088f081607f7031713db13d81362134b1098191d006817e70bfd0bf5088b081905e10534190605350533052d052a05210305031b06ec078a0caf0d550d590d5f0d600d620d670d690b680c000c6f1202126f12721275127b08970b900c170ed30f8308210bd50f080f110f190f2106f619290f75,0x7891a0d,0x5540032008505110b0b18ef0155025c055712bc00090116011802060f8a12b31255051d0db9000419161948191f00b6020e0f9910c40b0617310d330d2a02610208003b193f00ea01ae190e001615a603ce0cf009b116d712bf0a7315c216c00c56033b0161001b190b18fe1949007d0164018f19070019133702a3110c0ce809ac0c7b06040214033f17520a791115167c0c5e0f5d039d1922000e191c00e400af00a50038194d014d00f00188010c00d90066133c0a6202b0108910100cec09d6092a0923091b059a03e2087316f5150a14d311130ee60ee20edc0ed1071408680185190400e90075006f00bf019a015400d2004d0093150e14d50b1c0d9a0d9702b106690663059416f114660e0c1072106e106a0d3e03a90d870d850d8208e303d40441043f043402cb193019110041019f013f00e800b2006c00430020000f110f109a15190da3067a0ea80e01098a098709830970096008ce069a05fb043c0489042f02b81927198a1a8700fd00cb007218ed150413dc1562155f11ba0e9f152b09d90965069f0493017f19330128015918ff12fa12f612ec105a10030ff206c9043310f010550db50d430b0809e305550388011f19180046186418600cc10cb50cb2096708d506ce190a1a90173412340f5401b9010814b0122d192d10b510180a090a0019241901082e0824052f052c052902a80062006118f00b61082902f902eb008e00120b370b2d0b27031502e60088001307a3079f02f601d001ca005b18e803ba03b6033e01d312fb136c1593169a02cc07a60e280e330e4405ca05ce05d205d805dc05ed046a0a080a9a0b311159116511681171081a0c0419060bff191d04701a8f1a8005e11a8e059808b008b908c1137f15c0168116d0030107ab08200ba20f18147e05380b6a0d9f1274128019200f0d06d301330f1313f608c4145b1498014714781496185b0e37151516f717021942148318d4191408bc18be1a840e4800c31a891a171a151a6e1a141a121a6c1a6b1a7c1a1c1a661a1b1a691a7d1a751a161a191a7f1a671a651a0f19621a7e1a6d1a711a6f])
(.leaf [0x1549176f,0x1678018701ae166e1077018e00e816bc15b11736105801c0016201b9011f174f173115b4176212fd01b101c4018a16d01565155712f51056147f1850015d11bb00fd11c4017516430da4017a00b313b013a913a20da0012b10f810f210e900ee014214ae14a40d580f1e0f16014900b000d4170314ab148306ed046f019c0049002216fc127b12780d9d0a0a06e5046801b5010f007915e112770a0d1343133e132b01ff0168012200030c780c750c720c700c6d020300a408b4006b184f184d1173116a1158047000f605ef05ec05e601fe01c601d4183306ee0e300e330e370e48184c1781177d17831778177217c51776179317bf17bb179817c117b7179517c61787177117b1177317be17a617a217cb,0xf0400db00d40f700f0e17aa1795,0x18ee04ae04ab191e19160f9911d209b004a3193f016318fe138813851390064e0129012a00401599130210e50d760393069401610120191b191000190042159010711065105d1056096d068403a005af05ab193400e80072003915ce13090c8409c308ce05b405a7038b01a7015900a50075006c003817110b3609240920091c08cb064a05b9059b19440088006f11710b3106680662059301f7191d0041000305ea05dc05d805d205ca01fb003a195001c601d718c6059808b008b908c8,0x7c2005d006607d2052900d618f00bfa052d1906199d0bfd,0x58518f20093057f02c818fa000f046402b41a500589190a0cc802cf08b6186902c2004906f61929141619360a0d19e518ea03c305e2191d0e3205eb12750e4006f10ba50ba319140f041a161a10,0x12f31acf])))
(.node (.node (.leaf [0x1740176b,0x14f100012a400e3011408c00ba9006b0093057e02ca0037000f058d077702c5011f00550cc20cbf0cb60771058902cc07720e3708bc0ba30f1c17ba17a2179e,0x171901b801a71664171811c7018501a400fd133b14ec0b660122014f008e0c720825053100a40061002f0c760c05081b053514f70168009901501282127e1275088c0837082a010f006800620f7c0f700898083217d917be17a617b0177317c91771,0x7917b1,0x7d61921005d132107c1015e00661536131f086c015a0096086907c815380be10bd100930161009f0ba715920c2b01081934123511bd017f00fd164e15cd11c601a717121944152e1522,0xf47193c00d616b40f45194a014b170a1250019e010c14360edc08db013b00d2006c1139132a0b8c08e20cf700f41921009200e4190b113c13220b9d10a8109c100f0ceb071d0161015e00e9004d15371534101e0a3c07110d860ce306a2015a007b00b2004311950a3f0a7509d9069f00f8007d18ff0e7c0e760e710a6a07190492048900c718ed0b0f0a62049819040a8c007f0ff3076d076a191800550cb40cb1076f09e00b8f0ed20f6b157a109807730a330a9a1271046a077c119308c118fa046408bb153e1593101a1924136c1362113613f20a640dde00bb0de8013313f6193b148116910f1313f119290f740de20dda05ce05d20bf9190605e10bff0736005007390742045e18ec046e188c02cd06ed04991333133719220c721908020219ff01fb053801c818e819fc06ef0a080c7105ed069a08ce09700ede0e73118911df00ff11da013f098a1a001165145b115c191d0e3119fb11de01471478192b0f1619140f0e0f030e41188708990e3b141c0f771496193e0f7f19f70d6a1962,0xfe91917014d12970fdd080c011300e8005f0f3c098307fc00d6007200960f9e0c850c8108db08d0059d00dd00a5006c00380c210bd2093a092308ca059a05d805d20f3e009f006f003a01140671066305cc0594077900410055066b02f1008e001212a307a302f604e5014f1974002b082b100004ec105707ad121c121804ef04e80062191818630106007f083608c108b908b005980580121e0a9e0676015018fa016e19111230046a046416070da30828010818ec19390061149d122d031502e6116e0a9a0471147c1479077a0cbe0cb5096708d50bf90bf6081a05e2192d0013191d192b190a190614a901d018bc14810cc9127a12160d9f0c010b6a194218e8193b1920141f088e088b081507f603b603b401d30f1e0f1b0f180f0d0f0a0f070bd408bb0820046e03011929006818ea19140e490e420e3f0894077403c21a76188200c31a801a151a121a671a161a721a191a7f1a651a0f1a6419621a6f1a701a681a6d1a7e])
(.leaf [0x1081176e,0x16c801ae019015a515760d510161015e00af1336094f092c0122006f13390662092d0177004100b0162b173316cc067106ed017a01b1009f004917340dfe12ba088f030c01b900be01170068001314af14a20aa2163212b5089d02e30149008001b5016f01560012149b0aaf175a160f15900c290dfc0b1c02f4015001b60165013e0086005514f2162713ad13a1139a132b067d11be11b70c250b1b0aae02c5019f0175012b00fd000f14980da40da10678049d049702b8014700b3002509eb09e809da0491007610f510ed10e80d430aa909e318400743073e00500460002208af0465006b058002bc003712fe058c011f0cc1058802fe00a7183e170016f814ab1173116111580c660738019c00f600a41482077b15e115d7116b0c7601420168169c15951481136d12fd0cc914181415018a013816d01691157a1496141c183d127c12791276126a0d9e0c700741010f0f7e0f7c0f790f760f730f7009e20898049b031f00db01cf01d4183302cc06ee077208920e300e330e370e3b0e480300046d08ba0f030f0c0f150f1d17be17b7177d17c117c417d317b4177617bf1793179c178f178717a2179e17b617c617cb17a617981773177817ac177117aa,0x30a0049001317e90304002f18c00535009905e1003a035d0017037500e310050159153201ac152e12260a9401a40106007f14ad121e0a9e0149016e14a903b403561607019c001a01750e4906f003c21278121400c3010f1483147e147b0e430f70031f046c014200db00220f180f160f0d0f0a0f04046e00d418bf01cf01d41833187305eb0a990bfe0e311167116d1170147f16960369006b184d0f1d18bd047017b017c917ba177c17d917c117c6178617ae17761771179817aa1787179517a2,0x19517d8,0x1102d902e018ef191302500f010008051d193a024a191f168c000d0cee025502dd19460298190b1909120808f8001e0cf70ca4010418fb0d35153b029c041c193c011316b112060ff008fb190e015a004000640f470f3a01af014b19170d300fd803950b99084200d6055a10aa109b0c8000ed00e1001900920ce3065702a209cc08e908db08d3041701dc003300e900a510530fdc0fcc0d2e03ab01f40ed50b8c174910d500b20075006c004318e9030709420923064900e8000300d201c301280f400ff309740970096008ea08ce069a039f01e70013006f0c6c0c6902020b2e0b2b16d2137e011419180072005503150667066119080088193e0cbd0cb40cb1096608d4076f0062004105e505de05da05d405d001cd01c713df109a0671190a082a066c003a18e81927009f172912ec105a0fd30cc2008e170414c412a803b403b001e601d30899088e03161947011f07ad07a2079a07961942017f18ea0068153112f20b3619740e490e46077403c20bf9088c05e20201015900c31906190111660e300bfd0b2f0a0705ea031b092e09bf0c7e0caf0d620d6908b008b608b908c108c819b41962,0x51a008d18ef0b58051b051d00f51905191f11490bf20d35191e190e11d20cee0694068f068d0c7b0163190b004200a5156811070cea05c505bf05af0925015e191c00e40039006f139a0d8208e105b4108910100cec0943192500b2006c05bd00e910e8097208d0068500700da10d99191b00720958155911510b5a191110f409d70963015f19330da3193418ff0bad15251521193911bc04920093187f0b2000fd17dc02c91901190418ce000f06e502c2076c02c40b1d00490055193006f6077a0f7e09e21929192b19e419151589157a141c10180f180f160ba2046e19e1193e1924191416921587136d0f1f0ff20587193b191818f20cc80cb50cb20967095108d507700588190a1a4005d205d80d9d127811581170057e08ae08b702cf06f107750e360e400e4303b103b71099136313d913de037700170355036918fa184d0470191d0bff19b705ea035b089c0068089a19270e3d03bf18ea03c3088d19060c00192018d118d005e11a151a121a131a181a101a161a1c,0x16501abf]))
(.node (.leaf [0x8a6176d,0x15d4016701b411fc1156010300f511f8114e0c620c5c010e015b132900a30cf015d3154e11fd01210c5a00a901ab0dc000e70d330ce305c605c205c112090ff00fed00b80ac600ae00b20039010400e20dbf00820d32065505ab04d504d200bf04bb00ed004000290e00002709ca064d07cb04cd00cb045900750074005d175710d50e9e17dc120709400921091d05ba04b807c2027201c40128000f014b006f0066000a1764138004b202c613190d8d0fd409aa092a03a3039b0393026504c801b9019100590055012a00e100af0019002d086807c70fbb170114c5141b0786076c106410530fdc0fcc0d400d2e050d03ab04fc009300e0019c017f0138008600e80033164e0ba80fb80e4a0e470e40049802b912fe12ee10580fd110e410540d42056109d701a7010800e600c30025011f00ee007614f8123110330e34049c12f404140410040d03fc0387026b015000fd0159001d14ee156512f511ba115110340b370667066103fd017a015d0088004114af14aa14a50fc20b700b6c0b670b28066e08370834082d04020149008e006207b107ad07a2079604ff01e9005b000202f602f201e0177017d117a517bd1791177b17a817b917a41783177917c617ac17b417ab179c17bb178f177217c517c11785,0x1130b9a12940092011a0b9212c600f201b30b96129c112b161f11170a3d0d7500ff016a017300f0007b00b106a611970afd0af30a2c096d0d6e004300f80084007200ef06ab118d0af710af098711021100012d010100ea0152013215ed13c611ed10c5124a12460ea201aa0161010b00cb171c15a6124e082f01ae00621734171d079601b9005b14b014a0124507b3014918a0170210b3019c00f1151412c512981119015616e3150f0194018516e416620e910e8f01b800ca1458145114500e95013e167a16761672145217b817bc17c117c617c417d7,0x12117bd,0x13e51928018206c213e90be618f8193f009606c115990bce01010161009d0af7113d0c19059e0c1b008400f4011a003801640af41311113f0d7406c0059c139e00fb0120016c1910006f192511f1111f130c094d0ce00cca05a20a2c03e1132c017300f2015e00a8007b001b192215c612c6169e131315e8112b0a4410a50cd50a3b03ee134301b3018b016a00e901b5174616a515ee10aa160b01af016e172716a314791947192b169715941480,0x192b0e42147f00c3193b0e480f1f0f171942191414aa0f180cc8187f190a10050cb61a16,0x19291a701a9b])
(.leaf [0xf02cc17dc00c3049a0e3100db00f60f700471010f00220f0c0f03046d17aa17cb17711787,0x58d011f00370cc2058900a71860185f12fb018a185e0022057e046418330e37185116910301046e07ab0f160f1800d4185d185c0e48184c179e17b6177817871795,0xf9d011000dd12880c8a0bd6015400a5009614be0c900be3014b01230161109b108f159100e901650ffb0ff315ca00e3019413350ff713ac0122012b0d06067d00aa00410da50d970cf8067600b318e0121b0c3805ef05e90106003a0b3303b303550088001a07a1079d050203ba08b908c117d317ba17d717be17bf17921793178617ae,0x7fe0096005f0be4059e0545018200380031131005a9054d01200092130b0b9b1653015e0186139c1306165e192501851513166904e404e207f60547067d059214e4193001b6002b00680041014f1515163c02e7170b0b2a03bf03b510cb1942017a0012019f008818ea191a14a914a402ee14f40b6e07a103ba03fe0a9704e9192d00460150008e005b001d007f165814ed152313080b360c040a0b06cc0836082907960401076a04df187b0159190619010062005518f015200b6b11660bfd0b2f0a07082e0b1c0a8c076c052e1933191d00cb190411cd11bb11590e9d0b1b067c18c6083008960b8f0f7a077307a70e29059808c8046a184f030107ab0bd40f180f1b077c148305380b6a0c01127d128019200f0d0f6e06d3013313f6193b0f1e0f1308c4089b040d157a049718ed04930499041310e810ed10f5191b09e418ff195c0f0409e00d580ea4149801471496147818d4191408bc195e0f03195a0f7706c506e502e603150013030c004906f81929141c193e13df19270d640e3c19590f7f0f74195501d406eb01cf031a190f19601833,0x141b193e19290f800f75,0x170501c3194216d41483193e192b151a13e113de148019301927193b089e089b184400680e48088b00c319060e310bfe191d1a60031700130f800f7d0f75031e05e305ec03bf03c201d118e801d218ea03b41a580f150f1d1a5b1a1c1a0f1962]))))
set_option maxRecDepth 5000 in
private def hintsBasePart9 : Table := (.node (.node (.node (.leaf [0x16ce176b,0xb270088008e05dd0533003a002f07a2079e01fd01f917e6000302040a0901ff02fb00a4007900610c750a0c081905e101680099116b0bff0b3107ac082117b017a617b1177317c9,0xc8300e800a518780923006f124206610ebc01170041010812b51244167705cd06f4016f01490187003a004911c114ad133e05ed030a00fd01a40122001311c614eb134402e501a7014f01b500121735151814e216ee0b650b620b5e066c01e201b901560198008e0002170116fb1514164f150414c412330dea07b107a201e703b503b301e50c770c6c0c6905e4019c017f00bb005b0055001a00a40e4a0e470ddc07a9077503c315e115d70c76155c11bb0b6c00c30168015d141814150e3e127612731270126a0b6912ff12f912f510590fd207af0138010f011f0f840f7e0f760f730f70187400db14820e42077b13f90de80de613db141c0f80014201330125183e1876169c148113f8136d12fd018a1877100d100a100510020ff90471046902b600e3002208c708c308c008b808b508af0465006b0f200f1d0f1a0f150f120f0c0f0308ba07aa046d030001cf01d4187302fd076f0cb40cc00cc3031c06ed092f0c7f0d5d00b00cae183317c117d917be17c4178517c6178617ae17a61773177217c517ac177117aa179817ce177817ba178717a217b7,0x6a17a1,0x18e901e901e5005518ea02c603ba01e0000f005b001202b6077a07ae02fd18ec192b011f190a07ab046e0301148112fd0cc9191418da0f05191509e118ff09dc1911147d0da312f51939193311c511bb0d9d1278192018d118d0,0x1893100c10040a9419180ff7192205ef003a0c7205e519080c7419360a0c190119f806d102f900bb006106d30de708240133192413f6136c08c808c1193b18fa1481046a0464192b18ec0f1b0f180f160f1308bb082007ab046e0301081a05e2191419060f0e0c710c010f03169113f1141719290f7405ea0a070bfd0de0136207a70dda0e41188c0e3102cd06ed06ef188708990e30141c193e0f7f0d6a049919f7,0x1d1001318e8030c01d51a651a0f1962])
(.leaf [0xfde176e,0x860a8d02ae007f000e0a9b02a5014f001b0827183809b800610074081e064d00bb004009ce0de30d3503930075011b00ae001915c4066812cb10700d2e03ab01640041012100e8139e1397067d131710620d8a065d012b012a156c139b138d10a50c7a015e00a5094f09250921091d03e4006f18370f3f01de01140002077901e900550765005918360cd200e3152a152212cc100301591715153014ed01a40ea614ac01f412b40dbd019f01490003011714f30a0a0200056505580150007900330aaf09f7055b008018340494002509de069e062602b802880076003d000f000b06ae061d05f403d602bd028202cc07720dd9081f0f060f1a0f20049b09e20f730f7c0d9e126a010f0f700f0c105610e610e910eb17b417a417a817bd17bf178517ba17d917c117b1179c178f178a1771,0x47f00f7002311770607047800fe003b047d18b1069405f111d2007a00c3004201630a140ae7068505fd110700830084007200ef0adf0aee09740ae91108015300e800d200c6016610a110890ad70fdd0ecf11e30e6509f300e900e200d900ff00770fe20e661568118110a409f00c81060409c6068804c104b906800120015e00dd00a50075002700700fa510db0ad90c52094c09390922091e04b5047915030958015200ed00a2006f01c0015f104b10390c4e0a20093f12b912b412410dbd174f0bad00e7011701b100930d200d1d0c4b0c2716d015890f530ba800ad009f01910108067306700668137e10d6104306f200410128004913b013a6139b1305067e0d630c7f09c00955092f06ed012b00b010e70d5800ee123010ed01500fbb0c4c0836078c04b200e0006200590a0403140310030c00790013052b030301cf01d4183318730e310e61115b0d07132d02b6045a04690022047017cc17bc17d417b917901781177d17a7177917bf17b717bb17b11787,0x1751776,0xc30e330e4900fd194211ba151419331930148315631519192b01a7148015ce193b1934196c10f306ba049c191b18f718ed09ec09e406b0049318ff19b8052f18f00f830f7d09e1171106e4052b191519441901127a0f700d9f053811710a081890191d06b60d5908b60ba10f150f1d0f2002b50456046818ec046d19b719b6046619b4,0x10c2015500ea088810c700670161080f106f006000e8081410660bc9192e014c0095122807f007de0bcd0bc00107005e01811916122907e4123d125a09b1016b00c0010a191f18fe122a14690e180f660f5f0d350650064c01ad014000da190e0040172f14e014700f690eec0ee908110c5415f9124003a70398039401bd01901913190701ae0019168f168a0f0115b90cee0c5e124e033a193a0163190b010c010b00160cac139311071024101d0cea0edb0ed8071508f80c7b033f03481909012a191c00e400d2004d18fb00a50038005f146c1747172c168505a90c9a0d8a0d8208e104410434125008f109280925091d059c0546193d01af01880120191000b2006c0020014b00a8006f003116b715831572156f1568138c130c0d6b098f09890985097d0972096e08ec08d0043e040503f9038410ac109d108910100cec0cd50943054f04e404e21940015e00b70072001d00e9002b0489042f13ab139a130409dd09d70963040b0d990d960ccf02ea18ed192518ff1911001212410dbd0494173116ca10f010e810e509e304130da302f1011700801948191b1939005512b70ab515d115cc10f40b20076e016f1934190411bf11bc0b1900fd1a38155911510b2d19330088152d15251521130a0b38187f09f719010532052c02a805d205d805dc059608ae08b707740e35033e03ae03bc18ea03c21a151a121a18,0x122c1ab7]))
(.node (.leaf [0x99e176c,0x5ea00f6003a0bfe05e201fd00990003053401f8002f181803b4001a181717cb17c917b0178617ae,0x16700187019016c7167613d001ae012d15a613c80161189816301337133010b30177012200f116321343111901b5015616fc07c7170f1518019c009301a7173417010bb31563155c01b9017f015d12ff12f912f5011f189716ee0f3f0198011414ea12a5014f171714ec01a4152e1526152212cc17be17c417c6177217c517d9,0xe617ab,0xd49011900af12c40fa00d3f194900dd00e816dc0fa70984019300720d90096c00b21910110b0d830d6f191c0dbc0d6c,0xd5b1a0d,0xe3a1a95])
(.leaf [0x15ae176f,0xf611700a0801a4007914ac0a09014907b20468005b00220f210f1907ac046f00d40f1e018a12fb07ae011f058d00370cc90cc2058900a71858057e046417cb17d917b117c1178717951778179e17b6,0x1e03c70423001b007703e304ba006f03cf002708ae003c04c1006b061100ff18d5004511e402f306c1017100120101143202eb09f10af7013b002f00ef00840944071e01f90dbc073700e9004d000300b7005004be0d7e06a806100419043401f40d980d95073c035a00dd00b200430020001900b300170bd706bd0971069b043d03a00da1022200960072012b000611ed0be009900d4f06a4067d0221016100af0041000b106f0d3f0aee03aa04000387027c00e8001d105704010dbd011f0062011710fe12eb083404b212b8013201280059016f0ea20ea0078d0c200bd10ab300cb009f008011b10e9b0c230aac00fd18d80cb30968023600a715940cc8018a147f11ea014218d70ea4048a04300147002510e810e510550d4309e809dd09d70491040b06c7043102ee00ee0076004612f9159213ee10f409ec13f206d3017f01650133164e15cd15d915d613f40c6e0c68073a01a70168186915190a0d09fc09f906cc02010156007913d913d51099089c088e06e906e506c502c203150311012e17e700490013158a149713800d640d610d580953092d078906eb031a0289019100b0141b141813ef187a01381712164c152f0f830f800f7d0f780f750f720ba509e10831049a031e01a400db0f210f140f080f050bd5030200d418d405d905cf05cb035c003a0bf705e305350099116f1166115a11570bfd0a0705ea03b903b703b503b303af03ad03550277022600f6001a0e4a0e470e430e400e3d0e3a0e360e320e2b0ae70a3507a9077506f103c302cf00c3188201c601cf01d41833187318a318c618cf07400b680c000d9d126912751278010f18d118d018ca18d31790178917a2178c17b017bc179317bf17b617781798179c17bb178f17d3177317c417b117cf177917b717ac17d917aa179517c917cb178617ae1771,0x195700c3188218731958,0x2ce00c3000f0e3b02c802b61927009318ec06ba06b1045518f717dc18ed06af049218ff19d80ba2046e191406b70d65049b09e20ba60f05191519d5,0x198c19800f801278])))
(.node (.node (.leaf [0x614176c,0x1080f530ba700d900930eb902ca00d017e00ec10465013b006b1436093108ae09c7019e006f180010a709411807092e0d5c115c02f700a70771005501e7000201e107720caf16ec01980dea00bb06d0004602ef0de20dd917a217b61785,0x960bdf0be0010b016105a01200158d09920038010401640072059b120709d30d73096e006f014b007500b103e114c7156d09ce0cd70cca05a20a42001b019e015e00f000a8007b035a10a810a4108c0cd40a3a03ed0d6b001700e900b7066803650ff30cd10d9c0d990d960ccf00410dbd006100e300b30400011702fc16ed100a16240da3001d12b700120198017509dd0963040b0736016f02f614e80b200076005003d711bf0679005b014f008615d70492048c004400fd124307b10a9b0a8c016817dc02bd0e9c02790149007f0a0c000f00cb000b14ad11580a99007912a502c8078c022101a400f6187f0114009300590006152e15221166164c12a80bb10dea0778076d076a076602c603b503ad0355027702260159017f00bb0055001a15210e470e360e2b0ddc0a3507a9077503c3022d015d00c3003712f912f512f30e39058d011f0ea41888078f14181275126f126912020d9d074001470138010f0f790f760f730f700ba609e200db1887147c14760e41077a13f90de80471046c0469046002b60142013300220de6082313db110d109808990f1b0f180f160f130f0d0bd40ba2082007ab046e03010125183e00d41595148113f8136d12fd0f1f1873023502fd076f09660cb40cbd0cc00cc3028b06b7078b092f09c000b00cae183303690464057e059608ae08c208c6006b187d18790f80141c1496157a15c0187e17b817ba17931776178f17b4178b177317c117b117d917cb178617ae177217c5179e17ac177117aa1798178717ce179517a217b7,0xa617b5,0xe54192a00c40efc083b191300630e52083d0eec083c0129191613890f99193f159914250f0016d70161193a194915461745168a15bd1302193101af019001630120168b154e158215751567130b1946015e168415700ff00fed018819170c950c8009b100a518fe0925091d006f06610041067a00fd17271559115719471933191d1533152d1521130a11680159198808b718fa046519861392138e13190fd40d5209aa092a012a00e100af123510641060105c0fdc0fcc0d400984017f00e812f812f212ee10580fd1011f092e0c7e158615941697,0x14c10660ecd00e800d10d410ec607e800af00d8005e0c97125a085e07dc1909191f00650f5107e008d708d20f85085c013c0095006c191600c80f2b065208db0f990e8500d5004000d6193f0126143e0f2f136e09b105ab0f4515c20cdf03eb03e0018b192818fe0039014b016400a8001b154b135c0ca9094909380935091b064905b807d9156d12500ce003e519311923006f005d015e010c016c00c7135012d612d30f34093907c409b60cf005c411df0edc0a7d0a6b0123011c00dd008a191c190b00ff00d2007d134810f90c3b07d705c8101b0ce80bd70b4909460ede10bb10b80d860d830ce3065706a70441043f192600a0192100e40096013b013f00ea00b20043002013b713250c380fa8131d101e0b5013590d4e0bdd114011390bdc0443098a09870983097008ce069a043c015f01060193015a012d010100f400720bad07c7121f0b0f0a620dde0a64159e159a1597153913c813b911ef113c0bcb0992090b0093016e190400bb016118fc02cb0a9e0a8c03700358169315931585153e11ec06240620000f007f0017193b18d418f402cc0ffb0ff50cd10a940376136d10b7101a062b18871918183e18940cb40cb1092f0ba40ed20f6b157a158915c016910e3c134c02be03d7061e06b2069f096509d9042f049711de145b014709ea0f77149613ca159015c70d43105508200b4d0bd40f070f0a121612710a9a0de2115c1165116e02b4046a036b08b308c1195d0538113311b115fd16070ccd16a208610e86139a139e192513ac19400da515ca10e8191b10f30d5a035b05ce05d205d80bf9190605e10c010c3007ee12d213301333133709080cfd0d00190c0d070cf819110da3193911c3127a09dc0e9100ca0e9419220c7205ed0e95013e074311b500fd115911bc193409ec13d9049d1162073f0050045e18ec0471191d1a0719fb0456074219200f0d0f6e048c18ed049318ff06af18f706ba19271a040d6506b709e004990de8113613f2013313f319360c7514170f1319141a050f0313f11929141c193e0f7f0d6a0f7419f719d0,0x140321032918ef1916025c051d0f990009191f193f02060d33026109b1159a0004190e18fe01610cf013e802080d3d09b610c8190b19280016018f191c00ea0ce813e70d7903270348106e01e4155f0d820a73020e00e401821910005f00e818e9193300b2007d003b108910100cec124b0d720806105a01e0156309d9043f03ce00e9010b00d2011f001201a718ff0020001b109a0f5c0f560ecf07ad02f515180492042f02a3192700d91974193018ed000e13d914910b6207a30b1e0a62049802b019340146008e190411bc11b80b640b1900fd1a880acc00ff1460145a11da0ede013f0f3c098a09870983097005fb043c0be50bdf0bda07fc00d6007200960fa60fa40fa00f9e0f340c850c7b021409d609d209cf09c709c308e908e308db08d005a7059d038b033f00dd00a50075006c00380c2b0c210bd2094d09490945093e093a09310923091f091b08ca05b8059a03e2009f006f067e067106690663059402ac00410d9a0d97067602b1191116280da31a8706c90433057b0388004618f20cbb0cb2096708d506ce0588190a1a861656194414ec0a8d014f007f100310000ffd0ff20a930a1b1918037603610359001705ed05dc05d805d205ca035b003a1a8508c108b908b00598058018fa046a046410b510180a630370082b18ec192400bb0062117411681165115c11590b310a9a047108280824081e14f50836191d006101500bfe0bf90bf6081a05e212300f54190601080de806d30d9f0c710c010b6a14ad149d1245122d145b11de031502e601331920192d014700130f1b0f180f130f0d0f070bd408bb0820046e030114a9149601d001ca19141942193e18e8147e147b14780f17141f141d13f103b603b40356033e01e601d3089c088e088b081507f6192b192918ea1a820e490e420e3f0e390e350ddb03c21a8012fb136c13f6147f15931a841a6c1a741a691a1c1a661a151a141a121a7d1a161a671a721a191a7f1a6f1a711a651a0f1a6d1a7319621a70])
(.leaf [0xc02176f,0x16e12201609010601b50b320a9f15df0088007f016811740b310a9a0c7500f600a405eb05e405dd177317cb17a6,0x15208541500104a006401a900e705031668157e104d002d0186015e104405070c2e130e0128008417f2012016690ea10aef055f055804fc0fe2139b130501b600cb00e8003300e2012b162711cc0e9c105605630fe00c3713a3067d017500fd00ee011b00a0017a00410b200b1b0d580de40c380b6e066c008600b000bb0106008e15120b1d0d65081d0b340b2803b605cc0156012e00610088001a003a089c0899081507a0079c050103b90c6c0c2f05e40068005b00a40318030802fc02f8020401fe0013001200030531051f030302eb01f818b8002f18c809e3073f073e07370076005004940491048b002502b8000f14980ea4078f127f127c126d0b690741086802c80147010f009316d21495137e0f7c0f790f700ba609e20898031f019100db150512340bb2141c141911a00f75017f01380e450e3e0e3c0e340e290dda0ae50893077302cd00c31706170016fd16f81516141f0e4a12f712ea12c71057019c011f172812251482147d14770e420cc1077002fe01ac014200a7169816921595148112fd0cc901c601cf1833187318a30200052c17b917bf177617bb17b417b717c417cf178617ae17a617b0178f179c1771177917aa17ac17c6177c179817b6,0x1b2177e,0x75e00c100530a1a075c0e1c007a008500fc075f04da0a800a190bc30112002a190200c00095128a120d04de051604d807e607e20118010518ef005e1257120c051d037d191f00180cee02530250024b190b000805c301db003918e903b201e6075d0d5f,0x109b014b00e914be10a50154015e15790fd70afb0d7f1508094f193e00e1008400b2019a006f141c0fcc0aef0d8a0afc146608ca192900e8012a0173013f006c16f11418107713950fd811f1098c097208d0019f016f01ae0193015a0101007216781498145b160f145115a5159d153811ee09910e920187014701b6013e016114f31847133f133613321492175e13ad11b715c71590015019221939194e192500fd193415ce122f0ff90ff416081643067e067b10f410e6105601a701081918016e017a0041191b1517150e16501234152615221003121e0b6e066c0ab309e31930017f01590106008e008018ff089d17631736164d0b380b340b280494049106f506ea006801b9194419a4008818ed004903b6031714ae14ac14a4149b07a002b806c418ea0013192d005b1868004601d201d00a0a09fe09f806e502f802f402f018e8190100120743073f073e01c815dd15d70531052b02eb005019ff193618f00c77073802020c050535127c12761273127012150b690741053718c219061920116d116a1164116111580bfe0b300f840f7c0f790f7009e20898031f191d191506d3047104690460045719e1013318ec170016f8161b151614ab141f08c708c308af0465194218fa1482147d147a147711eb12fe12f812f212ee10580fd10580192b011f1863169c1695169215951540148113f812fd193b0cc80cc10cb50cb2096708d506ce02fe190a1a480e480e440e370e330ae4089207a61a460300046d07aa08ba0f090f0c0f120f150f1d0f201a121a191a181a101a0f19621a16,0x19441ab51ac7]))
(.node (.leaf [0x916176d,0xdd0f3609ef093900d60077006f09f10f3804ba04b800ef00df00270dbc0fae04af00b7011400510dbd12a407550d8208d90117014f013f00b2006c12b810cb098b0980097108cf016f00eb007214eb11bf0a9705d805d201a400fd007f003a1170116411580a9905eb179017bc179717ca17d9,0xc01010f0099127608190168006115e1082801b5014f16fb081d0a9d019c00bb007f0e4a0ddc0de8046c00c30133002214820e4208c304650142006b0f1a0f150f120f0c08ba081f04700a990bfe0de10e31116a1173177117c9177317c61787179817a2,0x13817ac,0x146142e145a09d0013b013f00751138098a096000f40072113d0993,0x142f196a013b00fd01ef0ec111ba19f600d0193318f00ec2138204cb014b0129002904cf12050d7704c7007d0104193e1910002d0a740ed5168112010d73051000ea00d20188010b10120ed00eb909c61686124d00e400d901ae101c0f5c15f9014c018f016b0ecc144c15f100d1013d01720ec80df40ae3010900bd0083123609f50720192f0078004e0ec90abc09f40481112f010a1903002400f312390a0f119f0f6204870b42014a007a00fa00da00890df511fb073507260abb0a220b7e0b7a0b3c01790103004f191e00f700911265125b11f9073404ad070106f9124b14bf0f5b10460a1e0c4506090600191f18ee004a0182015400e700a1003b11790f930f8604490447044502db0a750be416c4087e0fc90c3f072a069305f00137191618eb001100f40096194d006600e1190b00420ef80ef50eef0eec045102e00c8e09b204a505a605a0144a13c513c3087c08e308df08d805c305b1191300a518fe0038193c1926006c003914110f00130f1302093e0923091b05b8059a13271326131a0df2090308f908f605f9044d0ca20c9a08d106fc02dd05ab06350630193a0120006f192118fb1909004018f5157415711322130e119d11830b85094f16f40fe60a6f09f608fa04d30c9809ab039c039409a2048502870280015e019a191700af001918fd000b16ab1433153b1535112e0b4410771072106a1066105e0fdb0fca0d3e050b03a9040803fa027a02690193015a00e8001d159e153913b9113c10c710700be2040c016118ff0991097b0974096308ea08ce068305fb0483039f1a2815c719340d1d072316390df616f10ea610f810f410e610560d4409a50592190d194e00be019f191b0041139b13050d2415ce17631736171e16430dfe0a0109fe09fb14f310ed066c192501a701b9017a19010150008e160d1498145b11de0da1122f0f530ebd0868151a15170b1c14ae14a714a4149e124311f30a0908360829040101b601471911010800931930192d0062162714920cff0cfc0cf81706170016f8161b15eb165012340bb2089d07b2079805011939190c1942017f0068005b16080d0a0c370c340e480e440e330e28089207a6016e00a000c3121e0c38162e162b14770e4212fe12f812ee12eb12c801060177192b011f1658164d14ad058b0584057d057a038a0b3b0b340b28175a16fc1634160b169c169515951540148112fd19441863008801b5193b152e152a1522130712f112cc0b351343133e133b133813351331132e132b0cc80cc60cc10cbb0c3d01591922190a10050fff0ff90cb60c440a1d19181a2613f21136013308c708c308c008b808b208af05970743073f073e0737073618fa0050046c046604601a251173116d116711641161115b11580e310bfe0b300a99191d1a2406f5004903170313030b001315e115dd15d713f50a0d0f840f810f7e0f7c0f790f760ed40ba60b9109e20832031f0f200f1d0f150f120f090bd30ba10b4c07aa046d1936191518d0127f127c1279127612731270126d121512030f6f0d9e0b690741053719200c770c740c6f0c6c0c690c660c630c2f08b4073802021a2305cc05d405de05e805ee027803ae03b203b603b803ba03c003c301cd01d001d501d818e801d318ea03b31a1d1a151a121a0e1a181a191a161a101a0f1962,0x19421a9e1aa6])
(.leaf [0x31a00b0001306ed030d17b7,0xc75016800a412750c6f177317a6,0x21785,0x316180c001318ea030f03ba0059005b076702f700550012076f02fd190a0cc9078f193b014714801477077b0773192b00c314830e4a194214a907b1192d14ad0a0a19441901116f0e300a07191d196816d215bf15881579149513de137e141e0e3f193e19290f810f7e0f790f760ed40c180ba60b9109e20898083217e819150f6f19200538053505330530052a0527030502ed01fa031b078a0caf0d69030007aa0f0c0f150f1d0f200469047118ec046d,0x18470c051922190605ed05e1003a0c7305e6,0x9e01a64]))))
set_option maxRecDepth 5000 in
private def hintsBasePart5 : Table := (.node (.node (.node (.leaf [0x1611176b,0x43d002017f0044106a500d200af0ed604430929010400f4006f1205113f05a4059a014b016c003814c70ce00cd705a20a430711019e00a8007b162515fe10a90d800cd50a3b017500e90da20d970ccd00b306780595004117f40d3f098300e817f317f117ef16a4121216ec15ff01ac0198100d100a0ffc0ff40cd2037700e308c0059707370736006b00500464045e045b092e0d5908bc0bd517761793177c17ba17a2,0x790a0a06e40149004914ad06f707b101a40138005b152e0e4007a9015900c311670e3101d4187317b117c117d917ac,0x3e179f,0x3b9005b18ea07a903c3,0x61081b082502fb1906014f001205e112a501e2003a011418e905db077701e7007200550cbd0966076f,0x49318ff18ed09e1049a1a691a66])
(.leaf [0xc9f176e,0x13f146213ff0188013513fc0c9608e4013b00a5006c0945092308ca,0x7f718b000680fdd08990aa700e8012e008010ec105406ba0494042e00ee0044002509e306af049218820e31187302b6045700220470105817cf17bb178b179c1787,0x16617d4,0x1929141717e818690f041920191418d118d00d6908b608bc19b4,0x1535015a015e1537139a01611925106f0da100e8191110550da3191b193910f40b201934190411bc0b1900fd1a341057186007ae19741a330cfc190c0d02101801061924121e10990823016e192715060ea400610aa013e215ce017f01470815007f01c301a7198a16d0157a1496137f00680ff20a93053206c704311711164b151b15180b1d17e80317031302e41525191818f000461944193019290013187f1a21052b06d214ad0f840f7e0f790f7609e20832031f046c190100bb192d191518ec19e41476077a0de806d30f180f0a0f04046e192b01331914169c169515951540148113f8136d0f1f058e038a02bc193b18f20cc80cb2096706ce058802fe190a1a3219de0b680d9d121412721278192018d118d0184d057e08ae08c206f008940ddb0e350e3f0e420e4601d018e801d318ea03c214a916f61701170419420e491a181a1c1a0f1a161962,0xf211ab1]))
(.node (.leaf [0x99a176c,0x8b500a4006b0c740466016800220a0c046817a617a217731787,0x122134005ed0187003a0c7705e417be,0xdb17aa,0xd22010d190d0f630d1b00da00e70f61104f010a015e123c0bc80b820b7a016b0095009114460bc40b86013d00fc017d114d1146135400f5012311510ffb1933191815211005,0xc7d1a0d,0x538192018f018c2030408b40013053418fa01d11906184d184f18e8116a0bfe047001d2191d18ea05ec05e303b41a941a801a6f1a651a0f1a6d1962])
(.leaf [0x15aa176f,0x5d9003a007205e1043b00990020081a0442006100f4081d113d099300bb016106d0043102f9133605ee004618080430012206c600250c730049049200a406f700760c74013809da016817e800b312760f6f0d9e06ee07a60dd9082117c917be179c17a6178f17ac17731793,0xcb078d0e9b005900fd076511ba0055015d02c41521000f015917dc08c70465177217c5,0x423001e1900041a04b900640027084c04c2042100dd00ff18fe0fa011e4091b01190171006f0fa7056d1431094601930035013b15c90d4a1395084f09f2056c071f193400af012a191c004d10f30d4211da10630d900ad10ac9071204bb191b013f00e800b200820aaa079b0e0b098c098506600658064e02740271026d0080005b00bf00720040000a06e712ed07ad03a903a2039e039202640049011f001902c3058c057b0388000f18f20dbb02c40cb20967058806c700b70055190a004613f206d30dbd0e010ac4076502ff02f00133011700cb0059001213ef0c27041303fb0386026a0ea4078f02e81929009f001d0147002b0e3f0e2a066f066103fd1493076a04e800c300411939007f0d9603c303b603b003ae066d0b200a8e0788076e031001f701ef191118ea008e1904001300030cf907a104eb03550531052e0522030302eb01f8190c0088001718f005e705dd035c11b10e9b0e340c230aac067a09eb09e809dd09d70963040b0bf70a0109fb06e506cb052c003a17fa00fd18ff190619010d0705ef049d049704950492048902b81163115a11570bfd0b2f0a0705ea192218ed12f611bb0b6c0ff70a9304ec0375191d0c720c6d0c6705e502030f790f7309e2049b031f1933191815da1417116b0a0d19081915152012f310040b3718691278126c12690d9d0c6f0c000b680f130f070f0407ab030118911920046a0458045502b4191418d118d0184f195408c808c408c108bf08bc08b608b005800466036b18db01c601cf01d4187318a318c6,0xec000d0013b0eba094500d9006f09c609200f520ebc007501080960122c0072192d05da06670661096514ad003a004118ff194405eb0671049114eb191d009f18ed014f11b311590c25049e082700fd00610b650b620b5e066c0b1902fc13f20966008e190400120133190a0bfd0bf5081905e10532052f02ec13f70cc8190618f0193b0c010b6a053807a218c51920005b0f200f1a0f150f120f0c07aa030019d406f306e814e30b1e01ca0049193018e8030a030302e316fb16e9151414a903ba03b603b403ae035601d30013194218ea088f088c081603170e490e460e390e350ddb07a806f003c2006800c31882141f13f10e3b0899192919271690141b13de193e0f800f7d0f750f6f09e10897049a031e031c06ed092f09c00cb00d5d0d650d6a1962,0x19e408bb046e19140f0519151a5419e5191d18ea0e3203c31a4e192018d118d005e205eb003a1a4a1a31])))
(.node (.node (.leaf [0x1eb176c,0xe30ff40a9300e9007f18000a96066a066400eb00410d98145b11de10ca03fd16ec00b3014700f1001d019816250da411b911b109e809e5040b16eb017500fd05cb0076019c14e910010b1f0b1a0b170a8d003a06b014aa014f0086082605e10044014914e111190b1c17f90099109906ba13f913f20a09015612780d9d0c6f0c000404012e01330079089e010f0062157b149713df13f40a0c17e70f7d0f780f6f09e108310191016817e8141b141513ef01381804116b11590a9a05ec01c601c906b60d6902c306c606e606ea06f80306031203160e330e3b0e480f0e0f140f190f1c01e5033d03ad03af03b103b303b503b703bb03bf03c405000797079b079f07a307ae02ef02f302fb02a90521052a053005330535002f02ec001202f6005b03b907ac07a602e3030203030013030d01cf031b17ba179717ca17931776178f17c617b4178b17c117c917c417cf17b117711779177317ac17b0,0x114d00f5013d11471449073500fe018c004f0e4e0e4d16aa072d072900c4019300ae008313950e520fa70d310adb0e51072b012a012900dd00ed012400a9132813191302069506910fa310380ca804be08f60d78012101200042013b00e700a60027006d00b109560fe608fa130506860e790946093f092704b705f705f10d6b007000e2012b007500c7006f003b00b709580c370c34139a138b09ce0cdb0cca03e503e103cb09dd015f00a0015e00f000a8001b00760bad05f50c3810a41093108c0ceb0cd40ad603ed02a5049200930044010600e9000e0b0f17dc02c902bd12210d9c0d990d960ccf02b30086000f0285016e00b3076d02c6000b12ca0fdf0d090cf900550221011b00aa077500060de30dde0907180c03c403b70277022600bb006e001a0d200d1d132d0d070372036e0362035a0356022500ad012200170dbd0673066802ab05ed035b01170041003a0c640c300c27067101fe00a4009f00030c76088f04b202a701f8016800680059002f0a0c02000318031003040079001306e4030a02c001c601cf0235076f0950028b031c06b7078b092f095509c0036908ae08b108b4157a1589158716950ba20f070f0a1098110d0de602b6045a0de813f201330f1313f808c2077a147912c812ee104210d50376090c0cd10ff30ff8122401ac100c169805eb116a0a8c0a9e007f0a99046c0a9412cf130a15251151138105de0088079e0b300b3809e20ba60f730f760d9d0f6e1269078f01470f79149614760533066e0c2b016515ce01a70f841711156213d806790c2200fd0b67008e0b68010f0f7007a2005b07b3014914ac07ae0b6b11ba015d15210159152e01a4188413db117008c6100400e318830833012812eb0d63137f18820e4101420f1614811873047104690022046e0464082301250cc30899183e136d0f1b0f180f0d082007ab00d40f1f169c0f80187e006b187d187900b00cae18330cb4115817cc17d517a817cd179117bd17b5178d17b817b917bf178f178b17b417931792178e178617ae17a717be17a6177317b017b117c5177217ba17b717a2179517ce1787179817d917c1177117d3177c,0x9817c8,0x12ea0128011f137912f619331520198407ae079719740d6202ce07740e2a0e350e3918ea03c2,0xe42192b00c3147f0e48193b185d0f1f0f1716910e401929141c193e0f7f0d6a0f7419f70e3c19271a040d65,0xb64008e00fd07a311c31974193907ad1607011f016e160a0cc20a9e01b5190a007f15e00cb50a94193619180c7403751908001705e5035d0e350e39035618ea03c2141716fb1942141f19290e3f0e491a161a70])
(.leaf [0x1085176e,0xe8106a10710154016114be1351014b0123109b108f00e90ff300e313350ff70122133c0185166601c5175d01b5175801b6175e01c41642017a13af0b6e012b008e0c91067d066b00a5004109420923066217ba17be178417db178317bf,0xe40013800c3141b0e42019101421692148117ac17791798,0x1a817da,0xf02c802b5009318ec0ba1046d19140f040ba5046608bc02bf06b3,0x151b01c3193013e2170415141927194216d213de141e193e19290f810f7e0f7617e819151a441483192b16911480193b0cc91a1c,0xbb01ac3]))
(.node (.leaf [0x912176d,0x77100a7005502fd02f10012077a0774182416971594018a147f01420e460e420e390e350e2e0ae60a3407a802ce00c3182303c303b203b003ae0356033e01e6001a18220c730c6e0c6b0c680c3105e600a413f40c750168127b12751272126f121412020c6f0c000b68010f0f210f1f0f170f140f0e0f0b0f080bd50ba308bc07ac00d40f830f7d0f7b0f750f6c0f040ed30ba50b9009e10831049a182001fb01f401f001ec000305370532052f05290526052004ca02ec01f901cc095409bf0d5c06f203090315020106cc09fc09fd0a020a050a080a0b0a0d181f181a031102c00d620d590c7e092e078a0633028a031f0319030502e60013030a01cf031b06ee06e706e406c30049181401d406ec0d690caf06b601c617b617781798178617ae17a6177317711795,0xf1800d401490f1507b10142005b0e4207a800c303c303ba001a18a407ae011f0cc100a7169c148112fd0cc9187318a30e3112f10f2114ad01a4152e015911671170179517c11798178617ae17b617d9,0x12b17bf,0x8009f80aaf1901015001ff08380003006201fc082f003a00cb035b0ea200170132036113b4003b192613bc060b10f903cc035801640123191c001b15c61091108903ee01b300e9174610aa01af17271947100d0ffc0ff419180cb4190a07710055077a192b16971480,0x52b190118f0046817fa18ec,0x141c1aa1])
(.leaf [0x141d0191013816900f75018a00db14800f6e0142010f0f1f0f170f0e177917ac177817aa17981771,0xdb0f82049b01a7002511c8049d17aa179c,0x99100720161097a0bc900da0095088306520067004003a0040503f90019001d039703fe005e004107e9067d00d1012b0eca13ac010a019407071455004b013e088507090e96012d013a00ca132f0e9314280bbc0a900122016900d5007f16b613411185047e0a97018d00f7002300eb146e117d047410cd014000480157075b1409117906e30f950052013700dc04a104730ef90eee0eeb002600d30b57070304a602e102da008d008100110519051702d8002e151d0f2c07dc051401a1013c00650867148e14370e890e81085c08a50153014500c8006909b804a3140c0ae01620146b0eb60eb50e7f08a00a83051604fb04f7007401430083017400ce007e002c0422041f0e580e4c0ad40b0c0b000a7f0228001e00c40085000603e903dd03c70f6708860a4d0a4804f30232001b0155007c03e815e2148a14290abd16041485140f0a8a14cc14ca0ecb07ef0726072500c70170016d014c004f0e771262125f12590f850ef50b5907320121010e0cf50cf20cf0072c00a9028e101c0ce90a52000c00e4029210160e4f004501240eb108a306c210c410150b0610a0109610930ad603ed012f00ea00e9111010ae108b00f011120d4d0758015400af15080c66019a00a415dc0c75028f06d90168002d004715d504fc06d8016f0033007b0ab3055b0736008000500494048b00250493007618e40ca906e0061a02df00a60fec0fe50c9d00e210c00fea0e6b014d00c60a790a67007d0a7700f411370e79013b143501930ae90a5e0a2b162216f11394065e008401b1019f012a074906d510f710f510f010e50b080d390d34072e005100ee00ae06be050904b1107510711069106510560fdd0d410d2f0af00a5504fa03ac0096002700e80fa60bd604be0c940c840c7a00dd00a5094a093b0936092b092709240920091c064a047b03e3036b08b608b917bf17d717be17d6179717ca1796178817a917b317af17a4179917b21775177417bd17701791178c17cd17d017a61773179c178f17b517b9177d17bb17a8,0x54301120030128f0541017d00e9109f1645053a0942015301a30060006f0fab14df0814093400de192e00d5125e085f0a8914b40f2e191f00651902014a0f020ef508110f330a820b800855102a0a840a24191301a500c8009100e5007a0f000e8711860e810b7c0a220f32102710480a200d34027d193a192500f7018b191a00e7190e000b157d1574139c118310500b8516a00fac10ca10dc103802610207015e194000f100ed0009000411e015cb111d03f803f5025a020800ff1934001c001611db10f303820339020b013f191b00190e0c0aaa01f600bf008000030a0009f701ff028a092e0d590d5f,0x3a05e301fc190619e30bfd05ea03b301c818e801d21962,0x31d1a64]))))
set_option maxRecDepth 5000 in
private def hintsBasePart13 : Table := (.node (.node (.node (.leaf [0x173c176b,0x11512ab0c1312ac0151009c01720ae210d20f930c0f1618008300ec00dc01af10d10ad709b309b00f9915f0012700e900740192016a13750adc12de0a3c0422169d144f019000ed011e007b001e018b013e16c910df0c14112a0941103912e70a2b03c816a00743028501ae016400f2006f00e7017e0084001b01940050000b15a6159a159715831576156b1127094d0d1b1314104c0ba00b95050703d20da5073b027a0161015e00ad012001520092002d004300b3001d1335139f139b0d241310085108410503041a14c214ba0a41069c02a50678066404000122012b01820064014b0072000e00411344165513a7150708500fd40fce0fc80d530d4c09ab096601de05cf05cb01b501860154012a00e100af00a70002003a165d175816691078106b1063105b10520fcb0d3f0aee0983077101e905e1018501b600e800550099166515221307163b10e710e410540d42041217340777081a01b80159017a00ee01b90114006117171657152f15cc159214f010ee169a1593150614c612aa174814e412a2082501a401650150018a017f01c3014f17191711164715cd14f512fc12f912ef10590fd2102e151b151214e212a6055904fd01a7011f00e601560033156312f612e410350b1c02ae0aa5055c015d0086008011cc11c811ba11b60b1a0aad028a092e0caf0d590d600d6707720a320ae40e370e4408210f1c0f1f0f2105ec11621168117409f7149c149f14af01490a090f1917c3179617a4177a17d717a7179317be17bf17b6178517c917bb17d917d3177817ab17c4177217c517b417c1,0x15014ee0ab2017a008013a3055c012b003310e8056200ee187c05f403d60044035f035706b20017009305d9035c030602c8003a0013000f132b05ed06e9030c02c2052101f601220049002f0003134405de09f706e4052b01ff01b50088007911740b310a0800f6187b0b6e0b26008e0b6c015d109807a2079e02c70c6e0c6805e6020412f512ef1059012e005b005500a4011f0e3c07a7077315df0c74130000c3016801b90e42077b14170e4012760b69053714af14a5149c0a0a07b201420138010f0149169a147f12fb0f7a0f740f6e0ba4170116fb14a9018a00db185d1691157a141c0f80187a10050ff90ff403770f210f1f0f190f170f0e0f050ba307ac047002b400e300d4184d08c708c008bb08b808b508af036a01c601c901cf01d41873076f09660cb10cb40cc0031c063406b706ed092f0c7f0d5a0d6500b00cae183317bf17bb178b17be17b017b117cb177217c517cf17a61773179817ac177117c1177817aa17ba179517b7,0x7317a3,0x171101a7194415ce0f211934191410f30f04191b191509e409e218ff09db19110da415631939193311c811c411ba00fd197c06ae02bd18f713da06bb19270e3b0e370e3307a6077202cc06b60caf0d590d9d1278192018d118d013de047011581170,0x47a006f00230946047f013b00f71430047e1184016a00d50169129c0f2e13fb07b70113014a0134005c076213fa125211fa0dee0deb04f2060a0054192a010d010300bc002c003b076311fd12970ded07ba0efb0ef30ef00c480d210a4b04f40c930922060201411946014d0120191300a1190d007c00a514260f011217119711900fef0fea0fe308f708ee0cdb0cd9067514720a5304f8074e193a010600f8191718fb00a80041016c00e800511361121f0e790e720e67154f0fed09050ccd067615fd0af0074b1923016e00c700c61931191119ae008410160a500d090a7c0a780a6e0a6a0a6607600748134f0c900d9b0a450a2b00e4190c007d012300f0007b153c102010bf10af10130cff0a7210941092108e0cd60a3c11dc118a0e64015a00ea00e900ff1546153710c5106e145c0d7f06a60161013f00b200430992098b0988097108eb069b05fc007209d90965069f18ff049218ed0b0f0a6207610498190415e6090b04780a9e0a8c194718fc007f100c0ffe0ffb0ff30cd10c43090c076d076a0234022a1918005500060cb40cb10c3c076f0235092f0c7f09e01098110d134b07730a330ae50a9a0e62115c1165116e022603b518ea01d318e819fc0d9f12160f0a0461046a077c119308c108c511de145b014714780f771496153e15931696101a10b71924136c136213f20a640dde05ca05ce05d8022303600364036c03730017035b036b18fa046408bb037100bb0de8013313f6193b1481192b0f160e4116910f1313f119290f740de2191d19fb0dda0c640c6d07360737005007390742045e18ec046e19140f0e0f03188c0e3102cd06ed06ef188708990e3b141c193e0f7f0d6a049919f70d071333133719220c7205ed1962,0x6c41a7b])
(.leaf [0x107d176e,0x10b124b05100182002d124d0be4050801ae009616c605a00190003815ba130f059a01630120006f1569130e094f13eb015e0131139b13981305012b067d05920dbe004100b70bd106710d9616781671009f00b301870dbd0c260da215591453066c01170175015d013e008e16cb056504fc11c511bb11b70b6709de01b1003300fd007615261522130710f810eb10e905630b1a0491015900ee0086002517361658153010ed03b6078802b801b901a40150001a0059000f14ae14ac149b1243050103b9076502c50149005b00550bf70a0a02f802f400990079001205340531052e052b051f02eb002f183c074300500c77073800a40c760168116a1161115800f613b6132404710460015f0022122f0f530ebd0bad0ba9086807c708c708be08b808b208af0597046501080093006b165012340bb20580057d057a038a0331017f003712fe12f812f212ee12c810580fd1058c06d006c70431011f004613f206d30cc10cbe0cb50cb2096708d506ce06270588013300a71595158713f812fd0cc91498145b11de018a0147088f088c14801477077b00680d610d5b0d580d540cae0c7d09be092d078902890142031803140310030802e500b01703170016f814ab148317e906f506ea06e606c602c313dd13da13d6134d110f109a0d6506bb019c0049012e141e141913f006f716cf168015bf15881579149513de137e0138019117e801c601cf01d4183302cc06ee077207a608920e300e330e370e3b0e440e480300046d07aa08ba0ba10bd30f120f150f1d0f20049b089809e20ba60f730f760f790f7c0f81053707410b690c700d9e126a12761279010f0f7000db0f030f0c17bf17931776177217c5177d178f17bb17b4179c17d9178617ae17c117c917b117b017a6177317cb178717a2179e17b61778179817b717c617cf17ac1779177117aa,0xc76016800a412760c70010f0f0e00d40f1e018a18bc08b4006b184d0f6e0f0318bb18730470116a177317a617711795177817a2,0x18d17d6,0x19290f7617e8191519bc151419421483192b0e490e420e3f00c311c611bc0e33,0xc31a3b19de,0x1501a721aba1abc]))
(.node (.leaf [0x570176d,0x5e500a4003a0c7405e20168009912770c01010f181c116f116605ea00f60e3100c303c303ba001a03bf00680899012e181b0e3f0138141d13df01910f7f0f6e09e00896049900db17e817a6177317c9177117cb178617ae17cf17ac177917aa,0x10c0edc125000d2014b0b8c14be009201540b9d106a0d86015e00e800b2153409830970015a00721539107009920161189c090b006e036c001705ce035b003a189b1675166f166d01871340133713331330132d0d070122189a164a01a7150514c51562155d155b155712e312ca0fdf017f015d011b12fa12f612f012c9105a178e17be177217c5,0xf617cb,0x18f00535052c190619010bfd0a07,0xd661a0d,0xe471a95])
(.leaf [0xf6116f047101a400220f20046d00d414ad0f19014907b1005b0e3107a717cb17d91787179517c1,0x19c1482141f01420138147f0f74018a00db0f1f0f170f050f80141c169117c6179817ac177817aa,0x7e1005e0095037e0bbf001800dc037a0eee0512003c00d3002e0652061a0f850ef50251024c004000a6010e000806550c9d0cf0025600b200e200a90bc909d908fa08f808f5061301610076006d0991096308ea007206820042068a008f0b73017b14a80378024e0149001b07b307a501db03ce025d005b0002003b000903b901e5020e0205001a00040e0e033e020a00bf001603a40398033b020c00190fdd03ac00e8034d0d340d2e069002620b7100b900ae00d90a2e13bf0e0a0d3706980eba007b012c00d00347054a087b08760872039a07cf005f00310066005d04e504e3086b07ca002b00930f5a087e0c840c7a0603021304e702c8015400a5007f000f0ec20a4007d8135213490dca0809060d1111096b08f3093209270924064a03e3076b02c701e90529052604df014b012300f000a8006f0055002f150514c5109c1090108c0d7f0ceb0cd40942054e03ed0c7d092d02f102eb017f00e900b0001213dd134d110f109a031c02e6012e00130d9b0d980cce089907f60547031600b300680da20ffa0ff20cd00a9304ec057b0388089e017500e300370156147d0cb50cb209670770058802fe151414a912f7105707ad014200a718441863159514810cc901c901cf183318a3058008b008b908c102cd077308930a330dc40e3c0e451796178917a917af17b5177017b91791178f178d17c11785178617ae17a817c017b017b717cf1793177617ba179e17c4179817b6,0xb20193919040da2052e191118f012790d9e053719200f0e191408bb18fa046418ec0497045618ed09dc049304990f030f6e,0x199f19140f800f04,0x1a911e6166800ff01860b9712b9009201170b9912b60113016f12a00d2704c001af190d002710ab0d1b04af00e900e700511582157e10a3104d0b9b074d015e00a5094e093f09241a15])))
(.node (.node (.leaf [0x8ed176c,0xc74016800a412760203010f0003053801fa177317a61771,0x3905c405c100a900a30cf10c56012100ae0c5a07d60c7b05ad00e7005d00a50040104e03330922064805b70ce20656015e0015006f00b20fbe01f21522138e13190fc80337092b097200e000030159012a00e100af00720a0301ff152110630fcb0d3f0d2d09830079015d00e8052d052712f512f312ef10590fd2002f011f057d0331030313000037001301b90c6e0c6b0c68020410e410540d4207c90586030c14af0fc200a400ee0093004901490c70053709e309d8096402c802c0170114a9010f0076000f185d0f190f0e0ba3049302b900d40025046e0468045602b50022188c0f6e0ba409e0049900db0f7601380e3e0e3102cd188b169a12fb018a18891691157a141c0f80187e08c608bd08b708b408ae057e0464006b187d187901c601cf01d409660cb10cc0031c06ed092f0c7f0d5a00b00cae1833179117a517bd17a817b1177217c517b0179e17a617bb17c11771178f1795179c178717aa17ac177817a217b7,0xad17a7,0x192e14dc14dd0efe0157018419130f9412660eff1916191f193a08f80f9909b113c10cf012e818fb193f18fe1926190b011e05f715c3091d0d33110310f90cf108fb0fce09aa003b0164006f190e191c1921191700e100af153d131f1349060d0ceb156a094c0d320aca12ca0fdf0fdc0fcc0d400d2e015a012300e9015e00ed0082011b00e810ce1599158d153813510ffc0ff4104e103e10380ac612c810580fd1191a0161191800e7011f10cb133513310375035f152412ce100410d5104207ad014f1922001701590128197414e605ee035d12e40fc70fbe134b1098083407970185003a193300e017e700620c0305e10b6b0a0309fa031603121906008e1901001305350533052d0305031b092e0d620d690b680c00127e08310e39035603b418ea03c205f618f706ae18ff19870e350f830f7d049a19800d5909e106b6,0x190f19d01a0c,0x8e05320b2518f0008802eb0b310012191d02e604700013184f07a3079f02f601d018fa005b18e808b403ba01d3190818ea05e505de03b31a8007a600c31a8905380b6a0c71030107ab08bb19140f0e1a651a0f1a6d19621a7e])
(.leaf [0x135f176f,0x46f00d4002208bb046517951787,0x15214bb0854014b00640f43050400d6002d0f42050e0840013500e8008f06dd03aa0b7205080a430047001901100096007b06d4068b03920f9b0f350bd70acf0a2706d6004d0042004000dd0082005112b413fd0fa3071f0c8905b005ac05a004be04bb04af0117013b00a50039003800270c270946092405b9059b04b7009f006f066f06610592004103ff03fb038606c7001d0046040102f00062001207a4079702f6005b105707ad011f18cc055804fc068005bb00330070055e095800800b1809e5040b015f11c711bd11b10c230aac008600760bb00bad00fd04970492048900930e9d0ac417dc02c900cb000f078c074504b206e702c0005900490d5a0c7f0955092f078b06ed00b018cb0ea4078f014716d01589157a1496137f17e803ba03b803b603b203ae0138001a0e490e460e3f0e350e2a0a3403c202ce01d4183317b4178f17b717ac178617ae,0x1c11782,0x193b148018c5192b0f1d0f15191419900f750f040d6908bc19b40e400e4319cc,0x192b0f17147f19141a4b0f0419151a4c01d018e803b601d318ea0e420e350894077406f003c202ce00c318821a2c11570e3001fc05e2003a1a4a1a3119de192018d118d01962,0x191d1a981acb]))
(.node (.leaf [0x91a176d,0xc80aff0e830085012602a01370000d015c0cde0298090e00a8001e006e10b90b05029c0248042a03ea090c00ea0040000700ef001b00e310c60d8302a20393028d02370243108803ec1000016100b20019000c003800e9014f02930990096f0969039e029005921099082700840072002d0944059c0041012e006110700aef0984050d006f0e88040003fc03870d010909136613620822057c10b203d800e8182b012b001d00aa0125003700f1004410580fae10e710540b0704120da00d980cf90cce0cc40cb60cb3096808d60589074504b208ae0596073702ba04fc09e509d706ae011f011400ee00b300a70059006b0050000f0033007612f912a9159210ee0da40776076f076404650462045f045902b502a40239055d0493017f01650150017500551828000e00800025164e15cd14f50b1f0b17076d02af11bd0aac049c01a7008600fd151912a7111b0b1e0e9c0e001712164c14ec05e705d905d305cb015600cb01a4003a15140e9e116f115705ea019c012800f614aa08370834082d04020de60de10149006200bb07b107ad079604ff06d101df005b0046000202fa02f602f202ee01e00012182c158a1497138013f211360de801910133141b141813ef01380e4a0e470e400e3d0e3a0e360e2b0ddc0ae70a35077502cf00c303c203b903b503af03ad028c01e517d2178e17bc17ba17cf17bf179217ce179e178b17bb179317b617a2178f17d31776179c17b417c417d917c617cb17c11785177917ac,0x84f0064012a084c131900dd01210fa70fe509390841019300e2006f0092159e0c9e05c805b90b8d016100a6003900d210c50c9a0ede106f10630d9005b406a2044100ea00b1013f00e800b2006c0043002005bb0d000d6b098c098909850972096e08d0069c043e007000aa00b700720958090709dd09d70963069d015f006e00760bad036d0492042f0093001717dc02c903b20356000f001a02ce180c00c30e31116417bd17b917b517b81792178e178f178617ae,0x14917c1,0x52c190118f00a0b05381820192019ac082f00cb0ea40147052e09e9190418ff0498049318ed0e9c0b1a049d00fd11570a07031b049909e00f030f6e0f77195614970f751929141d193e0f7f0d690f740e290e34,0x55076c07711904190a0b1e0cc81930077a193b1514169017e50f1f1942193e1914141f0f800f04052f19e106f6191518f013df0049031f0305192717e90013089a031700680e490894077403c001d001d518e801d318d01a161a101a1c19d01a0f1962,0x14a91aa9])
(.leaf [0xf5115405c6114e016d0039015b125f05af0fed010e004200e20d3405f20cf50cf00c800fe600ae003b00a900a501210d37134f060c0cec0925131f012c012300e9006f015a13b913520d2d0c840d7f0ce2091f068708e805b5016100e800b20075006c13351331105409930972096208d005fd035f012200ee00720017134410ee09d8096405d905d3035c01b501500076003a16fb14f504930667066105ca019c01a700250041151611c8049d02ac015600fd000e0b1c0b1902ae008617ec15e516ec15ff01ac0198100d100a0fff0ffc0ff40cd20a1d090d04dc00e308c00736006b0050046a0464045e092e09bf0c7e0d59177417d1177017b917a8179117bd17c017be17bb178f17c6179c17c417b4177c17ba17a2,0xaac008000fd06ea18650049031e030c0013031900680817006109f717110826007901a4014f0a0a152f0a9d01490159007f14ae0822100310000a9301b9012500e3089a031a170315630cc40cb6012e00b0019c015d00a713df0d6a148212ff12f50cc101910142011f169a1690147f136c12fb018a186c01cf01d4183306ee08920e330e370e3b0aa91867186b057f08c008c70455046a08210f170f190f1c0f1f0f21185d00d408bb0e480a080a9a1159116800f60470184d184c0e3017b117d917c117ce17ba17cf17b717c6177217c517b617791798177817cb1795,0x25179c,0xe48194200c3141e0e3f,0x12a0eac139500cd01930eaa065e13ea00ff0040013006a803920fa7106510be0043001900dd00e800ea069b03a00fa30c8304be0a710072013b00a50027007d096e0aee0e790e6e09460924064a04b702451910008400c7006f00070cca0a2b03e503e1023e03fc038700a8007b001b001d0cd40a3a03ed027900e9000b0ff30cd10221191800060cb40235028b092f0c7f0a350ae70e2f0226027703ad18ea03c3,0xf031a64]))))
set_option maxRecDepth 5000 in
private def hintsBasePart3 : Table := (.node (.node (.node (.leaf [0x15de176b,0x14be014b015414c711140a43019e00f0007b162510a9108d0a3b017500e90da20d9a0d9700b30678004117f20c2a016510f400ee106a10541776179317d317bb,0xecd014c00d1125a0ece1066010e018700e80f8507f007e81527105f00dc005e015901290f9907ee07e0152a13830d350d2f0d770192012200950188016300ae00b1159a13360bcb167d15b70d3b0d7108d70161018f010b006c0652135315c20f5e0f570bdf05b309bc09b100400123016400d90096003900740398039415710c910c7b09d609c7059d05c80d7009b60019015e00a500750038012100ef03f90384094d0923091f091b08ca05b8059a13c21348131a10f9001d006f012c0624027a06690663059413b310ff003d000b00410132061e02830bd203b603b202780ea30044009f001a00cb13d5134c06ba089003bf082e012e0068006213dd1560155c155a1382057b038803190315017f015d0037001312f912f5058d0c7d09be092d028902e3011f00b000120cc20cb008d6062802ff00a71872166c01b613ad13a5139e139a132b1304012b0b370b2d0b2a13ac0088019412330f53079f02f60b610b250829066b01f70da50d970cf80ccd02b10df80df613b713250108005b008e000300b300be015f1245122d07b30aa4053202a801f90da315cd15ca159013ec13ca0c2914530e950dfc0bad0ba90ba701490080002f01750165013e00930a0909f7052b01ff11cb11c311bd11b511b111330e9b0c230b650aac067a0743073f073e02cb007900fd0050000f06f406e5030c049d0497048c02b80049002511de141411a1112506f809ec06b0069f0493040d0147013800760f820f770f740ed20ba40b8f09e00896083000db16ff15151280127412710f700d9f0b6a07420538019c010f1483147e147811ec077c186913f2113601421171116b1162115c11590e620b310a08013315931585153e147f13f612fb00f60f1b0f180f160f130f0d0bd40ba20b4d07ab0301018a1691168115c01589157a1496141c0f800470045e045502b400d41863185b184f08c808c408c108bc08b908b608b005980580036b006b1871186f186b10e810550d430aa909e304131867184c0e480e440e3b0e370e330e300e28089207a6077206ee02cc01c601cf01d4183317701796177a17be17a817b817a417bd17bc17c0178a178b178617ae17cf177217c5179e17b717b617bf17d7179317c117b0177617d317b1179c17ac178f17aa17c61771179817cb1778179517a2,0x3c1789,0x1810030e02e300130317006818820e3b030d1927004906ba06e418f702021901088b053406b019081815190618ff0e4306f612770c710c010491192b1929192018ed14800f750f6f09e10897049a193b19151692141d13df0f81193e19720e310bfe031b06b606ec0d69030007aa08ba0ba10f0c0f150f1a0f1d0f2002b60457046918ec046d,0x200000319010202052b01f818c218f0116a0530191d190411570b1900fd11c30469193918ec0da4049d0456191118ed09da049105370d9e1279,0xf7f1a64])
(.leaf [0xab7176e,0x939006f00dd04b80fa70027019304af15c90c2000510165009f07550d9011bc0c22013f00b200fd1164098b0971067a067000f60072004105ea05d805ca003a1832145b0da00cf90677014700b3160814940da40bb0017500930b1f0b1702c90086000f06b505f6049e049802b90044002509eb09e509d7096306ae04910076183113f21136013308c208b708b108ae059607370736006b005004650462045f04591830074504b20059076400550cb3096807710628058900a7182f169b169716941594018a147f14791476077a01420e490e460e420e390e350e2a0ddb0ae60a34077402ce00c303c503c303be03bc03b803b603ae03560227001a182d15e015d613f40c730c6e0c680c650c31073a0c050bfc0bfa0bf705e3016800a40099127e127812751272126f126c126912140d9d0c6f0c000b680740010f18230f210f1f0f1c0f170f140f110f0e0f0b0f080bd50ba308bc082107ac00d40f830f7d0f7b0f780f750f720f6f0f040ed30ba509e10831049a1827020301fd01f601ee000305340531052e0528051f02eb02a701f8002f18250a0d0a0b0a080a050a0209ff09fd09fc09f906cc04690201181f181a031f0319031503110309030502e6001306ee06e706e406c3030a02c0004918140d690d670d620d600d5f0d590caf0c7e09bf0954092e078a06ec06b60633031b028a01c601cc01cf01d417d317cb1793177617b4178b179c178f17a217b617781798178617ae177317a617c91771179517b0,0xe7100c700f80e79118b013b00ff0fa30ec004c100dd00d000270939093004b5006f0b60092f0ebd008e00b0010804b20662082a122d0d640c200ba70059004100620149012e009f009311de078f06780314031014af089a088f12340bb2014700b3001301b90068017f14920da2030312fe0bf70815164f0e8f0175002f011f0099006101a700ca0b200b0f0788053007ad079605e108280f840f790ba60832031f073f0086005b003a014f00db005017010c220b640b1906790dde081d03bf03b903b503b30a9d0a910a8d0f6f0d9e07410537019c00fd00bb001a007f010f0e4a0e470e3d0e360ddc07a903c313f20de80738046c0460045a127700c3013300a400220168147d147711920e4208c308b508af046516fc15e00142006b18a90f1a0f150f120f0c0f060ba108ba081f07aa01cf1833047005eb0a990bfe0de11158115b116a18820e31187317b717c117cf1793177617b017c917b417aa17c6178617ae177117a617871773179817a2,0x15d17c51772,0x19140f0d0f191920192d126b149c0117015014a912b510331942016f191915160ab40aa519300080111a0aa800f1191b12bb14f50b1c0b1609e709e4194801a7190418ff15d0111d156210340497049504921934193318ed11c911c211be11bb0b1b0aae049e19b213d819270e3c0d59049909e00f030f6e0f710f7a0f8213df16d11419141e1929141d193e0f7f0d690f7419a0,0x14c125a14d0191f194b0d351765190e01c217550c5416cd0cee09a8194919070190190b18fe16dd0715175413d313d0101d0cea091d0193004d194d012d00e4006f0d90043416c916f3159d150a0c570d4e09aa10100cec094300b2002001ae019a0161015400e100af00e90972043e16f210771072106e106a10660fca0d3e0d990072019f00e8191109d70963173116ca10f510550d430da318ff1948191b193904920489042f0ea615d113cc10f40b2017dc00cb19341904000f17360ea111bc076c02c401b9012800fd005512fe12eb10580fd10b6702f4011f008e001207ad07a202f502ce07740e2a0e350e391a121a181a1b,0xba31ab1]))
(.node (.leaf [0x998176c,0x4f072607340083010e02880f86000b00dc027909b2001d0074040209ab006200af08380d440414015000ee0aaf0aa8008009f8007918120720004e072300ad09a004810073002409a3048700da0f65049f014000260449044704450444140911d004ae0add0021013700fe00fa0ef50eec0451117a11760b7e0b7a00d300f7009114110f000609060004200189003b001e06931574119d11830b85090308f9044d03ce03c90042015e006d001b153b0698138d0fdc08fa035f03db015a012c012a00e20017005d131d131a13170fe506350630062d022307c50121003e0006009212cb0fe1057a038a022d0b2a011b0037008812ee12c8058c117e152212cc0b35011f015c015912f9100710050d8d08e806a406a0041703d2017f00e300b2006c004313b613241233122f08c708c01367098d097b097008ea08ce069a06830483039f015f0108006b012500720bad0ba707c7049404660cc30cb40cb1096608d4023500930025002200a709d80964069e02ca02bb02b802b5158715400cc90076000f018a06ae05f403d602bd028214800044014213dd06bb1483012e15881579019c0de3089a0c6c0c660c630191141e00bb006800a40f810f7c0ba60b9109e2049b01380824081e081805e605db05d505d1035e00db17e80061003a0f6f0c70081905e1010f009905380535052701fa002f02fb02ec001207b007a1079902f8005b03bf03b903b703b303af03ad03550226028a063306b60caf0d590d5c0d691770179617a417bb17b117a717a31788179b17cc17a91777178d17c017b917bd179f179e17d217ba17a217ce179c178717b6178f1778178b179817cf17c6177917a617ac17aa177117c917b0,0x82401250061136c0825018a014f169810cb01ac00eb1531081a0a9714ed01590099007f187b11660bfd0a9817ce1778177c179717ca17c9,0xd317a9,0x14130197013716e80ef9019b191314cf15e30eec014c016919161610140e14cb1210120f09020f99193819370153010518fb193f12631260125d120c0ef605f715e41211169e191f003b1947018b0cf50cf0154a03cd172916a8190b1931001b01af0ce51599159615470ce303c815ef1912016100b2001e016a0d380d330da90be010aa109f0d7e03ec04250a46190e0110009600e900cd007b0fee0fed08fb10de0d320f9b0bd70751109d09b10aeb0a2a041c191700ed00dd0051014b18fe00840064142f0c930c870c80060209ca04be04af12880ead0d8d0fd409aa05070505013b00a5007500270154012a00e100af002d0947094409250921091d04b81076106c1068106410530fdc0fcc0d400d2e050d055804fc006f00e800330737073608b708ae10e410540d4205610309005018fa191b00130462045f0459184d150614c6159210f4074504b2030f0667066117dc02b4017f193400590041000f164e15cd078e0c200bd1067105600c6e0c6b0c6802c001a700cb009f1869004911c711b10e9b0c23067a0a0d06e600fd190111570a07191d0bff0bf71749190601c3088e088b031613e1109917e71927031b06ec078a092e09bf0c7e07400c00126f12720bd50f080f1119140f0406f619290f7509d702b9048d03d805f618f706ae06b6151919301992049818ed049109eb09e518ff19870f83049a1980192018d118d019780d5909e10d690f7d,0x9531a0d,0xa80ce008f2016c19a2113f167600f40187113d1526016101590cd215901736152f1864193401b9194409e315cf14ae14ac15ff18ff01a717e60198195d151702f90dea0a6403051930006100bb0013089d0817037001d00068001718e803c0035601d31593169a07a608920ae40dd9035b05d8046a04710a9a0de2116511681171081a036a08c707ac0821113613f911eb1405151615eb161b16e716eb17031942148213d9145b0147149714770c6e0c7902fe09671336133f0433004606ce15621133121b0106121f12150f0b15fe1939160612790e9100ca0e990185165f127f0c0419060bff05e10e93073f14501451013e11b500fd11ba193312f6011f0cc1190a1a8b13dc192713df193e185d0e4806d317e408c318be0a080f190e3712fb11590e3300c31a8907430050073a045e074111620ccd19110cfa190c0d08016e160901b5134415df1174147a192b0f17147f1a84116e0d0619220c7319080c7419361276116b191d04701a8008b505ed1a8e0d9e19200f0e191408bb18fa1a9204641a8f1a6c1a661a751a691a741a641a651a0f1a6819621a6f1a6d1a7e1a161a1c1a731a7d1a71])
(.leaf [0x15a8176f,0x7509d4066901640041139e067d012b1852158e0161113d00f41138013b09470921066417bf,0x6eb00b00049187a00d417e90f800f04031e00db18d206f001cf01d4183318cf0c000d9d12751278127e010f18d118d018ca17b7179517aa1771,0x15ce01a7193411c611bc00fd195218e21519151314e314d7129a0b1e0bf605e219301906150514c506c7089c088e088b07f6017f0046006813dd13da134d110f109a06bb06e906c5031903110309192700490013149811de0ea412f712f112ed10570fd007ad0d640d580d540c7d09be092d078906eb031a0147011f190f147b147813f2113606d30cc40cc20cbc0cb30cb00c3e096808d60771070506cf062802ff0236192b0133190a16971694159415861480142b13f712fc0cc8193b18dd16cf15bf158815791495193e141f141d141a11a119290e450e3e0e3c0e380e340e2d0e290dc40ae50a330893077302cd01d418a308c4030007aa0ba10bd30f060f090f0f0f120f150f1d0f20053807420b6a0c010d9f1216126b12711274127a189018c608b602b504560459045f04620468046b18ec046d046617e9183301cf,0xab8190300ec051710d018ef0127051d12df191f011e0260025d0cf0103e0009190b00e713770d3302610ceb12e40fbe0190190e00e90257193300e0157509b409a90ff4102d00190b6b0a03015e18fe1918191901f5008e1901094e091c1009103317fa0533052d006f01980d1c015018f0092214e8190d14f6052f00a5014f067301a7190408bd08b716f014eb004111c60b1918fa01b5194417f200fd184d1173117011580470191d19d219d107da0f390d800ce3014b00df00b20fb4087d1988138e13190fd40fce0fc80d520d4b09aa092a09810972069c03a10154012a00e100af0072106c10640fcc0d400d2e0c8509840aa603ff038600e80080001d10e710e410540d420aa80412191b16cb10f7194815d115920c2b0496193418ed09eb09d70963069d0491040b092f0c7f0d5a046f0f21,0x45018eb190204510515191318ef0ef7051e02540251191f00080d340cee0255024e190e190b001b0c7c08f808f5044c02a400a518fb000e092408f103d401df01dd02ae006f00a8004318e919040ced094403ef096b08ec069c01e7052f00e90072005518f00cd00d7e096f02f102eb191800b200120cb50cb2096702fe190a1a520a95007f08ae046b18fa18ec184d05cf05d9077501e50a98109919270e3d0469052d19e518ea03c305e2191d0e3205eb1a151a121a161a1c])))
(.node (.node (.leaf [0x1742176b,0x17fe070c14fe00c601a003a40a670eae00bf007d00cd075207480e6f005100c704b103e60027001b04b503e1006f094d015e074a04bc11260084008200f20a2c0a290b95007b00920a4411200af40b8c0d720712016a00fb00d200b1004d15e711a40eaa0e640acd04c10976096e071e017300ff0072013b145f11d90e0b098a0754113911320e030a77013f00f4145d113f0cca016c00a8170816010e7c0cd2019e00e310a910a50ff30cd50a3b03ee00e917ff1800092e07720a320ae40e2c0bd50a9a0e62115c116509660cb417b817ba,0x17a0b6f14a6008e0149127b0b68053114ee149b010f002f18810c01053500db00990896088c0068031803140013156311bb0b6c030a015d004915200a0c06e5052c01590079116f116611570bfd0a0700f61880100510020ff901cf01d41873031c06ed08b408c617c1177117b017aa17c9177217c517b117cb,0x8117b3,0x52b18f0190102ec0a0817e6191d02fd187b190a12f40cc20f21,0x1901052c01ff18f019ff19f601fc003a1a02053805ec0a08191d0e3119fb01c803b318ea01d318e819fc06ef188708990e3b141c193e0f7f19f70d6a1962,0x192d14ae07b201b9005b12fe07ae1703011f196d0cc21929190a141d169b12fc0cc8193e193b185d0f1f0f1907ac07a60e370e481a811a7e1a701a161a73])
(.leaf [0x1083176e,0xabc0081015110d30ab90f9300ec00dc09b309b0025f007400090f990263063c0205019200ae003f000415990d2e064202100209016100e800b1003b001613370982096c05fa103615c3038f033a0122007200e70164001905ee05da10500c7a0603021309d609c3038b033f003a015e00a5007500380fbc01f703b4033e094e09240920091c059b00e00003001a006f0a0301ff03b9102e0fb910440668066205cb05930079005b00e6012800410a0b07b30aa510350ea1067201490080015d00cb009f149b0aaf11ba0e9c0c24015000fd14f20ea611c3139e139a132b067d05f501f9019f0175012b0044002f08bf08b908b00598159014980da30da00677049e15bf157906bb0bf505e10534006b0165014700b300250191012e009916f714aa057f038909eb09e809da096306ae0491141d089a088f088c019c0037007617e700681483147812eb1058058c10f610f410ee10e910560aaa09e403190142011f00ee00131594148012fc0d610d580c7d09be092d031a018a00b00cc90cc20cb00968058901c601c907a608920e280e330e370e3b0e4807aa08ba0f150f1d049a089709e10f780f7b0f8005380c010d9f127a010f0f6f0f0c06e506e9004917e9031e1841183301cf01d406ee17b317c3179617a4177a17a817a017b817be178617ae17b117ab17c1177217c5177617bf178b17b017a217d31793179c177917cf17c917c6179e178f179817bb177817b71771,0xc75016800a412770c71010f18c20f6e18c108b4006b184d0f1d18bd0470116a177317a6177117a2,0x19d17c7,0xa4a0085007c0b0b0a5b0155016b119a0f6815f300f900da19430e8c146a0f6514de00c90140192e073107250e8d11d0150c0a880a800b7a004f0100191e018319020091119807330c1104ad049f0e8b0a820601192c191f009c18ee00c8003b14271409044a0f8f0f870c1004ac13710e84102b0a85069305f0192a013718eb1916012600e500420efa0ef80ef50b77045109b104a410b810250689191318fe00ea0075090208fd08f8044c063b03ea03cd098d0987097b0960068318fb18f6001b0072136f08ff064103dc069903d219280136009d005d0043148613e80f970e8e069708fb14040e690b8a07c506a1193f19261917013f00c60092169e13730e6c0590142614120f0111e80c1409d3131a0fe511db0e650b92018b018200380ba0193a0164192100ff00f216a01312130f05a8017e1573156c132111e011280b8419400120162e184b13ac13a413060e880df60177192500be162c13a209ff1325145b017a1901015f014714a40a090bad07c715bf15881495192d0093193e14aa02cb141d11251942000f19900e4802cc00c319c2118f118800f809ac118d0f3700af010100dd1769176616da16aa0d901543153b1535101f08e713ce06ab1079106c1064105c0fdc0d400d2e0a5409840be40bdd0bd60bce059d194f0193015a012d00e80096175d1635159f159b1598158f1548153a13c913ba1353119910c810710be310270e910e8f01b50161191a00ca1343133813351331132e10b30a970a92192200f1007f12a2167813400b160a8c076c014f018719040c6c0c6610010ffb0ff8167a163f0c200bd10671052f052604ca02ec1908191801b8009f18f015e00c75152a15261522130712f110030b3514580e950bfb0bf80bf505e1053419360159013e19061173116a116711641161115b0e610de10bfe0b300a9905eb191d19c11658164d14ad151c14e312a7129a089e194419301483140611ec1193077c0de817191711164e16471517192b013301a7169b1697169415941586153f148013f715ce15cb15c8159113cb111d0c2a0aa3055d193b19340080196c0743073f073e10f310ef10e710e410540d420b070aa8056106ba06b806b405f403d60050191b18f71284127d12771274127112040c010742053809ea09e709e409d9096506b0069f192018ff0f7d0f780f6f0ed30c170ba50b9009e10897083106b609bf0d590d69059808b608c108c408c8067c0aae0b1b0b670c25115911b711be11c90b6b12f5155b155f156202b7048b04910494030007aa0ba10bd30f060f0c0f120f150f1a0f1d0f20184f02b5045f0468046b18ec045518ed19c01520193311bb049e19bf046619b4,0xc34190900a00c9d0c35191708fa18fb08ec00720967190a1a420d390d340c55190e10781067105f0d2d0a5304f800e80aef00840c860c820c7c0a2a080100a5007b005f062112500f430a4013490af1096a08f1093b0927092408cb054a054518fc014b012300f000a8006f0031117f090e10a2109e1092108e108a10110d810ced0cd60944055004e404e2193200e9002b155a138210060ffa0ff20cd00c4204ec19331918152c1524152010010159014f172915560b380b2e0b2b105710cb19470088011f1749191a17371225121d12190c390b3304f014c512f901c314d7129a0a9704e901b90106017f16d41682158a157b1930007f14af121e0a9e0d9b0d980cce164b152e14eb19e10f7d0f6c0ed30b90046b192d016e19111944191518ec1704170114a916080da40f210f1c0f190f0b0f080f05046f1942193919141482147d147a18d4192b18be169a16961585153e147f12fb1a41089c088907f605470377036e02250068001713e113dc13d913d51363134c110e1099089a03bf03b703550226192718ea0e4a0e470e430e400e3d0e3a0ae70a3503c31a3d1a3c08b708b108ae036918fa184d1170116d11670b300a990470191d0bff0bfa088d19061278126f12140d9d0c00192019b718d118d0035b05d805dc05e105ea1a161a151a121a1c,0x17f1aa31a9d1ac1]))
(.node (.leaf [0x910176d,0x17e50e410e3e,0xd8300ef00b210f90970012c007213b90992016118a2110001320ea200cb082f00620796005b07b301490fc100e015230fc50159166f1526018718a113b71325134013371333133003ad015f0122001a12b412410bad05ed05ce03c001170093003a006812b70c7805e502cb0c0405e20318031401f701f301ef016f00a4000f00990013000315d50c7402c005340525030301f801680049002f0a0c0a040a0109fb06e5052c02000079189e1751174e173316cc15b601b115d015cb13ed13cb111d016511ca11c611bf0b6409ec09d90965069f040d07430737073600fd007600500de30dde0a6406d1049d0492048c0489042f00bb00251729121313f913f211360de810b7101a08240b1e0b180b120b0f0a62049801ac013301250086169a1696169315931585153e13f6136c145b11de0ea40778076d02c6018a014700551481147811ec1193077c13db13d813d4134b110d10980142012e0e450e410e3c0e380e340e2d0e290dda0ae50a3307a70773188718940a9b0a8f0a8c04e6007f1174117111651162115f115c11590de20b310a9a0a0805ec00f61893141f141a1125013816d01589157a1496141c01910f820f7f0f7a0f770f740f710f6b0ed20ba40b8f09e00896083000db0f1e0f180f160f130f0a0f040bd40ba2082007ab0301046a0461045e045b045502b400d4184f189212841280127d127712741271126b12160f700c010b6a074205381891188f100c1009100410010ffe0ffb0ff80ff30cd10c430a94090c04ed037600e308c808c408c108bf08bc08b6059805800466036b188d0d6a0d680d650d5a0c7f09c0092f06ed0634031c00b00cc50cc30cc00cbd0cb40cb10cae0c3c096608d4076f06cd02fd01c601cf01d41833187317bc17c017c117be178617ae17a617c9177317b017b1177d17d3178f179c177c17ce17b41778179817cf17cb17ac177917aa179517ba17b7,0x12417cd,0x15414be106a014b00e80a4311140c84007b00f000a50a4411150925016a0164006f1197156b094d066114c700f8015e0041019e108d0a3b1196139b05cc143600e9015a1925003a013b108f0c8f1331132b05ed11390123192200f4158e153913521336113c1070016119a21736140511eb119201b9192b169a1593153e147f193b19a108ef00a10c49011b12c9011f12eb012816ec15ff16760d6c16e316e216a208330de30198018700b71940006200bb1522130712cc14e916790df90df70dbd15ca15900838100d0ffc0ff40cd20c44037003580c3c09660159014f01b800be01171934015019180017190a0e910e8f1657152f14ec163f0dfd12b810f410ee10e90a9e0a9308c00597036a06cf00ca1944017a016f191b007f18fa004616650e990365152012f514ae14ac14a40ab30aaf0aa8046a046406c4018500611933192d008018ec00490c04081a0b700b6c0a0a09f806cb04680315030d01fc1906008e19010013000305340531052b030301f8031b06ec092e0c7e0caf0d590d62031d08300c160ed20f710f7a1380157b15c1112411a014190b69126a12701273127c127f1283046f08210bd50f1c0f2105ec0a080a9a0bff0de211651168116e15d515df02040c6e0c730c7919080c740c7018200f75195606d3113613f213f9013313f31936116b14160f14191418d416920f0313f01929141d193e0f7f0d690f7419a0,0xf5c018f00d916c40f5b194d01540d3c16f41288190e019a01100d2d111214670da900e800f0013f19120fdc09ce09c613c50dae0754075019170075192600510fe211da091f0c8b0c8211150e100e0804af012000ff006f00a5016400bf0027130e11e1094f0c8c10e10d3209cc0acc0abf04bc015e011d00ed0082104d103b10370ac500e70d1e0d1b190d074604b313b6139f139b13050d240059015f19250e010ac4078e0bad13a300cb0093017a12d910d710440e9c0bb20b6e0b62012800fd017f008e1560137911bb12f710570fc00fbe082c08291933011f00e00062155b0b28158712fd14a40fc1079801870088193b192d17dd110f152713080fc50b360cc80cc10a0a0a0109fb19270159190a190115bf15881579137e0e450e3c0e380e340e29164d14ad10050cb604690463045a193e00c31944191818ec141c0e3f0313030f116f11661163115a11570e300b2f0a0708c708c008be08b808af046519290013191d18fa0f810f760ba60832031f15db1415116a0f200f1d0f0f0ba108ba046d191518c218d0127c12730f6f0f0d0b6919201a22133e132b0ff719220c790c730c6e0c6508b6190805de05e505ee03ba03c301d018e801d318ea03b31a141a121a151a111a1b1a1c1a161a0f1962,0x13dc1aa0])
(.leaf [0xf81019100db141b0f740138141e019c0e4800c317e214ab01490f180f0400d417e103c003c3177917aa17ac17c617c11795,0x58c011f00370cc1058800a712fd0cc9179e17b6,0x11d6017000fe126211d20694010e016300420cf009bb05af00a90074003913850d390d340c40064e0343012900ae00a10040001613020d2f0d7608ee03930347012000e800b1006d0019005f0cdd08f30984096d08eb03a007fd00a8007200960ceb0cd413090c840c7a09c3068908ce05b405a7059d033f00e9015900a50075006c00380ff20cd00c420fc509240920091c08cb064a059b03f9038400e300e0006f001d100104e50fc206680662059303fe01f7014f002b01490041000314eb04e70a090a0305d805d205ca01fb01a4007f0079003a11710a9a0a0805ec059808b008b908bf08c108c80bd30f1a0f200468046b0022046d046607b3033d03ad03b103b303b7001a03ba177517cc1770179117a417a817b8178d17ba17c117d917b117ae17861787,0x190a0cc902fd193b0012148002f7192b005b148303ba194218ea0e4807a601d200c318e806f101d6030007aa0f150f1d1962,0x3020001f81901199d0a07,0x3a9183700e80f3f10700114006f01610779094f13350055015e19220765139b132c00591925152a1522078e067d015900cb004115301591040e03fe19441934001d171115cd0ea7040101a7019f006214f614f20837183910e910560aaa191b13b613240288027c09e3015f000b18ff16500bad0ba907c705f402820491046c017f009318f718ed18ec12f812ee12c808c708b808af059702ca02be02b802b5011f18fa000f0cc10cbe0cb50cb2096708d506270580057d057a038a033102bc190a1863159515870cc91498145b11de193b014714801477077b192b168015bf158815791495137e13f216f81483193e0133196d141c13f0192906f602c1004913dd13da13d6134d110f109a06bb03140310030c03081927001307b307b0079d089a088f0317005b00680e440e370e2807a6077202cc0bfb0bf80bf5088b081900c3190611671164115e115b11580e310de10bfe0a99191d1a6205300527052102a918f019f613f50a0d19360c740c6c0c690c630202190812760c70053719200f840f810f790f760f700ba609e208980832049b19151a6101fe05cd05d105d505db05e305e605ec05ef01e50277033d03ad03af03b103b503b703b903bf03c201d101d618e801d218ea03b41a58046d07aa08ba0ba10f0c0f120f150f1d0f201a5b1a151a1b1a121a111a171a141a0e1a181a161a101a1c1a0f1962]))))
set_option maxRecDepth 5000 in
private def hintsBasePart11 : Table := (.node (.node (.node (.leaf [0x1721176b,0xfc700e0015908bd0b37006b0088152e08b50b2801a400a4008e0fc2117011670b30020407a2079e014900f60003005b0a090a070a0301ff02f6007900120532052c02ec01f9002f17fa17f90c6f0b68010f088c08160f6f006817e8141503c003b40138001a0e3f089407a803c200c317f80f210f190f0e08bc07ac046f030201c60d6906e606f106f802e3030303160013030d01cf031b17a217d917a617c117cb17b117b0177117ac178617ae,0x152f01a40159116f116617d9,0x6d178d,0xfc11a711450bc5014500f500951438114a04f6013c002c148d09b9143f04f5193f18fe018b007c0a500d7c094b091d154a114e16a80232022900e41910006f1441193101af0006101409c1091e018e0fed09aa16da10210625022f00ea00750d29191700af0193015a18f410b20989096e0962190d0fdc0d400a5404f9159d15991547153811a90bca061f00f100720673066800e8016118f709e50963004110540d4215c9159210b61019062a0fdf06b118ff0b17172716a309660679191b19341924011b0093183119041947190a00fd10ee13d8136212c810580ba70a8c166e100d0cb6155e11bb115201501927011f0108007f01871918193314ee13dd12fa12350a97152812ce10040b6b017a017f191a0159008e1641164f15ce14f610cb0fc707ad07a201b801a7014f00e018081749166417161711164b152e14eb169716941594153f14a50fc2082702fb046b0de70de406d201c301851944193b192d006118ec00bb0a0306ca151c15191510111b0f210f1f0f1c0f190ba30821046f06f3133e133513310375036f02221901193019140049192200171704151414a90a0c0c790c730c6e0c680c650f830f7d0f7b0f040ba509e1049a030a02e305ee05da05cc035d19421936186919150013003a141f14170f7606f80816031703b603b4035602271929006818ea0e490e460e3f0e390e350ddb089403c200c31882197a0c03088b081905e11906053505330530052d0305031b06b606ec092e09bf0caf0d590d5c0b680c000d9d12751278127b127e1282192018d118d013de141b169016d2047005eb0a990de1115811671170,0x18e801d001d3001318ea031603c2188700c30e3c192719fa0e30031c0d65031d0e401929141c193e0f7f0d6a0f7419f71962,0x491a101a791a7a])
(.leaf [0x107b176e,0x15d155b13820187012916780d7701ae00b1124d09c3010b00750f5709c600d90f5c0f5b018f0154051016c41509002d01c104fc1077106a105e050b0c9a16f4003300e800a6019a055b13c513c30fdc0c9e16120080012c00e201710ab4167e131a0fe5130211e5091f016f01880121012000ff006f160d15711322130e11e1094f01b6015e13ae139b13050c370c34012b00a0132b0c38012201060ff90b3400e30088152a15261522130710030b35170b16f116130159019f153014f309f801a40150007914ac149b124301ff0149000307b2050105ee05de01fd005b003a03ba03b4001a183a173201b110f810e9105607a607aa0f090f200f7c1215127305eb0b30115b15d715da15dd0c2f0c7700a40c760168116a00f604710022046d0e3012760c70010f0f700f0c177217c517b8178217b517c017b917bd17bf17be17ba17d917b117c1178617ae177d177117a6177317cb1787,0x78c00cb00590e9c076600fd00550ea40b1902f101470086001214970b1e052f02ec01910156002f0e360e2b02ee141b089c052b00c30046013817e7007906f006c514170a0d0311030500490168001317e90c751476077a06d30f7d0f780f75031e046800a40142013300db002208c208b40f170f140f05046f006b00d4184d0d64078906eb031a18ab00b00cc20cb0077106cf02ff00a71691148013f70f1e0cc8018a18ba0c7318ac01cf01d4183318a304701158116a18820e31187317b4177917c417b017ac17b1177317a6179817aa178717a2179517b717b61778,0x18a1778,0x9e1191518ff049b0493,0xbcd009501810bc91393123d0bc70bc00161012a010a1916159e139511f70eec01930103191316ac0c480cbb0c5b11f80f860f01193c00a1190a1907191f193a0cf60cee0c3f096808a812400d351572190b007218f901ae190e015e0cea08f808ef08eb0349107810630d2d16da16b0158200e418fb001600e801af08e108fb08ab0c58034d0af016e1006c191700e100b9008419400cac08d20c810c7b0a370a2d0a2a034816b61675190900a5007b005f193d01870dcb096a08f10928092508cc054b054616b9167b1525012300a8006f0031194b0159109110100cec0cd50943054f172a17280c350c320b3704e404e200e9194700a00088002b0da60d990ccf12260c3a0b3404f119110106173612ed10570fd00da3121e01b9011f136a10181939016e169a16961693159312fb1924147e147b193b14b012fa0de718d41a3a1766194f176a174a01c31704170113e1134c10991942192715ce14ab14a612450fc314c613dd01a7192d017f1711164b14ac10c90aa004e807370736198a1944191a00bb007f005014ed10cc0de806d3046c0460014f013318ec1518111a0b1d0f1b0f180f130f0a046e03011930191416d316d016911681157a0f840f7e0f730f6d0f050ed409e2049b17e819151a37082608230061089c081507f605470068100310000ffa0ff20cd00c420a9304ec031702e4191817e906ea06c602c313471342134013371330132d0ff90e1607ee00491922141806f60c780c720c6d0c6a0c3007391929190815d7141713f50c760a0d1a360376036701d0001718e80356033e01d318ea0e490e460e3f0e390e350ddb0dc50ae60a34089406f003c2035b05d205d805dc05ed07400b680c6f0d9d12141269126f1278127b0535081b088d0a990b300de111581167116d1170036908ae08b108b708c218fa184d0470191d0bff19060c00192018d118d005e119b705ea1a161a151a121a1c19d01a101962,0x1081a7f1a191ab9]))
(.node (.leaf [0x44e176d,0x115700fd00f60b1a0aac04700086008000220498049604570025049200760e3606b000c300440e3c06ba17cb17b41787179c178f178b,0x13c143a11a6017200fc15f10949144411ab016b006f018e0162161715f603e316bb10f1065c01af01ad001b01c000ee004016b116ae03e613b010e5065f018c00c7012b012a132810220a6a15f8039216ad1582139a138b094c012100e4007d01ae00190195015e1544131e10130a72107803aa0fb703ef0b9d015a00ea00e800df00e90092153711a810c5106e14640fb10d8b0d7f065606a00161013f00b200430cfd0bfb0992098b0988098409800971069b03a0035700aa00990072001705e705e205d905cf035c178117bb17d517bf17bd17d8179217c9,0xee17bb,0x12c2011901540fa00d49111100dd00af00f0093a092a108e006f00e909470d7e013b00b214340d92199900b70d9b0d980d9519110da41939147d192b147f193b199a0dbd0cb309680117190a10fe05660cc001320033011f0ea20c20055d07ae00cb009f0080197511b10e9b0c230aac079600fd0661006218d8004104040400001d10540d420561041213f2191b0133150512f915c9159213ee10f413f40c730c6e0c68017f193419361869164e15cd0a0d01a7181f171205e705cb01fc1944003a116f115705ea092e0caf0d590b680d9d1269126c1272127512780e2b0e360e3a0e430e4703ad03b303b508310f720f83199003020f050f080f140f1f0f2119140f0413ef06c306e406e703070313088e053505e30bf71906088b0c001099110e13d513d913dc15191930089c0f7d040b096309d709dd049618ed0491049a0ea4014709e818ff06b018f706ba19270899006803170013030a004906f606f106ec01d118e801d2031b089503bf18ea03c30e3d06b609e11497193e141b19290f750e400d690f781962,0xd611a0d,0xe401a95])
(.leaf [0x15b0176f,0x58c011f00370cc1058800a712fd0cc9018a185a0f1e00d408bc0580179e17b617781795,0x182300d40f800f0400db18da0e3e18d918d018cf18ca17aa1795,0x11f130007ad01b9005b14af07b2192d170114a9185d0f1907ac191408bb18fa046418ec045618ed049318ff06af18f7061d18f4062b1924169a136c193b13620cc80cc10627193e1927190a188c0d6a0d650cb006ed06b701d418a318c6049909e00f030f7f195502cd07a70e380e3c1959195a,0x192b14810e42193b00c316910892193e006813de089a089d1927193013d80b1c1934190411be0b1b00fd19da058e18f202c502ba057f000f18fa11c302c8046602b61939009318ec0da406b2049d0497045602b8191118f718ed09eb09da06ae049106b70d650d6a,0x1927089a0e3d006800c318821a5a088b19060c00192019de18d118d005e303bf03c218ea03b41a581a1c])))
(.node (.node (.leaf [0x6ad176c,0x2ee0012004602ed06cd002f00a706cb052c0cc90079018a0a09147f0149014214ab1483019c141e013817e80f1e0f180f160f04030100d4180a0e4817fc0caf0d6906c606e606f802e303030013030d01cf031b17b017b617b1177817c1179817c617ac1795,0xe4000c301380e420f74014200db0f170f0500d4188a187318790f80141c147f018a18891691187e17ac179817aa17951778,0xa91791,0x950bc507e200fc005e114507db00f500650e4d11a70bb9085b037e00c40145009c00180ad30f900c0e03800083191600e40adc148d0f99101400ed193f00ea0c1509ca159910c60bca05c503df03790164007501610039001b0863111610b10667133507ec05b4037f035716d70e52192500f000411922006c0017194901290da00d9b067a05ee05d4035d17450cea15bd1384191100fd003a01af190b016302850da410b2115705ea10ab108c100f0ceb0ad603ed09bc09b909b1000b193900f1191d00e918fe027f0b1f0b170a0801fc0cf105c809440921091d08cc18f51904190100031921006f062f052e052b01f81582156a15671320094c109d18fd18f0015e014b11ab09a610d50532138e13190fd408dc09aa01620128008e012a00e100af155a15581382137911520b6c08ae03691064106010530fcc0d40193318fa00e81524152008c712ee10580fd11989011f14c612fa017f198a040903ff001d16cb15b510f110e710e410540d4204121948191b15d1159210f4193413db13d8134b110d1098192706bb06b503d818f709eb09e506ae040b18ff198707ad07a21985198219801749169716941594153f01c3077a193b151c1519151012a7111b0b1e17e50f210f1f0ba3046f193019141704170116fb151414a915e00a0c0c790c730c6e0c6b0c6802040f830f7d0f7b0f780f040ed30ba50b9009e10831049a01ca01c7194219361869191518e8141f14170f7606f803c503be03ba03b603b403b203ae0356033e027801d3192918ea0e490e460e3f0e390e350e2a0ddb0894077403c202ce00c31882197f197e16d216cf1690168015bf158815791495141b13de137e028a063306b6092e09bf0d590d620d690b680d9d126f12751278192018d118d019781962,0x2f00012004602f61a08005b0dd907a6188703ba031602e306c418ea001306ca19fc01d201d0190118e80a0c01c8193619ff0c74020219081a0a035b01fb031c031d14171929141c193e0f7f0d6a0f740e3c19271a040d65030107ab05380c7119200f0d19141a050f030f6e19f70a08191d1a0719fb1962,0x122c0108192d12350a09017f190112f906cb011f00460cc206cf12fb1a840e370e4400c31a891a191a7f1a7d1a7e])
(.leaf [0x1169176f,0x1004015900e315220ff7015e0122139c132d17ba17be,0x920b9b0b8d015e00d21535094f0ede06a20441015a006f013f0043002008e609270e0b098c069c043e006c00a600bf0072153908df0c9706a403a2039e016100e100af00191590106f0fcb0d3f03aa016500e810f410560d4400ee04130386001d0c3410570fd0040100a0011f00620c3812eb08340106012812210ea10e01016e00cb1607078c017500590b20078809eb040b0086007604970492042f17dc000f02c4005502f40012043102ee004606c600490d610d58092d06eb17b517d317bb177617b4178f,0x1bc1780,0x1471016c01410a7c0e2711dd007d00c200ff0a5f0e2616020acc0084012d019e00820af513c914360e1e0a750ac500fb0161013b00f400e7111f133513f21136104500f219220133012811e01128104f0ff8159413f712ea015e1918193b011f139c132d10a710a310950ff20cc90cc2192500e9190a0da00d98162315fc1473076f19ae193900550b1f0a61076d190419ca0c8f0c870c80074c09d609c709c305a905a505a10590038d00a5007500380b6209450942093e0923091f091b05b8059a008e006f13b210fe066b0667066105920132004113d6134d109a0bd106711927009f0899088e006803fe03fa0385026914d7089e1451150514c5001d1930013e017f0ea20e000ac3040f170e15170dfb0df80df60bb00bad086807c700cb01a700be00930ea415ce159113ed13cb111d0aa302cb02c7014719340080000f15bf15881495137e10f310e70db40b07041206e702c0193e191b073e07370736004903d6141d11a1112509ea09e709e4069f040d00500a0209ff09fc06e618f7192918ff0462045f02b5190119c50f7d0f780f750f6c0ed30c170ba50b9009e108970bf618ec0f1d0f120bd30ba10b4c18151915190604940491048b0455164d18d11277127412710f700c010742053818ed15311523130808c6187b189119c0015915621520138112f50b6b11661160115a0e600bfd0a071933191d11c911c511be11bb11b711b3115911350e9d0e220c250b670b1b0aae067c049e19c80e450e410e3e0e3c0e380e310e290ae50a330893077306ef02cd19c406b606ec092e09bf0c7e0caf0d590d620d690466059808b008b608b908bc08bf08c108c408c819b4,0x6e61a250049052f02c102b41904000f076c02c400550771190a049802b90cc8077a18ed193b192b049c0f1f0f17046f00fd191419800f04049a1a101a16,0x11701ac9]))
(.node (.leaf [0x918176d,0x39d00660019087a087303a300df00bf097e038407520072001d005108cf040004b1006c0041002708c9066104b503ad03b5,0x3ba001a005b07a803c207ad00c3186c0e43057f0142006b0f1508ba07aa187318a31480178617ae179817a2,0x1421798,0x8b418fa18c2184d116a0470191d19aa145b11de049e04980496048d0430014718ed09e909de0964049218ff06b005f603d802bf18f713e113dc13d913d5134c110e109906ba182019271703170016fd16eb16e7161b15eb151614ab14830e440e3b0e370e330e300e280dd90ae40a32089207a6077206ee02cc196d00c306b6049909e00f030f77195613df14970e3f0f751929141d193e0f7f0d690f7419a0,0xfd18460e9c094e00cb078c006f0ea80059184a019f076610e81055176414f20055191b01b90150077709e414ae149b011418ff192d0ba904911231122d009318ed010808c808b002cb02b9150514c512a9123418fa000f017f057f02bb12fe12f8186c011f14980cc20cbf0cb6096808d60147190a1478077c15940cc8192b193b170216ff16f71482184419420e480e440e370e330e2802cc00c307b207af1974005b02f502f1001213dd109a031102e61579149506f302c119270013193e0049089a0317141f141d06f802ec006817e718f0088b05341906116711580e310bfe191d1a2a18150f800f7b0f780f750ba509e10897049a0c6c02020f1d0f150ba108ba07aa046d03001915190818d11277127412710f700c710c0105381a2905cc05d405da05e505ee03b603ba03c003c301d001d518e801d318ea03b31a121a111a181a191a161a1c1a0f1a101962,0x16921aa8])
(.leaf [0x1154016d00f5125f114e010e015b0d34135e05c600ae012400390d370cf50cf00ca805c7012c00a900a6012113bb1359134f0cec0928131f0164012d012300e9006f015a158e13c813520d2d0d7f0ce209d4091f08e808d205b5016100e800b20075006c13351331132e10540972096208d0012200ee00721344159213cc10f4105905d905d301b50165011f003a16fb111d12f611520667066105ca019c00f1015d00411516111b11ba02ac015600fd000e0b1c0b190b1602ae008617ea16ec15ff0198100a0ffc0ff40cd200e313b6132409e609de09d8096408c007370736015f0076006b00500bad086807c70493046a0464045e00930025002202ca02b802b5092e09bf0d59046f08bc0ba31774177017d117a817cd17c0179117b517bd17be17bb17d317c6177217c517c417b417ba178f17a2179c1787,0xe10fd30fd6011f014b12501271186a129f0113091b12960a410a3703e0006f014d010c007b001b09390ee20ed1071c071507110db20a79035800dd00d2004d00b5007d00170a3f0bd70946044104340db10a710d860d83035b00f80096013b002000ea00b2003a0fa80fd80db3118c0bdd11390e030bdc0443098a09870970096005fb05d90193015a012d010100f40072159e153913c813b911ef113c0992016115c7159013ca01650fad09ec09d9096502a301940076000e0f6b0ed20da509da02b100db00b30f700d9f010f18690e910e8f00ca0e9813ab139e139a08610185012b0a641666170d133d133713331330132d0b2d00bb01c501b60122008806d006c70431176a175813430b320d000cfb05e8004601c301b5010600aa02f0151a150e14d51298053202a8160a121f0d0800120156002f016e079f02f60b1e0b120a62053002b016070da3005b00860175149d07b3172912260a9e0a8f0a8c090911cb11c311b111330b65014901ac007f006e00fd0a090a0009fa13f21136100c0ffb0ff80ff30a94090c0376049d04970489042f0079013300e300251174116b1165115c11590b310a9a0a0805ec08c408c108b6036b02cb02bc02b900f6006b000f0470046a0464045502b40022186816ff16fc15150620019c003d03031483147e147b147811ec1193077c061e05f503d700130142004406f406e506c5030c02c20f180f160f130f0d0f0a0f070bd40ba208bb07ab046e03011696169315931585153e147f13f612fb13e113d9134c109906ba004900d4018a012e0d680d5d09c0092f06ed06b70634031c185d16d3169115c01589157a14960f80136d136410b70de7062b00b01842183e0cb40cb10cae096606cd02fd01cf01d4183302cc06ee07a60a320dd90e300e330e370e3b0e48184c09e310e8186717d317d7178f17aa1793177117bf178417db17be179217c417b017b4177617c1177c178e17b117ba179c17cb17a2178717c6178a1798178b1795177817cf17b7,0x21179b,0x8ee00a118fb0c4008f5190b0cf219211317012a139501930d910ce200b2097208ec0072196a12da0c370c3403850269012816f100a0001d0833019f13b6132412ee12c80c3815c71590152a1526152212cc17320279006214f3015f011f0106193401591948000b0cb10c3c096608d40798015016951595158712fd122115ce10050c4410f810e610560d4403ae0278190a005b122f193b016e01a71918191b18ea02ff02f8010814a7149e12431480147a02820bad0ba715170a9e0a930aaf0aa801f701ef03bf196306f5192d192b18f700931930007f008000030068004916f815eb14ab148306bb02ca1136145005e3066c0b1d0a8d0a0a0a0109fb09f8020003170313030b19421927000f0133013e1906008e1904190100130e480e3b0e37089207a606ee02cc15dd13f50743073605340531052e052b030301f800c30c2f02021936005018f01498145b141e0e3f18c212761215074105370147192919200f7e0f7c0f790f760f700ba608980832031f0494048b191517dc18ed09e909e109d809640492040c028a031b06b606ec09bf0caf0d590d5c0d6207aa0ba10f090f0c0f120f150f1d02b6045704600469046c18ec046d0a990bfe0e31116111641167116a116d137e13de141b1495158816cf0aae0b1b0b670e3611b711be11c90b6b12f51562193311bb,0x93f19e7006f155703e11933001b1525152103ed015900e910040ff319180cb4092f08ae,0xba41a64]))))
set_option maxRecDepth 5000 in
private def hintsBasePart7 : Table := (.node (.node (.node (.leaf [0x168e176b,0xc007e50e13005e00fc07f10b0a014c00850a81075604d90a590a49007e0052002a007c11440a870e1904a106de120e04dd072500f50a4f020d0140002600480105004f0454044f00c40004140906e311cf0e4e04ad04750472120b073200210e52075903a50396020b013700fe0023010e0452012900af0019117b117704800d34072e00d31067105f0d3f03aa00f700ae090108f7044b00e8117e0783006d17f3015c005814110f00060905f8020f121216ec090e047605c607820189003b01ac0198006e0039008415721181060c100d100a090d04dc0cf0072c05c40a2c015e012300e300a9007b10a510910ff30cec0a3b00e917b21788179b17cc177017a917a8178d17d21777177c178e17ba1791,0xf02c502c000550049077406f002ce00c30e3100f61166015915310e43077c01ac01421697148001d41873076f06ed00b00cae183317cb177c179817b7,0x44178b,0x15014f60f7c01a71915164e08380831017f006212f9082f011f00cb12ea0e9e0833,0x854015200641246084b1101010b00dd191c149f12440bd60f581089192d009600d900e9084214ad0be20ed70ecf09c6094200921944016100d20075006f0d840d8108cb06a014eb13350b2d0b2a066706610c210bd200b2006c0043014f192200880041009f099109740970096008ce069a082805ef05df05d505d105cd0c2419f50cb108d40061003a00fd190a0bf5081905e10b62066c0b1902fe02fb1906008e1904001205350533053002ed18f019f6134401b515e10a0d0202193618c21173116a0b3005eb191d19f4088f088c00681098089919270aa806ba049c0494191b18f718ed09e309d8096406af069e049218ff19f314e212a60b1d193016fb151415951942193b14821480077b12760b69053707b107a2079e079a02f5192b192019750f200f1d0f1a0f150f0c0f060bd3081f07aa046d030019f20f7e0f700ed40b9109e2049b191519e101c818e803bf03b503b301e501d218ea0e4a0e430e400e360e320895077503c319e006b7092f09c00cb00d5a0d650d6a1962,0x5e8190c003a0d0a0cf803b4016e191118ea16070da303c2193900c3147c14790e4105e2192b19061481127a0d9f0c01193b19200f1e0f160f0d19141a7605ea0bfd0e30116c1a6f1a6d])
(.leaf [0xd57176e,0x830ad50add00e900fa0cec0b7e0ada00a9009100ed06000cf606350630105110d7003b018c003e00e801280f4905f01327119d0b850d20062e03ab0ea100d600420121015e00ad0073001900cb0f42068305c905c405b2139b0d24040803850e9c013500720039012b001d00fd060508e408cd05b3067d03fd13fd11b300a5006c004118350942092308ca066205b80e280e33041409a5105610e9179117d5179f17bd17a717a317bf,0x943006f00e9094c03ed015e001b104e03d700e7157a0044104217e802bd01280138000f0fbd0d63092f06b706f702c200e000b000490a03031a030a02a300790013000e052c030402a8002f18b60dbd01170d200d1d09a10c2700ad009f12ca0fdf06730670066803fe02ab0362035a011b0041001715050de303bf03b503b10355017f00bb001a0e470e2b0ddc06f103c300c318b41498145b11de0d990d960ccf014700b315fd14930da3076402c40175005513ee13da10f40b200b0f0a620788076e02b00165008611bc0e9a0c220b190aab00fd0b67066e008e07a2005b12eb12c8105807ae01cf01d4183318730de10e311158116402b6046900220470178b17ac17b717b117b017a7178617ae1793177617d317b41787,0x16d1774,0x116b191d186904701920184f18d118d008b6,0x18f0052f052b190419010b190b1e046800fd1930181e19800f7d,0x192d1aad1ab4]))
(.node (.leaf [0x99c176c,0xfe100e2011b0c360c8012c700a000a5011f0c3809230cc20106006f00a70b330661076f00880041005512cd0b26066c02c70159008e000f152012f50b6b0e38077302b7015d00c3002511bb0e36049e00fd11c301750b1f0b1a0de3008600bb05df05cd0b1e081e003a01560061116611570de00b2f05ea089c081506d00c2f00f60068004600a40bfe088c05e202fb02f302ef020300990012000305340531052e02eb01f8002f181603c203b503b317b917b6177217c5179c177617b417c417cb17a617c917b0,0xa5074e09220051006f0748059b007d00380a7505a400f406d711420443004701a2002005a20c9006dc094d0ee7044100a801230135015e00d20cd606da060e0f420b9d0b8e00e900a9003b00d6009213fe0d7f08f408f105f708db06a01630013f00b2006d006c00430177098b097108eb08cf069b05fc12220072010605d905d305cf043104ef003a0046002b0bf8035f035b02f002ea009900170012081a036602fa0061189617100c4108f001a700a115620c49015d011b12f612c91791178d17c9177217c5,0xe217b9,0x6f0940066100e700410d1c067a190d00fd0c6511570fbb1869191d00e00a0d0a080a05099f190118fd052b08bd08ae040903ff18f018fa001d02ec0465040117e61830006202f102c4082f062f005500cb18f50771058910430e9f06370797190a198519740cc007ad028a063306b6092e0caf07ac02ce07740e2a0e3503ae03b618ea03c2077a192b0e420f170a0a0fc2192d0f19,0xd541a0d,0x8951a95])
(.leaf [0x15ac176f,0x15615180b1c01a700860f82053000db002f031e0304001303190068052b089a151608170079012e019c00610a0a13df148208220149019101420125171114ac08261690147f136c156301a4014f018a015d152f0a9d0a8d12fc12f50159007f011f100310000a93031a058c00e300b000370cc40cc20cb60cb0058900a7185611680a9a0a0800f60f210f1f0f1c0f190f170f0508210470046a00d4184d08c708c008bb057f01cf08920e300e370e48184c18420e3b183317c417b417aa17b017b117cf17c617c11779179817ce17d91778177217c517ba17b7179e17b617cb1795,0x42068104150070001e04220959069804230074015f012c0077064c09520bad10fa09f1004000a7009300ef0655091c064a02fe02c90dbc00b2006f17e6000f00b7071804ba04b802f102c40dbd004d00270055011713b20ac9071204bb076504b212b8013200820059016f0ea20ac3078d0ab300cb00800e9b0aac00fd18d60459002208ae0464006b18d50a27007b0d8d06600a2b0829012a0084006210630aee07970737073600e8005b005012ed105707ad0d95073c011f00b314a9158512fb0da4019c018a017514821480147d077b046f0ba317a417c0179017b617bc178717a2179317c617781776,0x620836082f015000cb14f810ed078c01a7191b005915cd10f30ea4078f19340147151809ec09ea193018ff151c06af01c318f713e113d906ba03140310192700130d650d5a078b06b7031c190f170416d3149606eb1942193e0049141f141d06f8089c08990316192900680e490e3f0e2a089406f001cf01d418330830089609e00f740f770f7a0f7f0f821955,0xb3e009500890bc00b401916191304aa0bcd0f0118ee0181193a04ae123d0b451689191e010a015a019011d511f7131d15b911d213931938010319210163012a126311f8132809bc09b104a4084f191f193c18fe00640d3a0d3516c912400c4816b00650064c084c190e01ae00a101af004000dd0c5b0c54085216850cf60cee0c3f08f8158315721568138c0c7b05c805ad04bf190701520188190b18fb015e00a5003900270c5e124e1247084113580cea08f1094c0939092205b704b5174a010c010b0092012300e400a8006f01c3110709b611e10ee40edb0ed80b8d071510ac109110100cec0cd509431704191c00ff00d2004d00e919420ede0d8a0d8506550d6e08e708e105b406a706a2044104340ffa0ff20cd00c4214ab14a01245013f00b21910006c004300201918192d0dbb0d6b136a1018098c0972096e08ec08d0069c043e13330ff914ac00b7192400721922194412b412410dbd0de705d805d205ce133b164d0584057d06c70431011700bb003a0185017f18f2004612b70de80c7205e5150f13e113dc1363134c10990c050cbb0cb20c3d096708d505880a9402f0016f01331908193019271906190a007f001215d713f50c76089c0899088b04b30bb0076f076802f1193600680059009300550a0c06cb0317030f02e402c902c5173116ca19010013000f194806e406c3030a02c001d0145b11de078f0d990d960ccf16d316d01681157a004918e80147191117e8141806f603b403b201d314930da3192918ea193915d10e490e460e3f0ddb0894077406f003c20b20076e193400c3190411bf11bc0e330b1900fd11701164115b11580de10a9905eb191d0471046c0469045a02b618ec08c208b708ae057e046418fa19b719d6031c06ed078b092f0c7f0cb00d6508980b910ba60ed40f6d0f730f760f790f7e0301046e08bb0ba20f070f130f1819140f050c000c6f0d9d126912751278127e192018d00f70069d096309d709dd09e809eb02b8042f04890497049d18ed0491049b191519d51962,0x191d19e30471046918ec046518fa08b60204])))
(.node (.node (.leaf [0x467176c,0x4240077001e04ba04170027004309ef04c1069c00dd00ff00720fa211df05d9013b015e003a0e7b094c093904b5035b00c7006f00170e7c03e603e203d303c80358019e001b10a910a503ee00e90ff400e31001014f16ec14e804b2019800590dea0371076700bb005506d001e70046000202ef01e1078a092e07720dd909660cb4179017ba1785,0xc30e400894013800680f740896188217ac,0xa317a5,0xfd049c0b1918ed183104930d9d1278,0x190808b40c7518fa1936184f116a047014171929141c193e0f7f0d6a0f7408bb0c7119200f0d19141a050f030f6e19f7,0x8e0b64066c00fd004111c30677193919ae0b6a])
(.leaf [0x1087176e,0xe97018500ca133c0e93,0xca0e950a90013e007f145511b704e8019400fd002b16e20c2404e401af009f005f17440bd207fe01b2009612c4086e07f40119006612c0087e15ca16140508015401650171002d150815910d4f0d480afb0507019a016100af0084107410700d400aef050d00e815dd15da0c6c0c66181500a417d7177e17d317a6,0x1ac177c,0xfd11570aad191d00800a0809f9190106e40aa818150049191b141706f808ba09e4049404551929191418ff18ed0f750f0409e1049a06ec0d5908b608bc19b406ef0e310e340e3e,0x7b3192d005b0a0903b9190118ea0a0803c0191d00680bfe088c19060c0119200f6f089707a60892,0x164b1ac3]))
(.node (.leaf [0x914176d,0x46a007f00220a8d02b50086000f076e076b02c70055076f00a70cc40125136c018a1480077b01420e41077302cd00c303c3001a03bf006813620899012e182605dd05d905cf003a11570b2f0a9805ea073a05e6141e11a011240e3f00f600a40138116a0c740f1716921497141d13df016800d40191127912760f0d0d9e0b6907410f7f0f770b8f09e0089608300499182000db17e8178717b417b617ce17781798178617ae17cf17cb17a617ac17731795177917aa,0x1202f602f1005b005507a9077502ed00c3002f079e03c201f80088001a000305df03b401fe003a05ed01220c7205e500a40c7601680a0c052c02000079077a0469187f014200220f180f1607ab046e077002fe00d400a714810f1f0cc901c6187318a3047005eb0b300e31116a117008b408ba17b0178617ae17be17a6177317b117981787179517b6,0x12e17cf,0xbce0096009d0c1b059e0b8b0164003800920bd1156b05a2054c009f015e00a800310c2910a50cd5054f193400e915cf180001a7139e16ec1517192501981930132c14e90b1d1922014f190413430a9b0a8c01b5007f160b0aa004e212a3016e002b01141522121e04ee0779015901060055153112241479077a1947192b169714800b8f0c160f82157b15c10bd50f0b0f1c0a9a1168116e15df13f213f9013313f31936116b14160f14191418d416920f0313f01929141d193e0f7f0d690f74,0x12e5011e017e05760b9f18f1009212e905750b47193a00f2008a15720a3d0b4f06a1015e007b0102004313220a3e13cf0ca00573069c192100f8012d19090072131e0b51112a118c13c70fe50c9706a40a2c039e015a016a01010161191700af00840019154111f6168913d215e811f20afc10700fdc0d400aef03ab01aa0190017300e80e920e90171b16c6161c107700ca01ae0e971678167416710385145114500b1101850187001d013e19041667155b12e3040f11b70b1b194f193300cb00fd1769173116ca13790ea111c101c319480128016f16d316d0137f14181844192905d005da03ae18ea03b315401595119211eb192b14811a1b,0x681a681a971aa2])
(.leaf [0x13df0191012e141b089a013800680f750897177917cf17ac,0x6e9008000490aaf06f8015001380f7a0f7400db186614f701a711c70aac00fd186515cd016515d001b1156310f810f410ee0aaa015d00ee12f50d58011f00b00cc20cb000a718641515019c14830142147f12fb018a18631862117111590a9a00f60470046a0455184f08c808c10580006b18610f1608bb00d4185d16d01691141c0f80185c01d4183306ee0e300e330e370e48184c17ac17aa17d3177d177217c517bb17b717b617c61798177817cb17a21795,0x820acc071200ff004d06a7048a11e10a28071000430025015e007b139a06a4069d0491094e0a390736012b00af0076006f00e1005010e90d4409e409230c690c66073800ee00a500a410550fcc0d400c850c6d18e6121b0d0b0cff0cfc075701f4010600aa0003122009f905ef05e905d101fe016e0079003a116c11600e600a0705ea00f618e303c403b703b303b103af03ad0355028c0226001a050203ba01c601cc08b008b90bd30f060f090742121612741277189018c608b604560459045c045f04620468046b0022046d0466179c17bf178f17bb17a6179217b117cb178617ae1787,0x196508fe08f918fb02820609060005f8020f18f7003b16a603eb03e003d803ce03f1102501af001b18f600ea064010ac03ee059103410e0a0d3716da10b4009d00e900381926137c1042153b0b8a0387019300f110df0c1a0942059a03e2069605f0025e19010128015a0092001d15c8111d0164006f00420a0a1561137914561553117e1522159e1597158e13b910c708e806a003d20dff040e193409d609cc09c90921068903f7192d1933013e193201590161006c004300cb0c2b007514ad11ba11b60aad100710050fff0ff40a1d0991096008ea08ce069a068305fb039f082e17f206670661059203fd194400fd191800720062004113351331132b174a14eb0b190b160cb4096608d4136710b6082a066c0b2a192201c3014f1904190a1924008e00881344151b14e20b1d1695159515400cc908280824088f07a2079e079605ef05df05db05d505d105cd01cb01b51930193b00610068005b003a18e816fb151414a9148013e013d813621098081d03bf03bb03b903b703b503b3033d01d21942192b192700bb18ea0e4a0e430e3d0e360e2b0ddc07a903c300c31966145b11de0ea40494048e0488042e014717dc18ed09e909e609d80964069e0492040c06b6092e09bf0caf0d621962,0xfc0bc411ad0095017404f612b0065a0650002c0116004012ae04fa04f40d8f0d890392015300e8007c00b200190a4715030c830a50097103a00083194c00a500e4007210dd0adb13b00924064a1015098900ed1925006f00ea11ac1038139a094c0d000cfd03fc0387016200e7015e190c001d137a10d5104210a410a00ad6090702850279012800e918fc000b12eb10580ff3090c023202290221011f191800060cc00cb40cb109660235028b092f0c7f0d630e3a0226027703ad18ea03c308ae08b7,0x8301a64]))))
set_option maxRecDepth 5000 in
private def hintsBasePart15 : Table := (.node (.node (.node (.leaf [0x173e176b,0x77d007e00560a8b077f016d00c4125f044f0810010e002100600ef7081204520e4f081300d3012401ea0f0012d400020189011c01e915720cad12d70055015e00a6015b0769139b094c0926090408f7044b0c9b077e007f012b006f006d00b10a9b134e132b12d00cca08ae0cf40cef08f5096e08ec014f0123012200a8006b00a9007210010ffb0ff80ff50cd10a9408c00ce2097000e300b2109410920ff40d810ced0cd608bc0f1c09660cb10cb417b217741770179b17a917cd1785177717b517d117bf178d17b817be17a2179117ba,0x159152e0fc601a400e014ad0fc301490a090a0308bd08c617d917c1,0x76178f,0xf19192d191414aa0f0419421915141f0f760a091929190114160a0c1936116b0a08191d0e480e301275192018d118d0,0x1f918f0000319f6,0x6f31a7b])
(.leaf [0x107f176e,0x920b4707c5008a005d0b4b0334009600150b510508032c015a002d00191541050d03ab0b2a01aa00e80088171b10770b3501ae0159167816741736171e1530018701b901a4133e133114ae14ac01f401f0012201490003132c0a0a0200012b007913ad09f701b6008016270bd1160f0ab5055c04fc0175009f016f003311c50c2512b5056400fd0117155b11ba173112ba05ef015d01b1003a07c7137910f810e910560bf505e106ea0093012800ee009900490bb20d610d5805350527052101fa030c0308017f00b0002f001313dd0d6502eb02e3012e0012089a088f07a1050202f80068005b03bf03b903b301c601cf01d406ee07a608920e330e44030007aa0b4c0ba10bd30f20031f08980b910ba60f730537126a1279137f16d014181540169c0a0d15d705e40c6c0c7700a40c760c700b300bfe1158116700f6116b016814150138141c0f761276010f0f7000db0f030f0c0e3014ab1700019c1482014214810f150e4802fe12eb12f812fe0331038a08c7006b05800037058c011f0cc112fd0e37058800a7183e136d0e3b18330cc9018a1691183d0f1d08ba17d917be17c117bf17b11776177217c5177d17bb17c917b717b017cf17a2177817b6179e17c6179817cb177117aa177317ac17a6,0x55c0080003305620aab051f00ee00fd002f10ee0ab20b6605320150008e0836082900620b2807970088005b05dc07ad14f6003a011f0b3301a705e312f9010615190099017f121e0156088b13dc06e9031503090305016e151403b317e7012e004900131608019c001a0d640d5806eb031a017507b20e4a0e470e3a0e3603c300b0141d13df127812140b68014900c3187a0191010f17e91711164b14ac1482147d147a0e420f830f800f7d0f7b0f6f0831031e01a4014200db0f210f190f170f0e0f0b0f0507ac01cf01d4183305eb0b300bfe1158116d117018820e31187312fb147f169017bb17b017c917c417cf17c6178617ae177617b717c11779177117d9179817aa,0x192177a,0xf28011200d50d110f230b800f3200ab19160091018b0d0d0eec0b770ce11912191300a809340da808f908f3006f00f018fb0606060009b209310af208fa003b18fe00d00084191705f0063b0ebb0a2b0fe503ce004218f60102007b1921001b0689064511f50a4407d707d003db007500fb016a005d0daa09d3111f15f00ec507bc0f000110016400f201af014b0064193a1288156d11290b850a29113016b213280fd409ab06400f9c084b0cad0ca10154015e008200f4193c00e100af009d00dd1909087e11e00ac00b930b8a0842114316aa10ae0d0e106d0fdd0fcd0d410af00bce129b0f9e0ca3006600ff00bf009201a2019300ea00e800960113039a11db0e0d0b2a163015a2159e1597158e10c710700be2153b0f480f440f3b07d30019013f008801770161015a00d6170e03870fb2087a172716a315220b3513381335133108e808de08da08d206a003d201a7001d00df194701591922006c00430c210bd21223121a10b415c814f60dff0ac2040e0fb00f41100c10040ff80cd109910987097f096a096008ea08ce069a0683039f009f010600f11934015000cb0114191800721748088f121e10c910f310ec10540d420412078e0cbd0cb4096608d401c30068016e191a191b00591863169816951595154003b7151b12a61299089d0aa10a9714a2149c11f40aaa01f6079d07770765193b18ea1930007f192d00800003005b00551480147a05ef05df05db05d505d103b40bfb0bf80bf50b1c0b160a8c0a090a0009fa09f701ff02f702f3192b113617fa116b1906190419010012145b11de15eb14ab148301330c6c0c690c660202193605350530052d052a052702ed01fa0147196d13f011a0112418c21276127312701215196f09e909e60964069e040c030e02e31929192018ff00130f7e0f7c0f790f760f700c180b9109e2031f191519be16d215bf15791495193e13e213df13da110f089b192706f606f3030b06ba05f403d6004918f702cb02c702c302bf000f15630e3b0e370e280ae40a32089207a6077206ee02cc193300c311c811ba11340e9c0e350c240b1a0aad00fd19bd049402b718ed19bb19ba116d116a11671164115b11580bfe0b300a9919b9046b0468045602b518ec0f1d0f150f120f0f0f0c0f090f060bd30ba107aa046d030019b719b6031b06b606ec078a092e09bf0d590d5f0d690466058008b008c108c408c819b4,0x1445016b013d15f4144b01ad018f144a154513c315f8193c015a192601ae16c5172c16b0153713b21685167c124f194d01af016101320188010b095616e6150b16db16ab159d10ff10230ee40ed8007013571349194101540193191c00e400d209580123173114650edf0fb60fb40d900d8208e708e10441015f10ad1092108a10111948013f00df00b2006c00200bad00e9124110f7098b0980097108cf043d043000930d980117191b007218ed0fae02c9191112b815c9159213ee10f409d7096304940114000f0da4016f193419bc0080077602c4193911bf11bc0aab00550b1f00fd09f902f3190418ce19010012052e052b02eb18f01a3e15d61936186905d205d80b680d9d1269127212751278127b05350bf70bfc0b30115811641167191d0bff05ea02cf07750e361099134c13d513d9088e08310b900ed30f72141819290f750e400b1e111b151319300f7d089c0068089a19270e3d03bf088d19060c0005e106e90049030b0013031e01d118e801d218ea03c306f11a131a181a101a0f19621a1c,0x1a71ab81a741abe]))
(.node (.leaf [0x62c176d,0x55076f01e800a7000206cf01e60046001a077c02ee01e003bf0142001200680f160301089900d4012e08bc0e410e3c0773006b00c308b50e3f00a401380c740464141d13df016800220191116b0e3204710f7f0896181d00db17e8181e020401fe00030534052e02eb01f8002f0a0c0a0a09f806cb052c04680200007917b61785178617ae1798179517cf17a217a617ac17731787177917aa17b017b1,0x1644017b18980e0f033400bf00150b960e0b03a2032b00ff013f001906a6098b097503a00043007206ab13be0987012d012c00ea13c613b810c517c0,0x10e1770,0x18230f05,0x191810090cb60198190a14e806ce014f004614eb13f906d3194401330f210f1c0f14191406c4046e004919e406e606cc0f0c1a161a10,0x18ea1a96])
(.leaf [0x37022b057f0006006b022f022008bc003d000b00d4061d0282046d04640044002202bf02b602270278179e17a2178a1795178b1787,0xfd049d11be17dc0165000f10f302c213d900ee0049012e0d5a06ed136400b0183e0cae01d4183302cc06ee0e330e3b046e00d4185d185c0e48184c02b6115800f604710e3017d317bb17cf17b717cb1795,0x5e07e1037e0095001807ef0bbf037a014c00dc003c0bc9101c03810f990611016100e401920045061a037809910652101509b013e806c200a6001b0072004000ea0074012f101814d00c9d03e8096f065510ae15c3063c0e6b012501bc00e200c700b200f00164003f00c613671346035810c00fea071b0718111213bd063f13e50e63015c01220017014d004d0154012c009d018200ff10060ff70375080b11a30712087d087b087003a003980390165911e604c200e3005f00fb00820066001901a900270ffb08090e050abf087303a30fa904be012300bf00dd0dc90dc10bd90bcf086f07fe06bf00b900960a2e07110508007b002d0d8b065e0d360ae90a2b0506012a00ae008411310dc71071106910650fdd0d2f0af003ac00f400e811370e790c900c840c7a013b00a5094609270924091c064a03e3036b08b908c117961789177a178c17b517a417d017ce178017b917a017d217be17c017ba17a8,0x1238010a0116070812b0004b0174070211ae007a00fc021211a50004013a0bc60bc20208112c0095001600f3065c0652033f0b420b3f0040003800890394020c059e0e5f07060b410019009600c5191303a902430b4b0e5b0a230b7700e80007008a00f700910aef02410615060705fe020e0084002918f3003b0bdd0a2c04d003d103ce02400101007b007d001b11830b85118d0a3f08f8034b0a6a03e5015e00f818fb00c715341194112d0b500b430e5e08fb04d403540e73015a012a191700ff131e13180fe60d8e0d8a0d87065508e906a7060f192100b2006c004312ca0fdf0983097008ea08ce069a011b0072152312cd05d805d205ce0159003a12f012c9105a0b3705de011f008807ad079e005b07b301f7192d00030b260a0901ff008e19010532052c04ca01f901c607a70a330ae50e38059808c807ab0b4d0bd40f18119311ec0b6a142a153e070408d509670cb20cbb0cc1157a0388057b0582058a0a1b10030e5d11de0147149614780f77063118f5057818f205880580063406240a640dde0de3117f19321368100603d705f5023b0358035c03600017037100bb0de70dda0de8013313f60f1308c4036b037519180cb508c1069f096509d9073607370a620b0f1325015f0bad009302cb0ba40ba21585158912b31622194815d0193409ec18ff06af09e013d816d0193e0d6a0f7f0b640e8f0e9100ca0a91007f0a8e0768046a0b12073f0050048c045e184f074219200f0d0f6e05ec0a080b31115c191d115700fd0b1b19040497076c0e34049d18ed02b9000f02be18f7061d18f4062b1924136219270d650e3c136c193b0f1e062706b702c400550770190a0cb018a3077c18d4191408bc195e0f03195a077302cd19590499195518c6,0x11e000ff015e0acc139a0082192510500ac810e800e7191b0d1b10ec190d01500c6410310fbd1908191900e002020ac30aa70fc5000300cb00800159115c067f06750a0309fa01ff082f06e901f9152e191d004119010062004918f01944104211570aab0679149d0fc30a0b082a066c0494030a030314ed012800fd192d008e18ed0013014f1520137811ba10340b6b07b107a207960b1b0498030f14e61933005b19040059018512f612f407b0076d0766166611de0ea4078f011f0055194f01470cc0076f176a1478077c190a01c3192b12fc0cc8170514aa1482193b01c81942184418e81514150e14e10b1c03b903b501d21815193018ea16d215791495137e141f128012770c710b6a0538089e03c0193e1929192000680f800f7d0f7b0f780f750f6f08970831049a031e031c06ed078b0cb00d5a0d630d6a1962,0x76600590055078e076c00cb19040e9c0b1a00fd1a5e121701061220016e16060da00d9b0d98193919ae1a5c082904010062150514c50799017f005b0ea412f707ad0147011f147b14780cc20771192b190a16971594148012fc0cc803b907aa0f090f1508310f78030f03130013031e01d118e801d218ea03b41a581216127a19200f6f0f0c1a5b1a111a161a0f1962])))
(.node (.node (.leaf [0x994176c,0x17dd0a0a046800790a0700f60e3100c30e3f013817e80f6f010f0538002f030102f702ec17b117cb17ac177117b0,0xc30e4006f001380049141b030a019100130f800f75031e00db188e0f03184f0e31047001cf01d41873031c06ed0d6a00b00cae1833188d17ac177917aa17b7,0xb017b7,0x1447013d14490172144c193c1618018f0cf7095701af13c31619190b007010ab192601b00cf1095010f90ceb15c513bc16aa1921190a191c00e901640193173016bd13190d3b09680d6f0944158d0fa701ae012a190e00721910006f016100dd1582132010a31737107910640d2e098409d309c1095f091e0be00bd6015e01b900e800750096158012fe12ee105810e30d3209cc124d0bdf01a9011f00ed010b150112ea10d50c500152012800a2104e104a104310380c4d00e7198e0958015f0bad009302c9000f0fbb0c4c02c000e000490a05030d19010013052b030318f0198d030f00590ac4078e00cb0ea61749019f01c3170c1769165b01b6194f166a16680dbc0d6c175d018600b701b512b912b412410dbd15e00117193612b80c760c6e0c6b0c68016f19080d270d1f0d1c0c640c4a190d132d0d251704170116fb0c2d0c200bd119251942009f0da00d980d9515161513151006730670066819111930004116290da411190de414f4083903ff193900f100bb015012fa001d0b1f0b17052f0de814f6017f10ec10e710e410540d4204121904013301a7198a191b049802b9169415941586153f13f71498078f15cf15c91592111e10f40c2b18ed193b0147193409eb09e509dd09630491040b147f147611ca11bf11bc0e9a0c220b640b19067918ff03b603ae192b00fd198718ea0e460e420e390e350e2a0ddb03c200c31882198c14af14aa149f12440fc2192d08bd08ae036917141711164b152e14eb14ac046802b518fa194418ec184d11731170116711580de105eb0470031b06ec078a092e095409bf0caf0d590d620d670c6f0d9d12691275127813801497157b158a15c1169216d4049a09e10ba50f720f780f7b0f7d0f831980192018d118d0046f0ba30bd50f080f140f170f190f1c0f2119140f04197806f613ef141819290f7519150f81141d193e198b0d69,0x31a1a0d,0x18fa1a3c184d184f1a8000c31a891a6d1a7e])
(.leaf [0x13d7176f,0x46e00d4002208bc046617951787,0x1231349080a012c005f06980805004200d210f91351097306800ee1080b00ef016100720070014d0d700be008d00fea0958015f158917e8128707fb013800b10110009614190dbb0d6b113c0f9b0bd7016f00b7006c00e200f400dd12b50dbd0fa30c9a08d10c8f0c890c80068705a605a004be0117013b00a600a50075003800270c370c340c270946092709240920059b04b700a0009f006f121b0c38066f0667066105920106004112210d960678016e00b316070da301750b2009dd0bad0086007600930497049202c90025188c11c011b111330c23049c00fd18ce04b200590c7f09c00955092f078b00b0076406eb03b703b500550049001a0e36077506f103c300c318cd073605d905d305cf05cb0050003a0314031003080c6d0c6a0c670c30073905e5001300a4052e051f030302eb15d70c76002f01680bfa0bf705e305350a0c0a0109fb09f806e5052c00990079116c1163115d11570bfd0a0705ea00f61275126f126912140d9d0c00074013f2113606d3057d038a0471046904630460045d045a02b6010f013300370022147c147914760e41077a0f840f7e0f7c0f790f760f730f700ed40ba60b9109e20832049b031f08c208b708b408b108ae0596057e0464014200db006b0f180f160f130f100f0d0f0a0f070f040bd40ba208bb07ab046e0cc10967095108d5077006ce058802fe00d400a7169c159515871540148113f812fd0f1f0cc901cf01d41833187318a318c618ca17c017bc17ac17b817b917b51793177617b4178f179c17b7178617ae17a617b0177317c917b117cb1771179e1787179817aa17a2179517b6,0x1c517db1784,0xe90d81094200b2006f09700ff30661007219180041066c09d809640cb40cb1096605db05cd008e18ff186317fa053304910a0d0202193b18f018ed193618c214800b69053707ad07a20456116a192b1920197518ec18900f150f0c07aa046d19ce03030013088c03170068109808991927169013de1416193e19290f810f7009e2049b17e8191519cd19c8031b092e0d690466058008b008b608c119b408950e320e360e3d0e400e4303b503bf01d118e801d218ea03c319cc1962,0x1179013700f70ef8117719130b7d191e14110f0000910693193a0e4e053f0042147500c40030060805ff041601410a4f0e4f053d003b001e1190007c192300830cad03cb03c700f80a52147410940ad80542090308f905b21909001b0ad911dc118a00e4193900e918fb0039092703e300ed00ff10130da30d98061203cf05ac198e103a04c000ea191118f3004000e7002713590d010cfe0cfa06110d7e065506a8061004190ac504bb0853012d190c18f800b2004300820064132f0d06118e06c106bd0988097108eb069b05fc05b30a2705030362035a1922010100960072006c007b002d0017133511ed0be00990066008de0af70a2b05060d1f0d1c023102220161012a00e10084190d00060d4d0c9706a4106f10630fcb0aee0a53079b0500099f0286027e0221199a00e8197518fd000b12ed10570fd007ad0632062f028112b40dbd011f18f5011710fe12eb10d61043063704b40566055a04fe01320128005900330ea20ea00ac3078d0c200bd1055b00cb009f00800e9b0c230aac035c05cf05d305d905e70d9d126912780a350ae70e2b0e3a02260277035503af03b103b703c4115a109913d509f909fc0bf719060bfd088e0068089a03bf08950c650c680c6b0c6e0c73186906e90307030f0013030c004906f61929141619360a0d19e505e2191d0e3205eb12750e4006f101d118e801d218ea03c31594023608d609680cb3119111ea192b14800e43101810b519240cc4190a0cc8136319270e3d1a0e1a1b1a111a1c1a161a0f19621a10,0x187b1ac41ab51acd]))
(.node (.leaf [0x51c176e,0x14b60199014a15f20f2d016b00d50def104715f50f3100bc00e701ad018b0dec094009370a5c0a4c172d16a80120006f007c01af0cdb03e110220a500a5416e016a000a8001b00e400e8019417490cd403ed10141306105816b816b701c300e900ea012b011f018d176913e0109810b210e7105412f60fbb15510d0c0d010cfe01c5012e00f100ee015d00e0015c00aa175d151c136310b6101915cc111e10f4172716a3152013090fc6090e090a090701b501560125016501ac0159006e165f150e152e0de711bc0d1c100d100b100710050fff0ff40cd2090d0232018501a400bb00fd00ad00e30006133c117311700de1067a067303760374036d03590224012200f60041001705ed05ea05ca035b003a182e0ea100cb078c074504b200590ea4078f0da00d980cf90cce067709eb09e509d70963040b13f211360de8014700b3007601331629160814940da40bb006bb05f603d8049e049308c608c208bd08b708b108ae059603690743073f073707360175009300440025006b00500b1f0b170b1102c902bd02b7046b04650462045f04590086000f17de076e076b02c700550cc50cc30cc00cb40cb10c3c096608d4076f023517d717bf17d6178417db17cf17bb177217c517d2179217c417ce17d3177c178e17d917a717ba17be17cb1793178f1776178b179c17a217b4,0x546005f0031080c07ff054f014d009700e914d40bec054c108c05c00154010c009200f0003915080edb0b8d0afa09ce0a7905bb019a00d200840075007d007014660ede10730aee0d8509c105b406a20441043f0958013f00e800b200b1006c00430020015f0d6b098c09850972096e08d0069c043e0bad00b70072042f009309dd09d70963069d17dc02c90076000f06af02be004418ae16000362035a023d019800170dea0dde0a6403b10355033d00bb001a0ddc0ae703c318ad110d012e0d6509c00955092f06b7158900b010b6089a088a17e806eb012500680138004908220815141906ea0061016f008014e80826160e0aa212ed1057014f01b600be186014ed163d0dfe07ae079b01a4017a005b14ac14a407b101d418330de11164117018820e31187308d5095109670cb202bc05870037058809e20b910ed40f6d00db17b8178f178b178617ae17cf17b717ce17ac17d917aa179e,0x15117c3,0x1311018201200be60fe3009619171507059e0be00fe5015400380161192114be059c0fed13ba131c014b006f1931192612d614c7130c094d134f111405a20a4303e110f9011c019e015e012300f000a8007b001b191c133612d110a910a51091108d10890cd50a3b03ee0dbc03d8192200e900b718f705ed0d9a0d970d940ccd0c3b061d003a191100a018f405cc16250da40c3813b61324022f004119390106015f000603fe1522130716ec1606121f0ffc0ff60ff40cd20bad03580223001d01590198016e19180093001704011657152f16eb0a9e08c708c008b20597073602ca03b603ae03560227006219441942007f18fa0050000f18ea0365079814ac14a9046a0464045e02c001d2006117dd192d18ec004918e8081a05e20a0a04680315030d01d11906190100130534052b0303031b06b606ec092e031d08300ba4157b158a141e02cd06ef0a331098110d134b047105ec0a080a9a0bff1168116e117107411215127012730c310c7319080c700c741936116b141607ac08210ba30bd50f0b0f1913f9147a0371081d0dea00bb0de817e413f01929141d0f740de20dda15851593062b02350cb4190a0cc41924136c193b1480192b0f1719140f0d192019ae0f6e0f030e411692136219270e3c13df193e0f7f19a00d690caf1962,0x2ff190a00120cc802f5193b197418c500c31a16,0x18d41a9c1aab])
(.leaf [0x830adc0ad200ed00c403f80e5110d80e52001c0124012903f21359105f0285003f012d00e8000b0d77064206a903a9038210970ad7028400b10043001900e900441059027a13cc069e0ca80c9a096e069c03a103ed03d6011f001d0165007600a60072001b138212f604100c2a049308d208cf0357015d00cb009f0025006c001711ba0e9c0c24049d09ca03f605d905d305cf035c058f038c02a500fd0075003a0038000e0679066f066705ca059203fd02aa00410928092108cc0664059c03e4028a06b609bf17cd17a017b8178b17d3178f17b5177217c5179c,0x319001317e7031e186e031a00b0141d0d6a01911690018a0cc800a70cc2186d185d0f1f0f05045502b400d4184d08bb01cf01d4183302cc06ee08920e3b0e48184c09e31867186b17b71779177817b61795,0x2e17af,0x788190400590b1a030f00fd00130e33052e030300c318f0078f0e3f05370147192919200f790f760f70031f191509e909e1031b078a0e311158,0x11a7014500fc0f9211ac142111af19160162192a017415570eec11a9137a1489142212b11933191301610128193801160b6c14260f0113b812d8126312550f86008e193a1926011d191f0b5f0cac0eb80e070d3a0d3500d0190900cf00bf190e07d1061a12dc10c70e700dc108750873068f005d18f3018800ea00c700b9006600420cee08f815720c8d0c7b03da03cf0ee40a720a6b080307f40680190b18fb015e00a5001b00d2007d005f00700ebd087f07d413580cea08f10a2d094c0930092203e10441043f054609580108015400d6012300e400a8007b006f00200031015f150512340fb40f38109110100cec0cd50a3b054f10fb092011e1043104e404e20bad0ba7086807c7017f00df00e9191c007500ff0046002b0093164b0fae0ffa04ec0fb20ede0e0c0d8e0d870d7e0d6e0cca0c9a09c108e108d906a7060f04e802f002ea02c9194401141918013f00b21910006c0043007f0012000f14ed12a50377035a098c09890972096e08ec08d0069c0685043e0776076802f102c4014f001714e40072005510b51018082602fa05d805d205ce035b01850cb50cb20967095108d5077019240061003a150f12a6190a13dc1363134c10990c050bfc0bfa081b05e31930183e19271906089c0899088b081507f60547006819ee0dbb0d6b00b70dbd01170c27009f0670066800410d990d960ccf06781911162115b412b20da31948193915d10c2b0b200b140b0f0a62073619341904005011bc0c220b640b1906790dde0a6406d100fd00bb0de806d30133145b11de13ef0147192916d016811589157a1496141c137f19e203d7049d0497048c042f02b818f718ed09eb09dd09d7096306ae069d049106b7092f095509c00c7f0cb00d5d0d630d6502cf077508950a350dc60ddc0e360e47035503b303b503b703bf049b0ba60ed40f730f790f7e030108200ba20f130f1b07400b680d9d126912721278127e136d13f81587159518d4077a1476192b0f160e4305eb0a990de11158115b11641170036908ae08b718fa19b70460046c18ec0470191d19e519e408bb0c00192018d00f7018ea03c30e32046e19140f05191519e10e4019e00d6a19d0,0xf6e1a64]))))
def hintsBase : Table := (.node (.node (.node (.node hintsBasePart0 hintsBasePart8) (.node hintsBasePart4 hintsBasePart12)) (.node (.node hintsBasePart2 hintsBasePart10) (.node hintsBasePart6 hintsBasePart14))) (.node (.node (.node hintsBasePart1 hintsBasePart9) (.node hintsBasePart5 hintsBasePart13)) (.node (.node hintsBasePart3 hintsBasePart11) (.node hintsBasePart7 hintsBasePart15))))
def contextBase := context 5999 rowsBase
end OMA.ColorPlane.Cert

namespace OMA.ColorPlane.Cert
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run12 : steps 5999 rowsBase hintsBase 0 12 :=
  by decide +kernel
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run24 : steps 5999 rowsBase hintsBase 0 24 :=
  join_steps 5999 rowsBase hintsBase 12 12 run12 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run36 : steps 5999 rowsBase hintsBase 0 36 :=
  join_steps 5999 rowsBase hintsBase 24 12 run24 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run48 : steps 5999 rowsBase hintsBase 0 48 :=
  join_steps 5999 rowsBase hintsBase 36 12 run36 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run60 : steps 5999 rowsBase hintsBase 0 60 :=
  join_steps 5999 rowsBase hintsBase 48 12 run48 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run72 : steps 5999 rowsBase hintsBase 0 72 :=
  join_steps 5999 rowsBase hintsBase 60 12 run60 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run84 : steps 5999 rowsBase hintsBase 0 84 :=
  join_steps 5999 rowsBase hintsBase 72 12 run72 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run96 : steps 5999 rowsBase hintsBase 0 96 :=
  join_steps 5999 rowsBase hintsBase 84 12 run84 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run108 : steps 5999 rowsBase hintsBase 0 108 :=
  join_steps 5999 rowsBase hintsBase 96 12 run96 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run120 : steps 5999 rowsBase hintsBase 0 120 :=
  join_steps 5999 rowsBase hintsBase 108 12 run108 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run132 : steps 5999 rowsBase hintsBase 0 132 :=
  join_steps 5999 rowsBase hintsBase 120 12 run120 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run144 : steps 5999 rowsBase hintsBase 0 144 :=
  join_steps 5999 rowsBase hintsBase 132 12 run132 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run156 : steps 5999 rowsBase hintsBase 0 156 :=
  join_steps 5999 rowsBase hintsBase 144 12 run144 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run168 : steps 5999 rowsBase hintsBase 0 168 :=
  join_steps 5999 rowsBase hintsBase 156 12 run156 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run180 : steps 5999 rowsBase hintsBase 0 180 :=
  join_steps 5999 rowsBase hintsBase 168 12 run168 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run192 : steps 5999 rowsBase hintsBase 0 192 :=
  join_steps 5999 rowsBase hintsBase 180 12 run180 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run204 : steps 5999 rowsBase hintsBase 0 204 :=
  join_steps 5999 rowsBase hintsBase 192 12 run192 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run216 : steps 5999 rowsBase hintsBase 0 216 :=
  join_steps 5999 rowsBase hintsBase 204 12 run204 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run228 : steps 5999 rowsBase hintsBase 0 228 :=
  join_steps 5999 rowsBase hintsBase 216 12 run216 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run240 : steps 5999 rowsBase hintsBase 0 240 :=
  join_steps 5999 rowsBase hintsBase 228 12 run228 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run252 : steps 5999 rowsBase hintsBase 0 252 :=
  join_steps 5999 rowsBase hintsBase 240 12 run240 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run264 : steps 5999 rowsBase hintsBase 0 264 :=
  join_steps 5999 rowsBase hintsBase 252 12 run252 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run276 : steps 5999 rowsBase hintsBase 0 276 :=
  join_steps 5999 rowsBase hintsBase 264 12 run264 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run288 : steps 5999 rowsBase hintsBase 0 288 :=
  join_steps 5999 rowsBase hintsBase 276 12 run276 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run300 : steps 5999 rowsBase hintsBase 0 300 :=
  join_steps 5999 rowsBase hintsBase 288 12 run288 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run312 : steps 5999 rowsBase hintsBase 0 312 :=
  join_steps 5999 rowsBase hintsBase 300 12 run300 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run324 : steps 5999 rowsBase hintsBase 0 324 :=
  join_steps 5999 rowsBase hintsBase 312 12 run312 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run336 : steps 5999 rowsBase hintsBase 0 336 :=
  join_steps 5999 rowsBase hintsBase 324 12 run324 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run348 : steps 5999 rowsBase hintsBase 0 348 :=
  join_steps 5999 rowsBase hintsBase 336 12 run336 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run360 : steps 5999 rowsBase hintsBase 0 360 :=
  join_steps 5999 rowsBase hintsBase 348 12 run348 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run372 : steps 5999 rowsBase hintsBase 0 372 :=
  join_steps 5999 rowsBase hintsBase 360 12 run360 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run384 : steps 5999 rowsBase hintsBase 0 384 :=
  join_steps 5999 rowsBase hintsBase 372 12 run372 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run396 : steps 5999 rowsBase hintsBase 0 396 :=
  join_steps 5999 rowsBase hintsBase 384 12 run384 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run408 : steps 5999 rowsBase hintsBase 0 408 :=
  join_steps 5999 rowsBase hintsBase 396 12 run396 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run420 : steps 5999 rowsBase hintsBase 0 420 :=
  join_steps 5999 rowsBase hintsBase 408 12 run408 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run432 : steps 5999 rowsBase hintsBase 0 432 :=
  join_steps 5999 rowsBase hintsBase 420 12 run420 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run444 : steps 5999 rowsBase hintsBase 0 444 :=
  join_steps 5999 rowsBase hintsBase 432 12 run432 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run456 : steps 5999 rowsBase hintsBase 0 456 :=
  join_steps 5999 rowsBase hintsBase 444 12 run444 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run468 : steps 5999 rowsBase hintsBase 0 468 :=
  join_steps 5999 rowsBase hintsBase 456 12 run456 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run480 : steps 5999 rowsBase hintsBase 0 480 :=
  join_steps 5999 rowsBase hintsBase 468 12 run468 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run492 : steps 5999 rowsBase hintsBase 0 492 :=
  join_steps 5999 rowsBase hintsBase 480 12 run480 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run504 : steps 5999 rowsBase hintsBase 0 504 :=
  join_steps 5999 rowsBase hintsBase 492 12 run492 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run516 : steps 5999 rowsBase hintsBase 0 516 :=
  join_steps 5999 rowsBase hintsBase 504 12 run504 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run528 : steps 5999 rowsBase hintsBase 0 528 :=
  join_steps 5999 rowsBase hintsBase 516 12 run516 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run540 : steps 5999 rowsBase hintsBase 0 540 :=
  join_steps 5999 rowsBase hintsBase 528 12 run528 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run552 : steps 5999 rowsBase hintsBase 0 552 :=
  join_steps 5999 rowsBase hintsBase 540 12 run540 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run564 : steps 5999 rowsBase hintsBase 0 564 :=
  join_steps 5999 rowsBase hintsBase 552 12 run552 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run576 : steps 5999 rowsBase hintsBase 0 576 :=
  join_steps 5999 rowsBase hintsBase 564 12 run564 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run588 : steps 5999 rowsBase hintsBase 0 588 :=
  join_steps 5999 rowsBase hintsBase 576 12 run576 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run600 : steps 5999 rowsBase hintsBase 0 600 :=
  join_steps 5999 rowsBase hintsBase 588 12 run588 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run612 : steps 5999 rowsBase hintsBase 0 612 :=
  join_steps 5999 rowsBase hintsBase 600 12 run600 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run624 : steps 5999 rowsBase hintsBase 0 624 :=
  join_steps 5999 rowsBase hintsBase 612 12 run612 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run636 : steps 5999 rowsBase hintsBase 0 636 :=
  join_steps 5999 rowsBase hintsBase 624 12 run624 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run648 : steps 5999 rowsBase hintsBase 0 648 :=
  join_steps 5999 rowsBase hintsBase 636 12 run636 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run660 : steps 5999 rowsBase hintsBase 0 660 :=
  join_steps 5999 rowsBase hintsBase 648 12 run648 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run672 : steps 5999 rowsBase hintsBase 0 672 :=
  join_steps 5999 rowsBase hintsBase 660 12 run660 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run684 : steps 5999 rowsBase hintsBase 0 684 :=
  join_steps 5999 rowsBase hintsBase 672 12 run672 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run696 : steps 5999 rowsBase hintsBase 0 696 :=
  join_steps 5999 rowsBase hintsBase 684 12 run684 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run708 : steps 5999 rowsBase hintsBase 0 708 :=
  join_steps 5999 rowsBase hintsBase 696 12 run696 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run720 : steps 5999 rowsBase hintsBase 0 720 :=
  join_steps 5999 rowsBase hintsBase 708 12 run708 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run732 : steps 5999 rowsBase hintsBase 0 732 :=
  join_steps 5999 rowsBase hintsBase 720 12 run720 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run744 : steps 5999 rowsBase hintsBase 0 744 :=
  join_steps 5999 rowsBase hintsBase 732 12 run732 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run756 : steps 5999 rowsBase hintsBase 0 756 :=
  join_steps 5999 rowsBase hintsBase 744 12 run744 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run768 : steps 5999 rowsBase hintsBase 0 768 :=
  join_steps 5999 rowsBase hintsBase 756 12 run756 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run780 : steps 5999 rowsBase hintsBase 0 780 :=
  join_steps 5999 rowsBase hintsBase 768 12 run768 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run792 : steps 5999 rowsBase hintsBase 0 792 :=
  join_steps 5999 rowsBase hintsBase 780 12 run780 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run804 : steps 5999 rowsBase hintsBase 0 804 :=
  join_steps 5999 rowsBase hintsBase 792 12 run792 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run816 : steps 5999 rowsBase hintsBase 0 816 :=
  join_steps 5999 rowsBase hintsBase 804 12 run804 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run828 : steps 5999 rowsBase hintsBase 0 828 :=
  join_steps 5999 rowsBase hintsBase 816 12 run816 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run840 : steps 5999 rowsBase hintsBase 0 840 :=
  join_steps 5999 rowsBase hintsBase 828 12 run828 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run852 : steps 5999 rowsBase hintsBase 0 852 :=
  join_steps 5999 rowsBase hintsBase 840 12 run840 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run864 : steps 5999 rowsBase hintsBase 0 864 :=
  join_steps 5999 rowsBase hintsBase 852 12 run852 (by decide +kernel)
set_option maxHeartbeats 12000000 in
set_option maxRecDepth 40000 in
private theorem run867 : steps 5999 rowsBase hintsBase 0 867 :=
  join_steps 5999 rowsBase hintsBase 864 3 run864 (by decide +kernel)
theorem isoBase : contextBase.proof [] :=
  refute 5999 867 rowsBase hintsBase (verify_from_steps _ _ _ _ (by decide) (by decide +kernel) run867)
end OMA.ColorPlane.Cert

namespace OMA.ColorPlane.Cert
set_option maxHeartbeats 2500000 in
def rowsWheel : Table := (.node (.node (.node (.node (.node (.node (.node (.leaf [0x8000600040002,0x1650045,0x11700f7,0x20101c9,0x1c101890169,0x30162])
(.leaf [0x930003,0xa900a1,0x17f0177,0xf300bb0003,0x9c0067007800a000740047,0x1ec020c01ee022001e70219]))
(.node (.leaf [0x158015601540152,0x7f0077,0x1610159,0x217020f,0x5b,0x501c401ba01f001f7])
(.leaf [0x3f001f,0xed00c5,0x1bd0195,0xd100a90071,0x300a2006c0077,0xa1])))
(.node (.node (.leaf [0xa800a600a400a2,0x97005f,0x1610139,0x21701ef,0x21f01ff01bf,0x64006a009d])
(.leaf [0x1850005,0xe700b7,0x18d0185,0x8f0067002f,0xd100dc00de010600a9,0xc900cf00a4]))
(.node (.leaf [0x1f001ee01ec01ea,0xbb008b,0x1910161,0x2290221,0x700ee00a6,0x4b])
(.leaf [0x65003d,0xfd00d5,0x1e901b9,0x18701670137,0x9200cf009800f000ea00bd]))))
(.node (.node (.node (.leaf [0x60005e005c005a,0x910059,0x11b0113,0x21101e9,0x1e901b10189,0x650041009200660006])
(.leaf [0xc30003,0xd700a7,0x1ab017b,0x193015b0003,0x2140212020c020a01e9,0x520069002e00560091]))
(.node (.leaf [0x198019601940192,0xa70077,0x165015d,0x2330213,0x21d,0x6b000500a1])
(.leaf [0x610031,0xd900d1,0x1c901a1,0x10300cb00a3,0x3016201aa0192018f])))
(.node (.node (.leaf [0xf000ee00ec00ea,0x73006b,0x157014f,0x21b01f3,0x23b020b01eb,0x1ec01bf01f401c3])
(.leaf [0x1e50005,0xeb00bb,0x1990191,0xa5006d004d,0x18a01b5015a015e018e0155,0x9]))
(.node (.leaf [0x240023e023c023a,0xc10099,0x1950165,0x75003d0005,0x7006a009c,0x1e4021401bb01e60216021b])
(.leaf [0x6d0045,0xf700ef,0x1f701bf,0x1b501750155,0x3016201b6015a])))))
(.node (.node (.node (.node (.leaf [0x40003e003c003a,0x810051,0x12100f9,0x1ef01e7,0x1c7018f016f,0x3009d])
(.leaf [0x9b0003,0xd3009b,0x1b10179,0xf700d70007,0xc400ec00ba00c200bc00ca,0x1e4021401e6021601c10221]))
(.node (.leaf [0x178017601740172,0x9f0077,0x1850155,0x2390211,0xd5,0x18c01bc016401c4016201ba019401c2])
(.leaf [0x490021,0xf700c7,0x1c70197,0xef00cf0097,0x300a2006c,0x77])))
(.node (.node (.leaf [0xd000ce00cc00ca,0x710069,0x165013d,0x22101f1,0x22901f101c9,0x64003c0071])
(.leaf [0x1b50005,0xc700bf,0x1b70187,0x9d00650045,0xd1007600a600a200720071,0xca]))
(.node (.leaf [0x218021602140212,0x1ab008b,0x18d0165,0x23d0235,0x700f0009000c3,0xca00c30009])
(.leaf [0x6f003f,0x10300db,0x1eb01bb,0x19101590141,0x18a01b9015e018e015a0159]))))
(.node (.node (.node (.leaf [0x80007e007c007a,0x8d005d,0x1570137,0x1f301eb,0x21b01e301bb,0x420065009c])
(.leaf [0xcb0003,0xe100a9,0x1b3017b,0x6500450015,0x30196018501910165,0x501ef0214020c]))
(.node (.leaf [0x1c001be01bc01ba,0x95008d,0x187015f,0x23f0217,0x700ee011f,0xc400c20007])
(.leaf [0x1530033,0xfd00cd,0x1df01af,0x11b00eb00cb,0x3008a006d])))
(.node (.node (.leaf [0x120011e011c011a,0x9b006b,0x17f014f,0x22701f7,0xfc,0x1c401bb01f401f1])
(.leaf [0x210019,0xcb00c3,0x19b0193,0xc900a10069,0x301aa016201b501b1,0x9d]))
(.node (.leaf [0x6b0003,0xc90099,0x197016f,0xc100610009,0x20006009200660096,0x1e4020c021401eb0221])
(.leaf [0x750045,0x11900f1,0x1f701c7,0x1b7018f0157,0x1aa01b7017a014e01760189]))))))
(.node (.node (.node (.node (.node (.leaf [0x20001e001c001a,0x790051,0x11b00f3,0x1e901e1,0x1c101a10169,0x3009d0067])
(.leaf [0x970007,0xcf009f,0x1ad0175,0xf900c10009,0xec00ba00ca00bc00c9,0x5020c021401be01ee]))
(.node (.leaf [0x168016601640162,0x9b0073,0x17f0157,0x233020b,0x153,0x501c401ba01f4])
(.leaf [0x45001d,0xf100c9,0x1c10199,0xed00b50095,0x300a2006c009d,0x9e])))
(.node (.node (.leaf [0xc000be00bc00ba,0x6d0065,0x15f013f,0x21b01eb,0x22301eb01c3,0x42006a006f])
(.leaf [0x18d0005,0xc300bb,0x1910189,0x9300530033,0x92009400bc00ba008a0069,0xca00c9]))
(.node (.leaf [0x20001fe01fc01fa,0xbf008f,0x1710169,0x23f021f,0x700ee008e00cb,0x73])
(.leaf [0x690041,0x10700d7,0x1c701bf,0x18d0155013d,0x3008a]))))
(.node (.node (.node (.leaf [0x70006e006c006a,0x67005f,0x13b0133,0x21701e7,0x1ef01c7018f,0x65009c0070001c007400140041])
(.leaf [0xc70007,0xdb00a3,0x1af017f,0x1f501950005,0x18201e501b9017a01aa,0x501940214020c01c301ee]))
(.node (.leaf [0x1b001ae01ac01aa,0xa5007d,0x1690161,0x2390219,0x700a60107,0x420004009f])
(.leaf [0x5b0033,0xf700cf,0x1b701af,0x10900d100a9,0x3017a018701ac01b901aa])))
(.node (.node (.leaf [0x108010601040102,0x77006f,0x173014b,0x22101f9,0x241021101f1,0x5016301820156])
(.leaf [0x1d0015,0xef00bf,0x1bf018f,0xc900910069,0x30042006d,0x65]))
(.node (.leaf [0x670007,0xc50095,0x1990169,0x7900410009,0x700c9,0x1c4019401c2019201c1])
(.leaf [0x710049,0x11300eb,0x1f301c3,0x1b901790159,0x17e017a01560185])))))
(.node (.node (.node (.node (.leaf [0x50004e004c004a,0x610059,0x11d00fd,0x20b01e3,0x1e501ad0185,0x65003f00920007])
(.leaf [0x9f0007,0xd900a1,0x187017f,0x17b015b0003,0x7200a200cf00a80078006f,0x1e4020c01f10217]))
(.node (.leaf [0x188018601840182,0xa30073,0x1890159,0x21f0217,0x105,0x5016401c4])
(.leaf [0x55002d,0xd300cb,0x1c3019b,0xfd00c5009d,0x3016201aa0192018f0165])))
(.node (.node (.leaf [0xe000de00dc00da,0x970067,0x1690141,0x1ff01f7,0x237021f01e7,0x1c4018f01c801f801f401ef])
(.leaf [0x1bd0005,0xe700bf,0x193018b,0xa100690049,0x18201b5017a01af,0xd3]))
(.node (.leaf [0x228022602240222,0xbd0095,0x1910169,0x5f003f0007,0x7009c006a00d1,0x9600d10092])
(.leaf [0x4b0043,0xed00e5,0x1f101c1,0x1af0187014f,0x3016201b5]))))
(.node (.node (.node (.leaf [0x98009600940092,0x910061,0x15d0135,0x1f901f1,0x22101e901c1,0x4005c009400c40092])
(.leaf [0xd10009,0xbf00b7,0x1b7017f,0x6900490019,0x9a00ca0076000300a200c40071,0xc200c900cf00ec]))
(.node (.leaf [0x1e001de01dc01da,0x990091,0x18d015d,0x223021b,0x700ee00a600d1,0x4200cf])
(.leaf [0x47003f,0xdf00d7,0x1dd01b5,0x12100f100d1,0x300d2009c])))
(.node (.node (.leaf [0x140013e013c013a,0x9f006f,0x15d0155,0x22501fd,0x2b,0x5016401c401bb])
(.leaf [0x3f0017,0xd100c9,0x1a10199,0xcb00a3006b,0x3016201b501b001e7017b,0x70]))
(.node (.leaf [0x6f0007,0xa5009d,0x19d016d,0xd700770007,0x200060005004400920066,0x1ec021401ee022001e9])
(.leaf [0x790049,0xfd00f5,0x1fb01c3,0x1bb01830163,0x301620157])))))))
(.node (.node (.node (.node (.node (.node (.leaf [0x18001600140012,0x77004f,0x11900f9,0x1e701df,0x1bf019f0167,0x3009d0069])
(.leaf [0x950005,0xcb009b,0x1810179,0xf700bf0007,0x52006700300058008f,0x5020c021401be01ee0220]))
(.node (.leaf [0x160015e015c015a,0x810079,0x17d0155,0x2190211,0x63,0x501c401ba01f401f0])
(.leaf [0x410021,0xef00c7,0x1bf0197,0xe300c3008b,0x30076009d00a9,0x3c])))
(.node (.node (.leaf [0xb800b600b400b2,0x990061,0x15d013d,0x21901f1,0x221020101c1,0x42006a0009])
(.leaf [0x18b0003,0xe900b9,0x18f0187,0x9100690031,0x11400d10116011e00f1,0x1940214020c000501c3]))
(.node (.leaf [0x1f801f601f401f2,0xbd008d,0x16f0167,0x23b021b,0x7008e00c900bb,0x6b])
(.leaf [0x67003f,0x10300d3,0x1c301bb,0x18901690139,0x3008a00cf]))))
(.node (.node (.node (.leaf [0x68006600640062,0x65005d,0x11f0117,0x21301e3,0x1eb01c3018b,0x65009c00700047])
(.leaf [0xc50005,0xd900a9,0x1ad017d,0x1db017b0003,0x1e5018001b0017a01aa0185,0x1e401ec021401ee01bf01e2021a0220]))
(.node (.leaf [0x1a0019e019c019a,0xa90079,0x167015f,0x2370217,0x700a600de00d3,0x6b009c0005])
(.leaf [0x3b0033,0xf300cb,0x1b501ad,0x10700cf00a7,0x301b6018e01560185])))
(.node (.node (.leaf [0xf800f600f400f2,0x75006d,0x1590151,0x21f01f7,0x23f020f01ef,0x501c4016301ba])
(.leaf [0x1ed0005,0xed00bd,0x1bb018b,0xc7008f0067,0x30042006d0069,0x4]))
(.node (.leaf [0x650005,0xc30093,0x1970167,0x77003f0007,0x7006a,0x5020c01c401c201920191])
(.leaf [0x6f0047,0xf900f1,0x1f901c1,0x1b701770157,0x3016201b6])))))
(.node (.node (.node (.node (.leaf [0x48004600440042,0x5f0057,0x10500fd,0x1f101e9,0x1c901910171,0x3])
(.leaf [0x9d0005,0xd7009f,0x185017d,0xf900d90009,0x44006900460076007400a1,0x5020c021401ba01ef]))
(.node (.leaf [0x180017e017c017a,0xa10079,0x1870157,0x21b0213,0xf5,0x18c01640162019401c3018e01bf])
(.leaf [0x33002b,0xf900c9,0x1c90199,0xf100d10099,0x3016201aa017a01b5,0x0])))
(.node (.node (.leaf [0xd800d600d400d2,0x950065,0x167013f,0x1fb01f3,0x233021b01e3,0x18c016301560189])
(.leaf [0x1bb0003,0xc900c1,0x1b90189,0x9f00670047,0x92009400bc006400ba008a,0x9b]))
(.node (.leaf [0x220021e021c021a,0xbb0093,0x18f0167,0x5d003d0005,0x6e006a009b00a600760069,0xca00c3])
(.leaf [0x710041,0x10700df,0x1ef01bf,0x1ad0185014d,0x30162018401b9]))))
(.node (.node (.node (.leaf [0x90008e008c008a,0x8f005f,0x1590139,0x1f701ef,0x21f01e701bf,0x9400c400920007])
(.leaf [0xcf0007,0x1c500a5,0x1b5017d,0x6700470017,0xca0076000300a2007800a8009d,0xc9008a008c005c0069]))
(.node (.leaf [0x1c801c601c401c2,0x97008f,0x1890161,0x2410219,0xc600ee011e00d100f3,0x4200cb])
(.leaf [0x45003d,0xdb00d3,0x1e101b1,0x11f00ef00cf,0x9a00d2009c00d1])))
(.node (.node (.leaf [0x138013601340132,0x9d006d,0x1810151,0x22901f9,0x13,0x5016401c401bb018f])
(.leaf [0x330013,0xcf00c7,0x19f0197,0xd100990071,0x18a01b5015a016001900155,0x6f]))
(.node (.leaf [0x6d0005,0xa3009b,0x1990171,0xd300730003,0x21f01fa01c401fc01c201bf,0x5020c01c401c2018e])
(.leaf [0x770047,0x20d00ed,0x1f901c9,0x1b901910159,0x301b7017a]))))))
(.node (.node (.node (.node (.node (.leaf [0x30002e002c002a,0x7f004f,0x11f00f7,0x1eb01e3,0x1c3018b016b,0x42003c00440071])
(.leaf [0x990009,0xd100a1,0x1af0177,0xf300d30003,0x500ec0044008a00ba00c20052006a0067,0x5020c01c401c2]))
(.node (.leaf [0x170016e016c016a,0x9d0075,0x1810159,0x237020f,0xcd,0x18c016401c40162019401c201c1])
(.leaf [0x47001f,0xf300c3,0x1c30193,0xeb00cb0093,0x300a2006c00d1,0x75])))
(.node (.node (.leaf [0xc800c600c400c2,0x6f0067,0x1610141,0x21f01ef,0x22701ef01c7,0x42006a])
(.leaf [0x1b30003,0xc500bd,0x1b50185,0x93006b0033,0x92009400bc00ba008a0067,0xca00c4]))
(.node (.leaf [0x210020e020c020a,0xc10091,0x18b0163,0x2410221,0x9600ee00d1009200ea00bd,0x7])
(.leaf [0x6d003d,0x10900d9,0x1c901c1,0x18f0157013f,0x301b90187017a]))))
(.node (.node (.node (.leaf [0x78007600740072,0x690061,0x1550135,0x21901e9,0x1f101c90191,0x420065009c0070])
(.leaf [0xc90009,0xdf00a7,0x1b10181,0x21501f50005,0xca007100c4000300a9,0xca00c400c7]))
(.node (.leaf [0x1b801b601b401b2,0x93008b,0x185015d,0x23b0213,0xc600ee011f00cb,0x42009c])
(.leaf [0x630033,0xf900d1,0x1b901b1,0x11500fd00c5,0x3008a006d00cf])))
(.node (.node (.leaf [0x118011601140112,0x790071,0x17d014d,0x22301f3,0x32,0x501c40163])
(.leaf [0x1f0017,0xf100c1,0x1c10191,0xc7009f0067,0x301aa016201b501b101e9,0x6d]))
(.node (.leaf [0x690009,0xc70097,0x193016b,0xbd005d0005,0x92006600960005,0x5020c01c401c2018e0192])
(.leaf [0x730043,0x11700ef,0x1f501c5,0x1b5018d0155,0x18201b7017a0156])))))
(.node (.node (.node (.node (.leaf [0x58005600540052,0x8f0057,0x21d00fd,0x20f01e7,0x1e701af0187,0x65009c00700049])
(.leaf [0xa10009,0xd300a3,0x1890181,0x17d015d0005,0xcf01180120011400ef,0xc200c700d10067]))
(.node (.leaf [0x190018e018c018a,0xa50075,0x163015b,0x2210219,0x11d,0x18c01bc01ec019401f401c3])
(.leaf [0x5f002f,0xd700cf,0x1c7019f,0xfd00dd009d,0x18f0154017c017a01b7])))
(.node (.node (.leaf [0xe800e600e400e2,0x990069,0x155014d,0x20101f9,0x239022101e9,0x501c4019201ba018f])
(.leaf [0x1e30003,0xe900c1,0x197018f,0x9b007b0043,0x18201aa01e901b5017a,0x9009f]))
(.node (.leaf [0x238023602340232,0xbf0097,0x1930163,0x6100410009,0x7006a0069,0x501c401f4])
(.leaf [0x6b0043,0xf300eb,0x1f301bb,0x1b101890151,0x18a01620185015a0157]))))
(.node (.node (.node (.leaf [0xa0009e009c009a,0x95005d,0x15f0137,0x21301eb,0x21b01fb01bb,0x420065])
(.leaf [0x1830003,0xc100b9,0x1b90181,0x6b0033001b,0xca000300c4009f,0x5009e00d600a40071]))
(.node (.leaf [0x1e801e601e401e2,0xb3008b,0x18f015f,0x227021f,0x9e00a6010600cb00d9,0x42])
(.leaf [0x490041,0xe100d9,0x1e501b5,0x18501650135,0x92008a00c900ba006400bc])))
(.node (.node (.leaf [0x150014e014c014a,0xa10071,0x15f0157,0x213020b,0x3b,0x501c401ba01f401f9])
(.leaf [0x410019,0xeb00c3,0x1bb0193,0xcf00a7006f,0x1ba01890192019601be0169,0x79]))
(.node (.leaf [0x710009,0xa7009f,0x17d0175,0xd900790009,0x20006000500440092,0x5021401be01ee022001e3])
(.leaf [0x1630043,0x11300f3,0x1ff01c7,0x1bd01850165,0x18a0162015a01560189]))))))))
set_option maxHeartbeats 2500000 in
def hintsWheel : Table := (.node (.node (.node (.node (.node (.leaf [0x5e021c,0x1810033002e02110173,0x1300028002201fc011f,0x11b0020002501f60143002b014c0142011e002601460027027d01fa0119027c005000b50273014f0155016b,0x17e002e0032020b018e0031029d01cb0029013b002301580136005a029c0160017201750178,0x18c00300035020e01a7003602bd0193019001840031020c002e01760173002d015c00280160015702bc005300570059005a01cc02b80229,0x1b9000c000500a600730010000a009f009b0094007502da02b3022002dd02d6022202db])
(.leaf [0x1901ef00e1001d0014010300f800e400df0228,0x1b00f501ea0017001500f400f000e9001600cc00c901be0011000c01e800bf00a4022702240225021d,0xc60016001000e900c40225,0x1e60015023500dd00af0014000f023b004e004b00430224,0xe00b1008f0013000901c300b700ad0090001a000f01da00e500d50097008b0014000a004c0044003c000102ad00ea00dd029001d40294004601e702ac0221022602220286021d021c,0x8e000e000901db008c0221]))
(.node (.leaf [0xff021d,0x7c0006000c01d700a6,0x2b0257025d016a0050,0xc80265026f025b028500800281,0x13f002a002402040202013200280023015f0159013e013b0029016201640167,0x1b500390038021a01a4003402160187003001ae01ab01a2018c003501b201a6003602c5002d0194019101850176005700590229,0xc02b302e002e502e4])
(.leaf [0x840007000d01d900ab01d800770011000600aa00a20083007f006f000c0005009a00790074000b0095007300a300be0220,0xa025402530222,0x10b001e001f01f10116002301f3013500280131012b011401110022011f010c0021027501c702740152012d012600270156005000520223,0x220130011f002800210153012e0127012801340223,0x73000a000500940075000b0295006e0240003e003a000102b500ba0222022002b202b40286,0xc202d5])))
(.node (.node (.leaf [0x6c021c,0x670004000801d10088021f,0x251001500f300ef00e8001601be000c00ca00aa004d00a401e802240225021d,0x6007f006e000c0005009b007a0075000b00950073003d0080028100a400a70265009e0220,0x19f0037003302140180002e021201b101740036002d019401760031019c01990196018d017b003202a10057005a02a00229,0x1b500380039021701b3021b01a500360034003101ac01a901a601a00190003502c1018b0188003002c002bf0059005a0229,0x29502db02df])
(.leaf [0x1db000e000a00ad0096000f00b600b1003b004300bd0222,0x109001d001c01ef00fd0228,0xf009600b802700013027101c100f8001a00e600e300d600bd001400eb00de0041004901e7026f00c80265026d0226021d,0x241000601bb00700005009a00790074000b00940072000a00480040003c0291029002200222,0x7802b0,0x2cd02cb]))
(.node (.leaf [0xcd0017001101e800bf001000c4001500ee00e700c800c50047004e021d0224,0x14b002b002602070146,0x1fe002c00280021015401510125005200540223,0xc90011001601df00e700a80015000c00c700c400c100a60010004e0047028901ce0002005b000301d001d4009d009900620060000b0005007e007a006f00640071009302250224021e021c0220,0x15026e01df00c8001100aa000c00c300c000a5001002a900ce02a70081007d0240028e004a00420099009d01d402240286021c,0x20e0036003002bf0229])
(.leaf [0x7c0006000c01d500a4023901ba006f0005009c007b0076000b00930071000a0238003b003f02200222,0x1600e901be0015000c00c600c300a5001001d7007f0006006f000500730045004d00740079009a009e022502240220,0x26a01230269002601c901c70279014602760150002c005400b502730277,0x18d00310032020c017e002e029901cb00290179017601730162002d015c01590028029800530057005a01340138,0x1b500390038021a01a4003402180189003001ac01a901a0018a003501b401a8003602b90194019101850031020c0175002e002d016501620029015c015900570059005a013902a701cc02b80229,0x102b4028602d9]))))
(.node (.node (.node (.leaf [0x6a021c,0x5b0002000301ce0064000601d00078000b0076007000620060000501b600090092000f00970094008b0072023f003e0042021e021c02200221,0x161002d00290201013b,0x10b001e001f01f20117002301f3013500280130012a011301100022011f010c00210153012e01270223,0x2e02990173002d017e017a0057005a,0x3601a7020d0035002d019201770031018a01840057005a0229,0x9c02df])
(.leaf [0x1101e900bf001b001000f400ca00c700c20227,0x1a01c400e50016001400ec00e900df001500c600c30049022602250224,0x8b000a000901db008f000e00ad009000b30256001300d602220221,0x7000060005007a0075000b01d4028f028401d501e7028d00960093008a0071003a0220021c021d,0x23500dc00b4001301c2001a00e400d300b702ad028e000100ec004f001502af02ae01e7004602ac01d40294022602860224021d021c,0x1100ca00a90016000c00c500be01b90010029500a0009c003a0046022502b3]))
(.node (.leaf [0x107021d,0x109001d001c01ee00fc0228,0x1240021002601fd014f0223,0xca0011001600a801df00e7000c001500a500c300c600c00010004f00480001028701d4009d0099000b00750005007f0070003a00710093022502240286021c0220,0x20a00310028018e015800320029017a01770163015c002d0299017b01720164,0x20e0036003001a6018a003502c70195019201860031020a002801590029016202c302c602980172016402c401cc02b8013902a700ce001100fe00c902440016006e00c500be01e102950010000b01dc009400c400e9003a003e004600530059005a0001004f00ac00b601d302b700bc022902b20225021c02b40286])
(.leaf [0x7c0006000c01d700a6001000c2001501ba006f02370005009e009a00790074000b00950073003f0047004e02240220,0x147002700260209014c002b0257014e0154016a,0x10b001e001f01f00115002301f4013600280131012b0114011100220120010d012c0151,0x19f00330037021201b10213017f0036002e019d019a0197017d00320193018d0031029701cb0029017a017701740163002d015b01580057005a0229,0x15900280029020b0165002e017e0032018e0031029d017801750160015a02a802a300530057005a013902a7,0xc01c0009a0016000b00c600a5009f004002b3022502d702b2])))
(.node (.node (.leaf [0xed021d,0xf8001a001900ec00dc0015001300e500e200de00d50014024300b2000e024200c2001000a5000c007c00060241008f00870069000901b901b6000500a0009c007b0076000b0094008b0072003e0046004a0226022402210220,0x1be02550016000b00c600c0009f001000e900c4003d0045026102630225,0x6f00060005007b00760220,0x13f002a0024020301330023020501360028015d0157013c002901680165002e01740163015c,0x160002d002901740166002e020b02c3015b015802be0057013902a701cc02b8,0x1b902da02e2])
(.leaf [0x1e60019000f00da00b7,0xe00b3008d0013000900b900af0092000f0097008b0221,0x14a0026026b00b5027301500147,0x241000601b9006e00050072000a00a0009c0095007b0076000b0293003e000102920291023a0290022002220286,0x23a02b2,0x1402cc02b602d3]))
(.node (.leaf [0xfb001c001901ec00e10014010200fa00e6001a00ea00dd0104010a021d0226,0x1a01c400e60016001400eb00e800de001501e100ca0049022602250224,0x1900d90248025601ec00e100d400bb00140105010200fa00e6001a01c4001600c7001000eb00e800de00c30041004500490093009e021d02260225,0x301d0005d000b000200750061005f0005028b01cd007d00630006028a028800710093021c021e0220,0xbb0014000f00dd00980015000a023b004e004b0043003b000100c40048001002ab02aa0290009d01d40294022402220286021c,0x2c602cb017202c400fe024500b2000e02c901cc013902b802a700ce001100c900aa008e008600680016000c000900c500be01b901b600100005009f009b0075000b0095008c0073000a02c801d300b600ac02b70046003e003a000100e900c4004f001500de00bc02b6022502b30221022002b20222021c028602b40224])
(.leaf [0x98000f000a0042003a0222,0x10b001e001f01f10116002301f501370028012f01290112010f00220121010e002102590152012d0126002701c7020902580050005201540223,0x12200260021014801270027027b014f01550223,0x14d002c002601fd01c800280022015601530148012e0027012601230120029b01ff029a01340128005100530055,0x166002e002901730162002d02bb015a002802ba00530057013902a7,0x3e02da])))))
(.node (.node (.node (.node (.leaf [0x66021c,0x5b0002000301cf0065000601d00078000b0075006f0061005f000501b600090095008c0073000a0091023d003a003e021e021c022002210222,0x10b001e001f01f20117002301f401360028012f01290112010f00220120010d0021025e0153012e012700270208002b01c70149005000520154016a0223,0x12f002800220153012e0027027801fd012000500052015501c7027e027a,0x19f00370033021001af021401800036002e019e019b0198017e00320194018e0031029d01cb0029013a0023015901370028029e0178017501720160015a0053005a029c0229,0x1a700360035019301900031018c01860229,0xb02dc02b202de])
(.leaf [0x1101eb00bf001b001000f200c800c5001601c5001a022e00ec00e900c40047004b022d022b022702250226,0x1be0016000c00e900a80015001100c600c300c00010024e024c00a0009c02250224,0xc70016001000e800c30015026e0045004d02250224,0x1a00fa00eb02710015001300e400e000dd00d301bd0014000900bc00b80091000f004f004c00440001028e0226022402210286,0xd20012001801e300f701e200b00019000e00db00d700cf00b3008f0013000901c300fa00b700ad0090001a000f00e400e000d30097008b0014000a004c0044003c000100eb00de004e029001d40294004601e702ac0221022602220286021d021c,0x295006e000b02440094000a02ce01bc00b2001301d300b600ac000f01e500db001900bd00d600e3003a003e00420001004c00f8001a00eb00e602b20222021c022602b40286]))
(.node (.leaf [0x106021d,0xa80011000c01e0009b,0x1220021002601fd014f002c026601c7002201560148012e012700270200002d0163002901390129005000540056013001520158015b0223,0x920009000f01b70043008a00960221,0x13f002a0024020301330023015e013d013a0204002900280163015c002d02a602980167016402a501cb02a3029f029c00530057,0x1b500390038021b01a5003401b2021601870036003001ad01aa01a701a1018b018601950229])
(.leaf [0xa80011000c01e1009c000b0093000a023601bf00c9001600c500be00a3001000e900c4003b003f004702220225,0x11b0025002001f90118002101f701260027014801420124011e0026014b0144014e01540223,0x183002f0030016d025f01ca002b0266025d0170016f016a005800b50273,0x17b002e0032020b018e,0xb01de0094000f023d003e00420001004f02b202b40286,0xe702d5])))
(.node (.node (.leaf [0x6d021c,0xf8001a001900eb00db0015001300e600e300df00d602260224,0x1a01c400e50016001400ec00e900df001501e000c900110262000b024f01e700bf003d00450049004d0261022602250224021d,0x6007e006e000c0005009c007b0076000b00940072003d0080028100a400a70265009e0220,0x19f0037023e01b00036019c0199019602150032002e029901790173002d0195017702a202a00057005a0229,0x3102bd019502c20059005a,0x1002d602dd02e1])
(.leaf [0x1e40019000f00da00b70013023201c2001a00e600e300d600bd001401e7001000c7001600ea00e700dd00c200430047004b00c902310226021d0225,0xe00b4008d0013000900b800ae0091000f0098008c0221,0x8c000a000901da008e000e00ad00960090000f00b900b40013023401c100f8001a00e500e200d500bc001400ec00df0015027201e7026f00c80265026d00410049004d0222022102260224021d,0xa3000c0010007f0246000601b9006e00050073000a009f009b0094007a00750291029000010292023a022002220286,0x7c02b0,0x2d201cc013902c402b802a700ce00fe02d102cf0015000100df004c02b60224028602b4]))
(.node (.leaf [0xcb0017001101e800bf001000c2001500f000e900ca00c70016022a00f600f30047004e021d02240225,0x11b0020002501f7014401fb011a002b0021014a01400122011c0026014701260027024a01500156016c0223,0x2080030002b024b00500058016c0171,0xa3000c001001bb0048009f009b0001000b023a01d00003005c000200620060003a00930286021c021e,0xbb0014000f00dd01dc00970015000a004f004c0044003c000100c30047029001d40294022402220286021c,0x19502ca01a6018a003502c701920031020a0028015900290162015b02c300530059005a0164])
(.leaf [0x8e0233000900f9008c001a000a00ea009600900015000f00e600df00bd003b0043004e01d4023a0221022602220224021c,0x1600e801be0015000c00c700c400a6001001d6007e0006007000050072000a025a009e009a0093007900740045004d0225022402200222,0x12400260021014601250223,0x14d002c002601fe0124002101c8011f002201310028015501520147012d00270296005100530055012801340223,0x165002e002901740163,0x3a02da]))))
(.node (.node (.node (.leaf [0x6b021c,0xa30010000c01d6007e,0x24c001101e700bf001000a0000b00a900a5009b003d0045004d021d,0x2d01620200024d0023015c013700280130012a0022012100210151012c012500270280027f01c7027e0155027a0050005200560223,0x280298020a0164002e0174015c0031002d018e017d017900530057005a,0x1b500380039021701b30036021901a301930034003101ae01ab01a2019201880229,0xa002df])
(.leaf [0x1901ed00e1001d0014010500fa00e6001a01c50016023000ea00e700dd0015022f022b0047004b004e022d0228022602250224,0xf5001b001701eb00cd0227,0x1e50019000f00da00b7,0x94000b000a0040003c0001009e0046023a02220286,0x7702b0,0xaa0011000c00be01b90010000501dd0073000a01e0009b00940075000b02d0003a003e00460001004c00c300e802b30220022202b202b40286]))
(.node (.leaf [0x108021d,0x1a100350034018c0189,0x11b0025002001f6014301fb011a002b0021014b01410123011d0026016c0150002c026801c7002201540146012c012500270260012b00230267015b01580152013601300050005400560223,0x9009101b8023d0001003a008a02210286,0xe80015001601df00c8001100a9000c00c700c400c100a60099007d00ce02a700810240028e004a004201d4022402250286021c,0x670004000801d20089021f])
(.leaf [0xc20015001002370047004e00a0000b0093000a0238003b003f02240222,0x1310028002201fc011f,0x22012101300021026a027800520125012c0276002c027700540223,0x19f00330037021101b00036021301930031019e019b0198018f0032017f017b017601790229,0x18c00300035020d01a6,0x1bb000c0005009b00750071000b029100a4009e001002d80048004002b3022002b202d6])))
(.node (.node (.leaf [0xf1021d,0xf8001a001900ec00dc0015001300e500e200de00d50014024302260224,0x24700c101be0016000b00c700a600a0001000e800c3001502640263003d0045004d02250224,0x7000060005007a0075000b028401d50071000a02830282009e003d0080028102200222,0x13f002a0024020201320023020601370028015d0157013c002901690166002e01730162015b002d02a4,0x18a00300035020f01a8,0xa502e3])
(.leaf [0xd10018001201e200b0000e008e0009008c000a01e300ad00960090000f00d800d000b900f700130019023401c200f9001a00ec001500e400e000dd00d300ba003b0043004e0221022202260224,0xa80011000c01e1009c,0x12f0028002201fe0121,0x72000a00050095007602220220,0x29100960010000f00c500b800160013027101c601c300fa001a00eb00e800c30015004f0048004400ba00d300e000e402b2022502260224,0x850007000d01d900ab001100a900a10082000c009a000b024701c000ca001601d800c500be001000e800c30015004f00480040000101e7004a02d402b102b302b2022502b00224028602b4021d]))
(.node (.leaf [0xfd001c001901ec00e10014010000f800e4001a00ec00df0015022c010a0104004b004e021d02260224,0x10b001f001e01f5010e0021012001130110002201c9002901f0013901150125012c013101590223,0x25200190104010100f900d9001a025601c401ec00e100d400bb0016025000c6001000ec00e900c40015026c009e009300410045004d0226021d02250224,0x9d0010023a0047000100a00040028c003a0286,0x14023b004b,0x32019b017c003602c402b90178017202c600590185018e019101940229])
(.leaf [0x96000f000a0044003c0001023c0222,0x11b0025002001f90118002101f801270027014701410123011d002601ca002f01820030025c016e014c014500500058014e0154016f01700223,0x11b0020002501f80145002b014a0140011c00260148014f016b,0x19f00370033021001af021501810036002e019d019a0197017d00320195018f017201780229,0x1b500390038021901a302180249003001ad01aa018b003501b401a801840190,0x4602da]))))))
def contextWheel := context 541 rowsWheel
set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem isoWheel : (contextWheel).proof [] :=
  refute 541 201 rowsWheel hintsWheel (by decide +kernel)
end OMA.ColorPlane.Cert


namespace OMA.ColorPlane
open Mathlib.Tactic
open Sat

def ValidClause (edge : Nat → Nat → Bool) (triple : Nat → Nat → Nat → Bool)
    (fixed : Nat → Bool) : Sat.Clause → Bool
  | [.pos a, .pos b, .pos c, .pos d] =>
      a % 4 == 0 && b == a+1 && c == a+2 && d == a+3
  | [.neg a, .neg b] => a%4 == b%4 && edge (a/4) (b/4)
  | [.neg a, .neg b, .neg c] => a%4 == b%4 && a%4 == c%4 && triple (a/4) (b/4) (c/4)
  | [.pos a] => fixed a
  | _ => false

theorem valid_satisfies {f : Sat.Fmla} {c : Nat → Fin 4}
    {edge : Nat → Nat → Bool} {tri : Nat → Nat → Nat → Bool} {fixed : Nat → Bool}
    (check : f.all (ValidClause edge tri fixed))
    (hedge : ∀ i j, edge i j → c i ≠ c j)
    (htri : ∀ i j k, tri i j k → ¬(c i = c j ∧ c i = c k))
    (hfix : ∀ a, fixed a → (c (a/4)).val = a%4) :
    Sat.Valuation.satisfies_fmla (fun q => (c (q/4)).val = q%4) f := by
  refine ⟨fun l hl => ?_⟩
  have ok := List.all_eq_true.mp check l hl
  fun_cases ValidClause edge tri fixed l
  case case1 a b e d =>
    simp only [ValidClause, Bool.and_eq_true, beq_iff_eq] at ok
    obtain ⟨⟨⟨ha,rfl⟩,rfl⟩,rfl⟩ := ok
    simp only [Valuation.satisfies, Valuation.neg]
    have h := (c (a/4)).isLt
    have e1 : (a+1)/4 = a/4 := by omega
    have e2 : (a+2)/4 = a/4 := by omega
    have e3 : (a+3)/4 = a/4 := by omega
    simp only [e1,e2,e3]; omega
  case case2 a b =>
    simp only [ValidClause, Bool.and_eq_true, beq_iff_eq] at ok
    exact fun ha hb => hedge _ _ ok.2 (Fin.ext (ha.trans (ok.1.trans hb.symm)))
  case case3 a b d =>
    simp only [ValidClause, Bool.and_eq_true, beq_iff_eq] at ok
    exact fun ha hb hd => htri _ _ _ ok.2
      ⟨Fin.ext (ha.trans (ok.1.1.trans hb.symm)), Fin.ext (ha.trans (ok.1.2.trans hd.symm))⟩
  case case4 a => exact fun h => h (hfix a ok)
  all_goals simp_all [ValidClause]
end OMA.ColorPlane

namespace OMA.ColorPlane

abbrev Quad := ℤ × ℤ × ℤ × ℤ

noncomputable def point (v : Quad) : ℂ :=
  ⟨(v.1 + v.2.1 * (Real.sqrt 3 * Real.sqrt 11)) / 12,
    (v.2.2.1 * Real.sqrt 3 + v.2.2.2 * Real.sqrt 11) / 12⟩

def unitDelta (p q : Quad) : Bool :=
  let a := p.1-q.1
  let b := p.2.1-q.2.1
  let c := p.2.2.1-q.2.2.1
  let d := p.2.2.2-q.2.2.2
  a^2 + 33*b^2 + 3*c^2 + 11*d^2 == 144 && a*b+c*d == 0

private theorem sqnorm_one {w : ℂ} (h : w.re^2 + w.im^2 = 1) : ‖w‖ = 1 := by
  have k := Complex.sq_norm w
  rw [Complex.normSq_apply] at k
  nlinarith [norm_nonneg w]

theorem unitDelta_sound (p q : Quad) (h : unitDelta p q) : ‖point p - point q‖ = 1 := by
  rcases p with ⟨a,b,c,d⟩; rcases q with ⟨a',b',c',d'⟩
  simp only [unitDelta, Bool.and_eq_true, beq_iff_eq] at h
  have h1 : ((a:ℝ)-a')^2+33*((b:ℝ)-b')^2+3*((c:ℝ)-c')^2+11*((d:ℝ)-d')^2=144 := by exact_mod_cast h.1
  have h2 : ((a:ℝ)-a')*((b:ℝ)-b')+((c:ℝ)-c')*((d:ℝ)-d')=0 := by exact_mod_cast h.2
  apply sqnorm_one
  change (_ / 12 - _ / 12)^2 + (_ / 12 - _ / 12)^2 = 1
  let r := Real.sqrt 3
  let s := Real.sqrt 11
  have hr : r^2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : s^2 = 11 := Real.sq_sqrt (by norm_num)
  change ((a + b*(r*s))/12 - (a' + b'*(r*s))/12)^2 + ((c*r+d*s)/12-(c'*r+d'*s)/12)^2 = 1
  calc
    _ = ((((a:ℝ)-a')^2+33*((b:ℝ)-b')^2+3*((c:ℝ)-c')^2+11*((d:ℝ)-d')^2) +
           2*(((a:ℝ)-a')*((b:ℝ)-b')+((c:ℝ)-c')*((d:ℝ)-d'))*(r*s))/144 := by
      ring_nf; rw [hr, hs]; ring
    _ = _ := by rw [h1, h2]; norm_num
end OMA.ColorPlane

namespace OMA.ColorPlane

private def ren (a b d : Fin 4) (k : Fin 4) : Fin 4 :=
  if k = a then 0 else if k = b then 1 else if k = d then 2 else 3

private theorem ren_inj : ∀ a b d : Fin 4, a ≠ b → a ≠ d → b ≠ d →
    ∀ x y, ren a b d x = ren a b d y → x = y := by decide +kernel

private def allBase : Cert.Table := (.node (.node (.node (.node (.node (.node (.leaf [8497166,9304151,8796123,8005534,8804321,8013732,8771687,8788075])
(.leaf [8255445,8271833,9029788,8239199,9037986,8247397,7739369,8546354]))
(.node (.leaf [8779731,9570328,9062300,9594910,7448610,7981220,7473192,8263789])
(.leaf [9062422,8497178,7772125,8521760,9271395,8546342,7981098])))
(.node (.node (.leaf [7714897,9062296,8271963,9562142,8280161,7473188,9045928,8538156])
(.leaf [9037718,8796249,7706589,8497056,7714787,8521638,9312361]))
(.node (.leaf [8505364,7997592,9570332,8763359,7481378,8771557,7981224,9328623])
(.leaf [7731159,8521882,9328733,8546464,9336931,8247271,8005802]))))
(.node (.node (.node (.leaf [9304017,9336919,8239195,9545758,8247393,7456804,8804455,8529836])
(.leaf [8779861,8763481,9062556,8271967,7722851,8280165,9279593]))
(.node (.leaf [8497044,9586712,9553948,8005790,7464994,8013988,7489576,9295855])
(.leaf [9054358,8529946,9295965,8480928,9304163,8538278,8013866])))
(.node (.node (.leaf [7747665,9553944,9029532,9578526,9037730,7489572,7456808,8546476])
(.leaf [9029654,8505242,7739357,8562592,7747555,8513574,7989162]))
(.node (.leaf [8513684,8239065,9586716,8796127,7497762,8804325,7706601,7739503])
(.leaf [7763927,8763355,9320669,8771553,7980964,8280039,8263659])))))
(.node (.node (.node (.node (.leaf [9287633,9320535,8812507,9070494,8231009,7972900,8788071,8497068])
(.leaf [8271829,8288217,9046172,8255583,9054370,8263781,7755753]))
(.node (.leaf [8255571,9054232,9021468,7989406,7981090,7997604,8005672,9046062])
(.leaf [9037974,6948890,9279581,8554528,9287779,8505510,7997482])))
(.node (.node (.leaf [7731281,9021464,8288347,9046046,9021346,8005668,7972904,8513708])
(.leaf [9054102,8812633,7722973,8529824,7731171,8554406,9328745]))
(.node (.leaf [8538132,8013976,9054236,8779743,8013858,8787941,9046184,7723119])
(.leaf [7747543,8554650,9345117,8755169,9296099,8263655,8247275]))))
(.node (.node (.node (.leaf [9320401,7997336,8255579,9029662,8263777,7989284,9029544,8505388])
(.leaf [8796245,8779865,7747421,8288351,7698403,8488870,9295977]))
(.node (.leaf [8529812,9070616,9037852,8022174,7997474,8755173,8022056,9312239])
(.leaf [7714775,8489114,9312349,8513696,9320547,8230887,7989418])))
(.node (.node (.leaf [7997458,9037848,9045916,9062430,9054114,8022052,7989288,8787949])
(.leaf [9046038,8538010,7755741,8488992,7763939,10094630,8005546]))
(.node (.leaf [8546452,8255449,9070620,8812511,7973026,8231013,7722985,7755887])
(.leaf [9287767,8779739,7989150,8787937,7997348,8755303,8771691]))))))
(.node (.node (.node (.node (.node (.leaf [8546318,7739479,8280027,9054110,8288225,9062308,8255591,8271979])
(.leaf [8787925,8804313,7997596,8771679,8005794,8779877,9320425]))
(.node (.leaf [8263635,8005656,7972892,9021598,9545762,9029796,9570344,7997486])
(.leaf [7989398,8513562,7698525,8538144,7706723,8489126,9029674])))
(.node (.node (.leaf [9295953,7972888,8804443,7997470,8812641,9570340,8013736,8497324])
(.leaf [8005526,8280153,9287645,8513440,9295843,8538022,7747689]))
(.node (.leaf [8521748,9046168,8005660,8247263,9578530,8255461,7997608,9287791])
(.leaf [9312215,8538266,7764061,8562848,7772259,8779751,9054378]))))
(.node (.node (.node (.leaf [7739345,7980952,8771675,7981086,8779873,9553956,8288359,8546220])
(.leaf [8263765,8247385,9295709,8804447,9320291,8812645,7714921]))
(.node (.leaf [8513428,8022040,7989276,9054366,9562146,9062564,9586728,7731183])
(.leaf [9279447,8546330,7731293,8497312,7739491,8554662,9062442])))
(.node (.node (.leaf [9328721,7989272,7997340,8013854,8005538,9586724,9553960,8255469])
(.leaf [7997462,8521626,9320413,8472608,9328611,6948902,9037738]))
(.node (.leaf [8530068,8771545,8022044,8280031,9594914,8288229,9287657,9320559])
(.leaf [7706711,8247259,7972766,8255457,9029540,8812519,8796139])))))
(.node (.node (.node (.node (.leaf [7722961,7755863,8755291,7448606,8763489,9021476,8271975,8513452])
(.leaf [8247381,8231001,8013980,8788063,9070754,8796261,9336809]))
(.node (.leaf [8788051,7489560,7456796,9037982,9029666,9046180,9054248,7714799])
(.leaf [8005782,10094618,7714909,8570912,7723107,8521894,9046058])))
(.node (.node (.leaf [9312337,7456792,7980956,7481374,7989154,9054244,9021480,8530092])
(.leaf [7981078,8488858,9304029,8546208,9312227,8497190,7764073]))
(.node (.leaf [8497300,8755161,7489564,8263647,9062434,8271845,9062568,9304175])
(.leaf [9328599,8230875,7723229,8239073,7747811,8796135,8779755]))))
(.node (.node (.node (.leaf [7755729,9045912,8788059,7464990,8796257,9037860,7997352,8521772])
(.leaf [7989142,8263769,9271261,8480672,9279459,8505254,7731305]))
(.node (.leaf [8546196,9029784,7473180,8230879,9046050,8239077,9070632,7747567])
(.leaf [9295831,8505498,7747677,8530080,7755875,8763367,9037994])))
(.node (.node (.leaf [9046034,7473176,8013724,7497758,8021922,9070628,9037864,8779885])
(.leaf [8013846,8554394,9336797,8505376,9344995,8529958,9054122]))
(.node (.leaf [8771541,8787929,7981212,8755295,7989410,8763493,9304041,8497202])
(.leaf [7723095,8263643,9037726,8271841,9045924,8239207,8255595])))))))

private def bvert (i : Nat) : Quad :=
  let n := allBase.get i
  (↑(n % 64)-32, ↑(n / 64 % 64)-32, ↑(n / 4096 % 64)-32, ↑(n / 262144 % 64)-32)

def bedge (i j : ℕ) := unitDelta ((bvert i)) ((bvert j))

def bfixed (a : ℕ) := a == 455*4 || a == 117*4 || a == 112*4 ||
  a == 240*4+1 || a == 368*4+2

set_option maxRecDepth 50000 in
set_option maxHeartbeats 8000000 in
private theorem bcert : Cert.contextBase.all (ValidClause bedge (fun _ _ _ => false) bfixed) := by
  decide +kernel

private noncomputable def bp (n : Nat) : ℂ := point (bvert n)

private theorem bedge_sound (i j : Nat) (h : bedge i j) : ‖bp i - bp j‖ = 1 :=
  unitDelta_sound ((bvert i)) ((bvert j)) h

theorem forbidden (g : ℂ → Fin 4) (h : ∀ z w, ‖z-w‖=1 → g z ≠ g w) :
    ¬(g 1 = g ⟨-1/2, Real.sqrt 3/2⟩ ∧ g 1 = g ⟨-1/2,-Real.sqrt 3/2⟩) := by
  rintro ⟨hy,hz⟩
  have p1 : bp 455 = 1 := by change point (12,0,0,0) = 1; apply Complex.ext <;> norm_num [point]
  have p2 : bp 117 = ⟨-1/2,Real.sqrt 3/2⟩ := by
    change point (-6,0,6,0) = _
    apply Complex.ext <;> norm_num [point]
    ring
  have p3 : bp 112 = ⟨-1/2,-Real.sqrt 3/2⟩ := by
    change point (-6,0,-6,0) = _
    apply Complex.ext <;> norm_num [point]
    ring
  let A := g (bp 455)
  let B := g (bp 240)
  let D := g (bp 368)
  have ab : A ≠ B := h _ _ (bedge_sound 455 240 (by decide +kernel))
  have ad : A ≠ D := h _ _ (bedge_sound 455 368 (by decide +kernel))
  have bd : B ≠ D := h _ _ (bedge_sound 240 368 (by decide +kernel))
  let cv (i : Nat) := ren A B D (g (bp i))
  have ce (i j) (he : bedge i j) : cv i ≠ cv j := fun hh =>
    h _ _ (bedge_sound i j he) (ren_inj A B D ab ad bd _ _ hh)
  have fh : ∀ a, bfixed a → (cv (a/4)).val = a%4 := by
    intro a hfix
    simp only [bfixed, Bool.or_eq_true, beq_iff_eq] at hfix
    rcases hfix with (((ha|ha)|ha)|ha)|ha <;> subst a
    · norm_num [cv, ren, A]
    · change (ren A B D (g (bp 117))).val = 0
      rw [p2, ←hy, ←p1]; simp [ren,A]
    · change (ren A B D (g (bp 112))).val = 0
      rw [p3, ←hz, ←p1]; simp [ren,A]
    · change (ren A B D B).val = 1; simp [ren, ab.symm]
    · change (ren A B D D).val = 2; simp [ren, ad.symm,bd.symm]
  exact Cert.isoBase _ (valid_satisfies bcert ce (by simp) fh)
end OMA.ColorPlane


namespace OMA.ColorPlane

abbrev WheelCoord := Nat × Int × Int

-- x + √5 x' + i√3(y + √5 y'), with all coordinates scaled by 16.
private structure WC where
  x : ℤ
  x' : ℤ
  y : ℤ
  y' : ℤ

private def coords (p : WheelCoord) : WC :=
  let a := 2*p.2.1+p.2.2
  let b := p.2.2
  if p.1 = 0 then ⟨8*a, 0, 8*b, 0⟩ else ⟨7*a, -3*b, 7*b, a⟩

private def subc (p q : WC) : WC := ⟨p.x-q.x,p.x'-q.x',p.y-q.y,p.y'-q.y'⟩
private noncomputable def value (v : WC) : ℂ :=
  ⟨(v.x + Real.sqrt 5*v.x')/16, Real.sqrt 3*(v.y + Real.sqrt 5*v.y')/16⟩
noncomputable def wpoint (p : WheelCoord) : ℂ := value (coords p)
theorem wpoint_neg_two : wpoint (0,-2,0) = -2 := by
  apply Complex.ext <;> norm_num [wpoint,value,coords]
theorem wpoint_pos_two : wpoint (0,2,0) = 2 := by
  apply Complex.ext <;> norm_num [wpoint,value,coords]

private theorem subc_value (p q : WC) : value (subc p q) = value p - value q := by
  apply Complex.ext <;> simp [value, subc] <;> ring

private def normCheck (d : ℕ) (u : WC) : Bool :=
  decide (u.x^2+5*u.x'^2+3*u.y^2+15*u.y'^2=256*(d:ℤ) ∧ 2*u.x*u.x'+6*u.y*u.y'=0)

private theorem normCheck_sound (d : ℕ) (u : WC) (h : normCheck d u) :
    ‖value u‖ ^ 2 = (d : ℝ) := by
  obtain ⟨h0,h1⟩ := of_decide_eq_true h
  have h0' : (u.x:ℝ)^2+5*(u.x':ℝ)^2+3*(u.y:ℝ)^2+15*(u.y':ℝ)^2 = 256*(d:ℝ) := by exact_mod_cast h0
  have h1' : 2*(u.x:ℝ)*(u.x':ℝ)+6*(u.y:ℝ)*(u.y':ℝ) = 0 := by exact_mod_cast h1
  rw [Complex.sq_norm, Complex.normSq_apply]
  dsimp [value]
  have h5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  ring_nf at *
  linear_combination (norm := ring_nf) h0'/256 + Real.sqrt 5*h1'/256 +
    h3*((u.y:ℝ)+Real.sqrt 5*(u.y':ℝ))^2/256 +
    h5*((u.x':ℝ)^2+3*(u.y':ℝ)^2)/256

def wedge (p q : WheelCoord) : Bool := normCheck 1 (subc (coords p) (coords q))

theorem wedge_sound (p q : WheelCoord) (h : wedge p q) : ‖wpoint p - wpoint q‖ = 1 := by
  have hs := normCheck_sound _ _ h
  rw [subc_value] at hs
  change ‖value (coords p) - value (coords q)‖ = 1
  simp only [Nat.cast_one] at hs
  nlinarith [norm_nonneg (value (coords p) - value (coords q))]

private noncomputable def sixth : ℂ := ⟨1/2, Real.sqrt 3/2⟩

-- The third vertex is recovered by a 60-degree rotation of the second.
private def turnCheck (u v : WC) : Bool := decide
  (2*v.x = u.x-3*u.y ∧ 2*v.x' = u.x'-3*u.y' ∧ 2*v.y = u.y+u.x ∧ 2*v.y' = u.y'+u.x')

private theorem turnCheck_sound (u v : WC) (h : turnCheck u v) : value v = value u * sixth := by
  obtain ⟨ha,hb,hc,hd⟩ := of_decide_eq_true h
  have ha' : 2*(v.x:ℝ) = (u.x:ℝ)-3*(u.y:ℝ) := by exact_mod_cast ha
  have hb' : 2*(v.x':ℝ) = (u.x':ℝ)-3*(u.y':ℝ) := by exact_mod_cast hb
  have hc' : 2*(v.y:ℝ) = (u.y:ℝ)+(u.x:ℝ) := by exact_mod_cast hc
  have hd' : 2*(v.y':ℝ) = (u.y':ℝ)+(u.x':ℝ) := by exact_mod_cast hd
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  apply Complex.ext
  · rw [Complex.mul_re]
    dsimp [value, sixth]
    linear_combination ha'/32 + Real.sqrt 5*hb'/32 +
      h3*((u.y:ℝ)+Real.sqrt 5*(u.y':ℝ))/32
  · rw [Complex.mul_im]
    dsimp [value, sixth]
    linear_combination Real.sqrt 3*hc'/32 + Real.sqrt 3*Real.sqrt 5*hd'/32

private def oriented (p q r : WheelCoord) : Bool :=
  let u := subc (coords q) (coords p)
  normCheck 3 u && turnCheck u (subc (coords r) (coords p))

def wtri (p q r : WheelCoord) : Bool := oriented p q r || oriented p r q

private theorem oriented_sound (c : ℂ → Fin 4)
    (hc : ∀ z w : ℂ, ‖z-w‖=1 → c z ≠ c w)
    (hn : ∀ g : ℂ → Fin 4, (∀ z w : ℂ, ‖z-w‖=1 → g z ≠ g w) →
      ¬(g 1 = g ⟨-1/2, Real.sqrt 3/2⟩ ∧ g 1 = g ⟨-1/2,-Real.sqrt 3/2⟩))
    (p q r : WheelCoord) (h : oriented p q r) :
    ¬(c (wpoint p) = c (wpoint q) ∧ c (wpoint p) = c (wpoint r)) := by
  obtain ⟨he,ht⟩ := Bool.and_eq_true_iff.mp h
  have he' := normCheck_sound _ _ he
  have ht' := turnCheck_sound _ _ ht
  simp only [subc_value] at he' ht'
  change ‖wpoint q - wpoint p‖ ^ 2 = 3 at he'
  change wpoint r - wpoint p = (wpoint q - wpoint p) * sixth at ht'
  let b : ℂ := ⟨-1/2, Real.sqrt 3/2⟩
  let e : ℂ := ⟨-1/2, -Real.sqrt 3/2⟩
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hb : ‖b-1‖^2 = 3 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num [b]; nlinarith
  have hbe : b-1 ≠ 0 := by intro hz; simp [hz] at hb
  have her : e-1 = (b-1)*sixth := by
    apply Complex.ext <;> norm_num [e,b,sixth,Complex.mul_re,Complex.mul_im] <;> nlinarith
  let u := (wpoint q - wpoint p)/(b-1)
  have hu : ‖u‖ = 1 := by
    rw [show ‖u‖ = ‖wpoint q - wpoint p‖ / ‖b-1‖ by simp [u]]
    apply (div_eq_one_iff_eq (norm_ne_zero_iff.mpr hbe)).mpr
    nlinarith [norm_nonneg (wpoint q - wpoint p), norm_nonneg (b-1)]
  let f := fun z : ℂ => wpoint p + (z-1)*u
  have hf : ∀ z w : ℂ, ‖z-w‖=1 → c (f z) ≠ c (f w) := by
    intro z w hzw
    apply hc
    rw [show f z - f w = (z-w)*u by dsimp [f]; ring, norm_mul, hzw, hu, one_mul]
  have h1 : f 1 = wpoint p := by simp [f]
  have hq : f b = wpoint q := by dsimp [f,u]; field_simp; ring
  have hr : f e = wpoint r := by
    have hbq : (b-1)*u = wpoint q - wpoint p := by dsimp [u]; field_simp
    calc
      _ = wpoint p + ((b-1)*u)*sixth := by dsimp [f]; rw [her]; ring
      _ = wpoint r := by rw [hbq]; linear_combination -ht'
  intro ⟨hpq,hpr⟩
  apply hn (fun z => c (f z)) hf
  change c (f 1) = c (f b) ∧ c (f 1) = c (f e)
  simpa only [h1,hq,hr] using And.intro hpq hpr

theorem wtri_sound (c : ℂ → Fin 4) (hc : ∀ z w : ℂ, ‖z-w‖=1 → c z ≠ c w)
    (hn : ∀ g : ℂ → Fin 4, (∀ z w : ℂ, ‖z-w‖=1 → g z ≠ g w) →
      ¬(g 1 = g ⟨-1/2, Real.sqrt 3/2⟩ ∧ g 1 = g ⟨-1/2,-Real.sqrt 3/2⟩))
    (p q r : WheelCoord) (h : wtri p q r) :
    ¬(c (wpoint p) = c (wpoint q) ∧ c (wpoint p) = c (wpoint r)) := by
  rcases Bool.or_eq_true_iff.mp h with h|h
  · exact oriented_sound c hc hn p q r h
  · exact fun ⟨hq,hr⟩ => oriented_sound c hc hn p r q h ⟨hr,hq⟩
end OMA.ColorPlane

namespace OMA.ColorPlane

private def allWheel : Cert.Table := (.node (.node (.node (.node (.leaf [54,6,74,53,11])
(.leaf [82,40,97,87,61]))
(.node (.leaf [96,86,60,7,75])
(.leaf [52,10,83,41])))
(.node (.node (.leaf [64,38,28,85,43])
(.leaf [20,72,51,9]))
(.node (.leaf [50,8,65,39,29])
(.leaf [84,42,21,73]))))
(.node (.node (.node (.leaf [48,22,12,69,27])
(.leaf [98,56,35,103]))
(.node (.leaf [34,102,49,23,13])
(.leaf [68,26,99,57])))
(.node (.node (.leaf [80,70,44,101,59])
(.leaf [36,88,67,25]))
(.node (.leaf [66,24,81,71,45])
(.leaf [100,58,37,89])))))

private def wvert (i : Nat) : WheelCoord :=
  let n := allWheel.get i
  (n%2, ↑(n/2%8)-3, ↑(n/16%8)-3)

private noncomputable def wp (i : Nat) := wpoint (wvert i)

private def we (i j : ℕ) := wedge (wvert i) (wvert j) || (i == 6 && j == 31)

private def wt (i j k : ℕ) := wtri (wvert i) (wvert j) (wvert k)

private def wf (a : ℕ) := a == 6*4 || a == 31*4+1

set_option maxRecDepth 50000 in
set_option maxHeartbeats 8000000 in
private theorem wcert : Cert.contextWheel.all (ValidClause we wt wf) := by decide +kernel

private def norm2 (a b : Fin 4) : Equiv.Perm (Fin 4) :=
  (Equiv.swap 0 a).trans (Equiv.swap 1 ((Equiv.swap 0 a) b))

private theorem norm2_anchors : ∀ a b : Fin 4, a ≠ b → norm2 a b a = 0 ∧ norm2 a b b = 1 := by
  decide +kernel

theorem wheel_forced (g : ℂ → Fin 4) (h : ∀ z w : ℂ, ‖z-w‖=1 → g z ≠ g w) :
    g (-2) = g 2 := by
  by_contra hh
  have a1 : wp 6 = -2 := wpoint_neg_two
  have a2 : wp 31 = 2 := wpoint_pos_two
  have ne : g (wp 6) ≠ g (wp 31) := by simpa [a1,a2] using hh
  let σ := norm2 (g (wp 6)) (g (wp 31))
  let cv (i : ℕ) := σ (g (wp i))
  have he : ∀ i j, we i j → cv i ≠ cv j := by
    intro i j hij eq
    have eq' := σ.injective eq
    simp only [we, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hij
    rcases hij with hj|⟨rfl,rfl⟩
    · exact h _ _ (wedge_sound _ _ hj) eq'
    · exact ne eq'
  have ht : ∀ i j k, wt i j k → ¬(cv i = cv j ∧ cv i = cv k) := by
    rintro i j k hik ⟨ha,hb⟩
    exact wtri_sound g h forbidden _ _ _ hik ⟨σ.injective ha, σ.injective hb⟩
  obtain ⟨h1,h2⟩ := norm2_anchors _ _ ne
  have hf : ∀ a, wf a → (cv (a/4)).val = a%4 := by
    intro a hfix
    simp only [wf, Bool.or_eq_true, beq_iff_eq] at hfix
    rcases hfix with hl|hr
    · subst a; exact congrArg Fin.val h1
    · subst a; exact congrArg Fin.val h2
  exact Cert.isoWheel _ (valid_satisfies wcert he ht hf)
end OMA.ColorPlane


namespace PlaneSpindle
theorem spindle (forced : ∀ c : ℂ → Fin 4,
    (∀ z w : ℂ, ‖z - w‖ = 1 → c z ≠ c w) → c (-2) = c 2) :
    ¬ ∃ c : ℂ → Fin 4, ∀ z w : ℂ, ‖z - w‖ = 1 → c z ≠ c w := by
  rintro ⟨c, hc⟩
  have radial (u : ℂ) (hu : ‖u‖ = 1) : c 0 = c (4*u) := by
    have h := forced (fun z => c ((z+2)*u)) (by
      intro z w hzw
      apply hc
      rw [show (z+2)*u - (w+2)*u = (z-w)*u by ring, norm_mul, hu, hzw, one_mul])
    convert h using 1 <;> congr 1 <;> ring
  let u : ℂ := ⟨1/8, Real.sqrt 63/8⟩
  let v : ℂ := ⟨-1/8, Real.sqrt 63/8⟩
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 63)
  have unit_of_coords (x : ℂ) (hx : x.re ^ 2 + x.im ^ 2 = 1) : ‖x‖ = 1 := by
    have normSq := Complex.sq_norm x
    rw [Complex.normSq_apply] at normSq
    nlinarith [norm_nonneg x]
  have hu : ‖u‖ = 1 := unit_of_coords u (by dsimp [u]; nlinarith)
  have hv : ‖v‖ = 1 := unit_of_coords v (by dsimp [v]; nlinarith)
  have edge : 4*u - 4*v = 1 := by
    apply Complex.ext <;> norm_num [u, v, Complex.mul_re, Complex.mul_im] <;> ring
  exact hc _ _ (by rw [edge, norm_one]) ((radial u hu).symm.trans (radial v hv))
end PlaneSpindle


namespace OMA.ColorPlane
open SimpleGraph

theorem graph_bound
    (h : ¬ ∃ g : ℂ → Fin 4, ∀ z w : ℂ, ‖z-w‖=1 → g z ≠ g w) :
    5 ≤ (UnitDistancePlaneGraph Set.univ).chromaticNumber := by
  by_contra! hχ
  have hn : (UnitDistancePlaneGraph Set.univ).chromaticNumber ≤ (4 : ℕ) :=
    (ENat.lt_add_one_iff (by norm_num : (4 : ℕ∞) ≠ ⊤)).mp hχ
  obtain ⟨c⟩ := chromaticNumber_le_iff_colorable.mp hn
  let e := Complex.orthonormalBasisOneI.repr
  refine h ⟨fun z => c ⟨e z, Set.mem_univ _⟩, ?_⟩
  intro z w hw
  apply c.valid
  change dist (e z) (e w) = 1
  rw [e.dist_map, dist_eq_norm, hw]
end OMA.ColorPlane

theorem OMA.solution : type_of% @Erdos508.HadwigerNelsonAtLeastFive :=
  OMA.ColorPlane.graph_bound (PlaneSpindle.spindle OMA.ColorPlane.wheel_forced)
