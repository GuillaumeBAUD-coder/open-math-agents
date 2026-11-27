import OMAReductions.R_Green14_W_3_12_R1

/-!
A reflected search for the two central cases. A hypothetical counterexample
has a triple-free red set meeting every twelve-term progression. The checker
branches on a red point or deduces a red point when only one remains on a
progression. The stored certificate records branch points. Every forced step and
leaf is recomputed by the kernel.

The broad strategy follows MrSeizy's neighboring Green14.W_3_12.R1.H1 and H3
proofs, and Vincent T. Mossman's earlier Green14.W_3_11.R1 certificates. This
checker uses its own branch stream and certificate for the two H2 seeds.
-/

namespace OMA.Green135H2

private def TripleFree (R : ℕ → Prop) :=
  ∀ a d : ℕ, 0 < d → R a → R (a + d) → R (a + 2 * d) → False

private theorem midpoint_impossible {R : ℕ → Prop} (h : TripleFree R)
    {x y z : ℕ} (hx : R x) (hy : R y) (hz : R z) (he : x + z = 2 * y) (hd : x ≠ z) :
    False := by
  rcases lt_or_gt_of_ne hd with hl | hl
  · refine h x (y - x) (by omega) hx ?_ ?_
    · rwa [show x + (y - x) = y by omega]
    · rwa [show x + 2 * (y - x) = z by omega]
  · refine h z (y - z) (by omega) hz ?_ ?_
    · rwa [show z + (y - z) = y by omega]
    · rwa [show z + 2 * (y - z) = x by omega]

private structure Shadow where
  reflected : ℕ
  doubled : ℕ
  even : ℕ
  odd : ℕ

private def spaced (i : ℕ) : ℕ := 1 <<< (9 * i)

private def atom (p : ℕ) : Shadow :=
  ⟨spaced (134 - p), spaced (2 * p),
    if p % 2 = 0 then spaced (p / 2) else 0,
    if p % 2 = 1 then spaced (p / 2) else 0⟩

private def Shadow.merge (s t : Shadow) : Shadow :=
  ⟨s.reflected ||| t.reflected, s.doubled ||| t.doubled, s.even ||| t.even, s.odd ||| t.odd⟩

private def Shadow.excluded (s : Shadow) (p : ℕ) : ℕ :=
  ((s.reflected <<< (18 * p)) >>> (9 * 134)) ||| (s.doubled >>> (9 * p)) |||
    ((if p % 2 = 0 then s.even else s.odd) <<< (9 * ((p + 1) / 2)))

private def Shadow.Valid (R : ℕ → Prop) (s : Shadow) :=
  ∀ p q, R p → R q → p ≠ q → (s.excluded p).testBit (9 * q) = false

private theorem atom_valid {R : ℕ → Prop} (h : TripleFree R) {p : ℕ}
    (hp : R p) (hbound : p < 135) : Shadow.Valid R (atom p) := by
  intro q r hq hr hd
  have h₁ : r + p ≠ 2 * q := fun he =>
    midpoint_impossible h hr hq hp he (by intro hEq; omega)
  have h₂ : q + r ≠ 2 * p := fun he => midpoint_impossible h hq hp hr he hd
  have h₃ : p + q ≠ 2 * r := fun he =>
    midpoint_impossible h hp hr hq he (by intro hEq; omega)
  have single (x i : ℕ) : (spaced x).testBit i = decide (9 * x = i) := by
    rw [spaced, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
  unfold Shadow.excluded atom
  split_ifs <;> simp only [Nat.testBit_or, Nat.testBit_shiftRight, single,
    Nat.testBit_shiftLeft, Nat.zero_testBit, Bool.or_eq_false_iff,
    Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals (repeat' apply And.intro) <;> intros <;> first | trivial | omega

private theorem merge_valid {R : ℕ → Prop} {s t : Shadow}
    (hs : s.Valid R) (ht : t.Valid R) : (s.merge t).Valid R := by
  intro p q hp hq hd
  have h₁ := hs p q hp hq hd
  have h₂ := ht p q hp hq hd
  unfold Shadow.excluded Shadow.merge at *
  split_ifs at * <;> simp_all [Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]

private structure Board where
  shadow : Shadow
  allowed : ℕ
  weight : ℕ

private def placeRed (b : Board) (p : ℕ) : Board :=
  let ban := b.shadow.excluded p
  ⟨b.shadow.merge (atom p), (b.allowed ^^^ (b.allowed &&& ban)) ||| spaced p,
    b.weight ||| (12 <<< (9 * p))⟩

private def markBlue (b : Board) (p : ℕ) : Board :=
  ⟨b.shadow, b.allowed ^^^ (b.allowed &&& spaced p), b.weight⟩

private def Covers (R : ℕ → Prop) (b : Board) :=
  ∀ t, R t → b.allowed.testBit (9 * t) = true

private theorem include_covers {R : ℕ → Prop} {b : Board} {p : ℕ}
    (hs : b.shadow.Valid R) (ha : Covers R b) (hp : R p) : Covers R (placeRed b p) := by
  intro t ht
  by_cases h : t = p
  · simp [placeRed, h, spaced, Nat.shiftLeft_eq]
  · have hn := hs p t hp ht (Ne.symm h)
    simp [placeRed, Nat.testBit_xor, ha t ht, hn]

private theorem omit_covers {R : ℕ → Prop} {b : Board} {p : ℕ}
    (ha : Covers R b) (hp : ¬ R p) : Covers R (markBlue b p) := by
  intro t ht
  have hne : p ≠ t := fun h => hp (h ▸ ht)
  simp [markBlue, spaced, Nat.testBit_xor, ha t ht, Nat.shiftLeft_eq, hne]

private def bases : Array ℕ := #[0x8040201008040201008040201, 0x40001000040001000040001000040001000040001000040001, 0x200000040000008000001000000200000040000008000001000000200000040000008000001, 0x1000000001000000001000000001000000001000000001000000001000000001000000001000000001000000001000000001, 0x8000000000040000000000200000000001000000000008000000000040000000000200000000001000000000008000000000040000000000200000000001, 0x40000000000001000000000000040000000000001000000000000040000000000001000000000000040000000000001000000000000040000000000001000000000000040000000000001, 0x200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001, 0x1000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001, 0x8000000000000000000040000000000000000000200000000000000000001000000000000000000008000000000000000000040000000000000000000200000000000000000001000000000000000000008000000000000000000040000000000000000000200000000000000000001, 0x40000000000000000000001000000000000000000000040000000000000000000001000000000000000000000040000000000000000000001000000000000000000000040000000000000000000001000000000000000000000040000000000000000000001000000000000000000000040000000000000000000001, 0x200000000000000000000000040000000000000000000000008000000000000000000000001000000000000000000000000200000000000000000000000040000000000000000000000008000000000000000000000001000000000000000000000000200000000000000000000000040000000000000000000000008000000000000000000000001, 0x1000000000000000000000000001000000000000000000000000001000000000000000000000000001000000000000000000000000001000000000000000000000000001000000000000000000000000001000000000000000000000000001000000000000000000000000001000000000000000000000000001000000000000000000000000001000000000000000000000000001]
private def positionTable : ℕ := 0x294a646b458500000b6656120e188019002c010032774433612f4639050d693a0016134d312249143e53020427650754598230502b67725a3c26002e6f006d5b2a1e15377f34206e00520843246a7e35815f6874112340257848708610281d75067a380f0a511b714e4c09005e006c7b035d6047841f574f830079177d002d7c3d4b763f633662585c0c1c5542413b00211a0073
private def progressionTable : ℕ := 0x169070000000024f0001d6000688000fa71c0049d000000000006f600148e510e702800000000428001c600062406800b8e000000004b82902b1870000021a37a000000001336520000027d000630000000000012c000000000000002dce68aad2e288bc000544000b9e0a00c00000000431000000000003f0000f5000000574000a300000000000a8219ae48000001480007e000002520001b800000000936000000000000009c8000000000027c0000000006400000000000000000000c362200000257000000000190000000026d43572c000100004f50339900000138312302e545915a85a0000010c0001a4f00000000018f0000480000007026c0010000026ae28e5c300000000005d000860004b60009a80000085ebc8259e90009dc000000645c40040b15800010800000734528000000029fc21000634000001f8710002745e2bd81a0005267f8000002f4000ed38200000029b0e0620000000018a00068306000c6143000000c906a800000000005cc18e00000000000000000007420e80020ba7c00000000000000391fa4d6845c8ba6000000000003860020f00020a000e2af494d27c7239d05200215800524001018c264a000005bf8460000003b000000000be702000000000005580008500000000000000000b0800000001bc5ca1530a19400095411c0009d000000002a062e0002280002c0000053600000000213000000768b3000000b3159822000000000012e800000000000000000014e8001df0001ed778000f0be4000000005600001b000000ed800000000000006fca1cf71080000004f8000000014513400000000392000eb8000830014e4728000010c80005c2a0000001920009a00014a0001dc7b8000012a0b9800ca60003280000000000000000068e801f1c600000276626000000000000001700029a000819ef0000002f0ab0009c8002fc0000003683716000185531844000000000000009c0003a80000002f1c20018384117a000370003e20000004d000000002543f6209d5800000000002f595e000005c1000002e000000000009862000218001791ba3292b0000001540900097a99c005371503c80030d500000000002ea00064800000000000000002e8000cf0003d49e0000000025e3939700000030308851cc9b2395a000c000071a0018601d52873c001c8000000000c683200085afd000550641f300000000000000000000000001398ecb420cb985cae8b8453000326000000af00000000000000000000000002d42a8001680000000021002f4d000000000001814128381b09f2fe0f5284001c20ea1aa5a800000000bf80071600000296000284602f30010d825151000144e700000074c00000000bdca942a1a4c50b80da00036e0c000000100c28003da0002b80042ae8c001ec16e000f925f000002130000012c0a00000014f2101eb1bc0000000081220400281000000000000004e80042531e001728000012b8001e30003a47d0008347d4fed3b2c6c400000000000000263000804000000000000000000006000320866001c30220ec000004a9000000000002ee000003a800015069901ca40000029f1ac859428000000029980000029d3f000000000000004134bc000e80010b20d800000000be000000000000001e600000162000000e08bb000000000d7000000a44100003b9052624dc000bf2830003d00015b0000000000000000038800000e24500003ef2dc000005f639a06800819288000001f000000000144c88001d1612001c1af8000df0820000000000027ab90c2c000590012c40000061060dce3a7000000b7bac000001cf0ea1c00000a0000000f101000a840001f8000000000049c0000018009e000000000000000010a0000000000029000000000000304001c00000000012f025000c717690900000000000000000420e70000cc9fa5a00052c005c60000000005b0012c8b017b00000000000000000001860c26281c00007c002138000000c0000004d8000000004aa00066ca700000000000000c161200040a0000018b4cc001c38000000000040f95635000000728000000004fea380001e51e7600017d000000fa2ea0001e40052d000ba4980006fe00000000000e80000000000013c4130004bc0000063600000000000000000f03fe00000000000e7c5700000079800000000e40002600010d4ea800086000000364b200177000000000004150000000000000000000000000e5cabb2153b294bb0003d10a5d4800000000000000000000000071c0008000000105d038000007943e0bc0c078483a790000014202c398000000000000000004c00075944800000000530000002d80027b0000d4003aa000001d6800000001040004e600000000170000c4000000508000df0000000002600107cc8000a8a0012d800408590c8800196ddc000000002003f800000a71bc9780000007b000530118001dd1880000000f2ce00000011000bac00000000c588684f000000ee26f000000000f151aa2c000000014d530dc40003e5510000d7058b69740000013ac370003b000000000c3d8a8000e817ea1800000e9016a5d0000000020ca7a0000006f0000ac0013b00051400000534000fb0273f2000001ca17e000000000000000000000077800000000e1550a170a0000ca4ac6342d2985c5436000000000000000042e0000000001c1de8349b95f00000000000050000000001b20025180015a00000000000df4000fd182a78000203080000015371e000f803d1fc0002c0000014c8000007445040000008400129800000001cd800000000150fb00000031cb3000000000cc0cf4e0000000000014c800000000000000000000030400053c00000000000e49d90000000000072c000002650005240000064e00000000000a6d0c9693ce4c80040e0005c97f800760001c200031ca5dcc20f000000000000000000014e02a0018c8003c403858b011fe000001d700038800000424a08000003f8000344a03c850c00000000000002642ca0025f0390000001180000002c6700009040976000972e2000000000a30002950000025d8000009c400131000be86c3a563f70c00049510570a30002d62bc003af0000000041d0005b1349d216b501c6000
private def placed : ℕ := 0x8040200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001008040201008040201008040201008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000201008040201008040201008040201008040201008040201008040200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040201008040201008040201008040201008040201008040201008040201008040201008040201008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008000000000000000000000000000000000000000000000000000000000000000000000000000201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040200000000000000000000000000000000000000000000000000040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008000000000000000000000000
private def shifts : ℕ := 0x200000000000000000000000000200000000000000000000000000200000000000000000000000000200000000000000000000000000200000000000000000000000000200000000000000000000000000200000000000000000000000000200000000000000000000000000200000000000000000000000000200000000000000000000000000200000000000000000000000000200000000000000000000000000000008000000000000000000000001000000000000000000000000200000000000000000000000040000000000000000000000008000000000000000000000001000000000000000000000000200000000000000000000000040000000000000000000000008000000000000000000000001000000000000000000000000200000000000000000000000040000000000000000000000000000000000000000000000000000000200000000000000000000008000000000000000000000200000000000000000000008000000000000000000000200000000000000000000008000000000000000000000200000000000000000000008000000000000000000000200000000000000000000008000000000000000000000200000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000040000000000000000000200000000000000000001000000000000000000008000000000000000000040000000000000000000200000000000000000001000000000000000000008000000000000000000040000000000000000000200000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000200000000000000000200000000000000000200000000000000000200000000000000000200000000000000000200000000000000000200000000000000000200000000000000000200000000000000000200000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000008000000000000001000000000000000200000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000008000000000000200000000000008000000000000200000000000008000000000000200000000000008000000000000200000000000008000000000000200000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000040000000000200000000001000000000008000000000040000000000200000000001000000000008000000000040000000000200000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000200000000200000000200000000200000000200000000200000000200000000200000000200000000200000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000001000000200000040000008000001000000200000040000008000001000000200000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200008000200008000200008000200008000200008000200008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008040201008040201008040201
private def allPositions : ℕ := 0x40201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201008040201

private def progression (i : ℕ) : ℕ :=
  let d := i / 135 + 1
  let e := i % 135
  if 11 * d ≤ e then bases[d - 1]! <<< (9 * (e - 11 * d)) else bases[0]!

private def pivotOf (m : ℕ) : ℕ :=
  (positionTable >>> (8 * ((m ^^^ (m - 1)) % 149))) % 256

private def slotOf (m : ℕ) : ℕ :=
  (progressionTable >>> (11 * ((m ^^^ (m - 1)) % 1637))) % 2048

private def candidatesAtMost (totals k : ℕ) : ℕ :=
  let high := placed <<< 8
  ((high + placed * k) - totals) &&& high

private def firstCount (totals : ℕ) : ℕ → ℕ → ℕ
  | 0, k => candidatesAtMost totals k
  | n + 1, k =>
    let eligible := candidatesAtMost totals k
    if eligible = 0 then firstCount totals n (k + 1) else eligible

private def choose (b : Board) : ℕ :=
  let totals := ((b.allowed ||| b.weight) * shifts) &&& (placed * 511)
  slotOf (firstCount totals 12 0)

private def readPivot (queue : Array ℕ) (i : ℕ) : ℕ :=
  (queue[i / 32]! >>> (8 * (i % 32))) % 256

private def peek (b : Board) : ℕ := progression (choose b) &&& b.allowed

private def verify (queue : Array ℕ) : ℕ → Board → ℕ → Option ℕ
  | 0, _, _ => none
  | fuel + 1, b, i =>
    let m := peek b
    if m = 0 then some i else
      let p := pivotOf m
      if m = spaced p then verify queue fuel (placeRed b p) i else
        let q := readPivot queue i
        match verify queue fuel (placeRed b q) (i + 1) with
        | none => none
        | some j => verify queue fuel (markBlue b q) j

private def Hits (R : ℕ → Prop) :=
  ∀ i, ∃ q, (progression i).testBit (9 * q) = true ∧ R q

private def Impossible (b : Board) :=
  ∀ (R : ℕ → Prop), (∀ q, R q → q < 135) → TripleFree R → Hits R →
    b.shadow.Valid R → Covers R b → False

private theorem fork {b : Board} (p : ℕ)
    (yes : Impossible (placeRed b p)) (no : Impossible (markBlue b p)) : Impossible b := by
  intro R bound free hit shadow cov
  by_cases hp : R p
  · exact yes R bound free hit (merge_valid shadow (atom_valid free hp (bound _ hp)))
      (include_covers shadow cov hp)
  · exact no R bound free hit shadow (omit_covers cov hp)

private theorem forced {b : Board} (p : ℕ) (h : peek b = spaced p)
    (yes : Impossible (placeRed b p)) : Impossible b := by
  intro R bound free hit shadow cov
  obtain ⟨q, hbit, hred⟩ := hit (choose b)
  have hm : (peek b).testBit (9 * q) = true := by simp [peek, hbit, cov q hred]
  rw [h, spaced, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow] at hm
  have he : p = q := by have := of_decide_eq_true hm; omega
  have hp : R p := he.symm ▸ hred
  exact yes R bound free hit (merge_valid shadow (atom_valid free hp (bound _ hp)))
    (include_covers shadow cov hp)

private theorem conflict {b : Board} (h : peek b = 0) : Impossible b := by
  intro R _ _ hit _ cov
  obtain ⟨p, hp, hr⟩ := hit (choose b)
  have hh : (peek b).testBit (9 * p) = true := by simp [peek, hp, cov p hr]
  simp [h] at hh

private theorem verifies (queue : Array ℕ) (fuel : ℕ) (b : Board) (i j : ℕ)
    (h : verify queue fuel b i = some j) : Impossible b := by
  induction fuel generalizing b i j with
  | zero => simp [verify] at h
  | succ fuel ih =>
    simp only [verify] at h
    split at h
    · rename_i he
      exact conflict he
    · split at h
      · rename_i he
        exact forced _ he (ih _ _ _ h)
      · split at h
        · contradiction
        · rename_i k hk
          exact fork _ (ih _ _ k hk) (ih _ _ _ h)

private theorem kernelLeaf (b : Board) (queue : Array ℕ)
    (h : (verify queue 140 b 0).isSome = true) : Impossible b := by
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp h
  exact verifies _ _ _ _ _ hj

private def blank : Board := ⟨⟨0, 0, 0, 0⟩, allPositions, 0⟩
private def seed0 : Board := placeRed (placeRed blank 66) 68
private def seed1 : Board := markBlue (placeRed (markBlue blank 66) 67) 68

private def Mono (r : ℕ → Bool) :=
  ∃ (b : Bool) (a d : ℕ), 0 < d ∧ a + (if b then 11 else 2) * d < 135 ∧
    ∀ t ≤ (if b then 11 else 2), r (a + t * d) = b

private def Red (r : ℕ → Bool) (p : ℕ) := p < 135 ∧ r p = false

private theorem red_free {r : ℕ → Bool} (h : ¬ Mono r) : TripleFree (Red r) := by
  intro a d hd ha hb hc
  apply h
  refine ⟨false, a, d, hd, hc.1, ?_⟩
  intro t ht
  change t ≤ 2 at ht
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl
  · simpa using ha.2
  · simpa using hb.2
  · exact hc.2

private theorem base_has_bit : ∀ d : Fin 13, 0 < d.val → ∀ t : Fin 12,
    bases[d.val - 1]!.testBit (9 * (t.val * d.val)) = true := by decide +kernel

private theorem red_meets {r : ℕ → Bool} {a d : ℕ} (h : ¬ Mono r)
    (hd : 0 < d) (hb : a + 11 * d < 135) :
    ∃ t, (bases[d - 1]! <<< (9 * a)).testBit (9 * t) = true ∧ Red r t := by
  by_contra! no
  apply h
  refine ⟨true, a, d, hd, hb, ?_⟩
  intro t ht
  change t ≤ 11 at ht
  have hm : (bases[d - 1]! <<< (9 * a)).testBit (9 * (a + t * d)) = true := by
    simpa [Nat.testBit_shiftLeft, Nat.mul_add, Nat.le_add_right] using
      base_has_bit ⟨d, by omega⟩ hd ⟨t, by omega⟩
  cases hr : r (a + t * d)
  · have hb' := Nat.mul_le_mul_right d ht
    exact (no _ hm ⟨by omega, hr⟩).elim
  · rfl

private theorem red_hits {r : ℕ → Bool} (h : ¬ Mono r) : Hits (Red r) := by
  intro i
  dsimp only [progression]
  split
  · apply red_meets h <;> omega
  · simpa using red_meets h (a := 0) (d := 1) (by decide) (by decide)

private theorem blank_valid (R : ℕ → Prop) : blank.shadow.Valid R := by
  intro p q hp hq hne
  simp [blank, Shadow.excluded]

private theorem blank_covers (r : ℕ → Bool) : Covers (Red r) blank := by
  have h : ∀ t : Fin 135, allPositions.testBit (9 * t.val) = true := by decide +kernel
  intro t ht
  exact h ⟨t, ht.1⟩

private theorem seed0_case (bad : Impossible seed0) (r : ℕ → Bool)
    (h₀ : r 66 = false) (h₁ : r 68 = false) : Mono r := by
  by_contra hn
  let R := Red r
  have h₂ : R 66 := ⟨by decide, h₀⟩
  have h₃ : R 68 := ⟨by decide, h₁⟩
  have free := red_free hn
  have va := blank_valid R
  have vb : (placeRed blank 66).shadow.Valid R := merge_valid va (atom_valid free h₂ (by decide))
  have vc : seed0.shadow.Valid R := merge_valid vb (atom_valid free h₃ (by decide))
  exact bad R (fun t ht => ht.1) free (red_hits hn) vc
    (include_covers vb (include_covers va (blank_covers r) h₂) h₃)

private theorem seed1_case (bad : Impossible seed1) (r : ℕ → Bool)
    (h₀ : r 66 = true) (h₁ : r 67 = false) (h₂ : r 68 = true) : Mono r := by
  by_contra hn
  let R := Red r
  have p : R 67 := ⟨by decide, h₁⟩
  have p₀ : ¬ R 66 := fun h => by simpa [h₀] using h.2
  have p₁ : ¬ R 68 := fun h => by simpa [h₂] using h.2
  have free := red_free hn
  have va : (markBlue blank 66).shadow.Valid R := blank_valid R
  have vb : seed1.shadow.Valid R := merge_valid va (atom_valid free p (by decide))
  exact bad R (fun t ht => ht.1) free (red_hits hn) vb
    (omit_covers (include_covers va (omit_covers (blank_covers r) p₀) p) p₁)

private def board_a := seed0
private def board_b := seed1
private def board_a0 := placeRed board_a 58
private def board_a1 := markBlue board_a 58
private def board_a00 := placeRed board_a0 79
private def board_a01 := markBlue board_a0 79
private def board_a000 := placeRed board_a00 82
private def board_a001 := markBlue board_a00 82
private def board_a0010 := placeRed board_a001 72
private def board_a0011 := markBlue board_a001 72
private def board_a00110 := placeRed board_a0011 88
private def board_a00111 := markBlue board_a0011 88
private def board_a010 := placeRed board_a01 71
private def board_a011 := markBlue board_a01 71
private def board_a0100 := placeRed board_a010 82
private def board_a0101 := markBlue board_a010 82
private def board_a0110 := placeRed board_a011 75
private def board_a0111 := markBlue board_a011 75
private def board_a01110 := placeRed board_a0111 77
private def board_a01111 := markBlue board_a0111 77
private def board_a011110 := placeRed board_a01111 73
private def board_a011111 := markBlue board_a01111 73
private def board_a0111110 := placeRed board_a011111 69
private def board_a0111111 := markBlue board_a011111 69
private def board_a10 := placeRed board_a1 52
private def board_a11 := markBlue board_a1 52
private def board_a100 := placeRed board_a10 55
private def board_a101 := markBlue board_a10 55
private def board_a1000 := placeRed board_a100 79
private def board_a1001 := markBlue board_a100 79
private def board_a10000 := placeRed board_a1000 88
private def board_a10001 := markBlue board_a1000 88
private def board_a10010 := placeRed board_a1001 74
private def board_a10011 := markBlue board_a1001 74
private def board_a1010 := placeRed board_a101 61
private def board_a1011 := markBlue board_a101 61
private def board_a10100 := placeRed board_a1010 63
private def board_a10101 := markBlue board_a1010 63
private def board_a101010 := placeRed board_a10101 51
private def board_a101011 := markBlue board_a10101 51
private def board_a10110 := placeRed board_a1011 57
private def board_a10111 := markBlue board_a1011 57
private def board_a101100 := placeRed board_a10110 85
private def board_a101101 := markBlue board_a10110 85
private def board_a101110 := placeRed board_a10111 63
private def board_a101111 := markBlue board_a10111 63
private def board_a1011100 := placeRed board_a101110 85
private def board_a1011101 := markBlue board_a101110 85
private def board_a1011110 := placeRed board_a101111 53
private def board_a1011111 := markBlue board_a101111 53
private def board_a10111110 := placeRed board_a1011111 54
private def board_a10111111 := markBlue board_a1011111 54
private def board_a110 := placeRed board_a11 46
private def board_a111 := markBlue board_a11 46
private def board_a1100 := placeRed board_a110 55
private def board_a1101 := markBlue board_a110 55
private def board_a11000 := placeRed board_a1100 47
private def board_a11001 := markBlue board_a1100 47
private def board_a110010 := placeRed board_a11001 72
private def board_a110011 := markBlue board_a11001 72
private def board_a1100110 := placeRed board_a110011 62
private def board_a1100111 := markBlue board_a110011 62
private def board_a11001110 := placeRed board_a1100111 32
private def board_a11001111 := markBlue board_a1100111 32
private def board_a11010 := placeRed board_a1101 61
private def board_a11011 := markBlue board_a1101 61
private def board_a110100 := placeRed board_a11010 51
private def board_a110101 := markBlue board_a11010 51
private def board_a110110 := placeRed board_a11011 79
private def board_a110111 := markBlue board_a11011 79
private def board_a1101100 := placeRed board_a110110 54
private def board_a1101101 := markBlue board_a110110 54
private def board_a1101110 := placeRed board_a110111 73
private def board_a1101111 := markBlue board_a110111 73
private def board_a11011110 := placeRed board_a1101111 82
private def board_a11011111 := markBlue board_a1101111 82
private def board_a1110 := placeRed board_a111 40
private def board_a1111 := markBlue board_a111 40
private def board_a11100 := placeRed board_a1110 55
private def board_a11101 := markBlue board_a1110 55
private def board_a111000 := placeRed board_a11100 62
private def board_a111001 := markBlue board_a11100 62
private def board_a1110010 := placeRed board_a111001 50
private def board_a1110011 := markBlue board_a111001 50
private def board_a111010 := placeRed board_a11101 73
private def board_a111011 := markBlue board_a11101 73
private def board_a1110100 := placeRed board_a111010 57
private def board_a1110101 := markBlue board_a111010 57
private def board_a1110110 := placeRed board_a111011 61
private def board_a1110111 := markBlue board_a111011 61
private def board_a11101100 := placeRed board_a1110110 51
private def board_a11101101 := markBlue board_a1110110 51
private def board_a11101110 := placeRed board_a1110111 49
private def board_a11101111 := markBlue board_a1110111 49
private def board_a111011100 := placeRed board_a11101110 85
private def board_a111011101 := markBlue board_a11101110 85
private def board_a11110 := placeRed board_a1111 49
private def board_a11111 := markBlue board_a1111 49
private def board_a111100 := placeRed board_a11110 34
private def board_a111101 := markBlue board_a11110 34
private def board_a1111000 := placeRed board_a111100 100
private def board_a1111001 := markBlue board_a111100 100
private def board_a11110000 := placeRed board_a1111000 56
private def board_a11110001 := markBlue board_a1111000 56
private def board_a11110010 := placeRed board_a1111001 88
private def board_a11110011 := markBlue board_a1111001 88
private def board_a111100110 := placeRed board_a11110011 94
private def board_a111100111 := markBlue board_a11110011 94
private def board_a1111010 := placeRed board_a111101 28
private def board_a1111011 := markBlue board_a111101 28
private def board_a11110100 := placeRed board_a1111010 42
private def board_a11110101 := markBlue board_a1111010 42
private def board_a11110110 := placeRed board_a1111011 22
private def board_a11110111 := markBlue board_a1111011 22
private def board_a111101100 := placeRed board_a11110110 88
private def board_a111101101 := markBlue board_a11110110 88
private def board_a111101110 := placeRed board_a11110111 16
private def board_a111101111 := markBlue board_a11110111 16
private def board_a111110 := placeRed board_a11111 55
private def board_a111111 := markBlue board_a11111 55
private def board_a1111100 := placeRed board_a111110 48
private def board_a1111101 := markBlue board_a111110 48
private def board_a11111000 := placeRed board_a1111100 34
private def board_a11111001 := markBlue board_a1111100 34
private def board_a11111010 := placeRed board_a1111101 50
private def board_a11111011 := markBlue board_a1111101 50
private def board_a111110110 := placeRed board_a11111011 54
private def board_a111110111 := markBlue board_a11111011 54
private def board_a1111101110 := placeRed board_a111110111 38
private def board_a1111101111 := markBlue board_a111110111 38
private def board_a1111110 := placeRed board_a111111 61
private def board_a1111111 := markBlue board_a111111 61
private def board_a11111100 := placeRed board_a1111110 50
private def board_a11111101 := markBlue board_a1111110 50
private def board_a111111010 := placeRed board_a11111101 48
private def board_a111111011 := markBlue board_a11111101 48
private def board_a1111110110 := placeRed board_a111111011 51
private def board_a1111110111 := markBlue board_a111111011 51
private def board_a11111110 := placeRed board_a1111111 43
private def board_a11111111 := markBlue board_a1111111 43
private def board_a111111100 := placeRed board_a11111110 79
private def board_a111111101 := markBlue board_a11111110 79
private def board_a1111111010 := placeRed board_a111111101 73
private def board_a1111111011 := markBlue board_a111111101 73
private def board_b0 := placeRed board_b 56
private def board_b1 := markBlue board_b 56
private def board_b00 := placeRed board_b0 72
private def board_b01 := markBlue board_b0 72
private def board_b000 := placeRed board_b00 82
private def board_b001 := markBlue board_b00 82
private def board_b0000 := placeRed board_b000 83
private def board_b0001 := markBlue board_b000 83
private def board_b00010 := placeRed board_b0001 80
private def board_b00011 := markBlue board_b0001 80
private def board_b000110 := placeRed board_b00011 89
private def board_b000111 := markBlue board_b00011 89
private def board_b0010 := placeRed board_b001 83
private def board_b0011 := markBlue board_b001 83
private def board_b00100 := placeRed board_b0010 54
private def board_b00101 := markBlue board_b0010 54
private def board_b001010 := placeRed board_b00101 89
private def board_b001011 := markBlue board_b00101 89
private def board_b0010110 := placeRed board_b001011 96
private def board_b0010111 := markBlue board_b001011 96
private def board_b00110 := placeRed board_b0011 86
private def board_b00111 := markBlue board_b0011 86
private def board_b001100 := placeRed board_b00110 73
private def board_b001101 := markBlue board_b00110 73
private def board_b0011010 := placeRed board_b001101 53
private def board_b0011011 := markBlue board_b001101 53
private def board_b00110110 := placeRed board_b0011011 63
private def board_b00110111 := markBlue board_b0011011 63
private def board_b001110 := placeRed board_b00111 80
private def board_b001111 := markBlue board_b00111 80
private def board_b0011100 := placeRed board_b001110 58
private def board_b0011101 := markBlue board_b001110 58
private def board_b0011110 := placeRed board_b001111 85
private def board_b0011111 := markBlue board_b001111 85
private def board_b00111110 := placeRed board_b0011111 81
private def board_b00111111 := markBlue board_b0011111 81
private def board_b001111110 := placeRed board_b00111111 84
private def board_b001111111 := markBlue board_b00111111 84
private def board_b010 := placeRed board_b01 60
private def board_b011 := markBlue board_b01 60
private def board_b0100 := placeRed board_b010 82
private def board_b0101 := markBlue board_b010 82
private def board_b01000 := placeRed board_b0100 73
private def board_b01001 := markBlue board_b0100 73
private def board_b010000 := placeRed board_b01000 54
private def board_b010001 := markBlue board_b01000 54
private def board_b010010 := placeRed board_b01001 77
private def board_b010011 := markBlue board_b01001 77
private def board_b01010 := placeRed board_b0101 84
private def board_b01011 := markBlue board_b0101 84
private def board_b010100 := placeRed board_b01010 46
private def board_b010101 := markBlue board_b01010 46
private def board_b010110 := placeRed board_b01011 80
private def board_b010111 := markBlue board_b01011 80
private def board_b0101110 := placeRed board_b010111 76
private def board_b0101111 := markBlue board_b010111 76
private def board_b01011100 := placeRed board_b0101110 90
private def board_b01011101 := markBlue board_b0101110 90
private def board_b010111010 := placeRed board_b01011101 86
private def board_b010111011 := markBlue board_b01011101 86
private def board_b0110 := placeRed board_b011 80
private def board_b0111 := markBlue board_b011 80
private def board_b01100 := placeRed board_b0110 48
private def board_b01101 := markBlue board_b0110 48
private def board_b011000 := placeRed board_b01100 84
private def board_b011001 := markBlue board_b01100 84
private def board_b0110010 := placeRed board_b011001 81
private def board_b0110011 := markBlue board_b011001 81
private def board_b01100110 := placeRed board_b0110011 69
private def board_b01100111 := markBlue board_b0110011 69
private def board_b011010 := placeRed board_b01101 69
private def board_b011011 := markBlue board_b01101 69
private def board_b0110100 := placeRed board_b011010 38
private def board_b0110101 := markBlue board_b011010 38
private def board_b01101010 := placeRed board_b0110101 53
private def board_b01101011 := markBlue board_b0110101 53
private def board_b011010110 := placeRed board_b01101011 73
private def board_b011010111 := markBlue board_b01101011 73
private def board_b0110110 := placeRed board_b011011 57
private def board_b0110111 := markBlue board_b011011 57
private def board_b01101110 := placeRed board_b0110111 51
private def board_b01101111 := markBlue board_b0110111 51
private def board_b011011100 := placeRed board_b01101110 84
private def board_b011011101 := markBlue board_b01101110 84
private def board_b011011110 := placeRed board_b01101111 63
private def board_b011011111 := markBlue board_b01101111 63
private def board_b0110111100 := placeRed board_b011011110 53
private def board_b0110111101 := markBlue board_b011011110 53
private def board_b01110 := placeRed board_b0111 70
private def board_b01111 := markBlue board_b0111 70
private def board_b011100 := placeRed board_b01110 54
private def board_b011101 := markBlue board_b01110 54
private def board_b0111000 := placeRed board_b011100 87
private def board_b0111001 := markBlue board_b011100 87
private def board_b01110010 := placeRed board_b0111001 81
private def board_b01110011 := markBlue board_b0111001 81
private def board_b0111010 := placeRed board_b011101 48
private def board_b0111011 := markBlue board_b011101 48
private def board_b01110110 := placeRed board_b0111011 57
private def board_b01110111 := markBlue board_b0111011 57
private def board_b011101110 := placeRed board_b01110111 69
private def board_b011101111 := markBlue board_b01110111 69
private def board_b011110 := placeRed board_b01111 74
private def board_b011111 := markBlue board_b01111 74
private def board_b0111100 := placeRed board_b011110 75
private def board_b0111101 := markBlue board_b011110 75
private def board_b01111000 := placeRed board_b0111100 52
private def board_b01111001 := markBlue board_b0111100 52
private def board_b011110010 := placeRed board_b01111001 87
private def board_b011110011 := markBlue board_b01111001 87
private def board_b01111010 := placeRed board_b0111101 69
private def board_b01111011 := markBlue board_b0111101 69
private def board_b011110100 := placeRed board_b01111010 85
private def board_b011110101 := markBlue board_b01111010 85
private def board_b011110110 := placeRed board_b01111011 63
private def board_b011110111 := markBlue board_b01111011 63
private def board_b0111101110 := placeRed board_b011110111 57
private def board_b0111101111 := markBlue board_b011110111 57
private def board_b01111011110 := placeRed board_b0111101111 54
private def board_b01111011111 := markBlue board_b0111101111 54
private def board_b0111110 := placeRed board_b011111 76
private def board_b0111111 := markBlue board_b011111 76
private def board_b01111100 := placeRed board_b0111110 54
private def board_b01111101 := markBlue board_b0111110 54
private def board_b011111000 := placeRed board_b01111100 75
private def board_b011111001 := markBlue board_b01111100 75
private def board_b0111110010 := placeRed board_b011111001 50
private def board_b0111110011 := markBlue board_b011111001 50
private def board_b01111100110 := placeRed board_b0111110011 40
private def board_b01111100111 := markBlue board_b0111110011 40
private def board_b011111010 := placeRed board_b01111101 90
private def board_b011111011 := markBlue board_b01111101 90
private def board_b0111110100 := placeRed board_b011111010 42
private def board_b0111110101 := markBlue board_b011111010 42
private def board_b0111110110 := placeRed board_b011111011 84
private def board_b0111110111 := markBlue board_b011111011 84
private def board_b01111101110 := placeRed board_b0111110111 48
private def board_b01111101111 := markBlue board_b0111110111 48
private def board_b01111110 := placeRed board_b0111111 64
private def board_b01111111 := markBlue board_b0111111 64
private def board_b011111100 := placeRed board_b01111110 86
private def board_b011111101 := markBlue board_b01111110 86
private def board_b0111111010 := placeRed board_b011111101 84
private def board_b0111111011 := markBlue board_b011111101 84
private def board_b011111110 := placeRed board_b01111111 62
private def board_b011111111 := markBlue board_b01111111 62
private def board_b0111111100 := placeRed board_b011111110 84
private def board_b0111111101 := markBlue board_b011111110 84
private def board_b01111111010 := placeRed board_b0111111101 82
private def board_b01111111011 := markBlue board_b0111111101 82
private def board_b10 := placeRed board_b1 62
private def board_b11 := markBlue board_b1 62
private def board_b100 := placeRed board_b10 84
private def board_b101 := markBlue board_b10 84
private def board_b1000 := placeRed board_b100 48
private def board_b1001 := markBlue board_b100 48
private def board_b10000 := placeRed board_b1000 96
private def board_b10001 := markBlue board_b1000 96
private def board_b100010 := placeRed board_b10001 81
private def board_b100011 := markBlue board_b10001 81
private def board_b1000110 := placeRed board_b100011 71
private def board_b1000111 := markBlue board_b100011 71
private def board_b10001110 := placeRed board_b1000111 91
private def board_b10001111 := markBlue board_b1000111 91
private def board_b100011110 := placeRed board_b10001111 61
private def board_b100011111 := markBlue board_b10001111 61
private def board_b10010 := placeRed board_b1001 52
private def board_b10011 := markBlue board_b1001 52
private def board_b100100 := placeRed board_b10010 45
private def board_b100101 := markBlue board_b10010 45
private def board_b1001000 := placeRed board_b100100 34
private def board_b1001001 := markBlue board_b100100 34
private def board_b1001010 := placeRed board_b100101 51
private def board_b1001011 := markBlue board_b100101 51
private def board_b100110 := placeRed board_b10011 44
private def board_b100111 := markBlue board_b10011 44
private def board_b1001100 := placeRed board_b100110 51
private def board_b1001101 := markBlue board_b100110 51
private def board_b1001110 := placeRed board_b100111 36
private def board_b1001111 := markBlue board_b100111 36
private def board_b10011100 := placeRed board_b1001110 54
private def board_b10011101 := markBlue board_b1001110 54
private def board_b100111010 := placeRed board_b10011101 58
private def board_b100111011 := markBlue board_b10011101 58
private def board_b10011110 := placeRed board_b1001111 64
private def board_b10011111 := markBlue board_b1001111 64
private def board_b100111110 := placeRed board_b10011111 60
private def board_b100111111 := markBlue board_b10011111 60
private def board_b1010 := placeRed board_b101 78
private def board_b1011 := markBlue board_b101 78
private def board_b10100 := placeRed board_b1010 76
private def board_b10101 := markBlue board_b1010 76
private def board_b101000 := placeRed board_b10100 88
private def board_b101001 := markBlue board_b10100 88
private def board_b1010010 := placeRed board_b101001 86
private def board_b1010011 := markBlue board_b101001 86
private def board_b101010 := placeRed board_b10101 64
private def board_b101011 := markBlue board_b10101 64
private def board_b1010100 := placeRed board_b101010 51
private def board_b1010101 := markBlue board_b101010 51
private def board_b1010110 := placeRed board_b101011 52
private def board_b1010111 := markBlue board_b101011 52
private def board_b10101100 := placeRed board_b1010110 96
private def board_b10101101 := markBlue board_b1010110 96
private def board_b101011010 := placeRed board_b10101101 100
private def board_b101011011 := markBlue board_b10101101 100
private def board_b1010110110 := placeRed board_b101011011 92
private def board_b1010110111 := markBlue board_b101011011 92
private def board_b10101110 := placeRed board_b1010111 40
private def board_b10101111 := markBlue board_b1010111 40
private def board_b101011100 := placeRed board_b10101110 88
private def board_b101011101 := markBlue board_b10101110 88
private def board_b101011110 := placeRed board_b10101111 60
private def board_b101011111 := markBlue board_b10101111 60
private def board_b1010111110 := placeRed board_b101011111 48
private def board_b1010111111 := markBlue board_b101011111 48
private def board_b10101111100 := placeRed board_b1010111110 88
private def board_b10101111101 := markBlue board_b1010111110 88
private def board_b10110 := placeRed board_b1011 80
private def board_b10111 := markBlue board_b1011 80
private def board_b101100 := placeRed board_b10110 60
private def board_b101101 := markBlue board_b10110 60
private def board_b1011010 := placeRed board_b101101 63
private def board_b1011011 := markBlue board_b101101 63
private def board_b10110100 := placeRed board_b1011010 51
private def board_b10110101 := markBlue board_b1011010 51
private def board_b10110110 := placeRed board_b1011011 69
private def board_b10110111 := markBlue board_b1011011 69
private def board_b101101100 := placeRed board_b10110110 51
private def board_b101101101 := markBlue board_b10110110 51
private def board_b101101110 := placeRed board_b10110111 81
private def board_b101101111 := markBlue board_b10110111 81
private def board_b101110 := placeRed board_b10111 76
private def board_b101111 := markBlue board_b10111 76
private def board_b1011100 := placeRed board_b101110 60
private def board_b1011101 := markBlue board_b101110 60
private def board_b10111000 := placeRed board_b1011100 96
private def board_b10111001 := markBlue board_b1011100 96
private def board_b101110010 := placeRed board_b10111001 93
private def board_b101110011 := markBlue board_b10111001 93
private def board_b1011100100 := placeRed board_b101110010 120
private def board_b1011100101 := markBlue board_b101110010 120
private def board_b10111010 := placeRed board_b1011101 63
private def board_b10111011 := markBlue board_b1011101 63
private def board_b101110110 := placeRed board_b10111011 75
private def board_b101110111 := markBlue board_b10111011 75
private def board_b1011110 := placeRed board_b101111 64
private def board_b1011111 := markBlue board_b101111 64
private def board_b10111100 := placeRed board_b1011110 86
private def board_b10111101 := markBlue board_b1011110 86
private def board_b10111110 := placeRed board_b1011111 86
private def board_b10111111 := markBlue board_b1011111 86
private def board_b101111100 := placeRed board_b10111110 60
private def board_b101111101 := markBlue board_b10111110 60
private def board_b101111110 := placeRed board_b10111111 82
private def board_b101111111 := markBlue board_b10111111 82
private def board_b1011111100 := placeRed board_b101111110 60
private def board_b1011111101 := markBlue board_b101111110 60
private def board_b10111111000 := placeRed board_b1011111100 96
private def board_b10111111001 := markBlue board_b1011111100 96
private def board_b101111110010 := placeRed board_b10111111001 108
private def board_b101111110011 := markBlue board_b10111111001 108
private def board_b10111111010 := placeRed board_b1011111101 48
private def board_b10111111011 := markBlue board_b1011111101 48
private def board_b1011111110 := placeRed board_b101111111 70
private def board_b1011111111 := markBlue board_b101111111 70
private def board_b110 := placeRed board_b11 50
private def board_b111 := markBlue board_b11 50
private def board_b1100 := placeRed board_b110 72
private def board_b1101 := markBlue board_b110 72
private def board_b11000 := placeRed board_b1100 63
private def board_b11001 := markBlue board_b1100 63
private def board_b110000 := placeRed board_b11000 86
private def board_b110001 := markBlue board_b11000 86
private def board_b110010 := placeRed board_b11001 58
private def board_b110011 := markBlue board_b11001 58
private def board_b1100100 := placeRed board_b110010 35
private def board_b1100101 := markBlue board_b110010 35
private def board_b11001010 := placeRed board_b1100101 70
private def board_b11001011 := markBlue board_b1100101 70
private def board_b1100110 := placeRed board_b110011 57
private def board_b1100111 := markBlue board_b110011 57
private def board_b11001100 := placeRed board_b1100110 38
private def board_b11001101 := markBlue board_b1100110 38
private def board_b110011010 := placeRed board_b11001101 53
private def board_b110011011 := markBlue board_b11001101 53
private def board_b11001110 := placeRed board_b1100111 59
private def board_b11001111 := markBlue board_b1100111 59
private def board_b110011100 := placeRed board_b11001110 21
private def board_b110011101 := markBlue board_b11001110 21
private def board_b110011110 := placeRed board_b11001111 55
private def board_b110011111 := markBlue board_b11001111 55
private def board_b1100111110 := placeRed board_b110011111 60
private def board_b1100111111 := markBlue board_b110011111 60
private def board_b11001111100 := placeRed board_b1100111110 83
private def board_b11001111101 := markBlue board_b1100111110 83
private def board_b11010 := placeRed board_b1101 64
private def board_b11011 := markBlue board_b1101 64
private def board_b110100 := placeRed board_b11010 86
private def board_b110101 := markBlue board_b11010 86
private def board_b1101000 := placeRed board_b110100 60
private def board_b1101001 := markBlue board_b110100 60
private def board_b1101010 := placeRed board_b110101 88
private def board_b1101011 := markBlue board_b110101 88
private def board_b11010110 := placeRed board_b1101011 80
private def board_b11010111 := markBlue board_b1101011 80
private def board_b110101110 := placeRed board_b11010111 76
private def board_b110101111 := markBlue board_b11010111 76
private def board_b110110 := placeRed board_b11011 60
private def board_b110111 := markBlue board_b11011 60
private def board_b1101100 := placeRed board_b110110 82
private def board_b1101101 := markBlue board_b110110 82
private def board_b11011000 := placeRed board_b1101100 80
private def board_b11011001 := markBlue board_b1101100 80
private def board_b110110010 := placeRed board_b11011001 86
private def board_b110110011 := markBlue board_b11011001 86
private def board_b11011010 := placeRed board_b1101101 80
private def board_b11011011 := markBlue board_b1101101 80
private def board_b110110100 := placeRed board_b11011010 94
private def board_b110110101 := markBlue board_b11011010 94
private def board_b1101101010 := placeRed board_b110110101 98
private def board_b1101101011 := markBlue board_b110110101 98
private def board_b110110110 := placeRed board_b11011011 76
private def board_b110110111 := markBlue board_b11011011 76
private def board_b1101101100 := placeRed board_b110110110 86
private def board_b1101101101 := markBlue board_b110110110 86
private def board_b11011011010 := placeRed board_b1101101101 98
private def board_b11011011011 := markBlue board_b1101101101 98
private def board_b1101101110 := placeRed board_b110110111 78
private def board_b11011011100 := placeRed board_b1101101110 88
private def board_b11011011101 := markBlue board_b1101101110 88
private def board_b110110111010 := placeRed board_b11011011101 104
private def board_b110110111011 := markBlue board_b11011011101 104
private def board_b1101110 := placeRed board_b110111 74
private def board_b1101111 := markBlue board_b110111 74
private def board_b11011100 := placeRed board_b1101110 76
private def board_b11011101 := markBlue board_b1101110 76
private def board_b110111010 := placeRed board_b11011101 80
private def board_b110111011 := markBlue board_b11011101 80
private def board_b1101110100 := placeRed board_b110111010 61
private def board_b1101110101 := markBlue board_b110111010 61
private def board_b1101110110 := placeRed board_b110111011 52
private def board_b1101110111 := markBlue board_b110111011 52
private def board_b11011101110 := placeRed board_b1101110111 48
private def board_b11011101111 := markBlue board_b1101110111 48
private def board_b110111011100 := placeRed board_b11011101110 96
private def board_b110111011101 := markBlue board_b11011101110 96
private def board_b11011110 := placeRed board_b1101111 70
private def board_b11011111 := markBlue board_b1101111 70
private def board_b110111100 := placeRed board_b11011110 48
private def board_b110111101 := markBlue board_b11011110 48
private def board_b1101111000 := placeRed board_b110111100 96
private def board_b1101111001 := markBlue board_b110111100 96
private def board_b1101111010 := placeRed board_b110111101 76
private def board_b1101111011 := markBlue board_b110111101 76
private def board_b11011110110 := placeRed board_b1101111011 80
private def board_b11011110111 := markBlue board_b1101111011 80
private def board_b110111110 := placeRed board_b11011111 58
private def board_b110111111 := markBlue board_b11011111 58
private def board_b1101111100 := placeRed board_b110111110 80
private def board_b1101111101 := markBlue board_b110111110 80
private def board_b1101111110 := placeRed board_b110111111 54
private def board_b1101111111 := markBlue board_b110111111 54
private def board_b11011111100 := placeRed board_b1101111110 76
private def board_b11011111101 := markBlue board_b1101111110 76
private def board_b110111111000 := placeRed board_b11011111100 57
private def board_b110111111001 := markBlue board_b11011111100 57
private def board_b1110 := placeRed board_b111 60
private def board_b1111 := markBlue board_b111 60
private def board_b11100 := placeRed board_b1110 44
private def board_b11101 := markBlue board_b1110 44
private def board_b111000 := placeRed board_b11100 80
private def board_b111001 := markBlue board_b11100 80
private def board_b1110000 := placeRed board_b111000 58
private def board_b1110001 := markBlue board_b111000 58
private def board_b1110010 := placeRed board_b111001 77
private def board_b1110011 := markBlue board_b111001 77
private def board_b11100100 := placeRed board_b1110010 82
private def board_b11100101 := markBlue board_b1110010 82
private def board_b111001000 := placeRed board_b11100100 86
private def board_b111001001 := markBlue board_b11100100 86
private def board_b111001010 := placeRed board_b11100101 78
private def board_b111001011 := markBlue board_b11100101 78
private def board_b11100110 := placeRed board_b1110011 71
private def board_b11100111 := markBlue board_b1110011 71
private def board_b111001110 := placeRed board_b11100111 65
private def board_b111001111 := markBlue board_b11100111 65
private def board_b111010 := placeRed board_b11101 59
private def board_b111011 := markBlue board_b11101 59
private def board_b1110100 := placeRed board_b111010 38
private def board_b1110101 := markBlue board_b111010 38
private def board_b11101000 := placeRed board_b1110100 86
private def board_b11101001 := markBlue board_b1110100 86
private def board_b111010010 := placeRed board_b11101001 98
private def board_b111010011 := markBlue board_b11101001 98
private def board_b11101010 := placeRed board_b1110101 32
private def board_b11101011 := markBlue board_b1110101 32
private def board_b111010110 := placeRed board_b11101011 26
private def board_b111010111 := markBlue board_b11101011 26
private def board_b1110101110 := placeRed board_b111010111 20
private def board_b1110101111 := markBlue board_b111010111 20
private def board_b1110110 := placeRed board_b111011 65
private def board_b1110111 := markBlue board_b111011 65
private def board_b11101100 := placeRed board_b1110110 38
private def board_b11101101 := markBlue board_b1110110 38
private def board_b111011000 := placeRed board_b11101100 86
private def board_b111011001 := markBlue board_b11101100 86
private def board_b1110110010 := placeRed board_b111011001 98
private def board_b1110110011 := markBlue board_b111011001 98
private def board_b111011010 := placeRed board_b11101101 32
private def board_b111011011 := markBlue board_b11101101 32
private def board_b1110110110 := placeRed board_b111011011 41
private def board_b1110110111 := markBlue board_b111011011 41
private def board_b11101101100 := placeRed board_b1110110110 26
private def board_b11101101101 := markBlue board_b1110110110 26
private def board_b11101101110 := placeRed board_b1110110111 29
private def board_b11101101111 := markBlue board_b1110110111 29
private def board_b111011011100 := placeRed board_b11101101110 26
private def board_b111011011101 := markBlue board_b11101101110 26
private def board_b111011011110 := placeRed board_b11101101111 35
private def board_b111011011111 := markBlue board_b11101101111 35
private def board_b1110110111100 := placeRed board_b111011011110 26
private def board_b1110110111101 := markBlue board_b111011011110 26
private def board_b11101110 := placeRed board_b1110111 47
private def board_b11101111 := markBlue board_b1110111 47
private def board_b111011100 := placeRed board_b11101110 80
private def board_b111011101 := markBlue board_b11101110 80
private def board_b1110111010 := placeRed board_b111011101 83
private def board_b1110111011 := markBlue board_b111011101 83
private def board_b11101110100 := placeRed board_b1110111010 38
private def board_b11101110101 := markBlue board_b1110111010 38
private def board_b111011101010 := placeRed board_b11101110101 32
private def board_b111011101011 := markBlue board_b11101110101 32
private def board_b11101110110 := placeRed board_b1110111011 77
private def board_b11101110111 := markBlue board_b1110111011 77
private def board_b111011101100 := placeRed board_b11101110110 38
private def board_b111011101101 := markBlue board_b11101110110 38
private def board_b111011110 := placeRed board_b11101111 41
private def board_b111011111 := markBlue board_b11101111 41
private def board_b1110111100 := placeRed board_b111011110 77
private def board_b1110111101 := markBlue board_b111011110 77
private def board_b1110111110 := placeRed board_b111011111 71
private def board_b11101111100 := placeRed board_b1110111110 38
private def board_b11101111101 := markBlue board_b1110111110 38
private def board_b111011111000 := placeRed board_b11101111100 86
private def board_b111011111001 := markBlue board_b11101111100 86
private def board_b1110111110010 := placeRed board_b111011111001 98
private def board_b1110111110011 := markBlue board_b111011111001 98
private def board_b11110 := placeRed board_b1111 58
private def board_b11111 := markBlue board_b1111 58
private def board_b111100 := placeRed board_b11110 80
private def board_b111101 := markBlue board_b11110 80
private def board_b1111000 := placeRed board_b111100 48
private def board_b1111001 := markBlue board_b111100 48
private def board_b11110000 := placeRed board_b1111000 44
private def board_b11110001 := markBlue board_b1111000 44
private def board_b111100010 := placeRed board_b11110001 59
private def board_b111100011 := markBlue board_b11110001 59
private def board_b1111000110 := placeRed board_b111100011 41
private def board_b1111000111 := markBlue board_b111100011 41
private def board_b11110010 := placeRed board_b1111001 42
private def board_b11110011 := markBlue board_b1111001 42
private def board_b111100100 := placeRed board_b11110010 44
private def board_b111100101 := markBlue board_b11110010 44
private def board_b1111001010 := placeRed board_b111100101 52
private def board_b1111001011 := markBlue board_b111100101 52
private def board_b11110010110 := placeRed board_b1111001011 32
private def board_b11110010111 := markBlue board_b1111001011 32
private def board_b111100110 := placeRed board_b11110011 45
private def board_b111100111 := markBlue board_b11110011 45
private def board_b1111001100 := placeRed board_b111100110 72
private def board_b1111001101 := markBlue board_b111100110 72
private def board_b11110011010 := placeRed board_b1111001101 44
private def board_b11110011011 := markBlue board_b1111001101 44
private def board_b111100110110 := placeRed board_b11110011011 40
private def board_b111100110111 := markBlue board_b11110011011 40
private def board_b1111001110 := placeRed board_b111100111 51
private def board_b1111001111 := markBlue board_b111100111 51
private def board_b1111010 := placeRed board_b111101 74
private def board_b1111011 := markBlue board_b111101 74
private def board_b11110100 := placeRed board_b1111010 72
private def board_b11110101 := markBlue board_b1111010 72
private def board_b111101000 := placeRed board_b11110100 35
private def board_b111101001 := markBlue board_b11110100 35
private def board_b111101010 := placeRed board_b11110101 48
private def board_b111101011 := markBlue board_b11110101 48
private def board_b1111010100 := placeRed board_b111101010 96
private def board_b1111010101 := markBlue board_b111101010 96
private def board_b1111010110 := placeRed board_b111101011 36
private def board_b1111010111 := markBlue board_b111101011 36
private def board_b11110101100 := placeRed board_b1111010110 84
private def board_b11110101101 := markBlue board_b1111010110 84
private def board_b11110101110 := placeRed board_b1111010111 52
private def board_b11110101111 := markBlue board_b1111010111 52
private def board_b111101011110 := placeRed board_b11110101111 44
private def board_b111101011111 := markBlue board_b11110101111 44
private def board_b1111010111110 := placeRed board_b111101011111 40
private def board_b1111010111111 := markBlue board_b111101011111 40
private def board_b11110110 := placeRed board_b1111011 78
private def board_b11110111 := markBlue board_b1111011 78
private def board_b111101100 := placeRed board_b11110110 44
private def board_b111101101 := markBlue board_b11110110 44
private def board_b1111011000 := placeRed board_b111101100 92
private def board_b1111011001 := markBlue board_b111101100 92
private def board_b11110110010 := placeRed board_b1111011001 104
private def board_b11110110011 := markBlue board_b1111011001 104
private def board_b1111011010 := placeRed board_b111101101 86
private def board_b1111011011 := markBlue board_b111101101 86
private def board_b11110110110 := placeRed board_b1111011011 92
private def board_b11110110111 := markBlue board_b1111011011 92
private def board_b111101110 := placeRed board_b11110111 72
private def board_b111101111 := markBlue board_b11110111 72
private def board_b1111011100 := placeRed board_b111101110 71
private def board_b1111011101 := markBlue board_b111101110 71
private def board_b1111011110 := placeRed board_b111101111 82
private def board_b1111011111 := markBlue board_b111101111 82
private def board_b11110111110 := placeRed board_b1111011111 64
private def board_b11110111111 := markBlue board_b1111011111 64
private def board_b111110 := placeRed board_b11111 64
private def board_b111111 := markBlue board_b11111 64
private def board_b1111100 := placeRed board_b111110 54
private def board_b1111101 := markBlue board_b111110 54
private def board_b11111000 := placeRed board_b1111100 53
private def board_b11111001 := markBlue board_b1111100 53
private def board_b111110000 := placeRed board_b11111000 38
private def board_b111110001 := markBlue board_b11111000 38
private def board_b111110010 := placeRed board_b11111001 65
private def board_b111110011 := markBlue board_b11111001 65
private def board_b1111100100 := placeRed board_b111110010 38
private def board_b1111100101 := markBlue board_b111110010 38
private def board_b11111010 := placeRed board_b1111101 52
private def board_b11111011 := markBlue board_b1111101 52
private def board_b111110100 := placeRed board_b11111010 74
private def board_b111110101 := markBlue board_b11111010 74
private def board_b111110110 := placeRed board_b11111011 53
private def board_b111110111 := markBlue board_b11111011 53
private def board_b1111101100 := placeRed board_b111110110 46
private def board_b1111101101 := markBlue board_b111110110 46
private def board_b11111011000 := placeRed board_b1111101100 90
private def board_b11111011001 := markBlue board_b1111101100 90
private def board_b11111011010 := placeRed board_b1111101101 40
private def board_b11111011011 := markBlue board_b1111101101 40
private def board_b111110110110 := placeRed board_b11111011011 48
private def board_b111110110111 := markBlue board_b11111011011 48
private def board_b1111101110 := placeRed board_b111110111 57
private def board_b1111101111 := markBlue board_b111110111 57
private def board_b11111011100 := placeRed board_b1111101110 65
private def board_b11111011101 := markBlue board_b1111101110 65
private def board_b11111011110 := placeRed board_b1111101111 51
private def board_b11111011111 := markBlue board_b1111101111 51
private def board_b111110111110 := placeRed board_b11111011111 55
private def board_b111110111111 := markBlue board_b11111011111 55
private def board_b1111101111100 := placeRed board_b111110111110 42
private def board_b1111101111101 := markBlue board_b111110111110 42
private def board_b1111110 := placeRed board_b111111 54
private def board_b1111111 := markBlue board_b111111 54
private def board_b11111100 := placeRed board_b1111110 76
private def board_b11111101 := markBlue board_b1111110 76
private def board_b111111000 := placeRed board_b11111100 59
private def board_b111111001 := markBlue board_b11111100 59
private def board_b1111110000 := placeRed board_b111111000 74
private def board_b1111110001 := markBlue board_b111111000 74
private def board_b1111110010 := placeRed board_b111111001 57
private def board_b1111110011 := markBlue board_b111111001 57
private def board_b11111100110 := placeRed board_b1111110011 63
private def board_b11111100111 := markBlue board_b1111110011 63
private def board_b111111001110 := placeRed board_b11111100111 55
private def board_b111111001111 := markBlue board_b11111100111 55
private def board_b111111010 := placeRed board_b11111101 78
private def board_b111111011 := markBlue board_b11111101 78
private def board_b1111110100 := placeRed board_b111111010 65
private def board_b1111110101 := markBlue board_b111111010 65
private def board_b11111101000 := placeRed board_b1111110100 72
private def board_b11111101001 := markBlue board_b1111110100 72
private def board_b111111010010 := placeRed board_b11111101001 48
private def board_b111111010011 := markBlue board_b11111101001 48
private def board_b11111101010 := placeRed board_b1111110101 59
private def board_b11111101011 := markBlue board_b1111110101 59
private def board_b111111010110 := placeRed board_b11111101011 55
private def board_b111111010111 := markBlue board_b11111101011 55
private def board_b1111110110 := placeRed board_b111111011 74
private def board_b1111110111 := markBlue board_b111111011 74
private def board_b11111101100 := placeRed board_b1111110110 61
private def board_b11111101101 := markBlue board_b1111110110 61
private def board_b111111011010 := placeRed board_b11111101101 65
private def board_b111111011011 := markBlue board_b11111101101 65
private def board_b1111110110110 := placeRed board_b111111011011 57
private def board_b1111110110111 := markBlue board_b111111011011 57
private def board_b11111101101110 := placeRed board_b1111110110111 63
private def board_b11111101101111 := markBlue board_b1111110110111 63
private def board_b11111101110 := placeRed board_b1111110111 70
private def board_b11111101111 := markBlue board_b1111110111 70
private def board_b111111011100 := placeRed board_b11111101110 44
private def board_b111111011101 := markBlue board_b11111101110 44
private def board_b111111011110 := placeRed board_b11111101111 72
private def board_b1111110111100 := placeRed board_b111111011110 65
private def board_b1111110111101 := markBlue board_b111111011110 65
private def board_b11111101111000 := placeRed board_b1111110111100 86
private def board_b11111101111001 := markBlue board_b1111110111100 86
private def board_b11111110 := placeRed board_b1111111 52
private def board_b11111111 := markBlue board_b1111111 52
private def board_b111111100 := placeRed board_b11111110 74
private def board_b111111101 := markBlue board_b11111110 74
private def board_b1111111000 := placeRed board_b111111100 57
private def board_b1111111001 := markBlue board_b111111100 57
private def board_b11111110000 := placeRed board_b1111111000 26
private def board_b11111110001 := markBlue board_b1111111000 26
private def board_b111111100010 := placeRed board_b11111110001 38
private def board_b111111100011 := markBlue board_b11111110001 38
private def board_b1111111000110 := placeRed board_b111111100011 42
private def board_b1111111000111 := markBlue board_b111111100011 42
private def board_b11111110010 := placeRed board_b1111111001 61
private def board_b11111110011 := markBlue board_b1111111001 61
private def board_b111111100110 := placeRed board_b11111110011 55
private def board_b111111100111 := markBlue board_b11111110011 55
private def board_b1111111010 := placeRed board_b111111101 72
private def board_b1111111011 := markBlue board_b111111101 72
private def board_b11111110100 := placeRed board_b1111111010 38
private def board_b11111110101 := markBlue board_b1111111010 38
private def board_b111111101010 := placeRed board_b11111110101 70
private def board_b111111101011 := markBlue board_b11111110101 70
private def board_b11111110110 := placeRed board_b1111111011 70
private def board_b11111110111 := markBlue board_b1111111011 70
private def board_b111111101100 := placeRed board_b11111110110 57
private def board_b111111101101 := markBlue board_b11111110110 57
private def board_b111111110 := placeRed board_b11111111 48
private def board_b111111111 := markBlue board_b11111111 48
private def board_b1111111100 := placeRed board_b111111110 70
private def board_b1111111101 := markBlue board_b111111110 70
private def board_b11111111000 := placeRed board_b1111111100 57
private def board_b11111111001 := markBlue board_b1111111100 57
private def board_b111111110010 := placeRed board_b11111111001 55
private def board_b111111110011 := markBlue board_b11111111001 55
private def board_b11111111010 := placeRed board_b1111111101 72
private def board_b111111110100 := placeRed board_b11111111010 74
private def board_b111111110101 := markBlue board_b11111111010 74
private def board_b1111111101010 := placeRed board_b111111110101 78
private def board_b1111111101011 := markBlue board_b111111110101 78
private def board_b1111111110 := placeRed board_b111111111 46
private def board_b11111111100 := placeRed board_b1111111110 70
private def board_b111111111000 := placeRed board_b11111111100 72
private def board_b111111111001 := markBlue board_b11111111100 72

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111111111001 : Impossible board_b111111111001 :=
  kernelLeaf board_b111111111001 #[0x71592a20543b20353b20351e6229411f145435215b3d4155693b5b60204e3950, 0x4e37285541204133282d4e56202a202a59374535606059561f5f1d2a5b1f1d2a, 0x57542f4e2462112b2c3312202a1c15592b24452f3b531715451d1426311b332c, 0x566c35392a35522a611d2a1c136129184f1d184c35393b2854414e2426452726, 0x1821573f202c45536c35292f4a47074a474a6110332c353d695d26564c5d5f45, 0x26243b3317260c68566a4b675c3f1a33525c253f3f373f3d334a70213d333f68, 0x212d4a213947264537262f4c2b2b14532f4a454e3b24333f21331726523b561d, 0x1a5a2a205635394c273726184760574a39374f3935454a393b2037596a393118, 0x515d2b5a4e20414f574f625715135a60204e3b3b20455c4a5d625c615a3b594f, 0x5f565a4f4a5c3f35414e2456592f35453b3f4f1e573f204a4e285a4e1d4f5170, 0x1a4e2c60244a45564d472d565d213f705a3f6020372656202d202a2d53416465, 0x4d4e37573d334e354a3f454a4e08295a261800] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111111111000 : Impossible board_b111111111000 :=
  kernelLeaf board_b111111111000 #[0x50184c651f285226455613216715504515261d1c0e15265a2026561a18593935, 0x85c205c0a2c6a53535508535545314b54630f561b535c4f65593f61455c714f, 0x5152564c5d5939411b505554562a2d531d59414b5c5d2d53375c5d2c4e65184e, 0x33271c37335b37532f4e57314e33574e172c53375d] (by decide +kernel)

private theorem ok_b11111111100 : Impossible board_b11111111100 :=
  fork 72 ok_b111111111000 ok_b111111111001

private theorem ok_b1111111110 : Impossible board_b1111111110 :=
  forced 70 (by decide +kernel) ok_b11111111100

private theorem ok_b111111111 : Impossible board_b111111111 :=
  forced 46 (by decide +kernel) ok_b1111111110

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111111101011 : Impossible board_b1111111101011 :=
  kernelLeaf board_b1111111101011 #[0x2d67594c53685a6d213d5e22285d3d707823685d1047231f5d54286e5f3b2652, 0x223517212d4731551e59312e50353d6c1716352231502c47394754736e515747, 0x2e1c545a2c4c5f3b1a4762172f193f332f47555e2c371c2c763d5b1f1e6a3b50, 0x5b1f6a501e49635f3b3b3b1c1a505e3923373753391e1e240f3116372050352e, 0x1f3719254725371f6a2c6e1f37193b1f1358166a3b0a2884103b1a3b3b162c62, 0x3f39655935165c502b312137513922311c211a3727415e2e473b3b3b29501c19, 0x20375339415039593f6a231524372341202121162631354b311339311e3d724f, 0x2268206135226e7c371c5e503b3d314c105035553b584c162637173126395031, 0x373b6e1e] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111111101010 : Impossible board_b1111111101010 :=
  kernelLeaf board_b1111111101010 #[0x5b5a6965725f665c5b5a5a70535a5c624c2d772f452f501e1537395f231f223b, 0x395f5223532f513d412423241a17511545375b3d51515c581a1b1a5b0e212c6a, 0x6a2d1b2d0b1c062d15205b3d5a5a705a5e4c692d5c265131242c2c2a212c6a50, 0x715a41534c4c5264623d414c242d1658074c105a31473952583952105f231f26, 0x41531c50515d5147376a2a0e641c2c520e106e74315c20525c1c1f1c162c4c1e, 0x505f5d4737572131281b64503d241b28162c4135512151211a1f2321511a641c, 0x2516452341192a1e2d1b2d1a536a505113472f52222c372c23282e535c2c502c, 0x51555e2c415b5a68312c17312c264f473950575051675e416f5150452f415d19, 0x5e262a5e2241275c6d2d6d5b174f261924265c5e2e2461772a69682057413158, 0x2226202a] (by decide +kernel)

private theorem ok_b111111110101 : Impossible board_b111111110101 :=
  fork 78 ok_b1111111101010 ok_b1111111101011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111111110100 : Impossible board_b111111110100 :=
  kernelLeaf board_b111111110100 #[0x19505065591f5a35283f1f101f1a2c2141262235412e392e091b4119222c3733, 0x316126672e214e2353621e2115672110265859582269545f5247391a26212859, 0x1b1724351b0e1f2d1a1e29252d25350f1b2d0f2d0e3126132d1e29652e542d70, 0x1f281a3f012365352e255f3b6921662f2c552d473726523b62122d5e1a1c1f25, 0x212a1f2d1f5e6524222d471a1e6a24285b3b2d2c693b454e6c55231a23675c28, 0x4b4713075065255e576a0e21172e41586e58534e505035585d2d47100c52111e, 0x25581728534f1a544b6a2e57251721135d2157281a6a0e] (by decide +kernel)

private theorem ok_b11111111010 : Impossible board_b11111111010 :=
  fork 74 ok_b111111110100 ok_b111111110101

private theorem ok_b1111111101 : Impossible board_b1111111101 :=
  forced 72 (by decide +kernel) ok_b11111111010

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111111110011 : Impossible board_b111111110011 :=
  kernelLeaf board_b111111110011 #[0x182a5033504f3d534e2c2f5047221e475f285b5d47151b0a0728213326544135, 0x5e4c5d532c552e4f4c5868265a4e502833254a5b716050471b25502c23101b33, 0x62264754334e50225f195950475321544b595554503f2c3d5355503d2c685d5e, 0x595963605225141933505525332e501b481b2a28501e4721263154182519534e, 0x514d2c3d33254f26251f59544a2e5d4c5959291f455960502c59506316481f2e, 0x570c51260d552f1c6c4c5455575019192216224c0e632127686251415e5b6858, 0x5f472c511425552f295b454a24172251220d5545501662150a5e225722314126, 0x57634726544857575f533f17201126292152132421201e6a172b50514d636721, 0x6157415e571e62475247132722584e5950546841204b505a1753625e574e4162] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111111110010 : Impossible board_b111111110010 :=
  kernelLeaf board_b111111110010 #[0x254151744754596650631f74620a0d1b595f0b4d35170917251f0b502a4c162c, 0x525b5e66225124505151334159515124505d51255d2d47541b0f206a4b7c5b1f, 0x50517063516374675f6e5b595f662d2d1068475422415b355b2559516a1f4e5e, 0x231f33621e4e414e5119335e70416e242d681b13335147580e0c170e65505033, 0x2419254d190f106210131b052519184c265959695431200a192a3359474a0835, 0x33331845526a505133351b5f0f2417190e25130f24190f17101b471854195417, 0x1b545d521b255147190c170c350f631f474e0e190c4e51631f107447246c6414, 0x5458314723316b312441511f252141515447335026353341251c4d1f184e1b35, 0x587a6a596b5f41594735514a2e4133685935245951534e41525f21251731476e, 0x535e6e5153515a415a31534e622451593545354e336841633147624b454c474a, 0x1e13121f222f47221f21472e355750471524542a275e2267224768514120575a, 0x2a222222172163452e352124161f1f132a54481f172408222f50253151150a19, 0x2d213559472a2e24544722254c15] (by decide +kernel)

private theorem ok_b11111111001 : Impossible board_b11111111001 :=
  fork 55 ok_b111111110010 ok_b111111110011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11111111000 : Impossible board_b11111111000 :=
  kernelLeaf board_b11111111000 #[0x820c1431625725355d65335247585961595d5d335f59255f6a595d214754264a, 0x52571e571e740e6d4f59135f571c60595a4f1e574c59525f542e296359455f18, 0x13091823181f1521500e0d3f6c187214181f59600d146c185a0d57604b0e251e, 0x255950544c41172557545d131f152d4c5d15252258655d59574c6c52501e4723, 0x185a4f471e59181b1f2e251421540a1f2a185d0a2222591f1454182e25173558, 0x6a6c5418542161211757171e233150474c57224f4c672b5447584c5d1f1b2d22, 0x5d222967184151355a21544f22252329625931152117525f2254265b5b692a4e, 0x1f71594550575051255960252013574f594e2a50541825592e4f595426224154, 0x294f2e6252585254265548593377145919283328260a2a2e5418605f541f2e18, 0x4f4f1f1f] (by decide +kernel)

private theorem ok_b1111111100 : Impossible board_b1111111100 :=
  fork 57 ok_b11111111000 ok_b11111111001

private theorem ok_b111111110 : Impossible board_b111111110 :=
  fork 70 ok_b1111111100 ok_b1111111101

private theorem ok_b11111111 : Impossible board_b11111111 :=
  fork 48 ok_b111111110 ok_b111111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11111110111 : Impossible board_b11111110111 :=
  kernelLeaf board_b11111110111 #[0x2a2c374722495c5a1e5a511e511e4f265a1e5b5a5a1e5b5f452e141e56393b4e, 0x2d375f3f2d2c374b3f5f54615a2a3d394f56355757295c1b2c28395d1d263569, 0x504b5e6a353f6572502c745a4b2c5035351a542314225a35285a5d1d4139562a, 0x394b35504f35543039414163263935353941505a543d263d3724182641354b49, 0x4d3f5c412062502456393535231562415124452b2b1e2b1e14393b5a2e542929, 0x3041394d3f22505008244b354b3937205456262f41201e213f22201539415061, 0x3f33376e26546212533916513b0850306e3f3f5c724f3f3f2d54621a453b4b21, 0x3d5a4d212f193124353f571d41594d543d212f] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111111101101 : Impossible board_b111111101101 :=
  kernelLeaf board_b111111101101 #[0x4f2e592c60541a5054545b315d4b4c235971182121265a1e2e601a2a4f56353f, 0x645a4551532f5b2c655b1f1e284e546a214e2e4f5c4f6154545c5d4c5355215c, 0x455f112b1a592145593345554c6b7721595e1a6845512e4e4c1d64106d5b215e, 0x2b1a1e2c214c453b59515f332a201b565e51591d3153571c552d5b51552d6931, 0x2c2e6455605f5c544d215d645c5a4e1e122754241e212460502b4e294e24101a, 0x4e245c59502f4c1f4d592e59503545372c55505a5c605c6a352e5a592a652a29, 0x1d26351a18292d231a4e291c1f35262a2c334e4b592a2d4e264d2c27594e5026, 0x2a26472d41331d41] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111111101100 : Impossible board_b111111101100 :=
  kernelLeaf board_b111111101100 #[0x2a5454595d544f62502626543150302a16292054292a60134c5c5d5412284e47, 0x1355756d597c5a564f4e4e3b5b4560544f1d54296445715950354f2a1250291d, 0x5a5c4e2067415a625a59551e5c2a135a41621f2a2e29596060594b712a61542a, 0x674c57502620292b26215c5b60504e3b2e1854561a616867545b5a1f59564c20, 0x205956512b511f565430294f18543362261d59622b695a625d2b604f201e0d] (by decide +kernel)

private theorem ok_b11111110110 : Impossible board_b11111110110 :=
  fork 57 ok_b111111101100 ok_b111111101101

private theorem ok_b1111111011 : Impossible board_b1111111011 :=
  fork 70 ok_b11111110110 ok_b11111110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111111101011 : Impossible board_b111111101011 :=
  kernelLeaf board_b111111101011 #[0x5733351b50292a4763372e562e502e56224739211f21222951671f212a3b2c4e, 0x292723271e31672a3b0a28623b37282a350e505635564549223350602f55505e, 0x3d5a3b5b5b3b212a3d2d5e3d3f2f5b0c2729292729212a3b22143d3d2229293d, 0x3b212a573d2a211d19233b49245f0c5e70111c172e7886123d0c5b622f222f27, 0x2c562e275f0a35373b2a2a3b27632f37282229292227513d2a3b142f2f455b5b, 0x35245435242a3d2335592f276e0e21235e41222d351d1c1a2337636c1a393f22, 0x6e37473d59372a7135503d353d2f1d2a6916591d1c356e223d2f1a5a39591d41, 0x61586e751a676a5357416751496261596335503b561d21541c6a2b0721211c1a, 0xe2b1b1a541b0e1b1a591d413529635f350e5d285a6e636a411a212b41512941, 0x492d472c3728235a542c654b241d311a1e2c3f1a1937231e6d1a1e311b0e1728, 0x4c633735412949491d5b3b503168413d414729] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111111101010 : Impossible board_b111111101010 :=
  kernelLeaf board_b111111101010 #[0x1a3145502d27455041372d2a37532e1c1a212a3f355b1a2916271f4e292a3b2c, 0xc23137018282d7028412135283b21642b18573723352d4c2b215e1e621a1c21, 0x416a5d3b2a3f545354632a3b54353f353b681c563b21393b212b1d293b3b5e78, 0x27242d1c27620a0e3f39414c2a533b14563733453f2f533b532b3b2437542135, 0x603b682a140c291d2a1c1d6e3b68673f596e576a802a16351d28271f1e2f2e1e, 0x16373541293b2a29271e3b534129350e28275b1f1e3f413b6a5b29593541] (by decide +kernel)

private theorem ok_b11111110101 : Impossible board_b11111110101 :=
  fork 70 ok_b111111101010 ok_b111111101011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11111110100 : Impossible board_b11111110100 :=
  kernelLeaf board_b11111110100 #[0x1f293941564e3959455927244c536829534e4c625b24415b395d59545356463b, 0x1910215459631e10677606395431724e235a6e1a5163516e54632421242b5354, 0x551b1b1e563f50504e241b594b7256132a3d354f41534c215f234e54394e4c23, 0x5f4e4c2155214b0f1a1e2c1d104c31563f501f0f212c1b56281b2e1d39504e59, 0x564172644f284e285454224e5f613d62505647393156242423162c1b2a1b4b59, 0x314c502756473d2856211a5b3d56625051220f5e5446282e592e5b4b76592822, 0x33211d311931452431532f5751625656295e4e2f4c305e2e62312a564157504e, 0x49] (by decide +kernel)

private theorem ok_b1111111010 : Impossible board_b1111111010 :=
  fork 38 ok_b11111110100 ok_b11111110101

private theorem ok_b111111101 : Impossible board_b111111101 :=
  fork 72 ok_b1111111010 ok_b1111111011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111111100111 : Impossible board_b111111100111 :=
  kernelLeaf board_b111111100111 #[0x504e63455b455524475b3121235d4d265d5b4154534e35475d5441455b48303b, 0x19544c081917291f17355b2824282964791f271f29285b2145555d2a21235a5c, 0x285d476556285d352923215b412a48150a1719281d50282a2f1d2b095a0a4829, 0x261b2a5648215b49292921235d2f215b56412929215b28351a3157564126271d, 0x2e561b24642a4b23175075505e556a645d542b241b554757541a4b5954245a0d, 0x4c170d1b470b5b7158561a14182e0f5c2317125a63540331575b24305a2e5471, 0xa0e0e2219265d5b71] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111111100110 : Impossible board_b111111100110 :=
  kernelLeaf board_b111111100110 #[0x291b4e171320122a1a294e274e121d2217121707555949305028305441212633, 0x4e2a281d1d2212202d22492c54221d1d7b6a6717224e20540a135815554e2221, 0x4b55584979291b0f6435282927553b172e45215b282d4b2955644b4d61574956, 0x1926544130594c482e564b17355b484b0f414847474529233528562148596358, 0x1c1f29351a482d284e542e2221542645453b222d471a1a23352e485b232f2255, 0x164b1229474e634e5621616a21355b292155220a2f210629211f290c581c5521, 0x28262e4d594e1d2c265b56222c4d294e4b4e295321292e4827] (by decide +kernel)

private theorem ok_b11111110011 : Impossible board_b11111110011 :=
  fork 55 ok_b111111100110 ok_b111111100111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11111110010 : Impossible board_b11111110010 :=
  kernelLeaf board_b11111110010 #[0x236b155d615664554823235e261877132635191478647723146b561574582a4e, 0x233578184f28645623794f296b08213b5b5a23271b35232955482816214f230e, 0x6b6f0c234831294b272722124d2833261c3523280f294b21275a262335232914, 0x275e2d6f62655e2d705a5b4833502231296b3121233145242919652955191b2e, 0x292d564b3355285a70274f294b5c636b4f5e3b6b705b5a5e271956652955484b, 0x232e1b0e551b29280e1a5d0e232e542435484b2927141616244827234806181c, 0x585a472a56555d261d232e4b4756585a4f21471b554b58315a5950645e581d2a, 0x41273b41562a4f3b235d21246928656c63562a292a272764555b6928595a4f62, 0xf19585523354b2923290e246e2d242d29562a1d564f3b1c147e29162a567e1a, 0x27614f3129275f4d315a242623211423262c2c2678292a58140f21555424101b, 0x1953212d295d292131313326284541552426556412452924291624295a216b29, 0x5d2d1a4129533b272a642955] (by decide +kernel)

private theorem ok_b1111111001 : Impossible board_b1111111001 :=
  fork 61 ok_b11111110010 ok_b11111110011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111111000111 : Impossible board_b1111111000111 :=
  kernelLeaf board_b1111111000111 #[0x56355820295a242d5f2c624c1220210e594c125f2c41475d581f2d2e306e5422, 0x532156144858292d5d626a4e182e3335172c2e6a562d5d6a172c352e780a2d2e, 0x625d216a56622d58780a0c2962294e685e563b085a29184e21535866554e6a29, 0x5c2d0a2969172d3024334c5e5a47232c3721564b4e58291d6a2129292116122d, 0x18460a20533721292e564130231955316c125a70064756184e172d210a5a2e30, 0x2c4e14553d1365531c30144e4b1f18184e1c1d70642d0e1b182b57134c4f3020, 0x18292b20205d2b24172b24211d3b2d24213521481c21273754] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111111000110 : Impossible board_b1111111000110 :=
  kernelLeaf board_b1111111000110 #[0x37575f4e1429224b133d212c672435245d090e243b4e56295d594717172c2358, 0x59502d210c172435212d13214b14215571224e14220e37294e133d2d291d1d17, 0x10234e1f2e7323562c29231453534e653d783d5572681864495a5a654b646553, 0x1056676e545a563b212e35191f1715193d21144e1f293d1c230f213523081468, 0x59780e6c53625d56185a0e30213068235d685608306856085a555f5f79475d24, 0x5a565a23125d566853] (by decide +kernel)

private theorem ok_b111111100011 : Impossible board_b111111100011 :=
  fork 42 ok_b1111111000110 ok_b1111111000111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111111100010 : Impossible board_b111111100010 :=
  kernelLeaf board_b111111100010 #[0x1b2b6d170c65111b24291c302a29371b351b302e0e21233d2117332c5f23314b, 0x54332c48485d485856215a1d242c1f2a233d59483754296c5c6a542e16291930, 0x53745854542e503754336a502e1f5a372965485d58560c27460a303750303037, 0x2c271053642a233d483756302e1d565f1b41111d373362536258763772645448, 0x644855564654544f6f33645a5457533337495667535a534e2a53315019245355, 0x6164555d544f4f5a554e556a334e53494e] (by decide +kernel)

private theorem ok_b11111110001 : Impossible board_b11111110001 :=
  fork 38 ok_b111111100010 ok_b111111100011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11111110000 : Impossible board_b11111110000 :=
  kernelLeaf board_b11111110000 #[0x476456615453792e555e56476e642324306a545d266a542d5a4f595947536248, 0x23496e3035466747545954562b56265f4b5467476613295a6447665a615a5623, 0x463b192d57612a35084618682b2941762b292420562923644659624c53645d2d, 0x55305d41336a5a63416259572a462c415d4c295a2a2a575f61647618295d2a23, 0x3126563d53701033553d531256692d1720245a6453292918264b0f2d172c3d29, 0x554f624f5d595a4c5a4b5767305c355d263d5056505d6255722a4f26233b4646, 0x5a3d233b613057493d4f5a621966574f5a53502667354b2d185d595d68675a24, 0x202d29301067415a53465a5646665e56675a57] (by decide +kernel)

private theorem ok_b1111111000 : Impossible board_b1111111000 :=
  fork 26 ok_b11111110000 ok_b11111110001

private theorem ok_b111111100 : Impossible board_b111111100 :=
  fork 57 ok_b1111111000 ok_b1111111001

private theorem ok_b11111110 : Impossible board_b11111110 :=
  fork 74 ok_b111111100 ok_b111111101

private theorem ok_b1111111 : Impossible board_b1111111 :=
  fork 52 ok_b11111110 ok_b11111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111110111101 : Impossible board_b1111110111101 :=
  kernelLeaf board_b1111110111101 #[0x47642d2c56470d21495449535d562a5d2147156222152d28202715215c51373b, 0x585c4754152022625c515e695c201c151a622853515457521c1a302b30266228, 0x5461572c57520f4f3d54356552472b1a225c54515c3d47222b155c4f5c3d5862, 0x35303953525b2b4961542a4553561f3021543d305206302b1030522662642858, 0x215131343072392330302d2c4737605826304762395e3d54301f393d52302130, 0x26642d4739315d64515c5b1f255b561a2d55191c2d2a1a202a53511c14225d2d, 0x52263454263062642860525428355252281a22261f535c7723691a1c3035285f, 0x302c1c222b23542a192326622d5247282c66281c605928552d1f2e56522c5430, 0x551f642862542623521c4b1b565c355e27592a28] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11111101111001 : Impossible board_b11111101111001 :=
  kernelLeaf board_b11111101111001 #[0xc2853471052571d582d221d39511c1b761b1c5e53301a172830736447542662, 0x39305e27213063161d583b511a3034225153271f391c3071515833536d111f6f, 0x6d2d5b21276447535423343023172a5d2f212d212c5d5e2330716f5d5427216a, 0x351f6349332c5e305c5f2d617959276327303b6a575749227161333430644754, 0x5135545c5e1d2827281733714b5230512125300b16581c0616215c1f281c1f28, 0x526c1465511c512a35522c51342233495b30556539591026687358725b692c30, 0x67537a53721c5f3568522e4b306551585f54491c4754341a2655305264516e1c, 0x1a5c6537471f232e53592e2d2e55605b555b2c475314655560252a552e205326, 0x2d685b2153586a542c5416583b6a1269535b212d336d212214212e1853222d30, 0x306e58] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11111101111000 : Impossible board_b11111101111000 :=
  kernelLeaf board_b11111101111000 #[0x7a534762515d54682165212a345549701b7161476c5d542a68212a55495e141c, 0x5767536e1a635e540f1a0f087254310a2252556254471b47526c58532660533d, 0x2e352a6e1f225860536c522f122d737c53520e6f634b6560612d340a67584937, 0x531421156651700a39330c537062330f222f191453623110514970142a263472, 0x5321144715132d62473326282a14222328312a53175d512a232d531d2a492a1f, 0x21356c6a3312725c58172a5c212d215c2a546a352d58530e273153172a3b1d2d, 0x14225b5b6a5c2e1f2e225c2d26392d1f6c49750f6c5e22141865312a54675f53, 0x2d2f2a586a542d33496c5e26] (by decide +kernel)

private theorem ok_b1111110111100 : Impossible board_b1111110111100 :=
  fork 86 ok_b11111101111000 ok_b11111101111001

private theorem ok_b111111011110 : Impossible board_b111111011110 :=
  fork 65 ok_b1111110111100 ok_b1111110111101

private theorem ok_b11111101111 : Impossible board_b11111101111 :=
  forced 72 (by decide +kernel) ok_b111111011110

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111111011101 : Impossible board_b111111011101 :=
  kernelLeaf board_b111111011101 #[0x2d413d2d582825172f27542d3d41536a222e483b4d3f5a4d2d57414753345c20, 0x474f3953651f3d352d484d5a343b622f313f2f763b5a41315d2121410c411f35, 0x602d3b27212d17231a543f2d5123412341305a3439303452533051473f2f4f59, 0x5164415a47532d543059515e63593553523b2a3b595b3b5d6a1d5354482d2351, 0x2318345c1a41742d272e5253412d5935523b54395139741c524d0e51741c602f, 0x3b3b1b1d412d215a2b514f60482f53412d1c2e23345341226a2e3518482e232b, 0x3b2b4d280a2e5747232f12621841335a345335535b6a12283b416222482b2253, 0x52233939352b331f35522b3b284d] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111111011100 : Impossible board_b111111011100 :=
  kernelLeaf board_b111111011100 #[0x4f1a0e2d475c6c6a532119191630252d215c5b526a1a5e205347212d1f355441, 0x21352e5c5353352e685f5521524868515e47532751521b5d1c08021a142d4710, 0x5d5c2f685952595247543b5321372d213058214f5c726662215258573030581a, 0x21545347525869514d3d58533d5d5c524f535257535f3d48593561143d5c4f55, 0x2d1f5d512047271c1c4551584d255e58594f353f59211630542d2d682a] (by decide +kernel)

private theorem ok_b11111101110 : Impossible board_b11111101110 :=
  fork 44 ok_b111111011100 ok_b111111011101

private theorem ok_b1111110111 : Impossible board_b1111110111 :=
  fork 70 ok_b11111101110 ok_b11111101111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11111101101111 : Impossible board_b11111101101111 :=
  kernelLeaf board_b11111101101111 #[0x33581b2c312d4721177b6255583354282745331a54582833271d334521342637, 0x13215547301d4970101c546a4b63451d5b1f1d1f33582c571f301e2c174b5c4d, 0x271c300f6c5830551f251d58470f1d1f554730565860575620477d54492d2c25, 0x552a1c552030252f3045451f583b472330544749202e1c4d1f28565727491d0b, 0x2d2d0e0f1c2e281d2a452d282e21282d4720272134481a551c561c190e1f1a1c, 0x28491f471b555b642a212835245456281f35565d28472d48212825571c2e212d, 0x3561562b1b2a491f1c492749251d2d142d352e282b5a4d2b252b192769475a17, 0x2e2d4d172e2323216a2769092e2d5d302a2135301e5d2d551d5d273021351035, 0x305858212b452f286449345a602b2d5555213524285f5c2d2e30345723214923, 0x2a6e5d64635b172b24525260521f352858302b34535b2a242d47555c2458] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11111101101110 : Impossible board_b11111101101110 :=
  kernelLeaf board_b11111101101110 #[0x584d3737584933284d562b45215856242e284d492554541754541746304b352c, 0x1725655a5c54311d244d4517582835525b4b24634d595a743328542637585637, 0x301311182e2524305a] (by decide +kernel)

private theorem ok_b1111110110111 : Impossible board_b1111110110111 :=
  fork 63 ok_b11111101101110 ok_b11111101101111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111110110110 : Impossible board_b1111110110110 :=
  kernelLeaf board_b1111110110110 #[0x7a60645a53675f691f1d2653301523596a4635462e2d30301a676423345d5447, 0x37675c3f2e2c56605a48372634565d37485d48236234531f56594852601d6757, 0x2b23342435184858152310705874195a7058642a234b1a313426581025211a14, 0x2b3035162c4f17341a1f2b30145c214b182530252d1f48353f4b372c2e245524, 0x2546] (by decide +kernel)

private theorem ok_b111111011011 : Impossible board_b111111011011 :=
  fork 57 ok_b1111110110110 ok_b1111110110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111111011010 : Impossible board_b111111011010 :=
  kernelLeaf board_b111111011010 #[0x331949285f645d20282628202d1b495b1b5b686223575d491c235b6930344754, 0x2430312d641c5b692f242c1f571730523073623021261b332d5d33703127731b, 0x521d6f621d0a34285d28685d34376a58262f241f1f7b28353330635949351c49, 0x286320622c0d165b376a582c2c245a341620285d21285b2f6b1555641b346357, 0x30231b3134155d23580f2f1f4966252131521b57355b242c245a592017342464, 0x492861594964311c2328303152683b233031581f6160155d23575d2330200d5d, 0x3556486a5d3435576449581c2d212d5834371d2849357a1c2d3561372c5b1f5d, 0x62312e5b585c5b475b6f1b37525d5c58551f34211f63285b375823571c1f1c1b, 0x622e4f247020146c6a2e55305c2c684b52266935525b24372852553358576e33, 0x23553033105b241526332f5b2e55566426655b58345a6a652455352c6a5b3571, 0x465c5556654f305c674d5b2d2856584b252e604f5855] (by decide +kernel)

private theorem ok_b11111101101 : Impossible board_b11111101101 :=
  fork 65 ok_b111111011010 ok_b111111011011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11111101100 : Impossible board_b11111101100 :=
  kernelLeaf board_b11111101100 #[0x5848550d61622d2d7123755f233f58215d471c2d2b34232d5f21612d4654532c, 0x5c553f605d56112b466c2d54145646594d542d23455c6f54272b2e5d2d5d561c, 0x4665585d5c594b5d1c6c5f58565c2b5d2b5d776a646c5f58552d2b392b2d5648, 0x14212331585855484d1923584b3133271d3b14235a1b083328263426465d5c2b, 0x1c48212d541d283b4d242821284f2d21415447231f14335a133923561d410d5a, 0x584f26582a2e35556f5b35765c356f58555d2d584156611b562d525f58552645, 0x555b352b553b2a5b21541a64765c556461145d5b54645b62525b5d644b5b543b, 0x315826202b5d563b3554265c2658553b54611b2d5545282d3b5b2d5635352e2d, 0x211d232d232d213b1b355f5d3b53542845262b2a581b352e16232e252d3b582a, 0x3f535a26102d3b1b70566523262d5556212b3b452b2d475d350b5d2d4d2b213b, 0x2b232a2b237335235523535d462b5a2b4635232e3b] (by decide +kernel)

private theorem ok_b1111110110 : Impossible board_b1111110110 :=
  fork 61 ok_b11111101100 ok_b11111101101

private theorem ok_b111111011 : Impossible board_b111111011 :=
  fork 74 ok_b1111110110 ok_b1111110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111111010111 : Impossible board_b111111010111 :=
  kernelLeaf board_b111111010111 #[0x4a4b23645646562048174d5330575c531f17573048305833536456575428353d, 0x5828233348236408106733275a233164173328342228233134571b2d4847264a, 0x345656342822262d48152347392b28692717344f692d48642b231c552378641b, 0x306552265c642c28302d53342d2234305a62565b0954645f5d1f22222d301a61, 0x2d0a15301f281b22142115302d1b2826271b6464645d546a2e5f546852282c2d, 0x132853202e2c204f15540e2e06202d1f285635201b2d22302a1d204f48542e0f, 0x254d462e14214f4a282528585e28551f286154352c232a34252e2c1b2d201d20, 0xa232e142e154d335b4a5828353414212e235b1658494a2334282e3328212b28, 0x332853234d5a61212356232453342f2f] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111111010110 : Impossible board_b111111010110 :=
  kernelLeaf board_b111111010110 #[0x4926331c041951271a2d58242555525f6028542419335456615c6c28581d4d2c, 0x6433582d55235b56452a1f2e5f494a33541d265d391d28285c26281f2d474627, 0x221a095d30267256344d1f232e302326344a2f252a1f2d335b56561f252e391f, 0x30472624302d345d0921562d5148222d34133051222d22141851306848534b19, 0x174d54332817452133341d282a5d311f2d1d1017215d703328541f1f54213117, 0x3131212e60392a4a31172810] (by decide +kernel)

private theorem ok_b11111101011 : Impossible board_b11111101011 :=
  fork 55 ok_b111111010110 ok_b111111010111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11111101010 : Impossible board_b11111101010 :=
  kernelLeaf board_b11111101010 #[0x252c45572d3d4647212a192c1f5b452c2c1f5d49645d6453635856225c513748, 0x5d22475c5c221c5e22475e574a585c3d695c1a3047255757681c584a5c3d642d, 0x37095d265a4f5a1551211716212a3d2651512b2a1f392334302c47392c564558, 0x39205a2b534546221d2460491d272a2c5f2419265c1f26242f4517101f262a21, 0x451f395f23535a472c5122263d5d156b512e4f2d5c302c56262c2b492f5c2120, 0x2d6022271937243d23235b245f23231f244a582c2445074565522e6439075a5d, 0x21375d395235214d2e452c395f354a231a535d2b1c22472222533d234a23202e, 0x2b395f231a21531c27203d1c1a235b141c202e2d2121472d37245f2451451924, 0x455b1f5f25372d376e1c565851202e2e1237165158601f35392e525c2c4a3d4d, 0x4621372a2e2d536b47374755251f1c372e6056466a5d1f2d374725392e68375b, 0x354a372f532b55] (by decide +kernel)

private theorem ok_b1111110101 : Impossible board_b1111110101 :=
  fork 59 ok_b11111101010 ok_b11111101011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111111010011 : Impossible board_b111111010011 :=
  kernelLeaf board_b111111010011 #[0x53212d52523328611427393b532e125c0e166a68681b1f4d6a3733195c51582c, 0x2d4f602d53280e4d27532e5253201a1c47515e33574d5d526f1b2e0e52694751, 0x1b4d1d49193733646a5d7d606e2d5f52681f5f23192a5d3747281b4720465753, 0x357033562335203d1521261521353320121f20222d58285f55681062605f1b28, 0x26092a1b22175706215d5d6b56681b617d261511214a1f68555d2d63572d6122, 0x1f64562a353d151d532020525c141f1c531210707120261b472d52175535111b, 0x22141c475521372f3d532027475f523d3d3d704a5d686157616a3517143d3720, 0x1c1d37261c602553571d470c2064263156526822351752261046202a221f23] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111111010010 : Impossible board_b111111010010 :=
  kernelLeaf board_b111111010010 #[0x203d1a5c5c1a20531a550f0f17252d352d2021614a24211735145c237c5a2e60, 0x7c07645a2e5c201c5e1a53152027312328472f58204d5a31551b3b284a584924, 0x512d5d3d6f6717201c693d2328655714705e142362514d61744761704f1a271a, 0x5158573128642814352719271c22203d222073695e1a1a1c27271c1a5e372814, 0x262628684922645f4962692864571c27203d5e282665685e1528262265] (by decide +kernel)

private theorem ok_b11111101001 : Impossible board_b11111101001 :=
  fork 48 ok_b111111010010 ok_b111111010011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11111101000 : Impossible board_b11111101000 :=
  kernelLeaf board_b11111101000 #[0x2252685c645d6d4756615169645c641c1f3525225c20372c6d5c47642c682e53, 0x5c5e642c3d273d211357785e5c623051285757461a5d2a5d5c2d64513561575c, 0x27522c1f23621a212f1c2a2819235c5e621c2c375d5d181c78625e5c222c6a65, 0x26686c2047655c64623d64471a1d682e626861561c2757272a62641c2f272f26, 0x23223d26171d283305311f2d311b31300e311a143371206f2837332e2c0c3d0c, 0x2c17353d0b2a1421685d2864645c2e1b216265251a132125261b0e2d3d302e1a, 0x2c2e1c4a281f2c1d33312846332c1b0c471b645e0b2e231f2d473b3d1b20640e, 0x332e6f701c565520101c1f771f260d1d122625262518371f2a0f1d56252c311b, 0x67685d56496a58466833615826332a2c2e2c633368653d5f772e7065644a235d, 0x69686870675d565d5826616f6a6a] (by decide +kernel)

private theorem ok_b1111110100 : Impossible board_b1111110100 :=
  fork 72 ok_b11111101000 ok_b11111101001

private theorem ok_b111111010 : Impossible board_b111111010 :=
  fork 65 ok_b1111110100 ok_b1111110101

private theorem ok_b11111101 : Impossible board_b11111101 :=
  fork 78 ok_b111111010 ok_b111111011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111111001111 : Impossible board_b111111001111 :=
  kernelLeaf board_b111111001111 #[0x5717542c1f215f5656545956573364286c715f1d2c6d5f652b252a23705d4b35, 0x1c314d3314654a3121576c4d33265a2c541f1d597617532b230b150e4f2a5a56, 0x471a250a806823544d2c5c1a542c4f242b5948182a5d234e54562a545666575f, 0x4726602b562546585d2d2b2759545428575746275623302a215d1f546d1f572d, 0x56283123585d4f5d4d2b4d70585a4a2813232a21560d1b2b1e27575d4f2b5f2d, 0x242b532d2b5a5a4e14285d1e4f5a4a2d5f] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111111001110 : Impossible board_b111111001110 :=
  kernelLeaf board_b111111001110 #[0x5c3026111a262f1a192d535e245360692551675d4a5d5e6926102d475f544d2c, 0x1d58454a561b641d545426195660685d54492d47651d5c66521d23195d26261a, 0x2a52301d1f59454a2f0951250d2a2d271d594960541d495725282a4925590f28, 0x54645126532330257714255831455d265d2645681d5d58564d492d492d5a564d, 0x1818101d181b2d28211b2d305a4726595a5a2d5d515b5e6d511a1c143156311c, 0x11311f281d565d564964286449592d5d6a2856596e546749314e192d101c4931, 0x4d303357583049630f2d1c] (by decide +kernel)

private theorem ok_b11111100111 : Impossible board_b11111100111 :=
  fork 55 ok_b111111001110 ok_b111111001111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11111100110 : Impossible board_b11111100110 :=
  kernelLeaf board_b11111100110 #[0x1d1f26656d575a5d5319330c651f2c1d2664284a2a1a1d1724652e2e1c235635, 0x262c0f26237821612a685f665264286528686a5d5c465330572a3025652c4609, 0x2e1c1e566121345a234d214e1a0a255146532f5c1c5a522133265a281a262c10, 0x3d532458331d37255e635470496a5e585f4d2c23454930100b26301a5d522654, 0x232b1d3173331d3125331d310c6b285d2b5d58253757277264101d2849564f53, 0x152b313710273137681c314d0f3730495a2b] (by decide +kernel)

private theorem ok_b1111110011 : Impossible board_b1111110011 :=
  fork 63 ok_b11111100110 ok_b11111100111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111110010 : Impossible board_b1111110010 :=
  kernelLeaf board_b1111110010 #[0x1c30464a2a5b241a245b5959135b1265252c1d6519252d2c07132864155a5635, 0x591f71576e532b282869532d141d28522d535e592c24301f1f2d21252a255825, 0x1c1d2819121d5d242337256954602345595657374a2c2d0f5a57592253241728, 0x2a1761282a21561d19230b5254565721231d1c1b28573d08191c1b1c2368692d, 0x57271c532d286a68142d5354575a2d304a28] (by decide +kernel)

private theorem ok_b111111001 : Impossible board_b111111001 :=
  fork 57 ok_b1111110010 ok_b1111110011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111110001 : Impossible board_b1111110001 :=
  kernelLeaf board_b1111110001 #[0x4e5b452d5f612b1815262b18247a2d262b242b0e6c3566642b26243449285a56, 0x4d4559735949252c071052181c2d5228641c4554282e2e45235754616d57613d, 0x7663526451302315354f3d23675a265c63544d5b2c102c6a12704e5863481a5c, 0x452e23245a4e14302d3023475348152d66370a305769765851666a5f23377a4e, 0x573928232e57392339282b575a4f2d67354666516951464853517660232c2222, 0x6e2c1e1f30514d6648213546573d5f12514e525a4f4522465968575a52524866, 0x4653162360104e25532d7212452553253d3d5f4e721c2d4e545e5948486a461a, 0x375b6939534d252d54534e6a461a492d6357285964543d2d4e575f5268535823, 0x252d1a5e59643d646f66575f525f544610104e584e721259454d25161c194d27, 0x5b1c48575f2d68545f57665f585e2f274d254e486a461c1c532637455f266a53, 0x213054592b69584d17252b2b242b284f5a24212b19122b2851101c5b48536135, 0x30213037221c2d646a584e5b5f54226634] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111110000 : Impossible board_b1111110000 :=
  kernelLeaf board_b1111110000 #[0x674f4d2f24255f4f585a5a235a65565a2b4665252e252d6939282b2b25564557, 0x49646137301e2d64531c2d25695426245b4549284d5b67615649545f30616939, 0x5b1e2863562b2d25582e286037495f53] (by decide +kernel)

private theorem ok_b111111000 : Impossible board_b111111000 :=
  fork 74 ok_b1111110000 ok_b1111110001

private theorem ok_b11111100 : Impossible board_b11111100 :=
  fork 59 ok_b111111000 ok_b111111001

private theorem ok_b1111110 : Impossible board_b1111110 :=
  fork 76 ok_b11111100 ok_b11111101

private theorem ok_b111111 : Impossible board_b111111 :=
  fork 54 ok_b1111110 ok_b1111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111110111111 : Impossible board_b111110111111 :=
  kernelLeaf board_b111110111111 #[0x2e53555b412a1e74291c66585b5f606e585a6a66607c656e57556674244a4e30, 0x1f6e2e54534c62262d554d1e1c295555495f53572b10292a1c5d5122412c1f60, 0x6e595a542e5c5a5251271f235a412223412e6457582d652952515823315f2955, 0x4e2a31534a2a295952284f5a1a4f4947311a5a2e2d6247291f315f5226545a2d, 0x5248514e262c264e2e2d4752245354205a485365505a0f5357152e29412e1b2d, 0x53632952534a245a2a22162d2c2155210a29550b16214129222d2a4e53282651, 0x2d56264a1a2d28] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111101111101 : Impossible board_b1111101111101 :=
  kernelLeaf board_b1111101111101 #[0x7b27313151301a1e41111e271b25301f2f2f6a19584531161a414d52244e262c, 0x4b4d5d684d6c302d514d304b24697330515d4c4d45521f514d3f245641254156, 0x663f51301b1f30134d1e292d50301d122d4d675b604d3f247b1e30234e223163, 0x2d2730415e60522d60564d411f294a4e1e1e4d3f55473047190b2d1e30524d1c, 0x2355474a304d416b55483f7b4e273029301c552d29304b29594d3f2724302956, 0x454c4d514c3b2d554d5c5147264d31315f2416314d3b1a4d5141264e2d4c5366, 0x273f4a1e612126452f4e292f3f29221c111e29262d243b] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111101111100 : Impossible board_b1111101111100 :=
  kernelLeaf board_b1111101111100 #[0x294a5d3b4120314a4751292d4c484b5e62204b4541505b1c294e4e294b4a2f5a, 0x4d5b213b0b292d2d292727671a2c50514e1a4e414a232147244e1a274e1a1c3f, 0x2c1c174d295b735f265d414c195d1c1f2c31292c3b0f301a6e5d0d1f535e682c, 0x2d1e551717533f2c292131502f2d19312c554a2f2d45211f4a172c3b2255090d, 0x2d632660592d6031293f2f2d4d27152c172c6575294b4a17536e4d31534a4d53, 0x26542f62312530314d5b4d454d476c4c6e5d476e5851262c29535e5f4758554c, 0x59290e18295424266a4d303b086e542658313b203b47262d5045485045482447, 0x2151263b4120474126417041204741267c3f18291e20] (by decide +kernel)

private theorem ok_b111110111110 : Impossible board_b111110111110 :=
  fork 42 ok_b1111101111100 ok_b1111101111101

private theorem ok_b11111011111 : Impossible board_b11111011111 :=
  fork 55 ok_b111110111110 ok_b111110111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11111011110 : Impossible board_b11111011110 :=
  kernelLeaf board_b11111011110 #[0x4e2c282a1959565d495d5059315f1d5d2d2c651e5074281560222a1d59294a3f, 0x191c5a4919282a1b1f552d49287f6f0c5757625f66221a651d51587d515b291e, 0x55471c2a2955314a302a2a1c675f5055526f192a0d57414e2c55684e1d191d20, 0x2a2061554a22554a22636015] (by decide +kernel)

private theorem ok_b1111101111 : Impossible board_b1111101111 :=
  fork 51 ok_b11111011110 ok_b11111011111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11111011101 : Impossible board_b11111011101 :=
  kernelLeaf board_b11111011101 #[0x6053505010575d4c1c372a57301357262b241e1e1c0a111c1e30502d29232c4a, 0x4c302d25290f2d1d332257331729372a111e585553374b2d2a1353374f4b522d, 0x50334b1a4e614b2e2e654b5e531e5926255f561a161e2937221611292d3f3350, 0x601e2e263f5a4e4c1e301c654b134f2d223733292a5013211b13261d241e264e, 0x72181f59691c1f5a524b3f524b534e484b101a726553537260231e29302d1a5a, 0x3f1e29551e241e1a574c23212d261f141f654b14261c1f231a254f604f590e18, 0x4c142d56552d604e2e3b1e1e172b654b142d264e554e4b4f563f2d5a142b206c, 0x5a28561e285053611b28265462622b502d1f28545a4f502d54561e623056495a, 0x2a4816265f4e22262c501c5f4e2a2d5126514f4c525a1e261e1c1e1f295f4e30, 0x1e5e2716021e314e2e4c654b37334537513729625b4b334e2a26281e15501d4e, 0x5b522445522d51535e56311a4e] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11111011100 : Impossible board_b11111011100 :=
  kernelLeaf board_b11111011100 #[0x20515a3b290c5a4c17204e5a24504e1a6b604f1d50594e6555201724574a2a2e, 0x4f53253b5a53615065574e4c535b2528611d1a5a1a30132214174e291f266215, 0x2a234a1a1c294e30214c565348214c535a484f4a181a295c534c30620e5a4a4f, 0x1c5a294f223355673b4c4a15231a65232a5e532c4c11331e262526285a604a2c, 0x81b141c521e291c22262c1c1f122652182b5a501c296751624c4e2a2d4c2333, 0x616f6150271f5520270a1c6a1d572c5a50514e2a335054124e224e0a291b260d, 0x574a195e51251a294e4e1e4a222c1f4e222819201f505a] (by decide +kernel)

private theorem ok_b1111101110 : Impossible board_b1111101110 :=
  fork 65 ok_b11111011100 ok_b11111011101

private theorem ok_b111110111 : Impossible board_b111110111 :=
  fork 57 ok_b1111101110 ok_b1111101111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111110110111 : Impossible board_b111110110111 :=
  kernelLeaf board_b111110110111 #[0x5863586122213f50213f13377b2d4d293f1d0f115b1b1b165750451924314e1e, 0x45521b6656263955292d31486129566637596663503f4a53521f39507d22611f, 0x553f24372d56452441561d222d4c4e26394d5859504d604545471c5519451f39, 0x5037452f373f240c4e223952371f4a3f662d47522d5648451f19453f37243924, 0x21663f243f68615b5024212d50665b3f7f3f723312191f3f19331b41414f2119, 0x47450e4d522d371a1b2d2d0e211445562911164a14662d451f162d0e142d4d55, 0x1f483341376639502d3f456e56] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111110110110 : Impossible board_b111110110110 :=
  kernelLeaf board_b111110110110 #[0x4733144e5a292555526947585b536a604e525b3f4e331152525a602933391e4a, 0x1f4f295a2324216e4e6024267141231b4e26371a52291c523f13604e2c1f3323, 0x2366620e5d2417244c665a391f5a2d373f600c190c244e2221334d1f391c5b24, 0x6e4d5b264e3f5b191021153121371910482c193710780a2d524e5b4147142c41, 0x53620e4d2c22315352494f41372141534c2d52646e1f1b53556421641f1f1b1e, 0x6e1e2c574c4d472d482d544755244562546e4c4d473726601b29316e19605353, 0x4745] (by decide +kernel)

private theorem ok_b11111011011 : Impossible board_b11111011011 :=
  fork 48 ok_b111110110110 ok_b111110110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11111011010 : Impossible board_b11111011010 :=
  kernelLeaf board_b11111011010 #[0x505f61412137294e185f15491329482d2322152b22151f0e54152b1f29395626, 0x295554304750293f5d122d625f191625304c52212c53505b2962305d414c4e63, 0x290e192f4556241a4e22374c375c302d55536248302c306a4d111f481f451e65, 0x5006332f17305f54110c12503f2c170911122d062d41331520722b2933301829, 0x3f395b18132d295757624a5b49565b5568655062491520162c5612200e195b15, 0x24742f505950240c665a65506e601665501e3f4a562d2f11562d5b1424172450, 0x5433475d603f4d564c692d4d33246529661e50451456140c1415172116241917, 0x31645b2d4d0c2429335d0a2d54564e1e56393f5a593f50335954505766564c55, 0x53602c533129644a5b5b5a6e573361546429315b6a502b45247c61702d331524, 0x5a6e69471130555d2d485029666a5a17296616294f33253f3f1f53615a667c0e, 0x57153f5a55484e304e295b24301f331729111552] (by decide +kernel)

private theorem ok_b1111101101 : Impossible board_b1111101101 :=
  fork 40 ok_b11111011010 ok_b11111011011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11111011001 : Impossible board_b11111011001 :=
  kernelLeaf board_b11111011001 #[0x67132618231607182654220e104e640c646220214e484a20624c641245282d56, 0x2f314e5b334e185b394115240e6067292222261813120e16115007290a670e48, 0x5f3f23631264555445241d0f6555544f5013625d54456a1f3961645f54453328, 0x4a604e2239122c456a484f593f5512100e0e122f5f45244e26241254485e2426, 0x283f5e755d1d835f6a534524505b6154332f305f39532853412141533f552c53, 0x57645b4a625f5f5415643350533f6257534a126250576433506a5b7528455d53, 0x574a5333572d532d7d5b505d5e236a57411f5d4c216217212c5b6a5070621a62, 0x4a105039452f331a2b414c4854721a335462573f484a61534d4d215454506a5e, 0x48234d3f4a535016234d4a5350234d4a535085234d4a53506d1f502350185541, 0x22556230605530414c3069155739572d3f55536048574c6c4a4c573059] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11111011000 : Impossible board_b11111011000 :=
  kernelLeaf board_b11111011000 #[0xf3950762839506c5c1e41654e23454e6176215009232f162153232f4e562420, 0x22410e1b0a2d184e3f0c0c540f33545048533f4f334961493f536a5613544f7c, 0x5c1459165028332f4e0d135c216e5c7621754e1f2121231f15212d540c252f62, 0x2470334c6f3380473370545062307c4f3f3b12574c395039334f3347336a4954, 0x4e4e0c603f65574c531e4f3f7570535b604e644a6e4f685b70452f2462392522, 0x84a0e481f3f0c23303318110f1f30131f1f33114f5c391e281a39414f4c541d, 0x2439211533281861235670282445500e1f3f293f2522410a5c294c2212071348, 0x2f18231d532f4849211d2d5470576a484945237624562411281d285415151d28, 0x3f3365574c2f594f1f1517121f334121542d18284f4970705549544845482121, 0x223341212d186c335c3369151850184823394861554764236d0c3f6141604f61, 0xc1723171e17531e28253f] (by decide +kernel)

private theorem ok_b1111101100 : Impossible board_b1111101100 :=
  fork 90 ok_b11111011000 ok_b11111011001

private theorem ok_b111110110 : Impossible board_b111110110 :=
  fork 46 ok_b1111101100 ok_b1111101101

private theorem ok_b11111011 : Impossible board_b11111011 :=
  fork 53 ok_b111110110 ok_b111110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111110101 : Impossible board_b111110101 :=
  kernelLeaf board_b111110101 #[0x2d2c241c552d564d1c4d201c2c5a0c1733123f29272627565549337350222f4e, 0x162724231f2714211729620a214b2727625b1226245518242d303b3f35455326, 0x2c35223956262e2329392e29392c60132a5629565a232c2c512a50213b212714, 0x2c222922261e2c30242d2d7d29225b6e22552c60213555292a5f1b226222271e, 0x212a102d4d291e53220e565364505a5362612d6939505b2d5d50712e6261562d, 0xc37194b22211f4d1421212167781c136a2a4b2a21302b261703262a372c2121, 0x1a4b29334954484b4b49501a415a2a21394b31651d33211f214b3f271c2d2a1d, 0x54495a763f4d24264d352d39545435604f4d2d1862562e3b54455350392e2362, 0x2214211a12505a5318492350413941231e541a3553593f4f483f706a161e1a67, 0x4d30231a54457033625450356235621a546e234145351e2d211722274b1d3515, 0x1e4f31352f243f2f53546e24142939413f2c51662f062255485123261e354b6e, 0x2b24] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111110100 : Impossible board_b111110100 :=
  kernelLeaf board_b111110100 #[0x504d26585857244d5d1c1f222e31263026117d2d222f6a6e4d266455294e5b4b, 0x4d592d415e5739232d65595a6c30554e652957412955316a24292a653361214d, 0x6e2a295a235337672127302d261f300224292d5b50624912120e2d33222e2f4e, 0x29232931501023372926485629332229242b2d232e2c6170566b615814705b22, 0x5d5a661a5b686670566c57472d657e292a7f652969585548534d371d312e3139, 0x415d5b56211a293956395f392956652e355a23536535352f5b5d3929656f682f, 0x5d5555295929355955232953656f565a39352f2d5d615a316757315a3923592d, 0x242d1d2c56615e565641675656412d] (by decide +kernel)

private theorem ok_b11111010 : Impossible board_b11111010 :=
  fork 74 ok_b111110100 ok_b111110101

private theorem ok_b1111101 : Impossible board_b1111101 :=
  fork 52 ok_b11111010 ok_b11111011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111110011 : Impossible board_b111110011 :=
  kernelLeaf board_b111110011 #[0x376a5637212b49522149374d311b485d4f4f696f152169224d37102d62542647, 0x31552b4f564c5d2d4853672b662b52492a10551a3124481c102a5e6e492d2d5d, 0x30565a37565761481d565131532328312b1e204c2b102d5d2d37707e31645651, 0x2a494c5d5d051d21331c66552056492d5a2d1a665a51564d2d624d2d6754311a, 0x566c6f605f3f4d273120482e15564523534f5d2d4927243722203056492d5456, 0x375d5e1454625d7345656363254e55561a2417183148184c5e5b5d3121215f54, 0x26371923265f152134232e585d4b374e55562324602e585858] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111100101 : Impossible board_b1111100101 :=
  kernelLeaf board_b1111100101 #[0x740f1415495a2d341c562e47573156274731531c37252e5327474d2d5d215c20, 0x2753573127495a2f52215163522168075a094f5122082d4e63541a82332d6e22, 0x4e4e0c271a492f4e2d6a5412480d0777642d4d2d585b2d2d4e645e4e63542149, 0x331c4d2d514e2f542d222d253458335849232e2f54223164612377645a1a4e17, 0x2a171f62244e57312f561a23493152594d5a495831571765576f141165332a27, 0x1d51282e532f244e515431282e532e2e271f2d2d2e4e561458544d5a54471c39, 0x33212d33312827535c1449242727342e272e27215c212e2533274e39332a621a, 0x2514481c492722621a2e2e252e24315328151e27243339272e224d33224e1c4e, 0x631c21241c2427245a1c274d5d4d2e6321221c25544b5a225c541c211c27254e, 0x5a592452302d211c672227241c5a4d17225449491c7022624e561437174f5a4d, 0x255a2149] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111100100 : Impossible board_b1111100100 :=
  kernelLeaf board_b1111100100 #[0x2f54154d151323111d4e19522449576e575737704e1a3127541c182251152d56, 0x302a1c4d2a4e371c652d68515d5222140a0f15271c1f1f1c1a244e275b372154, 0x5f5462535262584b5224372a5254212f1f5b47584e375e4d4e372a4d152d0717, 0x495f5f5e542d5f1452485337575d71573717524f] (by decide +kernel)

private theorem ok_b111110010 : Impossible board_b111110010 :=
  fork 38 ok_b1111100100 ok_b1111100101

private theorem ok_b11111001 : Impossible board_b11111001 :=
  fork 65 ok_b111110010 ok_b111110011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111110001 : Impossible board_b111110001 :=
  kernelLeaf board_b111110001 #[0x631f3328471b332e451f234e4519451f2815334f4d5c4e634e5f5a54222d5620, 0x24493319244f4f5a45232f220f4d1e450e15232e15545a452e1c19211c221559, 0x532e232e524f544933285955102e57765a542d225352482d5a2e53542847623f, 0x335b695b6c7a781552482e251a4f47524154217d5d4f52475a5c542e21542e28, 0x23242f1e221b1e22102e39644e1c5a232b561a534d581a5a23245365334e2d5a, 0x2b232223236441542e1e25484c2325544f174d5455624c5a5c491e0b23490f1c, 0x47574f2d2d151e2d2e4d545e6254334823535a5d5a4d2d222d525d595a284c14, 0x47574f1f6057662b4f585225335b2857234c1e49664f2b7949701c5a2467475d, 0x18332b541f1f4c1715192b1f23122b5418546d495a2b1f49091f4511331c2866, 0x2d4f232d23231f2b1e53314c] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111110000 : Impossible board_b111110000 :=
  kernelLeaf board_b111110000 #[0x64282b0f244c07072b1528154131181c646a4e64152f540b1b491b644c472d56, 0x5259665c2b5d07155f285d111b544d2d4c3f4e45552321414e39191211391557, 0x223013152f6b2d301b416f4153625423314e544e301f536e54475b5e61454d57, 0x534152482d4d5d55535e6e5f574f] (by decide +kernel)

private theorem ok_b11111000 : Impossible board_b11111000 :=
  fork 38 ok_b111110000 ok_b111110001

private theorem ok_b1111100 : Impossible board_b1111100 :=
  fork 53 ok_b11111000 ok_b11111001

private theorem ok_b111110 : Impossible board_b111110 :=
  fork 54 ok_b1111100 ok_b1111101

private theorem ok_b11111 : Impossible board_b11111 :=
  fork 64 ok_b111110 ok_b111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11110111111 : Impossible board_b11110111111 :=
  kernelLeaf board_b11110111111 #[0x6c72652d2437675e745e781a3062512c582d5a2966353653593428362c455c4d, 0x5145592c51565129455a3545332f562a1424141468302456303d30293756452f, 0x2c58346356542d59625e292475582c30416260296039566b3033622c59305847, 0x4b292d36362b587d5e2d5654671d293465375337536e283462362c1a4f603636, 0x33352d24636d33342a283539615f611c284556544f595f45542d3d542c393456, 0x39295a3f3557413956415e3033331e3b1641476d133b5e2428334736362c5c36, 0x2b5a] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11110111110 : Impossible board_b11110111110 :=
  kernelLeaf board_b11110111110 #[0x2f221f2e2d36414f37373f35213f2f613751452d542f552d21262d5441364d56, 0x455467543559623f2045233b5461352d5a4545623f552e545428612e512d3554, 0x332d19216128186a22352f777028532f145a1a22222d41544936542365547128, 0x2d511e265c542b573351473b39352e2f41282e39352f36533b51662f7333350a, 0x4f696651252e332d1e226a495e514d414930366a4d29214d23302b361e5e1a4d, 0x2d6630262a2c305c2014742c5e2d30365c6637514d334133162636664151303b, 0x2c66162a294733624f622d57514b1f372d35663029452f30302d244b742c2c2c, 0x3351472d51415a29301e2a2d412630232d41] (by decide +kernel)

private theorem ok_b1111011111 : Impossible board_b1111011111 :=
  fork 64 ok_b11110111110 ok_b11110111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111011110 : Impossible board_b1111011110 :=
  kernelLeaf board_b1111011110 #[0x766d68363d624b4130362b304b5e2e4b6f63302b62636270735e695c514d542c, 0x4f3549694d4527474d6c304d4d457236515c295c30495c51453b395f514f3d14, 0x2d247356566940374d456371244562410f815162685b71372f791f51404d4b58, 0x4d37564b68144b41476e2440413941511830573947403736304d373756516269, 0x1a1c253b25291f4d5e45296266456c4b2d45476c106e2a374568127060563539, 0x2947544d2f5c1a36621c7c232468604d29513647602f512736603b5c20304568, 0x3b293b1f452f3b2b1e5e4723692e394d292460642b2d18514d2f3b541f2d454d, 0x5b2d353f2f2b24364d2a2857202f20352b355726513647401e213f23553b212d, 0x354f3614415c5424545a353b245a5f69512d2f561f2d36414524362d2f4b5129, 0x293549417b761e5c1a13295b63412d3b62512654392d5666561a2137135b334d, 0x56263318354b7e36566c0c47265a14514572565c3b1d4d3651411b331d291e4d, 0x4151454d3347182a36562047] (by decide +kernel)

private theorem ok_b111101111 : Impossible board_b111101111 :=
  fork 82 ok_b1111011110 ok_b1111011111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111011101 : Impossible board_b1111011101 :=
  kernelLeaf board_b1111011101 #[0x243d2d45535a3d4f5b2d292b2b304015173724666937375b15116b6a51145c3b, 0x292f37512d2d3d35361e0e192846405e5169621c2d102f265f2f2d3646282935, 0x2b4062205a2b6346515451634062402f523d516e2659463d5d27295b532f2124, 0x23526820352d345a4f52356e455b292d523d265f2b0f2728534652534651510c, 0x40352f2d625b62585451262d60525b29525745543d5a13302953645246605349, 0x622060593527253027282d295430281d22302d2b5135464672525a6462205a34, 0x15092024232e334058265a5245296546344f29624f1f5a2469465c53392a364f, 0x36235c206a2e54361454283336543374265a4b142a15521f2528331d5c1e202a, 0x4662405a453940522d242d346228452060294f5d5a674f5a20602d2824235a36, 0x365125495b5c1c725c54512d5b404055263f59264664585c545129662d182a20, 0x5119261e285c5554462737] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111011100 : Impossible board_b1111011100 :=
  kernelLeaf board_b1111011100 #[0x2839536a59725958533b3b365c6258655c553b3b642033293b253329625c3751, 0x705e245a64286226522f592b59296536191b3657352e5923372e4f34622e5a59, 0x355c615e696e2629555728353d5e3629275f3d23553768205f33646955291c23, 0x23596759353b6220742a5d272f261e2e3d235a2733] (by decide +kernel)

private theorem ok_b111101110 : Impossible board_b111101110 :=
  fork 71 ok_b1111011100 ok_b1111011101

private theorem ok_b11110111 : Impossible board_b11110111 :=
  fork 72 ok_b111101110 ok_b111101111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11110110111 : Impossible board_b11110110111 :=
  kernelLeaf board_b11110110111 #[0x2346552f3b533947483664535a555a24093523554d3614411564652465293340, 0x140f3b644d16133b2b47233b4d0a2441475a41537469232460302923645f4536, 0x4514163b3b746e45643b74] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11110110110 : Impossible board_b11110110110 :=
  kernelLeaf board_b11110110110 #[0x362b233b4d4130354f0c2e364739294d35332f4d331a581e35537a4760342820, 0x2957493958604f47235e5a4927160a3b2907573b3b3623515729052707491569, 0x5f23362f0a2445294634292b4d3b495d3b4d392f216d5224453b5f2315275765, 0x541c2d1b612729572954604f472330411a2f39234716232b362f3b244d292f29, 0x5e51782e372457365f2330464f2847354f2f2960542d284722545d51281c1c2d, 0x2254283d3d512d302f2d4554285e36302f336f332d54281f2d2d670e30294d2f, 0x3b47363b07572e3b1b23301946362930413d69747a3b5b54242d4813112d5428, 0x411e233b29302e3522354529333d3b3d3b233548152137574d0a3b5e2936215b, 0x2f13512916211f29792f3b2f47232b3b21341e2d342274352d3b523b2d1c2823, 0x474113210e293028512f6b3b16412921252d0947210a4f3b253b29470e23302d, 0x5a6e3b301e29131f3b3b690e2330236e3b29341e222d2d1f3529542d70346c0e, 0x302221413b3b39210e3022] (by decide +kernel)

private theorem ok_b1111011011 : Impossible board_b1111011011 :=
  fork 92 ok_b11110110110 ok_b11110110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111011010 : Impossible board_b1111011010 :=
  kernelLeaf board_b1111011010 #[0x2318514f2f6c5f542228365f5739282f3b64474f5814232f184f39232f362034, 0x642040356035186023082919580c224b292d2f2718601c0935292f1f54351d36, 0x145d492f416a182335416a49742423354d0c283345352423412e27686f232f36, 0x3661707018747761412f2d4166542237392e5d2d412d2f28232d411d29373b24, 0x742f2f542241603b412b33296424714139281a412518363664411a2f2d5d2f2d, 0x350b2f182d41701a54282d331c33352f18332f5d1c61605b3518645470281049, 0x186470350e6d614176682f6b6f355f396d2d417c665b5b1d352d2f61642f6171, 0xe1a4535356f3329454d362a23413d6b2f142b2341291f276b2f3d2a4b452d3d, 0x33577035292d3761361073373b23364168144f2f412a18294f151f1f] (by decide +kernel)

private theorem ok_b111101101 : Impossible board_b111101101 :=
  fork 86 ok_b1111011010 ok_b1111011011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11110110011 : Impossible board_b11110110011 :=
  kernelLeaf board_b11110110011 #[0x557753416040295b552d51375d576f695b5b5d217a455f3b65412a2a4f47586e, 0x284760345b41510961165b6f5d53393f3524566435555f0e5f2d1b55532a3b55, 0x252d116678374d1458565b1a7f7729415545536f532047122835562a294f1039, 0x61374d4b63292a356b55513b372d2d3b37454d64512a2d2f3b2d1f2f1d642925, 0x2f162d4d3f64405f2e2a64496b6153646064616d5f212d1d350e1f2d2f285435, 0x212d306545294d18291639475864142d1f360e472d511f632964603b3f614d39, 0x5340715d4d552327512d1f2a5e0c295334555b4565412145211f6a45726b6551, 0x5e58145b6d415545770c3b666b66075e53374d5d4d55671a2f605e1f6b512f4d, 0x21371a672d5f4737302f6547636529544d3b5b7a4f2f6a5f6c67654d51372f47, 0x654763362429165f674d511f475e583b30535b40635f6534652d2947375f45] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11110110010 : Impossible board_b11110110010 :=
  kernelLeaf board_b11110110010 #[0x5455412d4d3035647e2a4b29355d2f644d56210e18214d395d4629394d2a4758, 0x24373f2d615d555640554d243b78287653602876604b731f6a2f2d7616616456, 0x4160556016532e3b064d0965553b3b6e603024655f3565605e532961574d2d1a, 0x104129551a3b371a533f] (by decide +kernel)

private theorem ok_b1111011001 : Impossible board_b1111011001 :=
  fork 104 ok_b11110110010 ok_b11110110011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111011000 : Impossible board_b1111011000 :=
  kernelLeaf board_b1111011000 #[0x35511c2416303b74693037697467784d576512276007211a131b27163041292d, 0x3565304d5b212f644d3536561f161f564d3b371a163b725b4d30245407465365, 0x391f4d4725372157511c5725221b23545e514d413035644d4165374d5141304d, 0x202e355841111a23353b2723416e58162436131c211410290e224d581f693b45, 0x46351f1b39511c2e5351371f41275d0f0e141f1b1c2e47411a2146172537141d, 0x4551374135472e413f2128684947411b394153251a1c282e23251a25282e415b, 0x37096f282925371b28214d293b46213516273b3b356d2437] (by decide +kernel)

private theorem ok_b111101100 : Impossible board_b111101100 :=
  fork 92 ok_b1111011000 ok_b1111011001

private theorem ok_b11110110 : Impossible board_b11110110 :=
  fork 44 ok_b111101100 ok_b111101101

private theorem ok_b1111011 : Impossible board_b1111011 :=
  fork 78 ok_b11110110 ok_b11110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111010111111 : Impossible board_b1111010111111 :=
  kernelLeaf board_b1111010111111 #[0x4b144e55391c2d1c0e601e4d335855294b27062d1c2d662d1874144e222d2926, 0x853640c1853251e2055212f273f2920640c41] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111010111110 : Impossible board_b1111010111110 :=
  kernelLeaf board_b1111010111110 #[0x3d2d0e250e255f2d7057111f35331423490e601d1f6a110c1f2d6153352e3654, 0xf61454b262e2d2117116f6373596a4d2d2f5722550f2263353318113b3d141d, 0x272f352f272f3f2e2261451a1f374b6b563d04531a4e2f611d110c374e61351d, 0x294b37191f074e702d354b27294b131f116b4d35150e0969531a4e702d2f123f, 0x336a7e2d2f6937637a612d53351f6b6a4e0e1a0e2d2d2f3d2235263308701e45, 0x33336010295c2e2d2f3f332f3f27334e2e27330a1a2d355733633545603d4b67, 0x3f1c1c261b55213f1b33630f1b4e2e3f2f2f3f2955662249295c6a17350f1326, 0x4b352d1b0e1314222259675f354926630f35144b224e3370111c3314291b1b2f, 0x72352f335b2d33330c3565644e58171c2f2226261b552249337b2f294b2f1d29, 0x5553644e1e35333d4535330c455d4f2645556a725c363356682937692f2f121a, 0xe2d5664335c4b601e2f2d2d2d61] (by decide +kernel)

private theorem ok_b111101011111 : Impossible board_b111101011111 :=
  fork 40 ok_b1111010111110 ok_b1111010111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111101011110 : Impossible board_b111101011110 :=
  kernelLeaf board_b111101011110 #[0x371d284e37392d12292e70612f4b3636731f2553765356395b411f53362d3d54, 0x10213925394539141d2737212f3f2728182e61602117102e370060562d0c211c, 0x3537351b4e2114581a162d365b1f374925391625270c3728361b0f1c0c233528, 0x2f282d2726162722602d0c572d35164e2f496035141a2d6136164e272d374e2d, 0x4d3536650b0961162d5b1f4721376039122d294e58605735492f226170391812, 0x634b531645702d45651d5b1f3f537523555f6c64535265453d36364d2d3f2f37, 0x605f2d5f7c456f78286456355b7228574e5c532d392d3f564d3f2d784b0a3f56, 0xa560b1256215b265645781428563925272e57115752370c1b1f204d6c666b82, 0x2e3f275337492d6f667c6e61662d5b56644956352753604f1b212e1b2e082111, 0x552d2e39] (by decide +kernel)

private theorem ok_b11110101111 : Impossible board_b11110101111 :=
  fork 44 ok_b111101011110 ok_b111101011111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11110101110 : Impossible board_b11110101110 :=
  kernelLeaf board_b11110101110 #[0x1a392c22182d1c2218680e4e704b5b706a2233330e644e2d182b260e36285654, 0x361a2d1f6622021228275f5f3d5f0c4e2d292f0f26212f592928335b2c464e2d, 0x2d1a4e1f211264286a3d362c1c64354e1b10362835282f222f0e184e0e12284b, 0x18702c5f28101666361a3318161c3661281016662d23361a6f53274518222321, 0x182014182935476f0e2856644e29282f0f15280c262922292846553628266a2c, 0x6142f165f29202f6529290e2858582958161c746f276f82162d1c23232b272f, 0x662866692d5c5f691b127820211b290e215d0e19281f2f36204d1f2d0e285336, 0x2d455b58336a5d295f5f292345815f2d354b28354b70452c274b122d6e5b291b, 0x4545556c56201b572d3355455c4b2c3d332c454519282f33535664571d21] (by decide +kernel)

private theorem ok_b1111010111 : Impossible board_b1111010111 :=
  fork 52 ok_b11110101110 ok_b11110101111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11110101101 : Impossible board_b11110101101 :=
  kernelLeaf board_b11110101101 #[0x392e555735162323141f64142135295666522516232c60392d4e55593f293340, 0x281b4b4b585e556c454729181208232b4529234529232780204e6434273f2c60, 0x465e556c7855456809364557724e283929332d4e294d18276a4b2d6e4e5b5853, 0x392d1f7241354d45416c3d6e460f2b3d4d193920193d2707061139162336582c, 0x1a45026029333957564f1f78362d562e520a60642b4d4560694e4b3f22163f60, 0x15453b294b4e2d35141f1f174e4d1909] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11110101100 : Impossible board_b11110101100 :=
  kernelLeaf board_b11110101100 #[0x2933293945774b57352d1a675f6a74562e2d820a2b36494b3f1653392d642c60, 0x351139162e23006411351c2e282d3357352b390c111268352d0857352b252846, 0x33291f4b1e5c142e362e1857072233614b52346445352829334b28352e393564, 0x6a3d2d5f347a4159536a36685b5836101d232b6a552e34453b1a5b45131a497b, 0x148210685d4b6464454d3552296f63595f3536687a2c722c726f6468685d3664, 0x3b522e5f1d33264b352d18332e0233292e14727a145229192e232b08362b3b2e, 0x64691b636b675b56676b5d6a4b35363b3d4b562b3435263d2d233366352b2e39, 0x2269675d6b675f533d4b565f5f531b455b] (by decide +kernel)

private theorem ok_b1111010110 : Impossible board_b1111010110 :=
  fork 84 ok_b11110101100 ok_b11110101101

private theorem ok_b111101011 : Impossible board_b111101011 :=
  fork 36 ok_b1111010110 ok_b1111010111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111010101 : Impossible board_b1111010101 :=
  kernelLeaf board_b1111010101 #[0x6b5534593b4b245d55686a2929244141492d6924415f36685f367666555c5b54, 0x4e1a2f742971245d34556859494e3b76596f5f1455665d2d2d245d7169417e55, 0x5b7014364167574e5c1a2d55292849256a4d46665c345f5566626359556a2933, 0x335b243b2325066a236c2e3657554d29284174470a687a474d5b725841296923, 0x62525d395d414e47585927293f294536414f2f596329295f454d416929665b45, 0x25654d2d2c1f726e5f454e294b3b2d4e4d3b681b291f2d2c4d1b0a4e346e245b, 0x5e2c526c573f45523f52456c2d5f231334284e2513574d555546293328182f0a, 0x1a474e5566741c230a555e295224534e47534e741c295e2c706633] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111010100 : Impossible board_b1111010100 :=
  kernelLeaf board_b1111010100 #[0x36253937394e5f39826a70692d536e65296a2084594f29596a7c572f08665446, 0x62415f1c29694f4e5c0e4f4e4e41122b2324201e23396c2c70234b6945774e5b, 0x45542d243b450a452b0a24291517071f292f2b541f4f3610245c231a4e5f1053, 0x416613104e1a6a4e0e5f29282b2d1f544154152f394f4e54153b792423243b29, 0x3f5253694b1a19525c5f4b23247845522e541a2147542b3b4123492d4e2f584e, 0x292e4f241c027a5b531c205b69541c7a704e524e4e372057471f2d1a20534b2c, 0x2454707a4518471c52392d4f531a2d543b41620c5320] (by decide +kernel)

private theorem ok_b111101010 : Impossible board_b111101010 :=
  fork 96 ok_b1111010100 ok_b1111010101

private theorem ok_b11110101 : Impossible board_b11110101 :=
  fork 48 ok_b111101010 ok_b111101011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111101001 : Impossible board_b111101001 :=
  kernelLeaf board_b111101001 #[0x2d3d5433224e34372f4e765933283d2f301e52340c721c345315741a2d5b5529, 0x59652f265e7633475c5c6f5c573559653530471c5c665c5f71356f332e34711a, 0x2e2713585f39543553642d57282d5f532e393753335c3307225c135c58741a33, 0x601f614e1f455839535b5460345853697154584f3d1c53395f343d453d685465, 0x585b453434455b655952452170245b5954342e3f53645852655752652f3d5b58, 0x535d2d2d5335542d2819271c192d553d2f2454525b5466546159544e4e306a34, 0x3534352e225545332845545c713952652e244f6535334f3d2d26285b33475f5b, 0x1f3315740a4e141d1560212e5d60371d712d330e2835195d553d2b5b2e4b3d36, 0x60242d172461156a2d210e18542d08572d211c2e1f2e07170c1c2b333b342d1a, 0x342824343d3d1a2d4b245853] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111101000 : Impossible board_b111101000 :=
  kernelLeaf board_b111101000 #[0x455f2b302b3d2e350e65572e1a52651c302d0d090622281b1c0639300e345529, 0x5b65575834615b453953345b5453642d3537542e655339343d61592d5b304e2e, 0x392d2e6c771769553d26352e19272d3d2f2b2e245d55273d24394753212e3434, 0x152434283d2465241f55651c2d2e35351c242d5c2e2d5b182b242e392d4f5d2d, 0x542445521c2d54343d4b6453692d] (by decide +kernel)

private theorem ok_b11110100 : Impossible board_b11110100 :=
  fork 35 ok_b111101000 ok_b111101001

private theorem ok_b1111010 : Impossible board_b1111010 :=
  fork 72 ok_b11110100 ok_b11110101

private theorem ok_b111101 : Impossible board_b111101 :=
  fork 74 ok_b1111010 ok_b1111011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111001111 : Impossible board_b1111001111 :=
  kernelLeaf board_b1111001111 #[0x1b1b282154121c524f534b5b0e1d521c603735255e4b37596a4a7054182c2e39, 0x28154f145a5a1f2854403521696a21295b07280b211c1b21697665681c28254b, 0x6920484f471e2027061e481c4a291e291c4e181d591d55544f132848614f205b, 0x4b5e12235e27281b1421294e2c34484847275a4f4e281d2560182041205a404e, 0x1f13171d150614121d212306234a271c35471d28292616263f1a21214f291b27, 0x51e400e215f4e40281c211b2c29352727211d41631f471d3528144f5a48265c, 0x104e282822291e2f3f25515b1d1d1a604e29512523471b4e2510234718284e2c, 0x5e541426340c14402234511a40222921281d15481048145e4e5359284d4e5a3d, 0x16514e2967251b51213d27341a511c19494e0d280c1a19223d192229274d2654, 0x1c22601c1929632f492c3d34411b5a3d372e2e400d2e4922512f4b594e512549, 0x230e231c3b2934372955573d472e651e5519282e491a5425531c341929515125, 0x3d0e3b2b234a] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111001110 : Impossible board_b1111001110 :=
  kernelLeaf board_b1111001110 #[0x6f120b17190c0e1e222f51555f0a150e2064545b4e0c4e4f6a5a474a1e402829, 0xc5c1c6c565a124f134d131a1a3435052b130e26130e194e200c154e5b4e194f, 0x1c1222193420072147075b4e1257190c6f1e20151b55204e4e540c4715622654, 0x1520222f271c150c224a4e1d1326215947152248142f272013130c470c0e4715, 0x145c5547470d0c2f4a151e104e154a591e14404d2f05371d120e3f4e0c483714, 0x4e403f4e0c18195e0f4e4d4b142025180917463d491928222f25251e481c1212, 0x2e25214854182614210f213d1c0c481a1927550d0f60680d0f1c5e1862490c1c, 0x11282134252826192e1c26610d1912191c181f5a4e124054752009184b6e6a5a, 0x612b54181218405a14611814154a4a4e260c541f12264e140c212228352e2519, 0x4022181e142048264820180e4014252e1e0e2118266a404e0b39541f0e4e2140, 0x69186c2b143d14393964346a59544a4a2b142b271e4839285a471b1448184f] (by decide +kernel)

private theorem ok_b111100111 : Impossible board_b111100111 :=
  fork 51 ok_b1111001110 ok_b1111001111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111100110111 : Impossible board_b111100110111 :=
  kernelLeaf board_b111100110111 #[0x2f274e4b293d4e5a54084b154e5e144e60122222391d354e5e224b211a2f1e34, 0xe4f1a541d13291d2129271229155c271f135e081b2f4d511d351b0c4e0c4d5e, 0x5a5a63651b5b142f5661704e222e18264a272f1a274d1d4d51354a39290c4e4a, 0x1210234b141e5a412135183351492f4b493351336249624d565414] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111100110110 : Impossible board_b111100110110 :=
  kernelLeaf board_b111100110110 #[0x755b54351854221454585658681a2f702f27721e4a142f222929355b1e545c4e, 0x6a1b630f2b7033260c54145429142f562e613937544d492e1e4a29645b4a5671, 0x1d3b466a222f144d616a4d142251751d7e0e70562f2f5139295b55134f5c671b, 0x352f765a2f5161564d612f5a495f0e2f3f5b4a3957460b70184d337e5a086141, 0x140f353b5135390e05411d333935562f09412e1d1d1435142f2f4d2e2b332607, 0x223308701e5b33612f334f39561d0f111d394d4639112f103f3302223f5a564d, 0x2951294d4d5c6a2e395770561a1b404f29334d515c1d6a1d26103529330e2f10, 0x331f2e144d3b292f2f4f4d5c1326331f29390c350e1e4b40142f3b185a2f2939, 0x4a294f394a5b4b3b510e1a18] (by decide +kernel)

private theorem ok_b11110011011 : Impossible board_b11110011011 :=
  fork 40 ok_b111100110110 ok_b111100110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11110011010 : Impossible board_b11110011010 :=
  kernelLeaf board_b11110011010 #[0x181f5b606d691b763460340723164961391a27051c342221602354283912294e, 0x512f1f4f4a53393d1854391b253f273739513449376c495b4b2737370e232716, 0x4d1a461a1d702f495c37514f1d290e1b1b2560271a390c562809252f25163516, 0x273956534f2f4a53393d37514f3929530b3d2f1d491f371f1d4b4d1d27464d1f, 0x2f564b3516371f4f4f2316393d2f2539] (by decide +kernel)

private theorem ok_b1111001101 : Impossible board_b1111001101 :=
  fork 44 ok_b11110011010 ok_b11110011011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111001100 : Impossible board_b1111001100 :=
  kernelLeaf board_b1111001100 #[0x55265f604e21061c4e18225f5f060f3d1826682f1a625c5e511c2f513735283b, 0x275b605e6b5e6522131422342622091a1d281d211e101e2834551c105e221c6c, 0x18610e60292e182e1d654f2854185e612368651c2e262e341e280e294a35080c, 0x6e162e55553d27265f4f60532e391c291b261b262e26331d2e6a290e60282e2e, 0x5533181b611876791c2e4e3d1b1d1e55284e5b2e1a28370e110676] (by decide +kernel)

private theorem ok_b111100110 : Impossible board_b111100110 :=
  fork 72 ok_b1111001100 ok_b1111001101

private theorem ok_b11110011 : Impossible board_b11110011 :=
  fork 45 ok_b111100110 ok_b111100111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11110010111 : Impossible board_b11110010111 :=
  kernelLeaf board_b11110010111 #[0x2f741c5b6a182f372d515e541d182d2e3b4129540e2d212d5110374b2f1c2640, 0x4e2f1922353315171b4b1b234d354e2f1335352f634b590f391d2e14281e181f, 0x1e17335435351d2e352e2335352e1d540e0a4d1d2f39354f474919221c092b17, 0x2d151e27292f1965295f594f133510261c464b461b171d7c681c2f2d4e512f1f, 0x2e597a68605e555427357a3b352e64642155543b212f226c1014471333351d15, 0x155a59744955146a25333559512d492f5447295a0b152d292f5e3568495a595e, 0x642f5b] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11110010110 : Impossible board_b11110010110 :=
  kernelLeaf board_b11110010110 #[0x3513281d3b15091d4f394e14393b10351d0f131d2f0f37153b0f104e145e2e1c, 0x1d0a141d2f151015191d3709394f14470b13374d29336139392939291d4b2233, 0x492e481539596c1419686c495e603b3b514107121d0a29274e1912141d3f1f4b, 0x2e512f4e3b6335292f2e4e3b64355b222f2f2e4e2b393f2933392e696555484f, 0x3559194e3537131347154e132f1929336c5363495a1d290c2f334e5922292f35, 0x1f1929353333594d4651464b6a72532f276e353b600d407e222740634e2f2939, 0x40] (by decide +kernel)

private theorem ok_b1111001011 : Impossible board_b1111001011 :=
  fork 32 ok_b11110010110 ok_b11110010111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111001010 : Impossible board_b1111001010 :=
  kernelLeaf board_b1111001010 #[0x5e3b4b5329475b2d292921745129213b4e3b1d333b1722514e3b213959295a14, 0x4d2d4e1d0c16290e2947415f1b160a0f1c294659393f0c1d2726354759296859, 0x411d4b3b2847231f192d1f0c2d132d1d606a544e6549190c221b13104e41591f, 0x28351f39411d3b15162847234d2d2d3b4e39151623592935275b5b154e354739, 0x3527] (by decide +kernel)

private theorem ok_b111100101 : Impossible board_b111100101 :=
  fork 52 ok_b1111001010 ok_b1111001011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111100100 : Impossible board_b111100100 :=
  kernelLeaf board_b111100100 #[0x194e35601327491f16600c3f1c4e39374d21675135164e134e521f371d392d29, 0x2d4b183f184b250b2d37531d0b2d18210c4e514e602d374b2f1f21144f234e39, 0x373557213537255157356f0c21376839233735104e276a4e0c1c4e4e4b16] (by decide +kernel)

private theorem ok_b11110010 : Impossible board_b11110010 :=
  fork 44 ok_b111100100 ok_b111100101

private theorem ok_b1111001 : Impossible board_b1111001 :=
  fork 42 ok_b11110010 ok_b11110011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111000111 : Impossible board_b1111000111 :=
  kernelLeaf board_b1111000111 #[0x2a19473f1933252054765919272d766a1c1c4a2d005c544e3d1c08685e1a222f, 0x163d604e0c4d515c232d4e271f4e114e3f600b3d19170f1e335408270f33490c, 0xf164b0f4b160f17330a2520271c344e5e19682d1619192d122d166a2319171e, 0x3d1c2551210f3d213d257a5a4e181a49334e1c3d680c514115511a15211c214b, 0x394f47232d7b47230c3f12201e252d3d544f1c4f21152a2b1f1e11165418195c, 0x1515133d2e394a254f18222b2b15511546515c4e693d271c274e2b52] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1111000110 : Impossible board_b1111000110 :=
  kernelLeaf board_b1111000110 #[0x16645e743d0a6160541a1a61691b091660540e1c4e414e1c634e4f460a234727, 0x542f1c2d5b2d2f554e4a696a004f1b161a1646463d1b2d160e1c5419202a1a54, 0x281c542f69205a62217a096054413d2e48474f1321200c4e150c2d1a1c232d20, 0x415858633957575c2f5b4e2034192d3923122d231f1539341c1a2d3959395733, 0x1a4e3f65574e3f17142125333f0a2b285c4e21331f2d14390c28210e1c5c556a, 0x211b1c545b60576e0d2d1721231c091b210d2b1e19765c20093921092d1c2361, 0x154e33190c15142b2133254657252b211e601139392d11211741252d14] (by decide +kernel)

private theorem ok_b111100011 : Impossible board_b111100011 :=
  fork 41 ok_b1111000110 ok_b1111000111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111100010 : Impossible board_b111100010 :=
  kernelLeaf board_b111100010 #[0x475b5c73695b6d605b5c22587c2f5b1a3760636f6d63555b6a29145c695e4e51, 0x196a27216a5e5561756a1629492b735c5c5a6d6362732b5e4d2a28626d276321, 0x214f4d57271b5b1b270257212d4e3d545b1a64625b613d6e5c6a541a2b5e1a27, 0x5921270e34161c0d1a685b2959596a605560552d2e69591e572d1e1c2d29692d, 0x6029551f215b4d2d7e5b735c57272d21147e5b693d4e281e134e1c1a2d1e5c08, 0x7757615957615a5b29161c2b211a575b2d693d5c6957295b492d2d645b632d75, 0x5e494f2d1c] (by decide +kernel)

private theorem ok_b11110001 : Impossible board_b11110001 :=
  fork 59 ok_b111100010 ok_b111100011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11110000 : Impossible board_b11110000 :=
  kernelLeaf board_b11110000 #[0x41495b2d09552d65272d142b0d21295b606a1b2d201c6e635c64226a5e514e1a, 0x1f29227849605b6f3d4b4f3d542b396049644d515e2f4d2d682b21471b2d4d1f, 0x605c6f573d4d221f4b621f540d54071b13291b295449476a2d515147624b6e16, 0x252a1447494f5e121454072720130b3d2d1f250c1b1916296a19476a1f4b1b1f, 0x3f20250c182a602d463d544959463d3f0b3f5b594651161f136551190e545c39, 0x12071b1f52410c4e16296057492125511b1625213927205e4f5454682016463d, 0x4e3f2a2a063d182b0a5e1f1f13634e0e1917390a4e2313195b764e5c0e1c2b5e, 0x546276252958684e161f515c395b4e2d62225e4f5225414b3d4f522d5b2d5b51, 0x185418215b463d512516291c05172a] (by decide +kernel)

private theorem ok_b1111000 : Impossible board_b1111000 :=
  fork 44 ok_b11110000 ok_b11110001

private theorem ok_b111100 : Impossible board_b111100 :=
  fork 48 ok_b1111000 ok_b1111001

private theorem ok_b11110 : Impossible board_b11110 :=
  fork 80 ok_b111100 ok_b111101

private theorem ok_b1111 : Impossible board_b1111 :=
  fork 58 ok_b11110 ok_b11111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11101111101 : Impossible board_b11101111101 :=
  kernelLeaf board_b11101111101 #[0x644853512e4622202e2a56142b3434560968204e34566e531c201a2e215d362d, 0x141d2b1a0809272e5d4e221c342e394f100c5a2e1a304e214d48481462224e20, 0x503a2a584c252054223039141421362e5a2130495918151821302a5636512b2a, 0x4f4e3a2a4f3a502e271d302e21675d492a2225362a185d21513756] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1110111110011 : Impossible board_b1110111110011 :=
  kernelLeaf board_b1110111110011 #[0x7f5f154f286a4f30225a50616921331b510b374f1c074e54221c5a36332d4d6e, 0x394c54545a362d5d155a2d5822394f5f30304e271b372e3046282536112e3628, 0x304e3d5b542e5e5046373d4c592b4e395d393d537117363d2d49572d5a4e225d, 0x252e285a19362b3349531b36300b2524304c590d273d53243d1c397a584f574c, 0x6751695e50545d4e4f3d4e5a4e544969515c396d64392b675d54695330243737, 0x4e3a5058463a5d482e5e594e58285d505b583d6571545b51515149545d665a51, 0x4f2d54365c544e482a2d51364e245a3a23462e2b3d4c5446224e546737405e22, 0x334f3933182e2b394f2d46332b39482e3a675366283d344e2728212840225a28, 0x27344d4f396349542333483a2b396a2e465954305f545a30544f745e5a224e33, 0x332d2d4d5a61332e135e516739692e5f5a693a232e2e2d5e3d4e2d392e4e4d63, 0x5b4e39495469334d4f5a33] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1110111110010 : Impossible board_b1110111110010 :=
  kernelLeaf board_b1110111110010 #[0x5a271b372d6a27591a2e1d2e0b54592554274630223654224c2828612e21334d, 0x614e6a54334e3333285d2d59343d4c20495a544c5a2e403a505d543936494e5f, 0x2d3664515a514667735e36542b252d54304e742d283754515150572b546f2b5e, 0x2e5d2b392e2133270e224e30333d4c4e5d59503663513771175e4e2d4e2d3336, 0x391f251a30512e215436252b4e2e51213334592e4e30213928364e304c3d7a5e, 0x1b2133715436252a2e675137072814546751213330252e30273d51642e214e54, 0x2d4839282d51304c1839152821333046365151503a2d2d723d48272d28391855, 0x4628741e2a5c36] (by decide +kernel)

private theorem ok_b111011111001 : Impossible board_b111011111001 :=
  fork 98 ok_b1110111110010 ok_b1110111110011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111011111000 : Impossible board_b111011111000 :=
  kernelLeaf board_b111011111000 #[0x2b535554624d1b28360b335d541d28121b283336371a1b281d37275d6d3d392d, 0x3327535d363d2b515d51675418542b1d511b14402b5d4c5e482b401c210e621c, 0x591a4d0e1618211d33480d343d332416161b2848271b281d4f4e21615f18392e, 0x51544c4d21580f6254182533283923483d274837362a0d281828734d4d541825, 0x1c39340f1a1b392337] (by decide +kernel)

private theorem ok_b11101111100 : Impossible board_b11101111100 :=
  fork 86 ok_b111011111000 ok_b111011111001

private theorem ok_b1110111110 : Impossible board_b1110111110 :=
  fork 38 ok_b11101111100 ok_b11101111101

private theorem ok_b111011111 : Impossible board_b111011111 :=
  forced 71 (by decide +kernel) ok_b1110111110

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1110111101 : Impossible board_b1110111101 :=
  kernelLeaf board_b1110111101 #[0x33132d343d4e3d3451142150333a265e2230212e51302d261f2d374951503340, 0x332d3a34372e2415213a335014542a3d344e671350333a203748394c460c3351, 0x54333434172e103a3d3433544e635458616f621d343a67515334372e24514e3a, 0x3327332d5033343d4e51342e5a48372e4659392e2a2d37513346343d335b494e, 0x3a5b4e34506363145b4e303d1426030d5b3d344e302d4e26501c481c50593a34, 0x1d20503a4c481c1d591c535373591d2e5b4e503a19594c265e503a1c0e63260e, 0x535153592e4959392e374667624c595633331b1226101a1b1a182e26562a3454, 0x5a672e6277624c5959395626265a5357264c2a51513a34532e48392e53513446, 0xe341228333d46301e3956463d39211f531a1e4e3925142e1a2e53466649] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1110111100 : Impossible board_b1110111100 :=
  kernelLeaf board_b1110111100 #[0x4e502422131b565849244b402a534e52534e184e5c2749496a1e561a4e502e31, 0x1a1c073363125017330d58101a300a1a3317491a1b284e1e17284e121c111a1c, 0x342763626f61556a226d626a5a646328615626251c26586a4e223a5433251730, 0x3a2d542e5266582a52403f304e223f271e1d3a504966072422525928204e2822, 0x5656634e273d461a2a54542a1a1c561f56543a2d344b1b2e1b54172747545c40, 0x4056545b56402d453a2e26565a506c26565956185627542e18221d21542e5026, 0x1d561d56145c5a1726493f5937142a562874072d37595c6a541b26561054142d, 0x673a5222114e602656281d563a54] (by decide +kernel)

private theorem ok_b111011110 : Impossible board_b111011110 :=
  fork 77 ok_b1110111100 ok_b1110111101

private theorem ok_b11101111 : Impossible board_b11101111 :=
  fork 41 ok_b111011110 ok_b111011111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11101110111 : Impossible board_b11101110111 :=
  kernelLeaf board_b11101110111 #[0x3a562a34591d20213646375d18375e46375e25182026362d3334342e18295451, 0x5c685d2d4f29591d2a5d3721361c2668615e5d761421263a685e3021254f4e30, 0x3a3a192727096e56205a362d5d4e5d7330683a184e3a4e5c30273d3058553036, 0x59622d5d59465826633d59365426631026365b782d5d564c54203a303a716327, 0x675a29] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111011101101 : Impossible board_b111011101101 :=
  kernelLeaf board_b111011101101 #[0x12541e4e34625234403623214034363f343154680634364e252a1f4e343a5620, 0x4c5a3a463140365a3a4e681952335225363a302a1f2a252521362d21545a3a46, 0x28460223553724292e4034561a253f303a5246523627525247615a631e544e36, 0x364e283a331818283a2a28334018283a731f373724374f3a282d362336283a54, 0x363a5446283a1d124646331d1c29464c54102e460f302d462921346240362e2e, 0x6a2e25305245403a3a252963331d293021403045731f4628362a2d4c40584651, 0x543a2e3a30731f541d3a28302d2e283a544634272e0a17292823272e281d3a28, 0x3a2a2d1d1d184e401c1c271e34561452361e17314e1e3a523a2e3a303a092833, 0x622d2552171f2e184637212e365224541f27341e2e2423246c33183a33241f54, 0x243a286c4e332918282a3a1f2e371e271e0a283a34362a3a45233a295428102a, 0x24363a2e2e313a2862] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111011101100 : Impossible board_b111011101100 :=
  kernelLeaf board_b111011101100 #[0x251c19252d374e0a294f213421682962186459622d0b0f7354152d215d3a5640, 0x140815191c363a3a5618732d54581c2a6218583a5b5462293029254e2d0d1c1a, 0x3a18731c281a61715d3a47696a36366f0f300b250737562815132537183a7a25, 0x690d182521374e181c27297a0d0f3325360b212e59642556332e371e33565921, 0x1c58364c560d001c27290c2e165a27213433514e0f33561836251f18643a3a33, 0x3034451356133430272e33132930342534364e584559456e5a58273427335656, 0x34] (by decide +kernel)

private theorem ok_b11101110110 : Impossible board_b11101110110 :=
  fork 38 ok_b111011101100 ok_b111011101101

private theorem ok_b1110111011 : Impossible board_b1110111011 :=
  fork 77 ok_b11101110110 ok_b11101110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111011101011 : Impossible board_b111011101011 :=
  kernelLeaf board_b111011101011 #[0x5121295a5a5154460f0c061c40244d4c0d236d482d21361d092d54283a34561a, 0x6b281c4e1e622a451f1d2e2436404d1d283a18651d09543a0d1c1f362d400d10, 0x2e1d1c462129545c2d462834622a45281c364c721e465d3124281c4e1e4c3124, 0x4e29293a281d28232830291f18652848362a2d301c2d674d545c2e4023302e13, 0x561430511d3a2823302d4f4f5a544746343045281d2e2e292931281e36451f28, 0x3a1f18212d2a1d23452b521e4d522e186c24362b1d1816212e2e5a271c2e1e34, 0x1d271f2e1846362e3160365224361f293a60521e401e271724733f2e2a311d2a, 0x1f272345211f2b1e4f5231524045526518451f24362e1e1e0a545418181c3a34, 0x4d542a3a2a104e274e1e241c242e5d245e114f211c2807620a732e18311f182a, 0x28401f18513d271d5c542d284f] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111011101010 : Impossible board_b111011101010 :=
  kernelLeaf board_b111011101010 #[0x183151522a3a2405212d2a2d1f36311a544e1e5d211a476254064e364e3a3456, 0x28514e1e513a34483a735e522a1c100f311c232a511c2d452a1f36622a5d6b2a, 0x46483628545a511d5e36451f362d462a27295a463d642936744e3a68461e3a2d, 0x91f1227511a16215b46605224363034293d3a1f231f4f3121341a1f4e24175c, 0x2831346e345e46] (by decide +kernel)

private theorem ok_b11101110101 : Impossible board_b11101110101 :=
  fork 32 ok_b111011101010 ok_b111011101011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11101110100 : Impossible board_b11101110100 :=
  kernelLeaf board_b11101110100 #[0x62292421484e29275a34404045212d365a48273d4f48481a284828541a5c2d3a, 0x2e4051173d4f4e274f13277446301e2413565c464e214048022927] (by decide +kernel)

private theorem ok_b1110111010 : Impossible board_b1110111010 :=
  fork 38 ok_b11101110100 ok_b11101110101

private theorem ok_b111011101 : Impossible board_b111011101 :=
  fork 83 ok_b1110111010 ok_b1110111011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111011100 : Impossible board_b111011100 :=
  kernelLeaf board_b111011100 #[0x2d615a4f254f516719372d052e0d214d541813630847481a2d0d1c5a3d27263a, 0x1025181a15185a23611d4b254d4b591d51142e1916212d4d1a192d4f134b4b3d, 0x1e1d1727136329292a5929271d1c272518291515070f27212751471e54214d29, 0x47295e514740294d12514719404d291d2005510a211c545419291d142a1e1529, 0x3d27205a251654181c5e203d191a1c4f4e203d1627304f1f2d47291e1f1d1c51, 0x1717150d4510104f1a2153312e23624e4d59291d6816276923141e291d134f4e, 0x8291d5a1a2159214d1d4537210d212740544d61274e33485b2525211c1a1e27, 0x5a08231a1e1d1429531c635a1c2627041640160f125e1023161c1d4d161c275a, 0x1a5a4f5162294b51453f1c6b6a635e66630d1c21720d1c681a5856312a151245, 0x375626451545137845131f2b72295a305e453f594f5351594c484c4f14454c4f, 0x27374048275a631c1727294d162721023d1c185a59153d1c2733545945212d13, 0x5e31305314343d4d4d5a2934] (by decide +kernel)

private theorem ok_b11101110 : Impossible board_b11101110 :=
  fork 80 ok_b111011100 ok_b111011101

private theorem ok_b1110111 : Impossible board_b1110111 :=
  fork 47 ok_b11101110 ok_b11101111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111011011111 : Impossible board_b111011011111 :=
  kernelLeaf board_b111011011111 #[0x312b212a4d3a6d5a21241c24331f2e1c3a212a68271f1f364e271c2b24615614, 0x1e2b1f2e312e4e36245c2e2a313476665b5b6367674c596c361f2e3a212a6a48, 0x4e40584b0d58671a652e252e272a624d1c1f4e2e2e2518213a6850273a25301e, 0x58314c5b5a314c5b5a0265305e4f5a312e4b3a595155627a2a215a253a4e2418, 0x7a2a2e253a4d2424314e3a56501a2d21252d21252d274d554c5b5a4e4c5b6702, 0x21610d1c344c273a211e3062482e4e24610d1c314c56274c2e5a2a4c0f1c2730, 0x4c1736242a2a2159242a4e24610d2e2a2a1e6231344c0e240d4e192d21302534, 0x5167244021244e2e2a253a681c314e3a2e111e3a1c302a1f0f0d2e5a] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1110110111101 : Impossible board_b1110110111101 :=
  kernelLeaf board_b1110110111101 #[0x362e22685c17312f2d1f402e3a1c2d2e2a3427312e4e5d3a2f2a341c2d365614, 0x52792e7a2e09342b0d2e53307117603d67523d543a2f316d4d18363a4e241f2d, 0x362424162e223d3624162e716715650d092e070e362e5a2e1e303130274f5a31, 0x31655a5b3a4d222a2f302f472f3d3a1c1c1c311c1c672d13273d2e682d221f3d, 0x593d31315e4b792e3d675162515e3d5e596d7a31302e25315e2e3d7117305a2e, 0x215e305a02742e525a2b2e3116313058312e305a023115703d0e653910067525, 0x3d535722516221312e604947304e2d34162e3d71524c395a605a2b2e31162a09, 0x36162a34281c4f40532e3a560e58616d675e60512d5e703d6b5e6c6659584b4c, 0x302b1c2b3021161c3a161c312e1c2e312a34615d0d2f282e53522431182e1c2d, 0x30303a1e272a2d40121e271c3a1e301c1c52312e2a31225e344f182d15] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1110110111100 : Impossible board_b1110110111100 :=
  kernelLeaf board_b1110110111100 #[0x532e393a2a39182d342e3a15211c5a2f482e341c2d36242d1c362d504e2e3156, 0x4c574e317117523654302f3a222d0f5a2e31364e5858615b502e31404d622d2d, 0x2e313a2a30472d3954392e31522d22304e341c1b3671272e30394c79312e3039, 0x2f520f4f542d36363d526d654e2e314d5c1f3a342f4e4e363447542d4e4c302f, 0x52303a364e586f4f514e2e392e12315271272e394e09272e3117272e3a365a30, 0x66613960585b5260713a30394e573117305a614b315b3a4d30502e5a24314f3a, 0x2e3131306e5a594e] (by decide +kernel)

private theorem ok_b111011011110 : Impossible board_b111011011110 :=
  fork 26 ok_b1110110111100 ok_b1110110111101

private theorem ok_b11101101111 : Impossible board_b11101101111 :=
  fork 35 ok_b111011011110 ok_b111011011111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111011011101 : Impossible board_b111011011101 :=
  kernelLeaf board_b111011011101 #[0x364d5a674f2d233a34342763622b2e2b310627153a244f4c2d233a502e2a5614, 0x79677a5a6053522e5c212b361e272d2427082d271c0a1c273368612707364e25, 0x3315273d2e6836272d242b4d364752512d22494d3133515e1e3a23364d4e2b6c, 0x4e2d3a4f5749605e2e0e71332a31606b635a2e4d3a22243a2a2a3322271c2413, 0x492e62665e59342e3333316763173a222a6031635e2e62582e515e6763172431, 0xe614f60515167615a63615e7060636c3321666b635e5a6c66592d222a574b60, 0x4f4d604f5239314c173148532e362b341e31283a53534f1f2b28341621242a56, 0x4c5131605e2e7128334f28343a27271118131c282d362350332b2b5061342b4c, 0x51535e39493d3a31186363701667394770535e1c5a2e682a24314e5e343a4f52, 0x5a2739535e23674f60533a2e51222d312a313a2e4d2d22313a2a332267591c39, 0x6c2a313a342a31271c186268532e222b52222d2a393149336b395a3433492d31, 0x24562b5934312a623a4d593118595a0d3431494c] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111011011100 : Impossible board_b111011011100 :=
  kernelLeaf board_b111011011100 #[0x361c33481c392a343627332e21392e545336544d4e532e63286d54344f2d3a56, 0x1f4e470f2d4d2d21335f622e392e25242831233153312a2e5827274834232d53, 0xe273454362d21273336222a0f314d152d28254e2d2a2512314c1b2e2a4c542d, 0x4b3a2d28392e4e222d3a28282a495c3a4b5221394c2e2a1b573152284e4b3a71, 0x3a2e2d4e6052710e3a27332d2a1c3160274e225c4e4e635a2e4d505148493152, 0x2e4e1233222d334e4d2e21392e2e4e4f542d3a5c31523a3a222d2a602739495a, 0x2323] (by decide +kernel)

private theorem ok_b11101101110 : Impossible board_b11101101110 :=
  fork 26 ok_b111011011100 ok_b111011011101

private theorem ok_b1110110111 : Impossible board_b1110110111 :=
  fork 29 ok_b11101101110 ok_b11101101111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11101101101 : Impossible board_b11101101101 :=
  kernelLeaf board_b11101101101 #[0x4e34343a4e39312e225c3a244031271c31341f1739311d182e271731532a5614, 0x312e1e30275317312a333a345e2d312e2262173931341f243a303a4e31522e1e, 0x4e3a2767271c2f4d3d2e68301b4e604e6351341f2a275e717a391d4739312e1c, 0x534b2e3a22310d1d2a492e4e5e515e186f1f63513a4e552f312e1c30276b4d2a, 0x4b31525e705a63554b5e666530395a2e31305a2a2e3a680e60574e542a312e5a, 0x5a34765e7e557e636622345e5b69635e70606c4e5e31526671312b58605e316c, 0x71332e4e4b5b6d405e2e63275a573165522234334d632e5a345b76697d5e706c, 0x4e6330472a4e2e5a5a22495e4e3a684b5752635b6034532a5155312e343a5b5e, 0x3152212a1c2e404d2e40473a560e6654675e5a607966546a675e212e5b493a1c, 0x30342230212431522a5e34303a4b5218470539311c34222e122818213931532e, 0xd3456311e0c1e3131532e09471d4d3a1c152f1b2434392f2756311c1034122a, 0x301e3a2f15301039311c40392f31182e3a0a301e3100301e] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11101101100 : Impossible board_b11101101100 :=
  kernelLeaf board_b11101101100 #[0x62071b315c283034225b636e49300e625247562a303466304957302d564e3a54, 0x505a2a3a34495a502e5a702e4e623151394e4d34212e27502e3a564015173310, 0x272e272824224e63316165636a58215b177265342a342e6e5a303a495a502e5c, 0x331709212e3049301030574e3a6f4e33565b4956562e50571b302f0e12281c] (by decide +kernel)

private theorem ok_b1110110110 : Impossible board_b1110110110 :=
  fork 26 ok_b11101101100 ok_b11101101101

private theorem ok_b111011011 : Impossible board_b111011011 :=
  fork 41 ok_b1110110110 ok_b1110110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111011010 : Impossible board_b111011010 :=
  kernelLeaf board_b111011010 #[0x3628471f1c2d5336171b241b3d2b312a293447614e684e12362a1427292f3a56, 0x141c276410576454471c2d53312d61716a2861236a232d0e5a31270d2f1a404e, 0x333151255e51231f2f57547a6a6a22166a5a2d4e36686c12314f313157282d5a, 0x6a4b3d5e305a30675e2f5e555a6a635a4f282f4e3a2755491c541f2222270527, 0x3050502736742f4e362f523a5c6a5463575a505754500c6e6a303147485e2a29, 0x3122275317285d162d53213629764f6a5e3027302f3d2723273d0c3d27092274, 0x2f15295a5b3d15295e303a3031335228493374723317543352284e2254521a3d, 0x30555a5e786a30222969606c314053293115305e5a2a29272a2f2751] (by decide +kernel)

private theorem ok_b11101101 : Impossible board_b11101101 :=
  fork 32 ok_b111011010 ok_b111011011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1110110011 : Impossible board_b1110110011 :=
  kernelLeaf board_b1110110011 #[0x1c2e394d232f533d2d365527225055145a2258364d28505d57506a2254334e68, 0x2f4b572e4d69634f5a502d2f4b543a182e4d3d225f2e2716212d2e775a291b2d, 0x487a6a34532b2f212749332d16304f39505a2e2d485d222d495a54362d2d242b, 0x675e2d22300f5e5a1c270c13215e575e5422334e504f3d3430275015480c211c, 0x4f2f536a4927702e5a2b292d514b3d4f2f29535a472e5e3a402e235e2e275415, 0x2233364e513430275b5b516a2b591659274f392729304d5a2e63542b292d4d63, 0x3d22304c5a286a2254335122121b282f47065a3d51581a1c2d2d271f28585871, 0x305a4c27584d28471a2d13275e49585a333654121b11281a5d4015540e001a2d, 0x2d2d0d3a5a53514851] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1110110010 : Impossible board_b1110110010 :=
  kernelLeaf board_b1110110010 #[0x131d5115641c4e3d5458481a2d2d5e513d22550c22284e2f0c6a582228543336, 0x111e1c220c57133d556327334e2a191c14515b14511f474e5a1a2f5f4e22131c, 0x2e6d4c27062813702d131b0c0e5e3d22302b48573d5515286654225e5e494d5a, 0x1d5033685134595a4c2e1b2827551f402e281a63132e275529252d2e401b2323, 0x4c2b59343027542d515054404d514b2f3a27574d5a4b5e] (by decide +kernel)

private theorem ok_b111011001 : Impossible board_b111011001 :=
  fork 98 ok_b1110110010 ok_b1110110011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111011000 : Impossible board_b111011000 :=
  kernelLeaf board_b111011000 #[0x345168142f40331854027a121b28535e544e1b40534f54405a4e8148131c2d36, 0x592e3d15291c622733512a15154e3d4d15124e28334e4d4e33610d40611c4d67, 0x636d4754292b1d3464622b4c2e2d4c4b111c2b541d4e2e5d1d2b544b1a5a4c2e, 0x5b2e150a7a5429181b282d391b4f14542f4d1b0e5e51291340544f282351634d, 0x14294f2d4d404b475a274d216816764f54614f5d402f4b4b15] (by decide +kernel)

private theorem ok_b11101100 : Impossible board_b11101100 :=
  fork 86 ok_b111011000 ok_b111011001

private theorem ok_b1110110 : Impossible board_b1110110 :=
  fork 38 ok_b11101100 ok_b11101101

private theorem ok_b111011 : Impossible board_b111011 :=
  fork 65 ok_b1110110 ok_b1110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1110101111 : Impossible board_b1110101111 :=
  kernelLeaf board_b1110101111 #[0x2b2b28362f5247455836452b4d48551f62532a2f1f39244d602728532e17560e, 0x2b36244516632a212f2f28182b2e2f2a2931285a2b24192f31282f344e1e2451, 0x213934241e312e2d4c45362b232e1d242e2e62271c4e5131511e1e545115452b, 0x1952271c16242d2d1624312a212a1e1531472d646f4c45362b362d4e1c2d362a, 0x494e34522a482a301e2921242152223115305a2a223139522e172d553158282e, 0x22162d2e5c2e3134222e3041272e3722242a22521c2e314e341d1c522e102e63, 0x24514e2f6329301e531c4963395a455e624545291e2b1d5718522e314f4e1e30, 0x452b562a452727291e1e23234f4f5a536257304d4e13456253452b5a6a1c1e41, 0x5b29302f493016697a60515851607a721b341d6f6868757c866a125e5a51344f, 0x30] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1110101110 : Impossible board_b1110101110 :=
  kernelLeaf board_b1110101110 #[0x27251c1045151e460a1624212f36362e2e1e3452212358545136502e1d2b2a56, 0x522734312f273125581c3931520e6e48465e2f5146685836475346245d214531, 0x3653272d2b2529094e0a252f1d2b452f1f184d2f53172f2b242e5a2b27462b2e, 0x5227371e1731505e705250024e2e225c36271d462b2e1f505d4e2e1e4e2e2412, 0x5d514136705e7a4d30546e2e1e52314e24514518232d36392b4639494d781718, 0x65251d5d6a5b5170634670651f2e3016292b36235d295327296c5e6a236f306a, 0x4e517a2e61664e7430677b5d6e7654162b362f4f2b46364e2e245a39250d275f, 0x2f39414d4f1c60522e462e5016151f2f2b36212449542e1e4f2b4612271d361f, 0x4f1d2b1d6e2f5a296a5e4f6a572b4d5b636a5a39495e5b6a457a305e1e31225b, 0x2a5b5b2f51170f554e1c232a3013514e4f2a2f5e3117224e233013514e53241f, 0x341d3422496031225b30471630664f344f3051585e5a] (by decide +kernel)

private theorem ok_b111010111 : Impossible board_b111010111 :=
  fork 20 ok_b1110101110 ok_b1110101111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111010110 : Impossible board_b111010110 :=
  kernelLeaf board_b111010110 #[0x2446392f63514d46592f45635251362748584552343146531c2f52485d2a2156, 0x551f2f2f4572515062536e51482a58313650682e4e1c29341e1c4e53372d5d46, 0x2339274c0a1036390c252e4e174c46404f46550f240f24372d242d362f453152, 0x4c41274c2d22304e622f24236a680c2e2e2f31282e271e2f2a1f2f2425242f0c, 0x1750492d3141255436102e1b5551105b1f291e1f27545b1b27574123672e1b67, 0x1b256800296a25120d650a2555376b700a2217682240121846170c27175b501c, 0x5d39492e5249531d58512a2e252e492e49475436282d531c2d29342146514829, 0x6417542e3030632f4849292130101e512a39414d17395051454d306a1d5d3755, 0x2e4e2d48283130406e0e494122394d51224141494c25615d0d23103073596753, 0x2d304960292a6066535a53554d60492e52253122472d22305b5b4d6331574167, 0x406158166647673022492e] (by decide +kernel)

private theorem ok_b11101011 : Impossible board_b11101011 :=
  fork 26 ok_b111010110 ok_b111010111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11101010 : Impossible board_b11101010 :=
  kernelLeaf board_b11101010 #[0x51522a2f2a49542a4e2d4737284721211f2f232a47542864471c21482d513662, 0x29534c1e27102b1e4e2b721e31224628272b2b341e30484049494829302b6e59, 0x46682434472b5234524e1e271f5230313146282227462546242f2122152d365c, 0x534f482a49545e222d4e36271f2b291a1a54392d4d47125a282d4736294f472a, 0x635b30342f125e271f5e4e30224960294f402f1d2f2b49305e5a2a51304f] (by decide +kernel)

private theorem ok_b1110101 : Impossible board_b1110101 :=
  fork 32 ok_b11101010 ok_b11101011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111010011 : Impossible board_b111010011 :=
  kernelLeaf board_b111010011 #[0x2e2f517051345a0e292e7049365e224e2e2e374e2e2d37475a2e2e2f4f6a465c, 0x1a4548294f4c2e4659682f675d4970705149257b5d6a5a5e2b2d0e5a28543634, 0x4e3027342a2d366b58514e30545a344e222d2836234d48235d6a542e542b4c36, 0x1a530c1f2f212f215d302d4f4e18212f36251f2f212f215d4f4e212f36257d2e, 0x485b515a5b735a554e5d394f5d2f4e5b5a484e5a4e5d2f4e5b5a48392e2d4f74, 0x245f4f5f77585a4e4c4e2a2823302f4e2f4e464e6a2e485b36491a576a4c5f48, 0x4c252d142114401f301a402d4d306a5d77725f582248414830697c495f4c3016, 0x6a5448455e2e4d25374c485845594f542f544f39465d5434377258584d375851, 0x5a392d305a542e220c5a5b66495f5a58585f1c585e1a342d0e285a542d5e4836, 0x6a583434484130] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111010010 : Impossible board_b111010010 :=
  kernelLeaf board_b111010010 #[0x294d5958454c2f46305e5115071a39151a182f4e274e3915281d17554e39252e, 0xc1234211f535b55655e485c554151292f4e4c39284c4e29344712392d455f4e, 0x534c534c1a41270c39220c0c1a4767192339752117306b5b3451514c1a1e411e, 0x5e2d7253691577536f585158492b28285a1747543647492b12372047362d0a34, 0x481a2b221c] (by decide +kernel)

private theorem ok_b11101001 : Impossible board_b11101001 :=
  fork 98 ok_b111010010 ok_b111010011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11101000 : Impossible board_b11101000 :=
  kernelLeaf board_b11101000 #[0x614d452b656b5848644e51622e25214c48455162634c4551584867404d5d592f, 0x514e48534e545d6c4e554554516b455b1c2e6840554e5a5b4c2d5a4c411a5d40, 0x51482a1e392b1f231b21280e13554e4751154162594e0e395373514829344551, 0xb252d3751481c1a25485d282d4f1c152a514c45252b364c1b2740234d4f4d54, 0x4618294f48461a284f4f68674f59514f282e4d294d5d67476a47404d4c28] (by decide +kernel)

private theorem ok_b1110100 : Impossible board_b1110100 :=
  fork 86 ok_b11101000 ok_b11101001

private theorem ok_b111010 : Impossible board_b111010 :=
  fork 38 ok_b1110100 ok_b1110101

private theorem ok_b11101 : Impossible board_b11101 :=
  fork 59 ok_b111010 ok_b111011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111001111 : Impossible board_b111001111 :=
  kernelLeaf board_b111001111 #[0x574f1a5d5246645d2f122e4e3151542b1f2151482e4e5d52211f52514536563b, 0x2e2e25171a2d4e26374525250a12191a262d461a2b46511f212f242e2e524f5d, 0x4624374e37192d22295e2b521b29375249315d52466451684e2e5c26284f5d4e, 0x455d5449702e5259463736452725364521233730365245360a2f21515d514e4e, 0x73222952486054366462646e314e51535436694f463145223130291b1e251718, 0x465d6c521b314e2e54495d2152482d222d552e394e5b522e542a622e52492d2d, 0x2d7452654e292b4f5d492526645768652b626c57686a4e2e3031301f1e301b46, 0x111d240a074e0d4e5e212e18313621554e6024466049521f1e31142d22461b39, 0x1056091f2d3651513d461f2d4e302a465451461306280e281f4e2d3a461a3f1e, 0x262b48512e4856465121] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111001110 : Impossible board_b111001110 :=
  kernelLeaf board_b111001110 #[0x5203191e1b12573165333652286733522236305268537730361f362e6223514e, 0x5d4926711d365d57495d575262291b5530572268071b220d5731626a40571b29, 0x33312e2b52483a3031365723625d1e141e165723652e1455680e201d31575c28, 0x524f3931536255165e362e33622d3155330d36536a3653662a6e493322366221, 0x3354625f2b6f22335f2b3129524b3d5e5e1a21301f2f3d3a54532d533a312e2b, 0x363a542231363a272e2e62315d6f542233522f26185e301f2f3a54312b5d395f, 0x6219] (by decide +kernel)

private theorem ok_b11100111 : Impossible board_b11100111 :=
  fork 65 ok_b111001110 ok_b111001111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11100110 : Impossible board_b11100110 :=
  kernelLeaf board_b11100110 #[0x20732f0f65591b37251a3a140d1468182b0c186833212f373621182f302d5146, 0x4e5c3068542d5d3d2d3d571a36302d5d531933211a4e5961335e2f3059593071, 0x2e1a2d3021685d1b6a5e5d2d2d30333923785d49675f82335d5d636b6a6e2254, 0x265830223b58492e305e395b2d372e392856495d2e686a2f2526332868697349, 0x36576a57495330393a37302822365e2d362857617268645d685c536953643728, 0x516c5b2a5653486d0e741853165e36365e5d512d2e392a53565461535e513758, 0x295137532f515b565536372e2a56] (by decide +kernel)

private theorem ok_b1110011 : Impossible board_b1110011 :=
  fork 71 ok_b11100110 ok_b11100111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111001011 : Impossible board_b111001011 :=
  kernelLeaf board_b111001011 #[0x5d6a261d331d331f253b2e212f3737212f731f251d532a75161f2f362d3a5654, 0x28491d731d6a2e622f1a263d5c2f662f1f2651251f1d1d37492e6a3a62376f61, 0x68725156593337211a685d512f1f6f5164246c375b5d565c4558465358251a33, 0x1a311d21335d68293a6369334b7668674759535d5c5933556c1f266868623662, 0x1b12282d375d2d2f3a562f3a31331833286c3a372651212f3a4b2a1f20370f21, 0x622f2924144b6c5c06372f6621316168657372515c076158785d3726211a1a51, 0x251a] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111001010 : Impossible board_b111001010 :=
  kernelLeaf board_b111001010 #[0x1d12186821222222333620286a226c5d3b5b5361685d51466c5b533126564062, 0x29610623532f36562d3a375c5158334172335d67546a2268336c1e3b515c2e55, 0x72542d565f6f562878545d586a1a2e1d25184b1f0d2e636c211f2f28213f3730, 0x26545c36612e5821283326565f5464515d2e6a554654556d365636006564402e, 0x16305c5d72636a403363535f6a6540535d644663305c1a5b665c306722743325, 0x58543a1a76632f633a6c643b634b695836725c6453546663645b6a6553645d2f, 0x65636f7837267c5b402861641a2e1b2d37542d1a63250e0e092d211f2f3a587a, 0x33241d1e61642e1636206a655d6b61546a] (by decide +kernel)

private theorem ok_b11100101 : Impossible board_b11100101 :=
  fork 78 ok_b111001010 ok_b111001011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111001001 : Impossible board_b111001001 :=
  kernelLeaf board_b111001001 #[0x335d106c3355190f2230607333221073706770734e4654736f7a461a765c6362, 0x6965516f5c6d362e3b735d4959511d51303d5f51805459335d5171717b5b3022, 0x735d5f735f6960555455495f604e4b33556c5b55465b6c53537473695b304e65, 0x452e5336212d3d292e2f295b4e51373a7437224e295d4045676a64337a6a6f33, 0x275d366054335d4953204e171e5d1f1e461a2422460a514e496d310c5d4e334e, 0x65645d377336631b7273656f513a4e6022334e1e307a2e36275d5c335b452436, 0x6f636a5d304e22204e3a726065761a5133455d586c4e5d2e0d3754633349455d, 0x226c60720e60462e7e77334954497e6a293a22304e37182e72606f67827d6d71, 0x3669587e1e1e466328362824221e7e6c49331936762e103a80205f5169586533, 0x3336247e6c331d1b10304e1e18213637102e72122e5d455d6f33216a02603149, 0x30767b3a6f657245457d5d372e496a6036675821307e314636492233101e1b22, 0x737e11336d333676182e5d6f51737d6d6379497d634977692e22276d734e6933, 0x6377696065632e29] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b111001000 : Impossible board_b111001000 :=
  kernelLeaf board_b111001000 #[0x2d0c1f6571596640372f583a2831732f5d2931665d2f45582e36606b64315321, 0x66735d5c1b2f092f1a1d182f1f2d28] (by decide +kernel)

private theorem ok_b11100100 : Impossible board_b11100100 :=
  fork 86 ok_b111001000 ok_b111001001

private theorem ok_b1110010 : Impossible board_b1110010 :=
  fork 82 ok_b11100100 ok_b11100101

private theorem ok_b111001 : Impossible board_b111001 :=
  fork 77 ok_b1110010 ok_b1110011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1110001 : Impossible board_b1110001 :=
  kernelLeaf board_b1110001 #[0x1a6a20335b51617857206a493f4d1b17513067583b614d5b3f51214d4b31224e, 0x1a51755e211b211d1321131d1b581a293f67666a0c556229725e5f7229293f78, 0x6a292d495b301b2d2e671a4b372965494d5c13576f554d662d060f0d0d13261d, 0x2166765b31485f272161375b2f7a4d57625b7c5b315478676a1a2e47162b1a2d, 0x1f5831401e2b2714141b3923141e23785c5e2933073921370d332f6a1257625c, 0x21455333234b595c37236c635c4b4d6355536062492e523924375e5b1a663740, 0x211b1b162b243117494f575c63601e5c4b65605e3322391b3945626c60483931, 0x314924302925244917374d5b301f65295e53174d3d30211730601a0914451e29, 0x313125214b373f162a33622b2e5656294924192d19496c2416450a2124454029, 0x497a333954391221496a515b376b31224951332b5c4b6237246637406345651a, 0x1b1d07335b493131] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1110000 : Impossible board_b1110000 :=
  kernelLeaf board_b1110000 #[0x49495b624b4b5218393d3d5b07472113391b0e1a493d3d5b1b3d560e2316272e, 0x25251d251f292b2625391b1b2f1d471b3d4739291a49540e00391b1821544770, 0x3063614d54511a4b5b5b545b4b764d4b4d4d54475e511f1827544f51304d3d2f, 0x4e511d126029491d1a524d374e5419264f392d21512151104d4e2d257f4d564d, 0x4747271d4d51251f4d395147131a1d4e2729376a16214f4d291f115c5127161a, 0x273f25765763476e6a161a39391a294e2b41274f3d4e295e276a621b51251a25, 0x593d] (by decide +kernel)

private theorem ok_b111000 : Impossible board_b111000 :=
  fork 58 ok_b1110000 ok_b1110001

private theorem ok_b11100 : Impossible board_b11100 :=
  fork 80 ok_b111000 ok_b111001

private theorem ok_b1110 : Impossible board_b1110 :=
  fork 44 ok_b11100 ok_b11101

private theorem ok_b111 : Impossible board_b111 :=
  fork 60 ok_b1110 ok_b1111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1101111111 : Impossible board_b1101111111 :=
  kernelLeaf board_b1101111111 #[0x284f0c4b1b56154e0c3b67283b6c56290e224b5e242316245a1a13281d2a3539, 0x625e534e12272c2a236557473b614f564e562a416a4f7362605d694f5e4e5317, 0x1d2613471f5826291b4f231b4b352a472d3d2d27273b5a5761655847616e5d4f, 0x535e4e452a534b241d4d4527374d2f1e101e261e4d194e151d2f4e5b17243b50, 0x561b2a2f1f] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11011111101 : Impossible board_b11011111101 :=
  kernelLeaf board_b11011111101 #[0x1a1c5f511c5e39525322512425371b3d4d2837222709511b171c28253d415c30, 0x1c726e4d582d231851062b1523180a4f2223234f2422240e245f1c3d150a155f, 0x2c23685222100e5a25244d55706817680a521c24512f24701c6541655e241c20, 0x3b6e2a371012252d0f3b2a10410e1f2a2820331c582c2741652810253d2c623d, 0x180e1f2851330e513939641a1c200e1f411f39564d4d253b396f613f5556681b, 0x1b766865573163516e51725c4d3139313d4f653d231b61615c23686337561b18, 0x1b] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b110111111001 : Impossible board_b110111111001 :=
  kernelLeaf board_b110111111001 #[0x252b4d305764534715351f473b69584d5a1d151d1f4d1b31314b156b5c56283d, 0x4e4d35604f585a1c51593b524705224e3b572457606547251f3b5a596547691c, 0x5d64534e5d6e574b2a5761575f5f685d70106c4b58562b5d2b595d2b5f2d474d, 0x1b141b10682a1733135810231947531d233126244b6453535d2d69586457476b, 0x252f59692b1c2b6b5c5c52222b593015453b5776602a58564d2b574b5e2c3314, 0x25702d0c5649255b522b3526304d10562856495628266f1e0c28233024266849, 0x2423566122233035574d1d1e231c534e5c691c222d51305a166c565922595f56, 0xd24195f1959105d26696d2765495a4d564935584d222d564927244d4927285a, 0x255153231952521919735265565d2630301e6a316a605869255e51581030581e, 0x285f5d734e450f0a1d26172c2f2758192a2757151d3149563157261c5e5b6e5e, 0x31315f5a4e2a262826581c5d0c103110241b] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b110111111000 : Impossible board_b110111111000 :=
  kernelLeaf board_b110111111000 #[0x23371910174e641a25475753172a35241f65235c4923571d5712231f5b352856, 0x735957175d5217605c0a25736872237a30642c232d16601c642d23576e5e5323, 0x235e5d57685b725d5a5a616457654e475d5768646128640f302d1a25155c5c69, 0x24301f57695e1f28305a593b6b5a5260356c355e68596035355a6557282a1f5a, 0x171d640d150e281f5a17171f2325301b2c5e30255a252d301551280a] (by decide +kernel)

private theorem ok_b11011111100 : Impossible board_b11011111100 :=
  fork 57 ok_b110111111000 ok_b110111111001

private theorem ok_b1101111110 : Impossible board_b1101111110 :=
  fork 76 ok_b11011111100 ok_b11011111101

private theorem ok_b110111111 : Impossible board_b110111111 :=
  fork 54 ok_b1101111110 ok_b1101111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1101111101 : Impossible board_b1101111101 :=
  kernelLeaf board_b1101111101 #[0x273f2328121b3d53392c141b244f611e1b454560243d105345292f4d2d5c344e, 0x4723555b7669290c291327280c226e53554b2d233d393f4f3b5660293b272f53, 0x64522c4d5c305e39271b5a5e2d2956635b284724452d4d7427182d3b5664514f, 0x2c691c412f691f192d535a4f6013245b5b1524076b3d3b532f51525145233b58, 0x45642c6e53605f272d3d4f5151395f2d2c5f3d2d45090e2d656b515e272d2229, 0x701c5f414f5a585a653b476155455561557c5269695d5f5e7c247a2d45451777, 0x1a12194d1a11195207242d5c2c7b745141395b47512c5b245e513b4d192d585a, 0x293b605d45245b285b45206e1a533f271f1f10143f76601a391d1c274d275125, 0x4127234f1b4739686e1a4f565e4d662d786e6566514d3f4545535e4d29685639, 0x51473b514d66491e51453b51233b452c4d5c453d452d395325512c3947603033, 0x4f56414f664f6039183956145d70706c600a244d634545605c2c2c1a16535739] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1101111100 : Impossible board_b1101111100 :=
  kernelLeaf board_b1101111100 #[0x1f2c204f60521c1f7472694d513d1c0e634d0c493d0a1b273d220c1a4e5c5e30, 0x4e20235b6b4e27524e1f495b495b4e532259221a525b3d4b5120652c15330c25, 0x2974225c4f2b3b761e39472b292d63515c5c645c745b632722272d1f4d2b3d3b, 0x272c4e4f5727294d121f294f593f682c5b2c3d4b5c6227774d5951293b4d5c6a, 0x234d2920290c6023232068391b1a491f4b2d2e1828691a2d4b5b51491d1f293f, 0x3d1e345a1f271c042d1e0c2d74720e6327223333121d49282b3b393325632720, 0x27331c18164f2e5c281c5c123f18201c271d1c5e26222339101f2d39264f2d22, 0x51393d2c3f4f1c2039232d351b2c4b5c574f22595b5e4b341e395c2e] (by decide +kernel)

private theorem ok_b110111110 : Impossible board_b110111110 :=
  fork 80 ok_b1101111100 ok_b1101111101

private theorem ok_b11011111 : Impossible board_b11011111 :=
  fork 58 ok_b110111110 ok_b110111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11011110111 : Impossible board_b11011110111 :=
  kernelLeaf board_b11011110111 #[0x723f24353914391b3f4d3a23313f511f656f1b3f273a4b18565d514d554e6034, 0x6e3510473f24594f415118594d3b6255393f594f185c1c4b351c1f3f2310394f, 0x5174666c2456272e18625770532f4e4b3f31454d6c2d2945535b4e5c1f411f61, 0x685351365f3a57365141243b4171515e4d41352d514d78372a474e582c4d514d, 0x4b3d5168661f3d33313f6c2a634d374d4b375e742b4d173d1710165e78625e66, 0x3f1f512d33173f664d1c373f4b231f53684b3d3d513f56183f24514b4d4b596e, 0x4b4b1f534d4b3d454d333657363b674157653b574d3a2945535b4e4b2d33174b, 0xe766c365c5127364e4139566351473952663960745165594d3b24524b3f186c, 0x39512a63315d3b6c532a5d3b621723167453361c574152] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11011110110 : Impossible board_b11011110110 :=
  kernelLeaf board_b11011110110 #[0x296f33661b753f45061b3f3a2d4d130f221d51453b2417513f372d3a1a672c4e, 0x4d5347134d4d5c60452f37176d3f3179555e5315453d4d531c2d5c5560453b24, 0x272360396417472d3d3925393a203f315f55605c3d3945285345174533294533, 0x394f4f2f784533603f24645b13121d10262a2326451c3b603b2d263d27273934, 0x335e5166396737806a277237274564396c650e1c29274564592951456b174576, 0x51265c3d455328395c65575f4552636c373329593d637674582f102c6459592c, 0x39391f354519331c28232d1f34291d1a370929375166592c3f2a1c396c391d1c, 0x393f1b56231d4572561d456c1c3d4f3935453362456a763f5c28453756595158, 0x27273a3d2b765b4f5c23] (by decide +kernel)

private theorem ok_b1101111011 : Impossible board_b1101111011 :=
  fork 80 ok_b11011110110 ok_b11011110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1101111010 : Impossible board_b1101111010 :=
  kernelLeaf board_b1101111010 #[0x57534d255e515758533728574e4739654f533545645c0c4527252d1c39573b36, 0x685d625d51685e5e3b5e315d3d2d53414e5d2b57474d315d1f580f245e515c28, 0x602a573d5d574f3964205e231020312d3d53533d272d2d2757652367135c393b, 0x641c12202b3d391d1d2823374537375d564b353939315035373d456c394f3568, 0x1c4b27453b703d26604b451c586458] (by decide +kernel)

private theorem ok_b110111101 : Impossible board_b110111101 :=
  fork 76 ok_b1101111010 ok_b1101111011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1101111001 : Impossible board_b1101111001 :=
  kernelLeaf board_b1101111001 #[0x6a293d5957392c351f553533633d452f3d2c59456c593d6b45333d2c66513f50, 0x1c24222f17453d18241c232625453955332f1772593d223d6b591c665f3d453a, 0x2459513557594537745b3351591753512c192c645f250d5f252418241c292524, 0xb1511374d254e16694e1c156324514136585e585e554e335e222f25222d512c, 0x411068514e513d41634b514b725125373f3575592c4c65695e3d6b6651531b25, 0xe65663f354b7259515153243a5e53514137273d1c1b4b4d51534e4e4151534e, 0x5e517a4f5337415d536c645e534f5359726251510a25374d372f412339206975, 0x16784d4557726436575759745753593653271c57226751531678365353166c6e, 0x351c294d412c1b1f2c57072d163959537c7239391f1f1c1045514d5153395141, 0x725937252436392465535772593d6e536f41532753256f191b37531f16785307, 0x51593d5737166c36764d45203d5357727a51575745] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1101111000 : Impossible board_b1101111000 :=
  kernelLeaf board_b1101111000 #[0x5759456550514e3d2559514e25245e5e59574f5e4e4e0c511411372024362741, 0x572225221c3a59453725241c5b5e3f59223d2f3f245e3f593359353f4f243917, 0x512459112522522419356d5b515e58517759715e593358741f6225374d515b45, 0x4f3f4f1f5d4e5137524e363d6e574c52520a231f24222d36594f3947] (by decide +kernel)

private theorem ok_b110111100 : Impossible board_b110111100 :=
  fork 96 ok_b1101111000 ok_b1101111001

private theorem ok_b11011110 : Impossible board_b11011110 :=
  fork 48 ok_b110111100 ok_b110111101

private theorem ok_b1101111 : Impossible board_b1101111 :=
  fork 70 ok_b11011110 ok_b11011111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11011101111 : Impossible board_b11011101111 :=
  kernelLeaf board_b11011101111 #[0x5b3f35613a244d223356185c5e5b57566c222a391c294b3129725c12284e582c, 0x604b37232d2d351f255e745d6e5b6e65393311273a18673f1f376e2a371c3669, 0x6c52573d563f5d63693556576e2a411f24333736524d2a596b5e594d373d4d61, 0x56725e4d4d56673523390f603f602a33376c557b65606e393936537018763963, 0x574e24593d551c4f693d5b766c5956224d59495f49596e565d6e73614d7c5f73, 0x24234557393d35564f464d1d283f3639286645605f3a372864566c6c672e5b5e, 0x1f2835561c6a2e3f1f291835601e392e3a55563a7820664d523f3f4f82563a60, 0x1f603f575311110a254f755d653d6a374141333d725c2a173318250a1c241b36, 0x565a124e24334b1f644e181b3d33186033351d1f3d3f3b2a4b5b2515411f3335, 0x3a4e3d59181b46353d4e243f5c5a3727566f145a18] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b110111011101 : Impossible board_b110111011101 :=
  kernelLeaf board_b110111011101 #[0x594e283952246510264f4b78523f6c6a333a7665635a7039393a2f24284e4758, 0x4e373f493552374e575b4f394e4f591355572855394e6c134e5c22526f2c104f, 0x284e3a1f4e1f13572539652955135e5c223f1f2c39355d3f244d3f371f353974, 0x225b3341252d3a3a4e3b2d413f35352d2d4e3a354e3b5d52533f1f521f4e3a41, 0x5b29554f3f5569524d52523f6a575252374d4f3f655528574b57666a25413735, 0x3f3f3555573b3b272d3a353b523f4e3a1f4f1b2c1c131f39575255593a52613a] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b110111011100 : Impossible board_b110111011100 :=
  kernelLeaf board_b110111011100 #[0x5f3923524b530a6e584e3a1f2328394f695822232d133a4e5a45224e584d3b24, 0x1f391f3959465745295e452d3f7f5e691339535d395e45395f52592539232d57, 0xe282d1b1f22353f2d2d4f5245462513200625174f4f5f6d6c57655f064f5d52, 0x131f393f1f120e1e5745593f4f0e457c535f39534e1c3a292835293352520636, 0x141f103f39222c252539224d661e4f4e5c331c2c1f350c2c4f571c0a5e52584f, 0x37354e2507102a1c393a2d3b283f355b1f2227191b252a283f2846373f584d6c, 0x41572d58414e3a1c2c2d531515232d2539] (by decide +kernel)

private theorem ok_b11011101110 : Impossible board_b11011101110 :=
  fork 96 ok_b110111011100 ok_b110111011101

private theorem ok_b1101110111 : Impossible board_b1101110111 :=
  fork 48 ok_b11011101110 ok_b11011101111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1101110110 : Impossible board_b1101110110 :=
  kernelLeaf board_b1101110110 #[0x29233d2d1c2d221839291f394b1f093d2a742d3b4f65134f4f1c3a2d3d244e58, 0x14233d2d613918271b3d1d1439353d186c70146e2a5d221f144b396c4b065765, 0x260d1c296356723d2a3d69565d5d1f564b722a171c243d5a393d393d200a204d, 0x173d5a535b2f6b3d81175b6b3d28655a293b5b2f3d534e4564233a3d5a243a27, 0x70202a232a4f1f797018293d392a2323781524203d2d4e3a3a5e495a55663924, 0x5629491866491220765a39246c2a5c5353595623533d5a293735631b3d5a535a, 0x3d5a2635185639233d56123d182d4e354b2d4e3d554e3a45575d5529234b5d7c, 0x393d373d2d1845] (by decide +kernel)

private theorem ok_b110111011 : Impossible board_b110111011 :=
  fork 52 ok_b1101110110 ok_b1101110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1101110101 : Impossible board_b1101110101 :=
  kernelLeaf board_b1101110101 #[0x191b26282959646c52632f2230666a5e60452f37295a29291e666a455949333f, 0x176d4f536459351d1c1f3923301c1c593a60295857285b221f1b3a2c2b762422, 0x590d372a1c3a302a223924300c5e4b0c221c0c172437303a28652a535e64655e, 0x5e534e3a3060392d372860593553301f6d594f2a2859644b76595b35244e3063, 0x4e2c691c592e6c2d7e521c25522e532423295e1c1c574625080a130a1c181f57, 0x2e456c305c3366576a594e252e4e1c334e273a3a595345615365525778655e53, 0x24555c45662a6c5824131f6c6a3063575225352a5e5a4b6157295e5a2e2e3333, 0x201e293033354b2c332f5c645b4964645b2f554e3a5e5a5e652e2a33335f5c65, 0x5353602e452926451c344728452c1c294b2a254b47302045292c2a2c295b3337, 0x6455355a] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1101110100 : Impossible board_b1101110100 :=
  kernelLeaf board_b1101110100 #[0x596045535a312e55644e5360593f796169395a3365725c6f72645b614b4e5824, 0x295b160c1b283f22452229151753263546134e2d1f2f59223f45295b11223f2c, 0x4e252d31252d234e2023601e452c392b225b4e1664591e2c224f29294b5c185a, 0x5a5e2c60584b22531e204e5b4b4e33261f1b29231b26] (by decide +kernel)

private theorem ok_b110111010 : Impossible board_b110111010 :=
  fork 61 ok_b1101110100 ok_b1101110101

private theorem ok_b11011101 : Impossible board_b11011101 :=
  fork 80 ok_b110111010 ok_b110111011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11011100 : Impossible board_b11011100 :=
  kernelLeaf board_b11011100 #[0x22292357251e235d522223605d5925573056525d23574939266c5f26565d3d45, 0x261952251e256719571069576c15305a566556635963235f101557493767525d, 0x581c6560571f6c575e595830465d39615a5e5b5225576e2849561c231925176a, 0x5323585c572360536b474959725c5753415772592358121c69471d1f25472d2a, 0x353158241920491e25301f2a367a595e36594930523549251f30595822526860, 0x6965366c1f3559686336565e531f693635495752565a586564312e5317351030, 0x6a25363572355665651c1c2a6761607d5e6915336c301d251d5e25501c175623, 0x1f1f586135251f5c3669816e601710581c525c36123025501c60675a1f603070, 0x306b6758506735592a5636494f6853306d60132d1c24351f36533025685e5268, 0x4d583726592b5d1b472d1c4d4f67644f695d283d5b691928615f493757362a5c, 0x49284f7216585f60594d6533] (by decide +kernel)

private theorem ok_b1101110 : Impossible board_b1101110 :=
  fork 76 ok_b11011100 ok_b11011101

private theorem ok_b110111 : Impossible board_b110111 :=
  fork 74 ok_b1101110 ok_b1101111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b110110111011 : Impossible board_b110110111011 :=
  kernelLeaf board_b110110111011 #[0x66185765475a4d5d532b36106e536d5a2541362b533b6270255a472b3b301c64, 0x1b1d531b275a243113652f3b70182e36122d251a26746d56233b29743d615756, 0x4f3d4d4f3d535c24565a0d5e53202f3453245e3d57273d1b1d3d41575e296353, 0x344156762c56533f4f51223d535e3a5c2d1a633f6327293b292947702329232d, 0x613d5370182e223d1272786d565f635f744d2e7818535e5b4d6d611b623d5370, 0x1551413d24534d5e4157415e313d534f517d6c616151564f72515e5e41576731, 0x535e22625b666d625e47345341552f2e62701862703a53786257745e20516930, 0x57532e3d31361c5541] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b110110111010 : Impossible board_b110110111010 :=
  kernelLeaf board_b110110111010 #[0x6539552924234f3d53643d235e393d572f5e4f3d696f5e5d705a473d3d3f563a, 0xa177022072447134f1d245322313d3f4f1d1d2431790f3f3127632f182e221c, 0xc1862412d5a2d3d573d2d1847292422231c3b1a5524313d66761f2f1c5e271d, 0xc36153156204b41363b26577025650241512f470b3131476608245e3d652615, 0x3d33251a303b65292347313157633d2418700f2d255a5f410a47742b1d253d26] (by decide +kernel)

private theorem ok_b11011011101 : Impossible board_b11011011101 :=
  fork 104 ok_b110110111010 ok_b110110111011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11011011100 : Impossible board_b11011011100 :=
  kernelLeaf board_b11011011100 #[0x646b727c6c63106372634f1b3b1c66263b660a1c0a720a764f240a1c1e183456, 0x663d314d5c1a786e61786e5d636172104b2c2d2c2529142c1f1a271a1f1a2c18, 0x241c6e3b616e5d1c7a653b2d2d3b1c68475d5b3b4d6e6e65575d7368475d5b4d, 0x6e7036292f65415c5d726f725b3b4d2c3b2d2f3d1c23683b5d234f6e4724250d, 0x4f6625474b30254f3d7a783d314d3b5c36515f293a515f31275d] (by decide +kernel)

private theorem ok_b1101101110 : Impossible board_b1101101110 :=
  fork 88 ok_b11011011100 ok_b11011011101

private theorem ok_b110110111 : Impossible board_b110110111 :=
  forced 78 (by decide +kernel) ok_b1101101110

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11011011011 : Impossible board_b11011011011 :=
  kernelLeaf board_b11011011011 #[0x73202d6b5b12195d4f23167c58683b3961232d5957291e3b311f6423516e535e, 0x1664576b174f772371655d726b607e646b7731816b77311c2434086f5f6c313d, 0x34315859412b594f5d59496e68572b27572358475764276b60516b6b64607760, 0x5b594e694b6b5b514b27273d315b74114f4f586b652b5b222b1d512526251c6e, 0x4f47595b65616a655b657b0d58271c3625633359494d6e5a4945582b30515869, 0x3d722f020c225930744f514f59584f5851655159413b3059335749584e695923, 0x3658585f64266d4f2f5d594f587f221626594f58474d2b224d5d171c4e59205f, 0x68644f16594f516567304f59413b49595758705d706970266759696b4f471f0e, 0x7065415d234f493b4757205f365753315b6e4757122b2d23532d57253d310a20, 0x4f] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11011011010 : Impossible board_b11011011010 :=
  kernelLeaf board_b11011011010 #[0x2779595134602d315d5375591e6004103b5a271e175a2b141e513431535e2a58, 0x3059222b343b4151395f646f305e5b5b5960682d263b672f5e644175607f5951, 0x5d5f3b495d395b3b475d3033252230264d263b1f22304d264b5d] (by decide +kernel)

private theorem ok_b1101101101 : Impossible board_b1101101101 :=
  fork 98 ok_b11011011010 ok_b11011011011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1101101100 : Impossible board_b1101101100 :=
  kernelLeaf board_b1101101100 #[0x14311c2b27173d2d311c4e206831345e756c594b3627682d676c4d2b34315d58, 0x272b2b7c5b53672b6c7257612d535b163d4b624b5d75615d53161f2a1d] (by decide +kernel)

private theorem ok_b110110110 : Impossible board_b110110110 :=
  fork 86 ok_b1101101100 ok_b1101101101

private theorem ok_b11011011 : Impossible board_b11011011 :=
  fork 76 ok_b110110110 ok_b110110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1101101011 : Impossible board_b1101101011 :=
  kernelLeaf board_b1101101011 #[0x79704d2e3d2a3f45673a293f2233331a2e496a6565276c30271c6333494c595a, 0x673f5753453f2e2e1c2425096969585f531f4f3d3d3f4f563349613d604f3a61, 0x15514f534e455168512d3a4d4f31583a1c315b31474567314f2e182f2b23566d, 0x3f4527491717661c311a313b494969534513676331330d3f4f4c455b6531676f, 0x5b2e454f531a1f1c225c4f273a256156532e1325451522563b51251c2d3f451b, 0x6825595131672b4f582c596c3a29164d5f29783a31343f6a56255b1522615663, 0x554f4b51676051586777583158293f635758517e2a574e151c2b316147574b5b, 0x61651b763a2c4c51582a7e3b45672b4c166c3f7d296361664c314b723f3a6d3a, 0x682f2c77222c6168333110796f31826c5533705547517a55272b7263584e3f61, 0x4f600a763449673b7e6170630a5c3b6357703b7034662c61577047396157273a, 0x515c49634b3d29472c3d78576861591b2747593d3f] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1101101010 : Impossible board_b1101101010 :=
  kernelLeaf board_b1101101010 #[0x607826603d261a3d1e34182c27345765572c6757553d702e26256d634b564c45, 0x674d4d71294b496331495a574e57132b4d531e4c602555514c271c254d2f3b0c, 0x2e292f4d632751564b4e1a5b4b49674c51494e172e2c4b491c4d6d2b4e584c51, 0x53493a4b5c49563f294d601d2b5b3f1058294b63492e2b4b4949552633563f55] (by decide +kernel)

private theorem ok_b110110101 : Impossible board_b110110101 :=
  fork 98 ok_b1101101010 ok_b1101101011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b110110100 : Impossible board_b110110100 :=
  kernelLeaf board_b110110100 #[0x653d4560456b1e454f5316274e5178561c623f454f610f2b101e45565131632f, 0x1d6772315158233d45594551273f25725945201e183d30674c514c4f5a58454c, 0x3d2d3b23183f1c512431514f5c6751555156624527554f3d5a696961314b4c59, 0x232e09590a69224f581e4b5f51264c455923255a77314e693f2967695f4b5b3d, 0x292c221b2b310a45293a2d164b2c136d5c22512269152231162c312c1e29162d, 0x29221b2b3155616653555a616b2d4c2669132c102623311615221d183a1b453f, 0x393f755633395b2277337b4959654b222c1d2020455360222b45533f294b1b53, 0x5b6a39456f615c5f692949754c693f5158592c63514f2b491d2e33293f776363, 0x685a494f5c5345673f6972744c5a4f2e2c536059135c61565c696129494c5649, 0x5a7245512a2b722223254c1516492c590c473f6f68616b53635c225b4e725f7a, 0x1e5333535a3b2a61515b5339475369392d3f33554f2551151e5366294569494c, 0x33605a251733514c726749722b16455b397229] (by decide +kernel)

private theorem ok_b11011010 : Impossible board_b11011010 :=
  fork 94 ok_b110110100 ok_b110110101

private theorem ok_b1101101 : Impossible board_b1101101 :=
  fork 80 ok_b11011010 ok_b11011011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b110110011 : Impossible board_b110110011 :=
  kernelLeaf board_b110110011 #[0x6e5d5b70363d642c555b5b6d5e3d6c5b3f5b456d4d5e495f5e595e5d604c6253, 0x306b4f605c4e5d644f4e6479573d5d4d596c5a58656c5845306c4d5b5e57644c, 0x5f595d6d5d645e4c5d235e5d454d235e6b2e4f604f1f6b4e786f646c5f5e4e5b, 0x63644e621f1c196c2d23103d163325226e304d645d5a6c5d4f2e4d6465301059, 0x161f252222062c16761e3b1f78644e5c1f186c6045653b2c3b633b591e2c1070, 0x5a072d232c204e5c2d632c29456c2d244f583a5d2c60232558761e4e63116029, 0x3b642d33635d33705a495d5a4f2e4f3d646b4f2d7a603f60655d5a6e4f59581c, 0x605d4f1f3327202951582e7a2d60222e4f1f0829222e494f1f0d3f3163625a5a, 0x655e29495e515925702049605e5d20592b4c415858333127335a3b33635d2d2e, 0x5f515e29716c512b6f62225e296c4f5c704f58654e656c275c5d576f0c622233, 0x6b2b1545512745671e20642b2722304c595d225d5f2b5e6525516e2e2b3a4f31, 0x232b222b49395b1f234f6f2e49605a2e4c5f656c4931] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b110110010 : Impossible board_b110110010 :=
  kernelLeaf board_b110110010 #[0x294b53513f455e394f3a161e312b2c601c2951594d6e6351656b6f7665534f58, 0x6f6b51456463534d626e634d251551456c7820533d531c4d4d3f51457665313f, 0x15513163311c4d456c272b5145183f4d2d4d27452b186c5e6353633f4d634d57, 0x53594d57594d1c2b2329592f51455c51291f3a242f2331291c4d232e2b59] (by decide +kernel)

private theorem ok_b11011001 : Impossible board_b11011001 :=
  fork 86 ok_b110110010 ok_b110110011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11011000 : Impossible board_b11011000 :=
  kernelLeaf board_b11011000 #[0x1e2966596b3d57295731230b63292b563f151e1e252925621c29594f3f3d3045, 0x5731623d675a4918231c6b592e0c19106b0e631e56571b101e2f18292b292d24, 0x3d31312729226024242f672917602e5e4f1c59651c594c1749565e59151e176b, 0x392e602d271d3f4d58695f57233f53602d2e1c2425692d22301f5a3d4f292316, 0x604d4c2c29655c49315c3f564d633d2b654963693f69623d65495f5e4b5a5369, 0x305953602257336a3365591c313a5f5a4922276b3a656a6659335a633f] (by decide +kernel)

private theorem ok_b1101100 : Impossible board_b1101100 :=
  fork 80 ok_b11011000 ok_b11011001

private theorem ok_b110110 : Impossible board_b110110 :=
  fork 82 ok_b1101100 ok_b1101101

private theorem ok_b11011 : Impossible board_b11011 :=
  fork 60 ok_b110110 ok_b110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b110101111 : Impossible board_b110101111 :=
  kernelLeaf board_b110101111 #[0x4b35533f4a3f3555411e3c4d29237c6c336c1c68415736376c30303a51476052, 0x106c414b413c4d3a5c4f4130373b5d374b5c155d3c41371f4d51354b41335e14, 0x3c4b3c455b65635c373c1f30653a51294d35412b261c415736655a37303a5147, 0x3f33453a5d365b1f3a414b30263a2d3c5c37414b3c661b3f373c372530511f35, 0x354b353f47331c4d4b4d41471c36473f333b1c2a5d2b293f4d3f29453c742a59, 0x4d181e304d365c45593c4d47330c3662364d2926455c2c291859065c1e304a6a, 0x5a5c1822300c6e414b203647785b4d3c62453f2b1e20172d5b0d2265294d7611, 0x1c36685d414b1f35334b333b2d364d5141514d4b4d30694f304d637e3c514f4b, 0x6529654b4a333541355736473b3f5a472c3047414741784b5a4751474b477874, 0x5b5a2e181f306053355a222959333f414b202d5d4d6e664d3c4b1e3c4d413c4b, 0x6c3330412d57603a4b4f4b29305e4f651c53296060594d293760295a1e2e4f1e, 0x55292b34] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b110101110 : Impossible board_b110101110 :=
  kernelLeaf board_b110101110 #[0x5d514d5d27097371572b5b3151535e301f1c2b4f5728351c3549574f6e475a36, 0x5914452b104d5d744d5757536057593553682d514d605c5d5759235747155d59, 0x4957473b59654151704f6e5a2f2f5d4b412b52262a09275d53623c15575f3565, 0x575d2b675941516d57510c2a2f16683b0c516e535e493059594f306c5951412d, 0x5a2741412d303b5d521c2359300e285e3057333551593b2b53605f5941334947, 0x53605e535127256a5e412319230952605e5145305c] (by decide +kernel)

private theorem ok_b11010111 : Impossible board_b11010111 :=
  fork 76 ok_b110101110 ok_b110101111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11010110 : Impossible board_b11010110 :=
  kernelLeaf board_b11010110 #[0x2d341c3a4b1e4c2953452d2d253349132733492e1a6753452f3a496566593c5a, 0x3345332a341a2a3f332e3545136749200e57353333512b3a761c33293f593157, 0x2d28353f352e5c2b5e1c333a5e1c4f1f28352e335c187034371c5134662a3345, 0x66454557266118635c4557334d315b4b623c2b253f203745271d10342f20101c, 0x6949636b4545513f615129333f65495c49315b7b6549594b5e4d55255c250c63, 0x55515e59341e1e2c455e1c3f33662a20515c4b6c761e333f6a3f665265292e49, 0x595e3f354f451c3f33526434623f51344b3f55535e4a333f266c6559293f3762, 0x3559573f334d334b55352933] (by decide +kernel)

private theorem ok_b1101011 : Impossible board_b1101011 :=
  fork 80 ok_b11010110 ok_b11010111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1101010 : Impossible board_b1101010 :=
  kernelLeaf board_b1101010 #[0x69725c15365e6715675d5c6e5c65767a6037667c31665b735c65746077524d51, 0x363060302d3a2a15255c1e112c29374b342a3a293f2741301a0f6727695c2567, 0x5e313665414f372d1a3c5a37522a31472b5b5c765e665a504b29292d30662d5c, 0x574a36692a2929502c221e29353f4f3a3c295950275d52572d2236414b333c53, 0x374d34604b29534d53492d555a574d6e5d47573552413c475a3f50495a525552, 0x49655950656318354f5e4a1f18102a37623c4d603f4d1e4d41623c4d344d3f4d, 0x522d57414b53364b492d525d372d4b4d1a1c624d49] (by decide +kernel)

private theorem ok_b110101 : Impossible board_b110101 :=
  fork 88 ok_b1101010 ok_b1101011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1101001 : Impossible board_b1101001 :=
  kernelLeaf board_b1101001 #[0xf6851674f1c414f5c471a263f512b3f4f64671e26647235251c70495a4c5736, 0x1c2349272b4515263f74156e6037736a6e61232765635e1a5c4d5160514f4145, 0x4f5a55493360491249312525495a185c2b1a45452d271a491e14642047311d1f, 0x4c492d1e4925151a1c276e275d1d4d2755493f525f372826785f5d1528351935, 0x2b67704f64293f595a34512d33601e1720331a62492b5d4c4c492d4f494c2b41, 0x29372c1c22110c1c29333f594f2e3f33614f495c3f7634354f3f671a4a234934, 0x51455f574f354f1c1f4a4f1c223f336018333f5f574d5f5d703f585245354534, 0x35221c22293f334d5d674d3445271f133a3a514f343f2229453a3a0c511c2d22, 0x4f5b3a1c2509453528334f29345955495149343f273f2f2d45282049644f5c57, 0x2b373f3f374527231c3b4523352d1d203a272f1c25] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1101000 : Impossible board_b1101000 :=
  kernelLeaf board_b1101000 #[0x5c624c2f5d2618231f1d271f2d1b0d232d1026196366601c5c7d63521f293f4d, 0x3f4f291f29162c2d121f2d315825721d53456e536051291c632f3651252e132d, 0x5d5a20265d595d572b315d534c2d514c2953625d50535b472b45512d1927552d, 0x57311c293f175e315323152b6559293f51155b2d] (by decide +kernel)

private theorem ok_b110100 : Impossible board_b110100 :=
  fork 60 ok_b1101000 ok_b1101001

private theorem ok_b11010 : Impossible board_b11010 :=
  fork 86 ok_b110100 ok_b110101

private theorem ok_b1101 : Impossible board_b1101 :=
  fork 64 ok_b11010 ok_b11011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1100111111 : Impossible board_b1100111111 :=
  kernelLeaf board_b1100111111 #[0x655928255228522020564c62153326575226524c62154f29184c6256232d3540, 0x34281f575260284c5d5c56120c232326471b25104c364c1428151f30591f1f4f, 0x3157535c561d2653512b1b4b41295156414b2b2d1b1e311e532b181d29222f27, 0x2b14524c475f312b604c68316047625341411f1e20516e4c6e263128312b5131, 0x6146141f586c2652521526181b4e611715282233365c33515c621f5251304159, 0x201a6c2615184730221856351f2d53642716155220223115261b2a285c1b496d, 0x26521f2425192517524728332a4a255d4c101d2556572431282a561f2746222f, 0x53187024565d5267564c2a252a2e55464b256055584e63301f336246592c1b1f, 0x24] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11001111101 : Impossible board_b11001111101 :=
  kernelLeaf board_b11001111101 #[0x29344b5958194c402f5d51342d4062152d1629342a450c452b161b182d232656, 0x1d59457723362d4167774c20721436622a611e1e155007592f1e29312b411f14, 0x45672e2b52502f365d514c5731252f2c292e20296d1e311729253667151e6c1e, 0x59490c572b6757265b3462511817314931702f246331344e5a59593317335a6a, 0x5d2d58512d2e624c2d5a511f0c227663624c26254f265d2d2215414e4745315f, 0x635d274c3155311e2a272917494e4b291f2a2b336b07221462584c5a364e2668, 0x58636557172d5f555b4c522d1f4e612922626f221f334c25241f291f33122752, 0x365531685751] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11001111100 : Impossible board_b11001111100 :=
  kernelLeaf board_b11001111100 #[0x1e2a2762494c1564572f512757592f5165642f225245291e22511b5d272e1731, 0xc152b232723156d571b292962234912565962222d4c15621015566d57292b27, 0x9232a102245521656452f1823232e26184c161870511b26166936184c796222, 0x221f26453622690a2a1d52452350291e361d79451436692d1d1b2d231622171e, 0x2d102749450d12201d362d451812451d0c17521829512247182d23361b1e4560, 0x51402e1a620e1f1e5b2e292f5145272a1f36452e4c15362226] (by decide +kernel)

private theorem ok_b1100111110 : Impossible board_b1100111110 :=
  fork 83 ok_b11001111100 ok_b11001111101

private theorem ok_b110011111 : Impossible board_b110011111 :=
  fork 60 ok_b1100111110 ok_b1100111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b110011110 : Impossible board_b110011110 :=
  kernelLeaf board_b110011110 #[0x5c4519552c5b625c512535505b4c62366358512749240f255562685127574130, 0x63142a576a68523124356258511f35471145354a6d23361e1f51254c35532f51, 0x255728497009562345071d0718284b2e0e531d0718285a494b5615571519501b, 0x6840682c4e2423316525365153174c15191517291e1b1b1a572c254c45230a63, 0x36245c455a50284524311d28361e151f36152f152f5f452a5649312a411f101e, 0x312445231d5d312c5649125128411f51781e345d2a5129515045245555455033, 0x28364e584c5f455a506d3127624c3653624c1f1f6d584c2828231d2f1d1d705d, 0x24505b5560712955292331531d1f28565167574127232c33571b511b1464411f, 0x245d45231324312c561b281b5d2356551f1a1f2c332e2e63686d533123555045, 0x2a335c295f5a505c515323532723452a204c20681a5245] (by decide +kernel)

private theorem ok_b11001111 : Impossible board_b11001111 :=
  fork 55 ok_b110011110 ok_b110011111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b110011101 : Impossible board_b110011101 :=
  kernelLeaf board_b110011101 #[0x1a5d615d2345283556574153455b2566255953255b53451756081f4c31264624, 0x5a454c51275a4c454c7270284941612a53515b5a4549171d1d34572d31262d25, 0x2835604966685053656434455f494e5b5b5f4e57574e315c453037574e316e4c, 0x172231312613312f347060585c30271927341f23352f314c4e2d4f5d4e454517, 0xd0f271d6f272b1153271d41511f356158604f0f283560536e5d4f6e5d60192d, 0x1d1b1d2a2b2d511a252630352a5d56535a6356286f195b49275c235d0f65262a, 0x182b2549522b4149534e2a56270e564927272345192b53562b45655b56565049, 0x23585720532d41455927464c272b18192b452c2d46574c61494919272d652349, 0x4f5d2d592759367a255b2725582559276e620e2d2b1e28222d5f2728256e5965, 0x26342d275a25535934272722620e2b2d31162b3034274013302d231e4c102568, 0x252722122330452319492b1d172527283030162d0c402d23300f162b1d342726, 0x62692b365d2d25092a35131e2d312b2d1712252b2762161d300f2d1b16302d46, 0x25312b5119252d] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b110011100 : Impossible board_b110011100 :=
  kernelLeaf board_b110011100 #[0x3147695207585226224064525d64627d6d57575358692b2d272b585636524951, 0x1718622734502227162622231e231d346459522b45141e2b102053262a264e24, 0x455725255641272773622b07245645672b2431303557594c175b1f5d2f1f5822, 0x49344e22173553562450355931475626496969194556265627495b49412d5331, 0x225a4517465345504930221a2f4e4135354a53455b534e6058355f664950495b, 0x2b184e3c344152592a271849265327495b1f4930] (by decide +kernel)

private theorem ok_b11001110 : Impossible board_b11001110 :=
  fork 21 ok_b110011100 ok_b110011101

private theorem ok_b1100111 : Impossible board_b1100111 :=
  fork 59 ok_b11001110 ok_b11001111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b110011011 : Impossible board_b110011011 :=
  kernelLeaf board_b110011011 #[0x152352234923192313155245465025222323283650224747234a135a243b1f30, 0x111a1b534c6913473b0f15130a521b4a1e15533b1a232d220e222c4c13134c4a, 0x2e3153172350451323241b3b3b451950523b1a23283b10193b1a2c235b241347, 0x9193418522245223459295034242c234c2247273615252c252520501d222718, 0x585218295c2223472e312c4e691b25271813342922242e0d590d695222182915, 0x45235349125f5a52502c235c6b5d3156341520202e25223331201a6e2734454f, 0x235c4c3427564c255651655b564c283b202419191d5a2862152525241d315656, 0x2329534531534f283b46272c1b1518476d5d1f28362337315f2c617028452356, 0x2c2c257d1f273b3756451d25273b533423183125202746272e2c3b671a702356] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b110011010 : Impossible board_b110011010 :=
  kernelLeaf board_b110011010 #[0x551a181f293020253b25151d293b4c23504f18300f524f4c62154c58591f2846, 0x254a551f2d34181f4a2910721518564c5f244c65593b53645f454c591f362823, 0x59181f281b1a2c1f140f591f5a19122825291f24594c1f284c1f521f36286215, 0x1e1f5912] (by decide +kernel)

private theorem ok_b11001101 : Impossible board_b11001101 :=
  fork 53 ok_b110011010 ok_b110011011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11001100 : Impossible board_b11001100 :=
  kernelLeaf board_b11001100 #[0x1852625652674b62673062301452185256163b51657466245276522453585b59, 0x74141d10581f2452651f46526e317046582476674a45525d674b76227d222914, 0x313b47585162694a47145a53645a5350187c6e62226c1f151f2829291b151f28, 0x314a285a645a7e536751646262225f5375302564625164627452473376584a46, 0x170e58691f465d1f5b275b1d102e245262645c27463b625358622267153b5258, 0x47625d5d62225d4b226218566c3b1f151b281b622729221715227418140a2319, 0x4b49567414294515345a64727c12513b2e51533b4b635846565c28535d5a6730, 0x3b5f53455b5623361b4e1b535a64585b534b584b465618644f6231474f5a4636, 0x182265554a660e185a34503631564b705d67] (by decide +kernel)

private theorem ok_b1100110 : Impossible board_b1100110 :=
  fork 38 ok_b11001100 ok_b11001101

private theorem ok_b110011 : Impossible board_b110011 :=
  fork 57 ok_b1100110 ok_b1100111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11001011 : Impossible board_b11001011 :=
  kernelLeaf board_b11001011 #[0x3c4537274029532f274725252b6e395c45531952526445272253182d3b516215, 0x3b2513522d132d3529244a695729333b40294759523b502d493947302f393c2b, 0x243b252926253429392e2f292d6776265020596c0c5222282029221755335318, 0x22765355294a3953253953663052475c2f3c53402b295345222d26511e13532d, 0x603b4e3b455559665c5349371a292f5925522d514e273b502d452f5959641d28, 0x2d4f29261b5340274726535928511a5c585164726e620e5159524772585a3c68, 0x18271f5b2f3029761e345a592d525c517664507e26593c5a57753b69585d591f, 0x60503c5a286a4e5c222d282750764e60346d305b2d60342227346050641f5225, 0x2818611a274e0a4e12271a30254a374a2d2957292d50604e505a1428605c6a3c, 0x2d45274a2f4525273b593950294a221a3b500b221f764a6a2e162d1b271d4a18, 0x5339271d113427506027135953391b221b2650331a55272f2952294e454a513b, 0x4727112f24373b495945] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b11001010 : Impossible board_b11001010 :=
  kernelLeaf board_b11001010 #[0x396459515534602722127659294f33502d58355f4e5c2459295b58582f595153, 0x574f3b591d] (by decide +kernel)

private theorem ok_b1100101 : Impossible board_b1100101 :=
  fork 70 ok_b11001010 ok_b11001011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1100100 : Impossible board_b1100100 :=
  kernelLeaf board_b1100100 #[0x536e4e586069130813182d5b4a2437295853520926133422604a242752593947, 0x4f3b13602d1d34395926281b2e3519394553282d2e2d1f352e6019132d2e5d53, 0x34534f501a45392865291d2f2d2f59452d162b1e533c2e12072e4f602d2d5f2d, 0x3c1e2d34405c1a1015284553395310522d5b3c532d1634223c1f39301e393060, 0x3b492d39] (by decide +kernel)

private theorem ok_b110010 : Impossible board_b110010 :=
  fork 35 ok_b1100100 ok_b1100101

private theorem ok_b11001 : Impossible board_b11001 :=
  fork 58 ok_b110010 ok_b110011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b110001 : Impossible board_b110001 :=
  kernelLeaf board_b110001 #[0x6e1a451a2d276a5a6e6139133a244a72554f272d406a76614e69555a5c602e53, 0x5a656e2d352d575a2d403a5c5d6c526a1f2d5d241f3559392c3466347a6a553a, 0x246e0e2858622c16726029642f5a4e465c5f6652686455591f1859347a594a64, 0x24243a45286870822c58406e351b5f522d5250661a1b281228243a1a3a241062, 0x1f455f4a587a5a7c24261f6e282f5a1f162864351f585b6b7239101664695965, 0x5d6a283950520e2d613527794519314e60242d221f593a452250593c5939580d, 0x65596633504a5d72645d315d52172f693431392f2d664f523a4a313a4a2d0a0f, 0x5f5545461d590c46221b6245155c28655a4f5c456f261d283549495a655c5f55, 0x2c1a1f463759595b3c2230371f18172435642c392865294a5f55451f602d5524, 0x27463931375b243a49461f3c463a594a243c4539465b2476645960301f373731, 0x605b454539456b355d59524a37394b3959395227453937463435194e52604e34, 0x5a4f60335a5835574e606965291b65335960396e6558615a64605d586559354f, 0x6d46584f1d3918296d6234] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b110000 : Impossible board_b110000 :=
  kernelLeaf board_b110000 #[0x4b59391f5b501b4b2f22633126222f11224b6822495924224b63494062591a34, 0x405910243131294b18314565271a684053636c18522e3c0917352d535d2e2635, 0x295320235c591e13330c531f202c1f2c4b31242e355863452940535d291f591e, 0x27292e2c392c1e16290608171e1024314026245924530d1a292c1f1b29181b61, 0x182229634a655d4b656318527755586e587c0827272e176560244b246a224b55, 0x5f5922293359275c1f222e525527292e5f17270d22291f6c142731294b632e5c, 0x27192345244020222b19266c635222591d4522192f2d16591d2b52490c09520c, 0x451429232a1f272027493149292c29614b5d31296327] (by decide +kernel)

private theorem ok_b11000 : Impossible board_b11000 :=
  fork 86 ok_b110000 ok_b110001

private theorem ok_b1100 : Impossible board_b1100 :=
  fork 63 ok_b11000 ok_b11001

private theorem ok_b110 : Impossible board_b110 :=
  fork 72 ok_b1100 ok_b1101

private theorem ok_b11 : Impossible board_b11 :=
  fork 50 ok_b110 ok_b111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1011111111 : Impossible board_b1011111111 :=
  kernelLeaf board_b1011111111 #[0xe55594d244b5d146f3d5a585d624b262d3d1928265b5a5558553d5a53366434, 0x4d335555335763232b6e4d686355701a5a3658205d1c53534d5a24132633105a, 0x33330e2d2d5b284555693567355b5a57234f21305d554b553378281a2d125a45, 0x23243a2833584d5a2d3b2d3a5f453a2d3f536030263d5a3630472d5757333029, 0x29282328182e35334b553f334753365a4d45193a57335558235b17182e355d2d, 0x4d3f582c21172e3533656c4b2e353641575a4f352457333a49283b335b451713, 0xc4d1c5a3d365e4b41574f3324285d3655555533365f3d36334d3d5545532d33, 0x314d3531351f2d354d60354f293f2d6a647e556f4f7455] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1011111110 : Impossible board_b1011111110 :=
  kernelLeaf board_b1011111110 #[0x333a3d32783037623322783c10335e3d6763623a1f16325e4d5e6c30742c5158, 0x3362313c79732a7a331c476e6e5937252318213a32627e25477a183d7a321c16, 0x33552d3033473c4d2d3232311662293a2f261c47332f25322721263331302f30, 0x33314f3c34284b4b326c24334b3133224f3c2c5c3d453029305733554a35332b, 0x68513c5a5b454a4545575a334f455d3345552924654f4b4533554b5d33453f6a, 0x4a6030455f33314f3121685d4f26266a47645d59534d30476c315d5955304f47, 0x4d3178655b63331e275b4520245955594d62593f51604d4f47514d5e59512733, 0x5160303759293362554b2655334f655d59305d2c536c2f312959334768513c5e, 0x353a205529805951592b4d24604b722412574a354b594d2775275d4d5d272459, 0x2d334d60536c2929] (by decide +kernel)

private theorem ok_b101111111 : Impossible board_b101111111 :=
  fork 70 ok_b1011111110 ok_b1011111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b10111111011 : Impossible board_b10111111011 :=
  kernelLeaf board_b10111111011 #[0x57455c1d70216a51185b4a656a28456c4a414a33476351211e3a692d4560582c, 0x18284f623d2b4b363149334b6045235d21363a3a2d374960514a4951740f1e6a, 0x312d3b32457a6c14603745601e4f5c27492d511f364918372b33605d3d2b3632, 0x5f31326a1c2d655d6a6c3b] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b10111111010 : Impossible board_b10111111010 :=
  kernelLeaf board_b10111111010 #[0x311418584d3232621f55511e2b4d332b23251f7180115d6d765e654d324b2c60, 0x7879512d4955452b292345330f4a13354b5c2347333a3b29493b5d324d45311f, 0x517a1e2f103d25175a254d352f16362455655a73555147553b273f4923184971, 0x3532532d33463349325345130c4a4945535d4d4b1933683227061e4d4a254d35, 0x2e45205e4d47454d53804d63165736474d3b4d3d147a642b3328352835334d4a, 0x14360a20271f3572652016575f58334572654547530c4b367c6a5f284714572d, 0x805a2023464d23211828282120274a634d2b174b35325e35326b25623d2b2e5d, 0x264f29251b2d2e4a133d36354b5c2128162e17291f3329213b2318270a2b4d3a, 0x511e2f25243d231f2f24253d6951782c5b1c636c293211252f2b291c3323293f, 0x3669556c685a47326d4f29166368196c6f5e785b6b6c69326b5e6f554551452d, 0x4651454a6a6c53726924475b315d4f493f58335d5549634f452c632c325a213b, 0x3d45516962696236647823634f10365733645a635953461c652b453331] (by decide +kernel)

private theorem ok_b1011111101 : Impossible board_b1011111101 :=
  fork 48 ok_b10111111010 ok_b10111111011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b101111110011 : Impossible board_b101111110011 :=
  kernelLeaf board_b101111110011 #[0x6e312c6e1d7e496730286a282f281d293210181432453229212d102278625158, 0x4d5d4d4f334946596359631c651d5d677e656e3b592565595c4f5d49214d6a30, 0x512b454b2363295e1f51495d3331653f514f305c654d4d5c5a454d4d5a496529, 0x65724667656a5d59315151314978364b624b4963292f6b49315176286b1f103f, 0x33322262496312274b2f334b491272462e5a4f3f494963326b4922625178185b, 0x67306f67304b4965292c8057304b4b5f5d4d6f4b4f202b294f2b313065331f33, 0x3f5d0b30102b1f272330654b1a114b5e4b7e4b2b] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b101111110010 : Impossible board_b101111110010 :=
  kernelLeaf board_b101111110010 #[0x62302c323f6316696a304563654f635d583b3f302d730d2c37633f6b31495c51, 0x5d4f6380184d592e212d5e78180a6a203f4d2c2530322f2d6b78314929323f1d, 0x5d5d6249596a78181c3b4f17212b29302e655d655a45584d32253230657a1867, 0x37654f1c311b2c53414b241f3f1f37215d316a49493b2f596a4f171d5d463128, 0x45594b4965292b4b361d6a594f4b30655a2730253f2d3f621d3065185d4d3349, 0x464b3f414b323b304d1f4545624b304d0e5a4d2b304b] (by decide +kernel)

private theorem ok_b10111111001 : Impossible board_b10111111001 :=
  fork 108 ok_b101111110010 ok_b101111110011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b10111111000 : Impossible board_b10111111000 :=
  kernelLeaf board_b10111111000 #[0x2e3b3345122d3f2d63332e332d31211f5562466330305d1d313624316329494d, 0x5e5d2e5e2c2d2b24363b231e292c5c53306b5c21252c145f165f222e57293149, 0x55200c102e2262315f312e62773f58211e1f2c3062514555622f30455e4b2724] (by decide +kernel)

private theorem ok_b1011111100 : Impossible board_b1011111100 :=
  fork 96 ok_b10111111000 ok_b10111111001

private theorem ok_b101111110 : Impossible board_b101111110 :=
  fork 60 ok_b1011111100 ok_b1011111101

private theorem ok_b10111111 : Impossible board_b10111111 :=
  fork 82 ok_b101111110 ok_b101111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b101111101 : Impossible board_b101111101 :=
  kernelLeaf board_b101111101 #[0x3f3a476746512d5e29632d274b7624535a53512b373f55491a6b705a4d366034, 0x3121512d595d4b2b331e593f13280c023f27671832020c5e4d222d4b4627492d, 0x32223a273a2c4b2d4d465d4b273a332e27555a4d59491a676b595e4b3f3d3523, 0x3f24615a57245549573f31285a4f2b2824201c4b36643a5e3d31555d21463a3a, 0x4b4b6a6c36284d634f4f334d6868621a55704f66365158281a322c5a3a274b6c, 0x274f1c5a1829234b2e271c4b7c2702764b6c2d235a242b671c36683d232c512d, 0x47323d734628126371624f63456665605551582c3f4b322c3f366a6d674b2429, 0x5218512b52281c364f59604d492a4f314d463328633f494d364565365e6c4d2d, 0x52601e682e332e32186c4b324532457049493a3f60242118233d3b1823283353, 0x3129664d182d2a352a4f5115654f2d554f512a1f364549323f55324b64324531, 0x4f552a4d4174325c37203136212d512a2a6351] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b101111100 : Impossible board_b101111100 :=
  kernelLeaf board_b101111100 #[0x362d473167415a205765581f3231454f202c625268623f5e321f453641344b2b, 0x606152274f1f322c2925252c2e333659372d2e0d1d3227344d3f21331e332c31, 0x1a6831514637682f51362517592c592e32294b2c27654553211a2a2759314f1b, 0x6367585a1d686a344d5d211c2332732520156529783131602d33242537672133, 0x51472d372c33681d532e282e2c52314624282c282d2e33582d1a1d3331685867, 0x2f0a2c374f340c6261156f316a336c1f28341e51582e182e334b61685e534762, 0x674d2d314f316645676c51363b4d5145604d314f634759454d60312c29286263, 0x6f624f5e2a7c6f7e68675e250f291b311e636c5146516b7867596c684d5d581c, 0x5a4f28312f313127202f41711d47286c4f314f634565456746636b282f473278, 0x32372a282f281b1b08284f321a4f5c602e314f31273147] (by decide +kernel)

private theorem ok_b10111110 : Impossible board_b10111110 :=
  fork 60 ok_b101111100 ok_b101111101

private theorem ok_b1011111 : Impossible board_b1011111 :=
  fork 86 ok_b10111110 ok_b10111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b10111101 : Impossible board_b10111101 :=
  kernelLeaf board_b10111101 #[0x2a153736323a41303737103037302c6a34293a685d1532272330211f2d4d5158, 0x5c41292a2959334f3413181c2a2533213b233331306b3052332a37212d472541, 0x2d4d303a2d3429455f2c30554a5f575a5f1e454f33323631325c593129692d45, 0x4d512d2f1f2d51262b4b6c2b4131535a536853416c574736522d4d4f2d304d16, 0x2b1e2d3029325b2d4f3529302930621a5a5c4f303032595133452b35514f2451, 0x60323051416c47354f5741605d2b2c5f5f243a2951304b3351245b4d2d2d271c, 0x624d3a2d372f2b601e2b2d2b4d292d30324b29553229703a324f5f602c306262, 0x5a341e672130415721252955334b243a4d234f5a3b604d2d323055232d2f4d26, 0x2d5523572d2e4d572f4123572d302d2d29372d686c306c5c55555b] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b10111100 : Impossible board_b10111100 :=
  kernelLeaf board_b10111100 #[0x513153276d3164534935644f5766232f285a2b606d5a2d2f55494d535a514536, 0x70352f532732495a45472d6453492f35344f494915312833495a31274d492d51, 0x31373a4d5a493a3151514f334f35326435492d324d602f624f64] (by decide +kernel)

private theorem ok_b1011110 : Impossible board_b1011110 :=
  fork 86 ok_b10111100 ok_b10111101

private theorem ok_b101111 : Impossible board_b101111 :=
  fork 64 ok_b1011110 ok_b1011111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b101110111 : Impossible board_b101110111 :=
  kernelLeaf board_b101110111 #[0x5c63786e5c58235c1978694052246c33194d5e5c73314d243369224166262d51, 0x5c2a2c5867416658415d636231365c342446415e371d3128367253211e4d781e, 0x696a6053336032586e3736375c313223532c531260683667713668583634315c, 0x6e31531c496926661c1923317e265d592a5321254d33585960665c6a53695e59, 0x345d2125460f1d41205952244d2c1e244d4166263d28315c5e6f581c58493115, 0x6449583260721028313637594d662a29631e462c271d736018462c4127621d46, 0x33271a142d1e5911642610404911262a37111b232a321c171e1b0a651c1c7206, 0x2128352649261f28352b1e345d2321195d265f401d282a2d262333235f1e2d26, 0x1816221d222e2a32355d642b1d2b322a1d322b492a5d691c242a3264322a6923, 0x585f6935473240585f612a3532592b4626373121472d] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b101110110 : Impossible board_b101110110 :=
  kernelLeaf board_b101110110 #[0x49362b29322d5b591d5d5b5762662a2b6c22242b2549182a1c326c5b28363556, 0x322c5d2a59371d6c591f2d660f2a2524182f3649592727342a2033283d0f102a, 0x35365c376a492b3636286020685d5e2a355957222d34412433592f275e27592a, 0x5c292c3762495132232d64363564526d5d495e6a22245b4940603d2b2b1c6a28, 0x5e6a6d5d785f365246601862602c40375c34595e5c29272a3362263237612f2d, 0x365d5e366c2b2e2b3d2c3240212c2d4949625d2c33322760632d35725d5d6d49, 0x5e] (by decide +kernel)

private theorem ok_b10111011 : Impossible board_b10111011 :=
  fork 75 ok_b101110110 ok_b101110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b10111010 : Impossible board_b10111010 :=
  kernelLeaf board_b10111010 #[0x26311d175f6a5810352c355c5c35531f5137535f21355d641d315d522b152836, 0x37652f352b5f242a65197378651d5d5f49564b0f64352b346031571957312164, 0x5e4b4f2435252a3564251a23242a5827495e5860531766536e51252c4a262a31, 0x5d5d572c5f605826524d2d335f572d4a532258281a5d2a562a142e2d572d4a57, 0x4951461d494f58285f1526622810311e4f212f5e2d2224342c572c51514a4d37, 0x51665351270a1613121810242a602c5f1e515f17281e1d5d31230d2d1f631657, 0x275121634d4d204a2d244d245e29] (by decide +kernel)

private theorem ok_b1011101 : Impossible board_b1011101 :=
  fork 63 ok_b10111010 ok_b10111011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b101110011 : Impossible board_b101110011 :=
  kernelLeaf board_b101110011 #[0x3349592949142b591d53785932531d6d53715658616e5965313f515e5f492d57, 0x591c2f32156c6a615963156e2636326e2926596a225e78585132362b326d1d49, 0x266259595359685e4d25651d6f3215626a16596162631d7e4d65596a65596e1e, 0x295f584936624d335e523259321d41564b321e323162332e331d] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1011100101 : Impossible board_b1011100101 :=
  kernelLeaf board_b1011100101 #[0x622d27371d362f0e181c1a6410590e3f5371593f6a1d64596a1e2f152b312872, 0x6556340e5912626c46656451325362704f7051622b4d41675927463156682051, 0x51211d2e62184f516224121c321a564b312e1221212f2e62186831627d0b6367, 0x2e5618685336627a612b637456282831314f4d5b56464758665265642b2a5962, 0x5162681826624f68265162245270202514267a6a591d22251c3258336c4f6257, 0x6a3647241c525331202249592b14255e1c583215511c6227595152627f56631d, 0x4936534f2f312b593773592a2f1d31647359262528595f6558366a2f75593756, 0x1d31717a51626818211d2121711d1831282e5e4d2d2737682f322b52274d3624, 0x5e6a5832105259656222521d3326535934621870322b092d361d271c53521d37, 0x62633162282864656982267a592f34280a73598075597a22737a] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1011100100 : Impossible board_b1011100100 :=
  kernelLeaf board_b1011100100 #[0x517a6a595856241c32476a59472a56582d242e242d232e533f2f47332226185e, 0x1d362b28642d28336b6324513f2f186a52654d2b656a6680566373652b564d26, 0x266a4d573666535768662d216d28364d2d212424683f6a56593636] (by decide +kernel)

private theorem ok_b101110010 : Impossible board_b101110010 :=
  fork 120 ok_b1011100100 ok_b1011100101

private theorem ok_b10111001 : Impossible board_b10111001 :=
  fork 93 ok_b101110010 ok_b101110011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b10111000 : Impossible board_b10111000 :=
  kernelLeaf board_b10111000 #[0x572a362d1e2a12103132412e2d2a153157173649531d2831314120535e5d522b, 0x5d73598070226263586259615e532132411459592a341d364968495f312a4959, 0x31495f282a364d3f33314962732f34595d515f625d522547516e1d6b69477a6a, 0x1b57570f572d711d31122e27284129341a285d59571d3117495d1d3110315331, 0x5d41627932312e2a2d362729362d341a73571b1d312e2934222d36201e0f686e] (by decide +kernel)

private theorem ok_b1011100 : Impossible board_b1011100 :=
  fork 96 ok_b10111000 ok_b10111001

private theorem ok_b101110 : Impossible board_b101110 :=
  fork 60 ok_b1011100 ok_b1011101

private theorem ok_b10111 : Impossible board_b10111 :=
  fork 76 ok_b101110 ok_b101111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b101101111 : Impossible board_b101101111 :=
  kernelLeaf board_b101101111 #[0x4d415e1c29654c725b631c7241632735414f566535351965334140245a672a4b, 0x1d2e2f27374c2f272f4c403215242f725b63606677592235495e354135494164, 0x2d3d5b3a27301d412d64415b7066574f1d641d2464662e301d33297259355640, 0x1b5b71606c590f0f135a246a570e65354a5b3d4f674f2e59416733294d253223, 0x5e565a4d615a4012405a344a352e341e34405a3a5b2d5e2318292b3a33410e69, 0x37493d5b323228182e343d2f495a3a273549495a6d343d5a61645c3d40495f77, 0x14242e4c1c211d2426352b34594d4035675a3a5a4133344d61232b5a592f3434, 0x2a24354a552961603058554a31304163463d4c1c1722242922201d1d0f1d074d, 0x4f314f3561242a35594c58292a2e6c30315934241967212e30412e262e302267, 0x552922641d7e352a2b203031] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b101101110 : Impossible board_b101101110 :=
  kernelLeaf board_b101101110 #[0x2f19153b496032582d53783a5b605e2f412d63463267584d274d3d3b6b163130, 0x491a331a3d333126222f183b284b5a403a2d342f3a2d4d33605b6a63415a675e, 0x324d58332a72345e462a2a4633344d583140234b24401232402366121a211e34, 0x3a65372f3a2a591d204d5e592065255a404b2f661c2a27461c34275e346a2a1c, 0x372f181c5a] (by decide +kernel)

private theorem ok_b10110111 : Impossible board_b10110111 :=
  fork 81 ok_b101101110 ok_b101101111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b101101101 : Impossible board_b101101101 :=
  kernelLeaf board_b101101101 #[0x576a2859596a347212104d5957521764605f5a7060712e1c5f5a704d6c562435, 0x132a1c562e161e19262b1b5a575c574f2361576c4f576c5f79615a4f6a2e594d, 0x516b52596c693d30321e2d571f464f302a591e64602a56295752301f30146a4f, 0x236c2a2f24492324181c292f1e651e1e60092b2f24092f51251c2f242464255c, 0x235a5c28565a271e31286459655a51631c2a56252356230d2d2565791c2e705f, 0x17303d3153342e272a1a2a253d34645c60792f242e2b5c655a79241c53341e20, 0x72511e1e2f31294d60242b3b29315c212b1e5930675a3d4f58512b24213d2f1c, 0x3d6429513d1e30532d532b1e282b4f29575c575f26515317303124175c665c5a, 0x1c27132e0c2b1d2a2b1c1c14152e56152a244d6c1559] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b101101100 : Impossible board_b101101100 :=
  kernelLeaf board_b101101100 #[0x191c51512b14596c202a515e146a631f592563292b6c31342919271a1c663058, 0x5f4b4b5c6a1d641b2a5f5971665c5a2a5f4b246a59673551272b6a2b5a1e3466, 0x646a12196952594f4f5c2e2a5967305f4b614f5a304f5c635f611c242e2a6459, 0x65294f65246a2a592e] (by decide +kernel)

private theorem ok_b10110110 : Impossible board_b10110110 :=
  fork 51 ok_b101101100 ok_b101101101

private theorem ok_b1011011 : Impossible board_b1011011 :=
  fork 69 ok_b10110110 ok_b10110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b10110101 : Impossible board_b10110101 :=
  kernelLeaf board_b10110101 #[0x511a1f725a1e3a51305b4959491c56215166492f1d102f453256126b17602434, 0x57525218561745276a5b52596c22243232514f1f5f4c31585c59511f701f6a0c, 0x1c274f271f46495260451d0e4564170b4f285e51762f57767476174574566056, 0x4b76724b4f271f2b2a605127152a1c1f203560605c3a515c651c453029286017, 0x244a174b241664605c4f1f24231565292a231524654c283523271e2b0d057659, 0x66602f725e451b6c6a22242a17236529250c29181f30302a17100e2560594a5b, 0x4a284c282a3129292f5b29594a5b1929595e5127303a201f2429204b4a25654b, 0x20292426] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b10110100 : Impossible board_b10110100 :=
  kernelLeaf board_b10110100 #[0x181959632425354a201926195924351f4d29512f252b2419344519514f593130, 0x29324c4a63566f2d135e226f600c51572f4d4f55514f1c59662a24251f526325, 0x45222f224c667212601f1f2b522d2d1d66264522590d021d452f170d570c1d22, 0x2667725a1e344c5b651d1c780c596c6f0c456f18603a262a1c2b5b1e345a202d, 0x512a212b26223126212b31265b65] (by decide +kernel)

private theorem ok_b1011010 : Impossible board_b1011010 :=
  fork 51 ok_b10110100 ok_b10110101

private theorem ok_b101101 : Impossible board_b101101 :=
  fork 63 ok_b1011010 ok_b1011011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b101100 : Impossible board_b101100 :=
  kernelLeaf board_b101100 #[0x65305e45532e221d5a5931633f6a5a4d3331672b591f323127452b31253f564f, 0x6a6b30512551591c2b32552b312f5856454b595732451b163118451669672331, 0x65292929495c51721e63596659595f496b30322459555a5e596b2e602a32632e, 0x4958675a0f5b6349601c3051314d2322342324516a236051316052294d30525c, 0x615230605b41495a632749602734273f272e375829582229581d33592765632e, 0x5e4c59724b32252d292e30272e1a59276031414961632e2d3060585149603060, 0x345f293029605c295131721e2916511d2a635f745f6a5a512d5c516b2e312751, 0x5e4b596d551d3f603151374b153f2b29513b581d3f2b633f2931656632304c2b, 0x3f68242f6b2163586a26337858535e51305e3f59322251345c6730414b5e514b, 0x5941312d53602b593157262f] (by decide +kernel)

private theorem ok_b10110 : Impossible board_b10110 :=
  fork 60 ok_b101100 ok_b101101

private theorem ok_b1011 : Impossible board_b1011 :=
  fork 80 ok_b10110 ok_b10111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1010111111 : Impossible board_b1010111111 :=
  kernelLeaf board_b1010111111 #[0x2d2233272a3f334a226e2a1c2d6e67132d52373133222d673a102d523229582c, 0x1e19273768410c1d2d2f2a331d2a780c495b4a163241271c361f1d1e412b521e, 0x1b5d123f211e2d2233142d3b25223f572d37633a5232170f21142d222b16211c, 0x781621102d2711264d1d1c3710261957116a1d26412126162d31311d310c4126, 0x1663167e6c32634b6d6d65635f765f60763723106e685225513125373231104a, 0x4522244133105637645616495f675376603a6967455b6d335129623380088018, 0xa7e6f650c1c332a57613d272b1c723264333b4a2a2f293d453270565f667461, 0x21350a141c33454531331c2a3b32582735324a333a6c314a331c31353131133a, 0x3d45333d631445192a3332333a1c602a] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b10101111101 : Impossible board_b10101111101 :=
  kernelLeaf board_b10101111101 #[0x25f3524362c1f102c453d6f6d332c551e4d4b153525201f2c363d312d165260, 0x312518640a23244d3d241a1e36244d242c232b2c320624362551297e5c3b5545, 0x2c2a5b5a5b2d45531a1a192455231818065c641a5c5b3b1e3a1e291719195d23, 0x55533b5a55246e615c501e2d452c3d2f2d152529290b2d1e2761151f5b192918, 0x65091845331c2b51691f2d322c651b211c23472b213d326551231f3b10525c1e, 0x245f51317633272d315a6831182d331c00162d3a721a3535511f182d72354b72, 0x1a2d3d5b3a1f250a2d365f5123361c141323081e3a722d15161736063629161c, 0x1a257251275a3d25675751293b492f3d4127691c495a5a2f2b694147232f5724, 0x2929243d573241330c2725323d36233d29315a2f173d2427726419502772642b, 0x4532633b3d7c685b2d5b3b643a41575b365b500c1933365741625b50453d532b, 0x5b195b3b633157332a3d5f55] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b10101111100 : Impossible board_b10101111100 :=
  kernelLeaf board_b10101111100 #[0x3b4d255f502a500a41685a3320232f1f51152f36252518294f2b1f3b3d32741c, 0x5c5a2155233b3268273d36641a411a190319271b1e291f3d4136155519554a23, 0x6864366e2a1f3b32233633212c102b292919412b21686341273b5136234a2332, 0x3229320b1e0529142a1f6332251e32295c2563217c3d25366f47336f7c6e2a7e, 0x6e50451a3b2c684d415c3b47095233477e68655a3116364a2323321f2325331e, 0x321f47321f33142c1021266e525c1f3b50695c4565506a64745c69632d5b4764, 0x14642d4a1e66325218526f3d7c66316e1a5c2d1f7c523b526e26253221251b25, 0x2a13334a352325355f1f173d192631473b23362331260c5f1f0f264d2a321e0e, 0x1f50190e2d4a1e1f335f452c214a14454a6a2c18253a4d2a605f13251e0e3b47, 0x4d3b1a0d6433502a5c521e414520653320453d64194f2d5b452c512d14322c4d, 0x6e321a68642c140e201e631a69695a1a680a170a1714201e] (by decide +kernel)

private theorem ok_b1010111110 : Impossible board_b1010111110 :=
  fork 88 ok_b10101111100 ok_b10101111101

private theorem ok_b101011111 : Impossible board_b101011111 :=
  fork 48 ok_b1010111110 ok_b1010111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b101011110 : Impossible board_b101011110 :=
  kernelLeaf board_b101011110 #[0x252c316268674f5762505b2d364d2c585b0c685074211a5220365b2427336a22, 0x36272d0068787c6627144f106e321a5868624d1a10582d295221182c262d374d, 0x5b4132212d32316278185c337c314f6e4f176e2b4f52324d31254f6e36636518, 0x36655a32804d5b206c271a17306f292c2f255c514f6c1e5169702c6a5f635852, 0x2c101c1e303b57365d7862305a5f576f724f27364d30316533645b1c29785162, 0x290b29332f3615251a321c581f70271e311a703027723016302b29301e3b1672, 0x6e0c2729311a273615293727331a265a31253631331d29182f1f822f250a3656, 0x2c211e2b3665312c3b254f252c2529493f2c362521316310292931273326212f, 0x571a57333130272533272131301a1e260b7e303b2f18265a21301a6a291a1f32, 0x15552f243255472b5a29102b272b323331252331273620293b2527253b291f65, 0x33275a2f241b25] (by decide +kernel)

private theorem ok_b10101111 : Impossible board_b10101111 :=
  fork 60 ok_b101011110 ok_b101011111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b101011101 : Impossible board_b101011101 :=
  kernelLeaf board_b101011101 #[0x615c4d615f566435453d565a5b566c411e5c416a1e30295c1a30532d3d643150, 0x37705c2a292d5b64295b5b1d6424354a5656615a3d5c53605561566055634d64, 0x3f115210301a1b6329313c4d25322d2f515115413a2d5b0e290c29043d2f552d, 0x6417561a57655251575c221b570a1151561e6c1a51225657616a185f1b68171d, 0x1a510951252f4f6c52682c375a2b0e2b214715262d361b651d564f682f17525c, 0x1c131b154515637206573d57680a1a27645107571e532d72275a0e3a5c301f2d, 0x5b24524f133565171b29680e721a3d31520e3d35243664111f23654f41292d13, 0x733623264f535a1a3d31075268495a4f2935533d495d254b134f653270274945, 0x5a36555a63556e6a534564231c0a231f182b76296d5b72352660764772652d35, 0x32063a1f1d1032492d37295565557755704d495b1f537a705a1a233a7c3d5552, 0x2b362d322d1836371056492d1445363f2732642f2f] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b101011100 : Impossible board_b101011100 :=
  kernelLeaf board_b101011100 #[0x4a17152d3a451a1c1b3d1b3c313029293c3d5b31303037312d51685f6c2a4763, 0x1f2f645632311b36572d4164695c3d1a1b313c37350e152d60323c60653f3518, 0x2d3c312d413a7c60652f511a65503535715c2f5c512d372f452f51772d355b56, 0x1f306564654f2d7730155b5c29354531321e321c2f1c2f2d694135115055715b, 0x2d5764575c516b561c363d682d292d6429501c2a2f312d1f233d362d4d1e305b, 0x51312a32312d375d152f373c471c2764797e75645a3125324a354f18312a4731, 0x2c2d6529503130151b5c3f4d2d2c3761325c325c15365d65155d6a3c514d3029, 0x65314a2a6569321c6523175735363d644f5d372a4d4f312d1f1b411b30321b3f, 0x5b2b2a311b806a71145c2d3d67315741655c653d5c3d65475d5d5f3f35293c47, 0x2d4d2d643537472d30312c1e2d37645c3529] (by decide +kernel)

private theorem ok_b10101110 : Impossible board_b10101110 :=
  fork 88 ok_b101011100 ok_b101011101

private theorem ok_b1010111 : Impossible board_b1010111 :=
  fork 40 ok_b10101110 ok_b10101111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1010110111 : Impossible board_b1010110111 :=
  kernelLeaf board_b1010110111 #[0x4d745a655b561b1b3a6556295b45335f77333f3622314756294967505b636a58, 0x495f4f704f707a66566965692d5d2d49315f4d5d4d5b2936335f456b4d5a5166, 0x736545657f5b45675f6c57736f4d655b5765474f5d6569774533474f5f6e744f, 0x1c1c154d2d20124a6e7a4a655b4d5d2265471c297a1e5063574a63794a5a3663, 0x5356672f226a745f66500a230e14286561675f4a5b4a4d5b331f18283a65703d, 0x4d6529494d635b3d57495f457a5f7c7751776b5b7067725a576d2d7056615533, 0x4d2d2263313b455b336e3114306a1e5628332b3312704a786526295f63656d69, 0x51245a5778576a6256205b6a5362220a1d1823235115165a28] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1010110110 : Impossible board_b1010110110 :=
  kernelLeaf board_b1010110110 #[0x234f7063365f501c0e360a5014262d36227e69674f5d6e7463375d496c5f5658, 0x4f2477230a364f6b5a5661635b76693a53535a6f7d5a4f4b7b6b7b775a566770, 0x501c47505b5d5121333d6d35511c4f35455a304a104950515a364b5a51455a51, 0x5d5163293551654f3172506524495051635b28335b3f21281421301823371833, 0x72564f163a504a5756173a5130656572673b505b673a4551283f2476635d5a6e, 0x3d10283316511e5a723d672f49693a307c6f5b1e231c36230e4f184a30313c31, 0x184f5a69274f5b63513f326b5a69614a2d513f664f16451e6e24284f72504a49, 0x69283f722c2d2d232c291018473623064f51695b632251695a61143266782d62, 0x51457261476730] (by decide +kernel)

private theorem ok_b101011011 : Impossible board_b101011011 :=
  fork 92 ok_b1010110110 ok_b1010110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b101011010 : Impossible board_b101011010 :=
  kernelLeaf board_b101011010 #[0x473357787e564d4a6a476a4a337819124a37230c584d1d3a2d5b2d472d29282c, 0x5d2810311031272d33142d5310062d1f33165a2610122036124736624a33552d, 0x1f100614273d2314565d536a0a561057315d5a53171d28490e5d7753212d5524, 0x575c714d27263d3a2d49274a3b5b50721f3758273d23313114303d265330242b, 0x16693b30333d45263b10625f21092d1d7020334a553b556357292913634b313d, 0x31304b5d674a5b28655a5f3b623b3a3d3d3b625a303d3f624f62323128573b5f, 0x65295d656a060e4d2420334a7d3d5b160c263d5b263d4d10624d4d4b293d5d3b, 0x1d2850760e29215b3d285b50285a4b275b201d63245c243a2d1d293721271424, 0x76232d5024555b287e32292732273d841e1e57271e3a303a287c5a285b2b1912, 0x537028235b695820747e3b565b705074581e45532824] (by decide +kernel)

private theorem ok_b10101101 : Impossible board_b10101101 :=
  fork 100 ok_b101011010 ok_b101011011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b10101100 : Impossible board_b10101100 :=
  kernelLeaf board_b10101100 #[0x7c514d4b6761763f32645612243b5f1e16282d10332d1620364d3a7456185a63, 0x5165495f58243b5f365f32104d2d6a2c1e3362555155747a4b4d376d55745562, 0x3b665c505132567c28512d561e335a316d223371496e4d277b5b6276616a505b, 0x2d163d4d203d0a1d4d180a56235a362b2b1e222732453a0e242918231f2b1e30, 0x3153316127295a55175b77455b515f29552017703a185a4d555f49513055622d, 0x555a282d641f6424535b7c33552d533655292c642d3153755351673a281f355f, 0x2c644d5a4d1f690e2d3153315c5f5b5c53537661515f5a625f554928532c645f, 0x2b2c4d4d271e3a51305d5553203322356131696a5f6158] (by decide +kernel)

private theorem ok_b1010110 : Impossible board_b1010110 :=
  fork 96 ok_b10101100 ok_b10101101

private theorem ok_b101011 : Impossible board_b101011 :=
  fork 52 ok_b1010110 ok_b1010111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1010101 : Impossible board_b1010101 :=
  kernelLeaf board_b1010101 #[0x3b2c262d5b2a372b375a4b27455a4b4b23302024246424562c167018222d3429, 0x3025285a5a5f5b452d2435161d193a155b5b3a154d242d5a2d556e602d50512f, 0x551f621c555f302c5f5a652d605f3b555f1b16242d5b212a5a682a1c2f3a1f28, 0x12192650614d1d3712341d3b1d5d152f1d1f635f521d5d092f352d5b242a2f1c, 0x562d7a17372a554d60302c374b2f281470641f30172f351e3b1e131d12341419, 0x2d3a64615f685f2d6555775f515535555f536923412f362353372a514a455f53, 0x524535532b1a18526a25412f415551362f453a2d5651372d6756672b565f536d, 0x703767373767614d2d23302c2a373a4d4d26372313342d51525f282d1f301427, 0x1d3023352234344d2f303a2c2d5b1f232b5d232f07362b1a362f45641e2f3461, 0x6963376051273037362f2f231e15283035362a101e3036273a22272828196414, 0x64282b1c2f3677645737250e0d1555623763344d2d342d58632330364d342d53, 0x533160223656124d342d35232327492f223630563130582a3731741c511a3523, 0x23302a37362a50603761] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1010100 : Impossible board_b1010100 :=
  kernelLeaf board_b1010100 #[0x345d553074705b746c1c4157222a56681f0f5560576c2d20142112122a642c62, 0x452d2236242915355f5b601408552f2d29342d14362d3420551d572a22676f34, 0x36242f6456515664242d6422293451515a55642a502d136f2920311c5a143417, 0x2d2b2a1e1d1964362a201c3620274157315d2d6664556e3129553565615a7027, 0x276819555a1c654151174f41515a644157776160555161505a702a19582a5051, 0x68563466565d1224611e3461565a25122d516458612f55505a61576155505715, 0x2f342934] (by decide +kernel)

private theorem ok_b101010 : Impossible board_b101010 :=
  fork 51 ok_b1010100 ok_b1010101

private theorem ok_b10101 : Impossible board_b10101 :=
  fork 64 ok_b101010 ok_b101011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1010011 : Impossible board_b1010011 :=
  kernelLeaf board_b1010011 #[0x22362c35242d3268353d2d312d7c6e2b365b2d72223d1b230c35243632285c57, 0x28367519313661811a613140791f35316d497736493568100f313f5f642c2d34, 0x40615f6631312033652761365d68362d316d7479316e40353d40363177615337, 0x366d2664262a3c4f5d53782d695d492d6931745d5f495f6833685d5335407433, 0x2c262d6e515b4f4f614f6961312d415f64282d36322d3d312d5f6969725c2d64, 0x15353d6151363236726131782c12725141692d2d2d6e2d6d3f61352d66603b31, 0x632d3b62515b2d4b5c496f3162362831495f6d324b49315c4b327062635d5251, 0x73323b695b2d5c51362d324933414b32312d495f33733765632d657236695169, 0x2c31262d3b625d2c1517283236343370411e69693141102c3b613470] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1010010 : Impossible board_b1010010 :=
  kernelLeaf board_b1010010 #[0x223636405d37214f352a3215362b2d285f2d5d185d202a614f35182a2d284131, 0x3227415d5332681c7853785d3c285b495762653d6d53772c65576d532d61642c, 0x2a3628643d122d5d37403b286f685d773f5f281f655f645b36492a3240372a63, 0x324f361f362d286461352336356d35275c5d7036653625361032353220355761, 0x615f682c4b7e6836123668362a212868366d6f57642a1128364b656f6a6f7866, 0x40] (by decide +kernel)

private theorem ok_b101001 : Impossible board_b101001 :=
  fork 86 ok_b1010010 ok_b1010011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b101000 : Impossible board_b101000 :=
  kernelLeaf board_b101000 #[0x56515d37696549283147312d513341325c25366b324f753141687549315d5f63, 0x1c612d41695d2549573669497a496f154f472d2a3c267a49757657315d5f684f, 0x5f65565f36662c2d65325c5d69316a5d5f4f761c36325157] (by decide +kernel)

private theorem ok_b10100 : Impossible board_b10100 :=
  fork 88 ok_b101000 ok_b101001

private theorem ok_b1010 : Impossible board_b1010 :=
  fork 76 ok_b10100 ok_b10101

private theorem ok_b101 : Impossible board_b101 :=
  fork 78 ok_b1010 ok_b1011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b100111111 : Impossible board_b100111111 :=
  kernelLeaf board_b100111111 #[0x2235512d462a4f5a35330f35330f1031351d352b1461454a5645646c2a2e5020, 0x2d4b332a2d292d352b223335354535333535561d355b6e4e336433356e4b3512, 0x512d372e2b622d0f2b221453313121644e352926565e5d4e412b3d2d6f5f3762, 0x6718522d59622d684b3335352d371415222d33373335252614332d182e2b4e2d, 0x3d5f294726334e37582a25471d0c22412d355137373f317c637a4a592b1b5241, 0xf253d2b104b22365f6626644d594e7a26260f293757685e6235354b3d314e18, 0x272737353f1b41526341586233262b5831374b26273d] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b100111110 : Impossible board_b100111110 :=
  kernelLeaf board_b100111110 #[0x2a2d1a0c2d4c2b5d6e212d1d10582b514f2d2b5f4c4162516041532d475e2236, 0x215933274e2d52164d273131704f642a1c206610254e624d60521241574d2d1d, 0x1a21104d5e4c581c2b4c58252b3b4c31232b571e1a14082b4c2a252f41581c26, 0x2b1d331d4d4c565e4f6f711d53212f4f163f312e1a4d2f174c211a58101f5d0b, 0x3b2f1821254d0f3f1a0d16050c62004d62220f1a11252d18264d102d6218262d, 0x292059147a4b1c734c6222332626213f29475d2d534d1d5121291d45271a5318, 0x270a1c62582f274d255e29514d77471c51465a5118215e595e5d145d6659587a, 0xf211c29711d2f102b311c294f51514c3b2f271829182f72252747184b29252b, 0x29452b1e1f372f3b5d211a581c1a] (by decide +kernel)

private theorem ok_b10011111 : Impossible board_b10011111 :=
  fork 60 ok_b100111110 ok_b100111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b10011110 : Impossible board_b10011110 :=
  kernelLeaf board_b10011110 #[0x41472631474147373141332a52475a62104d3551374721744d4d624e562d2036, 0x1d351515253141414b41272f31314d4f47470f37516e2a261c4e56414e171127, 0x2d512131375e5e5d4d4f5f4726102b4d2b614d2b351e251f1a4d551961411d2a, 0x7462262b1f1f142f2d4b2b352d1e1722332b1f1a2a2f5f6e5f4d667a2a644c31, 0x19211f35661f3319212f7a35704e1e15411f232d2263315e1a5f31415e521541, 0x4e4b1919171d0f5a1a2b59474e5f4f581c332a33352d231d23071f2b27412b57, 0x2f251f412b1e3a29222f104b5b59416f4f472b201e294b742f5550784c622f6c, 0x47512d2f45232d181c2d4b2f3a1c294c1c594b2f4d6e4d512f295529104e2d37, 0x105f4d4b475c5137351e5131294d4b5c513729134c2245355e4d512e3a182d26, 0x2d221412253a252714213a22614d45352d182e2e374b27512f47103757453551, 0x4b2d18605f2d1d29661e331a3321351b22622d335320332020222d1435233a22, 0x29294e2d35145b4b2d2f4b504f291c2d1427] (by decide +kernel)

private theorem ok_b1001111 : Impossible board_b1001111 :=
  fork 64 ok_b10011110 ok_b10011111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b100111011 : Impossible board_b100111011 :=
  kernelLeaf board_b100111011 #[0x451825333d501c2a454d671d1d0f182d71103722212a2514710e2b0f594b352e, 0xe211d2d5d3337183722644a4a6c2f10141d112d331b5b501021231f18501d2d, 0x2d76262d2d202f3f211d100717262137142b11640718214d11100b1326101047, 0x18162d5d27291d133721132a1d1f332650143f1d1d21262d375921162d111425, 0x5b351c2a4b2f135a4d190c0f1d132164640b13195d105251131e2d371d292d5d, 0x194b25375f172b375064194d5045141b4b224e101d644c35451f2b4b2d2b1f1f, 0x2d37131d500f29660c645019220f0c1f190b0c40372917456e1004190e1a2b33, 0x1c452b55414e1f2f19201421] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b100111010 : Impossible board_b100111010 :=
  kernelLeaf board_b100111010 #[0x1d2e2b10141d182a6f1855192222291e1a1a525f4b18116857004a6f4d2d3335, 0x641d5e5a184b5b531a3b64604d232b4b2d2d4b4b615b641f5b2d4e2d2b4b6045, 0x68522d110f274b2a37272a6d591d4555571e4d263710516755465170602d2933, 0x213b102b4f4d45092b1d16212d4b232e0b182d2122275d112d1a61372e5a6f61, 0x4e404d294d4b4d1e195c22024e1d4b3b513b17374b09531367075a102d1d2d21, 0x5351] (by decide +kernel)

private theorem ok_b10011101 : Impossible board_b10011101 :=
  fork 58 ok_b100111010 ok_b100111011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b10011100 : Impossible board_b10011100 :=
  kernelLeaf board_b10011100 #[0x1a11191a55256060551e0915234c4c1959170f68104b35111435601e5f233d2b, 0x2137531c2522352a5d4c3722231f354e154e1f37401c26413b373b1e252f231e, 0x4d6452414e60334c5633415f642541173b21470d10192137265d23254c51] (by decide +kernel)

private theorem ok_b1001110 : Impossible board_b1001110 :=
  fork 54 ok_b10011100 ok_b10011101

private theorem ok_b100111 : Impossible board_b100111 :=
  fork 36 ok_b1001110 ok_b1001111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1001101 : Impossible board_b1001101 :=
  kernelLeaf board_b1001101 #[0x4b47535119242655525d4b5e4d5346513a4d4a1d221f6160136f614d4b3f2d37, 0x314a4a274a590c594e4d4b293f4c223c18240d104652584d1d1d511d1947101d, 0x101d1c1f41514c511c10411b1f51242536413c4e411f36514d4b276b1f53252e, 0x41212b21413d3b252d101f361b5967243a4d4e254b291b5317161f25263c2423, 0x4b2b3d25172a06641c637e4a521e41061e110a1c4e522d4c2d3d4a1658244758, 0x293c2b2321512d3d31214e2d2b192425212d4a520a5819065541571c21112362, 0x464521184e19252d514b3f21163d4e1646514e2d1f3a2f5d512d3f18212b5b4e, 0x4d4a245f4521213f2b23274b253c217051] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1001100 : Impossible board_b1001100 :=
  kernelLeaf board_b1001100 #[0x73592e5920526c58416f4e2e4b4f574d2e4b193c2b2069694d1c63184c585e62, 0x182d41634d59684c631b142119451e3d5859551b411f4a554c0e211f4d37182d, 0x7e5d5d5f746e520c0a0a554e172a582279584d586f584c4c554e3f4d1d31211f, 0x4d601473215f57132f673f2d1e2d1b1d21134f4d74216e6060267b4a6c5f6076, 0x212d1e1d1b6846605b4a0c4d763c3f56782a5f55686760524e7a5e7a66472d6e, 0x604d4e5f47745852454b3c1e1d0a0c5e0a19476008193c1e702d21463c265d37, 0x581c2a4541605f4d6f605f554e5c5e5c5c212b206c5d0f2b1647806e26644d5f, 0x16677a18765f6e46581f581f181d3126311061101020644e1929193d74555146, 0x5f1e206416721e603f18466c46376e3d6c18762e261d26106c2d6b6e64412d7a] (by decide +kernel)

private theorem ok_b100110 : Impossible board_b100110 :=
  fork 51 ok_b1001100 ok_b1001101

private theorem ok_b10011 : Impossible board_b10011 :=
  fork 44 ok_b100110 ok_b100111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1001011 : Impossible board_b1001011 :=
  kernelLeaf board_b1001011 #[0x671d461c26221e4e594b2435500e1e51452f3c3c3c5d26511551204c2b1a313f, 0x26212b1a2331362327242422212223352e21272c1e231e1a4c1d24452b554b2c, 0x5119244a47511526584f21412f5523241c1e15212b3c201a1e212b41263d2121, 0x4d554e2953474c45671b4b4c2153474c62122e4f5a2b3c41373727233d62584f, 0x272321372e181a1e4f102e21451608212645272f41314d4d6b51474158575f31, 0x532f2b5f2f4b6e0d6e1a15515072602f1e503a3d174b353b53642b1924451d27, 0x1f1e2b2f7e124b3a4660272927296f274b0f2e29602c2f2c1f271e2f4651212b, 0x4d294d5b194e3d3b2f5150204e3d1d1d4b0f2e] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1001010 : Impossible board_b1001010 :=
  kernelLeaf board_b1001010 #[0x1d274e2229272e264d3c6260454a1d27114e1e3d262f1d1522511d552419293a, 0x2c18415a1d31264c41552c1d5a27554d5a2b1e18296961592641474c554e1c0f, 0x313c294a2b1a585a512c2029601d2721291837262c2b58262c2b5958267b0c21, 0xf1e202b2f4d2b4d032e180a1d21271c517824202b4d61265d274d1e2626294a, 0x41580c415d2655314147191924366f2b4a561d6f4d5b5551263f1e402e241e21, 0x59661e6e582c3c263f7a223727292419191a580a68181924416c5d214d37227a, 0x55295f191b2450204e2c21564e604d4e406e5d726e08184d08130d4f6e0a216b, 0x82e1a161d0d2e1a2c1d0c1d2e6e2c0a5d21212e372c3f2f3c711d2c1d660f71, 0x4d2b4d3c29584d2b265d7a29665070665658474c7066564e172956504c4d582c, 0x594b4d2b24265d1e2b4f662f3c263f4520191c2b5b4610262f] (by decide +kernel)

private theorem ok_b100101 : Impossible board_b100101 :=
  fork 51 ok_b1001010 ok_b1001011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1001001 : Impossible board_b1001001 :=
  kernelLeaf board_b1001001 #[0x4b35562b6c5a0819294d514e601d1d101e1321644e2768184b23164a181a3a24, 0x5051451833131d4d6e45721a6e410d5557576c5d1a2b334a5b454d5d514d515d, 0x4d102b335a201e46575f4d517f454d644c1e3f5c201d64102f3d1e4e334d135e, 0x5f6256102133163d2b1060410d3d1b2b21536212310d2147312b2b6e721a511a, 0x331d582c13232f16111d332f13021f0d1a18571d51624c1d67514c4d1a4b3d4c, 0x2b411220364e1f27554e1f35314c10150e581a2b534e3d3a234523131a31331d, 0x33231621181516272b211d294c1b215d10290f160d1b1d1b62102c5335101f4b, 0x813213a0e46233a210a182c314d233f1a3333164d1a362c0d29352e0d194d11, 0xc234d101d2b211d101a27111f5d4d5d101d3321181d58273a231d10] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1001000 : Impossible board_b1001000 :=
  kernelLeaf board_b1001000 #[0x8133c111870400c2940182e214b4d50515860454b605f0c50675c4e70505b3a, 0x1629402f1105331257130b4d29661a18291212240f1a292c12080b2929400d4d, 0x5d4c610d3f1a244d50451f2f4e1929193724564e4b3529081a764e412913164b, 0x242f1e2c2004154d3c1d0a702e4b5f725b2c1d4c120b190a0a1833247008564b, 0x20] (by decide +kernel)

private theorem ok_b100100 : Impossible board_b100100 :=
  fork 34 ok_b1001000 ok_b1001001

private theorem ok_b10010 : Impossible board_b10010 :=
  fork 45 ok_b100100 ok_b100101

private theorem ok_b1001 : Impossible board_b1001 :=
  fork 52 ok_b10010 ok_b10011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b100011111 : Impossible board_b100011111 :=
  kernelLeaf board_b100011111 #[0x5a311e525f5a554b4d4d2c55554e344d1a4d4b416445614b4e5c344a1850552f, 0x554a1a4a5d214f7167254b3564194f455c4e521e5f6e55296327643c581a5518, 0x2613] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b100011110 : Impossible board_b100011110 :=
  kernelLeaf board_b100011110 #[0x245c631b2b414b1f645a632a1b292c33554d6157355c4b62273a416461504e6f, 0x1a31293a50465e4153675e50356855191829715727415c4f2169252419133529, 0x671a3a4b5a66295a3b553a5569584b2b3a14251641635e4d534f5c584e743453, 0x160a21693b1629556241636929555a4f611a5c4133294f13635e1835252b415f, 0x3b2d696e63526c191a4e3a697a6e5264355a14245345243a6767192e3a5e1e3a, 0x34455a535f355c4b46502134410f293a5f25645345673a165f525c19275f3a4e, 0x4b2d534e4b2b21592d4f575c271a0715094e5f4b1106135a086c4161255f6453, 0x200f2e0e41291b3429681c173b6e2b203b111e2d5c29332a1f311e29575c4e3a, 0x294f1664675f4b2a171c5c62294e2110274b2d3345203b2b253b173b2a554b63, 0x5f644b6c3b2b574b633141292c2a2d574e0b2d5c291f362d2535332c0b16621e, 0x2020254b632c62525c2962631620202719294e] (by decide +kernel)

private theorem ok_b10001111 : Impossible board_b10001111 :=
  fork 61 ok_b100011110 ok_b100011111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b10001110 : Impossible board_b10001110 :=
  kernelLeaf board_b10001110 #[0x2d1a34555f693d766150641b7d3a6967725f3a5f3b672d69457e3a3472615c4e, 0x6c59685e6834764a6855696c3d525c4b5f6e556e45692d532d551a455f66713a, 0x5c244a636135244163684a18416350642d6c3a3345405f353f6e64193a1f4668, 0x34235a523b41635d55335545552d1f0f6e5955664171343a52683a72503a6614, 0x35673d3d275952462f25713a291f4171261a5550551f08] (by decide +kernel)

private theorem ok_b1000111 : Impossible board_b1000111 :=
  fork 91 ok_b10001110 ok_b10001111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b1000110 : Impossible board_b1000110 :=
  kernelLeaf board_b1000110 #[0x36663d646d7c6e5f4d6333677e3446594a531a342d2327364f291e4e203d4131, 0x235b631a584a41555c335f4f1a4d242f414a29341e15202d1e2d5c524f695a2d, 0x20231a76274a1553647a5d2718234d1a1a1e766853647a5d69112d10232d5315, 0x2d24241e522c2d3d1f2c3d411c364f2e4d25550f4d62551825264157333d5b23, 0x2a55293d5d4d211e21162064521a2d2b594d4029631f23294a231b52102d2e3b, 0x25412e5d2d53412f4f5f2567182e4d4f293d] (by decide +kernel)

private theorem ok_b100011 : Impossible board_b100011 :=
  fork 71 ok_b1000110 ok_b1000111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b100010 : Impossible board_b100010 :=
  kernelLeaf board_b100010 #[0x231e2d40362946414673253c2e26331e6b291f2d2e69692d313b596855623447, 0x4b2c2d62415e3a67505e525d4b6e692d5e63245e692d3a2941404d2f62182d31, 0x3b6855084b5d3a3a34416376695e745516624f5e2a5368663a2459463d52415d, 0x6c5c522c08615533553a166263594b24216d55665d686b3b6c615a4b63522334, 0x620824191a3a1f342f5c62693c5c503b3a5c696162553a33242755615233] (by decide +kernel)

private theorem ok_b10001 : Impossible board_b10001 :=
  fork 81 ok_b100010 ok_b100011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b10000 : Impossible board_b10000 :=
  kernelLeaf board_b10000 #[0x585d692d503b72241850242d52722d255b2d6d122d69451f57290e3b2b1e3a4a, 0x1e7b716976673f6d635562344d1e1059415d575b50331f46186163242e352e45, 0x402a5d5571525e6b595d646e2924647a31292d64163b64246b596f5d64726e1a, 0x2b102e3b251e2b47362d3d3627333331352b331f40102e3b4b33721a4b3b232e, 0x35332d5f1a2d3d412d21332d1f2f3a4b47556e501a1a2e5218102e3523105d47, 0x51555247551f4127292b45676e1a34620e5f672433242e2529346220250f2e18, 0x34117a5d2d6e7071581023342d1a6441537373676673331f3b6e58511e316946, 0x5b451f2f3a3d536818763a3340332f3a6876525f685f6d2c337362554e3b3b5f, 0x352a183a763a245b59511852466e3a1a2d5f6471761e3d505b1e2d232d1a3a69, 0x533b5c6e3c6255241e3464535e2434721a50242427352e31] (by decide +kernel)

private theorem ok_b1000 : Impossible board_b1000 :=
  fork 96 ok_b10000 ok_b10001

private theorem ok_b100 : Impossible board_b100 :=
  fork 48 ok_b1000 ok_b1001

private theorem ok_b10 : Impossible board_b10 :=
  fork 84 ok_b100 ok_b101

private theorem ok_b1 : Impossible board_b1 :=
  fork 62 ok_b10 ok_b11

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b011111111 : Impossible board_b011111111 :=
  kernelLeaf board_b011111111 #[0x2a2c2c35682a2c3760491d2e2b2c2c1b2b2741336f26635f185d2f652a2c4d4b, 0x2a2f1d302e372f5d645a5e242b2f541d4d2969333d32321d295a4f3f21643d68, 0x2521491b184d3718472732515e655a2821271d324f5525594f57491d284d5433, 0x5949374d] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b01111111011 : Impossible board_b01111111011 :=
  kernelLeaf board_b01111111011 #[0x2c16243a282a452b1c36490f29355a1d4d63272a604d492c2b2a2b283667644b, 0x163a245a1c365a5c411c364f347124452b28366c352b34353f2b20572a572c2a, 0x762c554d344d34766d4d632c6760121f493a1460282a2a351d1c232c4919122c, 0x55722a6a28367012243a27345a68152445283a3a34222449453a6259702e7f3a, 0x6b2f5e333a5a5145675a3d3427632435492f2428452b28363418123a28766c3a, 0x2a28595822250f5c1d1e662f552e31284d2a35362863636c285c611f645a4f62, 0x19192b1d376055606022242b64575e6b225136493171662f665c5c64286d2260, 0x511e64595a3f515e1c2b5a2857225c2b731c5a2b5a1735285764364f294d5f2a, 0x605e582a5a362b5a63641e24600a2a5e6759373f3a] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b01111111010 : Impossible board_b01111111010 :=
  kernelLeaf board_b01111111010 #[0x1f6962355f492b27305d112b3d6433551f30232b4163636871722635655c4b36, 0x514733283f2b2868245a4d3060641d282b2c512c605d2857492c567833675a49, 0x30285a5c3131317228574131745d53595a644141412753653d31136460625730, 0x4f555123575c3d29183d5c4d214d1463275c5c5c6468551463602c4b30415a51, 0x273f244d6357122b105c18262b374b123a4b5d24336f2e4f5c684f5c183f5a4f, 0x33223f142c3a224b64332f] (by decide +kernel)

private theorem ok_b0111111101 : Impossible board_b0111111101 :=
  fork 82 ok_b01111111010 ok_b01111111011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b0111111100 : Impossible board_b0111111100 :=
  kernelLeaf board_b0111111100 #[0x64565f417f6d615f59646f61636159731f2b5a55195f6f415126352b57623a4b, 0x746c5a61745b122c647a665f5a63825b274d51672c161f2c142a171f122c1624, 0x57522f2435762c2b4d222124592f353f34636c6b5a3568515b66592c57781861, 0x5759306f2612126f62572a642e60624d62635b33415f555c73262b7469736762, 0x2c252c555958525d293f261d293a33374d59372945621f2718226c5a621a272b, 0x220f1d6f2721520f146b272b2b5122276b2b605f58332b2b5e161b183a30415e, 0x4f5a5e30362b3f315f33633a21332734333a6f2666332a33296e551e2a263127, 0x2f3d696255745a4730242474455f23352a2727263116311e622016255e3d3041, 0x5c33265f6e692c36342f62551e35315130353f24454530685c30645d6e6b7845, 0x3126305147623536265d6f646b367f7147695e5f253126241f3a2f272f24345c, 0x582e233a2f62552731413d41303d2b312658413330523158222a316c172633] (by decide +kernel)

private theorem ok_b011111110 : Impossible board_b011111110 :=
  fork 84 ok_b0111111100 ok_b0111111101

private theorem ok_b01111111 : Impossible board_b01111111 :=
  fork 62 ok_b011111110 ok_b011111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b0111111011 : Impossible board_b0111111011 :=
  kernelLeaf board_b0111111011 #[0x5d6e667368265b2c366671601d5d654d325a1839411f415d72393f5a365c4b52, 0x5d5c73263a2a2932745e3f4d5f316d6826602a263662112b3a685d2b6065412a, 0x51362b29515a3f2c2a2628395c2b59262b395a113328352a41364f2b325d3232, 0x1f105c200c624b362b251832672b213a5e416562573135415f352741535a0c21, 0x625f39556b575a4f665e1d5d452b226e695e41514d555719272b4d4d49595a2a, 0x453e47531e2f3e4f4b5a2a3132575145252f333e192a55492a51456a60453257, 0x51333e5c4b29334b4d5a293f1e3234624b2f1f59335d4d37454d4b2c3a4f4f2f, 0x33291e4d4f3329332b4b66374d3f452c24515a215734341c594f225a272c471e, 0x20204f] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b0111111010 : Impossible board_b0111111010 :=
  kernelLeaf board_b0111111010 #[0x6a612233616a626a2e3f5a3e2a330e451d5f3a596b3e2b41522b2a212f3a4d4b, 0x523f2a2f55282741364d2f45623a5f6d333626316241495149613f4955455c74, 0x5771174162362f35451e66282f665559333a49242935281e662b2f3a2f5f3729, 0x5f6b16335c626c53392853392a262b12416257364f2a535559662a6f5528330d, 0x2952395a5c2f3e4535623a5c29295f1e3e3339333f53695d5f5a64205a552010, 0x2631412f3527314153212b5122273659362b2a282b5e523347352e5553352e15, 0x3a335a34592e3e3153] (by decide +kernel)

private theorem ok_b011111101 : Impossible board_b011111101 :=
  fork 84 ok_b0111111010 ok_b0111111011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b011111100 : Impossible board_b011111100 :=
  kernelLeaf board_b011111100 #[0x6458716528603664325133542f5d2f642e33321e66332c622f5c662260554945, 0x603f29575a4f2728653a176458313271265837262c5a23272e1c600c36323f51, 0x351f273f64322c26272624376e6458633a535f28543f29362f283f6418326557, 0x392954552832332b1254642f243f6255313173315457412b6151535164323649, 0x332835362b546827602b226429321e5d262c5d32373f4d24322b322928555426, 0x22285735331828601e2e2b26393f2b182351412b3918235c222e2b17572b1f11, 0x272e5a59295a2e1e352b321151321851342954] (by decide +kernel)

private theorem ok_b01111110 : Impossible board_b01111110 :=
  fork 86 ok_b011111100 ok_b011111101

private theorem ok_b0111111 : Impossible board_b0111111 :=
  fork 64 ok_b01111110 ok_b01111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b01111101111 : Impossible board_b01111101111 :=
  kernelLeaf board_b01111101111 #[0x286c5f2f3d2e2126632f71225f284914351b712f29634b1d5b634b394556662a, 0x3f265e3f5368532c1462523f2b4b414b624b6b5d5b394b29293937632c4b5d71, 0x2f1332263f6356456c395d39532f3f53746c572b51274d2c3f222c5d574b3e28, 0x57584f62375e3e37563f37575d265e32593f5f7d35643209626a593332255f5d, 0x591626595e133e3e49355657175e322856571753175e326759591f78565d3937, 0x4b49513e417c6b3f58634f5d392158634b2b494b28564b2b5640375645493262, 0x4163455d63633732655d594b6a56125145685d34346a634b5658516451415d53, 0x16521a783f454165785d565e573f2e685257412b5d1f5d5d590d574b5765785d, 0x454b37164565782c184b68565d6852675d4b1b344b2b636a565959655d513253, 0x411d3139493f4b223f745e2e6329265758272141636251334d3f3e5664524b65, 0x4b273f2c45336212397c3b7c374521673f6172125b] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b01111101110 : Impossible board_b01111101110 :=
  kernelLeaf board_b01111101110 #[0x2522596e266a635d63802257326e512e311a3227645e3f2e4b7251576e376652, 0x202b2b3969512522252f595122255745166c5e3251264b6e7e2e5d372e7a6459, 0x45495c3b59496e221651295d39576345721945101e57391b1751274d1959450a, 0x455121375c67782b6c51415916514b594f76535d594b3b4f1e72295739295763] (by decide +kernel)

private theorem ok_b0111110111 : Impossible board_b0111110111 :=
  fork 48 ok_b01111101110 ok_b01111101111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b0111110110 : Impossible board_b0111110110 :=
  kernelLeaf board_b0111110110 #[0x632629162652212235514b222c5d525d514759636226261d2a2b592b3541333e, 0x1b41492833695e41395f4b2a522b6457355f662b592662412b27514d3f315225, 0x5d5f5e7a1833477a3b165f4d5947374b6e30266447623726784d642662592b64, 0x592b634b2a564d23281759392c30232b30234b391241222e2e373f63312b101d, 0x1b35355f281d45335735343541391d2b1d2c2b2b22571d352235711d35342b1b, 0x6a49753f122825333331410d3331121d1e6226275f2927372749594159733721, 0x3f594b39622b2b2c213112161b2933275d59635d7684781e0a5d4b272c4b3f12, 0x3f453063374b66724b222f404b274945] (by decide +kernel)

private theorem ok_b011111011 : Impossible board_b011111011 :=
  fork 84 ok_b0111110110 ok_b0111110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b0111110101 : Impossible board_b0111110101 :=
  kernelLeaf board_b0111110101 #[0x3b4f411257575b1e393057234035651e391e1f4f40352340515c524f2b4d3f2e, 0x2b281f411f281b41211235392725471e47235d5965570e5c4b59225d5c2b5122, 0x3559565d633451315641660c315d261d412b264527541d59224156141f112141, 0x33261e581159571e22253967592527225c695139251f2627574139223330325d, 0x1d1e292b0c542b2b072b5d4b27314b0f251e3318562657332b7239624b0e5e10, 0x5d541d284d3f2b194527311b0f201b207f28334521312b273331675d34133363, 0x4133293312593067415e5d41183533351935222225303118334b4b0f30] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b0111110100 : Impossible board_b0111110100 :=
  kernelLeaf board_b0111110100 #[0x6332454d614f2f2f23453f7065350a6c141d59596c105434272b10343f1f3956, 0x61706751304b394f62596235282b35576565705962356a5962705d4b2f352f64, 0x2339225f54335735636a39526d6b655151214554304d5d746d342e5d6c6d7539, 0x192635262b6739392e452f212e22301f2b6b4d27121f331d265d6133616a5e27, 0x21513d183f52744545213f3d7a6b4d654727153922395e0a2635275e0a22395e, 0x3245513f584547651e3f273063523f1f6a300c136a0e2019046a3d6c10264545, 0x1f6b3565395b4b4065513970624b4f5d335d5f4b614b6d6254416c1e2252333f, 0x3d3322303021] (by decide +kernel)

private theorem ok_b011111010 : Impossible board_b011111010 :=
  fork 42 ok_b0111110100 ok_b0111110101

private theorem ok_b01111101 : Impossible board_b01111101 :=
  fork 90 ok_b011111010 ok_b011111011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b01111100111 : Impossible board_b01111100111 :=
  kernelLeaf board_b01111100111 #[0x25566c6a590f26215731315c3557666c3f1231596a2f1d5d56695e5a58455f23, 0x180f1c2e2a12566a52645d57253f223f262b4f192625252b2a3d215d215a5617, 0x647965665767353965573f2f6b5b727b7d7067595d56525d2b595d5a5d3f1817, 0x1d30103f0f2f25305810335d31262b25306a570d5d7a5c39672b39303b391c0a, 0x82f3f082f3f6e1f5d212f3f27311d513b184d08] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b01111100110 : Impossible board_b01111100110 :=
  kernelLeaf board_b01111100110 #[0x1c2b33351f1d172517154d5d170e101725216c1b2b5d0b352115451b33265a5f, 0xa561e316166651209171b0a312b173112161d2a3523571735582b3b2b214521, 0x1c2b5a58495d2a2a6635235254591d786a5d3512265d404966451d5d5214647a, 0x1d3b2a14561526352a2615101d14210e641f2714210e0308113311080c151b26, 0x351c1b21157308351f630f5d21472659213557337814176759264d5d52171d26, 0x524d353f171e21390c1f15351c5617350a101f2a25215835265d31591c0e210f, 0x3326735c7a3f51591678150e151d102672545d7a26591f35683f5154596b122b, 0x101b573f39171926211f3512595117337859331939331f3535596b5c3f123535, 0x3d175c57727a5d745d572a53666c5761531d4957171035171f23122a565d3533, 0x536c312a6a57573157725431] (by decide +kernel)

private theorem ok_b0111110011 : Impossible board_b0111110011 :=
  fork 40 ok_b01111100110 ok_b01111100111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b0111110010 : Impossible board_b0111110010 :=
  kernelLeaf board_b0111110010 #[0xc235c235919101c703d692b594f45310b11081c516a4d10254d456c335d265a, 0x316965591f5d2b2239112f574d101e6a112225301151153d673d305f706e4d58, 0x45236c61112559496e26491c7059862a6c645756114d1c255751033d67525964, 0x1e1b681c532b25251f11305972142b39302b25166c575e6c6b706b7078266a5d, 0x59695c825964517859695d4f4525302572535c7808490c5949786e4d58596951, 0x70576a517a301c64] (by decide +kernel)

private theorem ok_b011111001 : Impossible board_b011111001 :=
  fork 50 ok_b0111110010 ok_b0111110011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b011111000 : Impossible board_b011111000 :=
  kernelLeaf board_b011111000 #[0x2a232b265f717b65085735642a6a2f1d3222652b4956655f355f4f70565d5a59, 0x394f192b222b182b2623115d2b1c2e23122835655c2b221d576a353139312658, 0x5a4f355d7326095d31331b45235d5d6908355763565230300c2745282c56672b, 0x575a355b3965222f2a1d28355b1d2a6b2f5d287135326c6a326d5f49561b5f56, 0x637158453123262f19353572311d6772082b5d66701c5d2b5b725d2b3571191e, 0x5735547a546768635d6a525f396d713526] (by decide +kernel)

private theorem ok_b01111100 : Impossible board_b01111100 :=
  fork 75 ok_b011111000 ok_b011111001

private theorem ok_b0111110 : Impossible board_b0111110 :=
  fork 54 ok_b01111100 ok_b01111101

private theorem ok_b011111 : Impossible board_b011111 :=
  fork 76 ok_b0111110 ok_b0111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b01111011111 : Impossible board_b01111011111 :=
  kernelLeaf board_b01111011111 #[0x627066551a2929555855656759355a28554749255a755f305e4f605929325733, 0x49283e1822212955294959291d5925546e21554c29552122355a1e3a595d315f, 0x291834552a59294937243a2916213466555d6368595d2411645966667463557b, 0x5929164921351f7a5d296359636f22736a352f6f1f582f493a551e472163594d, 0x5a1f2f5d1522581f25492e376a223a6c2f21551e6618353a342959596e0e1822, 0x3a35573e685d5b2e552349494757256a635725492155372a4963494737473558, 0x1f292722182f4921473b315f622b] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b01111011110 : Impossible board_b01111011110 :=
  kernelLeaf board_b01111011110 #[0x1c2b1b5d2b273231621c30331e5833142868581e1e2b1c0e65174c14285a3557, 0x5a55141b5f321d2b1c2b583055255370496a52234c615a5f49581c581c175d25, 0x5514283323212f252e1e6c581b3365351f252b28214d142b142814282b213d3b, 0x2b2e5f4f234c642b231b336518645b330e2a1c32475d59321165282b3d63241b, 0x6a16352e6c1927303b282b5d2e2c19304955172b475d1b24251b2b2831274d33, 0x21316e592a2b142a532b3b256f21536f2b593352716f1f2b477b493b5f282825, 0x2b2b] (by decide +kernel)

private theorem ok_b0111101111 : Impossible board_b0111101111 :=
  fork 54 ok_b01111011110 ok_b01111011111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b0111101110 : Impossible board_b0111101110 :=
  kernelLeaf board_b0111101110 #[0x3b5e6c5d58302912352e355629356c356435352958556630585857214c1f1e5a, 0x532e2e2127224f1c293530595557583155273d3522292e65112731214f2e4c30, 0x10532b1a24346623596553254c30336f5570304f691729304c53401513582457, 0x3417531c2436304012221a121c3022112a574c300857351f5364083513171413, 0x32545d275d36696b2b2a2a276f552a34251a2a5e533129646517532a0c563417, 0x191f17362530325d172a30532a685d1a3635276b292934531c2429592a1f2530, 0x64665f236427556b72792723253b6617524953231e24251c1f5223242349490e, 0x36122b1e342c343422302a2a3119311614362b2c342a5760171c30246a725260, 0x6a633427532b366b36534f351c5e643635581e34342c6d30573b1e1f300b2130, 0x235e5e25306e495e3024536652686e3060253053365265605f69253672583257, 0x36583658622c49562c09592c7e12521f581c36256f5552536566162c5356245f, 0x3b6b74615f596158617b6a6b59553b220c2a34754753695f2361] (by decide +kernel)

private theorem ok_b011110111 : Impossible board_b011110111 :=
  fork 57 ok_b0111101110 ok_b0111101111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b011110110 : Impossible board_b011110110 :=
  kernelLeaf board_b011110110 #[0x631d2c64595449596164641d5a59541b2c403332251b22222c3318321d604d37, 0x532c57605316615260521629541e2a2e646b5a5659355f5e571d5260566d6b60, 0x604d32321156752a675a0c565a212e546d0d1e5227542c12331d562c30251e29, 0x5d293d293d11286b591d2a1f2b741e11293d645a2b226c595a1d4f655f6c5929, 0x1919236c1818591e1c64185a293d2929222339536c29565659296464102b221d, 0x63701c5a64593d565f591d68596664635b3d602b6459233964495d526460655a, 0x605929595f362f1d5d600c2a5a605a64055929591e0c2922233960295b635a60, 0x584f5d5972536036405a6552362b63584d595d527458694964283d5a3d645a58, 0x54584c36525269495d5354634d53364c654035575a5d5d3d53665d5a4d35252a, 0x2f565d2e4c6d586039185d3052492e1d2a563d2f2e35402b304c571f19395a23, 0x561f39602b1539576077242c2f3d602f546c592c39571857602b2139602b2e5d, 0x1c35252f10252a2f29221d33222935404f3025572730306629112a0e4f59646c, 0x1f212a5e4c7b4d2f] (by decide +kernel)

private theorem ok_b01111011 : Impossible board_b01111011 :=
  fork 63 ok_b011110110 ok_b011110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b011110101 : Impossible board_b011110101 :=
  kernelLeaf board_b011110101 #[0x7124642131343a71245f2828340c6e6467597359223a21642c592c113f163754, 0x535a645635396456395f2312491b2a1d16341a3b1e15092a093a56784956567b, 0x53602a1e395f235336492812252312361c3a32662718291c323f78286539653d, 0x5e717080793a7c3a256c59362f73597873231c5f49495e28715f6f3128233265, 0x256c2a1d2c235d32365f3f6d705f656d6c5a4c3f37596c6b716f6163357c7873, 0x6063606c2f7a236a59632c4970652c236c605f585b322a7337701c2c33323332, 0x662034173d2924341c5a3b293a292e18603264533a24375a705f71323a61375e, 0x5a675e3260291c1c2e3927311c39667a736f65605f2360113e60765a2428716f, 0x752369111e5a5b69585e395a5a285e5a32685b4939583124282531295e741e39, 0x355a755a745d6b5e6076293f325e326c60735d635a646737605f376a584d6528, 0x73635923236c5f2a6c5f5d5a6331365f5e5858255a5733305d] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b011110100 : Impossible board_b011110100 :=
  kernelLeaf board_b011110100 #[0x58365e7b632f1c5666755b665449105e535f61715e5f546d535a7a715e665d64, 0x496258346f3412282f491934245469535a68162a21625e662f176d3d346b5a53, 0x5428682c362a6f5a3421585f5666176d5a535b543a585358632a6f1956666f54, 0x2f1a6f1c30582f56306a2f213d5d2e2e37303a233366565d585a2e2e5b49243a, 0x6b2f3230251f2558212a372139252125532a3053273429192f5a2f1c21362a24, 0x27616f592c59146319305d5f5d695f61236c585a5d305a567d3a3d6c5e34175a, 0x272e3d3a692f1c6a492c29346a126254536e5a2c30200f303a5621082a5f5e69, 0x6b625f236c6a2e306a5d59576a62492e21620f3021592e3766593334] (by decide +kernel)

private theorem ok_b01111010 : Impossible board_b01111010 :=
  fork 85 ok_b011110100 ok_b011110101

private theorem ok_b0111101 : Impossible board_b0111101 :=
  fork 69 ok_b01111010 ok_b01111011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b011110011 : Impossible board_b011110011 :=
  kernelLeaf board_b011110011 #[0x6c70703223565b526852553d5d4f392e563f3a644f2e2e0f3f64565d5260651f, 0x372c392e272c4d3d3623392b0f394561394f5f29584d5439631e5855306c625a, 0x3a2c6a612e545a33682b552e593a54612f292c632c452f1e2c21587d33331e27, 0x59153d2b33240d562b2a1d565a746158294d602c1e585a2e1e1c4f1c1e585616, 0x2c36271d62202e142b646518564560616255293a54333a562b3914301c305829, 0x562c20171e292e3356603a5a594f293a291e2e563535241b27352a3536192923, 0x606723352c5927453a4d6764567d5a6c2b3a563a5b52684f3a67563a735d5260, 0x68406a62556b76624d6122666a59615f3a61591e29162b596a202e5460555f68, 0x35294d3355362b5a644f3a671e64567430666856526060406059353d5a4f646b, 0x5a6c5b5d30525a6823282c39275224566f282b36] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b011110010 : Impossible board_b011110010 :=
  kernelLeaf board_b011110010 #[0x5b5d55607754605d163029392930225b6a6024112b5b24221e5b290a716e5835, 0x5b3a6567186054361c3654126a282133283a71656760556252681c11365d682c, 0x7158296645336a621d226552715b29676a525d1b3a67667124526511292b2e6a, 0x2c4558395d2b616159312e55332b602e302a2c391e0b2a32161c622c301c6e1e, 0x1d676065625223115452592130] (by decide +kernel)

private theorem ok_b01111001 : Impossible board_b01111001 :=
  fork 87 ok_b011110010 ok_b011110011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b01111000 : Impossible board_b01111000 :=
  kernelLeaf board_b01111000 #[0xd22332a2a4d672b2727453a285b64646a395a455b5b63215b172471582a3554, 0x222732122321162a584f2b6c4f2b4570684d315d2b2e3923132a3564585a396b, 0x275d795d665d2a2a642729212f0f] (by decide +kernel)

private theorem ok_b0111100 : Impossible board_b0111100 :=
  fork 52 ok_b01111000 ok_b01111001

private theorem ok_b011110 : Impossible board_b011110 :=
  fork 75 ok_b0111100 ok_b0111101

private theorem ok_b01111 : Impossible board_b01111 :=
  fork 74 ok_b011110 ok_b011111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b011101111 : Impossible board_b011101111 :=
  kernelLeaf board_b011101111 #[0x292b6056286022256247513e6247476226614a4a26651d5d315e655852415733, 0x22275e3a22564d2262275a321c171c22682b6018514a476062624f5c5a4a2960, 0x662f1d0a65475e58246341625d565e6624653a244f6752265a644b2b22552668, 0x5d212734601e2856655a672b5e29563a1a5a5e6e5e26655d473a64265a1a4d61, 0x4d1e2c55184a29225d5a4f35165d56685d4d314d3468294f372c5e3464475a22, 0x595d212f3a601e2f191d3d222326312629242b18622b5829225f5855146c214a, 0x1d2b593131311d5d592b2b3a60185937595d212f3a2f2f3d26310f2e1d5a3131, 0x3d316b2b56115d3129596b3151345d4d313a31632b4d295d314f5d31] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b011101110 : Impossible board_b011101110 :=
  kernelLeaf board_b011101110 #[0x586c4d4a0e162f4d164b2f31285d2151373b323b3433281311334f34293a6024, 0x5663213a5f67534d283a312f4f5c284d1126314b23162f1421223b514a3d3a2c, 0x314a78271a135c4d171e2f53642f4a63580e325351293a2f0e3a5a2c4b53565f, 0x5a632f2f563134585a574b285d5d56584d2f3a51601e2155536a4d344f33293a, 0x4c31282c58574d4d2c18635c586258676a1d4c2e34631d6457594d765d704b5c, 0x2f22765c082f2668634d6d4c795c0f2337102e582f1d35312e2556292e60184c, 0xf292f531c33343a2f333a603311172f583319565d315c0f33343a1d5a1e272f, 0x6b1a2219795c0f33581c1f33102e261d4c2e56315c622e31533a343260180f1f, 0x295c0e28265a18295c3a4a4f110f1f3528601e171c15681f1c15281c34193319, 0x221c1556351f2831341d114b2626290b2960185528280c1f581d294c355c28] (by decide +kernel)

private theorem ok_b01110111 : Impossible board_b01110111 :=
  fork 69 ok_b011101110 ok_b011101111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b01110110 : Impossible board_b01110110 :=
  kernelLeaf board_b01110110 #[0x4a5165112747514a6b4b2659514a57291c32221d081452251621475a26315824, 0x29750a4f15311b115a57601433595a4f5a52316c6f2b4f5c28111433222b605d, 0x22515d31294b21114f1d4f344f4f254a4f222e564a625a6c4f2935601e1a1b1a, 0x4c224b3158214a35596a4f314f35225c59315d2629356422292833514731585a, 0x1b5c0f14525c3133225d2b594f20224b4f14224b2956254a5945564f2e351822, 0x79275c4f2652553314292e2e3468565157655657224b685651674a2e51594f68, 0x655c562e085935595d5c52471d316459516f345908046479281b5d337e457647, 0x334a516862205659355d562b704c521c17203129332b521f355c225959225c55, 0x34281c4f2835350e202b6464591c1f34354f213552682e] (by decide +kernel)

private theorem ok_b0111011 : Impossible board_b0111011 :=
  fork 57 ok_b01110110 ok_b01110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b0111010 : Impossible board_b0111010 :=
  kernelLeaf board_b0111010 #[0x60600a3a2b164f393e6260584578653a64602b371809375d53665a1475595e51, 0x41323a67713a215d67607b6827686022715b685a4d74716422212b2f3253783a, 0x4c22592f6247315913416757592526470b4f5a6867135d55755b64572b216c62, 0x3162475760524d24536c472668232664181e4c181e6414253a78182957276270, 0x2226762445654562576070655345706362592c456511665857642c5862595766, 0x5e2272695359606c5f574b5d1e626e5e594c252711314d584541415d6c623145, 0x4c4f65594b121f5531244d60675759624c2f211c5d53594c5d2f24594d55534f, 0x685a67685d6452726c312b294a584d212e2939602c62291f605d575a2b295762, 0x594f5d3957603d5f294f5f5a29555f576c62225a555268655a4f5d653957604a, 0x4f59595a526065552252584a5757645259255722685560524a60681725354747, 0x4c525d4f4a2955415268554a2626670c6c4f59585952256259] (by decide +kernel)

private theorem ok_b011101 : Impossible board_b011101 :=
  fork 48 ok_b0111010 ok_b0111011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b01110011 : Impossible board_b01110011 :=
  kernelLeaf board_b01110011 #[0x2525254d212f25142725182128185d4f231825224d474f175c4f645d242b3b5a, 0x58652e2e1c68684a4b55455f2b69395d355c794f5d6935275d475c4f536c1f27, 0x62584c4f5c305c52595d5d475d59452b1e356953735c5235456453556353524c, 0x2e4f5c2e2147682b556c55456453556355534d65182b53644f584c553959354f, 0x531765115947536425352235695d4d2b672b1447667a1764252e4f5d2b5c5325, 0x2b1c1a4f4764537a25552b535367525363524d475c242225682f4d47584d5245, 0x4f6c6e3b25225d4d2c252f5972584c45646c4d70154c274d14801e744d254d24, 0x536f2f304b685d5c255e59616c212f5e69252c252f1c1d5c584d24315c534f5e, 0x525272232b65185d635c2b2858172b391f4b2f3025635f766f582e5f0f256458, 0x5b2b124f60115c5b4f5c6f224f1c59305267355c5559232b5c552c355c525922, 0x6a6f6e58731f72594c11355c4c2b4730594f5b] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b01110010 : Impossible board_b01110010 :=
  kernelLeaf board_b01110010 #[0x2b112c22172c391730255a62594c53212421116414222147215d6f53092b185e, 0x1d222130532f33251a24321a2c16250c53161c7347685309273d5d6668642114, 0x252b5d225d682b59305a12095d2b255a4c18242b771c253216585d307027212f, 0x2828332253252f3915590f534f5309] (by decide +kernel)

private theorem ok_b0111001 : Impossible board_b0111001 :=
  fork 81 ok_b01110010 ok_b01110011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b0111000 : Impossible board_b0111000 :=
  kernelLeaf board_b0111000 #[0x413d535239301165310a722b535133452317253017301c2b391d525311314a58, 0x47535a64286a3b595a4f665d4c2b7e5d6d663d2b213147535c613d535c4c2b39, 0x5930593d2b416213535217242523174762203123145124471739592b2b512b3d, 0x30605d597a72532721276153134753741e2b251630592553322c324f6c625e2b, 0x47521b675a2b234f314f745216520f17525f2539144f59472b1c415f5d4a6c24, 0x394717471759672b2b591831256a3d535e52] (by decide +kernel)

private theorem ok_b011100 : Impossible board_b011100 :=
  fork 87 ok_b0111000 ok_b0111001

private theorem ok_b01110 : Impossible board_b01110 :=
  fork 54 ok_b011100 ok_b011101

private theorem ok_b0111 : Impossible board_b0111 :=
  fork 70 ok_b01110 ok_b01111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b011011111 : Impossible board_b011011111 :=
  kernelLeaf board_b011011111 #[0x18231e2e1357416f1d7f2b67675a591d594a74596a3a54183a19212c690f352a, 0x545422134d215f5457656e565b54491b672c2c216313632854712e1d261b2b2b, 0x163e1628656d56631208131b2c7f221d41651d0a281d221518261b2b724a5f49, 0x2f1f3426565965493729584a4f5a5b22491d545f564f22213417223729630c1e, 0x27214949741d2f235410211815224127141d2e322b1f49591e225f171d222149, 0x181b2c1d3d3a216a590d59655b543a590f491d58404d5f56516d1d49212f1f19, 0x2e41622b4a6e34326b326332661e1e744a222b56635a522624582b56542f2c41, 0x2931184c5a312e545c512e3e564d2c5a141d2e412c1d] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b0110111101 : Impossible board_b0110111101 :=
  kernelLeaf board_b0110111101 #[0x2b282a141e3240212a561e1d325f182c2a255a5e1e3a73146059635652224d2f, 0x4a225e6f602a495e081e191e566f1d271e5a2c28541d1e3a5663400c291d1921, 0x184a22545128293a541e325f5f60522251594a171d603e245b223e5922513a6b, 0x64105929241511283a2254101e1d1e6a1e1d695b24665a1e593d4a2a514c2229, 0x60181b491d2a320f1424595f491a4a594d21294f4b6f543a2c2b59282a645658, 0xc49634d292a3a2c2a27212a564928213a2a4d1d4f5c22261d5e261c29091c22, 0x592949542524286d541e293d4a272527371d280c29282921294f4b1d27543737, 0x37374b22141d224b370c0d22371216292a37162a221c1b63401f7d1e585f6054, 0x1c24602827672227634d6d65766060675c5a594f29321c4c1e2759492537251d, 0x401e1f2a51401b18521f22274d5f1e601b5b60533d3a5872641e594a1e641f18, 0x21131e5a4d5a4d1d272a1d23603752595a272a593763655140637d5856594b24, 0x1e1d4f3a2749] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b0110111100 : Impossible board_b0110111100 :=
  kernelLeaf board_b0110111100 #[0x634f554a6a17224b29654a1d4f285a4a2c63224a2472226463714a5a4f67592a, 0x4b3e174f1e1c1e1b65174a24291e2437172454586665591e4a2c4f6c225a6f63, 0x4a1e25224d4a244a1e4d4f34284a171e1b5440265a164a1e2254595222631722, 0x4a22] (by decide +kernel)

private theorem ok_b011011110 : Impossible board_b011011110 :=
  fork 53 ok_b0110111100 ok_b0110111101

private theorem ok_b01101111 : Impossible board_b01101111 :=
  fork 63 ok_b011011110 ok_b011011111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b011011101 : Impossible board_b011011101 :=
  kernelLeaf board_b011011101 #[0x474d140c3426662a494c613a606525224d5c7832663273324c6e65475a1e5e51, 0x27603a1e63273229171c2266474c5a32274d5a655846462549783266242b6725, 0x58674c666b3a644d592c463a2758463e244c4d3e56662a66324c664658496246, 0x4a2c22281e35573a5a41473a4b1d77475a5b4b647d5a495a674725294b5a6572, 0x294a2a660e4024222a3e14291c261117242a2825221f4f4a2c24224a15114f29, 0x7d5a651d524a3f1e4a3a59293e622637656131464b2c24466358412c607a675a, 0x5a1d6c493a6c652265562f2a3a22241c1c19261d2b5f35594b47664a24714f66, 0x6b5e592269634f4d5a6224112b293e5c3561415b49401d5b4a6a221564664a58, 0x244a4a29626637564f5e4a524f0c5e666f2a60674f5c4f59356a326b5e633469, 0x291d292215291d2c290b1c226f4f5f494d523e1a3228323e6f0c3e594d594a66, 0x22344d4c3a56582c566f4c3e4a58556222561e6c354c5264594d585949662a32, 0x644c594929323e4d6e7856594a0a1e22494d4952224d2b6624] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b011011100 : Impossible board_b011011100 :=
  kernelLeaf board_b011011100 #[0x1b214d081722281f4d253e4d61495e2a2828404022492263554f151d4d291e3a, 0x4d1727273e2b2618354f55250f2240491b5e226a59566c615e714d2a4d252740, 0x5a6a22352a4d783f343e1e222b61494d345626351f371d1a5e294d375c6a0e26, 0x354f4024614d5e354d5e3f223e51416228646a220d612b5649241e49714d6c4d, 0x493460666a18225b496f55281e2b3f] (by decide +kernel)

private theorem ok_b01101110 : Impossible board_b01101110 :=
  fork 84 ok_b011011100 ok_b011011101

private theorem ok_b0110111 : Impossible board_b0110111 :=
  fork 51 ok_b01101110 ok_b01101111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b0110110 : Impossible board_b0110110 :=
  kernelLeaf board_b0110110 #[0x4024341d2e142a2325583d291c58586c6540243340331f2a4f6c5e532e1e4a5a, 0x342b2e6d1526322b2e25692a4f2e1a31251c25342b1a240e34610c621a585833, 0x5326123f59273425311c1e32621d53696960351e2e79171e5f6c59784b62615f, 0x622b3f2733402a4c31352a5e2e23273126251c313b1732476270343319245269, 0x4b356b49612a64242b2a4a2a144b4961565e2e545f615461583134582a40352e, 0x474c665259614f65593f4c565f6c586c626025332b533334664a2a57284b4961, 0x53601e464a461c58463f4a29524a536663464660614b584a6c244f534b532672, 0x5e323f63586149562b322b66245846511f293235532e4c464b32401c2c4a4a4a, 0x5b524f2b63662a4c65323f2a2c6b4f5929564b4c47491e4c5b6d311e3b496547, 0x5324173d1c1829532a4f5e2c25534a605c4f643f291e342a584a696358582c60, 0x2c4f5b2c4c] (by decide +kernel)

private theorem ok_b011011 : Impossible board_b011011 :=
  fork 57 ok_b0110110 ok_b0110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b011010111 : Impossible board_b011010111 :=
  kernelLeaf board_b011010111 #[0x595a67516467594d19275a282222183d281b5e6c245e225e400c661e1c29323f, 0x214073222f2a236433282428151c1e15235567282810591d2f2228105912281d, 0x592c4a1d2757592937271f2259562c252925225f661259194034221e1d331317, 0x34641e285407215573222f285f28241d286a1e29592f5824661e295763665864, 0x22222a2f1223542f25675a6b51641e2e245864395c0f24462c21531d1e223324, 0x1e17282817252a3931172746664a64341e2916461a252455542425251e3e6646, 0x25771e322f341e394a2c27642965512f467a645e4a6025315e322f3e5a241c5a, 0x3234393432462c3d251e292f7e242539092822292f2a231e2c291e2e181b3d29, 0x222a2f1e4a1422562a2c211e2c2532341e3e46661e5825281e2c2729392c2928, 0x244a2229341e273e3e2a1e3e22662524311e29253e661e222263462459091f56, 0x222f245767162f6c] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b011010110 : Impossible board_b011010110 :=
  kernelLeaf board_b011010110 #[0x2f5658553255212f4b566266584c662e4a582f3e625f145f5954556251566c2a, 0x3e5e595f5672725e1f171554566d3934565410331b7571733359344c645f1222, 0x1e212e221c2939221c2f25336a5f2432594a2f5e3b61565e592c6358586e4a59, 0x2831226d60602922211e34226a5673564b6c242f3e5e25376118396b51126a2f, 0x28545960242c6a21332f18545e2422592f5e536a2f59604c2f593328661e17] (by decide +kernel)

private theorem ok_b01101011 : Impossible board_b01101011 :=
  fork 73 ok_b011010110 ok_b011010111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b01101010 : Impossible board_b01101010 :=
  kernelLeaf board_b01101010 #[0x235e6a562f2f6354596a562437724a5a2f4b1e1b1d370b1d2f145a4b1b24672a, 0x5a5a5e2c1d08232419565a2209222f12390939132324166c0c150a1623731d28, 0x57571d3e63131d28566c1321292f1e4a562116495f4b1b571d661d4f2821396d, 0x29225a181c1f57165e637156534a6609104054641e212e57625f6f64215f5e57, 0x226c59401c22242964725a0c17296434215a1d296c562f7324283e1e1f1f1f1e, 0x126a29395929597128601e46231e3416405a1c49651f1c235f732433583f161e, 0x331f22215822172c1f24162229291d2c5766585a6360546a281e765c5f531d72, 0x242459] (by decide +kernel)

private theorem ok_b0110101 : Impossible board_b0110101 :=
  fork 53 ok_b01101010 ok_b01101011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b0110100 : Impossible board_b0110100 :=
  kernelLeaf board_b0110100 #[0x2e755f636135631d4c565e221d1d275c29674f70344c622731673d5c4f53325a, 0x5f7c2e6251615f5e5654583135341e293f28102537351d29372413342a392118, 0x5e353e1b211659212732232c19374c2c1f632c585925562a5f312a195e723e62, 0x3131341a192c125662293f615e32693167582c2c2c1f0a585624574b1e345972, 0x29] (by decide +kernel)

private theorem ok_b011010 : Impossible board_b011010 :=
  fork 38 ok_b0110100 ok_b0110101

private theorem ok_b01101 : Impossible board_b01101 :=
  fork 69 ok_b011010 ok_b011011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b01100111 : Impossible board_b01100111 :=
  kernelLeaf board_b01100111 #[0x726429276a3e6d6c6a5f3222213a614c5a591e391739650d5863246539354a4b, 0x63656052292e622732297269583d183e6035525c233509390d6d5a4f411a1c64, 0x183e4f1e2529522f222a2527194d633f60605752221f26725221524d27265231, 0x594d5a5265355b1c3a152929355965354f4c192b2b181f2c2949521f2b6c1f29, 0x231a1c3922354a603525250e394a535c1829693d1c187929594f292265526b5e, 0x4a3a25292c526b5e4d653a55592965655376593267525e4f3a22595219592b49, 0x2631291c1e1f2a2e134f6b535e2e1e57594c4a5a3952293e4f65593552626e39, 0x602e1e4a2b3217254a1e0a314617332532162e657d145263291e31253b472b19, 0x675a6e4c592e1e4a4a214659124f4a5261604a250e231e316c46242e14131c25, 0x551e352421554a22244641154f4a3541212b294a4f55633e296667524a6c] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b01100110 : Impossible board_b01100110 :=
  kernelLeaf board_b01100110 #[0x175f293d57675364292966582f5f131f242272643722662c644c696658255946, 0x2f555f246c60391717621e67135f232131216d7231776c623153650b13646d72, 0x1c2f5f326653215f6662335e29292c3d1e22224f1c0d1f243d1c137e2c212273, 0x5e4c66222339252e4a24722560195e231a0f584a311a5e1c5e3d252e3e625f25, 0x223f25603f741c66593f723d662915674f2f635c5e320c0a322519745e661c2a, 0x49625549635c574b4c4c222f5f3f601625646053] (by decide +kernel)

private theorem ok_b0110011 : Impossible board_b0110011 :=
  fork 69 ok_b01100110 ok_b01100111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b0110010 : Impossible board_b0110010 :=
  kernelLeaf board_b0110010 #[0x5e326659655e3a5e5861586c213b5c4d58473b67786d5c222a5e25223b324c5a, 0x6233575e170623587a2246232725591c224659715c5c7a2353092515493b2764, 0x5b4d5e60534c5967645e2e3e451723125e7145605e4d585e71172c4558637117, 0x3a626c67473a62183e173a6e636d5b1c6246715b3765533a4659253264453771, 0x6e5e29215e452561532b5e2f63462c47455c62766e64464c7763572c5b465b3b, 0x27536753676d25493a6f6d63454c5c656f3a69762e5c495c4d5c1b3a] (by decide +kernel)

private theorem ok_b011001 : Impossible board_b011001 :=
  fork 81 ok_b0110010 ok_b0110011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b011000 : Impossible board_b011000 :=
  kernelLeaf board_b011000 #[0x16224b412521145e4d5e515a414b3d2b1b605a3e1f214b1f293f494b6a167e3a, 0x4b594f4b3b2e6a16734d2922272c4d2549254d630f1e4b293b494b5c5b49766a, 0x4d21492f4d25631e254d67495c0f4121643d4b6c61676367515e4d2b1e294f60, 0x3d161a2b2e6a1e2f5561675c49633f67514d5e29254d494d6a5176552533122a, 0x1e354f23311a27754f3d5e142e60185a253b083e4b614f4b6a16761e1637291e, 0x4f5a1212225e16042717216b374a255e29352a0a161e181b2b6a4a47256c6a5a, 0x244541725e354d5e086149607a66611e7b660e4a222923316b1b290a23255e16] (by decide +kernel)

private theorem ok_b01100 : Impossible board_b01100 :=
  fork 84 ok_b011000 ok_b011001

private theorem ok_b0110 : Impossible board_b0110 :=
  fork 48 ok_b01100 ok_b01101

private theorem ok_b011 : Impossible board_b011 :=
  fork 80 ok_b0110 ok_b0111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b0101111 : Impossible board_b0101111 :=
  kernelLeaf board_b0101111 #[0x3664532064594f56552f5e2236215922685d4f254726334f47310b59395a5146, 0x292c2c72646c1e0a2933212b478267626c3d6c5d53627258756859225e265e58, 0x252e202c1e260a2f372f45206c573112625620312536192c1e3725182c26301c, 0x71636257304559210a331672622c264f2e6c182e2e2b2626132e202e312c1e1d, 0x55686a264f313b595d3b4758652908312764212f5c535a4d456b226e6362537a, 0x5d1a5b683b6031662c45555c5c6645316f2c47685d7a662c1d3b215d47722258, 0x2b180c30315a4f68262e26686a125d4521317059665d535c2626476f2c664568, 0x396a4b6c5d26395d675365557a222b5c5d45282b0c22672b2e25593039222064, 0x261d182e2b6a0a2b5729242f452b3112564b395339595d25596068536c225e33, 0x412b4f215d2b2c59642b5c5d2c33265d592b5c55202e2b2726182e2c1c20262e, 0x293f1d64592e412b4b582c2e3f18452e2a2c1f4d581c5a45273f5a57311c2731, 0x2e5828532e2f58312e59] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b010111011 : Impossible board_b010111011 :=
  kernelLeaf board_b010111011 #[0x64623251312b592e734736312b3e27212b4166627f7c626c732b3278755d535e, 0x2b132e2929491d3e1e10787b6e677d39337416326c5957326d6517412b574168, 0x623073252b26582b2f5d4f7559513d333d5f697549161b6e291b2b33495d782a, 0x516231752a30594541477572595d5829223e5d6e5b22654167621867721d6471, 0x26633059454663594b392246183153222b593b413b7559326570631d6e1d313e, 0x574f1a6e314d2836576a3e265f3059572b592b2b182e596e72125131531a4664, 0x6c5d6a3e363b311a685f4b5f6c336168475d7a664d733b7222463b61315d535f, 0x615d53365d416347576e573166597386] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b010111010 : Impossible board_b010111010 :=
  kernelLeaf board_b010111010 #[0x191559732a271d1e3e2120212e272b32312a2f254d21312a312b1f1032366c5d, 0x3d322b266a7867734d3921393221162a2f4541392f6a2b10322e0a685e78456b, 0x416d2b724b68363f76726657681e1d1614762a5e253221282f1636122a273325, 0x1e67595e766b325f256a216d6b652b6a4163735e7226262f45142b362a667c66, 0x3f6359416259652b2b672b32325b2e1862266c4b393b293932533d3f57727266, 0x1e2f2f2a58162e2f2f1d2a3f63455b31455f5f664562585926182e2b3f656345, 0x4d5b253228] (by decide +kernel)

private theorem ok_b01011101 : Impossible board_b01011101 :=
  fork 86 ok_b010111010 ok_b010111011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b01011100 : Impossible board_b01011100 :=
  kernelLeaf board_b01011100 #[0x7041304f2a301c3239725d7041476126326b70210a22366a2a327a61326e4d58, 0x4f265f30474f33266e3230594d3933325d26103f4f5d6b20592b566c454f1b4f, 0x577065676b325947366e6e293d1b2a2a33130e305957614141475f262e262a59, 0x51622b366a452f1d4d3f6759744f594d5d64413b51337a3b67595d4f7d6e7b59, 0x4f41626265515e69594f5d477a4f477a59562b59] (by decide +kernel)

private theorem ok_b0101110 : Impossible board_b0101110 :=
  fork 90 ok_b01011100 ok_b01011101

private theorem ok_b010111 : Impossible board_b010111 :=
  fork 76 ok_b0101110 ok_b0101111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b010110 : Impossible board_b010110 :=
  kernelLeaf board_b010110 #[0x185a65530e226b21495563745925534f5645782b4741514f47606b4f535a5e2e, 0x173d2b2714661c47043045290f70474f672b4f4770530e6c4f5c76673d4f6a30, 0x27226a6060554525144b2b573141663e4c4c51604f4b672b56474f2b2741701c, 0x29181b49271a5c5158272b2131223e1e104b18552727255b174b491e6b4f4b6a, 0x262a261626451c5e254f5a1c6a262b102a584d2529594f4b2b33576a1e2b1d49, 0x45291e1e25021c2f63534f493f263f235c4925452a594c5849255651165e322b, 0x69583d5f4f6153455a452f312f6751240a2b6b5345661c600b4767131e107025, 0x22624f1c1c264c3d45765866225a6f5f473d5f4f492247677251533d531c6f55, 0x2b1a58102f5a2a6c5f4c5163725827493b265b45634b56724c4b63580418266a, 0x25134b621f2725582c1c4b2c2b452125123f161f2f2b0e4717221722] (by decide +kernel)

private theorem ok_b01011 : Impossible board_b01011 :=
  fork 80 ok_b010110 ok_b010111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b010101 : Impossible board_b010101 :=
  kernelLeaf board_b010101 #[0x492b6a222147211727254921281d312f5a12261449222b2f1d1f51492b2a4c36, 0x2549172b6e102b2b512a277a0a1426204f2b47310d495e21212733204931474f, 0x62472b6f62564f62491b4f2b47536431564f5a3f4d6a28496e664962251d6f7c, 0x49172b1f4d552a1a2f21271e4d25492a66532c472b496e762a5e166e104d5a49, 0x4f5714604d4f6e622c4f4f332c5147215e224d2271292122312f2a2f252b4c3e, 0x4c5e2b1a1a1f582b282f45161f212f3d2b562a471a2c47372b2a265e1647572b, 0x214d6a284b2b2c28625959186241285d4d4c335e3d47274c4f5e223b] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b010100 : Impossible board_b010100 :=
  kernelLeaf board_b010100 #[0x47536b67495c3b171b471310471717492b1022496a496b6e49744978142a625e, 0x4567502269174f3d514c49213029512c3700184717745a212678514c51375121, 0x155372171f2321231321171e4917253d2b142a53472a745a50534f5339254f22, 0x4f185c4f6a501f121a1b621b1239671a760c591826291f3930391f291d2b3b5a, 0x5d3f4d4d3f4f6a56275f674d56174d4f2b5625394f474c123725212f4d1f4767, 0x5728102a62645c62122f1d4d1f501b67162826394f2b3b76625b674b27212667, 0x31534d2226573f2b1f573f2a4d645d6e4c294b451f4b57623e5d4d266159623b, 0x2b1449250c2c1a6453594b4722476a49622b] (by decide +kernel)

private theorem ok_b01010 : Impossible board_b01010 :=
  fork 46 ok_b010100 ok_b010101

private theorem ok_b0101 : Impossible board_b0101 :=
  fork 84 ok_b01010 ok_b01011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b010011 : Impossible board_b010011 :=
  kernelLeaf board_b010011 #[0x67532253052e673b22675a6a6750602e14171b222c2b2b2c2b1722502530394f, 0x3d6432581c6522653e2c652232581825194b0f5a27672b412c2732695d31531c, 0x305c697b275309303b596953145d311b23222c242a152f3f2f30252e3f173027, 0x2c3065634b3065235c5c5a592b5c1871305e2f2b5c58645758516b593b27713b, 0x633b5d59584630505c5c653e2b646d366b625c4157543d50391f29565d292962, 0x3d5d2b5357316257312b561536552b5f3b60275360533d595d5c56515763393b, 0x2b65395d533956563b2b62517857512c673e5d2b3112573059312c71363d5736, 0x29622b635439542251222a6718625d30595e29740e59645e782e416622183136, 0x33575a63363251745e1c39705a7d25746e51726527645e57112e2e56185d5454, 0x564130392122182e675e2b6241513d5d3f563e315f5739696b11] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b010010 : Impossible board_b010010 :=
  kernelLeaf board_b010010 #[0x4f33705c316330655d32581c22301f2c1d2a2c252c0b0f22312a1f20252f213b, 0x30292e3f5463765c605a5830326359333227302a4f3f505d315d845d581c335d, 0x2f334f2e2f5d2f215d3029] (by decide +kernel)

private theorem ok_b01001 : Impossible board_b01001 :=
  fork 77 ok_b010010 ok_b010011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b010001 : Impossible board_b010001 :=
  kernelLeaf board_b010001 #[0x307123125c55226a5d2330371b37223f3b3718295c3f295d672c376a4c59542e, 0x212c604b5e3b37630378631b712325302b21395d2c6a2b22282b2b1817220f4b, 0x59787f18627c2b5e50535d6d505e415d6a312a1b175d6f533b575712171a6312, 0xf6f635d51215f4d635c516928602c6d571b313e3b59595d62305d745f78785d, 0x222b1d1f372960571b5759245c574b1b5f21632b2c251c205129576a185f4d63, 0x5c1b166e2c305774511b41542b6f63297f29336778625c515d4154535060765e, 0x4d547616671577296e655f74505060606d507c325977332b332b57593967255f, 0x58636f251130666d60655c5d775c654b606e5c6331635c5d3b415d3130282c33, 0x322b582a6b152b2463316054742876660e312b4d5d54633b305d51305c655f6f, 0x18257e256e6b6e7c60671b6d310f331c575f545d2963515c606d242929311c6e, 0x301621302b2b591d3916105e16291f171b2329372c2a2428581d59102b505954, 0x24295118253b4b2324291623202b311a165f5d101f] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b010000 : Impossible board_b010000 :=
  kernelLeaf board_b010000 #[0x1b57771725316022631b4d17284d2c33255f58145d3b226a1d64574c5957532b, 0x5911605d1d176317631758282021] (by decide +kernel)

private theorem ok_b01000 : Impossible board_b01000 :=
  fork 54 ok_b010000 ok_b010001

private theorem ok_b0100 : Impossible board_b0100 :=
  fork 73 ok_b01000 ok_b01001

private theorem ok_b010 : Impossible board_b010 :=
  fork 82 ok_b0100 ok_b0101

private theorem ok_b01 : Impossible board_b01 :=
  fork 60 ok_b010 ok_b011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b001111111 : Impossible board_b001111111 :=
  kernelLeaf board_b001111111 #[0x345c293a6026392e4c6e5d5d4c471c26623d6757296d74782b29323479595a4f, 0x1e6d3a1a263946622e692e263b5d7430743139470b610e76745e7b5e763f2f35, 0x313573263d3b5d5c3a3476393a220e462b467426301e392a69672e5c1e62603f, 0x354a1b3d60675e612539352e23626a5f1e3d5d474c263d616e7e6a356e6d6d64, 0x695d6560462e682e2a3c5e5932395d32603f3f1e695d393d292e2361682e745d, 0x6d692274747f277f3a73686018642b39697b2a686d2a648469324c3a4b4a6262, 0x69726765765d5c27793922765d604665306c6d305d6e6d327b7369394b6d867b, 0x102b2e682a2b3d5d46595e4c30305d65623535325e265d4631453d295c326e6e, 0x624a7259456a5c2e21453559675a5f476e302e465c3c5a5a352930293c2b2e6c, 0x625964595a5936645a465c65672431615a3a] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b001111110 : Impossible board_b001111110 :=
  kernelLeaf board_b001111110 #[0x345f3d4b61331b3f377659376c182e2b2729233a2445162a211f37182e34644a, 0x3d5d6a76663a783b34395f23215f5f693d4b5b37675f231d57376a30313f1d29, 0x243d5f23304574734967375c74614b3d2b2f494b66731e7b6d76745a593a3f4b, 0x4b27412a49416239613030252c492a252a2631233922415e3623304545614f45, 0x67594c4720764c2662395f3f7749375c5d4f5f175d4764235d2334595a2e2159, 0x5e4c47645930683d476e1e59] (by decide +kernel)

private theorem ok_b00111111 : Impossible board_b00111111 :=
  fork 84 ok_b001111110 ok_b001111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b00111110 : Impossible board_b00111110 :=
  kernelLeaf board_b00111110 #[0x49373a224c4b364f1d1b1d27222f2927373a622b27413c492e302e212f3a5e5c, 0x5d69700a306e3a2f69677871572b752b723962465e5964455b24645b2929736d, 0x6b3a71766e3a46646030391d1d6e8222682e782a26672581682b785d2e3c682b, 0x5d26271e2b272634696c642b46746c6c4b2226326262643a543a363a6d62465b, 0x2b5d5d603254272554225e3662625e3a623a6f2241212e682b36625e5d5e5447, 0x2639365e275d2530305e2c33305e573d272c2c27] (by decide +kernel)

private theorem ok_b0011111 : Impossible board_b0011111 :=
  fork 81 ok_b00111110 ok_b00111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b0011110 : Impossible board_b0011110 :=
  kernelLeaf board_b0011110 #[0x464b211d2f593f3319453723332f225d29456a2959302e2f1d232f225e3a495c, 0x2b333532275926293a4f543a2f332f1925272f1e3a5e516a54765d2e5a2e5a35, 0x2e7c2f5e3a5976475d2e576c356a226c35572e5e392e186c26333546302f3345, 0x356f306c2c616c646f6b5d1e4a5e7e305e107135820a20225e3f27235a2e5a26, 0x732f34347133142230152922270e2b2425306c0a3a192f6430213517372f2c39, 0x306c476947682b3d14686b5d232169646b2f30685d35342a2f686b2f6f6c3022, 0x657b6160756b5b71686c60495921252225293a211c6c303530216918272a356f, 0x655934763f61644a5d5a364949655d2725243521356b5422256851473f653f3f, 0x39186c245d646e2a343576271e223468573a4a494f473a764b3a153a49665960, 0x49226c76685b184976743a3919342f1e34232139226a206a2e6c301a6a] (by decide +kernel)

private theorem ok_b001111 : Impossible board_b001111 :=
  fork 85 ok_b0011110 ok_b0011111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b0011101 : Impossible board_b0011101 :=
  kernelLeaf board_b0011101 #[0x6463225e63571c2366223259673d724f6c63635b623033302c55212926593546, 0x3725391a495e2e6c4f63456f2745215778635b275759576f22672b63455f3d57, 0x17233151374f59355951212351412b672f171d16606d766b306a222130212f5c, 0x641c5935604b6e546a4b3c5f412b6a186a2a045947131c21355a594a542a1727, 0x271927453f455c625c62164b5a666a223259716c357161575b6a394521765935, 0x1c1e3d61273d6755551e5945675e302c3d3059592c5e3f224a103f5a5b312662, 0x6234571c2c67592c3f596e301d145e35596259155e162a59353559312c557a64, 0x416735705b5e67] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b0011100 : Impossible board_b0011100 :=
  kernelLeaf board_b0011100 #[0x296f221e2f305a2e2361252e1930211e1e29104a1c2e26293446591c306e3d27, 0x625c191d5e615e1e5a633233191d5959191c2e2e5e6037600d1c65100c6c2f55, 0x6d59675e6364676362196f375e6422321822326c5e5e2b47597155255761635b, 0x78496a545959701d5b3b7a645e142a22596467632f3b625963556e7561737163, 0x1e71515e172f223b102f1d331325555f6f1e5e6a3518545a18646e29351e2149, 0x1455225e2b06155e0e1d301512221c29182529593226336216232923293b1069, 0x21233d6a161c293b2b62080e5e0e5e1e5e085c23040e471c2522305e220e2230, 0x493d252f1f2f291e25222f2b2921292923294f13573d] (by decide +kernel)

private theorem ok_b001110 : Impossible board_b001110 :=
  fork 58 ok_b0011100 ok_b0011101

private theorem ok_b00111 : Impossible board_b00111 :=
  fork 80 ok_b001110 ok_b001111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b00110111 : Impossible board_b00110111 :=
  kernelLeaf board_b00110111 #[0x412c46225e51553141674b6a685741625f624b6870736c765a397067594c5d2b, 0x4151675e59235f253d555a59547e34762746226e67543b6136786f2e3c2e412a, 0x6e50414c2e39254a41361c4c3d63593946712f505e5763685932275e322e7622, 0x264c4c63574b635f706c4c59596c5736635e5127276d63414b463d395e7f3157, 0x212722342c2e396e5a315446272c36235a21314c633676415b415b4c27314b5d, 0x515e416321313231414b3333296c6c326c736763594c323b673b2a3d1b183667, 0x6b59687027506751332c674b4678634154296733766d6c6f3d78636d7f6f6739, 0x676a5a23456b37541722272f34236c6c5e1e4a2e67515427675b506751706357, 0x3b2c452f3b275467235137342a2f362a460f2f2a45705a4c5141635927592a4b, 0x366b1e234a3b255e246b2223362f4a551c361e784b513146222c3b] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b00110110 : Impossible board_b00110110 :=
  kernelLeaf board_b00110110 #[0x3239671c706576612e572e375e4a2f4b392c4b232c3d262f1d2f294b2c3d2a4c, 0x2239554b221b2b455e455923593d675d5e37372b23612e542b57613d5b1c6511, 0x45222c5b39555e265e295e452a1f1f29392e29653d653d677059] (by decide +kernel)

private theorem ok_b0011011 : Impossible board_b0011011 :=
  fork 63 ok_b00110110 ok_b00110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b0011010 : Impossible board_b0011010 :=
  kernelLeaf board_b0011010 #[0x376c165a3455235e55214b371857365a1c396c554b39615570575d6c6a1e2e4a, 0x2e676d54366557366a46685d2a36212a2e71211d2e396d594c4b39552c552a21, 0x67414c59372b2a342a5f236d1272372e57542c365533262c2a3457315a1b2a37, 0x5a292a3757782a2a2b5f39671d41182e3946594c2f2e76345d231e5a7634675a, 0x606c63312a45212e6157675a2345341e2a592a362e4536] (by decide +kernel)

private theorem ok_b001101 : Impossible board_b001101 :=
  fork 53 ok_b0011010 ok_b0011011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b001100 : Impossible board_b001100 :=
  kernelLeaf board_b001100 #[0x3f1d5012551e452221263122255f4b221e3239551d186c4c2f1d676a61542a2e, 0x29252f544b1b312222412f224b222f551e365c312345186145292c1e6a415f55, 0x575e36455f6a4c5d6137412162611623375d3b65616e54625f4c556c59342a59, 0x62784161546a22755d80545d5f5e2b5d412f22362b325f6c61092c374b2f5d35, 0x6a13215d6d62516154625060606c555e785e2c6c4b5f456c502f5d5e786f415d, 0x364b1e253161576e26362059141522334c261e3118294b682f24343260553750, 0x145f222b2c2b62314c590a6829660022342b590a2c23543341225e265f365524, 0x221e2f252c211c21] (by decide +kernel)

private theorem ok_b00110 : Impossible board_b00110 :=
  fork 73 ok_b001100 ok_b001101

private theorem ok_b0011 : Impossible board_b0011 :=
  fork 86 ok_b00110 ok_b00111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b0010111 : Impossible board_b0010111 :=
  kernelLeaf board_b0010111 #[0x55566655455f51354c5655215d7549325b5154322765246a5a1e22465c45672f, 0x2e1e25665d6827686b3256452169465c7c6a6555546651625b566d45625b655a, 0x5a5f216a454654544a5556665565553f54666c6a56455f4a54325b1e3255565d, 0x32625f21222a7b5d3f7f73175c7655112e2c56555b515f5c665a555c1a2c6d1e, 0x644a661e1e546a5b544a3f4f556821745d55455a2e5a6a6a2a0e5f2b2b203717, 0x5a320e644c62325d5c3a646465555a6f3a5d645a655b6f5a6d5d62763a505524, 0x355a69395f6a50454a352c3b4131512c355a6d5c314546672121190f2122323a, 0x34565039554a56455d242c453b466d4541452e3c3161512a6d312a5a542e5657, 0x27392e55222c413b5a54342c295a34261e543f395a5f452e563b505035612b2e, 0x27352639352e392b2b2e2a2c325a2e3925326237395b37395c41112e395a271a, 0x2c39232a2c5a31352e314932392532172e1c56233226795a652c2e1c39514137, 0x30244524262c241b413515] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b0010110 : Impossible board_b0010110 :=
  kernelLeaf board_b0010110 #[0x4f3f1e2f5525294f291c22651b1c2739455a2a356423213245645a5032394a2e, 0x2b2424291666232a2529373255292f271e3a27456a3c3c6155316c4556503955, 0x7c1e3721502c66224a292f5a395c6265767a5d764f1e62243b5634322a456a3b, 0x4f3b56352b] (by decide +kernel)

private theorem ok_b001011 : Impossible board_b001011 :=
  fork 96 ok_b0010110 ok_b0010111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b001010 : Impossible board_b001010 :=
  kernelLeaf board_b001010 #[0x1f2b1272715164552465665071745d57315d695b125c2f6d6655693155655a46, 0x84761e7879346554395d796078796b76346512645a2768727227326221326d57, 0x2669353a68296d2960347065706065763a60703455726567456b2e6d745d473a, 0x2b2b661425310e0b647661662e64396576646671296465665569666660324a39, 0x5b602a7616251f1086107e1322264c5c305c2434710b5c55663a3966142e0e] (by decide +kernel)

private theorem ok_b00101 : Impossible board_b00101 :=
  fork 89 ok_b001010 ok_b001011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b00100 : Impossible board_b00100 :=
  kernelLeaf board_b00100 #[0x1a32662c575b5d6f272b6f1262272f573131231a214f6c1f353525552b6a5c46, 0x643c4c66252b4a607a5c69322a4122622b18312e3567456f5d2b4521086c5f22, 0x27542530232b18325c225518043c225c5c7a1a731f642335415c35551e6a2e68, 0x39326068655f3557396c236d22656c555c2322416a56455f235c2b6d60] (by decide +kernel)

private theorem ok_b0010 : Impossible board_b0010 :=
  fork 54 ok_b00100 ok_b00101

private theorem ok_b001 : Impossible board_b001 :=
  fork 83 ok_b0010 ok_b0011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b000111 : Impossible board_b000111 :=
  kernelLeaf board_b000111 #[0x512b415e6726412a33412b223337517e417878692b5f5e415b32542641576247, 0x5e68415e371c4f1d3d272468572a375e302755713a695f5a65395b5151372c2a, 0x365f6a663131635d4b2665393326415b5e636e5e63685d78635d126a574c5657, 0x5b60575e60327c247657672b574b55356f5757621460492c68415e5d2b632a66, 0x5f5e296e5e206f63515d2b553f3c0c325563576e5d6a6384313c2478575e4635, 0x3f5176225e245e352c37325e31246246625e5d242b6f222e22292a2435372c70, 0x5e35785f692278305d554a6355497165624b674b6522554b63552b557614496f, 0x31572a14363565412731325d3d5b303557571d6257355d654b5e5f30195e7171, 0x5d222c5d222c512b2b75672c5b395e62295e555d5e575b39625d2655555e5768, 0x5160666d5d6d2c515d2a2c393b265b640d6f216f6a1d54253532266857513d6b, 0x2b2c3763376b70642b326d5d493771355e716f37363557493657545d2b763649, 0x2b232b5b39] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b000110 : Impossible board_b000110 :=
  kernelLeaf board_b000110 #[0x686d1d7129572465673322656362687415304c572b3f2531746b4c2b155d4932, 0x391d5d5d3967333051293a653362753011673341251326316e6430307d2b1b62, 0x227569622726395d1f2b6626395f15396351626456393115745d753b4c6e4c70, 0x29697622742b29262b22702c30626662622262305a70166e645d463322294c24, 0x292b7474332274182e5a3c636474512b5b6530672c2c2939266857513b682c21, 0x5e232e2256126b49211d675e641c6418082b6457492b232e786633785e62227d, 0x2b622b26665749262e2a3962312b39317876222731392e5a5d41626263492a19, 0x656e35243b2b3139745d5a234c26643b7227266e64685e2b222c392669676976, 0x642a4c39395b64292b4c3064747569152b734967685f743f4731652639676739, 0x696529336b656863713a3349693d63493f6b66293a3f69662e6469625d] (by decide +kernel)

private theorem ok_b00011 : Impossible board_b00011 :=
  fork 89 ok_b000110 ok_b000111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b00010 : Impossible board_b00010 :=
  kernelLeaf board_b00010 #[0x551f262b6f663376602222702b22697c2a3b7c226f635f5e325f226733635949, 0x2b4167572b5764635b572a1f16571f3529655635605b5741222a3565702c6260, 0x6b23693c5e766639322527193d223030372a35713f7465304f5a575a59355956, 0x71241b1c21197624374f5957316a1b2a211b16265e7c2c307135592f392a3560, 0x301c606955635964] (by decide +kernel)

private theorem ok_b0001 : Impossible board_b0001 :=
  fork 80 ok_b00010 ok_b00011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_b0000 : Impossible board_b0000 :=
  kernelLeaf board_b0000 #[0x392671326f1b647f65314f32356a573131312a2b2c2c2b2162213b1f27416d5d, 0x4131156d59366a653035575f236660643264623965393c3b417459246a262532, 0x365f4921694665237464652932252b6d3149262e3b602c62685f2c6275647d25, 0x255059737a2c3562645a5f77263960554662591f7b6259317a26554a5b59503c, 0x676749555f2e364a68173b5f73551c6539606659475f186a5f492b312330322e, 0x2c1859262b5f50727722272e672b593c5a5b49493b5f715921396665553f7149, 0x6459643f5065592126395b29593f2659302522502c2e594750] (by decide +kernel)

private theorem ok_b000 : Impossible board_b000 :=
  fork 83 ok_b0000 ok_b0001

private theorem ok_b00 : Impossible board_b00 :=
  fork 82 ok_b000 ok_b001

private theorem ok_b0 : Impossible board_b0 :=
  fork 72 ok_b00 ok_b01

private theorem ok_b : Impossible board_b :=
  fork 56 ok_b0 ok_b1

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a11111111 : Impossible board_a11111111 :=
  kernelLeaf board_a11111111 #[0x2d58142c325327531a5326232a33522c2c5a535e5e68223c322d522c5a544739, 0x271a325a682f580e1b2c1c364b352a5e2c172d26102c2d1c325471606969602c, 0x592a56325e325e696f5957275755305b575e5c3c552a222a56593e692f221913, 0x54552a54384732273336556f2741171d1b30332a33525916695532545e273c57, 0x5e0d24240e58162f41532f15261010261c3233363e16275a5a4d273632335e5c, 0x32452f2664304f1630183c534a0e545816133233381f1e1632382f4b271b2922, 0x45242f452d412d30234f1620291826164f1a2732333c32134f23452d32] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a1111111011 : Impossible board_a1111111011 :=
  kernelLeaf board_a1111111011 #[0x3b1b35455a673572554d57604b353e51353b65553f45252324516b1e3958361c, 0x253e324b061e5b5f0c4b355565643915255c511839355c35393f724d552c393f, 0x25235c39517263390868516e1e1836224d192c394d3e3341150f271a41452a35, 0x301e5b1b41512a2d391b452a352d233f3b08170b16291e24253f39085c6a5116, 0x195a2f0b3917585017236b36242025293f3618512f413b3016172c2d06512f41, 0x195e1e183610644d735a0b295e453933230b41352a233b5b5b454135094d650c, 0x3e323b3b194d39211907390f1a2c265a250b261e241a574b2c0e1d66253f6426, 0x413918331e761a2c2625392a35303f192a392a35335b200f27351a2c3e3e3326, 0x8701e1e35535f36501a2c19393b556b1e3039352a182a331b3e1d331e265530, 0x3360575f36272739500e3333192133275b60] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a1111111010 : Impossible board_a1111111010 :=
  kernelLeaf board_a1111111010 #[0x1a2626484b531c69165e4d1a11190b1e571c25323326381e45324539261c2d36, 0x1c544d57485e1d295758556e5e171c1d1f1c64165a1e151f18251c32350b2916, 0x26264c2c530b561c4c2c5a1e393e1c57250e1b55571c0a165524196948561c57, 0x2d154d3c5b22225a5b0b225509192215571e351322195f232f2c39321e45575e, 0x643c4a6f555719542351253c5b2a353818225a2a1e2f232a380e1523223e2627, 0x5e2454521b052018233c223835263c22555c515b2013235f740a102357223851, 0x522255175b41170c152a4a514a5e5e5c3e5552243c2a0e57162a4a4a232a521b, 0x413c5232164a33381c2f5b54522c554a5b542a452a3e3e3e1c1e5f522c582009, 0x2f2a41225341302c20532c182658542c52333c632d54] (by decide +kernel)

private theorem ok_a111111101 : Impossible board_a111111101 :=
  fork 73 ok_a1111111010 ok_a1111111011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a111111100 : Impossible board_a111111100 :=
  kernelLeaf board_a111111100 #[0x2d385e533c566358505e32581c3e364545263e361e4a1c4c324a0e38202d4d33, 0x2d2f2d25553b5e5727554d193b5519554d2550574d293f364b1848531c582532, 0x26100d513b56615e2a2610545152412d380c580a10251c502350231858452f58, 0x3c30102a41411e5e162f1e5e1c4d3f3e3256553f56414d1b29544d4132472f4d, 0x9163c512d21562d515b512a412f452f205e162d3b2a4122] (by decide +kernel)

private theorem ok_a11111110 : Impossible board_a11111110 :=
  fork 79 ok_a111111100 ok_a111111101

private theorem ok_a1111111 : Impossible board_a1111111 :=
  fork 43 ok_a11111110 ok_a11111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a1111110111 : Impossible board_a1111110111 :=
  kernelLeaf board_a1111110111 #[0x4e3b195c641e27523f483b4a3f4c1c1e4d644a4c1e60184c27294e2022552a35, 0x52522249491948525454572b492f4d3c524a2b1b5b2251524e22572f41541e57, 0x2f27413c412f193b271c12153c5e3f2122202b29291c505b521d3f2f221e2c68, 0x23230a0b1e574c19194d68524806111e231353192d222c392f4a6b5149572b4a, 0x1b2d2a5045451645571f152345453c261f5211221954222d58163c2a180a1e4c, 0x2226171e221e600f604c771c2c23532d2d0a4c51222c511f111b0d571b512214, 0x4c4c222c1920135e50504c2c202a222b2a202a] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a1111110110 : Impossible board_a1111110110 :=
  kernelLeaf board_a1111110110 #[0x494e4f642d4e2b201f4e6a5420591c5c18165266605f535c521c634e594c412a, 0x5a5221354d115023495a234d39641c2c164c355c0c2758141619494f4c534f5f, 0x5f6259676657631e395a202d233912102d26664f5d4f5f5b5966506a656a7c50, 0x395e194d2b204d1a2b1e1f0a271e271d393e0e20200a1e191f15131e2b4c6a60, 0x1e234d1c27151c2b452d2f4f2d272d27641c3c4d0f2350124963193c2b202320, 0x1e1f14234f64] (by decide +kernel)

private theorem ok_a111111011 : Impossible board_a111111011 :=
  fork 51 ok_a1111110110 ok_a1111110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a111111010 : Impossible board_a111111010 :=
  kernelLeaf board_a111111010 #[0x155e204f5b6a50182a2f1652181652261b170e260e0f2057272a20252c2b223c, 0x532a5c4c1941331d1b2f5b0b2727565b202c1f1a2a1d6e2c271a102a5c6a2527, 0x2f2d69154c27555219271527550f4e4f1b2f2a27415e19202d223b0a19504d27, 0x5e22412a5522193f5550572241274e4c101a2d1f274f5527] (by decide +kernel)

private theorem ok_a11111101 : Impossible board_a11111101 :=
  fork 48 ok_a111111010 ok_a111111011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a11111100 : Impossible board_a11111100 :=
  kernelLeaf board_a11111100 #[0x394a1b2a132a1b233f294f183f3e2b4a4f663e2a4f18334f662a3339261d581c, 0x3f5729604c594c262a57332c575760331950254f64391b2a2d2a2d23294f133f, 0x336026514a2345294557261f23592c5045332c1b5b59514a613f4a1b3e505950, 0x1a2d2a331e2c1f1e2c2b4c4a626250574d4a4f234a1e2c572b4f5912112a5f35, 0x2f262f4d26352a1433252a334d4f1d1e29264d142f2d4d254f2f5c0a2402350e, 0x25141e5c29234d2b6849291e185e164f39122c2c2123331d1d142f15191e1d24, 0x1f2a261f2f254f144a5a684f4a23662a1b2f532b26181b4d5c29304f234a2b2f, 0x492d181f2314261b511725242f4f1e532f76264a2b2a3f4a1d26] (by decide +kernel)

private theorem ok_a1111110 : Impossible board_a1111110 :=
  fork 50 ok_a11111100 ok_a11111101

private theorem ok_a111111 : Impossible board_a111111 :=
  fork 61 ok_a1111110 ok_a1111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a1111101111 : Impossible board_a1111101111 :=
  kernelLeaf board_a1111101111 #[0x540849544935251d570f291d254554494b35244b2424454a244a2b49212f2238, 0x414f4b3f25244820481a4808351811274811410e254a645e1a162921552b4f57, 0x1849254f452f5e16244b2049564b54561d1b523524524857215e49214952634f, 0x411d2d1a4f25172d5525170c27252d1a5e1c2b215f4f2b184f4f7457254f3c2b, 0x5e122f1247252d252f1e10582b2d10100a13122125353329413318212b165256, 0x1e4b455f1d17092345202d4f2f532b2d535a354933290f330f633c2b16254a5a, 0x3b4b4f52200b22293958101e4f5c205e16232b47204f1d225e6915391c2d1650, 0x24920250e45] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a1111101110 : Impossible board_a1111101110 :=
  kernelLeaf board_a1111101110 #[0x255216292425555f54524f41525554492b1d11521947583b2547613b251c2d38, 0x1c4f061b39294f0c16390b0c5c0c7255583929256418253949580b542d223c4f, 0x50494f6645504b674f695f50397270552b27392d39274a1855582b55392d641c, 0x49533d3b1e24551c2b5259194752473b524722542d4914394747672953503963, 0x1c1d3d1616184f18271c59293b1e213b244939182f3d5407553f27523b10244f] (by decide +kernel)

private theorem ok_a111110111 : Impossible board_a111110111 :=
  fork 38 ok_a1111101110 ok_a1111101111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a111110110 : Impossible board_a111110110 :=
  kernelLeaf board_a111110110 #[0x4807115c0f03152769065548484f4b254748555e3b4f12254b26395a58201c2d, 0x554f15194b49271f4f49693e4f6e69152220481d1e1a552b335c474939265403, 0x294525534923101e4c39583b26274c3e4c2545233919242b48295e15221a1215, 0x22692147641d4f3b230c4a0c1325231e451d4c3b0b114a552545534939261c55, 0x1620242f4f191623645c55452f6e1058394c3f55253958102653724b5c55290b, 0x4f2322180e254b6f1625124f1b25232220164f15180d251022581e15250e1f70, 0x49251e25181249201629224f122223124c264f16251521232510262558505845, 0x1f1c204120] (by decide +kernel)

private theorem ok_a11111011 : Impossible board_a11111011 :=
  fork 54 ok_a111110110 ok_a111110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a11111010 : Impossible board_a11111010 :=
  kernelLeaf board_a11111010 #[0x5839264121584f502111584f5c584a3918245e2117333e574150583f391d291c, 0x4a3d6045090c197007116110361e4a0e3341361b254a4e5036544950531b704a, 0x585b39454514251e265c2710244c3e21100e45334a0e2121114b453625412319, 0x251d29381e161b12252515272939100d257262100e271e416e0e261f2329252f, 0x38644f6248761e274b38251918505b39265c2727084f74294f23685539184925, 0x25393636534f1e2f4b391f35251b1d361f18361a1d1b23] (by decide +kernel)

private theorem ok_a1111101 : Impossible board_a1111101 :=
  fork 50 ok_a11111010 ok_a11111011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a11111001 : Impossible board_a11111001 :=
  kernelLeaf board_a11111001 #[0x1a27350f27185a567a20691535212b1d4938184f661d5f18263d2757353f1652, 0x26684f3b53214f6b273521191d6927273524451a242025211a5a212035272524, 0x5e182313242d3b2345705e20662b232b4f274e1b101a3f1923451d4f4e192510, 0x1d5a1620234555123f1d2f273516181023453d2625574c23190a13202f23230a, 0x5316362610361625555c5c4926643d4f19273d653d4f203d182764351b1b0e5b, 0x357c5c451d381b4e381d4f18554b6c484f2025534f5b5a5b6b230e1827250a20, 0x4f5c5920272055484f3d4f5b4f486c4b174b485c14485b5a2409353517212f35, 0x3c2f4f1a5a1738190f5a21200e0b1d49700e0b4f08155b4f6f481a48] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a11111000 : Impossible board_a11111000 :=
  kernelLeaf board_a11111000 #[0x20275d0b5218520c121d452f154a12184a120e19453f20456a4e41150c25235e, 0x1620564a6b4f25382725174b3525414b351d3f15200e1b55411108150e1b1108, 0x642748251124175c4a25206b2435155b4f554964571b572148412b204f48274a, 0x4b253520572f216b2f4b3524351a202735161b1d4e2f0c59200b4b3524250e27, 0x1d3f2f414e4952673555230c644f411d414f3b2d252027203525202f2f4b240b, 0x27564f25255a495226387255524b274f483f042d253c12412635255b264f4135, 0x41261b261b70160b35454f254e10564f4e1b0b577e4f564e70480e2725155b41, 0x1127082745234e2545524e4e52062f23085c2535112538110b26161825172b1d, 0x272d163845233c2f2d414e11162725352d1b2f2357351b0935231b4963571b35, 0x4f6849682450273520483f2d5f506a5c4e3c5252262f234e4957520b38261b23, 0x4b4a25555c493b1523255c45250c4725106e4e3f453f4963476e56353b483f5c, 0x59635b4a354e5f3d5b2f60475b41495348555a5b492627414847] (by decide +kernel)

private theorem ok_a1111100 : Impossible board_a1111100 :=
  fork 34 ok_a11111000 ok_a11111001

private theorem ok_a111110 : Impossible board_a111110 :=
  fork 48 ok_a1111100 ok_a1111101

private theorem ok_a11111 : Impossible board_a11111 :=
  fork 55 ok_a111110 ok_a111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a111101111 : Impossible board_a111101111 :=
  kernelLeaf board_a111101111 #[0x1d3b3b6c5d501d553f35502135246e0e3b3b1d3c45725024191d1856142a520a, 0x1b355e38294f253c1a24591b3541663c0e1f3939551f3d1941183b1739193b21, 0x1a2c512f383d3c701f303537194f3d2c6e5e233c2c2f385639374f1b3039194d, 0x173e0c192b0f193b333b2b212b5c0c1b231a68396e5633683e122b1f394f5025, 0x502a66302a4e5915191a305e29502f5e4f5c3f18353732253624233723253f5c, 0x12252519625523124f7c5b3d395d51662c3f353d33251d39303d1f2a18252c51, 0x26304f4b1d3d25354e412a18396614254b395d51502c29301a1f234b0f36230f, 0x1a2c583f0f3e3e5826253e39663e582a143766211927581d193e253612371d25, 0x2513111d370f211917371d2512193350331d1266396d395d6650] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a111101110 : Impossible board_a111101110 :=
  kernelLeaf board_a111101110 #[0x1b3c35255e4c122f4f705e4b393d51252f4f660e231f2f5118375d3926322458, 0x392332185161493938264f705e2f3737411863502f2636631b1d256f2f664f2f, 0x6d7e4f69665037643776192f5a511d4f3745336a50491d68503b516a5a3e3949, 0x645160333f664f3750180f143e263c663c4b5c2d233c253e475139271f543e39, 0x30493637305c3f18363b61253232600c3f365b50323b5a455036512f55193b55, 0x3f393b252c1a3b392c0a6650510363500a2f3619504e5c6850354d6255703224, 0x352536391d25553d396623122c181b273d4f303921] (by decide +kernel)

private theorem ok_a11110111 : Impossible board_a11110111 :=
  fork 16 ok_a111101110 ok_a111101111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a111101101 : Impossible board_a111101101 :=
  kernelLeaf board_a111101101 #[0x6945557c6a192156254a6c5237681438554f184f1b0d4f2f491b4f25383c245e, 0x371b27301a5a184d19114d5c6c55375214354f3b49354b293048555435251a19, 0x1929354d546025384517553b550f1955214b331d294f29093d353e0f4b352135, 0x353b1b503524665d0a3d3b184166503c2a1f410d0537251d1f271d414b1f3f1d, 0x351a244f194f5f263527376830350b5b3b68174d2f393f39243f355519681b27, 0x263c594f505d76596a4f5978660d255029330b1d21192664185b3b5b3d3b1948, 0x335a77236818334d243721493733295d4f5664382627374d27591f0921192947, 0x682f1466662b1b2b504f665d4f45116a50664f23183c1f374f506a4f37335a5b, 0x49354f69684f376856780a473729375b] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a111101100 : Impossible board_a111101100 :=
  kernelLeaf board_a111101100 #[0x353b254f2f21144b354f2f2f4f3d564b4f5e1b564b4f5e506552356176453c24, 0x3d355b193b504f3b4b14514b55234f3625564f4b2f3849414b6127191951491f, 0x322178273d4f3377233e2139543e0f3b3b1a2121192a142149390c38264f3b35, 0x251d3b4b3539354f0f350932064b1b611a21760f210e4f3b4f6866142a194f39, 0x3218643b55657e2129627c2f3d3f3f09350d0951093b0b351b254f553b33170c, 0x14411b3e09210b1b142525212f45251b291f33291d194839623d66] (by decide +kernel)

private theorem ok_a11110110 : Impossible board_a11110110 :=
  fork 88 ok_a111101100 ok_a111101101

private theorem ok_a1111011 : Impossible board_a1111011 :=
  fork 22 ok_a11110110 ok_a11110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a11110101 : Impossible board_a11110101 :=
  kernelLeaf board_a11110101 #[0x47233739273b495f475a45335023494f376a39502350766a334f3766183e5826, 0x1d615537594b5c2549373936382d2355493739324f544737043b391915373316, 0x550b371839324f5c1710153f5125235539362347391915394d5950273e645a4b, 0x4d2347185a38523b33172d0d39392d27522739184f514f3b29527238383f3f15, 0x185c3e333b0f2d184539335a335f23395f395a336a503e4f2d1929474766470d, 0x3d5f3e33333b1b4d5f3b54524739231b3f353f392d663b25122c45365c51255b, 0x1f33393b2d251a5a4f603f3d4e3e64393554705e321d0b32392d06320b1b2148, 0x395e4735364e35213655375c4141366b36505837614b25323d473952451b3323, 0x2b231b3c1b244d294a415b453e4121214a5e6137451b454d234f3e4939582d4e, 0x16391a270f554c4c0a1d271a253623213c39234d1b235466582118231636214d, 0x5e52745e5a1a6a695e164f23294b1d29256611581a0b230d23271a25163c234d, 0x41564f58] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a11110100 : Impossible board_a11110100 :=
  kernelLeaf board_a11110100 #[0x66723c5649664f3c5166500b083f08170b4f1f32182747552547324f1d543e58, 0x1717142d3b2655352d3d1a13211a1321062d21554a2d554b143b354f1d604f4b, 0x48623b4f4b4a5161320f5129324f3d1f321866163327334f3314471445391455, 0x194e3d263d1f323b190f273d27354118641f3c293d4b3f35141f501d3b724f3b, 0x354c5925353b0c3e5572504a17163b0f14591472292655503e481f3b27273926, 0x4f4f61564a7a59274f5f554e4f214a6156083b0a3b51066e0a603b26523e324f, 0x455b7b3926636a3b614f5945704f5d66505239554e19560f0a1f0672264e4f59, 0x1f4e3d4e0f1d190a7818623966504e6e5c41616a482c61] (by decide +kernel)

private theorem ok_a1111010 : Impossible board_a1111010 :=
  fork 42 ok_a11110100 ok_a11110101

private theorem ok_a111101 : Impossible board_a111101 :=
  fork 28 ok_a1111010 ok_a1111011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a111100111 : Impossible board_a111100111 :=
  kernelLeaf board_a111100111 #[0x4f41252521633c352168164d6a474776271c396811043912186e264f6e563852, 0x371b126e5627182d3f163b6a5a5f253726303c171b082f47374f2711274f2f24, 0x68475a21265b5d6c636c3b56502c276c5a254f2b3b5d65683b255c4e4535163b, 0x37506818264e4f2f3b4118632f563b485b3568456c416c3b56502a23415b485b, 0x4d165147674b555c365a6a4d6e456a5068375f59375027252312372547725c4f, 0x55213d2c5b60352a2a3c54504d30515c4d305c2655615548301675494b595555, 0x6e555c4c4f7b3c4f5b4f3f3b3b3547715f4b2a3c4d3f37263e5937304f2a3c48, 0x5b37543b5b254b5d4c394b3c49515d514b7a48364726493b513e6f494b5d5d41, 0x6e4e38264f24245d0c6e212f371027164f65275b481436544b3c2f47495d3848, 0x6e4a4c4a4f4b2a4e5935594d5f18304d6e4e3827485525212a372b383c2c2c4d, 0x55604e3b5d364b554b254b5d515c655010256c363b61556e5560365c5a484e38, 0x363e723b354d504f4b7259364f6e23274b3572] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a111100110 : Impossible board_a111100110 :=
  kernelLeaf board_a111100110 #[0x292337492f4d272363271947523c2f3c5d1b56450e5663526e37685214274f38, 0x494f1b523b5a484f45232c3d354d30484d3c54493949474d414937544748552f, 0x55550e5a4f556c0a3d4a482c371d3f354e566f246935554b5c273b233c3f3525, 0x2368351836553506396e526e683e1b391b3d0b35684b243b4f5541543c70104d, 0x4f4f184d4f5670104810242d3e686810292f6d2748144d2f5f554d] (by decide +kernel)

private theorem ok_a11110011 : Impossible board_a11110011 :=
  fork 94 ok_a111100110 ok_a111100111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a11110010 : Impossible board_a11110010 :=
  kernelLeaf board_a11110010 #[0x14496a5168255516385a65254f5e275b61254f5e24493b4f2b0c4f3b143e2a3c, 0x471f5b49396a09352f242116383e2f395051683e6a4f4f602517153e6a553b2a, 0x3e2d3b2a2f1056683655474f2d3b51] (by decide +kernel)

private theorem ok_a1111001 : Impossible board_a1111001 :=
  fork 88 ok_a11110010 ok_a11110011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a11110001 : Impossible board_a11110001 :=
  kernelLeaf board_a11110001 #[0x3d4d453d514e0c1b3b52302f41552a63520a4e2f3b1515052f2a413b1935502c, 0x597868723c3e4e683c4f555f6e554c4b3d4f4a396c5670103c0c564e0e2a3c5a, 0x3c51375610164b10231b0c0b253530554c2d4a4c2d193b3d35175606395e524e, 0xb250c3c231637083c4d3f27411d08172a374c1b4d56414e375c0a174b1b3716, 0x2a5c55593c5c4d5f411d480c483b25101b27374e4f4d064e184f2d375c4e4b1d, 0x2a170c483f3d52163b5f2537262d0f0c3d2537080c0f510b2a084f525251483b, 0x3e5017153b144f4f193550414e4f2f3951412f41173b2f0555193556182a2d08, 0x504e1c1d4f482f3909410b414b27160b2f351d170b212f170b16290f3e211d0f, 0x515c505c4f475950474b5c55724f5e4814364f3e4f395d0c4f3c4b3b4f605629, 0x100b23510c515c5155727a48184923515c18295b6b502f2d6355273f2345503e, 0x5c51485a163555374b5c5b115a165a5a166b4c5c2f4c47235139505823115525, 0x1921273d47194f213b4d5239145f56701215720c554b236a4f3e581d4b264f47, 0x27] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a11110000 : Impossible board_a11110000 :=
  kernelLeaf board_a11110000 #[0x27125c235d180e6e27477c63271863272b3c0e294d5f726f636e5e37274f5652, 0x364b4f17144b186f476027482b26472b214d16414748454a373b25233b395561, 0x4b395f4b565f566e69565c5149372f56585616595e484f6027] (by decide +kernel)

private theorem ok_a1111000 : Impossible board_a1111000 :=
  fork 56 ok_a11110000 ok_a11110001

private theorem ok_a111100 : Impossible board_a111100 :=
  fork 100 ok_a1111000 ok_a1111001

private theorem ok_a11110 : Impossible board_a11110 :=
  fork 34 ok_a111100 ok_a111101

private theorem ok_a1111 : Impossible board_a1111 :=
  fork 49 ok_a11110 ok_a11111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a11101111 : Impossible board_a11101111 :=
  kernelLeaf board_a11101111 #[0x1e2c2f4d451927634d20091963452a4d415e5b19122b6d19414d201e2c33394c, 0x5553693b5e5a3b553f2c2d573f681e1e64275b0d322b452a101b515b1515512b, 0x3b5851125e1645644d58514d53274d553f724d3b55273f1a695353553f222a5e, 0x23182a062f5b621e4d20122c333f3f3f29571b3e29513f2f4521165b52452c33, 0x30574d3f3229162a41472f513b1110651b4d1a112a412d3829573f4d3329412f, 0x5e2a562f2a41212a555257212a56513b] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a111011101 : Impossible board_a111011101 :=
  kernelLeaf board_a111011101 #[0x213e18683e2a3e261d3e5266735864655461687454543c5e0a3e62166a5d3b4f, 0x61565f5b752b566458651d1a14562a2d515e0f5868584a5e543c520a5b621d1c, 0x2d5f5450245962564152625b66612f1717162161545f582a56640d1b5b695661, 0x6c566b453c65524b5b2a5871171b2d65663e482a252a246659256c4b785e1b2a, 0x5242b4d3e562f2f3e585b562c2f655208665e6a16542f695b631b71637c165e, 0x4538232f2d23302759172b2d5b715b614b2f4d631b412352541a6c560a232f69, 0x45290f5921511b1d3f252c331b121b2d4e522741244e6114632722471b242f4d, 0x515a5a65396364591a16335a59635f301664182c5f3e1951473b52255b51585b, 0x1b5f4e4d0d47385f5b26236a4d265f0d3819452c47392a3f333e265a7b2c2a48, 0x2c2c5f2f4d23682c4e5f2f4e3f51595f5f767b715a2c5f5b4822232c6347394e, 0x5b5b594d3e2b107e102b2f5b1d125b152a3e3f51395b4d4516265a2547387a5e, 0x334b581d3e513b] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a111011100 : Impossible board_a111011100 :=
  kernelLeaf board_a111011100 #[0x3f4c512d512a47522a0f2a1851585d6a585150171b17514c580a621a514f3e3b, 0x394a411c4f4a1b0b2217725d704f2d691d564b2a560b4f172a4a16123c254c39, 0x641b0b17211951651d3f4f2b413c27452752211661452547382c51485a634d3f, 0x214f58512147580b1950] (by decide +kernel)

private theorem ok_a11101110 : Impossible board_a11101110 :=
  fork 85 ok_a111011100 ok_a111011101

private theorem ok_a1110111 : Impossible board_a1110111 :=
  fork 49 ok_a11101110 ok_a11101111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a11101101 : Impossible board_a11101101 :=
  kernelLeaf board_a11101101 #[0x2f1b2f554f2a4f4f235e1618182f183902061b1016141b294f1d215a502c3f32, 0x5b2a2b5018451b5f5145103951180a741817705e12241d1d141f23544f58182a, 0x50141b182129121550182c39152a250f0b3e210a18182129254f23185b41214a, 0x5855514f3b1d164f192216141424160f6411221b152b5114150d4f1d2f2a311d, 0x512f39484f215f4f5b2f27164e394d6455503b1d644e274f1a3e2b1b3b415148, 0x2f4c513f392c180b231c3b21185651102f6c5e2f274f64142d56510a221b5b50, 0x51274d4f1d0a4f271b104f4d0d1b235b4d066f1b5b23122f3c2d2f184d121d18, 0x4550574c1e1561534c57534d5e061e685050575a4d5b2c392f5516295e4f3b56, 0x5f164a1b06641d4f2a3b534d455304584e453e4c4c45454d5f09542a5a2b1e1d, 0x1d2748272a3b304f565e5e70164e1e1e1d3048275b07585851481145000d181d, 0x502c3f53251d4f56294d1d4e1d51] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a11101100 : Impossible board_a11101100 :=
  kernelLeaf board_a11101100 #[0x4a19191221392c452623544d191b5954571b584d3f4f536b2f5a645e4d4a1832, 0x1e2f1115075b581b112715540815273b1c201b1508164f3b0d232a5325171c21, 0x1c1f4d1a11202b505b4c53531c645a1e4c15201a5953125e4d392c534a1f0811, 0x4d31574f54615a4d181a271b162f315a4e26301111271c191f1c201a1c274d1e, 0x4f5a5b] (by decide +kernel)

private theorem ok_a1110110 : Impossible board_a1110110 :=
  fork 51 ok_a11101100 ok_a11101101

private theorem ok_a111011 : Impossible board_a111011 :=
  fork 61 ok_a1110110 ok_a1110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a1110101 : Impossible board_a1110101 :=
  kernelLeaf board_a1110101 #[0x1b66221b59332247337264582b336f331b2d6b684f525d3c6366525e544d3138, 0x32452f545e6356575e4d544554626329573c295257165e5256614f13330d1b16, 0x333c542b254b58634f1d134f1f452d5e582d544f5f5857086c565f5e7124541d, 0x5f583e234f4b31531b1653524f4d5a5754471b161c6519525466596423524d63, 0x1b26302b48202c1f27200d232a63333d2b4f41263d231010164a1b1d275f524d, 0x455e241d1d166658182a2f2f2c2323164f232f2a184d27572132182c532b2316, 0x4551665823586562584721185116584f21251a2731215321231d23253e212a2b, 0x2758] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a1110100 : Impossible board_a1110100 :=
  kernelLeaf board_a1110100 #[0x1d3251101b1e1918111910261e535e2d515b6410455f1b532310533319122c2f, 0x565f265d5f522651313e1164576453455854085f45540d2a23060927191f5453, 0x2732536f205e3c1a1e27522c5a612c4752685a574d6433575251643153585153, 0x455e54535e546e2366235e521616061826585e1b543c5316233154585358165e, 0x2523473122193e1d0b275d7b4d64103c631b5a632b3e1a091a192c27532d4d53, 0x235125542c1421254d6412572a545f5e2c54485327325a634d1a25324d64182c, 0x542c18452c53] (by decide +kernel)

private theorem ok_a111010 : Impossible board_a111010 :=
  fork 57 ok_a1110100 ok_a1110101

private theorem ok_a11101 : Impossible board_a11101 :=
  fork 73 ok_a111010 ok_a111011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a1110011 : Impossible board_a1110011 :=
  kernelLeaf board_a1110011 #[0x1423173c161f221712242049131f2d4f1756114b4b615845132d081d491e2f38, 0x3c163133201d4f594e681b124f3b1d5947264f1b4f4e47251a2d5231454f1d16, 0x221621631b49271a1a4721163c63495f59271a633c4f1b312715251a5b121b4f, 0x5d5f63534963637145234f523c4f3b334e454a31494f271b492b57557b4e4f41, 0x15295e315d5f3333745323495d311d2d2b205d316545201b12651e2f665d1666, 0x5e261b2b4f54452f5770582358532626332d5d54492b18555e53474e395e5333, 0x71165e56454e454f183d6b4a4b58315b7b54451b12314f612f3d23253d4e3363, 0x1a4c5b5b4e5670264a4f3b2d4f331a554b245529310611231b5a30151d111658, 0x1422491d10231a275b2f104f415510482355122756411d41276b15237041571b, 0x151f2217242f1b1f25261623171a5e246612451b574141101b1b122348113b41, 0x2615483b3123521b2d2f221b311b242f2b311b22153b311d161f2d1b2631231b, 0x3b4f312d1d1b181d1b] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a1110010 : Impossible board_a1110010 :=
  kernelLeaf board_a1110010 #[0x415545504c53334959455b455b455b73104e27396549584f495a4a504a661648, 0x5047504916181d6d105f33495f540b58415050506615095f45554c664e311257, 0x31241d61251d234f135e120a5e4f74184a1831021731665e12242f3354491d31, 0x664e5412157d5e5e584a41216610301d45544e5e544f41273d4b4e1a12151721, 0x1d4a211d27455427624f] (by decide +kernel)

private theorem ok_a111001 : Impossible board_a111001 :=
  fork 50 ok_a1110010 ok_a1110011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a111000 : Impossible board_a111000 :=
  kernelLeaf board_a111000 #[0x5852225f2d1d3c6355495b524e152d0b475d581d553c1b58105d162159274f31, 0x27392b49491d22594e4c521d59585358591d553f2d221b0b5f501d5f17631763, 0x4f49392f4b2121584f1e2223154f21211b214f151165271d493b554c3b533d48, 0x1b0b4f0d15492708151e] (by decide +kernel)

private theorem ok_a11100 : Impossible board_a11100 :=
  fork 62 ok_a111000 ok_a111001

private theorem ok_a1110 : Impossible board_a1110 :=
  fork 55 ok_a11100 ok_a11101

private theorem ok_a111 : Impossible board_a111 :=
  fork 40 ok_a1110 ok_a1111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a11011111 : Impossible board_a11011111 :=
  kernelLeaf board_a11011111 #[0x3159264e594b1d611428332558572431514524616616246d4b585b51412f3b4c, 0x3357204b244b641b282d5131264b59333e5855245c19592458554b353f24614b, 0x4a4151570e257236553f3529293023193555196b6e414b355823332b2b2c3523, 0x582f4b3658512f5825452a2b4a2f5b5058515b58662f4e595c4b41695f5d235c, 0x3f3633251b5e224b235f2f191b5766502f2b334d2b2c19232224305c25576666, 0x2c58503e3b2c5325573f33313123332b235757582f45292f5155554d29302523, 0x241d1b584b614b5f62514b4a1f22175141504b251d584b1f0c2261305c2a1f61, 0x1c0e1b353651164821161c483647472132254b2c4e0e11245448353f47501d5c] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a11011110 : Impossible board_a11011110 :=
  kernelLeaf board_a11011110 #[0x4e55500f595061515514232d233312252d1c172d142a781225635f336d47313b, 0x4e414c45632a611d50592547335b414e51505d2b54452f41281b642c513c1630, 0x455b615064575547544e4c4c5523204e105f552d51355953412025455b45535f, 0x2d47223f3550471d1610455155295c200c22105517473f2d55554e1e5d2b5750, 0x4e2257452451455b2b4e59453341242459415e686a30646a63554d415e684e5f, 0x45312d19236350454e2816533c1c413f33332b335045] (by decide +kernel)

private theorem ok_a1101111 : Impossible board_a1101111 :=
  fork 82 ok_a11011110 ok_a11011111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a1101110 : Impossible board_a1101110 :=
  kernelLeaf board_a1101110 #[0x2b35551d5e67624a5520273358534135574c55664c0a4c70556b57621e584b36, 0x574b2d66335752555f2f225c756b59574b4135253320205f31571b11241e4c1c, 0x55314d68251416261717634d1623274d1b522c333c5524572f6a5c22555e5c48, 0x4547212827312d4b5841162b22413029] (by decide +kernel)

private theorem ok_a110111 : Impossible board_a110111 :=
  fork 73 ok_a1101110 ok_a1101111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a1101101 : Impossible board_a1101101 :=
  kernelLeaf board_a1101101 #[0x1f30301f1b0e2a233333585f5d29301b711d51501c665178471516304e52313b, 0x5d510a1566081d24121b2f335422281d5d335d62516b14661b58556e5d503e3c, 0x64625b59556a500f146a1d1655285028146a1754612a1f151d1517514c66151f, 0x5d1e625715581f4c1524572a412f241f241d5460551b68501b141f29511d581c, 0x142a1f551b5d2a1d16505157414a5e4a50625520292d536111523c524e593377, 0x241f23585045315f544d47276a165863312c5249333c152a2357281d57281d2a, 0x232d2f4d23274123601b231c1623215b2f65521b63243e5f23586a545514636a, 0x2d51255841570c54452f1619412d302360275f23231d3e582c58302352595825, 0x211432132d4d3254585f5d19675058455031325454503f32474d3e3355545841, 0x171b1428500f16281b1d231c2131541b3168283131211c583f6459232d165332, 0x515445] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a1101100 : Impossible board_a1101100 :=
  kernelLeaf board_a1101100 #[0x4116605b232b3f4c3f47333f2054294554664776504d291c4731594749533348, 0x612f63454521143016291b16302c2f2425543b55505e2f160829456650582057, 0x54206462596650495460515b5e692921412058245841245850664b47315b5450, 0x3041604a3b55] (by decide +kernel)

private theorem ok_a110110 : Impossible board_a110110 :=
  fork 54 ok_a1101100 ok_a1101101

private theorem ok_a11011 : Impossible board_a11011 :=
  fork 79 ok_a110110 ok_a110111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a110101 : Impossible board_a110101 :=
  kernelLeaf board_a110101 #[0x64712d621c3c2d55171b14234f285428614e226432294f524e522c3548553f31, 0x5b783e621b772c4848124e485e16281b1652246c1908170816070b0f29272d3e, 0x5951645f545d1b5e164e6e696a5412285d524524192d58733e176b2124596045, 0x1b22521d2a3e1914161c09141b292719222a281d3c121b2f54661b0c222c541b, 0x6f4523271d24515f5d2a51555255414e222d3e55222d2f51503b1d1d581d1d1d, 0x4e55223f57501e62574e572454571e50553b35501d1d244e50273c35171b5117, 0x23514a514154515f4157244a5451505054515f225450571e2f2961551e2c5423, 0x450d1b4f450710494f57170d1d242f32232a52545f1e511720152c2c1d1e5720, 0x4f293f23102c3e210e1b4d1c2b450c263c582310581d25141e142517450a1311, 0x645e574e251e154f41514e5107204e1e516154072041671524502f2d1e25294d, 0x261b29274f552a4114202d4e55275b142b1522645752503b1d114a6f451b5851, 0x225c574e4f1b57] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a110100 : Impossible board_a110100 :=
  kernelLeaf board_a110100 #[0x2c452b535366525f255453415b2c234526102c1e21111c700d14231526311d50, 0x57301d53575730735e2a3161415d5230271c3b57644e4d31615361452c321c20, 0x541d3c20411453535f147010163c23591d325c4d65525961314d5b5b594f7857, 0x6059703260534a3c2316233c63526023616160101d1c0d231d2b5f5e16252832, 0x6a5f161e1c1457585f1663523c1d54252f235e1d58324f5923282857595e5e32, 0x525b2f2c2754494149544845534a1b711c2c53232f5852631c602331230c7911, 0x5c57233c63] (by decide +kernel)

private theorem ok_a11010 : Impossible board_a11010 :=
  fork 51 ok_a110100 ok_a110101

private theorem ok_a1101 : Impossible board_a1101 :=
  fork 61 ok_a11010 ok_a11011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a11001111 : Impossible board_a11001111 :=
  kernelLeaf board_a11001111 #[0x1d5023681d224e214e3022641049235449141d4962544e686f4958241e35571b, 0x2b2832211d22190d155b23451d555d674f62590e216b2349220e706e0e215824, 0x31495b50637259456b5031170d354515106a22552355502627214f273b262659, 0x728543f264e221431105d1d10070e221724355f634909590d24686763583f16, 0x31261d30416819312150311f173519270d21284150232422311d4f45496a1416, 0x545f2161211d09615b4f2159266c1e271d636828476831263126214531354721, 0xe1f1e0d413d09497b231e086827142921311d215d748665746c1d26477d216a, 0x272149547010231d231926] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a11001110 : Impossible board_a11001110 :=
  kernelLeaf board_a11001110 #[0x6649294b283024193015231e29146550602b07267965296255764a545e614f57, 0x23451629364c4b3b6b1e1936493352692163235b4a63665b5041595565604c50, 0x3b1e5c58212458456b6e2145555059234962554b59454c5865454c291d495d4a, 0x14413517554b2d22496e2363495b2154151d55470d55294b365b232353291915, 0x5549545578554b1d2d491523242d471d071d69243623225d174a3f4154362333, 0x7c546a795b6c6a6c47132d53541d722863630e66746c63656e80545e4f21605d, 0x59541d2d22494533235b55721e656c593354475066292478417c0e6674592159, 0x45413b5b59455e454522776a5b5063] (by decide +kernel)

private theorem ok_a1100111 : Impossible board_a1100111 :=
  fork 32 ok_a11001110 ok_a11001111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a1100110 : Impossible board_a1100110 :=
  kernelLeaf board_a1100110 #[0x272858491216203f7221292333331c1d3c22583f281b59271d2810287221314f, 0x222831215d17524b20543d31332333661d275306205472215e681d231c276974, 0x49315047595c554b644b311510281d3b3b28202d23151020150755351d245424, 0x504b5f5852492d554b66646e553d4b505d10472d554b231b2421222d47595255, 0x4b281d2d28571c226b214b591b1d22503b2450] (by decide +kernel)

private theorem ok_a110011 : Impossible board_a110011 :=
  fork 62 ok_a1100110 ok_a1100111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a110010 : Impossible board_a110010 :=
  kernelLeaf board_a110010 #[0x22536a0e6a105421506353230f16555349540d535e5d71134f15552308293620, 0x176524656921553d2b2b3549541d5e5e762d0f3d1b6a4a192d5c2d541b782d50, 0x553d6b212316293d4f132b5547211621115e3e15285b4f552b213529552d4f24, 0x735224b3531355d215c6e6368571065353115495722210e1b1d2421553d2341, 0x21291c211550311b35171b1527475421312349214f5e68105e0e545e54105e0e, 0x13112d5e5c5e5716274f5c071508130c4a4f6416554f4f5508136955642b2211, 0x3d4a696b5d6a545536632749535c474954530d471b312755672355115e13224f, 0x907222149273e1d115e414a6a3d4a4f3d5f4a546049534f03553d211b725e69, 0x5b556a5421553d5f232123553e651d5e16282121502869212211411316492b69, 0x1b23580d41496923211150325f231b1d10211e3131231b122331215d29215d23, 0x275727555c1052640c2322411d0a0721174931] (by decide +kernel)

private theorem ok_a11001 : Impossible board_a11001 :=
  fork 72 ok_a110010 ok_a110011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a11000 : Impossible board_a11000 :=
  kernelLeaf board_a11000 #[0x7236411517364b48316b5c244110151b4516171524291d4550295b0d23362021, 0x176b0e414145151650104b5d48317d494754584f3110570c0e4f101549546917, 0x15160e1b50311052311b22481d220e170d161d10475222483617084522101649, 0x450d315c5d544f5c54625752575f574b49241b584f4545162310315b05164822, 0x151e23201023201117281e3d234b1e58233112284f453c4515451d0909584b52, 0x3b57415263525d415708206372231d282b0a1d0852524b7461095d6223412445, 0x24132b1d07141d090c620814111d0909131d14117223453b5d4f4a6e53354f24, 0x524e157452132315091f0f125223121015091d5d202352081d231d724f45244b, 0x4f41292015491d314f1f4f1d5715573558127a5d151d314b41] (by decide +kernel)

private theorem ok_a1100 : Impossible board_a1100 :=
  fork 47 ok_a11000 ok_a11001

private theorem ok_a110 : Impossible board_a110 :=
  fork 55 ok_a1100 ok_a1101

private theorem ok_a11 : Impossible board_a11 :=
  fork 46 ok_a110 ok_a111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a10111111 : Impossible board_a10111111 :=
  kernelLeaf board_a10111111 #[0x564f1f202a1e232d314b58234d1d52331f283361616418566358562d4f2b4138, 0x631a4a4f642d4931604e4f2b562d721e66281e0c68584b3362564f4b21292132, 0x182a53582831312d4f4a69284f5845214f1e131a1b2321314f585625560e5352, 0x21282f211b5a144f1b12291c4f55222745282845191c52635e22274731312812, 0x53584b0e4b1f17125c475e1e27555e5e6b611f55131d1e584f452d234b2f2f4b, 0x4d582d452d454f4b332527204e4f22215e584f1d2758251e455851271e2f5c53, 0x5123301a2528580823222d0b1623280e1c290d0b23222747316353582d275e20, 0x22212f5d1a51561c2322287869663221584f1827284f081622212f45231a2851, 0x25515a635e474d1d254f324958492d25252d4f272b584f251e6915452f2728] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a10111110 : Impossible board_a10111110 :=
  kernelLeaf board_a10111110 #[0x23575329164b58291b311c2d4d581b2d3180235f58164f4a5671215323295541, 0x62201c5131594f4d452d57562f16331c455129632353532378722545630f572f, 0x221c561c1c14561a55234731202b56472b2047493325252021252533695a2125, 0x552347225527231c31254c272b4923534f31292b455820292b494b335151564f, 0x4d4d4b45065649251f4956472923471d23291a2f2f29454b4b2f271627] (by decide +kernel)

private theorem ok_a1011111 : Impossible board_a1011111 :=
  fork 54 ok_a10111110 ok_a10111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a1011110 : Impossible board_a1011110 :=
  kernelLeaf board_a1011110 #[0x3821224a515b514a5c5723451e5b2b222a312c575c4c202b2e5b21451e584b41, 0x4b224b4b2f1e5c511e562d49472d522d572749525e472363312b6f291e5a4b55, 0x575127495a49522727572b4d2159592227595756492e1b554b47511e575d5956, 0x5827511e452f2357521e5f63] (by decide +kernel)

private theorem ok_a101111 : Impossible board_a101111 :=
  fork 53 ok_a1011110 ok_a1011111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a1011101 : Impossible board_a1011101 :=
  kernelLeaf board_a1011101 #[0x3158781459532a415358325e235d526141566570694158635e606169594e2d4f, 0x234b3e583225526048594d27582132514e2c2a604e281a7858325925321b5841, 0x36353159514b581d214c574d5e1d624c5b611a6651561d1e607018651b58412b, 0x4c5d31412f2b68632f61315d5c5927606b632256592d5325682b23311815252f, 0x59275b251a591d1b2f51413152572d4153637266593125285164473635574153, 0x355a572825411f2f616153472d4e4d47354e2a4e671f2d59225f1d2b63514d5b, 0x68283172254b6a2f2723305a36514141332f2c2d6136415e25535e5e23336d4d, 0x5b2c65] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a1011100 : Impossible board_a1011100 :=
  kernelLeaf board_a1011100 #[0x4f21324f254c411d1c32214e6f1b6d190e4c0617222a5c4b1427485c4b253531, 0x591b326461214c512c222d4c584f1b5958706577281a282c4e511b286d0b480b, 0x5a1e321f352c62581714604f282235282c5e25274f5147272a1f21415e282827, 0x1e22115e2b4d6569634b5e535a48645c104e0d204e2352592d6f6363592c1e4d, 0x2d191c30645f4f2b595e487459365a6d69194b5a60655e53714d214d605a3219, 0x1425115e1e141515144d534e520d592322565a564e251560706d1f35234e5f2c, 0x2c4d254c194d1d23362b1270581e28072a1f3523591d4f20354d11200f0d4d14, 0x614163623e25654d1d1a410d151d1e5751624c6271481c2e5e212c254d1d211e, 0x4e4d2361194e1b2e4e582e5e225b4e1f4b4b4d1f21225e1f632c4d2325] (by decide +kernel)

private theorem ok_a101110 : Impossible board_a101110 :=
  fork 85 ok_a1011100 ok_a1011101

private theorem ok_a10111 : Impossible board_a10111 :=
  fork 63 ok_a101110 ok_a101111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a101101 : Impossible board_a101101 :=
  kernelLeaf board_a101101 #[0x45594c4a66323f492d694a384538672b23493f455b09454a145a4a56495f5358, 0x28355f574959572d31635f47524c2b5a23572749255972314764516322285948, 0x110d190a2b1a4d282349695f475b2b482c1e522a2d6565453f5a2b5b59414c66, 0x2259683363272d2b48352d2d225a4c49272351414747682b472112685b152733, 0x1d2d352929482d47284e59575e685f592d2c5f51472c5323292d311729382327, 0x33282b2c1a47310e561a47683823566828142c535f2345665641182a282d5e41, 0x2933411c296419274d21471b5e2c2821312d485e51251b2b23311d45281b2128, 0x4c234a57675f455c2c56675f2d6017661c237c322c236a4d2c66455b5a534921, 0x35681e2d47364a565c36275a63766d6327645a4d6d634d5a4c2c2b5a1927675a, 0x323f6251606312665e5341514d66336d6066655b2c334d5b2b7151653f67575a, 0x3f53514d6e515327] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a101100 : Impossible board_a101100 :=
  kernelLeaf board_a101100 #[0x522759534864653561535e53221f316c6a60594e602c233636232b272c634c3f, 0x6581525f635a4a4d5e1e411e2c60604e4a45532b645c63625e535a5a2b272335, 0x634c3628634c4a625a4d4a4c2336514549491b414c634d5e455b385a1a636a6b, 0x2c605a104d1c48195e5e601b4e45285a562c5f2c635a2c4a105a4a630b495327, 0x2c484d4a495c4e254a4a5f492945282319294c6332281e7e] (by decide +kernel)

private theorem ok_a10110 : Impossible board_a10110 :=
  fork 85 ok_a101100 ok_a101101

private theorem ok_a1011 : Impossible board_a1011 :=
  fork 57 ok_a10110 ok_a10111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a101011 : Impossible board_a101011 :=
  kernelLeaf board_a101011 #[0x32155d285b4e4f4d4f3228694e5e2c285862514d27284d22631227284e171e2f, 0x125b4f635649565a1628152051564f2d27275a4d5a5b235e4d635f4e20624e15, 0x2349321f1220515122324f1b532d222263524d490d2e4f22085f4d144e20574e, 0x4d4d392e6b45195b2c551e5f0b184d122c162c163e1d285727254f1f125a2228, 0x55292d0d141714225659296b692d144958162256635f4c5e4d5e596f55234d2c, 0xe1b0f08221e1e17561c2c702d53231d2c171e175f20455f162c3e1d28205912, 0x1a581b2013212c660f1e131c1e5e5d1a4a0e202c17775e4f5f1c5f4f134f4f06, 0x1a58412d5a211e25321822082a21281e5a5a6349554c56185e4a2c3913585c2a, 0x2d1e061628315d2129485e664c5f1c1732680e4e226b0d5f52485e15224e6b14, 0x322a3116081b322a28535d3221290e250e2a1c58212a782153176b1362132a29, 0x2c412c1c2a32411b] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a101010 : Impossible board_a101010 :=
  kernelLeaf board_a101010 #[0x4a4f5d4a2c4d5a53232823284d564a234c2c1e6a2113124c202c1e4a1f2a1d41, 0x1e5a5f525a1c6339175f594d181a59692d645818690b31635f4f634f194f1c6d, 0x2139574e1611171e2f4f4c4d2f1615272028532125205a2f630f4e2d52631027, 0x25524939635210594d271f155312] (by decide +kernel)

private theorem ok_a10101 : Impossible board_a10101 :=
  fork 51 ok_a101010 ok_a101011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a10100 : Impossible board_a10100 :=
  kernelLeaf board_a10100 #[0x554c2d552059596918222848224d2755231d28651b1d661d2a586913582d324f, 0x2e554859552e285e522f1e632759555e5e3357554c61763555275e5a2c4d2d56, 0x645e606159554e23282a283923252823231e2f5e222367555a286728236b5e1d, 0x1e276363596f23555a2c635e2c532c5e2c28576a554c61322257532765] (by decide +kernel)

private theorem ok_a1010 : Impossible board_a1010 :=
  fork 63 ok_a10100 ok_a10101

private theorem ok_a101 : Impossible board_a101 :=
  fork 61 ok_a1010 ok_a1011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a10011 : Impossible board_a10011 :=
  kernelLeaf board_a10011 #[0x1d285b6d5b415562154c5b21286b38551e271d6628270e356b33285b38594e45, 0x571d20352759272b551e6e1e5530251d573235275b0e5d4b5855252b3527206e, 0x661e205b5d382d5c385955493227202b2f5c5c385859554b1d1d206930252028, 0x2d2b1c5549492957295b4956302520227c29554b231a492e39232f4b491e4c36, 0x55580e32355538294b592758232e2e295b47675a586d20201e29632062152721, 0x53234963566b553f4e2e1e33635c6355624925201e251e322d2520114e132030, 0x553f29485655354b553555621529535848551c79695f527007181d5f55607033, 0x4e592264485f4e4c533f1611560b35161c29554b2d564e23484c32704e534c39, 0x2129384958574756642d2e30052e5b1b554b23603555395b4725354b6a281b3f, 0x485355533f53476b0e4e302e35582d20072d111421352129554b5558172d5f52, 0x52635549531e2e2349282e2e5c23414c2355385b47283f4e395f2d532357685f, 0x5b58233358536652283853] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a10010 : Impossible board_a10010 :=
  kernelLeaf board_a10010 #[0x2710691c5a6322645a5a615664215a2d38554e45222530252118303227355b4b, 0x2810255730656257210c22631823631c2b395541455756711121352729272729, 0x6d5756492e33575b4e284e281725206b385955452e5f2859675c5b5756292b45, 0x636d665a53630e39631755612028865f7016295a532b235f1a6628097069675a, 0x2d2123285b2323286921481623482e63292763202d555f16235723706a69] (by decide +kernel)

private theorem ok_a1001 : Impossible board_a1001 :=
  fork 74 ok_a10010 ok_a10011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a10001 : Impossible board_a10001 :=
  kernelLeaf board_a10001 #[0x555721415e216d4125211d4157576c4e596b705e63615e65286b09705755624a, 0x2d202165271c711c1d481c71212965381b2d55552732215b2721233d25575b69, 0x295e4b29636b55275674595f55644e206970221a287066705f6c382227286456, 0x20632963295f1d69212965646660627c4e590e57113e1d2b494b236062697164, 0x2b41667062332b0e1d365e554b7933293d41636c6d61472d2d22557016235e60, 0x455f60536c695762603d2d6659274e5e6e30161e285e627b2b576e215f623d1a, 0x612b5957455d745e5229292128215b53382d5f126b661d5922602e5e6b1c5529, 0x1d457b82712e1d717c6f571a28666820641a233e1d226330202e5359276c123f, 0x605559624c591320665d59271e2768201a66282e6f6965725f476e7e281a6641, 0x3266415b2b6c6b593f726b2327101e55655e6b53206e5b45666066236341705d, 0x555b762912361c2227706923572d5f236529555e6e3f5945595768] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a10000 : Impossible board_a10000 :=
  kernelLeaf board_a10000 #[0x72726b626d6b6274636d6b7a5772646962456b252d11410e625d7b5e69717055, 0x6857411e251b3f2141252369211b3d325e656b65636b7f59694869631b0e6b7f, 0x28211c292e33711d29595f2d471465591d11704548631d693d2820652b65636b, 0x6221234927623d3e6206562823332d29481a3f1273627241766f5f7669282e29, 0xa2012292d0a321c1d322d65412b1e0d70232132182f04152f18041d1a1e1d18, 0x76621e20720c1e0e0a204778225f605627572525412b621e042b5f4b2b5f5d82, 0x1a292529631d14204173235d6841] (by decide +kernel)

private theorem ok_a1000 : Impossible board_a1000 :=
  fork 88 ok_a10000 ok_a10001

private theorem ok_a100 : Impossible board_a100 :=
  fork 79 ok_a1000 ok_a1001

private theorem ok_a10 : Impossible board_a10 :=
  fork 55 ok_a100 ok_a101

private theorem ok_a1 : Impossible board_a1 :=
  fork 52 ok_a10 ok_a11

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a0111111 : Impossible board_a0111111 :=
  kernelLeaf board_a0111111 #[0x2f5836542f5b6537701b235b632e2a6b62542e2e3763272c6e632e3b55574150, 0x2f5b612e375952392767272663376763613b552e2a2b2e37612d272637395327, 0x2d6a2f3b511c3b2633181e3b61542f682c686e54336a2e533d581e626d36546b, 0x14295755513b357235572b2c6e272e573b5f545b2b225b542f312b272e571564, 0x1b312f6b7a64632e2a582a622a1e2b2a351e2f21212a315b6c1d5f2b6e366e64, 0x365b1e36532b5736535831626d0f5b2f5d6a2e165255295d6052552d64312f2b, 0x3b53342e5b2b376320633b552e522d392d276372602e3b202e3759414c293553, 0x2c2353342d5324313b553d5d5b5b2b2b202c5b2f3b5f5d2b603763276025202e, 0x3b2d513d291e532d632b2d2f2d61256355272e312f291e2f2d513b2f2f3b2d2f, 0x542d2f5d582d665f2f28646b582d513b5f5727356a355f2b54275f592f54282f, 0x5b2b] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a0111110 : Impossible board_a0111110 :=
  kernelLeaf board_a0111110 #[0x271f365c2e276b341a535a66353c5435415c553c41625b2e3b7c733c35572b51, 0x232b37576b622938552a2d3565522e2c082e2e58712a5c34622e55575c255b53, 0x2b5c3755552519362c55232e1e39552e35276536552b635f641c655b2435205c, 0x6331375f253b2d39375963392b21416626665a5b5862522e3b2b52263b2d2620, 0x265c5a68591e652a6169682b41682e1d3524682e2b375b5a5f] (by decide +kernel)

private theorem ok_a011111 : Impossible board_a011111 :=
  fork 69 ok_a0111110 ok_a0111111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a011110 : Impossible board_a011110 :=
  kernelLeaf board_a011110 #[0x275e2e24572d5d1b5e2e20637c272e4523267e482e547319354553631d615237, 0x266e701f685d535c2e2e3933232e3c5473102d265f2d241b2d242745702d6439, 0x392d362d222e542f53271d265f242f3327161769546354162e262d262d272d63, 0x615e55233963273529352f27722f622e575429392015271d271c2936202e5429, 0x261b632d39482d315c5f262d6548636a2d232348312255612435392d2e5d2f68, 0x23231c2320341c1e273928204520632723161c2739265a533324725c1c2e2769, 0x681675592763522e6a485a572928263c29285927265a6354230e5c3615273c20, 0x5e20275c572c36235e065e231039532819682c3152515f2f596561285a593168, 0x5e70175e542c232d395327545a393922343551391e5a5a392854415b5127235a, 0x16774c6d555c23291c08205c151b412a352c2e2e2934452d23280e23282c3419, 0x5934292e13341d2e0f2c752215392d3928233934554152543d2e1f55111b3c55, 0x6839] (by decide +kernel)

private theorem ok_a01111 : Impossible board_a01111 :=
  fork 73 ok_a011110 ok_a011111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a01110 : Impossible board_a01110 :=
  kernelLeaf board_a01110 #[0x2320292b5e252b5b1e3635285e5c5b59283926642835612d63525f5e5b534533, 0x61142f2e232e591d5216182623315e502a541d263139262e522363312d364916, 0x5139255041362c21413c216d515a39515a5d68681b353c396350315b2f232825, 0x221b122839681f2a230a3d1b220d182b39632c572b502023222368182b395c5a, 0x181826312126102c52285a545a5a795765283d535e395f6835576c395a5d1b22, 0x5e57493552525e0b54202b2c282b1f2b21624119631e1e224c5254510f3d5a53, 0x49695a39233536646d5a5c494839226d685a415a39795e5757682a202c522b1f, 0x39361b55192a1918225c235a5a5e5b505e5a5b756e29225c1e35572b635a3c6a, 0x35392c285135152336235f35391e51202c3145632e415b5a2c5a242426197736, 0x453d292e665c67455513392d231e3d5e4534452e412c292336262d3945201a15, 0x395a2c5e19635f393436] (by decide +kernel)

private theorem ok_a0111 : Impossible board_a0111 :=
  fork 77 ok_a01110 ok_a01111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a0110 : Impossible board_a0110 :=
  kernelLeaf board_a0110 #[0x1b3638634957681b2b37273557515e3b33263750623558515a6d273559553148, 0x504163612f712e35452b697e555758496a5a595e4d2e492050492f3755334968, 0x27166d4c36316335633b515616265666236a6d31166b5d3b5350412b50315037, 0x5314723b53530866612a2d2a382b332d312b415156315e6b51562a6635345631, 0x1b642b4d493160600b1e383534555a62412b62556318453b514545684c2e2d63, 0x5731331d594d5e45642f312f333616354d505145352b575b593562352c572d63, 0x574922345b3555566d316d612f3b3151573116312f6157492b41576d2b342b68, 0x33356831331b412f3731616a5b50802a596d662a6d2445635e6345702f2c452b, 0x55625d515d535961573663351b4d373c68613668263522314d3331312b41616e, 0x453470491c1d2d533b6155551a3545183555576431635b] (by decide +kernel)

private theorem ok_a011 : Impossible board_a011 :=
  fork 75 ok_a0110 ok_a0111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a0101 : Impossible board_a0101 :=
  kernelLeaf board_a0101 #[0x4d5e35604d48503b3b453b6119514d5a2a272234585a276b645a2359484b3155, 0x27575c4d72256d64626e5750132a72513b5c57255a2c482b4b482b69746b205a, 0x5c766b73715b685a574d5e502b366b5729195c512c29502e50454b482e37291e, 0x3729222f2f5c2f733c332f5b5a3953282c484b31315c25285a332f1e681e222b, 0x685a39352b36391f63682a2c225a2131504d5b352f255d355734452527492f49, 0x146e5768216135232c603136362c682731282c311a6339503568362f352b5a59, 0x5a3537353157455637362c5a373953142a696821256e1e25652a571b0b2a6e5d, 0x152f2b38352e3b50353b4b2a212a14270d2756222a192a26726148144b315158, 0x3377236a5a53316345623545572a612739635a4b315059395a334553202e342f, 0x5a315a33595c5a51275c3369] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a0100 : Impossible board_a0100 :=
  kernelLeaf board_a0100 #[0x1878262663263924312b20246963202e59262869242b1d6969681e212e5b4537, 0x1a231b235f3912190d255e49272f585a4553451e5a492733282e333b1d331863, 0x5a2e5c6f27646731552e49681b12317518314d5a5f2323574527682a2e271b29, 0x2b4d33265a6457292a3b35551e5b4d39634d2c2f272633124d16244d2b762631, 0x315868635f312658312a56265a201c35572c3b45775f2b3155192a573b270c17, 0x682e632639] (by decide +kernel)

private theorem ok_a010 : Impossible board_a010 :=
  fork 82 ok_a0100 ok_a0101

private theorem ok_a01 : Impossible board_a01 :=
  fork 71 ok_a010 ok_a011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a00111 : Impossible board_a00111 :=
  kernelLeaf board_a00111 #[0x612f652762152f63412e7662372b41632957215d68315b573d5b622f57414d50, 0x7c6e315b2b41141c0f1d2955544b3b6a2e5b3d154b2d756a215626142e3c5b31, 0x6120626d616076665161631d37216d0d412b37472f563b1d1f3c543341557c14, 0x343166596c2d41616c33413c6160763145331c310a22332047606e2228702a62, 0x2b372b702c2b1b4727292049291a2833275522512d3353283d1b20232b212d41, 0x2b695f612f556a417841513b55612e57762a742f6876366d1933282e4d625433, 0x723c6541531b413c5e65535b4160166b2f5e6833455d4d6a2e672e1e166b2821, 0x6e1e5b70624d1b5f612b2f7024604d5f782b705f285d414d795f68412e55602a, 0x411e2b5b55415b2f4565576e451f532331266e2b66242e414d761e4b59666020, 0x635755556a414120] (by decide +kernel)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a00110 : Impossible board_a00110 :=
  kernelLeaf board_a00110 #[0x68776965293d292e41162320372e24452b3471651b542e2e7a6b344172556257, 0x1b2b4c411b633d4162624c516b2d68693c3d516863212b41662f3d7066635b41, 0x3d290b235528662b416b342b0c1e360a41655141693d2d416d13565b291e636a, 0x2b0a47284141651b472a4b1b637f132b565b362b414b3d232a4b2b2d41286655, 0x4b26316314143b45144b623c14682e1d201e292856] (by decide +kernel)

private theorem ok_a0011 : Impossible board_a0011 :=
  fork 88 ok_a00110 ok_a00111

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a0010 : Impossible board_a0010 :=
  kernelLeaf board_a0010 #[0x5d70186570122d5537146a58655b59282d6859595814664b5959336149375f5e, 0x232e151c2e2037233d556e606c282f371c54282959595527593d3d0a62371437, 0x3b4b3766582726312e236229206a2e2e2d6d761c503770495b59761e5d3d572d, 0x6255703d685f1c3d375b372e5d6a766254535f292d3d12282e6a2f371e366253, 0x312a3d262d6a5f1428203657] (by decide +kernel)

private theorem ok_a001 : Impossible board_a001 :=
  fork 72 ok_a0010 ok_a0011

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem ok_a000 : Impossible board_a000 :=
  kernelLeaf board_a000 #[0x261b242924155d3129541d2e270a245e5f5d312d491b282b20685e6b23453763, 0x5e31613150474d232e29582a692d455668582a2f5f2d2331452f70533c3d2f1d, 0x2b80663328615f593165263366235b26245b5e2e192b2069453747283c5d5f1b, 0x506e56615137682d6651415f7857576128240d37663418341b45415e54515f71, 0x451d416857746e56574569202d415e6151692d665141375f1a2f681866686857, 0x1b374d5f5d165f685b1b2331712469413145416565694569775b66667665415e, 0x5f37382a5f2d56697968545f215b311b411d271d5e7223372e4141275b291627, 0x273437275b686e1e3b5e4137292e3c3d372f372a26375d315f615b] (by decide +kernel)

private theorem ok_a00 : Impossible board_a00 :=
  fork 82 ok_a000 ok_a001

private theorem ok_a0 : Impossible board_a0 :=
  fork 79 ok_a00 ok_a01

private theorem ok_a : Impossible board_a :=
  fork 58 ok_a0 ok_a1

theorem central_cases : OMA.R_Green14_W_3_12_R1.H2 := by
  intro r hr
  rcases hr with ⟨h0, h1⟩ | ⟨h0, h1, h2⟩
  · exact seed0_case ok_a r h0 h1
  · exact seed1_case ok_b r h0 h2 h1

end OMA.Green135H2

theorem OMA.solution : OMA.R_Green14_W_3_12_R1.H2 := OMA.Green135H2.central_cases
