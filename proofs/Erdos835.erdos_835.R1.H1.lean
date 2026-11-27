import OMAReductions.R_Erdos835_erdos_835_R1
import Mathlib

-- Step Erdos835.erdos_835.R1.H1: hypothesis H1 of reduction Erdos835.erdos_835.R1
-- Credit: @ivillar

/-!
The 242 blocks are compared through their 32-bit masks: the list of blocks equals the list of
sets decoded from explicit masks (kernel evaluation, once per block), and no two masks have
exactly 15 common bits (kernel evaluation on numerals).
-/
open Finset
namespace F2E835

/-- The subset of `Fin 32` with bit mask `m`. -/
def ofMask (m : ℕ) : Finset (Fin 32) :=
  (Finset.univ : Finset (Fin 32)).filter (fun i => m.testBit i.val = true)

/-- Number of set bits among the lowest `n` bits. -/
def popc : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, m => m % 2 + popc n (m / 2)

theorem card_bits (n m : ℕ) :
    ((Finset.univ : Finset (Fin n)).filter (fun i => m.testBit i.val = true)).card = popc n m := by
  induction n generalizing m with
  | zero => simp [popc]
  | succ n ih =>
    rw [Finset.card_filter, Fin.sum_univ_succ, popc, ← ih (m / 2), Finset.card_filter]
    congr 1
    · simp only [Fin.val_zero, Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h]
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Fin.val_succ, Nat.testBit_succ]

theorem inter_card (a b : ℕ) : (ofMask a ∩ ofMask b).card = popc 32 (a &&& b) := by
  unfold ofMask
  rw [← Finset.filter_and, ← card_bits]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  simp [Nat.testBit_and]

def ck0 : List ℕ := [4294836225, 4294770690, 4294737924, 4294721544, 4294713360, 4294709280, 4294707264, 4294706304, 4294705920, 4294574086, 4294574120]
def ck1 : List ℕ := [4294574608, 4294578240, 4294590592, 4294639872, 4294583296, 4294608896, 4294312450, 4294312004, 4294312968, 4294312080, 4294314016]
def ck2 : List ℕ := [4294320384, 4294332416, 4294410240, 4293787658, 4293787684, 4293791760, 4293795904, 4293788032, 4293820928, 4293805056, 4293855232]
def ck3 : List ℕ := [4292739138, 4292739332, 4292739208, 4292741136, 4292747296, 4292740608, 4292775936, 4292820992, 4290641938, 4290650116, 4290642184]
def ck4 : List ℕ := [4290674720, 4290658368, 4290642560, 4290644992, 4290711552, 4286447650, 4286451716, 4286449672, 4286480400, 4286447808, 4286448896]
def ck5 : List ℕ := [4286464512, 4286521344, 4278060034, 4278124548, 4278091784, 4278075408, 4278059104, 4278067328, 4278063360, 4278061568, 4261314562]
def ck6 : List ℕ := [4261298180, 4261289992, 4261282832, 4261282336, 4261282112, 4261347456, 4261287936, 4227727618, 4227727492, 4227727384, 4227792928]
def ck7 : List ℕ := [4227760192, 4227736064, 4227732480, 4227745792, 4160622594, 4160620548, 4160618568, 4160618768, 4160618656, 4160684544, 4160652288]
def ck8 : List ℕ := [4160643072, 4026400898, 4026400780, 4026466320, 4026417184, 4026401856, 4026433792, 4026405376, 4026411008, 3757973506, 3757965828]
def ck9 : List ℕ := [3757969416, 3757965392, 3757965600, 3757967488, 3758031872, 3758014464, 3221096450, 3221094420, 3221159944, 3221095456, 3221094976]
def ck10 : List ℕ := [3221127296, 3221111040, 3221106688, 2147368962, 2147353604, 2147353096, 2147352624, 2147418176, 2147356800, 2147354880, 2147393536]
def ck11 : List ℕ := [131070, 196605, 229371, 245751, 253935, 258015, 260031, 260991, 261375, 393209, 393175]
def ck12 : List ℕ := [392687, 389055, 376703, 327423, 383999, 358399, 654845, 655291, 654327, 655215, 653279]
def ck13 : List ℕ := [646911, 634879, 557055, 1179637, 1179611, 1175535, 1171391, 1179263, 1146367, 1162239, 1112063]
def ck14 : List ℕ := [2228157, 2227963, 2228087, 2226159, 2219999, 2226687, 2191359, 2146303, 4325357, 4317179, 4325111]
def ck15 : List ℕ := [4292575, 4308927, 4324735, 4322303, 4255743, 8519645, 8515579, 8517623, 8486895, 8519487, 8518399]
def ck16 : List ℕ := [8502783, 8445951, 16907261, 16842747, 16875511, 16891887, 16908191, 16899967, 16903935, 16905727, 33652733]
def ck17 : List ℕ := [33669115, 33677303, 33684463, 33684959, 33685183, 33619839, 33679359, 67239677, 67239803, 67239911, 67174367]
def ck18 : List ℕ := [67207103, 67231231, 67234815, 67221503, 134344701, 134346747, 134348727, 134348527, 134348639, 134282751, 134315007]
def ck19 : List ℕ := [134324223, 268566397, 268566515, 268500975, 268550111, 268565439, 268533503, 268561919, 268556287, 536993789, 537001467]
def ck20 : List ℕ := [536997879, 537001903, 537001695, 536999807, 536935423, 536952831, 1073870845, 1073872875, 1073807351, 1073871839, 1073872319]
def ck21 : List ℕ := [1073839999, 1073856255, 1073860607, 2147598333, 2147613691, 2147614199, 2147614671, 2147549119, 2147610495, 2147612415, 2147573759]

def masks : List ℕ := ck0 ++ ck1 ++ ck2 ++ ck3 ++ ck4 ++ ck5 ++ ck6 ++ ck7 ++ ck8 ++ ck9 ++ ck10 ++ ck11 ++ ck12 ++ ck13 ++ ck14 ++ ck15 ++ ck16 ++ ck17 ++ ck18 ++ ck19 ++ ck20 ++ ck21

def Mrows : List (List Nat) := [[33, 49, 65, 81, 97, 113, 129, 145], [19, 56, 77, 114, 133, 152, 183, 202], [26, 40, 61, 75, 96, 149, 218, 271], [20, 39, 80, 115, 127, 168, 184, 203], [23, 42, 58, 79, 98, 163, 219, 254], [21, 47, 59, 100, 116, 128, 181, 220], [22, 46, 62, 83, 109, 146, 167, 237], [27, 50, 66, 82, 91, 132, 148, 164], [32, 48, 64, 78, 94, 110, 135, 199], [25, 41, 55, 101, 117, 166, 182, 201], [29, 45, 57, 76, 92, 169, 185, 235], [24, 37, 84, 99, 112, 151, 165, 200], [30, 43, 63, 74, 93, 130, 186, 253], [28, 38, 67, 95, 111, 134, 150, 217], [31, 44, 60, 73, 118, 131, 147, 236]]

def Xset : Finset (Fin 32) := (Finset.univ : Finset (Fin 32)).filter (fun x => 17 ≤ x.val)

def Llist : List (Finset (Fin 32)) :=
  (insert 0 Xset) :: (Mrows.zipIdx.flatMap (fun (r,j) =>
    r.map fun t => insert (Fin.ofNat 32 (t/17))
      (insert (Fin.ofNat 32 (t%17)) (Xset.erase (Fin.ofNat 32 (17+j))))))

def Dlist : List (Finset (Fin 32)) := Llist ++ Llist.map (fun B => Finset.univ \ B)

theorem hD : Dlist = masks.map ofMask := by
  decide +kernel

theorem hp0 : ∀ a ∈ ck0, ∀ b ∈ masks, popc 32 (a &&& b) ≠ 15 := by
  decide +kernel

theorem hp1 : ∀ a ∈ ck1, ∀ b ∈ masks, popc 32 (a &&& b) ≠ 15 := by
  decide +kernel

theorem hp2 : ∀ a ∈ ck2, ∀ b ∈ masks, popc 32 (a &&& b) ≠ 15 := by
  decide +kernel

theorem hp3 : ∀ a ∈ ck3, ∀ b ∈ masks, popc 32 (a &&& b) ≠ 15 := by
  decide +kernel

theorem hp4 : ∀ a ∈ ck4, ∀ b ∈ masks, popc 32 (a &&& b) ≠ 15 := by
  decide +kernel

theorem hp5 : ∀ a ∈ ck5, ∀ b ∈ masks, popc 32 (a &&& b) ≠ 15 := by
  decide +kernel

theorem hp6 : ∀ a ∈ ck6, ∀ b ∈ masks, popc 32 (a &&& b) ≠ 15 := by
  decide +kernel

theorem hp7 : ∀ a ∈ ck7, ∀ b ∈ masks, popc 32 (a &&& b) ≠ 15 := by
  decide +kernel

theorem hp8 : ∀ a ∈ ck8, ∀ b ∈ masks, popc 32 (a &&& b) ≠ 15 := by
  decide +kernel

theorem hp9 : ∀ a ∈ ck9, ∀ b ∈ masks, popc 32 (a &&& b) ≠ 15 := by
  decide +kernel

theorem hp10 : ∀ a ∈ ck10, ∀ b ∈ masks, popc 32 (a &&& b) ≠ 15 := by
  decide +kernel

theorem hp11 : ∀ a ∈ ck11, ∀ b ∈ masks, popc 32 (a &&& b) ≠ 15 := by
  decide +kernel

theorem hp12 : ∀ a ∈ ck12, ∀ b ∈ masks, popc 32 (a &&& b) ≠ 15 := by
  decide +kernel

theorem hp13 : ∀ a ∈ ck13, ∀ b ∈ masks, popc 32 (a &&& b) ≠ 15 := by
  decide +kernel

theorem hp14 : ∀ a ∈ ck14, ∀ b ∈ masks, popc 32 (a &&& b) ≠ 15 := by
  decide +kernel

theorem hp15 : ∀ a ∈ ck15, ∀ b ∈ masks, popc 32 (a &&& b) ≠ 15 := by
  decide +kernel

theorem hp16 : ∀ a ∈ ck16, ∀ b ∈ masks, popc 32 (a &&& b) ≠ 15 := by
  decide +kernel

theorem hp17 : ∀ a ∈ ck17, ∀ b ∈ masks, popc 32 (a &&& b) ≠ 15 := by
  decide +kernel

theorem hp18 : ∀ a ∈ ck18, ∀ b ∈ masks, popc 32 (a &&& b) ≠ 15 := by
  decide +kernel

theorem hp19 : ∀ a ∈ ck19, ∀ b ∈ masks, popc 32 (a &&& b) ≠ 15 := by
  decide +kernel

theorem hp20 : ∀ a ∈ ck20, ∀ b ∈ masks, popc 32 (a &&& b) ≠ 15 := by
  decide +kernel

theorem hp21 : ∀ a ∈ ck21, ∀ b ∈ masks, popc 32 (a &&& b) ≠ 15 := by
  decide +kernel

theorem hpairs : ∀ a ∈ masks, ∀ b ∈ masks, popc 32 (a &&& b) ≠ 15 := by
  intro a ha
  unfold masks at ha
  rcases List.mem_append.mp ha with ha | h
  swap
  · exact hp21 a h
  rcases List.mem_append.mp ha with ha | h
  swap
  · exact hp20 a h
  rcases List.mem_append.mp ha with ha | h
  swap
  · exact hp19 a h
  rcases List.mem_append.mp ha with ha | h
  swap
  · exact hp18 a h
  rcases List.mem_append.mp ha with ha | h
  swap
  · exact hp17 a h
  rcases List.mem_append.mp ha with ha | h
  swap
  · exact hp16 a h
  rcases List.mem_append.mp ha with ha | h
  swap
  · exact hp15 a h
  rcases List.mem_append.mp ha with ha | h
  swap
  · exact hp14 a h
  rcases List.mem_append.mp ha with ha | h
  swap
  · exact hp13 a h
  rcases List.mem_append.mp ha with ha | h
  swap
  · exact hp12 a h
  rcases List.mem_append.mp ha with ha | h
  swap
  · exact hp11 a h
  rcases List.mem_append.mp ha with ha | h
  swap
  · exact hp10 a h
  rcases List.mem_append.mp ha with ha | h
  swap
  · exact hp9 a h
  rcases List.mem_append.mp ha with ha | h
  swap
  · exact hp8 a h
  rcases List.mem_append.mp ha with ha | h
  swap
  · exact hp7 a h
  rcases List.mem_append.mp ha with ha | h
  swap
  · exact hp6 a h
  rcases List.mem_append.mp ha with ha | h
  swap
  · exact hp5 a h
  rcases List.mem_append.mp ha with ha | h
  swap
  · exact hp4 a h
  rcases List.mem_append.mp ha with ha | h
  swap
  · exact hp3 a h
  rcases List.mem_append.mp ha with ha | h
  swap
  · exact hp2 a h
  rcases List.mem_append.mp ha with ha | h
  swap
  · exact hp1 a h
  exact hp0 a ha

theorem h1 :
  let M : List (List Nat) := [[33,49,65,81,97,113,129,145],
    [19,56,77,114,133,152,183,202],
    [26,40,61,75,96,149,218,271],
    [20,39,80,115,127,168,184,203],
    [23,42,58,79,98,163,219,254],
    [21,47,59,100,116,128,181,220],
    [22,46,62,83,109,146,167,237],
    [27,50,66,82,91,132,148,164],
    [32,48,64,78,94,110,135,199],
    [25,41,55,101,117,166,182,201],
    [29,45,57,76,92,169,185,235],
    [24,37,84,99,112,151,165,200],
    [30,43,63,74,93,130,186,253],
    [28,38,67,95,111,134,150,217],
    [31,44,60,73,118,131,147,236]]
  let X := (Finset.univ : Finset (Fin 32)).filter (fun x => 17 ≤ x.val)
  let L := (insert 0 X) :: (M.zipIdx.flatMap (fun (r,j) =>
    r.map fun t => insert (Fin.ofNat 32 (t/17))
      (insert (Fin.ofNat 32 (t%17)) (X.erase (Fin.ofNat 32 (17+j))))))
  let D := L ++ L.map (fun B => Finset.univ \ B)
  ∀ A ∈ D, ∀ B ∈ D, A ≠ B → (A ∩ B).card ≠ 15 := by
  intro M X L D
  show ∀ A ∈ Dlist, ∀ B ∈ Dlist, A ≠ B → (A ∩ B).card ≠ 15
  rw [hD]
  intro A hA B hB _
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hA
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hB
  rw [inter_card]
  exact hpairs a ha b hb

end F2E835

theorem OMA.solution : OMA.R_Erdos835_erdos_835_R1.H1 :=
  F2E835.h1
