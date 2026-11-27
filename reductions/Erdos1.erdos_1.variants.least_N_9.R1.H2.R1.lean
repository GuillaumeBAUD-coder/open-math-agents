import OMAReductions.R_Erdos1_erdos_1_variants_least_N_9_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
/-! Integer interval growth for nine distinct subset sums. The vertex-boundary recurrence of the cube gives the lower bound 148. Each remaining maximum is tested using signed differences of subset sums, as in Lunnon (1988) and Borwein–Mossinghoff (2003). -/
namespace SumWindow
open Finset Erdos1
open scoped Classical

lemma advance (f : ℤ → ℕ) (g h : ℕ → ℕ) (d : ℕ) (M a : ℤ)
    (inc : Monotone f) (bound : ∀ z, f z ≤ d) (grow : ∀ z, g (f z) ≤ f (z+M))
    (ha : 0≤a) (ham : a≤M)
    (table : ∀ i j : Fin (d+1), h (i.val+j.val) ≤ max (g i.val) j.val + max (g j.val) i.val) (z : ℤ) :
    h (f z + f (z-a)) ≤ f (z+M) + f (z+M-a) := by
  have u := table ⟨f z, by have := bound z; omega⟩ ⟨f (z-a), by have := bound (z-a); omega⟩
  refine u.trans (Nat.add_le_add (max_le (grow _) (inc (by omega))) (max_le ?_ (inc (by omega))))
  simpa only [sub_add_eq_add_sub] using grow (z-a)

lemma iterate (C : Finset ℕ → ℤ → ℕ) (M : ℕ)
    (monoC : ∀ A, Monotone (C A)) (sizeC : ∀ A z, C A z ≤ 2^A.card)
    (stepC : ∀ A a, a∉A → ∀ z, C (insert a A) z = C A z + C A (z-a))
    (n : ℕ) (g h : ℕ → ℕ)
    (prev : ∀ A : Finset ℕ, A.card=n → (∀ a∈A, a≤M) → ∀ z, g (C A z) ≤ C A (z+M))
    (tab : ∀ i j : Fin (2^n+1), h (i.val+j.val) ≤ max (g i.val) j.val + max (g j.val) i.val) :
    ∀ A : Finset ℕ, A.card=n+1 → (∀ a∈A, a≤M) → ∀ z, h (C A z) ≤ C A (z+M) := by
  intro A hc cap z
  obtain ⟨a,ha⟩ := card_pos.mp (show 0<A.card by omega)
  let B := A.erase a
  have eq : insert a B = A := insert_erase ha
  have ne : a∉B := notMem_erase _ _
  have bc : B.card=n := by simpa [B,card_erase_of_mem ha,hc]
  have sub : B⊆A := erase_subset _ _
  have v := advance (C B) g h (2^n) M a (monoC B) (fun t => bc ▸ sizeC B t)
    (prev B bc (fun x hx => cap x (sub hx))) (by positivity) (by exact_mod_cast cap a ha) tab z
  simpa only [← stepC B a ne,eq] using v


lemma verifyRows (g h : ℕ→ℕ) (d : ℕ)
    (check : (List.range (d+1)).all (fun i => (List.range (d+1)).all (fun j =>
      decide (h (i+j) ≤ max (g i) j + max (g j) i))) = true) :
    ∀ i j : Fin (d+1), h (i.val+j.val) ≤ max (g i.val) j.val + max (g j.val) i.val := by
  intro i j
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp check i.val (List.mem_range.mpr i.isLt)) j.val (List.mem_range.mpr j.isLt))
lemma verifyBlocks (p : ℕ→Bool) (u m : ℕ)
    (lo : (List.range u).all p=true) (hi : (List.range' u m).all p=true) :
    (List.range (u+m)).all p=true := by
  rw [List.range_add,←List.range'_eq_map_range,List.all_append,lo,hi]; rfl
lemma table0 : ∀ i j : Fin (1+1), (fun j : ℕ => (0x200800 >>> (10*j)) % 1024) (i.val+j.val) ≤ max (id i.val) j.val + max (id j.val) i.val := by
  apply verifyRows id (fun j : ℕ => (0x200800 >>> (10*j)) % 1024) 1
  let test := (fun i : ℕ => (List.range (1+1)).all (fun j => decide ((fun j : ℕ => (0x200800 >>> (10*j)) % 1024) (i+j) ≤ max (id i) j + max (id j) i)))
  change (List.range 2).all test=true
  have block0 : (List.range 0).all test=true := rfl
  have block2 := verifyBlocks test 0 2 block0 (by decide +kernel)
  exact block2

lemma table1 : ∀ i j : Fin (2+1), (fun j : ℕ => (0x40100400c00 >>> (10*j)) % 1024) (i.val+j.val) ≤ max ((fun j : ℕ => (0x200800 >>> (10*j)) % 1024) i.val) j.val + max ((fun j : ℕ => (0x200800 >>> (10*j)) % 1024) j.val) i.val := by
  apply verifyRows (fun j : ℕ => (0x200800 >>> (10*j)) % 1024) (fun j : ℕ => (0x40100400c00 >>> (10*j)) % 1024) 2
  let test := (fun i : ℕ => (List.range (2+1)).all (fun j => decide ((fun j : ℕ => (0x40100400c00 >>> (10*j)) % 1024) (i+j) ≤ max ((fun j : ℕ => (0x200800 >>> (10*j)) % 1024) i) j + max ((fun j : ℕ => (0x200800 >>> (10*j)) % 1024) j) i)))
  change (List.range 3).all test=true
  have block0 : (List.range 0).all test=true := rfl
  have block3 := verifyBlocks test 0 3 block0 (by decide +kernel)
  exact block3

lemma table2 : ∀ i j : Fin (4+1), (fun j : ℕ => (0x8020080200701c0601000 >>> (10*j)) % 1024) (i.val+j.val) ≤ max ((fun j : ℕ => (0x40100400c00 >>> (10*j)) % 1024) i.val) j.val + max ((fun j : ℕ => (0x40100400c00 >>> (10*j)) % 1024) j.val) i.val := by
  apply verifyRows (fun j : ℕ => (0x40100400c00 >>> (10*j)) % 1024) (fun j : ℕ => (0x8020080200701c0601000 >>> (10*j)) % 1024) 4
  let test := (fun i : ℕ => (List.range (4+1)).all (fun j => decide ((fun j : ℕ => (0x8020080200701c0601000 >>> (10*j)) % 1024) (i+j) ≤ max ((fun j : ℕ => (0x40100400c00 >>> (10*j)) % 1024) i) j + max ((fun j : ℕ => (0x40100400c00 >>> (10*j)) % 1024) j) i)))
  change (List.range 5).all test=true
  have block0 : (List.range 0).all test=true := rfl
  have block4 := verifyBlocks test 0 4 block0 (by decide +kernel)
  have block5 := verifyBlocks test 4 1 block4 (by decide +kernel)
  exact block5

lemma table3 : ∀ i j : Fin (8+1), (fun j : ℕ => (0x10040100401003c0f03c0e0380d02c0b0280801400 >>> (10*j)) % 1024) (i.val+j.val) ≤ max ((fun j : ℕ => (0x8020080200701c0601000 >>> (10*j)) % 1024) i.val) j.val + max ((fun j : ℕ => (0x8020080200701c0601000 >>> (10*j)) % 1024) j.val) i.val := by
  apply verifyRows (fun j : ℕ => (0x8020080200701c0601000 >>> (10*j)) % 1024) (fun j : ℕ => (0x10040100401003c0f03c0e0380d02c0b0280801400 >>> (10*j)) % 1024) 8
  let test := (fun i : ℕ => (List.range (8+1)).all (fun j => decide ((fun j : ℕ => (0x10040100401003c0f03c0e0380d02c0b0280801400 >>> (10*j)) % 1024) (i+j) ≤ max ((fun j : ℕ => (0x8020080200701c0601000 >>> (10*j)) % 1024) i) j + max ((fun j : ℕ => (0x8020080200701c0601000 >>> (10*j)) % 1024) j) i)))
  change (List.range 9).all test=true
  have block0 : (List.range 0).all test=true := rfl
  have block4 := verifyBlocks test 0 4 block0 (by decide +kernel)
  have block8 := verifyBlocks test 4 4 block4 (by decide +kernel)
  have block9 := verifyBlocks test 8 1 block8 (by decide +kernel)
  exact block9

lemma table4 : ∀ i j : Fin (16+1), (fun j : ℕ => (0x2008020080200801f07c1f07c1e0781e0741d0701a0681a06419060160581504c100400f0340a01800 >>> (10*j)) % 1024) (i.val+j.val) ≤ max ((fun j : ℕ => (0x10040100401003c0f03c0e0380d02c0b0280801400 >>> (10*j)) % 1024) i.val) j.val + max ((fun j : ℕ => (0x10040100401003c0f03c0e0380d02c0b0280801400 >>> (10*j)) % 1024) j.val) i.val := by
  apply verifyRows (fun j : ℕ => (0x10040100401003c0f03c0e0380d02c0b0280801400 >>> (10*j)) % 1024) (fun j : ℕ => (0x2008020080200801f07c1f07c1e0781e0741d0701a0681a06419060160581504c100400f0340a01800 >>> (10*j)) % 1024) 16
  let test := (fun i : ℕ => (List.range (16+1)).all (fun j => decide ((fun j : ℕ => (0x2008020080200801f07c1f07c1e0781e0741d0701a0681a06419060160581504c100400f0340a01800 >>> (10*j)) % 1024) (i+j) ≤ max ((fun j : ℕ => (0x10040100401003c0f03c0e0380d02c0b0280801400 >>> (10*j)) % 1024) i) j + max ((fun j : ℕ => (0x10040100401003c0f03c0e0380d02c0b0280801400 >>> (10*j)) % 1024) j) i)))
  change (List.range 17).all test=true
  have block0 : (List.range 0).all test=true := rfl
  have block4 := verifyBlocks test 0 4 block0 (by decide +kernel)
  have block8 := verifyBlocks test 4 4 block4 (by decide +kernel)
  have block12 := verifyBlocks test 8 4 block8 (by decide +kernel)
  have block16 := verifyBlocks test 12 4 block12 (by decide +kernel)
  have block17 := verifyBlocks test 16 1 block16 (by decide +kernel)
  exact block17

lemma table5 : ∀ i j : Fin (32+1), (fun j : ℕ => (0x401004010040100400fc3f0fc3f0fc3e0f83e0f83d0f43d0f03c0ec390e4390e4380e0380dc370d8340d0340cc330c8300c02f0b42a0a82a0a4290a0260982508c200801f0741a05816054130400c01c00 >>> (10*j)) % 1024) (i.val+j.val) ≤ max ((fun j : ℕ => (0x2008020080200801f07c1f07c1e0781e0741d0701a0681a06419060160581504c100400f0340a01800 >>> (10*j)) % 1024) i.val) j.val + max ((fun j : ℕ => (0x2008020080200801f07c1f07c1e0781e0741d0701a0681a06419060160581504c100400f0340a01800 >>> (10*j)) % 1024) j.val) i.val := by
  apply verifyRows (fun j : ℕ => (0x2008020080200801f07c1f07c1e0781e0741d0701a0681a06419060160581504c100400f0340a01800 >>> (10*j)) % 1024) (fun j : ℕ => (0x401004010040100400fc3f0fc3f0fc3e0f83e0f83d0f43d0f03c0ec390e4390e4380e0380dc370d8340d0340cc330c8300c02f0b42a0a82a0a4290a0260982508c200801f0741a05816054130400c01c00 >>> (10*j)) % 1024) 32
  let test := (fun i : ℕ => (List.range (32+1)).all (fun j => decide ((fun j : ℕ => (0x401004010040100400fc3f0fc3f0fc3e0f83e0f83d0f43d0f03c0ec390e4390e4380e0380dc370d8340d0340cc330c8300c02f0b42a0a82a0a4290a0260982508c200801f0741a05816054130400c01c00 >>> (10*j)) % 1024) (i+j) ≤ max ((fun j : ℕ => (0x2008020080200801f07c1f07c1e0781e0741d0701a0681a06419060160581504c100400f0340a01800 >>> (10*j)) % 1024) i) j + max ((fun j : ℕ => (0x2008020080200801f07c1f07c1e0781e0741d0701a0681a06419060160581504c100400f0340a01800 >>> (10*j)) % 1024) j) i)))
  change (List.range 33).all test=true
  have block0 : (List.range 0).all test=true := rfl
  have block4 := verifyBlocks test 0 4 block0 (by decide +kernel)
  have block8 := verifyBlocks test 4 4 block4 (by decide +kernel)
  have block12 := verifyBlocks test 8 4 block8 (by decide +kernel)
  have block16 := verifyBlocks test 12 4 block12 (by decide +kernel)
  have block20 := verifyBlocks test 16 4 block16 (by decide +kernel)
  have block24 := verifyBlocks test 20 4 block20 (by decide +kernel)
  have block28 := verifyBlocks test 24 4 block24 (by decide +kernel)
  have block32 := verifyBlocks test 28 4 block28 (by decide +kernel)
  have block33 := verifyBlocks test 32 1 block32 (by decide +kernel)
  exact block33

lemma table6 : ∀ i j : Fin (64+1), (fun j : ℕ => (0x802008020080200802007f1fc7f1fc7f1fc7e1f87e1f87e1f47d1f47d1f07c1f07b1ec7a1e0781e0781e0771dc771dc761d8761d4751d0721c8721c8711c4711c0701bc6d1b46d1b06c1ac691a4681986318c6318c6218862184611805e1785e1745d1705a1685915c541505414c53148501404f1344a1284911c44100401003f0fc3e0f03c0ec390d8360d4330c02c0b02b0a4260881d0741c0681704c0e02000 >>> (10*j)) % 1024) (i.val+j.val) ≤ max ((fun j : ℕ => (0x401004010040100400fc3f0fc3f0fc3e0f83e0f83d0f43d0f03c0ec390e4390e4380e0380dc370d8340d0340cc330c8300c02f0b42a0a82a0a4290a0260982508c200801f0741a05816054130400c01c00 >>> (10*j)) % 1024) i.val) j.val + max ((fun j : ℕ => (0x401004010040100400fc3f0fc3f0fc3e0f83e0f83d0f43d0f03c0ec390e4390e4380e0380dc370d8340d0340cc330c8300c02f0b42a0a82a0a4290a0260982508c200801f0741a05816054130400c01c00 >>> (10*j)) % 1024) j.val) i.val := by
  apply verifyRows (fun j : ℕ => (0x401004010040100400fc3f0fc3f0fc3e0f83e0f83d0f43d0f03c0ec390e4390e4380e0380dc370d8340d0340cc330c8300c02f0b42a0a82a0a4290a0260982508c200801f0741a05816054130400c01c00 >>> (10*j)) % 1024) (fun j : ℕ => (0x802008020080200802007f1fc7f1fc7f1fc7e1f87e1f87e1f47d1f47d1f07c1f07b1ec7a1e0781e0781e0771dc771dc761d8761d4751d0721c8721c8711c4711c0701bc6d1b46d1b06c1ac691a4681986318c6318c6218862184611805e1785e1745d1705a1685915c541505414c53148501404f1344a1284911c44100401003f0fc3e0f03c0ec390d8360d4330c02c0b02b0a4260881d0741c0681704c0e02000 >>> (10*j)) % 1024) 64
  let test := (fun i : ℕ => (List.range (64+1)).all (fun j => decide ((fun j : ℕ => (0x802008020080200802007f1fc7f1fc7f1fc7e1f87e1f87e1f47d1f47d1f07c1f07b1ec7a1e0781e0781e0771dc771dc761d8761d4751d0721c8721c8711c4711c0701bc6d1b46d1b06c1ac691a4681986318c6318c6218862184611805e1785e1745d1705a1685915c541505414c53148501404f1344a1284911c44100401003f0fc3e0f03c0ec390d8360d4330c02c0b02b0a4260881d0741c0681704c0e02000 >>> (10*j)) % 1024) (i+j) ≤ max ((fun j : ℕ => (0x401004010040100400fc3f0fc3f0fc3e0f83e0f83d0f43d0f03c0ec390e4390e4380e0380dc370d8340d0340cc330c8300c02f0b42a0a82a0a4290a0260982508c200801f0741a05816054130400c01c00 >>> (10*j)) % 1024) i) j + max ((fun j : ℕ => (0x401004010040100400fc3f0fc3f0fc3e0f83e0f83d0f43d0f03c0ec390e4390e4380e0380dc370d8340d0340cc330c8300c02f0b42a0a82a0a4290a0260982508c200801f0741a05816054130400c01c00 >>> (10*j)) % 1024) j) i)))
  change (List.range 65).all test=true
  have block0 : (List.range 0).all test=true := rfl
  have block4 := verifyBlocks test 0 4 block0 (by decide +kernel)
  have block8 := verifyBlocks test 4 4 block4 (by decide +kernel)
  have block12 := verifyBlocks test 8 4 block8 (by decide +kernel)
  have block16 := verifyBlocks test 12 4 block12 (by decide +kernel)
  have block20 := verifyBlocks test 16 4 block16 (by decide +kernel)
  have block24 := verifyBlocks test 20 4 block20 (by decide +kernel)
  have block28 := verifyBlocks test 24 4 block24 (by decide +kernel)
  have block32 := verifyBlocks test 28 4 block28 (by decide +kernel)
  have block36 := verifyBlocks test 32 4 block32 (by decide +kernel)
  have block40 := verifyBlocks test 36 4 block36 (by decide +kernel)
  have block44 := verifyBlocks test 40 4 block40 (by decide +kernel)
  have block48 := verifyBlocks test 44 4 block44 (by decide +kernel)
  have block52 := verifyBlocks test 48 4 block48 (by decide +kernel)
  have block56 := verifyBlocks test 52 4 block52 (by decide +kernel)
  have block60 := verifyBlocks test 56 4 block56 (by decide +kernel)
  have block64 := verifyBlocks test 60 4 block60 (by decide +kernel)
  have block65 := verifyBlocks test 64 1 block64 (by decide +kernel)
  exact block65

lemma table7 : ∀ i j : Fin (128+1), (fun j : ℕ => (0x100401004010040100401003fcff3fcff3fcff3fcfe3f8fe3f8fe3f8fd3f4fd3f4fd3f0fc3f0fc3ecfb3ecfa3e8f93dcf73dcf73dcf73d8f63d8f63d8f53d4f53d4f43d0f43ccf33c8f03c0f03c0f03bcef3bcef3b8ee3b8ed3b4ec3a8ea3a8ea3a4e93a4e83a0e7394e5394e4390e3384e1380de36cdb36cdb36cda368da368d9364d9360d835cd5354d5354d4350d434cd3348d0340d033ccf338cc330cb324c6318c6318c5314c5310c430cc1304c1300c02fcbd2f4bc2e8b72dcb72d8b62d4b32ccb22c0ad2b4ac2a8a728ca328ca3288a2288a1284a02789e2789d2749c2689a26497250942509324c922409023c8d2288a2248721080200801fc7f1f87c1f07b1e4761d8751cc701b06c1ac69198621745d1745c1705b164591605614c53148501344912448118430fc3a0e8390dc340c02b094250902207c1b0581002400 >>> (10*j)) % 1024) (i.val+j.val) ≤ max ((fun j : ℕ => (0x802008020080200802007f1fc7f1fc7f1fc7e1f87e1f87e1f47d1f47d1f07c1f07b1ec7a1e0781e0781e0771dc771dc761d8761d4751d0721c8721c8711c4711c0701bc6d1b46d1b06c1ac691a4681986318c6318c6218862184611805e1785e1745d1705a1685915c541505414c53148501404f1344a1284911c44100401003f0fc3e0f03c0ec390d8360d4330c02c0b02b0a4260881d0741c0681704c0e02000 >>> (10*j)) % 1024) i.val) j.val + max ((fun j : ℕ => (0x802008020080200802007f1fc7f1fc7f1fc7e1f87e1f87e1f47d1f47d1f07c1f07b1ec7a1e0781e0781e0771dc771dc761d8761d4751d0721c8721c8711c4711c0701bc6d1b46d1b06c1ac691a4681986318c6318c6218862184611805e1785e1745d1705a1685915c541505414c53148501404f1344a1284911c44100401003f0fc3e0f03c0ec390d8360d4330c02c0b02b0a4260881d0741c0681704c0e02000 >>> (10*j)) % 1024) j.val) i.val := by
  apply verifyRows (fun j : ℕ => (0x802008020080200802007f1fc7f1fc7f1fc7e1f87e1f87e1f47d1f47d1f07c1f07b1ec7a1e0781e0781e0771dc771dc761d8761d4751d0721c8721c8711c4711c0701bc6d1b46d1b06c1ac691a4681986318c6318c6218862184611805e1785e1745d1705a1685915c541505414c53148501404f1344a1284911c44100401003f0fc3e0f03c0ec390d8360d4330c02c0b02b0a4260881d0741c0681704c0e02000 >>> (10*j)) % 1024) (fun j : ℕ => (0x100401004010040100401003fcff3fcff3fcff3fcfe3f8fe3f8fe3f8fd3f4fd3f4fd3f0fc3f0fc3ecfb3ecfa3e8f93dcf73dcf73dcf73d8f63d8f63d8f53d4f53d4f43d0f43ccf33c8f03c0f03c0f03bcef3bcef3b8ee3b8ed3b4ec3a8ea3a8ea3a4e93a4e83a0e7394e5394e4390e3384e1380de36cdb36cdb36cda368da368d9364d9360d835cd5354d5354d4350d434cd3348d0340d033ccf338cc330cb324c6318c6318c5314c5310c430cc1304c1300c02fcbd2f4bc2e8b72dcb72d8b62d4b32ccb22c0ad2b4ac2a8a728ca328ca3288a2288a1284a02789e2789d2749c2689a26497250942509324c922409023c8d2288a2248721080200801fc7f1f87c1f07b1e4761d8751cc701b06c1ac69198621745d1745c1705b164591605614c53148501344912448118430fc3a0e8390dc340c02b094250902207c1b0581002400 >>> (10*j)) % 1024) 128
  let test := (fun i : ℕ => (List.range (128+1)).all (fun j => decide ((fun j : ℕ => (0x100401004010040100401003fcff3fcff3fcff3fcfe3f8fe3f8fe3f8fd3f4fd3f4fd3f0fc3f0fc3ecfb3ecfa3e8f93dcf73dcf73dcf73d8f63d8f63d8f53d4f53d4f43d0f43ccf33c8f03c0f03c0f03bcef3bcef3b8ee3b8ed3b4ec3a8ea3a8ea3a4e93a4e83a0e7394e5394e4390e3384e1380de36cdb36cdb36cda368da368d9364d9360d835cd5354d5354d4350d434cd3348d0340d033ccf338cc330cb324c6318c6318c5314c5310c430cc1304c1300c02fcbd2f4bc2e8b72dcb72d8b62d4b32ccb22c0ad2b4ac2a8a728ca328ca3288a2288a1284a02789e2789d2749c2689a26497250942509324c922409023c8d2288a2248721080200801fc7f1f87c1f07b1e4761d8751cc701b06c1ac69198621745d1745c1705b164591605614c53148501344912448118430fc3a0e8390dc340c02b094250902207c1b0581002400 >>> (10*j)) % 1024) (i+j) ≤ max ((fun j : ℕ => (0x802008020080200802007f1fc7f1fc7f1fc7e1f87e1f87e1f47d1f47d1f07c1f07b1ec7a1e0781e0781e0771dc771dc761d8761d4751d0721c8721c8711c4711c0701bc6d1b46d1b06c1ac691a4681986318c6318c6218862184611805e1785e1745d1705a1685915c541505414c53148501404f1344a1284911c44100401003f0fc3e0f03c0ec390d8360d4330c02c0b02b0a4260881d0741c0681704c0e02000 >>> (10*j)) % 1024) i) j + max ((fun j : ℕ => (0x802008020080200802007f1fc7f1fc7f1fc7e1f87e1f87e1f47d1f47d1f07c1f07b1ec7a1e0781e0781e0771dc771dc761d8761d4751d0721c8721c8711c4711c0701bc6d1b46d1b06c1ac691a4681986318c6318c6218862184611805e1785e1745d1705a1685915c541505414c53148501404f1344a1284911c44100401003f0fc3e0f03c0ec390d8360d4330c02c0b02b0a4260881d0741c0681704c0e02000 >>> (10*j)) % 1024) j) i)))
  change (List.range 129).all test=true
  have block0 : (List.range 0).all test=true := rfl
  have block4 := verifyBlocks test 0 4 block0 (by decide +kernel)
  have block8 := verifyBlocks test 4 4 block4 (by decide +kernel)
  have block12 := verifyBlocks test 8 4 block8 (by decide +kernel)
  have block16 := verifyBlocks test 12 4 block12 (by decide +kernel)
  have block20 := verifyBlocks test 16 4 block16 (by decide +kernel)
  have block24 := verifyBlocks test 20 4 block20 (by decide +kernel)
  have block28 := verifyBlocks test 24 4 block24 (by decide +kernel)
  have block32 := verifyBlocks test 28 4 block28 (by decide +kernel)
  have block36 := verifyBlocks test 32 4 block32 (by decide +kernel)
  have block40 := verifyBlocks test 36 4 block36 (by decide +kernel)
  have block44 := verifyBlocks test 40 4 block40 (by decide +kernel)
  have block48 := verifyBlocks test 44 4 block44 (by decide +kernel)
  have block52 := verifyBlocks test 48 4 block48 (by decide +kernel)
  have block56 := verifyBlocks test 52 4 block52 (by decide +kernel)
  have block60 := verifyBlocks test 56 4 block56 (by decide +kernel)
  have block64 := verifyBlocks test 60 4 block60 (by decide +kernel)
  have block68 := verifyBlocks test 64 4 block64 (by decide +kernel)
  have block72 := verifyBlocks test 68 4 block68 (by decide +kernel)
  have block76 := verifyBlocks test 72 4 block72 (by decide +kernel)
  have block80 := verifyBlocks test 76 4 block76 (by decide +kernel)
  have block84 := verifyBlocks test 80 4 block80 (by decide +kernel)
  have block88 := verifyBlocks test 84 4 block84 (by decide +kernel)
  have block92 := verifyBlocks test 88 4 block88 (by decide +kernel)
  have block96 := verifyBlocks test 92 4 block92 (by decide +kernel)
  have block100 := verifyBlocks test 96 4 block96 (by decide +kernel)
  have block104 := verifyBlocks test 100 4 block100 (by decide +kernel)
  have block108 := verifyBlocks test 104 4 block104 (by decide +kernel)
  have block112 := verifyBlocks test 108 4 block108 (by decide +kernel)
  have block116 := verifyBlocks test 112 4 block112 (by decide +kernel)
  have block120 := verifyBlocks test 116 4 block116 (by decide +kernel)
  have block124 := verifyBlocks test 120 4 block120 (by decide +kernel)
  have block128 := verifyBlocks test 124 4 block124 (by decide +kernel)
  have block129 := verifyBlocks test 128 1 block128 (by decide +kernel)
  exact block129

lemma table8 : ∀ i j : Fin (256+1), (fun j : ℕ => if j=158 then 306 else 0) (i.val+j.val) ≤ max ((fun j : ℕ => (0x100401004010040100401003fcff3fcff3fcff3fcfe3f8fe3f8fe3f8fd3f4fd3f4fd3f0fc3f0fc3ecfb3ecfa3e8f93dcf73dcf73dcf73d8f63d8f63d8f53d4f53d4f43d0f43ccf33c8f03c0f03c0f03bcef3bcef3b8ee3b8ed3b4ec3a8ea3a8ea3a4e93a4e83a0e7394e5394e4390e3384e1380de36cdb36cdb36cda368da368d9364d9360d835cd5354d5354d4350d434cd3348d0340d033ccf338cc330cb324c6318c6318c5314c5310c430cc1304c1300c02fcbd2f4bc2e8b72dcb72d8b62d4b32ccb22c0ad2b4ac2a8a728ca328ca3288a2288a1284a02789e2789d2749c2689a26497250942509324c922409023c8d2288a2248721080200801fc7f1f87c1f07b1e4761d8751cc701b06c1ac69198621745d1745c1705b164591605614c53148501344912448118430fc3a0e8390dc340c02b094250902207c1b0581002400 >>> (10*j)) % 1024) i.val) j.val + max ((fun j : ℕ => (0x100401004010040100401003fcff3fcff3fcff3fcfe3f8fe3f8fe3f8fd3f4fd3f4fd3f0fc3f0fc3ecfb3ecfa3e8f93dcf73dcf73dcf73d8f63d8f63d8f53d4f53d4f43d0f43ccf33c8f03c0f03c0f03bcef3bcef3b8ee3b8ed3b4ec3a8ea3a8ea3a4e93a4e83a0e7394e5394e4390e3384e1380de36cdb36cdb36cda368da368d9364d9360d835cd5354d5354d4350d434cd3348d0340d033ccf338cc330cb324c6318c6318c5314c5310c430cc1304c1300c02fcbd2f4bc2e8b72dcb72d8b62d4b32ccb22c0ad2b4ac2a8a728ca328ca3288a2288a1284a02789e2789d2749c2689a26497250942509324c922409023c8d2288a2248721080200801fc7f1f87c1f07b1e4761d8751cc701b06c1ac69198621745d1745c1705b164591605614c53148501344912448118430fc3a0e8390dc340c02b094250902207c1b0581002400 >>> (10*j)) % 1024) j.val) i.val := by
  intro i j
  change (if i.val+j.val=158 then 306 else 0)≤_
  split
  · rename_i eq
    have chk : ∀ t ∈ List.range 159, 306 ≤ max ((fun j : ℕ => (0x100401004010040100401003fcff3fcff3fcff3fcfe3f8fe3f8fe3f8fd3f4fd3f4fd3f0fc3f0fc3ecfb3ecfa3e8f93dcf73dcf73dcf73d8f63d8f63d8f53d4f53d4f43d0f43ccf33c8f03c0f03c0f03bcef3bcef3b8ee3b8ed3b4ec3a8ea3a8ea3a4e93a4e83a0e7394e5394e4390e3384e1380de36cdb36cdb36cda368da368d9364d9360d835cd5354d5354d4350d434cd3348d0340d033ccf338cc330cb324c6318c6318c5314c5310c430cc1304c1300c02fcbd2f4bc2e8b72dcb72d8b62d4b32ccb22c0ad2b4ac2a8a728ca328ca3288a2288a1284a02789e2789d2749c2689a26497250942509324c922409023c8d2288a2248721080200801fc7f1f87c1f07b1e4761d8751cc701b06c1ac69198621745d1745c1705b164591605614c53148501344912448118430fc3a0e8390dc340c02b094250902207c1b0581002400 >>> (10*j)) % 1024) t) (158-t) + max ((fun j : ℕ => (0x100401004010040100401003fcff3fcff3fcff3fcfe3f8fe3f8fe3f8fd3f4fd3f4fd3f0fc3f0fc3ecfb3ecfa3e8f93dcf73dcf73dcf73d8f63d8f63d8f53d4f53d4f43d0f43ccf33c8f03c0f03c0f03bcef3bcef3b8ee3b8ed3b4ec3a8ea3a8ea3a4e93a4e83a0e7394e5394e4390e3384e1380de36cdb36cdb36cda368da368d9364d9360d835cd5354d5354d4350d434cd3348d0340d033ccf338cc330cb324c6318c6318c5314c5310c430cc1304c1300c02fcbd2f4bc2e8b72dcb72d8b62d4b32ccb22c0ad2b4ac2a8a728ca328ca3288a2288a1284a02789e2789d2749c2689a26497250942509324c922409023c8d2288a2248721080200801fc7f1f87c1f07b1e4761d8751cc701b06c1ac69198621745d1745c1705b164591605614c53148501344912448118430fc3a0e8390dc340c02b094250902207c1b0581002400 >>> (10*j)) % 1024) (158-t)) t := by decide +kernel
    have v := chk i.val (List.mem_range.mpr (by omega))
    rwa [show 158-i.val=j.val by omega] at v
  · omega

lemma count_growth (r K gap : ℕ) (positive : 0<K) (topBound : K≤2^r) (M : ℕ) (A : Finset ℕ) (hc : A.card=r) (hA : IsSumDistinctSet A M)
    (growth : ∀ (C : Finset ℕ → ℤ → ℕ), (∀ B, Monotone (C B)) → (∀ B z, C B z ≤ 2^B.card) →
      (∀ B a, a∉B → ∀ z, C (insert a B) z = C B z + C B (z-a)) →
      ∀ B : Finset ℕ, B.card=r → (∀ a∈B, a≤M) → ∀ z, C B z=K → K+gap≤C B (z+M)) : gap≤M := by
  classical
  let val (X : Finset ℕ) : ℤ := (X.sum id : ℕ)
  let P (B : Finset ℕ) (z : ℤ) := B.powerset.filter (fun X => val X ≤ z)
  let C (B : Finset ℕ) (z : ℤ) := (P B z).card
  have sub (B : Finset ℕ) {z w : ℤ} (hw : z≤w) : P B z ⊆ P B w :=
    fun _ h => mem_filter.mpr ⟨(mem_filter.mp h).1,(mem_filter.mp h).2.trans hw⟩
  have monoC (B) : Monotone (C B) := fun _ _ h => card_le_card (sub B h)
  have sizeC (B z) : C B z ≤ 2^B.card := (card_filter_le _ _).trans_eq (card_powerset _)
  have sums (B z) : C B z = ∑ X∈B.powerset, (if val X ≤ z then 1 else 0 : ℕ) := by
    simp [C,P,Finset.sum_boole]
  have stepC (B : Finset ℕ) (a : ℕ) (ha : a∉B) (z : ℤ) :
      C (insert a B) z = C B z + C B (z-a) := by
    rw [sums,sum_powerset_insert ha,sums,sums]
    apply congrArg (_ + ·)
    apply sum_congr rfl
    intro X hX
    have nmem : a∉X := fun q => ha (mem_powerset.mp hX q)
    have vs : val (insert a X) = (a : ℤ) + val X := by simp [val,sum_insert nmem]
    simp only [vs,show ((a:ℤ) + val X ≤ z) ↔ val X ≤ z - a by omega]
  have diff (z : ℤ) (n : ℕ) : C A (z+n) ≤ C A z + n := by
    let D := P A (z+n) \ P A z
    have inj : Set.InjOn val (D : Set (Finset ℕ)) := by
      intro X hx Y hy equal
      have hX := (mem_filter.mp (mem_sdiff.mp hx).1).1
      have hY := (mem_filter.mp (mem_sdiff.mp hy).1).1
      have raw : X.sum id = Y.sum id := Int.ofNat_inj.mp equal
      have e := @hA.2 ⟨X,hX⟩ ⟨Y,hY⟩ raw
      exact congrArg Subtype.val e
    have img : D.image val ⊆ Ioc z (z+n) := by
      intro u hu
      obtain ⟨X,hX,rfl⟩ := mem_image.mp hu
      obtain ⟨hfull,hn⟩ := mem_sdiff.mp hX
      obtain ⟨ha,hi⟩ := mem_filter.mp hfull
      exact mem_Ioc.mpr ⟨lt_of_not_ge (fun h => hn (mem_filter.mpr ⟨ha,h⟩)),hi⟩
    have d := card_le_card img
    rw [card_image_of_injOn inj,Int.card_Ioc] at d
    have eq := card_sdiff_add_card_eq_card (sub A (show z≤z+(n:ℤ) by omega))
    change D.card + C A z = C A (z+n) at eq
    omega
  have left : C A (-1)=0 := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro X h
    have neg := (mem_filter.mp h).2
    have pos : 0≤val X := Int.ofNat_zero_le _
    omega
  have top : K ≤ C A (A.sum id : ℕ) := by
    have all : P A (A.sum id : ℕ) = A.powerset := by
      apply filter_true_of_mem
      intro X hx
      change ((X.sum id : ℕ) : ℤ) ≤ ((A.sum id : ℕ) : ℤ)
      exact_mod_cast (sum_le_sum_of_subset (mem_powerset.mp hx) : X.sum id ≤ A.sum id)
    change K ≤ (P A _).card
    rw [all,card_powerset,hc]
    exact topBound
  let good (t : ℕ) := K ≤ C A (t:ℤ)
  have ex : ∃ t, good t := ⟨A.sum id,top⟩
  let t := Nat.find ex
  have cur : K≤C A (t:ℤ) := Nat.find_spec ex
  have before : C A ((t:ℤ)-1) < K := by
    by_cases zero : t=0
    · simpa [zero,left] using positive
    · have h : ¬good (t-1) := Nat.find_min ex (show t-1<t by omega)
      change ¬K ≤ C A ((t-1 : ℕ):ℤ) at h
      rw [Nat.cast_sub (by omega : 1≤t),Nat.cast_one] at h
      exact Nat.lt_of_not_ge h
  have upper := diff ((t:ℤ)-1) 1
  simp only [Nat.cast_one,sub_add_cancel] at upper
  have hit : C A (t:ℤ)=K := by omega
  have large := growth C monoC sizeC stepC A hc (fun a ha => (mem_Icc.mp (hA.1 ha)).2) t hit
  have short := diff (t:ℤ) M
  omega
lemma all_growth (C : Finset ℕ → ℤ → ℕ) (M : ℕ)
    (monoC : ∀ A, Monotone (C A)) (sizeC : ∀ A z, C A z ≤ 2^A.card)
    (stepC : ∀ A a, a∉A → ∀ z, C (insert a A) z = C A z + C A (z-a)) :
    (∀ B : Finset ℕ, B.card=1 → (∀ a∈B, a≤M) → ∀ z, C B z=1 → 1+1≤C B (z+M)) ∧
    (∀ B : Finset ℕ, B.card=2 → (∀ a∈B, a≤M) → ∀ z, C B z=1 → 1+2≤C B (z+M)) ∧
    (∀ B : Finset ℕ, B.card=3 → (∀ a∈B, a≤M) → ∀ z, C B z=2 → 2+4≤C B (z+M)) ∧
    (∀ B : Finset ℕ, B.card=4 → (∀ a∈B, a≤M) → ∀ z, C B z=3 → 3+7≤C B (z+M)) ∧
    (∀ B : Finset ℕ, B.card=5 → (∀ a∈B, a≤M) → ∀ z, C B z=8 → 8+13≤C B (z+M)) ∧
    (∀ B : Finset ℕ, B.card=6 → (∀ a∈B, a≤M) → ∀ z, C B z=14 → 14+23≤C B (z+M)) ∧
    (∀ B : Finset ℕ, B.card=7 → (∀ a∈B, a≤M) → ∀ z, C B z=36 → 36+43≤C B (z+M)) ∧
    (∀ B : Finset ℕ, B.card=8 → (∀ a∈B, a≤M) → ∀ z, C B z=65 → 65+78≤C B (z+M)) ∧
    (∀ B : Finset ℕ, B.card=9 → (∀ a∈B, a≤M) → ∀ z, C B z=158 → 158+148≤C B (z+M)) := by
  have base : ∀ A : Finset ℕ, A.card=0 → (∀ a∈A, a≤M) → ∀ z, id (C A z) ≤ C A (z+M) :=
    fun A _ _ z => monoC A (show z ≤ z + (M:ℤ) by omega)
  have h1 := iterate C M monoC sizeC stepC 0 id (fun j : ℕ => (0x200800 >>> (10*j)) % 1024) base table0
  have h2 := iterate C M monoC sizeC stepC 1 (fun j : ℕ => (0x200800 >>> (10*j)) % 1024) (fun j : ℕ => (0x40100400c00 >>> (10*j)) % 1024) h1 table1
  have h3 := iterate C M monoC sizeC stepC 2 (fun j : ℕ => (0x40100400c00 >>> (10*j)) % 1024) (fun j : ℕ => (0x8020080200701c0601000 >>> (10*j)) % 1024) h2 table2
  have h4 := iterate C M monoC sizeC stepC 3 (fun j : ℕ => (0x8020080200701c0601000 >>> (10*j)) % 1024) (fun j : ℕ => (0x10040100401003c0f03c0e0380d02c0b0280801400 >>> (10*j)) % 1024) h3 table3
  have h5 := iterate C M monoC sizeC stepC 4 (fun j : ℕ => (0x10040100401003c0f03c0e0380d02c0b0280801400 >>> (10*j)) % 1024) (fun j : ℕ => (0x2008020080200801f07c1f07c1e0781e0741d0701a0681a06419060160581504c100400f0340a01800 >>> (10*j)) % 1024) h4 table4
  have h6 := iterate C M monoC sizeC stepC 5 (fun j : ℕ => (0x2008020080200801f07c1f07c1e0781e0741d0701a0681a06419060160581504c100400f0340a01800 >>> (10*j)) % 1024) (fun j : ℕ => (0x401004010040100400fc3f0fc3f0fc3e0f83e0f83d0f43d0f03c0ec390e4390e4380e0380dc370d8340d0340cc330c8300c02f0b42a0a82a0a4290a0260982508c200801f0741a05816054130400c01c00 >>> (10*j)) % 1024) h5 table5
  have h7 := iterate C M monoC sizeC stepC 6 (fun j : ℕ => (0x401004010040100400fc3f0fc3f0fc3e0f83e0f83d0f43d0f03c0ec390e4390e4380e0380dc370d8340d0340cc330c8300c02f0b42a0a82a0a4290a0260982508c200801f0741a05816054130400c01c00 >>> (10*j)) % 1024) (fun j : ℕ => (0x802008020080200802007f1fc7f1fc7f1fc7e1f87e1f87e1f47d1f47d1f07c1f07b1ec7a1e0781e0781e0771dc771dc761d8761d4751d0721c8721c8711c4711c0701bc6d1b46d1b06c1ac691a4681986318c6318c6218862184611805e1785e1745d1705a1685915c541505414c53148501404f1344a1284911c44100401003f0fc3e0f03c0ec390d8360d4330c02c0b02b0a4260881d0741c0681704c0e02000 >>> (10*j)) % 1024) h6 table6
  have h8 := iterate C M monoC sizeC stepC 7 (fun j : ℕ => (0x802008020080200802007f1fc7f1fc7f1fc7e1f87e1f87e1f47d1f47d1f07c1f07b1ec7a1e0781e0781e0771dc771dc761d8761d4751d0721c8721c8711c4711c0701bc6d1b46d1b06c1ac691a4681986318c6318c6218862184611805e1785e1745d1705a1685915c541505414c53148501404f1344a1284911c44100401003f0fc3e0f03c0ec390d8360d4330c02c0b02b0a4260881d0741c0681704c0e02000 >>> (10*j)) % 1024) (fun j : ℕ => (0x100401004010040100401003fcff3fcff3fcff3fcfe3f8fe3f8fe3f8fd3f4fd3f4fd3f0fc3f0fc3ecfb3ecfa3e8f93dcf73dcf73dcf73d8f63d8f63d8f53d4f53d4f43d0f43ccf33c8f03c0f03c0f03bcef3bcef3b8ee3b8ed3b4ec3a8ea3a8ea3a4e93a4e83a0e7394e5394e4390e3384e1380de36cdb36cdb36cda368da368d9364d9360d835cd5354d5354d4350d434cd3348d0340d033ccf338cc330cb324c6318c6318c5314c5310c430cc1304c1300c02fcbd2f4bc2e8b72dcb72d8b62d4b32ccb22c0ad2b4ac2a8a728ca328ca3288a2288a1284a02789e2789d2749c2689a26497250942509324c922409023c8d2288a2248721080200801fc7f1f87c1f07b1e4761d8751cc701b06c1ac69198621745d1745c1705b164591605614c53148501344912448118430fc3a0e8390dc340c02b094250902207c1b0581002400 >>> (10*j)) % 1024) h7 table7
  have h9 := iterate C M monoC sizeC stepC 8 (fun j : ℕ => (0x100401004010040100401003fcff3fcff3fcff3fcfe3f8fe3f8fe3f8fd3f4fd3f4fd3f0fc3f0fc3ecfb3ecfa3e8f93dcf73dcf73dcf73d8f63d8f63d8f53d4f53d4f43d0f43ccf33c8f03c0f03c0f03bcef3bcef3b8ee3b8ed3b4ec3a8ea3a8ea3a4e93a4e83a0e7394e5394e4390e3384e1380de36cdb36cdb36cda368da368d9364d9360d835cd5354d5354d4350d434cd3348d0340d033ccf338cc330cb324c6318c6318c5314c5310c430cc1304c1300c02fcbd2f4bc2e8b72dcb72d8b62d4b32ccb22c0ad2b4ac2a8a728ca328ca3288a2288a1284a02789e2789d2749c2689a26497250942509324c922409023c8d2288a2248721080200801fc7f1f87c1f07b1e4761d8751cc701b06c1ac69198621745d1745c1705b164591605614c53148501344912448118430fc3a0e8390dc340c02b094250902207c1b0581002400 >>> (10*j)) % 1024) (fun j : ℕ => if j=158 then 306 else 0) h8 table8
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ⟩
  · intro B hc hb z hit
    have res := h1 B hc hb z
    rw [hit] at res
    exact res
  · intro B hc hb z hit
    have res := h2 B hc hb z
    rw [hit] at res
    exact res
  · intro B hc hb z hit
    have res := h3 B hc hb z
    rw [hit] at res
    exact res
  · intro B hc hb z hit
    have res := h4 B hc hb z
    rw [hit] at res
    exact res
  · intro B hc hb z hit
    have res := h5 B hc hb z
    rw [hit] at res
    exact res
  · intro B hc hb z hit
    have res := h6 B hc hb z
    rw [hit] at res
    exact res
  · intro B hc hb z hit
    have res := h7 B hc hb z
    rw [hit] at res
    exact res
  · intro B hc hb z hit
    have res := h8 B hc hb z
    rw [hit] at res
    exact res
  · intro B hc hb z hit
    have res := h9 B hc hb z
    rw [hit] at res
    exact res
lemma lower (A : Finset ℕ) (M : ℕ) (r : ℕ) (small : r≤9) (hc : A.card=r) (distinct : IsSumDistinctSet A M) :
    ([0,1,2,4,7,13,23,43,78,148] : List ℕ)[r]! ≤ M := by
  interval_cases r
  · exact Nat.zero_le M
  · exact count_growth 1 1 1 (by decide) (by decide) M A hc distinct (fun C mono sz step => (all_growth C M mono sz step).1)
  · exact count_growth 2 1 2 (by decide) (by decide) M A hc distinct (fun C mono sz step => (all_growth C M mono sz step).2.1)
  · exact count_growth 3 2 4 (by decide) (by decide) M A hc distinct (fun C mono sz step => (all_growth C M mono sz step).2.2.1)
  · exact count_growth 4 3 7 (by decide) (by decide) M A hc distinct (fun C mono sz step => (all_growth C M mono sz step).2.2.2.1)
  · exact count_growth 5 8 13 (by decide) (by decide) M A hc distinct (fun C mono sz step => (all_growth C M mono sz step).2.2.2.2.1)
  · exact count_growth 6 14 23 (by decide) (by decide) M A hc distinct (fun C mono sz step => (all_growth C M mono sz step).2.2.2.2.2.1)
  · exact count_growth 7 36 43 (by decide) (by decide) M A hc distinct (fun C mono sz step => (all_growth C M mono sz step).2.2.2.2.2.2.1)
  · exact count_growth 8 65 78 (by decide) (by decide) M A hc distinct (fun C mono sz step => (all_growth C M mono sz step).2.2.2.2.2.2.2.1)
  · exact count_growth 9 158 148 (by decide) (by decide) M A hc distinct (fun C mono sz step => (all_growth C M mono sz step).2.2.2.2.2.2.2.2)

end SumWindow
namespace SumSearch
open Finset Erdos1
open scoped Classical

lemma add_difference (S : Finset ℕ) (a mask : ℕ) (ne : a∉S)
    (sound : ∀ i, mask.testBit i = true → ∃ X⊆S, ∃ Y⊆S,
      (X.sum id : ℕ) + 1440 = (Y.sum id : ℕ) + i) :
    ∀ i, ((mask ||| (mask <<< a)) ||| (mask >>> a)).testBit i=true →
      ∃ X⊆insert a S, ∃ Y⊆insert a S, (X.sum id : ℕ)+1440 = (Y.sum id : ℕ)+i := by
  intro i hi
  simp only [Nat.testBit_or,Bool.or_eq_true,Nat.testBit_shiftLeft,Nat.testBit_shiftRight,
    Bool.and_eq_true,decide_eq_true_eq] at hi
  rcases hi with (hs|⟨he,hs⟩)|hs
  · obtain ⟨X,hX,Y,hY,v⟩ := sound _ hs
    exact ⟨X,hX.trans (subset_insert _ _),Y,hY.trans (subset_insert _ _),v⟩
  · obtain ⟨X,hX,Y,hY,v⟩ := sound _ hs
    refine ⟨insert a X,insert_subset_insert _ hX,Y,hY.trans (subset_insert _ _),?_⟩
    rw [sum_insert (fun h => ne (hX h))]; simp only [id_eq] at *; omega
  · obtain ⟨X,hX,Y,hY,v⟩ := sound _ hs
    refine ⟨X,hX.trans (subset_insert _ _),insert a Y,insert_subset_insert _ hY,?_⟩
    rw [sum_insert (fun h => ne (hY h))]; simp only [id_eq] at *; omega

lemma free_difference (A S : Finset ℕ) (M mask a : ℕ) (dist : IsSumDistinctSet A M) (sub : S⊆A)
    (ha : a∈A) (ne : a∉S)
    (sound : ∀ i, mask.testBit i = true → ∃ X⊆S, ∃ Y⊆S,
      (X.sum id : ℕ)+1440=(Y.sum id : ℕ)+i) : mask.testBit (1440+a) = false := by
  by_contra h
  have bit : mask.testBit (1440+a)=true := by cases t : mask.testBit (1440+a) <;> simp_all
  obtain ⟨X,hX,Y,hY,val⟩ := sound _ bit
  have xA := mem_powerset.mpr (hX.trans sub)
  have yA := mem_powerset.mpr (insert_subset ha (hY.trans sub))
  have eq : X.sum id = (insert a Y).sum id := by
    rw [sum_insert (fun h => ne (hY h))]; simp only [id_eq] at *; omega
  have same := congrArg Subtype.val (@dist.2 ⟨X,xA⟩ ⟨insert a Y,yA⟩ eq)
  change X=insert a Y at same
  exact ne (hX (same ▸ mem_insert_self _ _))

lemma restrict_distinct {B A : Finset ℕ} {M c : ℕ} (dist : IsSumDistinctSet A M) (sub : B⊆A)
    (cap : ∀ b∈B, b≤c) : IsSumDistinctSet B c := by
  refine ⟨fun b hb => mem_Icc.mpr ⟨(mem_Icc.mp (dist.1 (sub hb))).1,cap b hb⟩,?_⟩
  rintro ⟨X,hX⟩ ⟨Y,hY⟩ eq
  have hx := mem_powerset.mpr ((mem_powerset.mp hX).trans sub)
  have hy := mem_powerset.mpr ((mem_powerset.mp hY).trans sub)
  exact Subtype.ext (congrArg (fun t : A.powerset => t.val) (@dist.2 ⟨X,hx⟩ ⟨Y,hy⟩ eq))

lemma solver_sound (F : ℕ → ℕ → ℕ → Bool) (zero : ∀ c m, F 0 c m=true)
    (succ : ∀ r c m, F (r+1) c m =
      (List.range' 1 c).any (fun x => decide (([0,1,2,4,7,13,23,43,78,148] : List ℕ)[r+1]! ≤ x) && (!(m.testBit (1440+x)) &&
        F r (x-1) ((m ||| (m <<< x)) ||| (m >>> x)))))
    (lower : ∀ (B : Finset ℕ) (t r : ℕ), r≤9 → B.card=r → IsSumDistinctSet B t → ([0,1,2,4,7,13,23,43,78,148] : List ℕ)[r]! ≤ t)
    (A : Finset ℕ) (M : ℕ) (dist : IsSumDistinctSet A M) (space : A.card≤9) :
    ∀ r (B S : Finset ℕ) (c m : ℕ), B.card=r → B⊆A → S⊆A → Disjoint B S →
      (∀ x∈B, x≤c) →
      (∀ i, m.testBit i=true → ∃ X⊆S, ∃ Y⊆S, (X.sum id : ℕ)+1440 = (Y.sum id : ℕ)+i) →
      F r c m = true := by
  intro r
  induction r with
  | zero => intros; apply zero
  | succ r ih =>
    intro B S c m bc bA sA sep cap sound
    have nz := card_pos.mp (show 0<B.card by omega)
    let x := B.max' nz
    have mem : x∈B := max'_mem _ _
    have xmax (b) (hb : b∈B) : b≤x := le_max' _ _ hb
    have pos := (mem_Icc.mp (dist.1 (bA mem))).1
    have ne : x∉S := (Finset.disjoint_left.mp sep) mem
    rw [succ,List.any_eq_true]
    refine ⟨x,?_,?_⟩
    · simp only [List.mem_range'_1]; have := cap x mem; omega
    · have rem : r+1≤9 := bc ▸ (card_le_card bA).trans space
      have enough := lower B x (r+1) rem bc (restrict_distinct dist bA xmax)
      rw [decide_eq_true enough,Bool.true_and,free_difference A S M m x dist sA (bA mem) ne sound]
      change F r (x-1) _ = true
      apply ih (B.erase x) (insert x S) (x-1) _ (by simp [card_erase_of_mem mem,bc]) ((erase_subset _ _).trans bA)
        (insert_subset (bA mem) sA)
      · apply Finset.disjoint_left.mpr
        intro b hb h
        rcases mem_insert.mp h with h|h
        · exact (mem_erase.mp hb).1 h
        · exact (Finset.disjoint_left.mp sep) (mem_erase.mp hb).2 h
      · intro b hb
        have := xmax b (mem_erase.mp hb).2
        have := (mem_erase.mp hb).1
        omega
      · exact add_difference _ _ _ ne sound

end SumSearch
namespace OMA.R_Erdos1_erdos_1_variants_least_N_9_R1_H2_R1
open Finset Erdos1
open scoped Classical

/-- Check the signed subset-sum differences for largest elements 148 through 156. -/
def H1 : Prop :=
  let search := Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun r recur c mask => (List.range' 1 c).any (fun x =>
      decide (([0,1,2,4,7,13,23,43,78,148] : List ℕ)[r+1]! ≤ x) &&
      (!(mask.testBit (1440+x)) && recur (x-1) ((mask ||| (mask <<< x)) ||| (mask >>> x)))))
  (List.range' 148 9).all (fun m => !search 8 (m-1) (((2^1440 : ℕ) ||| ((2^1440 : ℕ) <<< m)) ||| ((2^1440 : ℕ) >>> m))) = true

/-- Check the signed subset-sum differences for largest elements 157 through 160. -/
def H2 : Prop :=
  let search := Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun r recur c mask => (List.range' 1 c).any (fun x =>
      decide (([0,1,2,4,7,13,23,43,78,148] : List ℕ)[r+1]! ≤ x) &&
      (!(mask.testBit (1440+x)) && recur (x-1) ((mask ||| (mask <<< x)) ||| (mask >>> x)))))
  (List.range' 157 4).all (fun m => !search 8 (m-1) (((2^1440 : ℕ) ||| ((2^1440 : ℕ) <<< m)) ||| ((2^1440 : ℕ) >>> m))) = true

set_option maxRecDepth 3000 in
theorem main : H1 → H2 → OMA.R_Erdos1_erdos_1_variants_least_N_9_R1.H2 := by
  intro h1 h2 N A dist card
  unfold H1 at h1
  unfold H2 at h2
  by_contra! hn
  let search := Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun r recur c mask => (List.range' 1 c).any (fun x =>
      decide (([0,1,2,4,7,13,23,43,78,148] : List ℕ)[r+1]! ≤ x) &&
      (!(mask.testBit (1440+x)) && recur (x-1) ((mask ||| (mask <<< x)) ||| (mask >>> x)))))
  let init := (2^1440 : ℕ)
  let mask (m : ℕ) := (init ||| (init <<< m)) ||| (init >>> m)
  have small : ∀ m ∈ List.range' 148 9, (!(search 8 (m-1) (mask m))) = true := by
    dsimp only [search,mask,init]
    exact List.all_eq_true.mp h1
  have large : ∀ m ∈ List.range' 157 4, (!(search 8 (m-1) (mask m))) = true := by
    dsimp only [search,mask,init]
    exact List.all_eq_true.mp h2
  have nz : A.Nonempty := card_pos.mp (by omega)
  let m := A.max' nz
  have hm : m∈A := max'_mem _ _
  have cap : ∀ a ∈ A, a ≤ m := fun a ha => Finset.le_max' A a ha
  have low : 148 ≤ m := SumWindow.lower A m 9 (by decide) card (SumSearch.restrict_distinct dist (Subset.rfl) cap)
  have high := (mem_Icc.mp (dist.1 hm)).2
  have absent : (!(search 8 (m-1) (mask m))) = true := by
    by_cases ch : m≤156
    · exact small m (by simp only [List.mem_range'_1]; omega)
    · exact large m (by simp only [List.mem_range'_1]; omega)
  have base : ∀ i, init.testBit i=true → ∃ X⊆(∅ : Finset ℕ), ∃ Y⊆(∅ : Finset ℕ), (X.sum id : ℕ)+1440=(Y.sum id : ℕ)+i := by
    intro i hi
    have e : 1440=i := of_decide_eq_true (Nat.testBit_two_pow ▸ hi)
    exact ⟨∅,Subset.rfl,∅,Subset.rfl,by simp [e]⟩
  have seeded := SumSearch.add_difference ∅ m init (by simp) base
  have ok := SumSearch.solver_sound search (fun _ _ => rfl) (fun _ _ _ => rfl) SumWindow.lower A N dist (by omega)
    8 (A.erase m) (insert m ∅) (m-1) (mask m) (by simp [card_erase_of_mem hm,card]) (erase_subset _ _)
    (by simpa using hm) (by simp) (fun b hb => by have b1 := cap b (mem_erase.mp hb).2; have b2 := (mem_erase.mp hb).1; omega) seeded
  simp [ok] at absent
end OMA.R_Erdos1_erdos_1_variants_least_N_9_R1_H2_R1
