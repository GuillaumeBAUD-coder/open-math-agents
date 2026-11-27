import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1

namespace CubicEight

abbrev V := Fin 8

def bit (w : Nat) (i j : V) : Bool := w.testBit (8 * i.val + j.val)

def atIndex (q : Nat) (i : V) : V := ⟨(q >>> (3*i.val)) % 8, Nat.mod_lt _ (by decide)⟩

def masks : List Nat := [7, 11, 13, 14, 19, 21, 22, 25, 26, 28, 35, 37, 38, 41, 42, 44, 49, 50, 52, 56, 67, 69, 70, 73, 74, 76, 81, 82, 84, 88, 97, 98, 100, 104, 112, 131, 133, 134, 137, 138, 140, 145, 146, 148, 152, 161, 162, 164, 168, 176, 193, 194, 196, 200, 208, 224]

def neighbors (r : Nat) : Finset V := Finset.univ.filter fun j => r.testBit j.val

set_option maxHeartbeats 4000000 in
theorem encode : ∀ s : Finset V, s.card = 3 → ∃ r ∈ masks, neighbors r = s := by
  decide +kernel

abbrev Table := List (Nat × List (Nat × (Nat × Nat)))

def fits (k : V) (w r : Nat) : Prop :=
  r.testBit k.val = false ∧ ∀ i : V, i < k → r.testBit i.val = bit w i k

instance (k : V) (w r : Nat) : Decidable (fits k w r) := by unfold fits; infer_instance

def checkStep (k : V) (old new : List Nat) (table : Table) : Prop :=
  ∀ w ∈ old, ∀ r ∈ masks, fits k w r →
    let result := (((table.lookup w).getD []).lookup r).getD (0,0)
    let v := result.1
    let f := atIndex result.2
    v ∈ new ∧ (∀ a b : V, f a = f b → a = b) ∧
    ∀ i j : V, i ≤ k → f i ≤ k ∧
      bit v i j = (if f i < k then bit w (f i) (f j) else r.testBit (f j).val)

instance (k : V) (old new : List Nat) (table : Table) : Decidable (checkStep k old new table) := by
  unfold checkStep
  infer_instance

def stage (G : V → V → Bool) (n : Nat) (ws : List Nat) : Prop :=
  ∃ e : Equiv.Perm V, ∃ w ∈ ws, ∀ i j : V, i.val < n → G (e i) (e j) = bit w i j

theorem advance {G : V → V → Bool} (symm : ∀ a b, G a b = G b a)
    (diag : ∀ a, G a a = false)
    (degree : ∀ a, (Finset.univ.filter fun b => G a b = true).card = 3)
    {k : V} {old new : List Nat} {table : Table}
    (hc : checkStep k old new table) (hs : stage G k.val old) : stage G (k.val+1) new := by
  obtain ⟨e,w,hw,hm⟩ := hs
  let s := Finset.univ.filter fun j : V => G (e k) (e j) = true
  have hs3 : s.card = 3 := by
    unfold s
    rw [← Finset.card_map (f := e.toEmbedding), Finset.map_filter]
    simpa using degree (e k)
  obtain ⟨r,hr,he⟩ := encode s hs3
  have row (j : V) : G (e k) (e j) = r.testBit j.val := by
    have h := Finset.ext_iff.mp he j
    simp [neighbors,s] at h
    cases h₁ : G (e k) (e j) <;> cases h₂ : r.testBit j.val <;> simp_all
  have fit : fits k w r := by
    constructor
    · rw [← row, diag]
    · intro i hi
      rw [← row, symm, hm i k hi]
  obtain ⟨hn,hinj,hv⟩ := hc w hw r hr fit
  let f := atIndex ((((table.lookup w).getD []).lookup r).getD (0,0)).2
  let p := Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩
  refine ⟨p.trans e, _, hn, ?_⟩
  intro i j hi
  have h := hv i j (by change i.val ≤ k.val; omega)
  change G (e (f i)) (e (f j)) = _
  rw [h.2]
  change G (e (f i)) (e (f j)) = if f i < k then _ else _
  split_ifs with hij
  · exact hm _ _ hij
  · have hki : f i = k := le_antisymm h.1 (le_of_not_gt hij)
    rw [hki, row]

def layer0 : List Nat := [0]

def layer1 : List Nat := [14]

def layer2 : List Nat := [0xd0e, 0x150e, 0x310e]

def layer3 : List Nat := [0xb0d0e, 0xb150e, 0xb641c, 0x132c1c, 0x1a251a, 0x23150e, 0x432c1c, 0x83641c]

def layer4 : List Nat := [0x70b0d0e, 0x70b1c1c, 0x70b2c1c, 0x719681c, 0x71a4c38, 0x729381c, 0x789681c, 0x13132c1c, 0x13232c1c, 0x13432c1c, 0x16292916, 0x16492916, 0x23924c38, 0x23c1381c, 0x26895834, 0x32834c34, 0x83432c1c]

def layer5 : List Nat := [0x70719381c, 0x707383838, 0x707385838, 0x707985838, 0x72331381c, 0x72351381c, 0x72370191a, 0x723d03838, 0x723d05838, 0x72558311a, 0x745987038, 0x76191701c, 0x761d0311a, 0x78351381c, 0x78370191a, 0x783705838, 0x7e0131516, 0x23258a5438, 0x2326895834, 0x23458a5438, 0x2346895834, 0x264598512a]

def layer6 : List Nat := [0x70707383838, 0x70743703838, 0x70783703838, 0x707c1323438, 0x707c1b07038, 0x70b152a3438, 0x70b15687038, 0x70b15a87038, 0x70b51623438, 0x70b51e07038, 0x70b54683132, 0x70b54a87070, 0x70b54a8b070, 0x70b91623438, 0x70b91e07038, 0x70b94683132, 0x74345a87038, 0x743c4297034, 0x74583b06838, 0x74952a16834, 0x74954a86132, 0x74992616834, 0x74992a16834, 0x74992a22c70, 0x78385687038, 0x783c4297034, 0x783c4683132, 0x7c8d0232526]

def layer7 : List Nat := [0x7070b94687070, 0x7078992e06870, 0x70b0d32d06870, 0x70b0db0d0e070, 0x70b85a2d06870, 0x70b85a458e070, 0x70b8c31526468, 0x70b8c31d0e068, 0x70b8c34586162, 0x70b8c3458e0e0, 0x71929b0c2c470, 0x7192ab0c1d064, 0x798a8b0434546]

def layer8 : List Nat := [0xe32546891a1c10e, 0x161a1ce061a1c10e, 0x162a54a851a1c10e, 0x162a58a46191c10e, 0x163858e06183850e, 0x70b0d0e0070b0d0e]

def table0 : List (Nat × List (Nat × (Nat × Nat))) := [(0, [(14, (14, 0xfac688)), (22, (14, 0xfab888)), (26, (14, 0xfaa8c8)), (28, (14, 0xfa98d0)), (38, (14, 0xfa3a88)), (42, (14, 0xfa2ac8)), (44, (14, 0xfa1ad0)), (50, (14, 0xf9ab08)), (52, (14, 0xf99b10)), (56, (14, 0xf91b18)), (70, (14, 0xf63c88)), (74, (14, 0xf62cc8)), (76, (14, 0xf61cd0)), (82, (14, 0xf5ad08)), (84, (14, 0xf59d10)), (88, (14, 0xf51d18)), (98, (14, 0xf1ad48)), (100, (14, 0xf19d50)), (104, (14, 0xf11d58)), (112, (14, 0xed1d60)), (134, (14, 0xd63e88)), (138, (14, 0xd62ec8)), (140, (14, 0xd61ed0)), (146, (14, 0xd5af08)), (148, (14, 0xd59f10)), (152, (14, 0xd51f18)), (162, (14, 0xd1af48)), (164, (14, 0xd19f50)), (168, (14, 0xd11f58)), (176, (14, 0xcd1f60)), (194, (14, 0xb1af88)), (196, (14, 0xb19f90)), (200, (14, 0xb11f98)), (208, (14, 0xad1fa0)), (224, (14, 0x8d1fa8))])]

def table1 : List (Nat × List (Nat × (Nat × Nat))) := [(14, [(13, (0xd0e, 0xfac688)), (21, (0x150e, 0xfac688)), (25, (0x150e, 0xfac4c8)), (37, (0x150e, 0xfa5688)), (41, (0x150e, 0xfa54c8)), (49, (0x310e, 0xfac688)), (69, (0x150e, 0xf66688)), (73, (0x150e, 0xf664c8)), (81, (0x310e, 0xf74688)), (97, (0x310e, 0xf35688)), (133, (0x150e, 0xd67688)), (137, (0x150e, 0xd674c8)), (145, (0x310e, 0xd7c688)), (161, (0x310e, 0xd3d688)), (193, (0x310e, 0xb3e688))])]

def table2 : List (Nat × List (Nat × (Nat × Nat))) := [(0xd0e, [(11, (0xb0d0e, 0xfac688)), (19, (0xb150e, 0xfac650)), (35, (0xb150e, 0xfa5650)), (67, (0xb150e, 0xf66650)), (131, (0xb150e, 0xd67650))]), (0x150e, [(11, (0xb150e, 0xfac688)), (19, (0xb150e, 0xfab881)), (35, (0x23150e, 0xfac688)), (67, (0x23150e, 0xf74688)), (131, (0x23150e, 0xd7c688))]), (0x310e, [(25, (0x132c1c, 0xfab80a)), (41, (0x132c1c, 0xfa3a0a)), (49, (0x1a251a, 0xf9d881)), (73, (0xb641c, 0xf6660a)), (81, (0x432c1c, 0xef5811)), (97, (0x432c1c, 0xef4a11)), (137, (0xb641c, 0xd6760a)), (145, (0x432c1c, 0xcfd811)), (161, (0x432c1c, 0xcfca11)), (193, (0x83641c, 0x7f5811))])]

def table3 : List (Nat × List (Nat × (Nat × Nat))) := [(0xb0d0e, [(7, (0x70b0d0e, 0xfac688))]), (0xb150e, [(21, (0x70b1c1c, 0xfac419)), (37, (0x70b2c1c, 0xfac419)), (69, (0x70b2c1c, 0xf74419)), (133, (0x70b2c1c, 0xd7c419))]), (0xb641c, [(21, (0x719681c, 0xfac4c8)), (37, (0x71a4c38, 0xf354c1)), (69, (0x71a4c38, 0xf2e4c1)), (133, (0x789681c, 0xfac4c8))]), (0x132c1c, [(19, (0x13132c1c, 0xfac688)), (35, (0x13232c1c, 0xfac4c8)), (67, (0x13432c1c, 0xfac4c8)), (131, (0x13432c1c, 0xdec4c8))]), (0x1a251a, [(21, (0x13132c1c, 0xfac40b)), (37, (0x16292916, 0xfac4c8)), (69, (0x16492916, 0xfac4c8)), (133, (0x16492916, 0xdec4c8))]), (0x23150e, [(49, (0x729381c, 0xfac099)), (81, (0x71a4c38, 0xf74053)), (97, (0x71a4c38, 0xf3508b)), (145, (0x71a4c38, 0xd7c053)), (161, (0x71a4c38, 0xd3d08b)), (193, (0x789681c, 0xbf4099))]), (0x432c1c, [(19, (0x13432c1c, 0xfac688)), (35, (0x13432c1c, 0xfa5681)), (67, (0x16492916, 0xf66642)), (131, (0x83432c1c, 0xfac688))]), (0x83641c, [(49, (0x23924c38, 0xde5053)), (81, (0x23924c38, 0xbe6053)), (97, (0x32834c34, 0xf35681)), (145, (0x23c1381c, 0xd6705a)), (161, (0x26895834, 0x9bd40b)), (193, (0x26895834, 0x97e40b))])]

def table4 : List (Nat × List (Nat × (Nat × Nat))) := [(0x70b0d0e, [(224, (0x7e0131516, 0xfab888))]), (0x70b1c1c, [(35, (0x70719381c, 0xfa90e2)), (67, (0x70719381c, 0xf710e2)), (131, (0x70719381c, 0xd790e2))]), (0x70b2c1c, [(97, (0x72370191a, 0xfa831a)), (161, (0x72370191a, 0xde831a)), (193, (0x78370191a, 0xbf031a))]), (0x719681c, [(37, (0x72370191a, 0xfab850)), (69, (0x72370191a, 0xf73850)), (133, (0x78370191a, 0xfab850))]), (0x71a4c38, [(37, (0x72351381c, 0xfab842)), (69, (0x72558311a, 0xf7380a)), (133, (0x78351381c, 0xfab842))]), (0x729381c, [(35, (0x72331381c, 0xfab888)), (67, (0x72558311a, 0xfa8313)), (131, (0x72558311a, 0xde8313))]), (0x789681c, [(97, (0x76191701c, 0xfab888)), (161, (0x761d0311a, 0xd7b850)), (193, (0x761d0311a, 0xbbb850))]), (0x13132c1c, [(13, (0x70719381c, 0xfab508))]), (0x13232c1c, [(41, (0x72331381c, 0xfab508)), (73, (0x72351381c, 0xfab508)), (137, (0x72351381c, 0xdeb508))]), (0x13432c1c, [(41, (0x72558311a, 0xfa82a3)), (73, (0x72558311a, 0xf73460)), (137, (0x78351381c, 0xdeb508))]), (0x16292916, [(41, (0x707383838, 0xfab111)), (73, (0x707385838, 0xfab0a1)), (137, (0x707385838, 0xdeb0a1))]), (0x16492916, [(41, (0x707385838, 0xfab111)), (73, (0x707385838, 0xf7310a)), (137, (0x707985838, 0xfab111))]), (0x23924c38, [(37, (0x23258a5438, 0xfab888)), (69, (0x23458a5438, 0xfab888)), (133, (0x2346895834, 0xd7c642))]), (0x23c1381c, [(35, (0x723d03838, 0xfa82a3)), (67, (0x723d05838, 0xfa82a3)), (131, (0x723d05838, 0xde82a3))]), (0x26895834, [(35, (0x2326895834, 0xfac688)), (67, (0x23458a5438, 0xf74681)), (131, (0x264598512a, 0xdeb850))]), (0x32834c34, [(41, (0x23258a5438, 0xfab08c)), (73, (0x264598512a, 0xfa82a3)), (137, (0x264598512a, 0xdeb460))]), (0x83432c1c, [(97, (0x745987038, 0xf702e2)), (161, (0x745987038, 0xd782a3)), (193, (0x783705838, 0xbf031a))])]

def table5 : List (Nat × List (Nat × (Nat × Nat))) := [(0x70719381c, [(194, (0x707c1323438, 0xfa3a81))]), (0x707383838, [(7, (0x70707383838, 0xfac688))]), (0x707385838, [(69, (0x70743703838, 0xfa3a50)), (133, (0x70783703838, 0xfa3a50))]), (0x707985838, [(193, (0x707c1b07038, 0xfa3a88))]), (0x72331381c, [(14, (0x70b152a3438, 0xf9c548))]), (0x72351381c, [(74, (0x70b51623438, 0xf9c548)), (138, (0x70b91623438, 0xddc548))]), (0x72370191a, [(76, (0x70b54683132, 0xfa3a88)), (140, (0x70b94683132, 0xfa3a88))]), (0x723d03838, [(11, (0x707c1323438, 0xf8855c))]), (0x723d05838, [(73, (0x70b51e07038, 0xfa3a88)), (137, (0x70b91e07038, 0xfa3a88))]), (0x72558311a, [(74, (0x70b15687038, 0xf9c350)), (138, (0x70b15a87038, 0xf9c350))]), (0x745987038, [(67, (0x74345a87038, 0xfa5688)), (131, (0x74583b06838, 0xfa3a88))]), (0x76191701c, [(74, (0x74952a16834, 0xfa3a88)), (138, (0x74992a16834, 0xfa3a88))]), (0x761d0311a, [(74, (0x743c4297034, 0xf8b528)), (138, (0x783c4297034, 0xdcb528))]), (0x78351381c, [(194, (0x70b91e07038, 0xdc855c))]), (0x78370191a, [(196, (0x783c4683132, 0xfa3a88))]), (0x783705838, [(69, (0x74345a87038, 0xf822ec)), (133, (0x78385687038, 0xfa3a88))]), (0x7e0131516, [(200, (0x7c8d0232526, 0xfa5688))]), (0x23258a5438, [(25, (0x70b94683132, 0xfa3468))]), (0x2326895834, [(25, (0x70b15a87038, 0xf9c08d))]), (0x23458a5438, [(81, (0x74992616834, 0xfa3548)), (145, (0x74992a16834, 0xfa3548))]), (0x2346895834, [(81, (0x74954a86132, 0xf816ac)), (145, (0x74992a22c70, 0xfa3541))]), (0x264598512a, [(81, (0x70b54a87070, 0xfa06a9)), (145, (0x70b54a8b070, 0xfa06a9))])]

def table6 : List (Nat × List (Nat × (Nat × Nat))) := [(0x70707383838, []), (0x70743703838, [(140, (0x7070b94687070, 0xf63c88))]), (0x70783703838, []), (0x707c1323438, []), (0x707c1b07038, [(138, (0x7078992e06870, 0xf63c88))]), (0x70b152a3438, []), (0x70b15687038, [(134, (0x70b0d32d06870, 0xe8199d))]), (0x70b15a87038, []), (0x70b51623438, [(140, (0x70b8c31526468, 0xf66688))]), (0x70b51e07038, [(14, (0x70b0d32d06870, 0xf66681))]), (0x70b54683132, [(140, (0x70b8c34586162, 0xf66688))]), (0x70b54a87070, [(11, (0x7070b94687070, 0xfa54c8))]), (0x70b54a8b070, [(137, (0x70b85a458e070, 0xf2e4c8))]), (0x70b91623438, []), (0x70b91e07038, [(134, (0x70b85a2d06870, 0xf66681))]), (0x70b94683132, []), (0x74345a87038, [(26, (0x70b0d32d06870, 0xf63c88))]), (0x743c4297034, [(26, (0x70b8c31526468, 0xf2b588))]), (0x74583b06838, [(146, (0x70b85a458e070, 0xf63c50))]), (0x74952a16834, [(26, (0x70b8c34586162, 0xf0aa33))]), (0x74954a86132, [(26, (0x70b8c31526468, 0xf0aaf0))]), (0x74992616834, [(22, (0x70b0d32d06870, 0xf11ac6))]), (0x74992a16834, [(146, (0x70b8c3458e0e0, 0xf0aa33))]), (0x74992a22c70, [(145, (0x7192ab0c1d064, 0xf29598))]), (0x78385687038, [(134, (0x70b0db0d0e070, 0xe11d1d))]), (0x783c4297034, [(138, (0x70b8c31d0e068, 0xe435a5))]), (0x783c4683132, [(140, (0x71929b0c2c470, 0xe8899d))]), (0x7c8d0232526, [(152, (0x798a8b0434546, 0xf74688))])]

def table7 : List (Nat × List (Nat × (Nat × Nat))) := [(0x7070b94687070, []), (0x7078992e06870, [(28, (0xe32546891a1c10e, 0xbdc056))]), (0x70b0d32d06870, []), (0x70b0db0d0e070, [(14, (0x161a1ce061a1c10e, 0x56f2b))]), (0x70b85a2d06870, [(28, (0x162a58a46191c10e, 0x95f286))]), (0x70b85a458e070, [(26, (0x162a54a851a1c10e, 0x1cd7a2))]), (0x70b8c31526468, []), (0x70b8c31d0e068, [(22, (0x162a58a46191c10e, 0xa3f71))]), (0x70b8c34586162, []), (0x70b8c3458e0e0, [(19, (0xe32546891a1c10e, 0x9cf71))]), (0x71929b0c2c470, [(14, (0x163858e06183850e, 0x56f2b))]), (0x7192ab0c1d064, [(14, (0x162a58a46191c10e, 0x9854cf))]), (0x798a8b0434546, [(56, (0x70b0d0e0070b0d0e, 0x5672f))])]
set_option maxHeartbeats 4000000 in
theorem tested0 : checkStep 0 layer0 layer1 table0 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem tested1 : checkStep 1 layer1 layer2 table1 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem tested2 : checkStep 2 layer2 layer3 table2 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem tested3 : checkStep 3 layer3 layer4 table3 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem tested4 : checkStep 4 layer4 layer5 table4 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem tested5 : checkStep 5 layer5 layer6 table5 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem tested6 : checkStep 6 layer6 layer7 table6 := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem tested7 : checkStep 7 layer7 layer8 table7 := by decide +kernel

def graphWord (G : V → V → Bool) : Nat :=
  let pairs : List (V × V) := [(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (2,3), (2,4), (2,5), (2,6), (2,7), (3,4), (3,5), (3,6), (3,7), (4,5), (4,6), (4,7), (5,6), (5,7), (6,7)]
  (pairs.zipIdx.map fun ((a,b),i) => if G a b then 2^i else 0).foldr Nat.lor 0

def targets : List Nat := [0x1da9807, 0x2e69807, 0x3569807, 0x35a5807, 0x3da1087, 0xfc02187]

theorem finalWords : ∀ w ∈ layer8, graphWord (bit w) ∈ targets := by decide +kernel

end CubicEight

open CubicEight

theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1.H1 := by
  intro G hs hd hr
  have start : stage G 0 layer0 := ⟨Equiv.refl _, 0, by decide, by simp⟩
  have s1 := advance hs hd hr tested0 start
  have s2 := advance hs hd hr tested1 s1
  have s3 := advance hs hd hr tested2 s2
  have s4 := advance hs hd hr tested3 s3
  have s5 := advance hs hd hr tested4 s4
  have s6 := advance hs hd hr tested5 s5
  have s7 := advance hs hd hr tested6 s6
  have s8 := advance hs hd hr tested7 s7
  obtain ⟨e,w,hw,he⟩ := s8
  refine ⟨e, ?_⟩
  change graphWord (fun i j => G (e i) (e j)) ∈ targets
  have h : (fun i j => G (e i) (e j)) = bit w := by
    funext i j
    exact he i j i.isLt
  rw [h]
  exact finalWords w hw

