import OMAReductions.R_OeisA228624_conjecture_1_R1

/-! Credit: @advancedsuperintelligence.
Each column of the certificate is supported on the first max(22,j+1)
indices. Multiplication by the square-sum matrix modulo 19 makes the
product lower triangular with diagonal 1. Every leading submatrix of
order 22 through 88 therefore has nonzero determinant. -/
namespace OMA.SquareSumMinors
open Finset Matrix

private def width (j : ℕ) := max 22 (j+1)
private def packed (j : ℕ) : ℕ :=
  (if j < 44 then (if j < 22 then (if j < 11 then (if j < 5 then (if j < 2 then (if j < 1 then 0x94a5294a52900010842108400 else 0x800000000048120000000020) else (if j < 3 then 0x9025294a52902410042108401 else (if j < 4 then 0x2419064090240906219040100401 else 0x2409025294a52906410042108401))) else (if j < 8 then (if j < 6 then 0x2409064090240906419040100401 else (if j < 7 then 0x2408825294a52906420042108401 else 0x2400040100401006409024090001)) else (if j < 9 then 0x2408023294a5290a430082108641 else (if j < 10 then 0x24008421088220841294a528c800 else 0x128ca5294812004220842108240)))) else (if j < 16 then (if j < 13 then (if j < 12 then 0x8021084220803204a5294812 else 0x320c82008020148520c81204812) else (if j < 14 then 0x2008021084210803204a5294812 else (if j < 15 then 0x200c820080200c8520c81204812 else 0x2010021084210c83204a5294812))) else (if j < 19 then (if j < 17 then 0x2008020080200c8320c81204812 else (if j < 18 then 0x2010041084210c83104a5294812 else 0x200480004812048200802008012)) else (if j < 20 then 0x2018041104210c4300465294832 else (if j < 21 then 0x200000000012048000000008000 else 0x108421084210025294a5290000))))) else (if j < 33 then (if j < 27 then (if j < 24 then (if j < 23 then 0x48321482008020144510c81204832 else 0x5254908140501490c9520240902540) else (if j < 25 then 0x8230e1595e87a0e474048711645b1f0 else (if j < 26 then 0x8151e081b9304b1020a5b02a86a3adb1 else 0x2602784ad231a52204c5124f399cf5a147))) else (if j < 30 then (if j < 28 then 0xc80004800048120c820080200803200012 else (if j < 29 then 0x11005a46914751d2a44043919e96292d1c070 else 0x1a1035f27b21184603184a5310e310c6f9064e)) else (if j < 31 then 0x3107604657b551546294b96b910c91244361caf else (if j < 32 then 0x5c1c34018d4c1f279e4c7b8ad4286409181839b1 else 0x969ccb5a48e11e1239412885ca845830b1ca3bca8)))) else (if j < 38 then (if j < 35 then (if j < 34 then 0x1af42c6688990444e45bc064c2461ac4c7a1442c820 else 0x48ab4a5a861a057906d5902f230e9491f032547719a5) else (if j < 36 then 0x5486f2ba0480d0c4044f3054713da42ae516b9ed38ce2 else (if j < 37 then 0xb3add00c109425e22380d701268488b5bca8934ad61986 else 0x1815a1f139646935424c58379e4453041329262be034110b))) else (if j < 41 then (if j < 39 then 0x2d8062a26515cd1b1e823a2559e0a4c45039182145d0914e4 else (if j < 40 then 0x6108c8400d218e2789cd526117a8c38ac44894ca29d2063c2f else 0x388a4180e418c800781e268de37880108c04012230065208200)) else (if j < 42 then 0x1ef1c4432c06349868621045446f1adab421475ac0d900a391501 else (if j < 43 then 0x60f1c4222c04139425498c24c46f235ee5adaa6b02e9488388ce1 else 0x106255acf20214f19972681650bce7511833ade689e0d604ab69a05)))))) else (if j < 66 then (if j < 55 then (if j < 49 then (if j < 46 then (if j < 45 then 0x33322a695097248d536255c52583a2d6c52159d257c60c5c230439c5 else 0x1c8684cf641aa628049262a7acf25ae0b195324842f72dcc799c61042d) else (if j < 47 then 0x80090401084000040088621882328ca409024290402084210000100252 else (if j < 48 then 0x19a2f8ac417c52461c0a83d040242574561129e622d6461d843292d841a6 else 0xf68c804180171cec2999139d448ac8f1a171630ee634420248f805ce11989))) else (if j < 52 then (if j < 50 then 0x14520ca8039888b9529320c12e06789ae6c06f2a4218c64f8ad91289af59849 else (if j < 51 then 0xcd17058f8a8900ac8874172204c63acc0281a643d686319050df1939234ac08 else 0x2884e1194d185e902caa501826a24b025a41b844439d021126394072994171548)) else (if j < 53 then 0x329c2a9358888c71311e51a4d053864295d1694c579c699088680a484265249c32 else (if j < 54 then 0x1c468dc72c0437a521939697224662c92421e0544f101d02711a87b9481c54a8a1c5 else 0x114519e03781070b92b801a46bd712042484851825a77088c6a04f00d8b69a4102545)))) else (if j < 60 then (if j < 57 then (if j < 56 then 0x9315053e500888e5a0ca79644849d11c8cf41443344408a091684501a5433303211951 else 0xe81dc7331aa8b60932064818c83a00d6016f61e211a88c785ac938d1335ec624d220c01) else (if j < 58 then 0xe01c00a18da791572540112320158125618ad6884d180028184e81007384d2780322c4ae else (if j < 59 then 0x296611e0a74431195885ac2531a4e53ca168d048bd677091178146821ed641600b60714227 else 0xb52a51e3223529780cd68162549cd9191171ccc13849648851224a02c645c64481d2d2c051))) else (if j < 63 then (if j < 61 then 0x8444435c24a3ca2d9204868200520603b98b744ea63c2c0c54890c32898925484a6c8a961623 else (if j < 62 then 0x1035b8eb585f061d487c1ee2c228349ed688a2918487c8ed1458820e0a6346979cb10848a114ec else 0x346b71843388c97a8b2328af231af58e100b92203a0b001c0018ed1365192404125c979ccd18063)) else (if j < 64 then 0x81882348ca70447104ae61831549ae72e21730c789042144a31000b1b0cf205432ac30308015c946 else (if j < 65 then 0x125c5a578d526c0e2120ed14431041827c029331a308c4a339b16c5c83980e729243bc881c56950120 else 0x12a40e433ae4649e11694221c1aa184e1048205360c8b9ce8adce342204148384083115c55918281450))))) else (if j < 77 then (if j < 71 then (if j < 68 then (if j < 67 then 0x98789d63530c1034cc20963616443a0123b1cf78187206118bc6d5222060523034e04c06058c8b49168 else 0x414010962b71d8282ced18124815d0638d112c4d43d5113d518423210daa910493c5c52a465388aa7b8cb) else (if j < 69 then 0x1143a2802cc75c46e5c02658d12340c72996a6464f7004c7946b748e1511ed289aa404d12000728d8731427 else (if j < 70 then 0x21223a437c0b1001a02b4b128e460840a7196a79da41a6123944a9498459981945702a5ee4bcd1898ab2b50a else 0x40ef42dd27088b43daa7153121ce52b48c421ca6244932ca41a50c68c6c5ad6f122436a4d2310290156d001b1))) else (if j < 74 then (if j < 72 then 0x8154030464489eb711881b24b5be2f4c84661c4f105486408d2252b0184f0988b2009200ce49394838924700ae else (if j < 73 then 0x2191665c9a64111148a0b710a49182a204a0391920b1f132c207822859d6182c01724026b9c00bd0e2a96c00d85 else 0x25228705a543129e528248336015346c1806a6814f124c551dc1511ee929c77090842e4132c482a60478e0024050)) else (if j < 75 then 0x3e0110d852b82a3b0203b1e45886c014e452d84138cf119327314f2a028324ea4a12d7ca2179c227c0678218d22a47 else (if j < 76 then 0x53612744e43bc200994e90d86121a5185c9480054c86059a254ba255192901e25280c548d841b42d8320f2b943415e9 else 0x68a07063d4e899c674a2a109d2844237050900560434c958dc33184d340e56300d1b9a67188e8024c021255a01258211)))) else (if j < 82 then (if j < 79 then (if j < 78 then 0x12110c48025cd6b026000ae4898859166020223b82e2c1ad4382d495076a4ab39dac335e843d821c4113924a7c18541c21 else 0x25c852d4483003918892980f6bcad3108c684c31c1e2589632396a614c8388e11a6043148313d2d93a496051071a0c8260e) else (if j < 80 then 0x38d2f8a02601449110c48198a2ad434912992a08508267be4f7ca455a8c84acd26c12c0c42b911d1800c308a3139a0a140a9 else (if j < 81 then 0x23a9c100c882b04849c29601b08a45128cea6bdf02990228dea83c8792cf1245e10264c5b64c4902f639a5291d1631506c047 else 0xa7235601c4c393dcf420e65a1a05ace659a452944d831067a0275964a518aa92e424a9017bd28400524414c2a591811c90388c))) else (if j < 85 then (if j < 83 then 0xcc610d454ba01748cd0308e840d05896d0486e8362a690ed59d4d43c8d235e88008450e2920e2293a201b8724160422d226298a else (if j < 84 then 0x53cc5311c949430141913ac8a4ac0a78d098c4e70316f408ae63a27040498088d10941731ae2224b4a06778d2163d4712c4d3880d else 0x851e3242089701e92adc77c88d890e11218970e2e63c030a2040262b735ec90124780e4745d05486b6864380d0e384d048a4910e10)) else (if j < 86 then 0x1ed2aa418c84d8b8c2109ec719c28ac2b4122d5096a540893ad105b907318ad098c859dcc59160315e000987224c038830306428392e else (if j < 87 then 0x31808864e29dc580d45628105090a7c245345a76c5281822b49d8319490738854a98a640d09156b29c6e721b1439c280c107064138d4c else 0x3a62f520eb709812392d6aa4b0ae4e68a495c1315c9c20ca455c0e483a423c4e810a2482a434c0a01816138da5228106b08b0c82b5b8b0)))))))

private def coeff (j k : ℕ) : ℕ :=
  if k < width j then ((packed j) >>> (5*k)) % 32 else 0

private def entry (i k : ℕ) : ℕ :=
  let s := i+k+2
  if s.sqrt^2 = s then 1 else 0

private def inner (i j : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => inner i j k + entry i k * coeff j k

private theorem inner_sum (i j m : ℕ) :
    ∑ k ∈ range m, entry i k * coeff j k = inner i j m := by
  induction m with
  | zero => simp [inner]
  | succ m ih => rw [sum_range_succ, ih, inner]

private theorem inner_stable (i j n : ℕ) (h : width j ≤ n) :
    inner i j n = inner i j (width j) := by
  induction n,h using Nat.le_induction with
  | base => rfl
  | succ n hn ih => simp [inner, coeff, Nat.not_lt.mpr hn, ih]

private def every (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | k+1 => f k && every f k

private theorem every_sound {f : ℕ → Bool} {k : ℕ} (h : every f k = true) :
    ∀ i < k, f i = true := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [every,Bool.and_eq_true] at h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hl | rfl
    · exact ih h.2 i hl
    · exact h.1

private def checkCol (j : ℕ) := every (fun i =>
  inner i j (width j) % 19 == (if i=j then 1 else 0)) (j+1)

set_option maxRecDepth 5000 in
set_option maxHeartbeats 6000000 in
private theorem allColumns {j : ℕ} (hj : j < 88) : checkCol j = true := by
  have c0 : every (fun z => checkCol (0+z)) 4 = true := by decide +kernel
  have c4 : every (fun z => checkCol (4+z)) 4 = true := by decide +kernel
  have c8 : every (fun z => checkCol (8+z)) 4 = true := by decide +kernel
  have c12 : every (fun z => checkCol (12+z)) 4 = true := by decide +kernel
  have c16 : every (fun z => checkCol (16+z)) 4 = true := by decide +kernel
  have c20 : every (fun z => checkCol (20+z)) 4 = true := by decide +kernel
  have c24 : every (fun z => checkCol (24+z)) 4 = true := by decide +kernel
  have c28 : every (fun z => checkCol (28+z)) 4 = true := by decide +kernel
  have c32 : every (fun z => checkCol (32+z)) 4 = true := by decide +kernel
  have c36 : every (fun z => checkCol (36+z)) 4 = true := by decide +kernel
  have c40 : every (fun z => checkCol (40+z)) 4 = true := by decide +kernel
  have c44 : every (fun z => checkCol (44+z)) 4 = true := by decide +kernel
  have c48 : every (fun z => checkCol (48+z)) 4 = true := by decide +kernel
  have c52 : every (fun z => checkCol (52+z)) 4 = true := by decide +kernel
  have c56 : every (fun z => checkCol (56+z)) 4 = true := by decide +kernel
  have c60 : every (fun z => checkCol (60+z)) 4 = true := by decide +kernel
  have c64 : every (fun z => checkCol (64+z)) 4 = true := by decide +kernel
  have c68 : every (fun z => checkCol (68+z)) 4 = true := by decide +kernel
  have c72 : every (fun z => checkCol (72+z)) 4 = true := by decide +kernel
  have c76 : every (fun z => checkCol (76+z)) 4 = true := by decide +kernel
  have c80 : every (fun z => checkCol (80+z)) 4 = true := by decide +kernel
  have c84 : every (fun z => checkCol (84+z)) 4 = true := by decide +kernel
  by_cases h0 : j < 4
  · have v := every_sound c0 (j-0) (by omega)
    simpa only [show 0+(j-0) = j by omega] using v
  by_cases h4 : j < 8
  · have v := every_sound c4 (j-4) (by omega)
    simpa only [show 4+(j-4) = j by omega] using v
  by_cases h8 : j < 12
  · have v := every_sound c8 (j-8) (by omega)
    simpa only [show 8+(j-8) = j by omega] using v
  by_cases h12 : j < 16
  · have v := every_sound c12 (j-12) (by omega)
    simpa only [show 12+(j-12) = j by omega] using v
  by_cases h16 : j < 20
  · have v := every_sound c16 (j-16) (by omega)
    simpa only [show 16+(j-16) = j by omega] using v
  by_cases h20 : j < 24
  · have v := every_sound c20 (j-20) (by omega)
    simpa only [show 20+(j-20) = j by omega] using v
  by_cases h24 : j < 28
  · have v := every_sound c24 (j-24) (by omega)
    simpa only [show 24+(j-24) = j by omega] using v
  by_cases h28 : j < 32
  · have v := every_sound c28 (j-28) (by omega)
    simpa only [show 28+(j-28) = j by omega] using v
  by_cases h32 : j < 36
  · have v := every_sound c32 (j-32) (by omega)
    simpa only [show 32+(j-32) = j by omega] using v
  by_cases h36 : j < 40
  · have v := every_sound c36 (j-36) (by omega)
    simpa only [show 36+(j-36) = j by omega] using v
  by_cases h40 : j < 44
  · have v := every_sound c40 (j-40) (by omega)
    simpa only [show 40+(j-40) = j by omega] using v
  by_cases h44 : j < 48
  · have v := every_sound c44 (j-44) (by omega)
    simpa only [show 44+(j-44) = j by omega] using v
  by_cases h48 : j < 52
  · have v := every_sound c48 (j-48) (by omega)
    simpa only [show 48+(j-48) = j by omega] using v
  by_cases h52 : j < 56
  · have v := every_sound c52 (j-52) (by omega)
    simpa only [show 52+(j-52) = j by omega] using v
  by_cases h56 : j < 60
  · have v := every_sound c56 (j-56) (by omega)
    simpa only [show 56+(j-56) = j by omega] using v
  by_cases h60 : j < 64
  · have v := every_sound c60 (j-60) (by omega)
    simpa only [show 60+(j-60) = j by omega] using v
  by_cases h64 : j < 68
  · have v := every_sound c64 (j-64) (by omega)
    simpa only [show 64+(j-64) = j by omega] using v
  by_cases h68 : j < 72
  · have v := every_sound c68 (j-68) (by omega)
    simpa only [show 68+(j-68) = j by omega] using v
  by_cases h72 : j < 76
  · have v := every_sound c72 (j-72) (by omega)
    simpa only [show 72+(j-72) = j by omega] using v
  by_cases h76 : j < 80
  · have v := every_sound c76 (j-76) (by omega)
    simpa only [show 76+(j-76) = j by omega] using v
  by_cases h80 : j < 84
  · have v := every_sound c80 (j-80) (by omega)
    simpa only [show 80+(j-80) = j by omega] using v
  by_cases h84 : j < 88
  · have v := every_sound c84 (j-84) (by omega)
    simpa only [show 84+(j-84) = j by omega] using v
  omega

private theorem triangular_entry (i j : ℕ) (hj : j < 88) (hi : i ≤ j) :
    inner i j (width j) % 19 = (if i=j then 1 else 0) :=
  beq_iff_eq.mp (every_sound (allColumns hj) i (by omega))

private theorem nonzero_minor (n : ℕ) (hn : 22 ≤ n) (hn' : n ≤ 88) :
    OeisA228624.a n ≠ 0 := by
  classical
  let : Fact (Nat.Prime 19) := ⟨by decide⟩
  let A : Matrix (Fin n) (Fin n) (ZMod 19) := fun i j => (entry i.val j.val : ZMod 19)
  let C : Matrix (Fin n) (Fin n) (ZMod 19) := fun i j => (coeff j.val i.val : ZMod 19)
  have prod_entry (i j : Fin n) (hij : i.val ≤ j.val) :
      (A*C) i j = if i=j then 1 else 0 := by
    have bound : width j.val ≤ n := by unfold width; exact max_le hn j.isLt
    have eq := triangular_entry i.val j.val (lt_of_lt_of_le j.isLt hn') hij
    calc
      (A*C) i j = ∑ k : Fin n, ((entry i.val k.val * coeff j.val k.val : ℕ) : ZMod 19) := by
        rw [Matrix.mul_apply]
        simp only [A,C,Nat.cast_mul]
      _ = ((∑ k ∈ range n, entry i.val k * coeff j.val k : ℕ) : ZMod 19) := by
        rw [Nat.cast_sum]
        exact Fin.sum_univ_eq_sum_range (fun k : ℕ => ((entry i.val k * coeff j.val k : ℕ) : ZMod 19)) n
      _ = (inner i.val j.val (width j.val) : ZMod 19) := by rw [inner_sum,inner_stable _ _ _ bound]
      _ = _ := by
        rw [← ZMod.natCast_mod (inner i.val j.val (width j.val)) 19,eq]
        by_cases e : i=j
        · simp [e]
        · have e' : i.val ≠ j.val := fun hv => e (Fin.ext hv)
          simp [e,e']
  have lower : (A*C).IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    exact (prod_entry i j hij.le).trans (if_neg hij.ne)
  have det_one : (A*C).det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ lower]
    exact Finset.prod_eq_one fun i _ => (prod_entry i i le_rfl).trans (if_pos rfl)
  have nz : A.det ≠ 0 := by
    intro hz
    rw [Matrix.det_mul,hz,zero_mul] at det_one
    exact (zero_ne_one : (0 : ZMod 19) ≠ 1) det_one
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j => (entry i.val j.val : ℤ)
  have eqM : OeisA228624.a n = M.det := by
    unfold OeisA228624.a
    apply congrArg Matrix.det
    ext i j
    dsimp [M,entry]
    split <;> simp
  have eqA : ((Int.castRingHom (ZMod 19)) M.det) = A.det := by
    rw [RingHom.map_det]
    congr 1
  intro hz
  rw [eqM] at hz
  apply nz
  rw [←eqA,hz,map_zero]

end OMA.SquareSumMinors

theorem OMA.solution : OMA.R_OeisA228624_conjecture_1_R1.H1 := by
  intro n hn hb
  exact OMA.SquareSumMinors.nonzero_minor n (by omega) (by omega)
