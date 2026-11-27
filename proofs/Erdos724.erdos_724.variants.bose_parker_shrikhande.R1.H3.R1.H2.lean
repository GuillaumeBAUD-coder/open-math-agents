import OMAReductions.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1_H3_R1

/-! Two squares on the residues modulo seventeen together with a fixed symbol.
The first square has its fixed symbol on diagonal zero, the second on diagonal
one. The other entries are developed by simultaneous cyclic translation.
Each row is packed in five-bit entries. The inverse tables let the kernel
check each inverse identity on just 324 cells. -/

namespace Squares18

private def entry (rows : Fin 18 → ℕ) (i j : Fin 18) : Fin 18 :=
  Fin.ofNat 18 ((rows i >>> (5 * j.val)) % 32)

private def first : Fin 18 → ℕ :=
  ![0x361562718898214f684f1, 0x2d3306f395404ae0e12224, 0x476920832c2a601e34c4ae,
    0x6e281276096d0c08a899e8, 0x860a90d1b1c2015713c12f, 0xa25a5c46bc613322802a07,
    0xcc53cae810476c52158103, 0xeb819e028d0e8a84c0a48d, 0x1003c026225f158da2515cc,
    0x128008e55422c2386b33da1, 0x1411a0cb045a57918783849, 0x16449d818b8d02b50078d42,
    0x18a4345179c067243022c65, 0x1a970e30404ef50805610cb, 0x1cf244091220b184cd29d8a,
    0x1e5885434818411dc643570, 0x21112c8a0b4a343ce973006, 0x2307b9ac5a928398a418820]

private def second : Fin 18 → ℕ :=
  ![0xd4a82e788e34418459626, 0x2a589f01a089034ac344ee, 0x4c1c00449541719a78a1eb,
    0x64004aa32c4f3b9114c18d, 0x811196760e087a62a035c5, 0xa33b10d201305456173cc2,
    0xc86a5c50a80b8b04f81c64, 0xee53cc25859168e00410a9, 0x10b81c6c1362e200292994f,
    0x120411a3745e5089463ae0c, 0x1492b88f8c0c21ace8601a1, 0x1667961101c646212d0b84a,
    0x19030221410ad4a9c278d67, 0x1a70c449299ca5bc7023100, 0x1c288d463bd6c810056a428,
    0x1f122ce8831a0284ce50923, 0x205621206b82611deb1a891, 0x22f7358b525073148310410]

private def rowInvA : Fin 18 → ℕ :=
  ![0x722c6f695060a9c983051, 0x256120e324e25bd4068e28, 0x4d281e75206c82c2e24526,
    0x660c10b491a0609e58a8ee, 0x820258a2b82d1c0d15a1e7, 0xa153566789c401e2c4c103,
    0xcb730f01bca1445aa02482, 0xef6a004818498b9615146c, 0x10e484a038d517b04b311b0,
    0x12a1182822e3068d872b80f, 0x143389256440e235067860b, 0x1681a8cd885e5724f010184,
    0x18459dd1140cf520030b4a9, 0x1ac43e2301e0b4848271945, 0x1c9844814018a1146f3accd,
    0x1e0894490b5633120861dca, 0x21130d42730872812d43d61, 0x2307b9ac5a928398a418820]

private def colInvA : Fin 18 → ℕ :=
  ![0xf208e86b9432c18132d31, 0x251a12e7ac860344762a30, 0x444a9f0614e170d0d5c406,
    0x6a5c00d3204f225cc884e5, 0x8c005c748e0553db1120cb, 0xa113d0a200cb83a2349d8d,
    0xc38256509d807c48a435c2, 0xe0530c2434308956973c64, 0x10b69c69708113314f810a1,
    0x12e4114f186276ae002984c, 0x1492ae041450e6002638daf, 0x166600a38a5ed088e823a0a,
    0x18d09891541c21a12578167, 0x1a23962b03c644a8d00b10e, 0x1c834581810aa59c026a5e3,
    0x1e78b4402996c4046e54089, 0x21170c263b1a9111eb01548, 0x2307b9ac5a928398a418820]

private def rowInvB : Fin 18 → ℕ :=
  ![0x265b2051b9e748044429b1, 0x4c680c47c10a08ca95ba27, 0x6e09cb0025622194c7c50d,
    0x8241801530653adb08a5cf, 0xa93844b690c86381153e03, 0xc810d8e29d2d7862b8008a,
    0xe3235e6429d01458009569, 0x105740e95bc038b42233144, 0x12f0214c80491708676aca6,
    0x1414ada01162f1910e618f0, 0x16a63823346042a5ed3a002, 0x18d78887880a6541c84846b,
    0x1b019511098eb03d2a1118e, 0x1c4326223a181829632b5e0, 0x1e7544684b4405b08674025,
    0x20b8912a70c2c694ef008c8, 0x112a96f209ae3220119d2c, 0x22083dcd62d4941cc520c41]

private def colInvB : Fin 18 → ℕ :=
  ![0x2114046912cee600867954d, 0x911143621ed094f032dd1, 0x232ac8d4c1c23200763e2a,
    0x46615ca03c674850d84564, 0x6d33d618110a125c08b0a7, 0x87830402a56353c316990e,
    0xa068c265308b80a2e3a5e8, 0xce208eb695801c5e854121, 0xe51a18e334248c12b0284f,
    0x1044b5e7708b10298158e06, 0x12a7410f19a215b44c200e5, 0x14f026043c44c70da50a0cb,
    0x161500a888daf238c249d90, 0x18b0993123a0579c6a43402, 0x1a23aa25780d0411697046c,
    0x1c85c4d009c092b14f111a3, 0x1ec89c02405466ae032b889, 0x2307b9ac5a928398a418820]

private def pairRow : Fin 18 → ℕ :=
  ![0x1512156f438293099069c60, 0x16533209789471b40e41031, 0x187681501ad04705e928a26,
    0x1ae0ac04624af141461c4e8, 0x1c2604ad51a0302ce48a12f, 0x1ed119cb38081620b14aa03,
    0x2033bd880944d49a2a5808e, 0x88352230dca3c56c095e4, 0x207286723d688b1a2340a9,
    0x4f59105831316b86701941, 0x6c2a4c06aa2e791013ac50, 0x8651c2e5c5f02a44860c0d,
    0xab409ec8c00650d2d205c7, 0xc91c1b1004eb229c513d0c, 0xe403a21121855bcc3825aa,
    0x1017c4434b4cc81c8053965, 0x13088c8a71da04142b7b0c2, 0x22a4a0e6290620820f7358b]


private def square (rows rInv cInv : Fin 18 → ℕ)
    (hr : ∀ i j, entry rInv i (entry rows i j) = j)
    (hc : ∀ i j, entry cInv j (entry rows i j) = i) : LatinSquare 18 where
  mat := entry rows
  row_injective i := Function.LeftInverse.injective (hr i)
  col_injective j := Function.LeftInverse.injective (fun i => hc i j)

private def A : LatinSquare 18 :=
  square first rowInvA colInvA (by decide +kernel) (by decide +kernel)

private def B : LatinSquare 18 :=
  square second rowInvB colInvB (by decide +kernel) (by decide +kernel)

private lemma recover : ∀ i j, entry pairRow (entry first i j) (entry second i j) = i := by
  decide +kernel

theorem exists_pair : ∃ L M : LatinSquare 18, L ≠ M ∧ Erdos724.IsOrthogonal L M := by
  refine ⟨A, B, fun h => ?_, ?_⟩
  · have e := congrArg (fun S : LatinSquare 18 => S.mat 0 0) h
    exact (by decide +kernel : A.mat 0 0 ≠ B.mat 0 0) e
  · rintro ⟨i,j⟩ ⟨k,l⟩ h
    change (entry first i j, entry second i j) = (entry first k l, entry second k l) at h
    have hi : i = k := by
      simpa only [recover] using congrArg (fun p : Fin 18 × Fin 18 => entry pairRow p.1 p.2) h
    subst k
    have hj : j = l := A.row_injective i (congrArg Prod.fst h)
    subst l
    rfl

end Squares18

theorem OMA.solution : OMA.R_Erdos724_erdos_724_variants_bose_parker_shrikhande_R1_H3_R1.H2 :=
  Squares18.exists_pair
