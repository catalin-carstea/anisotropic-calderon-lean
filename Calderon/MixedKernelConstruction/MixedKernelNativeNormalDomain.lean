import Calderon.MixedKernelConstruction.MixedKernelNativeGlobalEnergy
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth
open scoped ContDiff Topology InnerProductSpace

/-- The original packet flow has exactly zero displacement at zero actual frame velocity. -/
theorem packetEndpoint_zero_velocity
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (hlam : lam∈Icc (0 : ℝ) 1)
    (y : R3) (hy : y∈P.centers) (r : ℝ) : packetEndpoint S L P lam y r 0=y := by
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  rcases hEnd with ⟨_,_,_,_,_,_,_,_,hValue,_,_⟩
  change (P.Phi lam (y,r • conformalReferenceGramFrameOperatorJoint S.g1 L (lam,y) 0) 1).1=y
  simp only [map_zero,smul_zero]
  exact hValue lam hlam y (P.centers_room y hy).2

/-- The SAME coherent map sends an original zero velocity to the actual diagonal. -/
theorem nativeVelocityPair_zero_velocity
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam∈Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (y : R3) (hy : y∈nativeCoverCenterRoom S L C) :
    nativeVelocityPair S L C lam R (y,0)=(y,y) := by
  obtain ⟨i,hi⟩ := mem_iUnion.mp hy
  rw [nativeVelocityPair_eq_packet S L C lam hlam R hR hRoom i y hi 0 (by simpa only [norm_zero] using hR)]
  change (packetEndpoint S L (C.packet i) lam y R (R⁻¹ • 0),y)=(y,y)
  rw [smul_zero,packetEndpoint_zero_velocity S L (C.packet i) lam ⟨hlam.1,hlam.2.trans C.dilation_le_one⟩ y hi R]

/-- On the actual normal image, zero inverse velocity is EXACTLY the physical diagonal. -/
theorem nativeVelocityInverse_velocity_zero_iff
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam∈Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (q : R3 × R3) (hq : q∈nativeNormalImage S L C lam R) :
    (nativeVelocityInverse S L C lam R q).2=0 ↔ q.1=q.2 := by
  let a := nativeVelocityInverse S L C lam R q
  obtain ⟨hA,hRight⟩ := nativeVelocityInverse_mem_right S L C lam R q hq
  change a∈nativeNormalVelocityRoom S L C R at hA
  change nativeVelocityPair S L C lam R a=q at hRight
  have hy : a.1=q.2 := nativeVelocityInverse_fst S L C lam R q hq
  have hA0 : (a.1,0)∈nativeNormalVelocityRoom S L C R :=
    ⟨hA.1,by simpa only [mem_ball,dist_zero_right,norm_zero] using hR⟩
  have hZero := nativeVelocityPair_zero_velocity S L C lam hlam R hR hRoom a.1 hA.1
  constructor
  · intro hv
    have ha : a=(a.1,0) := Prod.ext rfl hv
    rw [ha,hZero] at hRight
    exact (congrArg Prod.fst hRight).symm.trans (congrArg Prod.snd hRight)
  · intro hDiag
    have hqZero : q=(a.1,a.1) := Prod.ext (hDiag.trans hy.symm) hy.symm
    have he : nativeVelocityPair S L C lam R a=nativeVelocityPair S L C lam R (a.1,0) :=
      hRight.trans (hqZero.trans hZero.symm)
    exact congrArg Prod.snd (nativeVelocityPair_injOn S L C lam hlam R hR hRoom hA hA0 he)

/-- Both coordinates of every actual normal image point lie in the original dilated source room. -/
theorem nativeNormalImage_coordinate_rooms
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam∈Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (q : R3 × R3) (hq : q∈nativeNormalImage S L C lam R) :
    lam • q.1∈S.coordinateRoom ∧ lam • q.2∈S.coordinateRoom := by
  obtain ⟨a,ha,rfl⟩ := hq
  obtain ⟨i,hi⟩ := mem_iUnion.mp ha.1
  have hu : ‖a.2‖<R := by simpa only [mem_ball,dist_zero_right] using ha.2
  rw [nativeVelocityPair_eq_packet S L C lam hlam R hR hRoom i a.1 hi a.2 hu]
  have hz : R⁻¹ • a.2∈closedBall (0 : R3) 2 := by
    have hh := norm_inv_smul_lt_one_of_norm_lt R hR a.2 hu
    simp only [mem_closedBall,dist_zero_right]
    linarith
  refine ⟨C.coordinate_room i lam hlam a.1 hi R hR hRoom (R⁻¹ • a.2) hz,?_⟩
  have hCenter := C.coordinate_room i lam hlam a.1 hi R hR hRoom 0 (by simp)
  rw [packetEndpoint_zero_velocity S L (C.packet i) lam ⟨hlam.1,hlam.2.trans C.dilation_le_one⟩ a.1 hi R] at hCenter
  exact hCenter

/-- The actual nonzero-velocity image is inside the unchanged original off-diagonal domain. -/
theorem nativeNormalImage_mem_dilatedOffDiagonal_of_velocity_ne_zero
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam∈Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (q : R3 × R3) (hq : q∈nativeNormalImage S L C lam R)
    (hv : (nativeVelocityInverse S L C lam R q).2≠0) : q∈dilatedOffDiagonal S lam := by
  obtain ⟨hx,hy⟩ := nativeNormalImage_coordinate_rooms S L C lam hlam R hR hRoom q hq
  exact ⟨hx,hy,fun h => hv ((nativeVelocityInverse_velocity_zero_iff S L C lam hlam R hR hRoom q hq).mpr h)⟩

/-- The ENTIRE original positive-radius compact front is off diagonal in the original source room. -/
theorem nativeSphereFront_subset_dilatedOffDiagonal
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam∈Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (delta Rstar : ℝ) (hd : 0<delta) (hRs : 0<Rstar) (p : ℕ)
    (hRadius : ∀ y∈cylinder, referenceRadius delta Rstar p L y<R) :
    nativeSphereFront S L C lam delta Rstar p⊆dilatedOffDiagonal S lam := by
  intro q hq
  have hU := nativeSphereFront_subset_nativeNormalImage S L C lam hlam R hR hRoom delta Rstar hd hRs p hRadius hq
  have hZero := nativeGlobalEnergy_zero_on_nativeSphereFront S L C lam hlam R hR hRoom delta Rstar hd hRs p hRadius q hq
  apply nativeNormalImage_mem_dilatedOffDiagonal_of_velocity_ne_zero S L C lam hlam R hR hRoom q hU
  intro hv
  unfold nativeGlobalEnergy at hZero
  simp only [hv,inner_zero_right,zero_sub] at hZero
  have hr := referenceRadius_pos delta Rstar p L q.2 hd hRs
  nlinarith only [hZero,sq_pos_of_pos hr]

/-- One OPEN actual source collar contains the WHOLE original front and carries the ONE smooth zero phase. -/
theorem exists_nativeGlobalEnergy_full_front_open_room
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam∈Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (delta Rstar : ℝ) (hd : 0<delta) (hRs : 0<Rstar) (p : ℕ)
    (hRadius : ∀ y∈cylinder, referenceRadius delta Rstar p L y<R) :
    ∃ W : Set (R3 × R3), IsOpen W ∧ nativeSphereFront S L C lam delta Rstar p⊆W ∧
      W⊆dilatedOffDiagonal S lam ∧
      ContDiffOn ℝ ∞ (nativeGlobalEnergy S L C lam R delta Rstar p) W ∧
      ∀ q∈nativeSphereFront S L C lam delta Rstar p, nativeGlobalEnergy S L C lam R delta Rstar p q=0 := by
  let W : Set (R3 × R3) := nativeNormalImage S L C lam R∩{q | q.1≠q.2}
  have hWU : W⊆nativeNormalImage S L C lam R := inter_subset_left
  have hW : IsOpen W := (isOpen_nativeNormalImage S L C lam hlam R hR hRoom).inter
    (isOpen_ne_fun continuous_fst continuous_snd)
  have hFrontU := nativeSphereFront_subset_nativeNormalImage S L C lam hlam R hR hRoom delta Rstar hd hRs p hRadius
  have hFrontD := nativeSphereFront_subset_dilatedOffDiagonal S L C lam hlam R hR hRoom delta Rstar hd hRs p hRadius
  refine ⟨W,hW,fun q hq => ⟨hFrontU hq,(hFrontD hq).2.2⟩,?_,
    (contDiffOn_nativeGlobalEnergy S L C lam hlam R hR hRoom delta Rstar hd hRs p).mono hWU,
    nativeGlobalEnergy_zero_on_nativeSphereFront S L C lam hlam R hR hRoom delta Rstar hd hRs p hRadius⟩
  intro q hq
  obtain ⟨hx,hy⟩ := nativeNormalImage_coordinate_rooms S L C lam hlam R hR hRoom q hq.1
  exact ⟨hx,hy,hq.2⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
