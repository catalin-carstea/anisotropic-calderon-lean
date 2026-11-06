import Calderon.MixedKernelConstruction.MixedKernelNativePairOpenImage
import Calderon.MixedKernelConstruction.MixedKernelNativeCompactFront
import Calderon.MixedKernelConstruction.MixedKernelNativeConstantRadiusPhase
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth ActualScalarPrincipalAdjoint
open scoped ContDiff Topology InnerProductSpace

/-- A literal positive-radius normalization sends its unscaled frame-velocity ball inside the unit angular ball. -/
theorem norm_inv_smul_lt_one_of_norm_lt (R : ℝ) (hR : 0 < R) (u : R3) (hu : ‖u‖ < R) :
    ‖R⁻¹ • u‖ < 1 := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
  have hh := mul_lt_mul_of_pos_left hu (inv_pos.mpr hR)
  simpa only [inv_mul_cancel₀ hR.ne'] using hh

/-- The actual native pair map expressed in unscaled native frame-velocity coordinates. -/
def packetVelocityPair (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam R : ℝ) (a : R3 × R3) : R3 × R3 :=
  (packetEndpoint S L P lam a.1 R (R⁻¹ • a.2),a.1)

theorem contDiff_packetVelocityPair (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam R : ℝ) : ContDiff ℝ ∞ (packetVelocityPair S L P lam R) := by
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (P.Phi a.1 a.2 1).1) := hEnd.2.2.2.2.2.2.2.1
  have hf : ContDiff ℝ ∞ (fun a : R3 × R3 => packetEndpoint S L P lam a.1 R (R⁻¹ • a.2)) :=
    (contDiff_referenceFramedPhysicalEndpoint S.g1 S.g1_admissible L P.Phi hTheta).comp
      (contDiff_const.prodMk ((contDiff_fst.prodMk contDiff_const).prodMk (contDiff_snd.const_smul R⁻¹)))
  exact hf.prodMk contDiff_fst

/-- The actual vertical derivative is J, and the actual full pair derivative is invertible. -/
theorem packetVelocityPair_derivative_isInvertible
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1) (R : ℝ) (hR : 0 < R) (hRoom : R ≤ 4*P.rho)
    (y : R3) (hy : y ∈ P.centers) (u : R3) (hu : ‖u‖ < R) :
    (fderiv ℝ (packetVelocityPair S L P lam R) (y,u)).IsInvertible := by
  let f : R3 × R3 → R3 := fun a => packetEndpoint S L P lam a.1 R (R⁻¹ • a.2)
  have hf : ContDiff ℝ ∞ f := (contDiff_packetVelocityPair S L P lam R).fst
  apply endpoint_pair_derivative_isInvertible f (y,u) (hf.differentiable (by simp) (y,u))
  let z := R⁻¹ • u
  let J := referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,R),z))
  have hz : z ∈ closedBall (0 : R3) 2 := by
    have hh := norm_inv_smul_lt_one_of_norm_lt R hR u hu
    simp only [mem_closedBall,dist_zero_right]
    change ‖R⁻¹ • u‖ ≤ 2
    linarith
  have hInv := packet_normalizedJacobian_isInvertible S L P lam hlam y hy R
    (by simpa only [abs_of_pos hR] using hRoom) z hz
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (P.Phi a.1 a.2 1).1) := hEnd.2.2.2.2.2.2.2.1
  have hSpatial : HasFDerivAt (packetEndpoint S L P lam y R) (R • J) z :=
    hasFDerivAt_framedScaledEndpoint_slice (fun b => (P.Phi lam b 1).1)
      (fun Y => conformalReferenceGramFrameOperatorJoint S.g1 L (lam,Y))
      (hTheta.comp (contDiff_const.prodMk contDiff_id)) y z R
  have hScale := (hasFDerivAt_id (𝕜 := ℝ) u).const_smul R⁻¹
  have hs := hSpatial.comp u hScale
  simp only [Function.comp_def] at hs
  have hCancel : (R • J).comp (R⁻¹ • ContinuousLinearMap.id ℝ R3)=J := by
    apply ContinuousLinearMap.ext
    intro V
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply,map_smul,smul_smul,mul_inv_cancel₀ hR.ne',inv_mul_cancel₀ hR.ne',one_smul]
  rw [hCancel] at hs
  have hv := (hf.differentiable (by simp) (y,u)).hasFDerivAt.comp u (hasFDerivAt_prodMk_right y u)
  simp only [Function.comp_def] at hv
  have heq : (fderiv ℝ f (y,u)).comp (ContinuousLinearMap.inr ℝ R3 R3)=J := hv.unique hs
  rw [heq]
  exact hInv.injective

/-- The original cover's actual open center room, with no cylinder boundary omitted. -/
def nativeCoverCenterRoom (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L) : Set R3 :=
  ⋃ i : Fin C.count, (C.packet i).centers

theorem isOpen_nativeCoverCenterRoom (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L) :
    IsOpen (nativeCoverCenterRoom S L C) := isOpen_iUnion (fun i => (C.packet i).centers_open)

/-- One global pair map from the SAME original coherent endpoint cover, at a fixed positive radius. -/
def nativeVelocityPair (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam R : ℝ) (a : R3 × R3) : R3 × R3 :=
  (nativeCoverEndpoint S L C lam ((a.1,R),R⁻¹ • a.2),a.1)

theorem nativeVelocityPair_eq_packet
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (i : Fin C.count) (y : R3) (hy : y ∈ (C.packet i).centers) (u : R3) (hu : ‖u‖ < R) :
    nativeVelocityPair S L C lam R (y,u)=packetVelocityPair S L (C.packet i) lam R (y,u) := by
  have hz : R⁻¹ • u ∈ closedBall (0 : R3) 2 := by
    have hh := norm_inv_smul_lt_one_of_norm_lt R hR u hu
    simp only [mem_closedBall,dist_zero_right]
    linarith
  exact congrArg (fun X : R3 => (X,y))
    (nativeCoverEndpoint_eq_packet S L C lam hlam i y hy R hR hRoom (R⁻¹ • u) hz)

/-- The coherent global map is genuinely smooth on its entire open velocity room. -/
theorem contDiffOn_nativeVelocityPair
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0 < R) (hRoom : R < C.radiusCeiling) :
    ContDiffOn ℝ ∞ (nativeVelocityPair S L C lam R)
      (nativeCoverCenterRoom S L C ×ˢ ball (0 : R3) R) := by
  intro a ha
  obtain ⟨i,hi⟩ := mem_iUnion.mp ha.1
  have hN : (C.packet i).centers ×ˢ ball (0 : R3) R ∈ 𝓝 a :=
    ((C.packet i).centers_open.prod isOpen_ball).mem_nhds ⟨hi,ha.2⟩
  have hEq : nativeVelocityPair S L C lam R =ᶠ[𝓝 a] packetVelocityPair S L (C.packet i) lam R := by
    filter_upwards [hN] with b hb
    exact nativeVelocityPair_eq_packet S L C lam hlam R hR hRoom i b.1 hb.1 b.2
      (by simpa only [mem_ball,dist_zero_right] using hb.2)
  exact ((contDiff_packetVelocityPair S L (C.packet i) lam R).contDiffAt.congr_of_eventuallyEq hEq).contDiffWithinAt

/-- Every open subset of the genuine global velocity room has OPEN physical image. -/
theorem isOpen_nativeVelocityPair_image
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (A : Set (R3 × R3)) (hA : IsOpen A)
    (hDomain : A ⊆ nativeCoverCenterRoom S L C ×ˢ ball (0 : R3) R) :
    IsOpen (nativeVelocityPair S L C lam R '' A) := by
  let Ai : Fin C.count → Set (R3 × R3) := fun i => A ∩ ((C.packet i).centers ×ˢ univ)
  have hImage : nativeVelocityPair S L C lam R '' A=
      ⋃ i : Fin C.count, packetVelocityPair S L (C.packet i) lam R '' Ai i := by
    ext q
    constructor
    · rintro ⟨a,ha,rfl⟩
      obtain ⟨i,hi⟩ := mem_iUnion.mp (hDomain ha).1
      refine mem_iUnion.mpr ⟨i,a,⟨ha,hi,mem_univ _⟩,?_⟩
      exact (nativeVelocityPair_eq_packet S L C lam hlam R hR hRoom i a.1 hi a.2
        (by simpa only [mem_ball,dist_zero_right] using (hDomain ha).2)).symm
    · intro hq
      obtain ⟨i,a,ha,hq⟩ := mem_iUnion.mp hq
      refine ⟨a,ha.1,?_⟩
      rw [nativeVelocityPair_eq_packet S L C lam hlam R hR hRoom i a.1 ha.2.1 a.2
        (by simpa only [mem_ball,dist_zero_right] using (hDomain ha.1).2)]
      exact hq
  rw [hImage]
  apply isOpen_iUnion
  intro i
  apply isOpen_image_of_actual_invertible_derivative (packetVelocityPair S L (C.packet i) lam R)
    (contDiff_packetVelocityPair S L (C.packet i) lam R) (Ai i)
    (hA.inter ((C.packet i).centers_open.prod isOpen_univ))
  intro a ha
  exact packetVelocityPair_derivative_isInvertible S L (C.packet i) lam
    ⟨hlam.1,hlam.2.trans C.dilation_le_one⟩ R hR (hRoom.le.trans (C.radius_room i).le)
    a.1 ha.2.1 a.2 (by simpa only [mem_ball,dist_zero_right] using (hDomain ha.1).2)

/-- The genuine global normal pair map is injective on its full velocity room. -/
theorem nativeVelocityPair_injOn
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0 < R) (hRoom : R < C.radiusCeiling) :
    InjOn (nativeVelocityPair S L C lam R) (nativeCoverCenterRoom S L C ×ˢ ball (0 : R3) R) := by
  intro a ha b hb hEq
  have hy : a.1=b.1 := congrArg Prod.snd hEq
  obtain ⟨i,hi⟩ := mem_iUnion.mp ha.1
  have hib : b.1 ∈ (C.packet i).centers := by rw [← hy];exact hi
  have hua : ‖a.2‖ < R := by simpa only [mem_ball,dist_zero_right] using ha.2
  have hub : ‖b.2‖ < R := by simpa only [mem_ball,dist_zero_right] using hb.2
  rw [nativeVelocityPair_eq_packet S L C lam hlam R hR hRoom i a.1 hi a.2 hua,
    nativeVelocityPair_eq_packet S L C lam hlam R hR hRoom i b.1 hib b.2 hub] at hEq
  have hEndpoint := congrArg Prod.fst hEq
  change packetEndpoint S L (C.packet i) lam a.1 R (R⁻¹ • a.2)=
    packetEndpoint S L (C.packet i) lam b.1 R (R⁻¹ • b.2) at hEndpoint
  rw [← hy] at hEndpoint
  have hza : R⁻¹ • a.2 ∈ closedBall (0 : R3) 2 := by
    have hh := norm_inv_smul_lt_one_of_norm_lt R hR a.2 hua
    simp only [mem_closedBall,dist_zero_right];linarith
  have hzb : R⁻¹ • b.2 ∈ closedBall (0 : R3) 2 := by
    have hh := norm_inv_smul_lt_one_of_norm_lt R hR b.2 hub
    simp only [mem_closedBall,dist_zero_right];linarith
  have hz := C.normal_injective i lam hlam a.1 hi R hR hRoom hza hzb hEndpoint
  exact Prod.ext hy (smul_right_injective (M := R3) (inv_ne_zero hR.ne') hz)

/-- Every smaller actual radius is represented by the SAME fixed-radius global normal map. -/
theorem packetEndpoint_pair_eq_nativeVelocityPair
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (i : Fin C.count) (y : R3) (hy : y ∈ (C.packet i).centers)
    (r : ℝ) (hr : 0 < r) (hrR : r < R) (z : R3) (hz : ‖z‖=1) :
    (packetEndpoint S L (C.packet i) lam y r z,y)=nativeVelocityPair S L C lam R (y,r • z) := by
  have hu : ‖r • z‖ < R := by simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hr,hz,mul_one] using hrR
  rw [nativeVelocityPair_eq_packet S L C lam hlam R hR hRoom i y hy (r • z) hu]
  change (packetEndpoint S L (C.packet i) lam y r z,y)=
    (packetEndpoint S L (C.packet i) lam y R (R⁻¹ • (r • z)),y)
  rw [packetEndpoint_radius_rescaling S L (C.packet i) lam y r R hR.ne' z]
  congr 2
  rw [smul_smul,div_eq_mul_inv,mul_comm r R⁻¹]

/-- The genuine radial-outside image used for later native continuation. -/
def nativeRadialOutsideRoom (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam R delta Rstar : ℝ) (p : ℕ) : Set (R3 × R3) :=
  nativeVelocityPair S L C lam R '' {a : R3 × R3 |
    a.1 ∈ nativeCoverCenterRoom S L C ∩ interior cylinder ∧
    referenceRadius delta Rstar p L a.1 < ‖a.2‖ ∧ ‖a.2‖ < R}

/-- The actual radial-outside image is open, without a global inverse/realization premise. -/
theorem isOpen_nativeRadialOutsideRoom
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (delta Rstar : ℝ) (hdelta : 0 < delta) (hRstar : 0 < Rstar) (p : ℕ) :
    IsOpen (nativeRadialOutsideRoom S L C lam R delta Rstar p) := by
  let A : Set (R3 × R3) := {a | a.1 ∈ nativeCoverCenterRoom S L C ∩ interior cylinder ∧
    referenceRadius delta Rstar p L a.1 < ‖a.2‖ ∧ ‖a.2‖ < R}
  have hRadius : Continuous (fun a : R3 × R3 => referenceRadius delta Rstar p L a.1) :=
    (contDiff_referenceRadius_actual delta Rstar p L hdelta hRstar).continuous.comp continuous_fst
  have hCenter : IsOpen {a : R3 × R3 | a.1 ∈ nativeCoverCenterRoom S L C ∩ interior cylinder} :=
    ((isOpen_nativeCoverCenterRoom S L C).inter isOpen_interior).preimage continuous_fst
  have hLower : IsOpen {a : R3 × R3 | referenceRadius delta Rstar p L a.1 < ‖a.2‖} :=
    isOpen_lt hRadius continuous_snd.norm
  have hUpper : IsOpen {a : R3 × R3 | ‖a.2‖ < R} := isOpen_lt continuous_snd.norm continuous_const
  have hA : IsOpen A := hCenter.inter (hLower.inter hUpper)
  apply isOpen_nativeVelocityPair_image S L C lam hlam R hR hRoom A hA
  intro a ha
  exact ⟨ha.1.1,by simpa only [mem_ball,dist_zero_right] using ha.2.2⟩

/-- The ENTIRE original compact native sphere front lies in ONE actual open normal image. -/
theorem nativeSphereFront_subset_nativeVelocityImage
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (delta Rstar : ℝ) (hdelta : 0 < delta) (hRstar : 0 < Rstar) (p : ℕ)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < R) :
    nativeSphereFront S L C lam delta Rstar p ⊆
      nativeVelocityPair S L C lam R '' (nativeCoverCenterRoom S L C ×ˢ ball (0 : R3) R) := by
  rintro q ⟨a,ha,rfl⟩
  obtain ⟨i,hi⟩ := C.covers_cylinder a.1 ha.1
  have hz : ‖a.2‖=1 := by simpa only [mem_sphere,dist_zero_right] using ha.2
  let r := referenceRadius delta Rstar p L a.1
  have hr : 0 < r := referenceRadius_pos delta Rstar p L a.1 hdelta hRstar
  have hrR : r < R := hRadius a.1 ha.1
  have hBall : r • a.2 ∈ ball (0 : R3) R := by
    simp only [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hr,hz,mul_one]
    exact hrR
  refine ⟨(a.1,r • a.2),⟨mem_iUnion.mpr ⟨i,hi⟩,hBall⟩,?_⟩
  have hPair := packetEndpoint_pair_eq_nativeVelocityPair S L C lam hlam R hR hRoom i a.1 hi r hr hrR a.2 hz
  have hzClosed : a.2 ∈ closedBall (0 : R3) 2 := by simp only [mem_closedBall,dist_zero_right,hz];norm_num
  have hNative := nativeCoverEndpoint_eq_packet S L C lam hlam i a.1 hi r hr (hrR.trans hRoom) a.2 hzClosed
  exact hPair.symm.trans (congrArg (fun X : R3 => (X,a.1)) hNative.symm)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
