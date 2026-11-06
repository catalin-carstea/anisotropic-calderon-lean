import Calderon.ActualNativeCoverSmoothPartition
import Calderon.ActualSupportedPacketPhysicalCoherence
import Calderon.ActualCutoffCommutatorSourceRoom
import Calderon.ActualDensityPrincipalFrameSmoothness
import Calderon.ActualScalarCutoffJointCoefficients
import Calderon.ActualNativeCutoffHalfLift
import Calderon.ActualFiniteCoreSobolevRepresentation
import Calderon.SphereSobolevHalfWeightedGraphLowering
import Calderon.ActualSupportedMeanZeroFiniteCore

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  ActualFiniteHarmonicCore ConnectionError ConformalDepth RadiusProfile
  ReferenceWeightedApproximation ActualScalarPrincipalAdjoint MetricOperator MetricVolume
  ActualNormalizedSecondMetricDrift SmoothMetricFrame MovingFrameConnection

attribute [local irreducible] referencePhysicalDensityOperator
  referenceDensityScalarCutoffCommutator
  referenceHighDensityFirstAction
  sphereSobolevInclusionL
  sphereSobolevZeroEquiv
  sphereSobolevHalfToSphereL2L
  finiteCoreSobolevLift

/-- The direct full physical Half commutator for the actual finite input, without
subtracting the continuation density's constant mode. -/
def nativePacketScalarCutoffCommutatorHalf
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (tau0 : UnitBallValueTrace) (S : KnownSideSourceData) (L : ℝ)
    (cover : NativeNormalCover S L) (q delta Rstar : ℝ) (p : ℕ)
    (theta : R3 → ℝ) (F : smoothCompactFiniteSphereCore hO hD)
    (i : Fin cover.count) (x : R3) : SphereSobolev (1/2 : ℝ) :=
  let P := cover.packet i
  referenceDensityScalarCutoffCommutator S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho
    P.H P.a P.w P.native_data S.g1_admissible hcalc hF hO hD tau0 S.g2 q
    (referenceRadius delta Rstar p L) theta (finiteCoreSobolevLift hO hD (3/2 : ℝ) F) x

/-- The full spherical L2 representative obtained through the genuine forward
Half-to-zero inclusion and the inverse zero-order isometry. -/
def nativePacketScalarCutoffCommutatorL2
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (tau0 : UnitBallValueTrace) (S : KnownSideSourceData) (L : ℝ)
    (cover : NativeNormalCover S L) (q delta Rstar : ℝ) (p : ℕ)
    (theta : R3 → ℝ) (F : smoothCompactFiniteSphereCore hO hD)
    (i : Fin cover.count) (x : R3) : SphereL2 :=
  sphereSobolevHalfToSphereL2L hO hD
    (nativePacketScalarCutoffCommutatorHalf hcalc hF hO hD tau0 S L cover q delta Rstar p theta F i x)

private lemma full_cutoff_graph_clm_algebra
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (K : E →L[ℝ] G) (theta : ℝ) (v c : E) (a b z : G)
    (hv : K v = a) (hc : K c = b) (hProduct : z-theta • a = b) :
    K (theta • v+c) = z := by
  rw [map_add, map_smul, hv, hc, ← hProduct]
  abel

private lemma raw_scalar_commutator_support_input
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Phi : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (eps C rho : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Phi B eps C rho H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (tau0 : UnitBallValueTrace) (g2 : MatrixField) (q : ℝ) (R theta : R3 → ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) :
    tsupport (referenceDensityScalarCutoffCommutator
      g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0 g2 q R theta u) ⊆ tsupport u := by
  apply closure_minimal _ (isClosed_tsupport u)
  intro y hy
  by_contra hOutside
  have hu0 : u y = 0 := image_eq_zero_of_notMem_tsupport hOutside
  have hFirst (j : Fin 3) : referenceHighDensityFirstAction
      g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0 q R u y j = 0 :=
    image_eq_zero_of_notMem_tsupport
      (f := fun z : R3 => referenceHighDensityFirstAction
        g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0 q R u z j)
      (fun hz => hOutside (tsupport_referenceHighDensityFirstAction_subset
        g L y0 Phi B eps C rho H a w hData hg hcalc hF hO hD tau0 q R u j hz))
  apply hy
  simp only [referenceDensityScalarCutoffCommutator, hu0, hFirst, map_zero,
    smul_zero, add_zero, Finset.sum_const_zero]

private lemma native_packet_scalar_cutoff_room
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (tau0 : UnitBallValueTrace) (S : KnownSideSourceData) (L q delta Rstar : ℝ)
    (p : ℕ) (cover : NativeNormalCover S L) (hd : 0 < delta) (hRs : 0 < Rstar)
    (hq : q ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (i : Fin cover.count) (y : R3) (hy : y ∈ interior cylinder ∩ (cover.packet i).centers) :
    let P := cover.packet i
    let R := referenceRadius delta Rstar p L
    (∀ omega : UnitSphere,
      (referenceFramedNormalizedJacobian S.g1 L P.Phi (q,((y,R y),omega.val))).IsInvertible) ∧
    (q,(y,R y)) ∈ referenceRadialEndpointInvertibleLocus S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho
      P.H P.a P.w P.native_data hcalc hF hO hD tau0 := by
  dsimp only
  let P := cover.packet i
  let R := referenceRadius delta Rstar p L
  have hqOne : q ∈ Icc (0 : ℝ) 1 := ⟨hq.1, hq.2.trans cover.dilation_le_one⟩
  have hPos : 0 < R y := referenceRadius_pos delta Rstar p L y hd hRs
  have hCenter : ‖y-P.y0‖ ≤ 4*P.rho := (P.centers_room y hy.2).1.le
  have hAbs : |R y| ≤ 4*P.rho := by
    rw [abs_of_pos hPos]
    exact ((hRadius y (interior_subset hy.1)).trans (cover.radius_room i)).le
  have hInv (omega : UnitSphere) :
      (referenceFramedNormalizedJacobian S.g1 L P.Phi (q,((y,R y),omega.val))).IsInvertible := by
    apply isInvertible_of_operatorMatrixMap_det_ne_zero
    exact referenceFramedNormalizedJacobian_det_ne_zero_on_closedDoubleBall S.g1 S.g1_admissible L
      P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data q hqOne y hCenter (R y) hAbs
      omega.val (closedBall_subset_closedBall (by norm_num) (sphere_subset_closedBall omega.property))
  have hp := referenceRadialEndpointInvertibleLocus_mem_on_actual_room S.g1 S.g1_admissible L
    P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data hcalc hreg hF hO hD tau0
    q hqOne y hCenter (R y) hAbs
  exact ⟨hInv, hp⟩

/-- The original full cover graph forces the arbitrary full output to be supported
in the original finite source, by locality and injectivity only. -/
theorem tsupport_native_cover_physical_output_subset_source
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (tau0 : UnitBallValueTrace) (S : KnownSideSourceData) (L q delta Rstar : ℝ)
    (p : ℕ) (cover : NativeNormalCover S L)
    (F : smoothCompactFiniteSphereCore hO hD) (V : R3 → SphereL2)
    (hVS : tsupport V ⊆ interior cylinder)
    (hGraph : ∀ i : Fin cover.count, ∀ y ∈ interior cylinder ∩ (cover.packet i).centers,
      sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (V y)) =
      nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F) i y) :
    tsupport V ⊆ tsupport F.val := by
  let u := finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have huSupport : tsupport u ⊆ tsupport F.val :=
    (finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) F).2.2.1
  apply closure_minimal _ (isClosed_tsupport F.val)
  intro y hy
  by_contra hOutside
  apply hy
  by_cases hyCylinder : y ∈ interior cylinder
  · obtain ⟨i, hi⟩ := cover.covers_cylinder y (interior_subset hyCylinder)
    have hZero : nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p u i y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hp => hOutside (huSupport
        (tsupport_nativePacketPhysicalDensityOperator_subset hcalc hF hO hD tau0 S L q delta Rstar p
          cover u i hp)))
    apply (sphereSobolevZeroEquiv hO hD).injective
    apply sphereSobolevInclusionL_injective 0 (-(1/2 : ℝ)) (by norm_num)
    rw [hGraph i y ⟨hyCylinder, hi⟩, hZero, map_zero, map_zero]
  · exact image_eq_zero_of_notMem_tsupport (fun hh => hyCylinder (hVS hh))

/-- The direct actual commutator is smooth and compact in the full L2 space;
its support stays in both the scalar cutoff and the original finite input. -/
theorem nativePacketScalarCutoffCommutatorL2_smooth_support
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (tau0 : UnitBallValueTrace) (S : KnownSideSourceData) (L q delta Rstar : ℝ)
    (p : ℕ) (cover : NativeNormalCover S L) (hd : 0 < delta) (hRs : 0 < Rstar)
    (hq : q ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (i : Fin cover.count) (theta : R3 → ℝ) (hTheta : ContDiff ℝ ∞ theta)
    (hThetaSupport : tsupport theta ⊆ (cover.packet i).centers)
    (F : smoothCompactFiniteSphereCore hO hD) (hFS : tsupport F.val ⊆ interior cylinder) :
    let C := nativePacketScalarCutoffCommutatorL2 hcalc hF hO hD tau0 S L cover q delta Rstar p theta F i
    ContDiff ℝ ∞ C ∧ HasCompactSupport C ∧ tsupport C ⊆ tsupport theta ∩ tsupport F.val := by
  let P := cover.packet i
  let R := referenceRadius delta Rstar p L
  let u := finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  let Half := nativePacketScalarCutoffCommutatorHalf hcalc hF hO hD tau0 S L cover q delta Rstar p theta F i
  let C := nativePacketScalarCutoffCommutatorL2 hcalc hF hO hD tau0 S L cover q delta Rstar p theta F i
  have hu : ContDiff ℝ ∞ u := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have huSupport : tsupport u ⊆ tsupport F.val :=
    (finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) F).2.2.1
  have hHalfU : tsupport Half ⊆ tsupport u := raw_scalar_commutator_support_input
    S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data S.g1_admissible
    hcalc hF hO hD tau0 S.g2 q R theta u
  have hHalfTheta : tsupport Half ⊆ tsupport theta :=
    (tsupport_referenceDensityScalarCutoffCommutator_subset S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho
      P.H P.a P.w P.native_data S.g1_admissible hcalc hF hO hD tau0 S.g2 q R theta u).trans
      (show tsupport (fderiv ℝ theta) ⊆ tsupport theta from tsupport_fderiv_subset ℝ)
  have hR : ContDiff ℝ ∞ R := contDiff_referenceRadius_actual delta Rstar p L hd hRs
  have hIu : ContDiff ℝ ∞ (fun y =>
      sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (u y)) :=
    (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).contDiff.comp hu
  have hPrincipal (j k : Fin 3) : ContDiff ℝ ∞
      (fun y : R3 => referenceDensityPrincipalFrameCoefficient S.g1 S.g2 L q y j k) := by
    simpa only [Function.comp_def, id_eq] using
      (contDiff_referenceDensityPrincipalFrameCoefficient_joint S.g1 S.g2
        S.g1_admissible S.g2_admissible L j k).comp (contDiff_const.prodMk contDiff_id)
  have hDerivative (j : Fin 3) : ContDiff ℝ ∞
      (fun y : R3 => referenceFrameScalarDerivative S.g1 L q theta y j) := by
    simpa only [Function.comp_def, id_eq] using
      (contDiff_referenceFrameScalarDerivative_joint S.g1 S.g1_admissible L theta hTheta j).comp
        (contDiff_const.prodMk contDiff_id)
  have hHessian (j k : Fin 3) : ContDiff ℝ ∞
      (fun y : R3 => referenceFrameScalarHessian S.g1 L q theta y j k) := by
    simpa only [Function.comp_def, id_eq] using
      (contDiff_referenceFrameScalarHessian_joint S.g1 S.g1_admissible L theta hTheta j k).comp
        (contDiff_const.prodMk contDiff_id)
  have hDrift (j : Fin 3) : ContDiff ℝ ∞
      (fun y : R3 => normalizedSecondDriftFrameJoint S.g1 S.g2 L j (q,y)) := by
    simpa only [Function.comp_def, id_eq] using
      (contDiff_normalizedSecondDriftFrameJoint S.g1 S.g2 S.g1_admissible S.g2_admissible L j).comp
        (contDiff_const.prodMk contDiff_id)
  have hHalf : ContDiff ℝ ∞ Half := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ tsupport Half
    · have hyRoom : y ∈ interior cylinder ∩ (cover.packet i).centers :=
        ⟨hFS (huSupport (hHalfU hy)), hThetaSupport (hHalfTheta hy)⟩
      obtain ⟨hInv, hp⟩ := native_packet_scalar_cutoff_room
        hcalc hreg hF hO hD tau0 S L q delta Rstar p cover hd hRs hq hRadius i y hyRoom
      have hPos : 0 < R y := referenceRadius_pos delta Rstar p L y hd hRs
      have hFirst (j : Fin 3) : ContDiffAt ℝ ∞ (fun z : R3 => referenceHighDensityFirstAction
          S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data S.g1_admissible
          hcalc hF hO hD tau0 q R u z j) y :=
        contDiffAt_referenceHighDensityFirstAction S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho
          P.H P.a P.w P.native_data S.g1_admissible hcalc hF hO hD tau0 hreg q R u y j
          hu.contDiffAt hR.contDiffAt hPos.ne' hInv hp
      dsimp only [Half]
      unfold nativePacketScalarCutoffCommutatorHalf
      unfold referenceDensityScalarCutoffCommutator
      change ContDiffAt ℝ ∞ (fun z : R3 => R z •
        ((∑ j : Fin 3, ∑ k : Fin 3,
          referenceDensityPrincipalFrameCoefficient S.g1 S.g2 L q z j k •
            (referenceFrameScalarDerivative S.g1 L q theta z j • referenceHighDensityFirstAction
                S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data S.g1_admissible
                hcalc hF hO hD tau0 q R u z k +
             referenceFrameScalarDerivative S.g1 L q theta z k • referenceHighDensityFirstAction
                S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data S.g1_admissible
                hcalc hF hO hD tau0 q R u z j +
             referenceFrameScalarHessian S.g1 L q theta z j k •
                sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (u z)))+
         ∑ j : Fin 3, normalizedSecondDriftFrameJoint S.g1 S.g2 L j (q,z) •
           (referenceFrameScalarDerivative S.g1 L q theta z j •
             sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (u z)))) y
      exact hR.contDiffAt.smul
        ((ContDiffAt.sum (fun j _ => ContDiffAt.sum (fun k _ =>
          (hPrincipal j k).contDiffAt.smul
            ((((hDerivative j).contDiffAt.smul (hFirst k)).add
              ((hDerivative k).contDiffAt.smul (hFirst j))).add
              ((hHessian j k).contDiffAt.smul hIu.contDiffAt))))).add
          (ContDiffAt.sum (fun j _ => (hDrift j).contDiffAt.smul
            ((hDerivative j).contDiffAt.smul hIu.contDiffAt))))
    · have hZero : Half =ᶠ[𝓝 y] (fun _ : R3 => (0 : SphereSobolev (1/2 : ℝ))) :=
        notMem_tsupport_iff_eventuallyEq.mp hy
      exact (contDiffAt_const : ContDiffAt ℝ ∞
        (fun _ : R3 => (0 : SphereSobolev (1/2 : ℝ))) y).congr_of_eventuallyEq hZero
  have hC : ContDiff ℝ ∞ C := (sphereSobolevHalfToSphereL2L hO hD).contDiff.comp hHalf
  have hMap : tsupport C ⊆ tsupport Half :=
    tsupport_comp_subset (map_zero (sphereSobolevHalfToSphereL2L hO hD)) Half
  have hSupport : tsupport C ⊆ tsupport theta ∩ tsupport F.val := fun y hy =>
    ⟨hHalfTheta (hMap hy), huSupport (hHalfU (hMap hy))⟩
  exact ⟨hC, F.property.2.1.of_isClosed_subset (isClosed_tsupport C)
    (fun y hy => (hSupport hy).2), hSupport⟩

/-- A scalar-localized finite source has the actual full L2 output theta V+C on
all native packets, with the unchanged physical negative graph. -/
theorem native_cover_scalar_cutoff_output_graph
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (tau0 : UnitBallValueTrace) (hKernel : UnitBallValueTraceKernel tau0)
    (S : KnownSideSourceData) (L q delta Rstar : ℝ) (p : ℕ) (cover : NativeNormalCover S L)
    (hd : 0 < delta) (hRs : 0 < Rstar) (hq : q ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (i : Fin cover.count) (theta : R3 → ℝ) (hTheta : ContDiff ℝ ∞ theta)
    (hThetaSupport : tsupport theta ⊆ (cover.packet i).centers)
    (F : smoothCompactFiniteSphereCore hO hD) (hFS : tsupport F.val ⊆ interior cylinder)
    (V : R3 → SphereL2) (hV : ContDiff ℝ ∞ V) (hVS : tsupport V ⊆ interior cylinder)
    (hGraph : ∀ j : Fin cover.count, ∀ y ∈ interior cylinder ∩ (cover.packet j).centers,
      sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (V y)) =
      nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) F) j y) :
    let Fi := coreScalar hO hD theta hTheta F
    let Wi : R3 → SphereL2 := fun y => theta y • V y +
      nativePacketScalarCutoffCommutatorL2 hcalc hF hO hD tau0 S L cover q delta Rstar p theta F i y
    ContDiff ℝ ∞ Wi ∧ HasCompactSupport Wi ∧ tsupport Wi ⊆ tsupport theta ∩ tsupport F.val ∧
    ∀ j : Fin cover.count, ∀ y ∈ interior cylinder ∩ (cover.packet j).centers,
      sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD (Wi y)) =
      nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
        (finiteCoreSobolevLift hO hD (3/2 : ℝ) Fi) j y := by
  let P := cover.packet i
  let R := referenceRadius delta Rstar p L
  let u := finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  let Fi := coreScalar hO hD theta hTheta F
  let ui := finiteCoreSobolevLift hO hD (3/2 : ℝ) Fi
  let Half := nativePacketScalarCutoffCommutatorHalf hcalc hF hO hD tau0 S L cover q delta Rstar p theta F i
  let C := nativePacketScalarCutoffCommutatorL2 hcalc hF hO hD tau0 S L cover q delta Rstar p theta F i
  let Wi : R3 → SphereL2 := fun y => theta y • V y+C y
  let K := tsupport theta ∩ tsupport F.val
  let K0 : SphereL2 →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)).comp
      (sphereSobolevZeroEquiv hO hD).toContinuousLinearEquiv.toContinuousLinearMap
  have hVSupport := tsupport_native_cover_physical_output_subset_source
    hcalc hF hO hD tau0 S L q delta Rstar p cover F V hVS hGraph
  have hCData := nativePacketScalarCutoffCommutatorL2_smooth_support
    hcalc hreg hF hO hD tau0 S L q delta Rstar p cover hd hRs hq hRadius i theta hTheta hThetaSupport F hFS
  change ContDiff ℝ ∞ C ∧ HasCompactSupport C ∧ tsupport C ⊆ K at hCData
  obtain ⟨hC, _hCCompact, hCSupport⟩ := hCData
  have hWi : ContDiff ℝ ∞ Wi := (hTheta.smul hV).add hC
  have hWSupport : tsupport Wi ⊆ K := tsupport_sphereL2_add_subset_of_closed K
    ((isClosed_tsupport theta).inter (isClosed_tsupport F.val)) (fun y => theta y • V y) C
    (fun y hy => ⟨tsupport_smul_subset_left theta V hy,
      hVSupport (tsupport_smul_subset_right theta V hy)⟩) hCSupport
  have hWCompact : HasCompactSupport Wi := F.property.2.1.of_isClosed_subset (isClosed_tsupport Wi)
    (fun y hy => (hWSupport hy).2)
  have hFiTheta : tsupport Fi.val ⊆ tsupport theta := tsupport_smul_subset_left theta F.val
  have hFiF : tsupport Fi.val ⊆ tsupport F.val := tsupport_smul_subset_right theta F.val
  have hUiSupport : tsupport ui ⊆ K := fun y hy =>
    let hh := (finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) Fi).2.2.1 hy
    ⟨hFiTheta hh, hFiF hh⟩
  have hui : ContDiff ℝ ∞ ui := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) Fi
  have hu : ContDiff ℝ ∞ u := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F
  have hLift : ui = fun y => theta y • u y := by
    funext y
    exact finiteCoreSobolevLift_coreScalar hO hD (3/2 : ℝ) theta hTheta F y
  have hR : ContDiff ℝ ∞ R := contDiff_referenceRadius_actual delta Rstar p L hd hRs
  have hCompat (y : R3) : K0 (C y) =
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (Half y) :=
    sphereSobolevHalfToSphereL2L_negative_compatibility hO hD (Half y)
  have hGlobal (y : R3) : K0 (Wi y) =
      nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p ui i y := by
    by_cases hy : y ∈ interior cylinder ∩ (cover.packet i).centers
    · obtain ⟨hInv, hp⟩ := native_packet_scalar_cutoff_room
        hcalc hreg hF hO hD tau0 S L q delta Rstar p cover hd hRs hq hRadius i y hy
      have hPos : 0 < R y := referenceRadius_pos delta Rstar p L y hd hRs
      have hRaw := referencePhysicalDensityOperator_smul_sub S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho
        P.H P.a P.w P.native_data S.g1_admissible hcalc hF hO hD tau0 S.g2 hreg q R theta u y
        hu hTheta hR.contDiffAt hPos.ne' hInv hp
      have hRawNative : nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
          (fun z => theta z • u z) i y-
          theta y • nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p u i y =
          sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (Half y) := hRaw
      have hTransport : nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p ui i y =
          nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p
            (fun z => theta z • u z) i y :=
        congrArg (fun v : R3 → SphereSobolev (3/2 : ℝ) =>
          nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p v i y) hLift
      have hProduct : nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p ui i y-
          theta y • nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p u i y =
          sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (Half y) :=
        (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => z-
          theta y • nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p u i y)
          hTransport).trans hRawNative
      have hOriginal : K0 (V y) =
          nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p u i y :=
        hGraph i y hy
      change K0 (theta y • V y+C y) =
        nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p ui i y
      exact full_cutoff_graph_clm_algebra K0 (theta y) (V y) (C y)
        (nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p u i y)
        (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (Half y))
        (nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover q delta Rstar p ui i y)
        hOriginal (hCompat y) hProduct
    · have hWZero : Wi y = 0 := image_eq_zero_of_notMem_tsupport
        (fun hh => hy ⟨hFS (hWSupport hh).2, hThetaSupport (hWSupport hh).1⟩)
      have hPZero : nativePacketPhysicalDensityOperator
          hcalc hF hO hD tau0 S L cover q delta Rstar p ui i y = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hh =>
          let huHere := hUiSupport (tsupport_nativePacketPhysicalDensityOperator_subset
            hcalc hF hO hD tau0 S L q delta Rstar p cover ui i hh)
          hy ⟨hFS huHere.2, hThetaSupport huHere.1⟩)
      calc
        K0 (Wi y) = K0 0 := congrArg K0 hWZero
        _ = 0 := K0.map_zero
        _ = nativePacketPhysicalDensityOperator
            hcalc hF hO hD tau0 S L cover q delta Rstar p ui i y := hPZero.symm
  refine ⟨hWi, hWCompact, hWSupport, ?_⟩
  intro j y hy
  exact (hGlobal y).trans (nativePacketPhysicalDensityOperator_eq_of_supported_source
    hcalc hreg hF hO hD tau0 hKernel S L q delta Rstar p cover hd hRs hq i j K
      (fun z hz => hThetaSupport hz.1) ui hui hUiSupport y hy.2 (hRadius y (interior_subset hy.1)))

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
