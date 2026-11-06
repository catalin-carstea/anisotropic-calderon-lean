import Calderon.ActualCoveredScalarTransfer
import Calderon.ActualPhysicalHarmonicTestPairingWithoutJointChart
import Calderon.ActualMixedKernelFunctionalTraceDictionary
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic ConnectionError
  ConformalDepth ReferenceWeightedApproximation ActualScalarPrincipalAdjoint MetricVolume MetricOperator
  NativeSmoothSharpTraceCompletion NativeH2ThreeHalfValueTrace ActualNormalizedSecondMetricDrift
attribute [local irreducible] referencePhysicalDensityOperator sphereSobolevInclusionL
  referenceRadialEndpointInvertibleLocus referenceFramedNormalizedJacobian harmonicSphereSubspace
  sphereSobolevDualPairing nativeMixedKernelDensityFunctional referencePhysicalNativeThreeHalfTraceSection

def nativePacketPhysicalDensityOperator
    (hcalc:FixedSobolevCalculus) (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics)
    (hD:DenseSphereHarmonics) (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (L:ℝ)
    (cover:NativeNormalCover S L) (lambda delta Rstar:ℝ) (p:ℕ)
    (Psi:R3→SphereSobolev (3/2:ℝ)) (i:Fin cover.count) (y:R3):SphereSobolev (-(1/2:ℝ)) :=
  let P:=cover.packet i
  referencePhysicalDensityOperator S.g1 L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
    S.g1_admissible hcalc hF hO hD tau0 S.g2 lambda (referenceRadius delta Rstar p L) Psi y

theorem nativePacketPhysicalDensityOperator_pairing_physical_harmonic_test
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (hKernel:UnitBallValueTraceKernel tau0)
    (S:KnownSideSourceData) (L lambda delta Rstar:ℝ) (p:ℕ) (cover:NativeNormalCover S L)
    (hd:0 < delta) (hRs:0 < Rstar) (hLam:lambda∈Icc (0:ℝ) cover.dilationCeiling)
    (i:Fin cover.count) (y:R3) (hy:y∈(cover.packet i).centers)
    (hrceil:referenceRadius delta Rstar p L y < cover.radiusCeiling)
    (Psi:R3→SphereSobolev (3/2:ℝ)) (hPsi:ContDiff ℝ ∞ Psi)
    (V:Set R3) (hV:IsOpen V) (u:SmoothData)
    (hCover:packetEndpoint S L (cover.packet i) lambda y (referenceRadius delta Rstar p L y) '' closedBall (0:R3) 1⊆V)
    (hPhysical:∀ x∈V,coordinateFluxDivergence (metricDivergenceFlux (fun z => S.g1 (lambda • z)) u.1) x=0):
    referenceRadius delta Rstar p L y * normalizedSecondLaplacian S.g1 S.g2 L lambda
      (nativeMixedKernelDensityFunctional hO hD tau0 S L (cover.packet i) lambda delta Rstar p Psi u) y=
    sphereSobolevDualPairing (-(1/2:ℝ))
      (nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p Psi i y)
      (smoothHalfTrace hF hO hD tau0 (referencePhysicalPullbackData S.g1 S.g1_admissible L
        (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B (cover.packet i).native_data.1.1.1
        lambda y (referenceRadius delta Rstar p L y) u)) := by
  let P:=cover.packet i
  let R:R3→ℝ := referenceRadius delta Rstar p L
  let r:=R y
  have hq:lambda∈Icc (0:ℝ) 1 := ⟨hLam.1,hLam.2.trans cover.dilation_le_one⟩
  have hc:‖y-P.y0‖ < 4*P.rho := (P.centers_room y hy).1
  have hrpos:0 < r := referenceRadius_pos delta Rstar p L y hd hRs
  have hr:|r| < 4*P.rho := by rw [abs_of_pos hrpos];exact hrceil.trans (cover.radius_room i)
  have hR:ContDiff ℝ ∞ R := contDiff_referenceRadius_actual delta Rstar p L hd hRs
  have hInv (x:UnitSphere):(referenceFramedNormalizedJacobian S.g1 L P.Phi (lambda,((y,r),x.val))).IsInvertible := by
    apply isInvertible_of_operatorMatrixMap_det_ne_zero
    exact referenceFramedNormalizedJacobian_det_ne_zero_on_closedDoubleBall S.g1 S.g1_admissible L
      P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data lambda hq y hc.le r hr.le x.val
      (closedBall_subset_closedBall (by norm_num) (sphere_subset_closedBall x.property))
  have hp:=referenceRadialEndpointInvertibleLocus_mem_on_actual_room S.g1 S.g1_admissible L P.y0 P.Phi
    P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data hcalc hreg hF hO hD tau0 lambda hq y hc.le r hr.le
  let U:R3→SphereSobolev (3/2:ℝ) := referencePhysicalNativeThreeHalfTraceSection
    S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
    hcalc hF hO hD tau0 lambda R u
  let I:=sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let J:=sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let f:R3→ℝ := fun z => sphereSobolevDualPairing (-(1/2:ℝ)) (J (I (Psi z))) (I (U z))
  have hFunc:f=nativeMixedKernelDensityFunctional hO hD tau0 S L P lambda delta Rstar p Psi u := by
    funext z
    simpa only [f,I,J,U,referencePhysicalNativeThreeHalfTraceSection,R] using
      (nativeMixedKernelDensityFunctional_eq_native_dualTracePairing hcalc hF hO hD tau0
        S L P lambda delta Rstar p Psi u z).symm
  have hPair:=referencePhysicalDensityOperator_pairing_physical_harmonic_neighborhood
    S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
    S.g2 S.g2_admissible hcalc hreg hF hO hD tau0 hKernel lambda hq R hR y hc hr hrpos.ne'
    (P.centers_room y hy).2 hInv hp V hV u hCover hPhysical Psi hPsi
  have hHalf:I (U y)=smoothHalfTrace hF hO hD tau0
      (referencePhysicalPullbackData S.g1 S.g1_admissible L P.y0 P.Phi P.B P.native_data.1.1.1 lambda y r u) :=
    by simpa only [I,U,referencePhysicalNativeThreeHalfTraceSection,R,r] using
      sphereSobolevInclusionL_nativeThreeHalfValueTraceL_smoothBallSobolev hcalc hF hO hD tau0
        (referencePhysicalPullbackData S.g1 S.g1_admissible L P.y0 P.Phi P.B P.native_data.1.1.1 lambda y r u)
  have hPair':r*normalizedSecondLaplacian S.g1 S.g2 L lambda f y=
      sphereSobolevDualPairing (-(1/2:ℝ))
        (nativePacketPhysicalDensityOperator hcalc hF hO hD tau0 S L cover lambda delta Rstar p Psi i y)
        (I (U y)) := hPair
  rw [hFunc,hHalf] at hPair'
  exact hPair'

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
