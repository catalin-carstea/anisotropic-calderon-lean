import Calderon.ActualPacketPhysicalOperatorPairing
import Calderon.ActualNativeDensityFiberMean
import Calderon.ActualSphereSobolevConstantOne
import Calderon.ActualNativeOutputCompression
set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic SpectralCoreRegularity SphereHilbertDecomposition ActualFiniteHarmonicCore
  EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConformalDepth
  NativeSmoothSharpTraceCompletion NativeH2ThreeHalfValueTrace MetricVolume MetricOperator
  ActualNormalizedSecondMetricDrift SpectralWeightedGraph SmoothAngularCasimir
attribute [local irreducible] sphereSobolevInclusionL nativePacketPhysicalDensityOperator
  nativeMixedKernelDensityFunctional sphereSobolevConstantOne harmonicSphereSubspace

theorem sphereSobolevDualPairing_constantOne_right
    (s:ℝ) (f:SphereSobolev s):
    sphereSobolevDualPairing s f (sphereSobolevConstantOne (-s))=
      ⟪(sphereSobolevCoefficientL s 0 f:SphereL2),polynomialSphereL2 (C 1)⟫_ℝ := by
  rw [sphereSobolevDualPairing_eq_tsum]
  have hSingle:sphereSobolevConstantOne (-s)=sphereSobolevSingleL (-s) 0
      ⟨polynomialSphereL2 (C 1),polynomialSphereL2_mem 0 (C 1) (C_harmonicHomogeneous 1)⟩ := by unfold sphereSobolevConstantOne; rfl
  rw [hSingle,tsum_eq_single 0]
  · rw [sphereSobolevCoefficientL_single_self]
    rfl
  · intro k hk
    rw [sphereSobolevCoefficientL_single_ne (-s) 0 k hk,inner_zero_right]

theorem sphereSobolevDualPairing_L2_constantOne_eq_sphereMean
    (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics) (v:SphereL2):
    sphereSobolevDualPairing (-(1/2:ℝ))
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD v))
      (sphereSobolevConstantOne (1/2:ℝ))=sphereMean v := by
  have h:=sphereSobolevDualPairing_constantOne_right (-(1/2:ℝ))
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD v))
  have hPair:sphereSobolevDualPairing (-(1/2:ℝ))
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD v))
      (sphereSobolevConstantOne (1/2:ℝ))=
      ⟪(sphereSobolevCoefficientL (-(1/2:ℝ)) 0
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (sphereSobolevZeroEquiv hO hD v)):SphereL2),
        polynomialSphereL2 (C 1)⟫_ℝ := by
    convert h using 1 <;> simp [sphereSobolevConstantOne,sphereSobolevSingleL,besselWeight]
  rw [hPair,sphereSobolevCoefficientL_inclusion,sphereSobolevCoefficientL_zeroEquiv]
  have hi:=sphereHarmonicCoordinate_inner hO hD 0 v
    (⟨polynomialSphereL2 (C 1),polynomialSphereL2_mem 0 (C 1) (C_harmonicHomogeneous 1)⟩:harmonicSphereSubspace 0)
  exact hi.trans (real_inner_comm _ _)

theorem smoothHalfTrace_constant_one
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace):
    smoothHalfTrace hF hO hD tau0 (⟨fun _ => (1:ℝ),contDiff_const⟩:SmoothData)=
      sphereSobolevConstantOne (1/2:ℝ) := by
  apply sphereSobolev_ext (1/2:ℝ)
  intro k
  rw [sphereSobolevCoefficientL_smoothHalfTrace,tau0.valueTrace_smooth]
  have hValue:smoothSphereValue (⟨fun _ => (1:ℝ),contDiff_const⟩:SmoothData)=polynomialSphere (C 1) := by
    ext z
    simp [smoothSphereValue,polynomialSphere]
  rw [hValue]
  change sphereHarmonicCoordinate hO hD k (polynomialSphereL2 (C 1))=_
  have hZero:=sphereSobolevZeroEquiv_symm_constantOne hO hD
  have hEq:sphereSobolevZeroEquiv hO hD (polynomialSphereL2 (C 1))=sphereSobolevConstantOne 0 :=
    (sphereSobolevZeroEquiv hO hD).apply_symm_apply (sphereSobolevConstantOne 0) ▸ congrArg (sphereSobolevZeroEquiv hO hD) hZero.symm
  rw [← sphereSobolevCoefficientL_zeroEquiv,hEq]
  have hInc:=congrArg (sphereSobolevCoefficientL 0 k)
    (sphereSobolevInclusionL_constantOne (1/2:ℝ) 0 (by norm_num))
  exact hInc.symm.trans (sphereSobolevCoefficientL_inclusion (1/2:ℝ) 0 (by norm_num) (sphereSobolevConstantOne (1/2:ℝ)) k)


theorem sphereSobolevDualPairing_partialSum_constantOne
    (s:ℝ) (n:ℕ) (hn:1 ≤ n) (f:SphereSobolev s):
    sphereSobolevDualPairing s (sphereSobolevPartialSumL s n f) (sphereSobolevConstantOne (-s))=
      sphereSobolevDualPairing s f (sphereSobolevConstantOne (-s)) := by
  rw [sphereSobolevDualPairing_constantOne_right,sphereSobolevDualPairing_constantOne_right,
    sphereSobolevPartialSumL_apply,sphereSobolevCoefficientL_partialSum,
    ite_eq_left (show 0 < n by omega)]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
