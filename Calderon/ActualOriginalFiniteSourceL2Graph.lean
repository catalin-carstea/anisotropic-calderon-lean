import Calderon.ActualOriginalDensitySourceNormShift
import Calderon.ActualFiniteCoreSobolevRepresentation
import Calderon.SupportedSpectralFiniteSumConvergence
import Calderon.ActualSameFiveHalfSourceCoreApprox
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open SphereHarmonic ActualFiniteHarmonicCore WeightedBaseSpectral ReferenceDensityBounds
  SpectralCoreRegularity SpectralWeightedGraph SphereHilbertDecomposition
attribute [local irreducible] nativeDensitySphereL2L sphereSobolevInclusionL sphereSobolevPartialSumL
  harmonicSphereSubspace finiteCoreSobolevLift

theorem nativeDensitySphereL2L_finiteCoreSobolevLift
    (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (A:smoothCompactFiniteSphereCore hO hD) (y:R3):
    nativeDensitySphereL2L hO hD (finiteCoreSobolevLift hO hD (3/2:ℝ) A y)=(A:R3→SphereL2) y := by
  have hRep:=finiteCoreSobolevLift_representation hO hD (3/2:ℝ) (by norm_num) A
  unfold nativeDensitySphereL2L
  change (sphereSobolevZeroEquiv hO hD).symm
    (sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) (finiteCoreSobolevLift hO hD (3/2:ℝ) A y))=_
  rw [hRep.2.2.2.1 y]
  exact (sphereSobolevZeroEquiv hO hD).symm_apply_apply _

theorem tendsto_weighted_nativeDensitySphereL2L_partialSum_of_fiveHalf
    (g:MatrixField) (hg:IsAdmissibleMetric g) (L q:ℝ)
    (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (U5:R3→SphereSobolev (5/2:ℝ)) (hU5:ContDiff ℝ ∞ U5) (hComp:HasCompactSupport U5)
    (u:R3→SphereSobolev (3/2:ℝ))
    (hEq:(fun y => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U5 y))=u):
    Tendsto (fun n:ℕ => ∫ y,referenceDensityFamily g L (q,y)*
      ‖nativeDensitySphereL2L hO hD (sphereSobolevPartialSumL (3/2:ℝ) n (u y))-
        nativeDensitySphereL2L hO hD (u y)‖^2) atTop (𝓝 0) := by
  let T:=nativeDensitySphereL2L hO hD
  let I:=sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
  let B:SphereSobolev (5/2:ℝ)→L[ℝ] SphereL2 := T.comp I
  have h:=tendsto_integral_supported_finite_clm_partialSum_error g hg L q (tsupport U5) hComp
    (fun _:Fin 1 => U5) (fun _ => hU5.continuous) (fun _ => Subset.rfl)
    (fun (_:Fin 1) (_:R3) => B) (fun _ _ _ => continuousAt_const)
  have hMap (n:ℕ) (y:R3):B (sphereSobolevPartialSumL (5/2:ℝ) n (U5 y)-U5 y)=
      T (sphereSobolevPartialSumL (3/2:ℝ) n (u y))-T (u y) := by
    change T (I (sphereSobolevPartialSumL (5/2:ℝ) n (U5 y)-U5 y))=_
    rw [map_sub,map_sub]
    have hInc:=sphereSobolevInclusionL_sphereSobolevPartialSumL_fiveHalf n (U5 y)
    have hValue:I (U5 y)=u y := congrFun hEq y
    exact (congrArg (fun z => T z-T (I (U5 y))) hInc).trans
      (congrArg (fun z => T (sphereSobolevPartialSumL (3/2:ℝ) n z)-T z) hValue)
  simpa only [Fin.sum_univ_one,hMap,T] using h

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
