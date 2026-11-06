import Calderon.PositiveCoefficientAffineAllOrderRegularity
import Calderon.NativeFullSharpHalfTrace

/-! EXPANSION.json precedes this exact actual native boundary trace identity. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeFullSharpHalfTrace NativeSmoothSharpTraceCompletion

theorem nativeHalfTraceL_positiveCoefficientDirichletSolution
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (hPos : ∀ x, (A x).PosDef) (f : SmoothData) :
    nativeHalfTraceL hF hO hD τ0 (positiveCoefficientDirichletSolution A hA hPos f) =
      smoothHalfTrace hF hO hD τ0 f := by
  let c : BallH1Zero := positiveCoefficientDirichletCorrection A hA hPos f
  have hAffine : positiveCoefficientDirichletSolution A hA hPos f =
      smoothSobolev f + (c : BallH1) := rfl
  rw [hAffine,map_add,nativeHalfTraceL_smoothSobolev,
    nativeHalfTraceL_zeroDirichlet hF hO hD τ0 c,add_zero]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeHalfTraceL_positiveCoefficientDirichletSolution
