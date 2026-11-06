import Calderon.NativeHarmonicH1LiftTraceCompatibility
import Calderon.NativeFullSharpHalfTrace

/-! EXPANSION.json precedes this ordinary smooth-boundary density specialization.
No actual variable-coefficient harmonic density is inferred here. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory MvPolynomial
open scoped ENNReal InnerProductSpace Classical
namespace OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
open EnergyBridge DirichletFamily SphereHarmonic SpectralWeightedGraph
  NativeHarmonicLiftCompletion NativeHarmonicH1LiftCompletion NativeHarmonicH1LiftTraceCompatibility

theorem smoothHalfTrace_finite_harmonic_polynomial
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (a : HarmonicFiniteCoefficients) :
    smoothHalfTrace hF hO hD τ0 (smoothPolynomialData
      (∑ k ∈ a.support, harmonicPolynomialRepresentativeL hF k (a k))) =
      harmonicHalfBoundaryFiniteL a := by
  apply sphereSobolev_ext (1/2 : ℝ)
  intro k
  rw [sphereSobolevCoefficientL_smoothHalfTrace]
  have h := sphereHarmonicCoordinate_valueTraceL_harmonicFirstOrderLiftCompletion
    hF hO hD τ0 k (harmonicHalfBoundaryFiniteL a)
  rw [harmonicFirstOrderLiftCompletion_finite hF hO,harmonicFirstOrderFiniteL_eq_polynomial] at h
  exact h

theorem denseRange_smoothHalfTrace
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    DenseRange (smoothHalfTrace hF hO hD τ0) := by
  intro u
  apply closure_mono (s := range harmonicHalfBoundaryFiniteL)
    (t := range (smoothHalfTrace hF hO hD τ0)) ?_ (denseRange_harmonicHalfBoundaryFiniteL u)
  rintro _ ⟨a,rfl⟩
  exact ⟨smoothPolynomialData (∑ k ∈ a.support, harmonicPolynomialRepresentativeL hF k (a k)),
    smoothHalfTrace_finite_harmonic_polynomial hF hO hD τ0 a⟩

end OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion
#print axioms OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion.smoothHalfTrace_finite_harmonic_polynomial
#print axioms OAI.AnisotropicCalderon.NativeSmoothSharpTraceCompletion.denseRange_smoothHalfTrace
