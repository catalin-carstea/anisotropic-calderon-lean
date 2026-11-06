import Calderon.NativeHarmonicH1LiftCompletion
import Calderon.NativeHarmonicLiftTraceCompatibility

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Set
open scoped InnerProductSpace DirectSum Topology ENNReal Classical
namespace OAI.AnisotropicCalderon.NativeHarmonicH1LiftTraceCompatibility
open NativeHarmonicLiftCompletion NativeHarmonicH1LiftCompletion
  NativeHarmonicLiftTraceCompatibility SphereHarmonic SphereHilbertDecomposition
  SpectralCoreRegularity DirichletFamily EnergyBridge

theorem valueTraceL_harmonicFirstOrderFiniteL (hF : SphereFischerInner)
    (τ0 : UnitBallValueTrace) (a : HarmonicFiniteCoefficients) :
    τ0.valueTraceL (harmonicFirstOrderFiniteL hF a) =
      ∑ k ∈ a.support, (a k : SphereL2) := by
  rw [harmonicFirstOrderFiniteL_eq_polynomial,τ0.valueTrace_smooth]
  change polynomialSphereL2 (∑ k ∈ a.support, harmonicPolynomialRepresentativeL hF k (a k)) = _
  rw [map_sum]
  simp only [polynomialSphereL2_harmonicPolynomialRepresentative]

theorem sphereHarmonicCoordinate_valueTraceL_harmonicFirstOrderLiftCompletion
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (k : ℕ) (u : SphereSobolev (1/2 : ℝ)) :
    sphereHarmonicCoordinate hO hD k
      (τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF u)) =
        sphereSobolevCoefficientL (1/2 : ℝ) k u := by
  let T : SphereSobolev (1/2 : ℝ) →L[ℝ] harmonicSphereSubspace k :=
    (sphereHarmonicCoordinate hO hD k).comp
      (τ0.valueTraceL.comp (harmonicFirstOrderLiftCompletion hF))
  have he : (T : SphereSobolev (1/2 : ℝ) → harmonicSphereSubspace k) =
      sphereSobolevCoefficientL (1/2 : ℝ) k := by
    apply denseRange_harmonicHalfBoundaryFiniteL.equalizer T.continuous
      (sphereSobolevCoefficientL (1/2 : ℝ) k).continuous
    funext a
    change sphereHarmonicCoordinate hO hD k
      (τ0.valueTraceL (harmonicFirstOrderLiftCompletion hF (harmonicHalfBoundaryFiniteL a))) =
        sphereSobolevCoefficientL (1/2 : ℝ) k (harmonicHalfBoundaryFiniteL a)
    rw [harmonicFirstOrderLiftCompletion_finite hF hO,
      valueTraceL_harmonicFirstOrderFiniteL, harmonicHalfBoundaryFiniteL_eq_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl (fun j hj =>
      sphereHarmonicCoordinate_subtype_eq_sobolevSingle hO hD (1/2 : ℝ) k j (a j))
  exact congr_fun he u

theorem harmonicFirstOrderLiftCompletion_injective
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    Function.Injective (harmonicFirstOrderLiftCompletion hF) := by
  intro u v huv
  apply sphereSobolev_ext (1/2 : ℝ)
  intro k
  rw [← sphereHarmonicCoordinate_valueTraceL_harmonicFirstOrderLiftCompletion hF hO hD τ0,
    ← sphereHarmonicCoordinate_valueTraceL_harmonicFirstOrderLiftCompletion hF hO hD τ0,huv]

#print axioms valueTraceL_harmonicFirstOrderFiniteL
#print axioms sphereHarmonicCoordinate_valueTraceL_harmonicFirstOrderLiftCompletion
#print axioms harmonicFirstOrderLiftCompletion_injective
end OAI.AnisotropicCalderon.NativeHarmonicH1LiftTraceCompatibility
