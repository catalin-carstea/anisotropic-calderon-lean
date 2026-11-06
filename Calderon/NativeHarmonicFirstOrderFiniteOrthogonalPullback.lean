import Calderon.NativeHarmonicH1LiftCompletion
import Calderon.SphereSobolevOrthogonalPullback
import Calderon.NativeH1OrthogonalPullback

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped DirectSum ENNReal
namespace OAI.AnisotropicCalderon.NativeHarmonicH1LiftCompletion
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap NativeHarmonicLiftCompletion
  NativePolynomialBulkMoments SphereHarmonic GreenRadialTrace SmoothAngularCasimir

/-! Agreement is proved on the actual harmonic polynomial singles. -/

lemma harmonicPolynomialRepresentativeL_orthogonalPullback (hF : SphereFischerInner)
    (e : R3 ≃ₗᵢ[ℝ] R3) (k : ℕ) (u : harmonicSphereSubspace k) :
    harmonicPolynomialRepresentativeL hF k (harmonicSphereOrthogonalPullback e k u) =
      polynomialOrthogonalPullback e (harmonicPolynomialRepresentativeL hF k u) := by
  apply (polynomialSphereL2_injective_degree hF k _ _
    (harmonicPolynomialRepresentative_mem hF k _)
    (polynomialOrthogonalPullback_harmonicHomogeneous e k _ (harmonicPolynomialRepresentative_mem hF k u))).mp
  rw [polynomialSphereL2_harmonicPolynomialRepresentative]
  change sphereL2OrthogonalPullback e u.val = _
  have h := sphereL2OrthogonalPullback_polynomialSphereL2 e (harmonicPolynomialRepresentativeL hF k u)
  rw [polynomialSphereL2_harmonicPolynomialRepresentative] at h
  exact h

lemma orthogonalSmoothPullback_smoothPolynomialData (e : R3 ≃ₗᵢ[ℝ] R3)
    (p : MvPolynomial (Fin 3) ℝ) :
    orthogonalSmoothPullback e (smoothPolynomialData p) =
      smoothPolynomialData (polynomialOrthogonalPullback e p) := by
  apply Subtype.ext
  funext x
  exact (congrFun (polynomialEvaluation_orthogonalPullback e p) x).symm

lemma harmonicFirstOrderLiftCompletion_single (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (k : ℕ) (u : harmonicSphereSubspace k) :
    harmonicFirstOrderLiftCompletion hF (sphereSobolevSingleL (1/2 : ℝ) k u) =
      smoothSobolev (smoothPolynomialData (harmonicPolynomialRepresentativeL hF k u)) := by
  let a : HarmonicFiniteCoefficients := DirectSum.lof ℝ ℕ (fun k => ↥(harmonicSphereSubspace k)) k u
  have hBoundary : harmonicHalfBoundaryFiniteL a = sphereSobolevSingleL (1/2 : ℝ) k u :=
    DirectSum.toModule_lof (R := ℝ) (φ := fun j => (sphereSobolevSingleL (1/2 : ℝ) j).toLinearMap) k u
  rw [← hBoundary,harmonicFirstOrderLiftCompletion_finite hF hO]
  unfold harmonicFirstOrderFiniteL
  rw [DirectSum.toModule_lof]
  exact firstOrder_smoothBallSobolev 0 (smoothPolynomialData (harmonicPolynomialRepresentativeL hF k u))

lemma harmonicFirstOrderLiftCompletion_single_orthogonalPullback (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (e : R3 ≃ₗᵢ[ℝ] R3) (k : ℕ) (u : harmonicSphereSubspace k) :
    nativeH1OrthogonalPullback e
      (harmonicFirstOrderLiftCompletion hF (sphereSobolevSingleL (1/2 : ℝ) k u)) =
    harmonicFirstOrderLiftCompletion hF
      (sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e (sphereSobolevSingleL (1/2 : ℝ) k u)) := by
  rw [harmonicFirstOrderLiftCompletion_single hF hO,sphereSobolevOrthogonalPullbackL_single,
    harmonicFirstOrderLiftCompletion_single hF hO,nativeH1OrthogonalPullback_smoothSobolev,
    orthogonalSmoothPullback_smoothPolynomialData,harmonicPolynomialRepresentativeL_orthogonalPullback]

end OAI.AnisotropicCalderon.NativeHarmonicH1LiftCompletion

#print axioms OAI.AnisotropicCalderon.NativeHarmonicH1LiftCompletion.harmonicPolynomialRepresentativeL_orthogonalPullback
#print axioms OAI.AnisotropicCalderon.NativeHarmonicH1LiftCompletion.orthogonalSmoothPullback_smoothPolynomialData
#print axioms OAI.AnisotropicCalderon.NativeHarmonicH1LiftCompletion.harmonicFirstOrderLiftCompletion_single
#print axioms OAI.AnisotropicCalderon.NativeHarmonicH1LiftCompletion.harmonicFirstOrderLiftCompletion_single_orthogonalPullback
