import Calderon.NativeHarmonicLiftExtension
import Calderon.NativeZeroValueTrace

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Set
open scoped InnerProductSpace DirectSum Topology ENNReal Classical
namespace OAI.AnisotropicCalderon.NativeHarmonicLiftTraceCompatibility
open NativeHarmonicLiftCompletion SphereHarmonic SphereHilbertDecomposition
  SpectralCoreRegularity DirichletFamily EnergyBridge

/-! Exact same-trace compatibility and native harmonicity of the completed
Euclidean H2 lift. -/

theorem strongValueTraceL_polynomialBallSobolev (τ0 : UnitBallValueTrace)
    (p : MvPolynomial (Fin 3) ℝ) :
    strongValueTraceL τ0 0 (polynomialBallSobolev 2 p) = polynomialSphereL2 p := by
  change strongValueTraceL τ0 0 (smoothBallSobolev (0+2) (smoothPolynomialData p)) = _
  rw [strongValueTraceL_smooth]
  rfl

theorem strongValueTraceL_harmonicNativeFiniteL (hF : SphereFischerInner)
    (τ0 : UnitBallValueTrace) (a : HarmonicFiniteCoefficients) :
    strongValueTraceL τ0 0 (harmonicNativeFiniteL hF a) =
      ∑ k ∈ a.support, (a k : SphereL2) := by
  classical
  rw [harmonicNativeFiniteL_eq_polynomial, strongValueTraceL_polynomialBallSobolev, map_sum]
  simp only [polynomialSphereL2_harmonicPolynomialRepresentative]

theorem sphereHarmonicCoordinate_subtype_eq_sobolevSingle
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (k j : ℕ) (v : harmonicSphereSubspace j) :
    sphereHarmonicCoordinate hO hD k (v : SphereL2) =
      sphereSobolevCoefficientL s k (sphereSobolevSingleL s j v) := by
  by_cases hkj : k = j
  · subst j
    rw [sphereHarmonicCoordinate_subtype, sphereSobolevCoefficientL_single_self]
  · rw [sphereSobolevCoefficientL_single_ne s j k hkj,
      sphereHarmonicCoordinate_apply, sphereHarmonicDecomposition_subtype]
    exact lp.single_apply_ne (E := fun n : ℕ => ↥(harmonicSphereSubspace n)) 2 j v hkj

theorem sphereHarmonicCoordinate_strongValueTraceL_harmonicLiftCompletion
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (k : ℕ) (u : SphereSobolev (3/2 : ℝ)) :
    sphereHarmonicCoordinate hO hD k
      (strongValueTraceL τ0 0 (harmonicLiftCompletion hF u)) =
        sphereSobolevCoefficientL (3/2 : ℝ) k u := by
  let T : SphereSobolev (3/2 : ℝ) →L[ℝ] harmonicSphereSubspace k :=
    (sphereHarmonicCoordinate hO hD k).comp
      ((strongValueTraceL τ0 0).comp (harmonicLiftCompletion hF))
  have he : (T : SphereSobolev (3/2 : ℝ) → harmonicSphereSubspace k) =
      sphereSobolevCoefficientL (3/2 : ℝ) k := by
    apply denseRange_harmonicBoundaryFiniteL.equalizer T.continuous
      (sphereSobolevCoefficientL (3/2 : ℝ) k).continuous
    funext a
    change sphereHarmonicCoordinate hO hD k
      (strongValueTraceL τ0 0 (harmonicLiftCompletion hF (harmonicBoundaryFiniteL a))) =
        sphereSobolevCoefficientL (3/2 : ℝ) k (harmonicBoundaryFiniteL a)
    rw [harmonicLiftCompletion_finite hF hO,
      strongValueTraceL_harmonicNativeFiniteL, harmonicBoundaryFiniteL_eq_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl (fun j hj =>
      sphereHarmonicCoordinate_subtype_eq_sobolevSingle hO hD (3/2 : ℝ) k j (a j))
  exact congr_fun he u

theorem sphereSobolevCoefficientL_zeroEquiv_strongValueTraceL_harmonicLiftCompletion
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (k : ℕ) (u : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevCoefficientL 0 k (sphereSobolevZeroEquiv hO hD
      (strongValueTraceL τ0 0 (harmonicLiftCompletion hF u))) =
        sphereSobolevCoefficientL (3/2 : ℝ) k u := by
  rw [sphereSobolevCoefficientL_zeroEquiv]
  exact sphereHarmonicCoordinate_strongValueTraceL_harmonicLiftCompletion hF hO hD τ0 k u

/-- The actual native weak coordinate Laplacian on the Euclidean bulk graph. -/
def nativeEuclideanLaplacianL (hcalc : FixedSobolevCalculus) :
    BallSobolev 2 →L[ℝ] BallSobolev 0 :=
  ∑ i : Fin 3, (unitBallCoordinateDerivativeL hcalc 0 i).comp
    (unitBallCoordinateDerivativeL hcalc 1 i)

theorem nativeEuclideanLaplacianL_polynomialBallSobolev (hcalc : FixedSobolevCalculus)
    (p : MvPolynomial (Fin 3) ℝ) :
    nativeEuclideanLaplacianL hcalc (polynomialBallSobolev 2 p) =
      polynomialBallSobolev 0 (AngularPolynomial.laplacian p) := by
  simp only [nativeEuclideanLaplacianL, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply]
  simp_rw [unitBallCoordinateDerivativeL_polynomialBallSobolev hcalc 1,
    unitBallCoordinateDerivativeL_polynomialBallSobolev hcalc 0]
  change (∑ i : Fin 3, polynomialBallSobolevLinearMap 0 (pderiv i (pderiv i p))) =
    polynomialBallSobolevLinearMap 0 (AngularPolynomial.laplacian p)
  rw [AngularPolynomial.laplacian, map_sum]

theorem nativeEuclideanLaplacianL_harmonicNativeFiniteL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (a : HarmonicFiniteCoefficients) :
    nativeEuclideanLaplacianL hcalc (harmonicNativeFiniteL hF a) = 0 := by
  classical
  rw [harmonicNativeFiniteL_eq_polynomial]
  change nativeEuclideanLaplacianL hcalc (polynomialBallSobolevLinearMap 2
    (∑ k ∈ a.support, harmonicPolynomialRepresentativeL hF k (a k))) = 0
  rw [map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro k hk
  change nativeEuclideanLaplacianL hcalc
    (polynomialBallSobolev 2 (harmonicPolynomialRepresentativeL hF k (a k))) = 0
  rw [nativeEuclideanLaplacianL_polynomialBallSobolev,
    (harmonicPolynomialRepresentative_mem hF k (a k)).2]
  exact (polynomialBallSobolevLinearMap 0).map_zero

theorem nativeEuclideanLaplacianL_harmonicLiftCompletion
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (u : SphereSobolev (3/2 : ℝ)) :
    nativeEuclideanLaplacianL hcalc (harmonicLiftCompletion hF u) = 0 := by
  let T : SphereSobolev (3/2 : ℝ) →L[ℝ] BallSobolev 0 :=
    (nativeEuclideanLaplacianL hcalc).comp (harmonicLiftCompletion hF)
  have he : (T : SphereSobolev (3/2 : ℝ) → BallSobolev 0) = (fun _ => 0) := by
    apply denseRange_harmonicBoundaryFiniteL.equalizer T.continuous continuous_const
    funext a
    change nativeEuclideanLaplacianL hcalc
      (harmonicLiftCompletion hF (harmonicBoundaryFiniteL a)) = 0
    rw [harmonicLiftCompletion_finite hF hO]
    exact nativeEuclideanLaplacianL_harmonicNativeFiniteL hcalc hF a
  exact congr_fun he u

end OAI.AnisotropicCalderon.NativeHarmonicLiftTraceCompatibility

#print axioms OAI.AnisotropicCalderon.NativeHarmonicLiftTraceCompatibility.strongValueTraceL_polynomialBallSobolev
#print axioms OAI.AnisotropicCalderon.NativeHarmonicLiftTraceCompatibility.strongValueTraceL_harmonicNativeFiniteL
#print axioms OAI.AnisotropicCalderon.NativeHarmonicLiftTraceCompatibility.sphereHarmonicCoordinate_subtype_eq_sobolevSingle
#print axioms OAI.AnisotropicCalderon.NativeHarmonicLiftTraceCompatibility.sphereHarmonicCoordinate_strongValueTraceL_harmonicLiftCompletion
#print axioms OAI.AnisotropicCalderon.NativeHarmonicLiftTraceCompatibility.sphereSobolevCoefficientL_zeroEquiv_strongValueTraceL_harmonicLiftCompletion
#print axioms OAI.AnisotropicCalderon.NativeHarmonicLiftTraceCompatibility.nativeEuclideanLaplacianL
#print axioms OAI.AnisotropicCalderon.NativeHarmonicLiftTraceCompatibility.nativeEuclideanLaplacianL_polynomialBallSobolev
#print axioms OAI.AnisotropicCalderon.NativeHarmonicLiftTraceCompatibility.nativeEuclideanLaplacianL_harmonicNativeFiniteL
#print axioms OAI.AnisotropicCalderon.NativeHarmonicLiftTraceCompatibility.nativeEuclideanLaplacianL_harmonicLiftCompletion
