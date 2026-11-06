import Calderon.NativeHarmonicFirstOrderFiniteOrthogonalPullback

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped DirectSum ENNReal
namespace OAI.AnisotropicCalderon.NativeHarmonicH1LiftCompletion
open EnergyBridge SphereHarmonic DirichletFamily.DriftBootstrap

/-! Expanded before source in EXPANSION-native-first-order-harmonic-orthogonal-lift-v001.json.
Only actual finite-coefficient density is used; no H2 smooth density. -/

lemma harmonicFirstOrderLiftCompletion_orthogonalPullback (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (e : R3 ≃ₗᵢ[ℝ] R3) (u : SphereSobolev (1/2 : ℝ)) :
    nativeH1OrthogonalPullback e (harmonicFirstOrderLiftCompletion hF u) =
      harmonicFirstOrderLiftCompletion hF (sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e u) := by
  let A : SphereSobolev (1/2 : ℝ) →L[ℝ] BallH1 :=
    (nativeH1OrthogonalPullback e).toContinuousLinearMap.comp (harmonicFirstOrderLiftCompletion hF)
  let B : SphereSobolev (1/2 : ℝ) →L[ℝ] BallH1 :=
    (harmonicFirstOrderLiftCompletion hF).comp (sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e)
  have hEq : (A : SphereSobolev (1/2 : ℝ) → BallH1) = B := by
    apply denseRange_harmonicHalfBoundaryFiniteL.equalizer A.continuous B.continuous
    funext a
    change nativeH1OrthogonalPullback e (harmonicFirstOrderLiftCompletion hF (harmonicHalfBoundaryFiniteL a)) =
      harmonicFirstOrderLiftCompletion hF (sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e (harmonicHalfBoundaryFiniteL a))
    rw [harmonicHalfBoundaryFiniteL_eq_sum]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact harmonicFirstOrderLiftCompletion_single_orthogonalPullback hF hO e k (a k)
  exact congr_fun hEq u

lemma harmonicFirstOrderLiftCompletion_comp_orthogonalPullback (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (e : R3 ≃ₗᵢ[ℝ] R3) :
    (nativeH1OrthogonalPullback e).toContinuousLinearMap.comp (harmonicFirstOrderLiftCompletion hF) =
      (harmonicFirstOrderLiftCompletion hF).comp (sphereSobolevOrthogonalPullbackL (1/2 : ℝ) e) := by
  apply ContinuousLinearMap.ext
  intro u
  exact harmonicFirstOrderLiftCompletion_orthogonalPullback hF hO e u

end OAI.AnisotropicCalderon.NativeHarmonicH1LiftCompletion

#print axioms OAI.AnisotropicCalderon.NativeHarmonicH1LiftCompletion.harmonicFirstOrderLiftCompletion_orthogonalPullback
#print axioms OAI.AnisotropicCalderon.NativeHarmonicH1LiftCompletion.harmonicFirstOrderLiftCompletion_comp_orthogonalPullback
