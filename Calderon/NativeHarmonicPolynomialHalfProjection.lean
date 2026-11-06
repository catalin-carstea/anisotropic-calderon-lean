import Calderon.NativeHarmonicFirstOrderFiniteOrthogonalPullback
import Calderon.NativeHalfTraceRightInverse
import Calderon.NativeRadialFactorZeroClosure

/-! Expanded before source in EXPANSION-native-coordinate-harmonic-defect-author-v001.json. -/
set_option autoImplicit false
noncomputable section
open MvPolynomial MeasureTheory
open scoped ENNReal ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeHarmonicLiftCompletion NativeHarmonicH1LiftCompletion
  NativeHalfTraceRightInverse NativeFullSharpHalfTrace AngularPolynomial

def nativePolynomialFirstOrderL : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] BallH1 :=
  (TauCeti.Wkp.firstOrderL (mu := (volume : Measure R3)) (Omega := ballOpens)
    (p := 2) 0).toLinearMap.comp (polynomialBallSobolevLinearMap 1)

lemma nativePolynomialFirstOrderL_apply (p : MvPolynomial (Fin 3) ℝ) :
    nativePolynomialFirstOrderL p = smoothSobolev (smoothPolynomialData p) :=
  firstOrder_smoothBallSobolev 0 (smoothPolynomialData p)

open SmoothSphereRotationProjection

lemma harmonicFirstOrderLiftCompletion_single_polynomial
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (k : ℕ) (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) :
    harmonicFirstOrderLiftCompletion hF
      (sphereSobolevSingleL (1/2:ℝ) k (harmonicPolynomialSphereMap k ⟨p,hp⟩)) =
    nativePolynomialFirstOrderL p := by
  have hrep : harmonicPolynomialRepresentativeL hF k
      (harmonicPolynomialSphereMap k ⟨p,hp⟩) = p :=
    congrArg Subtype.val ((harmonicPolynomialEquiv hF k).symm_apply_apply ⟨p,hp⟩)
  rw [harmonicFirstOrderLiftCompletion_single hF hO,hrep,nativePolynomialFirstOrderL_apply]

lemma harmonicHalfProjection_nativePolynomial
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (k : ℕ) (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k) :
    harmonicFirstOrderLiftCompletion hF
      (nativeHalfTraceL hF hO hD τ0 (nativePolynomialFirstOrderL p)) =
    nativePolynomialFirstOrderL p := by
  let f := sphereSobolevSingleL (1/2:ℝ) k (harmonicPolynomialSphereMap k ⟨p,hp⟩)
  have hf : harmonicFirstOrderLiftCompletion hF f = nativePolynomialFirstOrderL p :=
    harmonicFirstOrderLiftCompletion_single_polynomial hF hO k p hp
  have h := congrArg (harmonicFirstOrderLiftCompletion hF)
    (nativeHalfTraceL_harmonicFirstOrderLiftCompletion hF hO hD τ0 f)
  rw [hf] at h
  exact h

lemma nativePolynomialFirstOrderL_radialFactor_mem_zero (q : MvPolynomial (Fin 3) ℝ) :
    nativePolynomialFirstOrderL ((1-radiusSq)*q) ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  have hdata : smoothPolynomialData ((1-radiusSq)*q) =
      (⟨fun x : R3 => (1-‖x‖^2)*(smoothPolynomialData q).1 x,
        (contDiff_const.sub (contDiff_norm_sq ℝ)).mul (smoothPolynomialData q).2⟩ : SmoothData) := by
    apply Subtype.ext
    funext x
    have hr : eval (polynomialCoordinateMap x) (radiusSq : MvPolynomial (Fin 3) ℝ) = ‖x‖^2 := by
      simp only [radiusSq,map_sum,map_pow,eval_X]
      exact (EuclideanSpace.real_norm_sq_eq x).symm
    change eval (polynomialCoordinateMap x) ((1-radiusSq)*q) =
      (1-‖x‖^2)*eval (polynomialCoordinateMap x) q
    rw [map_mul,map_sub,map_one,hr]
  rw [nativePolynomialFirstOrderL_apply,hdata]
  exact smoothSobolev_radialFactor_mem_zero (smoothPolynomialData q)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativePolynomialFirstOrderL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativePolynomialFirstOrderL_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.harmonicFirstOrderLiftCompletion_single_polynomial
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.harmonicHalfProjection_nativePolynomial
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativePolynomialFirstOrderL_radialFactor_mem_zero
