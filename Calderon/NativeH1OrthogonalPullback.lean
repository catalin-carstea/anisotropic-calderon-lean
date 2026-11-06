import Calderon.NativeSmoothH1OrthogonalPullback

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal Gradient Distributions
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

def nativeH1OrthogonalPullback (e : R3 ≃ₗᵢ[ℝ] R3) : BallH1 →ₗᵢ[ℝ] BallH1 :=
  (nativeSmoothSobolevLinear.comp (nativeSmoothOrthogonalPullbackLinear e)).extendOfIsometry
    denseRange_nativeSmoothSobolevLinear (norm_nativeSmoothOrthogonalPullbackLinear e)

lemma nativeH1OrthogonalPullback_smoothLinear (e : R3 ≃ₗᵢ[ℝ] R3)
    (f : nativeSmoothFunctionSpace) :
    nativeH1OrthogonalPullback e (nativeSmoothSobolevLinear f) =
      nativeSmoothSobolevLinear (nativeSmoothOrthogonalPullbackLinear e f) :=
  LinearMap.extendOfIsometry_eq _ _ _ f

lemma nativeH1OrthogonalPullback_smoothSobolev (e : R3 ≃ₗᵢ[ℝ] R3) (f : SmoothData) :
    nativeH1OrthogonalPullback e (smoothSobolev f) =
      smoothSobolev (orthogonalSmoothPullback e f) :=
  nativeH1OrthogonalPullback_smoothLinear e ⟨f.1,f.2⟩

lemma nativeH1OrthogonalPullback_symm_apply (e : R3 ≃ₗᵢ[ℝ] R3) (u : BallH1) :
    nativeH1OrthogonalPullback e.symm (nativeH1OrthogonalPullback e u) = u := by
  refine denseRange_nativeSmoothSobolevLinear.induction_on u
    (isClosed_eq ((nativeH1OrthogonalPullback e.symm).continuous.comp
      (nativeH1OrthogonalPullback e).continuous) continuous_id) ?_
  intro f
  rw [nativeH1OrthogonalPullback_smoothLinear,nativeH1OrthogonalPullback_smoothLinear]
  apply congrArg nativeSmoothSobolevLinear
  apply Subtype.ext
  funext x
  exact congrArg f.1 (e.apply_symm_apply x)

def nativeH1OrthogonalPullbackEquiv (e : R3 ≃ₗᵢ[ℝ] R3) : BallH1 ≃ₗᵢ[ℝ] BallH1 where
  toLinearEquiv :=
    { (nativeH1OrthogonalPullback e).toLinearMap with
      invFun := nativeH1OrthogonalPullback e.symm
      left_inv := nativeH1OrthogonalPullback_symm_apply e
      right_inv := by
        intro u
        change nativeH1OrthogonalPullback e (nativeH1OrthogonalPullback e.symm u) = u
        simpa only [LinearIsometryEquiv.symm_symm] using
          nativeH1OrthogonalPullback_symm_apply e.symm u }
  norm_map' := (nativeH1OrthogonalPullback e).norm_map

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1OrthogonalPullback
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1OrthogonalPullback_smoothLinear
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1OrthogonalPullback_smoothSobolev
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1OrthogonalPullback_symm_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1OrthogonalPullbackEquiv
