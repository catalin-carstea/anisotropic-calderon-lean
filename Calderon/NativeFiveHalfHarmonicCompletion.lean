import Calderon.NativeFiveHalfHarmonicFiniteCore

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace DirectSum Topology ENNReal Classical
namespace OAI.AnisotropicCalderon.NativeFiveHalfHarmonicLift
open NativePolynomialBulkMoments NativeHarmonicLiftCompletion
  SphereHarmonic DirichletFamily DenseRealLinearExtension

private def ofRealLinearFunction {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F)
    (ha : ∀ a b, f (a+b) = f a + f b) (hs : ∀ (c : ℝ) a, f (c • a) = c • f a) : E →ₗ[ℝ] F where
  toFun := f
  map_add' := ha
  map_smul' := hs

private def completeRealLinearMap {E G F : Type*} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E →ₗ[ℝ] F) (e : E →ₗ[ℝ] G) : G →L[ℝ] F :=
  f.extendOfNorm e

private lemma completeRealLinearMap_finite {E G F : Type*} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E →ₗ[ℝ] F) (e : E →ₗ[ℝ] G) (hd : DenseRange e)
    (C : ℝ) (hb : ∀ a, ‖f a‖ ≤ C*‖e a‖) (a : E) :
    completeRealLinearMap f e (e a) = f a := by
  exact LinearMap.extendOfNorm_eq hd ⟨C,hb⟩ a

private lemma norm_completeRealLinearMap_le {E G F : Type*} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E →ₗ[ℝ] F) (e : E →ₗ[ℝ] G) (hd : DenseRange e)
    (C : ℝ) (hb : ∀ a, ‖f a‖ ≤ C*‖e a‖) (u : G) :
    ‖completeRealLinearMap f e u‖ ≤ C*‖u‖ := by
  exact LinearMap.norm_extendOfNorm_apply_le hd C hb u

def normalizedBoundaryFiniteL :=
  ofRealLinearFunction (fun a : HarmonicFiniteCoefficients => harmonicBoundaryFiniteL a)
    (fun a b => harmonicBoundaryFiniteL.map_add a b)
    (fun c a => harmonicBoundaryFiniteL.map_smul c a)

def normalizedNativeFiniteL (hF : SphereFischerInner) :=
  ofRealLinearFunction (fun a : HarmonicFiniteCoefficients => harmonicNativeFiniteL hF a)
    (fun a b => (harmonicNativeFiniteL hF).map_add a b)
    (fun c a => (harmonicNativeFiniteL hF).map_smul c a)

lemma normalizedBoundaryFiniteL_apply (a : HarmonicFiniteCoefficients) :
    normalizedBoundaryFiniteL a = harmonicBoundaryFiniteL a := rfl
lemma normalizedNativeFiniteL_apply (hF : SphereFischerInner) (a : HarmonicFiniteCoefficients) :
    normalizedNativeFiniteL hF a = harmonicNativeFiniteL hF a := rfl

attribute [local irreducible] normalizedNativeFiniteL normalizedBoundaryFiniteL

lemma denseRange_normalizedBoundaryFiniteL : DenseRange normalizedBoundaryFiniteL := by
  have he : (normalizedBoundaryFiniteL : HarmonicFiniteCoefficients → SphereSobolev (5/2:ℝ)) =
      harmonicBoundaryFiniteL := funext normalizedBoundaryFiniteL_apply
  rw [he]
  exact denseRange_harmonicBoundaryFiniteL

lemma norm_normalizedNativeFiniteL_le (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (a : HarmonicFiniteCoefficients) :
    ‖normalizedNativeFiniteL hF a‖ ≤ Real.sqrt (64*sphereSurfaceMass)*‖normalizedBoundaryFiniteL a‖ := by
  rw [normalizedNativeFiniteL_apply,normalizedBoundaryFiniteL_apply]
  exact norm_harmonicNativeFiniteL_le hF hO a

def harmonicLiftCompletion (hF : SphereFischerInner) :
    SphereSobolev (5/2:ℝ) →L[ℝ] BallSobolev 3 :=
  completeRealLinearMap (E := HarmonicFiniteCoefficients)
    (G := SphereSobolev (5/2:ℝ)) (F := BallSobolev 3)
    (normalizedNativeFiniteL hF) normalizedBoundaryFiniteL

lemma harmonicLiftCompletion_finite (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (a : HarmonicFiniteCoefficients) :
    harmonicLiftCompletion hF (harmonicBoundaryFiniteL a) = harmonicNativeFiniteL hF a := by
  have hSpecial := completeRealLinearMap_finite (E := HarmonicFiniteCoefficients)
    (G := SphereSobolev (5/2:ℝ)) (F := BallSobolev 3)
    (normalizedNativeFiniteL hF) normalizedBoundaryFiniteL
  have h := hSpecial denseRange_normalizedBoundaryFiniteL
    (Real.sqrt (64*sphereSurfaceMass)) (norm_normalizedNativeFiniteL_le hF hO) a
  rw [normalizedBoundaryFiniteL_apply,normalizedNativeFiniteL_apply] at h
  exact h

lemma norm_harmonicLiftCompletion_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (u : SphereSobolev (5/2:ℝ)) :
    ‖harmonicLiftCompletion hF u‖ ≤ Real.sqrt (64*sphereSurfaceMass)*‖u‖ := by
  have hSpecial := norm_completeRealLinearMap_le (E := HarmonicFiniteCoefficients)
    (G := SphereSobolev (5/2:ℝ)) (F := BallSobolev 3)
    (normalizedNativeFiniteL hF) normalizedBoundaryFiniteL
  exact hSpecial denseRange_normalizedBoundaryFiniteL
    (Real.sqrt (64*sphereSurfaceMass)) (norm_normalizedNativeFiniteL_le hF hO) u

end OAI.AnisotropicCalderon.NativeFiveHalfHarmonicLift
