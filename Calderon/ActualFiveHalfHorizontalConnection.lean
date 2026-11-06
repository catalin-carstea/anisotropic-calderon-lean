import Calderon.ActualHorizontalSobolevConnection
import Calderon.NativeFiveHalfRotationAdjointCompatibility
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ConformalDepth RadiusProfile ReferenceDensityBounds AmbientReferenceCovariantCore
  NormalCoordinatesFrame MetricOperator AngularPolynomial
attribute [local irreducible] referenceFrameConnectionCoefficient referenceMetricGramFrame
  sphereSobolevRotationL referenceHighHorizontalAngularL referenceHighHorizontalAction

lemma sphereSobolevRotationL_fivehalf_threehalf_compatibility (i j : Fin 3) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (sphereSobolevRotationL (5/2:ℝ) i j) =
    (sphereSobolevRotationL (3/2:ℝ) i j).comp
      (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)) := by
  have h := sphereSobolevRotationL_inclusion_comm (5/2:ℝ) (3/2:ℝ) (by norm_num) i j
  have hNorm := congrArg
    (fun I : SphereSobolev ((5/2:ℝ)-1) →L[ℝ] SphereSobolev ((3/2:ℝ)-1) =>
      I.comp (sphereSobolevRotationL (5/2:ℝ) i j))
    sphereSobolevInclusionL_fivehalf_rotation_orders
  exact hNorm.symm.trans h

def referenceFiveHalfHorizontalAngularL (g : MatrixField) (L q : ℝ) (y : R3) (i : Fin 3) :
    SphereSobolev (5/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  (1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3,
    referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) a b •
      sphereSobolevRotationL (5/2 : ℝ) a b

theorem referenceHorizontalAngularL_fivehalf_threehalf_compatibility
    (g : MatrixField) (L q : ℝ) (y : R3) (i : Fin 3) :
    (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).comp
      (referenceFiveHalfHorizontalAngularL g L q y i) =
    (referenceHighHorizontalAngularL g L q y i).comp
      (sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [referenceFiveHalfHorizontalAngularL,referenceHighHorizontalAngularL,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply,map_smul,map_sum]
  apply congrArg (fun z : SphereSobolev (1/2 : ℝ) => (1/2 : ℝ) • z)
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact congrArg (fun z : SphereSobolev (1/2 : ℝ) =>
    referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) a b • z)
    (congrArg (fun A : SphereSobolev (5/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A u)
      (sphereSobolevRotationL_fivehalf_threehalf_compatibility a b))

theorem contDiff_referenceFiveHalfHorizontalAngularL
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun y => referenceFiveHalfHorizontalAngularL g L q y i) := by
  unfold referenceFiveHalfHorizontalAngularL
  apply ContDiff.const_smul
  apply ContDiff.sum
  intro a ha
  apply ContDiff.sum
  intro b hb
  exact (contDiff_referenceFrameConnectionCoefficient_field g hg L q
    (fun y => referenceMetricGramFrame g L (q,y) i)
    (contDiff_referenceMetricGramFrame_slice g hg L q i) a b).smul contDiff_const

def referenceFiveHalfHorizontalAction (g : MatrixField) (L q : ℝ)
    (u : R3 → SphereSobolev (5/2 : ℝ)) (y : R3) (i : Fin 3) : SphereSobolev (3/2 : ℝ) :=
  sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)
    (fderiv ℝ u y (referenceMetricGramFrame g L (q,y) i)) +
      referenceFiveHalfHorizontalAngularL g L q y i (u y)

theorem referenceHorizontalAction_fivehalf_threehalf_compatibility
    (g : MatrixField) (L q : ℝ) (u : R3 → SphereSobolev (5/2 : ℝ))
    (y : R3) (i : Fin 3) (hu : DifferentiableAt ℝ u y) :
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      (referenceFiveHalfHorizontalAction g L q u y i) =
    referenceHighHorizontalAction g L q
      (fun x => sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num) (u x)) y i := by
  let Iin := sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  have hDerivative := (Iin.hasFDerivAt.comp y hu.hasFDerivAt).fderiv
  have hBase := congrArg (fun A : R3 →L[ℝ] SphereSobolev (3/2 : ℝ) =>
    Iout (A (referenceMetricGramFrame g L (q,y) i))) hDerivative
  have hAngular := congrArg
    (fun A : SphereSobolev (5/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A (u y))
    (referenceHorizontalAngularL_fivehalf_threehalf_compatibility g L q y i)
  have hCombined := congrArg₂ (fun a b : SphereSobolev (1/2 : ℝ) => a+b)
    hBase.symm hAngular
  simpa only [referenceFiveHalfHorizontalAction,referenceHighHorizontalAction,
    ContinuousLinearMap.comp_apply,Function.comp_def,map_add,Iin,Iout] using hCombined

theorem contDiffAt_referenceFiveHalfHorizontalAction
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ)
    (u : R3 → SphereSobolev (5/2 : ℝ)) (y : R3) (i : Fin 3)
    (hu : ContDiffAt ℝ ∞ u y) :
    ContDiffAt ℝ ∞ (fun x => referenceFiveHalfHorizontalAction g L q u x i) y := by
  have hDerivative := (hu.fderiv_right (m := ∞) (by simp)).clm_apply
    (contDiff_referenceMetricGramFrame_slice g hg L q i).contDiffAt
  have hBase := (sphereSobolevInclusionL (5/2 : ℝ) (3/2 : ℝ) (by norm_num)).contDiff.contDiffAt.comp
    y hDerivative
  have hAngular := (contDiff_referenceFiveHalfHorizontalAngularL g hg L q i).contDiffAt.clm_apply hu
  exact hBase.add hAngular

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
