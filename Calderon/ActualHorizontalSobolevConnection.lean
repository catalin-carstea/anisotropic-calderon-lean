import Calderon.SphereSobolevTangentialEndpointCompatibility
import Calderon.ActualConformalGramAngularVelocity
import Calderon.ActualHorizontalGraph

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/EXPANSION.md.
Actual reference connection on the compatible high/half/negative endpoints. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection
  ConformalDepth RadiusProfile ReferenceDensityBounds AmbientReferenceCovariantCore
  NormalCoordinatesFrame MetricOperator AngularPolynomial

theorem conformalReferenceMatrix_eq_referenceMetric (g : MatrixField) (L q : ℝ) :
    conformalReferenceMatrix g L q = referenceMetric (dilatedMetric g q) L := by
  funext y
  change Real.exp (-2*L*conformalReferenceCoordinateDepth y) • g (q • y) =
    Real.exp (2*(-L*referenceCoordinateDepth y)) • g (q • y)
  have h : -2*L*conformalReferenceCoordinateDepth y = 2*(-L*referenceCoordinateDepth y) := by
    unfold conformalReferenceCoordinateDepth referenceCoordinateDepth
    ring
  exact congrArg (fun c : ℝ => Real.exp c • g (q • y)) h

theorem conformalReferenceGramFrame_eq_referenceMetricGramFrame
    (g : MatrixField) (L q : ℝ) (y : R3) (i : Fin 3) :
    conformalReferenceGramFrame g L (q,y) i = referenceMetricGramFrame g L (q,y) i := by
  change NormalCoordinatesFrame.metricGramFrame
      (metricOperatorField (conformalReferenceMatrix g L q) y) i =
    SmoothMetricFrame.metricGramFrame
      (metricOperatorField (referenceMetric (dilatedMetric g q) L) y) i
  rw [conformalReferenceMatrix_eq_referenceMetric]
  simp only [NormalCoordinatesFrame.metricGramFrame, SmoothMetricFrame.metricGramFrame,
    NormalCoordinatesFrame.metricNormalize, SmoothMetricFrame.metricNormalize,
    NormalCoordinatesFrame.gramThird, SmoothMetricFrame.gramThird,
    NormalCoordinatesFrame.gramSecond, SmoothMetricFrame.gramSecond,
    NormalCoordinatesFrame.metricPair, SmoothMetricFrame.metricPair,
    NormalCoordinatesFrame.coordinateVector, MetricVolume.coordinateVector]

theorem conformalReferenceFrameConnectionCoefficient_eq_referenceFrameConnectionCoefficient
    (g : MatrixField) (L q : ℝ) (y X : R3) :
    conformalReferenceFrameConnectionCoefficient g L q y X =
    referenceFrameConnectionCoefficient g L q y X := by
  have hFrame : (fun x : R3 => conformalReferenceGramFrame g L (q,x)) =
      (fun x : R3 => referenceMetricGramFrame g L (q,x)) := by
    funext x i
    exact conformalReferenceGramFrame_eq_referenceMetricGramFrame g L q x i
  unfold conformalReferenceFrameConnectionCoefficient referenceFrameConnectionCoefficient
  simp only [conformalReferenceMatrix_eq_referenceMetric,hFrame,referenceConnectionFamily,
    inverseMetricOperator]

attribute [local irreducible] referenceFrameConnectionCoefficient referenceMetricGramFrame
  sphereSobolevRotationL

def referenceHighHorizontalAngularL (g : MatrixField) (L q : ℝ) (y : R3) (i : Fin 3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  (1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3,
    referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) a b •
      sphereSobolevRotationL (3/2 : ℝ) a b

def referenceLowerHorizontalAngularL (g : MatrixField) (L q : ℝ) (y : R3) (i : Fin 3) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  (1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3,
    referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) a b •
      sphereSobolevRotationL (1/2 : ℝ) a b

theorem referenceHorizontalAngularL_high_lower_compatibility
    (g : MatrixField) (L q : ℝ) (y : R3) (i : Fin 3) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (referenceHighHorizontalAngularL g L q y i) =
    (referenceLowerHorizontalAngularL g L q y i).comp
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [referenceHighHorizontalAngularL,referenceLowerHorizontalAngularL,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply,map_smul,map_sum]
  apply congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => (1/2 : ℝ) • z)
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) =>
    referenceFrameConnectionCoefficient g L q y (referenceMetricGramFrame g L (q,y) i) a b • z)
    (congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A u)
      (sphereSobolevRotationL_threehalf_half_compatibility a b))

theorem contDiff_referenceHighHorizontalAngularL
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun y => referenceHighHorizontalAngularL g L q y i) := by
  unfold referenceHighHorizontalAngularL
  apply ContDiff.const_smul
  apply ContDiff.sum
  intro a ha
  apply ContDiff.sum
  intro b hb
  exact (contDiff_referenceFrameConnectionCoefficient_field g hg L q
    (fun y => referenceMetricGramFrame g L (q,y) i)
    (contDiff_referenceMetricGramFrame_slice g hg L q i) a b).smul contDiff_const

theorem contDiff_referenceLowerHorizontalAngularL
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun y => referenceLowerHorizontalAngularL g L q y i) := by
  unfold referenceLowerHorizontalAngularL
  apply ContDiff.const_smul
  apply ContDiff.sum
  intro a ha
  apply ContDiff.sum
  intro b hb
  exact (contDiff_referenceFrameConnectionCoefficient_field g hg L q
    (fun y => referenceMetricGramFrame g L (q,y) i)
    (contDiff_referenceMetricGramFrame_slice g hg L q i) a b).smul contDiff_const

def referenceHighHorizontalAction (g : MatrixField) (L q : ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i : Fin 3) : SphereSobolev (1/2 : ℝ) :=
  sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
    (fderiv ℝ u y (referenceMetricGramFrame g L (q,y) i)) +
      referenceHighHorizontalAngularL g L q y i (u y)

def referenceLowerHorizontalAction (g : MatrixField) (L q : ℝ)
    (v : R3 → SphereSobolev (1/2 : ℝ)) (y : R3) (i : Fin 3) : SphereSobolev (-(1/2 : ℝ)) :=
  sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
    (fderiv ℝ v y (referenceMetricGramFrame g L (q,y) i)) +
      referenceLowerHorizontalAngularL g L q y i (v y)

theorem referenceHorizontalAction_high_lower_compatibility
    (g : MatrixField) (L q : ℝ) (u : R3 → SphereSobolev (3/2 : ℝ))
    (y : R3) (i : Fin 3) (hu : DifferentiableAt ℝ u y) :
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (referenceHighHorizontalAction g L q u y i) =
    referenceLowerHorizontalAction g L q
      (fun x => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (u x)) y i := by
  let Iin := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Iout := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  have hDerivative := (Iin.hasFDerivAt.comp y hu.hasFDerivAt).fderiv
  have hBase := congrArg (fun A : R3 →L[ℝ] SphereSobolev (1/2 : ℝ) =>
    Iout (A (referenceMetricGramFrame g L (q,y) i))) hDerivative
  have hAngular := congrArg
    (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A (u y))
    (referenceHorizontalAngularL_high_lower_compatibility g L q y i)
  have hCombined := congrArg₂ (fun a b : SphereSobolev (-(1/2 : ℝ)) => a+b)
    hBase.symm hAngular
  simpa only [referenceHighHorizontalAction,referenceLowerHorizontalAction,
    ContinuousLinearMap.comp_apply,Function.comp_def,map_add,Iin,Iout] using hCombined

theorem contDiffAt_referenceHighHorizontalAction
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ)
    (u : R3 → SphereSobolev (3/2 : ℝ)) (y : R3) (i : Fin 3)
    (hu : ContDiffAt ℝ ∞ u y) :
    ContDiffAt ℝ ∞ (fun x => referenceHighHorizontalAction g L q u x i) y := by
  have hDerivative := (hu.fderiv_right (m := ∞) (by simp)).clm_apply
    (contDiff_referenceMetricGramFrame_slice g hg L q i).contDiffAt
  have hBase := (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).contDiff.contDiffAt.comp
    y hDerivative
  have hAngular := (contDiff_referenceHighHorizontalAngularL g hg L q i).contDiffAt.clm_apply hu
  exact hBase.add hAngular

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.conformalReferenceMatrix_eq_referenceMetric
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.conformalReferenceGramFrame_eq_referenceMetricGramFrame
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.conformalReferenceFrameConnectionCoefficient_eq_referenceFrameConnectionCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighHorizontalAngularL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerHorizontalAngularL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHorizontalAngularL_high_lower_compatibility
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceHighHorizontalAngularL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceLowerHorizontalAngularL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighHorizontalAction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceLowerHorizontalAction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHorizontalAction_high_lower_compatibility
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceHighHorizontalAction
