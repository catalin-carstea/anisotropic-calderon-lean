import Calderon.WeightedFischerSquare
import Calderon.MetricFiberFischer
import Calderon.IndexedCovariantCurvature
import Calderon.FullCovectorCurvature
import Mathlib.Algebra.MvPolynomial.Funext

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MvPolynomial
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.FiniteCovariantCurvature
open RadiusProfile ConformalDepth MetricOperator AngularPolynomial CurvatureSkew
  MovingFrameConnection FischerConnectionTransport WeightedFischerSquare
  SmoothMetricFrame FrameCurvaturePolynomial MetricFiberMeasure MetricFiberFischer
  HorizontalCurvature VaryingHorizontalCurvature IndexedCovariantCurvature
  PolynomialSlotCompatibility FullCovectorCurvature

attribute [local irreducible] referenceMetricGramFrame referenceConnectionFamily
  metricOperatorField referenceMetric dilatedMetric
  referenceFrameConnectionCoefficient frameConnectionCoefficient covariantFrameDerivative

variable {ι : Type*} [Fintype ι]

lemma referenceMovingFramePolynomial_eq_metricFramePolynomial
    (g : MatrixField) (L lam : ℝ) (p : MvPolynomial (Fin 3) ℝ) (x v : R3) :
    referenceMovingFramePolynomial g L lam p (x,v) =
      metricFramePolynomial (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x)
        (referenceMetricGramFrame g L (lam,x)) p v := by
  unfold referenceMovingFramePolynomial movingFramePolynomial metricFramePolynomial
  apply congrArg (fun w : Fin 3 → ℝ => eval w p)
  funext i
  exact (metricFrameCoordinates_apply _ _ _ i).symm

lemma referenceMovingFramePolynomial_injective (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (x : R3) (p q : MvPolynomial (Fin 3) ℝ)
    (h : ∀ v : R3, referenceMovingFramePolynomial g L lam p (x,v) =
      referenceMovingFramePolynomial g L lam q (x,v)) : p = q := by
  apply MvPolynomial.funext
  intro w
  have he := referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (lam,x)
  have hv := h (metricFrameSynthesis _ _ he (WithLp.toLp 2 w))
  simp only [referenceMovingFramePolynomial_eq_metricFramePolynomial,
    metricFramePolynomial_synthesis] at hv
  simpa using hv

lemma referenceHorizontalCurvaturePolynomial_finite (g : MatrixField) (L lam : ℝ)
    (x : R3) (e : Fin 3 → R3) (i j : Fin 3)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) :
    referenceHorizontalCurvaturePolynomial g L lam x e i j (finitePolynomialField b c x) =
      ∑ a, c x a • referenceHorizontalCurvaturePolynomial g L lam x e i j (b a) := by
  let T : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] MvPolynomial (Fin 3) ℝ :=
    { toFun := fun p => -polynomialMatrixVectorField
        (CurvatureRotation.referenceCurvatureRotationCoefficient g L lam x e i j) p
      map_add' := fun p q => by rw [polynomialMatrixVectorField_add,neg_add]
      map_smul' := fun a p => by simp only [polynomialMatrixVectorField_smul,smul_neg,RingHom.id_apply] }
  change T (∑ a, c x a • b a) = ∑ a, c x a • T (b a)
  simp only [map_sum,map_smul]

lemma referenceHorizontalDerivative_eq_evaluated_augmented
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (hc : ContDiff ℝ ∞ c)
    (V : R3 → R3) :
    vectorFieldDeriv (varyingHorizontalVectorField (fun y => referenceConnectionFamily g L (lam,y)) V)
      (evaluatedReferencePolynomialField g L lam b c) =
    evaluatedReferencePolynomialField g L lam (covariantDerivativePolynomialFamily b)
      (covariantDerivativeCoefficientFamily g L lam c V) := by
  funext z
  change fderiv ℝ (evaluatedReferencePolynomialField g L lam b c) z
    (V z.1,-referenceConnectionFamily g L (lam,z.1) (V z.1) z.2) = _
  rw [fderiv_evaluatedReferencePolynomialField_horizontal g hg L lam b c hc,
    referenceCovariantPolynomialDerivative_eq_finite_augmented]
  exact (evaluatedReferencePolynomialField_eq g L lam _ _ z).symm

def referenceIndexedPolynomialHessian (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (x : R3) (i j : Fin 3) :
    MvPolynomial (Fin 3) ℝ :=
  referenceCovariantPolynomialDerivative g L lam (covariantDerivativePolynomialFamily b)
    (covariantDerivativeCoefficientFamily g L lam c (fun y => referenceMetricGramFrame g L (lam,y) j))
    x (referenceMetricGramFrame g L (lam,x) i) -
    ∑ a : Fin 3, C (referenceFrameConnectionCoefficient g L lam x
      (referenceMetricGramFrame g L (lam,x) i) a j) *
      referenceCovariantPolynomialDerivative g L lam b c x (referenceMetricGramFrame g L (lam,x) a)

lemma referenceIndexedPolynomialHessian_evaluation (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (hc : ContDiff ℝ ∞ c) (x v : R3) (i j : Fin 3) :
    referenceMovingFramePolynomial g L lam (referenceIndexedPolynomialHessian g L lam b c x i j) (x,v) =
      referenceIndexedCovariantHessian g L lam (evaluatedReferencePolynomialField g L lam b c) i j (x,v) := by
  unfold referenceIndexedCovariantHessian indexedCovariantHessian
  rw [referenceHorizontalDerivative_eq_evaluated_augmented g hg L lam b c hc]
  have hq := contDiff_covariantDerivativeCoefficientFamily g hg L lam c
    (fun y => referenceMetricGramFrame g L (lam,y) j) hc
    (contDiff_referenceMetricGramFrame_slice g hg L lam j)
  change _ = fderiv ℝ
    (evaluatedReferencePolynomialField g L lam (covariantDerivativePolynomialFamily b)
      (covariantDerivativeCoefficientFamily g L lam c (fun y => referenceMetricGramFrame g L (lam,y) j)))
    (x,v) (referenceMetricGramFrame g L (lam,x) i,
      -referenceConnectionFamily g L (lam,x) (referenceMetricGramFrame g L (lam,x) i) v) - _
  rw [fderiv_evaluatedReferencePolynomialField_horizontal g hg L lam _ _ hq]
  have hfirst (a : Fin 3) := fderiv_evaluatedReferencePolynomialField_horizontal g hg L lam b c hc x v
    (referenceMetricGramFrame g L (lam,x) a)
  simp only [vectorFieldDeriv,varyingHorizontalVectorField] at *
  simp_rw [hfirst]
  simp only [referenceIndexedPolynomialHessian,referenceMovingFramePolynomial,movingFramePolynomial,
    map_sub,map_sum,map_mul,eval_C,smul_eq_mul,referenceFrameConnectionCoefficient]

lemma fderiv_referencePolynomialFieldSummand_vertical (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (p : MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (hc : ContDiff ℝ ∞ c) (a : ι) (x v Y : R3) :
    fderiv ℝ (fun z : R3 × R3 => c z.1 a * referenceMovingFramePolynomial g L lam p z)
      (x,v) (0,Y) = c x a * fderiv ℝ (referenceMovingFramePolynomial g L lam p) (x,v) (0,Y) := by
  have hbase : HasFDerivAt (fun z : R3 × R3 => c z.1)
      ((fderiv ℝ c x).comp (ContinuousLinearMap.fst ℝ R3 R3)) (x,v) :=
    ((hc.differentiable (by simp) x).hasFDerivAt).comp (x,v) (hasFDerivAt_fst (p := (x,v)))
  have hcoef := (ContinuousLinearMap.proj a : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp (x,v) hbase
  have hpoly := ((contDiff_referenceMovingFramePolynomial g hg L lam p).differentiable
    (by simp) (x,v)).hasFDerivAt
  have hp := hcoef.mul hpoly
  change HasFDerivAt (fun z : R3 × R3 => c z.1 a * referenceMovingFramePolynomial g L lam p z) _ (x,v) at hp
  rw [hp.fderiv]
  change c x a * fderiv ℝ (referenceMovingFramePolynomial g L lam p) (x,v) (0,Y) +
    referenceMovingFramePolynomial g L lam p (x,v) * (fderiv ℝ c x 0) a = _
  simp only [map_zero,Pi.zero_apply,mul_zero,add_zero]

lemma fderiv_evaluatedReferencePolynomialField_vertical_curvature (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (hc : ContDiff ℝ ∞ c) (x v : R3) (i j : Fin 3) :
    fderiv ℝ (evaluatedReferencePolynomialField g L lam b c) (x,v)
      (0,-CurvatureRotation.referenceCurvatureAction g L lam x
        (referenceMetricGramFrame g L (lam,x) i) (referenceMetricGramFrame g L (lam,x) j) v) =
    referenceMovingFramePolynomial g L lam
      (referenceHorizontalCurvaturePolynomial g L lam x (referenceMetricGramFrame g L (lam,x)) i j
        (finitePolynomialField b c x)) (x,v) := by
  rw [show evaluatedReferencePolynomialField g L lam b c =
    (fun z : R3 × R3 => ∑ a, c z.1 a * referenceMovingFramePolynomial g L lam (b a) z) from rfl]
  rw [fderiv_fun_sum (fun a _ => ((contDiff_referencePolynomialFieldSummand g hg L lam (b a) c hc a).differentiable (by simp) (x,v)))]
  simp only [ContinuousLinearMap.sum_apply]
  simp_rw [fderiv_referencePolynomialFieldSummand_vertical g hg L lam _ c hc,
    fderiv_referenceMovingFramePolynomial_vertical_curvature g hg L lam]
  rw [referenceHorizontalCurvaturePolynomial_finite]
  simp only [referenceMovingFramePolynomial_eq_metricFramePolynomial,metricFramePolynomial,map_sum,
    smul_eq_C_mul,map_mul,eval_C]

theorem referenceIndexedPolynomialHessian_antisymm (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (hc : ContDiff ℝ ∞ c) (x : R3) (i j : Fin 3) :
    referenceIndexedPolynomialHessian g L lam b c x i j -
      referenceIndexedPolynomialHessian g L lam b c x j i =
    referenceHorizontalCurvaturePolynomial g L lam x (referenceMetricGramFrame g L (lam,x)) i j
      (finitePolynomialField b c x) := by
  apply referenceMovingFramePolynomial_injective g hg L lam x
  intro v
  have h := referenceIndexedCovariantHessian_antisymm g hg L lam
    (evaluatedReferencePolynomialField g L lam b c)
    (contDiff_evaluatedReferencePolynomialField g hg L lam b c hc) x v i j
  rw [fderiv_evaluatedReferencePolynomialField_vertical_curvature g hg L lam b c hc] at h
  rw [← referenceIndexedPolynomialHessian_evaluation g hg L lam b c hc,
    ← referenceIndexedPolynomialHessian_evaluation g hg L lam b c hc] at h
  simpa only [referenceMovingFramePolynomial,movingFramePolynomial,map_sub] using h

lemma referenceCovectorPolynomialDerivative_partial_eq_augmented (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (V : R3 → R3) (x : R3) (l : Fin 3) :
    referenceCovectorPolynomialDerivative g L lam (fun a t => pderiv t (b a)) c x (V x) l =
    finitePolynomialField (fun a => pderiv l (covariantDerivativePolynomialFamily b a))
      (covariantDerivativeCoefficientFamily g L lam c V) x := by
  rw [referenceCovectorPolynomialDerivative_partial,
    referenceCovariantPolynomialDerivative_eq_finite_augmented,finitePolynomialField_partial]

def referenceLoweredCovectorIndexedHessian (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (x : R3) (i j l : Fin 3) :
    MvPolynomial (Fin 3) ℝ :=
  referenceCovectorPolynomialDerivative g L lam
    (fun a t => pderiv t (covariantDerivativePolynomialFamily b a))
    (covariantDerivativeCoefficientFamily g L lam c (fun y => referenceMetricGramFrame g L (lam,y) j))
    x (referenceMetricGramFrame g L (lam,x) i) l -
    ∑ a : Fin 3, C (referenceFrameConnectionCoefficient g L lam x
      (referenceMetricGramFrame g L (lam,x) i) a j) *
      referenceCovectorPolynomialDerivative g L lam (fun a t => pderiv t (b a)) c x
        (referenceMetricGramFrame g L (lam,x) a) l

lemma referenceLoweredCovectorIndexedHessian_eq_partial (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (x : R3) (i j l : Fin 3) :
    referenceLoweredCovectorIndexedHessian g L lam b c x i j l =
      pderiv l (referenceIndexedPolynomialHessian g L lam b c x i j) := by
  simp only [referenceLoweredCovectorIndexedHessian,referenceCovectorPolynomialDerivative_partial,
    referenceIndexedPolynomialHessian,map_sub,map_sum,pderiv_C_mul]

theorem referenceLoweredCovectorIndexedHessian_antisymm (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (hc : ContDiff ℝ ∞ c) (x : R3) (i j l : Fin 3) :
    referenceLoweredCovectorIndexedHessian g L lam b c x i j l -
      referenceLoweredCovectorIndexedHessian g L lam b c x j i l =
    referenceCovectorCurvaturePolynomial g L lam x (referenceMetricGramFrame g L (lam,x)) i j
      (fun a => pderiv a (finitePolynomialField b c x)) l := by
  rw [referenceLoweredCovectorIndexedHessian_eq_partial,
    referenceLoweredCovectorIndexedHessian_eq_partial,← map_sub,
    referenceIndexedPolynomialHessian_antisymm g hg L lam b c hc,
    referenceCovectorCurvaturePolynomial_partial]

end OAI.AnisotropicCalderon.FiniteCovariantCurvature
