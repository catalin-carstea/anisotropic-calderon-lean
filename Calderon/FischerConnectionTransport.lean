import Calderon.MovingFrameConnection
import Calderon.AngularBaseFinite

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.FischerConnectionTransport
open RadiusProfile ConformalDepth MetricOperator AngularPolynomial SphereHarmonic PrincipalCommutator
  CurvatureSkew MovingFrameConnection SmoothMetricFrame FrameCurvaturePolynomial MvPolynomial

lemma fischerInner_rotationCombination_skew (c : Fin 3 → Fin 3 → ℝ)
    (p q : MvPolynomial (Fin 3) ℝ) :
    fischerInner (polynomialRotationCombination c p) q =
      -fischerInner p (polynomialRotationCombination c q) := by
  simp only [polynomialRotationCombination, fischerInner_finset_sum_left,
    fischerInner_sum_right, fischerInner_C_mul_left, fischerInner_C_mul_right,
    fischerInner_rotation_skew, mul_neg, Finset.sum_neg_distrib]

lemma referenceFrameAngularPolynomial_fischer_skew (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (x X : R3)
    (p q : MvPolynomial (Fin 3) ℝ) :
    fischerInner (referenceFrameAngularPolynomial g L lam x X p) q =
      -fischerInner p (referenceFrameAngularPolynomial g L lam x X q) := by
  rw [referenceFrameAngularPolynomial_eq_half_smul g hg L lam x X p,
    referenceFrameAngularPolynomial_eq_half_smul g hg L lam x X q]
  simp only [smul_eq_C_mul,fischerInner_C_mul_left,fischerInner_C_mul_right,
    fischerInner_rotationCombination_skew,mul_neg]

lemma polynomialMatrixVectorField_add (c : Fin 3 → Fin 3 → ℝ)
    (p q : MvPolynomial (Fin 3) ℝ) :
    polynomialMatrixVectorField c (p+q) = polynomialMatrixVectorField c p + polynomialMatrixVectorField c q := by
  simp only [polynomialMatrixVectorField,map_add,mul_add,Finset.sum_add_distrib]

lemma polynomialMatrixVectorField_smul (c : Fin 3 → Fin 3 → ℝ)
    (a : ℝ) (p : MvPolynomial (Fin 3) ℝ) :
    polynomialMatrixVectorField c (a • p) = a • polynomialMatrixVectorField c p := by
  simp only [polynomialMatrixVectorField,smul_eq_C_mul,pderiv_C_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma referenceFrameAngularPolynomial_add (g : MatrixField) (L lam : ℝ) (x X : R3)
    (p q : MvPolynomial (Fin 3) ℝ) :
    referenceFrameAngularPolynomial g L lam x X (p+q) =
      referenceFrameAngularPolynomial g L lam x X p + referenceFrameAngularPolynomial g L lam x X q := by
  simp only [referenceFrameAngularPolynomial,polynomialMatrixVectorField_add,neg_add]

lemma referenceFrameAngularPolynomial_smul (g : MatrixField) (L lam : ℝ) (x X : R3)
    (a : ℝ) (p : MvPolynomial (Fin 3) ℝ) :
    referenceFrameAngularPolynomial g L lam x X (a • p) =
      a • referenceFrameAngularPolynomial g L lam x X p := by
  simp only [referenceFrameAngularPolynomial,polynomialMatrixVectorField_smul,smul_neg]

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def finitePolynomialField (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (x : R3) : MvPolynomial (Fin 3) ℝ := ∑ i, c x i • b i

def finitePolynomialFieldDerivative (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (x X : R3) : MvPolynomial (Fin 3) ℝ :=
  ∑ i, (fderiv ℝ c x X) i • b i

lemma fischerInner_finitePolynomialField (b : ι → MvPolynomial (Fin 3) ℝ)
    (d : κ → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (z : R3 → κ → ℝ) (x : R3) :
    fischerInner (finitePolynomialField b c x) (finitePolynomialField d z x) =
      ∑ i, ∑ j, c x i * z x j * fischerInner (b i) (d j) := by
  simp only [finitePolynomialField,fischerInner_finset_sum_left,fischerInner_sum_right,
    smul_eq_C_mul,fischerInner_C_mul_left,fischerInner_C_mul_right,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def polynomialFamilyFischerBilinear (b : ι → MvPolynomial (Fin 3) ℝ)
    (d : κ → MvPolynomial (Fin 3) ℝ) : (ι → ℝ) →L[ℝ] (κ → ℝ) →L[ℝ] ℝ :=
  ∑ i, ∑ j, fischerInner (b i) (d j) •
    (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj j)

lemma polynomialFamilyFischerBilinear_apply (b : ι → MvPolynomial (Fin 3) ℝ)
    (d : κ → MvPolynomial (Fin 3) ℝ) (c : ι → ℝ) (z : κ → ℝ) :
    polynomialFamilyFischerBilinear b d c z =
      ∑ i, ∑ j, c i * z j * fischerInner (b i) (d j) := by
  simp only [polynomialFamilyFischerBilinear,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma fderiv_fischerInner_finitePolynomialField (b : ι → MvPolynomial (Fin 3) ℝ)
    (d : κ → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (z : R3 → κ → ℝ)
    (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z) (x X : R3) :
    fderiv ℝ (fun y => fischerInner (finitePolynomialField b c y) (finitePolynomialField d z y)) x X =
      fischerInner (finitePolynomialFieldDerivative b c x X) (finitePolynomialField d z x) +
      fischerInner (finitePolynomialField b c x) (finitePolynomialFieldDerivative d z x X) := by
  let B := polynomialFamilyFischerBilinear b d
  have hpair : (fun y => fischerInner (finitePolynomialField b c y) (finitePolynomialField d z y)) =
      fun y => B (c y) (z y) := by
    funext y
    rw [fischerInner_finitePolynomialField]
    exact (polynomialFamilyFischerBilinear_apply b d (c y) (z y)).symm
  have hp := ((B.hasFDerivAt.comp x ((hc.differentiable (by simp) x).hasFDerivAt)).clm_apply
    ((hz.differentiable (by simp) x).hasFDerivAt))
  change HasFDerivAt (fun y => B (c y) (z y)) _ x at hp
  rw [hpair,hp.fderiv]
  change B (c x) (fderiv ℝ z x X) + B (fderiv ℝ c x X) (z x) = _
  change B (c x) (fderiv ℝ z x X) + B (fderiv ℝ c x X) (z x) =
    fischerInner (finitePolynomialField b (fun _ => fderiv ℝ c x X) x) (finitePolynomialField d z x) +
    fischerInner (finitePolynomialField b c x) (finitePolynomialField d (fun _ => fderiv ℝ z x X) x)
  simp only [B,polynomialFamilyFischerBilinear_apply,fischerInner_finitePolynomialField]
  exact add_comm _ _

def referenceCovariantPolynomialDerivative (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (x X : R3) :
    MvPolynomial (Fin 3) ℝ :=
  finitePolynomialFieldDerivative b c x X +
    referenceFrameAngularPolynomial g L lam x X (finitePolynomialField b c x)

lemma referenceCovariantPolynomialDerivative_fischer_compatible (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (d : κ → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (z : R3 → κ → ℝ)
    (hc : ContDiff ℝ ∞ c) (hz : ContDiff ℝ ∞ z) (x X : R3) :
    fderiv ℝ (fun y => fischerInner (finitePolynomialField b c y) (finitePolynomialField d z y)) x X =
      fischerInner (referenceCovariantPolynomialDerivative g L lam b c x X) (finitePolynomialField d z x) +
      fischerInner (finitePolynomialField b c x) (referenceCovariantPolynomialDerivative g L lam d z x X) := by
  rw [fderiv_fischerInner_finitePolynomialField b d c z hc hz x X]
  simp only [referenceCovariantPolynomialDerivative,fischerInner_add_left,fischerInner_add_right]
  rw [referenceFrameAngularPolynomial_fischer_skew g hg L lam x X]
  ring

def referenceAngularPolynomialLinearMap (g : MatrixField) (L lam : ℝ) (x X : R3) :
    MvPolynomial (Fin 3) ℝ →ₗ[ℝ] MvPolynomial (Fin 3) ℝ where
  toFun := referenceFrameAngularPolynomial g L lam x X
  map_add' := referenceFrameAngularPolynomial_add g L lam x X
  map_smul' := referenceFrameAngularPolynomial_smul g L lam x X

lemma referenceFrameAngularPolynomial_sum (g : MatrixField) (L lam : ℝ) (x X : R3)
    (p : ι → MvPolynomial (Fin 3) ℝ) :
    referenceFrameAngularPolynomial g L lam x X (∑ i, p i) =
      ∑ i, referenceFrameAngularPolynomial g L lam x X (p i) :=
  map_sum (referenceAngularPolynomialLinearMap g L lam x X) p Finset.univ

lemma finitePolynomialField_harmonicHomogeneous (k : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ i, b i ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (x : R3) : finitePolynomialField b c x ∈ harmonicHomogeneous k :=
  (harmonicHomogeneous k).sum_mem (fun i _ => (harmonicHomogeneous k).smul_mem _ (hb i))

lemma finitePolynomialFieldDerivative_harmonicHomogeneous (k : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ i, b i ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (x X : R3) :
    finitePolynomialFieldDerivative b c x X ∈ harmonicHomogeneous k :=
  (harmonicHomogeneous k).sum_mem (fun i _ => (harmonicHomogeneous k).smul_mem _ (hb i))

lemma referenceCovariantPolynomialDerivative_harmonicHomogeneous (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (b : ι → MvPolynomial (Fin 3) ℝ) (hb : ∀ i, b i ∈ harmonicHomogeneous k)
    (c : R3 → ι → ℝ) (x X : R3) :
    referenceCovariantPolynomialDerivative g L lam b c x X ∈ harmonicHomogeneous k :=
  (harmonicHomogeneous k).add_mem (finitePolynomialFieldDerivative_harmonicHomogeneous k b hb c x X)
    (referenceFrameAngularPolynomial_harmonicHomogeneous g hg L lam x X k hk _
      (finitePolynomialField_harmonicHomogeneous k b hb c x))

def evaluatedReferencePolynomialField (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (z : R3 × R3) : ℝ :=
  ∑ i, c z.1 i * referenceMovingFramePolynomial g L lam (b i) z

lemma evaluatedReferencePolynomialField_eq (g : MatrixField) (L lam : ℝ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ) (z : R3 × R3) :
    evaluatedReferencePolynomialField g L lam b c z =
      referenceMovingFramePolynomial g L lam (finitePolynomialField b c z.1) z := by
  simp only [evaluatedReferencePolynomialField,referenceMovingFramePolynomial,
    movingFramePolynomial,finitePolynomialField,map_sum,smul_eq_C_mul,map_mul,eval_C]

lemma contDiff_referencePolynomialFieldSummand (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (p : MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (hc : ContDiff ℝ ∞ c) (i : ι) :
    ContDiff ℝ ∞ (fun z : R3 × R3 => c z.1 i * referenceMovingFramePolynomial g L lam p z) :=
  ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).contDiff.comp (hc.comp contDiff_fst)).mul
    (contDiff_referenceMovingFramePolynomial g hg L lam p)

lemma contDiff_evaluatedReferencePolynomialField (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (hc : ContDiff ℝ ∞ c) : ContDiff ℝ ∞ (evaluatedReferencePolynomialField g L lam b c) :=
  ContDiff.sum (fun i _ => contDiff_referencePolynomialFieldSummand g hg L lam (b i) c hc i)

attribute [local irreducible] referenceMetricGramFrame referenceConnectionFamily
  metricOperatorField referenceMetric dilatedMetric

lemma fderiv_referencePolynomialFieldSummand_horizontal (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (p : MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (hc : ContDiff ℝ ∞ c) (i : ι) (x v X : R3) :
    fderiv ℝ (fun z : R3 × R3 => c z.1 i * referenceMovingFramePolynomial g L lam p z)
      (x,v) (X,-referenceConnectionFamily g L (lam,x) X v) =
    (fderiv ℝ c x X) i * referenceMovingFramePolynomial g L lam p (x,v) +
      c x i * referenceMovingFramePolynomial g L lam
        (referenceFrameAngularPolynomial g L lam x X p) (x,v) := by
  have hbase : HasFDerivAt (fun z : R3 × R3 => c z.1)
      ((fderiv ℝ c x).comp (ContinuousLinearMap.fst ℝ R3 R3)) (x,v) :=
    ((hc.differentiable (by simp) x).hasFDerivAt).comp (x,v)
      (hasFDerivAt_fst (p := (x,v)))
  have hcoef := (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp (x,v) hbase
  have hpoly := ((contDiff_referenceMovingFramePolynomial g hg L lam p).differentiable
    (by simp) (x,v)).hasFDerivAt
  have hp := hcoef.mul hpoly
  change HasFDerivAt (fun z : R3 × R3 => c z.1 i * referenceMovingFramePolynomial g L lam p z) _ (x,v) at hp
  rw [hp.fderiv]
  change c x i * (fderiv ℝ (referenceMovingFramePolynomial g L lam p) (x,v)
    (X,-referenceConnectionFamily g L (lam,x) X v)) +
    referenceMovingFramePolynomial g L lam p (x,v) * (fderiv ℝ c x X) i = _
  have hd := fderiv_referenceMovingFramePolynomial_horizontal g hg L lam x v X p
  change fderiv ℝ (referenceMovingFramePolynomial g L lam p) (x,v)
    (X,-referenceConnectionFamily g L (lam,x) X v) =
    referenceMovingFramePolynomial g L lam (referenceFrameAngularPolynomial g L lam x X p) (x,v) at hd
  rw [hd]
  ring

theorem fderiv_evaluatedReferencePolynomialField_horizontal (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (hc : ContDiff ℝ ∞ c) (x v X : R3) :
    fderiv ℝ (evaluatedReferencePolynomialField g L lam b c) (x,v)
      (X,-referenceConnectionFamily g L (lam,x) X v) =
      referenceMovingFramePolynomial g L lam
        (referenceCovariantPolynomialDerivative g L lam b c x X) (x,v) := by
  rw [show evaluatedReferencePolynomialField g L lam b c =
    (fun z : R3 × R3 => ∑ i, c z.1 i * referenceMovingFramePolynomial g L lam (b i) z) from rfl]
  rw [fderiv_fun_sum (fun i _ =>
    ((contDiff_referencePolynomialFieldSummand g hg L lam (b i) c hc i).differentiable
      (by simp) (x,v)))]
  simp only [ContinuousLinearMap.sum_apply]
  simp_rw [fderiv_referencePolynomialFieldSummand_horizontal g hg L lam _ c hc _ x v X]
  simp only [referenceCovariantPolynomialDerivative,finitePolynomialFieldDerivative,
    finitePolynomialField,referenceFrameAngularPolynomial_sum,referenceFrameAngularPolynomial_smul]
  simp only [referenceMovingFramePolynomial,movingFramePolynomial,map_add,map_sum,
    smul_eq_C_mul,map_mul,eval_C,Finset.sum_add_distrib]

end OAI.AnisotropicCalderon.FischerConnectionTransport
