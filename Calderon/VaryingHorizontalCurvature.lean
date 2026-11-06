import Calderon.MovingFrameConnection

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.VaryingHorizontalCurvature
open RadiusProfile ConformalDepth MetricOperator CurvatureRotation CurvatureSkew
  HorizontalCurvature FrameCurvaturePolynomial SmoothMetricFrame MovingFrameConnection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def varyingHorizontalVectorField (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (X : R3 → R3) : R3 × R3 → R3 × R3 := fun z => (X z.1,-Γ z.1 (X z.1) z.2)

def baseVectorFieldBracket (X Y : R3 → R3) : R3 → R3 :=
  fun x => fderiv ℝ Y x (X x) - fderiv ℝ X x (Y x)

lemma contDiff_varyingHorizontalVectorField (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (X : R3 → R3) (hΓ : ContDiff ℝ ∞ Γ) (hX : ContDiff ℝ ∞ X) :
    ContDiff ℝ ∞ (varyingHorizontalVectorField Γ X) :=
  (hX.comp contDiff_fst).prodMk
    (((hΓ.comp contDiff_fst).clm_apply (hX.comp contDiff_fst)).clm_apply contDiff_snd).neg

lemma fderiv_varyingHorizontalVectorField_apply
    (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3) (X : R3 → R3)
    (hΓ : ContDiff ℝ ∞ Γ) (hX : ContDiff ℝ ∞ X) (z a : R3 × R3) :
    fderiv ℝ (varyingHorizontalVectorField Γ X) z a =
      (fderiv ℝ X z.1 a.1,
        -((fderiv ℝ Γ z.1 a.1) (X z.1) z.2) -
          Γ z.1 (fderiv ℝ X z.1 a.1) z.2 - Γ z.1 (X z.1) a.2) := by
  have hg := (hΓ.differentiable (by simp) z.1).hasFDerivAt.comp z
    (hasFDerivAt_fst (p := z))
  have hx := (hX.differentiable (by simp) z.1).hasFDerivAt.comp z
    (hasFDerivAt_fst (p := z))
  have h := hx.prodMk ((hg.clm_apply hx).clm_apply (hasFDerivAt_snd (p := z))).neg
  change HasFDerivAt (varyingHorizontalVectorField Γ X) _ z at h
  rw [h.fderiv]
  change (fderiv ℝ X z.1 a.1,
    -(Γ z.1 (X z.1) a.2 +
      (Γ z.1 (fderiv ℝ X z.1 a.1) + (fderiv ℝ Γ z.1 a.1) (X z.1)) z.2)) = _
  simp only [ContinuousLinearMap.add_apply]
  congr 1
  abel

theorem varyingHorizontalVectorField_bracket
    (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3) (X Y : R3 → R3)
    (hΓ : ContDiff ℝ ∞ Γ) (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y)
    (z : R3 × R3) :
    fderiv ℝ (varyingHorizontalVectorField Γ Y) z (varyingHorizontalVectorField Γ X z) -
      fderiv ℝ (varyingHorizontalVectorField Γ X) z (varyingHorizontalVectorField Γ Y z) =
      varyingHorizontalVectorField Γ (baseVectorFieldBracket X Y) z +
        (0,-coordinateCurvatureAction Γ z.1 (X z.1) (Y z.1) z.2) := by
  rw [fderiv_varyingHorizontalVectorField_apply Γ Y hΓ hY,
    fderiv_varyingHorizontalVectorField_apply Γ X hΓ hX]
  simp only [varyingHorizontalVectorField, baseVectorFieldBracket,
    Prod.mk_sub_mk, Prod.mk_add_mk, add_zero, coordinateCurvatureAction_apply,
    map_neg, map_sub, ContinuousLinearMap.sub_apply]
  congr 1
  abel

theorem varyingHorizontalVectorField_covariant_commutator
    (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3) (X Y : R3 → R3)
    (hΓ : ContDiff ℝ ∞ Γ) (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y)
    (u : R3 × R3 → E) (hu : ContDiff ℝ ∞ u) (z : R3 × R3) :
    vectorFieldDeriv (varyingHorizontalVectorField Γ X)
        (vectorFieldDeriv (varyingHorizontalVectorField Γ Y) u) z -
      vectorFieldDeriv (varyingHorizontalVectorField Γ Y)
        (vectorFieldDeriv (varyingHorizontalVectorField Γ X) u) z -
      vectorFieldDeriv (varyingHorizontalVectorField Γ (baseVectorFieldBracket X Y)) u z =
      fderiv ℝ u z (0,-coordinateCurvatureAction Γ z.1 (X z.1) (Y z.1) z.2) := by
  rw [vectorFieldDeriv_commutator _ _ u
    ((contDiff_varyingHorizontalVectorField Γ X hΓ hX).differentiable (by simp))
    ((contDiff_varyingHorizontalVectorField Γ Y hΓ hY).differentiable (by simp)) hu,
    varyingHorizontalVectorField_bracket Γ X Y hΓ hX hY, map_add]
  simp only [vectorFieldDeriv]
  abel

lemma fderiv_movingFramePolynomial_vertical (M : R3 → R3 →L[ℝ] R3)
    (e : R3 → Fin 3 → R3) (hM : ContDiff ℝ ∞ M)
    (hE : ∀ i, ContDiff ℝ ∞ (fun y => e y i))
    (p : MvPolynomial (Fin 3) ℝ) (x v w : R3) :
    fderiv ℝ (movingFramePolynomial M e p) (x,v) (0,w) =
      fderiv ℝ (metricFramePolynomial (M x) (e x) p) v w := by
  rw [fderiv_movingFramePolynomial_apply M e hM hE, fderiv_metricFramePolynomial_apply]
  simp only [fderiv_movingFrameCoordinate_apply M e hM hE,
    map_zero, zero_add, inner_zero_right, add_zero, movingFrameCoordinate,
    metricFrameCoordinates_apply, ContinuousLinearMap.zero_apply]
  have hc : (fun j => ⟪M x v,e x j⟫_ℝ) = metricFrameCoordinates (M x) (e x) v := by
    funext j
    exact (metricFrameCoordinates_apply (M x) (e x) v j).symm
  simp only [hc,zero_add]

attribute [local irreducible] referenceMetricGramFrame referenceConnectionFamily
  metricOperatorField referenceMetric dilatedMetric

theorem reference_varyingHorizontalVectorField_covariant_commutator
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (X Y : R3 → R3) (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y)
    (u : R3 × R3 → E) (hu : ContDiff ℝ ∞ u) (z : R3 × R3) :
    vectorFieldDeriv (varyingHorizontalVectorField (fun y => referenceConnectionFamily g L (lam,y)) X)
      (vectorFieldDeriv (varyingHorizontalVectorField (fun y => referenceConnectionFamily g L (lam,y)) Y) u) z -
    vectorFieldDeriv (varyingHorizontalVectorField (fun y => referenceConnectionFamily g L (lam,y)) Y)
      (vectorFieldDeriv (varyingHorizontalVectorField (fun y => referenceConnectionFamily g L (lam,y)) X) u) z -
    vectorFieldDeriv (varyingHorizontalVectorField (fun y => referenceConnectionFamily g L (lam,y))
      (baseVectorFieldBracket X Y)) u z =
      fderiv ℝ u z (0,-referenceCurvatureAction g L lam z.1 (X z.1) (Y z.1) z.2) := by
  have hpair : ContDiff ℝ ∞ (fun y : R3 => (lam,y)) := contDiff_const.prodMk contDiff_id
  exact varyingHorizontalVectorField_covariant_commutator _ X Y
    ((contDiff_referenceConnectionFamily g hg L).comp hpair) hX hY u hu z

theorem fderiv_referenceMovingFramePolynomial_vertical_curvature
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (x v : R3) (a b : Fin 3) (p : MvPolynomial (Fin 3) ℝ) :
    fderiv ℝ (referenceMovingFramePolynomial g L lam p) (x,v)
      (0,-referenceCurvatureAction g L lam x
        (referenceMetricGramFrame g L (lam,x) a) (referenceMetricGramFrame g L (lam,x) b) v) =
      MvPolynomial.eval (metricFrameCoordinates
        (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x)
        (referenceMetricGramFrame g L (lam,x)) v)
        (referenceHorizontalCurvaturePolynomial g L lam x (referenceMetricGramFrame g L (lam,x)) a b p) := by
  have hpair : ContDiff ℝ ∞ (fun y : R3 => (lam,y)) := contDiff_const.prodMk contDiff_id
  have hM : ContDiff ℝ ∞ (metricOperatorField (referenceMetric (dilatedMetric g lam) L)) :=
    (contDiff_referenceMetricOperator_joint g hg L).comp hpair
  unfold referenceMovingFramePolynomial
  rw [fderiv_movingFramePolynomial_vertical _ _ hM
    (fun i => contDiff_referenceMetricGramFrame_slice g hg L lam i), map_neg]
  rw [fderiv_metricFramePolynomial_operator_apply _ _ _
    (referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (lam,x))]
  simp only [referenceHorizontalCurvaturePolynomial, referenceCurvatureVectorFieldPolynomial,
    referenceCurvatureRotationCoefficient, map_neg]
  rfl

theorem reference_movingFrame_covariant_polynomial_commutator
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ)
    (a b : Fin 3) (p : MvPolynomial (Fin 3) ℝ) (x v : R3) :
    vectorFieldDeriv
      (varyingHorizontalVectorField (fun y => referenceConnectionFamily g L (lam,y))
        (fun y => referenceMetricGramFrame g L (lam,y) a))
      (vectorFieldDeriv
        (varyingHorizontalVectorField (fun y => referenceConnectionFamily g L (lam,y))
          (fun y => referenceMetricGramFrame g L (lam,y) b))
        (referenceMovingFramePolynomial g L lam p)) (x,v) -
    vectorFieldDeriv
      (varyingHorizontalVectorField (fun y => referenceConnectionFamily g L (lam,y))
        (fun y => referenceMetricGramFrame g L (lam,y) b))
      (vectorFieldDeriv
        (varyingHorizontalVectorField (fun y => referenceConnectionFamily g L (lam,y))
          (fun y => referenceMetricGramFrame g L (lam,y) a))
        (referenceMovingFramePolynomial g L lam p)) (x,v) -
    vectorFieldDeriv
      (varyingHorizontalVectorField (fun y => referenceConnectionFamily g L (lam,y))
        (baseVectorFieldBracket (fun y => referenceMetricGramFrame g L (lam,y) a)
          (fun y => referenceMetricGramFrame g L (lam,y) b)))
      (referenceMovingFramePolynomial g L lam p) (x,v) =
    MvPolynomial.eval (metricFrameCoordinates
      (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x)
      (referenceMetricGramFrame g L (lam,x)) v)
      (referenceHorizontalCurvaturePolynomial g L lam x (referenceMetricGramFrame g L (lam,x)) a b p) := by
  rw [reference_varyingHorizontalVectorField_covariant_commutator g hg L lam _ _
    (contDiff_referenceMetricGramFrame_slice g hg L lam a)
    (contDiff_referenceMetricGramFrame_slice g hg L lam b)
    (referenceMovingFramePolynomial g L lam p) (contDiff_referenceMovingFramePolynomial g hg L lam p)]
  exact fderiv_referenceMovingFramePolynomial_vertical_curvature g hg L lam x v a b p

end OAI.AnisotropicCalderon.VaryingHorizontalCurvature
