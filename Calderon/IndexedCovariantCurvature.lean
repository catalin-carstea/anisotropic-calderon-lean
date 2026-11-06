import Calderon.VaryingHorizontalCurvature

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.IndexedCovariantCurvature
open RadiusProfile ConformalDepth MetricOperator ConnectionError CurvatureRotation CurvatureSkew
  HorizontalCurvature FrameCurvaturePolynomial SmoothMetricFrame MovingFrameConnection
  VaryingHorizontalCurvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local irreducible] referenceMetricGramFrame referenceConnectionFamily
  metricOperatorField referenceMetric dilatedMetric

theorem referenceConnectionFamily_symmetric (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (x X Y : R3) :
    referenceConnectionFamily g L (lam,x) X Y = referenceConnectionFamily g L (lam,x) Y X := by
  have hpair : ContDiff ℝ ∞ (fun y : R3 => (lam,y)) := contDiff_const.prodMk contDiff_id
  have hM : ContDiff ℝ ∞ (metricOperatorField (referenceMetric (dilatedMetric g lam) L)) :=
    (contDiff_referenceMetricOperator_joint g hg L).comp hpair
  have hs : ∀ᶠ y in 𝓝 x, ∀ U V : R3,
      ⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) y U,V⟫_ℝ =
        ⟪metricOperatorField (referenceMetric (dilatedMetric g lam) L) y V,U⟫_ℝ :=
    Filter.Eventually.of_forall (fun y U V => referenceMetricOperator_symmetric g hg L lam y U V)
  simp only [referenceConnectionFamily,coordinateConnectionField_apply]
  apply coordinateConnection_symmetric
  intro U V W
  exact inverse_metric_derivative_symmetric _ _ x
    ((hM.differentiable (by simp) x).hasFDerivAt) hs U V W

theorem frame_baseVectorFieldBracket_eq_sum
    (M : R3 → R3 →L[ℝ] R3) (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (e : R3 → Fin 3 → R3) (x : R3) (he : IsMetricOrthonormalFrame (M x) (e x))
    (hsym : ∀ X Y, Γ x X Y = Γ x Y X) (a b : Fin 3) :
    baseVectorFieldBracket (fun y => e y a) (fun y => e y b) x =
      ∑ l : Fin 3, (frameConnectionCoefficient M Γ e x (e x a) l b -
        frameConnectionCoefficient M Γ e x (e x b) l a) • e x l := by
  have h1 := covariantFrameDerivative_eq_sum M Γ e x (e x a) he b
  have h2 := covariantFrameDerivative_eq_sum M Γ e x (e x b) he a
  have hdiff := congrArg₂ (fun U V : R3 => U-V) h1 h2
  simp only [covariantFrameDerivative, hsym (e x a) (e x b)] at hdiff
  simp only [sub_smul,Finset.sum_sub_distrib]
  rw [← hdiff]
  simp only [baseVectorFieldBracket]
  abel

def horizontalLiftAt (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3) (x v : R3) :
    R3 →L[ℝ] R3 × R3 :=
  (ContinuousLinearMap.id ℝ R3).prod (-((Γ x).flip v))

lemma horizontalLiftAt_apply (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3) (x v X : R3) :
    horizontalLiftAt Γ x v X = (X,-Γ x X v) := rfl

theorem frame_bracket_horizontal_derivative_eq_sum
    (M : R3 → R3 →L[ℝ] R3) (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (e : R3 → Fin 3 → R3) (x v : R3) (he : IsMetricOrthonormalFrame (M x) (e x))
    (hsym : ∀ X Y, Γ x X Y = Γ x Y X) (u : R3 × R3 → E) (a b : Fin 3) :
    vectorFieldDeriv (varyingHorizontalVectorField Γ
      (baseVectorFieldBracket (fun y => e y a) (fun y => e y b))) u (x,v) =
      ∑ l : Fin 3, (frameConnectionCoefficient M Γ e x (e x a) l b -
        frameConnectionCoefficient M Γ e x (e x b) l a) •
          vectorFieldDeriv (varyingHorizontalVectorField Γ (fun y => e y l)) u (x,v) := by
  change fderiv ℝ u (x,v) (horizontalLiftAt Γ x v
    (baseVectorFieldBracket (fun y => e y a) (fun y => e y b) x)) = _
  rw [frame_baseVectorFieldBracket_eq_sum M Γ e x he hsym a b]
  simp only [map_sum,map_smul,horizontalLiftAt_apply,vectorFieldDeriv,varyingHorizontalVectorField]

def indexedCovariantHessian (M : R3 → R3 →L[ℝ] R3)
    (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3) (e : R3 → Fin 3 → R3)
    (u : R3 × R3 → E) (a b : Fin 3) (z : R3 × R3) : E :=
  vectorFieldDeriv (varyingHorizontalVectorField Γ (fun y => e y a))
    (vectorFieldDeriv (varyingHorizontalVectorField Γ (fun y => e y b)) u) z -
      ∑ l : Fin 3, frameConnectionCoefficient M Γ e z.1 (e z.1 a) l b •
        vectorFieldDeriv (varyingHorizontalVectorField Γ (fun y => e y l)) u z

theorem indexedCovariantHessian_antisymm
    (M : R3 → R3 →L[ℝ] R3) (Γ : R3 → R3 →L[ℝ] R3 →L[ℝ] R3)
    (e : R3 → Fin 3 → R3) (hΓ : ContDiff ℝ ∞ Γ)
    (hE : ∀ i, ContDiff ℝ ∞ (fun y => e y i)) (x v : R3)
    (he : IsMetricOrthonormalFrame (M x) (e x))
    (hsym : ∀ X Y, Γ x X Y = Γ x Y X)
    (u : R3 × R3 → E) (hu : ContDiff ℝ ∞ u) (a b : Fin 3) :
    indexedCovariantHessian M Γ e u a b (x,v) - indexedCovariantHessian M Γ e u b a (x,v) =
      fderiv ℝ u (x,v) (0,-coordinateCurvatureAction Γ x (e x a) (e x b) v) := by
  have h := varyingHorizontalVectorField_covariant_commutator Γ
    (fun y => e y a) (fun y => e y b) hΓ (hE a) (hE b) u hu (x,v)
  rw [frame_bracket_horizontal_derivative_eq_sum M Γ e x v he hsym u a b] at h
  simp only [sub_smul,Finset.sum_sub_distrib] at h
  simp only [indexedCovariantHessian]
  exact (by abel : _ = _) |>.trans h


def referenceIndexedCovariantHessian (g : MatrixField) (L lam : ℝ)
    (u : R3 × R3 → E) (a b : Fin 3) : R3 × R3 → E :=
  indexedCovariantHessian (metricOperatorField (referenceMetric (dilatedMetric g lam) L))
    (fun y => referenceConnectionFamily g L (lam,y))
    (fun y => referenceMetricGramFrame g L (lam,y)) u a b

theorem referenceIndexedCovariantHessian_antisymm (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (u : R3 × R3 → E) (hu : ContDiff ℝ ∞ u) (x v : R3) (a b : Fin 3) :
    referenceIndexedCovariantHessian g L lam u a b (x,v) -
      referenceIndexedCovariantHessian g L lam u b a (x,v) =
        fderiv ℝ u (x,v) (0,-referenceCurvatureAction g L lam x
          (referenceMetricGramFrame g L (lam,x) a) (referenceMetricGramFrame g L (lam,x) b) v) := by
  have hpair : ContDiff ℝ ∞ (fun y : R3 => (lam,y)) := contDiff_const.prodMk contDiff_id
  exact indexedCovariantHessian_antisymm _ _ _
    ((contDiff_referenceConnectionFamily g hg L).comp hpair)
    (fun i => contDiff_referenceMetricGramFrame_slice g hg L lam i) x v
    (referenceMetricGramFrame_isMetricOrthonormalFrame g hg L (lam,x))
    (fun X Y => referenceConnectionFamily_symmetric g hg L lam x X Y) u hu a b

theorem referenceIndexedCovariantHessian_polynomial_antisymm (g : MatrixField)
    (hg : IsAdmissibleMetric g) (L lam : ℝ) (p : MvPolynomial (Fin 3) ℝ)
    (x v : R3) (a b : Fin 3) :
    referenceIndexedCovariantHessian g L lam (referenceMovingFramePolynomial g L lam p) a b (x,v) -
      referenceIndexedCovariantHessian g L lam (referenceMovingFramePolynomial g L lam p) b a (x,v) =
        referenceMovingFramePolynomial g L lam
          (referenceHorizontalCurvaturePolynomial g L lam x
            (referenceMetricGramFrame g L (lam,x)) a b p) (x,v) := by
  rw [referenceIndexedCovariantHessian_antisymm g hg L lam _
    (contDiff_referenceMovingFramePolynomial g hg L lam p) x v a b]
  have h := fderiv_referenceMovingFramePolynomial_vertical_curvature g hg L lam x v a b p
  have hc : (fun i => movingFrameCoordinate
      (metricOperatorField (referenceMetric (dilatedMetric g lam) L))
      (fun y => referenceMetricGramFrame g L (lam,y)) i (x,v)) =
      metricFrameCoordinates (metricOperatorField (referenceMetric (dilatedMetric g lam) L) x)
        (referenceMetricGramFrame g L (lam,x)) v := by
    funext i
    exact (metricFrameCoordinates_apply _ _ _ i).symm
  simpa only [referenceMovingFramePolynomial,movingFramePolynomial,hc] using h

end OAI.AnisotropicCalderon.IndexedCovariantCurvature
