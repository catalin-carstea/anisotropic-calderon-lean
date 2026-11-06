import Calderon.ConnectionField

set_option autoImplicit false
noncomputable section
open Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem coordinateConnectionField_symmetric_of_metric (Q M : E → E →L[ℝ] E)
    (hM : ContDiff ℝ ∞ M)
    (hsym : ∀ y X Z, inner ℝ (M y X) Z = inner ℝ (M y Z) X) (y X Y : E) :
    coordinateConnectionField Q M y X Y = coordinateConnectionField Q M y Y X := by
  have hD : ∀ U X Z, inner ℝ (fderiv ℝ M y U X) Z =
      inner ℝ (fderiv ℝ M y U Z) X :=
    inverse_metric_derivative_symmetric M (fderiv ℝ M y) y
      (hM.differentiable (by simp) y).hasFDerivAt
      (Eventually.of_forall (fun z => hsym z))
  simp only [coordinateConnectionField_apply]
  exact coordinateConnection_symmetric (Q y) (fderiv ℝ M y) hD X Y

theorem coordinateConnectionField_metric_compatible (Q M : E → E →L[ℝ] E)
    (hM : ContDiff ℝ ∞ M)
    (hsym : ∀ y X Z, inner ℝ (M y X) Z = inner ℝ (M y Z) X)
    (hMQ : ∀ y V, M y (Q y V) = V) (y X Y Z : E) :
    inner ℝ (M y (coordinateConnectionField Q M y X Y)) Z +
      inner ℝ (M y Y) (coordinateConnectionField Q M y X Z) =
        inner ℝ (fderiv ℝ M y X Y) Z := by
  have hD : ∀ U X Z, inner ℝ (fderiv ℝ M y U X) Z =
      inner ℝ (fderiv ℝ M y U Z) X :=
    inverse_metric_derivative_symmetric M (fderiv ℝ M y) y
      (hM.differentiable (by simp) y).hasFDerivAt
      (Eventually.of_forall (fun z => hsym z))
  simp only [coordinateConnectionField_apply]
  have h1 := coordinateConnection_koszul (Q y) (M y) (fderiv ℝ M y) (hMQ y) X Y Z
  have h2 := coordinateConnection_koszul (Q y) (M y) (fderiv ℝ M y) (hMQ y) X Z Y
  have hs := hsym y Y (coordinateConnection (Q y) (fderiv ℝ M y) X Z)
  have hd := hD X Y Z
  nlinarith
end OAI.AnisotropicCalderon.ConnectionError
