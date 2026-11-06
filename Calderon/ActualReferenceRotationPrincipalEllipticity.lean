import Calderon.ActualReferenceRotationCoefficientJets
import Calderon.ActualReferencePrincipalGlobalEllipticity
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError MetricOperator SmoothSphereRotation

lemma matrixBilinearForm_orthogonalPrincipalCoefficient
    (e : R3 ≃ₗᵢ[ℝ] R3) (a : MatrixField) (x η ξ : R3) :
    TauCeti.PDE.matrixBilinearForm (orthogonalPrincipalCoefficient e a x) η ξ =
      TauCeti.PDE.matrixBilinearForm (a (e x)) (e η) (e ξ) := by
  have hMap : matrixOperatorMap (orthogonalPrincipalCoefficient e a x) ξ =
      e.symm (matrixOperatorMap (a (e x)) (e ξ)) := by
    change (operatorMatrixMap _).toEuclideanLin ξ = _
    rw [operatorMatrixMap_apply]
    rfl
  exact (matrixBilinearForm_eq_matrixOperator_inner _ ξ η).trans
    ((congrArg (fun v : R3 => ⟪v,η⟫_ℝ) hMap).trans
      ((e.symm.inner_map_eq_flip (matrixOperatorMap (a (e x)) (e ξ)) η).trans
        (matrixBilinearForm_eq_matrixOperator_inner (a (e x)) (e ξ) (e η)).symm))

lemma uniformlyEllipticOn_orthogonalPrincipalCoefficient (e : R3 ≃ₗᵢ[ℝ] R3)
    (a : MatrixField) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) a lam Lam) :
    TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (orthogonalPrincipalCoefficient e a) lam Lam := by
  refine ⟨hUE.pos,hUE.le,?_⟩
  intro x hx
  have hmem : x ∈ e ⁻¹' (ballOpens : Set R3) := by
    rw [orthogonal_preimage_unitBall e]
    exact hx
  have hEx : e x ∈ (ballOpens : Set R3) := hmem
  constructor
  · intro ξ
    have hQuad : (orthogonalPrincipalCoefficient e a x).toQuadraticForm' ξ =
        (a (e x)).toQuadraticForm' (e ξ) :=
      (TauCeti.PDE.matrixBilinearForm_self _ ξ).symm.trans
        ((matrixBilinearForm_orthogonalPrincipalCoefficient e a x ξ ξ).trans
          (TauCeti.PDE.matrixBilinearForm_self _ (e ξ)))
    have hLower : lam * ‖ξ‖^2 ≤ (a (e x)).toQuadraticForm' (e ξ) := by
      simpa only [e.norm_map] using hUE.lower_bound hEx (e ξ)
    exact hLower.trans_eq hQuad.symm
  · intro η ξ
    have hCoeff : η ⬝ᵥ (orthogonalPrincipalCoefficient e a x *ᵥ ξ) =
        (e η) ⬝ᵥ (a (e x) *ᵥ e ξ) :=
      (TauCeti.PDE.matrixBilinearForm_apply _ η ξ).symm.trans
        ((matrixBilinearForm_orthogonalPrincipalCoefficient e a x η ξ).trans
          (TauCeti.PDE.matrixBilinearForm_apply _ (e η) (e ξ)))
    have hUpper : |(e η) ⬝ᵥ (a (e x) *ᵥ e ξ)| ≤ Lam * ‖η‖ * ‖ξ‖ := by
      simpa only [e.norm_map] using hUE.upper_bound hEx (e η) (e ξ)
    exact (congrArg (fun r : ℝ => |r|) hCoeff).le.trans hUpper

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hData

lemma exists_referenceRotationPrincipal_uniformlyElliptic_on_compact
    (q : Set (ℝ × (R3 × ℝ))) (hq : IsCompact q) :
    ∃ lam Lam : ℝ, ∀ i j : Fin 3, ∀ θ : ℝ, ∀ p ∈ q,
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
        (fun x => coordinateRotationPrincipalFamily i j a ((θ,p),x)) lam Lam := by
  obtain ⟨lam,Lam,hUE⟩ := exists_referencePrincipal_uniformlyElliptic_on_compact
    g L y0 Φ B ε C ρ H a w hData q hq
  refine ⟨lam,Lam,?_⟩
  intro i j θ p hp
  have hRot := uniformlyEllipticOn_orthogonalPrincipalCoefficient
    (coordinateRotationIsometry i j θ) (fun x => a (p,x)) lam Lam (hUE p hp)
  have hField : (fun x => coordinateRotationPrincipalFamily i j a ((θ,p),x)) =
      orthogonalPrincipalCoefficient (coordinateRotationIsometry i j θ) (fun x => a (p,x)) :=
    funext (coordinateRotationPrincipalFamily_eq_orthogonal i j a θ p)
  exact Eq.mp (congrArg (fun A : MatrixField =>
    TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) A lam Lam) hField.symm) hRot

lemma exists_referenceRotationPrincipal_uniformlyElliptic
    (i j : Fin 3) (θ : ℝ) (p : ℝ × (R3 × ℝ)) :
    ∃ lam Lam : ℝ, TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (fun x => coordinateRotationPrincipalFamily i j a ((θ,p),x)) lam Lam := by
  obtain ⟨lam,Lam,hUE⟩ := exists_referenceRotationPrincipal_uniformlyElliptic_on_compact
    g L y0 Φ B ε C ρ H a w hData {p} isCompact_singleton
  exact ⟨lam,Lam,hUE i j θ p (mem_singleton p)⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.matrixBilinearForm_orthogonalPrincipalCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.uniformlyEllipticOn_orthogonalPrincipalCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceRotationPrincipal_uniformlyElliptic_on_compact
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceRotationPrincipal_uniformlyElliptic
