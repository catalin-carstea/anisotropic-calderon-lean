import Calderon.OrthogonalPolynomialLinearPullback
import Calderon.NativePolynomialAnalyticLaplacian
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace OAI.AnisotropicCalderon.SphereHarmonic
open GreenRadialTrace SmoothAngularCasimir AngularPolynomial

/-! Expanded before source in EXPANSION-orthogonal-polynomial-harmonic-preservation-v001.json.
Actual harmonic block invariance is proved, not supplied as a premise. -/

lemma polynomialEvaluation_orthogonalPullback (e : R3 ≃ₗᵢ[ℝ] R3)
    (p : MvPolynomial (Fin 3) ℝ) :
    polynomialEvaluation (polynomialOrthogonalPullback e p) = polynomialEvaluation p ∘ e := by
  funext x
  exact polynomialOrthogonalPullback_eval e p (euclideanCoordinates x)

lemma laplacian_polynomialOrthogonalPullback (e : R3 ≃ₗᵢ[ℝ] R3)
    (p : MvPolynomial (Fin 3) ℝ) :
    AngularPolynomial.laplacian (polynomialOrthogonalPullback e p) =
      polynomialOrthogonalPullback e (AngularPolynomial.laplacian p) := by
  have hEval : polynomialEvaluation (AngularPolynomial.laplacian (polynomialOrthogonalPullback e p)) =
      polynomialEvaluation (polynomialOrthogonalPullback e (AngularPolynomial.laplacian p)) := by
    calc
      _ = Laplacian.laplacian (polynomialEvaluation (polynomialOrthogonalPullback e p)) :=
        (analyticLaplacian_polynomialEvaluation _).symm
      _ = Laplacian.laplacian (polynomialEvaluation p ∘ e) := by
        rw [polynomialEvaluation_orthogonalPullback]
      _ = Laplacian.laplacian (polynomialEvaluation p) ∘ e :=
        TauCeti.laplacian_comp_linearIsometryEquiv_right e _
      _ = polynomialEvaluation (AngularPolynomial.laplacian p) ∘ e := by
        rw [analyticLaplacian_polynomialEvaluation]
      _ = _ := (polynomialEvaluation_orthogonalPullback e _).symm
  apply MvPolynomial.funext
  intro x
  exact congrFun hEval (WithLp.toLp 2 x)

lemma polynomialOrthogonalPullback_harmonicHomogeneous
    (e : R3 ≃ₗᵢ[ℝ] R3) (k : ℕ) (p : MvPolynomial (Fin 3) ℝ)
    (hp : p ∈ harmonicHomogeneous k) : polynomialOrthogonalPullback e p ∈ harmonicHomogeneous k := by
  refine ⟨polynomialOrthogonalPullback_isHomogeneous e p k hp.1,?_⟩
  rw [laplacian_polynomialOrthogonalPullback,hp.2,map_zero]

lemma sphereL2OrthogonalPullback_polynomialSphereL2 (e : R3 ≃ₗᵢ[ℝ] R3)
    (p : MvPolynomial (Fin 3) ℝ) :
    sphereL2OrthogonalPullback e (polynomialSphereL2 p) =
      polynomialSphereL2 (polynomialOrthogonalPullback e p) := by
  change sphereL2OrthogonalPullback e (ContinuousMap.toLp 2 sphereProbability ℝ (polynomialSphere p)) =
    ContinuousMap.toLp 2 sphereProbability ℝ (polynomialSphere (polynomialOrthogonalPullback e p))
  rw [sphereL2OrthogonalPullback_toLp]
  apply congrArg (ContinuousMap.toLp 2 sphereProbability ℝ)
  ext «ω»
  exact (polynomialOrthogonalPullback_eval e p («ω».val : Fin 3 → ℝ)).symm

lemma sphereL2OrthogonalPullback_mem_harmonicSphereSubspace
    (e : R3 ≃ₗᵢ[ℝ] R3) (k : ℕ) (u : SphereL2) (hu : u ∈ harmonicSphereSubspace k) :
    sphereL2OrthogonalPullback e u ∈ harmonicSphereSubspace k := by
  rcases hu with ⟨p,hp,rfl⟩
  rw [sphereL2OrthogonalPullback_polynomialSphereL2]
  exact ⟨polynomialOrthogonalPullback e p,polynomialOrthogonalPullback_harmonicHomogeneous e k p hp,rfl⟩

def harmonicSphereOrthogonalPullback (e : R3 ≃ₗᵢ[ℝ] R3) (k : ℕ) :
    harmonicSphereSubspace k →ₗᵢ[ℝ] harmonicSphereSubspace k where
  toFun u := ⟨sphereL2OrthogonalPullback e u,
    sphereL2OrthogonalPullback_mem_harmonicSphereSubspace e k u u.2⟩
  map_add' u v := Subtype.ext ((sphereL2OrthogonalPullback e).map_add u v)
  map_smul' c u := Subtype.ext ((sphereL2OrthogonalPullback e).map_smul c u)
  norm_map' u := (sphereL2OrthogonalPullback e).norm_map u

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.polynomialEvaluation_orthogonalPullback
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.laplacian_polynomialOrthogonalPullback
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.polynomialOrthogonalPullback_harmonicHomogeneous
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereL2OrthogonalPullback_polynomialSphereL2
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereL2OrthogonalPullback_mem_harmonicSphereSubspace
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.harmonicSphereOrthogonalPullback
