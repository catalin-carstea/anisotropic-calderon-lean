import Calderon.GreenRadialTrace
import ComparatorChallenges.AnisotropicCalderon
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
namespace OAI.AnisotropicCalderon.GreenRadialTrace
open MvPolynomial AngularPolynomial

def euclideanCoordinates : R3 ≃L[ℝ] (Fin 3 → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)

def polynomialEvaluation (p : MvPolynomial (Fin 3) ℝ) (x : R3) : ℝ :=
  eval (euclideanCoordinates x) p

theorem hasFDerivAt_polynomialEvaluation (p : MvPolynomial (Fin 3) ℝ) (x : R3) :
    HasFDerivAt (polynomialEvaluation p)
      ((polynomialFDeriv p (euclideanCoordinates x)).comp
        euclideanCoordinates.toContinuousLinearMap) x := by
  exact (hasFDerivAt_eval p (euclideanCoordinates x)).comp x
    euclideanCoordinates.toContinuousLinearMap.hasFDerivAt

theorem fderiv_polynomialEvaluation_apply (p : MvPolynomial (Fin 3) ℝ) (x v : R3) :
    fderiv ℝ (polynomialEvaluation p) x v =
      ∑ i : Fin 3, v i * polynomialEvaluation (pderiv i p) x := by
  rw [(hasFDerivAt_polynomialEvaluation p x).fderiv]
  exact polynomialFDeriv_apply p (euclideanCoordinates x) (euclideanCoordinates v)

theorem fderiv_polynomialEvaluation_eq_coordinate (p : MvPolynomial (Fin 3) ℝ) (x v : R3) :
    fderiv ℝ (polynomialEvaluation p) x v =
      fderiv ℝ (fun z : Fin 3 → ℝ => eval z p)
        (euclideanCoordinates x) (euclideanCoordinates v) := by
  rw [(hasFDerivAt_polynomialEvaluation p x).fderiv,
    (hasFDerivAt_eval p (euclideanCoordinates x)).fderiv]
  rfl

theorem d_polynomialEvaluation (p : MvPolynomial (Fin 3) ℝ) (x : R3) (i : Fin 3) :
    d (polynomialEvaluation p) x i = polynomialEvaluation (pderiv i p) x := by
  classical
  simp [d, fderiv_polynomialEvaluation_apply, PiLp.single_apply]

def euclideanLaplacian (u : R3 → ℝ) (x : R3) : ℝ :=
  ∑ i : Fin 3, d (fun y => d u y i) x i

theorem euclideanLaplacian_polynomialEvaluation (p : MvPolynomial (Fin 3) ℝ) (x : R3) :
    euclideanLaplacian (polynomialEvaluation p) x = polynomialEvaluation (laplacian p) x := by
  classical
  simp only [euclideanLaplacian, d_polynomialEvaluation]
  simp only [polynomialEvaluation, laplacian, map_sum]

theorem euclideanCoordinates_sphere {x : R3} (hx : ‖x‖ = 1) :
    ∑ i : Fin 3, (euclideanCoordinates x i)^2 = 1 := by
  have hn := EuclideanSpace.real_norm_sq_eq x
  simpa [euclideanCoordinates, hx] using hn.symm

theorem euclideanLaplacian_driftFirstVariation {k : ℕ}
    {p : MvPolynomial (Fin 3) ℝ} (hp : p.IsHomogeneous k) (hΔ : laplacian p = 0)
    (b x : R3) :
    euclideanLaplacian (polynomialEvaluation (driftFirstVariation k (euclideanCoordinates b) p)) x =
      -fderiv ℝ (polynomialEvaluation p) x b := by
  rw [euclideanLaplacian_polynomialEvaluation]
  change eval (euclideanCoordinates x)
    (laplacian (driftFirstVariation k (euclideanCoordinates b) p)) = _
  rw [← cartesianLaplacian_eval,
    cartesianLaplacian_driftFirstVariation hp hΔ]
  rw [fderiv_polynomialEvaluation_eq_coordinate]

theorem polynomialEvaluation_driftFirstVariation_sphere (k : ℕ) (b x : R3)
    (p : MvPolynomial (Fin 3) ℝ) (hx : ‖x‖ = 1) :
    polynomialEvaluation (driftFirstVariation k (euclideanCoordinates b) p) x = 0 :=
  eval_driftFirstVariation_eq_zero k _ p _ (euclideanCoordinates_sphere hx)

theorem fderiv_polynomialEvaluation_driftFirstVariation_sphere {k : ℕ} (hk : 1 ≤ k)
    (b x : R3) (p : MvPolynomial (Fin 3) ℝ) (hx : ‖x‖ = 1) :
    fderiv ℝ (polynomialEvaluation (driftFirstVariation k (euclideanCoordinates b) p)) x x =
      -(2 * (k : ℝ) + 1)⁻¹ * fderiv ℝ (polynomialEvaluation p) x b := by
  rw [fderiv_polynomialEvaluation_eq_coordinate,
    fderiv_polynomialEvaluation_eq_coordinate]
  exact fderiv_driftFirstVariation_three_at_sphere hk (euclideanCoordinates b) p _
    (euclideanCoordinates_sphere hx)

theorem fderiv_polynomialEvaluation_driftFirstVariation_degree_one
    (b x : R3) (j : Fin 3) (hx : ‖x‖ = 1) :
    fderiv ℝ (polynomialEvaluation
      (driftFirstVariation 1 (euclideanCoordinates b) (X j))) x x = -(b j) / 3 := by
  rw [fderiv_polynomialEvaluation_eq_coordinate]
  exact fderiv_driftFirstVariation_three_degree_one (euclideanCoordinates b) _ j
    (euclideanCoordinates_sphere hx)

end OAI.AnisotropicCalderon.GreenRadialTrace
#print axioms OAI.AnisotropicCalderon.GreenRadialTrace.euclideanLaplacian_driftFirstVariation
#print axioms OAI.AnisotropicCalderon.GreenRadialTrace.polynomialEvaluation_driftFirstVariation_sphere
#print axioms OAI.AnisotropicCalderon.GreenRadialTrace.fderiv_polynomialEvaluation_driftFirstVariation_sphere
#print axioms OAI.AnisotropicCalderon.GreenRadialTrace.fderiv_polynomialEvaluation_driftFirstVariation_degree_one
