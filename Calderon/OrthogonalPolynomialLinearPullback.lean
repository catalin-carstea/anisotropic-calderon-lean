import Calderon.NativeSphereL2OrthogonalPullback
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option autoImplicit false
noncomputable section
open MvPolynomial
open scoped ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic

/-! Expanded before source in EXPANSION-orthogonal-polynomial-linear-pullback-v001.json.
This is an actual finite polynomial action; harmonic preservation is the next separate obligation. -/

def orthogonalCoordinatePolynomial (e : R3 ≃ₗᵢ[ℝ] R3) (i : Fin 3) : MvPolynomial (Fin 3) ℝ :=
  ∑ j : Fin 3, C ((e (EuclideanSpace.single j 1)) i) * X j

def polynomialOrthogonalPullback (e : R3 ≃ₗᵢ[ℝ] R3) :
    MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 3) ℝ :=
  bind₁ (orthogonalCoordinatePolynomial e)

lemma orthogonalCoordinatePolynomial_eval (e : R3 ≃ₗᵢ[ℝ] R3) (i : Fin 3) (x : Fin 3 → ℝ) :
    eval x (orthogonalCoordinatePolynomial e i) = (e (WithLp.toLp 2 x)) i := by
  have hx : (∑ j : Fin 3, x j • EuclideanSpace.single j (1 : ℝ)) = WithLp.toLp 2 x := by
    ext k
    simp [Pi.single_apply]
  rw [← hx,map_sum]
  simp only [orthogonalCoordinatePolynomial,map_sum,map_mul,eval_C,eval_X,map_smul,
    WithLp.ofLp_sum,WithLp.ofLp_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma polynomialOrthogonalPullback_eval (e : R3 ≃ₗᵢ[ℝ] R3)
    (p : MvPolynomial (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    eval x (polynomialOrthogonalPullback e p) =
      eval (fun i => (e (WithLp.toLp 2 x)) i) p := by
  change eval₂Hom (RingHom.id ℝ) x (bind₁ (orthogonalCoordinatePolynomial e) p) = _
  rw [eval₂Hom_bind₁]
  have hCoord : (fun i => eval₂Hom (RingHom.id ℝ) x (orthogonalCoordinatePolynomial e i)) =
      (fun i => (e (WithLp.toLp 2 x)) i) := by
    funext i
    exact orthogonalCoordinatePolynomial_eval e i x
  rw [hCoord]
  rfl

lemma orthogonalCoordinatePolynomial_isHomogeneous (e : R3 ≃ₗᵢ[ℝ] R3) (i : Fin 3) :
    (orthogonalCoordinatePolynomial e i).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro j hj
  exact isHomogeneous_C_mul_X _ _

lemma polynomialOrthogonalPullback_isHomogeneous (e : R3 ≃ₗᵢ[ℝ] R3)
    (p : MvPolynomial (Fin 3) ℝ) (k : ℕ) (hp : p.IsHomogeneous k) :
    (polynomialOrthogonalPullback e p).IsHomogeneous k := by
  unfold polynomialOrthogonalPullback
  change (eval₂ C (orthogonalCoordinatePolynomial e) p).IsHomogeneous k
  simpa only [coe_eval₂Hom,one_mul] using hp.eval₂ C (orthogonalCoordinatePolynomial e)
    (fun r => isHomogeneous_C (Fin 3) r) (orthogonalCoordinatePolynomial_isHomogeneous e)

lemma polynomialOrthogonalPullback_symm_apply (e : R3 ≃ₗᵢ[ℝ] R3)
    (p : MvPolynomial (Fin 3) ℝ) :
    polynomialOrthogonalPullback e.symm (polynomialOrthogonalPullback e p) = p := by
  apply MvPolynomial.funext
  intro x
  rw [polynomialOrthogonalPullback_eval,polynomialOrthogonalPullback_eval]
  have hToLp : WithLp.toLp 2 (fun i => (e.symm (WithLp.toLp 2 x)) i) =
      e.symm (WithLp.toLp 2 x) := rfl
  rw [hToLp,e.apply_symm_apply]

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.orthogonalCoordinatePolynomial
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.polynomialOrthogonalPullback
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.orthogonalCoordinatePolynomial_eval
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.polynomialOrthogonalPullback_eval
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.orthogonalCoordinatePolynomial_isHomogeneous
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.polynomialOrthogonalPullback_isHomogeneous
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.polynomialOrthogonalPullback_symm_apply
