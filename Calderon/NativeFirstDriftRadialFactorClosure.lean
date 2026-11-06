import Calderon.NativeRadialFactorZeroClosure
import Calderon.RelativeNativeFirstVariation

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory MvPolynomial
open scoped ContDiff ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError

/-! Closure for the explicit polynomial corrector, without a general zero-trace converse. -/
lemma polynomialEval_radiusSq_eq_norm_sq (x : R3) :
    eval (polynomialCoordinateMap x) (AngularPolynomial.radiusSq : MvPolynomial (Fin 3) ℝ) =
      ‖x‖^2 := by
  simp only [AngularPolynomial.radiusSq,map_sum,map_pow,eval_X,polynomialCoordinateMap_apply]
  exact (EuclideanSpace.real_norm_sq_eq x).symm

lemma smoothSobolev_driftFirstVariation_mem_zero_radialFactor
    (k : ℕ) (d : R3) (p : MvPolynomial (Fin 3) ℝ) :
    smoothSobolev (smoothPolynomialData
      (GreenRadialTrace.driftFirstVariation k (polynomialCoordinateMap d) p)) ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  let Q : MvPolynomial (Fin 3) ℝ :=
    C ((4 * ((k-1 : ℕ) : ℝ) + 2 * (Fintype.card (Fin 3) : ℝ))⁻¹) *
      GreenRadialTrace.driftDerivative (polynomialCoordinateMap d) p
  have hdata : smoothPolynomialData
      (GreenRadialTrace.driftFirstVariation k (polynomialCoordinateMap d) p) =
      (⟨fun x : R3 => (1-‖x‖^2)*(smoothPolynomialData Q).1 x,
        (contDiff_const.sub (contDiff_norm_sq ℝ)).mul (smoothPolynomialData Q).2⟩ : SmoothData) := by
    apply Subtype.ext
    funext x
    change eval (polynomialCoordinateMap x)
        (GreenRadialTrace.driftFirstVariation k (polynomialCoordinateMap d) p) =
      (1-‖x‖^2) * eval (polynomialCoordinateMap x) Q
    simp only [GreenRadialTrace.driftFirstVariation,AngularPolynomial.radialFirstVariation,
      Q,map_mul,map_sub,map_one,eval_C,polynomialEval_radiusSq_eq_norm_sq]
    ring
  rw [hdata]
  exact smoothSobolev_radialFactor_mem_zero (smoothPolynomialData Q)

lemma firstOrder_polynomialBallSobolev_driftFirstVariation_mem_zero_radialFactor
    (s k : ℕ) (d : R3) (p : MvPolynomial (Fin 3) ℝ) :
    TauCeti.Wkp.firstOrder (s+1)
      (polynomialBallSobolev (s+2) (GreenRadialTrace.driftFirstVariation k
        (polynomialCoordinateMap d) p)) ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  rw [firstOrder_polynomialBallSobolev]
  exact smoothSobolev_driftFirstVariation_mem_zero_radialFactor k d p

lemma polynomialBallSobolev_driftFirstVariation_mem_strongDirichlet_radialFactor
    (s k : ℕ) (d : R3) (p : MvPolynomial (Fin 3) ℝ) :
    polynomialBallSobolev (s+2) (GreenRadialTrace.driftFirstVariation k
      (polynomialCoordinateMap d) p) ∈ strongDirichletSubmodule s :=
  (mem_strongDirichletSubmodule s _).mpr
    (firstOrder_polynomialBallSobolev_driftFirstVariation_mem_zero_radialFactor s k d p)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
