import Calderon.StrongDerivativeValues
import Calderon.StrongOperatorTyped

set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

def coefficientMatrixField (r : ℕ) (F : SmoothCoefficientMatrix r) :
    R3 → Matrix (Fin 3) (Fin 3) ℝ :=
  fun x i j => coefficientValue r (F i j) x

theorem strongCoefficientOperator_forcing_sum (hcalc : FixedSobolevCalculus)
    (s : ℕ) (F : SmoothCoefficientMatrix (s + 2)) (u : StrongDirichletSpace s)
    (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
      (strongDirichletOperator hcalc s F u)) v =
      ∑ i : Fin 3, ∑ j : Fin 3,
        ⟪TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) (s + 1) (coefficientMultiplier hcalc (s + 1) (F i j)
          (strongCoordinateDerivativeL hcalc s j u)),
          unitBallCoordinateGradientL i (v : BallH1)⟫_ℝ := by
  rw [TauCeti.PDE.dirichletForcing_apply, strongDirichletOperator_apply]
  change ⟪TauCeti.Wkp.valueL s (-∑ i, ∑ j,
    unitBallCoordinateDerivativeL hcalc s i (coefficientMultiplier hcalc (s + 1) (F i j)
      (strongCoordinateDerivativeL hcalc s j u))), TauCeti.W1p.value (v : BallH1)⟫_ℝ = _
  simp only [map_neg, map_sum, inner_neg_left, sum_inner, TauCeti.Wkp.valueL_apply]
  simp_rw [unitBallCoordinateDerivative_inner_integration hcalc s]
  simp only [Finset.sum_neg_distrib, neg_neg]

end OAI.AnisotropicCalderon.DirichletFamily
