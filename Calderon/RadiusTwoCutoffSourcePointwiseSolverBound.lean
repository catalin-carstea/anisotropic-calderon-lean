import Calderon.RadiusTwoNormalizedCutoffSourceOrderLift
import Calderon.RadiusTwoNativeZeroDilationConstruction

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge ConnectionError DirichletFamily
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup
  TauCeti.W1p0.instInnerProductSpace

theorem exists_radiusTwoNormalizedCutoffSource_order_bound_of_solver
    (hcalc : FixedSobolevCalculus) (k : ℕ) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (C : ℝ) (hC : 0 ≤ C)
    (hSolve : ∀ (f : BallSobolev k) (z : BallH1Zero),
      TauCeti.PDE.IsWeakSolutionDirichlet
        (principalCoefficient (enlargedBallNormalizedMetric g 2))
        (0 : R3 → R3) (0 : R3 → ℝ) (TauCeti.Wkp.value k f) z →
      ∃ V : BallSobolev (k+2), TauCeti.Wkp.firstOrder (k+1) V = (z : BallH1) ∧
        ‖V‖ ≤ C * (‖z‖ + ‖f‖))
    (η : SmoothData) (w : RadiusTwoH1Zero) (U : BallSobolev (k+1))
    (hU : TauCeti.Wkp.firstOrder k U = (radiusTwoNativeZeroDilation w : BallH1)) :
    ∃ V : BallSobolev (k+2), TauCeti.Wkp.firstOrder (k+1) V =
        (radiusTwoNativeZeroDilation (radiusTwoSourceSolution g hg
          (radiusTwoFixedRowCutoffForcingLp g hg η (w : RadiusTwoH1))) : BallH1) ∧
      ‖V‖ ≤ C * (3 * ‖radiusTwoSourceSolution g hg
          (radiusTwoFixedRowCutoffForcingLp g hg η (w : RadiusTwoH1))‖ +
        ‖radiusTwoNormalizedCutoffOrderForcingL hcalc k g hg η‖ * ‖U‖) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "KS_POINTWISE_BODY"
    out.flush
  let f : BallSobolev k := radiusTwoNormalizedCutoffOrderForcingL hcalc k g hg η U
  let v : RadiusTwoH1Zero := radiusTwoSourceSolution g hg
    (radiusTwoFixedRowCutoffForcingLp g hg η (w : RadiusTwoH1))
  let z : BallH1Zero := radiusTwoNativeZeroDilation v
  have hWeak := radiusTwoNormalizedCutoffSource_order_weak_equation hcalc k g hg η w U hU
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "KS_POINTWISE_WEAK_EQUATION"
    out.flush
  have hResult := hSolve f z hWeak
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "KS_POINTWISE_SOLVER_APPLICATION"
    out.flush
  rcases hResult with ⟨V,hV,hNorm⟩
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "KS_POINTWISE_SOLVER_RESULT"
    out.flush
  have hDilation : ‖z‖ ≤ 3 * ‖v‖ := by
    calc
      ‖z‖ ≤ ‖radiusTwoNativeZeroDilation‖ * ‖v‖ := radiusTwoNativeZeroDilation.le_opNorm v
      _ ≤ 3 * ‖v‖ := mul_le_mul_of_nonneg_right norm_radiusTwoNativeZeroDilation_le_three (norm_nonneg v)
  have hForce : ‖f‖ ≤ ‖radiusTwoNormalizedCutoffOrderForcingL hcalc k g hg η‖ * ‖U‖ :=
    (radiusTwoNormalizedCutoffOrderForcingL hcalc k g hg η).le_opNorm U
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "KS_POINTWISE_NORMS_READY"
    out.flush
  refine ⟨V,hV,?_⟩
  exact hNorm.trans (mul_le_mul_of_nonneg_left (add_le_add hDilation hForce) hC)

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoNormalizedCutoffSource_order_bound_of_solver
