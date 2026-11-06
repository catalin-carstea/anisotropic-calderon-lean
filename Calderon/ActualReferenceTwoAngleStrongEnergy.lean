import Calderon.NativeCoefficientStrongDriftEnergy
import Calderon.ActualReferenceTwoAngleStrongOperator

/-! Exact original tested energy root, partitioned unchanged.
Upfront: high-degree-rotation-author-oct15-v001/
PARTITION-two-angle-strong-tested-energy-v073.md. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


lemma referenceTwoAngleOrdinaryStrongFamily_energy
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (U : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (TauCeti.Wkp.value 0
        (referenceTwoAngleOrdinaryStrongFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t U)) v =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
      (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x))
      0 (TauCeti.Wkp.firstOrder 1 U) (v : BallH1) := by
  have h := referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData i j k l
  have he := principal_add_fullDriftMultiplierSum_energy hcalc
    (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t)
    (fun d => referenceTwoAngleDriftJetsFamily g L y0 Φ B ε C ρ H a w hData 1 i j k l d t)
    (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x))
    (h.1.comp (contDiff_const.prodMk contDiff_id))
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _) (h.2 t)
    (fun d x => coefficientValue_referenceTwoAngleDriftJetsFamily
      g L y0 Φ B ε C ρ H a w hData 1 i j k l d t x) U v
  rw [coefficientMatrixField_referenceTwoAnglePrincipalJetsFamily] at he
  exact he


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleOrdinaryStrongFamily_energy
