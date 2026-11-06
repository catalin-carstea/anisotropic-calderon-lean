import Calderon.ActualReferenceRotationAdjointMassFamily
import Calderon.ActualReferenceTwoAngleCoefficientJets
import Calderon.NativeFormalAdjointOrthogonalCoefficients
/-! Literal negative divergence retained. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SmoothSphereRotation
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceTwoAngleAdjointMassFunction (i j k l : Fin 3)
    (q : (ℝ × (ℝ × (ℝ × (R3 × ℝ)))) × R3) : ℝ :=
  referenceRotationAdjointMassFunction g L Φ H w k l
    (q.1.2,coordinateRotation i j q.1.1 q.2)

include hData

lemma contDiff_referenceTwoAngleAdjointMassFunction (i j k l : Fin 3) :
    ContDiff ℝ ∞ (referenceTwoAngleAdjointMassFunction g L Φ H w i j k l) :=
  (contDiff_referenceRotationAdjointMassFunction g L y0 Φ B ε C ρ H a w hData k l).comp
    (contDiff_coordinateRotationSourceMap i j)

lemma referenceTwoAngleAdjointMassFunction_zero_outside (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (x : R3) (hx : x ∉ closedBall (0 : R3) 3) :
    referenceTwoAngleAdjointMassFunction g L Φ H w i j k l (t,x) = 0 :=
  referenceRotationAdjointMassFunction_zero_outside g L y0 Φ B ε C ρ H a w hData k l t.2
    (coordinateRotation i j t.1 x) (coordinateRotation_outside_closedBall i j t.1 x 3 hx)

def referenceTwoAngleAdjointMassJetsFamily (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) : SmoothCoefficientJets 1 :=
  commonSupportCoefficientFamily 1 (referenceTwoAngleAdjointMassFunction g L Φ H w i j k l)
    (contDiff_referenceTwoAngleAdjointMassFunction g L y0 Φ B ε C ρ H a w hData i j k l)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceTwoAngleAdjointMassFunction_zero_outside g L y0 Φ B ε C ρ H a w hData i j k l) t

lemma coefficientValue_referenceTwoAngleAdjointMassJetsFamily (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (x : R3) :
    coefficientValue 1 (referenceTwoAngleAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData i j k l t) x =
      -nativeSupportedDriftDivergence
        (fun y => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,y)) x := by
  let beta : R3 → R3 := fun y => coordinateRotationDriftFamily k l
    (conformalReferenceWeightedFramedDrift g L Φ H w) (t.2,y)
  let e : R3 ≃ₗᵢ[ℝ] R3 := coordinateRotationIsometry i j t.1
  have hbeta : ContDiff ℝ ∞ beta :=
    (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData k l).1.comp
      (contDiff_const.prodMk contDiff_id)
  have hField : (fun y => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,y)) =
      orthogonalDriftCoefficient e beta :=
    funext (coordinateRotationDriftFamily_eq_orthogonal i j
      (coordinateRotationDriftFamily k l (conformalReferenceWeightedFramedDrift g L Φ H w)) t.1 t.2)
  have hDiv : nativeSupportedDriftDivergence
      (fun y => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,y)) x =
      nativeSupportedDriftDivergence beta (e x) :=
    (congrArg (fun b : R3 → R3 => nativeSupportedDriftDivergence b x) hField).trans
      (nativeSupportedDriftDivergence_orthogonalDriftCoefficient e beta hbeta x)
  have hOldValue := coefficientValue_commonSupportCoefficientFamily 1
    (referenceRotationAdjointMassFunction g L Φ H w k l)
    (contDiff_referenceRotationAdjointMassFunction g L y0 Φ B ε C ρ H a w hData k l)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceRotationAdjointMassFunction_zero_outside g L y0 Φ B ε C ρ H a w hData k l) t.2 (e x)
  have hOldNative := coefficientValue_referenceRotationAdjointMassJetsFamily
    g L y0 Φ B ε C ρ H a w hData k l t.2 (e x)
  have hMass : referenceTwoAngleAdjointMassFunction g L Φ H w i j k l (t,x) =
      -nativeSupportedDriftDivergence beta (e x) := hOldValue.symm.trans hOldNative
  have hValue := coefficientValue_commonSupportCoefficientFamily 1
    (referenceTwoAngleAdjointMassFunction g L Φ H w i j k l)
    (contDiff_referenceTwoAngleAdjointMassFunction g L y0 Φ B ε C ρ H a w hData i j k l)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceTwoAngleAdjointMassFunction_zero_outside g L y0 Φ B ε C ρ H a w hData i j k l) t x
  exact hValue.trans (hMass.trans (congrArg (fun z : ℝ => -z) hDiv.symm))

lemma contDiff_referenceTwoAngleAdjointMassClosedJets (i j k l : Fin 3) :
    ContDiff ℝ ∞ (fun t => smoothCoefficientClosureInclusionL 1
      (referenceTwoAngleAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData i j k l t)) :=
  contDiff_commonSupportClosedCoefficientFamily 1 (referenceTwoAngleAdjointMassFunction g L Φ H w i j k l)
    (contDiff_referenceTwoAngleAdjointMassFunction g L y0 Φ B ε C ρ H a w hData i j k l)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceTwoAngleAdjointMassFunction_zero_outside g L y0 Φ B ε C ρ H a w hData i j k l)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointMassFunction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTwoAngleAdjointMassFunction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointMassFunction_zero_outside
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointMassJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_referenceTwoAngleAdjointMassJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTwoAngleAdjointMassClosedJets
