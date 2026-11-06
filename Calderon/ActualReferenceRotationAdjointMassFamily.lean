import Calderon.ActualReferenceAdjointMassFamily
import Calderon.ActualReferenceRotationCoefficientJets
import Calderon.NativeFormalAdjointOrthogonalCoefficients
set_option autoImplicit false
set_option maxSynthPendingDepth 10
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

def referenceRotationAdjointMassFunction (i j : Fin 3)
    (q : (ℝ × (ℝ × (R3 × ℝ))) × R3) : ℝ :=
  referenceAdjointMassFunction g L Φ H w
    (q.1.2,coordinateRotation i j q.1.1 q.2)

include hData
lemma contDiff_referenceRotationAdjointMassFunction (i j : Fin 3) :
    ContDiff ℝ ∞ (referenceRotationAdjointMassFunction g L Φ H w i j) :=
  (contDiff_referenceAdjointMassFunction g L y0 Φ B ε C ρ H a w hData).comp
    (contDiff_coordinateRotationSourceMap i j)

lemma referenceRotationAdjointMassFunction_zero_outside (i j : Fin 3)
    (t : ℝ × (ℝ × (R3 × ℝ))) (x : R3) (hx : x ∉ closedBall (0 : R3) 3) :
    referenceRotationAdjointMassFunction g L Φ H w i j (t,x) = 0 :=
  referenceAdjointMassFunction_zero_outside g L y0 Φ B ε C ρ H a w hData t.2
    (coordinateRotation i j t.1 x) (coordinateRotation_outside_closedBall i j t.1 x 3 hx)

def referenceRotationAdjointMassJetsFamily (i j : Fin 3)
    (t : ℝ × (ℝ × (R3 × ℝ))) : SmoothCoefficientJets 1 :=
  commonSupportCoefficientFamily 1 (referenceRotationAdjointMassFunction g L Φ H w i j)
    (contDiff_referenceRotationAdjointMassFunction g L y0 Φ B ε C ρ H a w hData i j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceRotationAdjointMassFunction_zero_outside g L y0 Φ B ε C ρ H a w hData i j) t

lemma coefficientValue_referenceRotationAdjointMassJetsFamily (i j : Fin 3)
    (t : ℝ × (ℝ × (R3 × ℝ))) (x : R3) :
    coefficientValue 1 (referenceRotationAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData i j t) x =
      -nativeSupportedDriftDivergence
        (fun y => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,y)) x := by
  let beta : R3 → R3 := fun y => conformalReferenceWeightedFramedDrift g L Φ H w (t.2,y)
  let e : R3 ≃ₗᵢ[ℝ] R3 := coordinateRotationIsometry i j t.1
  have hbeta : ContDiff ℝ ∞ beta :=
    (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1.comp
      (contDiff_const.prodMk contDiff_id)
  have hField : (fun y => coordinateRotationDriftFamily i j
      (conformalReferenceWeightedFramedDrift g L Φ H w) (t,y)) = orthogonalDriftCoefficient e beta :=
    funext (fun y => coordinateRotationDriftFamily_eq_orthogonal i j
      (conformalReferenceWeightedFramedDrift g L Φ H w) t.1 t.2 y)
  have hDiv : nativeSupportedDriftDivergence
      (fun y => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,y)) x =
      nativeSupportedDriftDivergence beta (e x) :=
    (congrArg (fun b : R3 → R3 => nativeSupportedDriftDivergence b x) hField).trans
      (nativeSupportedDriftDivergence_orthogonalDriftCoefficient e beta hbeta x)
  have hValue := coefficientValue_commonSupportCoefficientFamily 1
    (referenceRotationAdjointMassFunction g L Φ H w i j)
    (contDiff_referenceRotationAdjointMassFunction g L y0 Φ B ε C ρ H a w hData i j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceRotationAdjointMassFunction_zero_outside g L y0 Φ B ε C ρ H a w hData i j) t x
  have hMass : referenceRotationAdjointMassFunction g L Φ H w i j (t,x) =
      -nativeSupportedDriftDivergence beta (e x) :=
    congrArg (fun r : ℝ => -r)
      (referenceWeightedDriftDivergence_eq_native g L y0 Φ B ε C ρ H a w hData t.2 (e x))
  exact hValue.trans (hMass.trans (congrArg (fun r : ℝ => -r) hDiv.symm))

lemma contDiff_referenceRotationAdjointMassClosedJets (i j : Fin 3) :
    ContDiff ℝ ∞ (fun t => smoothCoefficientClosureInclusionL 1
      (referenceRotationAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData i j t)) :=
  contDiff_commonSupportClosedCoefficientFamily 1 (referenceRotationAdjointMassFunction g L Φ H w i j)
    (contDiff_referenceRotationAdjointMassFunction g L y0 Φ B ε C ρ H a w hData i j)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceRotationAdjointMassFunction_zero_outside g L y0 Φ B ε C ρ H a w hData i j)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointMassFunction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationAdjointMassFunction
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointMassFunction_zero_outside
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointMassJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_referenceRotationAdjointMassJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationAdjointMassClosedJets
