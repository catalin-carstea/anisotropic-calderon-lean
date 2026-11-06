import Calderon.CoordinateRotationCoefficientFamily
import Calderon.ActualReferenceWeakEnergyConstruction
import Calderon.CommonSupportMatrixInverse
import Calderon.ClosedCoefficientJets

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

include hData

/-! The literal beta preserves its actual L/r scaling. No same-order boundary rotation norm
regularity. -/

lemma referenceRotationPrincipal_data (i j : Fin 3) :
    ContDiff ℝ ∞ (coordinateRotationPrincipalFamily i j a) ∧
    ∀ t x, x ∉ closedBall (0 : R3) 3 → coordinateRotationPrincipalFamily i j a (t,x) = 0 := by
  have h := jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData
  exact ⟨contDiff_coordinateRotationPrincipalFamily i j a h.1,
    coordinateRotationPrincipalFamily_zero_outside i j a 3 h.2.2.2.1⟩

lemma referenceRotationDrift_data (i j : Fin 3) :
    ContDiff ℝ ∞ (coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w)) ∧
    ∀ t x, x ∉ closedBall (0 : R3) 3 →
      coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x) = 0 := by
  have h := jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData
  exact ⟨contDiff_coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) h.1,
    coordinateRotationDriftFamily_zero_outside i j (conformalReferenceWeightedFramedDrift g L Φ H w) 3 h.2⟩

def referenceRotationPrincipalJetsFamily (r : ℕ) (i j : Fin 3)
    (t : ℝ × (ℝ × (R3 × ℝ))) : SmoothCoefficientMatrix r :=
  commonSupportMatrixFamily r (coordinateRotationPrincipalFamily i j a)
    (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).2 t

def referenceRotationDriftJetsFamily (r : ℕ) (i j l : Fin 3)
    (t : ℝ × (ℝ × (R3 × ℝ))) : SmoothCoefficientJets r :=
  commonSupportCoefficientFamily r
    (fun q => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) q l)
    ((EuclideanSpace.proj l : R3 →L[ℝ] ℝ).contDiff.comp
      (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).1)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (fun t x hx => by rw [(referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).2 t x hx]; rfl) t

lemma coefficientMatrixField_referenceRotationPrincipalJetsFamily (r : ℕ) (i j : Fin 3)
    (t : ℝ × (ℝ × (R3 × ℝ))) :
    coefficientMatrixField r (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData r i j t) =
      fun x => coordinateRotationPrincipalFamily i j a (t,x) :=
  coefficientMatrixField_commonSupportMatrixFamily r (coordinateRotationPrincipalFamily i j a)
    (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).2 t

lemma coefficientValue_referenceRotationDriftJetsFamily (r : ℕ) (i j l : Fin 3)
    (t : ℝ × (ℝ × (R3 × ℝ))) (x : R3) :
    coefficientValue r (referenceRotationDriftJetsFamily g L y0 Φ B ε C ρ H a w hData r i j l t) x =
      coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x) l :=
  coefficientValue_commonSupportCoefficientFamily r _ _ (closedBall (0 : R3) 3) (isCompact_closedBall _ _) _ t x

lemma contDiff_referenceRotationPrincipalJetFields (r : ℕ) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun t => fun k l =>
      (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData r i j t k l).val) := by
  have h := referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j
  apply contDiff_pi.mpr
  intro k
  apply contDiff_pi.mpr
  intro l
  exact contDiff_commonSupportCoefficientFamily_val r
    (fun q => coordinateRotationPrincipalFamily i j a q k l)
    (contDiff_pi.mp (contDiff_pi.mp h.1 k) l) (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (fun t x hx => by rw [h.2 t x hx]; rfl)

lemma contDiff_referenceRotationDriftJetFields (r : ℕ) (i j l : Fin 3) :
    ContDiff ℝ ∞ (fun t =>
      (referenceRotationDriftJetsFamily g L y0 Φ B ε C ρ H a w hData r i j l t).val) := by
  have h := referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j
  exact contDiff_commonSupportCoefficientFamily_val r
    (fun q => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) q l)
    ((EuclideanSpace.proj l : R3 →L[ℝ] ℝ).contDiff.comp h.1)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (fun t x hx => by rw [h.2 t x hx]; rfl)

lemma contDiff_referenceRotationPrincipalClosedJets (r : ℕ) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun t => fun k l => smoothCoefficientClosureInclusionL r
      (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData r i j t k l)) := by
  have h := referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j
  apply contDiff_pi.mpr
  intro k
  apply contDiff_pi.mpr
  intro l
  exact contDiff_commonSupportClosedCoefficientFamily r
    (fun q => coordinateRotationPrincipalFamily i j a q k l)
    (contDiff_pi.mp (contDiff_pi.mp h.1 k) l) (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (fun t x hx => by rw [h.2 t x hx]; rfl)

lemma contDiff_referenceRotationDriftClosedJets (r : ℕ) (i j l : Fin 3) :
    ContDiff ℝ ∞ (fun t => smoothCoefficientClosureInclusionL r
      (referenceRotationDriftJetsFamily g L y0 Φ B ε C ρ H a w hData r i j l t)) := by
  have h := referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j
  exact contDiff_commonSupportClosedCoefficientFamily r
    (fun q => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) q l)
    ((EuclideanSpace.proj l : R3 →L[ℝ] ℝ).contDiff.comp h.1)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (fun t x hx => by rw [h.2 t x hx]; rfl)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationPrincipal_data
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationDrift_data
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationPrincipalJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationDriftJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientMatrixField_referenceRotationPrincipalJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_referenceRotationDriftJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationPrincipalJetFields
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationDriftJetFields
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationPrincipalClosedJets
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationDriftClosedJets
