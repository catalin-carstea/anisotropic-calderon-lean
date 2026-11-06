import Calderon.ActualReferenceRotationCoefficientJets

/-! Literal two independent rotations of SAME actual principal/full drift fields.
Only coefficient smoothness/support; no second commutator or high gain assumed. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceTwoAnglePrincipalFamily (i j k l : Fin 3) :
    (ℝ × (ℝ × (ℝ × (R3 × ℝ)))) × R3 → Matrix (Fin 3) (Fin 3) ℝ :=
  coordinateRotationPrincipalFamily i j (coordinateRotationPrincipalFamily k l a)

def referenceTwoAngleDriftFamily (i j k l : Fin 3) :
    (ℝ × (ℝ × (ℝ × (R3 × ℝ)))) × R3 → R3 :=
  coordinateRotationDriftFamily i j
    (coordinateRotationDriftFamily k l (conformalReferenceWeightedFramedDrift g L Φ H w))

include hData

lemma referenceTwoAnglePrincipal_data (i j k l : Fin 3) :
    ContDiff ℝ ∞ (referenceTwoAnglePrincipalFamily a i j k l) ∧
    ∀ t x, x ∉ closedBall (0 : R3) 3 → referenceTwoAnglePrincipalFamily a i j k l (t,x) = 0 := by
  have h := referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData k l
  exact ⟨contDiff_coordinateRotationPrincipalFamily i j (coordinateRotationPrincipalFamily k l a) h.1,
    coordinateRotationPrincipalFamily_zero_outside i j (coordinateRotationPrincipalFamily k l a) 3 h.2⟩

lemma referenceTwoAngleDrift_data (i j k l : Fin 3) :
    ContDiff ℝ ∞ (referenceTwoAngleDriftFamily g L Φ H w i j k l) ∧
    ∀ t x, x ∉ closedBall (0 : R3) 3 →
      referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x) = 0 := by
  have h := referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData k l
  exact ⟨contDiff_coordinateRotationDriftFamily i j
      (coordinateRotationDriftFamily k l (conformalReferenceWeightedFramedDrift g L Φ H w)) h.1,
    coordinateRotationDriftFamily_zero_outside i j
      (coordinateRotationDriftFamily k l (conformalReferenceWeightedFramedDrift g L Φ H w)) 3 h.2⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAnglePrincipalFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleDriftFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAnglePrincipal_data
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleDrift_data
