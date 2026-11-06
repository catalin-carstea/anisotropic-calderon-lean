import Calderon.ActualReferenceRotationCoefficientJets
import Calderon.ClosedCoefficientMultiplier

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

/-! Upfront expansion and full dependency plan: EXPANSION-actual-rotation-native-conormal-topology-v001.json.
These actual multiplier topologies are derived from true coefficient jets, not boundary group opnorm topology. -/

def referenceRotationPrincipalMultiplierFamily (hcalc : FixedSobolevCalculus)
    (k : ℕ) (i j m n : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    BallSobolev k →L[ℝ] BallSobolev k :=
  coefficientMultiplier hcalc k
    (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData (k+1) i j t m n)

lemma contDiff_referenceRotationPrincipalMultiplierFamily (hcalc : FixedSobolevCalculus)
    (k : ℕ) (i j m n : Fin 3) :
    ContDiff ℝ ∞ (referenceRotationPrincipalMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc k i j m n) := by
  have h := referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j
  exact contDiff_commonSupport_actual_coefficientMultiplier hcalc k
    (fun q => coordinateRotationPrincipalFamily i j a q m n)
    (contDiff_pi.mp (contDiff_pi.mp h.1 m) n) (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (fun t x hx => by rw [h.2 t x hx]; rfl)

def referenceRotationDriftMultiplierFamily (hcalc : FixedSobolevCalculus)
    (k : ℕ) (i j l : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    BallSobolev k →L[ℝ] BallSobolev k :=
  coefficientMultiplier hcalc k
    (referenceRotationDriftJetsFamily g L y0 Φ B ε C ρ H a w hData (k+1) i j l t)

lemma contDiff_referenceRotationDriftMultiplierFamily (hcalc : FixedSobolevCalculus)
    (k : ℕ) (i j l : Fin 3) :
    ContDiff ℝ ∞ (referenceRotationDriftMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc k i j l) := by
  have h := referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j
  exact contDiff_commonSupport_actual_coefficientMultiplier hcalc k
    (fun q => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) q l)
    ((EuclideanSpace.proj l : R3 →L[ℝ] ℝ).contDiff.comp h.1)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (fun t x hx => by rw [h.2 t x hx]; rfl)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationPrincipalMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationPrincipalMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationDriftMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationDriftMultiplierFamily
