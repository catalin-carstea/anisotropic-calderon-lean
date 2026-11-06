import Calderon.ActualReferenceTwoAngleCoefficientJets
import Calderon.ClosedCoefficientMultiplier

/-! Upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-native-two-angle-operators-v003.md. Same actual nested-rotation
coefficients; independent angles and original geometric data retained. -/
set_option autoImplicit false
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

def referenceTwoAnglePrincipalMultiplierFamily (hcalc : FixedSobolevCalculus)
    (n : ℕ) (i j k l d e : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    BallSobolev n →L[ℝ] BallSobolev n :=
  coefficientMultiplier hcalc n
    (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData (n+1) i j k l t d e)

lemma contDiff_referenceTwoAnglePrincipalMultiplierFamily (hcalc : FixedSobolevCalculus)
    (n : ℕ) (i j k l d e : Fin 3) :
    ContDiff ℝ ∞ (referenceTwoAnglePrincipalMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc n i j k l d e) := by
  have h := referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l
  exact contDiff_commonSupport_actual_coefficientMultiplier hcalc n
    (fun z => referenceTwoAnglePrincipalFamily a i j k l z d e)
    (contDiff_pi.mp (contDiff_pi.mp h.1 d) e)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (fun t x hx => by rw [h.2 t x hx]; rfl)

def referenceTwoAngleDriftMultiplierFamily (hcalc : FixedSobolevCalculus)
    (n : ℕ) (i j k l d : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    BallSobolev n →L[ℝ] BallSobolev n :=
  coefficientMultiplier hcalc n
    (referenceTwoAngleDriftJetsFamily g L y0 Φ B ε C ρ H a w hData (n+1) i j k l d t)

lemma contDiff_referenceTwoAngleDriftMultiplierFamily (hcalc : FixedSobolevCalculus)
    (n : ℕ) (i j k l d : Fin 3) :
    ContDiff ℝ ∞ (referenceTwoAngleDriftMultiplierFamily
      g L y0 Φ B ε C ρ H a w hData hcalc n i j k l d) := by
  have h := referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData i j k l
  exact contDiff_commonSupport_actual_coefficientMultiplier hcalc n
    (fun z => referenceTwoAngleDriftFamily g L Φ H w i j k l z d)
    ((EuclideanSpace.proj d : R3 →L[ℝ] ℝ).contDiff.comp h.1)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (fun t x hx => by rw [h.2 t x hx]; rfl)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAnglePrincipalMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTwoAnglePrincipalMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleDriftMultiplierFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceTwoAngleDriftMultiplierFamily
