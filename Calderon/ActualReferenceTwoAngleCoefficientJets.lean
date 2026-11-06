import Calderon.ActualReferenceTwoAngleCoefficientData
import Calderon.CommonSupportMatrixInverse

/-! Native two-angle operators. Same actual nested-rotation
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

def referenceTwoAnglePrincipalJetsFamily (n : ℕ) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) : SmoothCoefficientMatrix n :=
  commonSupportMatrixFamily n (referenceTwoAnglePrincipalFamily a i j k l)
    (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).2 t

def referenceTwoAngleDriftJetsFamily (n : ℕ) (i j k l d : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) : SmoothCoefficientJets n :=
  commonSupportCoefficientFamily n (fun z => referenceTwoAngleDriftFamily g L Φ H w i j k l z d)
    ((EuclideanSpace.proj d : R3 →L[ℝ] ℝ).contDiff.comp
      (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData i j k l).1)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (fun t x hx => by
      rw [(referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData i j k l).2 t x hx]
      rfl) t

lemma coefficientMatrixField_referenceTwoAnglePrincipalJetsFamily (n : ℕ) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    coefficientMatrixField n (referenceTwoAnglePrincipalJetsFamily
      g L y0 Φ B ε C ρ H a w hData n i j k l t) =
        fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x) :=
  coefficientMatrixField_commonSupportMatrixFamily n (referenceTwoAnglePrincipalFamily a i j k l)
    (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).2 t

lemma coefficientValue_referenceTwoAngleDriftJetsFamily (n : ℕ) (i j k l d : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (x : R3) :
    coefficientValue n (referenceTwoAngleDriftJetsFamily
      g L y0 Φ B ε C ρ H a w hData n i j k l d t) x =
        referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x) d :=
  coefficientValue_commonSupportCoefficientFamily n _ _ (closedBall (0 : R3) 3)
    (isCompact_closedBall _ _) _ t x

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAnglePrincipalJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleDriftJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientMatrixField_referenceTwoAnglePrincipalJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_referenceTwoAngleDriftJetsFamily
