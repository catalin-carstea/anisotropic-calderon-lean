import Calderon.ActualReferenceRotationLowerRadialEndpoint
import Calderon.ActualReferenceRotationPrincipalEllipticity
import Calderon.ActualReferenceNormalOrderOneFamily
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeBoundaryCoefficientFamilies
  NativeThreeHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (i j : Fin 3)

def referenceRotationNormalCoefficientJetsFamily3 :
    (ℝ × (ℝ × (R3 × ℝ))) → SmoothCoefficientJets 3 :=
  commonSupportCoefficientFamily 3 (normalCoefficientFunction (coordinateRotationPrincipalFamily i j a))
    (contDiff_normalCoefficientFunction _
      (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).1)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (normalCoefficientFunction_support _ (closedBall (0 : R3) 3)
      (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).2)

lemma coefficientValue_referenceRotationNormalCoefficientJetsFamily3_eq
    (t : ℝ × (ℝ × (R3 × ℝ))) :
    coefficientValue 3 (referenceRotationNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData i j t) =
      coefficientValue 2 (referenceRotationNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData i j t) :=
  coefficientValue_commonSupportCoefficientFamily_order_eq 3 2
    (normalCoefficientFunction (coordinateRotationPrincipalFamily i j a))
    (contDiff_normalCoefficientFunction _
      (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).1)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (normalCoefficientFunction_support _ (closedBall (0 : R3) 3)
      (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).2) t

lemma nativeH2CoefficientSmoothData_referenceRotationNormalCoefficientJetsFamily3
    (t : ℝ × (ℝ × (R3 × ℝ))) :
    nativeH2CoefficientSmoothData
      (referenceRotationNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData i j t) =
      boundaryNormalCoefficientData
        (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t) := by
  have hSame : nativeH2CoefficientSmoothData
      (referenceRotationNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData i j t) =
      coefficientSmoothData
        (referenceRotationNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData i j t) :=
    Subtype.ext (coefficientValue_referenceRotationNormalCoefficientJetsFamily3_eq
      g L y0 Φ B ε C ρ H a w hData i j t)
  exact hSame.trans (coefficientSmoothData_referenceRotationNormalJets_eq_boundaryData
    g L y0 Φ B ε C ρ H a w hData i j t)

lemma referenceRotationNormalCoefficientJetsFamily3_sphere_pos
    (t : ℝ × (ℝ × (R3 × ℝ))) (x : UnitSphere) :
    0 < coefficientValue 3
      (referenceRotationNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData i j t) x.val := by
  let F := referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t
  have hField : coefficientMatrixField 2 F = (fun z => coordinateRotationPrincipalFamily i j a (t,z)) :=
    coefficientMatrixField_referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t
  obtain ⟨lam,Lam,hUE⟩ := exists_referenceRotationPrincipal_uniformlyElliptic
    g L y0 Φ B ε C ρ H a w hData i j t.1 t.2
  have hUEF : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (coefficientMatrixField 2 F) lam Lam := hField.symm ▸ hUE
  have hValue := congrArg (fun m : SmoothData => m.val x.val)
    (nativeH2CoefficientSmoothData_referenceRotationNormalCoefficientJetsFamily3
      g L y0 Φ B ε C ρ H a w hData i j t)
  have hLiteral : coefficientValue 3
      (referenceRotationNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData i j t) x.val =
      (boundaryNormalCoefficientData F).val x.val := hValue
  exact lt_of_lt_of_eq (boundaryNormalCoefficientData_pos F lam Lam hUEF x) hLiteral.symm
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationNormalCoefficientJetsFamily3
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_referenceRotationNormalCoefficientJetsFamily3_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH2CoefficientSmoothData_referenceRotationNormalCoefficientJetsFamily3
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationNormalCoefficientJetsFamily3_sphere_pos
