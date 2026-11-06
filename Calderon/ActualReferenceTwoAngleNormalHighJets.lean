import Calderon.ActualReferenceTwoAngleNormalCovariance
import Calderon.ActualReferenceTwoAngleNativeAdjointInverse
import Calderon.ActualReferenceNormalOrderOneFamily
set_option autoImplicit false
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
  (i j k l : Fin 3)

def referenceTwoAngleNormalCoefficientJetsFamily3 :
    (ℝ × (ℝ × (ℝ × (R3 × ℝ)))) → SmoothCoefficientJets 3 :=
  commonSupportCoefficientFamily 3 (normalCoefficientFunction (referenceTwoAnglePrincipalFamily a i j k l))
    (contDiff_normalCoefficientFunction _
      (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).1)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (normalCoefficientFunction_support _ (closedBall (0 : R3) 3)
      (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).2)

lemma coefficientValue_referenceTwoAngleNormalCoefficientJetsFamily3_eq
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    coefficientValue 3 (referenceTwoAngleNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData i j k l t) =
      coefficientValue 2 (referenceTwoAngleNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData i j k l t) :=
  coefficientValue_commonSupportCoefficientFamily_order_eq 3 2
    (normalCoefficientFunction (referenceTwoAnglePrincipalFamily a i j k l))
    (contDiff_normalCoefficientFunction _
      (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).1)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (normalCoefficientFunction_support _ (closedBall (0 : R3) 3)
      (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).2) t

lemma nativeH2CoefficientSmoothData_referenceTwoAngleNormalCoefficientJetsFamily3
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    nativeH2CoefficientSmoothData
      (referenceTwoAngleNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData i j k l t) =
      boundaryNormalCoefficientData
        (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t) := by
  have hSame : nativeH2CoefficientSmoothData
      (referenceTwoAngleNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData i j k l t) =
      coefficientSmoothData
        (referenceTwoAngleNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData i j k l t) :=
    Subtype.ext (coefficientValue_referenceTwoAngleNormalCoefficientJetsFamily3_eq
      g L y0 Φ B ε C ρ H a w hData i j k l t)
  have hNative : coefficientSmoothData
      (referenceTwoAngleNormalCoefficientJetsFamily g L y0 Φ B ε C ρ H a w hData i j k l t) =
      boundaryNormalCoefficientData
        (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t) := by
    unfold referenceTwoAngleNormalCoefficientJetsFamily referenceTwoAnglePrincipalJetsFamily
    exact coefficientSmoothData_normalCoefficientJetsFamily
      (referenceTwoAnglePrincipalFamily a i j k l)
      (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).1
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (referenceTwoAnglePrincipal_data g L y0 Φ B ε C ρ H a w hData i j k l).2 t
  exact hSame.trans hNative

lemma referenceTwoAngleNormalCoefficientJetsFamily3_sphere_pos
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (x : UnitSphere) :
    0 < coefficientValue 3
      (referenceTwoAngleNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData i j k l t) x.val := by
  let F := referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t
  have hField : coefficientMatrixField 2 F = (fun z => referenceTwoAnglePrincipalFamily a i j k l (t,z)) :=
    coefficientMatrixField_referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t
  obtain ⟨lam,Lam,hUE⟩ := exists_referenceTwoAnglePrincipal_uniformlyElliptic_on_compact
    g L y0 Φ B ε C ρ H a w hData {t.2.2} isCompact_singleton
  have hActual := hUE i j k l t.1 t.2.1 t.2.2 (mem_singleton t.2.2)
  have hUEF : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (coefficientMatrixField 2 F) lam Lam := hField.symm ▸ hActual
  have hValue := congrArg (fun m : SmoothData => m.val x.val)
    (nativeH2CoefficientSmoothData_referenceTwoAngleNormalCoefficientJetsFamily3
      g L y0 Φ B ε C ρ H a w hData i j k l t)
  have hLiteral : coefficientValue 3
      (referenceTwoAngleNormalCoefficientJetsFamily3 g L y0 Φ B ε C ρ H a w hData i j k l t) x.val =
      (boundaryNormalCoefficientData F).val x.val := hValue
  exact lt_of_lt_of_eq (boundaryNormalCoefficientData_pos F lam Lam hUEF x) hLiteral.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNormalCoefficientJetsFamily3
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_referenceTwoAngleNormalCoefficientJetsFamily3_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH2CoefficientSmoothData_referenceTwoAngleNormalCoefficientJetsFamily3
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleNormalCoefficientJetsFamily3_sphere_pos
