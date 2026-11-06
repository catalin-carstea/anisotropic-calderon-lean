import Calderon.ActualReferenceTwoAngleMultipliers
import Calderon.NativeSmoothCoefficientFullEnergy
import Calderon.NativeFullFiniteForcingTopology
import Calderon.ActualReferenceRotationWeakEnergy

/-! Native literal tested energy
and actual inverse room of the same two-angle coefficients. -/
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

attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

def referenceTwoAngleFullWeakEnergyFamily (hcalc : FixedSobolevCalculus)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    BallH1 →L[ℝ] StrongDual ℝ BallH1 :=
  nativeSmoothCoefficientFullEnergyL hcalc
    (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 1 i j k l t)
    (fun d => referenceTwoAngleDriftJetsFamily g L y0 Φ B ε C ρ H a w hData 1 i j k l d t)

def referenceTwoAngleWeakEnergyFamily (hcalc : FixedSobolevCalculus)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    BallH1 →L[ℝ] StrongDual ℝ BallH1Zero :=
  nativeH1ZeroDualRestrictionL.comp
    (referenceTwoAngleFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t)

def referenceTwoAngleWeakDirichletEnergyFamily (hcalc : FixedSobolevCalculus)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) :
    BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
  (referenceTwoAngleWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).comp
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL

lemma referenceTwoAngleFullWeakEnergyFamily_apply (hcalc : FixedSobolevCalculus)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (u v : BallH1) :
    referenceTwoAngleFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
        (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) 0 u v := by
  have hDrift : nativeSmoothDriftField
      (fun d => referenceTwoAngleDriftJetsFamily g L y0 Φ B ε C ρ H a w hData 1 i j k l d t) =
      fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x) := by
    funext x
    ext d
    exact coefficientValue_referenceTwoAngleDriftJetsFamily
      g L y0 Φ B ε C ρ H a w hData 1 i j k l d t x
  unfold referenceTwoAngleFullWeakEnergyFamily
  rw [nativeSmoothCoefficientFullEnergyL_apply,
    coefficientMatrixField_referenceTwoAnglePrincipalJetsFamily,hDrift]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleFullWeakEnergyFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleWeakEnergyFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleWeakDirichletEnergyFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleFullWeakEnergyFamily_apply
