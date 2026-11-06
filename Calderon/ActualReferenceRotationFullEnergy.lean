import Calderon.NativeSmoothCoefficientFullEnergy
import Calderon.NativeFullFiniteForcingTopology
import Calderon.ActualReferenceRotationMultiplierTopology
import Calderon.NativeContinuousCoefficientOrthogonalEnergy

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

/-! Actual literal full native energy operator regularity is derived from coefficient multipliers. -/

def referenceRotationFullWeakEnergyFamily (hcalc : FixedSobolevCalculus)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) : BallH1 →L[ℝ] StrongDual ℝ BallH1 :=
  nativeSmoothCoefficientFullEnergyL hcalc
    (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 1 i j t)
    (fun l => referenceRotationDriftJetsFamily g L y0 Φ B ε C ρ H a w hData 1 i j l t)

lemma nativeSmoothDriftField_referenceRotationDriftJetsFamily (i j : Fin 3)
    (t : ℝ × (ℝ × (R3 × ℝ))) :
    nativeSmoothDriftField (fun l => referenceRotationDriftJetsFamily g L y0 Φ B ε C ρ H a w hData 1 i j l t) =
      fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x) := by
  funext x
  ext l
  change coefficientValue 1 (referenceRotationDriftJetsFamily g L y0 Φ B ε C ρ H a w hData 1 i j l t) x = _
  exact coefficientValue_referenceRotationDriftJetsFamily g L y0 Φ B ε C ρ H a w hData 1 i j l t x

lemma referenceRotationFullWeakEnergyFamily_apply (hcalc : FixedSobolevCalculus)
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) (u v : BallH1) :
    referenceRotationFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => coordinateRotationPrincipalFamily i j a (t,x))
        (fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
        0 u v := by
  rw [referenceRotationFullWeakEnergyFamily,nativeSmoothCoefficientFullEnergyL_apply,
    coefficientMatrixField_referenceRotationPrincipalJetsFamily,
    nativeSmoothDriftField_referenceRotationDriftJetsFamily]

include hData

lemma referenceRotationNativeEnergy_memLp (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    MemLp (fun x => TauCeti.PDE.energyIntegrand (coordinateRotationPrincipalFamily i j a (t,x))
      (coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)) 0) ⊤
      ((volume : Measure R3).restrict ballOpens) := by
  have ha : Continuous (fun x : R3 => coordinateRotationPrincipalFamily i j a (t,x)) :=
    (referenceRotationPrincipal_data g L y0 Φ B ε C ρ H a w hData i j).1.continuous.comp
      (continuous_const.prodMk continuous_id)
  have hb : Continuous (fun x : R3 => coordinateRotationDriftFamily i j
      (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)) :=
    (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).1.continuous.comp
      (continuous_const.prodMk continuous_id)
  exact memLp_nativeEnergyIntegrand_of_continuous _ _ 0 ha hb continuous_const

lemma referenceRotationFullWeakEnergyFamily_eq_nativeEnergyFormH1L
    (hcalc : FixedSobolevCalculus) (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) :
    referenceRotationFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j t =
      TauCeti.PDE.energyFormH1L (mu := (volume : Measure R3)) (Omega := ballOpens)
        (a := fun x => coordinateRotationPrincipalFamily i j a (t,x))
        (b := fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
        (c := 0) (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j t) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  exact (referenceRotationFullWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc i j t u v).trans
    (TauCeti.PDE.energyFormH1L_apply
      (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j t) u v).symm

lemma contDiff_referenceRotationFullWeakEnergyFamily (hcalc : FixedSobolevCalculus) (i j : Fin 3) :
    ContDiff ℝ ∞ (referenceRotationFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j) := by
  unfold referenceRotationFullWeakEnergyFamily nativeSmoothCoefficientFullEnergyL
  exact contDiff_nativeFullFiniteForcingEnergy
    (fun m n => referenceRotationPrincipalMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 i j m n)
    (fun l => referenceRotationDriftMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 i j l)
    (fun m n => contDiff_referenceRotationPrincipalMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 i j m n)
    (fun l => contDiff_referenceRotationDriftMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 i j l)

lemma contDiff_referenceRotationNativeEnergyFormH1L (hcalc : FixedSobolevCalculus) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun t => TauCeti.PDE.energyFormH1L (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := fun x => coordinateRotationPrincipalFamily i j a (t,x))
      (b := fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
      (c := 0) (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j t)) := by
  have he : (fun t => TauCeti.PDE.energyFormH1L (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := fun x => coordinateRotationPrincipalFamily i j a (t,x))
      (b := fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
      (c := 0) (referenceRotationNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData i j t)) =
    referenceRotationFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j :=
    funext (fun t => (referenceRotationFullWeakEnergyFamily_eq_nativeEnergyFormH1L
      g L y0 Φ B ε C ρ H a w hData hcalc i j t).symm)
  have hEq := congrArg (ContDiff ℝ ∞) he
  exact Eq.mpr hEq (contDiff_referenceRotationFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationFullWeakEnergyFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSmoothDriftField_referenceRotationDriftJetsFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationFullWeakEnergyFamily_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationNativeEnergy_memLp
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationFullWeakEnergyFamily_eq_nativeEnergyFormH1L
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationFullWeakEnergyFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceRotationNativeEnergyFormH1L
