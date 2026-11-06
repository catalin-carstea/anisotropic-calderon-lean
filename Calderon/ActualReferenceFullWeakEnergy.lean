import Calderon.ActualJointReferenceCoefficientData
import Calderon.CoordinateFluxEnergy
import Calderon.ClosedCoefficientMultiplier
import Calderon.ParametricWeightedForcing
import Calderon.ActualReferenceWeakEnergyApply

/-! Full-test actual energy, expanded before source in EXPANSION-actual-reference-full-weak-energy-author-v001.json. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hData

def referenceFullWeakEnergyFamily (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) : BallH1 →L[ℝ] StrongDual ℝ BallH1 :=
  let h := jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData
  let hc := jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData
  let K : Set R3 := closedBall (0 : R3) 3
  let hK : IsCompact K := isCompact_closedBall _ _
  let F : SmoothCoefficientMatrix 1 := commonSupportMatrixFamily 1 a h.1 K hK h.2.2.2.1 p
  let G : Fin 3 → SmoothCoefficientJets 1 := fun i =>
    commonSupportCoefficientFamily 1
      (fun t => conformalReferenceWeightedFramedDrift g L Φ H w t i)
      ((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp hc.1) K hK
      (fun t z hz => by rw [hc.2 t z hz]; rfl) p
  let E0 := Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)
  let J : BallH1 →L[ℝ] BallH1 := ContinuousLinearMap.id ℝ BallH1
  let D : Fin 3 → BallH1 →L[ℝ] E0 := unitBallCoordinateGradientL
  let V : BallH1 →L[ℝ] E0 :=
    TauCeti.W1p.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)
  let M : Fin 3 → Fin 3 → E0 →L[ℝ] E0 := fun i j => coefficientMultiplier hcalc 0 (F i j)
  let Mc : Fin 3 → E0 →L[ℝ] E0 := fun i => coefficientMultiplier hcalc 0 (G i)
  let P : Fin 3 → E0 →L[ℝ] StrongDual ℝ BallH1 :=
    fun i => forcingFromValueL ((D i).comp J)
  let P0 : E0 →L[ℝ] StrongDual ℝ BallH1 := forcingFromValueL (V.comp J)
  (∑ i : Fin 3, ∑ j : Fin 3, (P i).comp ((M i j).comp (D j))) +
    ∑ i : Fin 3, P0.comp ((Mc i).comp (D i))


theorem referenceFullWeakEnergyFamily_apply (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) (u : BallH1) (v : BallH1) :
    referenceFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) (fun z => a (p,z))
        (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)) 0 u (v : BallH1) := by
  let h := jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData
  let hc := jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData
  let K : Set R3 := closedBall (0 : R3) 3
  let hK : IsCompact K := isCompact_closedBall _ _
  let F : SmoothCoefficientMatrix 1 := commonSupportMatrixFamily 1 a h.1 K hK h.2.2.2.1 p
  let G : Fin 3 → SmoothCoefficientJets 1 := fun i =>
    commonSupportCoefficientFamily 1
      (fun t => conformalReferenceWeightedFramedDrift g L Φ H w t i)
      ((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp hc.1) K hK
      (fun t z hz => by rw [hc.2 t z hz]; rfl) p
  let Q : Fin 3 → Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) := fun i j =>
    coefficientMultiplier hcalc 0 (F i j) (unitBallCoordinateGradientL j u)
  let R : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) := fun i =>
    coefficientMultiplier hcalc 0 (G i) (unitBallCoordinateGradientL i u)
  let E0 := Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)
  let J : BallH1 →L[ℝ] BallH1 := ContinuousLinearMap.id ℝ BallH1
  let D : Fin 3 → BallH1 →L[ℝ] E0 := unitBallCoordinateGradientL
  let V : BallH1 →L[ℝ] E0 :=
    TauCeti.W1p.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)
  let M : Fin 3 → Fin 3 → E0 →L[ℝ] E0 := fun i j => coefficientMultiplier hcalc 0 (F i j)
  let Mc : Fin 3 → E0 →L[ℝ] E0 := fun i => coefficientMultiplier hcalc 0 (G i)
  let P : Fin 3 → E0 →L[ℝ] StrongDual ℝ BallH1 :=
    fun i => forcingFromValueL ((D i).comp J)
  let P0 : E0 →L[ℝ] StrongDual ℝ BallH1 := forcingFromValueL (V.comp J)
  have hEvaluation :
      ((∑ i : Fin 3, ∑ j : Fin 3, (P i).comp ((M i j).comp (D j))) +
        ∑ i : Fin 3, P0.comp ((Mc i).comp (D i))) u v =
      (∑ i : Fin 3, ∑ j : Fin 3, ⟪Q i j, unitBallCoordinateGradientL i (v : BallH1)⟫_ℝ) +
        ∑ i : Fin 3, ⟪R i, TauCeti.W1p.value (v : BallH1)⟫_ℝ := by
    have hJ : J v = (v : BallH1) := rfl
    have hV : V v = TauCeti.W1p.value (mu := (volume : Measure R3))
        (Omega := ballOpens) (p := (2:ℝ≥0∞)) v := rfl
    have hEval := finiteForcingEnergy_apply J D V M Mc u v
    simpa only [P, P0, Q, R, M, Mc, D, hJ, hV] using hEval
  have hField : coefficientMatrixField 1 F = fun x => a (p,x) :=
    coefficientMatrixField_commonSupportMatrixFamily 1 a h.1 K hK h.2.2.2.1 p
  have hQ (i j : Fin 3) : Q i j =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => a (p,x) i j * (TauCeti.W1p.gradient u x) j := by
    filter_upwards [coefficientMultiplier_value_ae hcalc 0 (F i j)
      (unitBallCoordinateGradientL j u),unitBallCoordinateGradientL_ae j u] with x hx hg
    simp only [TauCeti.Wkp.value_zero] at hx
    rw [hx,hg]
    change coefficientMatrixField 1 F x i j * _ = _
    rw [hField]
  have hR (i : Fin 3) : R i =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x) i *
        (TauCeti.W1p.gradient u x) i := by
    filter_upwards [coefficientMultiplier_value_ae hcalc 0 (G i)
      (unitBallCoordinateGradientL i u),unitBallCoordinateGradientL_ae i u] with x hx hg
    simp only [TauCeti.Wkp.value_zero] at hx
    rw [hx,hg]
    rw [show coefficientValue 1 (G i) x =
      conformalReferenceWeightedFramedDrift g L Φ H w (p,x) i from
        coefficientValue_commonSupportCoefficientFamily 1 _ _ K hK _ p x]
  have hIntegral : TauCeti.PDE.energyFormH1
      (mu := (volume : Measure R3)) (Omega := ballOpens) (fun x => a (p,x))
      (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0 u (v : BallH1) =
      (∑ i : Fin 3, ∑ j : Fin 3, ⟪Q i j,unitBallCoordinateGradientL i (v : BallH1)⟫_ℝ) +
        ∑ i : Fin 3, ⟪R i,TauCeti.W1p.value (v : BallH1)⟫_ℝ := by
    exact energyFormH1_eq_sum_coordinateFlux_inner_add_drift
      (fun x => a (p,x)) (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x))
      u (v : BallH1) Q R hQ hR

  calc
    _ = (∑ i : Fin 3, ∑ j : Fin 3, ⟪Q i j,unitBallCoordinateGradientL i (v : BallH1)⟫_ℝ) +
        ∑ i : Fin 3, ⟪R i,TauCeti.W1p.value (v : BallH1)⟫_ℝ := by
      change ((∑ i : Fin 3, ∑ j : Fin 3, (P i).comp ((M i j).comp (D j))) +
        ∑ i : Fin 3, P0.comp ((Mc i).comp (D i))) u v = _
      exact hEvaluation
    _ = _ := hIntegral.symm


theorem referenceFullWeakEnergyFamily_apply_zero (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) (u : BallH1) (v : BallH1Zero) :
    referenceFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p u (v : BallH1) =
      referenceWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p u v := by
  exact (referenceFullWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc p u (v : BallH1)).trans
    (referenceWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc p u v).symm

theorem referenceFullWeakEnergyFamily_restrict (hcalc : FixedSobolevCalculus)
    (p : ℝ × (R3 × ℝ)) :
    (((ContinuousLinearMap.compL ℝ BallH1Zero BallH1 ℝ).flip
      (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL).comp
        (referenceFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p)) =
      referenceWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  exact referenceFullWeakEnergyFamily_apply_zero g L y0 Φ B ε C ρ H a w hData hcalc p u v

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
