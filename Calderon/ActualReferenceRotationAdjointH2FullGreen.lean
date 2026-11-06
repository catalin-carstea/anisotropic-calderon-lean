import Calderon.ActualReferenceRotationAdjointH2LiftFamily
import Calderon.NativeScalarMassFullGreen

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativePolynomialBulkMoments
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma referenceRotationAdjointNativeCoefficient_energy_eq
    (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) (u v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField 2 (nativePrincipalTransposeJets
        (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t)))
      (-(fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)))
      (coefficientValue 1 (referenceRotationAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData i j t)) u v =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ) (fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
      (fun x => -nativeSupportedDriftDivergence (fun y => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,y)) x) u v := by
  let F := nativePrincipalTransposeJets (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t)
  let beta : R3 → R3 := fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)
  let M := referenceRotationAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData i j t
  have hField : coefficientMatrixField 2 F=(fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ) :=
    (coefficientMatrixField_nativePrincipalTransposeJets _).trans
      (congrArg (fun A : MatrixField => fun x => (A x)ᵀ)
        (coefficientMatrixField_referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t))
  have hDrift : (-beta : R3 → R3)=(fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)) := rfl
  have hMass : coefficientValue 1 M=(fun x => -nativeSupportedDriftDivergence beta x) :=
    funext (coefficientValue_referenceRotationAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData i j t)
  have hA := congrArg (fun A : MatrixField => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens) A (-beta) (coefficientValue 1 M) u v) hField
  have hB := congrArg (fun b : R3 → R3 => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens) (fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ) b (coefficientValue 1 M) u v) hDrift
  have hC := congrArg (fun c : R3 → ℝ => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens) (fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ)
    (fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)) c u v) hMass
  exact hA.trans (hB.trans hC)

lemma referenceRotationAdjointH2LiftFamily_full_test_energy_Green
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (i j : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ)))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc t.2).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) (v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (coordinateRotationPrincipalFamily i j a (t,x))ᵀ) (fun x => -coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x))
      (fun x => -nativeSupportedDriftDivergence (fun y => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,y)) x)
      (TauCeti.Wkp.firstOrder 1 (referenceRotationAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f)) v =
    sphereSurfaceMass*⟪ordinaryConormalTraceL hcalc τ0
      (nativePrincipalTransposeJets (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t))
      (referenceRotationAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f),τ0.valueTraceL v⟫_ℝ := by
  let F := nativePrincipalTransposeJets (referenceRotationPrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j t)
  let beta : R3 → R3 := fun x => coordinateRotationDriftFamily i j (conformalReferenceWeightedFramedDrift g L Φ H w) (t,x)
  let M := referenceRotationAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData i j t
  let U := referenceRotationAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j t f
  have hbeta : ContDiff ℝ ∞ beta := SpatialJetFields.contDiff_spatial_slice _
    (referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).1 t
  have hz : ∀ x, x ∉ closedBall (0 : R3) 3 → (-beta : R3 → R3) x=0 :=
    nativeSupportedNegativeDrift_zeroOutside beta (closedBall (0 : R3) 3)
      ((referenceRotationDrift_data g L y0 Φ B ε C ρ H a w hData i j).2 t)
  have hWeak : ∀ z : BallH1Zero, TauCeti.PDE.energyFormH1
      (mu := (volume : Measure R3)) (Omega := ballOpens) (coefficientMatrixField 2 F) (-beta)
      (coefficientValue 1 M) (TauCeti.Wkp.firstOrder 1 U) (z : BallH1)=0 := by
    intro z
    exact (referenceRotationAdjointNativeCoefficient_energy_eq g L y0 Φ B ε C ρ H a w hData i j t
      (TauCeti.Wkp.firstOrder 1 U) (z : BallH1)).trans
        (referenceRotationAdjointH2LiftFamily_homogeneous_weak_energy g L y0 Φ B ε C ρ H a w hData
          τ0 hcalc hreg hF i j t hOriginal f z)
  have hNative := nativeSupportedMass_homogeneous_full_test_energy hcalc τ0 F (-beta) hbeta.neg
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _) hz M U hWeak v
  exact (referenceRotationAdjointNativeCoefficient_energy_eq g L y0 Φ B ε C ρ H a w hData i j t
    (TauCeti.Wkp.firstOrder 1 U) v).symm.trans hNative

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointNativeCoefficient_energy_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointH2LiftFamily_full_test_energy_Green
