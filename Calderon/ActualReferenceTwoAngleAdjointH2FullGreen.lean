import Calderon.ActualReferenceTwoAngleAdjointH2LiftFamily
import Calderon.NativeScalarMassFullGreen

/-! Upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-two-angle-adjoint-Green-v050.md. -/
set_option autoImplicit false
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

lemma referenceTwoAngleAdjointNativeCoefficient_energy_eq
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (u v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField 2 (nativePrincipalTransposeJets
        (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t)))
      (-(fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)))
      (coefficientValue 1 (referenceTwoAngleAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData i j k l t)) u v =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (referenceTwoAnglePrincipalFamily a i j k l (t,x))ᵀ) (fun x => -referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x))
      (fun x => -nativeSupportedDriftDivergence (fun y => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,y)) x) u v := by
  let F := nativePrincipalTransposeJets (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t)
  let beta : R3 → R3 := fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)
  let M := referenceTwoAngleAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData i j k l t
  have hField : coefficientMatrixField 2 F=(fun x => (referenceTwoAnglePrincipalFamily a i j k l (t,x))ᵀ) :=
    (coefficientMatrixField_nativePrincipalTransposeJets _).trans
      (congrArg (fun A : MatrixField => fun x => (A x)ᵀ)
        (coefficientMatrixField_referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t))
  have hDrift : (-beta : R3 → R3)=(fun x => -referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) := rfl
  have hMass : coefficientValue 1 M=(fun x => -nativeSupportedDriftDivergence beta x) :=
    funext (coefficientValue_referenceTwoAngleAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData i j k l t)
  have hA := congrArg (fun A : MatrixField => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens) A (-beta) (coefficientValue 1 M) u v) hField
  have hB := congrArg (fun b : R3 → R3 => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens) (fun x => (referenceTwoAnglePrincipalFamily a i j k l (t,x))ᵀ) b (coefficientValue 1 M) u v) hDrift
  have hC := congrArg (fun c : R3 → ℝ => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens) (fun x => (referenceTwoAnglePrincipalFamily a i j k l (t,x))ᵀ)
    (fun x => -referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) c u v) hMass
  exact hA.trans (hB.trans hC)

lemma referenceTwoAngleAdjointH2LiftFamily_full_test_energy_Green
    (τ0 : UnitBallValueTrace) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hOriginal : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc t.2.2).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) (v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (referenceTwoAnglePrincipalFamily a i j k l (t,x))ᵀ) (fun x => -referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x))
      (fun x => -nativeSupportedDriftDivergence (fun y => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,y)) x)
      (TauCeti.Wkp.firstOrder 1 (referenceTwoAngleAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t f)) v =
    sphereSurfaceMass*⟪ordinaryConormalTraceL hcalc τ0
      (nativePrincipalTransposeJets (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t))
      (referenceTwoAngleAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t f),τ0.valueTraceL v⟫_ℝ := by
  let F := nativePrincipalTransposeJets (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t)
  let beta : R3 → R3 := fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)
  let M := referenceTwoAngleAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData i j k l t
  let U := referenceTwoAngleAdjointH2LiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t f
  have hbeta : ContDiff ℝ ∞ beta := SpatialJetFields.contDiff_spatial_slice _
    (referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData i j k l).1 t
  have hz : ∀ x, x ∉ closedBall (0 : R3) 3 → (-beta : R3 → R3) x=0 :=
    nativeSupportedNegativeDrift_zeroOutside beta (closedBall (0 : R3) 3)
      ((referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData i j k l).2 t)
  have hWeak : ∀ z : BallH1Zero, TauCeti.PDE.energyFormH1
      (mu := (volume : Measure R3)) (Omega := ballOpens) (coefficientMatrixField 2 F) (-beta)
      (coefficientValue 1 M) (TauCeti.Wkp.firstOrder 1 U) (z : BallH1)=0 := by
    intro z
    exact (referenceTwoAngleAdjointNativeCoefficient_energy_eq g L y0 Φ B ε C ρ H a w hData i j k l t
      (TauCeti.Wkp.firstOrder 1 U) (z : BallH1)).trans
        (referenceTwoAngleAdjointH2LiftFamily_homogeneous_weak_energy g L y0 Φ B ε C ρ H a w hData
          τ0 hcalc hreg hF i j k l t hOriginal f z)
  have hNative := nativeSupportedMass_homogeneous_full_test_energy hcalc τ0 F (-beta) hbeta.neg
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _) hz M U hWeak v
  exact (referenceTwoAngleAdjointNativeCoefficient_energy_eq g L y0 Φ B ε C ρ H a w hData i j k l t
    (TauCeti.Wkp.firstOrder 1 U) v).symm.trans hNative

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointNativeCoefficient_energy_eq
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleAdjointH2LiftFamily_full_test_energy_Green
