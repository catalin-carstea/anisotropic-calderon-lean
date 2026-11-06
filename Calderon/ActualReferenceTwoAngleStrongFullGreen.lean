import Calderon.NativeSmoothSharpTraceCompletion
import Calderon.ActualReferenceTwoAngleStrongEnergy
import Calderon.ActualReferenceTwoAngleHarmonicLiftTopology
import Calderon.NativeHarmonicLiftOrderCoherence
import Calderon.NativeH2CoefficientFluxGreen
import Calderon.NativeHarmonicHalfCoarseDualPairing
import Calderon.NativeHalfTraceRightInverse

/-! Exact original full Green statements. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion
  NativeHarmonicH1LiftCompletion NativeHarmonicLiftOrderCoherence
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


open NativePolynomialBulkMoments NativeHarmonicHalfCoarseDualPairing
  NativeFullSharpHalfTrace NativeHalfTraceRightInverse

lemma referenceTwoAngleOrdinaryStrongFamily_full_test_energy_Green
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) (U : BallSobolev 2) (v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
      (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) 0
      (TauCeti.Wkp.firstOrder 1 U) v =
    ⟪TauCeti.Wkp.value 0 (referenceTwoAngleOrdinaryStrongFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t U),TauCeti.W1p.value v⟫_ℝ +
    sphereSurfaceMass * ⟪ordinaryConormalTraceL hcalc τ0
      (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t) U,
      τ0.valueTraceL v⟫_ℝ := by
  let F := referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t
  let G := fun d => referenceTwoAngleDriftJetsFamily g L y0 Φ B ε C ρ H a w hData 1 i j k l d t
  let beta := fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)
  have hd := referenceTwoAngleDrift_data g L y0 Φ B ε C ρ H a w hData i j k l
  have hbeta : ContDiff ℝ ∞ beta := hd.1.comp (contDiff_const.prodMk contDiff_id)
  have hsplit := coefficient_energyFormH1_eq_principal_add_supportedDrift_inner
    hcalc F beta hbeta (closedBall (0 : R3) 3) (isCompact_closedBall _ _) (hd.2 t)
      (TauCeti.Wkp.firstOrder 1 U) v
  have hP := ordinaryPrincipalL_full_test_energy_Green hcalc τ0 F U v
  have hD := value_fullDriftMultiplierSum_eq_supportedDriftL hcalc G beta hbeta
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _) (hd.2 t)
    (fun d x => coefficientValue_referenceTwoAngleDriftJetsFamily
      g L y0 Φ B ε C ρ H a w hData 1 i j k l d t x) U
  have hfield : coefficientMatrixField 2 F =
      (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x)) :=
    coefficientMatrixField_referenceTwoAnglePrincipalJetsFamily
      g L y0 Φ B ε C ρ H a w hData 2 i j k l t
  rw [hP,← hD,hfield] at hsplit
  have hSum : TauCeti.Wkp.value 0 (referenceTwoAngleOrdinaryStrongFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t U) =
    TauCeti.Wkp.value 0 (ordinaryPrincipalL hcalc 0 F U) +
    TauCeti.Wkp.value 0 ((∑ d : Fin 3, (coefficientMultiplier hcalc 0 (G d)).comp
      (ordinaryLowerOrderCoordinateDerivativeL hcalc 0 d)) U) := by
    change TauCeti.Wkp.valueL 0 ((ordinaryPrincipalL hcalc 0 F U) + _) = _
    exact (TauCeti.Wkp.valueL 0).map_add _ _
  rw [hSum,inner_add_left]
  exact hsplit.trans (by ring)

lemma referenceTwoAngleHarmonicLiftFamily_normalized_full_test_energy_Green
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hStrong : (referenceTwoAngleStrongDirichletFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible)
    (E : BallSobolev 2) (v : BallH1) :
    sphereSurfaceMass⁻¹ * TauCeti.PDE.energyFormH1
      (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => referenceTwoAnglePrincipalFamily a i j k l (t,x))
      (fun x => referenceTwoAngleDriftFamily g L Φ H w i j k l (t,x)) 0
      (TauCeti.Wkp.firstOrder 1 (referenceTwoAngleHarmonicLiftFamily
        g L y0 Φ B ε C ρ H a w hData hcalc i j k l t E)) v =
    ⟪ordinaryConormalTraceL hcalc τ0
      (referenceTwoAnglePrincipalJetsFamily g L y0 Φ B ε C ρ H a w hData 2 i j k l t)
      (referenceTwoAngleHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t E),
      τ0.valueTraceL v⟫_ℝ := by
  have he := referenceTwoAngleOrdinaryStrongFamily_full_test_energy_Green
    g L y0 Φ B ε C ρ H a w hData hcalc τ0 i j k l t
      (referenceTwoAngleHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l t E) v
  rw [referenceTwoAngleHarmonicLiftFamily_kernel
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l t hStrong E,
    TauCeti.Wkp.value_zero,inner_zero_left,zero_add] at he
  have hn := congrArg (fun x : ℝ => sphereSurfaceMass⁻¹*x) he
  rw [← mul_assoc,inv_mul_cancel₀ NativeSmoothSharpTraceCompletion.sphereSurfaceMass_pos.ne',one_mul] at hn
  exact hn

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleOrdinaryStrongFamily_full_test_energy_Green
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleHarmonicLiftFamily_normalized_full_test_energy_Green
