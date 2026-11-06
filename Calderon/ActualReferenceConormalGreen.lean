import Calderon.NativeWeightedDriftFluxGreen
import Calderon.ActualReferenceStrongRoom

/-! Expanded before source in EXPANSION-actual-reference-conormal-strong-compatibility-v001.json.
Author draft; no checked acceptance claimed. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativePolynomialBulkMoments
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceConormalTraceFamily (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (q : ℝ) (p : R3 × ℝ) : BallSobolev 2 →L[ℝ] SphereL2 :=
  let h := jointFixedParameterSlice_data g L y0 Φ B ε C ρ H a w hData q
  ordinaryConormalTraceL hcalc τ0
    (commonSupportMatrixFamily 2 (jointFixedParameterSlice a q) h.1
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.1 p)

lemma referenceOrdinaryStrongDriftFamily_full_test_energy_Green
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (q : ℝ) (p : R3 × ℝ) (U : BallSobolev 2) (v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun z => a ((q,p),z))
      (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),z)) 0
      (TauCeti.Wkp.firstOrder 1 U) v =
        ⟪TauCeti.Wkp.value 0
          (referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p U),
            TauCeti.W1p.value v⟫_ℝ +
          sphereSurfaceMass * ⟪referenceConormalTraceFamily
            g L y0 Φ B ε C ρ H a w hData hcalc τ0 q p U,τ0.valueTraceL v⟫_ℝ := by
  let h := jointFixedParameterSlice_data g L y0 Φ B ε C ρ H a w hData q
  have he := ordinaryStrongDriftFamily_full_test_energy_Green hcalc τ0
    (jointFixedParameterSlice a q) h.1 (jointFixedParameterSlice w q) h.2.1
    (jointFixedParameterSlice (conformalReferenceFramedDriftBase g L Φ H) q) h.2.2.1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.1 h.2.2.2.2 L p U v
  rw [weightedDriftSlice_reference_eq g L y0 Φ B ε C ρ H a w hData q p] at he
  exact he

lemma referenceHarmonicLiftFamily_full_test_energy_Green
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (q : ℝ) (p : R3 × ℝ)
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p).IsInvertible)
    (E : BallSobolev 2) (v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun z => a ((q,p),z))
      (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),z)) 0
      (TauCeti.Wkp.firstOrder 1
        (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p E)) v =
      sphereSurfaceMass * ⟪referenceConormalTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc τ0 q p
        (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p E),τ0.valueTraceL v⟫_ℝ := by
  have hk : referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p
      (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p E) = 0 :=
    guardedHarmonicLiftFamily_kernel _ _ _ p hi rfl E
  rw [referenceOrdinaryStrongDriftFamily_full_test_energy_Green
    g L y0 Φ B ε C ρ H a w hData hcalc τ0 q p, hk]
  have hz : TauCeti.Wkp.value (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2) 0 0 = 0 :=
    (TauCeti.Wkp.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) 0).map_zero
  rw [hz,inner_zero_left,zero_add]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceConormalTraceFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceOrdinaryStrongDriftFamily_full_test_energy_Green
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHarmonicLiftFamily_full_test_energy_Green
