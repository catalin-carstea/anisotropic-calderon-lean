import Calderon.ActualReferenceStrongRoom
import Calderon.SupportedStrongOperatorEnergy
import Calderon.ReferenceSupportedEnergyBridge

/-! Actual native energy decomposition; no inverse or energy premise is added. -/
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

theorem referenceStrongDriftFamily_energy_of_elliptic
    (hcalc : FixedSobolevCalculus) (s : ℕ) (q : ℝ) (p : R3 × ℝ) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (fun z => a ((q,p),z)) lam Lam)
    (U : StrongDirichletSpace s) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p U)) v =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) (fun z => a ((q,p),z))
      (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),z)) 0
      (TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) (s+1)
        (U : BallSobolev (s+2))) (v : BallH1) := by
  let h := jointFixedParameterSlice_data g L y0 Φ B ε C ρ H a w hData q
  let D : StrongDirichletSpace s →L[ℝ] BallSobolev s :=
    commonSupportSupportedStrongOperatorL hcalc s (jointFixedParameterSlice a q) h.1
      (jointFixedParameterSlice w q) h.2.1
      (jointFixedParameterSlice (conformalReferenceFramedDriftBase g L Φ H) q) h.2.2.1
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.1 h.2.2.2.2 L p
  have hAD : referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p = D :=
    referenceStrongDriftFamily_eq_supportedOperator g L y0 Φ B ε C ρ H a w hData hcalc s q p
  have hForcing := congrArg (fun T : StrongDirichletSpace s →L[ℝ] BallSobolev s =>
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s (T U)) v) hAD
  have hNative := commonSupportSupportedStrongOperatorL_energy_of_elliptic hcalc s
    (jointFixedParameterSlice a q) h.1 (jointFixedParameterSlice w q) h.2.1
    (jointFixedParameterSlice (conformalReferenceFramedDriftBase g L Φ H) q) h.2.2.1
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _) h.2.2.2.1 h.2.2.2.2
    L p lam Lam hUE U v
  have he := hForcing.trans hNative
  rw [weightedDriftSlice_reference_eq g L y0 Φ B ε C ρ H a w hData q p] at he
  exact he


theorem referenceStrongDriftFamily_inverse_energy
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (s : ℕ) (q : ℝ) (p : R3 × ℝ) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (fun z => a ((q,p),z)) lam Lam)
    (hsmall : ∀ z ∈ (ballOpens : Set R3),
      ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),z)‖ ≤ lam/4)
    (f : BallSobolev s) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) (fun z => a ((q,p),z))
      (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),z)) 0
      (TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) (s+1)
        ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p).inverse f :
          BallSobolev (s+2)))
      (v : BallH1) = TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) (TauCeti.Wkp.value (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) s f) v := by
  have hi := referenceStrongDriftFamily_isInvertible_of_smallDrift
    g L y0 Φ B ε C ρ H a w hData hcalc hreg s q p lam Lam hUE hsmall
  have he := referenceStrongDriftFamily_energy_of_elliptic
    g L y0 Φ B ε C ρ H a w hData hcalc s q p lam Lam hUE
    ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p).inverse f) v
  rw [hi.self_apply_inverse f] at he
  exact he.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
