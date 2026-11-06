import Calderon.ActualReferenceConormalGreen
import Calderon.ActualReferenceWeakDirichletEvaluation
import Calderon.NativeZeroValueTrace

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

theorem referenceStrongDriftFamily_inverse_energy_of_isInvertible
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (q : ℝ) (p : R3 × ℝ)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p).IsInvertible)
    (f : BallSobolev 0) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun z => a ((q,p),z)) (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),z)) 0
      (TauCeti.Wkp.firstOrder 1
        ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p).inverse f : BallSobolev 2))
      (v : BallH1) = ⟪f,TauCeti.W1p.value (v : BallH1)⟫_ℝ := by
  let A := referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p
  let U : StrongDirichletSpace 0 := A.inverse f
  have hAU : referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p
      (U : BallSobolev 2) = f := hStrong.self_apply_inverse f
  have he := referenceOrdinaryStrongDriftFamily_full_test_energy_Green
    g L y0 Φ B ε C ρ H a w hData hcalc τ0 q p (U : BallSobolev 2) (v : BallH1)
  rw [hAU] at he
  simpa only [TauCeti.Wkp.value_zero,valueTraceL_zeroDirichlet,inner_zero_right,mul_zero,add_zero] using he

theorem eq_referenceStrongDriftFamily_inverse_projection_of_weak_forcing
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (q : ℝ) (p : R3 × ℝ)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,p)).IsInvertible)
    (f : BallSobolev 0) (U : BallH1Zero)
    (hU : ∀ v : BallH1Zero,
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun z => a ((q,p),z)) (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),z)) 0
        (U : BallH1) (v : BallH1) = ⟪f,TauCeti.W1p.value (v : BallH1)⟫_ℝ) :
    U = strongDirichletProjectionL 0
      ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p).inverse f) := by
  let Z : BallH1Zero := strongDirichletProjectionL 0
    ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p).inverse f)
  apply hWeak.injective
  apply ContinuousLinearMap.ext
  intro v
  have hleft := referenceWeakDirichletEnergyFamily_apply
    g L y0 Φ B ε C ρ H a w hData hcalc (q,p) U v
  have hright := referenceWeakDirichletEnergyFamily_apply
    g L y0 Φ B ε C ρ H a w hData hcalc (q,p) Z v
  have hp := strongDirichletProjectionL_apply 0
    ((referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p).inverse f)
  have hprojection := congrArg (fun u : BallH1 => TauCeti.PDE.energyFormH1
    (mu := (volume : Measure R3)) (Omega := ballOpens)
    (fun z => a ((q,p),z)) (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),z)) 0
    u (v : BallH1)) hp
  have hZ : TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun z => a ((q,p),z)) (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),z)) 0
      (Z : BallH1) (v : BallH1) = ⟪f,TauCeti.W1p.value (v : BallH1)⟫_ℝ :=
    hprojection.trans (referenceStrongDriftFamily_inverse_energy_of_isInvertible
      g L y0 Φ B ε C ρ H a w hData hcalc τ0 q p hStrong f v)
  exact hleft.trans ((hU v).trans (hZ.symm.trans hright.symm))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
