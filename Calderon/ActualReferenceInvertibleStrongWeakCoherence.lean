import Calderon.ActualReferenceConormalGreen
import Calderon.ActualReferenceStrongWeakHalfCoherence
import Calderon.NativeInvertibleWeakLiftUniqueness

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativePolynomialBulkMoments
  NativeHarmonicLiftCompletion NativeHarmonicH1LiftCompletion NativeHarmonicLiftOrderCoherence
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


lemma eq_referenceWeakHalfLiftFamily_of_weak_energy_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ))
    (hi : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (1/2:ℝ)) (U : BallH1)
    (hzero : harmonicFirstOrderLiftCompletion hF f-U ∈
      TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2)
    (hweak : ∀ v : BallH1Zero,
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun z => a (p,z)) (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)) 0 U (v : BallH1) = 0) :
    U = referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p f := by
  have he := eq_sub_functionalInverse_of_restriction_isInvertible
    (referenceWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p)
    (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p) hi
    (referenceWeakDirichletEnergyFamily_apply_reference g L y0 Φ B ε C ρ H a w hData hcalc p)
    (harmonicFirstOrderLiftCompletion hF f) U hzero
    (fun v => (referenceWeakEnergyFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc p U v).trans (hweak v))
  exact he.trans
    (referenceWeakHalfLiftFamily_apply g L y0 Φ B ε C ρ H a w hData hcalc hF p f).symm

lemma referenceHarmonicLiftFamily_weak_energy_of_isInvertible
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
    (q : ℝ) (p : R3 × ℝ)
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p).IsInvertible)
    (E : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun z => a ((q,p),z))
      (fun z => conformalReferenceWeightedFramedDrift g L Φ H w ((q,p),z)) 0
      (TauCeti.Wkp.firstOrder 1
        (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p E)) (v : BallH1) = 0 := by
  have he := referenceHarmonicLiftFamily_full_test_energy_Green
    g L y0 Φ B ε C ρ H a w hData hcalc τ0 q p hi E (v : BallH1)
  simpa only [valueTraceL_zeroDirichlet,inner_zero_right,mul_zero] using he

lemma firstOrder_referenceHarmonicLiftFamily_eq_weakHalfLift_of_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (p : R3 × ℝ)
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,p)).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    TauCeti.Wkp.firstOrderL 1
      (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p
        (harmonicLiftCompletion hF f)) =
      referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF (q,p)
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) := by
  apply eq_referenceWeakHalfLiftFamily_of_weak_energy_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF (q,p) hWeak
  · have hd := referenceHarmonicLiftFamily_boundary_difference
      g L y0 Φ B ε C ρ H a w hData hcalc 0 q p hStrong (harmonicLiftCompletion hF f)
    have hd' : TauCeti.Wkp.firstOrderL 1
        (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 q p
          (harmonicLiftCompletion hF f)) - TauCeti.Wkp.firstOrderL 1 (harmonicLiftCompletion hF f) ∈
          TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
      rw [← map_sub]
      exact hd
    have hn := (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).neg_mem hd'
    rw [neg_sub,firstOrder_harmonicLiftCompletion hF hO] at hn
    exact hn
  · intro v
    exact referenceHarmonicLiftFamily_weak_energy_of_isInvertible
      g L y0 Φ B ε C ρ H a w hData hcalc τ0 q p hStrong (harmonicLiftCompletion hF f) v

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.eq_referenceWeakHalfLiftFamily_of_weak_energy_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHarmonicLiftFamily_weak_energy_of_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.firstOrder_referenceHarmonicLiftFamily_eq_weakHalfLift_of_isInvertible
