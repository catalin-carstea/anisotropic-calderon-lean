import Calderon.ActualReferenceOrthogonalStrongLift
import Calderon.ActualReferenceOrthogonalWeakData
import Calderon.ActualReferenceInvertibleStrongWeakCoherence

/-! Expanded first in EXPANSION-actual-reference-orthogonal-strong-lift-author-v001.json. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicLiftCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma firstOrder_referenceOrthogonalStrongHarmonicLift_eq_nativeWeakHalfLift
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (τ0 : UnitBallValueTrace)
    (e : R3 ≃ₗᵢ[ℝ] R3) (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) :
    TauCeti.Wkp.firstOrder 1 (referenceOrthogonalStrongHarmonicLift
      g L y0 Φ B ε C ρ H a w hData hcalc hF e p f) =
    referenceOrthogonalNativeWeakHalfLift g L y0 Φ B ε C ρ H a w hData hF e p
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) := by
  let f' := sphereSobolevOrthogonalPullbackL (3/2:ℝ) e.symm f
  have hco := firstOrder_referenceHarmonicLiftFamily_eq_weakHalfLift_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO τ0 p.1 p.2 hStrong hWeak f'
  rw [TauCeti.Wkp.firstOrderL_apply,
    referenceWeakHalfLiftFamily_eq_nativeWeakHalfLift g L y0 Φ B ε C ρ H a w hData hcalc hF p
      (referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p)] at hco
  have hcov := nativeWeakHalfLift_orthogonal_covariance e (fun x => a (p,x))
    (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0
    (continuous_referenceNativePrincipal g L y0 Φ B ε C ρ H a w hData p)
    (continuous_referenceNativeDrift g L y0 Φ B ε C ρ H a w hData p) continuous_const
    (referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p)
    (referenceOrthogonalNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData e p) hF hO
    (referenceNativeEnergy_isInvertible g L y0 Φ B ε C ρ H a w hData hcalc p hWeak)
    (referenceOrthogonalNativeEnergy_isInvertible g L y0 Φ B ε C ρ H a w hData hcalc e p hWeak)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f')
  have hcancel := sphereSobolevOrthogonalPullback_inclusion_inverse
    (3/2:ℝ) (1/2:ℝ) (by norm_num) e f
  have hFirst := firstOrder_referenceOrthogonalStrongHarmonicLift
    g L y0 Φ B ε C ρ H a w hData hcalc hF e p f
  have hPull := congrArg (nativeH1OrthogonalPullback e) hco
  have hRight := hcov.trans (congrArg
    (referenceOrthogonalNativeWeakHalfLift g L y0 Φ B ε C ρ H a w hData hF e p) hcancel)
  exact hFirst.trans (hPull.trans hRight)

lemma referenceOrthogonalStrongHarmonicLift_weak_solution
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (τ0 : UnitBallValueTrace)
    (e : R3 ≃ₗᵢ[ℝ] R3) (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible)
    (f : SphereSobolev (3/2:ℝ)) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (orthogonalPrincipalCoefficient e (fun z => a (p,z)))
      (orthogonalDriftCoefficient e (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)))
      ((0 : R3 → ℝ) ∘ e)
      (TauCeti.Wkp.firstOrder 1 (referenceOrthogonalStrongHarmonicLift
        g L y0 Φ B ε C ρ H a w hData hcalc hF e p f)) (v : BallH1) = 0 := by
  have hLift := firstOrder_referenceOrthogonalStrongHarmonicLift_eq_nativeWeakHalfLift
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO τ0 e p hStrong hWeak f
  have hEnergy := congrArg (fun U : BallH1 =>
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (orthogonalPrincipalCoefficient e (fun z => a (p,z)))
      (orthogonalDriftCoefficient e (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)))
      ((0 : R3 → ℝ) ∘ e) U (v : BallH1)) hLift
  have hNative := nativeWeakHalfLift_weak_solution
    (orthogonalPrincipalCoefficient e (fun z => a (p,z)))
    (orthogonalDriftCoefficient e (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)))
    ((0 : R3 → ℝ) ∘ e)
    (referenceOrthogonalNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData e p) hF
    (referenceOrthogonalNativeEnergy_isInvertible g L y0 Φ B ε C ρ H a w hData hcalc e p hWeak)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) f) v

  exact hEnergy.trans hNative

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.firstOrder_referenceOrthogonalStrongHarmonicLift_eq_nativeWeakHalfLift
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceOrthogonalStrongHarmonicLift_weak_solution
