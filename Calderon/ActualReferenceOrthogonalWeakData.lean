import Calderon.ActualReferenceNativeWeakHalfLift
import Calderon.NativeWeakHalfLiftOrthogonalCovariance
import Calderon.NativeOrthogonalZeroEnergyInvertibility

/-! The coefficient-data part of the orthogonal strong/weak coherence. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

include hData

lemma continuous_referenceNativePrincipal (p : ℝ × (R3 × ℝ)) :
    Continuous (fun x : R3 => a (p,x)) :=
  (jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData).1.continuous.comp
    (continuous_const.prodMk continuous_id)

lemma continuous_referenceNativeDrift (p : ℝ × (R3 × ℝ)) :
    Continuous (fun x : R3 => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) :=
  (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1.continuous.comp
    (continuous_const.prodMk continuous_id)

lemma referenceOrthogonalNativeEnergy_memLp (e : R3 ≃ₗᵢ[ℝ] R3) (p : ℝ × (R3 × ℝ)) :
    MemLp (fun x => TauCeti.PDE.energyIntegrand
      (orthogonalPrincipalCoefficient e (fun z => a (p,z)) x)
      (orthogonalDriftCoefficient e (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)) x)
      (((0 : R3 → ℝ) ∘ e) x)) ⊤ ((volume : Measure R3).restrict ballOpens) :=
  memLp_nativeOrthogonalEnergyIntegrand_of_continuous e (fun z => a (p,z))
    (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)) 0
    (continuous_referenceNativePrincipal g L y0 Φ B ε C ρ H a w hData p)
    (continuous_referenceNativeDrift g L y0 Φ B ε C ρ H a w hData p) continuous_const

def referenceOrthogonalNativeWeakHalfLift
    (hF : SphereFischerInner) (e : R3 ≃ₗᵢ[ℝ] R3) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 :=
  nativeWeakHalfLift (orthogonalPrincipalCoefficient e (fun z => a (p,z)))
    (orthogonalDriftCoefficient e (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)))
    ((0 : R3 → ℝ) ∘ e) (referenceOrthogonalNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData e p) hF

lemma referenceNativeEnergy_isInvertible
    (hcalc : FixedSobolevCalculus) (p : ℝ × (R3 × ℝ))
    (hi : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := fun x => a (p,x))
      (b := fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) (c := 0)
      (referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p)).IsInvertible := by
  apply (nativeZeroCoefficientEnergyL_isInvertible_iff
    (fun x => a (p,x))
    (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) 0
    (referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p)).mp
  have hA := referenceWeakDirichletEnergyFamily_eq_nativeEnergyFormH1L0
    g L y0 Φ B ε C ρ H a w hData hcalc p
    (referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p)
  exact Eq.mp (congrArg
    (fun T : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => T.IsInvertible) hA) hi

lemma referenceOrthogonalNativeEnergy_isInvertible
    (hcalc : FixedSobolevCalculus) (e : R3 ≃ₗᵢ[ℝ] R3) (p : ℝ × (R3 × ℝ))
    (hi : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (a := orthogonalPrincipalCoefficient e (fun z => a (p,z)))
      (b := orthogonalDriftCoefficient e (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)))
      (c := (0 : R3 → ℝ) ∘ e)
      (referenceOrthogonalNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData e p)).IsInvertible :=
  energyFormH1L0_orthogonal_isInvertible e (fun z => a (p,z))
    (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)) 0
    (referenceNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData p)
    (referenceOrthogonalNativeEnergy_memLp g L y0 Φ B ε C ρ H a w hData e p)
    (referenceNativeEnergy_isInvertible g L y0 Φ B ε C ρ H a w hData hcalc p hi)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.continuous_referenceNativePrincipal
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.continuous_referenceNativeDrift
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceOrthogonalNativeEnergy_memLp
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceOrthogonalNativeWeakHalfLift
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceNativeEnergy_isInvertible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceOrthogonalNativeEnergy_isInvertible
