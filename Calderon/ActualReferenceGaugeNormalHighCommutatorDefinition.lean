import Calderon.ActualReferenceGaugeNormalThreeHalfMultiplier
import Calderon.ActualReferenceGaugeNormalHalfCommutator
import Calderon.ActualHighSmoothMultiplierBoundaryTopology

/-! Full upfront: general-boundary-multiplier-commutator-author-oct15-v001/
EXPANSION-actual-gauge-high-K-and-D-v092.md. Actual high K, negative native B
sign, right high reciprocal, independent joint topology, physical lower graph. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3)
  (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

def referenceGaugeNormalHighInvertibleLocus (hcalc : FixedSobolevCalculus) :
    Set (ℝ × (R3 × ℝ)) :=
  {p | (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2).IsInvertible ∧
    (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible}

lemma isOpen_referenceGaugeNormalHighInvertibleLocus (hcalc : FixedSobolevCalculus) :
    IsOpen (referenceGaugeNormalHighInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc) := by
  letI : CompleteSpace (StrongDirichletSpace 1) := instCompleteSpaceStrongDirichletSpace 1
  have hOne : IsOpen {p : ℝ × (R3 × ℝ) |
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2).IsInvertible} :=
    ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage
      (contDiff_joint_referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1).continuous
  have hZero := isOpen_referenceStrongDriftFamily_zero_invertible_set
    g L y0 Φ B ε C ρ H a w hData hcalc
  exact hOne.inter hZero

variable (hg : IsAdmissibleMetric g)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

def referenceGaugeNormalHighCommutatorFamily (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  -((referenceHighSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
        (referenceGaugeNormalCoefficientJetsFamily g L Φ y0 B ε C ρ H a w hData hg 3 p) p).comp
    (referenceGaugeNormalThreeHalfMultiplierFamily
      g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeNormalHighInvertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.isOpen_referenceGaugeNormalHighInvertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceGaugeNormalHighCommutatorFamily
