import Calderon.ActualHighSmoothMultiplierFixedTopology
import Calderon.ActualReferenceGaugeNormalHighCommutator
import Calderon.ActualReferenceGaugeTangentHighMultiplierCommutatorTopology

/-! Literal genuine high gain formula. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceHighSmoothMultiplierBoundaryCommutatorFamily
  referenceGaugeNormalHighCommutatorFamily referenceGaugeNormalThreeHalfMultiplierFamily
  referenceGaugeTangentSecondHighMultiplierCommutatorFamily nativeThreeHalfCoefficientMulL

def referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
    (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ)) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  referenceHighSmoothMultiplierBoundaryCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q p +
  (referenceGaugeNormalHighCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).comp
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q) -
  (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q).comp
    (referenceGaugeNormalHighCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p) +
  (p.2.2 ^ 2) • ((2 : ℝ) •
    (referenceGaugeTangentSecondHighMultiplierCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q p).comp
        (referenceGaugeNormalThreeHalfMultiplierFamily
          g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0 p).inverse)

attribute [local irreducible] referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
  referenceGaugeNormalHighInvertibleLocus referenceStrongDriftFamily

lemma contDiffAt_referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
    (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceGaugeNormalHighInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc) :
    ContDiffAt ℝ ∞ (referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q) p := by
  have hRoom := hp
  unfold referenceGaugeNormalHighInvertibleLocus at hRoom
  have hB := contDiffAt_referenceHighSmoothMultiplierBoundaryCommutatorFamily_fixed
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q p hRoom.1 hRoom.2
  have hK := contDiffAt_referenceGaugeNormalHighCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 p hp
  have hT := (contDiff_referenceGaugeTangentSecondHighMultiplierCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Q).contDiffAt (x := p)
  have hW := (contDiff_referenceGaugeNormalThreeHalfMultiplierFamily_inverse
    g L Φ y0 B ε C ρ H a w hData hg hcalc hF hO hD τ0).contDiffAt (x := p)
  have hR : ContDiffAt ℝ ∞ (fun z : ℝ × (R3 × ℝ) => z.2.2 ^ 2) p := by fun_prop
  unfold referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
  exact ((hB.add (hK.clm_comp contDiffAt_const)).sub
    (contDiffAt_const.clm_comp hK)).add (hR.smul ((hT.clm_comp hW).const_smul (2 : ℝ)))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
