import Calderon.ActualReferenceDegreeRotationWitness
import Calderon.SphereSobolevRotationCommutatorHighLift

/-! Full upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-actual-degree-rotation-witness-and-high-gain-v132.md. Genuine native high degree endpoint. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotation
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceRadialDegreeCommutatorHalfFamily
  referenceTwoAngleDegreeRotationDerivativeFamily

def referenceRadialDegreeCommutatorGainedHighFamily
    (p : ℝ × (R3 × ℝ)) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  sphereSobolevRotationCommutatorHighLiftL
    (referenceRadialDegreeCommutatorHalfFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p)
    (fun k l => referenceTwoAngleDegreeRotationDerivativeFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l p)

lemma referenceRadialDegreeCommutatorGainedHighFamily_lower_compatibility
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (referenceRadialDegreeCommutatorGainedHighFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p) =
    (referenceRadialDegreeCommutatorHalfFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  sphereSobolevRotationCommutatorHighLiftL_lower_compatibility _ _
    (fun u k l => referenceTwoAngleDegreeRotationDerivativeFamily_distribution_witness
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l p hp u)

lemma norm_referenceRadialDegreeCommutatorGainedHighFamily_le
    (p : ℝ × (R3 × ℝ)) :
    ‖referenceRadialDegreeCommutatorGainedHighFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p‖ ≤
    19*‖referenceRadialDegreeCommutatorHalfFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p‖ +
    Real.sqrt 2*∑ k : Fin 3, ∑ l : Fin 3,
      ‖referenceTwoAngleDegreeRotationDerivativeFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l p‖ :=
  norm_sphereSobolevRotationCommutatorHighLiftL_le _ _

lemma contDiffAt_referenceRadialDegreeCommutatorGainedHighFamily
    (p : ℝ × (R3 × ℝ))
    (hp : p ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (referenceRadialDegreeCommutatorGainedHighFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0) p := by
  have hC := contDiffAt_referenceRadialDegreeCommutatorHalfFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 p hp
  have hDij (k l : Fin 3) := contDiffAt_referenceTwoAngleDegreeRotationDerivativeFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 k l p hp
  unfold referenceRadialDegreeCommutatorGainedHighFamily sphereSobolevRotationCommutatorHighLiftL
  apply ContDiffAt.add
  · exact contDiffAt_const.clm_comp (hC.clm_comp contDiffAt_const)
  · apply ContDiffAt.sum
    intro k hk
    apply ContDiffAt.sum
    intro l hl
    exact contDiffAt_const.clm_comp
      ((hC.clm_comp contDiffAt_const).add ((hDij k l).clm_comp contDiffAt_const))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialDegreeCommutatorGainedHighFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialDegreeCommutatorGainedHighFamily_lower_compatibility
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_referenceRadialDegreeCommutatorGainedHighFamily_le
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceRadialDegreeCommutatorGainedHighFamily
