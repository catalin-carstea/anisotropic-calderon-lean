import Calderon.ActualReferenceRotationAdjointRadialEndpointFamilies
import Calderon.ActualReferenceSharpMidpointRadialTrace
import Calderon.SphereSobolevCompatibleInterpolationTopology
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

/-! Fully expanded before source in EXPANSION-actual-reference-sharp-midpoint-family-v001.json.
Actual same retained coefficient a, no parameter-dependent bound choices in the maps. -/
def referenceRotationAdjointRadialEndpointPairFamily (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (iA jA : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) : SphereSobolevEndpointPair :=
  (referenceRotationAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t,referenceRotationAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t)

lemma referenceRotationAdjointRadialEndpointPairFamily_mem_compatible (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (iA jA : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) (hp : t ∈ (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)) :
    referenceRotationAdjointRadialEndpointPairFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t ∈ sphereSobolevCompatibleEndpoints := by
  change (sphereSobolevInclusionL (1/2 : ℝ) (-1/2 : ℝ) (by norm_num)).comp
      (referenceRotationAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t) =
    (referenceRotationAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t).comp
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num))
  have hInc := sphereSobolevInclusionL_negative_half_notation_eq (1/2 : ℝ)
    (by norm_num) (by norm_num)
  have hComp := congrArg
    (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      A.comp (referenceRotationAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t)) hInc
  exact hComp.trans
    (referenceRotationAdjointRadialEndpointFamily_high_half_compatibility g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA hreg t hp.2.2.1)

def referenceRotationAdjointMidpointRadialFamily (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (iA jA : Fin 3) :
    (ℝ × (ℝ × (R3 × ℝ))) → (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
  sphereSobolevCompatibleInterpolationFamily (referenceRotationAdjointRadialEndpointPairFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA) (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) (referenceRotationAdjointRadialEndpointPairFamily_mem_compatible g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 iA jA)

lemma referenceRotationAdjointMidpointRadialFamily_of_mem (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (iA jA : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) (hp : t ∈ (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)) :
    referenceRotationAdjointMidpointRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 iA jA t = sphereSobolevMidpointL (referenceRotationAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t) (referenceRotationAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t) (referenceRotationAdjointRadialEndpointPairFamily_mem_compatible g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 iA jA t hp) :=
  sphereSobolevCompatibleInterpolationFamily_of_mem (referenceRotationAdjointRadialEndpointPairFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA) (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) (referenceRotationAdjointRadialEndpointPairFamily_mem_compatible g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 iA jA) t hp

lemma referenceRotationAdjointMidpointRadialFamily_lower_inclusion (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (iA jA : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) (hp : t ∈ (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)) :
    (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)).comp (referenceRotationAdjointMidpointRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 iA jA t) =
      (referenceRotationAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t).comp (sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num)) := by
  rw [referenceRotationAdjointMidpointRadialFamily_of_mem g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 iA jA t hp]
  have hInc := sphereSobolevInclusionL_negative_half_notation_eq (0 : ℝ)
    (by norm_num) (by norm_num)
  have hComp := congrArg
    (fun A : SphereSobolev 0 →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      A.comp (sphereSobolevMidpointL (referenceRotationAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t) (referenceRotationAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t) (referenceRotationAdjointRadialEndpointPairFamily_mem_compatible g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 iA jA t hp))) hInc.symm
  exact hComp.trans
    (sphereSobolevInclusionL_midpoint (referenceRotationAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t) (referenceRotationAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t) (referenceRotationAdjointRadialEndpointPairFamily_mem_compatible g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 iA jA t hp))

lemma referenceRotationAdjointMidpointRadialFamily_upper_inclusion (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (iA jA : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) (hp : t ∈ (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)) :
    (referenceRotationAdjointMidpointRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 iA jA t).comp (sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)).comp (referenceRotationAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t) := by
  rw [referenceRotationAdjointMidpointRadialFamily_of_mem g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 iA jA t hp]
  exact sphereSobolevMidpointL_inclusion (referenceRotationAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t) (referenceRotationAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t) (referenceRotationAdjointRadialEndpointPairFamily_mem_compatible g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 iA jA t hp)

lemma norm_referenceRotationAdjointMidpointRadialFamily_le (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (iA jA : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) (hp : t ∈ (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)) :
    ‖referenceRotationAdjointMidpointRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 iA jA t‖ ≤ (‖referenceRotationAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t‖+‖referenceRotationAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t‖)/2 := by
  rw [referenceRotationAdjointMidpointRadialFamily_of_mem g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 iA jA t hp]
  exact norm_sphereSobolevMidpointL_le (referenceRotationAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t) (referenceRotationAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA t) (referenceRotationAdjointRadialEndpointPairFamily_mem_compatible g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 iA jA t hp)

lemma contDiffOn_referenceRotationAdjointMidpointRadialFamily_invertibleLocus (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (iA jA : Fin 3) :
    ContDiffOn ℝ ∞ (referenceRotationAdjointMidpointRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 iA jA) (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  have hPair : ContDiffOn ℝ ∞ (referenceRotationAdjointRadialEndpointPairFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA) (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
    (contDiffOn_referenceRotationAdjointHalfRadialFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA).prodMk
      (contDiffOn_referenceRotationAdjointThreeHalfRadialFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA hreg)
  exact contDiffOn_sphereSobolevCompatibleInterpolationFamily (referenceRotationAdjointRadialEndpointPairFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 iA jA) (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (isOpen_univ.prod (isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)) (referenceRotationAdjointRadialEndpointPairFamily_mem_compatible g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 iA jA) hPair

lemma contDiffAt_referenceRotationAdjointMidpointRadialFamily (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (iA jA : Fin 3) (t : ℝ × (ℝ × (R3 × ℝ))) (hp : t ∈ (Set.univ ×ˢ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)) :
    ContDiffAt ℝ ∞ (referenceRotationAdjointMidpointRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 iA jA) t :=
  (contDiffOn_referenceRotationAdjointMidpointRadialFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 iA jA).contDiffAt
    ((isOpen_univ.prod (isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)).mem_nhds hp)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointRadialEndpointPairFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointRadialEndpointPairFamily_mem_compatible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointMidpointRadialFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointMidpointRadialFamily_of_mem
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointMidpointRadialFamily_lower_inclusion
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRotationAdjointMidpointRadialFamily_upper_inclusion
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_referenceRotationAdjointMidpointRadialFamily_le
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceRotationAdjointMidpointRadialFamily_invertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceRotationAdjointMidpointRadialFamily
