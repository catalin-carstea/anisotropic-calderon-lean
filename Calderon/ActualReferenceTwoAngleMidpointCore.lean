import Calderon.ActualReferenceTwoAngleRadialRoom
import Calderon.ActualReferenceTwoAngleEndpointCompatibility
import Calderon.ActualReferenceSharpMidpointRadialTrace

/-! Actual compatible primal midpoint. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

open Filter
open scoped Topology

open SphereHarmonic

def referenceTwoAngleRadialEndpointPairFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) : SphereSobolevEndpointPair :=
  (referenceTwoAngleLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t,
   referenceTwoAngleSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t)

lemma referenceTwoAngleRadialEndpointPairFamily_mem_compatible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hp : t ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) :
    referenceTwoAngleRadialEndpointPairFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t ∈ sphereSobolevCompatibleEndpoints := by
  change (sphereSobolevInclusionL (1/2:ℝ) (-1/2:ℝ) (by norm_num)).comp
      (referenceTwoAngleSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t) =
    (referenceTwoAngleLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  have hInc := sphereSobolevInclusionL_negative_half_notation_eq (1/2:ℝ) (by norm_num) (by norm_num)
  have hComp := congrArg
    (fun A : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
      A.comp (referenceTwoAngleSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t)) hInc
  have hOrig := hp.1.2.2
  exact hComp.trans (referenceTwoAngleSharpRadialTraceFamily_lower_compatibility
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t hOrig.2.2 hOrig.2.1 hp.2)

def referenceTwoAngleSharpMidpointRadialTraceFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3) : (ℝ × (ℝ × (ℝ × (R3 × ℝ)))) → (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
  sphereSobolevCompatibleInterpolationFamily
    (referenceTwoAngleRadialEndpointPairFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
    (referenceTwoAngleRadialInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
    (referenceTwoAngleRadialEndpointPairFamily_mem_compatible g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)

lemma referenceTwoAngleSharpMidpointRadialTraceFamily_of_mem
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hp : t ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) :
    referenceTwoAngleSharpMidpointRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t =
    sphereSobolevMidpointL
      (referenceTwoAngleLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t)
      (referenceTwoAngleSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t)
      (referenceTwoAngleRadialEndpointPairFamily_mem_compatible g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t hp) :=
  sphereSobolevCompatibleInterpolationFamily_of_mem
    (referenceTwoAngleRadialEndpointPairFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
    (referenceTwoAngleRadialInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l)
    (referenceTwoAngleRadialEndpointPairFamily_mem_compatible g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) t hp

lemma referenceTwoAngleSharpMidpointRadialTraceFamily_upper_inclusion
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hp : t ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) :
    (referenceTwoAngleSharpMidpointRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t).comp
      (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      (referenceTwoAngleSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t) := by
  rw [referenceTwoAngleSharpMidpointRadialTraceFamily_of_mem g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t hp]
  exact sphereSobolevMidpointL_inclusion _ _ _

lemma referenceTwoAngleSharpMidpointRadialTraceFamily_lower_inclusion
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hp : t ∈ referenceTwoAngleRadialInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (referenceTwoAngleSharpMidpointRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t) =
    (referenceTwoAngleLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t).comp
      (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  rw [referenceTwoAngleSharpMidpointRadialTraceFamily_of_mem g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t hp]
  have hInc := sphereSobolevInclusionL_negative_half_notation_eq (0:ℝ) (by norm_num) (by norm_num)
  have hComp := congrArg
    (fun A : SphereSobolev 0 →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
      A.comp (sphereSobolevMidpointL
        (referenceTwoAngleLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t)
        (referenceTwoAngleSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t)
        (referenceTwoAngleRadialEndpointPairFamily_mem_compatible g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j k l t hp))) hInc.symm
  exact hComp.trans (sphereSobolevInclusionL_midpoint _ _ _)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleRadialEndpointPairFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleRadialEndpointPairFamily_mem_compatible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleSharpMidpointRadialTraceFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleSharpMidpointRadialTraceFamily_of_mem
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleSharpMidpointRadialTraceFamily_upper_inclusion
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceTwoAngleSharpMidpointRadialTraceFamily_lower_inclusion
