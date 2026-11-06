import Calderon.ActualReferenceRadialEndpointInvertibleTopology
import Calderon.SphereSobolevCompatibleInterpolationTopology

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeHarmonicLiftCompletion NativeCoefficientBoundaryMultiplier
  NativeBoundaryCoefficientFamilies NativeNormalCoefficientInverseFamily
lemma sphereSobolevInclusionL_negative_half_notation_eq
    (s : ℝ) (hleft : (-1/2 : ℝ) ≤ s) (hright : -(1/2 : ℝ) ≤ s) :
    sphereSobolevInclusionL s (-1/2 : ℝ) hleft =
      sphereSobolevInclusionL s (-(1/2 : ℝ)) hright := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext k
  change SpectralWeightedGraph.besselWeight ((-1/2 : ℝ)-s) k • u k =
    SpectralWeightedGraph.besselWeight ((-(1/2 : ℝ))-s) k • u k
  have hindex : (-1/2 : ℝ) = -(1/2 : ℝ) := by norm_num
  exact congrArg (fun t : ℝ => SpectralWeightedGraph.besselWeight (t-s) k • u k) hindex

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

/-! Fully expanded before source in EXPANSION-actual-reference-sharp-midpoint-family-v001.json.
Actual same retained coefficient a, no parameter-dependent bound choices in the maps. -/
def referenceRadialEndpointPairFamily (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) (p : ℝ × (R3 × ℝ)) : SphereSobolevEndpointPair :=
  (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p,referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p)

lemma referenceRadialEndpointPairFamily_mem_compatible (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceRadialEndpointPairFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p ∈ sphereSobolevCompatibleEndpoints := by
  change (sphereSobolevInclusionL (1/2 : ℝ) (-1/2 : ℝ) (by norm_num)).comp
      (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) =
    (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num))
  have hInc := sphereSobolevInclusionL_negative_half_notation_eq (1/2 : ℝ)
    (by norm_num) (by norm_num)
  have hComp := congrArg
    (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      A.comp (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p)) hInc
  exact hComp.trans
    (referenceSharpRadialTraceFamily_lower_compatibility_on_locus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp)

def referenceSharpMidpointRadialTraceFamily (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    (ℝ × (R3 × ℝ)) → (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
  sphereSobolevCompatibleInterpolationFamily (referenceRadialEndpointPairFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) (referenceRadialEndpointPairFamily_mem_compatible g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)

lemma referenceSharpMidpointRadialTraceFamily_of_mem (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    referenceSharpMidpointRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p = sphereSobolevMidpointL (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) (referenceRadialEndpointPairFamily_mem_compatible g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp) :=
  sphereSobolevCompatibleInterpolationFamily_of_mem (referenceRadialEndpointPairFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) (referenceRadialEndpointPairFamily_mem_compatible g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) p hp

lemma referenceSharpMidpointRadialTraceFamily_lower_inclusion (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    (sphereSobolevInclusionL 0 (-(1/2 : ℝ)) (by norm_num)).comp (referenceSharpMidpointRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) =
      (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp (sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num)) := by
  rw [referenceSharpMidpointRadialTraceFamily_of_mem g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp]
  have hInc := sphereSobolevInclusionL_negative_half_notation_eq (0 : ℝ)
    (by norm_num) (by norm_num)
  have hComp := congrArg
    (fun A : SphereSobolev 0 →L[ℝ] SphereSobolev (-(1/2 : ℝ)) =>
      A.comp (sphereSobolevMidpointL (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) (referenceRadialEndpointPairFamily_mem_compatible g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp))) hInc.symm
  exact hComp.trans
    (sphereSobolevInclusionL_midpoint (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) (referenceRadialEndpointPairFamily_mem_compatible g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp))

lemma referenceSharpMidpointRadialTraceFamily_upper_inclusion (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    (referenceSharpMidpointRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p).comp (sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num)) =
      (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)).comp (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) := by
  rw [referenceSharpMidpointRadialTraceFamily_of_mem g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp]
  exact sphereSobolevMidpointL_inclusion (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) (referenceRadialEndpointPairFamily_mem_compatible g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp)

lemma referenceSharpMidpointRadialTraceFamily_eq_native_radial_on_high_data (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) (f : SphereSobolev (3/2 : ℝ)) :
    referenceSharpMidpointRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p (sphereSobolevInclusionL (3/2 : ℝ) 1 (by norm_num) f) =
      sphereSobolevZeroEquiv hO hD
        (referenceNativeRadialTraceOperatorFamily g L y0 Φ B ε C ρ H a w hData hcalc τ0 p.1 p.2
          (harmonicLiftCompletion hF f)) := by
  have h := congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev 0 => A f)
    (referenceSharpMidpointRadialTraceFamily_upper_inclusion g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp)
  exact h.trans (sphereSobolevInclusionL_referenceSharpRadialTraceFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p f)

lemma norm_referenceSharpMidpointRadialTraceFamily_le (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ‖referenceSharpMidpointRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p‖ ≤ (‖referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p‖+‖referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p‖)/2 := by
  rw [referenceSharpMidpointRadialTraceFamily_of_mem g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp]
  exact norm_sphereSobolevMidpointL_le (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p) (referenceRadialEndpointPairFamily_mem_compatible g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hp)

lemma contDiffOn_referenceSharpMidpointRadialTraceFamily_invertibleLocus (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiffOn ℝ ∞ (referenceSharpMidpointRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) := by
  have hPair : ContDiffOn ℝ ∞ (referenceRadialEndpointPairFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :=
    (contDiffOn_referenceLowerRadialEndpointFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).prodMk
      (contDiffOn_referenceSharpRadialTraceFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
  exact contDiffOn_sphereSobolevCompatibleInterpolationFamily (referenceRadialEndpointPairFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) (referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) (referenceRadialEndpointPairFamily_mem_compatible g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) hPair

lemma contDiffAt_referenceSharpMidpointRadialTraceFamily (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (hp : p ∈ referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (referenceSharpMidpointRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) p :=
  (contDiffOn_referenceSharpMidpointRadialTraceFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).contDiffAt
    ((isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds hp)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialEndpointPairFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialEndpointPairFamily_mem_compatible
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSharpMidpointRadialTraceFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSharpMidpointRadialTraceFamily_of_mem
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSharpMidpointRadialTraceFamily_lower_inclusion
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSharpMidpointRadialTraceFamily_upper_inclusion
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSharpMidpointRadialTraceFamily_eq_native_radial_on_high_data
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_referenceSharpMidpointRadialTraceFamily_le
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceSharpMidpointRadialTraceFamily_invertibleLocus
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceSharpMidpointRadialTraceFamily
