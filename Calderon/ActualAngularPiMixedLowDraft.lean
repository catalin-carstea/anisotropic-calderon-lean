import Calderon.ActualPiMixedWeakEndpointCore
import Calderon.ActualAngularPiMixedCapsDraft
import Calderon.SphereSobolevBalancedDualKernelRestriction
import Calderon.SphereSobolevBalancedDualInterpolationLinear
import Calderon.SphereSobolevBalancedDualEndpointExtension
import Calderon.SphereSobolevDualRiesz
import Calderon.SphereSobolevDualOrthogonalPullback
import Calderon.SphereSobolevPhysicalCrossInclusionPairing
import Calderon.SphereSobolevPairingInclusion
import Calderon.ActualReferenceLowerBoundaryTranspose
import Calderon.ActualReferenceAdjointRadialSignedRemainder

/-! Contents:
* §1 `v016TransposeL`: the continuous linear Riesz transpose `(Hi→Half) →L (Neg→H^{-3/2})`, its
  exact pairing identity, and `‖Dᵗ‖ ≤ ‖D‖`.
* §2 Lemma A: a paired adjunction (repository pairing, no extra factor) gives balanced endpoint
  compatibility of `(Dᵗ, C)`.
* §3 a generic family theorem. Given smooth `C, D` on a UniqueDiffOn `S` with the adjunction on `S`,
  it builds the canonical low endpoint with `ContDiffOn ∞`, the upper graph `C_l ∘ IH = JL ∘ C`, the
  lower (weak) graph, and the midpoint norm. It uses only the relative kernel restriction.
* §4 the uniform cap combiner over `i k` and two lower maps.
* §5 the generic algebraic mixed adjunction `[a,TΠ]^† = [ΠS,A]` from the primitive identities,
  plus the actual primitives (Tt), (Tc), (Sc) proved on the room. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter Metric
open scoped ContDiff ENNReal Topology InnerProductSpace

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft

open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotation MetricOperator
  NormalCoordinatesFrame NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier NativeNegativeHalfSmoothMultiplier ActualAngularHighDraft

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "NegH" => SphereSobolev (-(1/2 : ℝ))
local notation "Neg3" => SphereSobolev (-(3/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "I13" => sphereSobolevInclusionL (1/2 : ℝ) (-(3/2 : ℝ)) (by norm_num)
local notation "I31" => sphereSobolevInclusionL (3/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "I33" => sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)

/-! ### §5b Actual primitives (Tt), (Tc), (Sc) on the room -/

variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hreg : FixedDirichletRegularity)

local notation "Ω" => referenceRadialEndpointInvertibleLocus
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "ShS" => sharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "SlS" => lowerSharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Th" => adjointHighRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Tl" => adjointHalfRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData

/-- (Tt) The actual signed `Tl` is the half-level transpose of the actual signed `Sl`. -/
lemma v016_actual_Tl_eq_transpose_Sl (p : Pphys)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ Ω) :
    Tl p = sphereLowerDistributionalTranspose (SlS p) := by
  have hActual := secondTaylorRemainder_referenceAdjointHalfRadial_eq_transpose
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p.1 p.2.1 p.2.2 hSeg
  unfold adjointHalfRemainder lowerSharpRemainder referenceLowerRadialTraceSecondRemainder
  exact hActual

/-- (Tt), pairing form: `⟨v, Sl u⟩ = ⟨u, Tl v⟩` on Half, SAME `p`. -/
lemma v016_actual_pairing_Sl_Tl (p : Pphys)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ Ω) (u v : Half) :
    PP v (SlS p u) = PP u (Tl p v) := by
  rw [v016_actual_Tl_eq_transpose_Sl hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData p hSeg]
  exact sphereSobolevDualPairing_lower_distributionalTranspose (SlS p) u v

include hreg in
/-- (Tc) `JL ∘ Th = Tl ∘ IH`, pointwise. -/
lemma v016_actual_Th_compat (p : Pphys)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ Ω) (z : Hi) :
    JL (Th p z) = Tl p (IH z) :=
  congrArg (fun A : Hi →L[ℝ] NegH => A z)
    (referenceAdjointRadialSecondRemainder_high_half_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg p.1 p.2.1 p.2.2 hSeg)

/-- (Sc) `Sl ∘ IH = JL ∘ Sh`, pointwise. -/
lemma v016_actual_Sh_compat (p : Pphys)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ Ω) (z : Hi) :
    SlS p (IH z) = JL (ShS p z) :=
  (congrArg (fun A : Hi →L[ℝ] NegH => A z)
    (referenceSharpRadialTraceSecondRemainder_lower_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p.1 p.2.1 p.2.2 hSeg)).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft.v016_actual_pairing_Sl_Tl
