import Calderon.ActualReferenceSignedRemainderPivot
import Calderon.NativeHalfCoefficientL2Pivot
set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceSharpRadialTraceSecondRemainder
  referenceLowerRadialTraceSecondRemainder referenceAdjointThreeHalfRadialFamily
  referenceAdjointHalfRadialFamily secondTaylorRemainder sphereSobolevInclusionL

open NativeCoefficientBoundaryMultiplier NativeThreeHalfCoefficientMultiplier
  NativeOrderOneCoefficientMultiplier
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Ihi" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "Jlo" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "Z0" => sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
local notation "Piv" => sphereSobolevDualPairing (-(1/2 : ℝ))
attribute [local irreducible] nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL
  nativeNegativeHalfCoefficientMulL sphereSobolevDualPairing

lemma referenceRadialCoefficient_genuine_graphs_and_pivot_pairings
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (Q : SmoothCoefficientJets 3)
    (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    let Sh := referenceSharpRadialTraceSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
    let Sl := referenceLowerRadialTraceSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
    let Th := secondTaylorRemainder (fun s : ℝ => referenceAdjointThreeHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,s))) r
    let Tl := secondTaylorRemainder (fun s : ℝ => referenceAdjointHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,s))) r
    let MH := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
    let ML := nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
    let MN := nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
    (∀ v : Hi, Jlo (Th (MH v)) = Tl (ML (Ihi v))) ∧
    (∀ v : Hi, Jlo (ML (Sh v)) = MN (Sl (Ihi v))) ∧
    (∀ z : Half, ∀ v : Hi, Piv (MN (Sl z)) (Ihi v) = ⟪Z0 z,Z0 (Th (MH v))⟫_ℝ) ∧
    (∀ z : Half, ∀ v : Hi, Piv (Tl (ML z)) (Ihi v) = ⟪Z0 z,Z0 (ML (Sh v))⟫_ℝ) := by
  dsimp only
  let Sh := referenceSharpRadialTraceSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
  let Sl := referenceLowerRadialTraceSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
  let Th := secondTaylorRemainder (fun s : ℝ => referenceAdjointThreeHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,s))) r
  let Tl := secondTaylorRemainder (fun s : ℝ => referenceAdjointHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,s))) r
  let MH := nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q
  let ML := nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
  let MN := nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
  have hS (v : Hi) : Jlo (Sh v) = Sl (Ihi v) :=
    congrArg (fun A : Hi →L[ℝ] Neg => A v)
      (referenceSharpRadialTraceSecondRemainder_lower_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r hSegment)
  have hT (v : Hi) : Jlo (Th v) = Tl (Ihi v) :=
    congrArg (fun A : Hi →L[ℝ] Neg => A v)
      (referenceAdjointRadialSecondRemainder_high_half_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y r hSegment)
  have hI (v : Hi) : Ihi (MH v) = ML (Ihi v) :=
    congrArg (fun A : Hi →L[ℝ] Half => A v)
      (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 Q
        (smoothMultiplierLowerJets Q) (coefficientValue_smoothMultiplierLowerJets Q).symm)
  have hJ (z : Half) : Jlo (ML z) = MN (Jlo z) :=
    congrArg (fun A : Half →L[ℝ] Neg => A z)
      (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q))
  have hPiv := referenceRadialSecondRemainder_genuine_pivot_pairings
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y r hSegment
  refine ⟨?_,?_,?_,?_⟩
  · intro v
    exact (hT (MH v)).trans (congrArg Tl (hI v))
  · intro v
    exact (hJ (Sh v)).trans (congrArg MN (hS v))
  · intro z v
    have hN : Piv (MN (Sl z)) (Ihi v) = Piv (Sl z) (ML (Ihi v)) :=
      nativeNegativeHalfCoefficientMulL_dualPairing_left_eq_right hcalc hF hO hD τ0
        (smoothMultiplierLowerJets Q) (Sl z) (Ihi v)
    have hMove : Piv (Sl z) (ML (Ihi v)) = Piv (Sl z) (Ihi (MH v)) :=
      congrArg (fun w : Half => Piv (Sl z) w) (hI v).symm
    exact hN.trans (hMove.trans (hPiv.1 z (MH v)))
  · intro z v
    exact (hPiv.2 (ML z) v).trans
      (nativeHalfCoefficientMulL_lowerJets_inner_zero_left_eq_right hcalc hF hO hD τ0 Q z (Sh v))
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
